import "postprocessing.geometry";
import "util.multiset";

signature PATH =
sig
    type path;

    exception ZeroPath;

    val empty_path : path;
    val reverse_path : path -> path;
    val combine_path : path -> path -> path;

    
    val point_to_path : Geometry.point_con option ref -> Geometry.point_con option ref * path;
    val path_between : Geometry.point_con option ref -> Geometry.point_con option ref -> path;
    val distance_direction_to_path : Geometry.distance_con option ref * Geometry.direction_con option ref -> path;
    val path_to_points : path -> Geometry.point_con option ref -> Geometry.point_con option ref;

    val get_direction_constraints : path * path -> Geometry.pos_neg_constraint list list;
    val get_circle_constraints : path -> Geometry.pos_neg_constraint list list;
    val get_distance_constraints : path * path -> Geometry.point_con option ref -> Geometry.pos_neg_constraint list list;

    val does_hold : Geometry.constraint -> bool;
    val does_not_hold : Geometry.constraint -> bool;

    exception PathError of string;

    exception Timeout;
    val reset_time : unit -> unit;
    
    (*
    val direction_of_path : path -> Geometry.direction_con option ref;
    val distance_of_path : path -> Geometry.distance_con option ref;
    *)
end


structure Path : PATH =
struct
    exception Timeout
    val time = ref (Time.fromSeconds 0);
    fun reset_time () = time := Time.now ();
    fun timeout () = if Time.now () > (!time + (Time.fromMilliseconds 100)) then raise Timeout else ();

    val debug = false;

    val loop_root = ref NONE;

    datatype tvl = YES | NO | MAYBE;

    fun tvl_not YES = NO
      | tvl_not MAYBE = MAYBE
      | tvl_not NO = YES
    
    fun tvl_and NO _ = NO
      | tvl_and _ NO = NO
      | tvl_and YES YES = YES
      | tvl_and _ _ = MAYBE;
    
    fun tvl_or _ YES = YES
      | tvl_or YES _ = YES
      | tvl_or _ MAYBE = MAYBE
      | tvl_or MAYBE _ = MAYBE
      | tvl_or NO NO = NO
    
    fun tvl_xnor YES YES = YES
      | tvl_xnor YES NO = NO
      | tvl_xnor NO YES = NO
      | tvl_xnor _ _ = MAYBE;
    
    fun definite f x y = f x y = YES;

    fun tvl_any [] = NO
      | tvl_any (NO::l) = tvl_any l
      | tvl_any (MAYBE::l) = if tvl_any l = YES then YES else MAYBE
      | tvl_any (YES::l) = YES;

    exception ZeroPath;
    exception PathError of string;

    datatype path = Path of ((int * string  MultisetPair.multiset_pair * dir_rep) * (dis_term MultisetPair.multiset_pair)) Multiset.multiset
      and dir_rep = DRBetween of Geometry.point_con option ref * Geometry.point_con option ref | DRUnknown of Geometry.direction_con option ref (*These options should always be NONE*)
      and dis_term = SRTermBetween of Geometry.point_con option ref * Geometry.point_con option ref (*should always be NONE*)
                   | SRTermUnknown of Geometry.distance_con option ref
                   | SRTermValue of string
                   | SRTermPath of path
                   | SRTermDot of path * path
                   | SRTermSDot of int * string MultisetPair.multiset_pair;

    val empty_path = Path(Multiset.empty)

    fun steps_of (Path(x)) = x;

    (*EQUALITY*)

    fun same_step_direction ((x1,y1,DRUnknown z1), _) ((x2,y2,DRUnknown z2), _) =
            if z1 <> z2 then
                MAYBE
            else if x1 = x2 andalso MultisetPair.eq (fn x => fn y => x = y) y1 y2 then
                YES
            else
                NO
      | same_step_direction ((x1,y1,DRBetween (p1, q1)), _) ((x2,y2,DRBetween (p2, q2)), _) =
            if p1 = p2 andalso q1 = q2 then
                if x1 = x2 andalso MultisetPair.eq (fn x => fn y => x = y) y1 y2 then
                    YES
                else
                    NO
            else if p1 = q2 andalso q1 = p2 then
                if (x1 = (x2 + 2) mod 4) andalso MultisetPair.eq (fn x => fn y => x = y) y1 y2 then
                    YES
                else
                    NO
            else
                MAYBE
      | same_step_direction _ _ = MAYBE;
    fun common_rotation_terms (Path([])) = raise ZeroPath
      | common_rotation_terms (Path(steps as (((h, _, _), ss)::tsteps))) = (
            List.foldl (fn (((x,_,_),_),y) => Int.min (x,y)) h tsteps, 
            MultisetPair.normalising_factor (fn x => fn y => x = y) (List.map (fn ((_,x,_),_) => x) steps)
        );
    fun same_step step1 step2 = tvl_and (same_step_direction step1 step2) (same_step_distance step1 step2)
    and same_step_distance (_,dist_1) (_,dist_2) = if divide_distance dist_1 dist_2 = (Multiset.empty, Multiset.empty) then YES else MAYBE (*when can we guarantee they're not the same?*)
    and divide_distance d1 d2 = MultisetPair.divide (definite same_distance_term) (d1,d2)
    and same_distance_term (SRTermBetween(x1,y1)) (SRTermBetween(x2,y2)) = if (x1 = x2 andalso y1 = y2) orelse (x1 = y2 andalso y1 = x2) then YES else MAYBE
      | same_distance_term (SRTermUnknown(x)) (SRTermUnknown(y)) = if x = y then YES else MAYBE
      | same_distance_term (SRTermPath(p1)) (SRTermPath(p2)) = same_path_distance p1 p2
      | same_distance_term (SRTermDot(x1,y1)) (SRTermDot(x2,y2)) = 
            tvl_or 
                (tvl_xnor
                    (same_path_direction x1 x2)
                    (same_path_direction y1 y2))
                (tvl_xnor
                    (same_path_direction x1 y2)
                    (same_path_direction y1 x2))
      | same_distance_term (SRTermSDot(a1,b1)) (SRTermSDot(a2,b2)) = if a1 = a1 andalso MultisetPair.eq (fn x => fn y => x = y) b1 b2 then YES else NO
      | same_distance_term (SRTermValue(v1)) (SRTermValue(v2)) = if v1 = v2 then YES else NO
      | same_distance_term _ _ = MAYBE
    and same_path_distance (Path(steps_1)) (Path(steps_2)) = 
        let val _ = timeout ();
            fun normalise_direction [] = []
              | normalise_direction (steps as (((h,_,_),_)::tsteps)) =
                    let val (nf1,nf2) = common_rotation_terms (Path steps);
                    in 
                        Multiset.map (fn ((x,y,z),w) => ((x - nf1, MultisetPair.divide (fn p => fn q => p = q) (y,nf2), z), w)) steps
                    end
            val north = DRUnknown (ref NONE);
            fun orient ss = if singular_steps_direction ss = YES then Multiset.map (fn ((nn, vv, dd), ss) => ((nn, vv, north), ss)) ss else ss
            val (normalised_1, normalised_2) = (normalise_direction steps_1, normalise_direction steps_2);
            val (oriented_1, oriented_2) = (orient normalised_1, orient normalised_2);
            val (cancelled_1, cancelled_2) = Multiset.cancel (definite same_step) (oriented_1, oriented_2);
        in
            case (cancelled_1, cancelled_2) of
                ([], []) => YES
              | (_, _) => MAYBE
        end
    and singular_steps_direction [] = YES
      | singular_steps_direction [x] = YES
      | singular_steps_direction (x::(y::z)) = tvl_and (same_step_direction x y) (singular_steps_direction (y::z))
    and normalise_distance (Path([])) = Path([])
      | normalise_distance (Path((dd,(aa,bb))::xs)) =
            let val (numerator, denominator) = 
                        Multiset.fold 
                            (fn ((_,(n,d)), (hn, hd)) => (Multiset.intersect (definite same_distance_term) n hn, Multiset.intersect (definite same_distance_term) d hd)) 
                            (aa,bb) xs;
            in
                Path(Multiset.map (fn (x,(n,d)) => (x,(Multiset.subtract (definite same_distance_term) numerator n, Multiset.subtract (definite same_distance_term) denominator d))) ((dd,(aa,bb))::xs))
            end
    and same_path_direction path_1 path_2 = 
        let 
            val _ = timeout ();
            val (cancelled_1, cancelled_2) = Multiset.cancel (definite same_step) (steps_of (normalise_distance path_1), steps_of (normalise_distance path_2));
        in
            (case (cancelled_1, cancelled_2) of
                ([], []) => YES
              | ([], _) => MAYBE (*We don't know whether the right might cancel down*)
              | (_, []) => MAYBE
              | ((x::xs), (y::ys)) => 
                    if singular_steps_direction (x::xs) = YES andalso singular_steps_direction (y::ys) = YES then 
                        same_step_direction x y 
                    else 
                        MAYBE
            )
        end;
    
    fun singular_direction (Path((((a,b,c),s)::xs))) = (
            if Multiset.all (fn ((a1,b1,c1),_) => definite same_step_direction ((a1,b1,c1),s) ((a,b,c),s)) xs then
            SOME((a,b,c),s) else NONE)
      | singular_direction (Path([])) = raise ZeroPath;
    
    fun singular_direction_anchor (Path([])) = true
      | singular_direction_anchor (Path(((a,b,c),s)::xs)) = 
            Multiset.all (fn ((a1,b1,c1),_) => c1 = c) xs;

    (*OPERATIONS*)

    fun turn_step n ((x, y, z), s) = (((n + x) mod 4, y, z), s);
    fun reverse_step step = turn_step 2 step;
    fun reverse_path (Path(x)) = Path(Multiset.map reverse_step x);
    fun multiply_distance (x1,y1) (x2,y2) = 
            let val (uncancelled_num, uncancelled_denom) = (Multiset.append x1 x2, Multiset.append y1 y2)
                val intersection = Multiset.intersect (definite same_distance_term) uncancelled_num uncancelled_denom
            in
                (Multiset.subtract (definite same_distance_term) intersection uncancelled_num, Multiset.subtract (definite same_distance_term) intersection uncancelled_denom)
            end;
    fun multiply_step y (d,s) = (d, multiply_distance s y);
    fun multiply_path (Path(x)) y = Path(Multiset.map (multiply_step y) x);
    fun divide_step y (d,s) = (d, divide_distance s y);
    fun divide_path (Path(x)) y = Path(Multiset.map (divide_step y) x);
    fun right_path (Path(x)) = Path(Multiset.map (fn step => turn_step 1 step) x);
    fun turn_path n (Path(x)) = Path(Multiset.map (fn step => turn_step n step) x);
    fun unturn_path n p = turn_path (4-n mod 4) p;
    fun rdir_path (Path(x)) v = Path(Multiset.map (fn ((x,y,z),s) => ((x, MultisetPair.cons (fn x => fn y => x = y) v y, z), s)) x);
    fun ldir_path (Path(x)) v = Path(Multiset.map (fn ((x,y,z),s) => ((x, MultisetPair.uncons (fn x => fn y => x = y) v y, z), s)) x);
    fun unrdir_step vs ((a,b,c),d) = ((a, MultisetPair.divide (fn x => fn y => x = y) (b,vs),c),d)
    fun unrdir_path (Path xs) vs = Path (Multiset.map (unrdir_step vs) xs);
    fun flatten (Path []) = Path []
      | flatten (Path (x::xs)) = raise (PathError "Patherror")
    fun owrap f NONE = NONE | owrap f (SOME x) = SOME (f x)
    fun try_snap_step ((_,_,DRUnknown _), _) _ = NONE
      | try_snap_step _ ((_,_,DRUnknown _), _) = NONE
      | try_snap_step (x as ((0,([],[]),DRBetween(a,b)),_)) (y as ((0,([],[]),DRBetween(c,d)),_)) = 
        if b = c orelse a = d then
            let val nx = divide_step ([SRTermBetween(a,b)],[]) x;
                val ny = divide_step ([SRTermBetween(c,d)],[]) y;
                val nxd = case ny of ((a,b,c),d) => d
                val same_distance = same_step_distance nx ny = YES;
            in
                if same_distance then
                    if b = c then
                        SOME((0,MultisetPair.empty,DRBetween(a,d)), multiply_distance ([SRTermBetween(a,d)],[]) nxd)
                    else
                        SOME((0,MultisetPair.empty,DRBetween(c,b)), multiply_distance ([SRTermBetween(c,b)],[]) nxd)
                else
                    NONE
            end
        else
            NONE
      | try_snap_step ((1,([],[]),a),b) ((1,([],[]),c),d) = owrap (turn_step 1) (try_snap_step ((0,([],[]),a),b) ((0,([],[]),c),d))
      | try_snap_step ((1,([],[]),a),b) ((0,([],[]),c),d) = NONE
      | try_snap_step ((0,([],[]),a),b) ((1,([],[]),c),d) = NONE
      | try_snap_step ((x,([],[]),DRBetween(a,b)),c) d = try_snap_step ((x-2,([],[]),DRBetween(b,a)),c) d
      | try_snap_step d ((x,([],[]),DRBetween(a,b)),c) = try_snap_step d ((x-2,([],[]),DRBetween(b,a)),c)
      | try_snap_step ((a,b,c),d) ((e,f,g),h) = 
            if MultisetPair.eq (fn x => fn y => x = y) b f then 
                owrap (fn ((i,j,k),l) => ((i,MultisetPair.multiply (fn x => fn y => x = y) (b,j),k),l)) (try_snap_step ((a,([],[]),c),d) ((e,([],[]),g),h)) 
            else 
                NONE;
    fun combine_path (Path(x)) (Path(y)) = 
        let fun check_cancel a b = (same_step (reverse_step a) b) = YES;
            val cancelled = Multiset.collide check_cancel x y;
            exception Snap of (
                ((int * string MultisetPair.multiset_pair * dir_rep) * (dis_term MultisetPair.multiset_pair)) 
                * ((int * string MultisetPair.multiset_pair * dir_rep) * (dis_term MultisetPair.multiset_pair)) 
                * ((int * string MultisetPair.multiset_pair * dir_rep) * (dis_term MultisetPair.multiset_pair))
            );
            fun snap_all l = ((Multiset.map (fn (x,y) => owrap (fn z => raise (Snap (x,y,z))) (try_snap_step x y)) (Multiset.flat (Multiset.pairings cancelled cancelled));l)
                                handle Snap(a,b,c) => snap_all (Multiset.cons c (Multiset.remove (fn x => x = b) (Multiset.remove (fn x => x = a) l))))
            val snapped = (*snap_all*) cancelled;
        in 
            Path(snapped)
        end;
    fun combine_paths l = List.foldr (fn (x,y) => combine_path x y) (Path []) l;

    fun opposite_step_direction step1 = same_step_direction (reverse_step step1);

    fun distance_of (Path([])) = raise ZeroPath
      | distance_of (Path([(_,x)])) = x
      | distance_of (p as Path((_,(fn1,fd1))::xs)) = 
            let val (fnum, fdenom) = Multiset.fold (fn ((_,(n,d)), (hn, hd)) => (Multiset.intersect (definite same_distance_term) n hn, Multiset.intersect (definite same_distance_term) d hd)) (fn1,fd1) xs;
            in
                (SRTermPath (divide_path p (fnum, fdenom)) :: fnum, fdenom)
            end;
    
    (*MORE CHECKS*)

    fun perpendicular p1 p2 = tvl_or (same_path_direction (right_path p1) p2) (same_path_direction p1 (right_path p2))
    fun zero_length_sr_term (SRTermBetween (x, y)) = MAYBE (*Could use falsifiers here but that would get a bit complicated*)
      | zero_length_sr_term (SRTermUnknown x) = MAYBE
      | zero_length_sr_term (SRTermValue x) = NO
      | zero_length_sr_term (SRTermPath p) = zero_length_path p
      | zero_length_sr_term (SRTermDot (p1, p2)) = tvl_not (perpendicular p1 p2)
      | zero_length_sr_term (SRTermSDot (a,b)) = if (a mod 2) = 0 orelse MultisetPair.numerator b = [] orelse MultisetPair.denominator b = [] then NO else YES
    and zero_length_step (_, (l,_)) = tvl_any (List.map zero_length_sr_term l)
    and zero_length_path (Path([])) = YES
      | zero_length_path (Path([x])) = zero_length_step x
      | zero_length_path (p) = MAYBE;
    
    fun same_path p1 p2 = case (zero_length_path p1, zero_length_path p2) of
        (YES, YES) => YES
      | _ => tvl_and (same_path_direction p1 p2) (same_path_distance p1 p2);
    
    (*FROM GEOMETRY*)

    fun point_to_path p = (timeout (); case !p of
        NONE => (p, empty_path)
      | SOME(Geometry.PCopy(x)) => point_to_path(x)
      | SOME(Geometry.Move(x,y,z)) => let val (start_point, return_path) = point_to_path(x) in (start_point, combine_path (distance_direction_to_path(z,y)) return_path) end
    )
    and distance_direction_to_path (dist, dir) = (case !dir of
        NONE => (Path(Multiset.map (fn x => ((0, MultisetPair.empty, DRUnknown dir), x)) (rep_distances dist)) handle ZeroPath => Path([]))
      | SOME(Geometry.Direction(x,y)) =>
            (let val path = path_between x y;
                val path_length = distance_of path;
            in
                case (singular_direction path) of
                NONE => combine_paths (List.map (fn x => multiply_path (divide_path path path_length) x) (rep_distances dist))
              | SOME(d,_) => combine_paths (List.map (fn x => Path([(d, x)]) ) (rep_distances dist))
            end handle ZeroPath => Path([]))
      | SOME(Geometry.Right(x)) => right_path (distance_direction_to_path(dist,x))
      | SOME(Geometry.RDir(x,"9")) => right_path (distance_direction_to_path(dist,x))
      | SOME(Geometry.RDir(x,v)) => rdir_path (distance_direction_to_path(dist,x)) v
      | SOME(Geometry.LDir(x,v)) => ldir_path (distance_direction_to_path(dist,x)) v
      | SOME(Geometry.DCopy(x)) => distance_direction_to_path(dist,x)) handle ZeroPath => (Path [])
    
    and path_between a b = 
        let val (start_a, path_a) = point_to_path a;
            val (start_b, path_b) = point_to_path b;
        in
            if start_a = start_b then 
                combine_path (reverse_path path_a) path_b 
            else 
                combine_path (combine_path (reverse_path path_a) path_b) (
                    Path(
                        Multiset.single (
                            if Geometry.point_index start_a < Geometry.point_index start_b then 
                                ((0, MultisetPair.empty, DRBetween (start_a,start_b)),
                                ([SRTermBetween (start_a,start_b)],[]))
                            else
                                ((2, MultisetPair.empty, DRBetween (start_b,start_a)),
                                ([SRTermBetween (start_b,start_a)],[]))
                        )
                    )
                )
        end  
    and rep_distances dist = case !dist of
        NONE => [([SRTermUnknown(dist)],[])]
      | SOME(Geometry.Distance(a,b)) => 
            let val (full_path as (Path(full_steps))) = path_between a b;
            in
                if is_some (singular_direction full_path) then
                    List.map (distance_of o Path o Multiset.single) full_steps
                else
                    [distance_of full_path]
            end 
      | SOME(Geometry.Times(a,b)) => List.flatmap (fn x => List.map (fn y => multiply_distance x y) (rep_distances b)) (rep_distances a)
      | SOME(Geometry.Divide(a,b)) => 
            let val dir = ref NONE;
                val denominator = distance_of (Path(List.map (fn x => ((0, MultisetPair.empty, DRUnknown dir), x)) (rep_distances b)));
            in
                List.map (fn x => divide_distance x denominator) (rep_distances a)
            end
      | SOME(Geometry.Value(s)) => [([SRTermValue s],[])]
      | SOME(Geometry.SCopy(x)) => rep_distances x
      | SOME(Geometry.Dot(x,y)) => 
            let val p1 = distance_direction_to_path (ref NONE, x);
                val p2 = distance_direction_to_path (ref NONE, y);
                val (dhcf1r, dhcf1v) = common_rotation_terms p1;
                val (_, dhcf2v) = common_rotation_terms p2;
                val p = (fn x => fn y => x = y)
                val common_variables = (fn ((a,b),(c,d)) => (Multiset.intersect p a c, Multiset.union p b d)) (dhcf1v,dhcf2v);
                val rotated_p1 = unturn_path dhcf1r (unrdir_path p1 common_variables);
                val rotated_p2 = unturn_path dhcf1r (unrdir_path p2 common_variables);
            in
                case (singular_direction rotated_p1, singular_direction rotated_p2) of
                    (SOME((a1,b1,c1),_), SOME((a2,b2,c2),_)) => 
                        if definite same_step_direction ((0,([],[]),c1),(SRTermUnknown o ref) NONE) ((0,([],[]),c2), (SRTermUnknown o ref) NONE) then
                            if a2-a1 mod 4 = 3 then
                                let val d1 = ref NONE;
                                in
                                    [([
                                        SRTermPath(Path([
                                            ((0, b1, DRUnknown d1),([],[])),
                                            ((2, b2, DRUnknown d1),([],[]))
                                        ]))
                                    ],[])]
                                end
                            else
                                [([SRTermSDot(a2-a1 mod 4, MultisetPair.divide (fn x => fn y => x = y) (b2, b1))],[])]
                        else 
                            [([SRTermDot(rotated_p1, rotated_p2)],[])]
                    | _ => [([SRTermDot(rotated_p1, rotated_p2)],[])]
            end
      | SOME(Geometry.Zero) => raise ZeroPath;
    
    fun dedenom_loop loop =
        let fun dedenom_loop_rec (Path []) = (Path ([]), [])
              | dedenom_loop_rec (Path ((a,(n,d))::xs)) =
                    let val (Path steps, ds) = dedenom_loop_rec (divide_path (Path(xs)) ([],d)) in
                        (Path (divide_step ([],ds) (a,(n,[]))::steps), d@ds)
                    end
            val (p, _) = dedenom_loop_rec loop;
        in
            p
        end;


    (*TO GEOMETRY*)

    fun turn_through geom_dir ([],[]) = geom_dir
      | turn_through geom_dir ((v::vs),[]) = (ref o SOME o Geometry.RDir) (turn_through geom_dir (vs,[]), v)
      | turn_through geom_dir (us,(v::vs)) = (ref o SOME o Geometry.LDir) (turn_through geom_dir (us,vs), v)

    fun step_to_direction ((0, ([],[]), DRBetween(x,y)), s) = (ref o SOME o Geometry.Direction) (x,y)
      | step_to_direction ((0, ([],[]), DRUnknown(x)), s) = x
      | step_to_direction ((0, ((v::vs),[]), d), s) = (ref o SOME o Geometry.RDir) (step_to_direction ((0,(vs,[]),d),s), v)
      | step_to_direction ((0, (us,(v::vs)), d), s) = (ref o SOME o Geometry.LDir) (step_to_direction ((0,(us,vs),d),s), v)
      | step_to_direction ((n, vs, d), s) = (ref o SOME o Geometry.Right) (step_to_direction ((n-1, vs, d), s));

    fun path_to_points (Path([])) start_point = start_point
      | path_to_points (Path(step::steps)) start_point =
            let val end_point = path_to_points (Path(steps)) start_point;
            in (ref o SOME o Geometry.Move) (end_point, step_to_direction step, step_to_distance step) handle ZeroPath => start_point
            end
    and step_to_distance (d,([],[])) = (ref o SOME o Geometry.Divide) ((fn x => (x,x)) (ref NONE)) (*(PolyML.print(d); raise PathError ("unexpected distance"))*)
      | step_to_distance (d,([SRTermBetween(x,y)],[])) = (ref o SOME o Geometry.Distance) (x,y)
      | step_to_distance (d,([SRTermUnknown(z)],[])) = z
      | step_to_distance (d,([SRTermValue(s)],[])) = (ref o SOME o Geometry.Value) s
      | step_to_distance (d,([SRTermPath(p)],[])) = path_to_distance p
      | step_to_distance (d,([SRTermDot(p1,p2)],[])) = 
            let val direction_1 = path_to_direction p1;
                val direction_2 = path_to_direction p2;
            in
                (ref o SOME o Geometry.Dot) (direction_1, direction_2)
            end
      | step_to_distance (d,([SRTermSDot(a,(b,c))],[])) = 
            let fun repeat 0 f x = x
                  | repeat n f x = f (repeat (n-1) f x);
                val basic_direction = ref NONE;
                val direction_from = Multiset.fold (fn (v,g) => (ref o SOME o Geometry.RDir) (g, v)) basic_direction c;
                val direction_to = Multiset.fold (fn (v,g) => (ref o SOME o Geometry.RDir) (g,v)) (repeat a (ref o SOME o Geometry.Right) basic_direction) b;
            in
                (ref o SOME o Geometry.Dot) (direction_from, direction_to)
            end
      | step_to_distance (d, (x::xs,[])) = (ref o SOME o Geometry.Times) (
            step_to_distance (d, ([x],[])),
            step_to_distance (d, (xs,[]))
        )
      | step_to_distance (d, (xs, ys)) = (ref o SOME o Geometry.Divide) (
            step_to_distance (d, (xs, [])),
            step_to_distance (d, (ys, []))
        )
    and path_to_direction (Path(x)) = (case (singular_direction(Path(x))) of
            NONE => (ref o SOME o Geometry.Direction) (loop_root, (path_to_points (normalise_distance (Path x)) loop_root))
          | SOME(step) => step_to_direction step
    )
    and path_to_distance (Path []) = ref (SOME(Geometry.Zero))
      | path_to_distance (Path [x]) = step_to_distance x
      | path_to_distance p = 
            let val start_point = loop_root;
                val end_point = path_to_points p start_point;
            in
                (ref o SOME o Geometry.Distance) (start_point, end_point)
            end;


    (*CONSTRAINTS*)

    exception Proven of Geometry.pos_neg_constraint list list;
    exception Refuted;

    fun holds (Geometry.PC(p1,p2)) = 
        let val path_1 = path_between p1 p2;
        in
            if path_1 = Path([]) then YES else (if is_some (singular_direction path_1) then NO else MAYBE)
        end
  | holds (Geometry.DC(d1,d2)) = 
        let val s = ref NONE;
            val path_1 = distance_direction_to_path (s, d1);
            val path_2 = distance_direction_to_path (s, d2);
        in
            same_path_direction path_1 path_2
        end
  | holds (Geometry.SC(s1,s2)) = 
        let val d = ref NONE;
            val path_1 = distance_direction_to_path (s1, d);
            val path_2 = distance_direction_to_path (s2, d);
        in
            same_path_distance path_1 path_2
        end
  | holds (Geometry.RC(r1,r2)) = case (!r1, !r2) of
            (SOME(Geometry.Clockwise),SOME(Geometry.Clockwise)) => YES
          | (SOME(Geometry.Clockwise),SOME(Geometry.Opposite(a))) => (case !a of
                SOME(Geometry.Clockwise) => NO
              | SOME(Geometry.Opposite(b)) => holds (Geometry.RC(r1,b))
              | NONE => MAYBE
            )
          | (SOME(Geometry.Opposite(a)),SOME(Geometry.Clockwise)) => holds (Geometry.RC(r2,r1))
          | (SOME(Geometry.Opposite(a)),SOME(Geometry.Opposite(b))) => holds (Geometry.RC(a,b))
          | _ => MAYBE;
    
    fun does_hold x = holds x = YES;
    fun does_not_hold x = holds x = NO;

    fun is_step_free ((0,[],DRBetween(x1,y1)),([SRTermBetween(x2,y2)],[])) = 
            if (x1 = x2 andalso y1 = y2) orelse (x1 = y2 andalso x2 = y1) then
                SOME(x1,y1)
            else
                NONE
      | is_step_free  _ = NONE;
    fun sort_steps_by_direction step [] = ([],[],[],[])         (*same, opposite, perpendicular/different, anything*)
      | sort_steps_by_direction step (x::xs) = 
            let val (a,b,c,d) = sort_steps_by_direction step xs in case (same_step_direction step x, opposite_step_direction step x) of
                (YES, NO) => (x::a,b,c,d)
              | (NO, YES) => (a,x::b,c,d)
              | (NO, NO) => (a,b,x::c,d)
              | (MAYBE, MAYBE) => (a,b,c,x::d)
              | (_, _) => raise (PathError "step is opposite to itself??")
            end;
    fun try_set_point point new_value = if Geometry.point_contains_check point new_value then
                ()
            else
                (
                    (if debug then PolyML.print else (fn x => x)) ("Set >> ", Geometry.PC(point, new_value)); 
                    Geometry.af (); 
                    point := (SOME o Geometry.PCopy) (new_value);
                    raise Proven [[]]
                );
    fun try_set_direction direction new_value = if Geometry.direction_contains_check direction new_value then
                ()
            else
                (   
                    (if debug then PolyML.print else (fn x => x)) ("Set >> ", Geometry.DC(direction, new_value));
                    Geometry.af (); 
                    direction := (SOME o Geometry.DCopy) (new_value);
                    raise Proven [[]]
                );
    fun try_set_distance distance new_value = if Geometry.distance_contains_check distance new_value then
                ()
            else
                (   
                    (if debug then PolyML.print else (fn x => x)) ("Set >> ", Geometry.SC(distance, new_value));
                    Geometry.af (); 
                    distance := (SOME o Geometry.SCopy) (new_value);
                    raise Proven [[]]
                );
    fun try_set_point_and_distance point new_point_value distance new_distance_value = 
            if Geometry.point_contains_check point new_point_value orelse Geometry.distance_contains_check distance new_distance_value then
                ()
            else
                (
                    (if debug then PolyML.print else (fn x => x)) ("Set1 >> ", Geometry.PC(point, new_point_value));
                    (if debug then PolyML.print else (fn x => x)) ("Set2 >> ", Geometry.SC(distance, new_distance_value));
                    Geometry.af ();
                    point := (SOME o Geometry.PCopy) (new_point_value);
                    distance := (SOME o Geometry.SCopy) (new_distance_value);
                    raise Proven [[]]
                );
    fun try_set_distance_if_q distance new_distance_value [[Geometry.X(q)]] = 
            if Geometry.distance_contains_check distance new_distance_value then
                ()
            else
                (
                    (if debug then PolyML.print else (fn x => x)) ("Try Set >> ", Geometry.SC(distance, new_distance_value)); 
                    distance := (SOME o Geometry.SCopy) (new_distance_value);
                    if holds q = YES then
                        ((if debug then PolyML.print else (fn x => x)) "SUCCESS";
                        Geometry.af ();
                        raise Proven [[]])
                    else
                        ((if debug then PolyML.print else (fn x => x)) "FAIL";
                        distance := NONE)
                )
      | try_set_distance_if_q _ _ _ = ();
    fun try_set_point_if_q point new_point_value [[Geometry.X(q)]] = 
            if Geometry.point_contains_check point new_point_value then
                ()
            else
                (
                    (if debug then PolyML.print else (fn x => x)) ("Try Set >> ", Geometry.PC(point, new_point_value)); 
                    point := (SOME o Geometry.PCopy) (new_point_value);
                    if holds q = YES then (
                        (if debug then PolyML.print else (fn x => x)) "SUCCESS";
                        Geometry.af ();
                        raise Proven [[]]
                    ) else (
                        (if debug then PolyML.print else (fn x => x)) "FAIL";
                        point := NONE
                    )
                )
      | try_set_point_if_q _ _ _ = ();
    
    fun get_circle_constraints q = 
        let val (p as Path(xs)) = dedenom_loop q;
            val _ = (if debug then PolyML.print else (fn x => x)) p
            val otherwise = [[Geometry.X(Geometry.PC(loop_root, path_to_points (Path(xs)) loop_root))]] 
            val _ = if zero_length_path p = YES then raise Proven [[]] else ();
            val _ = if is_some (singular_direction (p)) andalso zero_length_path p = NO then raise Refuted else () handle ZeroPath => raise Proven [[]];
            fun set_dir_if_free (((n,m,DRBetween(x1,y1)),_), other_steps) = (
                    try_set_point y1 (* = *) (
                        let val other_path = turn_path ((6 - n) mod 4) (Path other_steps);
                        in
                            if zero_length_path other_path = NO then
                                (ref o SOME o Geometry.Move) (x1, turn_through (path_to_direction other_path) (MultisetPair.invert m), ref NONE)
                            else
                                (ref o SOME o Geometry.Move) (x1, turn_through (path_to_direction other_path) (MultisetPair.invert m), (ref o SOME o Geometry.Distance) (x1, ref NONE))
                        end
                    ) handle Proven [[]] => raise (Proven otherwise);
                    try_set_point x1 (* = *) (
                        let val other_path = (turn_path ((4 - n) mod 4) (Path other_steps));
                        in
                            if zero_length_path other_path = NO then
                                (ref o SOME o Geometry.Move) (y1, path_to_direction other_path, ref NONE)
                            else
                                (ref o SOME o Geometry.Move) (y1, path_to_direction other_path, (ref o SOME o Geometry.Distance) (y1, ref NONE))
                        end
                    ) handle Proven [[]] => raise (Proven otherwise)
                )
              | set_dir_if_free (((n,m,DRUnknown(d)),_), other_steps) = (
                    try_set_direction d (* = *) (
                        turn_through (path_to_direction (turn_path ((6 - n) mod 4) (Path other_steps)))  (MultisetPair.invert m)
                    )
                )

            fun set_dist_term_if_free p (SRTermBetween(x1,y1), other) = (
                    try_set_point y1 (* = *) ((ref o SOME o Geometry.Move) (x1, ref NONE, path_to_distance (divide_path p (other, []))))
                )
              | set_dist_term_if_free p (SRTermUnknown(x), other) = (
                    try_set_distance x (* = *) (path_to_distance (divide_path p (other, [])))
                )
              | set_dist_term_if_free p _ = ();
            fun set_dist_if_free ((step_dir, (numerator, denominator)), other_steps) = 
                    if same_path_direction (Path [turn_step 2 (step_dir, (numerator, denominator))]) (Path other_steps) = YES then
                        (Multiset.pick_map (set_dist_term_if_free (divide_path (Path other_steps) ([], denominator))) numerator; ())
                    else
                        ()
            fun set_dist_if_bij (step as (step_dir, (numerator, denominator)), other_steps) = 
                    let val turned_step = turn_step 2 step;
                        val opp_steps = Multiset.filter (fn x => same_step_direction x turned_step = YES) other_steps;
                        fun for_each_opp_step (opp_dir, (opp_num, opp_denom)) = 
                            let fun set_dist_term_if_bij (SRTermUnknown x, other) = (
                                        try_set_distance_if_q x (path_to_distance (reverse_path (divide_path (Path [(opp_dir, (opp_num, opp_denom))]) (other, denominator)))) otherwise)
                                | set_dist_term_if_bij (SRTermBetween (x,y), other) = (
                                        try_set_point_if_q y (* = *) ((ref o SOME o Geometry.Move) (
                                            x,
                                            ref NONE,
                                            path_to_distance (reverse_path (divide_path (Path [(opp_dir, (opp_num, opp_denom))]) (other, denominator)))
                                        )) otherwise;
                                        try_set_point_if_q x (* = *) ((ref o SOME o Geometry.Move) (
                                            y,
                                            ref NONE,
                                            path_to_distance (reverse_path (divide_path (Path [(opp_dir, (opp_num, opp_denom))]) (other, denominator)))
                                        )) otherwise
                                    )
                                | set_dist_term_if_bij _ = ()
                            in
                                Multiset.pick_map set_dist_term_if_bij numerator
                            end
                        val _ = Multiset.map for_each_opp_step opp_steps;
                    in
                        ()
                    end
            fun set_step_to_zero (_, (num,denom)) = 
                let fun can_set_to_zero (SRTermBetween(x1,x2)) = SOME (fn () => (
                            try_set_point x1 x2;
                            try_set_point x2 x1;
                            raise (Proven otherwise)
                        )) 
                      | can_set_to_zero (SRTermUnknown x) = SOME  (fn () => (
                            try_set_distance x ((ref o SOME) Geometry.Zero);
                            raise (Proven otherwise)
                      ))
                      | can_set_to_zero (SRTermValue _) = NONE
                      | can_set_to_zero (SRTermPath p) = (case zero_length_path p of 
                            YES => raise (Proven [[]])
                          | MAYBE => SOME (fn () => raise (Proven otherwise))
                          | NO => NONE
                        )
                      | can_set_to_zero (SRTermDot (p1, p2)) = NONE
                      | can_set_to_zero (SRTermSDot x) = NONE;
                    val zeroable_nums = Multiset.mapPartial can_set_to_zero num;
                in
                    case zeroable_nums of
                        [] => raise Refuted
                      | [x] => x ()
                      | _ => raise (Proven otherwise)
                end
            fun set_zero_if_other (step,others) =
                    if zero_length_path (Path others) = YES then
                        set_step_to_zero (step)
                    else
                        ();
            fun set_step_if_free (((n,([],[]),DRBetween(x1,y1)),([SRTermBetween(x2,y2)],[])), other_steps) = 
                if (x1 = x2 andalso y1 = y2) orelse (x1 = y2 andalso y1 = x2) then
                    (try_set_point x1 (path_to_points (turn_path ((4 - n) mod 4) (Path other_steps)) y1);
                    try_set_point y1 (path_to_points (turn_path ((6 - n) mod 4) (Path other_steps)) x1))
                else
                    ()
              | set_step_if_free (((n,([],[]),DRBetween(x1, y1)),([SRTermUnknown(z)],[])), other_steps) =
                (
                    try_set_point_and_distance
                        x1 (* = *) (
                            (ref o SOME o Geometry.Move) (y1, path_to_direction (turn_path ((4 - n) mod 4) (Path other_steps)), ref NONE)
                        )
                        z (* = *) (
                            path_to_distance (Path other_steps)
                        )
                        handle ZeroPath => raise Refuted
                )
              | set_step_if_free _ = (); (*TODO: ADD MORE CASES*)
            val _ = Multiset.pick_map set_zero_if_other xs;
            val _ = Multiset.pick_map set_step_if_free xs;
            val _ = Multiset.pick_map (fn (y, ys) => if same_path (reverse_path (Path [y])) (Path ys) = NO then (("RefPair"); raise Refuted) else ()) xs;
            val _ = Multiset.pick_map set_dir_if_free xs;
            val _ = Multiset.pick_map set_dist_if_free xs;
            val _ = Multiset.pick_map set_dist_if_bij xs;
        in
            otherwise
        end handle (Proven x) => x | Refuted => [];
    
    fun get_distance_constraints (path_1, path_2) start =
        let val _ = case same_path_distance path_1 path_2 of
                        YES => raise (Proven [[]])
                      | NO => raise Refuted
                      | _ => ();
            val distance_2 = distance_of path_2;
            val unitpath = divide_path path_1 distance_2;
            val _ = case unitpath of
                        (p as Path([(dir,(n,d))])) => (
                    if Multiset.all (fn x => case x of (SRTermValue x) => true | _ => false) (n @ d) then
                        raise Refuted
                    else
                        let val _ = case Multiset.pick_option (fn x => case x of (SRTermUnknown s) => SOME(s) | _ => NONE) n of
                                        (SOME(s),ss) => try_set_distance s (step_to_distance ((0,MultisetPair.empty,DRUnknown (ref NONE)),(d,ss)))
                                      | _ => ();
                            val _ = case Multiset.pick_option (fn x => case x of (SRTermUnknown s) => SOME(s) | _ => NONE) d of
                                        (SOME(s),ss) => try_set_distance s (step_to_distance ((0,MultisetPair.empty,DRUnknown (ref NONE)),(n,ss)))
                                      | _ => ();
                        in
                            ()
                        end
                    )
                    | _ => ();
            val start = ref NONE;
            val direction = ref NONE;
            
        in 
            [[Geometry.X(Geometry.SC(
                path_to_distance path_1,
                path_to_distance path_2
            ))]]
            (* [[Geometry.X(Geometry.PC(
                (ref o SOME o Geometry.Move) (start, direction, path_to_distance path_1),
                (ref o SOME o Geometry.Move) (start, direction, path_to_distance path_2)
            ))]] *)
        end handle (Proven x) => x | Refuted => [];

    fun get_direction_constraints ((path_1 as Path(steps_1 as (s1::_))),(path_2 as Path(steps_2 as (s2::_)))) = (
        let val _ = case same_path_direction path_1 path_2 of
                        YES => raise Proven [[]]
                      | NO => raise Refuted
                      | _ => ()
            val _ = case (singular_steps_direction steps_1, s1) of
                        (YES, ((a,([],[]),DRUnknown(x)),s)) => try_set_direction x (path_to_direction (turn_path (4-a) path_2))
                      | (YES, ((a,([],[]),DRBetween(p1,p2)),s)) => try_set_point p2 ((ref o SOME o Geometry.Move) (p1, path_to_direction (turn_path (4-a) path_2), ref NONE))
                      | _ => ()
            val _ = case (singular_steps_direction steps_2, s2) of
                        (YES, ((a,([],[]),DRUnknown(x)),s)) => try_set_direction x (path_to_direction (turn_path (4-a) path_1))
                      | (YES, ((a,([],[]),DRBetween(p1,p2)),s)) => try_set_point p2 ((ref o SOME o Geometry.Move) (p1, path_to_direction (turn_path (4-a) path_1), ref NONE))
                      | _ => ()
            val start = ref NONE;
            val distance = ref NONE;
        in
            (* [[Geometry.X(Geometry.DC(
                path_to_direction path_1,
                path_to_direction path_2
            ))]] *)
            [[Geometry.X(Geometry.PC(
                (ref o SOME o Geometry.Move) (start, path_to_direction path_1, distance),
                (ref o SOME o Geometry.Move) (start, path_to_direction path_2, distance)
            ))]]
        end handle (Proven x) => x | Refuted => [])
      | get_direction_constraints _ = raise ZeroPath;

end