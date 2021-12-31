import "postprocessing.geometry";

signature MULTISET =
sig
    type 'a multiset;
    val empty : 'a multiset;
    val single : 'a -> 'a multiset;
    val append : 'a multiset -> 'a multiset -> 'a multiset;
    val cons : 'a -> 'a multiset -> 'a multiset;
    val collide : ('a -> 'a -> bool) -> 'a multiset -> 'a multiset -> 'a multiset;
    val map : ('a -> 'b) -> 'a multiset -> 'b multiset;
    val pick : ('a -> bool) -> 'a multiset -> 'a option * 'a multiset;
    val pick_option : ('a -> 'b option) -> 'a multiset -> 'b option * 'a multiset;
    val pick_map : (('a * 'a multiset -> 'b) -> 'a multiset -> 'b multiset);
    val eq : ('a -> 'a -> bool) -> 'a multiset -> 'a multiset -> bool;
    val fold : (('a * 'b) -> 'b) -> 'b -> 'a list -> 'b;
    val intersect : ('a -> 'a -> bool) -> 'a list -> 'a list -> 'a list;
    val remove : ('a -> bool) -> 'a list -> 'a list;
    val subtract : ('a -> 'a -> bool) -> 'a list -> 'a list -> 'a list;
    val count : ('a -> bool) -> 'a list -> int;
    val daisy_chain : 'a multiset -> ('a * 'a) multiset;
    val list_of : 'a multiset -> 'a list;
    val of_list : 'a list -> 'a multiset;
    val pairings : 'a multiset -> 'b multiset -> ('a * 'b) multiset multiset;
    val size : 'a multiset -> int;
    val all : ('a -> bool) -> 'a multiset -> bool;
end

structure Multiset : MULTISET =
struct
    type 'a multiset = 'a list;
    val empty = [];
    fun single x = [x];
    fun append x y = x @ y;
    fun cons x y = x :: y;
    val map = List.map;
    fun pick p [] = (NONE, [])
      | pick p (x::xs) = 
            if p x then
                (SOME(x),xs) 
            else
                let val (q,r) = pick p xs; in (q,x::r) end;
    
    fun pick_option p [] = (NONE, [])
      | pick_option p (x::xs) = 
                if is_some (p x) then
                    (p x,xs) 
                else
                    let val (q,r) = pick_option p xs; in (q,x::r) end;
    fun pick_map p xs =
        let fun f p [] _ = []
              | f p (y::ys) zs = p (y,zs@ys) :: f p ys (y::zs);
        in
            f p xs []
        end
    
    fun collide p [] ys = ys
      | collide p (x::xs) ys = (case pick (p x) ys of
            (NONE,_) => collide p xs (x::ys)
          | (SOME(y),nys) => collide p xs nys
      )
    val fold = List.foldr;
    fun count p [] = 0
      | count p (x::xs) = if p x then (count p xs) + 1 else count p xs;
    fun intersect eq [] l2 = []
      | intersect eq (x::xs) l2 = if count (eq x) xs < count (eq x) l2  then 
            x::(intersect eq xs l2) 
        else 
            intersect eq xs l2;
    fun remove p [] = []
        | remove p (y::ys) = if p y then ys else y::(remove p ys);
    fun subtract eq [] l2 = l2
        | subtract eq (x::xs) l2 = remove (eq x) (subtract eq xs l2);
    fun eq ieq [] [] = true
      | eq ieq [] _ = false
      | eq ieq _ [] = false
      | eq ieq (x::xs) (ys) = (case pick (ieq x) ys of
            (NONE, _) => false
          | (SOME(z), zs) => eq ieq xs zs);
    
    fun daisy_chain [] = []
      | daisy_chain [_] = []
      | daisy_chain (x::(y::z)) = (x,y)::(daisy_chain (y::z));
    
    fun list_of x = x;
    fun of_list x = x;
    
    fun pairings [] _ = []
      | pairings (x::xs) ys = 
            let fun take_each [] acc =  []
                  | take_each (y::ys) acc =
                        (y, acc @ ys) :: take_each ys (y::acc);
            in
                List.flatmap (fn (z,zs) => List.map (fn w => (x,z)::w) (pairings xs zs)) (take_each ys [])
            end;
      
    val size = List.length;
    val all = List.all;

    exception ZeroPath;
end

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

    exception PathError of string;
    
    (*
    val direction_of_path : path -> Geometry.direction_con option ref;
    val distance_of_path : path -> Geometry.distance_con option ref;
    *)
end


structure Path : PATH =
struct

    exception ZeroPath;
    exception PathError of string;

    datatype path = Path of ((int * string  Multiset.multiset * dir_rep) * (dis_term Multiset.multiset * dis_term Multiset.multiset)) Multiset.multiset
      and dir_rep = DRBetween of Geometry.point_con option ref * Geometry.point_con option ref | DRUnknown of Geometry.direction_con option ref (*These options should always be NONE*)
      and dis_term = SRTermBetween of Geometry.point_con option ref * Geometry.point_con option ref (*should always be NONE*)
                   | SRTermUnknown of Geometry.distance_con option ref
                   | SRTermValue of string
                   | SRTermPath of path
                   | SRTermDot of path * path;

    val empty_path = Path(Multiset.empty)

    fun turn_step n ((x, y, DRBetween(z1,z2)), s) = ((n + x) mod 4) |> (fn x' => if x' > 1 then ((x' - 2, y, DRBetween(z2,z1)), s) else ((x', y, DRBetween(z1,z2)), s))
      | turn_step n ((x, y, DRUnknown(z)), s) = (((n + x) mod 4, y, DRUnknown(z)), s);
    
    fun compare_step ((x1,y1,DRBetween(a1,b1)),(wn1,wd1)) ((x2,y2,DRBetween(a2,b2)),(wn2,wd2)) = if a1 = a2 andalso b1 = b2 then
            (x1 = x2 andalso Multiset.eq (fn x => fn y => x = y) y1 y2 andalso Multiset.eq compare_distance_term wn1 wn2 andalso Multiset.eq compare_distance_term wd1 wd2)
        else if a1 = b2 andalso b1 = a2 then
            x1 = ((x2 + 2) mod 4) andalso Multiset.eq (fn x => fn y => x = y) y1 y2 andalso Multiset.eq compare_distance_term wn1 wn2 andalso Multiset.eq compare_distance_term wd1 wd2
        else
            false
      | compare_step ((x1,y1,DRUnknown(a1)),(wn1,wd1)) ((x2,y2,DRUnknown(a2)),(wn2,wd2)) = 
            a1 = a2 andalso x1 = x2 andalso Multiset.eq (fn x => fn y => x = y) y1 y2 andalso Multiset.eq compare_distance_term wn1 wn2 andalso Multiset.eq compare_distance_term wd1 wd2
      | compare_step _ _ = false
    and compare_distance_term (SRTermBetween(x1,y1)) (SRTermBetween(x2,y2)) = (x1 = x2 andalso y1 = y2) orelse (x1 = y2 andalso y1 = x2)
      | compare_distance_term (SRTermUnknown(x)) (SRTermUnknown(y)) = x = y
      | compare_distance_term (SRTermPath(p1)) (SRTermPath(p2)) = compare_path_distance p1 p2
      | compare_distance_term (SRTermDot(x1,y1)) (SRTermDot(x2,y2)) = (compare_path_direction x1 x2 andalso compare_path_direction y1 y2) orelse (compare_path_direction x1 y2 andalso compare_path_direction y1 x2)
      | compare_distance_term (SRTermValue(v1)) (SRTermValue(v2)) = v1 = v2
      | compare_distance_term _ _ = false
    and compare_path_distance (Path([])) (Path([])) = true
      | compare_path_distance (Path([])) _ = false
      | compare_path_distance _ (Path([])) = false
      | compare_path_distance (Path(steps1)) (Path(steps2)) = 
        let val ((fx1,fy1,_), _) = List.hd steps1;
            val ((fx2,fy2,_), _) = List.hd steps2;
            val (x1,y1) = Multiset.fold (fn (((x,y,z),w),(hx,hy)) => (Int.min (x, hx), Multiset.intersect (fn p => fn q => p = q) y hy)) (fx1, fy1) steps1;
            val (x2,y2) = Multiset.fold (fn (((x,y,z),w),(hx,hy)) => (Int.min (x, hx), Multiset.intersect (fn p => fn q => p = q) y hy)) (fx2, fy2) steps2;
            val rotated_1 = Multiset.map (fn ((x,y,z),w) => ((x - x1, Multiset.subtract (fn p => fn q => p = q) y1 y, z), w)) steps1;
            val rotated_2 = Multiset.map (fn ((x,y,z),w) => ((x - x2, Multiset.subtract (fn p => fn q => p = q) y2 y, z), w)) steps2;
        in
            Multiset.eq compare_step rotated_1 rotated_2
        end
    and compare_path_direction (Path([])) _ = raise ZeroPath
      | compare_path_direction _ (Path([])) = raise ZeroPath
      | compare_path_direction (Path(steps1)) (Path(steps2)) = 
        let val (_, (fn1,fd1)) = List.hd steps1;
            val (_, (fn2,fd2)) = List.hd steps2;
            val (num1,denom1) = Multiset.fold (fn ((_,(n,d)), (hn, hd)) => (Multiset.intersect compare_distance_term n hn, Multiset.intersect compare_distance_term d hd)) (fn1,fd1) steps1;
            val (num2,denom2) = Multiset.fold (fn ((_,(n,d)), (hn, hd)) => (Multiset.intersect compare_distance_term n hn, Multiset.intersect compare_distance_term d hd)) (fn2,fd2) steps2;
            val scaled_1 = Multiset.map (fn (x,(n,d)) => (x,(Multiset.subtract compare_distance_term num1 n, Multiset.subtract compare_distance_term denom1 d))) steps1;
            val scaled_2 = Multiset.map (fn (x,(n,d)) => (x,(Multiset.subtract compare_distance_term num2 n, Multiset.subtract compare_distance_term denom2 d))) steps2;
        in
            Multiset.eq compare_step scaled_1 scaled_2
        end
    
    datatype tvl = YES | NO | MAYBE;
    
    fun step_to_direction ((0, [], DRBetween(x,y)), s) = (ref o SOME o Geometry.Direction) (x,y)
      | step_to_direction ((0, [], DRUnknown(x)), s) = x
      | step_to_direction ((0, (v::vs), d), s) = (ref o SOME o Geometry.RDir) (step_to_direction ((0,vs,d),s), v)
      | step_to_direction ((n, vs, d), s) = (ref o SOME o Geometry.Right) (step_to_direction ((n-1, vs, d), s));

    fun reverse_step step = turn_step 2 step;
    fun reverse_path (Path(x)) = Path(Multiset.map reverse_step x);

    (*complete*)
    fun same_step_direction ((x1,y1,DRUnknown z1), _) ((x2,y2,DRUnknown z2), _) =
            if z1 <> z2 then
                MAYBE
            else if x1 = x2 andalso Multiset.eq (fn x => fn y => x = y) y1 y2 then
                YES
            else
                NO
      | same_step_direction ((x1,y1,DRBetween (p1, q1)), _) ((x2,y2,DRBetween (p2, q2)), _) =
            if p1 = p2 andalso q1 = q2 then
                if x1 = x2 andalso Multiset.eq (fn x => fn y => x = y) y1 y2 then
                    YES
                else
                    NO
            else if p1 = q2 andalso q1 = p2 then
                if (x1 = (x2 + 2) mod 4) andalso Multiset.eq (fn x => fn y => x = y) y1 y2 then
                    YES
                else
                    NO
            else
                MAYBE
      | same_step_direction _ _ = MAYBE;
    
    fun opposite_step_direction step1 = same_step_direction (reverse_step step1);

    fun combine_path (Path(x)) (Path(y)) = 
        let fun check_cancel a b = (compare_step (reverse_step a) b);
        in 
            Path(Multiset.collide check_cancel x y)
        end;
    
    fun combine_paths [] = Path([])
      | combine_paths (x::xs) = combine_path x (combine_paths xs);
    
    fun multiply_distance (x1,y1) (x2,y2) = 
            let val (uncancelled_num, uncancelled_denom) = (Multiset.append x1 x2, Multiset.append y1 y2)
                val intersection = Multiset.intersect compare_distance_term uncancelled_num uncancelled_denom
            in
                (Multiset.subtract compare_distance_term intersection uncancelled_num, Multiset.subtract compare_distance_term intersection uncancelled_denom)
            end;
    fun divide_distance (x1,y1) (x2,y2) = 
            let val (uncancelled_num, uncancelled_denom) = (Multiset.append x1 y2, Multiset.append y1 x2)
                val intersection = Multiset.intersect compare_distance_term uncancelled_num uncancelled_denom
            in
                (Multiset.subtract compare_distance_term intersection uncancelled_num, Multiset.subtract compare_distance_term intersection uncancelled_denom)
            end;
    fun multiply_path (Path(x)) y = Path(Multiset.map (fn (d,s) => (d, multiply_distance s y)) x);
    fun divide_path (Path(x)) y = Path(Multiset.map (fn (d,s) => (d, divide_distance s y)) x);
    fun right_path (Path(x)) = Path(Multiset.map (fn step => turn_step 1 step) x);
    fun rdir_path (Path(x)) v = Path(Multiset.map (fn ((x,y,z),s) => ((x, cons v y, z), s)) x);
    
    fun distance_of (Path([])) = raise ZeroPath
      | distance_of (Path([(_,x)])) = x
      | distance_of (p as Path((_,(fn1,fd1))::xs)) = 
            let val (fnum, fdenom) = Multiset.fold (fn ((_,(n,d)), (hn, hd)) => (Multiset.intersect compare_distance_term n hn, Multiset.intersect compare_distance_term d hd)) (fn1,fd1) xs;
            in
                (SRTermPath (divide_path p (fnum, fdenom)) :: fnum, fdenom)
            end;
    
    fun singular_direction (Path((((a,b,c),s)::xs))) = 
            if Multiset.all (fn ((a1,b1,c1),_) => compare_step ((a1,b1,c1),s) ((a,b,c),s)) xs then
            SOME((a,b,c),s) else NONE
      | singular_direction (Path([])) = raise ZeroPath;
    
    fun point_to_path p = (case !p of
        NONE => (p, empty_path)
      | SOME(Geometry.PCopy(x)) => point_to_path(x)
      | SOME(Geometry.Move(x,y,z)) => let val (start_point, return_path) = point_to_path(x) in (start_point, combine_path (distance_direction_to_path(z,y)) return_path) end
    )
    and distance_direction_to_path (dist, dir) = (case !dir of
        NONE => Path(Multiset.map (fn x => ((0, Multiset.empty, DRUnknown dir), x)) (rep_distances dist))
      | SOME(Geometry.Direction(x,y)) =>
            let val path = path_between x y;
                val path_length = distance_of path;
            in
                case (singular_direction path) of
                NONE => combine_paths (List.map (fn x => multiply_path (divide_path path path_length) x) (rep_distances dist))
              | SOME(d,_) => combine_paths (List.map (fn x => Path([(d, x)]) ) (rep_distances dist))
            end
      | SOME(Geometry.Right(x)) => right_path (distance_direction_to_path(dist,x))
      | SOME(Geometry.RDir(x,v)) => rdir_path (distance_direction_to_path(dist,x)) v
      | SOME(Geometry.DCopy(x)) => distance_direction_to_path(dist,x)
    )
    and path_between a b = 
        let val (start_a, path_a) = point_to_path a;
            val (start_b, path_b) = point_to_path b;
        in
            if start_a = start_b then 
                combine_path (reverse_path path_a) path_b 
            else 
                combine_path (combine_path (reverse_path path_a) path_b) (
                    Path(Multiset.single (
                        (0, Multiset.empty, DRBetween (start_a,start_b)),
                        ([SRTermBetween (start_a,start_b)],[])
                    ))
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
      | SOME(Geometry.Divide(a,b)) => List.flatmap (fn x => List.map (fn y => divide_distance x y) (rep_distances b)) (rep_distances a)
      | SOME(Geometry.Value(s)) => [([SRTermValue s],[])]
      | SOME(Geometry.SCopy(x)) => rep_distances x
      | SOME(Geometry.Dot(x,y)) => [([SRTermDot(distance_direction_to_path (ref NONE, x), distance_direction_to_path (ref NONE, y))],[])]
    ;
    (*
    fun get_unknowns ((_,_,a),(n,d)) = get_dir_unknowns a @ Multiset.flatmap get_dis_unknowns n @ Multiset.flatmap get_dis_unknowns d
    and get_dir_unknowns 
    *)
    

    fun path_to_points (Path([])) start_point = start_point
      | path_to_points (Path(step::steps)) start_point =
            let val end_point = path_to_points (Path(steps)) start_point;
            in (ref o SOME o Geometry.Move) (end_point, step_to_direction step, step_to_distance step)
            end
    and step_to_distance (d,([],[])) = (ref o SOME o Geometry.Divide) ((fn x => (x,x)) (ref NONE)) (*(PolyML.print(d); raise PathError ("unexpected distance"))*)
      | step_to_distance (d,([SRTermBetween(x,y)],[])) = (ref o SOME o Geometry.Distance) (x,y)
      | step_to_distance (d,([SRTermUnknown(z)],[])) = z
      | step_to_distance (d,([SRTermValue(s)],[])) = (ref o SOME o Geometry.Value) s
      | step_to_distance (d,([SRTermPath(p)],[])) =
            let val start_point = ref NONE;
                val end_point = path_to_points p start_point;
            in
                (ref o SOME o Geometry.Distance) (start_point, end_point)
            end
      | step_to_distance (d,([SRTermDot(p1,p2)],[])) = 
            let val sp_1 = ref NONE;
                val direction_1 = (ref o SOME o Geometry.Direction) (sp_1, path_to_points p1 sp_1);
                val sp_2 = ref NONE;
                val direction_2 = (ref o SOME o Geometry.Direction) (sp_2, path_to_points p2 sp_2);
            in
                (ref o SOME o Geometry.Dot) (direction_1, direction_2)
            end
      | step_to_distance (d, (x::xs,[])) = (ref o SOME o Geometry.Times) (
            step_to_distance (d, ([x],[])),
            step_to_distance (d, (xs,[]))
        )
      | step_to_distance (d, (xs, ys)) = (ref o SOME o Geometry.Divide) (
            step_to_distance (d, (xs, [])),
            step_to_distance (d, (ys, []))
        );
    
    fun path_to_direction (Path(x)) = (case (singular_direction(Path(x))) of
            NONE => let val start = ref NONE; in (ref o SOME o Geometry.Direction) (start, path_to_points (Path(x)) start) end
          | SOME(step) => step_to_direction step
    );

    fun is_step_free ((0,[],DRBetween(x1,y1)),([SRTermBetween(x2,y2)],[])) = 
            if (x1 = x2 andalso y1 = y2) orelse (x1 = y2 andalso x2 = y1) then
                SOME(x1,y1)
            else
                NONE
      | is_step_free  _ = NONE;


    (*same, opposite, perpendicular/different, anything*)
    fun sort_steps_by_direction step [] = ([],[],[],[])
      | sort_steps_by_direction step (x::xs) = 
            let val (a,b,c,d) = sort_steps_by_direction step xs in case (same_step_direction step x, opposite_step_direction step x) of
                (YES, NO) => (x::a,b,c,d)
              | (NO, YES) => (a,x::b,c,d)
              | (NO, NO) => (a,b,x::c,d)
              | (MAYBE, MAYBE) => (a,b,c,x::d)
              | (YES, YES) => raise (PathError "step is opposite to itself")
            end;


    exception Proven of Geometry.pos_neg_constraint list list;
    exception Refuted;


    fun get_circle_constraints (p as Path(xs)) = 
        let val _ = if p = empty_path then raise Proven [[]] else ();
            val _ = if is_some (singular_direction p) then raise Refuted else ();
            fun try_set_point point new_value = if Geometry.point_contains_check point new_value then
                    ()
                else
                    (
                        PolyML.print ("Set >> ", Geometry.PC(point, new_value)); 
                        Geometry.af (); 
                        point := (SOME o Geometry.PCopy) (new_value);
                        raise Proven [[]]
                    )
            fun set_step_if_free (((0,[],DRBetween(x1,y1)),([SRTermBetween(x2,y2)],[])), other_steps) = 
                if (x1 = x2 andalso y1 = y2) orelse (x1 = y2 andalso x2 = y1) then
                    try_set_point x1 (path_to_points (Path(other_steps)) y1)
                else
                    ()
              | set_step_if_free  _ = ();
            val _ = Multiset.pick_map set_step_if_free xs;
            val start = ref NONE;
        in
            [[Geometry.X(Geometry.PC(start, path_to_points (Path(xs)) start))]] 
        end handle (Proven x) => x | Refuted => [];
    
    fun get_distance_constraints (path_1, path_2) start = if compare_path_distance (path_1) (path_2) then [[]] else
        let val distance_2 = distance_of path_2;
            val unitpath = divide_path path_1 distance_2;
        in
            case unitpath of
                (Path([])) => raise ZeroPath
              | (p as Path([(dir,(n,d))])) => 
                    if Multiset.all (fn x => case x of (SRTermValue x) => true | _ => false) n andalso Multiset.all (fn x => case x of (SRTermValue x) => true | _ => false) d then
                        raise Refuted
                    else
              
                (
                    case Multiset.pick_option (fn x => case x of (SRTermUnknown s) => SOME(s) | _ => NONE) n of
                        (SOME(s),ss) => 
                            let val new_step = ((0,[],DRUnknown (ref NONE)),(d,ss));
                                val new_dist = step_to_distance new_step;
                            in if Geometry.distance_contains_check s new_dist then 
                                let val dist = ref NONE in [[Geometry.X(Geometry.SC(dist, step_to_distance(dir, ((SRTermUnknown dist)::n, d))))]] end
                            else
                                (PolyML.print (Geometry.SC(s, new_dist)); Geometry.af (); s := (SOME o Geometry.SCopy) new_dist; [[]])
                            end
                      | (NONE,_) => 
                    case Multiset.pick_option (fn x => case x of (SRTermUnknown s) => SOME(s) | _ => NONE) d of
                        (SOME(s),ss) =>
                            let val new_step = ((0,[],DRUnknown (ref NONE)),(n,ss));
                                val new_dist = step_to_distance new_step;
                                val _ = PolyML.print ("new_dist >> ", Geometry.SC(s, new_dist));
                            in if Geometry.distance_contains_check s new_dist then 
                                let val dist = ref NONE in [[Geometry.X(Geometry.SC(dist, step_to_distance(dir, ((SRTermUnknown dist)::n, d))))]] end
                            else
                                (PolyML.print (Geometry.SC(s, new_dist)); Geometry.af (); s := (SOME o Geometry.SCopy) new_dist; [[]])
                            end
                      | (NONE,_) =>
                    let val dist = ref NONE in [[Geometry.X(Geometry.SC(dist, step_to_distance(dir, ((SRTermUnknown dist)::n, d))))]] end
                )
              | (p) => let val dist = ref NONE; val dir = (0, [], DRUnknown(ref NONE)); in [[Geometry.X(Geometry.SC(dist, step_to_distance(dir, ([SRTermPath p],[]))))]] end
        end handle (Proven x) => x | Refuted => [];

    fun get_direction_constraints (Path(l1), Path(l2)) = if compare_path_direction (Path(l1)) (Path(l2)) then [[]] else case (singular_direction(Path l1), singular_direction(Path l2)) of
        (SOME((a,b,DRUnknown(x)),s), _) =>
            let val poss_x = path_to_direction (Path(l2)) 
            in 
                if Geometry.direction_contains_check x poss_x then 
                    [[Geometry.X(Geometry.DC(x, poss_x))]] 
                else 
                    (Geometry.af (); x := (SOME o Geometry.DCopy) poss_x; [[]]) 
            end
      | (_, SOME((a,b,DRUnknown(x)),s)) =>
            let val poss_x = path_to_direction (Path(l1)) 
            in 
                if Geometry.direction_contains_check x poss_x then 
                    [[Geometry.X(Geometry.DC(x, poss_x))]] 
                else 
                    (Geometry.af (); x := (SOME o Geometry.DCopy) poss_x; [[]]) 
            end
      | (SOME((a,b,DRBetween(p1,p2)),s), _) =>
            let val poss_x = path_to_points (Path(l2)) p1
            in 
                if Geometry.point_contains_check p2 poss_x then 
                    [[Geometry.X(Geometry.PC(p2, poss_x))]] 
                else 
                    (Geometry.af (); p2 := (SOME o Geometry.PCopy) poss_x; [[]]) 
            end
      | (_, SOME((a,b,DRBetween(p1,p2)),s)) =>
            let val poss_x = path_to_points (Path(l1)) p1
            in 
                if Geometry.point_contains_check p2 poss_x then 
                    [[Geometry.X(Geometry.PC(p2, poss_x))]] 
                else 
                    (Geometry.af (); p2 := (SOME o Geometry.PCopy) poss_x; [[]]) 
            end
      | (NONE, NONE) =>
            [[Geometry.X(Geometry.DC(path_to_direction (Path(l1)) , path_to_direction (Path(l2)) ))]];
end