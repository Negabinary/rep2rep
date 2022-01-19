import "postprocessing.constraint";


signature GEOMETRY_PROVER =
sig
    datatype 'a answer = YES | NO | MAYBE of 'a;

    val can_build : Geometry.construction -> (Geometry.construction * Geometry.pos_neg_constraint list list list) option;
end

structure GeometryProver : GEOMETRY_PROVER = 
struct
    open Geometry;

    datatype 'a answer = YES | NO | MAYBE of 'a;

    val debug = false;

    type state = {
        falsifiers : constraint list,
        unknowables : constraint list,
        constraints : pos_neg_constraint list list list, (* conjuction - disjunction - conjunction *)
        root : construction
    };

    fun state_from_construction root = 
        let val (pos_constraints, neg_constraints) = get_constraints root;
        in
            {
                falsifiers = neg_constraints,
                unknowables = [],
                constraints = List.map (fn x => [[Y(x)]]) pos_constraints,
                root = root
            }
        end;
    

    fun use_positive_constraint (PC(p1, p2)) = 
        (let val _ = (if debug then PolyML.print else (fn x => x)) "Point constraint";
            val _ = (if debug then PolyML.print else (fn x => x)) (PC(p1, p2));
            val start = ref NONE;
            val circle = Path.path_between p1 p2;
            val _ = (if debug then PolyML.print else (fn x => x)) "debug";
            val _ = (if debug then PolyML.print else (fn x => x)) (PC(start, Path.path_to_points circle start));
            val constraints = (if debug then PolyML.print else (fn x => x)) (Path.get_circle_constraints circle);
        in 
            constraints
        end handle Path.ZeroPath => (if debug then PolyML.print "ZeroPath1" else ""; []))
    | use_positive_constraint (DC(d1, d2)) = 
        (let val _ = (if debug then PolyML.print else (fn x => x)) "Direction constraint";
            val _ = (if debug then PolyML.print else (fn x => x)) (DC(d1, d2));
            val dist = ref NONE; val start = ref NONE;
            val path_1 = Path.distance_direction_to_path (dist, d1);
            val _ = (if debug then PolyML.print else (fn x => x)) (PC(start, Path.path_to_points path_1 start));
            val _ = (if debug then PolyML.print else (fn x => x)) (DC(d1, d2));
            val path_2 = Path.distance_direction_to_path (dist, d2);
            val _ = (if debug then PolyML.print else (fn x => x)) (PC(start, Path.path_to_points path_2 start));
            val _ = (if debug then PolyML.print else (fn x => x)) (DC(d1, d2));
            val constraints = (if debug then PolyML.print else (fn x => x)) (Path.get_direction_constraints (path_1, path_2));
        in 
            constraints
        end handle Path.ZeroPath => (if debug then PolyML.print "ZeroPath2" else ""; []))
    | use_positive_constraint (SC(s1,s2)) = 
        (let val _ = (if debug then PolyML.print else (fn x => x)) "Distance constraint";
            val _ = (if debug then PolyML.print else (fn x => x)) (SC(s1, s2));
            val dir = ref NONE; val start = ref NONE;
            val path_1 = Path.distance_direction_to_path (s1, dir);
            val _ = (if debug then PolyML.print else (fn x => x)) (PC(start, Path.path_to_points path_1 start));
            val path_2 = Path.distance_direction_to_path (s2, dir);
            val _ = (if debug then PolyML.print else (fn x => x)) (PC(start, Path.path_to_points path_2 start));
            val constraints = (if debug then PolyML.print else (fn x => x))(Path.get_distance_constraints (path_1, path_2) (ref NONE));
        in 
            constraints
        end handle Path.ZeroPath => (if debug then PolyML.print "ZeroPath3" else ""; []));
    (*
    YES => means the conjunction is proven and equivalent to []
    MAYBE(x : c) => means the conjunction is true if the possibly simpler conjunction x is true
    NO => means the conjunction is falsifiable
    *)
    fun check_if_conjunction_proven falsifiers [] = YES
      | check_if_conjunction_proven falsifiers (x::xs) = 
            case (x, check_if_conjunction_proven falsifiers xs) of
                (Y(a),YES) => if Path.does_hold a then YES else MAYBE([x])
              | (Y(a),MAYBE(cs)) => if Path.does_hold a then MAYBE(cs) else MAYBE(x::cs)
              | (Y(a),NO) => NO
              | (X(a),YES) => MAYBE([x])
              | (X(a),MAYBE(cs)) => MAYBE(x::cs)
              | (X(a),NO) => NO
              | (N(a),YES) => if Path.does_hold a then NO else MAYBE([x])
              | (N(a),MAYBE(cs)) => if Path.does_hold a then NO else MAYBE(x::cs)
              | (N(a),NO) => NO;

    (*
    makes a (c-d-c, new falsifiers, and new unprovables, true) from a c and changes references
    *)
    fun make_conjunction_true falsifiers [] = ([],[],[],true)
      | make_conjunction_true falsifiers (x::xs) =
            case (x, make_conjunction_true falsifiers xs) of
                (Y(a),(p,q,r,_)) => (use_positive_constraint a::p,q,r,true)
              | (X(a),(p,q,r,_)) => (p,q,a::r,true)
              | (N(a),(p,q,r,_)) => (p,a::q,r,true);
    
    (*
    YES => means the disjunction is proven and contains something equivalent to [[]]
    MAYBE(x) => 
    NO => means the disjunction is falsifiable
    *)
    fun check_if_disjunction_proven falsifiers disjunction =
        let val conjunction_statuses = List.map (check_if_conjunction_proven falsifiers) disjunction;
        in
            if List.exists (fn x => x = YES) conjunction_statuses then
                YES
            else if List.all (fn x => x = NO) conjunction_statuses then
                NO
            else
                MAYBE(
                    [List.mapPartial 
                        (fn x => case x of YES => NONE | NO => NONE | MAYBE(x) => SOME(x)) 
                        conjunction_statuses],
                    [], [],
                    if List.exists (fn x => x = NO) conjunction_statuses then true else false
                )
        end;

    exception Falsifiable;
    
    (*
    YES => means that after resolution the disjunction is now proven
    MAYBE(c-d-c, falsifiables, unprovables, changed) => means that after resolution the disjunction looks like the c-d-c
    NO => means that a contradiction arose during resolution
    *)
    fun resolve_disjunction falsifiers [] = raise Falsifiable
      | resolve_disjunction falsifiers [x] = MAYBE(make_conjunction_true falsifiers x)
      | resolve_disjunction falsifiers xs = check_if_disjunction_proven falsifiers xs;

    fun resolve_cdc st n = 
        let val constraints = #constraints st;
            val falsifiers = #falsifiers st;
            val unknowables = #unknowables st;
            fun shorten_point point = 
                let val (start, path) = Path.point_to_path point in 
                if is_some (!point) then
                    (point := (SOME o PCopy) (Path.path_to_points path start); point)
                else
                    point
                end handle ZeroPath => raise Falsifiable;
            fun iter (disj,prev) = case (Geometry.map_points (shorten_point, fn x => x) (#root st); (resolve_disjunction (#2 prev) disj, prev)) of
                (NO, _) => raise Falsifiable
              | (YES, x) => x
              | (MAYBE(cs', fs', us', cd'),(cs, fs, us, cd)) => (cs'@cs, fs'@fs, us'@us, cd' orelse cd)
            val (new_constraints, new_falsifiers, new_unknowables, changed) = 
                    List.foldr iter ([], falsifiers, unknowables, false) constraints;
            val _ = (Geometry.map_points (shorten_point, fn x => x) (#root st)); 
            val (changed, new_constraints_2, new_unknowables_2) = if not changed andalso !assignment_flag then 
                    (assignment_flag := false; (true, List.map (fn x => [[Y(x)]]) unknowables @ new_constraints, []))
                else 
                    (changed, new_constraints, new_unknowables);
            val next_state = {
                constraints=new_constraints_2,
                falsifiers=new_falsifiers,
                unknowables=new_unknowables_2,
                root=(#root st)
            };
            val _ = List.map (fn x => if Path.does_hold x then raise Falsifiable else ()) new_falsifiers;
        in
            if changed then resolve_cdc next_state (n - 1) else next_state
        end handle Path.ZeroPath => raise Falsifiable;
    
    fun can_build construction = 
        let val state = resolve_cdc (state_from_construction construction) 20;
        in
            SOME(#root state, (#constraints state) @ List.map (fn x => [[X(x)]]) (#unknowables state) @ List.map (fn x => [[N(x)]]) (List.filter (fn x => not (Path.does_not_hold x)) (#falsifiers state)))
        end
        handle
            Falsifiable => NONE;

end