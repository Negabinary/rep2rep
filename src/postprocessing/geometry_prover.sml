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
    

    fun use_positive_constraint (PC(p1, p2)) = if same_point (p1,p2) then [[]] else (case (!p1, !p2, point_contains_check p1 p2, point_contains_check p2 p1) of
            (SOME(PCopy(x)), _, _, _) =>
                use_positive_constraint (PC(x, p2))
        | (_, SOME(PCopy(x)), _, _) =>
                use_positive_constraint (PC(p1, x))
        | (NONE, _, false, _) =>
                (p1 := (SOME o PCopy) p2; [[]])
        | (_, NONE, _, false) =>
                (p2 := (SOME o PCopy) p1; [[]])
        | (NONE, NONE, true, true) => [[]] (*must be the same*)
        | (SOME(Move(b1,d1,s1)), SOME(Move(b2,d2,s2)), _, _) =>
                [
                    [Y(PC(b1,b2)), Y(DC(d1,d2)), Y(SC(s1, s2)), N(PC(b1,p2)), N(PC(b2,p1))],
                    [N(PC(b1,b2)), N(DC(d1,d2)), X(PC(p1, p2)), N(PC(b1,p2)), N(PC(b2,p1))],
                    [N(PC(b1,b2)), N(SC(s1,s2)), X(PC(p1, p2)), N(PC(b1,p2)), N(PC(b2,p1))]
                ]
        | (SOME(Move((b2),_,_)),NONE,_,_) => [[X(PC(p1, p2)), N(PC(b2,p2))]]
        | (NONE,SOME(Move((b1),_,_)),_,_) => [[X(PC(p1, p2)), N(PC(b1,p1))]])
    | use_positive_constraint (DC(d1,d2)) = (PolyML.print (DC(d1,d2)); PolyML.print (
        if same_direction(d1, d2) then [[]] else (case (!d1, !d2, (direction_contains_check d1 d2, direction_contains_check d2 d1)) of
            (SOME(DCopy(x)), _, _) =>
                use_positive_constraint (DC(x, d2))
        | (_, SOME(DCopy(x)), _) =>
                use_positive_constraint (DC(d1, x))
        | (NONE, _, (false, _)) =>
                (d1 := (SOME o DCopy) d2; [[]])
        | (_, NONE, (_, false)) => 
                (d2 := (SOME o DCopy) d1; [[]])
        | (SOME(Direction(x1,y1)), SOME(Direction(x2,y2)), _) => 
                let val poss_x1 = (ref o SOME o Move) (y1, (ref o SOME o Right o ref o SOME o Right) d2, ref NONE);
                    val poss_y1 = (ref o SOME o Move) (x1, d2, ref NONE);
                    val poss_x2 = (ref o SOME o Move) (y2, (ref o SOME o Right o ref o SOME o Right) d1, ref NONE);
                    val poss_y2 = (ref o SOME o Move) (x2, d1, ref NONE);
                in
                    if !y1 = NONE andalso not (point_contains_check y1 poss_y1) then
                        (y1 := !poss_y1; [[]])
                    else if !y2 = NONE andalso not (point_contains_check y2 poss_y2) then
                        (y2 := !poss_y2; [[]])
                    else if !x1 = NONE andalso not (point_contains_check x1 poss_x1) then
                        (x1 := !poss_x1; [[]])
                    else if !x2 = NONE andalso not (point_contains_check x2 poss_x2) then
                        (x2 := !poss_x2; [[]])
                    else 
                        [[X(DC(d1,d2))]]                
                end
        | (SOME(Direction(x,y)), _, _) => 
                let val poss_x = (ref o SOME o Move) (y, (ref o SOME o Right o ref o SOME o Right) d2, ref NONE);
                    val poss_y = (ref o SOME o Move) (x, d2, ref NONE);
                in
                    if !y = NONE andalso not (point_contains_check y poss_y) then
                        (y := !poss_y; [[]])
                    else if !x = NONE andalso not (point_contains_check x poss_x) then
                        (x := !poss_x; [[]])
                    else 
                        let val dist = ref NONE in Path.get_direction_constraints (Path.distance_direction_to_path (dist, d1), Path.distance_direction_to_path (dist, d2) ) end
                end
        | (_, SOME(Direction(x,y)), _) => 
                let val poss_x = (ref o SOME o Move) (y, (ref o SOME o Right o ref o SOME o Right) d1, ref NONE);
                    val poss_y = (ref o SOME o Move) (x, d1, ref NONE);
                in
                    if !y = NONE andalso not (point_contains_check y poss_y) then
                        (y := !poss_y; [[]])
                    else if !x = NONE andalso not (point_contains_check x poss_x) then
                        (x := !poss_x; [[]])
                    else 
                        let val dist = ref NONE in Path.get_direction_constraints (Path.distance_direction_to_path (dist, d1), Path.distance_direction_to_path (dist, d2) ) end
                end
        | _ => let val dist = ref NONE in Path.get_direction_constraints (Path.distance_direction_to_path (dist, d1), Path.distance_direction_to_path (dist, d2) ) end
        )))
    (*
    | use_positive_constraint (DC(d1,d2)) = (let val dist = ref NONE; in PolyML.print (Path.distance_direction_to_path (dist,d1), Path.distance_direction_to_path (dist,d2)) end; case (direction_to_intermediate (intermediate_to_direction (direction_to_intermediate d1 (0,[]))) (0,[]), direction_to_intermediate (intermediate_to_direction (direction_to_intermediate d2 (0,[]))) (0,[]), (direction_contains_check d1 d2, direction_contains_check d2 d1)) of
            (DIUnknown(x), y, (true, _)) => (x := (SOME o DCopy) (intermediate_to_direction y); [[]])
        | (x, DIUnknown(y), (_, true)) => (y := (SOME o DCopy) (intermediate_to_direction x); [[]])
        | (x,y,_) => [[X(DC(intermediate_to_direction x, intermediate_to_direction y))]])
    | use_positive_constraint (DC(d1, d2)) = 
        if same_direction(d1, d2) then [[]] else (case (!d1, !d2, (direction_contains_check d1 d2, direction_contains_check d2 d1)) of
            (SOME(DCopy(x)), _, _) =>
                use_positive_constraint (DC(x, d2))
        | (_, SOME(DCopy(x)), _) =>
                use_positive_constraint (DC(d1, x))
        | (NONE, _, (false, _)) =>
                (d1 := (SOME o DCopy) d2; [[]])
        | (_, NONE, (_, false)) => 
                (d2 := (SOME o DCopy) d1; [[]])
        | (SOME(Direction(p1,p2)), _, _) =>
                (case !p2 of
                    SOME(Move(x,y,z)) =>  if x = p1 then use_positive_constraint(DC(y,d2)) else [[X(DC(d1,d2))]]
                | _ => [[X(DC(d1,d2))]])
        | (_, SOME(Direction(p1,p2)), _) =>
                (case !p2 of
                    SOME(Move(x,y,z)) => if x = p1 then use_positive_constraint(DC(d1,y)) else [[X(DC(d1,d2))]]
                | _ => [[X(DC(d1,d2))]])
        | (SOME(RDir(b1,v1)),SOME(RDir(b2,v2)), _) =>
                if v1 = v2 then
                    use_positive_constraint (DC(b1, b2))
                else
                    [[N(DC(b1, b2)), X(DC(d1, d2))]]
        | (SOME(Right(b1)),SOME(Right(b2)), _) =>
                use_positive_constraint (DC(b1, b2))
        | _ =>
                [[X(DC(d1,d2))]])
    *)
    | use_positive_constraint (SC(s1,s2)) = if same_distance(s1, s2) then [[]] else (case (!s1, !s2, (distance_contains_check s1 s2, distance_contains_check s2 s1)) of
            (SOME(SCopy(x)), _, _) =>
                use_positive_constraint (SC(x, s2))
        | (_, SOME(SCopy(x)), _) =>
                use_positive_constraint (SC(s1, x))
        | (NONE, _, (false, _)) =>
                (s1 := (SOME o SCopy) s2; [[]])
        | (_, NONE, (_, false)) =>
                (s2 := (SOME o SCopy) s1; [[]])
        | (SOME(Distance(p1,p2)), _, _) =>
                (case !p2 of
                    SOME(Move(p1,y,z)) => use_positive_constraint(SC(z,s2))
                | _ => [[X(SC(s1,s2))]])
        | (_, SOME(Distance(p1,p2)), _) => 
                (case !p2 of
                    SOME(Move(p1,y,z)) => use_positive_constraint(SC(s1,z))
                | _ => [[X(SC(s1,s2))]])
        | (SOME(Value(x)), SOME(Value(y)), _) =>
                if x = y then
                    [[]]
                else
                    []
        | _ =>
                [[X(SC(s1,s2))]]);

    (*
    YES => means the conjunction is proven and equivalent to []
    MAYBE(x : c) => means the conjunction is true if the possibly simpler conjunction x is true
    NO => means the conjunction is falsifiable
    *)
    fun check_if_conjunction_proven falsifiers [] = YES
      | check_if_conjunction_proven falsifiers (x::xs) = 
            case (x, check_if_conjunction_proven falsifiers xs) of
                (Y(a),YES) => if holds a then YES else MAYBE([x])
              | (Y(a),MAYBE(cs)) => if holds a then MAYBE(cs) else MAYBE(x::cs)
              | (Y(a),NO) => NO
              | (X(a),YES) => MAYBE([x])
              | (X(a),MAYBE(cs)) => MAYBE(x::cs)
              | (X(a),NO) => NO
              | (N(a),YES) => if holds a then NO else MAYBE([x])
              | (N(a),MAYBE(cs)) => if holds a then NO else MAYBE(x::cs)
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
    
    (*
    YES => means that after resolution the disjunction is now proven
    MAYBE(c-d-c, falsifiables, unprovables, changed) => means that after resolution the disjunction looks like the c-d-c
    NO => means that a contradiction arose during resolution
    *)
    fun resolve_disjunction falsifiers [] = NO
      | resolve_disjunction falsifiers [x] = MAYBE(make_conjunction_true falsifiers x)
      | resolve_disjunction falsifiers xs = check_if_disjunction_proven falsifiers xs;
    
    exception Falsifiable;

    fun resolve_cdc st = 
        let val constraints = #constraints st;
            val _ = PolyML.print constraints;
            val _ = PolyML.print ">>>>>>>>>>";
            val falsifiers = #falsifiers st;
            val unknowables = #unknowables st;
            fun iter (disj,prev) = case (resolve_disjunction (#2 prev) disj, prev) of
                (NO, _) => raise Falsifiable
              | (YES, x) => x
              | (MAYBE(cs', fs', us', cd'),(cs, fs, us, cd)) => (cs'@cs, fs'@fs, us'@us, cd' orelse cd)
            val (new_constraints, new_falsifiers, new_unknowables, changed) = 
                    List.foldr iter ([], falsifiers, unknowables, false) constraints;
            val next_state = {
                constraints=new_constraints,
                falsifiers=new_falsifiers,
                unknowables=new_unknowables,
                root=(#root st)
            };
            (*val _ = PolyML.print(next_state);
            val _ = PolyML.print(">>>>")*)
            val _ = List.map (fn x => if holds x then raise Falsifiable else ()) new_falsifiers;
        in
            if changed then resolve_cdc next_state else next_state
        end;
    
    fun can_build construction = 
        let val state = resolve_cdc (state_from_construction construction);
        in
            SOME(#root state, (#constraints state) @ List.map (fn x => [[X(x)]]) (#unknowables state))
        end
        handle
            Falsifiable => NONE;

end