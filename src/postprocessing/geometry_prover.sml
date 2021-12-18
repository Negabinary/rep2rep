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
        in
            if changed then resolve_cdc next_state else next_state
        end;
    
    fun can_build construction = 
        let val state = resolve_cdc (state_from_construction construction);
        in
            SOME(#root state, #constraints state)
        end
        handle
            Falsifiable => NONE;
end