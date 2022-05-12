import "postprocessing.path";


signature GEOMETRY_PROVER =
sig
    datatype 'a answer = YES | NO | MAYBE of 'a;

    datatype proof_answer = Proven of Geometry.construction 
                          | Refuted 
                          | Possible of Geometry.construction * Geometry.pos_neg_constraint list list list 
                          | Probable of Geometry.construction * Geometry.pos_neg_constraint list list list 
                          | Timeout;

    val print_proof_answer : proof_answer -> string;

    val attempt_proof : (proof_answer -> unit) -> Geometry.construction -> proof_answer;
end

structure GeometryProver : GEOMETRY_PROVER = 
struct
    open Geometry;

    datatype 'a answer = YES | NO | MAYBE of 'a;

    val debug = false;
    fun debug_print x = if debug then PolyML.print x else x;
    fun debug_print_lazy f = if debug then PolyML.print (f ()) else ();

    datatype proof_answer = Proven of Geometry.construction 
                          | Refuted 
                          | Possible of Geometry.construction * Geometry.pos_neg_constraint list list list 
                          | Probable of Geometry.construction * Geometry.pos_neg_constraint list list list 
                          | Timeout;
    
    exception DisjunctionException;
    exception RefutationException;
    fun un_cdc [] = (raise RefutationException)
      | un_cdc [[]] = NONE 
      | un_cdc [[X(x)]] = SOME (x) 
      | un_cdc _ = raise DisjunctionException;
    
    val f = Geometry.create_map ();
    fun check_numerically ([],[]) = true
              | check_numerically ([],y::ys) = if Geometry.check_constraint f y then false else check_numerically ([],ys)
              | check_numerically (x::xs,ys) = if Geometry.check_constraint f x then check_numerically (xs, ys) else false;
    fun tape [] = ([],[])
      | tape (Y(x)::xs) = let val (a,b) = tape xs in (x::a,b) end
      | tape (N(x)::xs) = let val (a,b) = tape xs in (a,x::b) end
      | tape (X(x)::xs) = let val (a,b) = tape xs in (x::a,b) end;
    fun check_numerically_dc [] = false
        | check_numerically_dc (x::xs) = if check_numerically (tape x) then true else check_numerically_dc xs;

    fun attempt_proof debug_output construction =
        let val _ = Path.reset_time ();
            val (pos_constraints, neg_constraints) = get_constraints construction;
            fun until (c:'a -> bool) (f:'a -> 'a) (v:'a) : 'a = if c v then v else until c f (f v);
            fun use_pos_con (PC(p1,p2)) = (debug_print (PC(p1,p2)); un_cdc (Path.get_circle_constraints (Path.path_between p1 p2)))
              | use_pos_con (DC(d1,d2)) = 
                    let val dist = ref NONE;
                    in
                        un_cdc (Path.get_direction_constraints (
                            Path.distance_direction_to_path (dist, d1),
                            Path.distance_direction_to_path (dist, d2)
                        ))
                    end
              | use_pos_con (SC(s1, s2)) =
                    let val dir = ref NONE;
                    in
                        un_cdc (Path.get_distance_constraints (
                            Path.distance_direction_to_path (s1, dir),
                            Path.distance_direction_to_path (s2, dir)
                        ) (ref NONE))
                    end
              | use_pos_con (rc) = 
                    if Path.does_hold rc then
                        NONE
                    else if Path.does_not_hold rc then
                        raise RefutationException
                    else
                        SOME(rc)
            fun shorten_point point = 
                let val (start, path) = Path.point_to_path point in 
                if is_some (!point) then
                    (point := (SOME o PCopy) (Path.path_to_points path start); point)
                else
                    point
                end; (*ZeroPath?*)
            fun print_con x = (debug_print construction; x);
            fun shorten x = (Geometry.map_points (shorten_point, fn x => x) construction; x)
            fun iter pos_c = (assignment_flag := false; (List.mapPartial (shorten o print_con o use_pos_con) pos_c));
            val stop_count = ref 0;
            fun stopping _ = (stop_count := !stop_count + 1; 
                    (!stop_count > 2 andalso !assignment_flag = false) orelse !stop_count > 50
                )
            val remaining_pos = (until stopping iter (pos_constraints) handle Path.ZeroPath => raise RefutationException);
            val _ = if List.exists Path.does_hold neg_constraints then raise RefutationException else ();
            val remaining_neg = List.filter (not o Path.does_not_hold) neg_constraints;
            val result = 
                if (remaining_pos, remaining_neg) = ([],[]) then
                    Proven(construction)
                else if check_numerically (remaining_pos, remaining_neg) then
                    Probable(construction, List.map (fn x => [[Geometry.X x]]) remaining_pos @ List.map (fn x => [[Geometry.N x]]) remaining_neg)
                else
                    Possible(construction, List.map (fn x => [[Geometry.X x]]) remaining_pos @ List.map (fn x => [[Geometry.N x]]) remaining_neg)
        in
            (debug_output result; result)
        end handle RefutationException => Refuted | Path.Timeout => Timeout;


    fun print_proof_answer Refuted = "REFUTED\n"
      | print_proof_answer Timeout = "TIMEOUT\n"
      | print_proof_answer (Proven c) = "PROVEN!!!\n" ^ PolyML.makestring c ^ "\n"
      | print_proof_answer (Probable (c,d)) = "PROBABLE\n" ^ PolyML.makestring c ^ "\n" ^ (String.concat (List.map (fn x => PolyML.makestring x ^ "\n") d)) ^ "\n"
      | print_proof_answer (Possible (c,d)) = "POSSIBLE\n" ^ PolyML.makestring c ^ "\n" ^ (String.concat (List.map (fn x => PolyML.makestring x ^ " : " ^ (if check_numerically_dc x then "likely" else "unknown") ^ "\n") d)) ^ "\n";

end