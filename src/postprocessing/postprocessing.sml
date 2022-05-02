import "util.dictionary";
import "postprocessing.instantiation";
import "postprocessing.geometry_prover";


signature POSTPROCESING = 
sig 
    (*val postprocess : State.T Seq.seq -> int -> int -> unit;
    val get_diagrams : State.T -> GeometryProver.proof_answer Seq.seq;
    val angel_5 : unit -> unit;
    *)

    type postprocessing_result;
    type constraints;

    val is_fully_transfered : State.T -> bool;
    val postprocess : int * int -> (GeometryProver.proof_answer -> unit) -> State.T -> postprocessing_result;
    val count_variants : State.T -> LargeInt.int;
    val postprocess_silent : int * int -> State.T -> postprocessing_result;

    val refuted_count : postprocessing_result -> int;
    val timeout_count : postprocessing_result -> int;
    val proven_results : postprocessing_result -> Geometry.construction list;
    val probable_results : postprocessing_result -> (Geometry.construction * constraints) list;
    val possible_results : postprocessing_result -> (Geometry.construction * constraints) list;

    exception PostProcessingException of string;
    exception UnresolvableGeometryTypes;

    val print_summary : postprocessing_result -> unit;
    val print_proven : postprocessing_result -> unit;
    val print_possible : postprocessing_result -> unit;
    val print_probable : postprocessing_result -> unit;
end

structure Postprocessing : POSTPROCESING = 
struct
    exception PostProcessingException of string;
    exception UnresolvableGeometryTypes;

    type postprocessing_result = GeometryProver.proof_answer list;
    type constraints = Geometry.pos_neg_constraint list list list;

    fun count p = List.foldr (fn (x,y) => if p x then y + 1 else y) 0;

    fun variable_name_of token = case Type.nameOfType (CSpace.typeOfToken token) of
        "ninety" => "9"
      | "one" => "1"
      | x => x;

    structure StringKeys = 
    struct
        type k = string;
        val compare = String.compare;
        fun fmt s = s;
    end
    structure StringDict = Dictionary(StringKeys)

    fun parse_relations (relations : Relation.relationship list) : ((string * CSpace.token) list) * ((CSpace.token * CSpace.token) list) * ((CSpace.token * CSpace.token) list) * bool = 
        let val identifications = StringDict.empty ();
            fun add_identification name kind value = 
                let val (prev_kind, _) = StringDict.update identifications name (fn (k,z) => (k, value :: z));
                    val _ = if kind <> prev_kind then (raise UnresolvableGeometryTypes) else ();
                in ()
                end
                handle
                    StringDict.KeyError => StringDict.insert identifications (name, (kind, [value]));
            fun iteration (relation,(hints, repeq)) = 
                case relation of
                    ([x],[y],"hint") => ((x,y) :: hints, repeq)
                  | ([x],[y],"length") => (add_identification (variable_name_of x) "length" y; (hints, repeq))
                  | ([x],[y],"area") => (add_identification (variable_name_of x) "area" y; (hints, repeq))
                  | ([x],[y],"angle") => (add_identification (variable_name_of x) "angle" y; (hints, repeq))
                  | ([],[y],"unitlength") => (add_identification "1" "length" y; (hints, repeq))
                  | ([],[y],"ninety") => (add_identification "9" "angle" y; (hints, repeq))
                  | (_,_,"repeq") => (hints, true)
                  | (_,_,r) => raise PostProcessingException ("Unexpected relation '" ^ r ^ "'' in structure transfer result");
            val (hints, repeq) = List.foldr iteration ([], false) relations;
            val variables = StringDict.keys identifications;
            val keep_tokens = List.map (fn x => (x, List.hd  (#2 (StringDict.get identifications x)))) variables;
            val replacements = 
                List.filter 
                    (fn (x,y) => (x <> y)) 
                    (List.flatmap 
                        (fn (x,y) => 
                            List.map 
                                (fn z => (z,y)) 
                                (#2(StringDict.get identifications x))
                        ) 
                        keep_tokens
                    );
            val fully_transfered = List.all (fn x => String.size x = 1 orelse x = "one") variables andalso not repeq
        in
            (keep_tokens, replacements, hints, fully_transfered)
        end;

    val _ = PolyML.print_depth 100;
    val _ = PolyML.line_length 1000000;

    exception NotFullyTransfered;

    fun is_fully_transfered state = #4 (parse_relations (State.goalsOf state));

    fun minlim_maxlim p 0 0 sequence = []
      | minlim_maxlim p 0 maxlim sequence = 
            (case Seq.pull sequence of
                NONE => []
              | SOME(x,xq) => if p x then [x] else let val xs = minlim_maxlim p 0 (maxlim - 1) xq; in x::xs end)
      | minlim_maxlim p minlim maxlim sequence = 
            (case Seq.pull sequence of
                NONE => []
              | SOME(x,xq) => let val xs = minlim_maxlim p (minlim-1) (if p x then 0 else maxlim) xq; in x::xs end);
    
    fun postprocess (lim1,lim2) output state = 
        let val result_construction =
                case Composition.resultingConstructions (State.patternCompOf state) of
                    [x] => x
                    | _ => raise PostProcessingException "Multiple constructions in structure transfer result";
            val (keep_tokens, replacements, hints, fully_transfered) = parse_relations (State.goalsOf state);
            val _ = if not fully_transfered then raise NotFullyTransfered else ();
            val instantiated = Instantiation.instantiate keep_tokens replacements result_construction
            val proof_answer_seq = Seq.map (GeometryProver.attempt_proof output) instantiated;
            val proof_answers = minlim_maxlim (fn x => case x of (GeometryProver.Proven x) => true | _ => false) lim1 lim2 proof_answer_seq;
        in
            proof_answers
        end
    fun count_variants state =
        let val result_construction = 
                case Composition.resultingConstructions (State.patternCompOf state) of
                    [x] => x
                    | _ => raise PostProcessingException "Multiple constructions in structure transfer result";
            val (keep_tokens, replacements, hints, fully_transfered) = parse_relations (State.goalsOf state);
            val _ = if not fully_transfered then raise NotFullyTransfered else ();
            val count = Instantiation.count_variants keep_tokens replacements result_construction;
        in
            count
        end;
    fun postprocess_silent limit = postprocess limit (fn x => ());
    fun refuted_count diagrams = count (fn x => x = GeometryProver.Refuted) diagrams;
    fun timeout_count diagrams = count (fn x => x = GeometryProver.Timeout) diagrams;
    fun proven_results diagrams = List.filterOption (List.map (fn x => case x of GeometryProver.Proven x => SOME x | _ => NONE) diagrams);
    fun probable_results diagrams = List.filterOption (List.map (fn x => case x of GeometryProver.Probable x => SOME x | _ => NONE) diagrams);
    fun possible_results diagrams = List.filterOption (List.map (fn x => case x of GeometryProver.Possible x => SOME x | _ => NONE) diagrams);
    fun print_summary diagrams =
        let val refuted = refuted_count diagrams;
            val timeout = timeout_count diagrams;
            val proven = proven_results diagrams;
            val probable = probable_results diagrams;
            val possible = possible_results diagrams;
            val _ = print (
                "Refuted: " ^ Int.toString refuted 
                ^ "; Timeout: " ^ Int.toString timeout
                ^ "; Proven: " ^ Int.toString (List.length proven)
                ^ "; Probable: " ^ Int.toString (List.length probable)
                ^ "; Possible: " ^ Int.toString (List.length possible)
                ^ "\n"
            )
        in
            ()
        end
    fun print_proven diagrams = (List.map (fn x => (print o GeometryProver.print_proof_answer) (GeometryProver.Proven x)) (proven_results diagrams); ());
    fun print_probable diagrams = (List.map (fn x => (print o GeometryProver.print_proof_answer) (GeometryProver.Probable x)) (probable_results diagrams); ());
    fun print_possible diagrams = (List.map (fn x => (print o GeometryProver.print_proof_answer) (GeometryProver.Possible x)) (possible_results diagrams); ());
end