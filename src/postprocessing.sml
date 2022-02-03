import "util.dictionary";
import "postprocessing.instantiation";
import "postprocessing.geometry_prover";


signature POSTPROCESING = 
sig 
    val postprocess : State.T Seq.seq -> int -> int -> unit;
    (*val postprocess_state : int -> State.T -> unit;
    val generate_isomorphic : int -> Construction.construction -> Geometry.construction Seq.seq;*)
    val is_fully_transfered : State.T -> bool;
    val get_diagrams : State.T -> GeometryProver.proof_answer Seq.seq;
    val test : unit -> unit;
end

structure Postprocessing : POSTPROCESING = 
struct
    exception PostProcessingException of string;
    exception UnresolvableGeometryTypes;

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
                    val _ = if kind <> prev_kind then raise PostProcessingException "Trying to resolve tokens of different type" else ();
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

    fun prove_instance instance = 
        let val _ = PolyML.print instance;
            val _ = Path.reset_time ()
            val _ = case GeometryProver.can_build instance of
                NONE => (PolyML.print "REFUTED"; ())
                | SOME(x,[]) => (PolyML.print x; PolyML.print "PROVEN!!!!"; ())
                | SOME(x,c) => (PolyML.print x; PolyML.print c; PolyML.print "POSSIBLE"; ())
            val _ = PolyML.print "----------------------------------------------------------------";
        in
            ()
        end
        handle Path.Timeout => (PolyML.print "TIMEOUT"; PolyML.print "----------------------------------------------------------------"; ());

    fun postprocess_state lim2 state = 
        let (*val _ = PolyML.print state;*)
            val result_construction : Construction.construction = 
                case Composition.resultingConstructions (State.patternCompOf state) of 
                    [x] => x 
                    | _ => raise PostProcessingException "Multiple constructions in structure transfer result";
            val (keep_tokens, replacements, hints, fully_transfered) = parse_relations (State.goalsOf state);
            val _ = PolyML.print fully_transfered;
            val _ = if not fully_transfered then raise NotFullyTransfered else ();
            val instantiated = Instantiation.instantiate keep_tokens replacements result_construction;
            val _ = (Seq.chop lim2 (Seq.map (fn x => (prove_instance x)) instantiated) ; ());
            val _ = (PolyML.print "================================================================"; ());
            val points_map = "";
        in ()
        end handle NotFullyTransfered => ();

    fun postprocess states limit lim2 = (PolyML.print (Seq.chop limit (Seq.map (postprocess_state lim2) states)); ());

    fun is_fully_transfered state = #4 (parse_relations (State.goalsOf state));

    fun get_diagrams state = 
        let val result_construction : Construction.construction = 
                case Composition.resultingConstructions (State.patternCompOf state) of 
                    [x] => x 
                    | _ => raise PostProcessingException "Multiple constructions in structure transfer result";
            val (keep_tokens, replacements, hints, fully_transfered) = parse_relations (State.goalsOf state);
            val _ = if not fully_transfered then raise NotFullyTransfered else ();
            val instantiated = Instantiation.instantiate keep_tokens replacements result_construction;
            val proof_answers = Seq.map GeometryProver.attempt_proof instantiated;
        in proof_answers
        end
    
    (*TODO!! FIX INSTANTIATION BREAKING IDENTIFICATION!!!*)

    fun test () = 
    let val p1 = ref NONE;
        val p2 = ref NONE;
        val p4 = ref NONE;
        val p10 = ref NONE;
    in
        prove_instance (
            Geometry.RectCon (
                Geometry.ResolveRect (
                    Geometry.Pythag (
                        Geometry.ResolveLine (
                            Geometry.Cosine(
                                Geometry.RootLine(
                                    p1, p2
                                ),
                                Geometry.RootAngle(
                                    p2, p1, p4
                                )
                            ),
                            Geometry.Cosine(
                                Geometry.RootLine(
                                    p1,p2
                                ),
                                Geometry.RootAngle(
                                    p2, p1, p4
                                )
                            )
                        ),
                        Geometry.ResolveLine (
                            Geometry.Sine(
                                Geometry.RootLine(
                                    p1, p2
                                ),
                                Geometry.RootAngle(
                                    p2, p1, p4
                                )
                            ),
                            Geometry.Sine(
                                Geometry.RootLine(
                                    p1,p2
                                ),
                                Geometry.RootAngle(
                                    p2, p1, p4
                                )
                            )
                        )
                    ),
                    Geometry.MKRect(
                        Geometry.RootLine(p1,p2),
                        Geometry.RootLine(p1,p10)
                    )
                )
            )
        )
    end


end