import "util.dictionary";
import "postprocessing.instantiation";
import "postprocessing.geometry_prover";


signature POSTPROCESING = 
sig 
    val postprocess : State.T Seq.seq -> int -> int -> unit;
    val postprocess_state : int -> State.T -> unit;
end

structure Postprocessing : POSTPROCESING = 
struct
    exception PostProcessingException of string;
    exception UnresolvableGeometryTypes;

    fun variable_name_of token = Type.nameOfType (CSpace.typeOfToken token);

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
            val fully_transfered = List.all (fn x => String.size x = 1) variables andalso not repeq
        in
            (keep_tokens, replacements, hints, fully_transfered)
        end;

    val _ = PolyML.print_depth 100;
    val _ = PolyML.line_length 1000000;

    exception NotFullyTransfered;

    fun postprocess_state lim2 state = 
        let val result_construction : Construction.construction = 
                case Composition.resultingConstructions (State.patternCompOf state) of 
                    [x] => x 
                    | _ => raise PostProcessingException "Multiple constructions in structure transfer result";
            val (keep_tokens, replacements, hints, fully_transfered) = parse_relations (State.goalsOf state);
            val _ = PolyML.print fully_transfered;
            val _ = if not fully_transfered then raise NotFullyTransfered else ();
            val instantiated = Instantiation.instantiate result_construction keep_tokens replacements;
            val _ = PolyML.print "Made it here!";
            fun prove_instance instance = 
                let val _ = PolyML.print instance;
                    val printer_config = (ref [], ref [], ref [], ref 0)
                    val _ = PolyML.print instance;
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
            val _ = if fully_transfered then (Seq.chop lim2 (Seq.map (fn x => (prove_instance x)) instantiated) ; ()) else () ;
            val _ = if fully_transfered then (PolyML.print "================================================================"; ()) else ();
            val points_map = "";
        in ()
        end handle NotFullyTransfered => ();

    fun postprocess states limit lim2 = (PolyML.print (Seq.chop limit (Seq.map (postprocess_state lim2) states)); ());

end