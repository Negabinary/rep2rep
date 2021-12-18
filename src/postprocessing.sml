import "util.dictionary";
import "postprocessing.instantiation";


signature POSTPROCESING = 
sig 
    val postprocess : State.T Seq.seq -> State.T Seq.seq;
    val postprocess_state : State.T -> State.T Seq.seq;
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

    fun parse_relations (relations : Relation.relationship list) : ((string * CSpace.token) list) * ((CSpace.token * CSpace.token) list) * ((CSpace.token * CSpace.token) list) = 
        let val identifications = StringDict.empty ();
            fun add_identification name kind value = 
                let val (prev_kind, _) = StringDict.update identifications name (fn (k,z) => (k, value :: z));
                    val _ = if kind <> prev_kind then raise PostProcessingException "Trying to resolve tokens of different type" else ();
                in ()
                end
                handle
                    StringDict.KeyError => StringDict.insert identifications (name, (kind, [value]));
            fun iteration (relation,hints) = 
                case relation of
                    ([x],[y],"hint") => (x,y) :: hints
                  | ([x],[y],"length") => (add_identification (variable_name_of x) "length" y; hints)
                  | ([x],[y],"area") => (add_identification (variable_name_of x) "area" y; hints)
                  | ([x],[y],"angle") => (add_identification (variable_name_of x) "angle" y; hints)
                  | ([],[y],"unitlength") => (add_identification "1" "length" y; hints)
                  | (_,_,r) => raise PostProcessingException ("Unexpected relation '" ^ r ^ "'' in structure transfer result");
            val hints = List.foldr iteration [] relations;
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
        in
            (keep_tokens, replacements, hints)
        end;

    fun postprocess_state state = 
        let val _ = PolyML.print_depth 100;
            val _ = PolyML.line_length 1000000;
            val result_composition : Composition.composition = State.patternCompOf state
            val result_construction : Construction.construction = 
                case Composition.resultingConstructions result_composition of 
                    [x] => x 
                    | _ => raise PostProcessingException "Multiple constructions in structure transfer result";
            val (keep_tokens, replacements, hints) = parse_relations (State.goalsOf state);
            val instantiated = Instantiation.instantiate result_construction keep_tokens replacements;
            fun prove_instance instance = 
                let val (pos_constraints, neg_constraints) = Geometry.get_constraints instance;
                    val printer_config = (ref [], ref [], ref [], ref 0)
                    (*val _ = PolyML.print (List.map (fn z => Geometry.print_constraint z printer_config) pos_constraints);
                    val _ = PolyML.print instance;
                    val _ = PolyML.print "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv";*)
                    val left_constraints = List.map (fn x => (Geometry.use_positive_constraint x)) pos_constraints;
                    (*val _ = PolyML.print pos_constraints;*)
                    val _ = PolyML.print (Geometry.print_construction instance printer_config);
                    val _ = PolyML.print left_constraints;
                    (*val _ = PolyML.print (List.map (fn z => Geometry.print_constraint z printer_config) pos_constraints);*)
                    val refuted = List.exists Geometry.holds neg_constraints orelse List.exists (fn x => x = []) left_constraints;
                    (*val _ = PolyML.print instance;*)
                    val _ = if refuted then (PolyML.print "REFUTED"; ()) else (PolyML.print "POSSIBLE!!!!"; ());
                    val _ = PolyML.print "----------------------------------------------------------------";
                in
                    ()
                end;
            val _ = Seq.chop 100 (Seq.map (fn x => (prove_instance x)) instantiated);
            val _ = PolyML.print "================================================================";
            val points_map = "";
        in Seq.single state
        end;

    fun postprocess states = Seq.flat (Seq.map postprocess_state (Seq.take 2 states));

end