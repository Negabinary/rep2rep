import "util.dictionary";
import "postprocessing.instantiation";

(*
signature POSTPROCESSING_STATE =
sig
    exception PostProcessingException of string;
    type T;
    val from_state : State.T -> T;
    val convert_construction : Type.typeSystem -> Construction.construction -> Geometry.construction * Geometry.construction list * Geometry.equivalence list * Geometry.relation list;
end


structure PostprocessingState : POSTPROCESSING_STATE =
struct
    exception PostProcessingException of string;

    type T = {
        top : Geometry.construction,
        geometryGoals : Geometry.relation list,
        equivalenceGoals : Geometry.equivalence list,
        constructions : Geometry.construction list
    };

    fun convert_construction type_system c = case c of
        Construction.TCPair({token=token,constructor=constructor}, cs) =>
            let val (root, gcs, rs, es) = Geometry.make_unit_construction (CSpace.nameOfConstructor(constructor));
                val children_conversions = List.map (convert_construction type_system) cs;
                val children_equivalences = List.funZip Geometry.mk_equivalence gcs (List.map #1 children_conversions);
            in
                (
                    root, 
                    root :: List.flatmap #2 children_conversions, 
                    children_equivalences @ es @ List.flatmap #3 children_conversions,
                    rs @ List.flatmap #4 children_conversions
                )
            end
      | Construction.Source(token) => 
            if (#subType type_system) ((CSpace.typeOfToken token), "line") then
                (Geometry.mk_leaf_line (), [], [], [])
            else if (#subType type_system) ((CSpace.typeOfToken token), "rect") then
                (Geometry.mk_leaf_rect (), [], [], [])
            else if (#subType type_system) ((CSpace.typeOfToken token), "angle") then
                (Geometry.mk_leaf_angle (), [], [], [])
            else raise PostProcessingException "unexpected leaf type"
      | Construction.Reference(token) => 
            if (#subType type_system) ((CSpace.typeOfToken token), "line") then
                (Geometry.mk_leaf_line (), [], [], [])
            else if (#subType type_system) ((CSpace.typeOfToken token), "rect") then
                (Geometry.mk_leaf_rect (), [], [], [])
            else if (#subType type_system) ((CSpace.typeOfToken token), "angle") then
                (Geometry.mk_leaf_angle (), [], [], [])
            else raise PostProcessingException "unexpected leaf type";
            

    fun from_state st =
        let val composition = #composition st;
            val construction = case Composition.constructionsInComposition composition of [] => raise PostProcessingException "No constructions!" | x::xs => x;
            val (r, cs, es, rs) = convert_construction (#sourceTypeSystem st) (construction);
        in {
            top = r,
            geometryGoals = rs,
            equivalenceGoals = es,
            constructions = cs
        }
        end

            
end

*)


signature IDENTIFICATION = 
sig
    val replace : ((CSpace.token * CSpace.token) list) -> Construction.construction -> Construction.construction;
end

structure Identification : IDENTIFICATION = 
struct
    fun replace replacements (Construction.TCPair(tc, constructions)) = Construction.TCPair(tc, List.map (replace replacements) constructions)
      | replace replacements (Construction.Source(token)) =
            (case List.find (fn (x,y) => x = token) replacements of
                None => Construction.Source(token)
              | SOME(x,y) => Construction.Reference(y))
      | replace replacements (Construction.Reference(token)) =
            (case List.find (fn (x,y) => x = token) replacements of
                None => Construction.Reference(token)
              | SOME(x,y) => Construction.Reference(y));
end







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
                  | _ => raise PostProcessingException "Unexpected relation in structure transfer result";
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
        let val result_composition : Composition.composition = State.patternCompOf state
            val result_construction : Construction.construction = 
                case Composition.resultingConstructions result_composition of 
                    [x] => x 
                    | _ => raise PostProcessingException "Multiple constructions in structure transfer result";
            val (keep_tokens, replacements, hints) = parse_relations (State.goalsOf state);
            (*val identified = Identification.replace replacements result_construction;*)
            val instantiated = Instantiation.instantiate result_construction keep_tokens replacements;
            val _ = PolyML.print (Seq.hd instantiated);
            val constraints = Seq.map Geometry.get_constraints instantiated;
            val _ = PolyML.print (Seq.hd constraints);
            val left_constraints = Seq.map ((List.filter Geometry.use_positive_constraint) o #1) constraints;
            val _ = PolyML.print (Seq.hd left_constraints);
            val _ = PolyML.print "================================================================";
            val points_map = "";
        in Seq.single state
        end;

    fun postprocess states = Seq.flat (Seq.map postprocess_state states);

end



  
    (*
    fun interpret_relationships relationships = 
        let datatype interpretation = Relations of relation list | Identification of string * CSpace.token | RelationOptions of relation list stream;
            fun interpret_relationship r = 
                case r of
                    ([], [l1, l2], "sameDirection") => 
                        let val l1 = Line(l1); val l2 = Line(l2); in 
                            Relations([
                                SameDirection(Start(l1),End(l1),Start(l2),End(l2))
                            ])
                  | ([], [l1, l2], "consecutive") =>
                        let val l1 = Line(l1); val l2 = Line(l2); in 
                            Relations([
                                SamePoint(End(l1),Start(l2))
                            ])
                  | ([], [l1, l2], "oppDirection") =>
                        let val l1 = Line(l1); val l2 = Line(l2); in 
                            Relations([
                                SameDirection(Start(l1),End(l1),End(l2),Start(l2))
                            ])
                  | ([], [l1, l2], "notParallel") =>
                        let val l1 = Line(l1); val l2 = Line(l2); in 
                            Relations([
                                Not(SameDirection(Start(l1),End(l1),Start(l2),End(l2))), 
                                Not(SameDirection(Start(l1),End(l1),End(l2),Start(l2)))
                            ])
                  | ([], [l1, l2], "startsOn") =>
                        raise GeometryError("TODO: startsOn isn't implemented")
                  | ([], [r1, r2], "shareSide") =>
                        let val r1 = Rect(r1); val r2 = Rect(r2); in 
                            Relations([
                                SameDirection(StartR(r1),EndR(r1),StartR(r2),EndR(r2)),
                                SamePoint(EndR(r1),StartR(r2)),
                                Equals(WidthR(r1),WidthR(r2))
                            ])
                  | ([], [l1, l2], "perpendicular") =>
                        let val l1 = Line(l1); val l2 = Line(l2); in
                            Relations([
                                SamePoint(End(l1),Start(l2)),
                                RightAngle(End(l1),Start(l1),End(l2))
                            ])
                  | ([], [l1, r1], "sideOf") =>
                        let val l1 = Line(l1); val r1 = Rect(r2) in
                            Relations([
                                SamePoint(End(l1),StartR(r1)),
                                RightAngle(Start(l1),End(l1),EndR(r1))
                            ])
    *)