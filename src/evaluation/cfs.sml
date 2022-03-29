structure CFS =
struct
    val document = Document.read "grammarTest";
    val KB = Document.knowledgeOf document;
    val sourceTypeSystem = Document.findTypeSystemWithName document "equation";
    val targetTypeSystem = Document.findTypeSystemWithName document "geometry";

    exception TestingException of string;

    fun get_ideas output source_construction = 
        let val goal = (
                [Construction.constructOf source_construction],
                [CSpace.makeToken "t'" (Type.typeOfString "value")], 
                "repeq"
            );
            val transfers = Transfer.masterTransfer false false NONE KB sourceTypeSystem targetTypeSystem source_construction goal;
            val full_transfers = Seq.filter (fn x => Postprocessing.is_fully_transfered x handle Postprocessing.UnresolvableGeometryTypes => false) transfers;
            val (ideas, _) = Seq.chop 10 full_transfers;
        in
            ideas
        end

    fun construction_of state = 
        (case Composition.resultingConstructions (State.patternCompOf state) of
            [x] => x
            | _ => raise Postprocessing.PostProcessingException "Multiple constructions in structure transfer result");

    fun get_idea_latex idea = (Latex.construction (0.0,0.0) (construction_of idea) ^ "\n\n");


    fun summary_test (source_construction_name,_,_) = 
        let val _ = print ("TRANSFERRING "^ source_construction_name ^ ".\n");
            val source_construction = #construction (Document.findConstructionWithName document source_construction_name);
            fun output x = (print (GeometryProver.print_proof_answer x); PolyML.print "----------------------------------------------------------------"; ());
            val ideas = get_ideas output source_construction
            val _ = print (PolyML.makestring (List.length ideas) ^ " full transfers.\n")
            (* val _ = List.map (print o get_idea_latex) ideas; *)
            fun loop x = 
                let 
                    (* val _ = (print o get_idea_latex) x; *)
                    fun pp_output x = (print (GeometryProver.print_proof_answer x); PolyML.print "----------------------------------------------------------------"; ());
                    val pp_result = (Postprocessing.postprocess (50,100) (fn x => ())) x;
                    val _ = Postprocessing.print_summary pp_result;
                    val _ = Postprocessing.print_proven pp_result;
                    val _ = Postprocessing.print_probable pp_result;
                    (* val _ = Postprocessing.print_possible pp_result; *)
                in
                    ()
                end
            val _ = List.map loop ideas;
        in
            ()
        end;


    fun summary_test_all () =
        let val inputs = [
                ("additionCommutes","t12","t13:equality"),
                ("additionAssociates","t25","t26:equality"),
                ("additionDistributes","t60","t61:equality"),
                ("cosSin","t93","t94:equality"),
                ("trigonometry","t124","t125:equality")
            ];
            val _ = List.map summary_test inputs;
        in
            ()
        end;
    
    fun test_probable () =
        let val source_construction = #construction (Document.findConstructionWithName document "cosSin");
            fun output x = ();
            val ideas = get_ideas output source_construction;
            val _ = print (PolyML.makestring (List.length ideas) ^ " full transfers.\n");
            val _ = List.map (print o get_idea_latex) ideas;
            fun loop x = 
                let val pp_result = Postprocessing.postprocess_silent (50,1000) x;
                    val _ = Postprocessing.print_summary pp_result;
                    val _ = Postprocessing.print_probable pp_result;
                in
                    ()
                end;
            val _ = List.map loop ideas;
        in
            ()
        end;
    
    fun test_string str lims = 
        let val grammar = Document.findGrammarWithName document "equationM";
            val tokens = String.tokens (fn x => x = #"\n" orelse x = #" ") str;
            val source_constructions = Grammar.parse grammar "equality" tokens;
            val source_construction = case source_constructions of (x::_) => x | _ => raise (TestingException "Could not parse expression.");
            fun output x = ();
            val ideas = get_ideas output source_construction;
            val _ = print (PolyML.makestring (List.length ideas) ^ " full transfers.\n");
            val _ = List.map (print o get_idea_latex) ideas;
            fun loop x = 
                let val pp_result = Postprocessing.postprocess_silent lims x;
                    val _ = Postprocessing.print_summary pp_result;
                    val _ = Postprocessing.print_proven pp_result;
                    val _ = Postprocessing.print_probable pp_result;
                    (* val _ = Postprocessing.print_possible pp_result; *)
                in
                    ()
                end;
            val _ = List.map loop ideas;
        in
            ()
        end

    fun angel_5 () = 
        let val p1 = ref NONE;
            val d1 = ref NONE;
            val p1e = ref (SOME(Geometry.Move(p1, d1, ref (SOME(Geometry.Value("1"))))));
            val p2 = ref NONE;
            val p2f = ref NONE;
            val p2t = ref (SOME(Geometry.Move(p2, ref (SOME(Geometry.RDir(ref (SOME(Geometry.Direction(p2, p2f))), "A"))), ref NONE)));
            val result = GeometryProver.attempt_proof (fn x => (PolyML.print x; ())) (
                    Geometry.RectCon (
                        Geometry.ResolveRect (
                            Geometry.Pythag (
                                Geometry.ResolveLine (
                                    Geometry.Cosine(
                                        Geometry.RootLine(
                                            p1, p1e
                                        ),
                                        Geometry.RootAngle(
                                            p2f, p2, p2t
                                        )
                                    ),
                                    Geometry.Cosine(
                                        Geometry.RootLine(
                                            p1,p1e
                                        ),
                                        Geometry.RootAngle(
                                            p2f, p2, p2t
                                        )
                                    )
                                ),
                                Geometry.ResolveLine (
                                    Geometry.Sine(
                                        Geometry.RootLine(
                                            p1, p1e
                                        ),
                                        Geometry.RootAngle(
                                            p2f, p2, p2t
                                        )
                                    ),
                                    Geometry.Sine(
                                        Geometry.RootLine(
                                            p1, p1e
                                        ),
                                        Geometry.RootAngle(
                                            p2f, p2, p2t
                                        )
                                    )
                                )
                            ),
                            Geometry.MKRect(
                                Geometry.Reverse(Geometry.RootLine(p1, p1e)),
                                Geometry.Rotate(Geometry.Reverse(Geometry.RootLine(p1, p1e)), Geometry.RootAngle(ref NONE, ref NONE, ref NONE))
                            )
                        )
                    )
                );
        in
            print (GeometryProver.print_proof_answer result)
        end

    fun test_numeric_eval () =
        let val Direction = (ref o SOME o Geometry.Direction);
            val Move = (ref o SOME o Geometry.Move);
            val Right = (ref o SOME o Geometry.Right);
            val RDir = (ref o SOME o Geometry.RDir);
            val Divide = (ref o SOME o Geometry.Divide);
            val Dot = (ref o SOME o Geometry.Dot);
            val p1 = ref NONE;
            val p2 = ref NONE;
            val p3 = ref NONE;
            val d4 = ref NONE;
            val s4 = ref NONE;
            val d5 = ref NONE;
            val s5 = ref NONE;
            val A = "A";
            val lhs = Geometry.Direction(p2, Move(Move(p2, Right(RDir(Right(Right(Direction(p1, p3))), A)), Dot(d4,RDir(d4, A))), Right(Right(Right(Right(Right(Direction(p1, p3)))))), Divide(s5, s5)));
            val rhs = Geometry.Right(Right(RDir(Right(Right(Direction(p1, p3))), A)));
            val map = Geometry.create_map ();
        in
            (Geometry.numeric_direction map lhs, Geometry.numeric_direction map rhs)
        end;

end