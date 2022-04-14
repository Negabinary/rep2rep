structure CFS =
struct
    val document = Document.read "geometryTests";
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


    fun summary_test (source_construction_name,_,_,lims) = 
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
                    val pp_result = (Postprocessing.postprocess lims (fn x => ())) x;
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
                ("additionCommutes","t12","t13:equality",(50,200)),
                ("additionAssociates","t25","t26:equality",(50,200)),
                ("additionDistributes","t60","t61:equality",(50,1000)),
                ("cosSin","t93","t94:equality",(50,200)),
                ("trigonometry","t124","t125:equality",(50,1000))
            ];
            val _ = PolyML.Profiling.profile PolyML.Profiling.ProfileTime (List.map summary_test) inputs;
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

    fun test_other_strings lims = 
        let val other_strings = [
                ("commutative multiplication", "A * B = B * A"),
                ("associative multiplication", "A * open B * C close = open A * B close * C"),
                ("definition of tan", "tan A = sin A / cos A"),
                ("completing the square", "open A + B close * open A + B close = open A * A + A * B close + open B * A + B * B close"),
                ("one with a tan is sexy", "1 + tan A * tan A = open 1 / cos A close / cos A")
            ];
            val _ = List.map (fn (x,y) => (PolyML.print x; test_string y lims)) other_strings;
        in
            ()
        end;

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
    
    fun test_split_distance () = 
        let val _ = ();
            val Direction = (ref o SOME o Geometry.Direction);
            val Move = (ref o SOME o Geometry.Move);
            val Right = (ref o SOME o Geometry.Right);
            val RDir = (ref o SOME o Geometry.RDir);
            val Divide = (ref o SOME o Geometry.Divide);
            val Dot = (ref o SOME o Geometry.Dot);
            val JoinRect = Geometry.JoinRect;
            val ResolveRect = Geometry.ResolveRect;
            val Value = (ref o SOME o Geometry.Value);
            val Distance = (ref o SOME o Geometry.Distance);
            val Times = (ref o SOME o Geometry.Times);
            val Rect = Geometry.RootRect
            val A = "A"; val B = "B"; val C = "C";
            val p229 = ref NONE;
            val p228 = ref NONE;
            val p230 = ref NONE;
            val d231 = ref NONE;
            val p232 = ref NONE;
            val d233 = ref NONE;
            val input = ResolveRect(JoinRect(JoinRect(Rect(Move(Move(Move(p228, Right(Right(Direction(p228, p229))), Divide(Times(Value(B), Distance(p229, p228)), Value(C))), Right(Right(Direction(p228, p229))), Divide(Times(Value(A), Distance(p229, p228)), Distance(p230, Move(Move(p230, d231, Value(C)), d231, Value(B))))), Right(Right(Direction(p228, p229))), Divide(Times(Value(A), Times(Value(B), Distance(p229, p228))), Times(Distance(p232, Move(Move(p232, d233, Value(C)), d233, Value(B))), Value(C)))), Move(p228, Right(Right(Direction(p228, p229))), Divide(Times(Value(B), Distance(p229, p228)), Value(C))), Divide(Value(A), Distance(Move(Move(Move(p228, Right(Right(Direction(p228, p229))), Divide(Times(Value(B), Distance(p229, p228)), Value(C))), Right(Right(Direction(p228, p229))), Divide(Times(Value(A), Distance(p229, p228)), Distance(p230, Move(Move(p230, d231, Value(C)), d231, Value(B))))), Right(Right(Direction(p228, p229))), Divide(Times(Value(A), Times(Value(B), Distance(p229, p228))), Times(Distance(p232, Move(Move(p232, d233, Value(C)), d233, Value(B))), Value(C)))), Move(p228, Right(Right(Direction(p228, p229))), Divide(Times(Value(B), Distance(p229, p228)), Value(C)))))), Rect(Move(p228, Right(Right(Direction(p228, p229))), Divide(Times(Value(B), Distance(p229, p228)), Value(C))), p228, Divide(Value(B), Distance(Move(p228, Right(Right(Direction(p228, p229))), Divide(Times(Value(B), Distance(p229, p228)), Value(C))), p228)))), Rect(p228, p229, Divide(Value(C), Distance(p228, p229)))), JoinRect(Rect(Move(Move(Move(p228, Right(Right(Direction(p228, p229))), Divide(Times(Value(B), Distance(p229, p228)), Value(C))), Right(Right(Direction(p228, p229))), Divide(Times(Value(A), Distance(p229, p228)), Distance(p230, Move(Move(p230, d231, Value(C)), d231, Value(B))))), Right(Right(Direction(p228, p229))), Divide(Times(Value(A), Times(Value(B), Distance(p229, p228))), Times(Distance(p232, Move(Move(p232, d233, Value(C)), d233, Value(B))), Value(C)))), Move(p228, Right(Right(Direction(p228, p229))), Divide(Times(Value(B), Distance(p229, p228)), Value(C))), Divide(Value(A), Distance(Move(Move(Move(p228, Right(Right(Direction(p228, p229))), Divide(Times(Value(B), Distance(p229, p228)), Value(C))), Right(Right(Direction(p228, p229))), Divide(Times(Value(A), Distance(p229, p228)), Distance(p230, Move(Move(p230, d231, Value(C)), d231, Value(B))))), Right(Right(Direction(p228, p229))), Divide(Times(Value(A), Times(Value(B), Distance(p229, p228))), Times(Distance(p232, Move(Move(p232, d233, Value(C)), d233, Value(B))), Value(C)))), Move(p228, Right(Right(Direction(p228, p229))), Divide(Times(Value(B), Distance(p229, p228)), Value(C)))))), JoinRect(Rect(Move(p228, Right(Right(Direction(p228, p229))), Divide(Times(Value(B), Distance(p229, p228)), Value(C))), p228, Divide(Value(B), Distance(Move(p228, Right(Right(Direction(p228, p229))), Divide(Times(Value(B), Distance(p229, p228)), Value(C))), p228))), Rect(p228, p229, Divide(Value(C), Distance(p228, p229))))))
            val _ = (print o GeometryProver.print_proof_answer) (GeometryProver.attempt_proof (fn x => ()) (Geometry.RectCon(input)));
        in 
            ()
        end;
    
    fun test_solver () =
        let open Geometry
            fun root_line letter = let val s = ref NONE in RootLine(s, (ref o SOME o Move) (s, ref NONE, (ref o SOME o Value) letter)) end;
            fun root_angle letter = let val s = ref NONE; val t = ref NONE in RootAngle(s, t, (ref o SOME o Move) (t, (ref o SOME o RDir) ((ref o SOME o Direction) (s,t), letter), (ref o SOME o Distance) (s,t))) end;
            fun root_rect letter = let val s = ref NONE; val t = ref NONE in RootRect(s, t, (ref o SOME o Divide) ((ref o SOME o Value) letter, (ref o SOME o Distance) (s,t))) end;
            val Al1 = root_line "A";
            val Bl1 = root_line "B";
            val Al2 = root_line "A";
            val Bl2 = root_line "B";
            val Aa1 = root_angle "A";
            val Ba1 = root_angle "B";
            val Ar1 = root_rect "A";
            val Br1 = root_rect "B";
            val Al3 = root_line "A";
            val Bl3 = root_line "B";
            val Cl3 = root_line "C";
            val Aa3 = root_angle "A";
            val Ba3 = root_angle "B";
            val Ca3 = root_angle "C";
            val Ar3 = root_rect "A";
            val Br3 = root_rect "B";
            val Cr3 = root_rect "C";
            val Al4 = root_line "A";
            val Bl4 = root_line "B";
            val Cl4 = root_line "C";
            val Ul5 = root_line "1";
            val Al5 = root_line "A";
            val Bl5 = root_line "B";
            val Cl5 = root_line "C";
            val Ul6 = root_line "1";
            val Aa6 = root_angle "A";
            val Na6 = root_angle "9";
            val Ul7 = root_line "1";
            val Aa7 = root_angle "A";
            val Na7 = root_angle "9";
            val Ul8 = root_line "1";
            val Aa8 = root_angle "A";
            val Ul9 = root_line "1";
            val Aa9 = root_angle "A";
            val tests = [
                    (*("Commutative-line-1",
                        LineCon(
                            ResolveLine(
                                Concat(
                                    Al1,
                                    Bl1
                                ),
                                Reverse(
                                    Concat(
                                        Reverse(Bl1),
                                        Reverse(Al1)
                                    )
                                )
                            )
                        )
                    ),*)
                    ("Commutative-line-2",
                        LineCon(
                            ResolveLine(
                                Concat(
                                    Al2,
                                    Bl2
                                ),
                                MoveLine(
                                    Concat(
                                        MoveLine(Bl2, RootLine(ref NONE, ref NONE)),
                                        MoveLine(Al2, RootLine(ref NONE, ref NONE))
                                    ),
                                    RootLine(ref NONE, ref NONE)
                                )
                            )
                        )
                    )(*,
                    ("Commutative-angle",
                        AngleCon(
                            ResolveAngle(
                                JoinAngle(
                                    Aa1,
                                    Ba1
                                ),
                                ReverseAngle(
                                    JoinAngle(
                                        ReverseAngle(
                                            Ba1
                                        ),
                                        ReverseAngle(
                                            Aa1
                                        )
                                    )
                                )
                            )
                        )
                    ),
                    ("commutative-rect",
                        RectCon(
                            ResolveRect(
                                JoinRect(
                                    Ar1,
                                    Br1
                                ),
                                NextRect(NextRect(
                                    JoinRect(
                                        NextRect(NextRect(Br1)),
                                        NextRect(NextRect(Ar1))
                                    )
                                ))
                            )
                        )
                    ),
                    ("associative-line",
                        LineCon(
                            ResolveLine(
                                Concat(
                                    Al3,
                                    Concat(
                                        Bl3,
                                        Cl3
                                    )
                                ),
                                Concat(
                                    Concat(
                                        Al3,
                                        Bl3
                                    ),
                                    Cl3
                                )
                            )
                        )
                    ),
                    ("associative-angle",
                        AngleCon(
                            ResolveAngle(
                                JoinAngle(
                                    Aa3,
                                    JoinAngle(
                                        Ba3,
                                        Ca3
                                    )
                                ),
                                JoinAngle(
                                    JoinAngle(
                                        Aa3,
                                        Ba3
                                    ),
                                    Ca3
                                )
                            )
                        )
                    ),
                    ("associative-rect",
                        RectCon(
                            ResolveRect(
                                JoinRect(
                                    Ar3,
                                    JoinRect(
                                        Br3,
                                        Cr3
                                    )
                                ),
                                JoinRect(
                                    JoinRect(
                                        Ar3,
                                        Br3
                                    ),
                                    Cr3
                                )
                            )
                        )
                    ),
                    ("distribution-rect",
                        RectCon(
                            ResolveRect(
                                JoinRect(
                                    MKRect(
                                        Al4,
                                        Cl4
                                    ),
                                    MKRect(
                                        Bl4,
                                        MoveLine(
                                            Cl4,
                                            RootLine(ref NONE, ref NONE)
                                        )
                                    )
                                ),
                                MKRect(
                                    Concat(
                                        Al4, Bl4
                                    ),
                                    Cl4
                                )
                            )
                        )
                    ),
                    ("distribution-triangles",
                        LineCon(
                            ResolveLine(
                                SimilarTriangle(
                                    Concat(
                                        Al5, Bl5
                                    ),
                                    Ul5,
                                    Cl5
                                ),
                                Concat(
                                    SimilarTriangle(
                                        Al5,
                                        Ul5,
                                        Cl5
                                    ),
                                    SimilarTriangle(
                                        MoveLine(
                                            MoveLine(
                                                Bl5,
                                                RootLine(ref NONE, ref NONE)
                                            ),
                                            RootLine(ref NONE, ref NONE)
                                        ),
                                        MoveLine(Ul5,RootLine(ref NONE, ref NONE)),
                                        MoveLine(Cl5,RootLine(ref NONE, ref NONE))
                                    )
                                )
                            )
                        )
                    ),
                    ("sin-cos-1",
                        LineCon(
                            ResolveLine(
                                Sine(
                                    Ul6,
                                    Aa6
                                ),
                                MoveLine(
                                    Cosine(
                                        Ul6,
                                        ReverseAngle(
                                            SubAngle(
                                                Na6,
                                                Aa6
                                            )
                                        )
                                    ),
                                    RootLine(ref NONE, ref NONE)
                                )
                            )
                        )
                    ),
                    ("sin-cos-2",
                        LineCon(
                            ResolveLine(
                                Cosine(
                                    Ul7,
                                    Aa7
                                ),
                                MoveLine(
                                    Sine(
                                        Ul7,
                                        ReverseAngle(
                                            SubAngle(
                                                Na7,
                                                Aa7
                                            )
                                        )
                                    ),
                                    RootLine(ref NONE, ref NONE)
                                )
                            )
                        )
                    ),
                    ("sin-sq-cos-sq",
                        RectCon(
                            ResolveRect(
                                Pythag(
                                    Reverse(
                                        Sine(
                                            Ul8,
                                            Aa8
                                        )
                                    ),
                                    Reverse(
                                        Cosine(
                                            Ul8,
                                            Aa8
                                        )
                                    )
                                ),
                                MKRect(
                                    Ul8,
                                    Rotate(Ul8, RootAngle(ref NONE, ref NONE, ref NONE))
                                )
                            )
                        )
                    ),
                    ("cos-sq-sin-sq",
                        RectCon(
                            ResolveRect(
                                Pythag(
                                    Cosine(
                                        Ul8,
                                        Aa8
                                    ),
                                    Sine(
                                        Ul8,
                                        Aa8
                                    )
                                ),
                                MKRect(
                                    Reverse(Ul8),
                                    Rotate(Reverse(Ul8), RootAngle(ref NONE, ref NONE, ref NONE))
                                )
                            )
                        )
                    )*)
                ]
            fun run_test (test_name, test) = 
                let val _ = print (test_name ^ ":-------------------------------------------------------\n");
                    val _ = PolyML.print test;
                    val result = GeometryProver.attempt_proof (fn x => ()) (test);
                in
                    print (GeometryProver.print_proof_answer result)
                end;
            val _ = List.map run_test tests;
        in
            ()
        end;

end