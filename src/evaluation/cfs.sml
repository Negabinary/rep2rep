structure CFS =
struct
    val document = Document.read "grammarTest";
    val KB = Document.knowledgeOf document;
    val sourceTypeSystem = Document.findTypeSystemWithName document "equation";
    val targetTypeSystem = Document.findTypeSystemWithName document "geometry";

    fun summary_test (source_construction_name,_,_) = 
        let val source_construction = #construction (Document.findConstructionWithName document source_construction_name);
            val _ = PolyML.print (Construction.constructOf source_construction);
            val goal = (
                [Construction.constructOf source_construction],
                [CSpace.makeToken "t'" (Type.typeOfString "value")], 
                "repeq"
            );
            val _ = print ("TRANSFERRING "^ source_construction_name ^ ".\n");
            fun output x = (print (GeometryProver.print_proof_answer x); PolyML.print "----------------------------------------------------------------"; ());
            val transfers = Transfer.masterTransfer false false NONE KB sourceTypeSystem targetTypeSystem source_construction goal;
            val full_transfers = Seq.filter (fn x => Postprocessing.is_fully_transfered x handle Postprocessing.UnresolvableGeometryTypes => false) transfers;
            val (ideas, _) = Seq.chop 10 full_transfers;
            val _ = print (PolyML.makestring (List.length ideas) ^ " full transfers.\n")
            fun construction_of state = 
                (case Composition.resultingConstructions (State.patternCompOf state) of
                    [x] => x
                    | _ => raise Postprocessing.PostProcessingException "Multiple constructions in structure transfer result");
            val _ = List.map (fn x => print (Latex.construction (0.0,0.0) (construction_of x) ^ "\n\n")) ideas;
            fun loop x = 
                let val pp_result = Postprocessing.postprocess_silent 50 x;
                    val _ = Postprocessing.print_summary pp_result;
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
    



    fun angel_5 () = 
        let val p1 = ref NONE;
            val d1 = ref NONE;
            val p1e = ref (SOME(Geometry.Move(p1, d1, ref (SOME(Geometry.Value("1"))))));
            val p2 = ref NONE;
            val p2f = ref NONE;
            val p2t = ref (SOME(Geometry.Move(p2, ref (SOME(Geometry.RDir(ref (SOME(Geometry.Direction(p2, p2f))), "A"))), ref NONE)));
        in
            GeometryProver.attempt_proof (fn x => (PolyML.print x; ())) (
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
                            Geometry.RootLine(p1, p1e),
                            Geometry.Rotate(Geometry.RootLine(p1, p1e), Geometry.RootAngle(ref NONE, ref NONE, ref NONE))
                        )
                    )
                )
            )
        end
end