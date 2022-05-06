import "evaluation.generator";

structure Evaluation = 
struct

    val idea_limit = 100
    val pp_limit = 50;

    fun count p = List.foldr (fn (x,y) => if p x then y + 1 else y) 0;

    fun evaluate_idea idea = 
        let val _ = print "--------------------------------------------------------------------\n"
            val pp_result = Postprocessing.postprocess_silent (2000, 0) idea;
            val _ = Postprocessing.print_summary pp_result;
            val _ = Postprocessing.print_proven pp_result;
            val _ = Postprocessing.print_probable pp_result;
            val _ = Postprocessing.print_possible pp_result;
        in
            ()
        end


    fun test n = 
        let val document = Document.read "correspondences/eqgeom";
            val KB = Document.knowledgeOf document;
            val sourceTypeSystem = Document.findTypeSystemWithName document "equation";
            val targetTypeSystem = Document.findTypeSystemWithName document "geometry";
            val equations = Generator.equations_2 n;
            val correct_equations = Seq.filter Generator.check_equality equations;
            fun evaluate_problem construction = 
                let val _ = print "====================================================================\n";
                    val _ = print (Generator.print_equation construction ^ "\n");
                    val goal = ([Construction.constructOf construction], [CSpace.makeToken "t'" (Type.typeOfString "value")], "repeq");
                    val transfers = Transfer.masterTransfer false false NONE KB sourceTypeSystem targetTypeSystem construction goal;
                    val full_transfers = Seq.filter (fn x => Postprocessing.is_fully_transfered x handle Postprocessing.UnresolvableGeometryTypes => false) transfers;
                    val (ideas, _) = Seq.chop idea_limit full_transfers;
                    val _ = Int.toString (List.length ideas) ^ " ideas found.";
                    val _ = List.map evaluate_idea ideas;
                in
                    ()
                end
            val _ = Seq.chop 100000 (Seq.map evaluate_problem correct_equations);
        in () end;
    
    fun number_of_ideas n =
        let val document = Document.read "correspondences/eqgeom";
            val KB = Document.knowledgeOf document;
            val sourceTypeSystem = Document.findTypeSystemWithName document "equation";
            val targetTypeSystem = Document.findTypeSystemWithName document "geometry";
            val equations = Generator.equations_2 n;
            val correct_equations = Seq.filter Generator.check_equality equations;

            fun evaluate_problem construction = 
                let val goal = ([Construction.constructOf construction], [CSpace.makeToken "t'" (Type.typeOfString "value")], "repeq");
                    val transfers = Transfer.masterTransfer false false NONE KB sourceTypeSystem targetTypeSystem construction goal;
                    val full_transfers = Seq.filter (fn x => Postprocessing.is_fully_transfered x handle Postprocessing.UnresolvableGeometryTypes => false) transfers;
                in
                    PolyML.print(List.length (Seq.list_of full_transfers))
                end
            val _ = Seq.chop 100000 (Seq.map evaluate_problem correct_equations);
        in () end;
    
    fun variations_per_idea n =
        let val document = Document.read "correspondences/eqgeom";
            val KB = Document.knowledgeOf document;
            val sourceTypeSystem = Document.findTypeSystemWithName document "equation";
            val targetTypeSystem = Document.findTypeSystemWithName document "geometry";
            val equations = Generator.equations_2 n;
            val correct_equations = Seq.filter Generator.check_equality equations;
            fun evaluate_idea eql idea = print (Int.toString (eql) ^ ", " ^ LargeInt.toString (Postprocessing.count_variants idea) ^ "\n")
            fun evaluate_problem construction = 
                let val eq_length = Generator.equation_length construction;
                    val goal = ([Construction.constructOf construction], [CSpace.makeToken "t'" (Type.typeOfString "value")], "repeq");
                    val transfers = Transfer.masterTransfer false false NONE KB sourceTypeSystem targetTypeSystem construction goal;
                    val full_transfers = Seq.filter (fn x => Postprocessing.is_fully_transfered x handle Postprocessing.UnresolvableGeometryTypes => false) transfers;
                    val (ideas, _) = Seq.chop idea_limit full_transfers;
                    val _ = List.map (evaluate_idea eq_length) ideas;
                in
                    ()
                end
            val _ = Seq.chop 100000 (Seq.map evaluate_problem correct_equations);
        in () end;
end