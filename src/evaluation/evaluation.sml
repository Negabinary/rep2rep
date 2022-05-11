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
    
    fun variation_distribution n = 
        let val document = Document.read "correspondences/eqgeom";
            val KB = Document.knowledgeOf document;
            val sourceTypeSystem = Document.findTypeSystemWithName document "equation";
            val targetTypeSystem = Document.findTypeSystemWithName document "geometry";
            val equations = Generator.equations_2 n;
            val correct_equations = Seq.filter Generator.check_equality equations;

            fun make_ideas construction = 
                let val _ = print "====================================================================\n";
                    val _ = print (Generator.print_equation construction ^ "\n");
                    val goal = ([Construction.constructOf construction], [CSpace.makeToken "t'" (Type.typeOfString "value")], "repeq");
                    val transfers = Transfer.masterTransfer false false NONE KB sourceTypeSystem targetTypeSystem construction goal;
                    val full_transfers = Seq.filter (fn x => Postprocessing.is_fully_transfered x handle Postprocessing.UnresolvableGeometryTypes => false) transfers;
                    val (ideas, _) = Seq.chop idea_limit full_transfers;
                in
                    ideas
                end
            
            val ideas = List.flatmap make_ideas (Seq.list_of correct_equations);
            
            val N = 2000;

            val refuted_array = Array.array (N,0);
            val timeout_array = Array.array (N,0);
            val proven_array = Array.array (N,0);
            val probable_array = Array.array (N,0);
            val possible_array = Array.array (N,0);

            val _ = PolyML.print "BEGIN EVALUATION";

            fun evaluate_idea idea = 
                let val _ = print "--------------------------------------------------------------------\n"
                    val pp_result = List.enumerate (Postprocessing.postprocess_silent (N, 0) idea);
                    fun inc_arr arr i = Array.update (arr, i, (Array.sub (arr, i)) + 1);
                    fun use_res (i,GeometryProver.Proven _) = (inc_arr proven_array i; true)
                      | use_res (i,GeometryProver.Refuted) = (inc_arr refuted_array i; false)
                      | use_res (i,GeometryProver.Possible _) = (inc_arr possible_array i; false)
                      | use_res (i,GeometryProver.Probable _) = (inc_arr probable_array i; true)
                      | use_res (i,GeometryProver.Timeout) = (inc_arr timeout_array i;false);
                    val _ = List.exists use_res pp_result;
                    val _ = PolyML.print (List.length pp_result);
                in
                    ()
                end
        
            val _ = List.map evaluate_idea ideas;
            val _ = PolyML.line_length 100000000000000;
            val _ = PolyML.print_depth 100000000000000;
            val _ = PolyML.print refuted_array;
            val _ = PolyML.print timeout_array;
            val _ = PolyML.print proven_array;
            val _ = PolyML.print probable_array;
            val _ = PolyML.print possible_array;

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