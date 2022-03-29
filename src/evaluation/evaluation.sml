import "evaluation.generator";

signature EVALUATION = 
sig
    val test : unit -> unit;
end

structure Evaluation : EVALUATION = 
struct

    val idea_limit = 100
    val limit = 50;
    val ulimit = 50;
    val pp_limit = 50;

    fun count p = List.foldr (fn (x,y) => if p x then y + 1 else y) 0;

    fun evaluate_idea idea = 
        let val _ = print "--------------------------------------------------------------------\n"
            val pp_result = Postprocessing.postprocess_silent (limit, ulimit) idea;
            val _ = Postprocessing.print_summary pp_result;
            val _ = Postprocessing.print_proven pp_result;
            val _ = Postprocessing.print_probable pp_result;
            val _ = Postprocessing.print_possible pp_result;
        in
            ()
        end


    fun test () = 
        let val document = Document.read "correspondences/eqgeom";
            val KB = Document.knowledgeOf document;
            val sourceTypeSystem = Document.findTypeSystemWithName document "equation";
            val targetTypeSystem = Document.findTypeSystemWithName document "geometry";
            val equations = Generator.equations 2;
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
end