import "evaluation.generator";

signature EVALUATION = 
sig
    val test : unit -> unit;
end

structure Evaluation : EVALUATION = 
struct

    val idea_limit = 100
    val limit = 50;
    val pp_limit = 50;

    fun count p = List.foldr (fn (x,y) => if p x then y + 1 else y) 0;

    fun evaluate_idea idea = 
        let val _ = print "--------------------------------------------------------------------\n"
            val (diagrams, _) = Seq.chop limit (Postprocessing.get_diagrams idea);
            val refuted = count (fn x => x = GeometryProver.Refuted) diagrams;
            val timeout = count (fn x => x = GeometryProver.Timeout) diagrams;
            val proven = List.filterOption (List.map (fn x => case x of GeometryProver.Proven x => SOME x | _ => NONE) diagrams);
            val probable = List.filterOption (List.map (fn x => case x of GeometryProver.Probable x => SOME x | _ => NONE) diagrams);
            val possible = List.filterOption (List.map (fn x => case x of GeometryProver.Possible x => SOME x | _ => NONE) diagrams);
            val _ = print (
                "Refuted: " ^ Int.toString refuted 
                ^ "; Timeout: " ^ Int.toString timeout
                ^ "; Proven: " ^ Int.toString (List.length proven)
                ^ "; Probable: " ^ Int.toString (List.length probable)
                ^ "; Possible: " ^ Int.toString (List.length possible)
                ^ "\n"
            )
            val _ = List.map (fn x => (
                print "Proven:\n";
                print (PolyML.makestring x ^ "\n")
            )) proven;
            val _ = List.map (fn (c,r) => (
                print "Probable:\n";
                print (PolyML.makestring c ^ "\n");
                print "if\n";
                print (PolyML.makestring r ^ "\n")
            )) probable;
            val _ = List.map (fn (c,r) => (
                print "Possible:\n";
                print (PolyML.makestring c ^ "\n");
                print "if\n";
                print (PolyML.makestring r ^ "\n")
            )) possible;
        in
            (refuted, timeout, proven, probable, possible)
        end


    fun test () = 
        let val document = Document.read "correspondences/eqgeom3";
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