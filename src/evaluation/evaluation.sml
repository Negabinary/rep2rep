import "evaluation.generator";

signature EVALUATION = 
sig
    val test : unit -> unit;
end

structure Evaluation : EVALUATION = 
struct

    val limit = 100;
    val pp_limit = 100;

    fun test () = 
        let val document = Document.read "correspondences/eqgeom3";
            val KB = Document.knowledgeOf document;
            val sourceTypeSystem = Document.findTypeSystemWithName document "equation";
            val targetTypeSystem = Document.findTypeSystemWithName document "geometry";
            val equations = Generator.equations 3;
            val correct_equations = Seq.filter Generator.check_equality equations;
            fun equation_to_geometries construction = 
                let val _ = PolyML.print ("CONSTRUCTION >> ", construction);
                    val goal = ([Construction.constructOf construction], [CSpace.makeToken "t'" (Type.typeOfString "value")], "repeq");
                    val transfers = Transfer.masterTransfer false false NONE KB sourceTypeSystem targetTypeSystem construction goal;
                    val _ = PolyML.print ("TRANSFERS >> ", Seq.chop 50 transfers);
                    val full_transfers = Seq.filter Postprocessing.is_fully_transfered transfers;
                    (*val _ = PolyML.print ("FULL_TRANSFERS >> ", Seq.chop 5 full_transfers);*)
                    val diagrams = Seq.flat (Seq.map (Seq.take pp_limit o Postprocessing.get_diagrams) full_transfers);
                    (*val _ = PolyML.print ("DIAGRAMS >> ", Seq.chop 5 diagrams);*)
                    val _ = PolyML.print ("");
                in
                    Seq.chop limit (Seq.map PolyML.print diagrams)
                end
            val _ = Seq.chop 100000 (Seq.map equation_to_geometries correct_equations);
        in () end;
end