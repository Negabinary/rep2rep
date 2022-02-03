signature GENERATOR = 
sig
    val equations : int -> Construction.construction Seq.seq;
    val check_equality : Construction.construction -> bool;
    val test : unit -> unit;
    val pdf_constructions : unit -> unit;
end

structure Generator:GENERATOR =
struct
    val counter = ref 0;
    fun unique_name () = (counter := !counter + 1; "t" ^ (PolyML.makestring (!counter)));

    val equation_document = Document.read "equation";
    val equation_type_system = Document.findTypeSystemWithName equation_document "equation";
    val equation_construction_space = Document.findConSpecWithName equation_document "equationG";
    fun leaf_of_string x = Construction.Source (CSpace.makeToken (unique_name ()) (Type.typeOfString x));
    fun leaves () = Seq.map leaf_of_string (Seq.of_list ["A","B","C","D","E","one","ninety"]);
    fun bin_ops () = Seq.map leaf_of_string (Seq.of_list ["plus","minus","times","divide"]);
    fun funcs () = Seq.map leaf_of_string (Seq.of_list ["sin","cos","tan"]);
    fun expressions max = if max > 0 then
        let val token = CSpace.makeToken (unique_name ()) (Type.typeOfString ((unique_name ()) ^ ":expr"));
            val all_options = Seq.of_list [
                (Seq.flat o Seq.flat)
                (Seq.map (fn x => 
                    Seq.map (fn y =>
                        Seq.map (fn z => 
                            Construction.TCPair ({token=token, constructor=the (CSpace.findConstructorWithName "infixOp" equation_construction_space)}, [x,y,z])
                        ) (expressions (max-1))
                    ) (bin_ops ())
                ) (expressions (max-1))),
                (Seq.flat)
                (Seq.map (fn x => 
                    Seq.map (fn y =>
                        Construction.TCPair ({token=token, constructor=the (CSpace.findConstructorWithName "app" equation_construction_space)}, [x,y])
                    ) (expressions (max-1))
                ) (funcs ()))
            ]
        in
            Seq.append (leaves ()) ((Seq.flat) all_options)
        end
    else
        leaves ();
    fun equations max = Seq.flat (
            Seq.map (fn x =>
                Seq.map (fn y =>
                    Construction.TCPair ({token=CSpace.makeToken (unique_name ()) (Type.typeOfString ((unique_name ()) ^ ":equality")), constructor=the (CSpace.findConstructorWithName "equality" equation_construction_space)}, [x, leaf_of_string "equals",y])
                ) (expressions (max))
            ) (expressions (max))
        );
    
    exception CalculationException of string;

    fun deg2rad x = x / 180.0 * Math.pi;

    fun calculate (a,b,c,d,e) (Construction.Source (_, "A")) = a
      | calculate (a,b,c,d,e) (Construction.Source (_, "B")) = b
      | calculate (a,b,c,d,e) (Construction.Source (_, "C")) = c
      | calculate (a,b,c,d,e) (Construction.Source (_, "D")) = d
      | calculate (a,b,c,d,e) (Construction.Source (_, "E")) = e
      | calculate _ (Construction.Source (_, "one")) = 1.0
      | calculate _ (Construction.Source (_, "ninety")) = 90.0
      | calculate v (Construction.TCPair ({constructor=constructor, ...}, c)) = (case (CSpace.nameOfConstructor constructor, c) of
            ("infixOp", [x, Construction.Source y, z]) => (case ((Type.nameOfType o CSpace.typeOfToken) y) of
                "plus" => calculate v x + calculate v z
              | "minus" => calculate v x - calculate v z
              | "times" => calculate v x * calculate v z
              | "divide" => calculate v x / calculate v z
              | _ => raise (CalculationException "5"))
          | ("app", [Construction.Source x, y]) => (case ((Type.nameOfType o CSpace.typeOfToken) x) of
                "sin" => Math.sin (deg2rad (calculate v y))
              | "cos" => Math.cos (deg2rad (calculate v y))
              | "tan" => Math.tan (deg2rad (calculate v y))
              | _ => raise (CalculationException "4"))
          | ("brackets", [x,y,z]) => calculate v y
          | _ => raise (CalculationException "3"))
      | calculate v _ = raise (CalculationException "2");
    
    fun same_real (x,y) = Real.abs (1.0 - (x / y)) < 0.00000001;

    val test_values = (4.914389147, 8.499798154, 69.78328681, 24.20897737, 23.89088144);

    fun check_equality (Construction.TCPair (_,[x,y,z])) = same_real (calculate test_values x, calculate test_values z)
      | check_equality _ = raise (CalculationException "1");
    
    fun test () = (Seq.chop 10000000 (Seq.map (fn x =>(PolyML.print (Construction.toString (x)), PolyML.print(check_equality x))) (equations 3));());

    fun pdf_constructions () = (Seq.chop 10 (Seq.map (print o Latex.construction (0.0,0.0)) (Seq.filter check_equality (equations 3))); ());
end