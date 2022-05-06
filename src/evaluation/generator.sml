signature GENERATOR = 
sig
    val equations : int -> Construction.construction Seq.seq;
    val equations_2 : int -> Construction.construction Seq.seq;
    val equations_3 : int -> Construction.construction list;
    val check_equality : Construction.construction -> bool;
    val test : unit -> unit;
    val test_3 : int -> int;
    val pdf_constructions : unit -> unit;
    val print_equation : Construction.construction -> string;
    val equation_length : Construction.construction -> int;
end

structure Generator:GENERATOR =
struct
    val counter = ref 0;
    fun unique_name () = (counter := !counter + 1; "t" ^ (PolyML.makestring (!counter)));

    val equation_document = Document.read "equation";
    val equation_type_system = Document.findTypeSystemWithName equation_document "equation";
    val equation_construction_space = Document.findConSpecWithName equation_document "equationG";
    val equation_grammar = Document.findGrammarWithName equation_document "equationM";
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
    
    fun all_var_options () = Seq.map (fn (i,x) => (i,leaf_of_string x)) (Seq.of_list [(0,"A"),(1,"B"),(2,"C"),(3,"D"),(4,"E")]);
    fun expressions_2 max_len (var_min, var_max) = 
            let val var_options = Seq.map (fn (i,x) => (x,1,Int.min (i + 1, var_max))) (Seq.take (Int.min (var_min+1,var_max)) (all_var_options ()))
                fun mk_expr () = CSpace.makeToken (unique_name ()) (Type.typeOfString ((unique_name ()) ^ ":expr"));
                val infix_options = 
                    if max_len >= 3 then
                        let val options_l = expressions_2 (max_len - 2) (var_min, var_max);
                            fun options_r (expr_l,len_l,var_l) = expressions_2 (max_len - len_l - 1) (var_l, var_max);
                            val options_lr = Seq.maps (fn (option_l as (expr_l,len_l,var_l)) => Seq.map (fn (expr_r, len_r, var_r) => (expr_l,expr_r, len_l + len_r, var_r)) (options_r option_l)) options_l;
                        in
                            Seq.maps (fn (el,er,l,v) => 
                                Seq.map (fn x => 
                                    (Construction.TCPair ({token=mk_expr (), constructor=the (CSpace.findConstructorWithName "infixOp" equation_construction_space)}, [el,x,er]), l+1, v)
                                ) (bin_ops ())
                            ) options_lr
                        end
                    else
                        Seq.empty;
                val app_options = 
                    if max_len >= 2 then
                        Seq.maps (fn (er,lr,vr) => 
                            Seq.map (fn x => 
                                (Construction.TCPair ({token=mk_expr (), constructor=the (CSpace.findConstructorWithName "app" equation_construction_space)}, [x,er]),lr+1,vr)
                            ) (funcs ())
                        ) (expressions_2 (max_len-1) (var_min,var_max))
                    else
                        Seq.empty;
            in
                Seq.append (Seq.append var_options infix_options) app_options
            end;
    
    fun equations_2 max_len : Construction.construction Seq.seq = 
        let val options_l = expressions_2 (max_len-2) (0,5);
            fun options_r (el,ll,vl) = Seq.map (fn (er,_,_) => (el,er)) (expressions_2 (max_len-ll-1) (vl,vl));
        in
            Seq.maps (fn option_l => 
                Seq.map (fn (el,er) => 
                    Construction.TCPair ({token=CSpace.makeToken (unique_name ()) (Type.typeOfString ((unique_name ()) ^ ":equality")), constructor=the (CSpace.findConstructorWithName "equality" equation_construction_space)}, [el, leaf_of_string "equals",er])
                ) (options_r option_l)
            ) options_l
        end;
    
    exception CalculationException of string;

    fun deg2rad x = x / 180.0 * Math.pi;

    exception NumericZero;
    val epsilon = 0.00000001;
    val big = 1000000000.0
    fun cz x = if x < epsilon then raise NumericZero else x;
    fun cb x = if Real.abs x > big then raise NumericZero else x;

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
              | "minus" => cz (calculate v x - calculate v z)
              | "times" => calculate v x * calculate v z
              | "divide" => calculate v x / calculate v z
              | _ => raise (CalculationException "5"))
          | ("app", [Construction.Source x, y]) => (case ((Type.nameOfType o CSpace.typeOfToken) x) of
                "sin" => cz (Math.sin (calculate v y))
              | "cos" => cz (Math.cos (calculate v y))
              | "tan" => cb (cz (Math.tan (calculate v y)))
              | _ => raise (CalculationException "4"))
          | ("brackets", [x,y,z]) => calculate v y
          | _ => raise (CalculationException "3"))
      | calculate v _ = raise (CalculationException "2");
    
    exception EquationPrinterException of string;

    fun join delim string_list = List.foldr (fn (x,y) => x ^ delim ^ y) "" string_list;
    fun print_equation (Construction.TCPair (_, children)) = "[" ^ join " " (List.map print_equation children) ^ "]"
      | print_equation (Construction.Source t) = Type.nameOfType (CSpace.typeOfToken t)
      | print_equation _ = raise (EquationPrinterException "References (non-tree constructions) are not supported.");
    
    fun equation_length (Construction.TCPair (_, children)) = List.foldr (op +) 0 (List.map equation_length children)
      | equation_length (Construction.Source t) = 1
      | equation_length _ = raise (EquationPrinterException "References (non-tree constructions) are not supported.");
    
    fun same_real (x,y) = Real.abs (1.0 - (x / y)) < 0.0000000001;

    val test_values = (0.9750061064065859, 0.44225947342754174, 0.7499296430131562, 0.610794349848656, 0.8710809157611894);

    fun check_equality (Construction.TCPair (_,[x,y,z])) = (same_real ((calculate test_values x, calculate test_values z)) handle NumericZero => false)
      | check_equality _ = raise (CalculationException "1");
    
    fun test () = (Seq.chop 10000000 (Seq.map (fn x =>(PolyML.print (print_equation x), PolyML.print(check_equality x))) (equations 3));());

    fun pdf_constructions () = (Seq.chop 10 (Seq.map (print o Latex.construction (0.0,0.0)) (Seq.filter check_equality (equations 3))); ());

    fun is_superset x y = 
        let val map = ref [];
            fun map_contains [] _ = NONE
              | map_contains ((x,v)::xs) k = if x = k then SOME(v) else map_contains xs k;
            fun is_same (Construction.Source t1) (Construction.Source t2) = (Type.nameOfType (CSpace.typeOfToken t1)) = (Type.nameOfType (CSpace.typeOfToken t2))
              | is_same (Construction.TCPair ({constructor=("infixOp",_), ...}, [a1,(Construction.Source b1),c1])) (Construction.TCPair ({constructor=("infixOp",_), ...}, [a2,(Construction.Source b2),c2])) =
                    (Type.nameOfType (CSpace.typeOfToken b1)) = (Type.nameOfType (CSpace.typeOfToken b2)) andalso is_same a1 a2 andalso is_same c1 c2
              | is_same (Construction.TCPair ({constructor=("app",_), ...}, [(Construction.Source a1),b1])) (Construction.TCPair ({constructor=("app",_), ...}, [(Construction.Source a2),b2])) =
                    (Type.nameOfType (CSpace.typeOfToken a1)) = (Type.nameOfType (CSpace.typeOfToken a2)) andalso is_same b1 b2
              | is_same (Construction.TCPair ({constructor=("brackets",_), ...}, [_,x,_])) y = is_same x y
              | is_same x (Construction.TCPair ({constructor=("brackets",_), ...}, [_,y,_])) = is_same x y
              | is_same _ _ = false;
            fun check k v1 = case map_contains (!map) k of
                    SOME(v2) => (is_same v1 v2)
                  | NONE => (map := ((k,v1) :: !map);true);
            fun recursive_check (Construction.Source t) v = (check (Type.nameOfType (CSpace.typeOfToken t)) v)
              | recursive_check (Construction.TCPair ({constructor=("infixOp",_), ...}, [a1,b1,c1])) (Construction.TCPair ({constructor=("infixOp",_), ...}, [a2,b2,c2])) =
                    b1 = b2 andalso recursive_check a1 a2 andalso recursive_check c1 c2
              | recursive_check (Construction.TCPair ({constructor=("app",_), ...}, [a1,b1])) (Construction.TCPair ({constructor=("app",_), ...}, [a2,b2])) =
                    a1 = a2 andalso recursive_check b1 b2
              | recursive_check (Construction.TCPair ({constructor=("brackets",_), ...}, [_,x,_])) y = recursive_check x y
              | recursive_check x (Construction.TCPair ({constructor=("brackets",_), ...}, [_,y,_])) = recursive_check x y
              | recursive_check (Construction.TCPair ({constructor=("equality",_), ...}, [x1,_,y1])) (Construction.TCPair ({constructor=("equality",_), ...}, [x2,_,y2])) = recursive_check x1 x2 andalso recursive_check y1 y2
              | recursive_check _ _ = false;
            val result = recursive_check x y;
        in
            result
        end;
    
    fun contains_superset l y = (List.exists (fn x => is_superset x y) l);
    
    fun equations_3 l : Construction.construction list = 
        let val es = equations_2 l;
            val ces = Seq.filter (check_equality) es;
            val eq_2 = (#1 o Seq.chop 10000000) ces;
        in
            List.foldl (fn (x,ys) => if contains_superset ys x then ys else (x::ys)) [] eq_2
        end
    
    fun test_3 l = List.length (List.map (PolyML.print o print_equation) (equations_3 l));
end