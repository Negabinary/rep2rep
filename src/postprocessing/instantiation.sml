import "util.sequence";
import "postprocessing.geometry";

signature INSTANTIATION = 
sig
    val instantiate : (string * CSpace.token) list -> (CSpace.token * CSpace.token) list -> Construction.construction -> Geometry.construction Seq.seq;
    val multiply_sequences : 'a Seq.seq list -> 'a list Seq.seq
end

structure Instantiation : INSTANTIATION =
struct
    exception InstantiationException of string;

    datatype isomorphism = LineIso of Geometry.line_con -> Geometry.line_con
                         | AngleIso of Geometry.angle_con -> Geometry.angle_con
                         | RectIso of Geometry.rect_con -> Geometry.rect_con;

    fun apply_iso iso con = case (iso, con) of
          (LineIso(f), Geometry.LineCon(l)) => Geometry.LineCon(f l)
        | (AngleIso(f), Geometry.AngleCon(l)) => Geometry.AngleCon(f l)
        | (RectIso(f), Geometry.RectCon(l)) => Geometry.RectCon(f l)
        | _ => raise InstantiationException "isomorphism / geometry type mismatch";

    val line_sequence = Seq.of_list [
        LineIso(fn cons => cons),
        LineIso(fn cons => Geometry.Reverse (cons)),
        LineIso(fn cons => Geometry.Rotate (cons, Geometry.RootAngle(ref NONE, ref NONE, ref NONE))),
        LineIso(fn cons => Geometry.Reverse (Geometry.Rotate (cons, Geometry.RootAngle(ref NONE, ref NONE, ref NONE)))),
        LineIso(fn cons => Geometry.MoveLine (cons, Geometry.RootLine(ref NONE, ref NONE))),
        LineIso(fn cons => Geometry.Reverse (Geometry.MoveLine (cons, Geometry.RootLine(ref NONE, ref NONE))))
        (*TODO: Complete sequence*)
    ];

    val angle_sequence = Seq.of_list [
        AngleIso(fn cons => cons),
        AngleIso(fn cons => Geometry.ReverseAngle (cons)),
        AngleIso(fn cons => Geometry.MoveAngle (cons, Geometry.RootLine(ref NONE, ref NONE))),
        AngleIso(fn cons => Geometry.OppositeAngle (cons)),
        AngleIso(fn cons => (Geometry.ReverseAngle o Geometry.MoveAngle) (cons, Geometry.RootLine(ref NONE, ref NONE)))
        (*TODO: Complete sequence*)
    ]

    val rect_sequence = Seq.of_list [
        RectIso(fn cons => cons),
        RectIso(fn cons => Geometry.NextRect (cons)),
        RectIso(fn cons => (Geometry.NextRect o Geometry.NextRect) (cons)),
        RectIso(fn cons => (Geometry.NextRect o Geometry.NextRect o Geometry.NextRect) (cons)),
        RectIso(fn cons => Geometry.MoveRect (cons, Geometry.RootLine(ref NONE, ref NONE))),
        RectIso(fn cons => (Geometry.NextRect o Geometry.MoveRect) (cons, Geometry.RootLine(ref NONE, ref NONE))),
        RectIso(fn cons => (Geometry.NextRect o Geometry.NextRect o Geometry.MoveRect) (cons, Geometry.RootLine(ref NONE, ref NONE))),
        RectIso(fn cons => (Geometry.NextRect o Geometry.NextRect o Geometry.NextRect o Geometry.MoveRect) (cons, Geometry.RootLine(ref NONE, ref NONE)))
    ]

    fun geom_to_iso_hack (Geometry.LineCon x) = LineIso(fn _ => x)
      | geom_to_iso_hack (Geometry.AngleCon x) = AngleIso(fn _ => x)
      | geom_to_iso_hack (Geometry.RectCon x) = RectIso(fn _ => x);
    
    fun iso_to_geom_hack (LineIso f) = Geometry.LineCon (f (Geometry.RootLine(ref NONE, ref NONE)))
      | iso_to_geom_hack (AngleIso f) = Geometry.AngleCon (f (Geometry.RootAngle(ref NONE, ref NONE, ref NONE)))
      | iso_to_geom_hack (RectIso f) = Geometry.RectCon (f (Geometry.RootRect(ref NONE, ref NONE, ref NONE)));

    fun multiply_sequences (sequences: 'a Seq.seq list) : 'a list Seq.seq = 
        let fun enumerate (n:int) (st:'a Seq.seq) (seq:'a Seq.seq) : ('a * 'a Seq.seq * int) Seq.seq = 
                    Seq.make (fn () => case Seq.pull seq of NONE => NONE | SOME(hd,tl) => SOME((hd, st, n), enumerate (n + 1) st tl));
            val enumerated : ('a * 'a Seq.seq * int) Seq.seq list = 
                    List.map (fn seq => enumerate 0 seq seq) sequences;
            fun increment ((hd,st,n),tl) max =
                if n < max then
                    case Seq.pull tl of
                        SOME(x) => (x, false)
                      | NONE => (Basics.the (Seq.pull (enumerate 0 st st)), true)
                else
                    (Basics.the(Seq.pull (enumerate 0 st st)), true);
            fun increment_all [] max = ([], true)
              | increment_all (x::xs) max = 
                    case increment x max of
                        (v, false) => (v::xs, false)
                      | (v, true) => case increment_all xs max of
                            (vs, false) => (v::vs, false)
                          | (vs, true) => (x::xs, true);
            fun any_left [] = false
              | any_left (x::xs) =
                    case Seq.pull (#2 x) of
                        NONE => any_left xs
                      | SOME(_) => true
            fun next (xs, max) = case increment_all xs max of
                (vs, false) => SOME(vs, max)
              | (vs, true) => if any_left xs then next(xs, max + 1) else NONE;  (*could include a check here for finite product*)
            fun nextSeq x = case next x of
                NONE => Seq.make (fn () => SOME (x, Seq.empty))
              | SOME(v) => Seq.make (fn () => SOME (x, nextSeq (v)));
            val annotated = nextSeq (List.map (Basics.the o Seq.pull) enumerated, 1);
        in
            Seq.map
                (fn s => List.map (#1 o #1) (#1 s)) 
                (annotated)
        end;

    
    
    
    
    fun instantiate keep_tokens replacements construction = 
        let fun sequence_for token = case Type.nameOfType (CSpace.typeOfToken token) of
                "line" => line_sequence
              | "rect" => rect_sequence
              | "angle" => angle_sequence
              | x => raise InstantiationException ("Unexpected type for isomorphism: " ^ x);
            fun make_input variable token = case CSpace.typeOfToken token of
                "line" => 
                    let val start = ref NONE;
                        val direction = ref NONE;
                        val distance = ref (SOME(Geometry.Value variable));
                    in
                        Geometry.LineCon(Geometry.RootLine(start, ref (SOME(Geometry.Move(start, direction, distance)))))
                    end
              | "rect" =>
                    let val start = ref NONE;
                        val r_end = ref NONE;
                        val distance = ref (SOME(Geometry.Distance(start,r_end)));
                        val area = ref (SOME(Geometry.Value variable));
                        val width = ref (SOME(Geometry.Divide(area, distance)));
                    in
                        Geometry.RectCon(Geometry.RootRect(start, r_end, width))
                    end
              | "angle" => 
                    let val center = ref NONE;
                        val from = ref NONE;
                        val dir_1 = ref (SOME(Geometry.Direction(center, from)));
                        val dir_2 = ref (SOME(Geometry.RDir(dir_1, variable)));
                        val p_to = ref (SOME(Geometry.Move(center, dir_2, ref NONE)));
                    in
                        Geometry.AngleCon(Geometry.RootAngle(from, center, p_to))
                    end
              | _ => raise InstantiationException ("Variable has unexpected type " ^ CSpace.typeOfToken token);
            val inputs_geom = List.map (fn (variable, token) => (token, make_input variable token)) keep_tokens;
            fun geom_from_source token = (
                    case List.find (fn (x,y) => x = token) inputs_geom of
                        SOME((x,y)) => y
                      | NONE => (
                            case List.find (fn (t1,t2) => t1 = token) replacements of
                                  SOME((t1,t2)) => geom_from_source t2
                                | NONE => Geometry.mk_leaf (CSpace.typeOfToken token)
                      )
                );
            fun mkseq (keep_tokens:(string * CSpace.token) list) (replacements:(CSpace.token * CSpace.token) list) (Construction.Reference(token)) = raise InstantiationException "Expected input construction to be a tree!"
              | mkseq (keep_tokens:(string * CSpace.token) list) (replacements:(CSpace.token * CSpace.token) list) (Construction.Source(token)) = Seq.map (fn x => apply_iso x (geom_from_source token)) (sequence_for token)
              | mkseq (keep_tokens:(string * CSpace.token) list) (replacements:(CSpace.token * CSpace.token) list) (Construction.TCPair({token=token, constructor=constructor}, children)) = 
                  let val root_seq = sequence_for token;
                      val child_seqs = List.map (Seq.map geom_to_iso_hack o mkseq keep_tokens replacements) children;
                      val mult_seq = multiply_sequences (root_seq :: child_seqs);
                      fun build_con (r::xs : isomorphism list) = apply_iso r (case (CSpace.nameOfConstructor constructor, List.map iso_to_geom_hack xs) of 
                            ("concat", [Geometry.LineCon(l1), Geometry.LineCon(l2)]) => Geometry.LineCon(Geometry.Concat(l1,l2))
                          | ("similarTriangle", [Geometry.LineCon(l1), Geometry.LineCon(l2), Geometry.LineCon(l3)]) => Geometry.LineCon(Geometry.SimilarTriangle(l1,l2,l3))
                          | ("mkrect", [Geometry.LineCon(l1), Geometry.LineCon(l2)]) => Geometry.RectCon(Geometry.MKRect(l1, l2))
                          | ("divrect", [Geometry.RectCon(r1), Geometry.LineCon(l2)]) => Geometry.LineCon(Geometry.DivRect(r1,l2))
                          | ("joinrect", [Geometry.RectCon(r1), Geometry.RectCon(r2)]) => Geometry.RectCon(Geometry.JoinRect(r1, r2))
                          | ("subrect", [Geometry.RectCon(r1), Geometry.RectCon(r2)]) => Geometry.RectCon(Geometry.SubRect(r1, r2))
                          | ("sine", [Geometry.LineCon(l1), Geometry.AngleCon(a2)]) => Geometry.LineCon(Geometry.Sine(l1, a2))
                          | ("cosine", [Geometry.LineCon(l1), Geometry.AngleCon(a2)]) => Geometry.LineCon(Geometry.Cosine(l1, a2))
                          | ("tangent", [Geometry.LineCon(l1), Geometry.AngleCon(a2)]) => Geometry.LineCon(Geometry.Tangent(l1, a2))
                          | ("anglebetween", [Geometry.LineCon(l1), Geometry.LineCon(l2)]) => Geometry.AngleCon(Geometry.AngleBetween(l1, l2))
                          | ("joinangle", [Geometry.AngleCon(a1), Geometry.AngleCon(a2)]) => Geometry.AngleCon(Geometry.JoinAngle(a1, a2))
                          | ("subangle", [Geometry.AngleCon(a1), Geometry.AngleCon(a2)]) => Geometry.AngleCon(Geometry.SubAngle(a1, a2))
                          | ("reverseline", [Geometry.LineCon(l1)]) => Geometry.LineCon(Geometry.Reverse(l1))
                          | ("rotateline", [Geometry.LineCon(l1), Geometry.AngleCon(a2)]) => Geometry.LineCon(Geometry.Rotate(l1, a2))
                          | ("moveline", [Geometry.LineCon(l1), Geometry.LineCon(l2)]) => Geometry.LineCon(Geometry.MoveLine(l1, l2))
                          | ("reverseangle", [Geometry.AngleCon(a1)]) => Geometry.AngleCon(Geometry.ReverseAngle(a1))
                          | ("oppositeangle", [Geometry.AngleCon(a1)]) => Geometry.AngleCon(Geometry.OppositeAngle(a1))
                          | ("nextRect", [Geometry.RectCon(r1)]) => Geometry.RectCon(Geometry.NextRect(r1))
                          | ("moveRect", [Geometry.RectCon(r1), Geometry.LineCon(l2)]) => Geometry.RectCon(Geometry.MoveRect(r1, l2))
                          | ("resolveLine", [Geometry.LineCon(l1), Geometry.LineCon(l2)]) => Geometry.LineCon(Geometry.ResolveLine(l1, l2))
                          | ("resolveAngle", [Geometry.AngleCon(a1), Geometry.AngleCon(a2)]) => Geometry.AngleCon(Geometry.ResolveAngle(a1,a2))
                          | ("resolveArea", [Geometry.RectCon(r1), Geometry.RectCon(r2)]) => Geometry.RectCon(Geometry.ResolveRect(r1,r2))
                          | (x,y) => raise InstantiationException ("unexpected constructor '" ^ x ^ "'' in instantiation")
                          )
                        | build_con [] = raise InstantiationException ("Error: construction without root");
                  in
                    Seq.map build_con mult_seq
                  end;
            val Construction.TCPair(_, [lhs, rhs]) = construction;
            val lhseq = mkseq keep_tokens replacements lhs;
            val rhseq = mkseq keep_tokens replacements rhs;
            val rhisos = sequence_for (Construction.constructOf rhs);
      in
        Seq.map (fn [rh,rt,l] => Geometry.resolve (iso_to_geom_hack l) (apply_iso rh (iso_to_geom_hack rt)) | _ => raise InstantiationException "Error") (multiply_sequences [rhisos, Seq.map geom_to_iso_hack rhseq, Seq.map geom_to_iso_hack lhseq])
      end

    (*
    fun instantiate (construction:Construction.construction) (keep_tokens:(string * CSpace.token) list) (replacements:(CSpace.token * CSpace.token) list) = 
        let fun make_input variable token = case CSpace.typeOfToken token of
                "line" => 
                    let val start = ref NONE;
                        val direction = ref NONE;
                        val distance = ref (SOME(Geometry.Value variable));
                    in
                        Geometry.LineCon(Geometry.RootLine(start, ref (SOME(Geometry.Move(start, direction, distance)))))
                    end
              | "rect" =>
                    let val start = ref NONE;
                        val r_end = ref NONE;
                        val distance = ref (SOME(Geometry.Distance(start,r_end)));
                        val area = ref (SOME(Geometry.Value variable));
                        val width = ref (SOME(Geometry.Divide(area, distance)));
                    in
                        Geometry.RectCon(Geometry.RootRect(start, r_end, width))
                    end
              | "angle" => 
                    let val center = ref NONE;
                        val from = ref NONE;
                        val dir_1 = ref (SOME(Geometry.Direction(center, from)));
                        val dir_2 = ref (SOME(Geometry.RDir(dir_1, variable)));
                        val p_to = ref (SOME(Geometry.Move(center, dir_2, ref NONE)));
                    in
                        Geometry.AngleCon(Geometry.RootAngle(from, center, p_to))
                    end
              | _ => raise InstantiationException ("Variable has unexpected type " ^ CSpace.typeOfToken token);
            fun sequence_for token = case Type.nameOfType (CSpace.typeOfToken token) of
                "line" => line_sequence
              | "rect" => rect_sequence
              | "angle" => angle_sequence
              | x => raise InstantiationException ("Unexpected type for isomorphism: " ^ x);
            val root_sequence = sequence_for (Construction.constructOf construction);
            val sequences = root_sequence :: (List.map (sequence_for o #2) replacements);
            val all_possibilities = multiply_sequences sequences;
            fun instantiate_possibility [] = raise InstantiationException "This should never be raised!"
              | instantiate_possibility (root_iso::var_isos) = 
                let fun zip [] [] = []
                      | zip (c::cs) (b::bs) = (c,b) :: (zip cs bs)
                      | zip _ _ = raise InstantiationException "Failed zip?"
                    val var_iso_map = zip replacements var_isos;
                    val Construction.TCPair(_, [lhs, rhs]) = construction;
                    val inputs_geom = List.map (fn (variable, token) => (token, make_input variable token)) keep_tokens;
                    fun build (Construction.TCPair({token=token, constructor=constructor}, children)) = (
                        case (CSpace.nameOfConstructor constructor, List.map build children) of 
                            ("concat", [Geometry.LineCon(l1), Geometry.LineCon(l2)]) => Geometry.LineCon(Geometry.Concat(l1,l2))
                          | ("similarTriangle", [Geometry.LineCon(l1), Geometry.LineCon(l2), Geometry.LineCon(l3)]) => Geometry.LineCon(Geometry.SimilarTriangle(l1,l2,l3))
                          | ("mkrect", [Geometry.LineCon(l1), Geometry.LineCon(l2)]) => Geometry.RectCon(Geometry.MKRect(l1, l2))
                          | ("divrect", [Geometry.RectCon(r1), Geometry.LineCon(l2)]) => Geometry.LineCon(Geometry.DivRect(r1,l2))
                          | ("joinrect", [Geometry.RectCon(r1), Geometry.RectCon(r2)]) => Geometry.RectCon(Geometry.JoinRect(r1, r2))
                          | ("subrect", [Geometry.RectCon(r1), Geometry.RectCon(r2)]) => Geometry.RectCon(Geometry.SubRect(r1, r2))
                          | ("sine", [Geometry.LineCon(l1), Geometry.AngleCon(a2)]) => Geometry.LineCon(Geometry.Sine(l1, a2))
                          | ("cosine", [Geometry.LineCon(l1), Geometry.AngleCon(a2)]) => Geometry.LineCon(Geometry.Cosine(l1, a2))
                          | ("tangent", [Geometry.LineCon(l1), Geometry.AngleCon(a2)]) => Geometry.LineCon(Geometry.Tangent(l1, a2))
                          | ("anglebetween", [Geometry.LineCon(l1), Geometry.LineCon(l2)]) => Geometry.AngleCon(Geometry.AngleBetween(l1, l2))
                          | ("joinangle", [Geometry.AngleCon(a1), Geometry.AngleCon(a2)]) => Geometry.AngleCon(Geometry.JoinAngle(a1, a2))
                          | ("subangle", [Geometry.AngleCon(a1), Geometry.AngleCon(a2)]) => Geometry.AngleCon(Geometry.SubAngle(a1, a2))
                          | ("reverseline", [Geometry.LineCon(l1)]) => Geometry.LineCon(Geometry.Reverse(l1))
                          | ("rotateline", [Geometry.LineCon(l1), Geometry.AngleCon(a2)]) => Geometry.LineCon(Geometry.Rotate(l1, a2))
                          | ("moveline", [Geometry.LineCon(l1), Geometry.LineCon(l2)]) => Geometry.LineCon(Geometry.MoveLine(l1, l2))
                          | ("reverseangle", [Geometry.AngleCon(a1)]) => Geometry.AngleCon(Geometry.ReverseAngle(a1))
                          | ("oppositeangle", [Geometry.AngleCon(a1)]) => Geometry.AngleCon(Geometry.OppositeAngle(a1))
                          | ("nextRect", [Geometry.RectCon(r1)]) => Geometry.RectCon(Geometry.NextRect(r1))
                          | ("moveRect", [Geometry.RectCon(r1), Geometry.LineCon(l2)]) => Geometry.RectCon(Geometry.MoveRect(r1, l2))
                          | (x,y) => raise InstantiationException ("unexpected constructor '" ^ x ^ "'' in instantiation")
                    )
                      | build (Construction.Source(token)) = (
                            case List.find (fn (x,y) => x = token) inputs_geom of
                                SOME((x,y)) => y
                              | NONE => (
                                    case List.find (fn ((t1,t2),iso) => t1 = token) var_iso_map of
                                         SOME(((t1,t2),iso)) => apply_iso iso (#2 (Basics.the (List.find (fn (p,q) => p = t2) inputs_geom)))
                                       | NONE => Geometry.mk_leaf (CSpace.typeOfToken token)
                              )
                        )
                      | build (Construction.Reference(token)) = raise InstantiationException "Expected input construction to be a tree!";
                    val built_lhs = build lhs;
                    val built_rhs = apply_iso root_iso (build rhs);
                in
                    Geometry.resolve built_lhs built_rhs
                end;
        in
            Seq.map instantiate_possibility all_possibilities
        end
        *)
end