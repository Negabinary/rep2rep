import "util.sequence";
import "postprocessing.geometry";

signature INSTANTIATION = 
sig
    val instantiate : Construction.construction -> (string * CSpace.token) list -> (CSpace.token * CSpace.token) list -> Geometry.construction Seq.seq;
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
        LineIso(fn cons => Geometry.Rotate (cons, Geometry.RootAngle(ref NONE, ref NONE, ref NONE)))
    ];

    val angle_sequence = Seq.of_list [
        AngleIso(fn cons => cons)
    ]

    val rect_sequence = Seq.of_list [
        RectIso(fn cons => cons)
    ]

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
            val inputs_geom = List.map (fn (variable, token) => (token, make_input variable token)) keep_tokens;
            fun sequence_for token = case CSpace.typeOfToken token of
                "line" => line_sequence
              | "rect" => rect_sequence
              | "angle" => angle_sequence
              | _ => raise InstantiationException "Unexpected type for isomorphism!";
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
                    fun build (Construction.TCPair({token=token, constructor=constructor}, children)) = (
                        case (CSpace.nameOfConstructor constructor, List.map build children) of 
                            ("concat", [Geometry.LineCon(l1), Geometry.LineCon(l2)]) => Geometry.LineCon(Geometry.Concat(l1,l2))
                          | ("similarTriangle", [Geometry.LineCon(l1), Geometry.LineCon(l2), Geometry.LineCon(l3)]) => Geometry.LineCon(Geometry.SimilarTriangle(l1,l2,l3))
                          | ("mkrect", [Geometry.LineCon(l1), Geometry.LineCon(l2)]) => Geometry.RectCon(Geometry.MKRect(l1, l2))
                          | ("divrect", [Geometry.RectCon(r1), Geometry.LineCon(l2)]) => Geometry.LineCon(Geometry.DivRect(r1,l2))
                          | ("joinrect", [Geometry.RectCon(r1), Geometry.RectCon(r2)]) => Geometry.RectCon(Geometry.JoinRect(r1, r2))
                          | ("subrect", [Geometry.RectCon(r1), Geometry.RectCon(r2)]) => Geometry.RectCon(Geometry.SubRect(r1, r2))
                          | (x,y) => raise InstantiationException ("unexpected constructor '" ^ x ^ "'' in instantiation")
                          (* TODO: Add the rest of the correspondences *)
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
end