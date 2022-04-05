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
        LineIso(fn cons => Geometry.Rotate (cons, Geometry.RootAngle(ref NONE, ref NONE, ref NONE)))
        ,
        LineIso(fn cons => Geometry.Reverse (Geometry.Rotate (cons, Geometry.RootAngle(ref NONE, ref NONE, ref NONE)))),
        LineIso(fn cons => Geometry.MoveLine (cons, Geometry.RootLine(ref NONE, ref NONE))),
        LineIso(fn cons => Geometry.Reverse (Geometry.MoveLine (cons, Geometry.RootLine(ref NONE, ref NONE))))
        (* TODO: Complete sequence *)
    ];

    val angle_sequence = Seq.of_list [
        AngleIso(fn cons => cons) 
        ,
        AngleIso(fn cons => Geometry.ReverseAngle (cons)),
        AngleIso(fn cons => Geometry.OppositeAngle (cons)),
        AngleIso(fn cons => Geometry.MoveAngle (cons, Geometry.RootLine(ref NONE, ref NONE))),
        AngleIso(fn cons => (Geometry.ReverseAngle o Geometry.MoveAngle) (cons, Geometry.RootLine(ref NONE, ref NONE))),
        AngleIso(fn cons => (Geometry.ReverseAngle o Geometry.OppositeAngle) (cons)),
        AngleIso(fn cons => (Geometry.OppositeAngle o Geometry.MoveAngle) (cons, Geometry.RootLine(ref NONE, ref NONE))),
        AngleIso(fn cons => (Geometry.ReverseAngle o Geometry.OppositeAngle o Geometry.MoveAngle) (cons, Geometry.RootLine(ref NONE, ref NONE)))
        (*TODO: Complete sequence*)
    ]

    val rect_sequence = Seq.of_list [
        RectIso(fn cons => cons)
        ,
        RectIso(fn cons => Geometry.NextRect (cons)),
        RectIso(fn cons => (Geometry.NextRect o Geometry.NextRect) (cons)),
        RectIso(fn cons => (Geometry.NextRect o Geometry.NextRect o Geometry.NextRect) (cons)),
        RectIso(fn cons => Geometry.MoveRect (cons, Geometry.RootLine(ref NONE, ref NONE))),
        RectIso(fn cons => (Geometry.NextRect o Geometry.MoveRect) (cons, Geometry.RootLine(ref NONE, ref NONE))),
        RectIso(fn cons => (Geometry.NextRect o Geometry.NextRect o Geometry.MoveRect) (cons, Geometry.RootLine(ref NONE, ref NONE))),
        RectIso(fn cons => (Geometry.NextRect o Geometry.NextRect o Geometry.NextRect o Geometry.MoveRect) (cons, Geometry.RootLine(ref NONE, ref NONE)))
    ]

    fun rep2rep_to_ml keep_tokens replacements construction =
        let
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
            fun rec_rep2rep_to_ml (Construction.Reference(token)) = raise InstantiationException "Expected input construction to be a tree!"
              | rec_rep2rep_to_ml (Construction.Source(token)) = geom_from_source token
              | rec_rep2rep_to_ml (Construction.TCPair({token=token, constructor=constructor}, children)) = 
                    (case (CSpace.nameOfConstructor constructor, List.map rec_rep2rep_to_ml children) of 
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
                        | ("pythag", [Geometry.LineCon(l1), Geometry.LineCon(l2)]) => Geometry.RectCon(Geometry.Pythag(l1,l2))
                        | (x,y) => raise InstantiationException ("unexpected constructor '" ^ x ^ "'' in instantiation")
                  )
        in
            rec_rep2rep_to_ml construction
        end
      
      fun gen_lists con = 
          let open Geometry;
              val seen_roots = ref [];
              fun seen x = List.exists (fn y => y = x) (!seen_roots);
              fun see x = seen_roots := x :: (!seen_roots);
              fun gen_lists_rec_line (l as RootLine(_,_)) = (if seen (LineCon l) then [Seq.of_list [LineIso(fn cons => cons)]] else (see (LineCon l); [line_sequence]))
                | gen_lists_rec_line line = (case line of
                      ResolveLine(l1,l2) => gen_lists_rec_line l1 @ gen_lists_rec_line l2
                    | Concat(l1,l2) => gen_lists_rec_line l1 @ gen_lists_rec_line l2
                    | SimilarTriangle(l1,l2,l3) => gen_lists_rec_line l1 @ gen_lists_rec_line l2 @ gen_lists_rec_line l3
                    | DivRect(r1,l2) => gen_lists_rec_rect r1 @ gen_lists_rec_line l2
                    | Reverse(l1) => gen_lists_rec_line l1
                    | Rotate(l1,a2) => gen_lists_rec_line l1 @ gen_lists_rec_angle a2
                    | Sine(l1,a2) => gen_lists_rec_line l1 @ gen_lists_rec_angle a2
                    | Cosine(l1,a2) => gen_lists_rec_line l1 @ gen_lists_rec_angle a2
                    | Tangent(l1,a2) => gen_lists_rec_line l1 @ gen_lists_rec_angle a2
                    | MoveLine(l1,l2) => gen_lists_rec_line l1 @ gen_lists_rec_line l2
                    | RootLine(_,_) => [] (*Case shouldn't occur*)
              ) @ [line_sequence]
              and gen_lists_rec_angle (a as RootAngle(_,_,_)) = (if seen (AngleCon a) then [Seq.of_list [AngleIso(fn cons => cons)]] else (see (AngleCon a); [angle_sequence]))
                | gen_lists_rec_angle angle = (case angle of
                      ResolveAngle(a1,a2) => gen_lists_rec_angle a1 @ gen_lists_rec_angle a2
                    | AngleBetween(l1,l2) => gen_lists_rec_line l1 @ gen_lists_rec_line l2
                    | JoinAngle(a1,a2) => gen_lists_rec_angle a1 @ gen_lists_rec_angle a2
                    | SubAngle(a1,a2) => gen_lists_rec_angle a1 @ gen_lists_rec_angle a2
                    | ReverseAngle(a1) => gen_lists_rec_angle a1
                    | MoveAngle(a1,l2) => gen_lists_rec_angle a1 @ gen_lists_rec_line l2
                    | OppositeAngle(a1) => gen_lists_rec_angle a1
                    | RootAngle(_,_,_) => [] (*Case shouldn't occur*)
                ) @ [angle_sequence]
              and gen_lists_rec_rect (r as RootRect(_,_,_)) = (if seen (RectCon r) then [Seq.of_list [RectIso(fn cons => cons)]] else (see (RectCon r); [rect_sequence]))
                | gen_lists_rec_rect rect = (case rect of
                      ResolveRect(r1,r2) => gen_lists_rec_rect r1 @ gen_lists_rec_rect r2
                    | MKRect(l1,l2) => gen_lists_rec_line l1 @ gen_lists_rec_line l2
                    | JoinRect(r1,r2) => gen_lists_rec_rect r1 @ gen_lists_rec_rect r2
                    | SubRect(r1,r2) => gen_lists_rec_rect r1 @ gen_lists_rec_rect r2
                    | NextRect(r1) => gen_lists_rec_rect r1
                    | MoveRect(r1,l2) => gen_lists_rec_rect r1 @ gen_lists_rec_line l2
                    | Pythag(l1,l2) => gen_lists_rec_line l1 @ gen_lists_rec_line l2
                    | RootRect(_,_,_) => [] (*Case shouldn't occur*)
                ) @ [rect_sequence];
          in
              case con of
                  LineCon(x) => gen_lists_rec_line x
                | AngleCon(x) => gen_lists_rec_angle x
                | RectCon(x) => gen_lists_rec_rect x
          end;
    
    fun use_isos con isos =
        let open Geometry
            val risos = ref isos;
            fun pop_iso () = (case (!risos) of [] => raise InstantiationException "Wrong number of isos!" | (x::xs) => (risos := xs; x));
            fun w () = raise (InstantiationException "Unexpected type in variation!")
            fun apl l = (case pop_iso () of LineIso x => x | _ => w()) l; 
            fun apa a = (case pop_iso () of AngleIso x => x | _ => w()) a; 
            fun apr r = (case pop_iso () of RectIso x => x | _ => w()) r;
            fun use_lists_rec_line (ResolveLine(l1, l2)) = apl (ResolveLine(use_lists_rec_line l1, use_lists_rec_line l2))
              | use_lists_rec_line (Concat(l1, l2)) = apl (Concat(use_lists_rec_line l1, use_lists_rec_line l2))
              | use_lists_rec_line (SimilarTriangle(l1,l2,l3)) = apl (SimilarTriangle(use_lists_rec_line l1, use_lists_rec_line l2, use_lists_rec_line l3))
              | use_lists_rec_line (DivRect(r1,l2)) = apl (DivRect(use_lists_rec_rect r1, use_lists_rec_line l2))
              | use_lists_rec_line (Reverse(l1)) = apl (Reverse(use_lists_rec_line l1))
              | use_lists_rec_line (Rotate(l1,a2)) = apl (Rotate(use_lists_rec_line l1, use_lists_rec_angle a2))
              | use_lists_rec_line (Sine(l1,a2)) = apl (Sine(use_lists_rec_line l1, use_lists_rec_angle a2))
              | use_lists_rec_line (Cosine(l1,a2)) = apl (Cosine(use_lists_rec_line l1, use_lists_rec_angle a2))
              | use_lists_rec_line (Tangent(l1,a2)) = apl (Tangent(use_lists_rec_line l1, use_lists_rec_angle a2))
              | use_lists_rec_line (MoveLine(l1,l2)) = apl (MoveLine(use_lists_rec_line l1, use_lists_rec_line l2))
              | use_lists_rec_line (RootLine(x,y)) = apl (RootLine(x,y))
            and use_lists_rec_angle (ResolveAngle(a1,a2)) = apa (ResolveAngle(use_lists_rec_angle a1, use_lists_rec_angle a2))
              | use_lists_rec_angle (AngleBetween(l1,l2)) = apa (AngleBetween(use_lists_rec_line l1, use_lists_rec_line l2))
              | use_lists_rec_angle (JoinAngle(a1,a2)) = apa (JoinAngle(use_lists_rec_angle a1, use_lists_rec_angle a2))
              | use_lists_rec_angle (SubAngle(a1,a2)) = apa (SubAngle(use_lists_rec_angle a1, use_lists_rec_angle a2))
              | use_lists_rec_angle (ReverseAngle(a1)) = apa (ReverseAngle(use_lists_rec_angle a1))
              | use_lists_rec_angle (MoveAngle(a1,l2)) = apa (MoveAngle(use_lists_rec_angle a1, use_lists_rec_line l2))
              | use_lists_rec_angle (OppositeAngle(a1)) = apa (OppositeAngle(use_lists_rec_angle a1))
              | use_lists_rec_angle (RootAngle(x,y,z)) = apa (RootAngle(x,y,z))
            and use_lists_rec_rect (RootRect(x,y,z)) = apr (RootRect(x,y,z))
              | use_lists_rec_rect (ResolveRect(r1,r2)) = apr (ResolveRect(use_lists_rec_rect r1, use_lists_rec_rect r2))
              | use_lists_rec_rect (MKRect(l1, l2)) = apr (MKRect(use_lists_rec_line l1, use_lists_rec_line l2))
              | use_lists_rec_rect (JoinRect(r1, r2)) = apr (JoinRect(use_lists_rec_rect r1, use_lists_rec_rect r2))
              | use_lists_rec_rect (SubRect(r1, r2)) = apr (SubRect(use_lists_rec_rect r1, use_lists_rec_rect r2))
              | use_lists_rec_rect (NextRect(r1)) = apr (NextRect(use_lists_rec_rect r1))
              | use_lists_rec_rect (MoveRect(r1,l2)) = apr (MoveRect(use_lists_rec_rect r1, use_lists_rec_line l2))
              | use_lists_rec_rect (Pythag(l1,l2)) = apr (Pythag(use_lists_rec_line l1, use_lists_rec_line l2))
        in
            case con of
                LineCon(x) => LineCon(use_lists_rec_line (x))
              | AngleCon(x) => AngleCon(use_lists_rec_angle (x))
              | RectCon(x) => RectCon(use_lists_rec_rect (x))
        end

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
      let val ml_rep = rep2rep_to_ml keep_tokens replacements construction;
          val seqs = gen_lists ml_rep;
          val counts = (List.map (List.length o Seq.list_of) seqs);
          (* val types = PolyML.print (List.map (fn x => case Seq.hd x of RectIso y => "Rect" | AngleIso y => "Angle" | LineIso y => "Line") seqs) *)
          val count = List.foldr (op *) 1 counts;
          val _ = print ((Int.toString count) ^ " variations available. \n");
          val multiplied = multiply_sequences seqs;
          val variations = Seq.map (use_isos ml_rep) multiplied;
      in
          variations
      end
end