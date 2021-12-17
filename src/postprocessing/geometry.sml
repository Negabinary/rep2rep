(* : TODO signature*)
structure Geometry = 
struct
    val counter = ref 0;
    fun unique_name () = (counter := !counter + 1; "g" ^ (PolyML.makestring (!counter)));

    exception GeometryError of string;

    datatype point_con = Move of point_con option ref * direction_con option ref * distance_con option ref
                       | PCopy of point_con option ref
     and direction_con = Direction of point_con option ref * point_con option ref
                       | RDir of direction_con option ref * string
                       | Right of direction_con option ref
                       | DCopy of direction_con option ref
      and distance_con = Distance of point_con option ref * point_con option ref
                       | Times of distance_con option ref * distance_con option ref
                       | Divide of distance_con option ref * distance_con option ref
                       | Value of string
                       | SCopy of distance_con option ref;
    
    datatype relation = SamePoint of point_con option ref * point_con option ref
                      | SameDirection of direction_con option ref * direction_con option ref
                      | sameDistance of distance_con option ref * distance_con option ref

    datatype line_con = RootLine of point_con option ref * point_con option ref
                      | ResolveLine of line_con * line_con
                      | Concat of line_con * line_con
                      | SimilarTriangle of line_con * line_con * line_con
                      | DivRect of rect_con * line_con
                      | Reverse of line_con
                      | Rotate of line_con * angle_con
        and angle_con = RootAngle of point_con option ref * point_con option ref * point_con option ref
                      | ResolveAngle of angle_con * angle_con
                      | AngleBetween of line_con * line_con
                      | JoinAngle of angle_con * angle_con
                      | SubAngle of angle_con * angle_con
         and rect_con = RootRect of point_con option ref * point_con option ref * distance_con option ref
                      | ResolveRect of rect_con * rect_con
                      | MKRect of line_con * line_con
                      | JoinRect of rect_con * rect_con
                      | SubRect of rect_con * rect_con;
    
    datatype construction = LineCon of line_con | AngleCon of angle_con | RectCon of rect_con;

    fun mk_leaf_line () = LineCon(RootLine(ref NONE, ref NONE));
    fun mk_leaf_angle () = AngleCon(RootAngle(ref NONE, ref NONE, ref NONE));
    fun mk_leaf_rect () = RectCon(RootRect(ref NONE, ref NONE, ref NONE));

    fun mk_leaf typestring = case typestring of
            "line" => mk_leaf_line ()
          | "angle" => mk_leaf_angle ()
          | "rect" => mk_leaf_rect ()
          | _ => raise GeometryError "Not a valid type"
    
    fun resolve lhs rhs = case (lhs, rhs) of
        (LineCon(x),LineCon(y)) => LineCon(ResolveLine(x,y))
      | (AngleCon(x),AngleCon(y)) => AngleCon(ResolveAngle(x,y))
      | (RectCon(x),RectCon(y)) => RectCon(ResolveRect(x,y))
      | _ => raise GeometryError "Resolve type mismatch"
    
    datatype constraint =
        SamePoint of point_con option ref * point_con option ref
      | SameDirection of direction_con option ref * direction_con option ref
      | SameDistsance of distance_con option ref * distance_con option ref
    
    fun get_line_start (RootLine(a,b)) = a
      | get_line_start (ResolveLine(a,b)) = get_line_start a
      | get_line_start (Concat(a,b)) = get_line_start a
      | get_line_start (SimilarTriangle(a,b,c)) = get_line_end c
      | get_line_start (DivRect(r,l)) = get_rect_end r
      | get_line_start (Reverse(l)) = get_line_end l
      | get_line_start (Rotate(l,a)) = get_line_start l

    and get_line_end (RootLine(a,b)) = b
      | get_line_end (ResolveLine(a,b)) = get_line_end a
      | get_line_end (Concat(a,b)) = get_line_end b
      | get_line_end (SimilarTriangle(a,b,c)) = 
        let val A = get_line_start a;
            val B = get_line_end a;
            val C = get_line_start b;
            val D = get_line_end c;
        in
            (ref o SOME o Move) (
                    C,
                    (ref o SOME o Direction) (C,A),
                    (ref o SOME o Divide) (
                        (ref o SOME o Distance) (C,A),
                        (ref o SOME o Times) (
                            (ref o SOME o Distance) (C,B),
                            (ref o SOME o Distance) (C,D)
                        )
                    )
                )
        end
      | get_line_end (DivRect(r,l)) =
        let val A = get_rect_start r;
            val B = get_rect_end r;
            val W = get_rect_width r;
        in
            (ref o SOME o Move) (
                B,
                (ref o SOME o Right) (
                    (ref o SOME o Direction) (A, B)
                ),
                W
            )
        end
      | get_line_end (Reverse(a)) = get_line_start a
      | get_line_end (Rotate(l,a)) = 
        let val A = get_line_start l;
            val B = get_angle_end a;
            val C = get_line_end l;
        in
            (ref o SOME o Move) (
                A,
                (ref o SOME o Direction) (A, B),
                (ref o SOME o Distance) (A,C)
            )
        end
        
    and get_angle_start (RootAngle(a,b,c)) = a
      | get_angle_start (ResolveAngle(a,b)) = get_angle_start a
      | get_angle_start (AngleBetween(a,b)) = get_line_end a
      | get_angle_start (JoinAngle(a,b)) = get_angle_start a
      | get_angle_start (SubAngle(a,b)) = get_angle_start a
    
    and get_angle_middle (RootAngle(a,b,c)) = b
      | get_angle_middle (ResolveAngle(a,b)) = get_angle_middle a
      | get_angle_middle (AngleBetween(a,b)) = get_line_start a
      | get_angle_middle (JoinAngle(a,b)) = get_angle_middle a
      | get_angle_middle (SubAngle(a,b)) = get_angle_middle a
    
    and get_angle_end (RootAngle(a, b,c)) = c
      | get_angle_end (ResolveAngle(a, b)) = get_angle_end a
      | get_angle_end (AngleBetween(a, b)) = get_line_end b
      | get_angle_end (JoinAngle(a, b)) = get_angle_end b
      | get_angle_end (SubAngle(a, b)) = get_angle_start b
    
    and get_rect_start (RootRect(a, b, c)) = a
      | get_rect_start (ResolveRect(a, b)) = get_rect_start a
      | get_rect_start (MKRect(a, b)) = get_line_start a
      | get_rect_start (JoinRect(a, b)) = get_rect_start a
      | get_rect_start (SubRect(a, b)) = get_rect_start a
    
    and get_rect_end (RootRect(a, b, c)) = b
      | get_rect_end (ResolveRect(a, b)) = get_rect_end a
      | get_rect_end (MKRect(a, b)) = get_line_end a
      | get_rect_end (JoinRect(a, b)) = get_rect_end b
      | get_rect_end (SubRect(a, b)) = get_rect_start b
    
    and get_rect_width (RootRect(a, b, c)) = c
      | get_rect_width (ResolveRect(a, b)) = get_rect_width a
      | get_rect_width (MKRect(a, b)) = 
        let val A = get_line_start b;
            val B = get_line_end b;
        in
            (ref o SOME o Distance) (A,B)
        end
      | get_rect_width (JoinRect(a, b)) = get_rect_width a
      | get_rect_width (SubRect(a, b)) = get_rect_width a;

    datatype constraint = PC of point_con option ref * point_con option ref
                        | DC of direction_con option ref * direction_con option ref
                        | SC of distance_con option ref * distance_con option ref;
    
    fun mc (a,b) (c,d) = (a @ c, b @ d);

    fun get_line_constraints line = case line of
        RootLine(a,b) => ([],[PC(a,b)])
      | ResolveLine(a,b) => mc (
          [PC(get_line_start a, get_line_start b), 
          PC(get_line_end a, get_line_end b)], []
        ) (mc (get_line_constraints a) (get_line_constraints b))
      | Concat(a,b) => mc
            (mc (get_line_constraints a) (get_line_constraints b))
            ([
                PC(get_line_end a, get_line_start b),
                DC(
                    (ref o SOME o Direction) (get_line_start a, get_line_end a),
                    (ref o SOME o Direction) (get_line_start b, get_line_end b)
                )
            ], [])
      | SimilarTriangle(a, b, c) => mc
            (mc (get_line_constraints a) (mc (get_line_constraints b) (get_line_constraints c)))
            (
                [
                    PC(get_line_start a, get_line_end b),
                    PC(get_line_start b, get_line_start c),
                    DC(
                        (ref o SOME o Direction) (get_line_start b, get_line_end b),
                        (ref o SOME o Direction) (get_line_start c, get_line_end c)
                    )
                ], []
            )
      | DivRect(r,l) => mc
            (mc (get_rect_constraints r) (get_line_constraints l))
            (
                [
                    PC(get_rect_start r, get_line_start l),
                    PC(get_rect_end r, get_line_end l)
                ], []
            )
      | Reverse(l) => get_line_constraints l
      | Rotate(l, a) => mc
            (mc (get_line_constraints l) (get_angle_constraints a))
            (
                [
                    PC(get_angle_middle a, get_line_start l),
                    PC(get_angle_start a, get_line_end l)
                ], []
            )

    and get_angle_constraints angle = case angle of
        RootAngle(a,b,c) => (
            [], [
                PC(a,b),
                PC(b,c),
                PC(a,c)
            ]
        )
      | ResolveAngle(a,b) => mc
            (mc (get_angle_constraints a) (get_angle_constraints b))
            (
                [
                    PC(get_angle_start a, get_angle_start a),
                    PC(get_angle_middle a, get_angle_middle a),
                    PC(get_angle_end a, get_angle_end a)
                ], []
            )
      | AngleBetween(a,b) => mc
            (mc (get_line_constraints a) (get_line_constraints b))
            (
                [PC(get_line_start a, get_line_start b)],
                [PC(get_line_end a, get_line_end b)]
            )
      | JoinAngle(a,b) => mc
            (mc (get_angle_constraints a) (get_angle_constraints b))
            (
                [PC(get_angle_middle a, get_angle_middle b),PC(get_angle_end a, get_angle_start b)],
                [PC(get_angle_start a, get_angle_end b)]
            )
      | SubAngle(a,b) => mc
            (mc (get_angle_constraints a) (get_angle_constraints b))
            (
                [PC(get_angle_middle a, get_angle_middle b), PC(get_angle_end a, get_angle_end b)],
                [PC(get_angle_start a, get_angle_start b)]
            )
      
    and get_rect_constraints rect = case rect of
        RootRect(a,b,c) => (
            [],[
                PC(a,b)
            ]
        )
      | ResolveRect(a,b) => mc
            (mc (get_rect_constraints a) (get_rect_constraints b))
            ([
                PC(get_rect_start a, get_rect_start a),
                PC(get_rect_end a, get_rect_end b),
                SC(get_rect_width a, get_rect_width b)
            ],[])
      | JoinRect(a,b) => mc
            (mc (get_rect_constraints a) (get_rect_constraints b))
            (
                [
                    SC(get_rect_width a, get_rect_width b),
                    PC(get_rect_end a, get_rect_start b),
                    DC(
                        (ref o SOME o Direction) (get_rect_start a, get_rect_end a),
                        (ref o SOME o Direction) (get_rect_start b, get_rect_end b)
                    )
                ],
                []
            )
      | MKRect(a,b) => mc
            (mc (get_line_constraints a) (get_line_constraints b))
            (
                [
                    PC(get_line_start a, get_line_start b),
                    DC(
                        (ref o SOME o Right) ((ref o SOME o Direction) (get_line_start a, get_line_end a)),
                        (ref o SOME o Direction) (get_line_start b, get_line_end b)
                    )
                ],
                []
            )
      | SubRect(a,b) => mc
            (mc (get_rect_constraints a) (get_rect_constraints b))
            (
                [
                    SC(get_rect_width a, get_rect_width b),
                    PC(get_rect_end a, get_rect_end b),
                    DC(
                        (ref o SOME o Direction) (get_rect_start a, get_rect_end a),
                        (ref o SOME o Direction) (get_rect_start a, get_rect_start b)
                    )
                ],
                [PC(get_rect_start a, get_rect_start b)]
            );
    
    fun get_constraints object = case object of
        LineCon(x) => get_line_constraints(x)
      | AngleCon(x) => get_angle_constraints(x)
      | RectCon(x) => get_rect_constraints(x);

    (*
    fun eq_point (p1, p2) = case (!p1, !p2) of
        (NONE, NONE) => p1 = p2
      | (SOME(Move(x1,y1,z1)),SOME(Move(x2,y2,z2))) => 
            same_point (x1,y1) andalso same_direction (y1,y2) andalso same_distance (z1,z2)
      | _ => false
    and eq_direction (d1, d2) = case (!d1, !d2) of
        (NONE, NONE) => d1 = d2
      | (SOME(Direction()))

    val (sp, sd, ss) = (same_point, same_direction, same_distance);
    *)

    fun use_positive_constraint (PC(p1, p2)) = if p1 = p2 then false else
        (case !p1 of
            NONE => (p1 := (SOME o PCopy) p2; false)
          | SOME(PCopy(p3)) => use_positive_constraint(PC(p3,p2))
          | SOME(Move(b1,d1,s1)) => (case !p2 of
                NONE => (p2 := (SOME o PCopy) p1; false)
              | SOME (PCopy(p3)) => use_positive_constraint (PC(p1,p3))
              | SOME (Move(b2,d2,s1)) => true))
      | use_positive_constraint (DC(d1, d2)) = if d1 = d2 then false else
        (case !d1 of
            NONE => (d1 := (SOME o DCopy) d2; false)
          | SOME (x) => (case !d2 of
                NONE => (d2 := (SOME o DCopy) d1; false)
              | SOME (y) => true))
      | use_positive_constraint (SC(s1, s2)) = if s1 = s2 then false else
        (case !s1 of
            NONE => (s1 := (SOME o SCopy) s2; false)
          | SOME(x) => (case !s2 of
                NONE => (s2 := (SOME o SCopy) s1; false)
              | SOME(y) => true));


end


(*

signature GEOMETRY2 =
sig    
    type relation;
    type equivalence;
    type line_con;
    type angle_con;
    type rect_con;
    type construction;

    val assert_line : construction -> line_con;
    val assert_angle : construction -> angle_con;
    val assert_rect : construction -> rect_con;

    val mk_leaf_line : unit -> construction;
    val mk_leaf_angle : unit -> construction;
    val mk_leaf_rect : unit -> construction;

    val mk_equivalence : construction -> construction -> equivalence

    val make_unit_construction : string -> construction * construction list * relation list * equivalence list;

    val propagate_goals : construction -> relation list -> relation list;
end

structure Geometry2 : GEOMETRY2 =
struct
    val counter = ref 0;
    fun unique_name () = (counter := !counter + 1; "g" ^ (PolyML.makestring (!counter)));

    exception GeometryError of string;

    datatype distance  = Distance of point * point | WidthR of rect
            and point = Point of string | Start of line | End of line | A of angle | B of angle | C of angle | StartR of rect | EndR of rect
            and line = Line of string
            and angle = Angle of string
            and rect  = Rect of string;
    
    datatype relation = SamePoint of point * point
                      | SameDirection of point * point * point * point
                      | RightAngle of point * point * point
                      | Equals of distance * distance
                      | Not of relation;
    
    datatype geometry = GLine of line | GAngle of angle | GRect of rect;
    datatype equivalence = VELine of line * line | VEAngle of angle * angle | VERect of rect * rect;

    datatype line_con = RootLine of line
                      | ResolveLine of line * line_con * line_con
                      | Concat of line * line_con * line_con
                      | SimilarTriangle of line * line_con * line_con * line_con
                      | DivRect of line * rect_con * line_con
                      | Reverse of line * line_con
                      | Rotate of line * line_con * angle_con
        and angle_con = RootAngle of angle
                      | ResolveAngle of angle * angle_con * angle_con
                      | AngleBetween of angle * line_con * line_con
                      | JoinAngle of angle * angle_con * angle_con
                      | SubAngle of angle * angle_con * angle_con
         and rect_con = RootRect of rect
                      | ResolveRect of rect * rect_con * rect_con
                      | MKRect of rect * line_con * line_con
                      | JoinRect of rect * rect_con * rect_con
                      | SubRect of rect * rect_con * rect_con;

    datatype construction = LineCon of line_con | AngleCon of angle_con | RectCon of rect_con;

    fun assert_line c = case c of
        LineCon(x) => x | _ => raise GeometryError "Not a line!";
    fun assert_angle c = case c of
        AngleCon(x) => x | _ => raise GeometryError "Not an angle!";
    fun assert_rect c = case c of
        RectCon(x) => x | _ => raise GeometryError "Not a rect!";
    
    fun get_line lc = case lc of
        RootLine(x) => x | ResolveLine(x, _, _) => x | Concat(x, _, _) => x | SimilarTriangle(x, _, _, _) => x | DivRect(x, _, _) => x | Reverse(x, _) => x | Rotate(x, _, _) => x;
    fun get_angle ac = case ac of
        RootAngle(x) => x | ResolveAngle(x, _, _) => x | AngleBetween(x, _, _) => x | JoinAngle(x, _, _) => x | SubAngle(x, _, _) => x;
    fun get_rect rc = case rc of
        RootRect(x) => x | ResolveRect(x, _, _) => x | MKRect(x, _, _) => x | JoinRect(x, _, _) => x | SubRect(x, _, _) => x;

    fun mk_equivalence c1 c2 = case (c1, c2) of
        (LineCon(x), LineCon(y)) => VELine(get_line x,get_line y)
      | (AngleCon(x), AngleCon(y)) => VEAngle(get_angle x,get_angle y)
      | (RectCon(x), RectCon(y)) => VERect(get_rect x,get_rect y)
      | _ => raise GeometryError "Not same type!";
    
    fun mk_leaf_line () = LineCon(RootLine(Line(unique_name ())));
    fun mk_leaf_angle () = AngleCon(RootAngle(Angle(unique_name ())));
    fun mk_leaf_rect () = RectCon(RootRect(Rect(unique_name ())));

    fun mk_line () = Line(unique_name ());
    fun mk_angle () = Angle(unique_name ());
    fun mk_rect () = Rect(unique_name ());

    fun make_unit_construction s = 
        let _ = ();
        in case s of
            "resolveLine" =>
                let val ml1 = mk_line();
                    val l1 = RootLine(ml1);
                    val ml2 = mk_line();
                    val l2 = RootLine(ml2);
                    val l3 = ResolveLine(mk_line(), l1, l2);
                in 
                    (LineCon(l3), [LineCon(l1),LineCon(l2)], [], [VELine(ml1, ml2)])
                end
          | "resolveArea" =>
                let val ma1 = mk_rect();
                    val a1 = RootRect(ma1);
                    val ma2 = mk_rect();
                    val a2 = RootRect(ma2);
                    val a3 = ResolveRect(mk_rect(), a1, a2);
                in
                    (RectCon(a3), [RectCon(a1),RectCon(a2)], [], [VERect(ma1, ma2)])
                end
          | "resolveAngle" =>
                let val ma1 = mk_angle();
                    val a1 = RootAngle(ma1);
                    val ma2 = mk_angle();
                    val a2 = RootAngle(ma2);
                    val a3 = ResolveAngle(mk_angle(), a1, a2);
                in
                    (AngleCon(a3), [AngleCon(a1),AngleCon(a2)], [], [VEAngle(ma1, ma2)])
                end
          | "concat" =>
                let val ml1 = mk_line();
                    val l1 = RootLine(ml1);
                    val ml2 = mk_line();
                    val l2 = RootLine(ml2);
                    val l3 = Concat(mk_line(), l1, l2);
                in
                    (LineCon(l3), [LineCon(l1),LineCon(l2)], [
                        SamePoint(End(ml1),Start(ml2)),
                        SameDirection(Start(ml1),End(ml1),Start(ml2),End(ml2))
                    ], [])
                end
          | "similarTriangle" => 
                let val ml1 = mk_line();
                    val ml2 = mk_line();
                    val ml3 = mk_line();
                    val ml4 = mk_line();
                    val l1 = RootLine(ml1);
                    val l2 = RootLine(ml2);
                    val l3 = RootLine(ml3);
                    val l4 = SimilarTriangle(ml4, l1, l2, l3);
                in (
                    LineCon(l4), [LineCon(l1), LineCon(l2), LineCon(l3)],
                    [
                        SamePoint(Start(ml2),Start(ml3)),
                        SamePoint(End(ml2),Start(ml1)),
                        SameDirection(Start(ml2),End(ml2),Start(ml3),End(ml3))
                    ], []
                ) end
          | "mkrect" => 
                let val ml1 = mk_line();
                    val ml2 = mk_line();
                    val mr3 = mk_rect();
                    val l1 = RootLine(ml1);
                    val l2 = RootLine(ml2);
                    val r3 = MKRect(mr3, l1, l2);
                in (
                    RectCon(r3), [LineCon(l1), LineCon(l2)],
                    [
                        SamePoint(Start(ml1),Start(ml2)),
                        RightAngle(End(ml1),Start(ml1),End(ml2))
                    ], []
                ) end
          | "divrect" =>
                let val mr1 = mk_rect();
                    val ml2 = mk_line();
                    val ml3 = mk_line();
                    val r1 = RootRect(mr1);
                    val l2 = RootLine(ml2);
                    val l3 = DivRect(ml3,r1,l2);
                in (
                    LineCon(l3), [RectCon(r1), LineCon(l2)],
                    [
                        SamePoint(StartR(mr1),Start(ml2)),
                        SamePoint(EndR(mr1),End(ml2))
                    ], []
                ) end
          | "joinrect" =>
                let val mr1 = mk_rect();
                    val mr2 = mk_rect();
                    val mr3 = mk_rect();
                    val r1 = RootRect(mr1);
                    val r2 = RootRect(mr2);
                    val r3 = JoinRect(mr3, r1, r2);
                in (
                    RectCon(r3), [RectCon(r1), RectCon(r2)],
                    [
                        SamePoint(EndR(mr1),StartR(mr2)),
                        SameDirection(StartR(mr1), EndR(mr1), StartR(mr2), EndR(mr2)),
                        Equals(WidthR(mr1),WidthR(mr2))
                    ], []
                ) end
          | "subrect" =>
                let val mr1 = mk_rect();
                    val mr2 = mk_rect();
                    val mr3 = mk_rect();
                    val r1 = RootRect(mr1);
                    val r2 = RootRect(mr2);
                    val r3 = SubRect(mr3, r1, r2);
                in (
                    RectCon(r3), [RectCon(r1), RectCon(r2)],
                    [
                        SamePoint(EndR(mr1),EndR(mr2)),
                        SameDirection(StartR(mr1), EndR(mr1), StartR(mr2), EndR(mr2)),
                        Equals(WidthR(mr1),WidthR(mr2))
                    ], []
                ) end
          | s =>
                raise GeometryError ("unexpected constructor " ^ s)
        end
    
    
    fun replace_point p1 p2 goals =
        let fun replace_point_in_goal goal = case goal of
            _ => raise GeometryError ("TODO")
        in
            raise GeometryError ("TODO")
        end

    
    fun propagate_goals construction goals =
        case construction of
            LineCon(RootLine(_)) => goals
          | LineCon(ResolveLine(l3, lc1, lc2)) => 
                propagate_goals (LineCon lc2) (
                    propagate_goals (LineCon lc1) (
                        replace_point (Start(l3)) (Start(get_line lc1)) (
                            replace_point (End(l3)) (End(get_line lc1)) goals
                        ) @ replace_point (Start(l3)) (Start(get_line lc2)) (       (*TODO: this is gonna make a bunch of duplicate goals!*)
                            replace_point (End(l3)) (End(get_line lc2)) goals
                        )
                    )
                )
          | LineCon(Concat(l3, lc1, lc2)) =>
                propagate_goals (LineCon lc2) (
                    propagate_goals (LineCon lc1) (
                        replace_point (Start(l3)) (Start(get_line lc1)) (
                            replace_point (End(l3)) (End(get_line lc2)) goals
                        )
                    )
                );
          | LineCon(SimilarTriangle(l4, lc1, lc2, lc3)) =>
                
end


*)