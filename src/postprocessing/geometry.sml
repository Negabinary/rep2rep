(* : TODO signature*)
structure Geometry = 
struct
    val counter = ref 0;
    fun unique_name () = (counter := !counter + 1; "g" ^ (PolyML.makestring (!counter)));

    val assignment_flag = ref false;
    fun af () = assignment_flag := true;

    exception GeometryError of string;

    datatype point_con = Move of point_con option ref * direction_con option ref * distance_con option ref
                       | PCopy of point_con option ref
     and direction_con = Direction of point_con option ref * point_con option ref
                       | RDir of direction_con option ref * string
                       | LDir of direction_con option ref * string
                       | Right of direction_con option ref
                       | DCopy of direction_con option ref
      and distance_con = Distance of point_con option ref * point_con option ref
                       | Times of distance_con option ref * distance_con option ref
                       | Divide of distance_con option ref * distance_con option ref
                       | Value of string
                       | SCopy of distance_con option ref
                       | Dot of direction_con option ref * direction_con option ref
                       | Zero
           and rot_con = Clockwise
                       | Opposite of rot_con option ref;

    datatype line_con = RootLine of point_con option ref * point_con option ref
                      | ResolveLine of line_con * line_con
                      | Concat of line_con * line_con
                      | SimilarTriangle of line_con * line_con * line_con
                      | DivRect of rect_con * line_con
                      | Reverse of line_con
                      | Rotate of line_con * angle_con
                      | Sine of line_con * angle_con
                      | Cosine of line_con * angle_con
                      | Tangent of line_con * angle_con
                      | MoveLine of line_con * line_con
        and angle_con = RootAngle of point_con option ref * point_con option ref * point_con option ref
                      | ResolveAngle of angle_con * angle_con
                      | AngleBetween of line_con * line_con
                      | JoinAngle of angle_con * angle_con
                      | SubAngle of angle_con * angle_con
                      | ReverseAngle of angle_con
                      | MoveAngle of angle_con * line_con
                      | OppositeAngle of angle_con
         and rect_con = RootRect of point_con option ref * point_con option ref * distance_con option ref
                      | ResolveRect of rect_con * rect_con
                      | MKRect of line_con * line_con
                      | JoinRect of rect_con * rect_con
                      | SubRect of rect_con * rect_con
                      | NextRect of rect_con
                      | MoveRect of rect_con * line_con
                      | Pythag of line_con * line_con;
    
    fun map_deep_state_p (f as (fp,_,_)) p = case !p of
            NONE => fp p
          | (SOME(Move (p1,d1,s1))) => (map_deep_state_p f p1; map_deep_state_d f d1; map_deep_state_s f s1; fp p)
          | (SOME(PCopy (p1))) => (map_deep_state_p f p1; fp p)
    and map_deep_state_d (f as (_,fd,_)) d = case !d of
            NONE => fd d
          | (SOME(Direction (p1,p2))) => (map_deep_state_p f p1; map_deep_state_p f p2; fd d)
          | (SOME(RDir (d1,v1))) => (map_deep_state_d f d1; fd d)
          | (SOME(LDir (d1,v1))) => (map_deep_state_d f d1; fd d)
          | (SOME(Right (d1))) => (map_deep_state_d f d1; fd d)
          | (SOME(DCopy (d1))) => (map_deep_state_d f d1; fd d)
    and map_deep_state_s (f as (_,_,fs)) s = case !s of
            NONE => fs s
          | (SOME(Distance (p1,p2))) => (map_deep_state_p f p1; map_deep_state_p f p2; fs s)
          | (SOME(Times (s1,s2))) => (map_deep_state_s f s1; map_deep_state_s f s2; fs s)
          | (SOME(Divide (s1,s2))) => (map_deep_state_s f s1; map_deep_state_s f s2; fs s)
          | (SOME(Value (x))) => fs s
          | (SOME(SCopy (s1))) => fs s
          | (SOME(Dot (d1, d2))) => (map_deep_state_d f d1; map_deep_state_d f d2; fs s)
          | (SOME(Zero)) => fs s;

    fun map_leaves_p (f as (fp,_,_)) p = case !p of
            NONE => fp p
          | (SOME(Move (p1,d1,s1))) => (ref o SOME) (Move(map_leaves_p f p1, map_leaves_d f d1, map_leaves_s f s1))
          | (SOME(PCopy (p1))) => (ref o SOME) (PCopy (map_leaves_p f p1))
    and map_leaves_d (f as (_,fd,_)) d = case !d of
            NONE => fd d
          | (SOME(Direction (p1,p2))) => (ref o SOME) (Direction (map_leaves_p f p1, map_leaves_p f p2))
          | (SOME(RDir (d1,v1))) => (ref o SOME) (RDir (map_leaves_d f d1,v1))
          | (SOME(LDir (d1,v1))) => (ref o SOME) (LDir (map_leaves_d f d1,v1))
          | (SOME(Right (d1))) => (ref o SOME) (Right (map_leaves_d f d1))
          | (SOME(DCopy (d1))) => (ref o SOME) (DCopy (map_leaves_d f d1))
    and map_leaves_s (f as (_,_,fs)) s = case !s of
            NONE => fs s
          | (SOME(Distance (p1,p2))) => (ref o SOME) (Distance (map_leaves_p f p1,map_leaves_p f p2))
          | (SOME(Times (s1,s2))) => (ref o SOME) (Times (map_leaves_s f s1, map_leaves_s f s2))
          | (SOME(Divide (s1,s2))) => (ref o SOME) (Divide (map_leaves_s f s1, map_leaves_s f s2))
          | (SOME(Value (x))) => (ref o SOME) (Value (x))
          | (SOME(SCopy (s1))) => (ref o SOME) (SCopy (map_leaves_s f s1))
          | (SOME(Dot (d1, d2))) => (ref o SOME) (Dot (map_leaves_d f d1, map_leaves_d f d2))
          | (SOME(Zero)) => (ref o SOME) Zero;
    
    fun map_points_l (fp,fs) (RootLine (x,y)) = RootLine(fp x, fp y)
      | map_points_l f (ResolveLine (x,y)) = ResolveLine(map_points_l f x, map_points_l f y)
      | map_points_l f (Concat (x,y)) = Concat(map_points_l f x, map_points_l f y)
      | map_points_l f (SimilarTriangle (x,y,z)) = SimilarTriangle(map_points_l f x, map_points_l f y, map_points_l f z)
      | map_points_l f (DivRect (x,y)) = DivRect (map_points_r f x, map_points_l f y)
      | map_points_l f (Reverse (x)) = Reverse (map_points_l f x)
      | map_points_l f (Rotate (x,y)) = Rotate (map_points_l f x, map_points_a f y)
      | map_points_l f (Sine (x,y)) = Sine (map_points_l f x, map_points_a f y)
      | map_points_l f (Cosine (x,y)) = Cosine (map_points_l f x, map_points_a f y)
      | map_points_l f (Tangent (x,y)) = Tangent (map_points_l f x, map_points_a f y)
      | map_points_l f (MoveLine (x,y)) = MoveLine (map_points_l f x, map_points_l f y)
    and map_points_a (fp,fs) (RootAngle (x,y,z)) = RootAngle(fp x, fp y, fp z)
      | map_points_a f (ResolveAngle (x,y)) = ResolveAngle (map_points_a f x, map_points_a f y)
      | map_points_a f (AngleBetween (x,y)) = AngleBetween (map_points_l f x, map_points_l f y)
      | map_points_a f (JoinAngle (x,y)) = JoinAngle (map_points_a f x, map_points_a f y)
      | map_points_a f (SubAngle (x,y)) = SubAngle (map_points_a f x, map_points_a f y)
      | map_points_a f (ReverseAngle (x)) = ReverseAngle (map_points_a f x)
      | map_points_a f (MoveAngle (x,y)) = MoveAngle (map_points_a f x, map_points_l f y)
      | map_points_a f (OppositeAngle (x)) = OppositeAngle (map_points_a f x)
    and map_points_r (fp,fs) (RootRect (x,y,w)) = RootRect (fp x, fp y, fs w)
      | map_points_r f (ResolveRect (x,y)) = ResolveRect (map_points_r f x, map_points_r f y)
      | map_points_r f (MKRect (x,y)) = MKRect (map_points_l f x, map_points_l f y)
      | map_points_r f (JoinRect (x,y)) = JoinRect (map_points_r f x, map_points_r f y)
      | map_points_r f (SubRect (x,y)) = SubRect (map_points_r f x, map_points_r f y)
      | map_points_r f (NextRect (x)) = NextRect (map_points_r f x)
      | map_points_r f (MoveRect (x,y)) = MoveRect (map_points_r f x, map_points_l f y)
      | map_points_r f (Pythag (x,y)) = Pythag (map_points_l f x, map_points_l f y);
    
    datatype construction = LineCon of line_con | AngleCon of angle_con | RectCon of rect_con;

    fun map_points f (LineCon x) = LineCon(map_points_l f x)
      | map_points f (AngleCon x) = AngleCon(map_points_a f x)
      | map_points f (RectCon x) = RectCon(map_points_r f x);
    
    fun map_deep_points f x = map_points (map_deep_state_p f, map_deep_state_s f) x;

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
    
    fun dirof l = (ref o SOME o Direction) (get_line_start l, get_line_end l)
    and disof l = (ref o SOME o Distance) (get_line_start l, get_line_end l)
    and get_line_start (RootLine(a,b)) = a
      | get_line_start (ResolveLine(a,b)) = get_line_start a
      | get_line_start (Concat(a,b)) = get_line_start a
      | get_line_start (SimilarTriangle(a,b,c)) = get_line_end c
      | get_line_start (DivRect(r,l)) = get_rect_end r
      | get_line_start (Reverse(l)) = get_line_end l
      | get_line_start (Rotate(l,a)) = get_line_start l
      | get_line_start (Sine(l,a)) = (ref o SOME o Move) (
            get_line_start l, 
            (ref o SOME o Direction) (get_angle_middle a, get_angle_end a),
            (ref o SOME o Times) (
                (ref o SOME o Dot) (
                    (ref o SOME o Direction) (get_angle_middle a, get_angle_start a), 
                    (ref o SOME o Direction) (get_angle_middle a, get_angle_end a)
                ), 
                disof l
            )
        )
      | get_line_start (Cosine(l,a)) = get_line_start l
      | get_line_start (Tangent(l,a)) = get_line_end l
      | get_line_start (MoveLine(l,lm)) = (ref o SOME o Move) (get_line_start l, dirof lm, disof lm)

    and get_line_end (RootLine(a,b)) = b
      | get_line_end (ResolveLine(a,b)) = get_line_end a
      | get_line_end (Concat(a,b)) = get_line_end b
      | get_line_end (SimilarTriangle(a,b,c)) = 
        let val B = get_line_start a;
            val A = get_line_end a;
            val C = get_line_start b;
            val D = get_line_end c;
        in
            (ref o SOME o Move) (
                    C,
                    (ref o SOME o Direction) (C,A),
                    (ref o SOME o Divide) (
                        (ref o SOME o Times) (
                            (ref o SOME o Distance) (C,A),
                            (ref o SOME o Distance) (C,D)
                        ),
                        (ref o SOME o Distance) (C,B)
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
                (ref o SOME o Direction) (A,B),
                (ref o SOME o Distance) (A,C)
            )
        end
      | get_line_end (Sine(l, a)) = get_line_end l
      | get_line_end (Cosine(l, a)) = get_line_start (Sine(l, a))
      | get_line_end (Tangent(l, a)) = (ref o SOME o Move) (
            get_angle_middle a,
            (ref o SOME o Direction) (get_angle_middle a, get_angle_start a),
            (ref o SOME o Divide) (disof l, (ref o SOME o Dot) (
                    (ref o SOME o Direction) (get_angle_middle a, get_angle_start a), 
                    (ref o SOME o Direction) (get_angle_middle a, get_angle_end a)
                ))
        )
      | get_line_end (MoveLine(l,lm)) = (ref o SOME o Move) (get_line_end l, dirof lm, disof lm)
      
        
    and get_angle_start (RootAngle(a,b,c)) = a
      | get_angle_start (ResolveAngle(a,b)) = get_angle_start a
      | get_angle_start (AngleBetween(a,b)) = get_line_end a
      | get_angle_start (JoinAngle(a,b)) = get_angle_start a
      | get_angle_start (SubAngle(a,b)) = get_angle_start a
      | get_angle_start (ReverseAngle(a)) = get_angle_end a
      | get_angle_start (MoveAngle(a,l)) = (ref o SOME o Move) (get_angle_start a, dirof l, disof l)
      | get_angle_start (OppositeAngle(a)) = (ref o SOME o Move) (
            get_angle_middle a,
            (ref o SOME o Right o ref o SOME o Right o ref o SOME o Direction) (get_angle_middle a, get_angle_start a),
            (ref o SOME o Distance) (get_angle_middle a, get_angle_start a)
        )
    
    and get_angle_middle (RootAngle(a,b,c)) = b
      | get_angle_middle (ResolveAngle(a,b)) = get_angle_middle a
      | get_angle_middle (AngleBetween(a,b)) = get_line_start a
      | get_angle_middle (JoinAngle(a,b)) = get_angle_middle a
      | get_angle_middle (SubAngle(a,b)) = get_angle_middle a
      | get_angle_middle (ReverseAngle(a)) = get_angle_middle a
      | get_angle_middle (MoveAngle(a,l)) = (ref o SOME o Move) (get_angle_middle a, dirof l, disof l)
      | get_angle_middle (OppositeAngle(a)) = get_angle_middle a
    
    and get_angle_end (RootAngle(a, b,c)) = c
      | get_angle_end (ResolveAngle(a, b)) = get_angle_end a
      | get_angle_end (AngleBetween(a, b)) = get_line_end b
      | get_angle_end (JoinAngle(a, b)) = get_angle_end b
      | get_angle_end (SubAngle(a, b)) = get_angle_start b
      | get_angle_end (ReverseAngle(a)) = get_angle_start a
      | get_angle_end (MoveAngle(a,l)) = (ref o SOME o Move) (get_angle_end a, dirof l, disof l)
      | get_angle_end (OppositeAngle(a)) = (ref o SOME o Move) (
            get_angle_middle a,
            (ref o SOME o Right o ref o SOME o Right o ref o SOME o Direction) (get_angle_middle a, get_angle_end a),
            (ref o SOME o Distance) (get_angle_middle a, get_angle_start a)
        )
    
    and get_angle_rot (RootAngle(a,b,c)) = ref (SOME (Clockwise))
      | get_angle_rot (ResolveAngle(a, b)) = get_angle_rot a
      | get_angle_rot (AngleBetween(a, b)) = ref (SOME (Clockwise))
      | get_angle_rot (JoinAngle(a, b)) = get_angle_rot a
      | get_angle_rot (SubAngle(a, b)) = get_angle_rot a
      | get_angle_rot (ReverseAngle(a)) = (ref o SOME o Opposite) (get_angle_rot a)
      | get_angle_rot (MoveAngle(a,l)) = get_angle_rot a
      | get_angle_rot (OppositeAngle(a)) = get_angle_rot a
    
    and get_rect_start (RootRect(a, b, c)) = a
      | get_rect_start (ResolveRect(a, b)) = get_rect_start a
      | get_rect_start (MKRect(a, b)) = get_line_start a
      | get_rect_start (JoinRect(a, b)) = get_rect_start a
      | get_rect_start (SubRect(a, b)) = get_rect_start a
      | get_rect_start (NextRect(a)) = get_rect_end a
      | get_rect_start (MoveRect(a,b)) = (ref o SOME o Move) (get_rect_start a, dirof b, disof b)
      | get_rect_start (Pythag(a,b)) = get_line_end b
    
    and get_rect_end (RootRect(a, b, c)) = b
      | get_rect_end (ResolveRect(a, b)) = get_rect_end a
      | get_rect_end (MKRect(a, b)) = get_line_end a
      | get_rect_end (JoinRect(a, b)) = get_rect_end b
      | get_rect_end (SubRect(a, b)) = get_rect_start b
      | get_rect_end (NextRect(a)) = (ref o SOME o Move) (get_rect_end a, (ref o SOME o Right o ref o SOME o Direction) (get_rect_start a, get_rect_end a), get_rect_width a)
      | get_rect_end (MoveRect(a,b)) = (ref o SOME o Move) (get_rect_end a, dirof b, disof b)
      | get_rect_end (Pythag(a,b)) = get_line_start a
    
    and get_rect_width (RootRect(a, b, c)) = c
      | get_rect_width (ResolveRect(a, b)) = get_rect_width a
      | get_rect_width (MKRect(a, b)) = 
        let val A = get_line_start b;
            val B = get_line_end b;
        in
            (ref o SOME o Distance) (A,B)
        end
      | get_rect_width (JoinRect(a, b)) = get_rect_width a
      | get_rect_width (SubRect(a, b)) = get_rect_width a
      | get_rect_width (NextRect(a)) = (ref o SOME o Distance) (get_rect_start a, get_rect_end a)
      | get_rect_width (MoveRect(a, b)) = get_rect_width a
      | get_rect_width (Pythag(a,b)) = (ref o SOME o Distance) (get_line_start a, get_line_end b);

    datatype constraint = PC of point_con option ref * point_con option ref
                        | DC of direction_con option ref * direction_con option ref
                        | SC of distance_con option ref * distance_con option ref
                        | RC of rot_con option ref * rot_con option ref;
    
    datatype pos_neg_constraint = Y of constraint | N of constraint | X of constraint;
      (*Y = Yes, N = No, X = Extra condition that can't be proven*)
    
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
                ], [
                  DC(
                    dirof a,
                    dirof b
                  ),
                  DC(
                    (ref o SOME o Right o ref o SOME o Right) (dirof a),
                    dirof b
                  )
                ]
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
                    DC((ref o SOME o Direction) (get_angle_middle a, get_angle_start a), dirof l)
                ], []
            )
      | Sine(l, a) => mc
            (mc (get_line_constraints l) (get_angle_constraints a))
            (
                [
                    PC(get_line_start l, get_angle_middle a),
                    DC(dirof l, (ref o SOME o Direction) (get_angle_middle a, get_angle_start a))
                    (*TODO: Constrain minimum / maximum angle*)
                ], []
            )
      | Cosine(l, a) => mc
            (mc (get_line_constraints l) (get_angle_constraints a))
            (
                [
                    PC(get_line_start l, get_angle_middle a),
                    DC(dirof l, (ref o SOME o Direction) (get_angle_middle a, get_angle_start a))
                ], []
            )
      | Tangent(l, a) => mc
            (mc (get_line_constraints l) (get_angle_constraints a))
            (
                [
                    PC(get_line_start l, get_angle_middle a),
                    DC(dirof l, (ref o SOME o Direction) (get_angle_middle a, get_angle_end a))
                ], []
            )
      | MoveLine(l, lm) => mc
            (mc (get_line_constraints l) (get_line_constraints lm))
            (
                [
                    PC(get_line_start l, get_line_start lm)
                ], [
                    DC(dirof l, dirof lm),
                    DC(dirof l, (ref o SOME o Right o ref o SOME o Right) (dirof lm))
                ]
            )
    and get_angle_constraints angle = case angle of
        RootAngle(a,b,c) => (
            [], [
                PC(a,b),
                PC(b,c),
                PC(a,c),
                DC((ref o SOME o Direction)(b,a), (ref o SOME o Direction)(b,c))
            ]
        )
      | ResolveAngle(a,b) => mc
            (mc (get_angle_constraints a) (get_angle_constraints b))
            (
                [
                    PC(get_angle_start a, get_angle_start b),
                    PC(get_angle_middle a, get_angle_middle b),
                    PC(get_angle_end a, get_angle_end b),
                    RC(get_angle_rot a, get_angle_rot b)
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
                [PC(get_angle_middle a, get_angle_middle b),PC(get_angle_end a, get_angle_start b),RC(get_angle_rot a, get_angle_rot b)],
                [PC(get_angle_start a, get_angle_end b)]
            )
      | SubAngle(a,b) => mc
            (mc (get_angle_constraints a) (get_angle_constraints b))
            (
                [
                    PC(get_angle_middle a, get_angle_middle b), 
                    PC(get_angle_end a, get_angle_end b),
                    RC(get_angle_rot a, get_angle_rot b)
                ], [PC(get_angle_start a, get_angle_start b)]
            )
      | ReverseAngle(a) => get_angle_constraints a
      | MoveAngle(a,l) => mc
            (mc (get_angle_constraints a) (get_line_constraints l))
            (
                [
                    PC(get_angle_middle a, get_line_start l)
                ], []
            )
      | OppositeAngle(a) => get_angle_constraints a
      
    and get_rect_constraints rect = case rect of
        RootRect(a,b,c) => (
            [],[
                PC(a,b)
            ]
        )
      | ResolveRect(a,b) => mc
            (mc (get_rect_constraints a) (get_rect_constraints b))
            ([
                PC(get_rect_start a, get_rect_start b),
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
            )
      | NextRect(a) => get_rect_constraints a
      | MoveRect(a,l) => mc
            (mc (get_rect_constraints a) (get_line_constraints l))
            (
                [
                    PC(get_rect_start a, get_line_start l)
                ], [
                    DC(
                      dirof l,
                      (ref o SOME o Direction) (get_rect_start a, get_rect_end a)
                    ),
                    DC(
                      (ref o SOME o Right) (dirof l),
                      (ref o SOME o Direction) (get_rect_start a, get_rect_end a)
                    ),
                    DC(
                      (ref o SOME o Right o ref o SOME o Right) (dirof l),
                      (ref o SOME o Direction) (get_rect_start a, get_rect_end a)
                    ),
                    DC(
                      (ref o SOME o Right o ref o SOME o Right o ref o SOME o Right) (dirof l),
                      (ref o SOME o Direction) (get_rect_start a, get_rect_end a)
                    )
                ]
            )
      | Pythag(l1,l2) => mc
            (mc (get_line_constraints l1) (get_line_constraints l2))
            (
                [
                    PC(get_line_end l1, get_line_start l2),
                    DC((ref o SOME o Right) (dirof l2), (dirof l1))
                ], []
            );
    
    fun get_constraints object = case object of
        LineCon(x) => get_line_constraints(x)
      | AngleCon(x) => get_angle_constraints(x)
      | RectCon(x) => get_rect_constraints(x);
    

    fun point_contains_check check const = case !const of
        NONE => const = check
      | SOME(Move(x,y,z)) => point_contains_check check x orelse pcd check y orelse pcs check z
      | SOME(PCopy(x)) => point_contains_check check x
    and pcd check const = case !const of
        NONE => false
      | SOME(Direction(x,y)) => point_contains_check check x orelse point_contains_check check y
      | SOME(RDir(x,s)) => pcd check x
      | SOME(LDir(x,s)) => pcd check x
      | SOME(Right(x)) => pcd check x
      | SOME(DCopy(x)) => pcd check x
    and pcs check const = case !const of
        NONE => false
      | SOME(Distance(x,y)) => point_contains_check check x orelse point_contains_check check y
      | SOME(Times(x,y)) => pcs check x orelse pcs check y
      | SOME(Divide(x,y)) => pcs check x orelse pcs check y
      | SOME(Value(x)) => false
      | SOME(SCopy(x)) => pcs check x
      | SOME(Dot(a,b)) => pcd check a orelse pcd check b
      | SOME(Zero) => false;
    
    fun dcp check const = case !const of
        NONE => false
      | SOME(Move(x,y,z)) => dcp check x orelse direction_contains_check check y orelse dcs check z
      | SOME(PCopy(x)) => dcp check x
    and direction_contains_check check const = case !const of
        NONE => const = check
      | SOME(Direction(x,y)) => dcp check x orelse dcp check y
      | SOME(RDir(x,s)) => direction_contains_check check x
      | SOME(LDir(x,s)) => direction_contains_check check x
      | SOME(Right(x)) => direction_contains_check check x
      | SOME(DCopy(x)) => direction_contains_check check x
    and dcs check const = case !const of
        NONE => false
      | SOME(Distance(x,y)) => dcp check x orelse dcp check y
      | SOME(Times(x,y)) => dcs check x orelse dcs check y
      | SOME(Divide(x,y)) => dcs check x orelse dcs check y
      | SOME(Value(x)) => false
      | SOME(SCopy(x)) => dcs check x
      | SOME(Dot(a,b)) => direction_contains_check check a orelse direction_contains_check check b
      | SOME(Zero) => false;
    
    fun scp check const = case !const of
        NONE => false
      | SOME(Move(x,y,z)) => scp check x orelse scd check y orelse distance_contains_check check z
      | SOME(PCopy(x)) => scp check x
    and scd check const = case !const of
        NONE => false
      | SOME(Direction(x,y)) => scp check x orelse scp check y
      | SOME(RDir(x,s)) => scd check x
      | SOME(LDir(x,s)) => scd check x
      | SOME(Right(x)) => scd check x
      | SOME(DCopy(x)) => scd check x
    and distance_contains_check check const = case !const of
        NONE => const = check
      | SOME(Distance(x,y)) => scp check x orelse scp check y
      | SOME(Times(x,y)) => distance_contains_check check x orelse distance_contains_check check y
      | SOME(Divide(x,y)) => distance_contains_check check x orelse distance_contains_check check y
      | SOME(Value(x)) => false
      | SOME(SCopy(x)) => distance_contains_check check x
      | SOME(Dot(a,b)) => scd check a orelse scd check b
      | SOME(Zero) => false;

    fun inc n = (n := !n + 1; !n);

    fun print_point point (pm,dm,sm,n) = case !point of
        NONE => (case List.find (fn (x,y) => x = point) (!pm) of 
            NONE => (pm := (point,(inc n))::(!pm); "p" ^ (PolyML.makestring (!n)) ) 
          | SOME(x,y) => "p" ^ (PolyML.makestring y))
      | SOME(Move(p,d,s)) => "Move("^(print_point p (pm,dm,sm,n))^", "^(print_direction d (pm,dm,sm,n))^", "^(print_distance s (pm,dm,sm,n))^")"
      | SOME(PCopy(p)) => print_point p (pm,dm,sm,n)
    and print_direction direction (pm,dm,sm,n) = case !direction of
        NONE => (case List.find (fn (x,y) => x = direction) (!dm) of
            NONE => (dm := (direction, (inc n))::(!dm); "d" ^ (PolyML.makestring (!n)))
          | SOME(x,y) => "d" ^ (PolyML.makestring y))
      | SOME(Direction(a,b)) => "Direction("^(print_point a (pm,dm,sm,n))^", "^(print_point b (pm,dm,sm,n))^")" 
      | SOME(RDir(d,v)) => "RDir(" ^ (print_direction d (pm,dm,sm,n)) ^ ", " ^ v ^ ")"
      | SOME(LDir(d,v)) => "LDir(" ^ (print_direction d (pm,dm,sm,n)) ^ ", " ^ v ^ ")"
      | SOME(Right(d)) => "Right(" ^ (print_direction d (pm,dm,sm,n)) ^ ")"
      | SOME(DCopy(d)) => print_direction d (pm,dm,sm,n)
    and print_distance distance (pm,dm,sm,n) = case !distance of
        NONE => (case List.find (fn (x,y) => x = distance) (!sm) of
            NONE => (sm := (distance, (inc n))::(!sm); "s" ^ (PolyML.makestring (!n)))
          | SOME(x,y) => "s" ^ (PolyML.makestring y))
      | SOME(Distance(a,b)) => "Distance("^(print_point a (pm,dm,sm,n))^", "^(print_point b (pm,dm,sm,n))^")"
      | SOME(Times(a,b)) => "Times("^(print_distance a (pm,dm,sm,n))^", "^(print_distance b (pm,dm,sm,n))^")"
      | SOME(Divide(a,b)) => "Divide("^(print_distance a (pm,dm,sm,n))^", "^(print_distance b (pm,dm,sm,n))^")"
      | SOME(Value(v)) => "Value(" ^ v ^")"
      | SOME(SCopy(s)) => print_distance s (pm,dm,sm,n)
      | SOME(Dot(a,b)) => "Dot(" ^ print_direction a (pm,dm,sm,n) ^ "," ^ print_direction b (pm,dm,sm,n) ^ ")"
      | SOME(Zero) => "Zero"
    and print_rot rot z = case !rot of
        SOME(Clockwise) => "Clockwise"
      | SOME(Opposite(r)) => "Opposite" ^ print_rot r z
      | NONE => "Error";
    
    fun print_constraint (PC(x,y)) z = (print_point x z) ^ " = " ^ (print_point y z)
      | print_constraint (DC(x,y)) z = (print_direction x z) ^ " = " ^ (print_direction y z)
      | print_constraint (SC(x,y)) z = (print_distance x z) ^ " = " ^ (print_distance y z)
      | print_constraint (RC(x,y)) z = (print_rot x z) ^ " = " ^ (print_rot y z);
    
    fun print_line (RootLine(a,b)) z = "Line(" ^ (print_point a z) ^ ", " ^ (print_point b z) ^ ")"
      | print_line (ResolveLine(a,b)) z = "ResolveLine(" ^ (print_line a z) ^ ", " ^ (print_line b z) ^ ")"
      | print_line (Concat(a,b)) z = "Concat(" ^ (print_line a z) ^ ", " ^ (print_line b z) ^ ")"
      | print_line (SimilarTriangle(a,b,c)) z = "SimilarTriangle(" ^ (print_line a z) ^ ", " ^ (print_line b z) ^ ", " ^ (print_line c z) ^ ")"
      | print_line (DivRect(r,l)) z = "DivRect(" ^ (print_rect r z) ^ ", " ^ (print_line l z) ^ ")"
      | print_line (Reverse(a)) z = "Reverse(" ^ (print_line a z) ^ ")"
      | print_line (Rotate(l, a)) z = "Rotate(" ^ (print_line l z) ^ ", " ^ (print_angle a z) ^ ")"
      | print_line (Sine(l, a)) z = "Sine(" ^ (print_line l z) ^ ", " ^ (print_angle a z) ^ ")"
      | print_line (Cosine(l, a)) z = "Cos(" ^ (print_line l z) ^ ", " ^ (print_angle a z) ^ ")"
      | print_line (Tangent(l, a)) z = "Tangent(" ^ (print_line l z) ^ ", " ^ (print_angle a z) ^ ")"
      | print_line (MoveLine(l, lm)) z = "MoveLine(" ^ (print_line l z) ^ ", " ^ (print_line lm z) ^ ")"
    and print_angle (RootAngle(a,b,c)) z = "Angle(" ^ (print_point a z) ^ ", " ^ (print_point b z) ^ ", " ^ (print_point c z) ^ ")"
      | print_angle (ResolveAngle(a,b)) z = "ResolveAngle(" ^ (print_angle a z) ^ ", " ^ (print_angle b z) ^ ")"
      | print_angle (AngleBetween(a,b)) z = "AngleBetween(" ^ (print_line a z) ^ ", " ^ (print_line b z) ^ ")"
      | print_angle (JoinAngle(a,b)) z = "JoinAngle(" ^ (print_angle a z) ^ ", " ^ (print_angle b z) ^ ")"
      | print_angle (SubAngle(a,b)) z = "SubAngle(" ^ (print_angle a z) ^ ", " ^ (print_angle b z) ^ ")"
      | print_angle (ReverseAngle(a)) z = "ReverseAngle(" ^ (print_angle a z) ^ ")"
      | print_angle (MoveAngle(a,l)) z = "MoveAngle(" ^ (print_angle a z) ^ "," ^ (print_line l z) ^ ")"
      | print_angle (OppositeAngle(a)) z = "OppositeAngle(" ^ (print_angle a z) ^ ")"
    and print_rect (RootRect(a,b,c)) z = "Rect(" ^ (print_point a z) ^ ", " ^ (print_point b z) ^ ", " ^ (print_distance c z) ^ ")"
      | print_rect (ResolveRect(a,b)) z = "ResolveRect(" ^ (print_rect a z) ^ ", " ^ (print_rect b z) ^ ")"
      | print_rect (MKRect(a,b)) z = "MKRect(" ^ (print_line a z) ^ ", " ^ (print_line b z) ^ ")"
      | print_rect (JoinRect(a,b)) z = "JoinRect(" ^ (print_rect a z) ^ ", " ^ (print_rect b z) ^ ")"
      | print_rect (SubRect(a,b)) z = "SubRect(" ^ (print_rect a z) ^ ", " ^ (print_rect b z) ^ ")"
      | print_rect (NextRect(r)) z = "NextRect(" ^ (print_rect r z) ^ ")"
      | print_rect (MoveRect(r, l)) z = "MoveRect(" ^ (print_rect r z) ^ "," ^ (print_line l z) ^ ")"
      | print_rect (Pythag(a,b)) z = "Pythag(" ^ (print_line a z) ^ ", " ^ (print_line b z) ^ ")";
    
    fun print_construction (LineCon x) z = print_line x z
      | print_construction (AngleCon x) z = print_angle x z
      | print_construction (RectCon x) z = print_rect x z;
    
    val printer_config = (ref [], ref [], ref [], ref 0)
    val _ = PolyML.addPrettyPrinter (fn x => fn y => fn z => PolyML.PrettyString (print_point (ref(SOME(z))) printer_config));
    val _ = PolyML.addPrettyPrinter (fn x => fn y => fn z => PolyML.PrettyString (print_constraint z printer_config));
    val _ = PolyML.addPrettyPrinter (fn x => fn y => fn z => PolyML.PrettyString (print_construction z printer_config));

    fun point_index x = 
      let val pm = #1 printer_config;
          val n = #4 printer_config;
      in 
        (case List.find (fn (x,y) => x = x) (!pm) of 
            NONE => (pm := (x,(inc n))::(!pm); !n) 
          | SOME(x,y) => y
        )
      end
    
    val sin = Math.sin;
    val cos = Math.cos;
    val atan2 = Math.atan2;
    fun mag a b = Math.sqrt (a * a + b * b);
    val pi = Math.pi;
    fun cadd x = if x < 0.0 then x + pi * 2.0 else x;

    fun hp x y z = case !z of SOME u => x y u | NONE => (y (print_point z printer_config ^ "_x"), y (print_point z printer_config ^ "_y"));
    fun hd x y z = case !z of SOME u => x y u | NONE => y (print_direction z printer_config);
    fun hs x y z = case !z of SOME u => x y u | NONE => y (print_distance z printer_config);
    fun numeric_point f (Move(a,b,c)) = 
            let val (nax, nay) = hp numeric_point f (a);
                val nb = hd numeric_direction f (b);
                val nc = hs numeric_distance f (c);
            in
                (nc * cos nb + nax, nc * sin nb + nay)
            end
      | numeric_point f (PCopy(p)) = hp numeric_point f (p)
    and numeric_direction f (Direction(a,b)) =
            let val (nax, nay) = hp numeric_point f (a)
                val (nbx, nby) = hp numeric_point f (b)
            in
                atan2 (nby - nay, nbx - nax)
            end
      | numeric_direction f (RDir(a,v)) = cadd (hd numeric_direction f (a) - (f v))
      | numeric_direction f (LDir(a,v)) = cadd (hd numeric_direction f (a) + (f v))
      | numeric_direction f (Right(a)) = cadd (hd numeric_direction f (a) - pi / 2.0)
      | numeric_direction f (DCopy(a)) = hd numeric_direction f (a)
    and numeric_distance f (Distance(a,b)) = 
            let val (nax, nay) = hp numeric_point f (a)
                val (nbx, nby) = hp numeric_point f (b)
            in
                mag (nby - nay) (nbx - nax)
            end
      | numeric_distance f (Times (a,b)) = hs numeric_distance f (a) * hs numeric_distance f (b)
      | numeric_distance f (Divide (a,b)) = hs numeric_distance f (a) / hs numeric_distance f (b)
      | numeric_distance f (Value (v)) = f v
      | numeric_distance f (SCopy (a)) = hs numeric_distance f (a)
      | numeric_distance f (Dot (a,b)) = cos (hd numeric_direction f (a) - hd numeric_direction f (b))
      | numeric_distance f (Zero) = 0.0
    and numeric_rot rot = case !rot of SOME(Clockwise) => false | SOME(Opposite(a)) => not (numeric_rot a) | NONE => false;

    fun create_map () =
        let val map = ref [];
            val counter = ref 0.0;
            fun nextval () = (counter := !counter + 1.0; Math.acos(Real.realMod (10.3421453195583 * cos (2.120351828579879 * !counter + 0.2151231249286498) + 100.0) * 2.0 - 1.0));
        in
            (fn v => 
              case List.find (fn (x,y) => x = v) (!map) of 
                  SOME (_,z) => z 
                | NONE => 
                    let val n = nextval () in 
                        map := ((v,n)::(!map)) ; n 
                    end
            )
        end

    fun check_constraint map (PC(a,b)) = 
        let val (x1,y1) = hp numeric_point map a;
            val (x2,y2) = hp numeric_point map b;
            val _ = ("PC",(x1,y1),(x2,y2));
        in
            Real.abs (x2 - x1) + Real.abs (y2 - y1) < 0.00000001
        end
      | check_constraint map (DC(a,b)) = 
        let val v1 = cadd (Real.rem (hd numeric_direction map a, 2.0*pi));
            val v2 = cadd (Real.rem (hd numeric_direction map b, 2.0*pi));
            val _ = ("DC",v1,v2);
        in
            Real.abs (v2 - v1) < 0.00000001
        end
      | check_constraint map (SC(a,b)) = 
        let val v1 = hs numeric_distance map a;
            val v2 = hs numeric_distance map b;
            val _ = ("SC",v1,v2);
        in
            Real.abs (v2 - v1) < 0.00000001
        end
      | check_constraint map (RC(a,b)) = (numeric_rot a = numeric_rot b);

end