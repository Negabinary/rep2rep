extends Control
class_name Drawer

var map := {}
onready var variables = $"../../ColorRect/VBoxContainer/Variables"
onready var parameters = $"../../ColorRect/VBoxContainer/Parameters"
onready var resolvers = $"../Resolver"

func reverse_children():
	var children = get_children()
	for i in len(children):
		move_child(children[-i-1], i)

func clear():
	for child in get_children():
		remove_child(child)
	for child in resolvers.get_children():
		resolvers.remove_child(child)
	map = {}
	variables.clear()
	parameters.clear()

func add_point_resolve(p1, p2, neg=false):
	resolvers.add_child(PointResolve.new(p1, p2, not neg))

func add_direction_resolve(pr, d1, d2, neg=false):
	resolvers.add_child(DirectionResolve.new(pr, d1, d2, not neg))

func add_distance_resolve(p1, d1, s1, p2, d2, s2, neg=false):
	pass

func generate(tree:Dictionary):
	match tree.kind:
		"Line":
			var p1 = generate(tree.children[0])
			var p2 = generate(tree.children[1])
			add_child(p1)
			add_child(p2)
			add_point_resolve(p1, p2, true)
			var line = Line.new(generate(tree.children[0]),generate(tree.children[1]))
			add_child(line)
			return line
		"ResolveLine":
			var l1 = generate(tree.children[0])
			var l2 = generate(tree.children[1])
			add_point_resolve(l1.get_line_start(), l2.get_line_start())
			add_point_resolve(l1.get_line_end(), l2.get_line_end())
			return l1
		"Concat":
			var l1 = generate(tree.children[0])
			var l2 = generate(tree.children[1])
			add_point_resolve(l1.get_line_end(), l2.get_line_start())
			add_direction_resolve(l2.get_line_start(), l1.get_line_direction(), l2.get_line_direction())
			var line = Line.new(l1.get_line_start(), l2.get_line_end())
			add_child(line)
			return line
		"SimilarTriangle":
			var a = generate(tree.children[0])
			var b = generate(tree.children[1])
			var c = generate(tree.children[2])
			var missing_point = Move.new(
					b.get_line_start(),
					DBetween.new(
						b.get_line_start(), 
						a.get_line_end()
					),
					Divide.new(
						Times.new(
							SBetween.new(b.get_line_start(), a.get_line_end()),
							SBetween.new(c.get_line_start(), c.get_line_end())
						),
						SBetween.new(b.get_line_start(), b.get_line_end())
					)
				)
			var line = Line.new(
				c.get_line_end(),
				missing_point
			)
			add_child(Line.new(c.get_line_start(), missing_point))
			add_point_resolve(a.get_line_start(), b.get_line_end())
			add_point_resolve(b.get_line_start(), c.get_line_end())
			add_direction_resolve(c.get_line_start(), b.get_line_direction(), c.get_line_direction())
			add_child(line)
			return line
		"DivRect":
			var rect_1 = generate(tree.children[0])
			var line_2 = generate(tree.children[1])
			add_point_resolve(rect_1.get_rect_start(), line_2.get_line_start())
			add_point_resolve(rect_1.get_rect_end(), line_2.get_line_end())
			var line = Line.new(rect_1.get_rect_end(), Move.new(
				rect_1.get_rect_end(),
				Right.new(DBetween.new(rect_1.get_rect_start(), rect_1.get_rect_end())),
				rect_1.get_rect_width()
			))
			add_child(line)
			return line
		"Reverse":
			var child = generate(tree.children[0])
			var line = Line.new(child.get_line_end(),child.get_line_start())
			add_child(line)
			return line
		"Rotate":
			var child = generate(tree.children[0])
			var angle = generate(tree.children[1])
			var line = Line.new(
				child.get_line_start(),
				Move.new(
					child.get_line_start(),
					DBetween.new(
						child.get_line_start(),
						angle.get_angle_end()
					),
					SBetween.new(
						child.get_line_start(),
						child.get_line_end()
					)
				)
			)
			add_point_resolve(angle.get_angle_middle(), child.get_line_start())
			add_point_resolve(angle.get_angle_start(), child.get_line_end())
			add_child(line)
			return line
		"Sine":
			var one = generate(tree.children[0])
			var angle = generate(tree.children[1])
			var dot = Dot.new(
					DBetween.new(angle.get_angle_middle(), angle.get_angle_start()),
					DBetween.new(angle.get_angle_middle(), angle.get_angle_end())
			)
			var middle_point = Move.new(
				one.get_line_start(),
				DBetween.new(angle.get_angle_middle(), angle.get_angle_end()),
				Times.new(
					dot,
					SBetween.new(one.get_line_start(),one.get_line_end())
				)
			)
			var line = Line.new(
				middle_point,
				one.get_line_end()
			)
			var other_line = Line.new(
				one.get_line_start(),
				middle_point
			)
			add_point_resolve(one.get_line_start(), angle.get_angle_middle())
			add_direction_resolve(
				angle.get_angle_middle(), 
				one.get_line_direction(), 
				DBetween.new(angle.get_angle_middle(), angle.get_angle_start())
				)
			add_child(other_line)
			add_child(line)
			return line
		"Cos":
			var one = generate(tree.children[0])
			var angle = generate(tree.children[1])
			var dot = Dot.new(
					DBetween.new(angle.get_angle_middle(), angle.get_angle_start()),
					DBetween.new(angle.get_angle_middle(), angle.get_angle_end())
			)
			var middle_point = Move.new(
				one.get_line_start(),
				DBetween.new(angle.get_angle_middle(), angle.get_angle_end()),
				Times.new(
					dot,
					SBetween.new(one.get_line_start(),one.get_line_end())
				)
			)
			var line = Line.new(
				one.get_line_start(),
				middle_point
			)
			var other_line = Line.new(
				middle_point,
				one.get_line_end()
			)
			add_point_resolve(one.get_line_start(), angle.get_angle_middle())
			add_direction_resolve(
				angle.get_angle_middle(), 
				one.get_line_direction(), 
				DBetween.new(angle.get_angle_middle(), angle.get_angle_start())
			)
			add_child(other_line)
			add_child(line)
			return line
		"Tangent":
			var one = generate(tree.children[0])
			var angle = generate(tree.children[1])
			var dot = Dot.new(
					DBetween.new(angle.get_angle_middle(), angle.get_angle_start()),
					DBetween.new(angle.get_angle_middle(), angle.get_angle_end())
			)
			var end_point = Move.new(
				angle.get_angle_middle(),
				DBetween.new(angle.get_angle_middle(), angle.get_angle_start()),
				Divide.new(
					SBetween.new(one.get_line_start(),one.get_line_end()),
					dot
				)
			)
			var line = Line.new(
				one.get_line_end(),
				end_point
			)
			add_point_resolve(one.get_line_start(), angle.get_angle_middle())
			add_direction_resolve(
				angle.get_angle_middle(), 
				one.get_line_direction(), 
				DBetween.new(angle.get_angle_middle(), angle.get_angle_start())
			)
			add_child(line)
			return line
		"MoveLine":
			var line_1 = generate(tree.children[0])
			var line_2 = generate(tree.children[1])
			var p1 = line_1.get_line_start()
			var p2 = line_1.get_line_end()
			var p3 = Move.new(
					line_1.get_line_start(),
					DBetween.new(line_2.get_line_start(), line_2.get_line_end()),
					SBetween.new(line_2.get_line_start(), line_2.get_line_end())
				)
			var p4 = Move.new(
					line_1.get_line_end(),
					DBetween.new(line_2.get_line_start(), line_2.get_line_end()),
					SBetween.new(line_2.get_line_start(), line_2.get_line_end())
				)
			add_point_resolve(line_1.get_line_start(), line_2.get_line_start())
			add_direction_resolve(
				line_1.get_line_start(), 
				line_1.get_line_direction(), 
				line_2.get_line_direction(), 
				true
			)
			add_direction_resolve(
				line_1.get_line_start(), 
				line_1.get_line_direction(), 
				Right.new(Right.new(line_2.get_line_direction())), 
				true
			)
			add_child(Line.new(p1,p3))
			add_child(Line.new(p2,p4))
			var line = Line.new(p3,p4)
			add_child(line)
			return line
		"Angle":
			var a = generate(tree.children[0])
			var b = generate(tree.children[1])
			var c = generate(tree.children[2])
			var angle = Angle.new(a,b,c)
			add_child(angle)
			add_point_resolve(a,b,true)
			add_point_resolve(b,c,true)
			add_direction_resolve(b, DBetween.new(b,a), DBetween.new(b,c), true)
			return angle
		"ResolveAngle":
			var angle_1 = generate(tree.children[0])
			var angle_2 = generate(tree.children[1])
			add_point_resolve(angle_1.get_angle_start(), angle_2.get_angle_start())
			add_point_resolve(angle_1.get_angle_middle(), angle_2.get_angle_middle())
			add_point_resolve(angle_1.get_angle_end(), angle_1.get_angle_end())
			return angle_1
		"AngleBetween":
			var line_1 = generate(tree.children[0])
			var line_2 = generate(tree.children[1])
			var angle = Angle.new(line_1.get_line_end(), line_1.get_line_start(), line_2.get_line_end())
			add_point_resolve(line_1.get_line_start(), line_2.get_line_start())
			add_point_resolve(line_1.get_line_end(), line_2.get_line_end(), true)
			add_child(angle)
			return angle
		"JoinAngle":
			var a1 = generate(tree.children[0])
			var a2 = generate(tree.children[1])
			var a = Angle.new(a1.get_angle_start(), a1.get_angle_middle(), a2.get_angle_end())
			add_point_resolve(a1.get_angle_middle(), a2.get_angle_middle())
			add_point_resolve(a1.get_angle_end(), a2.get_angle_start())
			add_point_resolve(a1.get_angle_start(), a2.get_angle_end(), true)
			add_child(a)
			return a
		"SubAngle":
			var a1 = generate(tree.children[0])
			var a2 = generate(tree.children[1])
			var a = Angle.new(a1.get_angle_start(), a1.get_angle_middle(), a2.get_angle_start())
			add_point_resolve(a1.get_angle_middle(), a2.get_angle_middle())
			add_point_resolve(a1.get_angle_end(), a2.get_angle_end())
			add_point_resolve(a1.get_angle_start(), a2.get_angle_start(), true)
			add_child(a)
			return a
		"ReverseAngle":
			var a1 = generate(tree.children[0])
			var a = Angle.new(a1.get_angle_end(), a1.get_angle_middle(), a1.get_angle_start())
			add_child(a)
			return a
		"MoveAngle":
			var angle_1 = generate(tree.children[0])
			var line_2 = generate(tree.children[1])
			var np1 = Move.new(
				angle_1.get_angle_start(),
				DBetween.new(line_2.get_line_start(), line_2.get_line_end()),
				SBetween.new(line_2.get_line_start(), line_2.get_line_end())
			)
			var np2 = Move.new(
				angle_1.get_angle_middle(),
				DBetween.new(line_2.get_line_start(), line_2.get_line_end()),
				SBetween.new(line_2.get_line_start(), line_2.get_line_end())
			)
			var np3 = Move.new(
				angle_1.get_angle_end(),
				DBetween.new(line_2.get_line_start(), line_2.get_line_end()),
				SBetween.new(line_2.get_line_start(), line_2.get_line_end())
			)
			var angle = Angle.new(np1, np2, np3)
			add_point_resolve(angle_1.get_angle_middle(), line_2.get_line_start())
			add_child(Line.new(angle_1.get_angle_start(), np1))
			add_child(Line.new(angle_1.get_angle_middle(), np2))
			add_child(Line.new(angle_1.get_angle_end(), np3))
			add_child(angle)
			return angle
		"OppositeAngle":
			var angle = generate(tree.children[0])
			var new_start = Move.new(
				angle.get_angle_middle(),
				DBetween.new(angle.get_angle_start(), angle.get_angle_middle()),
				SBetween.new(angle.get_angle_middle(), angle.get_angle_start())
			)
			var new_end = Move.new(
				angle.get_angle_middle(),
				DBetween.new(angle.get_angle_end(), angle.get_angle_middle()),
				SBetween.new(angle.get_angle_middle(), angle.get_angle_end())
			)
			var new_angle = Angle.new(new_start, angle.get_angle_middle(), new_end)
			add_child(new_angle)
			return new_angle
		"Rect":
			var rect = Rect.new(generate(tree.children[0]), generate(tree.children[1]), generate(tree.children[2]))
			add_child(rect)
			return rect
		"ResolveRect":
			var rect_1 = generate(tree.children[0])
			var rect_2 = generate(tree.children[1])
			add_point_resolve(rect_1.get_rect_start(), rect_2.get_rect_start())
			add_point_resolve(rect_1.get_rect_end(), rect_2.get_rect_end())
			add_distance_resolve(
				rect_1.get_rect_start(),
				Right.new(DBetween.new(rect_1.get_rect_start(), rect_1.get_rect_end())),
				rect_1.get_rect_width(),
				rect_2.get_rect_start(),
				Right.new(DBetween.new(rect_2.get_rect_start(), rect_2.get_rect_end())),
				rect_2.get_rect_width()
				)
			return rect_1
		"JoinRect":
			var r1 = generate(tree.children[0])
			var r2 = generate(tree.children[1])
			var c = Rect.new(r1.get_rect_start(),r2.get_rect_end(),r2.get_rect_width())
			add_point_resolve(r1.get_rect_end(), r2.get_rect_start())
			add_direction_resolve(
				r2.get_rect_start(), 
				DBetween.new(r1.get_rect_start(), r1.get_rect_end()),
				DBetween.new(r2.get_rect_start(), r2.get_rect_end())
			)
			add_distance_resolve(
				r1.get_rect_end(),
				Right.new(DBetween.new(r1.get_rect_start(), r1.get_rect_end())),
				r1.get_rect_width(),
				r2.get_rect_start(),
				Right.new(DBetween.new(r2.get_rect_start(), r2.get_rect_end())),
				r2.get_rect_width()
			)
			add_child(c)
			return c
		"MKRect":
			var l1 = generate(tree.children[0])
			var l2 = generate(tree.children[1])
			var c = Rect.new(l1.get_line_start(),l1.get_line_end(), SBetween.new(l2.get_line_start(),l2.get_line_end()))
			add_point_resolve(l1.get_line_start(), l2.get_line_start())
			add_direction_resolve(
				l2.get_line_start(),
				Right.new(l1.get_line_direction()),
				l2.get_line_direction()
			)
			add_child(c)
			return c
		"SubRect":
			var r1 = generate(tree.children[0])
			var r2 = generate(tree.children[1])
			var c = Rect.new(r1.get_rect_start(),r2.get_rect_start(),r1.get_rect_width())
			add_point_resolve(r1.get_rect_end(), r2.get_rect_end())
			add_direction_resolve(
				r2.get_rect_start(), 
				DBetween.new(r1.get_rect_start(), r1.get_rect_end()),
				DBetween.new(r2.get_rect_start(), r2.get_rect_end())
			)
			add_distance_resolve(
				r1.get_rect_end(),
				Right.new(DBetween.new(r1.get_rect_start(), r1.get_rect_end())),
				r1.get_rect_width(),
				r2.get_rect_end(),
				Right.new(DBetween.new(r2.get_rect_start(), r2.get_rect_end())),
				r2.get_rect_width()
			)
			add_child(c)
			return c
		"NextRect":
			var r = generate(tree.children[0])
			var c = Rect.new(r.get_rect_end(), Move.new(r.get_rect_end(),Right.new(DBetween.new(r.get_rect_start(),r.get_rect_end())), r.get_rect_width()), SBetween.new(r.get_rect_start(), r.get_rect_end()))
			add_child(c)
			return c
		"MoveRect":
			var rect_1 = generate(tree.children[0])
			var line_2 = generate(tree.children[1])
			var p1 = Move.new(
				rect_1.get_rect_start(),
				DBetween.new(line_2.get_line_start(), line_2.get_line_end()),
				SBetween.new(line_2.get_line_start(), line_2.get_line_end())
			)
			var p2 = Move.new(
				rect_1.get_rect_end(),
				DBetween.new(line_2.get_line_start(), line_2.get_line_end()),
				SBetween.new(line_2.get_line_start(), line_2.get_line_end())
			)
			var p3 = Move.new(
				p1,
				Right.new(DBetween.new(p1, p2)),
				rect_1.get_rect_width()
			)
			var p4 = Move.new(
				p2,
				Right.new(DBetween.new(p1, p2)),
				rect_1.get_rect_width()
			)
			var rect = Rect.new(
				Move.new(
					rect_1.get_rect_start(),
					DBetween.new(line_2.get_line_start(), line_2.get_line_end()),
					SBetween.new(line_2.get_line_start(), line_2.get_line_end())
				),
				Move.new(
					rect_1.get_rect_end(),
					DBetween.new(line_2.get_line_start(), line_2.get_line_end()),
					SBetween.new(line_2.get_line_start(), line_2.get_line_end())
				),
				rect_1.get_rect_width()
			)
			add_point_resolve(rect_1.get_rect_start(), line_2.get_line_start())
			add_direction_resolve(
				rect_1.get_rect_start(),
				line_2.get_line_direction(),
				DBetween.new(rect_1.get_rect_start(), rect_1.get_rect_end()),
				true
			)
			add_direction_resolve(
				rect_1.get_rect_start(),
				Right.new(line_2.get_line_direction()),
				DBetween.new(rect_1.get_rect_start(), rect_1.get_rect_end()),
				true
			)
			add_direction_resolve(
				rect_1.get_rect_start(),
				Right.new(line_2.get_line_direction()),
				DBetween.new(rect_1.get_rect_start(), rect_1.get_rect_end()),
				true
			)
			add_direction_resolve(
				rect_1.get_rect_start(),
				Right.new(line_2.get_line_direction()),
				DBetween.new(rect_1.get_rect_start(), rect_1.get_rect_end()),
				true
			)
			add_child(rect)
			return rect
		"Pythag":
			var l1 = generate(tree.children[0])
			var l2 = generate(tree.children[1])
			var sq = Rect.new(
				l2.get_line_end(),
				l1.get_line_start(),
				SBetween.new(l1.get_line_start(), l2.get_line_end())
			)
			var sq1 = Rect.new(
				l1.get_line_start(),
				l1.get_line_end(),
				l1.get_line_distance()
			)
			var sq2 = Rect.new(
				l2.get_line_start(),
				l2.get_line_end(),
				l2.get_line_distance()
			)
			add_child(sq)
			add_child(sq1)
			add_child(sq2)
			add_point_resolve(l1.get_line_end(), l2.get_line_start())
			add_direction_resolve(
				l2.get_line_start(),
				Right.new(l2.get_line_direction()),
				l1.get_line_direction()
			)
			return sq

# LOWEST LEVEL

		"Move":
			var p = Move.new(
				generate(tree.children[0]),
				generate(tree.children[1]),
				generate(tree.children[2])
			)
			return p
		"Direction":
			return DBetween.new(
				generate(tree.children[0]),
				generate(tree.children[1])
			)
		"RDir":
			return RDir.new(
				generate(tree.children[0]),
				generate(tree.children[1])
			)
		"Right":
			return Right.new(
				generate(tree.children[0])
			)
		"Distance":
			return SBetween.new(
				generate(tree.children[0]),
				generate(tree.children[1])
			)
		"Times":
			return Times.new(
				generate(tree.children[0]),
				generate(tree.children[1])
			)
		"Divide":
			return Divide.new(
				generate(tree.children[0]),
				generate(tree.children[1])
			)
		"Value":
			return SValue.new(
				generate(tree.children[0])
			)
		"Dot":
			return Dot.new(
				generate(tree.children[0]),
				generate(tree.children[1])
			)
		var other:
			if other in map:
				return map[other]
			else:			
				match other[0]:
					"p":
						var x = MovablePoint.new()
						x.set_point_pos(Vector2(rand_range(0,rect_size.x),rand_range(0,rect_size.y)))
						add_child(x)
						map[other] = x
						return x
					"d":
						var x = Value.new()
						x.value = rand_range(0.5, PI * 2)
						parameters.add_parameter(x,other)
						var sv = DValue.new(x)
						map[other] = sv
						return sv
					"s":
						var x = Value.new()
						x.value = rand_range(0.5, PI * 2)
						parameters.add_parameter(x,other)
						var sv = SValue.new(x)
						map[other] = sv
						return sv
					_:
						var x = Value.new()
						x.value = rand_range(0.5, PI * 2)
						map[other] = x
						variables.add_parameter(x,other)
						return x
