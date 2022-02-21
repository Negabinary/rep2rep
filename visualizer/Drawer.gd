extends Control
class_name Drawer

var map := {}
onready var variables = $"../../ColorRect/VBoxContainer/Variables"
onready var parameters = $"../../ColorRect/VBoxContainer/Parameters"

func reverse_children():
	var children = get_children()
	for i in len(children):
		move_child(children[-i-1], i)

func clear():
	for child in get_children():
		remove_child(child)
	map = {}
	variables.clear()
	parameters.clear()

func generate(tree:Dictionary):
	match tree.kind:
		"Line":
			var p1 = generate(tree.children[0])
			var p2 = generate(tree.children[1])
			add_child(p1)
			add_child(p2)
			var line = Line.new(generate(tree.children[0]),generate(tree.children[1]))
			add_child(line)
			return line
		"ResolveLine":
			var line = generate(tree.children[0])
			line.color = Color(0,1,0,0.5)
			generate(tree.children[1]).color = Color(1,0,0,0.5)
			return line
		"Concat":
			var line = Line.new(generate(tree.children[0]).get_line_start(),generate(tree.children[1]).get_line_end())
			add_child(line)
			return line
		"MoveLine":
			var line_1 = generate(tree.children[0])
			var line_2 = generate(tree.children[1])
			var p1 = line_1.get_line_start()
			var p2 = line_2.get_line_start()
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
			#add_child(Line.new(p1,p3))
			#add_child(Line.new(p2,p4))
			var line = Line.new(p3,p4)
			add_child(line)
			return line
		"MoveAngle":
			var angle_1 = generate(tree.children[0])
			var line_2 = generate(tree.children[1])
			var angle = Angle.new(
				Move.new(
					angle_1.get_angle_start(),
					DBetween.new(line_2.get_line_start(), line_2.get_line_end()),
					SBetween.new(line_2.get_line_start(), line_2.get_line_end())
				),
				Move.new(
					angle_1.get_angle_middle(),
					DBetween.new(line_2.get_line_start(), line_2.get_line_end()),
					SBetween.new(line_2.get_line_start(), line_2.get_line_end())
				),
				Move.new(
					angle_1.get_angle_end(),
					DBetween.new(line_2.get_line_start(), line_2.get_line_end()),
					SBetween.new(line_2.get_line_start(), line_2.get_line_end())
				)
			)
			add_child(angle)
			return angle
		"SimilarTriangle":
			var a = generate(tree.children[0])
			var b = generate(tree.children[1])
			var c = generate(tree.children[2])
			var line = Line.new(
				c.get_line_end(),
				Move.new(
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
			)
			add_child(line)
			return line
		"DivRect":
			#TODO
			pass
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
			add_child(line)
			return line
		"Angle":
			var angle = Angle.new(generate(tree.children[0]),generate(tree.children[1]),generate(tree.children[2]))
			add_child(angle)
			return angle
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
			add_child(other_line)
			add_child(line)
			return line
		"Pythag":
			var l1 = generate(tree.children[0])
			var l2 = generate(tree.children[1])
			var sq = Rect.new(
				l1.get_line_start(),
				l2.get_line_end(),
				SBetween.new(l1.get_line_start(), l2.get_line_end())
			)
			add_child(sq)
			return sq
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
			add_child(line)
			return line
		"Rect":
			var rect = Rect.new(generate(tree.children[0]), generate(tree.children[1]), generate(tree.children[2]))
			add_child(rect)
			return rect
		"ResolveAngle":
			var angle = generate(tree.children[0])
			angle.color = Color(0,1,0,0.5)
			generate(tree.children[1]).color = Color(1,0,0,0.5)
			return angle
		"JoinAngle":
			var a1 = generate(tree.children[0])
			var a2 = generate(tree.children[1])
			var a = Angle.new(a1.get_angle_start(), a1.get_angle_middle(), a2.get_angle_end())
			add_child(a)
			return a
		"SubAngle":
			var a1 = generate(tree.children[0])
			var a2 = generate(tree.children[1])
			var a = Angle.new(a1.get_angle_start(), a1.get_angle_middle(), a2.get_angle_start())
			add_child(a)
			return a
		"ReverseAngle":
			var a1 = generate(tree.children[0])
			var a = Angle.new(a1.get_angle_end(), a1.get_angle_middle(), a1.get_angle_start())
			add_child(a)
			return a
		"ResolveRect":
			var rect = generate(tree.children[0])
			rect.color = Color(0,1,0,0.5)
			generate(tree.children[1]).color = Color(1,0,0,0.5)
			return rect
		"MKRect":
			var l1 = generate(tree.children[0])
			var l2 = generate(tree.children[1])
			var c = Rect.new(l1.get_line_start(),l1.get_line_end(), SBetween.new(l2.get_line_start(),l2.get_line_end()))
			add_child(c)
			return c
		"JoinRect":
			var r1 = generate(tree.children[0])
			var r2 = generate(tree.children[1])
			var c = Rect.new(r1.get_rect_start(),r2.get_rect_end(),r2.get_rect_width())
			add_child(c)
			return c
		"SubRect":
			var r1 = generate(tree.children[0])
			var r2 = generate(tree.children[1])
			var c = Rect.new(r1.get_rect_start(),r2.get_rect_start(),r1.get_rect_width())
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
			add_child(rect)
			return rect

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
