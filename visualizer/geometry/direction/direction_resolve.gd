extends Control
class_name DirectionResolve

signal changed

var start : Point
var d1 : Direction
var d2 : Direction
var aim : bool

func _init(start:Point, d1:Direction, d2:Direction, aim:bool):
	self.start = start
	self.d1 = d1
	self.d2 = d2
	self.aim = aim
	start.connect("changed", self, "update")
	d1.connect("changed", self, "update")
	d2.connect("changed", self, "update")

func eval() -> float:
	return 1 - d1.get_unit().dot(d2.get_unit())

func _draw():
	if eval() > 0.001 and aim:
		var end_point_1 := start.get_point_pos() + d1.get_unit() * 20
		var end_point_2 := start.get_point_pos() + d2.get_unit() * 20
		draw_line(start.get_point_pos(), end_point_1, Color.orangered, 3, true)
		draw_line(start.get_point_pos(), end_point_2, Color.orangered, 3, true)
