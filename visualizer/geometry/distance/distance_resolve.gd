extends Control
class_name DistanceResolve

signal changed

var start : Point
var d1 : Direction
var d2 : Direction
var s1 : Distance
var s2 : Distance
var aim : bool

func _init(start:Point, d1:Direction, s1:Distance, p2:Point, d2:Direction, s2:Distance, aim:bool):
	self.start = start
	self.d1 = d1
	self.s1 = s1
	self.d2 = d2
	self.s2 = s2
	self.aim = aim
	start.connect("changed", self, "update")
	d1.connect("changed", self, "update")
	d2.connect("changed", self, "update")
	s1.connect("changed", self, "update")
	s2.connect("changed", self, "update")

func eval() -> float:
	return abs(s1.get_value() - s2.get_value())

func _draw():
	if eval() > 0.1 and aim:
		var end_point_1 := start.get_point_pos() + d1.get_unit() * s1.get_value()
		var end_point_2 := start.get_point_pos() + d2.get_unit() * s2.get_value()
		draw_line(start.get_point_pos(), end_point_1, Color.gold, 3, true)
		draw_line(start.get_point_pos(), end_point_2, Color.gold, 3, true)
