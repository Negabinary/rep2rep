extends Control
class_name PointResolve

signal changed

var start : Point
var end : Point
var aim : bool

func _init(start:Point, end:Point, aim:bool):
	self.start = start
	self.end = end
	self.aim = aim
	start.connect("changed", self, "update")
	end.connect("changed", self, "update")

func eval() -> float:
	return (start.get_point_pos()-end.get_point_pos()).length_squared()

func _draw():
	if eval() > 0.01 and aim:
		draw_line(start.get_point_pos(), end.get_point_pos(), Color.red, 3, true)
