extends Control
class_name Angle

signal changed

var start : Point
var middle : Point
var end : Point

var color := Color(0,0,0,0.2)

func _init(start, middle, end):
	self.start = start
	self.middle = middle
	self.end = end
	start.connect("changed", self, "update")
	middle.connect("changed", self, "update")
	end.connect("changed", self, "update")

func get_angle_start() -> Point:
	return start

func get_angle_middle() -> Point:
	return middle

func get_angle_end() -> Point:
	return end

func _draw():
	draw_arc(middle.get_point_pos(), 20, (start.get_point_pos() - middle.get_point_pos()).angle(), (end.get_point_pos() - middle.get_point_pos()).angle(), 10, color, 3, true)
	draw_line(start.get_point_pos(), middle.get_point_pos(), Color(0,0,0,0.2), 3, true)
	draw_line(middle.get_point_pos(), end.get_point_pos(), Color(0,0,0,0.2), 3, true)
