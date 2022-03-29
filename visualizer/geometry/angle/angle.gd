extends Control
class_name Angle

signal changed

var start : Point
var middle : Point
var end : Point

var color := Color(0,0,0,1)

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
	var start_angle = (start.get_point_pos() - middle.get_point_pos()).angle()
	var end_angle = (end.get_point_pos() - middle.get_point_pos()).angle()
	if end_angle < start_angle:
		end_angle = end_angle + 2 * PI
	draw_arc(middle.get_point_pos(), 20, start_angle, end_angle, 10, color, 3, true)
	draw_line(start.get_point_pos(), middle.get_point_pos(), Color(0,0,0,1), 3, true)
	draw_line(middle.get_point_pos(), end.get_point_pos(), Color(0,0,0,1), 3, true)
