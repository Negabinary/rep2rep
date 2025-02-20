extends Control
class_name Angle

signal changed

var start : Point
var middle : Point
var end : Point
var direction : bool
var size : float

var color := Color(0,0,0,1)

func _init(start, middle, end, direction):
	self.start = start
	self.middle = middle
	self.end = end
	self.direction = direction
	self.size = rand_range(20,30)
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
	if not direction:
		var tmp = start_angle
		start_angle = end_angle
		end_angle = tmp
	if (end_angle < start_angle):
		end_angle = end_angle + 2 * PI
	draw_arc(middle.get_point_pos(), self.size, start_angle, end_angle, 50, color, 3, true)
	draw_line(start.get_point_pos(), middle.get_point_pos(), Color(0,0,0,1), 3, true)
	draw_line(middle.get_point_pos(), end.get_point_pos(), Color(0,0,0,1), 3, true)
