extends Control
class_name Line

signal changed

var start : Point
var end : Point


func _init(start, end):
	self.start = start
	self.end = end
	start.connect("changed", self, "update")
	end.connect("changed", self, "update")

func get_line_start() -> Point:
	return start

func get_line_end() -> Point:
	return end

func get_line_direction() -> Direction:
	return DBetween.new(get_line_start(), get_line_end())

func get_line_distance() -> Distance:
	return SBetween.new(get_line_start(), get_line_end())

func _draw():
	draw_line(start.get_point_pos(), end.get_point_pos(), Color(0,0,0,1), 2, true)
