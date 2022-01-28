extends Control
class_name Rect

signal changed

var start : Point
var width : Distance
var end : Point

var color := Color(0.1,0.1,1,0.2)

func _init(start, end, width):
	self.start = start
	self.width = width
	self.end = end
	start.connect("changed", self, "update")
	width.connect("changed", self, "update")
	end.connect("changed", self, "update")

func get_rect_start() -> Point:
	return start

func get_rect_width() -> Distance:
	return width

func get_rect_end() -> Point:
	return end

func _draw():
	var perpendicular := (end.get_point_pos() - start.get_point_pos()).normalized().rotated(PI/2) * width.get_value()
	draw_colored_polygon(PoolVector2Array([
		start.get_point_pos(),
		end.get_point_pos(),
		end.get_point_pos() + perpendicular,
		start.get_point_pos() + perpendicular
	]),color)
