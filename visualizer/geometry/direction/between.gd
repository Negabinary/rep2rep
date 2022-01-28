extends Direction
class_name DBetween

var a:Point
var b:Point

func _init(a:Point,b:Point):
	self.a = a
	self.b = b
	a.connect("changed", self, "recalculate")
	b.connect("changed", self, "recalculate")
	recalculate()

func recalculate():
	var p = b.get_point_pos() - a.get_point_pos()
	angle = atan2(p.y, p.x)
	emit_signal("changed")
