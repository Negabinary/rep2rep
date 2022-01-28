extends Distance
class_name SBetween

var a:Point
var b:Point

func _init(a:Point,b:Point):
	self.a = a
	self.b = b
	a.connect("changed", self, "recalculate")
	b.connect("changed", self, "recalculate")
	recalculate()

func recalculate():
	var p:Vector2 = b.get_point_pos() - a.get_point_pos()
	value = p.length()
	emit_signal("changed")
