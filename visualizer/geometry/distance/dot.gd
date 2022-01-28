extends Distance
class_name Dot

var a:Direction
var b:Direction

func _init(a:Direction,b:Direction):
	self.a = a
	self.b = b
	a.connect("changed", self, "recalculate")
	b.connect("changed", self, "recalculate")
	recalculate()

func recalculate():
	value = b.get_unit().dot(a.get_unit())
	emit_signal("changed")
