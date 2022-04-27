extends Distance
class_name Times

var a:Distance
var b:Distance

func _init(a:Distance, b:Distance):
	self.a = a
	self.b = b
	a.connect("changed", self, "recalculate")
	b.connect("changed", self, "recalculate")
	recalculate()

func recalculate():
	value = a.get_value() * b.get_value() / 30
	emit_signal("changed")
