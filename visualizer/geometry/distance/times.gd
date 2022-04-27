extends Distance
class_name Divide

var a:Distance
var b:Distance

func _init(a:Distance, b:Distance):
	self.a = a
	self.b = b
	a.connect("changed", self, "recalculate")
	b.connect("changed", self, "recalculate")
	recalculate()

func recalculate():
	value = a.get_value() * 30 / b.get_value()
	emit_signal("changed")
