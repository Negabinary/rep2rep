extends Distance
class_name SValue

var v:Value

func _init(v:Value):
	self.v = v
	v.connect("changed", self, "recalculate")
	recalculate()

func recalculate():
	value = v.get_value() * 100
	emit_signal("changed")
