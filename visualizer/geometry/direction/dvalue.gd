extends Direction
class_name DValue

var v:Value

func _init(v:Value):
	self.v = v
	v.connect("changed", self, "recalculate")
	recalculate()

func recalculate():
	angle = v.get_value()
	emit_signal("changed")
