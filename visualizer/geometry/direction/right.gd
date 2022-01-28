extends Direction
class_name Right

var direction:Direction

func _init(direction:Direction):
	self.direction = direction
	direction.connect("changed", self, "recalculate")
	recalculate()

func recalculate():
	angle = direction.angle + PI/2
	emit_signal("changed")
