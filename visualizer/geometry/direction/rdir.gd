extends Direction
class_name RDir

var direction:Direction
var value:Value

func _init(direction:Direction, value:Value):
	self.direction = direction
	self.value = value
	direction.connect("changed", self, "recalculate")
	value.connect("changed", self, "recalculate")
	recalculate()

func recalculate():
	angle = direction.angle + value.get_value()
	emit_signal("changed")
