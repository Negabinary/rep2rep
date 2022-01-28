extends Point
class_name Move

var other : Point
var direction : Direction
var distance : Distance

func _init(other:Point, direction:Direction, distance:Distance):
	self.other = other
	self.direction = direction
	self.distance = distance
	other.connect("changed", self, "recalculate")
	direction.connect("changed", self, "recalculate")
	distance.connect("changed", self, "recalculate")
	recalculate()

func recalculate():
	set_point_pos(other.get_point_pos() + direction.get_unit() * distance.get_value())
	emit_signal("changed")
