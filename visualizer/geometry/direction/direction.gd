extends Object
class_name Direction

signal changed

var angle := 0.0

func get_unit() -> Vector2:
	return Vector2.RIGHT.rotated(angle)
