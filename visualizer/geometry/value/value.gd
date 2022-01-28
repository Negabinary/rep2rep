extends Object
class_name Value

signal changed

var value := 0.0

func get_value():
	return value

func set_value(val):
	value = val
	emit_signal("changed")
