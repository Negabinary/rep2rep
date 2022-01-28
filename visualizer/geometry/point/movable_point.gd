extends Point
class_name MovablePoint

var dragging := false

func _ready():
	mouse_filter = MOUSE_FILTER_STOP
	connect("mouse_entered", self, "_mouse_entered")
	connect("mouse_exited", self, "_mouse_exited")
	self.color = Color.darkcyan

func _gui_input(event):
	if event is InputEventMouseButton:
		if event.is_action_pressed("left"):
			dragging = true
		elif event.is_action_released("left"):
			dragging = false
	if event is InputEventMouseMotion:
		if dragging:
			set_position(event.position + rect_position - rect_size / 2)
			emit_signal("changed")

func _mouse_entered():
	self.color = Color.cyan
	update()

func _mouse_exited():
	self.color = Color.darkcyan
	update()
