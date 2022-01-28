extends Control
class_name Point

signal changed

var color := Color.black

func _init():
	set_size(Vector2(10,10))

func get_point_pos() -> Vector2:
	return rect_position + rect_size / 2

func set_point_pos(pos:Vector2):
	set_position(pos - rect_size / 2)

func _draw():
	print("HEY!")
	draw_circle(rect_size / 2, rect_size.x / 2, color)
