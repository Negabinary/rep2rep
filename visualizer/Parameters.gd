extends VBoxContainer

func add_parameter(value:Value, label:String):
	var plabel := Label.new()
	plabel.text = label
	add_child(plabel)
	var slider := HSlider.new()
	add_child(slider)
	slider.min_value = 0.0001
	slider.max_value = PI * 2
	slider.step = 0.0001
	slider.value = value.get_value()
	slider.connect("value_changed", value, "set_value")

func clear():
	for child in get_children():
		remove_child(child)
