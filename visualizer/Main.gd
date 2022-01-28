extends ColorRect

var tree : Dictionary

func _ready():
	randomize()
	#var string = "ResolveLine(Concat(Concat(Line(p1, Move(p1, d2, Value(A))), Line(Move(p1, d2, Value(A)), Move(Move(p1, d2, Value(A)), d2, Value(B)))), Line(Move(Move(p1, d2, Value(A)), d2, Value(B)), Move(Move(Move(p1, d2, Value(A)), d2, Value(B)), d2, Value(C)))), Concat(Line(p1, Move(p1, d2, Value(A))), Concat(Line(Move(p1, d2, Value(A)), Move(Move(p1, d2, Value(A)), d2, Value(B))), Line(Move(Move(p1, d2, Value(A)), d2, Value(B)), Move(Move(Move(p1, d2, Value(A)), d2, Value(B)), d2, Value(C))))))"
	#var string = "ResolveLine(Concat(Line(p389, Move(p389, d392, Value(A))), Line(Move(Move(Move(Move(p389, Right(Right(d392)), Value(A)), Direction(p389, p397), Divide(Times(Distance(p389, p397), Distance(p401, Move(Move(p401, Right(Right(d392)), Value(A)), Direction(p397, p389), Distance(p389, p397)))), Distance(p402, Move(Move(p402, Direction(p389, p397), Distance(p389, p397)), d392, Value(A))))), d392, Divide(Times(Value(A), Distance(p403, Move(Move(p403, Right(Right(d392)), Value(A)), Direction(p397, p389), Distance(p389, p397)))), Distance(p404, Move(Move(p404, Direction(p389, p397), Distance(p389, p397)), d392, Value(A))))), Right(Right(d392)), Value(B)), Move(Move(Move(p389, Right(Right(d392)), Value(A)), Direction(p389, p397), Divide(Times(Distance(p389, p397), Distance(p405, Move(Move(p405, Right(Right(d392)), Value(A)), Direction(p397, p389), Distance(p389, p397)))), Distance(p406, Move(Move(p406, Direction(p389, p397), Distance(p389, p397)), d392, Value(A))))), d392, Divide(Times(Value(A), Distance(p407, Move(Move(p407, Right(Right(d392)), Value(A)), Direction(p397, p389), Distance(p389, p397)))), Distance(p408, Move(Move(p408, Direction(p389, p397), Distance(p389, p397)), d392, Value(A))))))), Rotate(Concat(Rotate(Line(Move(Move(Move(Move(p389, Right(Right(d392)), Value(A)), Direction(p389, p397), Divide(Times(Distance(p389, p397), Distance(p401, Move(Move(p401, Right(Right(d392)), Value(A)), Direction(p397, p389), Distance(p389, p397)))), Distance(p402, Move(Move(p402, Direction(p389, p397), Distance(p389, p397)), d392, Value(A))))), d392, Divide(Times(Value(A), Distance(p403, Move(Move(p403, Right(Right(d392)), Value(A)), Direction(p397, p389), Distance(p389, p397)))), Distance(p404, Move(Move(p404, Direction(p389, p397), Distance(p389, p397)), d392, Value(A))))), Right(Right(d392)), Value(B)), Move(Move(Move(p389, Right(Right(d392)), Value(A)), Direction(p389, p397), Divide(Times(Distance(p389, p397), Distance(p405, Move(Move(p405, Right(Right(d392)), Value(A)), Direction(p397, p389), Distance(p389, p397)))), Distance(p406, Move(Move(p406, Direction(p389, p397), Distance(p389, p397)), d392, Value(A))))), d392, Divide(Times(Value(A), Distance(p407, Move(Move(p407, Right(Right(d392)), Value(A)), Direction(p397, p389), Distance(p389, p397)))), Distance(p408, Move(Move(p408, Direction(p389, p397), Distance(p389, p397)), d392, Value(A)))))), Angle(Move(Move(Move(p389, Right(Right(d392)), Value(A)), Direction(p389, p397), Divide(Times(Distance(p389, p397), Distance(p409, Move(Move(p409, Right(Right(d392)), Value(A)), Direction(p397, p389), Distance(p389, p397)))), Distance(p410, Move(Move(p410, Direction(p389, p397), Distance(p389, p397)), d392, Value(A))))), d392, Divide(Times(Value(A), Distance(p411, Move(Move(p411, Right(Right(d392)), Value(A)), Direction(p397, p389), Distance(p389, p397)))), Distance(p412, Move(Move(p412, Direction(p389, p397), Distance(p389, p397)), d392, Value(A))))), Move(Move(Move(Move(p389, Right(Right(d392)), Value(A)), Direction(p389, p397), Divide(Times(Distance(p389, p397), Distance(p413, Move(Move(p413, Right(Right(d392)), Value(A)), Direction(p397, p389), Distance(p389, p397)))), Distance(p414, Move(Move(p414, Direction(p389, p397), Distance(p389, p397)), d392, Value(A))))), d392, Divide(Times(Value(A), Distance(p415, Move(Move(p415, Right(Right(d392)), Value(A)), Direction(p397, p389), Distance(p389, p397)))), Distance(p416, Move(Move(p416, Direction(p389, p397), Distance(p389, p397)), d392, Value(A))))), Right(Right(d392)), Value(B)), Move(Move(Move(Move(Move(p389, Right(Right(d392)), Value(A)), Direction(p389, p397), Divide(Times(Distance(p389, p397), Distance(p417, Move(Move(p417, Right(Right(d392)), Value(A)), Direction(p397, p389), Distance(p389, p397)))), Distance(p418, Move(Move(p418, Direction(p389, p397), Distance(p389, p397)), d392, Value(A))))), d392, Divide(Times(Value(A), Distance(p419, Move(Move(p419, Right(Right(d392)), Value(A)), Direction(p397, p389), Distance(p389, p397)))), Distance(p420, Move(Move(p420, Direction(p389, p397), Distance(p389, p397)), d392, Value(A))))), Right(Right(d392)), Value(B)), d392, s421))), MoveLine(Line(p389, Move(p389, d392, Value(A))), Line(Move(p397, Direction(p397, p389), Distance(p389, p397)), p397))), Angle(Move(Move(p389, Direction(p389, p397), Distance(p389, p397)), d392, Value(A)), Move(Move(Move(Move(p389, Right(Right(d392)), Value(A)), Direction(p389, p397), Divide(Times(Distance(p389, p397), Distance(p422, Move(Move(p422, Right(Right(d392)), Value(A)), Direction(p397, p389), Distance(p389, p397)))), Distance(p423, Move(Move(p423, Direction(p389, p397), Distance(p389, p397)), d392, Value(A))))), d392, Divide(Times(Value(A), Distance(p424, Move(Move(p424, Right(Right(d392)), Value(A)), Direction(p397, p389), Distance(p389, p397)))), Distance(p425, Move(Move(p425, Direction(p389, p397), Distance(p389, p397)), d392, Value(A))))), Right(Right(d392)), Value(B)), p400)))"
	var string = "p1"
	tree = _generate_tree(string)
	$HSplitContainer/ColorRect2/Drawer.generate(tree)
	$HSplitContainer/ColorRect2/Drawer.reverse_children()

func _generate_tree(string:String) -> Dictionary:
	var context_stack := [[]]
	var current_string := ""
	for i in range(string.length() - 1, -1, -1):
		var chr = string[i]
		if chr == ")":
			context_stack.push_front([])
		elif chr == "," or chr == "(":
			var currrent_children = context_stack.pop_front()
			context_stack[0].push_front({kind=current_string, children=currrent_children})
			if chr == ",":
				context_stack.push_front([])
			current_string = ""
		elif chr != " ":
			current_string = chr + current_string
	var current_children = context_stack.pop_front()
	return {kind=current_string, children=current_children}


func _on_TextEdit_text_entered(new_text):
	$HSplitContainer/ColorRect2/Drawer.clear()
	tree = _generate_tree(new_text)
	$HSplitContainer/ColorRect2/Drawer.generate(tree)
	$HSplitContainer/ColorRect2/Drawer.reverse_children()
