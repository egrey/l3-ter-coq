Module CoTree.
	CoInductive tree (t: Type) :=
		  Leaf 
		| Node (n: tree t * t * tree t).

	Definition isLeaf {t: Type} (x: tree t): Prop :=
		match x with
			  Leaf  => True
			| _ => False
		end.

	Definition isNode {t: Type} (x: tree t): Prop :=
		match x with
			  Node n => True
			| _ => False
		end.
End CoTree.


Module Tree.
	Parameter Label: Type.

	Inductive tree (t: Type) :=
		  Leaf 
		| Node (n: tree t * t * tree t)
		| Labeled (tag: Label) (labeled: tree t)
		| Reference (tag: Label).

	Definition isLeaf {t: Type} (x: tree t): Prop :=
		match x with
			  Leaf  => True
			| _ => False
		end.

	Definition isNode {t: Type} (x: tree t): Prop :=
		match x with
			  Node n => True
			| _ => False
		end.

	Definition isLabeled {t: Type} (x: tree t): Prop :=
		match x with
			  Labeled tag labeled => True
			| _ => False
		end.

	Definition isReference {t: Type} (x: tree t): Prop :=
		match x with
			  Reference tag => True
			| _ => False
		end.
End Tree.