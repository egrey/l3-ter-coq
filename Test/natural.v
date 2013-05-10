Module CoNatural.
	CoInductive natural  :=
		  Zero 
		| Successor (n: natural).

	Definition isZero  (x: natural ): Prop :=
		match x with
			  Zero  => True
			| _ => False
		end.

	Definition isSuccessor  (x: natural ): Prop :=
		match x with
			  Successor n => True
			| _ => False
		end.
End CoNatural.


Module Natural.
	Parameter Label: Type.

	Inductive natural  :=
		  Zero 
		| Successor (n: natural)
		| Labeled (tag: Label) (labeled: natural)
		| Reference (tag: Label).

	Definition isZero  (x: natural ): Prop :=
		match x with
			  Zero  => True
			| _ => False
		end.

	Definition isSuccessor  (x: natural ): Prop :=
		match x with
			  Successor n => True
			| _ => False
		end.

	Definition isLabeled  (x: natural ): Prop :=
		match x with
			  Labeled tag labeled => True
			| _ => False
		end.

	Definition isReference  (x: natural ): Prop :=
		match x with
			  Reference tag => True
			| _ => False
		end.
End Natural.