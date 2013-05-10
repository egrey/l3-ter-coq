Module CoBit.
	CoInductive bit  :=
		  Zero 
		| One .

	Definition isZero  (x: bit ): Prop :=
		match x with
			  Zero  => True
			| _ => False
		end.

	Definition isOne  (x: bit ): Prop :=
		match x with
			  One  => True
			| _ => False
		end.
End CoBit.


Module Bit.
	Parameter Label: Type.

	Inductive bit  :=
		  Zero 
		| One 
		| Labeled (tag: Label) (labeled: bit)
		| Reference (tag: Label).

	Definition isZero  (x: bit ): Prop :=
		match x with
			  Zero  => True
			| _ => False
		end.

	Definition isOne  (x: bit ): Prop :=
		match x with
			  One  => True
			| _ => False
		end.

	Definition isLabeled  (x: bit ): Prop :=
		match x with
			  Labeled tag labeled => True
			| _ => False
		end.

	Definition isReference  (x: bit ): Prop :=
		match x with
			  Reference tag => True
			| _ => False
		end.
End Bit.