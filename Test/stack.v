Module CoStack.
	CoInductive stack (t: Type) :=
		  Empty 
		| Push (x: t) (s: stack t).

	Definition isEmpty {t: Type} (x: stack t): Prop :=
		match x with
			  Empty  => True
			| _ => False
		end.

	Definition isPush {t: Type} (x: stack t): Prop :=
		match x with
			  Push x s => True
			| _ => False
		end.
End CoStack.


Module Stack.
	Parameter Label: Type.

	Inductive stack (t: Type) :=
		  Empty 
		| Push (x: t) (s: stack t)
		| Labeled (tag: Label) (labeled: stack t)
		| Reference (tag: Label).

	Definition isEmpty {t: Type} (x: stack t): Prop :=
		match x with
			  Empty  => True
			| _ => False
		end.

	Definition isPush {t: Type} (x: stack t): Prop :=
		match x with
			  Push x s => True
			| _ => False
		end.

	Definition isLabeled {t: Type} (x: stack t): Prop :=
		match x with
			  Labeled tag labeled => True
			| _ => False
		end.

	Definition isReference {t: Type} (x: stack t): Prop :=
		match x with
			  Reference tag => True
			| _ => False
		end.
End Stack.