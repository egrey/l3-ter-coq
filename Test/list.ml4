type list (t: Type) =
    Empty
  | Add (x: t) (l: list t)
  | Permute (p: list t * t -> t * list t)
