type tree (t: Type) =
    Leaf
  | Node (n: tree t * t * tree t)
