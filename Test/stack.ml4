type stack (t: Type) =
      Empty
    | Push (x: t) (s: stack t)
