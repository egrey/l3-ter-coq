type expression =
    Type of string
  | Parenthesized of expression
  | GenericType of expression * expression list
  | Tuple of expression list
  | Function of expression * expression

type argument = Argument of string * expression
let argumentIdentifier = function Argument (i, _) -> i
let argumentType = function Argument (_, t) -> t

type constructor = Constructor of string * argument list
let constructorIdentifier = function Constructor (i, _) -> i
let arguments = function Constructor (_, a) -> a

type parameter = Parameter of string * expression
let parameterIdentifier = function Parameter (i, _) -> i
let parameterType = function Parameter (_, t) -> t

type declaration = Declaration of string * parameter list * constructor list
let identifier = function Declaration (i, _, _) -> i
let parameters = function Declaration (_, p, _) -> p
let constructors = function Declaration (_, _, c)-> c
