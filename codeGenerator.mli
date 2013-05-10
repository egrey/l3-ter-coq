module type SIG = sig
    val of_expression: Type.expression -> string
    val of_argument: Type.argument -> string
    val of_constructor: Type.constructor -> string
    val of_parameter: Type.parameter -> string
    val of_declaration: Type.declaration -> string
end
