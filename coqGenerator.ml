module String : CodeGenerator.SIG = struct
    let of_matchedVariable = "x"

    let of_genericType typeIdentifier parameters =
        let mapping = List.map Type.parameterIdentifier parameters
        in  typeIdentifier ^ " " ^ (String.concat " " mapping)

    let rec of_expression = function
          Type.Type t ->
              t
        | Type.Parenthesized expression ->
              of_expression expression
        | Type.GenericType (t, parameters) ->
              String.concat " " (List.map of_expression (t :: parameters))
        | Type.Tuple expression ->
              String.concat " * " (List.map of_expression expression)
        | Type.Function (domain, codomain) ->
              (of_expression domain) ^ " -> " ^ (of_expression codomain)

    let of_argument argument =
        let argumentIdentifier = Type.argumentIdentifier argument
        and argumentType = of_expression (Type.argumentType argument)
        in  "(" ^ argumentIdentifier ^ ": " ^ argumentType ^ ")"

    let of_constructor constructor =
        let constructorIdentifier = Type.constructorIdentifier constructor
        and arguments =
            let mapping = List.map of_argument (Type.arguments constructor)
            in  String.concat " " mapping
        in  constructorIdentifier ^ " " ^ arguments

    let of_constructors constructors =
        let mapping = List.map of_constructor constructors
        in  "\n\t\t  " ^ (String.concat "\n\t\t| " mapping)

    let of_parameter parameter =
        let parameterIdentifier = Type.parameterIdentifier parameter
        and parameterType = of_expression (Type.parameterType parameter)
        in  "(" ^ parameterIdentifier ^ ": " ^ parameterType ^ ")"

    let of_parameters parameters =
        let mapping = List.map of_parameter parameters
        in  String.concat " " mapping

    let of_inputs typeIdentifier parameters =
        let of_parameter parameter =
            let parameterIdentifier = Type.parameterIdentifier parameter
            and parameterType = of_expression (Type.parameterType parameter)
            in  "{" ^ parameterIdentifier ^ ": " ^ parameterType ^ "}"
        in  let mapping = List.map of_parameter parameters
            and of_genericType = of_genericType typeIdentifier parameters
            in  let of_parameters = String.concat " " mapping
                in  of_parameters ^ " (" ^ of_matchedVariable ^ ": " ^ of_genericType ^ ")"
            
    let of_pattern constructor =
        let constructorIdentifier = Type.constructorIdentifier constructor
        and mapping = List.map Type.argumentIdentifier (Type.arguments constructor)
        in  constructorIdentifier ^ " " ^ (String.concat " " mapping)

    let of_observer typeIdentifier parameters constructor =
        let constructorIdentifier = Type.constructorIdentifier constructor
        and of_inputs = of_inputs typeIdentifier parameters
        and of_pattern = of_pattern constructor
        in  "Definition is" ^ constructorIdentifier ^ " " ^ of_inputs ^ ": Prop :=" ^
            "\n\t\tmatch "^ of_matchedVariable ^ " with" ^
            "\n\t\t\t  " ^ of_pattern ^ " => True" ^
            "\n\t\t\t| _ => False" ^
            "\n\t\tend."

    let of_observers declaration =
        let typeIdentifier = Type.identifier declaration
        and parameters = Type.parameters declaration
        and constructors = Type.constructors declaration
        in  let mapping = List.map (of_observer typeIdentifier parameters) constructors
            in  "\n\n\t" ^ String.concat "\n\n\t" mapping

    let of_module declaration =
        let typeIdentifier = Type.identifier declaration
        and parameters = Type.parameters declaration
        and parameterIdentifier = function Type.Parameter (i, _) -> Type.Type i
        in  let of_genericType =
                let mapping = List.map parameterIdentifier parameters
                in  Type.GenericType (Type.Type typeIdentifier, mapping)
            in  let labelConstructor = Type.Constructor
                    ("Labeled", [Type.Argument ("tag", Type.Type "Label"); Type.Argument ("labeled", of_genericType)])
                and referenceConstructor = Type.Constructor
                    ("Reference", [Type.Argument ("tag", Type.Type "Label")])
                in  let declaration = Type.Declaration (typeIdentifier, parameters,
                        (Type.constructors declaration) @ [labelConstructor; referenceConstructor])
                    in  let moduleIdentifier = String.capitalize (Type.identifier declaration)
                        and of_parameters = of_parameters parameters
                        and of_constructors = of_constructors (Type.constructors declaration)
                        and of_observers = of_observers declaration
                        in  "\nModule " ^ moduleIdentifier ^ "." ^
                            "\n\tParameter Label: Type." ^
                            "\n\n\tInductive " ^ typeIdentifier ^ " " ^ of_parameters ^ " :=" ^
                            of_constructors ^ "." ^
                            of_observers ^
                            "\nEnd " ^ moduleIdentifier ^ "."

    let of_comodule declaration =
        let typeIdentifier = Type.identifier declaration
        and of_parameters = of_parameters (Type.parameters declaration)
        and of_constructors = of_constructors (Type.constructors declaration)
        and of_observers = of_observers declaration
        in  let moduleIdentifier = "Co" ^ (String.capitalize typeIdentifier)
            in  "Module " ^ moduleIdentifier ^ "." ^
                "\n\tCoInductive " ^ typeIdentifier ^ " " ^ of_parameters ^ " :=" ^
                of_constructors ^ "." ^
                of_observers ^
                "\nEnd " ^ moduleIdentifier ^ "."

    let of_declaration declaration =
        let of_comodule = of_comodule declaration
        and of_module = of_module declaration
        in  of_comodule ^ "\n\n" ^ of_module
end
