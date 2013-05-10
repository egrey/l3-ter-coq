let grammar = Grammar.gcreate (Plexer.gmake ())
let declaration = Grammar.Entry.create grammar "declaration"
let loc = ref 0

EXTEND
  GLOBAL: declaration;

  declaration:
  [ [ "type";
      i = LIDENT;
      pl = LIST0 parameter;
      "=";
      cl = LIST1 constructor SEP "|"  ->
          Type.Declaration (i, pl, cl) ] ];

  parameter:
  [ [ "(";
      i = LIDENT;
      ":";
      e = expression;
      ")" ->
          Type.Parameter (i, e) ] ];

  constructor:
  [ [ i = UIDENT;
      al = LIST0 argument ->
          Type.Constructor (i, al) ] ];

  argument:
  [ [ "(";
      i = LIDENT;
      ":";
      e = expression;
      ")" ->
          Type.Argument (i, e) ] ];

  expression:
  [ [ i = identifier ->
          Type.Type i ]
  | [ "(";
      e = expression;
      ")" ->
          Type.Parenthesized e ] 
  | [ e = expression;
      el = LIST1 expression ->
          Type.GenericType (e, el) ]
  | [ e = expression;
      "*";
      el = LIST1 expression SEP "*" ->
          Type.Tuple (e :: el) ] ];

  identifier:
  [ [ i = LIDENT -> i ]
  | [ i = UIDENT -> i ] ];
END

try
  let d = Grammar.Entry.parse declaration (Stream.of_channel stdin) in
  print_string (CoqGenerator.String.of_declaration d)
with Ploc.Exc(pos,ex) ->
  prerr_string "erreur ligne "; 
  prerr_int (Ploc.line_nb pos);
  prerr_string ",position "; 
  prerr_int (Ploc.bol_pos pos);
  prerr_newline()
