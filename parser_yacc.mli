type token =
  | Int of (int)
  | Float of (float)
  | Iden of (string)
  | UIden of (string)
  | Import
  | Datatype
  | Vertical
  | Val
  | Var
  | Match
  | With
  | Underline
  | Model
  | Transition
  | Property
  | If
  | Then
  | Else
  | For
  | In
  | While
  | Do
  | Done
  | LB1
  | RB1
  | LB2
  | RB2
  | LB3
  | RB3
  | Equal
  | Non_Equal
  | LT
  | GT
  | LE
  | GE
  | Comma
  | Semicolon
  | Dot
  | DotDot
  | Arrow
  | EOF
  | Add
  | AddDot
  | Minus
  | MinusDot
  | Mult
  | MultDot
  | Negb
  | Ando
  | Oro
  | And
  | Or
  | Neg
  | LArrow
  | Colon
  | ColonColon
  | Init
  | Top
  | Bottom
  | AX
  | EX
  | AF
  | EG
  | AR
  | EU
  | True
  | False
  | Function
  | TLst
  | TFloat
  | TAray
  | TInt
  | TBool
  | TUnt

val program :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> (string list) * (Ast.psymbol_tbl) * ((Ast.pkripke_model) option)
