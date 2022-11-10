
(* The type of tokens. *)

type token = 
  | TRUE
  | THEN
  | RPAREN
  | LPAREN
  | IF
  | FALSE
  | EOF
  | ELSE

(* This exception is raised by the monolithic API functions. *)

exception Error

(* The monolithic API. *)

val prog: (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (Ast.boolExpr)
