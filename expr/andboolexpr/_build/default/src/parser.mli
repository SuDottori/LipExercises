
(* The type of tokens. *)

type token = 
  | TRUE
  | THEN
  | RPAREN
  | OR
  | NOT
  | LPAREN
  | IF
  | FALSE
  | EOF
  | ELSE
  | AND

(* This exception is raised by the monolithic API functions. *)

exception Error

(* The monolithic API. *)

val prog: (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (Ast.boolExpr)
