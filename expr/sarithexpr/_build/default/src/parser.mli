
(* The type of tokens. *)

type token = 
  | ZERO
  | TRUE
  | THEN
  | SUCC
  | RPAREN
  | PRED
  | OR
  | NOT
  | LPAREN
  | ISZERO
  | IF
  | FALSE
  | EOF
  | ELSE
  | AND

(* This exception is raised by the monolithic API functions. *)

exception Error

(* The monolithic API. *)

val prog: (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (Ast.expr)
