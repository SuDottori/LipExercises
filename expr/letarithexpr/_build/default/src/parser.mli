
(* The type of tokens. *)

type token = 
  | ZERO
  | VAR
  | TRUE
  | THEN
  | SUCC
  | RPAREN
  | PRED
  | OR
  | NOT
  | LPAREN
  | LET
  | ISZERO
  | IN
  | IF
  | ID of (string)
  | FALSE
  | EQUALTO
  | EOF
  | ELSE
  | AND

(* This exception is raised by the monolithic API functions. *)

exception Error

(* The monolithic API. *)

val prog: (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (Ast.expr)
