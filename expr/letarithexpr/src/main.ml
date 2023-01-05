(*main*)

open Ast

type exprval = Bool of bool | Nat of int

(**)
let rec string_of_expr = function
    True -> "True"
  | False -> "False"
  | If(e0,e1,e2) -> "If(" ^ (string_of_expr e0) ^ "," ^ (string_of_expr e1) ^ "," ^ (string_of_expr e2) ^ ")"
  | Or(e0,e1) -> (string_of_expr e0) ^ " " ^ "Or" ^ " " ^ (string_of_expr e1)  
  | And(e0,e1) -> (string_of_expr e0) ^ " " ^ "And" ^ " " ^ (string_of_expr e1) 
  | Not(e0) -> "Not(" ^ (string_of_expr e0) ^ ")" 
  | Zero -> "0"
  | Succ(e) -> "succ(" ^ string_of_expr e ^ ")"
  | Pred(e) -> "pred(" ^ string_of_expr e ^ ")"
  | IsZero(e) -> "iszero(" ^ string_of_expr e ^ ")"
  | Let(x,e1,e2) -> "let(" ^string x^ " = " ^ string_of_expr x ^ " in " ^ string_of_expr e1 ^ ")"
;;

let string_of_val = function
    Bool b -> if b then "true" else "false"
  | Nat n -> string_of_int n
;;

let parse (s : string ) : expr = 
    let lexbuf = Lexing.from_string s in
    let ast = Parser.prog Lexer.read lexbuf in ast
;;


exception TypeError of string

let rec eval = function
  True -> Bool true
| False -> Bool false
| Not(e) -> (match eval e with
    Bool b -> Bool(not b)
  | _ -> raise (TypeError "Not on nat")
)
| And(e1,e2) -> (match (eval e1,eval e2) with
    (Bool b1,Bool b2) -> Bool (b1 && b2)
  | _ -> raise (TypeError "Or on nat")
)
| Or(e1,e2) -> (match (eval e1,eval e2) with
    (Bool b1,Bool b2) -> Bool (b1 || b2)
  | _ -> raise (TypeError "Or on nat")
) 
| If(e0,e1,e2) -> (match eval e0 with
    Bool b -> if b then eval e1 else eval e2
  | _ -> raise (TypeError "If on nat guard")
)
| Zero -> Nat 0
| Succ(e) -> (match eval e with
    Nat n -> Nat (n+1)
  | _ -> raise (TypeError "Succ on bool")
)
| Pred(e) -> (match eval e with
  | Nat n when n>0 -> Nat (n-1)
  | _ -> raise (TypeError "pred on 0")
)
| IsZero(e) -> (match eval e with
  | Nat n -> Bool (n=0)
  | _ -> raise (TypeError "IsZero on bool")
)
;;

exception NoRuleApplies
exception PredOfZero

let rec is_nv = function
    Zero -> true
  | Succ(e) -> is_nv e
  | _ -> false

let rec trace1 = function
    If(True,e1,_) -> e1
  | If(False,_,e2) -> e2
  | If(e0,e1,e2) -> let e0' = trace1 e0 in If(e0',e1,e2)
  | Or(True,_) -> True
  | Or(False,e1) -> e1
  | Or(e0,e1) -> let e0' = trace1 e0 in Or(e0',e1)
  | And(True,e1) -> e1
  | And(False,_) -> False
  | And(e0,e1) -> let e0' = trace1 e0 in And(e0',e1)
  | Not(True) -> False
  | Not(False) -> True
  | Not(e0) -> let e0' = trace1 e0 in Not(e0')
  | Succ(e) -> let e' = trace1 e in Succ(e')
  | Pred(Zero) -> raise NoRuleApplies
  | Pred(Succ(e)) when is_nv e -> e
  | Pred(e) -> let e' = trace1 e in Pred(e')
  | IsZero(Zero) -> True
  | IsZero(Succ(e)) when is_nv e -> False  
  | IsZero(e) -> let e' = trace1 e in IsZero(e')  
  | Let(x,e1,e2) -> let e1' = trace1 e1 in Let(x,e1',e2)
  | _ -> raise NoRuleApplies
;;

let rec trace e = try
    let e' = trace1 e
    in e::(trace e')
with NoRuleApplies -> [e]
;; 

