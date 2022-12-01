(*main*)

open Ast

exception TypeError of string;;

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
;;


let string_of_val = function
   n -> string_of_int n
;;

let parse (s : string ) : expr = 
    let lexbuf = Lexing.from_string s in
    let ast = Parser.prog Lexer.read lexbuf in ast
;;

let rec eval = function
      True ->  1
    | False ->  0
    | Not(e) -> (match eval e with
          0 ->  1
        | n when n > 0 ->  0
        | _ -> failwith "not possible"
      )
    | And(e1,e2) -> if eval e1 >  0 && eval e2 >  0 then  1 else  0
    | Or(e1,e2) -> if eval e1 >  0 || eval e2 >  0 then  1 else  0 
    | If(e0,e1,e2) -> if eval e0 >  0 then eval e1 else eval e2
    | Zero ->  0
    | Succ(e) -> eval e +1 
    | Pred(e) -> (match eval e with
          n when n <= 0 -> 0   
        | n when n > 0 -> (n-1)
        | _ -> failwith "not possible"    
      )
    | IsZero(e) -> (match eval e with
          0 ->  1   
        | n when n > 0 ->  0  
        | _ -> failwith "not possible" 
      )
;;

exception NoRuleApplies

let rec is_nv = function
    Zero -> true
  | Succ(e) -> is_nv e
  | _ -> false

let oneOrZero = function
     Zero -> false
    |Pred(Zero) -> false
    | _ -> true

let rec trace1 = function
    True -> Succ(Zero)
  | False -> Zero
  | If(Succ(Zero),e1,_) -> e1
  | If(Zero,_,e2) -> e2 
  | If(True,e1,_) -> e1
  | If(False,_,e2) -> e2
  | If(e0,e1,e2) -> let e0' = trace1 e0 in If(e0',e1,e2)
  | Or(Succ(Zero),_) -> Succ(Zero)
  | Or(Zero,e1) when oneOrZero e1 -> Succ(Zero)
  | Or(True,_) -> True
  | Or(False,e1) when oneOrZero e1 -> Succ(Zero) 
  | Or(e0,e1) -> let e0' = trace1 e0 in Or(e0',e1)
  | And(True,False) -> Zero
  | And(Succ(Zero),e1) when oneOrZero e1-> Succ(Zero)
  | And(Zero,_) -> Zero
  | And(True,e1) when oneOrZero e1 -> Succ(Zero) 
  | And(False,_) -> False
  | And(e0,e1) -> let e0' = trace1 e0 in And(e0',e1)
  | Not(Zero) -> Succ(Zero)
  | Not(Succ(Zero)) -> Zero
  | Not(True) -> False
  | Not(False) -> True
  | Not(e0) -> let e0' = trace1 e0 in Not(e0')
  | Succ(e) -> let e' = trace1 e in Succ(e')
  | Pred(Zero) -> Zero
  | Pred(Succ(e)) when is_nv e -> e
  | Pred(e) -> let e' = trace1 e in Pred(e')
  | IsZero(Zero) -> Succ(Zero)
  | IsZero(Succ(e)) when is_nv e -> False  
  | IsZero(e) -> let e' = trace1 e in IsZero(e')
  | _ -> raise NoRuleApplies
;;

let rec trace e = try
    let e' = trace1 e
    in e :: (trace e')
with NoRuleApplies -> [e]
;; 

(*
succ 0 and succ succ 0 -> 2 [NO: expected 1]
true and succ succ pred pred succ 0 -> 2 [NO: expected 1]
0 or succ succ 0 -> 2 [NO: expected 1]
*)