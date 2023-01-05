
module MenhirBasics = struct
  
  exception Error
  
  let _eRR =
    fun _s ->
      raise Error
  
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
    | ID of (
# 25 "src/parser.mly"
       (string)
# 29 "src/parser.ml"
  )
    | FALSE
    | EQUALTO
    | EOF
    | ELSE
    | AND
  
end

include MenhirBasics

# 3 "src/parser.mly"
  
open Ast

# 45 "src/parser.ml"

type ('s, 'r) _menhir_state = 
  | MenhirState00 : ('s, _menhir_box_prog) _menhir_state
    (** State 00.
        Stack shape : .
        Start symbol: prog. *)

  | MenhirState03 : (('s, _menhir_box_prog) _menhir_cell1_SUCC, _menhir_box_prog) _menhir_state
    (** State 03.
        Stack shape : SUCC.
        Start symbol: prog. *)

  | MenhirState04 : (('s, _menhir_box_prog) _menhir_cell1_PRED, _menhir_box_prog) _menhir_state
    (** State 04.
        Stack shape : PRED.
        Start symbol: prog. *)

  | MenhirState05 : (('s, _menhir_box_prog) _menhir_cell1_NOT, _menhir_box_prog) _menhir_state
    (** State 05.
        Stack shape : NOT.
        Start symbol: prog. *)

  | MenhirState06 : (('s, _menhir_box_prog) _menhir_cell1_LPAREN, _menhir_box_prog) _menhir_state
    (** State 06.
        Stack shape : LPAREN.
        Start symbol: prog. *)

  | MenhirState09 : (('s, _menhir_box_prog) _menhir_cell1_LET _menhir_cell0_ID, _menhir_box_prog) _menhir_state
    (** State 09.
        Stack shape : LET ID.
        Start symbol: prog. *)

  | MenhirState10 : (('s, _menhir_box_prog) _menhir_cell1_ISZERO, _menhir_box_prog) _menhir_state
    (** State 10.
        Stack shape : ISZERO.
        Start symbol: prog. *)

  | MenhirState11 : (('s, _menhir_box_prog) _menhir_cell1_IF, _menhir_box_prog) _menhir_state
    (** State 11.
        Stack shape : IF.
        Start symbol: prog. *)

  | MenhirState15 : ((('s, _menhir_box_prog) _menhir_cell1_IF, _menhir_box_prog) _menhir_cell1_expr, _menhir_box_prog) _menhir_state
    (** State 15.
        Stack shape : IF expr.
        Start symbol: prog. *)

  | MenhirState17 : (('s, _menhir_box_prog) _menhir_cell1_expr, _menhir_box_prog) _menhir_state
    (** State 17.
        Stack shape : expr.
        Start symbol: prog. *)

  | MenhirState19 : (('s, _menhir_box_prog) _menhir_cell1_expr, _menhir_box_prog) _menhir_state
    (** State 19.
        Stack shape : expr.
        Start symbol: prog. *)

  | MenhirState21 : (((('s, _menhir_box_prog) _menhir_cell1_IF, _menhir_box_prog) _menhir_cell1_expr, _menhir_box_prog) _menhir_cell1_expr, _menhir_box_prog) _menhir_state
    (** State 21.
        Stack shape : IF expr expr.
        Start symbol: prog. *)

  | MenhirState25 : ((('s, _menhir_box_prog) _menhir_cell1_LET _menhir_cell0_ID, _menhir_box_prog) _menhir_cell1_expr, _menhir_box_prog) _menhir_state
    (** State 25.
        Stack shape : LET ID expr.
        Start symbol: prog. *)


and ('s, 'r) _menhir_cell1_expr = 
  | MenhirCell1_expr of 's * ('s, 'r) _menhir_state * (Ast.expr)

and 's _menhir_cell0_ID = 
  | MenhirCell0_ID of 's * (
# 25 "src/parser.mly"
       (string)
# 121 "src/parser.ml"
)

and ('s, 'r) _menhir_cell1_IF = 
  | MenhirCell1_IF of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_ISZERO = 
  | MenhirCell1_ISZERO of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_LET = 
  | MenhirCell1_LET of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_LPAREN = 
  | MenhirCell1_LPAREN of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_NOT = 
  | MenhirCell1_NOT of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_PRED = 
  | MenhirCell1_PRED of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_SUCC = 
  | MenhirCell1_SUCC of 's * ('s, 'r) _menhir_state

and _menhir_box_prog = 
  | MenhirBox_prog of (Ast.expr) [@@unboxed]

let _menhir_action_01 =
  fun () ->
    (
# 43 "src/parser.mly"
           ( True )
# 153 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_02 =
  fun () ->
    (
# 44 "src/parser.mly"
            ( False )
# 161 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_03 =
  fun e1 e2 e3 ->
    (
# 45 "src/parser.mly"
                                                       ( If (e1, e2, e3) )
# 169 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_04 =
  fun e ->
    (
# 46 "src/parser.mly"
                               (e)
# 177 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_05 =
  fun e1 e2 ->
    (
# 47 "src/parser.mly"
                                  ( And (e1, e2) )
# 185 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_06 =
  fun e1 e2 ->
    (
# 48 "src/parser.mly"
                                ( Or (e1, e2) )
# 193 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_07 =
  fun e ->
    (
# 49 "src/parser.mly"
                     ( Not(e) )
# 201 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_08 =
  fun e ->
    (
# 50 "src/parser.mly"
                        ( IsZero(e) )
# 209 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_09 =
  fun e ->
    (
# 51 "src/parser.mly"
                      ( Pred(e) )
# 217 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_10 =
  fun e ->
    (
# 52 "src/parser.mly"
                      ( Succ(e) )
# 225 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_11 =
  fun () ->
    (
# 53 "src/parser.mly"
           ( Zero )
# 233 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_12 =
  fun x ->
    (
# 54 "src/parser.mly"
             ( Var x )
# 241 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_13 =
  fun e1 e2 x ->
    (
# 55 "src/parser.mly"
                                                        ( Let(x,e1,e2) )
# 249 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_14 =
  fun e ->
    (
# 39 "src/parser.mly"
                   ( e )
# 257 "src/parser.ml"
     : (Ast.expr))

let _menhir_print_token : token -> string =
  fun _tok ->
    match _tok with
    | AND ->
        "AND"
    | ELSE ->
        "ELSE"
    | EOF ->
        "EOF"
    | EQUALTO ->
        "EQUALTO"
    | FALSE ->
        "FALSE"
    | ID _ ->
        "ID"
    | IF ->
        "IF"
    | IN ->
        "IN"
    | ISZERO ->
        "ISZERO"
    | LET ->
        "LET"
    | LPAREN ->
        "LPAREN"
    | NOT ->
        "NOT"
    | OR ->
        "OR"
    | PRED ->
        "PRED"
    | RPAREN ->
        "RPAREN"
    | SUCC ->
        "SUCC"
    | THEN ->
        "THEN"
    | TRUE ->
        "TRUE"
    | VAR ->
        "VAR"
    | ZERO ->
        "ZERO"

let _menhir_fail : unit -> 'a =
  fun () ->
    Printf.eprintf "Internal failure -- please contact the parser generator's developers.\n%!";
    assert false

include struct
  
  [@@@ocaml.warning "-4-37-39"]
  
  let rec _menhir_run_33 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | OR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_17 _menhir_stack _menhir_lexbuf _menhir_lexer
      | EOF ->
          let e = _v in
          let _v = _menhir_action_14 e in
          MenhirBox_prog _v
      | AND ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_19 _menhir_stack _menhir_lexbuf _menhir_lexer
      | _ ->
          _eRR ()
  
  and _menhir_run_17 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_expr -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | ZERO ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_11 () in
          _menhir_run_18 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState17 _tok
      | TRUE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_01 () in
          _menhir_run_18 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState17 _tok
      | SUCC ->
          _menhir_run_03 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState17
      | PRED ->
          _menhir_run_04 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState17
      | NOT ->
          _menhir_run_05 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState17
      | LPAREN ->
          _menhir_run_06 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState17
      | LET ->
          _menhir_run_07 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState17
      | ISZERO ->
          _menhir_run_10 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState17
      | IF ->
          _menhir_run_11 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState17
      | ID _v ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let x = _v in
          let _v = _menhir_action_12 x in
          _menhir_run_18 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState17 _tok
      | FALSE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_02 () in
          _menhir_run_18 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState17 _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_18 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_expr as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | AND ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_19 _menhir_stack _menhir_lexbuf _menhir_lexer
      | ELSE | EOF | IN | OR | RPAREN | THEN ->
          let MenhirCell1_expr (_menhir_stack, _menhir_s, e1) = _menhir_stack in
          let e2 = _v in
          let _v = _menhir_action_06 e1 e2 in
          _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_19 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_expr -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | ZERO ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_11 () in
          _menhir_run_20 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | TRUE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_01 () in
          _menhir_run_20 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | SUCC ->
          _menhir_run_03 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState19
      | PRED ->
          _menhir_run_04 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState19
      | NOT ->
          _menhir_run_05 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState19
      | LPAREN ->
          _menhir_run_06 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState19
      | LET ->
          _menhir_run_07 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState19
      | ISZERO ->
          _menhir_run_10 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState19
      | IF ->
          _menhir_run_11 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState19
      | ID _v ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let x = _v in
          let _v = _menhir_action_12 x in
          _menhir_run_20 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | FALSE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_02 () in
          _menhir_run_20 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_20 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_expr -> _ -> _ -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_expr (_menhir_stack, _menhir_s, e1) = _menhir_stack in
      let e2 = _v in
      let _v = _menhir_action_05 e1 e2 in
      _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_expr : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState00 ->
          _menhir_run_33 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState03 ->
          _menhir_run_31 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState04 ->
          _menhir_run_30 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState05 ->
          _menhir_run_29 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState06 ->
          _menhir_run_27 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState25 ->
          _menhir_run_26 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState09 ->
          _menhir_run_24 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState10 ->
          _menhir_run_23 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState21 ->
          _menhir_run_22 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState19 ->
          _menhir_run_20 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState17 ->
          _menhir_run_18 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState15 ->
          _menhir_run_16 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState11 ->
          _menhir_run_14 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_31 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_SUCC -> _ -> _ -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_SUCC (_menhir_stack, _menhir_s) = _menhir_stack in
      let e = _v in
      let _v = _menhir_action_10 e in
      _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_30 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_PRED -> _ -> _ -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_PRED (_menhir_stack, _menhir_s) = _menhir_stack in
      let e = _v in
      let _v = _menhir_action_09 e in
      _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_29 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_NOT -> _ -> _ -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_NOT (_menhir_stack, _menhir_s) = _menhir_stack in
      let e = _v in
      let _v = _menhir_action_07 e in
      _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_27 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_LPAREN as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | RPAREN ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let MenhirCell1_LPAREN (_menhir_stack, _menhir_s) = _menhir_stack in
          let e = _v in
          let _v = _menhir_action_04 e in
          _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | OR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_17 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_19 _menhir_stack _menhir_lexbuf _menhir_lexer
      | _ ->
          _eRR ()
  
  and _menhir_run_26 : type  ttv_stack. (((ttv_stack, _menhir_box_prog) _menhir_cell1_LET _menhir_cell0_ID, _menhir_box_prog) _menhir_cell1_expr as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | OR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_17 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_19 _menhir_stack _menhir_lexbuf _menhir_lexer
      | ELSE | EOF | IN | RPAREN | THEN ->
          let MenhirCell1_expr (_menhir_stack, _, e1) = _menhir_stack in
          let MenhirCell0_ID (_menhir_stack, x) = _menhir_stack in
          let MenhirCell1_LET (_menhir_stack, _menhir_s) = _menhir_stack in
          let e2 = _v in
          let _v = _menhir_action_13 e1 e2 x in
          _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_24 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_LET _menhir_cell0_ID as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | OR ->
          _menhir_run_17 _menhir_stack _menhir_lexbuf _menhir_lexer
      | IN ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | ZERO ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let _v = _menhir_action_11 () in
              _menhir_run_26 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState25 _tok
          | TRUE ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let _v = _menhir_action_01 () in
              _menhir_run_26 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState25 _tok
          | SUCC ->
              _menhir_run_03 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState25
          | PRED ->
              _menhir_run_04 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState25
          | NOT ->
              _menhir_run_05 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState25
          | LPAREN ->
              _menhir_run_06 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState25
          | LET ->
              _menhir_run_07 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState25
          | ISZERO ->
              _menhir_run_10 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState25
          | IF ->
              _menhir_run_11 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState25
          | ID _v_2 ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let x = _v_2 in
              let _v = _menhir_action_12 x in
              _menhir_run_26 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState25 _tok
          | FALSE ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let _v = _menhir_action_02 () in
              _menhir_run_26 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState25 _tok
          | _ ->
              _eRR ())
      | AND ->
          _menhir_run_19 _menhir_stack _menhir_lexbuf _menhir_lexer
      | _ ->
          _eRR ()
  
  and _menhir_run_03 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_SUCC (_menhir_stack, _menhir_s) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | ZERO ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_11 () in
          _menhir_run_31 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | TRUE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_01 () in
          _menhir_run_31 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | SUCC ->
          _menhir_run_03 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState03
      | PRED ->
          _menhir_run_04 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState03
      | NOT ->
          _menhir_run_05 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState03
      | LPAREN ->
          _menhir_run_06 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState03
      | LET ->
          _menhir_run_07 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState03
      | ISZERO ->
          _menhir_run_10 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState03
      | IF ->
          _menhir_run_11 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState03
      | ID _v ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let x = _v in
          let _v = _menhir_action_12 x in
          _menhir_run_31 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | FALSE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_02 () in
          _menhir_run_31 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_04 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_PRED (_menhir_stack, _menhir_s) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | ZERO ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_11 () in
          _menhir_run_30 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | TRUE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_01 () in
          _menhir_run_30 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | SUCC ->
          _menhir_run_03 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState04
      | PRED ->
          _menhir_run_04 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState04
      | NOT ->
          _menhir_run_05 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState04
      | LPAREN ->
          _menhir_run_06 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState04
      | LET ->
          _menhir_run_07 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState04
      | ISZERO ->
          _menhir_run_10 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState04
      | IF ->
          _menhir_run_11 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState04
      | ID _v ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let x = _v in
          let _v = _menhir_action_12 x in
          _menhir_run_30 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | FALSE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_02 () in
          _menhir_run_30 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_05 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_NOT (_menhir_stack, _menhir_s) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | ZERO ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_11 () in
          _menhir_run_29 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | TRUE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_01 () in
          _menhir_run_29 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | SUCC ->
          _menhir_run_03 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState05
      | PRED ->
          _menhir_run_04 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState05
      | NOT ->
          _menhir_run_05 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState05
      | LPAREN ->
          _menhir_run_06 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState05
      | LET ->
          _menhir_run_07 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState05
      | ISZERO ->
          _menhir_run_10 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState05
      | IF ->
          _menhir_run_11 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState05
      | ID _v ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let x = _v in
          let _v = _menhir_action_12 x in
          _menhir_run_29 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | FALSE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_02 () in
          _menhir_run_29 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_06 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_LPAREN (_menhir_stack, _menhir_s) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | ZERO ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_11 () in
          _menhir_run_27 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState06 _tok
      | TRUE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_01 () in
          _menhir_run_27 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState06 _tok
      | SUCC ->
          _menhir_run_03 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState06
      | PRED ->
          _menhir_run_04 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState06
      | NOT ->
          _menhir_run_05 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState06
      | LPAREN ->
          _menhir_run_06 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState06
      | LET ->
          _menhir_run_07 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState06
      | ISZERO ->
          _menhir_run_10 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState06
      | IF ->
          _menhir_run_11 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState06
      | ID _v ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let x = _v in
          let _v = _menhir_action_12 x in
          _menhir_run_27 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState06 _tok
      | FALSE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_02 () in
          _menhir_run_27 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState06 _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_07 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_LET (_menhir_stack, _menhir_s) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | ID _v ->
          let _menhir_stack = MenhirCell0_ID (_menhir_stack, _v) in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | EQUALTO ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              (match (_tok : MenhirBasics.token) with
              | ZERO ->
                  let _tok = _menhir_lexer _menhir_lexbuf in
                  let _v = _menhir_action_11 () in
                  _menhir_run_24 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState09 _tok
              | TRUE ->
                  let _tok = _menhir_lexer _menhir_lexbuf in
                  let _v = _menhir_action_01 () in
                  _menhir_run_24 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState09 _tok
              | SUCC ->
                  _menhir_run_03 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState09
              | PRED ->
                  _menhir_run_04 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState09
              | NOT ->
                  _menhir_run_05 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState09
              | LPAREN ->
                  _menhir_run_06 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState09
              | LET ->
                  _menhir_run_07 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState09
              | ISZERO ->
                  _menhir_run_10 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState09
              | IF ->
                  _menhir_run_11 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState09
              | ID _v_2 ->
                  let _tok = _menhir_lexer _menhir_lexbuf in
                  let x = _v_2 in
                  let _v = _menhir_action_12 x in
                  _menhir_run_24 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState09 _tok
              | FALSE ->
                  let _tok = _menhir_lexer _menhir_lexbuf in
                  let _v = _menhir_action_02 () in
                  _menhir_run_24 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState09 _tok
              | _ ->
                  _eRR ())
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_10 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_ISZERO (_menhir_stack, _menhir_s) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | ZERO ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_11 () in
          _menhir_run_23 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | TRUE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_01 () in
          _menhir_run_23 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | SUCC ->
          _menhir_run_03 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState10
      | PRED ->
          _menhir_run_04 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState10
      | NOT ->
          _menhir_run_05 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState10
      | LPAREN ->
          _menhir_run_06 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState10
      | LET ->
          _menhir_run_07 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState10
      | ISZERO ->
          _menhir_run_10 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState10
      | IF ->
          _menhir_run_11 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState10
      | ID _v ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let x = _v in
          let _v = _menhir_action_12 x in
          _menhir_run_23 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | FALSE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_02 () in
          _menhir_run_23 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_23 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_ISZERO -> _ -> _ -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_ISZERO (_menhir_stack, _menhir_s) = _menhir_stack in
      let e = _v in
      let _v = _menhir_action_08 e in
      _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_11 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_IF (_menhir_stack, _menhir_s) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | ZERO ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_11 () in
          _menhir_run_14 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState11 _tok
      | TRUE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_01 () in
          _menhir_run_14 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState11 _tok
      | SUCC ->
          _menhir_run_03 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState11
      | PRED ->
          _menhir_run_04 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState11
      | NOT ->
          _menhir_run_05 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState11
      | LPAREN ->
          _menhir_run_06 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState11
      | LET ->
          _menhir_run_07 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState11
      | ISZERO ->
          _menhir_run_10 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState11
      | IF ->
          _menhir_run_11 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState11
      | ID _v ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let x = _v in
          let _v = _menhir_action_12 x in
          _menhir_run_14 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState11 _tok
      | FALSE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_02 () in
          _menhir_run_14 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState11 _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_14 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_IF as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | THEN ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | ZERO ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let _v = _menhir_action_11 () in
              _menhir_run_16 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState15 _tok
          | TRUE ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let _v = _menhir_action_01 () in
              _menhir_run_16 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState15 _tok
          | SUCC ->
              _menhir_run_03 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState15
          | PRED ->
              _menhir_run_04 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState15
          | NOT ->
              _menhir_run_05 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState15
          | LPAREN ->
              _menhir_run_06 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState15
          | LET ->
              _menhir_run_07 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState15
          | ISZERO ->
              _menhir_run_10 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState15
          | IF ->
              _menhir_run_11 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState15
          | ID _v_2 ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let x = _v_2 in
              let _v = _menhir_action_12 x in
              _menhir_run_16 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState15 _tok
          | FALSE ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let _v = _menhir_action_02 () in
              _menhir_run_16 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState15 _tok
          | _ ->
              _eRR ())
      | OR ->
          _menhir_run_17 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND ->
          _menhir_run_19 _menhir_stack _menhir_lexbuf _menhir_lexer
      | _ ->
          _eRR ()
  
  and _menhir_run_16 : type  ttv_stack. (((ttv_stack, _menhir_box_prog) _menhir_cell1_IF, _menhir_box_prog) _menhir_cell1_expr as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | OR ->
          _menhir_run_17 _menhir_stack _menhir_lexbuf _menhir_lexer
      | ELSE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | ZERO ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let _v = _menhir_action_11 () in
              _menhir_run_22 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState21 _tok
          | TRUE ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let _v = _menhir_action_01 () in
              _menhir_run_22 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState21 _tok
          | SUCC ->
              _menhir_run_03 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState21
          | PRED ->
              _menhir_run_04 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState21
          | NOT ->
              _menhir_run_05 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState21
          | LPAREN ->
              _menhir_run_06 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState21
          | LET ->
              _menhir_run_07 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState21
          | ISZERO ->
              _menhir_run_10 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState21
          | IF ->
              _menhir_run_11 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState21
          | ID _v_2 ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let x = _v_2 in
              let _v = _menhir_action_12 x in
              _menhir_run_22 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState21 _tok
          | FALSE ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let _v = _menhir_action_02 () in
              _menhir_run_22 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState21 _tok
          | _ ->
              _eRR ())
      | AND ->
          _menhir_run_19 _menhir_stack _menhir_lexbuf _menhir_lexer
      | _ ->
          _eRR ()
  
  and _menhir_run_22 : type  ttv_stack. ((((ttv_stack, _menhir_box_prog) _menhir_cell1_IF, _menhir_box_prog) _menhir_cell1_expr, _menhir_box_prog) _menhir_cell1_expr as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | OR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_17 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_19 _menhir_stack _menhir_lexbuf _menhir_lexer
      | ELSE | EOF | IN | RPAREN | THEN ->
          let MenhirCell1_expr (_menhir_stack, _, e2) = _menhir_stack in
          let MenhirCell1_expr (_menhir_stack, _, e1) = _menhir_stack in
          let MenhirCell1_IF (_menhir_stack, _menhir_s) = _menhir_stack in
          let e3 = _v in
          let _v = _menhir_action_03 e1 e2 e3 in
          _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  let rec _menhir_run_00 : type  ttv_stack. ttv_stack -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | ZERO ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_11 () in
          _menhir_run_33 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState00 _tok
      | TRUE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_01 () in
          _menhir_run_33 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState00 _tok
      | SUCC ->
          _menhir_run_03 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState00
      | PRED ->
          _menhir_run_04 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState00
      | NOT ->
          _menhir_run_05 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState00
      | LPAREN ->
          _menhir_run_06 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState00
      | LET ->
          _menhir_run_07 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState00
      | ISZERO ->
          _menhir_run_10 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState00
      | IF ->
          _menhir_run_11 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState00
      | ID _v ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let x = _v in
          let _v = _menhir_action_12 x in
          _menhir_run_33 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState00 _tok
      | FALSE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_02 () in
          _menhir_run_33 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState00 _tok
      | _ ->
          _eRR ()
  
end

let prog =
  fun _menhir_lexer _menhir_lexbuf ->
    let _menhir_stack = () in
    let MenhirBox_prog v = _menhir_run_00 _menhir_stack _menhir_lexbuf _menhir_lexer in
    v
