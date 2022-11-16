
module MenhirBasics = struct
  
  exception Error
  
  let _eRR =
    fun _s ->
      raise Error
  
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
  
end

include MenhirBasics

# 3 "src/parser.mly"
  
open Ast

# 36 "src/parser.ml"

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

  | MenhirState07 : (('s, _menhir_box_prog) _menhir_cell1_ISZERO, _menhir_box_prog) _menhir_state
    (** State 07.
        Stack shape : ISZERO.
        Start symbol: prog. *)

  | MenhirState08 : (('s, _menhir_box_prog) _menhir_cell1_IF, _menhir_box_prog) _menhir_state
    (** State 08.
        Stack shape : IF.
        Start symbol: prog. *)

  | MenhirState11 : ((('s, _menhir_box_prog) _menhir_cell1_IF, _menhir_box_prog) _menhir_cell1_expr, _menhir_box_prog) _menhir_state
    (** State 11.
        Stack shape : IF expr.
        Start symbol: prog. *)

  | MenhirState13 : (('s, _menhir_box_prog) _menhir_cell1_expr, _menhir_box_prog) _menhir_state
    (** State 13.
        Stack shape : expr.
        Start symbol: prog. *)

  | MenhirState15 : (('s, _menhir_box_prog) _menhir_cell1_expr, _menhir_box_prog) _menhir_state
    (** State 15.
        Stack shape : expr.
        Start symbol: prog. *)

  | MenhirState17 : (((('s, _menhir_box_prog) _menhir_cell1_IF, _menhir_box_prog) _menhir_cell1_expr, _menhir_box_prog) _menhir_cell1_expr, _menhir_box_prog) _menhir_state
    (** State 17.
        Stack shape : IF expr expr.
        Start symbol: prog. *)


and ('s, 'r) _menhir_cell1_expr = 
  | MenhirCell1_expr of 's * ('s, 'r) _menhir_state * (Ast.expr)

and ('s, 'r) _menhir_cell1_IF = 
  | MenhirCell1_IF of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_ISZERO = 
  | MenhirCell1_ISZERO of 's * ('s, 'r) _menhir_state

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
# 38 "src/parser.mly"
           ( True )
# 124 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_02 =
  fun () ->
    (
# 39 "src/parser.mly"
            ( False )
# 132 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_03 =
  fun e1 e2 e3 ->
    (
# 40 "src/parser.mly"
                                                       ( If (e1, e2, e3) )
# 140 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_04 =
  fun e ->
    (
# 41 "src/parser.mly"
                               (e)
# 148 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_05 =
  fun e1 e2 ->
    (
# 42 "src/parser.mly"
                                  ( And (e1, e2) )
# 156 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_06 =
  fun e1 e2 ->
    (
# 43 "src/parser.mly"
                                ( Or (e1, e2) )
# 164 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_07 =
  fun e ->
    (
# 44 "src/parser.mly"
                     ( Not(e) )
# 172 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_08 =
  fun e ->
    (
# 45 "src/parser.mly"
                        ( IsZero(e) )
# 180 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_09 =
  fun e ->
    (
# 46 "src/parser.mly"
                      ( Pred(e) )
# 188 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_10 =
  fun e ->
    (
# 47 "src/parser.mly"
                      ( Succ(e) )
# 196 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_11 =
  fun () ->
    (
# 48 "src/parser.mly"
           ( Zero )
# 204 "src/parser.ml"
     : (Ast.expr))

let _menhir_action_12 =
  fun e ->
    (
# 34 "src/parser.mly"
                   ( e )
# 212 "src/parser.ml"
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
    | FALSE ->
        "FALSE"
    | IF ->
        "IF"
    | ISZERO ->
        "ISZERO"
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
    | ZERO ->
        "ZERO"

let _menhir_fail : unit -> 'a =
  fun () ->
    Printf.eprintf "Internal failure -- please contact the parser generator's developers.\n%!";
    assert false

include struct
  
  [@@@ocaml.warning "-4-37-39"]
  
  let rec _menhir_run_26 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | OR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_13 _menhir_stack _menhir_lexbuf _menhir_lexer
      | EOF ->
          let e = _v in
          let _v = _menhir_action_12 e in
          MenhirBox_prog _v
      | AND ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_15 _menhir_stack _menhir_lexbuf _menhir_lexer
      | _ ->
          _eRR ()
  
  and _menhir_run_13 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_expr -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | ZERO ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_11 () in
          _menhir_run_14 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState13 _tok
      | TRUE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_01 () in
          _menhir_run_14 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState13 _tok
      | SUCC ->
          _menhir_run_03 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState13
      | PRED ->
          _menhir_run_04 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState13
      | NOT ->
          _menhir_run_05 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState13
      | LPAREN ->
          _menhir_run_06 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState13
      | ISZERO ->
          _menhir_run_07 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState13
      | IF ->
          _menhir_run_08 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState13
      | FALSE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_02 () in
          _menhir_run_14 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState13 _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_14 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_expr as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | AND ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_15 _menhir_stack _menhir_lexbuf _menhir_lexer
      | ELSE | EOF | OR | RPAREN | THEN ->
          let MenhirCell1_expr (_menhir_stack, _menhir_s, e1) = _menhir_stack in
          let e2 = _v in
          let _v = _menhir_action_06 e1 e2 in
          _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_15 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_expr -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | ZERO ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_11 () in
          _menhir_run_16 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | TRUE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_01 () in
          _menhir_run_16 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | SUCC ->
          _menhir_run_03 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState15
      | PRED ->
          _menhir_run_04 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState15
      | NOT ->
          _menhir_run_05 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState15
      | LPAREN ->
          _menhir_run_06 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState15
      | ISZERO ->
          _menhir_run_07 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState15
      | IF ->
          _menhir_run_08 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState15
      | FALSE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_02 () in
          _menhir_run_16 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_16 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_expr -> _ -> _ -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_expr (_menhir_stack, _menhir_s, e1) = _menhir_stack in
      let e2 = _v in
      let _v = _menhir_action_05 e1 e2 in
      _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_expr : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState00 ->
          _menhir_run_26 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState03 ->
          _menhir_run_24 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState04 ->
          _menhir_run_23 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState05 ->
          _menhir_run_22 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState06 ->
          _menhir_run_20 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState07 ->
          _menhir_run_19 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState17 ->
          _menhir_run_18 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState15 ->
          _menhir_run_16 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState13 ->
          _menhir_run_14 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState11 ->
          _menhir_run_12 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState08 ->
          _menhir_run_10 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_24 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_SUCC -> _ -> _ -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_SUCC (_menhir_stack, _menhir_s) = _menhir_stack in
      let e = _v in
      let _v = _menhir_action_10 e in
      _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_23 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_PRED -> _ -> _ -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_PRED (_menhir_stack, _menhir_s) = _menhir_stack in
      let e = _v in
      let _v = _menhir_action_09 e in
      _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_22 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_NOT -> _ -> _ -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_NOT (_menhir_stack, _menhir_s) = _menhir_stack in
      let e = _v in
      let _v = _menhir_action_07 e in
      _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_20 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_LPAREN as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
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
          _menhir_run_13 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_15 _menhir_stack _menhir_lexbuf _menhir_lexer
      | _ ->
          _eRR ()
  
  and _menhir_run_19 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_ISZERO -> _ -> _ -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_ISZERO (_menhir_stack, _menhir_s) = _menhir_stack in
      let e = _v in
      let _v = _menhir_action_08 e in
      _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_18 : type  ttv_stack. ((((ttv_stack, _menhir_box_prog) _menhir_cell1_IF, _menhir_box_prog) _menhir_cell1_expr, _menhir_box_prog) _menhir_cell1_expr as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | OR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_13 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_15 _menhir_stack _menhir_lexbuf _menhir_lexer
      | ELSE | EOF | RPAREN | THEN ->
          let MenhirCell1_expr (_menhir_stack, _, e2) = _menhir_stack in
          let MenhirCell1_expr (_menhir_stack, _, e1) = _menhir_stack in
          let MenhirCell1_IF (_menhir_stack, _menhir_s) = _menhir_stack in
          let e3 = _v in
          let _v = _menhir_action_03 e1 e2 e3 in
          _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_12 : type  ttv_stack. (((ttv_stack, _menhir_box_prog) _menhir_cell1_IF, _menhir_box_prog) _menhir_cell1_expr as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | OR ->
          _menhir_run_13 _menhir_stack _menhir_lexbuf _menhir_lexer
      | ELSE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
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
          | ISZERO ->
              _menhir_run_07 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState17
          | IF ->
              _menhir_run_08 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState17
          | FALSE ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let _v = _menhir_action_02 () in
              _menhir_run_18 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState17 _tok
          | _ ->
              _eRR ())
      | AND ->
          _menhir_run_15 _menhir_stack _menhir_lexbuf _menhir_lexer
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
          _menhir_run_24 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | TRUE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_01 () in
          _menhir_run_24 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | SUCC ->
          _menhir_run_03 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState03
      | PRED ->
          _menhir_run_04 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState03
      | NOT ->
          _menhir_run_05 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState03
      | LPAREN ->
          _menhir_run_06 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState03
      | ISZERO ->
          _menhir_run_07 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState03
      | IF ->
          _menhir_run_08 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState03
      | FALSE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_02 () in
          _menhir_run_24 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
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
          _menhir_run_23 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | TRUE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_01 () in
          _menhir_run_23 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | SUCC ->
          _menhir_run_03 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState04
      | PRED ->
          _menhir_run_04 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState04
      | NOT ->
          _menhir_run_05 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState04
      | LPAREN ->
          _menhir_run_06 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState04
      | ISZERO ->
          _menhir_run_07 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState04
      | IF ->
          _menhir_run_08 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState04
      | FALSE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_02 () in
          _menhir_run_23 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
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
          _menhir_run_22 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | TRUE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_01 () in
          _menhir_run_22 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | SUCC ->
          _menhir_run_03 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState05
      | PRED ->
          _menhir_run_04 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState05
      | NOT ->
          _menhir_run_05 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState05
      | LPAREN ->
          _menhir_run_06 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState05
      | ISZERO ->
          _menhir_run_07 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState05
      | IF ->
          _menhir_run_08 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState05
      | FALSE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_02 () in
          _menhir_run_22 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
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
          _menhir_run_20 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState06 _tok
      | TRUE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_01 () in
          _menhir_run_20 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState06 _tok
      | SUCC ->
          _menhir_run_03 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState06
      | PRED ->
          _menhir_run_04 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState06
      | NOT ->
          _menhir_run_05 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState06
      | LPAREN ->
          _menhir_run_06 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState06
      | ISZERO ->
          _menhir_run_07 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState06
      | IF ->
          _menhir_run_08 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState06
      | FALSE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_02 () in
          _menhir_run_20 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState06 _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_07 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_ISZERO (_menhir_stack, _menhir_s) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | ZERO ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_11 () in
          _menhir_run_19 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | TRUE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_01 () in
          _menhir_run_19 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | SUCC ->
          _menhir_run_03 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState07
      | PRED ->
          _menhir_run_04 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState07
      | NOT ->
          _menhir_run_05 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState07
      | LPAREN ->
          _menhir_run_06 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState07
      | ISZERO ->
          _menhir_run_07 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState07
      | IF ->
          _menhir_run_08 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState07
      | FALSE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_02 () in
          _menhir_run_19 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_08 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_IF (_menhir_stack, _menhir_s) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | ZERO ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_11 () in
          _menhir_run_10 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState08 _tok
      | TRUE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_01 () in
          _menhir_run_10 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState08 _tok
      | SUCC ->
          _menhir_run_03 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState08
      | PRED ->
          _menhir_run_04 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState08
      | NOT ->
          _menhir_run_05 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState08
      | LPAREN ->
          _menhir_run_06 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState08
      | ISZERO ->
          _menhir_run_07 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState08
      | IF ->
          _menhir_run_08 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState08
      | FALSE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_02 () in
          _menhir_run_10 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState08 _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_10 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_IF as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | THEN ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | ZERO ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let _v = _menhir_action_11 () in
              _menhir_run_12 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState11 _tok
          | TRUE ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let _v = _menhir_action_01 () in
              _menhir_run_12 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState11 _tok
          | SUCC ->
              _menhir_run_03 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState11
          | PRED ->
              _menhir_run_04 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState11
          | NOT ->
              _menhir_run_05 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState11
          | LPAREN ->
              _menhir_run_06 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState11
          | ISZERO ->
              _menhir_run_07 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState11
          | IF ->
              _menhir_run_08 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState11
          | FALSE ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let _v = _menhir_action_02 () in
              _menhir_run_12 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState11 _tok
          | _ ->
              _eRR ())
      | OR ->
          _menhir_run_13 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND ->
          _menhir_run_15 _menhir_stack _menhir_lexbuf _menhir_lexer
      | _ ->
          _eRR ()
  
  let rec _menhir_run_00 : type  ttv_stack. ttv_stack -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | ZERO ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_11 () in
          _menhir_run_26 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState00 _tok
      | TRUE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_01 () in
          _menhir_run_26 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState00 _tok
      | SUCC ->
          _menhir_run_03 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState00
      | PRED ->
          _menhir_run_04 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState00
      | NOT ->
          _menhir_run_05 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState00
      | LPAREN ->
          _menhir_run_06 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState00
      | ISZERO ->
          _menhir_run_07 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState00
      | IF ->
          _menhir_run_08 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState00
      | FALSE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_02 () in
          _menhir_run_26 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState00 _tok
      | _ ->
          _eRR ()
  
end

let prog =
  fun _menhir_lexer _menhir_lexbuf ->
    let _menhir_stack = () in
    let MenhirBox_prog v = _menhir_run_00 _menhir_stack _menhir_lexbuf _menhir_lexer in
    v
