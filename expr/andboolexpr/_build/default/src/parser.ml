
module MenhirBasics = struct
  
  exception Error
  
  let _eRR =
    fun _s ->
      raise Error
  
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
  
end

include MenhirBasics

# 1 "src/parser.mly"
  
open Ast

# 32 "src/parser.ml"

type ('s, 'r) _menhir_state = 
  | MenhirState00 : ('s, _menhir_box_prog) _menhir_state
    (** State 00.
        Stack shape : .
        Start symbol: prog. *)

  | MenhirState02 : (('s, _menhir_box_prog) _menhir_cell1_NOT, _menhir_box_prog) _menhir_state
    (** State 02.
        Stack shape : NOT.
        Start symbol: prog. *)

  | MenhirState03 : (('s, _menhir_box_prog) _menhir_cell1_LPAREN, _menhir_box_prog) _menhir_state
    (** State 03.
        Stack shape : LPAREN.
        Start symbol: prog. *)

  | MenhirState04 : (('s, _menhir_box_prog) _menhir_cell1_IF, _menhir_box_prog) _menhir_state
    (** State 04.
        Stack shape : IF.
        Start symbol: prog. *)

  | MenhirState07 : ((('s, _menhir_box_prog) _menhir_cell1_IF, _menhir_box_prog) _menhir_cell1_expr, _menhir_box_prog) _menhir_state
    (** State 07.
        Stack shape : IF expr.
        Start symbol: prog. *)

  | MenhirState09 : (('s, _menhir_box_prog) _menhir_cell1_expr, _menhir_box_prog) _menhir_state
    (** State 09.
        Stack shape : expr.
        Start symbol: prog. *)

  | MenhirState11 : (('s, _menhir_box_prog) _menhir_cell1_expr, _menhir_box_prog) _menhir_state
    (** State 11.
        Stack shape : expr.
        Start symbol: prog. *)

  | MenhirState13 : (((('s, _menhir_box_prog) _menhir_cell1_IF, _menhir_box_prog) _menhir_cell1_expr, _menhir_box_prog) _menhir_cell1_expr, _menhir_box_prog) _menhir_state
    (** State 13.
        Stack shape : IF expr expr.
        Start symbol: prog. *)


and ('s, 'r) _menhir_cell1_expr = 
  | MenhirCell1_expr of 's * ('s, 'r) _menhir_state * (Ast.boolExpr)

and ('s, 'r) _menhir_cell1_IF = 
  | MenhirCell1_IF of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_LPAREN = 
  | MenhirCell1_LPAREN of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_NOT = 
  | MenhirCell1_NOT of 's * ('s, 'r) _menhir_state

and _menhir_box_prog = 
  | MenhirBox_prog of (Ast.boolExpr) [@@unboxed]

let _menhir_action_1 =
  fun () ->
    (
# 33 "src/parser.mly"
           ( True )
# 96 "src/parser.ml"
     : (Ast.boolExpr))

let _menhir_action_2 =
  fun () ->
    (
# 34 "src/parser.mly"
            ( False )
# 104 "src/parser.ml"
     : (Ast.boolExpr))

let _menhir_action_3 =
  fun e1 e2 e3 ->
    (
# 35 "src/parser.mly"
                                                       ( If (e1, e2, e3) )
# 112 "src/parser.ml"
     : (Ast.boolExpr))

let _menhir_action_4 =
  fun e ->
    (
# 36 "src/parser.mly"
                               (e)
# 120 "src/parser.ml"
     : (Ast.boolExpr))

let _menhir_action_5 =
  fun e1 e2 ->
    (
# 37 "src/parser.mly"
                                  ( And (e1, e2) )
# 128 "src/parser.ml"
     : (Ast.boolExpr))

let _menhir_action_6 =
  fun e1 e2 ->
    (
# 38 "src/parser.mly"
                                ( Or (e1, e2) )
# 136 "src/parser.ml"
     : (Ast.boolExpr))

let _menhir_action_7 =
  fun e ->
    (
# 39 "src/parser.mly"
                     ( Not(e) )
# 144 "src/parser.ml"
     : (Ast.boolExpr))

let _menhir_action_8 =
  fun e ->
    (
# 27 "src/parser.mly"
                   ( e )
# 152 "src/parser.ml"
     : (Ast.boolExpr))

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
    | LPAREN ->
        "LPAREN"
    | NOT ->
        "NOT"
    | OR ->
        "OR"
    | RPAREN ->
        "RPAREN"
    | THEN ->
        "THEN"
    | TRUE ->
        "TRUE"

let _menhir_fail : unit -> 'a =
  fun () ->
    Printf.eprintf "Internal failure -- please contact the parser generator's developers.\n%!";
    assert false

include struct
  
  [@@@ocaml.warning "-4-37-39"]
  
  let rec _menhir_run_19 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | OR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_09 _menhir_stack _menhir_lexbuf _menhir_lexer
      | EOF ->
          let e = _v in
          let _v = _menhir_action_8 e in
          MenhirBox_prog _v
      | AND ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_11 _menhir_stack _menhir_lexbuf _menhir_lexer
      | _ ->
          _eRR ()
  
  and _menhir_run_09 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_expr -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | TRUE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_1 () in
          _menhir_run_10 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState09 _tok
      | NOT ->
          _menhir_run_02 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState09
      | LPAREN ->
          _menhir_run_03 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState09
      | IF ->
          _menhir_run_04 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState09
      | FALSE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_2 () in
          _menhir_run_10 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState09 _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_10 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_expr as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | AND ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_11 _menhir_stack _menhir_lexbuf _menhir_lexer
      | ELSE | EOF | OR | RPAREN | THEN ->
          let MenhirCell1_expr (_menhir_stack, _menhir_s, e1) = _menhir_stack in
          let e2 = _v in
          let _v = _menhir_action_6 e1 e2 in
          _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_11 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_expr -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | TRUE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_1 () in
          _menhir_run_12 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | NOT ->
          _menhir_run_02 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState11
      | LPAREN ->
          _menhir_run_03 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState11
      | IF ->
          _menhir_run_04 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState11
      | FALSE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_2 () in
          _menhir_run_12 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_12 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_expr -> _ -> _ -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_expr (_menhir_stack, _menhir_s, e1) = _menhir_stack in
      let e2 = _v in
      let _v = _menhir_action_5 e1 e2 in
      _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_expr : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState00 ->
          _menhir_run_19 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState02 ->
          _menhir_run_17 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState03 ->
          _menhir_run_15 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState13 ->
          _menhir_run_14 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState11 ->
          _menhir_run_12 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState09 ->
          _menhir_run_10 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState07 ->
          _menhir_run_08 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState04 ->
          _menhir_run_06 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_17 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_NOT -> _ -> _ -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_NOT (_menhir_stack, _menhir_s) = _menhir_stack in
      let e = _v in
      let _v = _menhir_action_7 e in
      _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_15 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_LPAREN as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | RPAREN ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let MenhirCell1_LPAREN (_menhir_stack, _menhir_s) = _menhir_stack in
          let e = _v in
          let _v = _menhir_action_4 e in
          _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | OR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_09 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_11 _menhir_stack _menhir_lexbuf _menhir_lexer
      | _ ->
          _eRR ()
  
  and _menhir_run_14 : type  ttv_stack. ((((ttv_stack, _menhir_box_prog) _menhir_cell1_IF, _menhir_box_prog) _menhir_cell1_expr, _menhir_box_prog) _menhir_cell1_expr as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | OR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_09 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_11 _menhir_stack _menhir_lexbuf _menhir_lexer
      | ELSE | EOF | RPAREN | THEN ->
          let MenhirCell1_expr (_menhir_stack, _, e2) = _menhir_stack in
          let MenhirCell1_expr (_menhir_stack, _, e1) = _menhir_stack in
          let MenhirCell1_IF (_menhir_stack, _menhir_s) = _menhir_stack in
          let e3 = _v in
          let _v = _menhir_action_3 e1 e2 e3 in
          _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_08 : type  ttv_stack. (((ttv_stack, _menhir_box_prog) _menhir_cell1_IF, _menhir_box_prog) _menhir_cell1_expr as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | OR ->
          _menhir_run_09 _menhir_stack _menhir_lexbuf _menhir_lexer
      | ELSE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | TRUE ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let _v = _menhir_action_1 () in
              _menhir_run_14 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState13 _tok
          | NOT ->
              _menhir_run_02 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState13
          | LPAREN ->
              _menhir_run_03 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState13
          | IF ->
              _menhir_run_04 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState13
          | FALSE ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let _v = _menhir_action_2 () in
              _menhir_run_14 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState13 _tok
          | _ ->
              _eRR ())
      | AND ->
          _menhir_run_11 _menhir_stack _menhir_lexbuf _menhir_lexer
      | _ ->
          _eRR ()
  
  and _menhir_run_02 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_NOT (_menhir_stack, _menhir_s) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | TRUE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_1 () in
          _menhir_run_17 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | NOT ->
          _menhir_run_02 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState02
      | LPAREN ->
          _menhir_run_03 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState02
      | IF ->
          _menhir_run_04 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState02
      | FALSE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_2 () in
          _menhir_run_17 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_03 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_LPAREN (_menhir_stack, _menhir_s) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | TRUE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_1 () in
          _menhir_run_15 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState03 _tok
      | NOT ->
          _menhir_run_02 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState03
      | LPAREN ->
          _menhir_run_03 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState03
      | IF ->
          _menhir_run_04 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState03
      | FALSE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_2 () in
          _menhir_run_15 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState03 _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_04 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_IF (_menhir_stack, _menhir_s) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | TRUE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_1 () in
          _menhir_run_06 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState04 _tok
      | NOT ->
          _menhir_run_02 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState04
      | LPAREN ->
          _menhir_run_03 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState04
      | IF ->
          _menhir_run_04 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState04
      | FALSE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_2 () in
          _menhir_run_06 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState04 _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_06 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_IF as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | THEN ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | TRUE ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let _v = _menhir_action_1 () in
              _menhir_run_08 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState07 _tok
          | NOT ->
              _menhir_run_02 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState07
          | LPAREN ->
              _menhir_run_03 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState07
          | IF ->
              _menhir_run_04 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState07
          | FALSE ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let _v = _menhir_action_2 () in
              _menhir_run_08 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState07 _tok
          | _ ->
              _eRR ())
      | OR ->
          _menhir_run_09 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND ->
          _menhir_run_11 _menhir_stack _menhir_lexbuf _menhir_lexer
      | _ ->
          _eRR ()
  
  let rec _menhir_run_00 : type  ttv_stack. ttv_stack -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | TRUE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_1 () in
          _menhir_run_19 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState00 _tok
      | NOT ->
          _menhir_run_02 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState00
      | LPAREN ->
          _menhir_run_03 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState00
      | IF ->
          _menhir_run_04 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState00
      | FALSE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_2 () in
          _menhir_run_19 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState00 _tok
      | _ ->
          _eRR ()
  
end

let prog =
  fun _menhir_lexer _menhir_lexbuf ->
    let _menhir_stack = () in
    let MenhirBox_prog v = _menhir_run_00 _menhir_stack _menhir_lexbuf _menhir_lexer in
    v
