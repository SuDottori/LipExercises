
module MenhirBasics = struct
  
  exception Error
  
  let _eRR =
    fun _s ->
      raise Error
  
  type token = 
    | TRUE
    | THEN
    | RPAREN
    | LPAREN
    | IF
    | FALSE
    | EOF
    | ELSE
  
end

include MenhirBasics

# 1 "src/parser.mly"
  
open Ast

# 29 "src/parser.ml"

type ('s, 'r) _menhir_state = 
  | MenhirState00 : ('s, _menhir_box_prog) _menhir_state
    (** State 00.
        Stack shape : .
        Start symbol: prog. *)

  | MenhirState02 : (('s, _menhir_box_prog) _menhir_cell1_LPAREN, _menhir_box_prog) _menhir_state
    (** State 02.
        Stack shape : LPAREN.
        Start symbol: prog. *)

  | MenhirState03 : (('s, _menhir_box_prog) _menhir_cell1_IF, _menhir_box_prog) _menhir_state
    (** State 03.
        Stack shape : IF.
        Start symbol: prog. *)

  | MenhirState06 : ((('s, _menhir_box_prog) _menhir_cell1_IF, _menhir_box_prog) _menhir_cell1_expr, _menhir_box_prog) _menhir_state
    (** State 06.
        Stack shape : IF expr.
        Start symbol: prog. *)

  | MenhirState08 : (((('s, _menhir_box_prog) _menhir_cell1_IF, _menhir_box_prog) _menhir_cell1_expr, _menhir_box_prog) _menhir_cell1_expr, _menhir_box_prog) _menhir_state
    (** State 08.
        Stack shape : IF expr expr.
        Start symbol: prog. *)


and ('s, 'r) _menhir_cell1_expr = 
  | MenhirCell1_expr of 's * ('s, 'r) _menhir_state * (Ast.boolExpr)

and ('s, 'r) _menhir_cell1_IF = 
  | MenhirCell1_IF of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_LPAREN = 
  | MenhirCell1_LPAREN of 's * ('s, 'r) _menhir_state

and _menhir_box_prog = 
  | MenhirBox_prog of (Ast.boolExpr) [@@unboxed]

let _menhir_action_1 =
  fun () ->
    (
# 23 "src/parser.mly"
           ( True )
# 75 "src/parser.ml"
     : (Ast.boolExpr))

let _menhir_action_2 =
  fun () ->
    (
# 24 "src/parser.mly"
            ( False )
# 83 "src/parser.ml"
     : (Ast.boolExpr))

let _menhir_action_3 =
  fun e1 e2 e3 ->
    (
# 25 "src/parser.mly"
                                                       ( If (e1, e2, e3) )
# 91 "src/parser.ml"
     : (Ast.boolExpr))

let _menhir_action_4 =
  fun e ->
    (
# 26 "src/parser.mly"
                               (e)
# 99 "src/parser.ml"
     : (Ast.boolExpr))

let _menhir_action_5 =
  fun e ->
    (
# 19 "src/parser.mly"
                   ( e )
# 107 "src/parser.ml"
     : (Ast.boolExpr))

let _menhir_print_token : token -> string =
  fun _tok ->
    match _tok with
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
  
  let rec _menhir_run_13 : type  ttv_stack. ttv_stack -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _v _tok ->
      match (_tok : MenhirBasics.token) with
      | EOF ->
          let e = _v in
          let _v = _menhir_action_5 e in
          MenhirBox_prog _v
      | _ ->
          _eRR ()
  
  let rec _menhir_run_02 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_LPAREN (_menhir_stack, _menhir_s) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | TRUE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_1 () in
          _menhir_run_10 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | LPAREN ->
          _menhir_run_02 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState02
      | IF ->
          _menhir_run_03 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState02
      | FALSE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_2 () in
          _menhir_run_10 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_10 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_LPAREN -> _ -> _ -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      match (_tok : MenhirBasics.token) with
      | RPAREN ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let MenhirCell1_LPAREN (_menhir_stack, _menhir_s) = _menhir_stack in
          let e = _v in
          let _v = _menhir_action_4 e in
          _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_goto_expr : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState00 ->
          _menhir_run_13 _menhir_stack _v _tok
      | MenhirState02 ->
          _menhir_run_10 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState08 ->
          _menhir_run_09 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState06 ->
          _menhir_run_07 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState03 ->
          _menhir_run_05 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_09 : type  ttv_stack. (((ttv_stack, _menhir_box_prog) _menhir_cell1_IF, _menhir_box_prog) _menhir_cell1_expr, _menhir_box_prog) _menhir_cell1_expr -> _ -> _ -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_expr (_menhir_stack, _, e2) = _menhir_stack in
      let MenhirCell1_expr (_menhir_stack, _, e1) = _menhir_stack in
      let MenhirCell1_IF (_menhir_stack, _menhir_s) = _menhir_stack in
      let e3 = _v in
      let _v = _menhir_action_3 e1 e2 e3 in
      _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_07 : type  ttv_stack. (((ttv_stack, _menhir_box_prog) _menhir_cell1_IF, _menhir_box_prog) _menhir_cell1_expr as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | ELSE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | TRUE ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let _v = _menhir_action_1 () in
              _menhir_run_09 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
          | LPAREN ->
              _menhir_run_02 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState08
          | IF ->
              _menhir_run_03 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState08
          | FALSE ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let _v = _menhir_action_2 () in
              _menhir_run_09 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_03 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_IF (_menhir_stack, _menhir_s) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | TRUE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_1 () in
          _menhir_run_05 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState03 _tok
      | LPAREN ->
          _menhir_run_02 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState03
      | IF ->
          _menhir_run_03 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState03
      | FALSE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_2 () in
          _menhir_run_05 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState03 _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_05 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_IF as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | THEN ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | TRUE ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let _v = _menhir_action_1 () in
              _menhir_run_07 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState06 _tok
          | LPAREN ->
              _menhir_run_02 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState06
          | IF ->
              _menhir_run_03 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState06
          | FALSE ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let _v = _menhir_action_2 () in
              _menhir_run_07 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState06 _tok
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  let rec _menhir_run_00 : type  ttv_stack. ttv_stack -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | TRUE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_1 () in
          _menhir_run_13 _menhir_stack _v _tok
      | LPAREN ->
          _menhir_run_02 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState00
      | IF ->
          _menhir_run_03 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState00
      | FALSE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_2 () in
          _menhir_run_13 _menhir_stack _v _tok
      | _ ->
          _eRR ()
  
end

let prog =
  fun _menhir_lexer _menhir_lexbuf ->
    let _menhir_stack = () in
    let MenhirBox_prog v = _menhir_run_00 _menhir_stack _menhir_lexbuf _menhir_lexer in
    v
