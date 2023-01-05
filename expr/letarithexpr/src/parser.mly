(*PARSER*)

%{
open Ast
%}

%token TRUE
%token FALSE
%token LPAREN
%token RPAREN
%token IF
%token THEN
%token ELSE
%token AND
%token OR
%token NOT
%token ZERO
%token SUCC
%token PRED
%token ISZERO
%token VAR
%token LET
%token IN
%token EQUALTO
%token <string> ID
%token EOF

%nonassoc ELSE
%left OR
%left AND
%right NOT
%nonassoc SUCC,PRED,ISZERO

%start <expr> prog

%%

prog:
    | e =expr; EOF { e }   
;

expr:
    | TRUE { True }
    | FALSE { False }
    | IF; e1 = expr; THEN; e2 = expr; ELSE; e3 = expr; { If (e1, e2, e3) }
    | LPAREN; e = expr; RPAREN {e}
    | e1 = expr; AND ; e2 = expr; { And (e1, e2) } 
    | e1 = expr; OR; e2 = expr; { Or (e1, e2) }
    | NOT; e = expr; { Not(e) }
    | ISZERO; e = expr; { IsZero(e) }
    | PRED; e = expr; { Pred(e) }
    | SUCC; e = expr; { Succ(e) } 
    | ZERO { Zero }
    | x = ID { Var x }
    | LET; x = ID ; EQUALTO ; e1 = expr; IN; e2 = expr; { Let(x,e1,e2) }
;
