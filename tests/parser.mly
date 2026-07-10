%{
(** Parser for named CoC syntax (Rocq-style) and REPL commands.
    Produces polymorphic-variant commands consumed by {!Top}.

    Syntax:
    - [fun (x : A) => body]         term abstraction
    - [forall (x : A), body]        dependent product
    - [A -> B]                      non-dependent product
    - [f x y]                       application (left-associative juxtaposition)
    - [let x : T := e in body]      local definition
    - [(e)]                         grouping *)
let ps = Pstring.unsafe_of_string
%}

%token <string> IDENT
%token SET PROP KIND
%token LPAREN RPAREN
%token COLON COMMA DOT ARROW DARROW ASSIGN
%token FUN FORALL
%token LET IN UNDERSCORE
%token QUIT AXIOM INFER CHECK DELETE LIST HELP EXTRACT
%token EOF

%start file toplevel
%type <[`Coc of Core.ast | `Extract of Core.expr] list> file
%type <[`Coc of Core.ast | `Extract of Core.expr] option> toplevel

%%

file:
  | EOF                         { [] }
  | command DOT file            { $1 :: $3 }
  ;

toplevel:
  | EOF                         { None }
  | command DOT                 { Some $1 }
  ;

command:
  | INFER expr                  { `Coc (Core.Ast_infer $2) }
  | AXIOM IDENT COLON expr      { `Coc (Core.Ast_axiom (ps $2, $4)) }
  | CHECK expr COLON expr       { `Coc (Core.Ast_check ($2, $4)) }
  | DELETE                      { `Coc Core.Ast_delete }
  | LIST                        { `Coc Core.Ast_list }
  | HELP                        { `Coc Core.Ast_help }
  | QUIT                        { `Coc Core.Ast_quit }
  | EXTRACT expr                { `Extract $2 }
  ;

/* Top-level expression: fun, forall, let, arrow, or application. */
expr:
  | FUN fun_binders DARROW expr
    { $2 $4 }
  | FORALL forall_binders COMMA expr
    { $2 $4 }
  | LET IDENT COLON expr ASSIGN expr IN expr
    { Core.Expr_app (Core.Expr_abs (ps $2, $4, $8), $6) }
  | app_expr ARROW expr
    { Core.Expr_prod (ps "_", $1, $3) }
  | app_expr
    { $1 }
  ;

/* fun binders: one or more binder groups, building nested Expr_abs.
   fun (x y : A) (z : B) => body  =  Expr_abs(x, A, Expr_abs(y, A, Expr_abs(z, B, body))) */
fun_binders:
  | LPAREN vars COLON expr RPAREN fun_binders
    { fun body -> List.fold_right (fun x t -> Core.Expr_abs (x, $4, t)) $2 ($6 body) }
  | LPAREN vars COLON expr RPAREN
    { fun body -> List.fold_right (fun x t -> Core.Expr_abs (x, $4, t)) $2 body }
  ;

/* forall binders: one or more binder groups, building nested Expr_prod.
   forall (x y : A) (z : B), body  =  Expr_prod(x, A, Expr_prod(y, A, Expr_prod(z, B, body))) */
forall_binders:
  | LPAREN vars COLON expr RPAREN forall_binders
    { fun body -> List.fold_right (fun x t -> Core.Expr_prod (x, $4, t)) $2 ($6 body) }
  | LPAREN vars COLON expr RPAREN
    { fun body -> List.fold_right (fun x t -> Core.Expr_prod (x, $4, t)) $2 body }
  ;

/* One or more variable names. */
vars:
  | var                         { [$1] }
  | var vars                    { $1 :: $2 }
  ;

var:
  | IDENT                       { ps $1 }
  | UNDERSCORE                  { ps "_" }
  ;

/* Application: left-associative juxtaposition. */
app_expr:
  | app_expr atom_expr          { Core.Expr_app ($1, $2) }
  | atom_expr                   { $1 }
  ;

/* Atomic expressions: sorts, variables, and parenthesized expressions. */
atom_expr:
  | PROP                        { Core.Expr_sort Core.Prop }
  | SET                         { Core.Expr_sort Core.Set }
  | KIND                        { Core.Expr_sort Core.Kind }
  | IDENT                       { Core.Expr_ref (ps $1) }
  | LPAREN expr RPAREN          { $2 }
  ;
