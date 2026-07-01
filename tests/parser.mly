%{
let ps = Pstring.unsafe_of_string

%}

%token <string> IDENT
%token SET PROP KIND
%token LBRACK RBRACK LPAREN RPAREN
%token COLON COMMA DOT ARROW ASSIGN
%token LET IN UNDERSCORE
%token QUIT AXIOM INFER CHECK DELETE LIST HELP
%token EOF

%nonassoc BELOW_ARROW
%right ARROW

%start file toplevel
%type <Core.ast list> file
%type <Core.ast option> toplevel

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
  | INFER expr                  { Core.Ast_infer $2 }
  | AXIOM IDENT COLON expr      { Core.Ast_axiom (ps $2, $4) }
  | CHECK expr COLON expr       { Core.Ast_check ($2, $4) }
  | DELETE                      { Core.Ast_delete }
  | LIST                        { Core.Ast_list }
  | HELP                        { Core.Ast_help }
  | QUIT                        { Core.Ast_quit }
  ;

var:
  | IDENT                       { ps $1 }
  | UNDERSCORE                  { ps "_" }
  ;

comma_vars:
  | /* empty */                 { [] }
  | COMMA var comma_vars        { $2 :: $3 }
  ;

/* An expression outside parentheses.
   No application — only lambda, let, atom, and non-dependent product (->). */
expr:
  | LBRACK var comma_vars COLON expr RBRACK expr
    { List.fold_right (fun x t -> Core.Expr_abs (x, $5, t)) ($2 :: $3) $7 }
  | LET var COLON expr ASSIGN expr IN expr
    { Core.Expr_app (Core.Expr_abs ($2, $4, $8), $6) }
  | atom_expr ARROW expr
    { Core.Expr_prod (ps "_", $1, $3) }
  | atom_expr     %prec BELOW_ARROW
    { $1 }
  ;

/* An atomic expression: sort, variable, or parenthesized. */
atom_expr:
  | PROP                        { Core.Expr_sort Core.Prop }
  | SET                         { Core.Expr_sort Core.Set }
  | KIND                        { Core.Expr_sort Core.Kind }
  | IDENT                       { Core.Expr_ref (ps $1) }
  | LPAREN paren_body           { $2 }
  ;

/* After LPAREN. Disambiguate pi forms vs general expressions. */
paren_body:
  /* (_ [, x, ...] : T) body */
  | UNDERSCORE comma_vars COLON expr RPAREN expr
    { List.fold_right
        (fun x t -> Core.Expr_prod (x, $4, t))
        (ps "_" :: $2) $6 }
  /* (x, y [, ...] : T) body */
  | IDENT COMMA pi_binders COLON expr RPAREN expr
    { List.fold_right
        (fun x t -> Core.Expr_prod (x, $5, t))
        (ps $1 :: $3) $7 }
  /* (x : T) body */
  | IDENT COLON expr RPAREN expr
    { Core.Expr_prod (ps $1, $3, $5) }
  /* (e1 e2 ... en) optionally followed by -> */
  | paren_exprs RPAREN paren_trail
    { $3 $1 }
  ;

pi_binders:
  | var comma_vars              { $1 :: $2 }
  ;

/* Inside parens: one or more expressions, left-folded into application. */
paren_exprs:
  | expr                        { $1 }
  | paren_exprs expr            { Core.Expr_app ($1, $2) }
  ;

/* Optional trailing arrow after closing paren. */
paren_trail:
  | ARROW expr                  { fun e -> Core.Expr_prod (ps "_", e, $2) }
  | /* empty */  %prec BELOW_ARROW
    { fun e -> e }
  ;
