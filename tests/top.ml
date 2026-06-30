open Genlex
open Core

let ps = Pstring.unsafe_of_string
let s_of_ps = Pstring.to_string

(*> lexer *)
let string_of_token = function
    Kwd k -> k
  | Ident i -> i
  | Int i -> string_of_int i
  | Float f -> string_of_float f
  | String s -> s
  | Char c -> String.make 1 c
;;

let lexer=
  make_lexer
    ["Set"; "Prop"; "Kind";
    "["; "]"; "("; ")"; ":"; "->"; "let"; "in"; "_"; ",";
     ":="; "Quit";"Axiom";"Infer";"Check";"Delete";"List";"."]
;;

(*> parser *)
let rec parse_star p = parser
    [< x = p; l = (parse_star p) >] -> x::l
  | [< >] -> []
;;

let anon_var = parser
    [< 'Kwd "_" >] -> ps "_"
  | [< 'Ident x >] -> ps x
;;

let virg_an_var = parser
    [< 'Kwd "," ; x = anon_var (*, ^ (<ident>|_)*)  >] -> x
;;

let lident = parser
    [< x = anon_var; l = (parse_star virg_an_var) >] -> x::l
;;

let parse_atom = parser
    [< 'Kwd "Prop" >] -> Expr_sort Prop
  | [< 'Kwd "Set" >] -> Expr_sort Set
  | [< 'Kwd "Kind" >] -> Expr_sort Kind
  | [< 'Ident x >] -> Expr_ref (ps x)
;;

let rec parse_expr = parser
    [< 'Kwd "[";
       l = lident       (*[ ^ <ident>*);
       'Kwd ":"         (*[ <ident>* ^ (,|:)*);
       typ = parse_expr (*[ ... : ^ <expr>*);
       'Kwd "]"         (*[ ... : <expr> ^ ]*);
       trm = parse_expr (*[ ... ] ^ <expr>*)
    >] -> List.fold_right (fun x t->Expr_abs (x,typ,t)) l trm

  | [< 'Kwd "let";
       x = anon_var     (*let ^ <ident>*);
       'Kwd ":"         (*let <ident> ^ :*);
       typ = parse_expr (*let <ident> : ^ <expr>*);
       'Kwd ":="        (*let <ident> : <expr> ^ :=*);
       arg = parse_expr (*let ... := ^ <expr>*);
        'Kwd "in"       (*let ... := <expr> ^ in*);
       trm = parse_expr (*let ... in ^ <expr>*)
    >] -> Expr_app (Expr_abs (x,typ,trm), arg)

  | [< 'Kwd "(" ; r = parse_expr1 (*( ^ (<ident>|<expr>)*) >] -> r

  | [< at = parse_atom; r = (parse_expr2 at) >] -> r

and parse_expr1 = parser
    [< 'Kwd "_"; r = (parse_end_pi [ps "_"]) >] -> r

  | [< 'Ident x; r = (parse_expr3 (ps x)) >] -> r

  | [< t1 = parse_expr;
       l = (parse_star parse_expr);
       'Kwd ")"                     (*( <expr>* ^ )*);
       r = (parse_expr2 (List.fold_left (fun t a->Expr_app (t,a)) t1 l))
    >] -> r

and parse_expr2 at = parser
    [< 'Kwd "->";
       t = parse_expr (*( <expr> ) -> ^ <expr>*)
    >] -> Expr_prod (ps "_",at,t)

  | [< >] -> at

and parse_expr3 x = parser
    [< 'Kwd ",";
       y = anon_var (*( <ident> , ^ (<ident>|_)*);
       r = (parse_end_pi [x;y])
    >] -> r

  | [< 'Kwd ":";
       typ = parse_expr (*( <ident> : ^ <expr>*);
       'Kwd ")"         (*( <ident> : <expr> ^ )*);
       trm = parse_expr (*( ... ) ^ <expr>*)
    >] -> Expr_prod(x,typ,trm)

  | [< 'Kwd "->";
       t = parse_expr               (*( <ident> -> ^ <expr>*);
       l = (parse_star parse_expr)  (*( <ident> -> <expr> ^ <expr>*);
       'Kwd ")"                     (*( <expr>* ^ )*);
       str
    >] -> parse_expr2 (List.fold_left (fun t a->Expr_app(t,a))
                         (Expr_prod (ps "_",(Expr_ref x),t)) l) str

  | [< l = (parse_star parse_expr);
       'Kwd ")"  (*( <expr>* ^ )*);
       str
    >] -> parse_expr2 (List.fold_left (fun t a->Expr_app(t,a)) (Expr_ref x) l) str

and parse_end_pi lb = parser
    [< l = (parse_star virg_an_var);
       'Kwd ":"         (*( <ident>* ^ :*);
       typ = parse_expr (*( <ident>* : ^ <expr>*);
       'Kwd ")"         (*( <ident>* : <expr> ^ )*);
       trm = parse_expr (*( ... ) ^ <expr>*)
    >] -> List.fold_right (fun x t->Expr_prod(x,typ,t)) (lb@l) trm
;;


let prompt () = print_string "\nCoc < "; flush stdout;;

let parse_ast strm =
  prompt();
  match strm with parser
      [< 'Kwd "Infer";
         e = parse_expr  (*Infer ^ <expr>*)
      >] -> Ast_infer e

    | [< 'Kwd "Axiom";
         'Ident x        (*Axiom ^ <ident>*);
         'Kwd ":"        (*Axiom <ident> ^ :*);
         e = parse_expr  (*Axiom <ident> : ^ <expr>*)
      >] -> Ast_axiom(ps x,e)

    | [< 'Kwd "Check";
         e1 = parse_expr (*Check ^ <expr>*);
         'Kwd ":"        (*Check <expr> ^ :*);
         e2 = parse_expr (*Check <expr> : ^ <expr>*)
      >] -> Ast_check(e1,e2)

    | [< 'Kwd "Delete" >] -> Ast_delete

    | [< 'Kwd "List" >] -> Ast_list

    | [< 'Kwd "Quit" >] -> Ast_quit
;;


(*> display *)
let string_of_sort = function
    Kind -> "Kind"
  | Prop -> "Prop"
  | Set -> "Set"
;;

let rec string_of_expr = function
    Expr_sort s -> string_of_sort s
  | Expr_ref x -> s_of_ps x
  | Expr_abs (x,tt,t) -> "["^(s_of_ps x)^":"^(string_of_expr tt)^"]"^(string_of_expr t)
  | Expr_app (u,v) -> "("^(string_of_app u)^" "^(string_of_expr v)^")"
  | Expr_prod (x,tt,u) ->
      (match is_free_var x u with
          true -> "("^(s_of_ps x)^":"^(string_of_expr tt)^")"^(string_of_expr u)
        | false -> (string_of_arrow tt)^"->"^(string_of_expr u))

and string_of_app = function
    Expr_app (u,v) -> (string_of_app u)^" "^(string_of_expr v)
  | t -> string_of_expr t

and string_of_arrow = function
    Expr_abs (x0,x1,x2) -> "("^(string_of_expr (Expr_abs (x0,x1,x2)))^")"
  | Expr_prod (x0,x1,x2) -> "("^(string_of_expr (Expr_prod (x0,x1,x2)))^")"
  | t -> string_of_expr t
;;

let print_expr e = print_string (string_of_expr e);;


let rec print_names = function
    [] -> ()
  | x :: l ->
      print_names l;
      print_string ((s_of_ps x)^" ")
;;

let print_message = function
    Pmsg_new_axiom x ->
      print_endline ((s_of_ps x)^" admitted.")
  | Pmsg_inferred_type e ->
      print_string "Inferred type: ";
      print_expr e;
      print_newline()
  | Pmsg_correct ->
      print_endline "Correct."
  | Pmsg_context_listing l ->
      print_string "Axioms: ";
      print_names l;
      print_newline()
  | Pmsg_delete_axiom x ->
      print_endline ((s_of_ps x)^" deleted.")
  | Pmsg_exiting ->
      print_endline "\nGoodbye..."; exit 0
;;

let rec print_type_err = function
    Perr_under (x,e,err) ->
      print_string (s_of_ps x);
      print_string " : ";
      print_expr e;
      print_newline();
      print_type_err err
  | Perr_expected_type(m,at,et) ->
      print_string "The term ";
      print_expr m;
      print_string " has type ";
      print_expr at;
      print_string " but is used with type ";
      print_expr et;
      print_endline "."
  | Perr_kind_ill_typed ->
      print_endline "Kind is ill-typed."
  | Perr_db n ->
      print_string "De Bruijn variable #";
      print_int n;
      print_endline " is free."
  | Perr_lambda_kind t ->
      print_string "The term ";
      print_expr t;
      print_endline " is an abstraction over a kind."
  | Perr_not_a_type(m,t) ->
      print_string "The type of ";
      print_expr m;
      print_string ", which is ";
      print_expr t;
      print_endline " does not reduce to a sort."
  | Perr_not_a_fun(m,t) ->
      print_string "The type of ";
      print_expr m;
      print_string ", which is ";
      print_expr t;
      print_endline " does not reduce to a product."
  | Perr_apply(u,tu,v,tv) ->
      print_string "The term ";
      print_expr u;
      print_string " of type ";
      print_expr tu;
      print_string " cannot be applied to ";
      print_expr v;
      print_string " which has type ";
      print_expr tv;
      print_endline "."
;;

let print_type_error err =
  begin
    match err with
        Perr_under _ ->
          print_endline "In context:";
      | _ -> ()
  end;
  print_type_err err
;;


let print_error = function
    Perr_unbound_vars l ->
      print_string "Unknown variables: [ ";
      print_names l;
      print_endline "]."
  | Perr_name_clash x ->
      print_endline ("Name "^(s_of_ps x)^" already in use.")
  | Perr_type_error te ->
      print_type_error te
  | Perr_cannot_delete ->
      print_endline "Context already empty."
;;



(*> state encapsulation *)
let update_state =
  let state = ref empty_state in
    (fun ast ->
       match (interpret_ast !state ast) with
           Inl(ns, msg) ->
             print_message msg;
             state := ns
         | Inr err ->
             print_string "Error: ";
             print_error err)
;;


(*> toplevel loop *)


let rec discarder stk strm =
  let head_tok =
    try
      match strm with parser
        | [< 't >] -> Some t
        | [< >] -> None
    with
        Stream.Error s when (* lexer error *)
          (String.sub s 0 17) = "Illegal character"
                                -> Some (Char s.[18])
  in
    match head_tok with
        Some (Kwd ".") -> List.rev ((Kwd ".")::stk)
      | Some tok -> discarder (tok::stk) strm
      | None -> []
;;

let skip_til_dot err_msg strm =
  let toklst = discarder [] strm in
    if toklst <> [] then
      begin
        print_string "\nDiscarding ";
        List.iter
          (fun tok -> print_string ((string_of_token tok)^" ")) toklst
      end;
    print_string "\nSyntax error: ";
    print_endline err_msg
;;

let rec parse_strm strm =
  try
    match strm with parser
        [< ast = parse_ast; 'Kwd "." (*<command> ^ .*); strm >] ->
          [< 'ast; parse_strm strm >]
      | [< _ = Stream.empty >] -> [< >]
  with
      Stream.Failure ->
        skip_til_dot "^ <command>" strm;
        parse_strm strm
    | Stream.Error s ->
        skip_til_dot s strm;
        parse_strm strm
;;

let go () =
  let ast_strm = parse_strm (lexer (Stream.of_channel stdin)) in
    Stream.iter update_state ast_strm;
    print_endline "EOF!";
    flush stdout
;;

go();;
