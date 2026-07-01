open Core

let s_of_ps = Pstring.to_string

let string_of_sort = function
    Kind -> "Kind"
  | Prop -> "Prop"
  | Set -> "Set"

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

let print_expr e = print_string (string_of_expr e)

let print_help () =
  print_endline "Commands (each terminated by '.'):";
  print_endline "  Infer <expr>            Infer the type of an expression";
  print_endline "  Check <expr> : <expr>   Check that a term has a given type";
  print_endline "  Axiom <name> : <expr>   Add an axiom to the context";
  print_endline "  Delete                  Remove the last axiom";
  print_endline "  List                    List current axioms";
  print_endline "  Help                    Show this help message";
  print_endline "  Quit                    Exit the REPL"

let rec print_names = function
    [] -> ()
  | x :: l ->
      print_names l;
      print_string ((s_of_ps x)^" ")

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
  | Pmsg_help ->
      print_help ()
  | Pmsg_exiting ->
      print_endline "\nGoodbye..."; exit 0

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

let print_type_error err =
  begin
    match err with
        Perr_under _ ->
          print_endline "In context:";
      | _ -> ()
  end;
  print_type_err err

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

let process_command state ast =
  match interpret_ast state ast with
  | Inl (ns, msg) ->
      print_message msg;
      ns
  | Inr err ->
      print_string "Error: ";
      print_error err;
      state

let rec skip_to_dot lexbuf =
  match Lexer.token lexbuf with
  | Parser.DOT | Parser.EOF -> ()
  | _ -> skip_to_dot lexbuf
  | exception _ -> ()

let prompt () =
  print_string "\nCoc < "; flush stdout

let run_interactive lexbuf =
  let rec loop state =
    prompt ();
    match Parser.toplevel Lexer.token lexbuf with
    | None -> ()
    | Some ast ->
        let state' = process_command state ast in
        loop state'
    | exception Parser.Error ->
        let pos = Lexing.lexeme_start_p lexbuf in
        Printf.printf "Syntax error at line %d, column %d.\n%!"
          pos.pos_lnum (pos.pos_cnum - pos.pos_bol);
        skip_to_dot lexbuf;
        loop state
    | exception Failure msg ->
        Printf.printf "Error: %s\n%!" msg;
        skip_to_dot lexbuf;
        loop state
  in
  loop empty_state

let run_batch lexbuf =
  match Parser.file Lexer.token lexbuf with
  | commands ->
      ignore (List.fold_left (fun state ast ->
        process_command state ast) empty_state commands)
  | exception Failure msg ->
      Printf.eprintf "Error: %s\n" msg; exit 1
  | exception Parser.Error ->
      let pos = Lexing.lexeme_start_p lexbuf in
      Printf.eprintf "Syntax error at line %d, column %d\n"
        pos.pos_lnum (pos.pos_cnum - pos.pos_bol);
      exit 1

let () =
  let lexbuf = Lexing.from_channel stdin in
  if Unix.isatty Unix.stdin then
    run_interactive lexbuf
  else
    run_batch lexbuf
