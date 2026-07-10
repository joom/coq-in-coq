(** REPL for the Calculus of Constructions.

    Supports type inference, type checking, axiom management, and extraction
    to System Fω + blame.  Runs interactively (with a prompt) when stdin is a
    terminal, or in batch mode when piped a file. *)

open Core

(** {1 CoC pretty-printing} *)

let s_of_ps = Pstring.to_string

let string_of_sort = function
    Kind -> "Kind"
  | Prop -> "Prop"
  | Set -> "Set"

let rec string_of_expr = function
    Expr_sort s -> string_of_sort s
  | Expr_ref x -> s_of_ps x
  | Expr_abs (x, tt, t) ->
      "fun (" ^ s_of_ps x ^ " : " ^ string_of_expr tt ^ ") => " ^ string_of_expr t
  | Expr_app (u, v) ->
      string_of_app u ^ " " ^ string_of_atom v
  | Expr_prod (x, tt, u) ->
      if is_free_var x u then
        "forall (" ^ s_of_ps x ^ " : " ^ string_of_expr tt ^ "), " ^ string_of_expr u
      else
        string_of_arrow tt ^ " -> " ^ string_of_expr u

and string_of_app = function
    Expr_app (u, v) -> string_of_app u ^ " " ^ string_of_atom v
  | t -> string_of_atom t

and string_of_atom = function
    Expr_sort _ | Expr_ref _ as t -> string_of_expr t
  | t -> "(" ^ string_of_expr t ^ ")"

and string_of_arrow = function
    Expr_abs _ | Expr_prod _ as t -> "(" ^ string_of_expr t ^ ")"
  | t -> string_of_expr t

let print_expr e = print_string (string_of_expr e)

(** {1 System Fω + blame pretty-printing}

    Shared helpers for kinds and labels; term/type printing works on the
    verified named expressions below. *)


let rec string_of_fkind = function
  | KStar -> "*"
  | KArr (k1, k2) -> "(" ^ string_of_fkind k1 ^ " => " ^ string_of_fkind k2 ^ ")"

let string_of_label l =
  string_of_int l.lbl_id ^ (if l.lbl_polarity then "+" else "-")

(** {1 Named Fω expression pretty-printing}

    These print the verified named expressions ([ftyp_expr], [fterm_expr])
    produced by the extracted conversion functions. *)

let rec string_of_ftyp_e = function
  | Ftyp_var x -> s_of_ps x
  | Ftyp_arrow (t1, t2) ->
    string_of_ftyp_e_arrow t1 ^ " -> " ^ string_of_ftyp_e t2
  | Ftyp_all (x, k, t) ->
    "forall " ^ s_of_ps x ^ ":" ^ string_of_fkind k ^ ". " ^ string_of_ftyp_e t
  | Ftyp_tyabs (x, k, t) ->
    "\xCE\x9B" ^ s_of_ps x ^ ":" ^ string_of_fkind k ^ ". " ^ string_of_ftyp_e t
  | Ftyp_tyapp (t1, t2) ->
    string_of_ftyp_e_app t1 ^ " " ^ string_of_ftyp_e_atom t2
  | Ftyp_dyn -> "?"

and string_of_ftyp_e_arrow = function
  | Ftyp_arrow _ | Ftyp_all _ | Ftyp_tyabs _ as t -> "(" ^ string_of_ftyp_e t ^ ")"
  | t -> string_of_ftyp_e t

and string_of_ftyp_e_app = function
  | Ftyp_tyapp (t1, t2) -> string_of_ftyp_e_app t1 ^ " " ^ string_of_ftyp_e_atom t2
  | t -> string_of_ftyp_e_atom t

and string_of_ftyp_e_atom = function
  | Ftyp_var _ | Ftyp_dyn as t -> string_of_ftyp_e t
  | t -> "(" ^ string_of_ftyp_e t ^ ")"

let rec string_of_fterm_e = function
  | Fterm_var x -> s_of_ps x
  | Fterm_abs (x, t, e) ->
    "\xCE\xBB" ^ s_of_ps x ^ ":" ^ string_of_ftyp_e t ^ ". " ^ string_of_fterm_e e
  | Fterm_app (e1, e2) ->
    "(" ^ string_of_fterm_e_app e1 ^ " " ^ string_of_fterm_e_atom e2 ^ ")"
  | Fterm_tabs (x, k, e) ->
    "\xCE\x9B" ^ s_of_ps x ^ ":" ^ string_of_fkind k ^ ". " ^ string_of_fterm_e e
  | Fterm_tapp (e, t) ->
    string_of_fterm_e_app e ^ " [" ^ string_of_ftyp_e t ^ "]"
  | Fterm_cast (e, a, b, p) ->
    "<" ^ string_of_ftyp_e a ^ " => " ^ string_of_ftyp_e b ^
    ">^" ^ string_of_label p ^ " " ^ string_of_fterm_e_atom e
  | Fterm_gnd (e, g) ->
    "gnd(" ^ string_of_fterm_e e ^ " : " ^ string_of_ftyp_e g ^ ")"
  | Fterm_is_gnd (e, g) ->
    "is_gnd(" ^ string_of_fterm_e e ^ ", " ^ string_of_ftyp_e g ^ ")"
  | Fterm_blame p ->
    "blame(" ^ string_of_label p ^ ")"
  | Fterm_nu (x, k, a, e) ->
    "\xCE\xBD" ^ s_of_ps x ^ ":" ^ string_of_fkind k ^
    " := " ^ string_of_ftyp_e a ^ ". " ^ string_of_fterm_e e

and string_of_fterm_e_app = function
  | Fterm_app (e1, e2) ->
    string_of_fterm_e_app e1 ^ " " ^ string_of_fterm_e_atom e2
  | Fterm_tapp (e, t) ->
    string_of_fterm_e_app e ^ " [" ^ string_of_ftyp_e t ^ "]"
  | e -> string_of_fterm_e_atom e

and string_of_fterm_e_atom = function
  | Fterm_var _ | Fterm_blame _ as e -> string_of_fterm_e e
  | e -> "(" ^ string_of_fterm_e e ^ ")"

(** {1 REPL command processing} *)

let print_help () =
  print_endline "Commands (each terminated by '.'):";
  print_endline "  Infer <expr>            Infer the type of an expression";
  print_endline "  Check <expr> : <expr>   Check that a term has a given type";
  print_endline "  Axiom <name> : <expr>   Add an axiom to the context";
  print_endline "  Delete                  Remove the last axiom";
  print_endline "  List                    List current axioms";
  print_endline "  Extract <expr>          Extract to System F-omega + blame";
  print_endline "  Help                    Show this help message";
  print_endline "  Quit                    Exit the REPL";
  print_endline "";
  print_endline "Syntax:";
  print_endline "  fun (x : A) => body     Lambda abstraction";
  print_endline "  forall (x : A), body    Dependent product (Pi type)";
  print_endline "  A -> B                  Non-dependent product";
  print_endline "  f x y                   Application (left-associative)";
  print_endline "  let x : T := e in body  Local definition";
  print_endline "  Set, Prop, Kind         Sorts"

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

(** Dispatch a CoC command (Infer, Check, Axiom, etc.) through the
    extracted [interpret_ast] and print the result.  Name recovery for
    inferred types is done inside [interpret_ast] (verified). *)
let process_command state ast =
  match interpret_ast state ast with
  | Inl (ns, msg) ->
      print_message msg;
      ns
  | Inr err ->
      print_string "Error: ";
      print_error err;
      state

(** Parse a named expression, infer its type, and extract to Fω+blame. *)
let process_extract state expr =
  match term_of_expression expr (glob_names state) with
  | Inr undef ->
      print_string "Error: Unknown variables: [ ";
      print_names undef;
      print_endline "].";
      state
  | Inl t ->
      match infer (glob_ctx state) t state.glob_wf_ctx with
      | Inr _ ->
          print_endline "Error: term is ill-typed.";
          state
      | Inl (ExistT (ty, deriv)) ->
          let result = extract (glob_ctx state) t ty deriv in
          let hints = collect_binder_names expr in
          let tl, vl =
            let rec split ctx names =
              match ctx, names with
              | tp :: ctx', n :: names' ->
                let (tl', vl') = split ctx' names' in
                if classifier tp then (n :: tl', vl') else (tl', n :: vl')
              | _ -> ([], [])
            in
            split (glob_ctx state) (glob_names state)
          in
          let (named, _) = fterm_expression_of result tl vl hints in
          print_string "Extracted: ";
          print_string (string_of_fterm_e named);
          print_newline ();
          state

let process_repl_command state = function
  | `Coc ast -> process_command state ast
  | `Extract expr -> process_extract state expr

(** {1 Main loop} *)

(** Consume tokens until a [.] or EOF, used for error recovery. *)
let rec skip_to_dot lexbuf =
  match Lexer.token lexbuf with
  | Parser.DOT | Parser.EOF -> ()
  | _ -> skip_to_dot lexbuf
  | exception _ -> ()

let prompt () =
  print_string "\nCoc < "; flush stdout

(** Interactive mode: prompt, parse one command, execute, repeat. *)
let run_interactive lexbuf =
  let rec loop state =
    prompt ();
    match Parser.toplevel Lexer.token lexbuf with
    | None -> ()
    | Some cmd ->
        let state' = process_repl_command state cmd in
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

(** Batch mode: parse the entire file, then execute all commands in sequence. *)
let run_batch lexbuf =
  match Parser.file Lexer.token lexbuf with
  | commands ->
      ignore (List.fold_left (fun state cmd ->
        process_repl_command state cmd) empty_state commands)
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
