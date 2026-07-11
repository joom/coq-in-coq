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

(** Render a run of binders [(name, rendered-annotation)] the way Rocq does:
    consecutive binders sharing an annotation collapse into one group, e.g.
    [(x, A); (y, A); (z, B)] becomes ["(x y : A)"; "(z : B)"]. *)
let group_binders binders =
  let rec go = function
    | [] -> []
    | (x, a) :: rest ->
        let rec take acc = function
          | (y, b) :: tl when b = a -> take (y :: acc) tl
          | tl -> (List.rev acc, tl)
        in
        let (names, rest') = take [x] rest in
        ("(" ^ String.concat " " names ^ " : " ^ a ^ ")") :: go rest'
  in
  String.concat " " (go binders)

let rec string_of_expr = function
    Expr_sort s -> string_of_sort s
  | Expr_ref x -> s_of_ps x
  | Expr_abs _ as t ->
      let (bs, body) = collect_abs t in
      "fun " ^ group_binders bs ^ " => " ^ string_of_expr body
  | Expr_app (u, v) ->
      string_of_app u ^ " " ^ string_of_atom v
  | Expr_prod (x, tt, u) ->
      if is_free_var x u then
        let (bs, body) = collect_prod (Expr_prod (x, tt, u)) in
        "forall " ^ group_binders bs ^ ", " ^ string_of_expr body
      else
        string_of_arrow tt ^ " -> " ^ string_of_expr u

(* Gather a maximal run of nested [fun] binders. *)
and collect_abs = function
  | Expr_abs (x, tt, t) ->
      let (bs, body) = collect_abs t in
      ((s_of_ps x, string_of_expr tt) :: bs, body)
  | t -> ([], t)

(* Gather a maximal run of dependent [forall] binders (stopping at the first
   non-dependent product, which prints as an arrow). *)
and collect_prod = function
  | Expr_prod (x, tt, u) when is_free_var x u ->
      let (bs, body) = collect_prod u in
      ((s_of_ps x, string_of_expr tt) :: bs, body)
  | t -> ([], t)

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
  | Ftyp_all _ as t ->
    let (bs, body) = collect_ftyp_all t in
    "forall " ^ group_binders bs ^ ", " ^ string_of_ftyp_e body
  | Ftyp_tyabs _ as t ->
    let (bs, body) = collect_ftyp_tyabs t in
    "fun " ^ group_binders bs ^ " => " ^ string_of_ftyp_e body
  | Ftyp_tyapp (t1, t2) ->
    string_of_ftyp_e_app t1 ^ " " ^ string_of_ftyp_e_atom t2
  | Ftyp_dyn -> "Dyn"

and collect_ftyp_all = function
  | Ftyp_all (x, k, t) ->
    let (bs, body) = collect_ftyp_all t in
    ((s_of_ps x, string_of_fkind k) :: bs, body)
  | t -> ([], t)

and collect_ftyp_tyabs = function
  | Ftyp_tyabs (x, k, t) ->
    let (bs, body) = collect_ftyp_tyabs t in
    ((s_of_ps x, string_of_fkind k) :: bs, body)
  | t -> ([], t)

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
  | Fterm_abs _ | Fterm_tabs _ as e ->
    let (bs, body) = collect_fterm_abs e in
    "fun " ^ group_binders bs ^ " => " ^ string_of_fterm_e body
  | Fterm_app _ | Fterm_tapp _ as e ->
    string_of_fterm_e_app e
  | Fterm_cast (e, a, b, p) ->
    "cast<" ^ string_of_ftyp_e a ^ " => " ^ string_of_ftyp_e b ^
    ">^" ^ string_of_label p ^ "(" ^ string_of_fterm_e e ^ ")"
  | Fterm_gnd (e, g) ->
    "gnd(" ^ string_of_fterm_e e ^ " : " ^ string_of_ftyp_e g ^ ")"
  | Fterm_is_gnd (e, g) ->
    "is_gnd(" ^ string_of_fterm_e e ^ ", " ^ string_of_ftyp_e g ^ ")"
  | Fterm_blame p ->
    "blame(" ^ string_of_label p ^ ")"
  | Fterm_nu (x, k, a, e) ->
    "nu (" ^ s_of_ps x ^ " : " ^ string_of_fkind k ^
    " := " ^ string_of_ftyp_e a ^ ") => " ^ string_of_fterm_e e

(* Gather a maximal run of term ([fun (x : T)]) and type ([fun (x : k)])
   abstractions, both of which print with the [fun] keyword. *)
and collect_fterm_abs = function
  | Fterm_abs (x, t, e) ->
    let (bs, body) = collect_fterm_abs e in
    ((s_of_ps x, string_of_ftyp_e t) :: bs, body)
  | Fterm_tabs (x, k, e) ->
    let (bs, body) = collect_fterm_abs e in
    ((s_of_ps x, string_of_fkind k) :: bs, body)
  | e -> ([], e)

and string_of_fterm_e_app = function
  | Fterm_app (e1, e2) ->
    string_of_fterm_e_app e1 ^ " " ^ string_of_fterm_e_atom e2
  | Fterm_tapp (e, t) ->
    string_of_fterm_e_app e ^ " [" ^ string_of_ftyp_e t ^ "]"
  | e -> string_of_fterm_e_atom e

and string_of_fterm_e_atom = function
  | Fterm_var _ | Fterm_blame _ | Fterm_gnd _ | Fterm_is_gnd _ | Fterm_cast _ as e ->
    string_of_fterm_e e
  | e -> "(" ^ string_of_fterm_e e ^ ")"

(** {1 Top-level definitions}

    [Definition x (a : A) : T := e.] is handled in the (unverified) shell by
    let-expansion: each subsequent command has its expressions wrapped in
    [let x : T := e in ...] (concretely [(fun (x : T) => ...) e]) for every
    definition the expression actually uses, transitively.  Scoping is correct
    by construction: definitions wrap outermost, so a user binder with the
    same name simply shadows the definition, exactly as a local binding
    shadows a global in Rocq.  The verified checker only ever sees the
    expanded term, so definitional transparency is ordinary beta
    conversion. *)

type definition = {
  def_name : string;
  def_type : expr;
  def_body : expr;
}

(** REPL state: the verified checker state plus the shell-level definitions
    (newest first). *)
type repl_state = {
  core : state;
  defs : definition list;
}

let initial_state = { core = empty_state; defs = [] }

(** Wrap [e] in a let-expansion of every definition it (transitively) uses.
    Folding newest-to-oldest is what makes dependencies work: once a newer
    definition is wrapped, its type and body are part of the accumulated
    term, so any older definition they mention is picked up in turn. *)
let wrap_defs defs e =
  List.fold_left
    (fun acc d ->
      if is_free_var d.def_name acc then
        Expr_app (Expr_abs (d.def_name, d.def_type, acc), d.def_body)
      else acc)
    e defs

(** If the expression is exactly a reference to a definition, use the
    definition's body instead of a self-referential let-wrap: name recovery
    threads source names down a leading binder spine only, so this keeps the
    definition's own binder names in inferred types and extractions. *)
let resolve_def_ref defs e =
  match e with
  | Expr_ref x ->
      (match
         List.find_opt (fun d -> s_of_ps d.def_name = s_of_ps x) defs
       with
       | Some d -> d.def_body
       | None -> e)
  | _ -> e

(** Expand definitions inside the expressions carried by a command. *)
let wrap_ast defs = function
  | Ast_infer e -> Ast_infer (wrap_defs defs (resolve_def_ref defs e))
  | Ast_check (e, t) -> Ast_check (wrap_defs defs e, wrap_defs defs t)
  | Ast_axiom (x, t) -> Ast_axiom (x, wrap_defs defs t)
  | (Ast_delete | Ast_list | Ast_help | Ast_quit) as a -> a

(** {1 REPL command processing} *)

let print_help () =
  print_endline "Commands (each terminated by '.'):";
  print_endline "  Infer <expr>            Infer the type of an expression";
  print_endline "  Check <expr> : <expr>   Check that a term has a given type";
  print_endline "  Check <expr>            Same as Infer";
  print_endline "  Definition x (a : A) : T := e";
  print_endline "                          Add a definition (expanded at use sites)";
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
      print_endline "\nGoodbye..."

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
    inferred types is done inside [interpret_ast] (verified).  Expressions
    are first expanded with the shell-level definitions. *)
let process_command rstate ast =
  match interpret_ast rstate.core (wrap_ast rstate.defs ast) with
  | Inl (ns, msg) ->
      print_message msg;
      let continue = match msg with Pmsg_exiting -> false | _ -> true in
      ({ rstate with core = ns }, true, continue)
  | Inr err ->
      print_string "Error: ";
      print_error err;
      (rstate, false, true)

(** Is [x] already an axiom or a definition? *)
let name_in_use rstate x =
  List.exists (fun n -> s_of_ps n = s_of_ps x) (glob_names rstate.core)
  || List.exists (fun d -> s_of_ps d.def_name = s_of_ps x) rstate.defs

(** Process [Definition x : T := e.] (T optional).  The body (and declared
    type, if any) are expanded with earlier definitions and validated by the
    verified checker: [Check e : T] when a type is declared, [Infer e]
    otherwise (the inferred type is recorded for later expansions). *)
let process_def rstate x oty body =
  if name_in_use rstate x then begin
    print_endline ("Error: Name " ^ s_of_ps x ^ " already in use.");
    (rstate, false, true)
  end else
    let accept ty =
      print_endline (s_of_ps x ^ " is defined.");
      ({ rstate with
         defs = { def_name = x; def_type = ty; def_body = body }
                :: rstate.defs },
       true, true)
    in
    let wbody = wrap_defs rstate.defs body in
    match oty with
    | Some ty ->
        (match interpret_ast rstate.core
                 (Ast_check (wbody, wrap_defs rstate.defs ty)) with
         | Inl (_, Pmsg_correct) -> accept ty
         | Inl (_, _) ->
             print_endline "Error: unexpected checker reply.";
             (rstate, false, true)
         | Inr err ->
             print_string "Error: ";
             print_error err;
             (rstate, false, true))
    | None ->
        (match interpret_ast rstate.core (Ast_infer wbody) with
         | Inl (_, Pmsg_inferred_type ty) -> accept ty
         | Inl (_, _) ->
             print_endline "Error: unexpected checker reply.";
             (rstate, false, true)
         | Inr err ->
             print_string "Error: ";
             print_error err;
             (rstate, false, true))

(** Parse a named expression, infer its type, and extract to Fω+blame. *)
let process_extract rstate expr =
  let expr = wrap_defs rstate.defs (resolve_def_ref rstate.defs expr) in
  let state = rstate.core in
  match term_of_expression expr (glob_names state) with
  | Inr undef ->
      print_string "Error: Unknown variables: [ ";
      print_names undef;
      print_endline "].";
      (rstate, false, true)
  | Inl t ->
      match infer (glob_ctx state) t state.glob_wf_ctx with
      | Inr (ExistT2 (err, explanation, _)) ->
          print_string "Error: ";
          print_type_error
            (translate_type_error_string err state explanation);
          (rstate, false, true)
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
          match fterm_expression_of_checked result tl vl hints [] with
          | Some (named, _) ->
              print_string "Extracted: ";
              print_string (string_of_fterm_e named);
              print_newline ();
              (rstate, true, true)
          | None ->
              print_endline
                "Error: extracted term is not scoped by the current namespaces.";
              (rstate, false, true)

let process_repl_command rstate = function
  | `Coc ast -> process_command rstate ast
  | `Extract expr -> process_extract rstate expr
  | `Def (x, oty, body) -> process_def rstate x oty body

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
        let (state', _, continue) = process_repl_command state cmd in
        if continue then loop state'
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
  loop initial_state

(** Batch mode: parse the entire file, then execute all commands in sequence. *)
let run_batch lexbuf =
  match Parser.file Lexer.token lexbuf with
  | commands ->
      let (_, success, _) = List.fold_left
        (fun (state, success, continue) cmd ->
          if not continue then (state, success, false)
          else
            let (state', command_success, continue') =
              process_repl_command state cmd in
            (state', success && command_success, continue'))
        (initial_state, true, true) commands in
      if not success then exit 1
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
