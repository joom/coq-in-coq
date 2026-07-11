(** REPL for the Calculus of Constructions.

    Supports type inference, type checking, axiom management, and extraction
    to System Fω + blame.  Runs interactively (with a prompt) when stdin is a
    terminal, or in batch mode when piped a file. *)

open Core

(** {1 CoC pretty-printing} *)

let s_of_ps = Pstring.to_string
let ps = Pstring.unsafe_of_string

(** Render a sort as CoC surface syntax. *)
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

(** Pretty-print a named CoC expression, collapsing runs of binders and
    printing non-dependent products as arrows. *)
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

(* Print the function side of an application without parenthesizing. *)
and string_of_app = function
    Expr_app (u, v) -> string_of_app u ^ " " ^ string_of_atom v
  | t -> string_of_atom t

(* Parenthesize unless already atomic (a sort or a variable). *)
and string_of_atom = function
    Expr_sort _ | Expr_ref _ as t -> string_of_expr t
  | t -> "(" ^ string_of_expr t ^ ")"

(* Parenthesize the domain of a non-dependent product if it is itself a
   binder form, so [(fun x => x) -> A] doesn't misparse. *)
and string_of_arrow = function
    Expr_abs _ | Expr_prod _ as t -> "(" ^ string_of_expr t ^ ")"
  | t -> string_of_expr t

(** Print a CoC expression to stdout. *)
let print_expr e = print_string (string_of_expr e)

(** {1 System Fω + blame pretty-printing}

    Shared helpers for kinds and labels; term/type printing works on the
    verified named expressions below. *)


(** Render an Fω kind. *)
let rec string_of_fkind = function
  | KStar -> "*"
  | KArr (k1, k2) -> "(" ^ string_of_fkind k1 ^ " => " ^ string_of_fkind k2 ^ ")"

(** Render a blame label as "<id><polarity>", e.g. "3+" or "3-". *)
let string_of_label l =
  string_of_int l.lbl_id ^ (if l.lbl_polarity then "+" else "-")

(** {1 Named Fω expression pretty-printing}

    These print the verified named expressions ([ftyp_expr], [fterm_expr])
    produced by the extracted conversion functions. *)

(** Pretty-print a named Fω type. *)
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

(** Pretty-print a named Fω+blame term. *)
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

(** The empty REPL state: no axioms, no shell-level definitions. *)
let initial_state = { core = empty_state; defs = [] }

(** Replace every free reference to [name] in [e] by [repl] (capture-avoiding:
    a binder that re-binds [name] shadows it in its body).  Used to unfold
    type-level definitions transparently. *)
let rec subst_ref name repl e =
  match e with
  | Expr_ref x -> if s_of_ps x = name then repl else e
  | Expr_sort _ -> e
  | Expr_app (f, a) -> Expr_app (subst_ref name repl f, subst_ref name repl a)
  | Expr_abs (x, a, b) ->
      Expr_abs (x, subst_ref name repl a,
                if s_of_ps x = name then b else subst_ref name repl b)
  | Expr_prod (x, a, b) ->
      Expr_prod (x, subst_ref name repl a,
                 if s_of_ps x = name then b else subst_ref name repl b)

(** Expand definitions inside [e] by unfolding every reference to its body
    (full delta by SUBSTITUTION), folding newest-to-oldest so a definition's
    body is in the accumulator before any older definition it mentions is
    processed.  Substitution -- rather than a let-wrapping beta-redex -- gives
    real transparency: a value of an encoded type must be eliminated (applied),
    and a constructor like [NZ] may appear in TYPE positions (e.g. [Fin NZ]);
    a let-bound name stays abstract under its binder, but a substituted one
    reduces, so the checker can convert as needed.  Definitions are acyclic, so
    one newest-to-oldest pass suffices. *)
let expand defs e =
  List.fold_left
    (fun acc d -> subst_ref (s_of_ps d.def_name) d.def_body acc)
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
  | Ast_infer e -> Ast_infer (expand defs (resolve_def_ref defs e))
  | Ast_check (e, t) -> Ast_check (expand defs e, expand defs t)
  | Ast_axiom (x, t) -> Ast_axiom (x, expand defs t)
  | (Ast_delete | Ast_list | Ast_help | Ast_quit) as a -> a

(** {1 REPL command processing} *)

(** Print the REPL's command and syntax reference (the [Help] command). *)
let print_help () =
  print_endline "Commands (each terminated by '.'):";
  print_endline "  Infer <expr>            Infer the type of an expression";
  print_endline "  Check <expr> : <expr>   Check that a term has a given type";
  print_endline "  Check <expr>            Same as Infer";
  print_endline "  Definition x (a : A) : T := e";
  print_endline "                          Add a definition (expanded at use sites)";
  print_endline "  Axiom <name> : <expr>   Add an axiom to the context";
  print_endline "  Inductive T ... := ...  Add a (Church-encoded) inductive type";
  print_endline "  Compute <expr>          Reduce an expression to normal form";
  print_endline "  Print Axioms            Show the current axioms";
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

(** Print a space-separated list of names in reverse order (so the oldest
    name prints first, matching axiom/definition declaration order). *)
let rec print_names = function
    [] -> ()
  | x :: l ->
      print_names l;
      print_string ((s_of_ps x)^" ")

(** Render one successful REPL command outcome ([Pmsg_*]) to stdout. *)
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

(** Render a single type-error constructor; [Perr_under] recurses to print
    the surrounding binder context first. *)
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

(** Print a type error, prefixing a "In context:" header when the error
    carries binder context ([Perr_under]). *)
let print_type_error err =
  begin
    match err with
        Perr_under _ ->
          print_endline "In context:";
      | _ -> ()
  end;
  print_type_err err

(** Print any REPL-level error, delegating type errors to [print_type_error]. *)
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
    let wbody = expand rstate.defs body in
    match oty with
    | Some ty ->
        (match interpret_ast rstate.core
                 (Ast_check (wbody, expand rstate.defs ty)) with
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
  let expr = expand rstate.defs (resolve_def_ref rstate.defs expr) in
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

(** Parse a named expression, infer its type (for well-typedness, hence
    termination of normalization), and print its beta-delta normal form.
    Shell definitions are inlined first, so [Compute] reduces through them;
    the verified [compute_normal_form] does the beta-normalization. *)
let process_compute rstate expr =
  let expr = expand rstate.defs (resolve_def_ref rstate.defs expr) in
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
          print_type_error (translate_type_error_string err state explanation);
          (rstate, false, true)
      | Inl (ExistT (_ty, _deriv)) ->
          let ExistT2 (u, _, _) = compute_normal_form t in
          let hints = collect_binder_names expr in
          let (named, _) =
            expression_of_term_with_hints u (glob_names state) hints in
          print_string "Computed: ";
          print_expr named;
          print_newline ();
          (rstate, true, true)

(** {1 Inductive desugaring: the (indexed) Boehm-Berarducci encoding}

    [Inductive T params : arity := C1 : T1 | ...] is desugared to ordinary
    definitions realising the impredicative Boehm-Berarducci encoding: the type
    former, one constructor per clause, and a recursor [T_rec].  Because these
    are definitions (not axioms), the data computes under [Compute].

    Indexed families are supported: [arity] may be [I1 -> ... -> Ik -> s], and
    the motive is index-parameterized ([X : arity]).  Each constructor may end
    in [T params t1..tk] for arbitrary index values [ti], and a recursive
    argument [T params u1..ul] is folded to [X u1..ul].  The recursor's motive
    thus depends on the INDICES; it is not the value-dependent induction
    principle (which impredicative encodings cannot provide).  Only first-order
    strictly-positive constructors are handled. *)

(** Wrap [body] in nested [fun] abstractions, one per binder. *)
let fold_abs_e binders body =
  List.fold_right (fun (x, t) acc -> Expr_abs (x, t, acc)) binders body

(** Wrap [ty] in nested [forall] products, one per binder. *)
let fold_prod_e binders ty =
  List.fold_right (fun (x, t) acc -> Expr_prod (x, t, acc)) binders ty

(** Build the non-dependent product (arrow type) [a -> b]. *)
let arrow_e a b = Expr_prod (ps "_", a, b)

(** Does the free (unbound) name [nm] occur anywhere in [e]? *)
let rec occurs_ref nm = function
  | Expr_ref x -> s_of_ps x = nm
  | Expr_sort _ -> false
  | Expr_app (f, x) -> occurs_ref nm f || occurs_ref nm x
  | Expr_abs (_, a, b) | Expr_prod (_, a, b) -> occurs_ref nm a || occurs_ref nm b

(* Application spine: [(head, [arg1; ...; argn])]. *)
let spine e =
  let rec go acc = function
    | Expr_app (f, a) -> go (a :: acc) f
    | h -> (h, acc)
  in
  go [] e

(* Split a (possibly dependent) product into named binders and the result. *)
let rec split_pi = function
  | Expr_prod (x, a, b) -> let (bs, res) = split_pi b in ((x, a) :: bs, res)
  | res -> ([], res)

(** Return [base], or [base] suffixed with underscores until it is not in
    [avoid]. *)
let fresh avoid base =
  let rec go s = if List.mem s avoid then go (s ^ "_") else s in
  go base

(** Generate [n] fresh names of the form [prefix0], [prefix1], ..., each
    avoiding [avoid] and all previously generated names in the sequence. *)
let fresh_seq avoid prefix n =
  let rec go avoid i =
    if i >= n then []
    else let x = fresh avoid (Printf.sprintf "%s%d" prefix i) in
         x :: go (x :: avoid) (i + 1)
  in
  go avoid 0

(* Returns the encoding as a list of (name, declared type, body) definitions.
   [arity] is the type former's arity ([Set], [Nat -> Set], ...); its domain
   types are the indices. *)
let expand_inductive tname params arity ctors =
  let tname_s = s_of_ps tname in
  let m = List.length params in
  let param_names = List.map (fun (a, _) -> s_of_ps a) params in
  let (arity_binders, final) = split_pi arity in
  let index_types = List.map snd arity_binders in
  let k = List.length index_types in
  (match final with
   | Expr_sort _ -> ()
   | _ -> failwith (Printf.sprintf
       "Inductive %s: its arity must end in a sort (Set or Prop)." tname_s));
  let xv = fresh param_names "X" in
  let x_e = Expr_ref (ps xv) in
  let x_app idxs = List.fold_left (fun f i -> Expr_app (f, i)) x_e idxs in
  let rec drop n l = if n <= 0 then l else match l with _::t -> drop (n-1) t | [] -> [] in
  (* index values of a saturated occurrence [T p1..pm i1..ik]: drop the params *)
  let occ_indices occ = drop m (snd (spine occ)) in
  let is_rec_occ e =
    match fst (spine e) with Expr_ref h -> s_of_ps h = tname_s | _ -> false in
  (* analyse a constructor: named binders (with kind) and result indices. *)
  let analyse (cname, cty) =
    let (binders, res) = split_pi cty in
    if not (is_rec_occ res) then
      failwith (Printf.sprintf
        "Inductive %s: constructor %s must return %s applied to its indices."
        tname_s (s_of_ps cname) tname_s);
    let classify (nm, a) =
      if is_rec_occ a then (nm, a, `Rec (occ_indices a))
      else if occurs_ref tname_s a then
        failwith (Printf.sprintf
          "Inductive %s: constructor %s has an unsupported occurrence of %s \
           (only first-order strictly-positive constructors are supported)."
          tname_s (s_of_ps cname) tname_s)
      else (nm, a, `NonRec)
    in
    (cname, cty, List.map classify binders, occ_indices res)
  in
  let ctors' = List.map analyse ctors in
  let hs = fresh_seq (xv :: param_names) "f" (List.length ctors) in
  (* case type: forall binders', X result_indices; a recursive binder's type
     [T .. u..] becomes [X u..]. *)
  let case_type (_, _, binders, res_idx) =
    List.fold_right
      (fun (nm, a, kind) acc ->
         let a' = match kind with `Rec idx -> x_app idx | `NonRec -> a in
         Expr_prod (nm, a', acc))
      binders (x_app res_idx) in
  let cases = List.map case_type ctors' in
  (* forall (X : arity), case1 -> ... -> casen -> tail *)
  let quantify tail =
    Expr_prod (ps xv, arity,
      List.fold_right2 (fun h c acc -> Expr_prod (ps h, c, acc)) hs cases tail) in
  let lam_cases body =
    Expr_abs (ps xv, arity,
      List.fold_right2 (fun h c acc -> Expr_abs (ps h, c, acc)) hs cases body) in
  let idx_names = fresh_seq (xv :: hs @ param_names) "i" k in
  let idx_refs = List.map (fun n -> Expr_ref (ps n)) idx_names in
  let idx_binders = List.combine (List.map ps idx_names) index_types in
  (* [T p1..pm i1..ik]. *)
  let t_at idxs =
    List.fold_left (fun f i -> Expr_app (f, i))
      (List.fold_left (fun f (a, _) -> Expr_app (f, Expr_ref a))
         (Expr_ref tname) params)
      idxs in
  (* --- the type former --- *)
  let t_def =
    (tname, Some (fold_prod_e params arity),
     fold_abs_e params
       (fold_abs_e idx_binders (quantify (x_app idx_refs)))) in
  (* --- the constructors --- *)
  let ctor_def j (cname, cty, binders, _res_idx) =
    let hj = Expr_ref (ps (List.nth hs j)) in
    (* usable names for the data binders (anonymous [_] args get fresh ones). *)
    let bnames =
      let rec go avoid = function
        | [] -> []
        | (nm, _, _) :: rest ->
            let n = if s_of_ps nm = "_" then fresh avoid "a" else s_of_ps nm in
            n :: go (n :: avoid) rest
      in go (xv :: hs @ param_names) binders in
    let applied =
      List.fold_left2
        (fun acc bn (_, _, kind) ->
           let v = match kind with
             | `NonRec -> Expr_ref (ps bn)
             | `Rec _ ->
                 List.fold_left (fun f h -> Expr_app (f, Expr_ref (ps h)))
                   (Expr_app (Expr_ref (ps bn), x_e)) hs
           in
           Expr_app (acc, v))
        hj bnames binders in
    let with_binders =
      List.fold_right2 (fun bn (_, a, _) acc -> Expr_abs (ps bn, a, acc))
        bnames binders (lam_cases applied) in
    (cname, Some (fold_prod_e params cty), fold_abs_e params with_binders)
  in
  let ctor_defs = List.mapi ctor_def ctors' in
  (* --- the index-dependent recursor T_rec --- *)
  let vn = fresh (xv :: hs @ param_names @ idx_names) "v" in
  let rec_applied =
    List.fold_left (fun f h -> Expr_app (f, Expr_ref (ps h)))
      (Expr_app (Expr_ref (ps vn), x_e)) hs in
  let rec_def =
    (ps (tname_s ^ "_rec"),
     Some (fold_prod_e params
             (quantify (fold_prod_e idx_binders
                (arrow_e (t_at idx_refs) (x_app idx_refs))))),
     fold_abs_e params
       (lam_cases (fold_abs_e idx_binders
          (Expr_abs (ps vn, t_at idx_refs, rec_applied))))) in
  t_def :: ctor_defs @ [rec_def]

(** Run each generated definition through [process_def], stopping on the
    first failure. *)
let process_inductive rstate tname params arity ctors =
  match expand_inductive tname params arity ctors with
  | defs ->
      List.fold_left
        (fun (st, ok, cont) (nm, oty, body) ->
           if not ok then (st, ok, cont)
           else process_def st nm oty body)
        (rstate, true, true) defs
  | exception Failure msg ->
      print_endline ("Error: " ^ msg);
      (rstate, false, true)

(** Dispatch a parsed top-level command to its handler. *)
let process_repl_command rstate = function
  | `Coc ast -> process_command rstate ast
  | `Extract expr -> process_extract rstate expr
  | `Def (x, oty, body) -> process_def rstate x oty body
  | `Compute expr -> process_compute rstate expr
  | `Inductive (tname, params, arity, ctors) ->
      process_inductive rstate tname params arity ctors

(** {1 Main loop} *)

(** Consume tokens until a [.] or EOF, used for error recovery. *)
let rec skip_to_dot lexbuf =
  match Lexer.token lexbuf with
  | Parser.DOT | Parser.EOF -> ()
  | _ -> skip_to_dot lexbuf
  | exception _ -> ()

(** Print the REPL prompt and flush stdout so it appears before input is read. *)
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
