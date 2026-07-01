(* This program is free software; you can redistribute it and/or      *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2.1   *)
(* of the License, or (at your option) any later version.             *)
(*                                                                    *)
(* This program is distributed in the hope that it will be useful,    *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of     *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the      *)
(* GNU General Public License for more details.                       *)
(*                                                                    *)
(* You should have received a copy of the GNU Lesser General Public   *)
(* License along with this program; if not, write to the Free         *)
(* Software Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA *)
(* 02110-1301 USA                                                     *)


From CoqInCoq Require Import terms.
From CoqInCoq Require Import confluence.
From CoqInCoq Require Import typing.
From CoqInCoq Require Import decidable_conversion.
From CoqInCoq Require Import inference.
From CoqInCoq Require Import expressions.


(** Machine state: global context with names, well-formedness proof, and uniqueness *)
  Record state : Set :=
    {glob_ctx : environment;
     glob_names : partial_names;
     glob_wf_ctx : well_formed glob_ctx;
     glob_length : length glob_ctx = length glob_names;
     glob_unique : name_unique glob_names}.

  Hint Resolve glob_wf_ctx glob_unique: coc.


(** The empty initial state with no declarations *)
  Definition empty_state : state.
  Proof.
    refine (Build_state nil nil _ _ _); auto with coc core arith datatypes.
    exact wf_nil.

    red in |- *; intros.
    destruct m; simpl in H; discriminate H.
  Defined.


(** Witness that state s1 extends s0 with a new binding (x : t) *)
  Record state_extend (x : name) (t : term) (s0 s1 : state) : Prop :=
    {cons_env : glob_ctx s1 = t :: glob_ctx s0;
     cons_names : glob_names s1 = x :: glob_names s0}.


(** Internal commands operating on de Bruijn terms *)
  Inductive command : Set :=
    | cmd_infer : term -> command
    | cmd_check : term -> term -> command
    | cmd_axiom : name -> term -> command
    | cmd_delete : command
    | cmd_list : command
    | cmd_help : command
    | cmd_quit : command.

(** Messages returned after successful command execution *)
  Inductive message : Set :=
    | msg_new_axiom : name -> message
    | msg_inferred_type : term -> message
    | msg_correct : message
    | msg_delete_axiom : name -> message
    | msg_context_listing : partial_names -> message
    | msg_help : message
    | msg_exiting : message.

(** Errors produced by failed command execution *)
  Inductive error : Set :=
    | name_clash : name -> error
    | type_error_err : type_error -> error
    | cannot_delete : error.


(** User-facing AST with named variables *)
  Inductive ast : Set :=
    | ast_infer : expr -> ast
    | ast_check : expr -> expr -> ast
    | ast_axiom : name -> expr -> ast
    | ast_delete : ast
    | ast_list : ast
    | ast_help : ast
    | ast_quit : ast.

(** Extracts sub-expressions from an AST node *)
  Inductive expr_of_ast : ast -> expr -> Prop :=
    | ea_inf : forall e : expr, expr_of_ast (ast_infer e) e
    | ea_chk1 : forall e1 e2 : expr, expr_of_ast (ast_check e1 e2) e1
    | ea_chk2 : forall e1 e2 : expr, expr_of_ast (ast_check e1 e2) e2
    | ea_ax : forall (x : name) (e : expr), expr_of_ast (ast_axiom x e) e.

  Hint Resolve ea_inf ea_chk1 ea_chk2 ea_ax: coc.

(** Printable messages for user display *)
  Inductive pmessage : Set :=
    | pmsg_new_axiom : name -> pmessage
    | pmsg_inferred_type : expr -> pmessage
    | pmsg_correct : pmessage
    | pmsg_context_listing : partial_names -> pmessage
    | pmsg_delete_axiom : name -> pmessage
    | pmsg_help : pmessage
    | pmsg_exiting : pmessage.


(** Printable type errors with named variables *)
  Inductive ptype_error : Set :=
    | perr_under : name -> expr -> ptype_error -> ptype_error
    | perr_expected_type : expr -> expr -> expr -> ptype_error
    | perr_kind_ill_typed : ptype_error
    | perr_db : nat -> ptype_error
    | perr_lambda_kind : expr -> ptype_error
    | perr_not_a_type : expr -> expr -> ptype_error
    | perr_not_a_fun : expr -> expr -> ptype_error
    | perr_apply : expr -> expr -> expr -> expr -> ptype_error.

(** Printable errors for user display *)
  Inductive perror : Set :=
    | perr_unbound_vars : partial_names -> perror
    | perr_name_clash : name -> perror
    | perr_type_error : ptype_error -> perror
    | perr_cannot_delete : perror.


(** Translation of an AST command to an internal command using name resolution *)
  Inductive synthesis_trans (s : state) : ast -> command -> Prop :=
    | sy_infer :
        forall (e : expr) (t : term),
        term_expression_equivalent (glob_names s) t e ->
        synthesis_trans s (ast_infer e) (cmd_infer t)
    | sy_check :
        forall (e1 e2 : expr) (m t : term),
        term_expression_equivalent (glob_names s) m e1 ->
        term_expression_equivalent (glob_names s) t e2 ->
        synthesis_trans s (ast_check e1 e2) (cmd_check m t)
    | sy_axiom :
        forall (x : name) (e : expr) (t : term),
        term_expression_equivalent (glob_names s) t e ->
        synthesis_trans s (ast_axiom x e) (cmd_axiom x t)
    | sy_delete : synthesis_trans s ast_delete cmd_delete
    | sy_list : synthesis_trans s ast_list cmd_list
    | sy_help : synthesis_trans s ast_help cmd_help
    | sy_quit : synthesis_trans s ast_quit cmd_quit.

  Hint Resolve sy_infer sy_check sy_axiom sy_delete sy_list sy_help sy_quit: coc.


(** State transitions for internal commands *)
  Inductive transition (s1 : state) : command -> state -> message -> Prop :=
    | tr_infer :
        forall m t : term,
        has_type (glob_ctx s1) m t -> transition s1 (cmd_infer m) s1 (msg_inferred_type t)
    | tr_check :
        forall m t : term,
        has_type (glob_ctx s1) m t -> transition s1 (cmd_check m t) s1 msg_correct
    | tr_axiom :
        forall (x : name) (t : term) (s2 : state),
        glob_ctx s2 = t :: glob_ctx s1 ->
        glob_names s2 = x :: glob_names s1 ->
        transition s1 (cmd_axiom x t) s2 (msg_new_axiom x)
    | tr_delete :
        forall (x : name) (s2 : state),
        x :: glob_names s2 = glob_names s1 ->
        transition s1 cmd_delete s2 (msg_delete_axiom x)
    | tr_list : transition s1 cmd_list s1 (msg_context_listing (glob_names s1))
    | tr_help : transition s1 cmd_help s1 msg_help
    | tr_quit : transition s1 cmd_quit s1 msg_exiting.

  Hint Resolve tr_infer tr_check tr_axiom tr_delete tr_list tr_help tr_quit: coc.


(** Translation of internal messages to printable messages *)
  Inductive translate_message (s : state) : message -> pmessage -> Prop :=
    | tm_infer :
        forall (t : term) (e : expr),
        term_expression_equivalent (glob_names s) t e ->
        translate_message s (msg_inferred_type t) (pmsg_inferred_type e)
    | tm_check : translate_message s msg_correct pmsg_correct
    | tm_axiom : forall x : name, translate_message s (msg_new_axiom x) (pmsg_new_axiom x)
    | tm_delete :
        forall x : name, translate_message s (msg_delete_axiom x) (pmsg_delete_axiom x)
    | tm_listing :
        forall l : partial_names,
        translate_message s (msg_context_listing l) (pmsg_context_listing l)
    | tm_help : translate_message s msg_help pmsg_help
    | tm_exit : translate_message s msg_exiting pmsg_exiting.

  Hint Resolve tm_infer tm_check tm_axiom tm_delete tm_listing tm_help tm_exit: coc.


  (* ERRORS *)

(** Errors during synthesis from AST to internal command *)
  Inductive synthesis_error (s : state) : ast -> perror -> Prop :=
      Syf_db_failed :
        forall (a : ast) (e : expr) (undef : partial_names),
        expr_of_ast a e ->
        undef_vars e (glob_names s) undef ->
        undef <> nil -> synthesis_error s a (perr_unbound_vars undef).


(** Errors from internal command execution *)
  Inductive command_error (s : state) : command -> error -> Prop :=
    | ce_inf_error :
        forall (m : term) (err : type_error),
        infer_error m err ->
        explanation (glob_ctx s) err -> command_error s (cmd_infer m) (type_error_err err)
    | ce_chk_error :
        forall (m t : term) (err : type_error),
        check_error m t err ->
        explanation (glob_ctx s) err -> command_error s (cmd_check m t) (type_error_err err)
    | ce_decl_error :
        forall (x : name) (m : term) (err : type_error),
        declare_error m err ->
        explanation (glob_ctx s) err -> command_error s (cmd_axiom x m) (type_error_err err)
    | ce_axiom :
        forall (x : name) (t : term),
        In x (glob_names s) -> command_error s (cmd_axiom x t) (name_clash x)
    | ce_delete : glob_names s = nil -> command_error s cmd_delete cannot_delete.

  Hint Resolve ce_inf_error ce_chk_error ce_decl_error ce_axiom ce_delete:
    coc.


(** Translation of type errors to printable type errors *)
  Inductive translate_type_error :
  partial_names -> ptype_error -> type_error -> Prop :=
    | tpe_under :
        forall (l : partial_names) (x : name) (t : term) (e : expr),
        ~ In x l ->
        term_expression_equivalent l t e ->
        forall (perr : ptype_error) (err : type_error),
        translate_type_error (x :: l) perr err ->
        translate_type_error l (perr_under x e perr) (err_under t err)
    | tpe_exp_type :
        forall (l : partial_names) (t0 t1 t2 : term) (e0 e1 e2 : expr),
        term_expression_equivalent l t0 e0 ->
        term_expression_equivalent l t1 e1 ->
        term_expression_equivalent l t2 e2 ->
        translate_type_error l (perr_expected_type e0 e1 e2)
          (err_expected_type t0 t1 t2)
    | tpe_is_kind :
        forall l : partial_names,
        translate_type_error l perr_kind_ill_typed err_kind_ill_typed
    | tpe_db_error :
        forall (l : partial_names) (n : nat),
        translate_type_error l (perr_db n) (err_db n)
    | tpe_lam_kind :
        forall (l : partial_names) (t : term) (e : expr),
        term_expression_equivalent l t e ->
        translate_type_error l (perr_lambda_kind e) (err_lambda_kind t)
    | tpe_not_a_type :
        forall (l : partial_names) (t0 t1 : term) (e0 e1 : expr),
        term_expression_equivalent l t0 e0 ->
        term_expression_equivalent l t1 e1 ->
        translate_type_error l (perr_not_a_type e0 e1) (err_not_a_type t0 t1)
    | tpe_not_a_fun :
        forall (l : partial_names) (t0 t1 : term) (e0 e1 : expr),
        term_expression_equivalent l t0 e0 ->
        term_expression_equivalent l t1 e1 ->
        translate_type_error l (perr_not_a_fun e0 e1) (err_not_a_fun t0 t1)
    | tpe_apply_err :
        forall (l : partial_names) (t0 t1 t2 t3 : term) (e0 e1 e2 e3 : expr),
        term_expression_equivalent l t0 e0 ->
        term_expression_equivalent l t1 e1 ->
        term_expression_equivalent l t2 e2 ->
        term_expression_equivalent l t3 e3 ->
        translate_type_error l (perr_apply e0 e1 e2 e3) (err_apply t0 t1 t2 t3).

  Hint Resolve tpe_exp_type tpe_is_kind tpe_db_error tpe_lam_kind
    tpe_not_a_type tpe_not_a_fun tpe_apply_err: coc.


(** Translation of internal errors to printable errors *)
  Inductive translate_error (s : state) : error -> perror -> Prop :=
    | te_name_clash :
        forall x : name, translate_error s (name_clash x) (perr_name_clash x)
    | te_type_error :
        forall (e : type_error) (pe : ptype_error),
        translate_type_error (glob_names s) pe e ->
        translate_error s (type_error_err e) (perr_type_error pe)
    | te_cannot_delete : translate_error s cannot_delete perr_cannot_delete.

  Hint Resolve te_name_clash te_type_error te_cannot_delete: coc.


  (* global architecture *)

(** A successful transition and a command error cannot coexist *)
  Lemma trans_error_no_confusion :
   forall (si sf : state) (c : command) (m : message) (err : error),
   transition si c sf m -> command_error si c err -> False.
  Proof.
    simple induction 1; intros.
    inversion_clear H1.
    elim infer_error_no_type with m0 err0 (glob_ctx si) t;
     auto with coc core arith datatypes.

    inversion_clear H1.
    elim check_error_no_type with (glob_ctx si) m0 t err0;
     auto with coc core arith datatypes.

    inversion_clear H2.
    elim declare_error_not_well_formed with (glob_ctx si) t err0;
     auto with coc core arith datatypes.
    elim H0.
    apply glob_wf_ctx.

    assert (exists n : nat, nth_error (glob_names si) n = Some x) as [x0 Hx0].
    { revert H3; set (gl := glob_names si).
      induction gl as [|gh gt IHgt]; simpl; intro H3.
      exact (match H3 with end).
      destruct H3 as [<- | H3].
      exists 0; reflexivity.
      destruct (IHgt H3) as [n Hn]; exists (S n); exact Hn. }
    absurd (0 = S x0); auto with coc core arith datatypes.
    generalize (glob_unique s2).
    unfold name_unique in |- *; intros.
    apply H2 with x.
    rewrite H1; reflexivity.
    rewrite H1; simpl; exact Hx0.

    inversion_clear H1.
    rewrite H2 in H0.
    discriminate H0.

    inversion_clear H0.

    inversion_clear H0.

    inversion_clear H0.
  Qed.


(** Top-level successful transition: synthesis, execution, and message translation *)
  Inductive top_transition (si : state) (a : ast) (sf : state)
  (m : pmessage) : Prop :=
      Top_int :
        forall (c : command) (im : message),
        synthesis_trans si a c ->
        transition si c sf im
        (* the message should be understandable in initial state! *)
         -> translate_message si im m -> top_transition si a sf m.


(** Top-level error: either a synthesis error or an internal command error *)
  Inductive top_transition_error (si : state) (a : ast) (e : perror) : Prop :=
    | te_sy : synthesis_error si a e -> top_transition_error si a e
    | te_int :
        forall (c : command) (ie : error),
        synthesis_trans si a c ->
        command_error si c ie -> translate_error si ie e -> top_transition_error si a e.

  Hint Resolve te_sy: coc.


(** Synthesis and synthesis error are mutually exclusive *)
  Lemma synthesis_no_confusion :
   forall (si : state) (a : ast) (c : command) (e : perror),
   synthesis_trans si a c -> synthesis_error si a e -> False.
  Proof.
    simple induction 1; intros.
    inversion_clear H1.
    apply H4.
    apply equivalent_no_undefined with (glob_names si) t e0;
     auto with coc core arith datatypes.
    inversion_clear H2; auto with coc core arith datatypes.

    inversion_clear H2.
    apply H5.
    generalize H0 H1.
    inversion_clear H3; intros.
    apply equivalent_no_undefined with (glob_names si) m e0;
     auto with coc core arith datatypes.

    apply equivalent_no_undefined with (glob_names si) t e0;
     auto with coc core arith datatypes.

    inversion_clear H1.
    apply H4.
    apply equivalent_no_undefined with (glob_names si) t e0;
     auto with coc core arith datatypes.
    inversion_clear H2; auto with coc core arith datatypes.

    inversion_clear H0.
    inversion_clear H1.

    inversion_clear H0.
    inversion_clear H1.

    inversion_clear H0.
    inversion_clear H1.

    inversion_clear H0.
    inversion_clear H1.
  Qed.


(** Synthesis is deterministic: same AST yields same command *)
  Lemma synthesis_deterministic :
   forall (si : state) (a : ast) (c d : command),
   synthesis_trans si a c -> synthesis_trans si a d -> c = d.
  Proof.
    simple induction 1; intros.
    inversion_clear H1.
    elim equivalent_unique with (glob_names si) t e t0;
     auto with coc core arith datatypes.

    inversion_clear H2.
    elim equivalent_unique with (glob_names si) m e1 m0;
     auto with coc core arith datatypes.
    elim equivalent_unique with (glob_names si) t e2 t0;
     auto with coc core arith datatypes.

    inversion_clear H1.
    elim equivalent_unique with (glob_names si) t e t0;
     auto with coc core arith datatypes.

    inversion_clear H0; auto with coc core arith datatypes.

    inversion_clear H0; auto with coc core arith datatypes.

    inversion_clear H0; auto with coc core arith datatypes.

    inversion_clear H0; auto with coc core arith datatypes.
  Qed.


(** Top-level success and top-level error are mutually exclusive *)
  Lemma top_trans_error_no_confusion :
   forall (si sf : state) (a : ast) (m : pmessage) (perr : perror),
   top_transition si a sf m -> top_transition_error si a perr -> False.
  Proof.
    simple induction 1; intros.
    inversion_clear H3.
    apply synthesis_no_confusion with si a c perr; auto with coc core arith datatypes.

    apply trans_error_no_confusion with si sf c im ie;
     auto with coc core arith datatypes.
    elim synthesis_deterministic with si a c0 c; auto with coc core arith datatypes.
  Qed.


(** Result type for top-level interpretation: success or error *)
  Definition answer (si : state) (a : ast) : Set :=
    ({p : state * pmessage |
     match p with
     | (sf, m) => top_transition si a sf m
     end} + {err : perror | top_transition_error si a err})%type.


(** Result type for synthesis: internal command or error *)
  Definition synthesis_answer (si : state) (a : ast) : Set :=
    ({c : command | synthesis_trans si a c} +
     {err : perror | synthesis_error si a err})%type.

(** Synthesize an AST into an internal command or report an error *)
  Definition synthesis : forall (si : state) (a : ast), synthesis_answer si a.
  Proof.
    simple destruct a; intros.
    elim (term_of_expression e (glob_names si)); intros.
    left.
    inversion_clear a0.
    exists (cmd_infer x); auto with coc core arith datatypes.

    right.
    inversion_clear b.
    exists (perr_unbound_vars x); auto with coc core arith datatypes.
    apply Syf_db_failed with e; auto with coc core arith datatypes.

    elim (term_of_expression e (glob_names si)); intros.
    inversion_clear a0.
    elim (term_of_expression e0 (glob_names si)); intros.
    left.
    inversion_clear a0.
    exists (cmd_check x x0); auto with coc core arith datatypes.

    right.
    inversion_clear b.
    exists (perr_unbound_vars x0); auto with coc core arith datatypes.
    apply Syf_db_failed with e0; auto with coc core arith datatypes.

    right.
    inversion_clear b.
    exists (perr_unbound_vars x); auto with coc core arith datatypes.
    apply Syf_db_failed with e; auto with coc core arith datatypes.

    elim (term_of_expression e (glob_names si)); intros.
    left.
    inversion_clear a0.
    exists (cmd_axiom n x); auto with coc core arith datatypes.

    right.
    inversion_clear b.
    exists (perr_unbound_vars x); auto with coc core arith datatypes.
    apply Syf_db_failed with e; auto with coc core arith datatypes.

    left.
    exists cmd_delete; auto with coc core arith datatypes.

    left.
    exists cmd_list; auto with coc core arith datatypes.

    left.
    exists cmd_help; auto with coc core arith datatypes.

    left.
    exists cmd_quit; auto with coc core arith datatypes.
  Defined.


(** Result type for command execution: success with new state and message, or error *)
  Definition command_answer (si : state) (c : command) : Set :=
    ({p : state * message |
     match p with
     | (sf, m) => transition si c sf m
     end} + {e : error | command_error si c e})%type.


(** Execute the cmd_infer command: infer the type of a term *)
  Definition execute_infer : forall (s : state) (m : term), command_answer s (cmd_infer m).
  Proof.
    intros.
    elim infer with (glob_ctx s) m; intros; auto with coc core arith datatypes.
    elim a.
    intros t H.
    left.
    exists (s, msg_inferred_type t).
    apply tr_infer; auto with coc core arith datatypes.

    right.
    inversion_clear b.
    exists (type_error_err x); auto with coc core arith datatypes.
  Defined.


(** Execute the cmd_check command: check a term against a type *)
  Definition execute_check :
   forall (s : state) (m t : term), command_answer s (cmd_check m t).
  Proof.
    intros.
    elim check_type with (glob_ctx s) m t; intros;
     auto with coc core arith datatypes.
    right.
    inversion_clear a.
    exists (type_error_err x); auto with coc core arith datatypes.

    left.
    exists (s, msg_correct); auto with coc core arith datatypes.
  Defined.


(** Execute the cmd_axiom command: add a new axiom to the context *)
  Definition execute_axiom :
   forall (s : state) (x : name) (t : term), command_answer s (cmd_axiom x t).
  Proof.
    intros.
    elim (add_type (glob_ctx s) t); intros; auto with coc core arith datatypes.
    right.
    inversion_clear a.
    exists (type_error_err x0); auto with coc core arith datatypes.

    elim (list_index name_dec x (glob_names s)); intros.
    right.
    exists (name_clash x); auto with coc core arith datatypes.
    destruct a as [n Hfi].
    apply ce_axiom.
    unfold first_item in Hfi; destruct Hfi as [Hnth _].
    exact (nth_error_In _ n Hnth).

    left.
    cut (name_unique (x :: glob_names s)); intros.
    cut (length (t :: glob_ctx s) = length (x :: glob_names s)); intros.
    exists
     (Build_state (t :: glob_ctx s) (x :: glob_names s) b H0 H, msg_new_axiom x);
     auto with coc core arith datatypes.

    simpl in |- *.
    elim glob_length with s; auto with coc core arith datatypes.

    apply free_var_extension; auto with coc core arith datatypes.
  Defined.


(** Execute the cmd_delete command: remove the most recent axiom *)
  Definition execute_delete : forall s : state, command_answer s cmd_delete.
  Proof.
    intros.
    generalize (refl_equal (glob_names s)).
    pattern (glob_names s) at 1 in |- *.
    case (glob_names s); intros.
    right.
    exists cannot_delete; auto with coc core arith datatypes.

    generalize (refl_equal (glob_ctx s)).
    pattern (glob_ctx s) at 1 in |- *.
    case (glob_ctx s); intros.
    generalize (glob_length s).
    elim H.
    elim H0; simpl in |- *; intros.
    discriminate H1.

    cut (length l0 = length l); intros.
    cut (name_unique l); intros.
    cut (well_formed l0); intros.
    left.
    exists (Build_state l0 l H3 H1 H2, msg_delete_axiom n);
     auto with coc core arith datatypes.

    generalize (glob_wf_ctx s).
    elim H0; intros.
    inversion_clear H3.
    apply has_type_well_formed with t (sort_term s0); auto with coc core arith datatypes.

    generalize (glob_unique s).
    elim H.
    unfold name_unique in |- *; intros.
    cut (S m = S n0); intros.
    injection H5; auto with coc core arith datatypes.

    apply H2 with x; auto with coc core arith datatypes.

    generalize (glob_length s).
    elim H.
    elim H0; simpl in |- *; intros.
    injection H1; auto with coc core arith datatypes.
  Defined.


(** Dispatch a command to the appropriate executor *)
  Definition interpret_command : forall (si : state) (c : command), command_answer si c.
  Proof.
    simple induction c.
    exact (execute_infer si).
    exact (execute_check si).
    exact (execute_axiom si).
    exact (execute_delete si).
    left; exists (si, msg_context_listing (glob_names si)); auto with coc.
    left; exists (si, msg_help); auto with coc.
    left; exists (si, msg_exiting); auto with coc.
  Defined.


(** Translate an internal message to a printable message *)
  Definition translate_message_string :
   forall (s : state) (im : message),
   (exists c : command, (exists sf : state, transition s c sf im)) ->
   {m : pmessage | translate_message s im m}.
  Proof.
    simple induction im.
    intro x; exists (pmsg_new_axiom x); auto with coc.
    intros t H; elim (expression_of_term t (glob_names s)); auto with coc.
    intros; exists (pmsg_inferred_type x); auto with coc.
    inversion_clear H.
    inversion_clear H0.
    inversion_clear H.
    elim glob_length.
    apply type_free_db_below with m; auto.
    exists pmsg_correct; auto with coc.
    intro x; exists (pmsg_delete_axiom x); auto with coc.
    intro l; exists (pmsg_context_listing l); auto with coc.
    exists pmsg_help; auto with coc.
    exists pmsg_exiting; auto with coc.
  Defined.


(** Translate a type error to a printable type error *)
  Definition translate_type_error_string :
   forall (err : type_error) (s : state),
   explanation (glob_ctx s) err ->
   {perr : ptype_error | translate_type_error (glob_names s) perr err}.
  Proof.
    simple induction err; intros.
    elim find_free_var with (glob_names s); intros.
    elim expression_of_term with t (glob_names s); intros;
     auto with coc core arith datatypes.
    cut {si : state | state_extend x t s si}; [intros H'; elim H' | ]; intros.
    elim H with x1; intros.
    exists (perr_under x x0 x2).
    apply tpe_under; auto with coc core arith datatypes.
    elim cons_names with x t s x1; auto with coc core arith datatypes.

    inversion_clear H0.
    rewrite (cons_env x t s x1); auto with coc core arith datatypes.

    cut (well_formed (t :: glob_ctx s)); intros.
    cut (S (length (glob_ctx s)) = S (length (glob_names s))); intros.
    cut (name_unique (x :: glob_names s)); intros.
    exists (Build_state (t :: glob_ctx s) (x :: glob_names s) H1 H2 H3).
    split; auto with coc core arith datatypes.

    apply free_var_extension; auto with coc core arith datatypes.

    elim glob_length with s; auto with coc core arith datatypes.

    inversion_clear H0; auto with coc core arith datatypes.
    apply explanation_well_formed with t0; auto with coc core arith datatypes.

    inversion_clear H0.
    elim glob_length with s; auto with coc core arith datatypes.
    cut (well_formed (t :: glob_ctx s)); intros.
    inversion_clear H0.
    apply has_type_free_db_below with (sort_term s0); auto with coc core arith datatypes.

    apply explanation_well_formed with t0; auto with coc core arith datatypes.

    elim expression_of_term with t (glob_names s); intros;
     auto with coc core arith datatypes.
    elim expression_of_term with t0 (glob_names s); intros;
     auto with coc core arith datatypes.
    elim expression_of_term with t1 (glob_names s); intros;
     auto with coc core arith datatypes.
    exists (perr_expected_type x x0 x1); auto with coc core arith datatypes.

    inversion_clear H.
    elim glob_length with s.
    auto with coc core arith datatypes.

    inversion_clear H.
    elim glob_length with s.
    apply type_free_db_below with t; auto with coc core arith datatypes.

    inversion_clear H.
    elim glob_length with s.
    apply has_type_free_db_below with t0; auto with coc core arith datatypes.

    exists perr_kind_ill_typed; auto with coc core arith datatypes.

    exists (perr_db n); auto with coc core arith datatypes.

    elim expression_of_term with t (glob_names s); intros;
     auto with coc core arith datatypes.
    exists (perr_lambda_kind x); auto with coc core arith datatypes.

    inversion_clear H.
    elim glob_length with s.
    apply db_lam.
    cut (well_formed (t0 :: glob_ctx s)); intros.
    inversion_clear H.
    apply has_type_free_db_below with (sort_term s0); auto with coc core arith datatypes.

    apply has_type_well_formed with m (sort_term kind); auto with coc core arith datatypes.

    change (free_db_below (length (t0 :: glob_ctx s)) m) in |- *.
    apply has_type_free_db_below with (sort_term kind); auto with coc core arith datatypes.

    elim expression_of_term with t (glob_names s); intros;
     auto with coc core arith datatypes.
    elim expression_of_term with t0 (glob_names s); intros;
     auto with coc core arith datatypes.
    exists (perr_not_a_type x x0); auto with coc core arith datatypes.

    inversion_clear H.
    elim glob_length with s.
    apply type_free_db_below with t; auto with coc core arith datatypes.

    inversion_clear H.
    elim glob_length with s.
    apply has_type_free_db_below with t0; auto with coc core arith datatypes.

    elim expression_of_term with t (glob_names s); intros;
     auto with coc core arith datatypes.
    elim expression_of_term with t0 (glob_names s); intros;
     auto with coc core arith datatypes.
    exists (perr_not_a_fun x x0); auto with coc core arith datatypes.

    inversion_clear H.
    elim glob_length with s.
    apply type_free_db_below with t; auto with coc core arith datatypes.

    inversion_clear H.
    elim glob_length with s.
    apply has_type_free_db_below with t0; auto with coc core arith datatypes.

    elim expression_of_term with t (glob_names s); intros;
     auto with coc core arith datatypes.
    elim expression_of_term with t0 (glob_names s); intros;
     auto with coc core arith datatypes.
    elim expression_of_term with t1 (glob_names s); intros;
     auto with coc core arith datatypes.
    elim expression_of_term with t2 (glob_names s); intros;
     auto with coc core arith datatypes.
    exists (perr_apply x x0 x1 x2); auto with coc core arith datatypes.

    inversion_clear H.
    elim glob_length with s.
    apply type_free_db_below with t1; auto with coc core arith datatypes.

    inversion_clear H.
    elim glob_length with s.
    apply has_type_free_db_below with t2; auto with coc core arith datatypes.

    inversion_clear H.
    elim glob_length with s.
    apply type_free_db_below with t; auto with coc core arith datatypes.

    inversion_clear H.
    elim glob_length with s.
    apply has_type_free_db_below with (prod a b); auto with coc core arith datatypes.
  Defined.


(** Translate an internal error to a printable error *)
  Definition translate_error_string :
   forall (s : state) (err : error),
   (forall terr : type_error,
    err = type_error_err terr -> explanation (glob_ctx s) terr) ->
   {perr : perror | translate_error s err perr}.
  Proof.
    simple induction err.
    intro x; exists (perr_name_clash x); auto with coc.
    intros er H; elim (translate_type_error_string er s); auto with coc.
    intros terr H0; exists (perr_type_error terr); auto with coc.
    exists perr_cannot_delete; auto with coc.
  Defined.


(** Top-level interpreter: synthesize, execute, and translate the result *)
  Definition interpret_ast : forall (si : state) (a : ast), answer si a.
  Proof.
    intros.
    elim synthesis with si a; intros.
    elim a0; intros c H.
    elim interpret_command with si c; intros.
    elim a1; simple destruct x; intros.
    elim translate_message_string with si m; intros.
    left.
    exists (s, x0); auto with coc core arith datatypes.
    apply Top_int with c m; auto with coc core arith datatypes.

    exists c; exists s; auto with coc core arith datatypes.

    right.
    inversion_clear b.
    elim translate_error_string with si x; intros.
    exists x0.
    apply te_int with c x; auto with coc core arith datatypes.

    rewrite H1 in H0.
    inversion_clear H0; auto with coc core arith datatypes.

    right.
    inversion_clear b.
    exists x; auto with coc core arith datatypes.
  Defined.
