(** * BlameFOmega.nonnormalization: A typed non-normalization result.

    The full blame calculus is not strongly normalizing.  The dynamic type
    embeds the usual untyped self-application pattern: a function can inject
    itself into [dyn], project itself back to [dyn -> dyn], and call the
    projected function on the same dynamic package.

    The closed term [omega] below has type [dyn] and returns to itself after
    beta reduction followed by COLLAPSE and ID:

    [[
      omega
        ~> (cast omega_arg dyn omega_type loop_label) omega_arg
        ~> (cast omega_fun omega_type omega_type loop_label) omega_arg
        ~> omega
    ]]

    Consequently, the expected theorem

    [[
      forall g e A, wf_ctx g -> typing g e A -> strongly_normalizing e
    ]]

    is false.  Everything in this file is constructive and admit-free. *)

From Stdlib Require Import List Relations Wellfounded.
Import ListNotations.
From BlameFOmega Require Import syntax infrastructure semantics typing
  typing_metatheory.

(** Reverse one-step reduction, in the orientation expected by [Acc]. *)
Definition step_predecessor (e' e : term) : Prop := step e e'.

(** Strong normalization means accessibility under reverse one-step
    reduction, equivalently the absence of an infinite [step] sequence. *)
Definition strongly_normalizing (e : term) : Prop :=
  Acc step_predecessor e.

(** Accessibility excludes a self-loop. *)
Lemma accessible_irreflexive : forall (A : Type) (R : A -> A -> Prop) x,
  Acc R x -> ~ R x x.
Proof.
  intros A R x Hacc.
  induction Hacc as [x Hpred IH].
  intro Hxx. exact (IH x Hxx Hxx).
Qed.

(** A forward transitive reduction path becomes a reverse-step path when its
    endpoints are exchanged. *)
Lemma clos_trans_step_predecessor : forall e e',
  clos_trans term step e e' ->
  clos_trans term step_predecessor e' e.
Proof.
  intros e e' H.
  induction H.
  - apply t_step. exact H.
  - eapply t_trans; [exact IHclos_trans2 | exact IHclos_trans1].
Qed.

(** Hence any nonempty forward reduction cycle refutes strong
    normalization. *)
Lemma cycle_not_strongly_normalizing : forall e,
  clos_trans term step e e -> ~ strongly_normalizing e.
Proof.
  intros e Hcycle Hsn.
  pose proof (Acc_clos_trans term step_predecessor e Hsn) as Hacc.
  exact (accessible_irreflexive term (clos_trans term step_predecessor)
           e Hacc (clos_trans_step_predecessor e e Hcycle)).
Qed.

(** ** The closed, well-typed looping term *)

Definition omega_type : typ := arrow dyn dyn.

Definition loop_label : label := mk_label first_external_label_id true.

Definition omega_body : term :=
  app (cast (var 0) dyn omega_type loop_label) (var 0).

Definition omega_fun : term := abs dyn omega_body.

Definition omega_arg : term := gnd omega_fun omega_type.

Definition omega : term := app omega_fun omega_arg.

Definition omega_after_beta : term :=
  app (cast omega_arg dyn omega_type loop_label) omega_arg.

Definition omega_after_collapse : term :=
  app (cast omega_fun omega_type omega_type loop_label) omega_arg.

Lemma omega_type_wf : wf_typ [] omega_type KStar.
Proof.
  unfold omega_type. apply wf_arrow; apply wf_dyn.
Qed.

Lemma omega_type_ground : ground omega_type.
Proof. unfold omega_type. apply ground_arrow. Qed.

Lemma omega_fun_value : value omega_fun.
Proof. unfold omega_fun. apply value_abs. Qed.

Lemma omega_arg_value : value omega_arg.
Proof.
  unfold omega_arg. apply value_gnd. apply omega_fun_value.
Qed.

Lemma omega_body_typed :
  typing (has_type dyn :: nil) omega_body dyn.
Proof.
  unfold omega_body.
  eapply typing_app.
  - eapply typing_cast.
    + apply typing_var. reflexivity.
    + apply compat_from_dyn.
      * unfold omega_type. discriminate.
      * unfold omega_type. apply cf_arrow.
    + apply wf_dyn.
    + apply wf_arrow; apply wf_dyn.
  - apply typing_var. reflexivity.
Qed.

Lemma omega_fun_typed : typing [] omega_fun omega_type.
Proof.
  unfold omega_fun, omega_type.
  apply typing_abs.
  - apply wf_dyn.
  - exact omega_body_typed.
Qed.

Lemma omega_arg_typed : typing [] omega_arg dyn.
Proof.
  unfold omega_arg.
  apply typing_gnd.
  - apply omega_fun_typed.
  - constructor.
    + apply omega_type_ground.
    + apply omega_type_wf.
Qed.

Theorem omega_typed : typing [] omega dyn.
Proof.
  unfold omega. eapply typing_app.
  - apply omega_fun_typed.
  - apply omega_arg_typed.
Qed.

(** Substitution in the beta step replaces both occurrences of the dynamic
    argument. *)
Lemma omega_subst : subst omega_arg 0 omega_body = omega_after_beta.
Proof.
  unfold omega_body, omega_after_beta.
  simpl. reflexivity.
Qed.

Lemma omega_step_beta : step omega omega_after_beta.
Proof.
  unfold omega, omega_fun.
  rewrite <- omega_subst.
  apply step_beta. apply omega_arg_value.
Qed.

Lemma omega_step_collapse : step omega_after_beta omega_after_collapse.
Proof.
  unfold omega_after_beta, omega_after_collapse, omega_arg.
  apply step_app_left.
  apply step_collapse.
  - apply omega_fun_value.
  - apply omega_type_ground.
  - unfold omega_type. discriminate.
  - apply compat_refl.
Qed.

Lemma omega_step_id : step omega_after_collapse omega.
Proof.
  unfold omega_after_collapse, omega.
  apply step_app_left.
  apply step_id. apply omega_fun_value.
Qed.

(** The three operational steps form a nonempty forward cycle. *)
Lemma omega_cycle :
  clos_trans term step omega omega.
Proof.
  eapply t_trans.
  - apply t_step. exact omega_step_beta.
  - eapply t_trans.
    + apply t_step. exact omega_step_collapse.
    + apply t_step. exact omega_step_id.
Qed.

Theorem omega_not_strongly_normalizing :
  ~ strongly_normalizing omega.
Proof.
  apply cycle_not_strongly_normalizing. exact omega_cycle.
Qed.

(** A closed, well-typed counterexample to strong normalization. *)
Theorem well_typed_non_normalizing :
  exists e A, typing [] e A /\ ~ strongly_normalizing e.
Proof.
  exists omega, dyn. split.
  - exact omega_typed.
  - exact omega_not_strongly_normalizing.
Qed.

(** This is the direct negation of the natural global theorem statement,
    including the well-formed-context premise used by preservation. *)
Theorem typing_does_not_imply_strong_normalization :
  ~ (forall g e A,
       wf_ctx g -> typing g e A -> strongly_normalizing e).
Proof.
  intro Hsn.
  apply omega_not_strongly_normalizing.
  apply (Hsn [] omega dyn).
  - apply wf_ctx_nil.
  - apply omega_typed.
Qed.
