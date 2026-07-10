(** * BlameFOmega.safety: Safety predicates for blame tracking.

    Defines [safe_pos_neg] (positive/negative subtyping on tracked casts) and
    [safe_sub] (ordinary subtyping on tracked casts), together with proofs
    that both predicates are preserved by term-variable lifting, type-variable
    lifting, and term substitution. *)

From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
From BlameFOmega Require Import syntax.
From BlameFOmega Require Import infrastructure.
From BlameFOmega Require Import subtyping.

(** ** Safety relations *)

(** [safe_pos_neg p s]: every cast labeled [p] in [s] has positive subtyping; every cast labeled [p̄] has negative subtyping. Positive blame [p] cannot fire in such a term (Blame Theorem). *)
Inductive safe_pos_neg (p: label): term -> Prop :=
  | spn_cast_pos: forall e A B,
    pos_subtype A B ->
    safe_pos_neg p e ->
    safe_pos_neg p (cast e A B p)
  | spn_cast_neg: forall e A B,
    neg_subtype A B ->
    safe_pos_neg p e ->
    safe_pos_neg p (cast e A B (negate p))
  | spn_cast_other: forall e A B q,
    lbl_id q <> lbl_id p ->
    safe_pos_neg p e ->
    safe_pos_neg p (cast e A B q)
  | spn_gnd: forall e G,
    safe_pos_neg p e ->
    safe_pos_neg p (gnd e G)
  | spn_is_gnd: forall e G,
    safe_pos_neg p e ->
    safe_pos_neg p (is_gnd e G)
  | spn_blame: forall q,
    q <> p ->
    safe_pos_neg p (blame q)
  | spn_var: forall n, safe_pos_neg p (var n)
  | spn_abs: forall t e,
    safe_pos_neg p e ->
    safe_pos_neg p (abs t e)
  | spn_app: forall e1 e2,
    safe_pos_neg p e1 ->
    safe_pos_neg p e2 ->
    safe_pos_neg p (app e1 e2)
  | spn_tabs: forall K e,
    safe_pos_neg p e ->
    safe_pos_neg p (tabs K e)
  | spn_tapp: forall e t,
    safe_pos_neg p e ->
    safe_pos_neg p (tapp e t)
  | spn_nu: forall K A e,
    safe_pos_neg p e ->
    safe_pos_neg p (nu K A e)
.

(** [safe_sub p s]: every cast labeled [p] or [p̄] in [s] has ordinary subtyping. Prevents both [blame p] and [blame p̄] (Subtyping Theorem). *)
Inductive safe_sub (p: label): term -> Prop :=
  | ss_cast_pos: forall e A B,
    subtype A B ->
    safe_sub p e ->
    safe_sub p (cast e A B p)
  | ss_cast_neg: forall e A B,
    subtype A B ->
    safe_sub p e ->
    safe_sub p (cast e A B (negate p))
  | ss_cast_other: forall e A B q,
    lbl_id q <> lbl_id p ->
    safe_sub p e ->
    safe_sub p (cast e A B q)
  | ss_gnd: forall e G,
    safe_sub p e ->
    safe_sub p (gnd e G)
  | ss_is_gnd: forall e G,
    safe_sub p e ->
    safe_sub p (is_gnd e G)
  | ss_blame: forall q,
    lbl_id q <> lbl_id p ->
    safe_sub p (blame q)
  | ss_var: forall n, safe_sub p (var n)
  | ss_abs: forall t e,
    safe_sub p e ->
    safe_sub p (abs t e)
  | ss_app: forall e1 e2,
    safe_sub p e1 ->
    safe_sub p e2 ->
    safe_sub p (app e1 e2)
  | ss_tabs: forall K e,
    safe_sub p e ->
    safe_sub p (tabs K e)
  | ss_tapp: forall e t,
    safe_sub p e ->
    safe_sub p (tapp e t)
  | ss_nu: forall K A e,
    safe_sub p e ->
    safe_sub p (nu K A e)
.

Hint Constructors safe_pos_neg safe_sub: blame.

(** ** Safety of subterms *)

(** [safe_pos_neg] is preserved by term-variable lifting. *)
Lemma safe_pos_neg_lift: forall p e i k,
  safe_pos_neg p e -> safe_pos_neg p (lift i k e).
Proof.
  intros p e i k Hs. revert i k.
  induction Hs; intros i k; simpl; eauto with blame.
  destruct (le_gt_dec k n); eauto with blame.
Qed.

(** [safe_pos_neg] is preserved by type-variable lifting inside a term. *)
Lemma safe_pos_neg_term_tlift: forall p e i k,
  safe_pos_neg p e -> safe_pos_neg p (term_tlift i k e).
Proof.
  intros p e i k Hs. revert i k.
  induction Hs; intros i k; simpl; eauto with blame.
  - apply spn_cast_pos; [apply pos_subtype_tlift; auto | auto].
  - apply spn_cast_neg; [apply neg_subtype_tlift; auto | auto].
Qed.

(** [safe_pos_neg] is preserved by term substitution. *)
Lemma safe_pos_neg_subst: forall p e1 e2 k,
  safe_pos_neg p e1 -> safe_pos_neg p e2 ->
  safe_pos_neg p (subst e2 k e1).
Proof.
  intros p e1 e2 k Hs1. revert e2 k. induction Hs1; intros e2' k Hs2; simpl;
    eauto with blame.
  - destruct (lt_eq_lt_dec k n) as [[? | ?] | ?]; eauto with blame.
    apply safe_pos_neg_lift. assumption.
  - apply spn_tabs. apply IHHs1; auto. apply safe_pos_neg_term_tlift. assumption.
  - apply spn_nu. apply IHHs1; auto. apply safe_pos_neg_term_tlift. assumption.
Qed.



(** [safe_sub] is preserved by term-variable lifting. *)
Lemma safe_sub_lift: forall p e i k,
  safe_sub p e -> safe_sub p (lift i k e).
Proof.
  intros p e i k Hs. revert i k.
  induction Hs; intros i k; simpl; eauto with blame.
  destruct (le_gt_dec k n); eauto with blame.
Qed.

(** [safe_sub] is preserved by type-variable lifting inside a term. *)
Lemma safe_sub_term_tlift: forall p e i k,
  safe_sub p e -> safe_sub p (term_tlift i k e).
Proof.
  intros p e i k Hs. revert i k.
  induction Hs; intros i k; simpl; eauto with blame.
  - apply ss_cast_pos; [apply subtype_tlift; auto | auto].
  - apply ss_cast_neg; [apply subtype_tlift; auto | auto].
Qed.

(** [safe_sub] is preserved by term substitution. *)
Lemma safe_sub_subst: forall p e1 e2 k,
  safe_sub p e1 -> safe_sub p e2 ->
  safe_sub p (subst e2 k e1).
Proof.
  intros p e1 e2 k Hs1. revert e2 k. induction Hs1; intros e2' k Hs2; simpl;
    eauto with blame.
  - destruct (lt_eq_lt_dec k n) as [[? | ?] | ?]; eauto with blame.
    apply safe_sub_lift. assumption.
  - apply ss_tabs. apply IHHs1; auto. apply safe_sub_term_tlift. assumption.
  - apply ss_nu. apply IHHs1; auto. apply safe_sub_term_tlift. assumption.
Qed.

(** [safe_pos_neg] is preserved by adjacent type-variable swap. *)
Lemma safe_pos_neg_term_tswap: forall p e k,
  safe_pos_neg p e -> safe_pos_neg p (term_tswap k e).
Proof.
  intros p e k Hs. revert k.
  induction Hs; intros k; simpl; eauto with blame.
  - apply spn_cast_pos; [apply pos_subtype_tswap; auto | auto].
  - apply spn_cast_neg; [apply neg_subtype_tswap; auto | auto].
Qed.

(** [safe_sub] is preserved by adjacent type-variable swap. *)
Lemma safe_sub_term_tswap: forall p e k,
  safe_sub p e -> safe_sub p (term_tswap k e).
Proof.
  intros p e k Hs. revert k.
  induction Hs; intros k; simpl; eauto with blame.
  - apply ss_cast_pos; [apply subtype_tswap; auto | auto].
  - apply ss_cast_neg; [apply subtype_tswap; auto | auto].
Qed.

(** ** Helper: safe terms are not blame p

    The tracked label [p] is assumed to have [lbl_id p >= 2] (see
    [external_label] in syntax.v), distinguishing it from the internal
    labels [nu_tamper_label] (id 0), [is_tamper_label] (id 1), and the
    extraction module's [internal_label] (id 0).  Internal label id 0 is
    shared by ν-tampering and extraction-time blame/casts. *)

(** A [safe_pos_neg p] term is never the blame term [blame p]. *)
Lemma safe_pos_neg_not_blame: forall p s,
  safe_pos_neg p s -> s <> blame p.
Proof.
  intros p s Hs. induction Hs; intro Heq; try discriminate.
  injection Heq; intro Heq'. subst. exact (H (eq_refl _)).
Qed.

(** A [safe_sub p] term is neither [blame p] nor [blame p̄]. *)
Lemma safe_sub_not_blame: forall p s,
  safe_sub p s -> s <> blame p /\ s <> blame (negate p).
Proof.
  intros p s Hs. induction Hs; split; intro Heq; try discriminate.
  - injection Heq; intro Heq'. subst. exact (H (eq_refl _)).
  - injection Heq; intro Heq'. subst. rewrite negate_id in H. exact (H (eq_refl _)).
Qed.
