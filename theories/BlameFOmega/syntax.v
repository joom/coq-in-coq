(** * BlameFOmega.syntax: Core syntax of the polymorphic blame calculus.

    Defines the abstract syntax of System Fω + blame: kinds, types, terms,
    blame labels, ground types, and values.

    Based on "Blame for All" (Ahmed, Findler, Siek, Wadler, POPL 2011). *)

From Stdlib Require Import Arith.
From Stdlib Require Import Compare_dec.
From Stdlib Require Import Bool.

(** ** Kinds *)

(** Kinds for the F_omega type language. *)
Inductive kind: Set :=
  | KStar
  | KArr (k1: kind) (k2: kind).

(** Decidable equality on kinds. *)
Lemma kind_eq_dec: forall (K L: kind), {K = L} + {K <> L}.
Proof. decide equality. Defined.

(** ** Types *)

(** F_omega types extended with the dynamic type [dyn].  [all] is the
    term-polymorphic type former; [tyabs]/[tyapp] are the higher-kinded
    type-level lambda/application forms used to preserve type families. *)
Inductive typ: Set :=
  | tvar (n: nat)
  | arrow (t1: typ) (t2: typ)
  | all (K: kind) (t: typ)
  | tyabs (K: kind) (t: typ)
  | tyapp (t1: typ) (t2: typ)
  | dyn.

(** Decidable equality on types, needed for case splits in reduction rules. *)
Lemma typ_eq_dec: forall (A B: typ), {A = B} + {A <> B}.
Proof. decide equality; try apply kind_eq_dec; try apply Nat.eq_dec. Defined.

(** ** Blame labels *)

(** A blame label: an id (which cast boundary) and polarity (positive or negative position). *)
Record label := mk_label { lbl_id: nat; lbl_polarity: bool }.

(** Flip the polarity of a label; a cast [A ⇒^p B] assigns label [p̄] to its argument. *)
Definition negate (p: label): label :=
  mk_label (lbl_id p) (negb (lbl_polarity p)).

(** Decidable equality on labels. *)
Lemma label_eq_dec: forall (p q: label), {p = q} + {p <> q}.
Proof.
  intros [n1 b1] [n2 b2].
  destruct (Nat.eq_dec n1 n2); destruct (Bool.bool_dec b1 b2);
    subst; try (left; reflexivity); right; intro H; injection H; auto.
Defined.

(** Double negation is identity: [p̄̄ = p]. *)
Lemma negate_negate: forall p, negate (negate p) = p.
Proof. intros [n b]; unfold negate; simpl; rewrite Bool.negb_involutive; reflexivity. Qed.

(** A label and its negation are always distinct. *)
Lemma negate_neq: forall p, negate p <> p.
Proof.
  intros [n b] H. unfold negate in H. simpl in H.
  injection H. intros. destruct b; discriminate.
Qed.

(** Negation preserves the label id; only the polarity changes. *)
Lemma negate_id: forall p, lbl_id (negate p) = lbl_id p.
Proof. intros [n b]; reflexivity. Qed.

(** Different ids imply different labels. *)
Lemma label_id_neq: forall p q, lbl_id p <> lbl_id q -> p <> q.
Proof. intros p q H Heq. subst. apply H. reflexivity. Qed.

(** ** Internal labels *)

(** The ν-tamper label: raised when sealed type variable is used at runtime. *)
Definition nu_tamper_label : label := mk_label 0 true.

(** The is_gnd-tamper label: raised when a sealed ground type is inspected. *)
Definition is_tamper_label : label := mk_label 1 true.

(** External labels are user-assigned labels with id >= 2, distinct from internal ones. *)
Definition external_label (p: label): Prop := lbl_id p >= 2.

(** ** Neutral types

    A neutral type is a type variable at its head, possibly applied to
    arguments: [α], [α A], [α A B], ....  In Fω these are the abstract type
    *names* — a type application whose head is unknown cannot compute, so it
    behaves like an opaque atom.  Neutrals are exactly the Fω generalization
    of "a type variable" from the System-F setting of Blame for All. *)
Inductive neutral: typ -> Prop :=
  | neutral_tvar: forall n, neutral (tvar n)
  | neutral_tyapp: forall F A, neutral F -> neutral (tyapp F A).

Hint Constructors neutral: blame.

(** Neutral types are never [dyn]/[arrow]/[all]/[tyabs] (their heads differ). *)
Lemma neutral_not_dyn: forall N, neutral N -> N <> dyn.
Proof. intros N H; inversion H; discriminate. Qed.
Lemma neutral_not_arrow: forall N, neutral N -> forall A B, N <> arrow A B.
Proof. intros N H; inversion H; discriminate. Qed.
Lemma neutral_not_all: forall N, neutral N -> forall K A, N <> all K A.
Proof. intros N H; inversion H; discriminate. Qed.
Lemma neutral_not_tyabs: forall N, neutral N -> forall K A, N <> tyabs K A.
Proof. intros N H; inversion H; discriminate. Qed.

(** Neutrality is decidable. *)
Lemma neutral_dec: forall A, {neutral A} + {~ neutral A}.
Proof.
  induction A as [n | A1 _ A2 _ | K A _ | K A _ | F IHF A2 _ | ].
  - left. apply neutral_tvar.
  - right. intro H; inversion H.
  - right. intro H; inversion H.
  - right. intro H; inversion H.
  - destruct IHF as [HF | HF].
    + left. apply neutral_tyapp. exact HF.
    + right. intro H; inversion H; subst; contradiction.
  - right. intro H; inversion H.
Qed.

(** ** Ground types

    Ground types are the canonical intermediate types at [dyn]: the function
    ground [? → ?], and — in this Fω setting — neutral types (abstract type
    names, e.g. a sealed variable [α] or an abstract family application
    [α A]).  A [gnd v G] wrapper injects a value of ground type [G] into
    [dyn]; [wf_ground] (in typing.v) additionally pins [G] to kind [*]. *)
Inductive ground: typ -> Prop :=
  | ground_arrow: ground (arrow dyn dyn)
  | ground_neutral: forall N, neutral N -> ground N.

Hint Constructors ground: blame.

(** Ground types are never [dyn]. *)
Lemma ground_not_dyn: forall G, ground G -> G <> dyn.
Proof.
  intros G HG; inversion HG; subst; [discriminate |].
  intro Heq; subst; match goal with H: neutral dyn |- _ => inversion H end.
Qed.

(** Ground types are never universal types. *)
Lemma ground_not_all: forall G, ground G -> forall K t, G <> all K t.
Proof.
  intros G HG K t; inversion HG; subst; [discriminate |].
  eapply neutral_not_all; eauto.
Qed.

(** ** Ground tags

    [ground_tag A G] is the *unique* ground type into which a value of type
    [A] is injected when cast to [dyn] (used by [step_ground]).  A function
    type injects at [? → ?]; a neutral type injects at itself.  Determinism of
    reduction relies on this being a partial function ([ground_tag_functional]). *)
Inductive ground_tag: typ -> typ -> Prop :=
  | gt_arrow: forall A B, ground_tag (arrow A B) (arrow dyn dyn)
  | gt_neutral: forall N, neutral N -> ground_tag N N.

Hint Constructors ground_tag: blame.

(** A ground tag is a ground type. *)
Lemma ground_tag_ground: forall A G, ground_tag A G -> ground G.
Proof. intros A G H; inversion H; subst; auto with blame. Qed.

(** Ground tags are unique: an [arrow] source and a [neutral] source never
    overlap, so at most one rule applies to any [A]. *)
Lemma ground_tag_functional: forall A G1 G2,
  ground_tag A G1 -> ground_tag A G2 -> G1 = G2.
Proof.
  intros A G1 G2 H1 H2; inversion H1; subst; inversion H2; subst;
    try reflexivity;
    match goal with H: neutral (arrow _ _) |- _ => inversion H end.
Qed.

(** ** Cast forms

    Cast annotations are weak-head canonical: [dyn], an [arrow], a [∀], or a
    neutral type.  A *reducible* type application ([tyapp (tyabs ..) ..]) is
    not a cast form, so [typing_cast] forces it to be normalized (connected to
    the term's actual type by [ty_equiv]) before it can annotate a cast — this
    is what removes the "unreduced [tyapp] as cast annotation" stuck case. *)
Inductive cast_form: typ -> Prop :=
  | cf_dyn: cast_form dyn
  | cf_arrow: forall A B, cast_form (arrow A B)
  | cf_all: forall K A, cast_form (all K A)
  | cf_neutral: forall N, neutral N -> cast_form N.

Hint Constructors cast_form: blame.

(** ** Terms *)

(** Blame calculus terms: System F extended with casts, blame, ground-wrappers, and [is_gnd] tests. *)
Inductive term: Set :=
  | var (n: nat)
  | abs (t: typ) (e: term)
  | app (e1: term) (e2: term)
  | tabs (K: kind) (e: term)
  | tapp (e: term) (t: typ)
  | cast (e: term) (A B: typ) (p: label)
  | gnd (e: term) (G: typ)
  | is_gnd (e: term) (G: typ)
  | blame (p: label)
  | nu (K: kind) (A: typ) (e: term).

(** ** Values *)

(** Values: lambda abstractions, type abstractions (body must be a value,
    following Blame for All's evaluation-under-tabs convention), and
    ground-wrapped values.

    [value_gnd] is intentionally syntactic and does not require [ground].
    Typed programs only construct [gnd] through [typing_gnd], which does
    require [ground]. *)
Inductive value: term -> Prop :=
  | value_abs: forall t e, value (abs t e)
  | value_tabs: forall K e, value e -> value (tabs K e)
  | value_gnd: forall v G, value v -> value (gnd v G).

Hint Constructors value: blame.
