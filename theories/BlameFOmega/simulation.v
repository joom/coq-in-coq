(** * BlameFOmega.simulation: Simulation relation and Jack-of-All-Trades.

    Defines the simulation relation [sim] (and its type-level companion
    [typ_sim]), their reflexive-transitive closure [sim_star], observational
    approximation, convergence, divergence, and proves the syntactic
    Jack-of-All-Trades simulation lemma.

    OPEN: [sim s t -> approximates s t].  This bridge is NOT merely a matter of
    proving context compatibility for the present relation.  The current [sim] is
    deliberately SYNTACTIC and too broad to be a contextual-approximation
    principle: it contains one-sided rules such as [sim_blame] ([blame q]
    simulates anything) and the [sim_left_*]/type-application rules, which are
    valid as extraction bookkeeping but are not sound approximation principles
    for an untyped relation.  Closing the gap therefore requires a TYPED
    replacement (or typed restriction) of [sim], together with context
    compatibility / CIU adequacy for THAT typed relation, via a CIU-style
    argument or a step-indexed logical relation.  Two infrastructure pieces are
    already in place: typed progress ([progress], [progress.v]) and
    determinism ([step_deterministic], [semantics.v], which subsumes
    "determinism-up-to-blame").  The extraction in [proofs.v] establishes the
    syntactic simulation ([extract_reduces_once], [extract_reduces]) and
    blame-safety ([extracted_safe]); the semantic bridge to observational
    approximation remains a conjecture. *)

From Stdlib Require Import Arith.
From Stdlib Require Import Compare_dec.
From Stdlib Require Import Relations.
From BlameFOmega Require Import syntax.
From BlameFOmega Require Import infrastructure.
From BlameFOmega Require Import semantics.

(** ** Convergence and divergence *)

(** A term converges if it reduces to a value.  Currently unused; retained as
    the intended semantic target for [sim] (see OPEN note above). *)
Definition converges (s: term): Prop := exists v, value v /\ [s ~>* v].

(** A term diverges if every reduct has a further reduct. *)
Definition diverges (s: term): Prop := forall t, [s ~>* t] -> exists t', [t ~> t'].

(** ** Observational approximation *)

(** Observational approximation (provisional): [s] approximates [t] if every
    context that makes [s] converge/diverge does the same for [t].  The intended
    theorem is [sim s t -> approximates s t]; see OPEN note above.  This
    definition is retained as a target for the open bridge; it is not used by
    any current theorem. *)
Definition approximates (s t: term): Prop :=
  forall (E: term -> term),
  (forall a b, [a ~> b] -> [E a ~> E b]) ->
  (diverges (E s) -> diverges (E t)) /\
  (converges (E s) -> converges (E t)).

(** ** Simulation relation *)

(** Syntactic simulation relation used by extraction.

    This relation is intentionally broader than a contextual approximation
    relation.  It supports the extraction proofs and the syntactic
    Jack-of-All-Trades lemma, but [sim s t -> approximates s t] is not proved
    and is false for the current untyped relation (see header). *)
Inductive sim: term -> term -> Prop :=
  | sim_pos_cast: forall s t A A' B p,
    sim s t -> typ_sim A A' ->
    sim (cast s A B p) (cast t A' B p)
  | sim_neg_cast: forall s t A A' B p,
    sim s t -> typ_sim A A' ->
    sim (cast s B A (negate p)) (cast t B A' (negate p))
  | sim_blame: forall t q,
    sim (blame q) t
  | sim_left_tabs: forall K s t,
    sim s t -> sim (tabs K s) t
  | sim_left_sc: forall s t A B P,
    sim s t -> sim (cast s A B P) t
  | sim_right_sc: forall s t A B P,
    sim s t -> sim s (cast t A B P)
  | sim_beta: forall A b x,
    sim (app (abs A b) x) (subst x 0 b)
  (* This is NOT the operational type-beta reduct.  Operational type-beta
     reduces to [nu K A b].  The [sim_tbeta] constructor targets
     [term_tsubst A 0 b] because [sim] is the extraction simulation relation:
     it connects source substitution with target instantiation.  [sim_left_nu]
     strips the sealing binder on the left, bridging the sealed operational
     term back to the simulated substitution result. *)
  | sim_tbeta: forall K b A,
    sim (tapp (tabs K b) A) (term_tsubst A 0 b)
  | sim_right_gnd: forall v w G,
    sim v w -> sim v (gnd w G)
  | sim_left_tapp: forall K v w,
    sim v w -> sim (tapp (tabs K v) dyn) w
  | sim_var: forall n, sim (var n) (var n)
  | sim_abs: forall s t A A',
    sim s t ->
    sim (abs A s) (abs A' t)
  | sim_app: forall s1 t1 s2 t2,
    sim s1 t1 -> sim s2 t2 ->
    sim (app s1 s2) (app t1 t2)
  | sim_type_abs: forall K K' s t,
    sim s t -> sim (tabs K s) (tabs K' t)
  | sim_type_app: forall s t A A',
    sim s t ->
    sim (tapp s A) (tapp t A')
  | sim_is: forall s t G,
    sim s t -> sim (is_gnd s G) (is_gnd t G)
  | sim_cast_congr: forall s t A B p,
    sim s t -> sim (cast s A B p) (cast t A B p)
  | sim_gnd_congr: forall s t G,
    sim s t -> sim (gnd s G) (gnd t G)
  | sim_left_nu: forall K A s t,
    sim s t -> sim (nu K A s) t
  | sim_nu_congr: forall K K' A A' s t,
    typ_sim A A' -> sim s t -> sim (nu K A s) (nu K' A' t)

(** Type simulation: relates types that may differ by replacing some type with [?]. *)
with typ_sim: typ -> typ -> Prop :=
  | tsim_refl: forall A, typ_sim A A
  | tsim_dyn: forall A, typ_sim A dyn
  | tsim_arrow: forall A B A' B',
    typ_sim A A' -> typ_sim B B' ->
    typ_sim (arrow A B) (arrow A' B')
  | tsim_all: forall K A A',
    typ_sim A A' -> typ_sim (all K A) (all K A')
  | tsim_tyabs: forall K A A',
    typ_sim A A' -> typ_sim (tyabs K A) (tyabs K A')
  | tsim_tyapp: forall A B A' B',
    typ_sim A A' -> typ_sim B B' -> typ_sim (tyapp A B) (tyapp A' B')
  | tsim_tvar: forall n, typ_sim (tvar n) (tvar n).

Hint Constructors sim typ_sim: blame.

(** Every type is related to itself by [typ_sim]. *)
Lemma typ_sim_refl: forall A, typ_sim A A.
Proof. induction A; eauto with blame. Qed.

Hint Resolve typ_sim_refl: blame.

(** Every term is related to itself by [sim]. *)
Lemma sim_refl: forall e, sim e e.
Proof.
  induction e; try solve [eauto with blame];
    try solve [apply sim_nu_congr; [apply typ_sim_refl | assumption]].
Qed.

Hint Resolve sim_refl: blame.

(** ** Reflexive-transitive closure *)

(** Reflexive-transitive closure of the simulation [sim]. *)
Definition sim_star: term -> term -> Prop := clos_refl_trans term sim.

(** [sim_star] is reflexive. *)
Lemma sim_star_refl: forall s, sim_star s s.
Proof. intro s. unfold sim_star. apply rt_refl. Qed.

(** A single [sim] step is a [sim_star] step. *)
Lemma sim_star_step: forall s t, sim s t -> sim_star s t.
Proof. intros s t H. unfold sim_star. apply rt_step. exact H. Qed.

(** [sim_star] is transitive. *)
Lemma sim_star_trans: forall s t u, sim_star s t -> sim_star t u -> sim_star s u.
Proof. intros s t u H1 H2. unfold sim_star in *. eapply rt_trans; eauto. Qed.

Hint Resolve sim_star_refl sim_star_step: blame.

(** ** Jack-of-All-Trades *)

(** Substituting any type [C] is related by [typ_sim] to substituting [?]. *)
Lemma typ_sim_tsubst_dyn: forall A C k,
  typ_sim (tsubst C k A) (tsubst dyn k A).
Proof.
  induction A; intros; simpl; eauto with blame.
  destruct (lt_eq_lt_dec k n) as [[?|?]|?]; eauto with blame.
Qed.

(** Jack-of-All-Trades: instantiating at [?] simulates instantiation at any type [C].
    The two [sim] obligations decompose into [sim_type_app] (the term part)
    and [typ_sim_tsubst_dyn] (the type part). *)
Theorem jack_of_all_trades:
  forall v A B C p,
  sim (cast (tapp v C) (tsubst C 0 A) B p)
      (cast (tapp v dyn) (tsubst dyn 0 A) B p).
Proof.
  intros.
  constructor.
  - apply sim_type_app; auto with blame.
  - apply typ_sim_tsubst_dyn.
Qed.
