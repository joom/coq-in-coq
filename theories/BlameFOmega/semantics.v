(** * BlameFOmega.semantics: Operational semantics.

    Defines one-step reduction [step] and its reflexive-transitive closure
    [star] for the polymorphic blame calculus.  Reduction rules include β,
    type-β, ν-elimination, cast rules (WRAP/ID/GROUND/COLLAPSE/CONFLICT/
    GENERALIZE/INSTANTIATE), and blame propagation.  Reduction rules are in the Blame-for-All style,
    adapted to this Fω variant. *)

From Stdlib Require Import Arith.
From Stdlib Require Import Compare_dec.
From Stdlib Require Import Relations.
From BlameFOmega Require Import syntax.
From BlameFOmega Require Import infrastructure.

(** ** Free type-variable occurrence *)

(** [tvar_occurs k A] is [true] iff the type variable [k] occurs free in [A].
    Used to detect ν-sealing tamper: a [gnd] whose ground tag mentions the
    sealed variable would, on ν-elimination, expose that abstract name, so it
    blames instead (the Fω generalization of the [G = tvar 0] tamper check —
    a sealed variable can now hide inside a neutral tag like [α A]). *)
Fixpoint tvar_occurs (k: nat) (A: typ) : bool :=
  match A with
  | tvar n => Nat.eqb n k
  | arrow a b => tvar_occurs k a || tvar_occurs k b
  | all _ a => tvar_occurs (S k) a
  | tyabs _ a => tvar_occurs (S k) a
  | tyapp a b => tvar_occurs k a || tvar_occurs k b
  | dyn => false
  end.

(** ** One-step reduction *)

(** One-step reduction: β, type-β, ν-elimination, cast rules (WRAP/ID/GROUND/COLLAPSE/CONFLICT/GENERALIZE/INSTANTIATE/ALL), and blame propagation (Figures 3–4). *)
Reserved Notation "[ a ~> b ]" (at level 0, a at level 99, b at level 99).

Inductive step: term -> term -> Prop :=
  | step_beta: forall t b x,
    value x ->
    [app (abs t b) x ~> subst x 0 b]
  | step_tbeta: forall K b t,
    value b ->
    [tapp (tabs K b) t ~> nu K t b]
  | step_wrap: forall v A B A' B' p,
    value v ->
    arrow A B <> arrow A' B' ->
    [cast v (arrow A B) (arrow A' B') p ~>
      abs A' (cast (app (lift 1 0 v) (cast (var 0) A' A (negate p))) B B' p)]
  | step_id: forall v A p,
    value v ->
    [cast v A A p ~> v]
  | step_ground: forall v A G p,
    value v -> A <> dyn -> (forall K A', A <> all K A') ->
    ground_tag A G -> compat A G -> A <> G ->
    [cast v A dyn p ~> gnd (cast v A G p) G]
  | step_ground_id: forall v G p,
    value v -> ground G -> G <> dyn ->
    [cast v G dyn p ~> gnd v G]
  | step_collapse: forall v G A p,
    value v -> ground G -> A <> dyn -> compat G A ->
    [cast (gnd v G) dyn A p ~> cast v G A p]
  | step_conflict: forall v G A p,
    value v -> ground G -> A <> dyn -> ~ compat G A ->
    [cast (gnd v G) dyn A p ~> blame p]
  | step_is_true: forall v G,
    value v -> ~ neutral G ->
    [is_gnd (gnd v G) G ~> abs dyn (abs dyn (var 1))]
  | step_is_false: forall v G H,
    value v -> G <> H -> ~ neutral H ->
    [is_gnd (gnd v H) G ~> abs dyn (abs dyn (var 0))]
  | step_is_tamper: forall v H G,
    value v -> neutral H ->
    [is_gnd (gnd v H) G ~> blame is_tamper_label]
  | step_tabs_congr: forall K e e',
    [e ~> e'] -> [tabs K e ~> tabs K e']
  | step_tabs_blame: forall K p,
    [tabs K (blame p) ~> blame p]
  | step_nu_var: forall K A n,
    [nu K A (var n) ~> var n]
  | step_nu_abs: forall K A T e,
    [nu K A (abs T e) ~> abs (tsubst A 0 T) (nu K A e)]
  | step_nu_tabs: forall K A L e,
    value e ->
    [nu K A (tabs L e) ~> tabs L (nu K (tlift 1 0 A) (term_tswap 0 e))]
  | step_nu_gnd: forall K A v G,
    value v -> ground G -> tvar_occurs 0 G = false ->
    [nu K A (gnd v G) ~> gnd (nu K A v) (tsubst A 0 G)]
  | step_nu_tamper: forall K A v G,
    value v -> ground G -> tvar_occurs 0 G = true ->
    [nu K A (gnd v G) ~> blame nu_tamper_label]
  | step_nu_congr: forall K A e e',
    [e ~> e'] -> [nu K A e ~> nu K A e']
  | step_nu_blame: forall K A p,
    [nu K A (blame p) ~> blame p]
  (* The [A <> dyn] guard gives dynamic values priority: a cast from [dyn] to a
     universal type must first reveal its ground tag via [step_collapse] /
     [step_conflict], rather than eagerly generalizing.  Without it this rule
     overlaps those two on [cast (gnd v G) dyn (all K B) p]. *)
  | step_generalize: forall v A K B p,
    value v -> A <> dyn -> (forall K' C, A <> all K' C) ->
    [cast v A (all K B) p ~> tabs K (cast (term_tlift 1 0 v) (tlift 1 0 A) B p)]
  (* [dyn : *]: instantiating with [dyn] is kind-correct only at kind [*]. *)
  | step_instantiate: forall v A B p,
    value v -> (forall K' B', B <> all K' B') ->
    [cast v (all KStar A) B p ~> cast (tapp v dyn) (tsubst dyn 0 A) B p]
  (** ALL/ALL: the structural cast between two [∀]-types of the same kind.  It
      goes under the binder — [Λα:K. ⟨A ⇒ B⟩ᵖ (v [α])] — mirroring [step_wrap]
      for arrows.  [compat] only admits [∀K.A ⇒ ∀K.B] with matching kinds and
      [compat A B] (via [compat_all]), so this is the sole shape it must handle;
      the [A <> B] guard hands the diagonal to [step_id].  Determinism holds
      because [step_generalize] needs the source not a [∀] and
      [step_instantiate] needs the target not a [∀]. *)
  | step_all_all: forall v K A B p,
    value v -> A <> B ->
    [cast v (all K A) (all K B) p ~>
      tabs K (cast (tapp (term_tlift 1 0 v) (tvar 0)) A B p)]
  | step_app_left: forall e1 e2 x,
    [e1 ~> e2] -> [app e1 x ~> app e2 x]
  | step_app_right: forall v x1 x2,
    value v -> [x1 ~> x2] -> [app v x1 ~> app v x2]
  | step_tapp_congr: forall e1 e2 t,
    [e1 ~> e2] -> [tapp e1 t ~> tapp e2 t]
  | step_cast_congr: forall e1 e2 A B p,
    [e1 ~> e2] -> [cast e1 A B p ~> cast e2 A B p]
  | step_gnd_congr: forall e1 e2 G,
    [e1 ~> e2] -> [gnd e1 G ~> gnd e2 G]
  | step_is_gnd_congr: forall e1 e2 G,
    [e1 ~> e2] -> [is_gnd e1 G ~> is_gnd e2 G]
  | step_app_blame_l: forall p x,
    [app (blame p) x ~> blame p]
  | step_app_blame_r: forall v p,
    value v -> [app v (blame p) ~> blame p]
  | step_tapp_blame: forall p t,
    [tapp (blame p) t ~> blame p]
  | step_cast_blame: forall p A B q,
    [cast (blame p) A B q ~> blame p]
  | step_gnd_blame: forall p G,
    [gnd (blame p) G ~> blame p]
  | step_is_gnd_blame: forall p G,
    [is_gnd (blame p) G ~> blame p]
where "[ a ~> b ]" := (step a b): type_scope.

Hint Constructors step: blame.

(** ** Multi-step reduction *)

(** Reflexive-transitive closure of [step]. *)
Definition star: term -> term -> Prop :=
  clos_refl_trans _ step.

Notation "[ a ~>* b ]" := (star a b)
  (at level 0, a at level 99, b at level 99): type_scope.

Hint Unfold star: blame.
Hint Constructors clos_refl_trans: blame.

(** A single step is a multi-step. *)
Lemma star_step: forall a b, [a ~> b] -> [a ~>* b].
Proof. eauto with blame. Qed.

(** Every term multi-steps to itself. *)
Lemma star_refl: forall a, [a ~>* a].
Proof. eauto with blame. Qed.

(** Multi-step is transitive. *)
Lemma star_trans: forall a b c, [a ~>* b] -> [b ~>* c] -> [a ~>* c].
Proof. eauto with blame. Qed.

Hint Resolve star_step star_refl star_trans: blame.

(** ** Basic value facts *)

(** Values are not blame terms. *)
Lemma value_not_blame: forall v p, value v -> v <> blame p.
Proof. intros v p H; induction H; discriminate. Qed.

(** Values are irreducible. *)
Lemma value_not_step: forall v, value v -> forall e, ~ [v ~> e].
Proof.
  induction 1; intros e' Hs; inversion Hs; subst;
    try (eapply IHvalue; eauto; fail);
    try (eapply value_not_blame; eauto; fail).
Qed.

(** [blame] is irreducible (it is stuck, not a value). *)
Lemma blame_not_step: forall p e, ~ [blame p ~> e].
Proof. intros p e H; inversion H. Qed.

(** Variables are irreducible (like [blame], stuck rather than a value). *)
Lemma var_not_step: forall n e, ~ [var n ~> e].
Proof. intros n e H; inversion H. Qed.

(** A ground type is its own ground tag.  This keeps [step_ground] (which fires
    only when [A <> ground_tag A]) from overlapping [step_ground_id] (which
    fires when the source is already ground). *)
Lemma ground_ground_tag_self: forall G, ground G -> ground_tag G G.
Proof.
  intros G HG. inversion HG; subst; [apply gt_arrow | apply gt_neutral; assumption].
Qed.

(** ** Determinism of one-step reduction

    The step relation is deterministic.  The [det] tactic dispatches every
    overlap:
    - reflexivity/congruence for matching rules;
    - [value_not_blame]/[blame_not_step]/[var_not_step]/[value_not_step] for
      congruence-vs-reduction and reduction-vs-stuck-term clashes;
    - [ground_tag_functional] to unify the tags chosen by two [step_ground]
      firings, and [ground_ground_tag_self] to separate [step_ground] from
      [step_ground_id];
    - [compat] vs [~compat] for [step_collapse]/[step_conflict];
    - the [is_gnd]/[nu] tamper guards ([forall n, _ <> tvar n],
      [tvar_occurs 0 _]) and the [∀]-cast guards
      ([forall K' C, _ <> all K' C]) that separate ID / GENERALIZE /
      INSTANTIATE / ALL; and
    - the induction hypotheses ([f_equal; eauto]) for congruence-vs-congruence. *)
Local Ltac det :=
  subst; try reflexivity; try congruence;
  try (exfalso; match goal with Hv: value (blame ?p) |- _ => exact (value_not_blame _ p Hv eq_refl) end);
  try (exfalso; match goal with Hs: [ blame ?p ~> _ ] |- _ => exact (blame_not_step p _ Hs) end);
  try (exfalso; match goal with Hs: [ var ?n ~> _ ] |- _ => exact (var_not_step n _ Hs) end);
  try (exfalso; match goal with Hs: [ ?x ~> _ ], Hv: value ?x |- _ => exact (value_not_step x Hv _ Hs) end);
  try (exfalso; match goal with Hs: [ ?x ~> _ ] |- _ => eapply (value_not_step x); [ solve [auto with blame] | exact Hs ] end);
  try (exfalso; match goal with Hn: neutral ?X, Hnn: ~ neutral ?X |- _ => exact (Hnn Hn) end);
  (* [step_ground] vs [step_ground_id]: source is ground yet [A <> ground_tag A] *)
  try (exfalso; match goal with
        | Ht: ground_tag ?A ?G, Hne: ?A <> ?G, Hg: ground ?A |- _ =>
            apply Hne;
            exact (ground_tag_functional _ _ _ (ground_ground_tag_self A Hg) Ht) end);
  (* two [step_ground] firings choose the same tag *)
  try (match goal with
        | Ht1: ground_tag ?A ?G1, Ht2: ground_tag ?A ?G2 |- _ =>
            rewrite (ground_tag_functional _ _ _ Ht1 Ht2) in *; f_equal; solve [eauto] end);
  (* [step_collapse] vs [step_conflict] *)
  try (exfalso; match goal with
        | Hc: compat ?G ?A, Hnc: ~ compat ?G ?A |- _ => exact (Hnc Hc) end);
  (* [∀]-guards separating ID / GENERALIZE / INSTANTIATE / ALL *)
  try (exfalso; match goal with H: forall K A', _ <> all K A' |- _ => eapply H; reflexivity end);
  try (exfalso; match goal with H: forall K' B', _ <> all K' B' |- _ => eapply H; reflexivity end);
  try (exfalso; match goal with H: forall K' C, _ <> all K' C |- _ => eapply H; reflexivity end);
  try (exfalso; match goal with H: ground (all _ _) |- _ => solve [inversion H; subst;
        match goal with Hn: neutral (all _ _) |- _ => inversion Hn end] end);
  try discriminate;
  try tauto;
  try (f_equal; solve [eauto]);
  try solve [
    match goal with
    | H: value ?v, Hs: [?v ~> _] |- _ =>
      exfalso; exact (value_not_step v H _ Hs)
    end];
  try solve [
    exfalso; match goal with
    | H: ?x <> ?x |- _ => exact (H eq_refl)
    end];
  try solve [
    exfalso; match goal with
    | H: _ <> _ |- _ => apply H; reflexivity
    end].

(** One-step reduction is deterministic. *)
Theorem step_deterministic: forall e a, [e ~> a] -> forall z, [e ~> z] -> a = z.
Proof.
  intros e a H1; induction H1; intros z Hz; inversion Hz; det.
Qed.
