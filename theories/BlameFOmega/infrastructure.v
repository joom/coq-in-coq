(** * BlameFOmega.infrastructure: Variable operations for types and terms.

    Defines lifting (weakening) and substitution for both the type and term
    layers, together with the basic commutation and cancellation lemmas
    needed by later files. *)

From Stdlib Require Import Arith.
From Stdlib Require Import Compare_dec.
From Stdlib Require Import Lia.
From Stdlib Require Import Relations.
From BlameFOmega Require Import syntax.

(** ** Type-level operations *)

(** Shift type variable indices >= [k] up by [i]. Used when pushing a type under a binder. *)
Fixpoint tlift (i: nat) (k: nat) (t: typ): typ :=
  match t with
  | tvar n => if le_gt_dec k n then tvar (i + n) else tvar n
  | arrow t1 t2 => arrow (tlift i k t1) (tlift i k t2)
  | all K t1 => all K (tlift i (S k) t1)
  | tyabs K t1 => tyabs K (tlift i (S k) t1)
  | tyapp t1 t2 => tyapp (tlift i k t1) (tlift i k t2)
  | dyn => dyn
  end.

(** Capture-avoiding substitution of type [s] for type variable [k] in [t]. *)
Fixpoint tsubst (s: typ) (k: nat) (t: typ): typ :=
  match t with
  | tvar n =>
    match lt_eq_lt_dec k n with
    | inleft (left _) => tvar (pred n)
    | inleft (right _) => tlift k 0 s
    | inright _ => tvar n
    end
  | arrow t1 t2 => arrow (tsubst s k t1) (tsubst s k t2)
  | all K t1 => all K (tsubst s (S k) t1)
  | tyabs K t1 => tyabs K (tsubst s (S k) t1)
  | tyapp t1 t2 => tyapp (tsubst s k t1) (tsubst s k t2)
  | dyn => dyn
  end.

(** Shifting by 0 is the identity. *)
Lemma tlift_zero: forall t k, tlift 0 k t = t.
Proof.
  induction t; intros; simpl; auto.
  - destruct (le_gt_dec k n); reflexivity.
  - rewrite IHt1, IHt2; reflexivity.
  - rewrite IHt; reflexivity.
  - rewrite IHt; reflexivity.
  - rewrite IHt1, IHt2; reflexivity.
Qed.

(** Two consecutive shifts at the same cutoff compose additively. *)
Lemma tlift_tlift: forall t i j k,
  tlift i k (tlift j k t) = tlift (i + j) k t.
Proof.
  induction t; intros; simpl.
  - destruct (le_gt_dec k n); simpl.
    + destruct (le_gt_dec k (j + n)); [f_equal; lia | lia].
    + destruct (le_gt_dec k n); [lia | reflexivity].
  - rewrite IHt1, IHt2; reflexivity.
  - rewrite IHt; reflexivity.
  - rewrite IHt; reflexivity.
  - rewrite IHt1, IHt2; reflexivity.
  - reflexivity.
Qed.

(** ** Executable compatibility

    [compat A B] is the precondition for a well-formed cast [A ⇒ B].  Unlike the
    System-F "consistency" relation of Blame for All, in this Fω setting it is an
    *executable* compatibility judgment: every constructor corresponds to a
    concrete cast-reduction strategy, so a well-typed cast always has an
    operational step (this is what makes [progress] hold without any stuck-cast
    rules).  Except for the identity cast ([compat_refl]), which steps without
    inspecting its annotation, each constructor decomposes the cast on a
    canonical cast-form head.  The correspondence is:

    - [compat_refl]       ⟶ ID          (identity cast; annotation not inspected)
    - [compat_arrow]      ⟶ WRAP        (contravariant domain, covariant codomain)
    - [compat_all]        ⟶ ALL/ALL     (structural cast under a matched binder)
    - [compat_generalize] ⟶ GENERALIZE  (cast into a [∀], under the binder)
    - [compat_instantiate]⟶ INSTANTIATE (cast a [∀α:*] out, instantiating at [?])
    - [compat_to_dyn]     ⟶ GROUND      (inject at the unique [ground_tag])
    - [compat_from_dyn]   ⟶ COLLAPSE/CONFLICT (project out of [?])

    Instantiation is restricted to [KStar] because this development has
    [dyn : KStar], not a kind-indexed family of unknowns. *)
Inductive compat: typ -> typ -> Prop :=
  | compat_refl: forall A,
    compat A A
  | compat_arrow: forall A1 A2 B1 B2,
    compat B1 A1 -> compat A2 B2 ->
    compat (arrow A1 A2) (arrow B1 B2)
  | compat_all: forall K A B,
    compat A B -> compat (all K A) (all K B)
  | compat_generalize: forall A K B,
    A <> dyn -> (forall K' C, A <> all K' C) ->
    compat (tlift 1 0 A) B ->
    compat A (all K B)
  | compat_instantiate: forall A B,
    (forall K' B', B <> all K' B') ->
    compat (tsubst dyn 0 A) B ->
    compat (all KStar A) B
  | compat_to_dyn: forall A G,
    A <> dyn -> (forall K B, A <> all K B) ->
    ground_tag A G -> compat A G ->
    compat A dyn
  | compat_from_dyn: forall B,
    B <> dyn -> cast_form B ->
    compat dyn B.

Hint Constructors compat: blame.

(** ** Type size (for deciding compatibility)

    [ty_size] is a structural measure used to justify termination of the
    compatibility decision procedure: INSTANTIATE recurses on
    [tsubst dyn 0 A], which has the same size as [A] (substituting the
    size-1 [dyn] for size-1 variables), hence strictly smaller than
    [∀α:*.A]. *)
Fixpoint ty_size (A: typ) : nat :=
  match A with
  | tvar _ => 1
  | arrow a b => S (ty_size a + ty_size b)
  | all _ a => S (ty_size a)
  | tyabs _ a => S (ty_size a)
  | tyapp a b => S (ty_size a + ty_size b)
  | dyn => 1
  end.

(** Every type has size at least 1. *)
Lemma ty_size_pos: forall A, 1 <= ty_size A.
Proof. induction A; simpl; lia. Qed.

(** Substituting [dyn] preserves size (it replaces size-1 variables with the
    size-1 [dyn]). *)
Lemma tsubst_dyn_size: forall A k, ty_size (tsubst dyn k A) = ty_size A.
Proof.
  induction A; intros k; simpl; auto.
  destruct (lt_eq_lt_dec k n) as [[?|?]|?]; reflexivity.
Qed.

(** Lifting preserves size (it only reindexes variables). *)
Lemma tlift_size: forall A i k, ty_size (tlift i k A) = ty_size A.
Proof.
  induction A; intros i k; simpl; auto.
  destruct (le_gt_dec k n); reflexivity.
Qed.

(** ** Decidability of executable compatibility

    A cast [A ⇒ B] is executable exactly when [compat A B].  The extractor uses
    this decision procedure to emit a real cast when the coercion is executable
    and reserved internal blame otherwise ("optimistic" extraction).  Recursion
    is on [ty_size A + ty_size B]: INSTANTIATE recurses on [tsubst dyn 0 A]
    (same size, but strips a [∀]) and GENERALIZE on [tlift 1 0 A] (same size)
    against a smaller target, so the sum strictly decreases. *)
Lemma compat_dec_fuel: forall n A B,
  ty_size A + ty_size B <= n -> {compat A B} + {~ compat A B}.
Proof.
  induction n as [|n IH]; intros A B Hn.
  - exfalso; pose proof (ty_size_pos A); pose proof (ty_size_pos B); lia.
  - destruct (typ_eq_dec A B) as [->|HAB]; [left; apply compat_refl|].
    (* [A <> B].  Decide by the shape of [B] then [A]. *)
    destruct B as [nB | B1 B2 | KB B0 | KB B0 | B1 B2 | ].
    + (* B = tvar nB *)
      destruct (typ_eq_dec A dyn) as [->|HAd].
      * left; apply compat_from_dyn; [discriminate | apply cf_neutral; apply neutral_tvar].
      * destruct A as [nA | A1 A2 | KA A0 | KA A0 | A1 A2 | ].
        -- right; intro Hc; inversion Hc; subst; try congruence.
        -- right; intro Hc; inversion Hc; subst; try congruence.
        -- destruct (kind_eq_dec KA KStar) as [->|HK].
           ++ destruct (IH (tsubst dyn 0 A0) (tvar nB)) as [Hc|Hnc];
                [rewrite tsubst_dyn_size; pose proof (ty_size_pos A0); simpl (ty_size (all _ _)) in Hn; lia| |].
              ** left; apply compat_instantiate; [intros K' B'; discriminate | exact Hc].
              ** right; intro Hc; inversion Hc; subst; try congruence;
                   match goal with H: forall _ _, all _ _ <> all _ _ |- _ =>
                     solve [eapply H; reflexivity] end.
           ++ right; intro Hc; inversion Hc; subst; try congruence;
                match goal with H: forall _ _, all _ _ <> all _ _ |- _ =>
                  solve [eapply H; reflexivity] end.
        -- right; intro Hc; inversion Hc; subst; try congruence.
        -- right; intro Hc; inversion Hc; subst; try congruence.
        -- exfalso; apply HAd; reflexivity.
    + (* B = arrow B1 B2 *)
      destruct (typ_eq_dec A dyn) as [->|HAd].
      * left; apply compat_from_dyn; [discriminate | apply cf_arrow].
      * destruct A as [nA | A1 A2 | KA A0 | KA A0 | A1 A2 | ].
        -- (* A = tvar: no rule (not arrow/dyn/all) *)
           right; intro Hc; inversion Hc; subst; try congruence.
        -- (* A = arrow: WRAP *)
           assert (Hc1_or: {compat B1 A1} + {~ compat B1 A1})
             by (apply IH; simpl (ty_size (arrow _ _)) in Hn; lia).
           assert (Hc2_or: {compat A2 B2} + {~ compat A2 B2})
             by (apply IH; simpl (ty_size (arrow _ _)) in Hn; lia).
           destruct Hc1_or as [Hc1|Hnc1]; destruct Hc2_or as [Hc2|Hnc2].
           ++ left; apply compat_arrow; assumption.
           ++ right; intro Hc; inversion Hc; subst; try congruence; contradiction.
           ++ right; intro Hc; inversion Hc; subst; try congruence; contradiction.
           ++ right; intro Hc; inversion Hc; subst; try congruence; contradiction.
        -- (* A = all KStar? INSTANTIATE, else no *)
           destruct (kind_eq_dec KA KStar) as [->|HK].
           ++ destruct (IH (tsubst dyn 0 A0) (arrow B1 B2)) as [Hc|Hnc];
                [rewrite tsubst_dyn_size; pose proof (ty_size_pos A0); simpl (ty_size (all _ _)) in Hn; lia| |].
              ** left; apply compat_instantiate; [intros K' B'; discriminate | exact Hc].
              ** right; intro Hc; inversion Hc; subst; try congruence;
                   match goal with H: forall _ _, all _ _ <> all _ _ |- _ =>
                     solve [eapply H; reflexivity] end.
           ++ right; intro Hc; inversion Hc; subst; try congruence;
                match goal with H: forall _ _, all _ _ <> all _ _ |- _ =>
                  solve [eapply H; reflexivity] end.
        -- (* A = tyabs: no rule *)
           right; intro Hc; inversion Hc; subst; try congruence.
        -- (* A = tyapp: no rule (arrow target, tyapp source) *)
           right; intro Hc; inversion Hc; subst; try congruence.
        -- (* A = dyn: excluded *) exfalso; apply HAd; reflexivity.
    + (* B = all KB B0 *)
      destruct A as [nA | A1 A2 | KA A0 | KA A0 | A1 A2 | ].
      * (* A = tvar: GENERALIZE *)
        destruct (IH (tlift 1 0 (tvar nA)) B0) as [Hc|Hnc];
          [rewrite tlift_size; pose proof (ty_size_pos B0); simpl (ty_size (all _ _)) in Hn; lia| |].
        -- left; apply compat_generalize; [discriminate | intros K' C; discriminate | exact Hc].
        -- right; intro Hc; inversion Hc; subst; try congruence; try contradiction.
      * (* A = arrow: GENERALIZE *)
        destruct (IH (tlift 1 0 (arrow A1 A2)) B0) as [Hc|Hnc];
          [rewrite tlift_size; pose proof (ty_size_pos B0); simpl (ty_size (all _ _)) in Hn; lia| |].
        -- left; apply compat_generalize; [discriminate | intros K' C; discriminate | exact Hc].
        -- right; intro Hc; inversion Hc; subst; try congruence; try contradiction.
      * (* A = all KA A0: compat_all (needs KA = KB) *)
        destruct (kind_eq_dec KA KB) as [->|HK].
        -- destruct (IH A0 B0) as [Hc|Hnc]; [simpl (ty_size (all _ _)) in Hn; lia| |].
           ++ left; apply compat_all; exact Hc.
           ++ right; intro Hc; inversion Hc; subst; try congruence;
                try (apply Hnc; assumption);
                match goal with H: forall _ _, _ <> all _ _ |- _ =>
                  solve [eapply H; reflexivity] end.
        -- right; intro Hc; inversion Hc; subst; try congruence;
             match goal with H: forall _ _, _ <> all _ _ |- _ =>
               solve [eapply H; reflexivity] end.
      * (* A = tyabs: GENERALIZE (tyabs not dyn/all) *)
        destruct (IH (tlift 1 0 (tyabs KA A0)) B0) as [Hc|Hnc];
          [rewrite tlift_size; pose proof (ty_size_pos B0); simpl (ty_size (all _ _)) in Hn; lia| |].
        -- left; apply compat_generalize; [discriminate | intros K' C; discriminate | exact Hc].
        -- right; intro Hc; inversion Hc; subst; try congruence; try contradiction.
      * (* A = tyapp: GENERALIZE *)
        destruct (IH (tlift 1 0 (tyapp A1 A2)) B0) as [Hc|Hnc];
          [rewrite tlift_size; pose proof (ty_size_pos B0); simpl (ty_size (all _ _)) in Hn; lia| |].
        -- left; apply compat_generalize; [discriminate | intros K' C; discriminate | exact Hc].
        -- right; intro Hc; inversion Hc; subst; try congruence; try contradiction.
      * (* A = dyn: from_dyn (cast_form (all)) *)
        left; apply compat_from_dyn; [discriminate | apply cf_all].
    + (* B = tyabs KB B0 *)
      destruct (typ_eq_dec A dyn) as [->|HAd].
      * right; intro Hc; inversion Hc; subst; try congruence;
          match goal with H: cast_form (tyabs _ _) |- _ =>
            inversion H; subst; match goal with Hn': neutral _ |- _ => inversion Hn' end end.
      * destruct A as [nA | A1 A2 | KA A0 | KA A0 | A1 A2 | ].
        -- right; intro Hc; inversion Hc; subst; try congruence.
        -- right; intro Hc; inversion Hc; subst; try congruence.
        -- destruct (kind_eq_dec KA KStar) as [->|HK].
           ++ destruct (IH (tsubst dyn 0 A0) (tyabs KB B0)) as [Hc|Hnc];
                [rewrite tsubst_dyn_size; pose proof (ty_size_pos A0); simpl (ty_size (all _ _)) in Hn; lia| |].
              ** left; apply compat_instantiate; [intros K' B'; discriminate | exact Hc].
              ** right; intro Hc; inversion Hc; subst; try congruence;
                   match goal with H: forall _ _, all _ _ <> all _ _ |- _ =>
                     solve [eapply H; reflexivity] end.
           ++ right; intro Hc; inversion Hc; subst; try congruence;
                match goal with H: forall _ _, all _ _ <> all _ _ |- _ =>
                  solve [eapply H; reflexivity] end.
        -- right; intro Hc; inversion Hc; subst; try congruence.
        -- right; intro Hc; inversion Hc; subst; try congruence.
        -- exfalso; apply HAd; reflexivity.
    + (* B = tyapp B1 B2 *)
      destruct (typ_eq_dec A dyn) as [->|HAd].
      * (* compat dyn (tyapp): from_dyn iff cast_form (tyapp) iff neutral *)
        destruct (neutral_dec (tyapp B1 B2)) as [Hne|Hnne].
        -- left; apply compat_from_dyn; [discriminate | apply cf_neutral; exact Hne].
        -- right; intro Hc; inversion Hc; subst; try congruence;
             match goal with H: cast_form (tyapp _ _) |- _ =>
               inversion H; subst; contradiction end.
      * (* A <> dyn, B = tyapp: INSTANTIATE if A = all KStar, else no *)
        destruct A as [nA | A1 A2 | KA A0 | KA A0 | A1 A2 | ].
        -- right; intro Hc; inversion Hc; subst; try congruence.
        -- right; intro Hc; inversion Hc; subst; try congruence.
        -- destruct (kind_eq_dec KA KStar) as [->|HK].
           ++ destruct (IH (tsubst dyn 0 A0) (tyapp B1 B2)) as [Hc|Hnc];
                [rewrite tsubst_dyn_size; pose proof (ty_size_pos A0); simpl (ty_size (all _ _)) in Hn; lia| |].
              ** left; apply compat_instantiate; [intros K' B'; discriminate | exact Hc].
              ** right; intro Hc; inversion Hc; subst; try congruence;
                   match goal with H: forall _ _, all _ _ <> all _ _ |- _ =>
                     solve [eapply H; reflexivity] end.
           ++ right; intro Hc; inversion Hc; subst; try congruence;
                match goal with H: forall _ _, all _ _ <> all _ _ |- _ =>
                  solve [eapply H; reflexivity] end.
        -- right; intro Hc; inversion Hc; subst; try congruence.
        -- right; intro Hc; inversion Hc; subst; try congruence.
        -- exfalso; apply HAd; reflexivity.
    + (* B = dyn *)
      destruct A as [nA | A1 A2 | KA A0 | KA A0 | A1 A2 | ].
      * left; eapply compat_to_dyn;
          [discriminate | intros K C; discriminate | apply gt_neutral; apply neutral_tvar | apply compat_refl].
      * (* arrow: need compat (arrow A1 A2) (arrow dyn dyn) *)
        destruct (IH dyn A1) as [Hc1|Hnc1];
          [simpl (ty_size (arrow _ _)) in Hn; pose proof (ty_size_pos A1); pose proof (ty_size_pos A2); lia| |].
        destruct (IH A2 dyn) as [Hc2|Hnc2];
          [simpl (ty_size (arrow _ _)) in Hn; pose proof (ty_size_pos A1); pose proof (ty_size_pos A2); lia| |].
        -- left; eapply compat_to_dyn;
             [discriminate | intros K C; discriminate | apply gt_arrow | apply compat_arrow; assumption].
        -- right. intro Hc.
           inversion Hc; subst; try congruence.
           apply Hnc2.
           inversion H1; subst;
             [| exfalso; match goal with Hn': neutral (arrow _ _) |- _ => inversion Hn' end].
           inversion H2; subst; [apply compat_refl | assumption].
        -- right. intro Hc.
           inversion Hc; subst; try congruence.
           apply Hnc1.
           inversion H1; subst;
             [| exfalso; match goal with Hn': neutral (arrow _ _) |- _ => inversion Hn' end].
           inversion H2; subst; [apply compat_refl | assumption].
      * destruct (kind_eq_dec KA KStar) as [->|HK].
        -- destruct (IH (tsubst dyn 0 A0) dyn) as [Hc|Hnc];
             [rewrite tsubst_dyn_size; pose proof (ty_size_pos A0); simpl (ty_size (all _ _)) in Hn; lia| |].
           ++ left; apply compat_instantiate; [intros K' B'; discriminate | exact Hc].
           ++ right; intro Hc; inversion Hc; subst; try congruence;
                match goal with H: forall _ _, all _ _ <> all _ _ |- _ =>
                  solve [eapply H; reflexivity] end.
        -- right; intro Hc; inversion Hc; subst; try congruence;
             match goal with H: forall _ _, all _ _ <> all _ _ |- _ =>
               solve [eapply H; reflexivity] end.
      * (* A = tyabs: no ground tag, not all *)
        right; intro Hc; inversion Hc; subst; try congruence;
          match goal with H: ground_tag (tyabs _ _) _ |- _ =>
            inversion H; subst; match goal with Hn': neutral _ |- _ => inversion Hn' end end.
      * (* A = tyapp: to_dyn iff neutral *)
        destruct (neutral_dec (tyapp A1 A2)) as [Hne|Hnne].
        -- left; eapply compat_to_dyn;
             [discriminate | intros K C; discriminate | apply gt_neutral; exact Hne | apply compat_refl].
        -- right; intro Hc; inversion Hc; subst; try congruence;
             match goal with H: ground_tag (tyapp _ _) _ |- _ =>
               inversion H; subst; contradiction end.
      * exfalso; apply HAB; reflexivity.
Qed.

(** Compatibility is decidable, by well-founded recursion on total type size. *)
Lemma compat_dec: forall A B, {compat A B} + {~ compat A B}.
Proof. intros A B. apply (compat_dec_fuel (ty_size A + ty_size B)); lia. Qed.

(** ** Compatibility inversions *)

(** Compatible arrows are compatible pointwise: contravariant domain, covariant
    codomain.  Both [compat_arrow] and [compat_refl] (via [cf_arrow]) can build
    an arrow/arrow compatibility, and [compat_refl] reduces to the reflexive
    subcase. *)
Lemma compat_arrow_inv: forall A1 A2 B1 B2,
  compat (arrow A1 A2) (arrow B1 B2) -> compat B1 A1 /\ compat A2 B2.
Proof.
  intros A1 A2 B1 B2 H. inversion H; subst.
  - (* compat_refl *) split; apply compat_refl.
  - split; assumption.
Qed.

(** ** Term-level operations *)

(** Shift term variable indices >= [k] up by [i]. *)
Fixpoint lift (i: nat) (k: nat) (e: term): term :=
  match e with
  | var n => if le_gt_dec k n then var (i + n) else var n
  | abs t e1 => abs t (lift i (S k) e1)
  | app e1 e2 => app (lift i k e1) (lift i k e2)
  | tabs K e1 => tabs K (lift i k e1)
  | tapp e1 t => tapp (lift i k e1) t
  | cast e1 A B p => cast (lift i k e1) A B p
  | gnd e1 G => gnd (lift i k e1) G
  | is_gnd e1 G => is_gnd (lift i k e1) G
  | blame p => blame p
  | nu K A e1 => nu K A (lift i k e1)
  end.

(** Shift type variable indices inside a term; increments cutoff when crossing [tabs]. *)
Fixpoint term_tlift (i: nat) (k: nat) (e: term): term :=
  match e with
  | var n => var n
  | abs t e1 => abs (tlift i k t) (term_tlift i k e1)
  | app e1 e2 => app (term_tlift i k e1) (term_tlift i k e2)
  | tabs K e1 => tabs K (term_tlift i (S k) e1)
  | tapp e1 t => tapp (term_tlift i k e1) (tlift i k t)
  | cast e1 A B p => cast (term_tlift i k e1) (tlift i k A) (tlift i k B) p
  | gnd e1 G => gnd (term_tlift i k e1) (tlift i k G)
  | is_gnd e1 G => is_gnd (term_tlift i k e1) (tlift i k G)
  | blame p => blame p
  | nu K A e1 => nu K (tlift i k A) (term_tlift i (S k) e1)
  end.

(** Capture-avoiding substitution of term [p] for term variable [k] in [q]. *)
Fixpoint subst (p: term) (k: nat) (q: term): term :=
  match q with
  | var n =>
    match lt_eq_lt_dec k n with
    | inleft (left _) => var (pred n)
    | inleft (right _) => lift k 0 p
    | inright _ => var n
    end
  | abs t e => abs t (subst p (S k) e)
  | app e1 e2 => app (subst p k e1) (subst p k e2)
  | tabs K e => tabs K (subst (term_tlift 1 0 p) k e)
  | tapp e t => tapp (subst p k e) t
  | cast e A B l => cast (subst p k e) A B l
  | gnd e G => gnd (subst p k e) G
  | is_gnd e G => is_gnd (subst p k e) G
  | blame l => blame l
  | nu K A e => nu K A (subst (term_tlift 1 0 p) k e)
  end.

(** Substitute type [s] for type variable [k] throughout term [e]. *)
Fixpoint term_tsubst (s: typ) (k: nat) (e: term): term :=
  match e with
  | var n => var n
  | abs t e1 => abs (tsubst s k t) (term_tsubst s k e1)
  | app e1 e2 => app (term_tsubst s k e1) (term_tsubst s k e2)
  | tabs K e1 => tabs K (term_tsubst s (S k) e1)
  | tapp e1 t => tapp (term_tsubst s k e1) (tsubst s k t)
  | cast e1 A B p => cast (term_tsubst s k e1) (tsubst s k A) (tsubst s k B) p
  | gnd e1 G => gnd (term_tsubst s k e1) (tsubst s k G)
  | is_gnd e1 G => is_gnd (term_tsubst s k e1) (tsubst s k G)
  | blame p => blame p
  | nu K A e1 => nu K (tsubst s k A) (term_tsubst s (S k) e1)
  end.

(** ** Commutation and cancellation lemmas *)

(** Neutrality is preserved by type lifting (lifting only reindexes the head
    variable, keeping the head a variable). *)
Lemma neutral_tlift: forall N i k, neutral N -> neutral (tlift i k N).
Proof.
  intros N i k HN. revert i k. induction HN; intros i k; simpl.
  - destruct (le_gt_dec k n); apply neutral_tvar.
  - apply neutral_tyapp. apply IHHN.
Qed.

(** Groundness is preserved by type lifting. *)
Lemma ground_tlift: forall G i k, ground G -> ground (tlift i k G).
Proof.
  intros G i k HG. inversion HG; subst; simpl.
  - apply ground_arrow.
  - apply ground_neutral. apply neutral_tlift. assumption.
Qed.

(** [tlift] preserves the head-constructor shape, so the "not [dyn]" and
    "not [∀]" guards (used by the [compat]/subtyping [∀]-rules) survive it. *)
Lemma tlift_not_dyn: forall A i k, A <> dyn -> tlift i k A <> dyn.
Proof.
  intros A i k H Heq. destruct A; simpl in Heq;
    [ destruct (le_gt_dec k n) | | | | | apply H; reflexivity ]; discriminate.
Qed.

Lemma tlift_not_all: forall A,
  (forall K C, A <> all K C) -> forall i k K C, tlift i k A <> all K C.
Proof.
  intros A Hna i k K C Heq.
  destruct A; simpl in Heq; try (destruct (le_gt_dec k n)); try discriminate.
  injection Heq; intros; subst. eapply Hna; reflexivity.
Qed.

(** [cast_form] and [ground_tag] are preserved by type lifting. *)
Lemma cast_form_tlift: forall A i k, cast_form A -> cast_form (tlift i k A).
Proof.
  intros A i k H. inversion H; subst; simpl;
    [ apply cf_dyn | apply cf_arrow | apply cf_all
    | apply cf_neutral; apply neutral_tlift; assumption ].
Qed.

Lemma ground_tag_tlift: forall A G i k,
  ground_tag A G -> ground_tag (tlift i k A) (tlift i k G).
Proof.
  intros A G i k H. inversion H; subst; simpl.
  - apply gt_arrow.
  - apply gt_neutral. apply neutral_tlift. assumption.
Qed.

(** ** Substituting an abstract (neutral) type name

    Neutrals are *not* closed under substitution in general (substituting a
    [tyabs] for the head variable of a neutral creates a redex).  But
    substituting a *neutral* type [s] — an abstract type name — for a variable
    does preserve neutrality, and hence groundness, cast-forms, and ground
    tags.  This is the ν-aware fragment of the substitution metatheory: a
    sealed variable stands for an abstract name, so type substitution during
    ν-elimination only ever plugs in neutral witnesses. *)

Lemma neutral_tsubst: forall N s k, neutral s -> neutral N -> neutral (tsubst s k N).
Proof.
  intros N s k Hs HN. revert k. induction HN; intros k; simpl.
  - destruct (lt_eq_lt_dec k n) as [[?|?]|?].
    + apply neutral_tvar.
    + apply neutral_tlift. exact Hs.
    + apply neutral_tvar.
  - apply neutral_tyapp. apply IHHN.
Qed.

Lemma tsubst_neutral_not_dyn: forall A s k,
  neutral s -> A <> dyn -> tsubst s k A <> dyn.
Proof.
  intros A s k Hs H Heq. destruct A; simpl in Heq.
  - destruct (lt_eq_lt_dec k n) as [[?|?]|?]; try discriminate.
    assert (Hn: neutral (tlift k 0 s)) by (apply neutral_tlift; exact Hs).
    exact (neutral_not_dyn _ Hn Heq).
  - discriminate.
  - discriminate.
  - discriminate.
  - discriminate.
  - apply H; reflexivity.
Qed.

Lemma tsubst_neutral_not_all: forall A s,
  neutral s -> (forall K C, A <> all K C) ->
  forall k K C, tsubst s k A <> all K C.
Proof.
  intros A s Hs Hna k K C Heq. destruct A; simpl in Heq.
  - destruct (lt_eq_lt_dec k n) as [[?|?]|?]; try discriminate.
    assert (Hn: neutral (tlift k 0 s)) by (apply neutral_tlift; exact Hs).
    exact (neutral_not_all _ Hn K C Heq).
  - discriminate.
  - injection Heq; intros; subst. eapply Hna; reflexivity.
  - discriminate.
  - discriminate.
  - discriminate.
Qed.

Lemma cast_form_tsubst: forall A s k,
  neutral s -> cast_form A -> cast_form (tsubst s k A).
Proof.
  intros A s k Hs H. inversion H; subst; simpl;
    [ apply cf_dyn | apply cf_arrow | apply cf_all
    | apply cf_neutral; apply neutral_tsubst; assumption ].
Qed.

Lemma ground_tag_tsubst: forall A G s k,
  neutral s -> ground_tag A G -> ground_tag (tsubst s k A) (tsubst s k G).
Proof.
  intros A G s k Hs H. inversion H; subst; simpl.
  - apply gt_arrow.
  - apply gt_neutral. apply neutral_tsubst; assumption.
Qed.

(** Auxiliary module proving that [tlift] and [tsubst dyn] commute: [tlift i k (tsubst dyn 0 A) = tsubst dyn 0 (tlift i (S k) A)]. *)
Module TliftTsubstDyn.
Local Opaque le_gt_dec lt_eq_lt_dec.

(** Base case of the commutation lemma for type variables. *)
Lemma tvar_case: forall n i j k,
  tlift i (j + k) (tsubst dyn j (tvar n)) = tsubst dyn j (tlift i (S (j + k)) (tvar n)).
Proof.
  intros. simpl.
  destruct (lt_eq_lt_dec j n) as [[Hjn|Hjn]|Hjn].
  - (* j < n *)
    destruct n as [|n']; [lia|]. simpl.
    destruct (le_gt_dec (j + k) n') as [H1|H1].
    + destruct (le_gt_dec (S (j + k)) (S n')) as [H2|H2]; [|lia].
      simpl. replace (i + S n') with (S (i + n')) by lia.
      destruct (lt_eq_lt_dec j (S (i + n'))) as [[?|?]|?]; [|lia|lia].
      simpl. reflexivity.
    + destruct (le_gt_dec (S (j + k)) (S n')) as [H2|H2]; [lia|].
      simpl. destruct (lt_eq_lt_dec j (S n')) as [[?|?]|?]; [|lia|lia].
      reflexivity.
  - (* j = n *)
    subst. simpl.
    destruct (lt_eq_lt_dec n n) as [[?|?]|?]; [lia| |lia]. simpl.
    destruct (le_gt_dec (S (n + k)) n) as [?|?]; [lia|]. simpl.
    destruct (lt_eq_lt_dec n n) as [[?|?]|?]; [lia| |lia]. simpl.
    destruct (le_gt_dec 0 n) as [?|?]; [|lia]. simpl.
    reflexivity.
  - (* j > n *)
    simpl.
    destruct (le_gt_dec (j + k) n) as [?|?]; [lia|]. simpl.
    destruct (le_gt_dec (S (j + k)) n) as [?|?]; [lia|]. simpl.
    destruct (lt_eq_lt_dec j n) as [[?|?]|?]; [lia|lia|]. simpl.
    reflexivity.
Qed.

(** Commutation for general types with explicit offset [j + k]. *)
Lemma tlift_tsubst_dyn_aux: forall A i j k,
  tlift i (j + k) (tsubst dyn j A) = tsubst dyn j (tlift i (S (j + k)) A).
Proof.
  induction A; intros i j k; simpl.
  - apply tvar_case.
  - f_equal; auto.
  - simpl. f_equal. replace (S (j + k)) with (S j + k) by lia. apply IHA.
  - simpl. f_equal. replace (S (j + k)) with (S j + k) by lia. apply IHA.
  - f_equal; auto.
  - reflexivity.
Qed.

(** Main commutation: [tlift i k (tsubst dyn 0 A) = tsubst dyn 0 (tlift i (S k) A)]. *)
Lemma tlift_tsubst_dyn: forall A i k,
  tlift i k (tsubst dyn 0 A) = tsubst dyn 0 (tlift i (S k) A).
Proof.
  intros. change k with (0 + k). apply tlift_tsubst_dyn_aux.
Qed.

End TliftTsubstDyn.

(** Export the commutation lemma outside the module. *)
Definition tlift_tsubst_dyn := TliftTsubstDyn.tlift_tsubst_dyn.

(** Substituting for the lifted variable cancels the lift: [tsubst s k (tlift 1 k t) = t]. *)
Lemma tsubst_tlift_cancel:
  forall t s k, tsubst s k (tlift 1 k t) = t.
Proof.
  induction t; intros; simpl.
  - destruct (le_gt_dec k n).
    + simpl. destruct (lt_eq_lt_dec k (S n)) as [[?|?]|?]; try lia.
      reflexivity.
    + simpl. destruct (lt_eq_lt_dec k n) as [[?|?]|?]; try lia.
      reflexivity.
  - f_equal; auto.
  - f_equal; auto.
  - f_equal; auto.
  - f_equal; auto.
  - reflexivity.
Qed.

(** Auxiliary module proving [tlift 1 j (tlift i k t) = tlift i (S k) (tlift 1 j t)] when [j ≤ k]. *)
Module TliftComm.
Local Opaque le_gt_dec.

(** Arithmetic helper: addition is commutative with 1 in the middle. *)
Lemma add_1_comm: forall i n, 1 + (i + n) = i + (1 + n).
Proof.
  intros i n.
  rewrite Nat.add_assoc. rewrite (Nat.add_comm 1 i). rewrite <- Nat.add_assoc. reflexivity.
Qed.

(** Base case of the lift-commutativity lemma for type variables. *)
Lemma tvar_case: forall n i j k,
  j <= k ->
  tlift 1 j (tlift i k (tvar n)) = tlift i (S k) (tlift 1 j (tvar n)).
Proof.
  intros n i j k Hjk. simpl.
  destruct (le_gt_dec k n) as [Hkn|Hkn].
  - simpl.
    destruct (le_gt_dec j (i+n)) as [H1|H1].
    + simpl. destruct (le_gt_dec j n) as [H2|H2].
      * simpl. destruct (le_gt_dec (S k) (1+n)) as [H3|H3].
        -- simpl. destruct (le_gt_dec (S k) (S n)) as [H4|H4].
           ++ f_equal. apply add_1_comm.
           ++ exfalso. apply Nat.lt_irrefl with n.
              apply Nat.lt_le_trans with k.
              ** unfold gt in H4. exact (proj2 (Nat.succ_lt_mono n k) H4).
              ** exact Hkn.
        -- exfalso. apply Nat.lt_irrefl with n.
           apply Nat.lt_le_trans with k.
           ++ unfold gt in H3. exact (proj2 (Nat.succ_lt_mono n k) H3).
           ++ exact Hkn.
      * exfalso. exact (Nat.lt_irrefl j
          (Nat.le_lt_trans j n j (Nat.le_trans j k n Hjk Hkn) H2)).
    + exfalso. exact (Nat.lt_irrefl j
        (Nat.le_lt_trans j (i+n) j
          (Nat.le_trans j k (i+n) Hjk
            (Nat.le_trans k n (i+n) Hkn (Nat.le_add_l n i)))
          H1)).
  - simpl. destruct (le_gt_dec j n) as [H1|H1].
    + simpl. destruct (le_gt_dec (S k) (1+n)) as [H2|H2].
      * exfalso. apply Nat.lt_irrefl with n.
        apply Nat.lt_le_trans with k.
        -- exact Hkn.
        -- exact (proj2 (Nat.succ_le_mono k n) H2).
      * simpl. destruct (le_gt_dec (S k) (S n)) as [H3|H3].
        -- exfalso. apply Nat.lt_irrefl with n. apply Nat.lt_le_trans with k.
           ++ exact Hkn.
           ++ exact (proj2 (Nat.succ_le_mono k n) H3).
        -- reflexivity.
    + simpl. destruct (le_gt_dec (S k) n) as [H2|H2].
      * exfalso. apply Nat.lt_irrefl with n.
        apply Nat.lt_le_trans with k.
        -- exact Hkn.
        -- apply Nat.le_trans with (S k).
           ++ exact (Nat.le_succ_diag_r k).
           ++ exact H2.
      * reflexivity.
Qed.

(** Two lifts at positions [j ≤ k] commute when one is by 1. *)
Lemma tlift_comm_1j: forall t i j k,
  j <= k -> tlift 1 j (tlift i k t) = tlift i (S k) (tlift 1 j t).
Proof.
  induction t; intros i j k Hjk.
  - apply tvar_case. exact Hjk.
  - simpl. f_equal; auto.
  - simpl. f_equal. apply IHt. exact (proj1 (Nat.succ_le_mono j k) Hjk).
  - simpl. f_equal. apply IHt. exact (proj1 (Nat.succ_le_mono j k) Hjk).
  - simpl. f_equal; auto.
  - reflexivity.
Qed.

(** Special case at [j = 0]: lifting from the outside commutes with lifting from the inside. *)
Lemma tlift_comm_10: forall t i k,
  tlift 1 0 (tlift i k t) = tlift i (S k) (tlift 1 0 t).
Proof. intros. apply tlift_comm_1j. apply Nat.le_0_l. Qed.

End TliftComm.

(** Export the lift-commutativity lemma outside the module. *)
Definition tlift_comm_10 := TliftComm.tlift_comm_10.

(** Compatibility is preserved by type lifting: every cast-reduction strategy
    named by a [compat] constructor survives a [tlift] (the guards use
    [tlift_not_dyn]/[tlift_not_all], the ground tags use [ground_tag_tlift],
    and the [generalize]/[instantiate] recursions use the [tlift] commutation
    lemmas [tlift_comm_10]/[tlift_tsubst_dyn]). *)
Lemma compat_tlift: forall A B, compat A B ->
  forall i k, compat (tlift i k A) (tlift i k B).
Proof.
  intros A B H. induction H; intros i k; simpl.
  - apply compat_refl.
  - apply compat_arrow; auto.
  - apply compat_all; auto.
  - apply compat_generalize.
    + apply tlift_not_dyn; assumption.
    + apply tlift_not_all; assumption.
    + rewrite tlift_comm_10. apply (IHcompat i (S k)).
  - apply compat_instantiate.
    + apply tlift_not_all; assumption.
    + rewrite <- tlift_tsubst_dyn. apply (IHcompat i k).
  - apply compat_to_dyn with (tlift i k G).
    + apply tlift_not_dyn; assumption.
    + apply tlift_not_all; assumption.
    + apply ground_tag_tlift; assumption.
    + apply IHcompat.
  - apply compat_from_dyn.
    + apply tlift_not_dyn; assumption.
    + apply cast_form_tlift; assumption.
Qed.

(** ** Adjacent type-variable swap *)

(** Swap type variables [k] and [S k] in a type.  Needed for the de Bruijn
    version of νX:=A.(ΛY.v) → ΛY.(νX:=A.v), which exchanges the two
    nearest type binders. *)
Fixpoint tswap (k: nat) (A: typ): typ :=
  match A with
  | tvar n =>
      if Nat.eq_dec n k then tvar (S k)
      else if Nat.eq_dec n (S k) then tvar k
      else tvar n
  | arrow A B => arrow (tswap k A) (tswap k B)
  | all K A => all K (tswap (S k) A)
  | tyabs K A => tyabs K (tswap (S k) A)
  | tyapp F A => tyapp (tswap k F) (tswap k A)
  | dyn => dyn
  end.

(** Swap type variables [k] and [S k] inside a term. *)
Fixpoint term_tswap (k: nat) (e: term): term :=
  match e with
  | var n => var n
  | abs A e => abs (tswap k A) (term_tswap k e)
  | app e1 e2 => app (term_tswap k e1) (term_tswap k e2)
  | tabs K e => tabs K (term_tswap (S k) e)
  | tapp e A => tapp (term_tswap k e) (tswap k A)
  | cast e A B p => cast (term_tswap k e) (tswap k A) (tswap k B) p
  | gnd e G => gnd (term_tswap k e) (tswap k G)
  | is_gnd e G => is_gnd (term_tswap k e) (tswap k G)
  | blame p => blame p
  | nu K A e => nu K (tswap k A) (term_tswap (S k) e)
  end.

(** [tswap] is an involution: swapping the same adjacent pair twice is the identity. *)

(** Base case of [tswap_involutive] for type variables. *)
Lemma tswap_tvar: forall n k,
  tswap k (tswap k (tvar n)) = tvar n.
Proof.
  intros n k.
  unfold tswap.
  destruct (Nat.eq_dec n k) as [->|Hn1].
  - destruct (Nat.eq_dec (S k) k) as [H|_]; [lia|].
    destruct (Nat.eq_dec (S k) (S k)) as [_|H]; [|exfalso; auto].
    reflexivity.
  - destruct (Nat.eq_dec n (S k)) as [->|Hn2].
    + destruct (Nat.eq_dec k k) as [_|H]; [|exfalso; auto].
      reflexivity.
    + destruct (Nat.eq_dec n k) as [H|_]; [congruence|].
      destruct (Nat.eq_dec n (S k)) as [H|_]; [congruence|].
      reflexivity.
Qed.

Lemma tswap_involutive: forall A k, tswap k (tswap k A) = A.
Proof.
  induction A; intros k; simpl; f_equal; auto.
  apply tswap_tvar.
Qed.

(** Case-splits every [lt_eq_lt_dec]/[Nat.eq_dec]/[le_gt_dec] scrutinee arising
    from unfolding [tswap]/[tsubst]/[tlift] on a variable, then closes each
    resulting arithmetic goal with [lia] or [congruence].  Shared by the
    variable-case lemmas below, which otherwise differ only in which
    De Bruijn operation is being commuted with [tswap]. *)
Local Ltac solve_tvar_cases :=
  repeat match goal with
  | |- context[lt_eq_lt_dec ?a ?b] => destruct (lt_eq_lt_dec a b) as [[?|?]|?]
  | |- context[Nat.eq_dec ?a ?b] => destruct (Nat.eq_dec a b)
  | |- context[le_gt_dec ?a ?b] => destruct (le_gt_dec a b)
  end;
  subst; simpl in *;
  try reflexivity; try (f_equal; lia); try (exfalso; lia); try congruence.

(** Swapping adjacent variables commutes with substituting [dyn], with the
    expected cutoff shift under binders.  This trio ([_tvar] base case,
    [_aux] structural induction with an explicit offset, and the [k = 0]
    corollary) mirrors the [TliftTsubstDyn] module above but for [tswap]. *)
Lemma tswap_tsubst_dyn_tvar: forall n j k,
  tswap (j + k) (tsubst dyn j (tvar n)) = tsubst dyn j (tswap (S (j + k)) (tvar n)).
Proof.
  intros n j k.
  unfold tswap, tsubst.
  solve_tvar_cases.
Qed.

(** Structural extension of [tswap_tsubst_dyn_tvar] to all types. *)
Lemma tswap_tsubst_dyn_aux: forall A j k,
  tswap (j + k) (tsubst dyn j A) = tsubst dyn j (tswap (S (j + k)) A).
Proof.
  induction A; intros j k; simpl.
  - apply tswap_tsubst_dyn_tvar.
  - rewrite IHA1, IHA2. reflexivity.
  - f_equal. replace (S (j + k)) with (S j + k) by lia. apply IHA.
  - f_equal. replace (S (j + k)) with (S j + k) by lia. apply IHA.
  - rewrite IHA1, IHA2. reflexivity.
  - reflexivity.
Qed.

(** Specialization of [tswap_tsubst_dyn_aux] at offset [0]. *)
Lemma tswap_tsubst_dyn: forall A k,
  tswap k (tsubst dyn 0 A) = tsubst dyn 0 (tswap (S k) A).
Proof. intros A k. change k with (0 + k). apply tswap_tsubst_dyn_aux. Qed.

(** Swapping adjacent variables commutes with weakening by one at the outside.
    Same [_tvar]/[_aux] structure as the [tsubst dyn] trio above. *)
Lemma tswap_tlift_1_tvar: forall n j k,
  tswap (S (j + k)) (tlift 1 j (tvar n)) = tlift 1 j (tswap (j + k) (tvar n)).
Proof.
  intros n j k.
  unfold tlift, tswap.
  solve_tvar_cases.
Qed.

(** Structural extension of [tswap_tlift_1_tvar] to all types. *)
Lemma tswap_tlift_1_aux: forall A j k,
  tswap (S (j + k)) (tlift 1 j A) = tlift 1 j (tswap (j + k) A).
Proof.
  induction A; intros j k; simpl.
  - apply tswap_tlift_1_tvar.
  - rewrite IHA1, IHA2. reflexivity.
  - f_equal. replace (S (j + k)) with (S j + k) by lia. apply IHA.
  - f_equal. replace (S (j + k)) with (S j + k) by lia. apply IHA.
  - rewrite IHA1, IHA2. reflexivity.
  - reflexivity.
Qed.

(** Specialization of [tswap_tlift_1_aux] at offset [0]. *)
Lemma tswap_tlift_10: forall A k,
  tswap (S k) (tlift 1 0 A) = tlift 1 0 (tswap k A).
Proof. intros A k. change k with (0 + k). apply tswap_tlift_1_aux. Qed.


(** ** Type-level reduction and definitional equality (F-omega)

    The higher-kinded type layer has its own [beta] rule for the type-operator
    application [tyapp (tyabs K A) B]; [ty_equiv] is the induced definitional
    equality (its reflexive/symmetric/transitive closure).  This is what makes
    the target's type language a genuine F-omega with type-level computation,
    rather than mere F-omega syntax. *)

(** One-step type-level reduction: beta for [tyapp (tyabs K A) B], plus structural congruence closure. *)
Inductive ty_step : typ -> typ -> Prop :=
  | tystep_beta : forall K A B,
      ty_step (tyapp (tyabs K A) B) (tsubst B 0 A)
  | tystep_arrow_l : forall A A' B,
      ty_step A A' -> ty_step (arrow A B) (arrow A' B)
  | tystep_arrow_r : forall A B B',
      ty_step B B' -> ty_step (arrow A B) (arrow A B')
  | tystep_all : forall K A A',
      ty_step A A' -> ty_step (all K A) (all K A')
  | tystep_tyabs : forall K A A',
      ty_step A A' -> ty_step (tyabs K A) (tyabs K A')
  | tystep_tyapp_l : forall F F' A,
      ty_step F F' -> ty_step (tyapp F A) (tyapp F' A)
  | tystep_tyapp_r : forall F A A',
      ty_step A A' -> ty_step (tyapp F A) (tyapp F A').

Hint Constructors ty_step: blame.

(** Definitional equality on types: the equivalence closure of [ty_step]. *)
Definition ty_equiv : typ -> typ -> Prop := clos_refl_sym_trans _ ty_step.

(** [ty_equiv] is reflexive. *)
Lemma ty_equiv_refl : forall A, ty_equiv A A.
Proof. intro A; apply rst_refl. Qed.

(** [ty_equiv] is symmetric. *)
Lemma ty_equiv_sym : forall A B, ty_equiv A B -> ty_equiv B A.
Proof. intros A B H; apply rst_sym; exact H. Qed.

(** [ty_equiv] is transitive. *)
Lemma ty_equiv_trans : forall A B C, ty_equiv A B -> ty_equiv B C -> ty_equiv A C.
Proof. intros A B C H1 H2; eapply rst_trans; eauto. Qed.

(** Every [ty_step] step is a [ty_equiv]. *)
Lemma ty_step_equiv : forall A B, ty_step A B -> ty_equiv A B.
Proof. intros A B H; apply rst_step; exact H. Qed.

(** The defining computation rule, as a definitional equality. *)
Lemma ty_equiv_beta : forall K A B,
  ty_equiv (tyapp (tyabs K A) B) (tsubst B 0 A).
Proof. intros; apply ty_step_equiv; apply tystep_beta. Qed.

Hint Resolve ty_equiv_refl ty_step_equiv ty_equiv_beta: blame.
