From Stdlib Require Import Arith Lia List Relations Bool Program.Equality.
Import ListNotations.
From CoC Require terms.
From CoC Require typing.
From CoC Require Import confluence.
From CoC Require Import inference.
From CoC Require Import strong_normalization.
From CoC Require Import decidable_conversion.
From BlameFOmega Require syntax infrastructure semantics typing subtyping safety blame subtyping_safety simulation.
From Extraction Require extraction.
From Extraction Require Import common.
From Extraction Require Import source_facts.
From Extraction Require Import translation.

Import terms.
Import CoC.typing.
Import extraction.

From Extraction Require Import context_facts.
From Extraction Require Import type_extraction_facts.
From Extraction Require Import typing_proof.


Lemma coerce_sim_l : forall s t A B,
  simulation.sim s t -> simulation.sim (coerce s A B) t.
Proof.
  intros s t A B Hst. unfold coerce.
  destruct (syntax.typ_eq_dec A B); [exact Hst |].
  destruct (infrastructure.compat_dec A B).
  - apply simulation.sim_left_sc. exact Hst.
  - apply simulation.sim_blame.
Qed.

(** Both sides of [sim] may have the same [coerce] (compat-agnostic). *)
Lemma coerce_sim_both : forall s t A B,
  simulation.sim s t -> simulation.sim (coerce s A B) (coerce t A B).
Proof.
  intros s t A B Hst. unfold coerce.
  destruct (syntax.typ_eq_dec A B); [exact Hst |].
  destruct (infrastructure.compat_dec A B).
  - apply simulation.sim_left_sc. apply simulation.sim_right_sc. exact Hst.
  - apply simulation.sim_blame.
Qed.

(** [sim_star] may strip a [coerce] on the left. *)
Lemma coerce_sim_star_l : forall s t A B,
  simulation.sim_star s t ->
  simulation.sim_star (coerce s A B) t.
Proof.
  intros s t A B H.
  eapply simulation.sim_star_trans; [| exact H].
  apply simulation.sim_star_step.
  apply coerce_sim_l. apply simulation.sim_refl.
Qed.

(** [sim_star s (coerce s A B)] when [compat A B]: the coerce is a no-op up to simulation. *)
Lemma sim_star_self_coerce_compat : forall s A B,
  infrastructure.compat A B ->
  simulation.sim_star s (extraction.coerce s A B).
Proof.
  intros s A B Hcomp.
  unfold extraction.coerce.
  destruct (syntax.typ_eq_dec A B) as [-> | Hne].
  - apply simulation.sim_star_refl.
  - destruct (infrastructure.compat_dec A B) as [_ | Hn].
    + apply simulation.sim_star_step. apply simulation.sim_right_sc.
      apply simulation.sim_refl.
    + exfalso. apply Hn. exact Hcomp.
Qed.

(** Compat: the coerce between an open and substituted type-extraction is
    always [compat]-valid when [V0] is small.  Proved (below, after the
    type-namespace substitution machinery) via the stronger syntactic equality
    [extract_typ (V0::e) Ur = extract_typ e (subst v0 Ur)]. *)
(** Proved below, after [extract_typ_small_subst_eq]. *)

(** Both sides of [sim_star] may have the same [coerce] (compat-agnostic). *)
Lemma coerce_sim_star_both : forall s t A B,
  simulation.sim_star s t ->
  simulation.sim_star (coerce s A B) (coerce t A B).
Proof.
  intros s t A B H. induction H.
  - apply simulation.sim_star_step. apply coerce_sim_both. exact H.
  - apply simulation.sim_star_refl.
  - eapply simulation.sim_star_trans; eassumption.
Qed.

(** The right-hand [coerce] may carry [tlift]ed annotations: a term-weakening
    leaves the (type) annotations of a cast unchanged on the left, but the
    corresponding extraction in the weakened context annotates with the
    type-lifted forms.  The branch chosen by [coerce] (id / cast / blame) is
    stable under [tlift] ([compat_tlift]), so any annotation mismatch is
    absorbed by [sim]'s cast-stripping rules. *)
Lemma coerce_sim_star_both_tlift : forall s t A B i k,
  simulation.sim_star s t ->
  simulation.sim_star (coerce s A B)
    (coerce t (infrastructure.tlift i k A) (infrastructure.tlift i k B)).
Proof.
  intros s t A B i k H. unfold coerce.
  destruct (syntax.typ_eq_dec A B) as [->|Hne].
  - destruct (syntax.typ_eq_dec (infrastructure.tlift i k B)
                (infrastructure.tlift i k B)) as [_|Hne']; [exact H | congruence].
  - destruct (infrastructure.compat_dec A B) as [Hc|Hnc].
    + destruct (syntax.typ_eq_dec (infrastructure.tlift i k A)
                  (infrastructure.tlift i k B)) as [Heq'|Hne'].
      * eapply simulation.sim_star_trans;
          [ apply simulation.sim_star_step; apply simulation.sim_left_sc;
            apply simulation.sim_refl | exact H ].
      * destruct (infrastructure.compat_dec (infrastructure.tlift i k A)
                    (infrastructure.tlift i k B)) as [Hc'|Hnc'].
        -- eapply simulation.sim_star_trans;
             [ apply simulation.sim_star_step; apply simulation.sim_left_sc;
               apply simulation.sim_refl |].
           eapply simulation.sim_star_trans; [ exact H |].
           apply simulation.sim_star_step; apply simulation.sim_right_sc;
             apply simulation.sim_refl.
        -- exfalso. apply Hnc'. apply infrastructure.compat_tlift. exact Hc.
    + apply simulation.sim_star_step. apply simulation.sim_blame.
Qed.

(** [sim_star] congruences for [tabs] and [tapp]. *)

Lemma sim_star_tabs : forall K s t,
  simulation.sim_star s t ->
  simulation.sim_star (syntax.tabs K s) (syntax.tabs K t).
Proof.
  intros K s t H. induction H.
  - apply simulation.sim_star_step.
    apply simulation.sim_type_abs. exact H.
  - apply simulation.sim_star_refl.
  - eapply simulation.sim_star_trans; eassumption.
Qed.

(** [tabs] congruence for [sim_star], ignoring the (irrelevant) kind annotations. *)
Lemma sim_star_tabs_gen : forall K K' s t,
  simulation.sim_star s t ->
  simulation.sim_star (syntax.tabs K s) (syntax.tabs K' t).
Proof.
  intros K K' s t H.
  eapply simulation.sim_star_trans.
  - exact (sim_star_tabs K s t H).
  - apply simulation.sim_star_step.
    apply simulation.sim_type_abs.
    apply simulation.sim_refl.
Qed.

(** [sim_star] congruence in the function position of a type application. *)
Lemma sim_star_tapp_l : forall s s' A,
  simulation.sim_star s s' ->
  simulation.sim_star (syntax.tapp s A) (syntax.tapp s' A).
Proof.
  intros s s' A H. induction H.
  - apply simulation.sim_star_step.
    apply simulation.sim_type_app; exact H.
  - apply simulation.sim_star_refl.
  - eapply simulation.sim_star_trans; eassumption.
Qed.

(** [sim_star] congruence in the type-argument position of a type application.
    Since [sim] ignores type arguments, this is trivially a one-step [sim]. *)
Lemma sim_star_tapp_r : forall s A A',
  simulation.sim_star (syntax.tapp s A) (syntax.tapp s A').
Proof.
  intros. apply simulation.sim_star_step.
  apply simulation.sim_type_app. apply simulation.sim_refl.
Qed.

(** [tapp] congruence for [sim_star], ignoring the (irrelevant) type arguments. *)
Lemma sim_star_tapp_gen : forall s s' A A',
  simulation.sim_star s s' ->
  simulation.sim_star (syntax.tapp s A) (syntax.tapp s' A').
Proof.
  intros s s' A A' H.
  eapply simulation.sim_star_trans.
  - exact (sim_star_tapp_l s s' A H).
  - apply simulation.sim_star_step.
    apply simulation.sim_type_app.
    apply simulation.sim_refl.
Qed.


(** ** Type-level infrastructure: weakening, environment reduction, subject
    reduction, and substitution for [has_type].

    These mirror the Prop-level lemmas in the CoC library but live in
    Type so that they produce [has_type] derivations we can feed to
    [extract].  The proofs follow the same structure as their Prop
    counterparts. *)

Lemma weakening_weak_t :
  forall A e t T,
  has_type e t T ->
  forall n f,
  insert_in_environment A n e f -> well_formed f ->
  has_type f (lift_rec 1 t n) (lift_rec 1 T n).
Proof.
  intros A.
  fix IH 4.
  intros e t T H.
  destruct H as [ e0 w0 | e0 w0 | e0 w0 v T0 il
                | e0 T0 s1 HT M U s2 HU HM | e0 v0 V0 Hv u Ur Hu
                | e0 T0 s1 HT U s2 HU | e0 t0 U0 V0 Htu Hconv s0 HV ];
    intros n f ins wf; simpl.
  - (* prop *) apply type_prop. exact wf.
  - (* set *) apply type_set. exact wf.
  - (* var *)
    destruct (le_gt_dec n v).
    + apply type_var; [exact wf |].
      destruct il as [x Heq Hnth]. subst T0.
      exists x.
      * unfold lift. rewrite simplify_lift_rec; [reflexivity | lia | lia].
      * exact (insert_item_ge A n e0 f ins v l x Hnth).
    + apply type_var; [exact wf |].
      exact (insert_item_lt A n e0 f ins v g T0 il).
  - (* abs *)
    assert (wf_ext : well_formed (lift_rec 1 T0 n :: f)).
    { apply wf_var with s1. exact (IH e0 T0 (sort_term s1) HT n f ins wf). }
    apply type_abs with s1 s2.
    + exact (IH e0 T0 (sort_term s1) HT n f ins wf).
    + exact (IH (T0 :: e0) U (sort_term s2) HU (S n) (lift_rec 1 T0 n :: f)
               (ins_succ A n e0 f T0 ins) wf_ext).
    + exact (IH (T0 :: e0) M U HM (S n) (lift_rec 1 T0 n :: f)
               (ins_succ A n e0 f T0 ins) wf_ext).
  - (* app *)
    rewrite distribute_lift_subst.
    apply type_app with (V := lift_rec 1 V0 n).
    + exact (IH e0 v0 V0 Hv n f ins wf).
    + exact (IH e0 u (prod V0 Ur) Hu n f ins wf).
  - (* prod *)
    assert (wf_ext : well_formed (lift_rec 1 T0 n :: f)).
    { apply wf_var with s1. exact (IH e0 T0 (sort_term s1) HT n f ins wf). }
    apply type_prod with s1.
    + exact (IH e0 T0 (sort_term s1) HT n f ins wf).
    + exact (IH (T0 :: e0) U (sort_term s2) HU (S n) (lift_rec 1 T0 n :: f)
               (ins_succ A n e0 f T0 ins) wf_ext).
  - (* conv *)
    apply type_conv with (U := lift_rec 1 U0 n) (s := s0).
    + exact (IH e0 t0 U0 Htu n f ins wf).
    + apply convertible_convertible_lift. exact Hconv.
    + exact (IH e0 V0 (sort_term s0) HV n f ins wf).
Qed.

(** Source weakening by one binder (Type-level typing). *)
Lemma weakening_t :
  forall e t T,
  has_type e t T -> forall A, well_formed (A :: e) ->
  has_type (A :: e) (lift 1 t) (lift 1 T).
Proof.
  intros e t T H A wfA.
  unfold lift.
  apply weakening_weak_t with (A := A) (e := e).
  - exact H.
  - apply ins_zero.
  - exact wfA.
Qed.

(** Source weakening by a block inserted at the bottom (Type-level typing). *)
Lemma weakening_at_t :
  forall n e f,
  skipn n e = f ->
  n <= length e ->
  forall t T, has_type f t T -> well_formed e ->
  has_type e (lift_rec n t 0) (lift_rec n T 0).
Proof.
  induction n as [|n0 IHn]; intros e f Htr Hlen t T Htyp Hwf.
  - rewrite lift_rec_zero. rewrite lift_rec_zero.
    simpl in Htr. subst f. exact Htyp.
  - destruct e as [|x l]; simpl in Htr; [simpl in Hlen; lia|].
    change (lift_rec (S n0) t 0) with (lift (S n0) t).
    change (lift_rec (S n0) T 0) with (lift (S n0) T).
    rewrite (simplify_lift t n0).
    pattern (lift (S n0) T). rewrite (simplify_lift T n0).
    subst f.
    inversion_clear Hwf as [| ? ? s0 HX].
    assert (Hlen' : n0 <= length l) by (simpl in Hlen; lia).
    apply weakening_t.
    + apply IHn with (skipn n0 l); auto.
      exact (has_type_t_well_formed_t l x (sort_term s0) HX).
    + exact (wf_var l x s0 HX).
Qed.

(** Extract a [has_type] sort proof from [well_formed] at any position. *)
Lemma wf_nth_sort_t :
  forall n e, well_formed e -> forall t, nth_error e n = Some t ->
  { s : sort & has_type (skipn (S n) e) t (sort_term s) }.
Proof.
  induction n as [|n0 IHn]; intros e Hwf t Hn.
  - destruct e as [|h l]; simpl in Hn; [discriminate|].
    injection Hn as <-.
    inversion_clear Hwf as [| ? ? s0 HX].
    exact (existT _ s0 HX).
  - destruct e as [|h l]; simpl in Hn; [discriminate|].
    inversion_clear Hwf as [| ? ? s0 HX].
    exact (IHn l (has_type_t_well_formed_t l h (sort_term s0) HX) t Hn).
Qed.

(** Typing is preserved when the environment reduces (Type-level). *)
Lemma has_type_reduces_environment_t :
  forall e t T, has_type e t T ->
  forall f, reduces_once_in_environment e f -> well_formed f ->
  has_type f t T.
Proof.
  fix IH 4.
  intros e t T H.
  destruct H as [ e0 w0 | e0 w0 | e0 w0 v T0 il
                | e0 T0 s1 HT M U s2 HU HM | e0 v0 V0 Hv u Ur Hu
                | e0 T0 s1 HT U s2 HU | e0 t0 U0 V0 Htu Hconv s0 HV ];
    intros f Hred wff.
  - (* prop *) apply type_prop. exact wff.
  - (* set *) apply type_set. exact wff.
  - (* var *)
    (* Case-split on nth_error e0 v (computable) to extract the raw binding *)
    destruct (nth_error e0 v) as [T0_raw|] eqn:Hn_e0.
    2: { exfalso. destruct il as [x Heq Hnth]. rewrite Hn_e0 in Hnth. discriminate. }
    (* Get T0 = lift (S v) T0_raw — eq is eliminable into Type *)
    assert (HT0 : T0 = lift (S v) T0_raw).
    { destruct il as [x Heq Hnth]. rewrite Hn_e0 in Hnth.
      injection Hnth as <-. exact Heq. }
    subst T0.
    (* Case-split on nth_error f v (computable) *)
    destruct (nth_error f v) as [u_f|] eqn:Hn_f.
    2: { exfalso.
         assert (Hlen : length f = length e0).
         { clear - Hred. induction Hred; simpl; lia. }
         assert (Hvlt : v < length e0).
         { apply (proj1 (nth_error_Some e0 v)). rewrite Hn_e0. discriminate. }
         assert (Hvltf : v < length f) by lia.
         apply (proj2 (nth_error_Some f v)) in Hvltf.
         rewrite Hn_f in Hvltf. exact (Hvltf eq_refl). }
    (* Build item_lift for f (Prop — fine) *)
    assert (il_f : item_lift (lift (S v) u_f) f v).
    { exists u_f; [reflexivity | exact Hn_f]. }
    (* Case-split on whether the lifted types are equal (Type-level) *)
    destruct (term_eq_dec (lift (S v) T0_raw) (lift (S v) u_f)) as [Heq_lift|Hneq_lift].
    + (* Unchanged *)
      rewrite Heq_lift.
      exact (type_var f wff v (lift (S v) u_f) il_f).
    + (* Changed: need type_conv *)
      (* Get sort of T0_raw from well_formed e0 *)
      destruct (wf_nth_sort_t v e0 w0 T0_raw Hn_e0) as [s Hs].
      (* skipn (S v) f = skipn (S v) e0 — from Prop, but eq on list is OK *)
      assert (Hskipn : skipn (S v) f = skipn (S v) e0).
      { destruct (reduces_item v (lift (S v) T0_raw) e0 il f Hred)
          as [Hkeep | [Hskip _]].
        - exfalso. apply Hneq_lift.
          destruct Hkeep as [x Heq Hnth]. rewrite Hn_f in Hnth.
          injection Hnth as <-. exact Heq.
        - exact (Hskip _ eq_refl). }
      (* Sort proof in f via skipn equality + weakening *)
      assert (Hvle : S v <= length f).
      { assert (Hlen : length f = length e0).
        { clear - Hred. induction Hred; simpl; lia. }
        assert (Hvlt : v < length e0).
        { apply (proj1 (nth_error_Some e0 v)). rewrite Hn_e0. discriminate. }
        lia. }
      assert (Hs_f : has_type f (lift (S v) T0_raw) (sort_term s)).
      { change (sort_term s) with (lift_rec (S v) (sort_term s) 0).
        apply weakening_at_t with (skipn (S v) f);
          [reflexivity | exact Hvle | rewrite Hskipn; exact Hs | exact wff]. }
      (* Convertibility (Prop — needed as Prop arg) *)
      assert (Hconv : convertible (lift (S v) u_f) (lift (S v) T0_raw)).
      { destruct (reduces_item v (lift (S v) T0_raw) e0 il f Hred)
          as [Hkeep | [_ [u0 Hred_u Hil_u]]].
        - exfalso. apply Hneq_lift.
          destruct Hkeep as [x Heq Hnth]. rewrite Hn_f in Hnth.
          injection Hnth as <-. exact Heq.
        - destruct Hil_u as [x Heq Hnth]. rewrite Hn_f in Hnth.
          injection Hnth as <-. rewrite Heq in Hred_u.
          apply one_step_convertible_expansion. exact Hred_u. }
      apply type_conv with (U := lift (S v) u_f) (s := s).
      * exact (type_var f wff v (lift (S v) u_f) il_f).
      * exact Hconv.
      * exact Hs_f.
  - (* abs *)
    assert (wff_ext : well_formed (T0 :: f)).
    { apply wf_var with s1. exact (IH e0 T0 (sort_term s1) HT f Hred wff). }
    apply type_abs with s1 s2.
    + exact (IH e0 T0 (sort_term s1) HT f Hred wff).
    + exact (IH (T0 :: e0) U (sort_term s2) HU (T0 :: f) (red_env_tl e0 f T0 Hred) wff_ext).
    + exact (IH (T0 :: e0) M U HM (T0 :: f) (red_env_tl e0 f T0 Hred) wff_ext).
  - (* app *)
    apply type_app with (V := V0).
    + exact (IH e0 v0 V0 Hv f Hred wff).
    + exact (IH e0 u (prod V0 Ur) Hu f Hred wff).
  - (* prod *)
    assert (wff_ext : well_formed (T0 :: f)).
    { apply wf_var with s1. exact (IH e0 T0 (sort_term s1) HT f Hred wff). }
    apply type_prod with s1.
    + exact (IH e0 T0 (sort_term s1) HT f Hred wff).
    + exact (IH (T0 :: e0) U (sort_term s2) HU (T0 :: f) (red_env_tl e0 f T0 Hred) wff_ext).
  - (* conv *)
    apply type_conv with (U := U0) (s := s0).
    + exact (IH e0 t0 U0 Htu f Hred wff).
    + exact Hconv.
    + exact (IH e0 V0 (sort_term s0) HV f Hred wff).
Qed.

(** Helper: var case for Type-level substitution weakening. *)
Lemma subst_weakening_var_t :
  forall g d t, has_type g d t ->
  forall e v T0, well_formed e -> item_lift T0 e v ->
  forall f n,
  substitute_in_environment d t n e f ->
  well_formed f -> skipn n f = g ->
  has_type f (subst_rec d (var v) n) (subst_rec d T0 n).
Proof.
  intros g d t Hd e v T0 w0 il f n Hsub wff Hskip.
  simpl.
  elim (lt_eq_lt_dec n v); [intro Hlt_eq | intro Hlt].
  - elim Hlt_eq; clear Hlt_eq; [intro Hgt | intro Heq].
    + destruct v as [|v0]; [exact (False_rect _ (Nat.nlt_0_r n Hgt))|].
      destruct (nth_error e (S v0)) as [x_raw|] eqn:Hn_e.
      2: { exfalso. destruct il as [x Hxeq Hxn].
           rewrite Hn_e in Hxn. discriminate. }
      assert (HT0 : T0 = lift (S (S v0)) x_raw).
      { destruct il as [x Hxeq Hxn]. rewrite Hn_e in Hxn.
        injection Hxn as <-. exact Hxeq. }
      subst T0. simpl.
      rewrite simplify_subst by auto with arith.
      assert (Hil_f : item_lift (lift (S v0) x_raw) f v0).
      { exists x_raw; [reflexivity |].
        exact (nth_substitute_above d t n e f Hsub v0
                 (proj1 (Nat.lt_succ_r n v0) Hgt) x_raw Hn_e). }
      exact (type_var f wff v0 (lift (S v0) x_raw) Hil_f).
    + subst v.
      destruct (nth_error e n) as [x_raw|] eqn:Hn_e.
      2: { exfalso. destruct il as [x Hxeq Hxn].
           rewrite Hn_e in Hxn. discriminate. }
      assert (HT0 : T0 = lift (S n) x_raw).
      { destruct il as [x Hxeq Hxn]. rewrite Hn_e in Hxn.
        injection Hxn as <-. exact Hxeq. }
      subst T0.
      assert (Hxt : x_raw = t).
      { pose proof (nth_substitute_eq d t n e f Hsub) as Hnt.
        rewrite Hn_e in Hnt. injection Hnt as <-. reflexivity. }
      subst x_raw.
      rewrite simplify_subst by auto with arith.
      exact (weakening_at_t n f g Hskip
               (substitute_length_le d t n e f Hsub) d t Hd wff).
  - exact (type_var f wff v (subst_rec d T0 n)
             (nth_substitute_below d t n e f Hsub v Hlt T0 il)).
Qed.

(** Type-level substitution lemma (general form). *)
Lemma has_type_substitute_weakening_t :
  forall g d t, has_type g d t ->
  forall e u U, has_type e u U ->
  forall f n,
  substitute_in_environment d t n e f ->
  well_formed f -> skipn n f = g ->
  has_type f (subst_rec d u n) (subst_rec d U n).
Proof.
  intros g d t Hd.
  fix IH 4.
  intros e u U Hu.
  destruct Hu as [ e0 w0 | e0 w0 | e0 w0 v T0 il
                 | e0 T0 s1 HT M U0 s2 HU HM | e0 v0 V0 Hv u0 Ur Hu
                 | e0 T0 s1 HT U0 s2 HU | e0 t0 U0 V0 Htu Hconv s0 HV ];
    intros f n Hsub wff Hskip; simpl.
  - apply type_prop. exact wff.
  - apply type_set. exact wff.
  - exact (subst_weakening_var_t g d t Hd e0 v T0 w0 il f n Hsub wff Hskip).
  - assert (wff_ext : well_formed (subst_rec d T0 n :: f)).
    { apply wf_var with s1.
      exact (IH e0 T0 (sort_term s1) HT f n Hsub wff Hskip). }
    apply type_abs with s1 s2.
    + exact (IH e0 T0 (sort_term s1) HT f n Hsub wff Hskip).
    + exact (IH (T0 :: e0) U0 (sort_term s2) HU (subst_rec d T0 n :: f) (S n)
               (sub_succ d t e0 f n T0 Hsub) wff_ext Hskip).
    + exact (IH (T0 :: e0) M U0 HM (subst_rec d T0 n :: f) (S n)
               (sub_succ d t e0 f n T0 Hsub) wff_ext Hskip).
  - rewrite distribute_subst.
    apply type_app with (V := subst_rec d V0 n).
    + exact (IH e0 v0 V0 Hv f n Hsub wff Hskip).
    + exact (IH e0 u0 (prod V0 Ur) Hu f n Hsub wff Hskip).
  - assert (wff_ext : well_formed (subst_rec d T0 n :: f)).
    { apply wf_var with s1.
      exact (IH e0 T0 (sort_term s1) HT f n Hsub wff Hskip). }
    apply type_prod with s1.
    + exact (IH e0 T0 (sort_term s1) HT f n Hsub wff Hskip).
    + exact (IH (T0 :: e0) U0 (sort_term s2) HU (subst_rec d T0 n :: f) (S n)
               (sub_succ d t e0 f n T0 Hsub) wff_ext Hskip).
  - apply type_conv with (U := subst_rec d U0 n) (s := s0).
    + exact (IH e0 t0 U0 Htu f n Hsub wff Hskip).
    + exact (convertible_convertible_subst d d U0 V0 n (refl_convertible d) Hconv).
    + exact (IH e0 V0 (sort_term s0) HV f n Hsub wff Hskip).
Qed.

(** Type-level substitution lemma. *)
Theorem substitution_t :
  forall e t u U,
  has_type (t :: e) u U ->
  forall d, has_type e d t -> well_formed e ->
  has_type e (subst d u) (subst d U).
Proof.
  intros e t u U Hu d Hd wfe.
  unfold subst.
  apply has_type_substitute_weakening_t with e t (t :: e);
    auto with coc core arith datatypes.
Qed.

(** Inversion of product typing through conversions (Type-level). *)
Lemma inversion_has_type_prod_t :
  forall e T U S, has_type e (terms.prod T U) S ->
  { s1 & { s2 &
    (has_type e T (sort_term s1) *
     has_type (T :: e) U (sort_term s2) *
     convertible (sort_term s2) S)%type }}.
Proof.
  intros e T U.
  fix IH 2.
  intros S H.
  inversion H; subst.
  - exists s1, s2. exact (H3, H5, refl_convertible _).
  - destruct (IH _ H0) as [s1' [s2' [[HD HU'] Hconv']]].
    exists s1', s2'.
    exact (HD, HU', trans_convertible_convertible _ _ _ Hconv' H1).
Qed.

(** Inversion of lambda typing through conversions (Type-level). *)
Lemma invert_lam_t :
  forall e T0 M U, has_type e (terms.lam T0 M) U ->
  { s1 & { Ubody & { s2 &
    (has_type e T0 (sort_term s1) *
     has_type (T0 :: e) Ubody (sort_term s2) *
     has_type (T0 :: e) M Ubody *
     convertible (terms.prod T0 Ubody) U)%type }}}.
Proof.
  intros e T0 M.
  fix IH 2.
  intros U H.
  inversion H; subst.
  - exists s1, U0, s2. exact (H2, H4, H6, refl_convertible _).
  - destruct (IH _ H0) as [s1' [Ub [s2' [[[HD HU'] HM'] Hconv']]]].
    exists s1', Ub, s2'.
    exact (HD, HU', HM', trans_convertible_convertible _ _ _ Hconv' H1).
Qed.

(** Type case: every well-typed term's type is either [sort_term kind] or has a sort.
    Type-level version of [type_case]. *)
Lemma type_case_t :
  forall e t T, has_type e t T -> well_formed e ->
  { s : sort & has_type e T (sort_term s) } + { T = sort_term kind }.
Proof.
  fix IH 4.
  intros e t T H wfe.
  destruct H.
  - (* type_prop *) right. reflexivity.
  - (* type_set *) right. reflexivity.
  - (* type_var *)
    left.
    destruct (nth_error e v) as [u|] eqn:Hnth.
    + destruct (wf_nth_sort_t v e w u Hnth) as [s0 Hs0].
      exists s0.
      assert (Ht : t = lift (S v) u).
      { destruct i as [x Heq Hnth']. rewrite Hnth in Hnth'.
        injection Hnth' as <-. exact Heq. }
      subst t.
      change (sort_term s0) with (lift (S v) (sort_term s0)).
      exact (weakening_at_t (S v) e (skipn (S v) e) eq_refl
               (nth_error_S_le _ e v u Hnth) u (sort_term s0) Hs0 w).
    + exfalso. destruct i as [x _ Hnth']. rewrite Hnth in Hnth'. discriminate.
  - (* type_abs *)
    left. exists s2. exact (type_prod e T s1 H U s2 H0).
  - (* type_app *)
    left.
    assert (wfe2 : well_formed e) by exact wfe.
    destruct (IH _ _ _ H0 wfe2) as [[s0 Hs0] | Heq]; [| discriminate].
    destruct (inversion_has_type_prod_t _ _ _ _ Hs0) as [s1' [s2' [[HD' HU'] _]]].
    exists s2'.
    change (sort_term s2') with (subst v (sort_term s2')).
    exact (substitution_t e V Ur (sort_term s2') HU' v H wfe).
  - (* type_prod *)
    destruct s2.
    + right. reflexivity.
    + left. exists kind.
      exact (type_prop e (has_type_t_well_formed_t e T (sort_term s1) H)).
    + left. exists kind.
      exact (type_set e (has_type_t_well_formed_t e T (sort_term s1) H)).
  - (* type_conv *)
    left. exists s. exact H0.
Qed.

(** Subject reduction (Type-level): typing is preserved under one-step reduction. *)
Lemma subject_reduction_t :
  forall e t T, has_type e t T ->
  forall v, reduces_once t v -> well_formed e ->
  has_type e v T.
Proof.
  fix IH 4.
  intros e t T H v Hred wfe.
  destruct H.
  - (* type_prop *) exfalso; inversion Hred.
  - (* type_set *) exfalso; inversion Hred.
  - (* type_var *) exfalso; inversion Hred.
  - (* type_abs: lam T M -> v *)
    inversion Hred; subst.
    + (* abs_reduces_left: domain T reduced to M' *)
      assert (HD' : has_type e M' (sort_term s1)) by exact (IH _ _ _ H _ H5 wfe).
      assert (wfe' : well_formed (M' :: e)) by exact (wf_var e M' s1 HD').
      apply type_conv with (U := terms.prod M' U) (s := s2).
      * apply type_abs with s1 s2.
        -- exact HD'.
        -- exact (has_type_reduces_environment_t _ _ _ H0 _
                    (red_env_hd e T M' H5) wfe').
        -- exact (has_type_reduces_environment_t _ _ _ H1 _
                    (red_env_hd e T M' H5) wfe').
      * apply convertible_convertible_product.
        -- apply sym_convertible. apply trans_conv_red with T.
           ++ exact (refl_convertible T).
           ++ exact H5.
        -- exact (refl_convertible U).
      * exact (type_prod e T s1 H U s2 H0).
    + (* abs_reduces_right: body M reduced to M' *)
      assert (HM' : has_type (T :: e) M' U).
      { exact (IH _ _ _ H1 _ H5 (wf_var e T s1 H)). }
      exact (type_abs e T s1 H M' U s2 H0 HM').
  - (* type_app: app u v0 -> w *)
    inversion Hred; subst.
    + (* beta: app (lam T M) v0 -> subst v0 M *)
      destruct (invert_lam_t _ _ _ _ H0) as [s1 [Ubody [s2 [[[HDom HUsort] HMbody] Hconv_prod]]]].
      assert (Hconv_dom : convertible T V) by
        exact (inversion_convertible_product_left _ _ _ _ Hconv_prod).
      assert (Hconv_cod : convertible Ubody Ur) by
        exact (inversion_convertible_product_right _ _ _ _ Hconv_prod).
      assert (Harg : has_type e v0 T).
      { apply type_conv with (U := V) (s := s1).
        - exact H.
        - exact (sym_convertible _ _ Hconv_dom).
        - exact HDom. }
      assert (Hsub : has_type e (subst v0 M) (subst v0 Ubody)).
      { apply substitution_t with T; auto. }
      destruct (type_case_t _ _ _ H0 wfe) as [[s Hs] | Heq]; [| discriminate].
      destruct (inversion_has_type_prod_t _ _ _ _ Hs) as [s1' [s2' [[_ HUr_sort] _]]].
      assert (HsubUr : has_type e (subst v0 Ur) (sort_term s2')).
      { change (sort_term s2') with (subst v0 (sort_term s2')).
        exact (substitution_t _ V _ _ HUr_sort v0 H wfe). }
      apply type_conv with (U := subst v0 Ubody) (s := s2').
      * exact Hsub.
      * unfold subst. apply convertible_convertible_subst.
        -- exact (refl_convertible v0).
        -- exact Hconv_cod.
      * exact HsubUr.
    + (* app_reduces_left: u reduced to N1 *)
      exact (type_app e v0 V H _ Ur (IH _ _ _ H0 _ H4 wfe)).
    + (* app_reduces_right: v0 reduced to N2 *)
      assert (Hv' : has_type e N2 V) by exact (IH _ _ _ H _ H4 wfe).
      destruct (type_case_t _ _ _ H0 wfe) as [[s Hs] | Heq]; [| discriminate].
      destruct (inversion_has_type_prod_t _ _ _ _ Hs) as [s1' [s2' [[_ HUr_sort] _]]].
      assert (HsubUr : has_type e (subst v0 Ur) (sort_term s2')).
      { change (sort_term s2') with (subst v0 (sort_term s2')).
        exact (substitution_t _ V _ _ HUr_sort v0 H wfe). }
      apply type_conv with (U := subst N2 Ur) (s := s2').
      * exact (type_app e N2 V Hv' u Ur H0).
      * unfold subst. apply convertible_convertible_subst.
        -- apply sym_convertible. apply trans_conv_red with v0.
           ++ exact (refl_convertible v0).
           ++ exact H4.
        -- exact (refl_convertible Ur).
      * exact HsubUr.
  - (* type_prod: prod T U -> v *)
    inversion Hred; subst.
    + (* prod_reduces_left: T reduced to N1 *)
      assert (HD' : has_type e N1 (sort_term s1)) by exact (IH _ _ _ H _ H4 wfe).
      assert (wfe' : well_formed (N1 :: e)) by exact (wf_var e N1 s1 HD').
      apply type_prod with s1.
      * exact HD'.
      * exact (has_type_reduces_environment_t _ _ _ H0 _
                  (red_env_hd e T N1 H4) wfe').
    + (* prod_reduces_right: U reduced to N2 *)
      assert (HU' : has_type (T :: e) N2 (sort_term s2)).
      { exact (IH _ _ _ H0 _ H4 (wf_var e T s1 H)). }
      exact (type_prod e T s1 H N2 s2 HU').
  - (* type_conv *)
    apply type_conv with U s; auto.
    exact (IH _ _ _ H _ Hred wfe).
Qed.
