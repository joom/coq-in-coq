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
From Extraction Require Import simulation_facts.
From Extraction Require Import derivation_independence.
From Extraction Require Import substitution_simulation.


(** [dyn_token] is closed, so type-substitution leaves it fixed. *)
Lemma term_tsubst_dyn_token : forall AA k, infrastructure.term_tsubst AA k dyn_token = dyn_token.
Proof.
  intros. Transparent dyn_token. unfold dyn_token, dyn_fun. cbn [infrastructure.term_tsubst].
  reflexivity. Opaque dyn_token.
Qed.

(** Type-substituting a [coerce] simulates type-substituting its scrutinee. *)
Lemma coerce_term_tsubst_sim_l : forall s t A B AA k,
  simulation.sim_star (infrastructure.term_tsubst AA k s) t ->
  simulation.sim_star (infrastructure.term_tsubst AA k (coerce s A B)) t.
Proof.
  intros s t A B AA k H. unfold coerce.
  destruct (syntax.typ_eq_dec A B).
  - cbn [infrastructure.term_tsubst]. exact H.
  - destruct (infrastructure.compat_dec A B);
    cbn [infrastructure.term_tsubst].
    + eapply simulation.sim_star_trans;
        [ apply simulation.sim_star_step; apply simulation.sim_left_sc;
          apply simulation.sim_refl |].
      exact H.
    + eapply simulation.sim_star_trans;
        [ apply simulation.sim_star_step; apply simulation.sim_blame |].
      exact H.
Qed.

(** Type-substitution is invisible to [sim_star] on extractions (it only touches type annotations). *)
(** Type-substitution is invisible to [sim_star] on extractions (it only touches type
    annotations, which every [sim_star] congruence ignores). *)
Lemma term_tsubst_extract_sim : forall e u U (H: has_type e u U) AA k,
  simulation.sim_star (infrastructure.term_tsubst AA k (extract e u U H))
    (extract e u U H).
Proof.
  fix IH 4. intros e u U H AA k.
  destruct H as [ e0 w0 | e0 w0
                | e0 w0 v T0 il
                | e0 T0 s1 HT M U s2 HU HM
                | e0 v0 V0 Hv u Ur Hu
                | e0 T0 s1 HT U s2 HU
                | e0 t0 U0 V0 Htu Hconv s0 HV ].
  - cbn [extract]. rewrite term_tsubst_dyn_token. apply simulation.sim_star_refl.
  - cbn [extract]. rewrite term_tsubst_dyn_token. apply simulation.sim_star_refl.
  - (* type_var *)
    cbn [extract].
    destruct (is_large_dec e0 T0) as [Hlarge | Hsmall].
    + apply coerce_self_tsubst_sim. cbn [infrastructure.term_tsubst]. apply simulation.sim_star_refl.
    + destruct il as [u0 Heq0 Hnth0].
      assert (Hnu : is_large (skipn (S v) e0) u0 -> False)
        by (intro Hil; apply Hsmall; rewrite Heq0;
            exact (snd (is_large_item_lift e0 v u0 w0 Hnth0) Hil)).
      pose (snT := sn_of_type e0 (terms.var v) T0
                     (type_var e0 w0 v T0 (existT2 _ _ u0 Heq0 Hnth0))).
      rewrite (extract_lookup_type_eq_extract_typ e0 v u0 T0 Hnth0 Heq0 Hnu w0 snT).
      rewrite coerce_id.
      cbn [infrastructure.term_tsubst]. apply simulation.sim_star_refl.
  - (* type_abs *)
    cbn [extract].
    destruct (is_large_dec e0 T0).
    + cbn [infrastructure.term_tsubst]. apply sim_star_tabs_gen. apply (IH _ _ _ HM).
    + cbn [infrastructure.term_tsubst]. apply sim_star_abs_gen. apply (IH _ _ _ HM).
  - (* type_app *)
    cbn [extract].
    destruct (is_large_dec e0 V0).
    + cbn [infrastructure.term_tsubst].
      apply sim_star_tapp_gen. apply (IH _ _ _ Hu).
    + apply coerce_self_tsubst_sim. cbn [infrastructure.term_tsubst].
      apply sim_star_app; [apply (IH _ _ _ Hu) | apply (IH _ _ _ Hv)].
  - cbn [extract]. rewrite term_tsubst_dyn_token. apply simulation.sim_star_refl.
  - (* type_conv *)
    cbn [extract].
    apply coerce_self_tsubst_sim. apply (IH _ _ _ Htu).
Qed.

(** Above the substitution point (large removed binder), [term_index] is unchanged. *)
(** [term_index] is unchanged for variables above a large substituted binder,
    since removing a large binder does not shift the term namespace's indices. *)
Lemma term_index_substitute_above_large :
  forall g v V (Hv: has_type g v V),
  is_large g V ->
  forall n e f,
  substitute_in_environment v V n e f ->
  well_formed e -> well_formed f -> skipn n f = g ->
  forall v0, n < v0 -> v0 <= length e ->
  term_index e v0 = term_index f (Nat.pred v0).
Proof.
  intros g v V Hv Hlarge_gV n e f Hse.
  induction Hse as [e0 | e0 f0 n' T Hse' IH].
  - intros wfe wff Hskip v0 Hlt Hlen.
    destruct v0 as [| v0']; [lia |]. simpl (Nat.pred (S v0')).
    assert (HlargeV : is_large e0 V)
      by (simpl in Hskip; rewrite Hskip; exact Hlarge_gV).
    rewrite (term_index_succ_large V e0 v0' HlargeV). reflexivity.
  - intros wfe wff Hskip v0 Hlt Hlen.
    destruct v0 as [| v0']; [lia |]. simpl (Nat.pred (S v0')).
    dependent destruction wfe. rename s into sT, h into HT_sort_e.
    pose (wfe0 := has_type_t_well_formed_t _ _ _ HT_sort_e).
    dependent destruction wff. rename s into sT', h into HT_sort_f.
    pose (wff0 := has_type_t_well_formed_t _ _ _ HT_sort_f).
    simpl in Hskip.
    assert (Hlarge_agree : iffT (is_large e0 T) (is_large f0 (terms.subst_rec v T n'))).
    { split.
      - intro Hl. apply (has_type_substitute_weakening g v V (Hv)
                           e0 T (sort_term kind) Hl f0 n' Hse'
                           (wff0) Hskip).
      - intro Hlf. exact (is_large_substitute_inv g v V Hv e0 T sT HT_sort_e f0 n' Hse' wff0 Hskip Hlf). }
    destruct v0' as [| v0'']; [lia |].
    destruct (is_large_dec e0 T) as [Hlarge | Hsmall].
    + rewrite (term_index_succ_large T e0 (S v0'') Hlarge).
      assert (Hlarge_f : is_large f0 (terms.subst_rec v T n')) by (apply (fst Hlarge_agree); exact Hlarge).
      rewrite (term_index_succ_large (terms.subst_rec v T n') f0 v0'' Hlarge_f).
      exact (IH wfe0 wff0 Hskip (S v0'') ltac:(lia) ltac:(simpl in Hlen; lia)).
    + rewrite (term_index_succ_small T e0 (S v0'') Hsmall).
      assert (Hsmall_f : (is_large f0 (terms.subst_rec v T n') -> False))
        by (intro Hl; apply Hsmall; apply (snd Hlarge_agree); exact Hl).
      rewrite (term_index_succ_small (terms.subst_rec v T n') f0 v0'' Hsmall_f).
      f_equal.
      exact (IH wfe0 wff0 Hskip (S v0'') ltac:(lia) ltac:(simpl in Hlen; lia)).
Qed.

(** Type-substitution commutes with extraction up to [sim_star]: generalized (arbitrary depth) core. *)
Lemma extract_tsubst_gen :
  forall n g v V (Hv: has_type g v V) (wfg: well_formed g),
  is_large g V ->
  forall e u Ur (HM: has_type e u Ur)
    f (Hse: substitute_in_environment v V n e f) (wff: well_formed f)
    (Hskip: skipn n f = g),
  forall (Hsub: has_type f (terms.subst_rec v u n) (terms.subst_rec v Ur n)),
    simulation.sim_star (extract e u Ur HM)
      (extract f (terms.subst_rec v u n) (terms.subst_rec v Ur n) Hsub).
Proof.
  fix IH 11.
  intros n g v V Hv wfg Hlarge_gV e u Ur HM.
  dependent destruction HM; intros f Hse wff Hskip Hsub.
  - (* prop *)
    cbn [extract].
    change (terms.subst_rec v (sort_term prop) n) with (sort_term prop) in Hsub |- *.
    change (terms.subst_rec v (sort_term terms.kind) n) with (sort_term terms.kind) in Hsub |- *.
    exact (extract_deriv_indep _ _ _ (type_prop f wff) Hsub).
  - (* set *)
    cbn [extract].
    change (terms.subst_rec v (sort_term set) n) with (sort_term set) in Hsub |- *.
    change (terms.subst_rec v (sort_term terms.kind) n) with (sort_term terms.kind) in Hsub |- *.
    exact (extract_deriv_indep _ _ _ (type_set f wff) Hsub).
  - (* var *)
    rename t into Tv. rename i into il. rename w into wfe_t.
    cbn [extract].
    destruct (is_large_dec e Tv) as [Hlarge_e | Hsmall_e].
    + apply coerce_sim_star_l. apply simulation.sim_star_step.
      apply simulation.sim_blame.
    + assert (HTv_sort : { s & has_type e Tv (sort_term s) })
        by (exact (well_formed_sort_lift v0 e Tv (wfe_t) il)).
      assert (Hsmall_f : (is_large f (terms.subst_rec v Tv n) -> False)).
      { intro Hlf. apply Hsmall_e.
        exact (is_large_substitute_inv_prop g v V Hv e Tv HTv_sort f n Hse wff Hskip Hlf). }
      assert (Hlen_v : v0 < length e)
        by (destruct il as [u0 _ Hnth0]; apply (proj1 (nth_error_Some e v0)); rewrite Hnth0; discriminate).
      destruct (lt_eq_lt_dec n v0) as [[Hlt | Heq] | Hgt].
      * assert (Hvar : terms.subst_rec v (terms.var v0) n = terms.var (Nat.pred v0))
          by (apply subst_ref_gt; lia).
        revert Hsub. rewrite Hvar. intro Hsub.
        eapply simulation.sim_star_trans;
          [| exact (extract_deriv_indep _ _ _
                      (type_var f wff (Nat.pred v0) (terms.subst_rec v Tv n)
                         (item_lift_substitute_above v V n e f Hse v0 Tv Hlt il)) Hsub)].
        cbn [extract].
        destruct (is_large_dec f (terms.subst_rec v Tv n)) as [Habs | _]; [contradiction |].
        destruct il as [u0 Heq0 Hnth0].
        assert (Hnu_e : is_large (skipn (S v0) e) u0 -> False)
          by (intro H; apply Hsmall_e; rewrite Heq0;
              exact (snd (is_large_item_lift e v0 u0 wfe_t Hnth0) H)).
        pose (sn_e_v := sn_of_type e (terms.var v0) Tv
                          (type_var e wfe_t v0 Tv (existT2 _ _ u0 Heq0 Hnth0))).
        rewrite (extract_lookup_type_eq_extract_typ e v0 u0 Tv Hnth0 Heq0 Hnu_e wfe_t sn_e_v).
        rewrite coerce_id.
        pose (il_f_raw := item_lift_substitute_above v V n e f Hse v0 Tv Hlt
                            (existT2 _ _ u0 Heq0 Hnth0)).
        destruct il_f_raw as [u0_f Heq0_f Hnth0_f].
        assert (Hnu_f : is_large (skipn (S (Nat.pred v0)) f) u0_f -> False)
          by (intro H; apply Hsmall_f; rewrite Heq0_f;
              exact (snd (is_large_item_lift f (Nat.pred v0) u0_f wff Hnth0_f) H)).
        pose (sn_f_v := sn_of_type f (terms.var (Nat.pred v0)) (terms.subst_rec v Tv n)
                          (type_var f wff (Nat.pred v0) _ (existT2 _ _ u0_f Heq0_f Hnth0_f))).
        eapply simulation.sim_star_trans;
          [| apply coerce_sim_star_id;
             rewrite (extract_lookup_type_eq_extract_typ f (Nat.pred v0) u0_f
                        (terms.subst_rec v Tv n) Hnth0_f Heq0_f Hnu_f wff sn_f_v);
             apply extract_typ_pi].
        rewrite (term_index_substitute_above_large g v V Hv Hlarge_gV n e f Hse
                   wfe_t wff Hskip v0 Hlt ltac:(lia)).
        apply simulation.sim_star_refl.
      * subst v0. exfalso. apply Hsmall_e.
        destruct il as [u0 Heq0 Hnth0].
        rewrite (nth_substitute_eq v V n e f Hse) in Hnth0. injection Hnth0 as Hu0. subst u0.
        rewrite Heq0.
        apply (snd (is_large_item_lift e n V (wfe_t)
                        (nth_substitute_eq v V n e f Hse))).
        rewrite (skipn_succ_substitute v V n e f Hse). rewrite Hskip. exact Hlarge_gV.
      * assert (Hvar : terms.subst_rec v (terms.var v0) n = terms.var v0)
          by (apply subst_ref_lt; lia).
        revert Hsub. rewrite Hvar. intro Hsub.
        eapply simulation.sim_star_trans;
          [| exact (extract_deriv_indep _ _ _
                      (type_var f wff v0 (terms.subst_rec v Tv n)
                         (item_lift_substitute_below v V n e f Hse v0 Tv Hgt il)) Hsub)].
        cbn [extract].
        destruct (is_large_dec f (terms.subst_rec v Tv n)) as [Habs | _]; [contradiction |].
        destruct il as [u0 Heq0 Hnth0].
        assert (Hnu_e : is_large (skipn (S v0) e) u0 -> False)
          by (intro H; apply Hsmall_e; rewrite Heq0;
              exact (snd (is_large_item_lift e v0 u0 wfe_t Hnth0) H)).
        pose (sn_e_v2 := sn_of_type e (terms.var v0) Tv
                           (type_var e wfe_t v0 Tv (existT2 _ _ u0 Heq0 Hnth0))).
        rewrite (extract_lookup_type_eq_extract_typ e v0 u0 Tv Hnth0 Heq0 Hnu_e wfe_t sn_e_v2).
        rewrite coerce_id.
        pose (il_f_raw := item_lift_substitute_below v V n e f Hse v0 Tv Hgt
                            (existT2 _ _ u0 Heq0 Hnth0)).
        destruct il_f_raw as [u0_f Heq0_f Hnth0_f].
        assert (Hnu_f : is_large (skipn (S v0) f) u0_f -> False)
          by (intro H; apply Hsmall_f; rewrite Heq0_f;
              exact (snd (is_large_item_lift f v0 u0_f wff Hnth0_f) H)).
        pose (sn_f_v2 := sn_of_type f (terms.var v0) (terms.subst_rec v Tv n)
                           (type_var f wff v0 _ (existT2 _ _ u0_f Heq0_f Hnth0_f))).
        eapply simulation.sim_star_trans;
          [| apply coerce_sim_star_id;
             rewrite (extract_lookup_type_eq_extract_typ f v0 u0_f
                        (terms.subst_rec v Tv n) Hnth0_f Heq0_f Hnu_f wff sn_f_v2);
             apply extract_typ_pi].
        rewrite (term_index_substitute_below g v V Hv wfg n e f Hse wfe_t wff Hskip v0 Hgt).
        apply simulation.sim_star_refl.
  - (* abs *)
    change (terms.subst_rec v (terms.lam T M) n) with
      (terms.lam (terms.subst_rec v T n) (terms.subst_rec v M (S n))) in Hsub |- *.
    change (terms.subst_rec v (terms.prod T U) n) with
      (terms.prod (terms.subst_rec v T n) (terms.subst_rec v U (S n))) in Hsub |- *.
    pose (HT_sub := has_type_substitute_weakening_t g v V Hv e T (sort_term s1) HM1 f n Hse wff Hskip).
    pose (wff' := wf_var f (terms.subst_rec v T n) s1 HT_sub).
    pose (Hse' := sub_succ v V e f n T Hse).
    pose (HM_sub := has_type_substitute_weakening_t g v V Hv (T :: e) M U HM3
                       (terms.subst_rec v T n :: f) (S n) Hse' wff' Hskip).
    pose (HU_sub := has_type_substitute_weakening_t g v V Hv (T :: e) U (sort_term s2) HM2
                       (terms.subst_rec v T n :: f) (S n) Hse' wff' Hskip).
    eapply simulation.sim_star_trans;
      [| exact (extract_deriv_indep _ _ _
                  (type_abs f (terms.subst_rec v T n) s1 HT_sub
                     (terms.subst_rec v M (S n)) (terms.subst_rec v U (S n)) s2 HU_sub HM_sub) Hsub)].
    cbn [extract].
    destruct (is_large_dec e T) as [Hlarge_e | Hsmall_e];
      destruct (is_large_dec f (terms.subst_rec v T n)) as [Hlarge_f | Hsmall_f].
    + apply sim_star_tabs_gen.
      exact (IH (S n) g v V Hv wfg Hlarge_gV (T :: e) M U HM3
               (terms.subst_rec v T n :: f) Hse' wff' Hskip HM_sub).
    + exfalso. apply Hsmall_f.
      pose proof (is_large_sort_eq e T s1 HM1 Hlarge_e) as Heq. subst s1.
      exact (HT_sub).
    + exfalso. apply Hsmall_e.
      exact (is_large_substitute_inv g v V Hv e T s1 HM1 f n Hse wff Hskip Hlarge_f).
    + apply sim_star_abs_gen.
      exact (IH (S n) g v V Hv wfg Hlarge_gV (T :: e) M U HM3
               (terms.subst_rec v T n :: f) Hse' wff' Hskip HM_sub).
  - (* app *)
    change (terms.subst_rec v (terms.app u v0) n) with
      (terms.app (terms.subst_rec v u n) (terms.subst_rec v v0 n)) in Hsub |- *.
    pose (Hv0_sub := has_type_substitute_weakening_t g v V Hv e v0 V0 HM1 f n Hse wff Hskip).
    pose (Hu_sub := has_type_substitute_weakening_t g v V Hv e u (terms.prod V0 Ur) HM2 f n Hse wff Hskip).
    pose (Happ := type_app f (terms.subst_rec v v0 n) (terms.subst_rec v V0 n) Hv0_sub
                    (terms.subst_rec v u n) (terms.subst_rec v Ur (S n)) Hu_sub).
    eapply simulation.sim_star_trans;
      [| apply (extract_deriv_indep_conv _ _ _ _ Happ Hsub);
         rewrite <- distribute_subst; apply refl_convertible].
    unfold Happ. cbn [extract].
    destruct (is_large_dec e V0) as [Hlarge_e | Hsmall_e];
      destruct (is_large_dec f (terms.subst_rec v V0 n)) as [Hlarge_f | Hsmall_f].
    + (* large/large: raw tapp on both sides (no coerce) *)
      apply sim_star_tapp_gen.
      exact (IH n g v V Hv wfg Hlarge_gV e u (terms.prod V0 Ur) HM2 f Hse wff Hskip Hu_sub).
    + exfalso. apply Hsmall_f.
      exact (has_type_substitute_weakening g v V (Hv)
               e V0 (sort_term kind) Hlarge_e f n Hse (wff) Hskip).
    + exfalso. apply Hsmall_e. unfold is_large.
      pose proof (HM2) as Hu_prop.
      destruct (type_case _ _ _ Hu_prop) as [[su Hsu] | Habsurd]; [| discriminate].
      apply (inversion_has_type_prod _ _ _ _ _ Hsu). intros s1 s2 HV0s _ _.
      pose proof (has_type_substitute_weakening g v V (Hv)
                    e V0 (sort_term s1) HV0s f n Hse (wff) Hskip) as HV0f.
      change (terms.subst_rec v (sort_term s1) n) with (sort_term s1) in HV0f.
      pose proof (has_type_unique_sort f (terms.subst_rec v V0 n) (sort_term s1)
                    HV0f (sort_term kind) Hlarge_f) as Hconv.
      apply confluence.convertible_sort in Hconv. subst s1. exact HV0s.
    + (* small/small: compat closes f-side coerce *)
      apply coerce_sim_star_l.
      eapply simulation.sim_star_trans.
      * apply sim_star_app;
          [exact (IH n g v V Hv wfg Hlarge_gV e u (terms.prod V0 Ur) HM2 f Hse wff Hskip Hu_sub)
          |exact (IH n g v V Hv wfg Hlarge_gV e v0 V0 HM1 f Hse wff Hskip Hv0_sub)].
      * apply sim_star_self_coerce_compat.
        destruct (type_case f (terms.subst_rec v u n)
                    (terms.prod (terms.subst_rec v V0 n) (terms.subst_rec v Ur (S n))) Hu_sub)
          as [[su_f Hsu_f] | Habsurd_f]; [| discriminate Habsurd_f].
        apply (inversion_has_type_prod _ f (terms.subst_rec v V0 n)
                 (terms.subst_rec v Ur (S n)) (sort_term su_f) Hsu_f).
        intros s1f s2f _ HUr_sub _.
        exact (extract_typ_coerce_compat_small f (terms.subst_rec v V0 n)
                 (terms.subst_rec v v0 n) Hv0_sub Hsmall_f
                 (terms.subst_rec v Ur (S n)) s2f HUr_sub _ _).
  - (* prod *)
    cbn [extract].
    change (terms.subst_rec v (terms.prod T U) n) with
      (terms.prod (terms.subst_rec v T n) (terms.subst_rec v U (S n))) in Hsub |- *.
    change (terms.subst_rec v (sort_term s2) n) with (sort_term s2) in Hsub |- *.
    exact (extract_deriv_indep _ _ _
             (type_prod f (terms.subst_rec v T n) s1
                (has_type_substitute_weakening_t g v V Hv e T (sort_term s1) HM1 f n Hse wff Hskip)
                (terms.subst_rec v U (S n)) s2
                (has_type_substitute_weakening_t g v V Hv (T :: e) U (sort_term s2) HM2
                   (terms.subst_rec v T n :: f) (S n) (sub_succ v V e f n T Hse)
                   (wf_var f (terms.subst_rec v T n) s1
                      (has_type_substitute_weakening_t g v V Hv e T (sort_term s1) HM1 f n Hse wff Hskip))
                   Hskip))
             Hsub).
  - (* conv *)
    cbn [extract].
    pose (Hsub_U := has_type_substitute_weakening_t g v V Hv e t U HM1 f n Hse wff Hskip).
    eapply simulation.sim_star_trans.
    + apply coerce_sim_star_l.
      exact (IH n g v V Hv wfg Hlarge_gV e t U HM1 f Hse wff Hskip Hsub_U).
    + apply (extract_deriv_indep_conv _ _ _ _ Hsub_U Hsub).
      apply convertible_convertible_subst; [apply refl_convertible | exact c].
Qed.

(** Type-substitution commutes with extraction up to [sim_star] when the substituted variable is type-level (large). *)
Lemma extract_tsubst_sim : forall e V u Ur (HM: has_type (V :: e) u Ur)
  v (Hv: has_type e v V) (wfe: well_formed e),
  is_large e V ->
  forall (Hsub: has_type e (terms.subst v u) (terms.subst v Ur)),
  simulation.sim_star
    (infrastructure.term_tsubst
       (extract_typ e v (strong_normalization e v V (Hv))) 0
       (extract (V :: e) u Ur HM))
    (extract e (terms.subst v u) (terms.subst v Ur) Hsub).
Proof.
  intros e V u Ur HM v Hv wfe Hlarge Hsub.
  unfold terms.subst in *.
  eapply simulation.sim_star_trans.
  - apply term_tsubst_extract_sim.
  - exact (extract_tsubst_gen 0 e v V Hv wfe Hlarge (V :: e) u Ur HM e
             (sub_zero v V e) wfe eq_refl Hsub).
Qed.

(** One-step simulation for [extract]: a source reduction step is simulated
    by [sim_star] of the typed extractions. *)
Theorem extract_reduces_once : forall e t T (H: has_type e t T)
  (w: well_formed e) v (Hred: reduces_once t v),
  simulation.sim_star (extract e t T H)
    (extract e v T (subject_reduction_t e t T H v Hred w)).
Proof.
  fix IH 4.
  intros e t T H w v Hred.
  destruct H as [ e0 w0 | e0 w0 | e0 w0 v0 T0 il
                | e0 T0 s1 HT M U s2 HU HM | e0 v0 V0 Hv u Ur Hu
                | e0 T0 s1 HT U0 s2 HU | e0 t0 U0 V0 Htu Hconv s0 HV ].
  - (* type_prop: sort prop can't reduce *) exfalso; inversion Hred.
  - (* type_set: sort set can't reduce *) exfalso; inversion Hred.
  - (* type_var: var can't reduce *) exfalso; inversion Hred.
  - (* type_abs: lam T0 M : prod T0 U *)
    inversion Hred; subst.
    + (* abs_reduces_left: T0 -> M', lam M' M *)
      rename H2 into Hred_T.
      pose (HT' := subject_reduction_t _ _ _ HT _ Hred_T w).
      pose (wfe' := wf_var e0 M' s1 HT').
      pose (HU' := has_type_reduces_environment_t _ _ _ HU _
                     (red_env_hd e0 T0 M' Hred_T) wfe').
      pose (HM' := has_type_reduces_environment_t _ _ _ HM _
                     (red_env_hd e0 T0 M' Hred_T) wfe').
      pose (H'lam := type_abs e0 M' s1 HT' M U s2 HU' HM').
      pose (Hsrt := subject_reduction_t e0 (lam T0 M) (prod T0 U)
              (type_abs e0 T0 s1 HT M U s2 HU HM) (lam M' M) Hred w).
      eapply simulation.sim_star_trans;
        [| apply (extract_deriv_indep_conv _ _ _ _ H'lam Hsrt);
           apply convertible_convertible_product;
             [ exact (one_step_convertible_expansion _ _ Hred_T)
             | apply refl_convertible ] ].
      subst H'lam HM' HU' wfe' HT' Hsrt. cbn [extract].
      assert (Hlarge_iff : iffT (is_large e0 T0) (is_large e0 M'))
        by (apply is_large_iff with (1 := HT);
            exact Hred_T).
      assert (Hkind_eq : forall sn1 sn2, extract_kind T0 sn1 = extract_kind M' sn2)
        by (intros; exact (extract_kind_stable _ _ _ _ Hred_T)).
      assert (Htyp_eq : forall sn1 sn2, extract_typ e0 T0 sn1 = extract_typ e0 M' sn2).
      { intros. unfold extract_typ.
        rewrite (nf_respects_conv _ _ sn1 sn2
          (sym_convertible _ _ (one_step_convertible_expansion _ _ Hred_T))).
        reflexivity. }
      destruct (is_large_dec e0 T0); destruct (is_large_dec e0 M');
        try (iffT_contra Hlarge_iff).
      * erewrite Hkind_eq. apply sim_star_tabs.
        apply (extract_ctx_swap nil T0 M' e0
                 Hred_T
                 ((wf_var e0 T0 s1 HT))
                 (wf_var e0 M' s1 (subject_reduction_t _ _ _ HT _ Hred_T w))).
      * erewrite Htyp_eq. apply sim_star_abs.
        apply (extract_ctx_swap nil T0 M' e0
                 Hred_T
                 ((wf_var e0 T0 s1 HT))
                 (wf_var e0 M' s1 (subject_reduction_t _ _ _ HT _ Hred_T w))).
    + (* abs_reduces_right: M -> M', lam T0 M' *)
      rename H2 into Hred_body.
      pose (H'body := subject_reduction_t _ _ _ HM _ Hred_body (wf_var e0 T0 s1 HT)).
      pose (H'lam := type_abs e0 T0 s1 HT M' U s2 HU H'body).
      eapply simulation.sim_star_trans; [| apply (extract_deriv_indep _ _ _ H'lam)].
      subst H'lam H'body. cbn [extract].
      destruct (is_large_dec e0 T0).
      * apply sim_star_tabs. exact (IH _ _ _ HM (wf_var e0 T0 s1 HT) _ Hred_body).
      * apply sim_star_abs. exact (IH _ _ _ HM (wf_var e0 T0 s1 HT) _ Hred_body).
  - (* type_app: app u v0 : subst v0 Ur *)
    inversion Hred; subst.
    + (* beta: app (lam T M) v0 -> subst v0 M *)
      destruct (invert_lam_t _ _ _ _ Hu) as [s1 [Ubody [s2 [[[HDom HUsort] HMbody] Hconv_prod]]]].
      (* HDom : has_type e0 T (sort_term s1)
         HUsort : has_type (T::e0) Ubody (sort_term s2)
         HMbody : has_type (T::e0) M Ubody
         Hconv_prod : convertible (prod T Ubody) (prod V0 Ur) *)
      pose (Hu_abs := type_abs e0 T s1 HDom M Ubody s2 HUsort HMbody).
      assert (Hconv_VT : convertible V0 T)
        by (apply sym_convertible; exact (inversion_convertible_product_left _ _ _ _ Hconv_prod)).
      assert (Hv_T : has_type e0 v0 T)
        by exact (type_conv e0 v0 V0 T Hv Hconv_VT s1 HDom).
      (* Bridge from original derivation (Hu) to our known type_abs derivation *)
      pose (Happ_known := type_app e0 v0 T Hv_T (terms.lam T M) Ubody Hu_abs).
      eapply simulation.sim_star_trans.
      { (* LHS: original app derivation → known app derivation *)
        apply (extract_deriv_indep_conv _ _ _ _
                 (type_app e0 v0 V0 Hv (terms.lam T M) Ur Hu) Happ_known).
        apply convertible_convertible_subst;
          [apply refl_convertible
          | apply sym_convertible; exact (inversion_convertible_product_right _ _ _ _ Hconv_prod)]. }
      subst Happ_known Hu_abs. cbn [extract].
      set (Hsrt := subject_reduction_t e0 (terms.app (terms.lam T M) v0)
             (terms.subst v0 Ur) (type_app e0 v0 V0 Hv (terms.lam T M) Ur Hu)
             (terms.subst v0 M) Hred w).
      assert (Hv_T2 : has_type e0 v0 T)
        by exact (type_conv e0 v0 V0 T Hv Hconv_VT s1 HDom).
      pose (Hsub_body := substitution_t _ _ _ _ HMbody _ Hv_T2 w).
      assert (Hconv_sub : convertible (terms.subst v0 Ubody) (terms.subst v0 Ur))
        by (apply convertible_convertible_subst; [apply refl_convertible | exact (inversion_convertible_product_right _ _ _ _ Hconv_prod)]).
      destruct (is_large_dec e0 T).
      * (* large domain: LHS is a target type-beta redex [tapp (tabs …) …] *)
        eapply simulation.sim_star_trans.
        -- apply simulation.sim_star_step. apply simulation.sim_tbeta.
        -- eapply simulation.sim_star_trans;
             [apply extract_tsubst_sim; assumption |].
           exact (extract_deriv_indep_conv _ _ _ _ Hsub_body Hsrt Hconv_sub).
      * apply coerce_sim_star_l.
        eapply simulation.sim_star_trans.
        -- apply simulation.sim_star_step. apply simulation.sim_beta.
        -- eapply simulation.sim_star_trans;
             [apply extract_subst_sim; assumption |].
           exact (extract_deriv_indep_conv _ _ _ _ Hsub_body Hsrt Hconv_sub).
      (* SN witnesses deferred by extract_typ/extract_kind calls *)
      Unshelve. all: try (eapply strong_normalization; eassumption).
    + (* app_reduces_left: u -> N1 *)
      rename H2 into Hred_u.
      pose (Hu' := subject_reduction_t _ _ _ Hu _ Hred_u w).
      pose (H'app := type_app e0 v0 V0 Hv N1 Ur Hu').
      eapply simulation.sim_star_trans; [| apply (extract_deriv_indep _ _ _ H'app)].
      subst H'app Hu'. cbn [extract].
      destruct (is_large_dec e0 V0).
      * apply sim_star_tapp_gen. exact (IH _ _ _ Hu w _ Hred_u).
      * apply (coerce_sim_star_both_conv _ _ _ _ _ _
                 (extract_typ_pi (V0 :: e0) Ur _ _)
                 (extract_typ_pi e0 (terms.subst v0 Ur) _ _)).
        apply sim_star_app_l. exact (IH _ _ _ Hu w _ Hred_u).
    + (* app_reduces_right: v0 -> N2 *)
      rename H2 into Hred_v.
      pose (Hv' := subject_reduction_t _ _ _ Hv _ Hred_v w).
      pose (H'app := type_app e0 N2 V0 Hv' u Ur Hu).
      assert (Hconv_sub : convertible (subst N2 Ur) (subst v0 Ur)).
      { unfold subst. apply convertible_convertible_subst.
        - apply one_step_convertible_expansion.
          exact Hred_v.
        - apply refl_convertible. }
      eapply simulation.sim_star_trans;
        [| apply (extract_deriv_indep_conv _ _ _ _ H'app _ Hconv_sub)].
      subst H'app Hv'. cbn [extract].
      assert (Heq_typ : extract_typ e0 v0
                (strong_normalization e0 v0 V0 (Hv))
              = extract_typ e0 N2
                (strong_normalization e0 N2 V0
                   ((subject_reduction_t e0 v0 V0 Hv N2 Hred_v w)))).
      { unfold extract_typ.
        apply f_equal. apply nf_respects_conv.
        apply sym_convertible. apply one_step_convertible_expansion.
        exact Hred_v. }
      assert (Heq_sub : forall sn1 sn2,
          extract_typ e0 (terms.subst v0 Ur) sn1 = extract_typ e0 (terms.subst N2 Ur) sn2).
      { intros sn1 sn2. unfold extract_typ. apply f_equal. apply nf_respects_conv.
        apply sym_convertible. exact Hconv_sub. }
      destruct (is_large_dec e0 V0).
      * (* raw tapp; same function, type argument ignored by [sim_star_tapp_gen] *)
        apply sim_star_tapp_gen. apply simulation.sim_star_refl.
      * apply (coerce_sim_star_both_conv _ _ _ _ _ _
          (extract_typ_pi (V0::e0) Ur _ _) (Heq_sub _ _)).
        apply sim_star_app_r. exact (IH _ _ _ Hv w _ Hred_v).
  - (* type_prod: prod T0 U0 -> v *)
    inversion Hred; subst.
    + (* prod_reduces_left: T0 -> N1, prod N1 U0 *)
      rename H2 into Hred_T.
      pose (HT' := subject_reduction_t _ _ _ HT _ Hred_T w).
      pose (wfe' := wf_var e0 N1 s1 HT').
      pose (HU' := has_type_reduces_environment_t _ _ _ HU _
                     (red_env_hd e0 T0 N1 Hred_T) wfe').
      pose (H'prod := type_prod e0 N1 s1 HT' U0 s2 HU').
      eapply simulation.sim_star_trans; [| apply (extract_deriv_indep _ _ _ H'prod)].
      subst H'prod HU' wfe' HT'. cbn [extract].
      apply simulation.sim_star_refl.
    + (* prod_reduces_right: U0 -> N2, prod T0 N2 *)
      rename H2 into Hred_U.
      pose (HU' := subject_reduction_t _ _ _ HU _ Hred_U (wf_var e0 T0 s1 HT)).
      pose (H'prod := type_prod e0 T0 s1 HT N2 s2 HU').
      eapply simulation.sim_star_trans; [| apply (extract_deriv_indep _ _ _ H'prod)].
      subst H'prod HU'. cbn [extract].
      apply simulation.sim_star_refl.
  - (* type_conv: coerce (extract ... Htu) ... *)
    cbn [extract].
    pose (Htu' := subject_reduction_t _ _ _ Htu _ Hred w).
    pose (H'conv := type_conv e0 t0 U0 V0 Htu Hconv s0 HV).
    pose (H'result := type_conv e0 v U0 V0 Htu' Hconv s0 HV).
    eapply simulation.sim_star_trans; [| apply (extract_deriv_indep _ _ _ H'result)].
    subst H'result Htu'. cbn [extract].
    apply (coerce_sim_star_both_conv _ _ _ _ _ _
             (extract_typ_pi e0 U0 _ _) (extract_typ_pi e0 V0 _ _)).
    exact (IH _ _ _ Htu w _ Hred).
(* SN witnesses deferred by extract_typ/extract_kind/nf calls throughout *)
Unshelve. all: try (eapply strong_normalization; eassumption).
Qed.

(** Multi-step simulation: source multi-step reduction is simulated by
    [sim_star] of the typed extractions (for any derivation of the reduct). *)
Corollary extract_reduces : forall e t T (H: has_type e t T)
  (w: well_formed e) v (Hred: reduces t v) (Hv: has_type e v T),
  simulation.sim_star (extract e t T H) (extract e v T Hv).
Proof.
  intros e t T H w v Hred. revert H.
  induction Hred as [M | M P N Hstep Hprefix IH]; intros H Hv.
  - apply extract_deriv_indep.
  - set (HP := subject_reduction_theorem e M P Hprefix T H).
    eapply simulation.sim_star_trans.
    + exact (IH H HP).
    + eapply simulation.sim_star_trans.
      * exact (extract_reduces_once e P T HP w N Hstep).
      * apply extract_deriv_indep.
Qed.
