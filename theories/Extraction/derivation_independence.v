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



(** Coercing to the same type is the identity: no cast is emitted. *)
Lemma coerce_id : forall s A, coerce s A A = s.
Proof.
  intros s A. unfold coerce.
  destruct (syntax.typ_eq_dec A A); [reflexivity | congruence].
Qed.

(** Convertible source types yield identical extracted types. *)
Lemma extract_typ_conv : forall e U V snU snV,
  convertible U V -> extract_typ e U snU = extract_typ e V snV.
Proof.
  intros. unfold extract_typ. rewrite (nf_respects_conv _ _ snU snV H). reflexivity.
Qed.

(** [coerce_sim_star_both] with propositional equality of the coerce arguments. *)
Lemma coerce_sim_star_both_conv : forall s t A1 B1 A2 B2,
  A1 = A2 -> B1 = B2 ->
  simulation.sim_star s t ->
  simulation.sim_star (coerce s A1 B1) (coerce t A2 B2).
Proof. intros; subst; apply coerce_sim_star_both; assumption. Qed.

(** Coercing between [extract_typ]s of convertible types is the identity. *)
Lemma coerce_conv_id : forall s e U V snU snV,
  convertible U V ->
  coerce s (extract_typ e U snU) (extract_typ e V snV) = s.
Proof.
  intros. rewrite (extract_typ_conv e U V snU snV H). apply coerce_id.
Qed.

(** [sim_star s (coerce s A B)] when [A = B] (coerce is identity). *)
Lemma coerce_sim_star_id : forall s A B,
  A = B -> simulation.sim_star s (coerce s A B).
Proof. intros; subst; rewrite coerce_id; apply simulation.sim_star_refl. Qed.

(** Strip all [type_conv] from the RIGHT derivation under [sim_star]. *)
Lemma extract_conv_strip_r : forall e t T1 T2
  (H1: has_type e t T1) (H2: has_type e t T2),
  convertible T1 T2 ->
  (forall T2' (H2': has_type e t T2'),
     convertible T1 T2' ->
     match H2' with type_conv _ _ _ _ _ _ _ _ => False | _ => True end ->
     simulation.sim_star (extract e t T1 H1) (extract e t T2' H2')) ->
  simulation.sim_star (extract e t T1 H1) (extract e t T2 H2).
Proof.
  fix strip 6.
  intros e t T1 T2 H1 H2 Hconv Hbase.
  destruct H2 as [ | | | | | | e2 t2 U2 V2 Htu2 Hconv2 s2 HV2 ].
  1-6: apply Hbase; [ exact Hconv | exact I ].
  cbn [extract].
  rewrite (coerce_conv_id _ _ _ _ _ _ Hconv2).
  apply (strip _ _ _ _ H1 Htu2
           (trans_convertible_convertible _ _ _ Hconv (sym_convertible _ _ Hconv2))).
  exact Hbase.
Qed.

(** Derivation independence: any two derivations of the same judgment produce
    [sim_star]-related extractions.  The only source of difference is [type_conv]
    layers (which insert [coerce]), and these are transparent to [sim]. *)
Lemma extract_deriv_indep_conv : forall e t T1 T2
  (H1: has_type e t T1) (H2: has_type e t T2),
  convertible T1 T2 ->
  simulation.sim_star (extract e t T1 H1) (extract e t T2 H2).
Proof.
  fix IH 5.
  intros e t T1 T2 H1 H2 Hconv.
  destruct H1 as [ e0 w0 | e0 w0 | e0 w0 v T0 il
                 | e0 T0 s1 HT M U s2 HU HM | e0 v0 V0 Hv u Ur Hu
                 | e0 T0 s1 HT U0 s2 HU | e0 t0 U0 V0 Htu Hconv1 s0 HV ].
  - (* type_prop *)
    apply extract_conv_strip_r with (1 := Hconv).
    intros T2' H2' Hconv' Hnotconv.
    cbn [extract].
    dependent destruction H2'; try contradiction;
      cbn [extract]; apply simulation.sim_star_refl.
  - (* type_set *)
    apply extract_conv_strip_r with (1 := Hconv).
    intros T2' H2' Hconv' Hnotconv.
    cbn [extract].
    dependent destruction H2'; try contradiction;
      cbn [extract]; apply simulation.sim_star_refl.
  - (* type_var *)
    apply extract_conv_strip_r with (1 := Hconv).
    intros T2' H2' Hconv' Hnotconv.
    cbn [extract].
    dependent destruction H2'; try contradiction.
    (* var/var *)
    cbn [extract].
    assert (HeqT : forall snA snB, extract_typ e T0 snA = extract_typ e t snB).
    { intros snA snB. unfold extract_typ.
      rewrite (nf_respects_conv _ _ snA snB Hconv'). reflexivity. }
    assert (Hlarge_iff : iffT (is_large e T0) (is_large e t)).
    { destruct (well_formed_sort_lift v _ T0 (w0) il) as [sT0 HsT0].
      match goal with
      | w2 : well_formed e, i2 : item_lift t e v |- _ =>
          destruct (well_formed_sort_lift v _ t (w2) i2) as [st Hst]
      end.
      eapply is_large_conv_iff; eassumption. }
    destruct (is_large_dec e T0); destruct (is_large_dec e t);
      try (iffT_contra Hlarge_iff).
    * match goal with
      | |- simulation.sim_star (coerce _ _ (extract_typ _ _ ?s1))
                                       (coerce _ _ (extract_typ _ _ ?s2)) =>
          rewrite (HeqT s1 s2); apply simulation.sim_star_refl
      end.
    * match goal with
      | w2 : well_formed e |- _ =>
          rewrite (extract_lookup_type_pi _ (w0) (w2))
      end.
      match goal with
      | |- simulation.sim_star (coerce _ _ (extract_typ _ _ ?s1))
                                       (coerce _ _ (extract_typ _ _ ?s2)) =>
          rewrite (HeqT s1 s2); apply simulation.sim_star_refl
      end.
  - (* type_abs *)
    apply extract_conv_strip_r with (1 := Hconv).
    intros T2' H2' Hconv' Hnotconv.
    cbn [extract].
    dependent destruction H2'; try contradiction.
    (* abs/abs *)
    assert (Hconv_U : convertible U U0).
    { apply inversion_convertible_product_right in Hconv'. exact Hconv'. }
    cbn [extract].
    destruct (is_large_dec _ T0).
    * match goal with
      | |- simulation.sim_star (syntax.tabs ?K1 _) (syntax.tabs ?K2 _) =>
          replace K2 with K1 by apply extract_kind_pi
      end.
      apply sim_star_tabs.
      match goal with
      | H2body : has_type _ M U0 |- _ => exact (IH _ _ _ _ HM H2body Hconv_U)
      end.
    * match goal with
      | |- simulation.sim_star (syntax.abs ?A1 _) (syntax.abs ?A2 _) =>
          replace A2 with A1 by apply extract_typ_pi
      end.
      apply sim_star_abs.
      match goal with
      | H2body : has_type _ M U0 |- _ => exact (IH _ _ _ _ HM H2body Hconv_U)
      end.
  - (* type_app *)
    apply extract_conv_strip_r with (1 := Hconv).
    intros T2' H2' Hconv' Hnotconv.
    cbn [extract].
    dependent destruction H2'; try contradiction.
    (* app/app *)
    cbn [extract].
    match goal with
    | Hu2 : has_type e u (terms.prod ?V2 ?Ur2),
      Hv2 : has_type e v0 ?V2 |- _ =>
    assert (Hconv_prod : convertible (terms.prod V0 Ur) (terms.prod V2 Ur2))
      by (eapply has_type_unique_sort; [ exact (Hu) | exact (Hu2) ]);
    assert (Hconv_V : convertible V0 V2)
      by (apply inversion_convertible_product_left in Hconv_prod as Hcp; exact Hcp);
    assert (Hconv_Ur : convertible Ur Ur2)
      by (exact (inversion_convertible_product_right _ _ _ _ Hconv_prod));
    assert (Hlarge_iff : iffT (is_large e V0) (is_large e V2))
      by (pose proof (Hu) as Hup;
          pose proof (Hu2) as H2p;
          destruct (type_case _ _ _ Hup) as [[s1' Hs1']|Heq]; [ idtac | discriminate ];
          destruct (type_case _ _ _ H2p) as [[s2' Hs2']|Heq]; [ idtac | discriminate ];
          apply (inversion_has_type_prod _ _ _ _ _ Hs1'); intros sV0 _ HV0 _ _;
          apply (inversion_has_type_prod _ _ _ _ _ Hs2'); intros sV _ HV _ _;
          eapply is_large_conv_iff; eassumption);
    assert (HUrT : sigT (fun s => has_type (V0 :: e) Ur (sort_term s)))
      by (destruct (type_case _ _ _ (Hu)) as [[s1' Hs1']|Heq]; [ idtac | discriminate ];
          exact (inversion_has_type_prod _ _ _ _ _ Hs1'
                   (fun _ s2 _ HU _ => existT _ s2 HU)));
    assert (HUr2T : sigT (fun s => has_type (V2 :: e) Ur2 (sort_term s)))
      by (destruct (type_case _ _ _ (Hu2)) as [[s2' Hs2']|Heq]; [ idtac | discriminate ];
          exact (inversion_has_type_prod _ _ _ _ _ Hs2'
                   (fun _ s2 _ HU _ => existT _ s2 HU)))
    end.
    match goal with
    | Hconv_V : convertible V0 ?V2 |- _ =>
    destruct (is_large_dec e V0); destruct (is_large_dec e V2);
      try (iffT_contra Hlarge_iff)
    end.
    + (* large: the raw [tapp] (no coerce); functions relate by IH *)
      apply sim_star_tapp_gen.
      exact (IH _ _ _ _ Hu _ Hconv_prod).
    + apply coerce_sim_star_both_conv.
      * change (V0 :: e) with (nil ++ V0 :: e).
        exact (extract_typ_ctx_conv _ _ Hconv_V _ _ Hconv_Ur nil e _ _ _ _ (projT2 HUrT) (projT2 HUr2T)).
      * apply extract_typ_conv.
        apply convertible_convertible_subst;
          [apply refl_convertible | exact Hconv_Ur].
      * apply sim_star_app.
        -- exact (IH _ _ _ _ Hu _ Hconv_prod).
        -- exact (IH _ _ _ _ Hv _ Hconv_V).
  - (* type_prod *)
    apply extract_conv_strip_r with (1 := Hconv).
    intros T2' H2' Hconv' Hnotconv.
    cbn [extract].
    dependent destruction H2'; try contradiction;
      cbn [extract]; apply simulation.sim_star_refl.
  - (* type_conv *)
    cbn [extract].
    apply coerce_sim_star_l.
    exact (IH _ _ _ _ Htu H2 (trans_convertible_convertible _ _ _ Hconv1 Hconv)).
Qed.

(** Two derivations of the same judgment have [sim_star]-equal extractions (casts aside). *)
Lemma extract_deriv_indep : forall e t T (H1 H2: has_type e t T),
  simulation.sim_star (extract e t T H1) (extract e t T H2).
Proof.
  intros. apply extract_deriv_indep_conv. apply refl_convertible.
Qed.

(** Context swap: [extract] is invariant (up to [sim_star]) when a context
    binder reduces. *)
Lemma extract_conv_strip_r_ctx : forall e1 e2 t T1 T2
  (H1: has_type e1 t T1) (H2: has_type e2 t T2),
  convertible T1 T2 ->
  (forall T2' (H2': has_type e2 t T2'),
     convertible T1 T2' ->
     match H2' with type_conv _ _ _ _ _ _ _ _ => False | _ => True end ->
     simulation.sim_star (extract e1 t T1 H1) (extract e2 t T2' H2')) ->
  simulation.sim_star (extract e1 t T1 H1) (extract e2 t T2 H2).
Proof.
  fix strip 7.
  intros e1 e2 t T1 T2 H1 H2 Hconv Hbase.
  destruct H2 as [ | | | | | | e2' t2 U2 V2 Htu2 Hconv2 s2 HV2 ].
  1-6: apply Hbase; [ exact Hconv | exact I ].
  cbn [extract].
  rewrite (coerce_conv_id _ _ _ _ _ _ Hconv2).
  apply (strip _ _ _ _ _ H1 Htu2
           (trans_convertible_convertible _ _ _ Hconv (sym_convertible _ _ Hconv2))).
  exact Hbase.
Qed.

(** Term extraction is invariant under swapping a context binder for a reduct. *)
Lemma extract_ctx_swap : forall D T T' e,
  reduces_once T T' -> well_formed (D ++ T :: e) ->
  well_formed (D ++ T' :: e) ->
  forall t U (H1: has_type (D ++ T :: e) t U) (H2: has_type (D ++ T' :: e) t U),
  simulation.sim_star
    (extract (D ++ T :: e) t U H1)
    (extract (D ++ T' :: e) t U H2).
Proof.
  intros D T T' e Hr. revert D.
  fix IH 6.
  intros D Hwf Hwf' t U H1 H2.
  dependent destruction H1.
  - (* prop *)
    apply (extract_conv_strip_r_ctx _ _ _ _ _ _ H2 (refl_convertible _)).
    intros T2' H2' HconvR HnotconvR.
    dependent destruction H2'; try contradiction.
    apply simulation.sim_star_refl.
  - (* set *)
    apply (extract_conv_strip_r_ctx _ _ _ _ _ _ H2 (refl_convertible _)).
    intros T2' H2' HconvR HnotconvR.
    dependent destruction H2'; try contradiction.
    apply simulation.sim_star_refl.
  - (* var *)
    apply (extract_conv_strip_r_ctx _ _ _ _ _ _ H2 (refl_convertible _)).
    intros T2' H2' HconvR HnotconvR.
    simpl extract.
    (* Construct item_lift in context 2, with possibly different lifted type *)
    destruct i as [u1 Heq1 Hnth1].
    assert (Hil2 : { t2 & (item_lift t2 (D ++ T' :: e) v * convertible t t2)%type }).
    { destruct (Nat.eq_dec v (length D)) as [Hveq|Hvne].
      - subst v. rewrite nth_error_app2 in Hnth1 by lia.
        replace (length D - length D) with 0 in Hnth1 by lia. simpl in Hnth1.
        injection Hnth1 as <-.
        exists (lift (S (length D)) T'). split.
        + exists T'; [reflexivity|].
          rewrite nth_error_app2 by lia.
          replace (length D - length D) with 0 by lia. reflexivity.
        + rewrite Heq1. unfold lift.
          apply sym_convertible. apply convertible_convertible_lift.
          apply one_step_convertible_expansion. exact Hr.
      - destruct (lt_dec v (length D)) as [Hlt|Hge].
        + exists t. split; [| apply refl_convertible].
          exists u1; [exact Heq1|].
          rewrite nth_error_app1 in Hnth1 by lia.
          rewrite nth_error_app1 by (apply nth_error_Some; congruence).
          exact Hnth1.
        + assert (Hgt : v > length D) by lia.
          exists t. split; [| apply refl_convertible].
          exists u1; [exact Heq1|].
          rewrite nth_error_app2 in Hnth1 by lia.
          rewrite nth_error_app2 by lia.
          destruct (v - length D) as [|k] eqn:Hk; [lia|].
          simpl. simpl in Hnth1. exact Hnth1. }
    destruct Hil2 as [t2 [il2 Hconv_t_t2]].
    pose (H2_var := type_var (D ++ T' :: e) Hwf' v t2 il2).
    assert (Hconv_t_T2' : convertible t2 T2').
    { exact (trans_convertible_convertible _ _ _
               (sym_convertible _ _ Hconv_t_t2) HconvR). }
    eapply simulation.sim_star_trans;
      [| exact (extract_deriv_indep_conv _ _ _ _ H2_var H2' Hconv_t_T2')].
    subst H2_var. simpl extract.
    destruct (well_formed_sort_lift _ _ _ Hwf
               (existT2 _ _ u1 Heq1 Hnth1)) as [sv Hsv].
    assert (Hlarge_iff : iffT (is_large (D ++ T :: e) t) (is_large (D ++ T' :: e) t2)).
    { assert (Hswap : iffT (is_large (D ++ T :: e) t) (is_large (D ++ T' :: e) t))
        by (eapply is_large_swap_at;
            [exact (one_step_reduces _ _ Hr) | exact Hwf | exact Hsv]).
      assert (Hsv' : has_type (D ++ T' :: e) t (sort_term sv))
        by (exact (has_type_ctx_red_at _ _ _ _ (one_step_reduces _ _ Hr) _ _ Hsv Hwf)).
      destruct (well_formed_sort_lift _ _ _ (Hwf') il2) as [sv2 Hsv2].
      pose proof (is_large_conv_iff _ _ _ _ _ Hconv_t_t2 Hsv' Hsv2) as Hconv_iff.
      split; [ intro x; exact (fst Hconv_iff (fst Hswap x))
             | intro y; exact (snd Hswap (snd Hconv_iff y)) ]. }
    assert (Hterm_idx : term_index (D ++ T :: e) v = term_index (D ++ T' :: e) v).
    { exact (term_index_swap _ _ _ _ _ (one_step_reduces _ _ Hr) Hwf). }
    destruct (well_formed_sort_lift _ _ _ (Hwf') il2) as [sv2 Hsv2].
    destruct (is_large_dec (D ++ T :: e) t);
      destruct (is_large_dec (D ++ T' :: e) t2);
      try (iffT_contra Hlarge_iff).
    + match goal with
      | |- simulation.sim_star (coerce _ _ (extract_typ _ _ ?sn1))
                               (coerce _ _ (extract_typ _ _ ?sn2)) =>
        rewrite (extract_typ_ctx_conv T T'
                   (reduces_convertible _ _ (one_step_reduces _ _ Hr)) t t2 Hconv_t_t2 D e sn1 sn2 _ _ Hsv Hsv2)
      end.
      apply simulation.sim_star_refl.
    + rewrite Hterm_idx.
      apply coerce_sim_star_both_conv;
        [ apply (extract_lookup_type_ctx_swap _ _ Hr D e _ _ v Hwf)
        | apply (extract_typ_ctx_conv T T'
                   (reduces_convertible _ _ (one_step_reduces _ _ Hr))
                   t t2 Hconv_t_t2 D e _ _ _ _ Hsv Hsv2)
        | apply simulation.sim_star_refl ].
  - (* abs *)
    apply (extract_conv_strip_r_ctx _ _ _ _ _ _ H2 (refl_convertible _)).
    intros T2' H2' HconvR HnotconvR.
    pose (HT2 := has_type_reduces_environment_t _ _ _ H1_ _
                   (red_env_at D T T' e Hr) Hwf').
    change (T0 :: D ++ T :: e) with ((T0 :: D) ++ T :: e) in H1_1, H1_0.
    pose (HM2 := has_type_reduces_environment_t _ _ _ H1_1 _
                   (red_env_at (T0 :: D) T T' e Hr)
                   (wf_var _ T0 s1 HT2)).
    pose (HU2 := has_type_reduces_environment_t _ _ _ H1_0 _
                   (red_env_at (T0 :: D) T T' e Hr)
                   (wf_var _ T0 s1 HT2)).
    change ((T0 :: D) ++ T' :: e) with (T0 :: D ++ T' :: e) in HM2, HU2.
    pose (H2_abs := type_abs (D ++ T' :: e) T0 s1 HT2 M U s2 HU2 HM2).
    eapply simulation.sim_star_trans;
      [| exact (extract_deriv_indep_conv _ _ _ _ H2_abs H2' HconvR)].
    subst H2_abs HM2 HU2 HT2. simpl extract.
    assert (Hlarge_iff : iffT (is_large (D ++ T :: e) T0) (is_large (D ++ T' :: e) T0))
      by (eapply is_large_swap_at;
          [ exact (one_step_reduces _ _ Hr) | exact Hwf
          | exact (H1_) ]).
    destruct (is_large_dec (D ++ T :: e) T0); destruct (is_large_dec (D ++ T' :: e) T0);
      try (iffT_contra Hlarge_iff).
    + erewrite extract_kind_pi.
      apply sim_star_tabs.
      pose (HT2' := has_type_reduces_environment_t _ _ _ H1_ _
                      (red_env_at D T T' e Hr) Hwf').
      exact (IH (T0 :: D)
               (wf_var _ _ _ (H1_))
               (wf_var _ T0 s1 HT2')
               M U H1_1
               (has_type_reduces_environment_t _ _ _ H1_1 _
                  (red_env_at (T0 :: D) T T' e Hr)
                  (wf_var _ T0 s1 HT2'))).
    + erewrite (extract_typ_ctx_swap T T' Hr T0 D e _ _ (sort_term s1)
                  (H1_)).
      apply sim_star_abs.
      pose (HT2' := has_type_reduces_environment_t _ _ _ H1_ _
                      (red_env_at D T T' e Hr) Hwf').
      exact (IH (T0 :: D)
               (wf_var _ _ _ (H1_))
               (wf_var _ T0 s1 HT2')
               M U H1_1
               (has_type_reduces_environment_t _ _ _ H1_1 _
                  (red_env_at (T0 :: D) T T' e Hr)
                  (wf_var _ T0 s1 HT2'))).
  - (* app *)
    apply (extract_conv_strip_r_ctx _ _ _ _ _ _ H2 (refl_convertible _)).
    intros T2' H2' HconvR HnotconvR.
    pose (Hv2 := has_type_reduces_environment_t _ _ _ H1_ _
                   (red_env_at D T T' e Hr) Hwf').
    pose (Hu2 := has_type_reduces_environment_t _ _ _ H1_0 _
                   (red_env_at D T T' e Hr) Hwf').
    pose (H2_app := type_app (D ++ T' :: e) v V Hv2 u Ur Hu2).
    set (rhs := extract (D ++ T' :: e) (terms.app u v) T2' H2').
    eapply simulation.sim_star_trans.
    2: { subst rhs. exact (extract_deriv_indep_conv _ _ _ _ H2_app H2' HconvR). }
    subst H2_app Hu2 Hv2. simpl extract.
    assert (Hlarge_iff : iffT (is_large (D ++ T :: e) V) (is_large (D ++ T' :: e) V)).
    { destruct (type_case _ _ _ (H1_)) as [[sV HsV]|HVkind].
      - eapply is_large_swap_at;
          [ exact (one_step_reduces _ _ Hr) | exact Hwf | exact HsV ].
      - subst V. split; intro Habs; exfalso;
          exact (inversion_has_type_kind _ _ Habs). }
    destruct (is_large_dec (D ++ T :: e) V); destruct (is_large_dec (D ++ T' :: e) V);
      try (iffT_contra Hlarge_iff).
    + (* large: raw tapp; type arguments are ignored by [sim_star_tapp_gen] *)
      apply sim_star_tapp_gen.
      exact (IH D Hwf Hwf' u (terms.prod V Ur) (H1_0)
               (has_type_reduces_environment_t _ _ _ (H1_0) _
                  (red_env_at D T T' e Hr) Hwf')).
    + assert (HUrT : sigT (fun s => has_type (V :: D ++ T :: e) Ur (sort_term s))).
      { destruct (type_case _ _ _ (H1_0)) as [[sp Hsp]|Hbad]; [| discriminate].
        exact (inversion_has_type_prod _ _ _ _ _ Hsp
                 (fun _ s2 _ HU _ => existT _ s2 HU)). }
      apply coerce_sim_star_both_conv.
      * change (V :: D ++ T :: e) with ((V :: D) ++ T :: e) in HUrT.
        exact (extract_typ_ctx_swap T T' Hr Ur (V :: D) e _ _ (sort_term (projT1 HUrT)) (projT2 HUrT)).
      * apply (extract_typ_ctx_swap T T' Hr (terms.subst v Ur) D e _ _ (sort_term (projT1 HUrT))).
        change (sort_term (projT1 HUrT)) with (terms.subst v (sort_term (projT1 HUrT))).
        exact (substitution _ _ _ _ (projT2 HUrT) v (H1_)).
      * apply sim_star_app.
        -- exact (IH D Hwf Hwf' u (terms.prod V Ur) (H1_0)
                    (has_type_reduces_environment_t _ _ _ (H1_0) _
                       (red_env_at D T T' e Hr) Hwf')).
        -- exact (IH D Hwf Hwf' v V (H1_)
                    (has_type_reduces_environment_t _ _ _ (H1_) _
                       (red_env_at D T T' e Hr) Hwf')).
  - (* prod *)
    apply (extract_conv_strip_r_ctx _ _ _ _ _ _ H2 (refl_convertible _)).
    intros T2' H2' HconvR HnotconvR.
    dependent destruction H2'; try contradiction.
    apply simulation.sim_star_refl.
  - (* conv *)
    cbn [extract]. apply coerce_sim_star_l.
    pose (H1_2 := has_type_reduces_environment_t _ _ _ H1_ _
                     (red_env_at D T T' e Hr) Hwf').
    eapply simulation.sim_star_trans;
      [exact (IH D Hwf Hwf' t U H1_ H1_2) |].
    exact (extract_deriv_indep_conv _ _ _ _ H1_2 H2 c).
all: try (eapply strong_normalization; eassumption).
all: try assumption.
all: try (eapply well_formed_t_well_formed; eassumption).
all: try exact Hwf.
all: try exact Hwf'.
all: try (apply wf_ctx_red_at_once; [exact (one_step_reduces _ _ Hr) | assumption]).
all: try eassumption.
all: try (constructor; eassumption).
all: try auto.
all: try (eapply red_env_at).
all: try (exact (well_formed_t_well_formed _ Hwf')).
all: try (exact (well_formed_t_well_formed _ Hwf)).
all: try (eapply strong_normalization; eassumption).
all: try eassumption.
all: try (match goal with |- reduces ?T ?T' => exact (one_step_reduces _ _ Hr) end).
all: try (eapply wf_ctx_red_at_once; [eassumption | eassumption]).
all: try (match goal with |- well_formed ?e =>
           eapply well_formed_t_well_formed; eassumption end).
Qed.

