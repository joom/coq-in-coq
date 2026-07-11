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


(** * Closing [extract_typ_tsubst_coc_equiv] and [extract_well_typed]

    This module is placed AFTER [substitution_simulation.v] so that the whole
    type-namespace substitution / weakening / [ty_equiv]-congruence library is in
    scope.  It proves the commutation of type extraction with source
    type-substitution up to target Fω definitional equality, and then the target
    well-typedness of the extraction. *)

(** ** Classifier soundness on well-typed (not-necessarily-normal) terms

    The syntactic [classifier] and the semantic [is_large] agree on ANY
    well-sorted source term, normal or not.  [classifier_sound] already gives
    [classifier T = true -> is_large]; here we prove the completeness direction
    without a normality hypothesis: the only source terms that can have sort
    [kind] are sorts and products ending in a kind (a [var]/[lam]/[app] of sort
    [kind] is impossible), and those are exactly the syntactic classifiers.  The
    usual counterexamples to reduction-stability of [classifier] (e.g.
    [(fun x:set=>set) y], whose [classifier] flips under reduction) cannot arise
    for well-sorted source terms: they are ill-typed (a [kind]-valued lambda has
    an untypable [kind] codomain). *)
Lemma classifier_complete_typed : forall T e s,
  has_type e T (sort_term s) -> is_large e T -> classifier T = true.
Proof.
  intros T.
  induction T as [s0 | n | A IHA M IHM | u IHu v IHv | A IHA B IHB];
    intros e s Hty HL; unfold is_large in HL.
  - (* sort_term: always a classifier *) reflexivity.
  - (* var: a variable can never have sort kind *)
    exfalso.
    apply (inversion_has_type_ref False e (sort_term kind) n HL).
    intros U Hnth Hconv.
    assert (Hwf: well_formed e) by (apply has_type_well_formed with (var n) (sort_term kind); exact HL).
    assert (Hil: item_lift (lift (S n) U) e n)
      by (refine (existT2 _ _ U _ _); [reflexivity | exact Hnth]).
    destruct (well_formed_sort_lift n e (lift (S n) U) Hwf Hil) as [s' Hs].
    apply (inversion_has_type_convertible_kind e (lift (S n) U) (sort_term s'));
      [ apply sym_convertible; exact Hconv | exact Hs ].
  - (* lam: its type is a product, never convertible to a sort *)
    exfalso.
    apply (inversion_has_type_abs False e A M (sort_term kind) HL).
    intros s1 s2 T HA HM HT Hconv.
    apply (convertible_sort_product kind A T). apply sym_convertible. exact Hconv.
  - (* app: a neutral application can never have sort kind *)
    exfalso.
    apply (inversion_has_type_app False e u v (sort_term kind) HL).
    intros V Ur Hu Hv Hconv.
    destruct (type_case e u (prod V Ur) Hu) as [[s' Hs'] | Hbad]; [| discriminate Hbad].
    apply (inversion_has_type_prod False e V Ur (sort_term s') Hs').
    intros s1 s2 HV HUr Hconv2.
    assert (Hsub: has_type e (subst v Ur) (subst v (sort_term s2)))
      by (apply substitution with (t := V); [exact HUr | exact Hv]).
    simpl in Hsub.
    apply (inversion_has_type_convertible_kind e (subst v Ur) (sort_term s2));
      [ apply sym_convertible; exact Hconv | exact Hsub ].
  - (* prod A B: large iff codomain large; recurse on the codomain (no normality) *)
    simpl.
    apply (inversion_has_type_prod (classifier B = true) e A B (sort_term s) Hty).
    intros s1 s2 HA HB Hconv.
    apply (IHB (A :: e) s2).
    + exact HB.
    + (* is_large (A::e) B, inlined from the product characterization of HL *)
      apply (inversion_has_type_prod (has_type (A :: e) B (sort_term kind))
               e A B (sort_term kind) HL).
      intros s1' s2' HA' HB' Hconv'. apply convertible_sort in Hconv'. subst s2'. exact HB'.
Qed.

(** Full agreement of [classifier] and [is_large] on ANY well-sorted term. *)
Lemma classifier_iff_is_large_typed : forall T e s,
  has_type e T (sort_term s) ->
  ((classifier T = true -> is_large e T) * (is_large e T -> classifier T = true))%type.
Proof.
  intros T e s Hty. split.
  - intro Hcl. unfold is_large. rewrite (classifier_sound T e s Hty Hcl) in Hty. exact Hty.
  - intro HL. exact (classifier_complete_typed T e s Hty HL).
Qed.

(** ** [type_expr] commutes with substitution, for [V0] of any size

    Generalizes [substitution_simulation.type_expr_subst] (which assumes [V0]
    small) to arbitrary [V0].  Only the substitution-point [var] case differs:
    when [V0] is large the point is a type binding on both sides. *)
Lemma type_expr_subst_gen : forall X,
  forall g v0 V0 (Hv0: has_type g v0 V0) (wfg: well_formed g),
  forall n e f B, substitute_in_environment v0 V0 n e f ->
  has_type e X B -> well_formed e -> well_formed f -> skipn n f = g ->
  type_expr f (subst_rec v0 X n) = type_expr e X.
Proof.
  induction X as [s0 | k | X1 IHX1 X2 IHX2 | X1 IHX1 X2 IHX2 | X1 IHX1 X2 IHX2];
    intros g v0 V0 Hv0 wfg n e f B Hse HX wfe wff Hskip.
  - reflexivity.
  - (* var k *)
    simpl (subst_rec v0 (terms.var k) n).
    destruct (lt_eq_lt_dec n k) as [[Hlt | Heq] | Hgt].
    + simpl. exact (type_binding_substitute_above g v0 V0 Hv0 wfg n e f Hse wfe wff Hskip k Hlt).
    + subst k. simpl (type_expr e (terms.var n)).
      destruct (is_large_dec g V0) as [Hlarge | Hsm].
      * (* large substitution point: both sides are type bindings (true) *)
        rewrite (type_binding_at_subst_true g v0 V0 Hlarge n e f Hse Hskip).
        assert (Hlift_ty : has_type f (lift n v0) (lift n V0)).
        { apply weakening_at with g; auto.
          exact (substitute_length_le v0 V0 n e f Hse). }
        assert (HlargeV0f : is_large f (lift n V0)).
        { unfold is_large.
          change (sort_term kind) with (lift n (sort_term kind)).
          apply weakening_at with g; auto.
          exact (substitute_length_le v0 V0 n e f Hse). }
        apply (snd (type_expr_iff f (lift n v0) (lift n V0) Hlift_ty)). right. exact HlargeV0f.
      * (* small substitution point: both sides false *)
        rewrite (type_binding_at_subst_false g v0 V0 Hsm n e f Hse Hskip).
        destruct (type_expr f (lift n v0)) eqn:Hte; [|reflexivity].
        exfalso.
        assert (Hlift_ty : has_type f (lift n v0) (lift n V0)).
        { apply weakening_at with g; auto.
          exact (substitute_length_le v0 V0 n e f Hse). }
        assert (Hnth : nth_error e n = Some V0) by (exact (nth_substitute_eq v0 V0 n e f Hse)).
        assert (HV0sort : {s_V0 : sort & has_type g V0 (sort_term s_V0)}).
        { assert (Htmp := well_formed_sort n e (skipn (S n) e) eq_refl wfe V0 Hnth).
          destruct Htmp as [s_V0 Hs_V0].
          exists s_V0. rewrite <- Hskip. rewrite <- (skipn_succ_substitute v0 V0 n e f Hse). exact Hs_V0. }
        destruct HV0sort as [s_V0 HV0_g].
        assert (HV0_f : has_type f (lift n V0) (sort_term s_V0)).
        { change (sort_term s_V0) with (lift n (sort_term s_V0)).
          apply weakening_at with g; auto.
          exact (substitute_length_le v0 V0 n e f Hse). }
        destruct (fst (type_expr_iff f (lift n v0) (lift n V0) Hlift_ty) Hte) as [[s_eq Hseq] | Hlarge_f].
        -- destruct V0; simpl in Hseq; try discriminate.
           injection Hseq as <-.
           destruct s.
           ++ exact (inversion_has_type_kind g (sort_term s_V0) HV0_g).
           ++ apply Hsm. unfold is_large.
              assert (Hck := inversion_has_type_prop g (sort_term s_V0) HV0_g).
              apply convertible_sort in Hck. subst s_V0. exact HV0_g.
           ++ apply Hsm. unfold is_large.
              assert (Hck := inversion_has_type_set g (sort_term s_V0) HV0_g).
              apply convertible_sort in Hck. subst s_V0. exact HV0_g.
        -- unfold is_large in Hlarge_f.
           assert (Hconv := has_type_unique_sort f (lift n V0) (sort_term kind) Hlarge_f (sort_term s_V0) HV0_f).
           apply convertible_sort in Hconv. subst s_V0.
           apply Hsm. exact HV0_g.
    + simpl. exact (type_binding_substitute_below g v0 V0 Hv0 wfg n e f Hse wfe wff Hskip k Hgt).
  - (* lam X1 X2 *)
    simpl (subst_rec v0 (lam X1 X2) n). simpl (type_expr _ (lam _ _)).
    apply (inversion_has_type_abs
             (type_expr (subst_rec v0 X1 n :: f) (subst_rec v0 X2 (S n)) = type_expr (X1 :: e) X2)
             e X1 X2 B HX).
    intros s1 s2 T'' HX1 HX2 HT'' Hconv.
    assert (HX1f : has_type f (subst_rec v0 X1 n) (sort_term s1)).
    { change (sort_term s1) with (subst_rec v0 (sort_term s1) n).
      exact (has_type_substitute_weakening g v0 V0 Hv0 e X1 (sort_term s1) HX1 f n Hse wff Hskip). }
    assert (wff' : well_formed (subst_rec v0 X1 n :: f)) by (apply wf_var with s1; exact HX1f).
    assert (wfe_X1e : well_formed (X1 :: e)) by (apply wf_var with s1; exact HX1).
    exact (IHX2 g v0 V0 Hv0 wfg (S n) (X1 :: e) (subst_rec v0 X1 n :: f) T''
             (@sub_succ v0 V0 e f n X1 Hse) HX2 wfe_X1e wff' Hskip).
  - (* app X1 X2 *)
    simpl (subst_rec v0 (terms.app X1 X2) n). simpl (type_expr _ (terms.app _ _)).
    apply (inversion_has_type_app
             (type_expr f (subst_rec v0 X1 n) = type_expr e X1)
             e X1 X2 B HX).
    intros V Ur Hu Hv Hconv.
    exact (IHX1 g v0 V0 Hv0 wfg n e f (prod V Ur) Hse Hu wfe wff Hskip).
  - (* prod *) reflexivity.
Qed.

(** ** [extract_kind_L] commutes with RAW substitution on well-typed classifiers

    Unlike [substitution_simulation.extract_kind_L_large_subst], this is the RAW
    version (no [nf] on the substituted term) and needs no normality: it relies on
    [classifier_iff_is_large_typed], which makes [classifier] agree with the
    (substitution-stable) [is_large] on any well-sorted term. *)
Lemma extract_kind_L_large_subst_raw : forall W,
  forall g v0 V0 (Hv0: has_type g v0 V0) (wfg: well_formed g),
  forall n e f s, substitute_in_environment v0 V0 n e f ->
  has_type e W (sort_term s) -> well_formed e -> well_formed f -> skipn n f = g ->
  classifier W = true ->
  extract_kind_L (subst_rec v0 W n) = extract_kind_L W.
Proof.
  induction W as [s0 | k | X1 IHX1 X2 IHX2 | X1 IHX1 X2 IHX2 | X1 IHX1 X2 IHX2];
    intros g v0 V0 Hv0 wfg n e f s Hse HW wfe wff Hskip Hcw; simpl in Hcw.
  - (* sort *) reflexivity.
  - (* var *) discriminate.
  - (* lam *) discriminate.
  - (* app *) discriminate.
  - (* prod X1 X2 *)
    apply (inversion_has_type_prod
             (extract_kind_L (subst_rec v0 (prod X1 X2) n) = extract_kind_L (prod X1 X2))
             e X1 X2 (sort_term s) HW).
    intros s1 s2 HX1 HX2 Hconv.
    change (subst_rec v0 (prod X1 X2) n)
      with (prod (subst_rec v0 X1 n) (subst_rec v0 X2 (S n))).
    simpl (extract_kind_L (prod _ _)).
    assert (HX1_f : has_type f (subst_rec v0 X1 n) (sort_term s1)).
    { change (sort_term s1) with (subst_rec v0 (sort_term s1) n).
      exact (has_type_substitute_weakening g v0 V0 Hv0 e X1 (sort_term s1) HX1 f n Hse wff Hskip). }
    assert (Hcl_eq : classifier (subst_rec v0 X1 n) = classifier X1).
    { pose proof (classifier_iff_is_large_typed X1 e s1 HX1) as Hcl_orig.
      pose proof (classifier_iff_is_large_typed (subst_rec v0 X1 n) f s1 HX1_f) as Hcl_sub.
      destruct (classifier X1) eqn:HclX1; destruct (classifier (subst_rec v0 X1 n)) eqn:HclS;
        try reflexivity; exfalso.
      - assert (Hlarge_f : is_large f (subst_rec v0 X1 n)).
        { apply (has_type_substitute_weakening g v0 V0 Hv0 e X1 (sort_term kind)
                   (fst Hcl_orig eq_refl) f n Hse wff Hskip). }
        pose proof (snd Hcl_sub Hlarge_f) as Habs. discriminate.
      - assert (Hlarge_e : is_large e X1).
        { exact (is_large_substitute_inv g v0 V0 Hv0 e X1 s1 HX1 f n Hse wff Hskip
                   (fst Hcl_sub eq_refl)). }
        pose proof (snd Hcl_orig Hlarge_e) as Habs. discriminate. }
    rewrite Hcl_eq.
    assert (wff' : well_formed (subst_rec v0 X1 n :: f))
      by (apply wf_var with s1; exact HX1_f).
    assert (wfe' : well_formed (X1 :: e))
      by (apply wf_var with s1; exact HX1).
    assert (Hcw2 : classifier X2 = true) by exact Hcw.
    destruct (classifier X1) eqn:HclX1e.
    + f_equal.
      * exact (IHX1 g v0 V0 Hv0 wfg n e f s1 Hse HX1 wfe wff Hskip eq_refl).
      * exact (IHX2 g v0 V0 Hv0 wfg (S n) (X1 :: e) (subst_rec v0 X1 n :: f) s2
                 (@sub_succ v0 V0 e f n X1 Hse) HX2 wfe' wff' Hskip Hcw2).
    + exact (IHX2 g v0 V0 Hv0 wfg (S n) (X1 :: e) (subst_rec v0 X1 n :: f) s2
               (@sub_succ v0 V0 e f n X1 Hse) HX2 wfe' wff' Hskip Hcw2).
Qed.

(** ** Target [tsubst] computation helpers *)
Lemma tsubst_tvar_eq_idx : forall s k,
  infrastructure.tsubst s k (syntax.tvar k) = infrastructure.tlift k 0 s.
Proof.
  intros s k. simpl. destruct (lt_eq_lt_dec k k) as [[H|H]|H]; try lia; reflexivity.
Qed.

Lemma tsubst_tvar_gt : forall s k i,
  k < i -> infrastructure.tsubst s k (syntax.tvar i) = syntax.tvar (Nat.pred i).
Proof.
  intros s k i H. simpl. destruct (lt_eq_lt_dec k i) as [[H'|H']|H']; try lia; reflexivity.
Qed.

Lemma tsubst_tvar_lt : forall s k i,
  i < k -> infrastructure.tsubst s k (syntax.tvar i) = syntax.tvar i.
Proof.
  intros s k i H. simpl. destruct (lt_eq_lt_dec k i) as [[H'|H']|H']; try lia; reflexivity.
Qed.

(** ** RAW structural commutation of [extract_typ_L] with large substitution

    Lemma 1.  [extract_typ_L] is purely structural (it never fires a source
    redex), so its commutation with source substitution is proved by plain
    structural induction on [W], with NO [nf] on the right side and hence no
    non-structural recursion.  The conclusion is up to [ty_equiv] only to absorb
    the target β-redex [tyapp (tyabs _ _) _] produced by lemma 2 downstream; here
    every step is actually an equality up to the congruences.  [v0] must be
    normal (used at the substitution-point [var] via
    [extract_typ_L_lift_n_large]). *)
Lemma extract_typ_L_large_subst_raw : forall W g v0 V0
  (Hv0 : has_type g v0 V0) (wfg : well_formed g) (Hnv0 : normal v0) (Hlg : is_large g V0),
  forall n e f B, substitute_in_environment v0 V0 n e f ->
  has_type e W B -> well_formed e -> well_formed f -> skipn n f = g ->
  type_expr e W = true ->
  infrastructure.ty_equiv
    (infrastructure.tsubst (extract_typ_L g v0) (type_index e n) (extract_typ_L e W))
    (extract_typ_L f (subst_rec v0 W n)).
Proof.
  induction W as [s0 | k | X1 IHX1 X2 IHX2 | X1 IHX1 X2 IHX2 | X1 IHX1 X2 IHX2];
    intros g v0 V0 Hv0 wfg Hnv0 Hlg n e f B Hse HW wfe wff Hskip Hte.
  - (* sort *)
    change (subst_rec v0 (sort_term s0) n) with (sort_term s0).
    simpl (extract_typ_L e (sort_term s0)). simpl (extract_typ_L f (sort_term s0)).
    simpl (infrastructure.tsubst _ _ syntax.dyn). apply infrastructure.ty_equiv_refl.
  - (* var k *)
    simpl in Hte. (* type_binding e k = true *)
    simpl (extract_typ_L e (terms.var k)). rewrite Hte.
    destruct (lt_eq_lt_dec n k) as [[Hlt | Heq] | Hgt].
    + (* k > n *)
      rewrite (subst_ref_gt v0 k n Hlt).
      simpl (extract_typ_L f (terms.var (Nat.pred k))).
      rewrite (type_binding_substitute_above g v0 V0 Hv0 wfg n e f Hse wfe wff Hskip k Hlt).
      rewrite Hte.
      assert (Hlt_idx : type_index e n < type_index e k).
      { apply (type_index_gt_of_type_binding e n k Hlt).
        exact (type_binding_at_subst_true g v0 V0 Hlg n e f Hse Hskip). }
      rewrite (tsubst_tvar_gt (extract_typ_L g v0) (type_index e n) (type_index e k) Hlt_idx).
      rewrite (type_index_substitute_above_large g v0 V0 Hv0 Hlg n e f Hse wfe wff Hskip k Hlt).
      apply infrastructure.ty_equiv_refl.
    + (* k = n : the substitution point (large) *)
      subst k. rewrite (subst_ref_eq v0 n).
      rewrite (tsubst_tvar_eq_idx (extract_typ_L g v0) (type_index e n)).
      pose (snv0 := strong_normalization g v0 V0 Hv0).
      assert (Hty_lift : has_type f (lift n v0) (lift n V0))
        by (apply weakening_at with g; auto; exact (substitute_length_le v0 V0 n e f Hse)).
      pose (snlift := strong_normalization f (lift n v0) (lift n V0) Hty_lift).
      pose proof (extract_typ_L_lift_n_large n f g
                    (substitute_length_le v0 V0 n e f Hse) Hskip wff v0 V0 Hv0 snlift snv0) as Hlift.
      rewrite (nf_normal_eq (lift n v0) snlift (normal_lift v0 Hnv0 n 0)) in Hlift.
      rewrite (nf_normal_eq v0 snv0 Hnv0) in Hlift.
      rewrite (type_index_substitute_at g v0 V0 Hv0 wfg n e f Hse wfe wff Hskip) in Hlift.
      rewrite Hlift. apply infrastructure.ty_equiv_refl.
    + (* k < n *)
      rewrite (subst_ref_lt v0 k n Hgt).
      simpl (extract_typ_L f (terms.var k)).
      rewrite (type_binding_substitute_below g v0 V0 Hv0 wfg n e f Hse wfe wff Hskip k Hgt).
      rewrite Hte.
      assert (Hgt_idx : type_index e k < type_index e n).
      { apply (type_index_gt_of_type_binding e k n Hgt).
        exact Hte. }
      rewrite (tsubst_tvar_lt (extract_typ_L g v0) (type_index e n) (type_index e k) Hgt_idx).
      rewrite (type_index_substitute_below g v0 V0 Hv0 wfg n e f Hse wfe wff Hskip k Hgt).
      apply infrastructure.ty_equiv_refl.
  - (* lam X1 X2 *)
    apply (inversion_has_type_abs
             (infrastructure.ty_equiv
                (infrastructure.tsubst (extract_typ_L g v0) (type_index e n) (extract_typ_L e (lam X1 X2)))
                (extract_typ_L f (subst_rec v0 (lam X1 X2) n)))
             e X1 X2 B HW).
    intros s1 s2 T'' HX1 HX2 HT'' Hconv.
    assert (Hte2 : type_expr (X1 :: e) X2 = true) by (simpl in Hte; exact Hte).
    change (subst_rec v0 (lam X1 X2) n)
      with (lam (subst_rec v0 X1 n) (subst_rec v0 X2 (S n))).
    assert (HX1_f : has_type f (subst_rec v0 X1 n) (sort_term s1)).
    { change (sort_term s1) with (subst_rec v0 (sort_term s1) n).
      exact (has_type_substitute_weakening g v0 V0 Hv0 e X1 (sort_term s1) HX1 f n Hse wff Hskip). }
    assert (Hcl_eq : classifier (subst_rec v0 X1 n) = classifier X1).
    { pose proof (classifier_iff_is_large_typed X1 e s1 HX1) as Hcl_orig.
      pose proof (classifier_iff_is_large_typed (subst_rec v0 X1 n) f s1 HX1_f) as Hcl_sub.
      destruct (classifier X1) eqn:HclX1; destruct (classifier (subst_rec v0 X1 n)) eqn:HclS;
        try reflexivity; exfalso.
      - assert (Hlarge_f : is_large f (subst_rec v0 X1 n)).
        { apply (has_type_substitute_weakening g v0 V0 Hv0 e X1 (sort_term kind)
                   (fst Hcl_orig eq_refl) f n Hse wff Hskip). }
        pose proof (snd Hcl_sub Hlarge_f) as Habs. discriminate.
      - assert (Hlarge_e : is_large e X1).
        { exact (is_large_substitute_inv g v0 V0 Hv0 e X1 s1 HX1 f n Hse wff Hskip
                   (fst Hcl_sub eq_refl)). }
        pose proof (snd Hcl_orig Hlarge_e) as Habs. discriminate. }
    assert (wff' : well_formed (subst_rec v0 X1 n :: f)) by (apply wf_var with s1; exact HX1_f).
    assert (wfe' : well_formed (X1 :: e)) by (apply wf_var with s1; exact HX1).
    pose proof (IHX2 g v0 V0 Hv0 wfg Hnv0 Hlg (S n) (X1 :: e) (subst_rec v0 X1 n :: f) T''
                  (@sub_succ v0 V0 e f n X1 Hse) HX2 wfe' wff' Hskip Hte2) as IH2.
    simpl (extract_typ_L e (lam X1 X2)). simpl (extract_typ_L f (lam _ _)).
    rewrite Hcl_eq.
    simpl (type_index (X1 :: e) (S n)) in IH2.
    destruct (classifier X1) eqn:HclX1e.
    + (* large domain: tyabs *)
      assert (HlX1 : is_large e X1) by (exact (fst (classifier_iff_is_large_typed X1 e s1 HX1) HclX1e)).
      destruct (is_large_dec e X1) as [_ | Hbad]; [| exfalso; exact (Hbad HlX1)].
      rewrite (extract_kind_L_large_subst_raw X1 g v0 V0 Hv0 wfg n e f s1 Hse HX1 wfe wff Hskip HclX1e).
      simpl (infrastructure.tsubst _ _ (syntax.tyabs _ _)).
      apply ty_equiv_tyabs_cong. exact IH2.
    + (* small domain: drop the binder *)
      assert (HnlX1 : is_large e X1 -> False)
        by (intro HL; rewrite (snd (classifier_iff_is_large_typed X1 e s1 HX1) HL) in HclX1e; discriminate).
      destruct (is_large_dec e X1) as [Hbad | _]; [exfalso; exact (HnlX1 Hbad) |].
      exact IH2.
  - (* app X1 X2 *)
    apply (inversion_has_type_app
             (infrastructure.ty_equiv
                (infrastructure.tsubst (extract_typ_L g v0) (type_index e n) (extract_typ_L e (terms.app X1 X2)))
                (extract_typ_L f (subst_rec v0 (terms.app X1 X2) n)))
             e X1 X2 B HW).
    intros V Ur Hu Hv Hconv.
    assert (Hte1 : type_expr e X1 = true) by (simpl in Hte; exact Hte).
    change (subst_rec v0 (terms.app X1 X2) n)
      with (terms.app (subst_rec v0 X1 n) (subst_rec v0 X2 n)).
    simpl (extract_typ_L e (terms.app X1 X2)). simpl (extract_typ_L f (terms.app _ _)).
    rewrite Hte1.
    rewrite (type_expr_subst_gen X1 g v0 V0 Hv0 wfg n e f (prod V Ur) Hse Hu wfe wff Hskip).
    rewrite (type_expr_subst_gen X2 g v0 V0 Hv0 wfg n e f V Hse Hv wfe wff Hskip).
    rewrite Hte1.
    pose proof (IHX1 g v0 V0 Hv0 wfg Hnv0 Hlg n e f (prod V Ur) Hse Hu wfe wff Hskip Hte1) as IH1.
    destruct (type_expr e X2) eqn:HeX2.
    + pose proof (IHX2 g v0 V0 Hv0 wfg Hnv0 Hlg n e f V Hse Hv wfe wff Hskip HeX2) as IH2.
      simpl (infrastructure.tsubst _ _ (syntax.tyapp _ _)).
      apply ty_equiv_tyapp_cong; [exact IH1 | exact IH2].
    + exact IH1.
  - (* prod X1 X2 *)
    apply (inversion_has_type_prod
             (infrastructure.ty_equiv
                (infrastructure.tsubst (extract_typ_L g v0) (type_index e n) (extract_typ_L e (prod X1 X2)))
                (extract_typ_L f (subst_rec v0 (prod X1 X2) n)))
             e X1 X2 B HW).
    intros s1 s2 HX1 HX2 Hconv.
    assert (Hte1 : type_expr e X1 = true)
      by (apply (snd (type_expr_iff e X1 (sort_term s1) HX1)); left; exists s1; reflexivity).
    assert (Hte2 : type_expr (X1 :: e) X2 = true)
      by (apply (snd (type_expr_iff (X1 :: e) X2 (sort_term s2) HX2)); left; exists s2; reflexivity).
    change (subst_rec v0 (prod X1 X2) n)
      with (prod (subst_rec v0 X1 n) (subst_rec v0 X2 (S n))).
    assert (HX1_f : has_type f (subst_rec v0 X1 n) (sort_term s1)).
    { change (sort_term s1) with (subst_rec v0 (sort_term s1) n).
      exact (has_type_substitute_weakening g v0 V0 Hv0 e X1 (sort_term s1) HX1 f n Hse wff Hskip). }
    assert (Hcl_eq : classifier (subst_rec v0 X1 n) = classifier X1).
    { pose proof (classifier_iff_is_large_typed X1 e s1 HX1) as Hcl_orig.
      pose proof (classifier_iff_is_large_typed (subst_rec v0 X1 n) f s1 HX1_f) as Hcl_sub.
      destruct (classifier X1) eqn:HclX1; destruct (classifier (subst_rec v0 X1 n)) eqn:HclS;
        try reflexivity; exfalso.
      - assert (Hlarge_f : is_large f (subst_rec v0 X1 n)).
        { apply (has_type_substitute_weakening g v0 V0 Hv0 e X1 (sort_term kind)
                   (fst Hcl_orig eq_refl) f n Hse wff Hskip). }
        pose proof (snd Hcl_sub Hlarge_f) as Habs. discriminate.
      - assert (Hlarge_e : is_large e X1).
        { exact (is_large_substitute_inv g v0 V0 Hv0 e X1 s1 HX1 f n Hse wff Hskip
                   (fst Hcl_sub eq_refl)). }
        pose proof (snd Hcl_orig Hlarge_e) as Habs. discriminate. }
    assert (wff' : well_formed (subst_rec v0 X1 n :: f)) by (apply wf_var with s1; exact HX1_f).
    assert (wfe' : well_formed (X1 :: e)) by (apply wf_var with s1; exact HX1).
    pose proof (IHX1 g v0 V0 Hv0 wfg Hnv0 Hlg n e f (sort_term s1) Hse HX1 wfe wff Hskip Hte1) as IH1.
    pose proof (IHX2 g v0 V0 Hv0 wfg Hnv0 Hlg (S n) (X1 :: e) (subst_rec v0 X1 n :: f) (sort_term s2)
                  (@sub_succ v0 V0 e f n X1 Hse) HX2 wfe' wff' Hskip Hte2) as IH2.
    simpl (extract_typ_L e (prod X1 X2)). simpl (extract_typ_L f (prod _ _)).
    rewrite Hcl_eq.
    simpl (type_index (X1 :: e) (S n)) in IH2.
    destruct (classifier X1) eqn:HclX1e.
    + (* large domain: all *)
      assert (HlX1 : is_large e X1) by (exact (fst (classifier_iff_is_large_typed X1 e s1 HX1) HclX1e)).
      destruct (is_large_dec e X1) as [_ | Hbad]; [| exfalso; exact (Hbad HlX1)].
      rewrite (extract_kind_L_large_subst_raw X1 g v0 V0 Hv0 wfg n e f s1 Hse HX1 wfe wff Hskip HclX1e).
      simpl (infrastructure.tsubst _ _ (syntax.all _ _)).
      apply ty_equiv_all_cong. exact IH2.
    + (* small domain: arrow *)
      assert (HnlX1 : is_large e X1 -> False)
        by (intro HL; rewrite (snd (classifier_iff_is_large_typed X1 e s1 HX1) HL) in HclX1e; discriminate).
      destruct (is_large_dec e X1) as [Hbad | _]; [exfalso; exact (HnlX1 Hbad) |].
      simpl (infrastructure.tsubst _ _ (syntax.arrow _ _)).
      apply ty_equiv_arrow_cong; [exact IH1 | exact IH2].
Qed.

(** ** Structural unfolding equations for [extract_typ_L] / [type_expr]

    These are definitional (each is [reflexivity]); we package them as rewrite
    lemmas so the single-step invariance proof below can unfold [extract_typ_L]
    on a specific head constructor WITHOUT accidentally reducing the opaque
    [type_expr]/[classifier]/[is_large_dec] guards. *)
Lemma extract_typ_L_app_eq : forall e u v,
  extract_typ_L e (terms.app u v) =
    (if type_expr e u
     then if type_expr e v
          then syntax.tyapp (extract_typ_L e u) (extract_typ_L e v)
          else extract_typ_L e u
     else syntax.dyn).
Proof. reflexivity. Qed.

Lemma extract_typ_L_lam_eq : forall e T M,
  extract_typ_L e (terms.lam T M) =
    (if classifier T
     then syntax.tyabs (extract_kind_L T) (extract_typ_L (T :: e) M)
     else extract_typ_L (T :: e) M).
Proof. reflexivity. Qed.

Lemma extract_typ_L_prod_eq : forall e T U,
  extract_typ_L e (terms.prod T U) =
    (if classifier T
     then syntax.all (extract_kind_L T) (extract_typ_L (T :: e) U)
     else syntax.arrow (extract_typ_L e T) (extract_typ_L (T :: e) U)).
Proof. reflexivity. Qed.

Lemma type_expr_lam_eq : forall e T M,
  type_expr e (terms.lam T M) = type_expr (T :: e) M.
Proof. reflexivity. Qed.

(** ** Classifier / [extract_kind_L] / [type_expr] stability under one source step *)

(** [classifier] agrees on a well-sorted term and its one-step reduct (both have
    the same sort, and [classifier] agrees with the reduction-stable [is_large]). *)
Lemma classifier_reduces_once : forall A A' e s,
  has_type e A (sort_term s) -> reduces_once A A' -> classifier A = classifier A'.
Proof.
  intros A A' e s HA Hr.
  assert (HA' : has_type e A' (sort_term s)) by (exact (subject_reduction e A (sort_term s) HA A' Hr)).
  assert (Hconv : convertible A A') by (apply reduces_convertible; apply one_step_reduces; exact Hr).
  assert (Hiff : iffT (is_large e A) (is_large e A'))
    by (exact (is_large_conv_iff e A A' s s Hconv HA HA')).
  destruct (classifier A) eqn:CA; destruct (classifier A') eqn:CA'; try reflexivity; exfalso.
  - assert (HLA : is_large e A) by (exact (fst (classifier_iff_is_large_typed A e s HA) CA)).
    rewrite (snd (classifier_iff_is_large_typed A' e s HA') (fst Hiff HLA)) in CA'. discriminate.
  - assert (HLA' : is_large e A') by (exact (fst (classifier_iff_is_large_typed A' e s HA') CA')).
    rewrite (snd (classifier_iff_is_large_typed A e s HA) (snd Hiff HLA')) in CA. discriminate.
Qed.

(** A large (sort-[kind]) source type is a [sort]/[prod] spine, so a one-step redex
    lives inside a product and [extract_kind_L] is invariant under it. *)
Lemma extract_kind_L_reduces_once_large : forall T e T',
  has_type e T (sort_term kind) -> reduces_once T T' -> extract_kind_L T = extract_kind_L T'.
Proof.
  induction T as [s0 | n | A IHA M IHM | u IHu v IHv | A IHA B IHB]; intros e T' HT Hr.
  - (* sort: no reduction out of a sort *) dependent destruction Hr.
  - (* var: cannot have sort kind *)
    exfalso. pose proof (classifier_complete_typed (terms.var n) e kind HT HT) as Hcc.
    simpl in Hcc. discriminate.
  - (* lam: cannot have sort kind *)
    exfalso. pose proof (classifier_complete_typed (lam A M) e kind HT HT) as Hcc.
    simpl in Hcc. discriminate.
  - (* app: cannot have sort kind *)
    exfalso. pose proof (classifier_complete_typed (terms.app u v) e kind HT HT) as Hcc.
    simpl in Hcc. discriminate.
  - (* prod A B *)
    apply (inversion_has_type_prod (extract_kind_L (prod A B) = extract_kind_L T')
             e A B (sort_term kind) HT).
    intros s1 s2 HA HB Hconv.
    apply convertible_sort in Hconv. subst s2.
    dependent destruction Hr.
    + (* prod_reduces_left: A -> A' *)
      match goal with H : reduces_once A ?a |- _ =>
        simpl (extract_kind_L (prod A B)); simpl (extract_kind_L (prod a B));
        rewrite <- (classifier_reduces_once A a e s1 HA H);
        destruct (classifier A) eqn:CA;
        [ assert (Hs1 : s1 = kind) by (exact (classifier_sound A e s1 HA CA)); subst s1;
          rewrite (IHA e a HA H); reflexivity
        | reflexivity ]
      end.
    + (* prod_reduces_right: B -> B' *)
      match goal with H : reduces_once B ?b |- _ =>
        simpl (extract_kind_L (prod A B)); simpl (extract_kind_L (prod A b));
        rewrite (IHB (A :: e) b HB H);
        destruct (classifier A); reflexivity
      end.
Qed.

(** [type_expr]'s truth value is invariant under a one-step reduction (it is
    characterized purely by the type [B], via [type_expr_iff] + subject reduction). *)
Lemma type_expr_reduces_once : forall e W W' B,
  has_type e W B -> reduces_once W W' -> type_expr e W = type_expr e W'.
Proof.
  intros e W W' B HW Hr.
  assert (HW' : has_type e W' B) by (exact (subject_reduction e W B HW W' Hr)).
  destruct (type_expr e W) eqn:E1; destruct (type_expr e W') eqn:E2; try reflexivity; exfalso.
  - assert (type_expr e W' = true)
      by (apply (snd (type_expr_iff e W' B HW')); exact (fst (type_expr_iff e W B HW) E1)).
    rewrite E2 in H. discriminate.
  - assert (type_expr e W = true)
      by (apply (snd (type_expr_iff e W B HW)); exact (fst (type_expr_iff e W' B HW') E2)).
    rewrite E1 in H. discriminate.
Qed.

(** ** [extract_typ_L] weakening on NON-normal (but well-sorted) terms

    A copy of [substitution_simulation.extract_typ_L_weaken] with the [normal X]
    hypothesis dropped: the only use of normality there was
    [classifier_iff_is_large_nf], replaced here by [classifier_iff_is_large_typed]
    (valid on any well-sorted term). *)
Lemma extract_typ_L_weaken_typed : forall X, forall A p ctx f B, insert_in_environment A p ctx f ->
  has_type ctx X B -> well_formed f ->
  extract_typ_L f (lift_rec 1 X p) =
    if is_large_dec (skipn p ctx) A
    then infrastructure.tlift 1 (type_index ctx p) (extract_typ_L ctx X)
    else extract_typ_L ctx X.
Proof.
  induction X as [s0 | n | X1 IHX1 X2 IHX2 | X1 IHX1 X2 IHX2 | X1 IHX1 X2 IHX2];
    intros A p ctx f B Hins HX wff; simpl.
  - destruct (is_large_dec (skipn p ctx) A); reflexivity.
  - assert (wfctx : well_formed ctx) by (apply has_type_well_formed with (var n) B; exact HX).
    destruct (le_gt_dec p n) as [Hle | Hgt];
      simpl (extract_typ_L f (var _)); simpl (extract_typ_L ctx (var n)).
    + rewrite (type_binding_insert_ge A p ctx f Hins wfctx wff n Hle).
      destruct (is_large_dec (skipn p ctx) A) as [HlA | HnlA].
      * rewrite (type_index_insert_ge_large A p ctx f Hins wfctx wff HlA n Hle).
        assert (Hm : type_index ctx p <= type_index ctx n) by (apply type_index_mono; exact Hle).
        destruct (type_binding ctx n); simpl;
          [destruct (le_gt_dec (type_index ctx p) (type_index ctx n));
            [f_equal; lia | lia] | reflexivity].
      * rewrite (type_index_insert_ge_small A p ctx f Hins wfctx wff HnlA n Hle).
        destruct (type_binding ctx n); reflexivity.
    + rewrite (type_binding_insert_lt A p ctx f Hins wfctx wff n Hgt).
      rewrite (type_index_insert_lt A p ctx f Hins wfctx wff n Hgt).
      destruct (is_large_dec (skipn p ctx) A) as [HlA | HnlA].
      * destruct (type_binding ctx n) eqn:Htb; simpl; [| reflexivity].
        assert (Hgt2 : type_index ctx p > type_index ctx n)
          by (apply type_index_gt_of_type_binding; [exact Hgt | exact Htb]).
        destruct (le_gt_dec (type_index ctx p) (type_index ctx n)); [lia | reflexivity].
      * destruct (type_binding ctx n); simpl; reflexivity.
  - (* lam X1 X2 *)
    apply (inversion_has_type_abs
             (extract_typ_L f (lam (lift_rec 1 X1 p) (lift_rec 1 X2 (S p))) =
              (if is_large_dec (skipn p ctx) A
               then infrastructure.tlift 1 (type_index ctx p) (extract_typ_L ctx (lam X1 X2))
               else extract_typ_L ctx (lam X1 X2)))
             ctx X1 X2 B HX).
    intros s1 s2 T'' HX1 HX2 HT'' Hconv.
    assert (wff' : well_formed (lift_rec 1 X1 p :: f))
      by (apply wf_var with s1;
          change (sort_term s1) with (lift_rec 1 (sort_term s1) p);
          exact (has_type_weakening_weak A ctx X1 (sort_term s1) HX1 p f Hins wff)).
    cbn [extract_typ_L].
    rewrite (classifier_lift X1 1 p).
    pose proof (IHX2 A (S p) (X1 :: ctx) (lift_rec 1 X1 p :: f) T''
                  (ins_succ A p ctx f X1 Hins) HX2 wff') as IH2.
    assert (Hskip : skipn (S p) (X1 :: ctx) = skipn p ctx) by reflexivity.
    rewrite Hskip in IH2.
    assert (Hcl_large : type_index (X1 :: ctx) (S p) =
              if classifier X1 then S (type_index ctx p) else type_index ctx p).
    { change (type_index (X1 :: ctx) (S p)) with
        (if is_large_dec ctx X1 then S (type_index ctx p) else type_index ctx p).
      destruct (classifier X1) eqn:Hcl.
      - destruct (is_large_dec ctx X1) as [_ | HNL]; [reflexivity |].
        exfalso. apply HNL. exact (fst (classifier_iff_is_large_typed X1 ctx s1 HX1) Hcl).
      - destruct (is_large_dec ctx X1) as [HL | _]; [| reflexivity].
        exfalso. rewrite (snd (classifier_iff_is_large_typed X1 ctx s1 HX1) HL) in Hcl.
        discriminate. }
    rewrite Hcl_large in IH2.
    destruct (classifier X1) eqn:Hcl.
    + rewrite (extract_kind_L_lift X1 1 p).
      destruct (is_large_dec (skipn p ctx) A) as [HlA | HnlA];
        rewrite IH2; reflexivity.
    + destruct (is_large_dec (skipn p ctx) A) as [HlA | HnlA];
        rewrite IH2; reflexivity.
  - (* app X1 X2 *)
    apply (inversion_has_type_app
             (extract_typ_L f (terms.app (lift_rec 1 X1 p) (lift_rec 1 X2 p)) =
              (if is_large_dec (skipn p ctx) A
               then infrastructure.tlift 1 (type_index ctx p) (extract_typ_L ctx (terms.app X1 X2))
               else extract_typ_L ctx (terms.app X1 X2)))
             ctx X1 X2 B HX).
    intros V Ur Hu Hv Hconv.
    cbn [extract_typ_L].
    rewrite (type_expr_weaken X1 A p ctx f (prod V Ur) Hins Hu wff).
    rewrite (type_expr_weaken X2 A p ctx f V Hins Hv wff).
    pose proof (IHX1 A p ctx f (prod V Ur) Hins Hu wff) as IH1.
    pose proof (IHX2 A p ctx f V Hins Hv wff) as IH2.
    destruct (type_expr ctx X1) eqn:He1; destruct (type_expr ctx X2) eqn:He2;
      destruct (is_large_dec (skipn p ctx) A) as [HlA | HnlA];
      try (rewrite IH1); try (rewrite IH2); reflexivity.
  - (* prod X1 X2 *)
    apply (inversion_has_type_prod
             (extract_typ_L f (prod (lift_rec 1 X1 p) (lift_rec 1 X2 (S p))) =
              (if is_large_dec (skipn p ctx) A
               then infrastructure.tlift 1 (type_index ctx p) (extract_typ_L ctx (prod X1 X2))
               else extract_typ_L ctx (prod X1 X2)))
             ctx X1 X2 B HX).
    intros s1 s2 HX1 HX2 Hconv.
    assert (wff' : well_formed (lift_rec 1 X1 p :: f))
      by (apply wf_var with s1;
          change (sort_term s1) with (lift_rec 1 (sort_term s1) p);
          exact (has_type_weakening_weak A ctx X1 (sort_term s1) HX1 p f Hins wff)).
    cbn [extract_typ_L].
    rewrite (classifier_lift X1 1 p).
    assert (Hcl_large : type_index (X1 :: ctx) (S p) =
              if classifier X1 then S (type_index ctx p) else type_index ctx p).
    { change (type_index (X1 :: ctx) (S p)) with
        (if is_large_dec ctx X1 then S (type_index ctx p) else type_index ctx p).
      destruct (classifier X1) eqn:Hcl.
      - destruct (is_large_dec ctx X1) as [_ | HNL]; [reflexivity |].
        exfalso. apply HNL. exact (fst (classifier_iff_is_large_typed X1 ctx s1 HX1) Hcl).
      - destruct (is_large_dec ctx X1) as [HL | _]; [| reflexivity].
        exfalso. rewrite (snd (classifier_iff_is_large_typed X1 ctx s1 HX1) HL) in Hcl.
        discriminate. }
    destruct (classifier X1) eqn:Hcl.
    + rewrite (extract_kind_L_lift X1 1 p).
      pose proof (IHX2 A (S p) (X1 :: ctx) (lift_rec 1 X1 p :: f) (sort_term s2)
                    (ins_succ A p ctx f X1 Hins) HX2 wff') as IH2.
      assert (Hskip : skipn (S p) (X1 :: ctx) = skipn p ctx) by reflexivity.
      rewrite Hskip in IH2. rewrite Hcl_large in IH2.
      destruct (is_large_dec (skipn p ctx) A) as [HlA | HnlA].
      * destruct (is_large_dec (skipn p ctx) A) as [_|Hc] in IH2; [| contradiction].
        rewrite IH2. reflexivity.
      * destruct (is_large_dec (skipn p ctx) A) as [Hc|_] in IH2; [contradiction |].
        rewrite IH2. reflexivity.
    + pose proof (IHX1 A p ctx f (sort_term s1) Hins HX1 wff) as IH1.
      pose proof (IHX2 A (S p) (X1 :: ctx) (lift_rec 1 X1 p :: f) (sort_term s2)
                    (ins_succ A p ctx f X1 Hins) HX2 wff') as IH2.
      assert (Hskip : skipn (S p) (X1 :: ctx) = skipn p ctx) by reflexivity.
      rewrite Hskip in IH2. rewrite Hcl_large in IH2.
      destruct (is_large_dec (skipn p ctx) A) as [HlA | HnlA].
      * destruct (is_large_dec (skipn p ctx) A) as [_|Hc] in IH2; [|contradiction].
        rewrite IH1, IH2. reflexivity.
      * destruct (is_large_dec (skipn p ctx) A) as [Hc|_] in IH2; [contradiction|].
        rewrite IH1, IH2. reflexivity.
Qed.

(** [nf]-free version of [extract_typ_L_lift_n_large]. *)
Lemma extract_typ_L_lift_n_large_typed : forall n f g, n <= length f -> skipn n f = g ->
  well_formed f ->
  forall v0 V0 (Hv0 : has_type g v0 V0),
  extract_typ_L f (lift n v0)
    = infrastructure.tlift (type_index f n) 0 (extract_typ_L g v0).
Proof.
  induction n as [| n' IH]; intros f g Hlen Hskip wff v0 V0 Hv0.
  - simpl in Hskip. subst g. rewrite type_index_zero. rewrite infrastructure.tlift_zero.
    rewrite lift_zero. reflexivity.
  - destruct f as [| T f']; [simpl in Hlen; lia |].
    simpl in Hskip. simpl in Hlen.
    assert (Hlen' : n' <= length f') by lia.
    assert (wff' : well_formed f') by (exact (wf_tail T f' wff)).
    assert (Hty : has_type f' (lift n' v0) (lift n' V0))
      by (apply weakening_at with g; auto).
    pose proof (IH f' g Hlen' Hskip wff' v0 V0 Hv0) as IHeq.
    pose proof (extract_typ_L_weaken_typed (lift n' v0) T 0 f' (T :: f') (lift n' V0)
                  (ins_zero T f') Hty wff) as Hw.
    simpl (skipn 0 f') in Hw.
    change (lift_rec 1 (lift n' v0) 0) with (lift 1 (lift n' v0)) in Hw.
    rewrite <- (simplify_lift v0 n') in Hw.
    simpl (type_index (T :: f') (S n')).
    destruct (is_large_dec f' T) as [Hl | Hs].
    + rewrite Hw. rewrite IHeq. rewrite type_index_zero.
      rewrite infrastructure.tlift_tlift. f_equal; lia.
    + rewrite Hw. exact IHeq.
Qed.

(** RAW large substitution, [nf]-free (drops [normal v0] from
    [extract_typ_L_large_subst_raw]; the [k = n] var-hit case uses
    [extract_typ_L_lift_n_large_typed] directly). *)
Lemma extract_typ_L_large_subst_gen : forall W g v0 V0
  (Hv0 : has_type g v0 V0) (wfg : well_formed g) (Hlg : is_large g V0),
  forall n e f B, substitute_in_environment v0 V0 n e f ->
  has_type e W B -> well_formed e -> well_formed f -> skipn n f = g ->
  type_expr e W = true ->
  infrastructure.ty_equiv
    (infrastructure.tsubst (extract_typ_L g v0) (type_index e n) (extract_typ_L e W))
    (extract_typ_L f (subst_rec v0 W n)).
Proof.
  induction W as [s0 | k | X1 IHX1 X2 IHX2 | X1 IHX1 X2 IHX2 | X1 IHX1 X2 IHX2];
    intros g v0 V0 Hv0 wfg Hlg n e f B Hse HW wfe wff Hskip Hte.
  - (* sort *)
    change (subst_rec v0 (sort_term s0) n) with (sort_term s0).
    simpl (extract_typ_L e (sort_term s0)). simpl (extract_typ_L f (sort_term s0)).
    simpl (infrastructure.tsubst _ _ syntax.dyn). apply infrastructure.ty_equiv_refl.
  - (* var k *)
    simpl in Hte.
    simpl (extract_typ_L e (terms.var k)). rewrite Hte.
    destruct (lt_eq_lt_dec n k) as [[Hlt | Heq] | Hgt].
    + (* k > n *)
      rewrite (subst_ref_gt v0 k n Hlt).
      simpl (extract_typ_L f (terms.var (Nat.pred k))).
      rewrite (type_binding_substitute_above g v0 V0 Hv0 wfg n e f Hse wfe wff Hskip k Hlt).
      rewrite Hte.
      assert (Hlt_idx : type_index e n < type_index e k).
      { apply (type_index_gt_of_type_binding e n k Hlt).
        exact (type_binding_at_subst_true g v0 V0 Hlg n e f Hse Hskip). }
      rewrite (tsubst_tvar_gt (extract_typ_L g v0) (type_index e n) (type_index e k) Hlt_idx).
      rewrite (type_index_substitute_above_large g v0 V0 Hv0 Hlg n e f Hse wfe wff Hskip k Hlt).
      apply infrastructure.ty_equiv_refl.
    + (* k = n : the substitution point (large) *)
      subst k. rewrite (subst_ref_eq v0 n).
      rewrite (tsubst_tvar_eq_idx (extract_typ_L g v0) (type_index e n)).
      pose proof (extract_typ_L_lift_n_large_typed n f g
                    (substitute_length_le v0 V0 n e f Hse) Hskip wff v0 V0 Hv0) as Hlift.
      rewrite (type_index_substitute_at g v0 V0 Hv0 wfg n e f Hse wfe wff Hskip) in Hlift.
      rewrite Hlift. apply infrastructure.ty_equiv_refl.
    + (* k < n *)
      rewrite (subst_ref_lt v0 k n Hgt).
      simpl (extract_typ_L f (terms.var k)).
      rewrite (type_binding_substitute_below g v0 V0 Hv0 wfg n e f Hse wfe wff Hskip k Hgt).
      rewrite Hte.
      assert (Hgt_idx : type_index e k < type_index e n).
      { apply (type_index_gt_of_type_binding e k n Hgt).
        exact Hte. }
      rewrite (tsubst_tvar_lt (extract_typ_L g v0) (type_index e n) (type_index e k) Hgt_idx).
      rewrite (type_index_substitute_below g v0 V0 Hv0 wfg n e f Hse wfe wff Hskip k Hgt).
      apply infrastructure.ty_equiv_refl.
  - (* lam X1 X2 *)
    apply (inversion_has_type_abs
             (infrastructure.ty_equiv
                (infrastructure.tsubst (extract_typ_L g v0) (type_index e n) (extract_typ_L e (lam X1 X2)))
                (extract_typ_L f (subst_rec v0 (lam X1 X2) n)))
             e X1 X2 B HW).
    intros s1 s2 T'' HX1 HX2 HT'' Hconv.
    assert (Hte2 : type_expr (X1 :: e) X2 = true) by (simpl in Hte; exact Hte).
    change (subst_rec v0 (lam X1 X2) n)
      with (lam (subst_rec v0 X1 n) (subst_rec v0 X2 (S n))).
    assert (HX1_f : has_type f (subst_rec v0 X1 n) (sort_term s1)).
    { change (sort_term s1) with (subst_rec v0 (sort_term s1) n).
      exact (has_type_substitute_weakening g v0 V0 Hv0 e X1 (sort_term s1) HX1 f n Hse wff Hskip). }
    assert (Hcl_eq : classifier (subst_rec v0 X1 n) = classifier X1).
    { pose proof (classifier_iff_is_large_typed X1 e s1 HX1) as Hcl_orig.
      pose proof (classifier_iff_is_large_typed (subst_rec v0 X1 n) f s1 HX1_f) as Hcl_sub.
      destruct (classifier X1) eqn:HclX1; destruct (classifier (subst_rec v0 X1 n)) eqn:HclS;
        try reflexivity; exfalso.
      - assert (Hlarge_f : is_large f (subst_rec v0 X1 n)).
        { apply (has_type_substitute_weakening g v0 V0 Hv0 e X1 (sort_term kind)
                   (fst Hcl_orig eq_refl) f n Hse wff Hskip). }
        pose proof (snd Hcl_sub Hlarge_f) as Habs. discriminate.
      - assert (Hlarge_e : is_large e X1).
        { exact (is_large_substitute_inv g v0 V0 Hv0 e X1 s1 HX1 f n Hse wff Hskip
                   (fst Hcl_sub eq_refl)). }
        pose proof (snd Hcl_orig Hlarge_e) as Habs. discriminate. }
    assert (wff' : well_formed (subst_rec v0 X1 n :: f)) by (apply wf_var with s1; exact HX1_f).
    assert (wfe' : well_formed (X1 :: e)) by (apply wf_var with s1; exact HX1).
    pose proof (IHX2 g v0 V0 Hv0 wfg Hlg (S n) (X1 :: e) (subst_rec v0 X1 n :: f) T''
                  (@sub_succ v0 V0 e f n X1 Hse) HX2 wfe' wff' Hskip Hte2) as IH2.
    simpl (extract_typ_L e (lam X1 X2)). simpl (extract_typ_L f (lam _ _)).
    rewrite Hcl_eq.
    simpl (type_index (X1 :: e) (S n)) in IH2.
    destruct (classifier X1) eqn:HclX1e.
    + assert (HlX1 : is_large e X1) by (exact (fst (classifier_iff_is_large_typed X1 e s1 HX1) HclX1e)).
      destruct (is_large_dec e X1) as [_ | Hbad]; [| exfalso; exact (Hbad HlX1)].
      rewrite (extract_kind_L_large_subst_raw X1 g v0 V0 Hv0 wfg n e f s1 Hse HX1 wfe wff Hskip HclX1e).
      simpl (infrastructure.tsubst _ _ (syntax.tyabs _ _)).
      apply ty_equiv_tyabs_cong. exact IH2.
    + assert (HnlX1 : is_large e X1 -> False)
        by (intro HL; rewrite (snd (classifier_iff_is_large_typed X1 e s1 HX1) HL) in HclX1e; discriminate).
      destruct (is_large_dec e X1) as [Hbad | _]; [exfalso; exact (HnlX1 Hbad) |].
      exact IH2.
  - (* app X1 X2 *)
    apply (inversion_has_type_app
             (infrastructure.ty_equiv
                (infrastructure.tsubst (extract_typ_L g v0) (type_index e n) (extract_typ_L e (terms.app X1 X2)))
                (extract_typ_L f (subst_rec v0 (terms.app X1 X2) n)))
             e X1 X2 B HW).
    intros V Ur Hu Hv Hconv.
    assert (Hte1 : type_expr e X1 = true) by (simpl in Hte; exact Hte).
    change (subst_rec v0 (terms.app X1 X2) n)
      with (terms.app (subst_rec v0 X1 n) (subst_rec v0 X2 n)).
    simpl (extract_typ_L e (terms.app X1 X2)). simpl (extract_typ_L f (terms.app _ _)).
    rewrite Hte1.
    rewrite (type_expr_subst_gen X1 g v0 V0 Hv0 wfg n e f (prod V Ur) Hse Hu wfe wff Hskip).
    rewrite (type_expr_subst_gen X2 g v0 V0 Hv0 wfg n e f V Hse Hv wfe wff Hskip).
    rewrite Hte1.
    pose proof (IHX1 g v0 V0 Hv0 wfg Hlg n e f (prod V Ur) Hse Hu wfe wff Hskip Hte1) as IH1.
    destruct (type_expr e X2) eqn:HeX2.
    + pose proof (IHX2 g v0 V0 Hv0 wfg Hlg n e f V Hse Hv wfe wff Hskip HeX2) as IH2.
      simpl (infrastructure.tsubst _ _ (syntax.tyapp _ _)).
      apply ty_equiv_tyapp_cong; [exact IH1 | exact IH2].
    + exact IH1.
  - (* prod X1 X2 *)
    apply (inversion_has_type_prod
             (infrastructure.ty_equiv
                (infrastructure.tsubst (extract_typ_L g v0) (type_index e n) (extract_typ_L e (prod X1 X2)))
                (extract_typ_L f (subst_rec v0 (prod X1 X2) n)))
             e X1 X2 B HW).
    intros s1 s2 HX1 HX2 Hconv.
    assert (Hte1 : type_expr e X1 = true)
      by (apply (snd (type_expr_iff e X1 (sort_term s1) HX1)); left; exists s1; reflexivity).
    assert (Hte2 : type_expr (X1 :: e) X2 = true)
      by (apply (snd (type_expr_iff (X1 :: e) X2 (sort_term s2) HX2)); left; exists s2; reflexivity).
    change (subst_rec v0 (prod X1 X2) n)
      with (prod (subst_rec v0 X1 n) (subst_rec v0 X2 (S n))).
    assert (HX1_f : has_type f (subst_rec v0 X1 n) (sort_term s1)).
    { change (sort_term s1) with (subst_rec v0 (sort_term s1) n).
      exact (has_type_substitute_weakening g v0 V0 Hv0 e X1 (sort_term s1) HX1 f n Hse wff Hskip). }
    assert (Hcl_eq : classifier (subst_rec v0 X1 n) = classifier X1).
    { pose proof (classifier_iff_is_large_typed X1 e s1 HX1) as Hcl_orig.
      pose proof (classifier_iff_is_large_typed (subst_rec v0 X1 n) f s1 HX1_f) as Hcl_sub.
      destruct (classifier X1) eqn:HclX1; destruct (classifier (subst_rec v0 X1 n)) eqn:HclS;
        try reflexivity; exfalso.
      - assert (Hlarge_f : is_large f (subst_rec v0 X1 n)).
        { apply (has_type_substitute_weakening g v0 V0 Hv0 e X1 (sort_term kind)
                   (fst Hcl_orig eq_refl) f n Hse wff Hskip). }
        pose proof (snd Hcl_sub Hlarge_f) as Habs. discriminate.
      - assert (Hlarge_e : is_large e X1).
        { exact (is_large_substitute_inv g v0 V0 Hv0 e X1 s1 HX1 f n Hse wff Hskip
                   (fst Hcl_sub eq_refl)). }
        pose proof (snd Hcl_orig Hlarge_e) as Habs. discriminate. }
    assert (wff' : well_formed (subst_rec v0 X1 n :: f)) by (apply wf_var with s1; exact HX1_f).
    assert (wfe' : well_formed (X1 :: e)) by (apply wf_var with s1; exact HX1).
    pose proof (IHX1 g v0 V0 Hv0 wfg Hlg n e f (sort_term s1) Hse HX1 wfe wff Hskip Hte1) as IH1.
    pose proof (IHX2 g v0 V0 Hv0 wfg Hlg (S n) (X1 :: e) (subst_rec v0 X1 n :: f) (sort_term s2)
                  (@sub_succ v0 V0 e f n X1 Hse) HX2 wfe' wff' Hskip Hte2) as IH2.
    simpl (extract_typ_L e (prod X1 X2)). simpl (extract_typ_L f (prod _ _)).
    rewrite Hcl_eq.
    simpl (type_index (X1 :: e) (S n)) in IH2.
    destruct (classifier X1) eqn:HclX1e.
    + assert (HlX1 : is_large e X1) by (exact (fst (classifier_iff_is_large_typed X1 e s1 HX1) HclX1e)).
      destruct (is_large_dec e X1) as [_ | Hbad]; [| exfalso; exact (Hbad HlX1)].
      rewrite (extract_kind_L_large_subst_raw X1 g v0 V0 Hv0 wfg n e f s1 Hse HX1 wfe wff Hskip HclX1e).
      simpl (infrastructure.tsubst _ _ (syntax.all _ _)).
      apply ty_equiv_all_cong. exact IH2.
    + assert (HnlX1 : is_large e X1 -> False)
        by (intro HL; rewrite (snd (classifier_iff_is_large_typed X1 e s1 HX1) HL) in HclX1e; discriminate).
      destruct (is_large_dec e X1) as [Hbad | _]; [exfalso; exact (HnlX1 Hbad) |].
      simpl (infrastructure.tsubst _ _ (syntax.arrow _ _)).
      apply ty_equiv_arrow_cong; [exact IH1 | exact IH2].
Qed.

(** RAW small substitution, [nf]-free: for a SMALL substitutee the two extractions
    are SYNTACTICALLY equal (no target β is created).  Simpler than
    [substitution_simulation.extract_typ_L_small_subst] because with no [nf] the
    body's context binder is exactly [subst_rec v0 X1 n :: f], matching the IH. *)
Lemma extract_typ_L_small_subst_raw : forall W,
  forall g v0 V0 (Hv0: has_type g v0 V0) (wfg: well_formed g) (Hsm: is_large g V0 -> False),
  forall n e f B, substitute_in_environment v0 V0 n e f ->
  has_type e W B -> well_formed e -> well_formed f -> skipn n f = g ->
  type_expr e W = true ->
  extract_typ_L e W = extract_typ_L f (subst_rec v0 W n).
Proof.
  induction W as [s0 | k | X1 IHX1 X2 IHX2 | X1 IHX1 X2 IHX2 | X1 IHX1 X2 IHX2];
    intros g v0 V0 Hv0 wfg Hsm n e f B Hse HW wfe wff Hskip Hte.
  - (* sort *)
    change (subst_rec v0 (sort_term s0) n) with (sort_term s0). reflexivity.
  - (* var k *)
    simpl in Hte.
    simpl (subst_rec v0 (terms.var k) n).
    destruct (lt_eq_lt_dec n k) as [[Hlt | Heq] | Hgt].
    + (* k > n *)
      simpl (extract_typ_L e (terms.var k)). simpl (extract_typ_L f (terms.var (Nat.pred k))).
      rewrite (type_binding_substitute_above g v0 V0 Hv0 wfg n e f Hse wfe wff Hskip k Hlt).
      rewrite Hte.
      rewrite (type_index_substitute_above g v0 V0 Hv0 wfg Hsm n e f Hse wfe wff Hskip k Hlt).
      reflexivity.
    + (* k = n : impossible, small point is not a type binding *)
      subst k. exfalso.
      rewrite (type_binding_at_subst_false g v0 V0 Hsm n e f Hse Hskip) in Hte. discriminate.
    + (* k < n *)
      simpl (extract_typ_L e (terms.var k)). simpl (extract_typ_L f (terms.var k)).
      rewrite (type_binding_substitute_below g v0 V0 Hv0 wfg n e f Hse wfe wff Hskip k Hgt).
      rewrite Hte.
      rewrite (type_index_substitute_below g v0 V0 Hv0 wfg n e f Hse wfe wff Hskip k Hgt).
      reflexivity.
  - (* lam X1 X2 *)
    apply (inversion_has_type_abs
             (extract_typ_L e (lam X1 X2) = extract_typ_L f (subst_rec v0 (lam X1 X2) n))
             e X1 X2 B HW).
    intros s1 s2 T'' HX1 HX2 HT'' Hconv.
    assert (Hte2 : type_expr (X1 :: e) X2 = true) by (simpl in Hte; exact Hte).
    change (subst_rec v0 (lam X1 X2) n)
      with (lam (subst_rec v0 X1 n) (subst_rec v0 X2 (S n))).
    assert (HX1_f : has_type f (subst_rec v0 X1 n) (sort_term s1)).
    { change (sort_term s1) with (subst_rec v0 (sort_term s1) n).
      exact (has_type_substitute_weakening g v0 V0 Hv0 e X1 (sort_term s1) HX1 f n Hse wff Hskip). }
    assert (Hcl_eq : classifier (subst_rec v0 X1 n) = classifier X1).
    { pose proof (classifier_iff_is_large_typed X1 e s1 HX1) as Hcl_orig.
      pose proof (classifier_iff_is_large_typed (subst_rec v0 X1 n) f s1 HX1_f) as Hcl_sub.
      destruct (classifier X1) eqn:HclX1; destruct (classifier (subst_rec v0 X1 n)) eqn:HclS;
        try reflexivity; exfalso.
      - assert (Hlarge_f : is_large f (subst_rec v0 X1 n)).
        { apply (has_type_substitute_weakening g v0 V0 Hv0 e X1 (sort_term kind)
                   (fst Hcl_orig eq_refl) f n Hse wff Hskip). }
        pose proof (snd Hcl_sub Hlarge_f) as Habs. discriminate.
      - assert (Hlarge_e : is_large e X1).
        { exact (is_large_substitute_inv g v0 V0 Hv0 e X1 s1 HX1 f n Hse wff Hskip
                   (fst Hcl_sub eq_refl)). }
        pose proof (snd Hcl_orig Hlarge_e) as Habs. discriminate. }
    assert (wff' : well_formed (subst_rec v0 X1 n :: f)) by (apply wf_var with s1; exact HX1_f).
    assert (wfe' : well_formed (X1 :: e)) by (apply wf_var with s1; exact HX1).
    pose proof (IHX2 g v0 V0 Hv0 wfg Hsm (S n) (X1 :: e) (subst_rec v0 X1 n :: f) T''
                  (@sub_succ v0 V0 e f n X1 Hse) HX2 wfe' wff' Hskip Hte2) as IH2.
    simpl (extract_typ_L e (lam X1 X2)). simpl (extract_typ_L f (lam _ _)).
    rewrite Hcl_eq.
    destruct (classifier X1) eqn:HclX1e.
    + rewrite (extract_kind_L_large_subst_raw X1 g v0 V0 Hv0 wfg n e f s1 Hse HX1 wfe wff Hskip HclX1e).
      f_equal. exact IH2.
    + exact IH2.
  - (* app X1 X2 *)
    apply (inversion_has_type_app
             (extract_typ_L e (terms.app X1 X2) = extract_typ_L f (subst_rec v0 (terms.app X1 X2) n))
             e X1 X2 B HW).
    intros V Ur Hu Hv Hconv.
    assert (Hte1 : type_expr e X1 = true) by (simpl in Hte; exact Hte).
    change (subst_rec v0 (terms.app X1 X2) n)
      with (terms.app (subst_rec v0 X1 n) (subst_rec v0 X2 n)).
    simpl (extract_typ_L e (terms.app X1 X2)). simpl (extract_typ_L f (terms.app _ _)).
    rewrite Hte1.
    rewrite (type_expr_subst_gen X1 g v0 V0 Hv0 wfg n e f (prod V Ur) Hse Hu wfe wff Hskip).
    rewrite (type_expr_subst_gen X2 g v0 V0 Hv0 wfg n e f V Hse Hv wfe wff Hskip).
    rewrite Hte1.
    pose proof (IHX1 g v0 V0 Hv0 wfg Hsm n e f (prod V Ur) Hse Hu wfe wff Hskip Hte1) as IH1.
    destruct (type_expr e X2) eqn:HeX2.
    + pose proof (IHX2 g v0 V0 Hv0 wfg Hsm n e f V Hse Hv wfe wff Hskip HeX2) as IH2.
      rewrite IH1. rewrite IH2. reflexivity.
    + rewrite IH1. reflexivity.
  - (* prod X1 X2 *)
    apply (inversion_has_type_prod
             (extract_typ_L e (prod X1 X2) = extract_typ_L f (subst_rec v0 (prod X1 X2) n))
             e X1 X2 B HW).
    intros s1 s2 HX1 HX2 Hconv.
    assert (Hte1 : type_expr e X1 = true)
      by (apply (snd (type_expr_iff e X1 (sort_term s1) HX1)); left; exists s1; reflexivity).
    assert (Hte2 : type_expr (X1 :: e) X2 = true)
      by (apply (snd (type_expr_iff (X1 :: e) X2 (sort_term s2) HX2)); left; exists s2; reflexivity).
    change (subst_rec v0 (prod X1 X2) n)
      with (prod (subst_rec v0 X1 n) (subst_rec v0 X2 (S n))).
    assert (HX1_f : has_type f (subst_rec v0 X1 n) (sort_term s1)).
    { change (sort_term s1) with (subst_rec v0 (sort_term s1) n).
      exact (has_type_substitute_weakening g v0 V0 Hv0 e X1 (sort_term s1) HX1 f n Hse wff Hskip). }
    assert (Hcl_eq : classifier (subst_rec v0 X1 n) = classifier X1).
    { pose proof (classifier_iff_is_large_typed X1 e s1 HX1) as Hcl_orig.
      pose proof (classifier_iff_is_large_typed (subst_rec v0 X1 n) f s1 HX1_f) as Hcl_sub.
      destruct (classifier X1) eqn:HclX1; destruct (classifier (subst_rec v0 X1 n)) eqn:HclS;
        try reflexivity; exfalso.
      - assert (Hlarge_f : is_large f (subst_rec v0 X1 n)).
        { apply (has_type_substitute_weakening g v0 V0 Hv0 e X1 (sort_term kind)
                   (fst Hcl_orig eq_refl) f n Hse wff Hskip). }
        pose proof (snd Hcl_sub Hlarge_f) as Habs. discriminate.
      - assert (Hlarge_e : is_large e X1).
        { exact (is_large_substitute_inv g v0 V0 Hv0 e X1 s1 HX1 f n Hse wff Hskip
                   (fst Hcl_sub eq_refl)). }
        pose proof (snd Hcl_orig Hlarge_e) as Habs. discriminate. }
    assert (wff' : well_formed (subst_rec v0 X1 n :: f)) by (apply wf_var with s1; exact HX1_f).
    assert (wfe' : well_formed (X1 :: e)) by (apply wf_var with s1; exact HX1).
    pose proof (IHX1 g v0 V0 Hv0 wfg Hsm n e f (sort_term s1) Hse HX1 wfe wff Hskip Hte1) as IH1.
    pose proof (IHX2 g v0 V0 Hv0 wfg Hsm (S n) (X1 :: e) (subst_rec v0 X1 n :: f) (sort_term s2)
                  (@sub_succ v0 V0 e f n X1 Hse) HX2 wfe' wff' Hskip Hte2) as IH2.
    simpl (extract_typ_L e (prod X1 X2)). simpl (extract_typ_L f (prod _ _)).
    rewrite Hcl_eq.
    destruct (classifier X1) eqn:HclX1e.
    + rewrite (extract_kind_L_large_subst_raw X1 g v0 V0 Hv0 wfg n e f s1 Hse HX1 wfe wff Hskip HclX1e).
      f_equal. exact IH2.
    + f_equal; [exact IH1 | exact IH2].
Qed.

(** ** Lemma 2: [extract_typ_L] respects source reduction up to [ty_equiv]

    Extraction is invariant, up to target definitional equality, under source
    reduction of a well-sorted type-level term to its normal form.  Proved by a
    plain SINGLE-STEP invariance lemma (structural induction on [reduces_once])
    chained over [W ->* nf W].  Every abs/tabs and arrow/all decision is driven by
    the reduction-stable [is_large]/[classifier] agreement
    ([classifier_reduces_once]), every kind annotation by the reduction-stable
    [extract_kind_L] ([extract_kind_L_reduces_once_large]), every context-binder
    reduction by [extract_typ_L_swap], and the two β steps by
    [extract_typ_L_large_subst_gen] / [extract_typ_L_small_subst_raw] (the RAW,
    [nf]-free substitution lemmas above). *)

(** Single-step invariance of [extract_typ_L] up to [ty_equiv]. *)
Lemma extract_typ_L_reduces_once_equiv : forall W W', reduces_once W W' ->
  forall e B, has_type e W B -> type_expr e W = true ->
  infrastructure.ty_equiv (extract_typ_L e W) (extract_typ_L e W').
Proof.
  intros W W' Hr.
  induction Hr as
    [ bM bN bT
    | dM dM' HrdM IHd dN
    | bM bM' HrbM IHb bN
    | lu lu' Hrlu IHlu lv
    | ra ra' Hrra IHra rf
    | pl pl' Hrpl IHpl pr
    | pc pc' Hrpc IHpc pd ];
    intros e B HW Hte.
  - (* beta: W = app (lam bT bM) bN, W' = subst bN bM *)
    apply (inversion_has_type_app _ e (lam bT bM) bN B HW).
    intros V Ur Hlam Harg Hconv.
    apply (inversion_has_type_abs _ e bT bM (prod V Ur) Hlam).
    intros s1 s2 T' HT HM HT'sort Hconv2.
    assert (HTV : convertible bT V)
      by (exact (inversion_convertible_product_left bT V T' Ur Hconv2)).
    assert (wfe : well_formed e) by (eapply has_type_well_formed; exact HT).
    assert (wfTe : well_formed (bT :: e)) by (apply wf_var with s1; exact HT).
    assert (HNT : has_type e bN bT)
      by (exact (type_conv e bN V bT Harg (sym_convertible _ _ HTV) s1 HT)).
    assert (Htlam : type_expr e (lam bT bM) = true) by (exact Hte).
    assert (Hte_M : type_expr (bT :: e) bM = true) by (exact Htlam).
    rewrite extract_typ_L_app_eq. rewrite extract_typ_L_lam_eq. rewrite Htlam.
    destruct (type_expr e bN) eqn:HteN.
    + (* large argument: target β then large raw substitution *)
      assert (HLT : is_large e bT).
      { apply (is_large_conv e V bT s1 (sym_convertible _ _ HTV) HT).
        destruct (fst (type_expr_iff e bN V Harg) HteN) as [[sv Hsv] | HLV].
        - subst V. destruct sv.
          + exfalso. exact (inversion_has_type_convertible_kind e bT (sort_term s1) HTV HT).
          + apply type_prop. eapply has_type_well_formed; exact Harg.
          + apply type_set. eapply has_type_well_formed; exact Harg.
        - exact HLV. }
      assert (HclT : classifier bT = true) by (exact (classifier_complete_typed bT e s1 HT HLT)).
      rewrite HclT.
      eapply infrastructure.ty_equiv_trans.
      * apply infrastructure.ty_equiv_beta.
      * pose proof (extract_typ_L_large_subst_gen bM e bN bT HNT wfe HLT 0 (bT :: e) e T'
                      (sub_zero bN bT e) HM wfTe wfe eq_refl Hte_M) as Hsub.
        rewrite type_index_zero in Hsub.
        exact Hsub.
    + (* small argument: raw small substitution, syntactic equality *)
      assert (HsmT : is_large e bT -> False).
      { intro HLT.
        assert (Hnot : ({sv : sort & V = sort_term sv} + is_large e V) -> False)
          by (intro Hc; rewrite (snd (type_expr_iff e bN V Harg) Hc) in HteN; discriminate).
        destruct (type_case e bN V Harg) as [[sV HV] | HVk].
        - apply Hnot. right. exact (is_large_conv e bT V sV HTV HV HLT).
        - apply Hnot. left. exists kind. exact HVk. }
      assert (HclT : classifier bT = false).
      { destruct (classifier bT) eqn:C; [| reflexivity]. exfalso.
        exact (HsmT (fst (classifier_iff_is_large_typed bT e s1 HT) C)). }
      rewrite HclT.
      rewrite (extract_typ_L_small_subst_raw bM e bN bT HNT wfe HsmT 0 (bT :: e) e T'
                 (sub_zero bN bT e) HM wfTe wfe eq_refl Hte_M).
      apply infrastructure.ty_equiv_refl.
  - (* abs_reduces_left: W = lam dM dN, W' = lam dM' dN (domain reduces) *)
    apply (inversion_has_type_abs _ e dM dN B HW).
    intros s1 s2 T' HdM HdN HT'sort Hconv.
    rewrite !extract_typ_L_lam_eq.
    assert (Hcl : classifier dM = classifier dM')
      by (exact (classifier_reduces_once dM dM' e s1 HdM HrdM)).
    rewrite <- Hcl.
    assert (Hswap : extract_typ_L (dM :: e) dN = extract_typ_L (dM' :: e) dN).
    { apply (extract_typ_L_swap dM dM' (one_step_reduces _ _ HrdM) dN nil e T'). simpl. exact HdN. }
    destruct (classifier dM) eqn:CdM.
    + assert (Hs1 : s1 = kind) by (exact (classifier_sound dM e s1 HdM CdM)). subst s1.
      rewrite (extract_kind_L_reduces_once_large dM e dM' HdM HrdM).
      rewrite Hswap. apply infrastructure.ty_equiv_refl.
    + rewrite Hswap. apply infrastructure.ty_equiv_refl.
  - (* abs_reduces_right: W = lam bN bM, W' = lam bN bM' (body reduces) *)
    apply (inversion_has_type_abs _ e bN bM B HW).
    intros s1 s2 T' HbN HbM HT'sort Hconv.
    rewrite !extract_typ_L_lam_eq.
    assert (Hte_body : type_expr (bN :: e) bM = true) by (exact Hte).
    pose proof (IHb (bN :: e) T' HbM Hte_body) as IHbody.
    destruct (classifier bN) eqn:CbN.
    + apply ty_equiv_tyabs_cong. exact IHbody.
    + exact IHbody.
  - (* app_reduces_left: W = app lu lv, W' = app lu' lv (head reduces) *)
    apply (inversion_has_type_app _ e lu lv B HW).
    intros V Ur Hlu Hlv Hconv.
    rewrite !extract_typ_L_app_eq.
    assert (Hlu_te : type_expr e lu = true) by (exact Hte).
    assert (Hlu'_te : type_expr e lu' = true)
      by (rewrite <- (type_expr_reduces_once e lu lu' (prod V Ur) Hlu Hrlu); exact Hlu_te).
    rewrite Hlu_te, Hlu'_te.
    pose proof (IHlu e (prod V Ur) Hlu Hlu_te) as IHhead.
    destruct (type_expr e lv) eqn:Hlv_te.
    + apply ty_equiv_tyapp_l_cong. exact IHhead.
    + exact IHhead.
  - (* app_reduces_right: W = app rf ra, W' = app rf ra' (argument reduces) *)
    apply (inversion_has_type_app _ e rf ra B HW).
    intros V Ur Hrf Hra Hconv.
    rewrite !extract_typ_L_app_eq.
    assert (Hrf_te : type_expr e rf = true) by (exact Hte).
    rewrite Hrf_te.
    assert (Hra_eq : type_expr e ra = type_expr e ra')
      by (exact (type_expr_reduces_once e ra ra' V Hra Hrra)).
    rewrite <- Hra_eq.
    destruct (type_expr e ra) eqn:Hra_te.
    + pose proof (IHra e V Hra Hra_te) as IHarg.
      apply ty_equiv_tyapp_r_cong. exact IHarg.
    + apply infrastructure.ty_equiv_refl.
  - (* prod_reduces_left: W = prod pl pr, W' = prod pl' pr (domain reduces) *)
    apply (inversion_has_type_prod _ e pl pr B HW).
    intros s1 s2 Hpl Hpr Hconv.
    rewrite !extract_typ_L_prod_eq.
    assert (Hcl : classifier pl = classifier pl')
      by (exact (classifier_reduces_once pl pl' e s1 Hpl Hrpl)).
    rewrite <- Hcl.
    assert (Hswap : extract_typ_L (pl :: e) pr = extract_typ_L (pl' :: e) pr).
    { apply (extract_typ_L_swap pl pl' (one_step_reduces _ _ Hrpl) pr nil e (sort_term s2)).
      simpl. exact Hpr. }
    destruct (classifier pl) eqn:Cpl.
    + assert (Hs1 : s1 = kind) by (exact (classifier_sound pl e s1 Hpl Cpl)). subst s1.
      rewrite (extract_kind_L_reduces_once_large pl e pl' Hpl Hrpl).
      rewrite Hswap. apply infrastructure.ty_equiv_refl.
    + assert (Hpl_te : type_expr e pl = true)
        by (apply (snd (type_expr_iff e pl (sort_term s1) Hpl)); left; exists s1; reflexivity).
      pose proof (IHpl e (sort_term s1) Hpl Hpl_te) as IHdom.
      rewrite Hswap. apply ty_equiv_arrow_l_cong. exact IHdom.
  - (* prod_reduces_right: W = prod pd pc, W' = prod pd pc' (codomain reduces) *)
    apply (inversion_has_type_prod _ e pd pc B HW).
    intros s1 s2 Hpd Hpc Hconv.
    rewrite !extract_typ_L_prod_eq.
    assert (Hpc_te : type_expr (pd :: e) pc = true)
      by (apply (snd (type_expr_iff (pd :: e) pc (sort_term s2) Hpc)); left; exists s2; reflexivity).
    pose proof (IHpc (pd :: e) (sort_term s2) Hpc Hpc_te) as IHcod.
    destruct (classifier pd) eqn:Cpd.
    + apply ty_equiv_all_cong. exact IHcod.
    + apply ty_equiv_arrow_r_cong. exact IHcod.
Qed.

(** Chain the single-step invariance over a multi-step reduction. *)
Lemma extract_typ_L_reduces_equiv : forall e W Wend B,
  reduces W Wend -> has_type e W B -> type_expr e W = true ->
  infrastructure.ty_equiv (extract_typ_L e W) (extract_typ_L e Wend).
Proof.
  intros e W Wend B Hr. revert B. induction Hr as [M | M P N Hstep Hrs IH]; intros B HW Hte.
  - apply infrastructure.ty_equiv_refl.
  - assert (HP : has_type e P B) by (eapply subject_reduction_theorem; [exact Hrs | exact HW]).
    assert (HteP : type_expr e P = true).
    { apply (snd (type_expr_iff e P B HP)).
      exact (fst (type_expr_iff e M B HW) Hte). }
    eapply infrastructure.ty_equiv_trans.
    + exact (IH B HW Hte).
    + exact (extract_typ_L_reduces_once_equiv P N Hstep e B HP HteP).
Qed.

(** [extract_typ_L] on a term agrees, up to [ty_equiv], with [extract_typ_L] on its normal form. *)
Lemma extract_typ_L_reduces_nf_equiv : forall e W B (sn : strongly_normalizing W),
  has_type e W B -> type_expr e W = true ->
  infrastructure.ty_equiv (extract_typ_L e W) (extract_typ_L e (nf W sn)).
Proof.
  intros e W B sn HW Hte.
  exact (extract_typ_L_reduces_equiv e W (nf W sn) B (nf_reduces W sn) HW Hte).
Qed.

(** ** Final commutation lemma (was the last admitted goal)

    Assembled from lemma 1 ([extract_typ_L_large_subst_raw]) at the top level
    ([n = 0]) and lemma 2 ([extract_typ_L_reduces_nf_equiv]) to collapse the
    residual source substitution to its normal form. *)
Lemma extract_typ_tsubst_coc_equiv :
  forall e V0 v0 (Hv0 : has_type e v0 V0) (Hlarge : is_large e V0)
  Ur s (HUr : has_type (V0 :: e) Ur (sort_term s)) snv0 snUr snSub,
  infrastructure.ty_equiv
    (infrastructure.tsubst (extract_typ e v0 snv0) 0 (extract_typ (V0 :: e) Ur snUr))
    (extract_typ e (terms.subst v0 Ur) snSub).
Proof.
  intros e V0 v0 Hv0 Hlarge Ur s HUr snv0 snUr snSub.
  unfold extract_typ.
  assert (wfe : well_formed e) by (eapply has_type_well_formed; exact Hv0).
  assert (wfVe : well_formed (V0 :: e)) by (eapply has_type_well_formed; exact HUr).
  (* normal forms are well-typed, normal, and type-level *)
  assert (Hnv0_ty : has_type e (nf v0 snv0) V0)
    by (eapply subject_reduction_theorem; [apply nf_reduces | exact Hv0]).
  assert (HnUr_ty : has_type (V0 :: e) (nf Ur snUr) (sort_term s))
    by (eapply subject_reduction_theorem; [apply nf_reduces | exact HUr]).
  assert (Hnnv0 : normal (nf v0 snv0)) by apply nf_normal.
  assert (HteUr : type_expr (V0 :: e) (nf Ur snUr) = true)
    by (apply (snd (type_expr_iff (V0 :: e) (nf Ur snUr) (sort_term s) HnUr_ty));
        left; exists s; reflexivity).
  (* Step 1: raw structural commutation at n = 0 (substitute [nf v0] into [nf Ur]). *)
  pose proof (extract_typ_L_large_subst_raw (nf Ur snUr) e (nf v0 snv0) V0
                Hnv0_ty wfe Hnnv0 Hlarge 0 (V0 :: e) e (sort_term s)
                (sub_zero (nf v0 snv0) V0 e) HnUr_ty wfVe wfe eq_refl HteUr) as Step1.
  rewrite type_index_zero in Step1.
  (* [Step1 : ty_equiv (tsubst (extract_typ_L e (nf v0)) 0 (extract_typ_L (V0::e) (nf Ur)))
                       (extract_typ_L e (subst_rec (nf v0) (nf Ur) 0))] *)
  (* Step 2: collapse the residual raw substitution to its normal form. *)
  assert (HS_ty : has_type e (subst_rec (nf v0 snv0) (nf Ur snUr) 0) (sort_term s)).
  { change (sort_term s) with (subst_rec (nf v0 snv0) (sort_term s) 0).
    exact (substitution e V0 (nf Ur snUr) (sort_term s) HnUr_ty (nf v0 snv0) Hnv0_ty). }
  assert (HteS : type_expr e (subst_rec (nf v0 snv0) (nf Ur snUr) 0) = true)
    by (apply (snd (type_expr_iff e (subst_rec (nf v0 snv0) (nf Ur snUr) 0) (sort_term s) HS_ty));
        left; exists s; reflexivity).
  pose proof (strong_normalization e (subst_rec (nf v0 snv0) (nf Ur snUr) 0) (sort_term s) HS_ty) as snS.
  pose proof (extract_typ_L_reduces_nf_equiv e (subst_rec (nf v0 snv0) (nf Ur snUr) 0)
                (sort_term s) snS HS_ty HteS) as Step2.
  (* bridge: [nf (subst_rec (nf v0) (nf Ur) 0)] = [nf (subst v0 Ur)] via conversion *)
  assert (Hconv : convertible (subst_rec (nf v0 snv0) (nf Ur snUr) 0) (terms.subst v0 Ur)).
  { unfold terms.subst.
    apply convertible_convertible_subst.
    - apply sym_convertible. apply nf_conv.
    - apply sym_convertible. apply nf_conv. }
  rewrite (nf_respects_conv (subst_rec (nf v0 snv0) (nf Ur snUr) 0) (terms.subst v0 Ur)
             snS snSub Hconv) in Step2.
  eapply infrastructure.ty_equiv_trans; [exact Step1 |].
  exact Step2.
Qed.

(** The main type-preservation theorem: the extraction of a well-typed CoC term is
    a well-typed Fω+blame term, at its extracted type in the extracted context. *)
Theorem extract_well_typed : forall e t T (H: has_type e t T)
  (w: well_formed e) (sn: strongly_normalizing T),
  typing.typing (extract_ctx e w) (extract e t T H) (extract_typ e T sn).
Proof.
  fix IH 4.
  intros e t T H w sn.
  destruct H as [ e0 w0 | e0 w0 | e0 w0 v T0 il
                | e0 T0 s1 HT M U s2 HU HM | e0 v0 V0 Hv u Ur Hu
                | e0 T0 s1 HT U s2 HU | e0 t0 U0 V0 Htu Hconv s0 HV ].
  - (* prop *) cbn [extract]. unfold extract_typ. rewrite (nf_sort kind sn).
    cbn [extract_typ_L]. apply typing_dyn_token.
  - (* set *) cbn [extract]. unfold extract_typ. rewrite (nf_sort kind sn).
    cbn [extract_typ_L]. apply typing_dyn_token.
  - (* var *) destruct il as [u Heq Hnth]. cbn [extract].
    destruct (well_formed_sort_lift v e0 T0 w0
                (existT2 _ _ u Heq Hnth)) as [sT HT0sort].
    replace (extract_typ e0 T0 sn)
      with (extract_typ e0 T0 (sn_of_type e0 (terms.var v) T0
              (typing.type_var e0 (w0) v T0 (existT2 _ _ u Heq Hnth))))
      by (apply extract_typ_pi).
    destruct (is_large_dec e0 T0) as [HL | HL].
    + eapply typing_coerce.
      * apply extract_ctx_wf.
      * apply typing.typing_blame. apply typing.wf_dyn.
      * apply (extract_typ_wf_sort e0 T0 sT HT0sort w).
    + eapply typing_coerce.
      * apply extract_ctx_wf.
      * assert (Hnl : (is_large (skipn (S v) e0) u -> False)).
        { intro Hc. apply HL. rewrite Heq.
          apply (snd (is_large_item_lift e0 v u (w0) Hnth)). exact Hc. }
        apply typing.typing_var.
        rewrite (extract_ctx_pi e0 w (w0)).
        exact (extract_ctx_lookup_term e0 v u Hnth Hnl (w0)).
      * apply (extract_typ_wf_sort e0 T0 sT HT0sort w).
  - (* abs *)
    pose (HT0p := HT).
    pose (HUp := HU).
    pose (sndU := strong_normalization (T0 :: e0) U (sort_term s2) HUp).
    pose (w' := (has_type_t_well_formed_t (T0 :: e0) M U HM)).
    cbn [extract].
    destruct (is_large_dec e0 T0) as [HL | HL].
    + rewrite (extract_typ_prod_large e0 T0 U s1 s2 HT0p HUp sn
                 (strong_normalization e0 T0 (sort_term s1) HT0p) sndU HL).
      apply typing.typing_tabs.
      pose proof (IH (T0 :: e0) M U HM w' sndU) as HM'.
      rewrite (extract_ctx_cons_large T0 e0 w' w
                 (strong_normalization e0 T0 (sort_term s1) HT0p) HL) in HM'.
      exact HM'.
    + rewrite (extract_typ_prod_small e0 T0 U s1 s2 HT0p HUp sn
                 (strong_normalization e0 T0 (sort_term s1) HT0p) sndU HL).
      apply typing.typing_abs.
      * apply (extract_typ_wf_sort e0 T0 s1 HT w).
      * pose proof (IH (T0 :: e0) M U HM w' sndU) as HM'.
        rewrite (extract_ctx_cons_small T0 e0 w' w
                   (strong_normalization e0 T0 (sort_term s1) HT0p) HL) in HM'.
        exact HM'.
  - (* app *)
    pose (Hup := Hu).
    pose (Hvp := Hv).
    destruct (type_case e0 u (terms.prod V0 Ur) Hup) as [[sp Hsp] | Hbad]; [| discriminate Hbad].
    apply (inversion_has_type_prod _ _ _ _ _ Hsp). intros sV sUr HV0p HUrp Hconvp.
    pose (sn_prod := sn_of_type e0 u (terms.prod V0 Ur) Hup).
    cbn [extract].
    replace (extract_typ e0 (terms.subst v0 Ur) sn)
      with (extract_typ e0 (terms.subst v0 Ur)
              (sn_of_type e0 (terms.app u v0) (terms.subst v0 Ur)
                 (typing.type_app e0 v0 V0 Hvp u Ur Hup)))
      by (apply extract_typ_pi).
    assert (Hsub_ty : has_type e0 (terms.subst v0 Ur) (sort_term sUr)).
    { change (sort_term sUr) with (terms.subst v0 (sort_term sUr)).
      exact (substitution e0 V0 Ur (sort_term sUr) HUrp v0 Hvp). }
    destruct (is_large_dec e0 V0) as [HL | HL].
    + (* large (type) argument: type the raw [tapp] at its natural type, then
         convert to the expected type via [typing_conv] (target Fω conversion). *)
      pose (snV := strong_normalization e0 V0 (sort_term sV) HV0p).
      pose (snv := strong_normalization e0 v0 V0 Hvp).
      pose (snUr := sn_of_prod_cod e0 u V0 Ur Hup).
      assert (Htapp :
        typing.typing (extract_ctx e0 w)
          (syntax.tapp (extract e0 u (terms.prod V0 Ur) Hu)
                       (extract_typ e0 v0 snv))
          (infrastructure.tsubst (extract_typ e0 v0 snv) 0
             (extract_typ (V0 :: e0) Ur snUr))).
      { eapply typing.typing_tapp.
        - pose proof (IH e0 u (terms.prod V0 Ur) Hu w sn_prod) as HHu.
          rewrite (extract_typ_prod_large e0 V0 Ur sV sUr HV0p HUrp sn_prod
                     snV snUr HL) in HHu.
          exact HHu.
        - exact (extract_typ_wf_large e0 v0 V0 Hvp HL w snV snv). }
      eapply typing.typing_conv.
      * exact Htapp.
      * apply typing.deq_ty_equiv.
        -- exact (typing_metatheory.typing_regular _ _ _ (extract_ctx_wf e0 w) Htapp).
        -- apply (extract_typ_wf_sort e0 (terms.subst v0 Ur) sUr Hsub_ty w).
        -- apply (extract_typ_tsubst_coc_equiv e0 V0 v0 Hvp HL Ur sUr HUrp).
      * apply (extract_typ_wf_sort e0 (terms.subst v0 Ur) sUr Hsub_ty w).
    + eapply typing_coerce.
      * apply extract_ctx_wf.
      * eapply typing.typing_app.
        -- pose proof (IH e0 u (terms.prod V0 Ur) Hu w sn_prod) as HHu.
           rewrite (extract_typ_prod_small e0 V0 Ur sV sUr HV0p HUrp sn_prod
                      (strong_normalization e0 V0 (sort_term sV) HV0p)
                      (sn_of_prod_cod e0 u V0 Ur Hup) HL) in HHu.
           exact HHu.
        -- exact (IH e0 v0 V0 Hv w (strong_normalization e0 V0 (sort_term sV) HV0p)).
      * apply (extract_typ_wf_sort e0 (terms.subst v0 Ur) sUr Hsub_ty w).
  - (* prod *) cbn [extract]. unfold extract_typ. rewrite (nf_sort s2 sn).
    cbn [extract_typ_L]. apply typing_dyn_token.
  - (* conv *)
    cbn [extract].
    replace (extract_typ e0 V0 sn)
      with (extract_typ e0 V0 (strong_normalization e0 V0 (sort_term s0)
              (HV)))
      by (apply extract_typ_pi).
    eapply typing_coerce.
    + apply extract_ctx_wf.
    + exact (IH e0 t0 U0 Htu w (sn_of_type e0 t0 U0 (Htu))).
    + apply (extract_typ_wf_sort e0 V0 s0 HV w).
Qed.
