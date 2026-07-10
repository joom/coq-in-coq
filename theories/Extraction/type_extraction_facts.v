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


(** The commutation of type extraction with CoC source type-substitution
    up to target Fω definitional equality ([extract_typ_tsubst_coc_equiv]) is
    proved downstream in [well_typed.v], where all the type-namespace
    substitution / weakening / [ty_equiv] machinery of
    [substitution_simulation.v] is in scope. *)

(** ** Kind regularity of type extraction

    We prove the stronger statement that for a NORMAL, type-level source term [t]
    of type [B], the extraction [extract_typ_L e t] is well-kinded at the target
    kind [extract_kind B] (the kind skeleton of its source type).  The [sort]
    case ([B] a sort, giving [KStar]) then follows.  The crux is the [app] case:
    aligning the head's [KArr]-domain kind with the argument's kind, and matching
    the result kind [extract_kind_L (nf Ur)] with the expected
    [extract_kind (subst v Ur)] via kind-skeleton subst-invariance. *)

(** [classifier] and [extract_kind_L] are purely syntactic, hence invariant under
    lifting (local copies; the downstream [substitution_simulation] has the same). *)
Lemma classifier_lift_k : forall T n k, classifier (lift_rec n T k) = classifier T.
Proof.
  induction T as [s | v | T1 IHT1 T2 IHT2 | T1 IHT1 T2 IHT2 | T1 IHT1 T2 IHT2];
    intros n k; simpl; try destruct (le_gt_dec k v); simpl; auto.
Qed.

Lemma extract_kind_L_lift_k : forall T n k, extract_kind_L (lift_rec n T k) = extract_kind_L T.
Proof.
  induction T as [s | v | T1 IHT1 T2 IHT2 | T1 IHT1 T2 IHT2 | T1 IHT1 T2 IHT2];
    intros n k; simpl; try destruct (le_gt_dec k v); simpl; auto.
  rewrite classifier_lift_k. destruct (classifier T1); [f_equal|]; auto.
Qed.

(** Substituting a variable reflects largeness of a type (self-contained variant
    for this file, using the upstream [has_type_substitute_weakening]). *)
Lemma is_large_subst_inv_k : forall g v V (Hv: has_type g v V)
  e T s (HT: has_type e T (sort_term s))
  f n (Hse: substitute_in_environment v V n e f) (wff: well_formed f)
  (Hskip: skipn n f = g),
  is_large f (terms.subst_rec v T n) -> is_large e T.
Proof.
  intros g v V Hv e T s HT f n Hse wff Hskip Hlarge. unfold is_large in *.
  pose proof (has_type_substitute_weakening g v V Hv e T (sort_term s) HT f n Hse wff Hskip) as HT_sub.
  change (terms.subst_rec v (sort_term s) n) with (sort_term s) in HT_sub.
  assert (Hconv : convertible (sort_term kind) (sort_term s)).
  { apply (has_type_unique_sort f (terms.subst_rec v T n)); [exact Hlarge | exact HT_sub]. }
  apply confluence.convertible_sort in Hconv. subst s. exact HT.
Qed.

(** The kind skeleton [extract_kind_L (nf _)] of a normal [classifier] is
    invariant under substitution (of any [v0]/[V0]): a classifier is built from
    [sort_term]/[prod] only, so substitution only touches domains, whose
    largeness (hence [classifier]) is preserved. *)
Lemma extract_kind_L_subst_inv : forall W,
  forall g v0 V0 (Hv0: has_type g v0 V0) (wfg: well_formed g),
  forall n e f s, substitute_in_environment v0 V0 n e f ->
  has_type e W (sort_term s) -> well_formed e -> well_formed f -> skipn n f = g ->
  normal W -> classifier W = true ->
  forall snsub, extract_kind_L (nf (subst_rec v0 W n) snsub) = extract_kind_L W.
Proof.
  induction W as [s0 | k | X1 IHX1 X2 IHX2 | X1 IHX1 X2 IHX2 | X1 IHX1 X2 IHX2];
    intros g v0 V0 Hv0 wfg n e f s Hse HW wfe wff Hskip Hnorm Hcw; simpl in Hcw.
  - (* sort *) intro snsub. simpl. rewrite nf_sort. reflexivity.
  - (* var *) discriminate.
  - (* lam *) discriminate.
  - (* app *) discriminate.
  - (* prod X1 X2 *)
    intro snsub.
    assert (HnX1 : normal X1)
      by (intros u Hu; exact (Hnorm _ (prod_reduces_left X1 u Hu X2))).
    assert (HnX2 : normal X2)
      by (intros u Hu; exact (Hnorm _ (prod_reduces_right X2 u Hu X1))).
    apply (inversion_has_type_prod
             (extract_kind_L (nf (subst_rec v0 (prod X1 X2) n) snsub) = extract_kind_L (prod X1 X2))
             e X1 X2 (sort_term s) HW).
    intros s1 s2 HX1 HX2 Hconv.
    change (subst_rec v0 (prod X1 X2) n)
      with (prod (subst_rec v0 X1 n) (subst_rec v0 X2 (S n))) in snsub |- *.
    assert (snX1 : strongly_normalizing (subst_rec v0 X1 n))
      by (apply (subterm_sn _ snsub); apply sub_no_bind; apply sub_no_binder_prod).
    assert (snX2 : strongly_normalizing (subst_rec v0 X2 (S n)))
      by (apply (subterm_sn _ snsub); apply sub_bind with (subst_rec v0 X1 n); apply sub_binder_prod).
    rewrite (nf_prod (subst_rec v0 X1 n) (subst_rec v0 X2 (S n)) snsub snX1 snX2).
    simpl.
    assert (HX1_f : has_type f (subst_rec v0 X1 n) (sort_term s1)).
    { change (sort_term s1) with (subst_rec v0 (sort_term s1) n).
      exact (has_type_substitute_weakening g v0 V0 Hv0 e X1 (sort_term s1) HX1 f n Hse wff Hskip). }
    assert (Hcl_eq : classifier (nf (subst_rec v0 X1 n) snX1) = classifier X1).
    { assert (Hcl_orig : iffT (classifier X1 = true) (is_large e X1))
        by (exact (classifier_iff_is_large_nf X1 e s1 HX1 HnX1)).
      assert (Hcl_sub : iffT (classifier (nf (subst_rec v0 X1 n) snX1) = true)
                              (is_large f (subst_rec v0 X1 n)))
        by (exact (classifier_nf_is_large f (subst_rec v0 X1 n) snX1 s1 HX1_f)).
      destruct (classifier X1) eqn:HclX1; destruct (classifier (nf (subst_rec v0 X1 n) snX1)) eqn:HclS;
        try reflexivity; exfalso.
      - assert (Hlarge_f : is_large f (subst_rec v0 X1 n)).
        { apply (has_type_substitute_weakening g v0 V0 Hv0 e X1 (sort_term kind)
                   (fst Hcl_orig eq_refl) f n Hse wff Hskip). }
        pose proof (snd Hcl_sub Hlarge_f) as Habs. discriminate.
      - assert (Hlarge_e : is_large e X1).
        { exact (is_large_subst_inv_k g v0 V0 Hv0 e X1 s1 HX1 f n Hse wff Hskip
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
      * exact (IHX1 g v0 V0 Hv0 wfg n e f s1 Hse HX1 wfe wff Hskip HnX1 eq_refl snX1).
      * exact (IHX2 g v0 V0 Hv0 wfg (S n) (X1 :: e) (subst_rec v0 X1 n :: f) s2
                 (@sub_succ v0 V0 e f n X1 Hse) HX2 wfe' wff' Hskip HnX2 Hcw2 snX2).
    + exact (IHX2 g v0 V0 Hv0 wfg (S n) (X1 :: e) (subst_rec v0 X1 n :: f) s2
               (@sub_succ v0 V0 e f n X1 Hse) HX2 wfe' wff' Hskip HnX2 Hcw2 snX2).
Qed.

(** [lookup_kind] ignores [has_type] (term) bindings entirely (no shift), so
    inserting one anywhere in a context leaves every type-variable lookup fixed. *)
Lemma lookup_kind_insert_has_type : forall D A g n,
  typing.lookup_kind (D ++ typing.has_type A :: g) n = typing.lookup_kind (D ++ g) n.
Proof.
  induction D as [|b D IH]; intros A g n; simpl.
  - reflexivity.
  - destruct b as [A' | K' | K' A'].
    + apply IH.
    + destruct n; [reflexivity | apply IH].
    + destruct n; [reflexivity | apply IH].
Qed.

(** Hence a [has_type] binding is invisible to kinding and can be removed. *)
Lemma wf_typ_strengthen_has_type : forall Gamma X K,
  typing.wf_typ Gamma X K ->
  forall D A g, Gamma = D ++ typing.has_type A :: g -> typing.wf_typ (D ++ g) X K.
Proof.
  intros Gamma X K Hwf.
  induction Hwf as
    [ Gamma n K Hlk
    | Gamma A0 B0 HA IHA HB IHB
    | Gamma K0 A0 HA IHA
    | Gamma K1 K2 A0 HA IHA
    | Gamma F0 A0 K1 K2 HF IHF HA IHA
    | Gamma ];
    intros D A g Heq; subst Gamma.
  - apply typing.wf_tvar. rewrite <- (lookup_kind_insert_has_type D A g n). exact Hlk.
  - apply typing.wf_arrow; [ exact (IHA D A g eq_refl) | exact (IHB D A g eq_refl) ].
  - apply typing.wf_all. exact (IHA (typing.has_kind K0 :: D) A g eq_refl).
  - apply typing.wf_tyabs. exact (IHA (typing.has_kind K1 :: D) A g eq_refl).
  - eapply typing.wf_tyapp; [ exact (IHF D A g eq_refl) | exact (IHA D A g eq_refl) ].
  - apply typing.wf_dyn.
Qed.

(** Head form of the strengthening lemma (remove a [has_type] binder at the top). *)
Lemma wf_typ_strengthen_has_type_hd : forall A g X K,
  typing.wf_typ (typing.has_type A :: g) X K -> typing.wf_typ g X K.
Proof.
  intros A g X K Hwf.
  exact (wf_typ_strengthen_has_type _ X K Hwf nil A g eq_refl).
Qed.

(** The main kind-regularity statement: a normal, type-level source term of type
    [B] extracts to a target type of the [B]-kind skeleton. *)
Lemma extract_typ_L_wf_kind : forall t e (w : well_formed e) B (snB : strongly_normalizing B),
  normal t -> has_type e t B -> type_expr e t = true ->
  typing.wf_typ (extract_ctx e w) (extract_typ_L e t) (extract_kind B snB).
Proof.
  induction t as [s0 | k | T IHT M IHM | u IHu a IHa | T IHT U IHU];
    intros e w B snB Hnorm Hty Hte.
  - (* sort_term s0 : extracts to dyn : KStar *)
    simpl (extract_typ_L e (sort_term s0)).
    assert (Hconv : convertible B (sort_term kind)).
    { destruct s0.
      - exfalso. exact (inversion_has_type_kind e B Hty).
      - exact (inversion_has_type_prop e B Hty).
      - exact (inversion_has_type_set e B Hty). }
    assert (Hkb : extract_kind B snB = syntax.KStar).
    { unfold extract_kind.
      rewrite (nf_respects_conv B (sort_term kind) snB
                 (sn_normal (sort_term kind) (normal_sort kind)) Hconv).
      rewrite nf_sort. reflexivity. }
    rewrite Hkb. apply typing.wf_dyn.
  - (* var k : extracts to tvar (type_index e k) *)
    assert (Htb : type_binding e k = true) by exact Hte.
    (* recover the binding [u] at [k] and its largeness from [type_binding] *)
    unfold type_binding in Htb.
    destruct (nth_error e k) as [u |] eqn:Hnth; [| discriminate].
    destruct (is_large_dec (skipn (S k) e) u) as [Hlu | _]; [| discriminate].
    (* B is convertible to the lifted binding type *)
    apply (inversion_has_type_ref
             (typing.wf_typ (extract_ctx e w) (extract_typ_L e (terms.var k)) (extract_kind B snB))
             e B k Hty).
    intros u' Hnth' Hconv.
    assert (u' = u) by (rewrite Hnth in Hnth'; injection Hnth' as ->; reflexivity). subst u'.
    (* extract_typ_L e (var k) = tvar (type_index e k) *)
    simpl (extract_typ_L e (terms.var k)). unfold type_binding.
    rewrite Hnth. destruct (is_large_dec (skipn (S k) e) u) as [Hlu2 | Hns]; [| contradiction].
    apply typing.wf_tvar.
    (* kind matches the binding's extracted kind *)
    pose (snu := strong_normalization (skipn (S k) e) u (sort_term kind) Hlu).
    rewrite (extract_ctx_lookup_kind e k u Hnth Hlu2 w snu).
    f_equal.
    assert (snlift : strongly_normalizing (lift (S k) u)).
    { apply (strong_normalization e (lift (S k) u) (sort_term kind)).
      destruct (is_large_item_lift e k u w Hnth) as [_ back]. exact (back Hlu). }
    transitivity (extract_kind (lift (S k) u) snlift).
    + unfold extract_kind.
      change (lift (S k) u) with (lift_rec (S k) u 0).
      rewrite (nf_lift u snu (S k) 0 snlift).
      rewrite extract_kind_L_lift_k. reflexivity.
    + apply extract_kind_conv. apply sym_convertible. exact Hconv.
  - (* lam T M : a type-level lambda (type family) *)
    apply (inversion_has_type_abs
             (typing.wf_typ (extract_ctx e w) (extract_typ_L e (lam T M)) (extract_kind B snB))
             e T M B Hty).
    intros s1 s2 Tcod HT HM HTcod Hconv.
    assert (HnT : normal T)
      by (intros x Hx; exact (Hnorm _ (abs_reduces_left T x Hx M))).
    assert (HnM : normal M)
      by (intros x Hx; exact (Hnorm _ (abs_reduces_right M x Hx T))).
    assert (wfTe : well_formed (T :: e)) by (apply wf_var with s1; exact HT).
    (* type_expr (lam T M) = type_expr (T::e) M *)
    assert (HteM : type_expr (T :: e) M = true) by exact Hte.
    (* B is convertible to prod T Tcod; compute its kind skeleton *)
    assert (snProd : strongly_normalizing (prod T Tcod))
      by (apply (strong_normalization e (prod T Tcod) (sort_term s2));
          apply type_prod with s1; [exact HT | exact HTcod]).
    assert (HkB : extract_kind B snB = extract_kind (prod T Tcod) snProd)
      by (apply extract_kind_conv; apply sym_convertible; exact Hconv).
    rewrite HkB.
    pose (snTcod := strong_normalization (T :: e) Tcod (sort_term s2) HTcod).
    pose (snM_ty := snTcod).
    simpl (extract_typ_L e (lam T M)).
    destruct (classifier T) eqn:Hcl.
    + (* large domain: tyabs *)
      assert (HlT : is_large e T)
        by (unfold is_large; rewrite <- (classifier_sound T e s1 HT Hcl); exact HT).
      pose (snT := sn_of_binding T e wfTe).
      pose proof (IHM (T :: e) wfTe Tcod snTcod HnM HM HteM) as IHbody.
      rewrite (extract_ctx_cons_large T e wfTe w snT HlT) in IHbody.
      assert (HkTeq : extract_kind T snT = extract_kind_L T).
      { unfold extract_kind. rewrite (nf_normal_eq T snT HnT). reflexivity. }
      rewrite HkTeq in IHbody.
      (* goal kind: extract_kind (prod T Tcod) = KArr (extract_kind_L T) (extract_kind Tcod) *)
      assert (HkProd : extract_kind (prod T Tcod) snProd
                       = syntax.KArr (extract_kind_L T) (extract_kind Tcod snTcod)).
      { unfold extract_kind.
        rewrite (nf_prod T Tcod snProd (sn_normal T HnT) snTcod).
        simpl. rewrite (nf_normal_eq T (sn_normal T HnT) HnT). rewrite Hcl. reflexivity. }
      rewrite HkProd.
      apply typing.wf_tyabs. exact IHbody.
    + (* small domain: drop the binder *)
      assert (HnlT : is_large e T -> False)
        by (intro HL; rewrite (snd (classifier_iff_is_large_nf T e s1 HT HnT) HL) in Hcl; discriminate).
      pose (snT := sn_of_binding T e wfTe).
      pose proof (IHM (T :: e) wfTe Tcod snTcod HnM HM HteM) as IHbody.
      rewrite (extract_ctx_cons_small T e wfTe w snT HnlT) in IHbody.
      assert (HkProd : extract_kind (prod T Tcod) snProd = extract_kind Tcod snTcod).
      { unfold extract_kind.
        rewrite (nf_prod T Tcod snProd (sn_normal T HnT) snTcod).
        simpl. rewrite (nf_normal_eq T (sn_normal T HnT) HnT). rewrite Hcl. reflexivity. }
      rewrite HkProd.
      exact (wf_typ_strengthen_has_type_hd _ _ _ _ IHbody).
  - (* app u a : a neutral type-family application *)
    apply (inversion_has_type_app
             (typing.wf_typ (extract_ctx e w) (extract_typ_L e (terms.app u a)) (extract_kind B snB))
             e u a B Hty).
    intros V Ur Hu Ha Hconv.
    assert (HnU : normal u)
      by (intros x Hx; exact (Hnorm _ (app_reduces_left u x Hx a))).
    assert (HnA : normal a)
      by (intros x Hx; exact (Hnorm _ (app_reduces_right a x Hx u))).
    (* type_expr (app u a) = type_expr e u *)
    assert (HteU : type_expr e u = true) by exact Hte.
    (* u : prod V Ur ; the product is a kind (large), so V : s1, Ur : kind in V::e *)
    destruct (type_case e u (prod V Ur) Hu) as [[sp Hsp] | Hbad]; [| discriminate Hbad].
    apply (inversion_has_type_prod
             (typing.wf_typ (extract_ctx e w) (extract_typ_L e (terms.app u a)) (extract_kind B snB))
             e V Ur (sort_term sp) Hsp).
    intros s1 s2 HV HUr Hconvsp.
    (* B convertible to subst a Ur *)
    assert (snsubUr : strongly_normalizing (subst a Ur)).
    { apply (sn_of_type e (terms.app u a) (subst a Ur)).
      exact (type_app e a V Ha u Ur Hu). }
    assert (HkB : extract_kind B snB = extract_kind (subst a Ur) snsubUr)
      by (apply extract_kind_conv; exact Hconv).
    rewrite HkB.
    (* SN of prod V Ur and its kind skeleton *)
    assert (snV : strongly_normalizing V) by (exact (strong_normalization e V (sort_term s1) HV)).
    assert (wfVe : well_formed (V :: e)) by (apply wf_var with s1; exact HV).
    assert (snUr : strongly_normalizing Ur)
      by (exact (strong_normalization (V :: e) Ur (sort_term s2) HUr)).
    assert (snProd : strongly_normalizing (prod V Ur)) by (exact (sn_of_type e u (prod V Ur) Hu)).
    (* kind skeleton of subst a Ur equals that of Ur via classifier subst-invariance *)
    assert (HkSub : extract_kind (subst a Ur) snsubUr = extract_kind_L (nf Ur snUr)).
    { unfold extract_kind, terms.subst.
      (* reduce to substituting into the normal form nf Ur *)
      assert (Hred : reduces (subst_rec a Ur 0) (subst_rec a (nf Ur snUr) 0))
        by (apply reduces_subst_right; apply nf_reduces).
      assert (HnfUr_ty : has_type (V :: e) (nf Ur snUr) (sort_term s2))
        by (eapply subject_reduction_theorem; [apply nf_reduces | exact HUr]).
      assert (HnfUr_cl : classifier (nf Ur snUr) = true).
      { (* prod V Ur is large (its type sp = kind, since [app u a] is type-level) *)
        assert (Hsp_kind : sp = kind).
        { destruct (fst (type_expr_iff e u (prod V Ur) Hu) HteU) as [[sx Hsx] | Hlprod].
          - discriminate Hsx.
          - apply confluence.convertible_sort.
            exact (has_type_unique_sort e (prod V Ur) (sort_term sp) Hsp (sort_term kind) Hlprod). }
        subst sp.
        assert (HUr_large : is_large (V :: e) Ur) by (exact (is_large_prod_cod_inv e V Ur Hsp)).
        assert (Hs2kind : s2 = kind).
        { apply confluence.convertible_sort.
          exact (has_type_unique_sort (V :: e) Ur (sort_term s2) HUr (sort_term kind) HUr_large). }
        subst s2.
        exact (snd (classifier_iff_is_large_nf (nf Ur snUr) (V :: e) kind HnfUr_ty (nf_normal Ur snUr))
                 HnfUr_ty). }
      pose proof (strong_normalization (V :: e) (nf Ur snUr) (sort_term s2) HnfUr_ty) as snNfUr.
      assert (snSubNf : strongly_normalizing (subst_rec a (nf Ur snUr) 0))
        by (apply (strong_normalization e (subst_rec a (nf Ur snUr) 0) (sort_term s2));
            change (sort_term s2) with (subst_rec a (sort_term s2) 0);
            exact (substitution e V (nf Ur snUr) (sort_term s2) HnfUr_ty a Ha)).
      rewrite (nf_stable_star (subst_rec a Ur 0) (subst_rec a (nf Ur snUr) 0) snsubUr snSubNf Hred).
      rewrite (extract_kind_L_subst_inv (nf Ur snUr) e a V Ha w 0 (V :: e) e s2
                 (sub_zero a V e) HnfUr_ty wfVe w eq_refl (nf_normal Ur snUr) HnfUr_cl snSubNf).
      reflexivity. }
    (* now branch on the extraction shape *)
    simpl (extract_typ_L e (terms.app u a)).
    rewrite HteU.
    (* head IH: extract u : extract_kind (prod V Ur) *)
    pose proof (IHu e w (prod V Ur) snProd HnU Hu HteU) as IHhead.
    (* the head kind is a KArr since V is large-or-sort in the tyapp branch *)
    destruct (type_expr e a) eqn:HteA.
    + (* tyapp: argument is type-level, so V is large or a literal sort => classifier (nf V) = true *)
      assert (HclV : classifier (nf V snV) = true).
      { destruct (fst (type_expr_iff e a V Ha) HteA) as [[sx Hsx] | HlV].
        - (* V = sort_term sx *)
          subst V. rewrite (nf_normal_eq (sort_term sx) snV (normal_sort sx)). reflexivity.
        - (* V large *)
          exact (snd (classifier_nf_is_large e V snV s1 HV) HlV). }
      assert (HkHead : extract_kind (prod V Ur) snProd
                       = syntax.KArr (extract_kind V snV) (extract_kind_L (nf Ur snUr))).
      { unfold extract_kind.
        rewrite (nf_prod V Ur snProd snV snUr). simpl. rewrite HclV. reflexivity. }
      rewrite HkHead in IHhead.
      pose proof (IHa e w V snV HnA Ha HteA) as IHarg.
      rewrite HkSub.
      eapply typing.wf_tyapp; [ exact IHhead | exact IHarg ].
    + (* argument dropped: V is small, head kind = extract_kind_L (nf Ur) *)
      assert (HnlV : is_large e V -> False).
      { intro HL. assert (Habs : type_expr e a = true).
        { apply (snd (type_expr_iff e a V Ha)). right. exact HL. }
        rewrite Habs in HteA. discriminate. }
      assert (HclV : classifier (nf V snV) = false).
      { destruct (classifier (nf V snV)) eqn:E; [| reflexivity].
        exfalso. apply HnlV. exact (fst (classifier_nf_is_large e V snV s1 HV) E). }
      assert (HkHead : extract_kind (prod V Ur) snProd = extract_kind_L (nf Ur snUr)).
      { unfold extract_kind.
        rewrite (nf_prod V Ur snProd snV snUr). simpl. rewrite HclV. reflexivity. }
      rewrite HkHead in IHhead.
      rewrite HkSub. exact IHhead.
  - (* prod T U : extracts to all/arrow, always KStar (its type is a sort) *)
    apply (inversion_has_type_prod
             (typing.wf_typ (extract_ctx e w) (extract_typ_L e (prod T U)) (extract_kind B snB))
             e T U B Hty).
    intros s1 s2 HT HU Hconv.
    assert (HnT : normal T)
      by (intros x Hx; exact (Hnorm _ (prod_reduces_left T x Hx U))).
    assert (HnU : normal U)
      by (intros x Hx; exact (Hnorm _ (prod_reduces_right U x Hx T))).
    assert (wfTe : well_formed (T :: e)) by (apply wf_var with s1; exact HT).
    (* B convertible to sort_term s2 => kind is KStar *)
    assert (HkB : extract_kind B snB = syntax.KStar).
    { unfold extract_kind.
      rewrite (nf_respects_conv B (sort_term s2) snB
                 (sn_normal (sort_term s2) (normal_sort s2)) (sym_convertible _ _ Hconv)).
      rewrite nf_sort. reflexivity. }
    rewrite HkB.
    pose (sns2 := sn_normal (sort_term s2) (normal_sort s2)).
    pose (sns1 := sn_normal (sort_term s1) (normal_sort s1)).
    assert (HkKStar : forall sq (SN : strongly_normalizing (sort_term sq)),
              extract_kind (sort_term sq) SN = syntax.KStar)
      by (intros sq SN; unfold extract_kind; rewrite nf_sort; reflexivity).
    assert (HteU : type_expr (T :: e) U = true)
      by (apply (snd (type_expr_iff (T :: e) U (sort_term s2) HU)); left; exists s2; reflexivity).
    simpl (extract_typ_L e (prod T U)).
    destruct (classifier T) eqn:Hcl.
    + (* large domain: all *)
      assert (HlT : is_large e T)
        by (unfold is_large; rewrite <- (classifier_sound T e s1 HT Hcl); exact HT).
      pose (snT := sn_of_binding T e wfTe).
      pose proof (IHU (T :: e) wfTe (sort_term s2) sns2 HnU HU HteU) as IHbody.
      rewrite (HkKStar s2 sns2) in IHbody.
      rewrite (extract_ctx_cons_large T e wfTe w snT HlT) in IHbody.
      assert (HkTeq : extract_kind T snT = extract_kind_L T)
        by (unfold extract_kind; rewrite (nf_normal_eq T snT HnT); reflexivity).
      rewrite HkTeq in IHbody.
      apply typing.wf_all. exact IHbody.
    + (* small domain: arrow *)
      assert (HnlT : is_large e T -> False)
        by (intro HL; rewrite (snd (classifier_iff_is_large_nf T e s1 HT HnT) HL) in Hcl; discriminate).
      pose (snT := sn_of_binding T e wfTe).
      assert (HteT : type_expr e T = true)
        by (apply (snd (type_expr_iff e T (sort_term s1) HT)); left; exists s1; reflexivity).
      pose proof (IHT e w (sort_term s1) sns1 HnT HT HteT) as IHdom.
      rewrite (HkKStar s1 sns1) in IHdom.
      (* wait: IHdom kind uses sns1, KStar too *)
      pose proof (IHU (T :: e) wfTe (sort_term s2) sns2 HnU HU HteU) as IHbody.
      rewrite (HkKStar s2 sns2) in IHbody.
      rewrite (extract_ctx_cons_small T e wfTe w snT HnlT) in IHbody.
      apply typing.wf_arrow.
      * exact IHdom.
      * exact (wf_typ_strengthen_has_type_hd _ _ _ _ IHbody).
Qed.

(** Kind regularity of type extraction: a source type of some sort extracts to a
    well-kinded target type of kind [KStar].  Needed to discharge the [wf_typ]
    premise of [typing_conv] in [extract_well_typed]. *)
Lemma extract_typ_wf_sort :
  forall e T s (HT : has_type e T (sort_term s)) (w : well_formed e) sn,
  typing.wf_typ (extract_ctx e w) (extract_typ e T sn) syntax.KStar.
Proof.
  intros e T s HT w sn. unfold extract_typ.
  assert (Ht : has_type e (nf T sn) (sort_term s))
    by (eapply subject_reduction_theorem; [apply nf_reduces | exact HT]).
  assert (Hn : normal (nf T sn)) by apply nf_normal.
  assert (Hte : type_expr e (nf T sn) = true)
    by (apply (snd (type_expr_iff e (nf T sn) (sort_term s) Ht)); left; exists s; reflexivity).
  pose (snB := sn_normal (sort_term s) (normal_sort s)).
  assert (Hkb : extract_kind (sort_term s) snB = syntax.KStar)
    by (unfold extract_kind; rewrite nf_sort; reflexivity).
  rewrite <- Hkb.
  exact (extract_typ_L_wf_kind (nf T sn) e w (sort_term s) snB Hn Ht Hte).
Qed.

(** A source term whose type is itself large extracts to a target type at the
    kind skeleton of that source type.  This is the kinding premise needed by
    target type application. *)
Lemma extract_typ_wf_large :
  forall e t T (Ht : has_type e t T) (HL : is_large e T)
         (w : well_formed e) snT sn,
  typing.wf_typ (extract_ctx e w) (extract_typ e t sn) (extract_kind T snT).
Proof.
  intros e t T Ht HL w snT sn. unfold extract_typ.
  assert (Htnf : has_type e (nf t sn) T)
    by (eapply subject_reduction_theorem; [apply nf_reduces | exact Ht]).
  apply (extract_typ_L_wf_kind (nf t sn) e w T snT).
  - apply nf_normal.
  - exact Htnf.
  - apply (snd (type_expr_iff e (nf t sn) T Htnf)).
    right. exact HL.
Qed.

(** A well-formed CoC environment extracts to a well-formed target context.
    Large source bindings become kind bindings; small bindings carry the
    well-kinded extracted source type established above. *)
Lemma extract_ctx_wf : forall e (w : well_formed e),
  typing_metatheory.wf_ctx (extract_ctx e w).
Proof.
  induction e as [|T e IH]; intro w; simpl.
  - apply typing_metatheory.wf_ctx_nil.
  - destruct (is_large_dec e T) as [HL | Hsmall].
    + apply typing_metatheory.wf_ctx_kind.
      apply IH.
    + apply typing_metatheory.wf_ctx_type.
      * apply IH.
      * destruct (well_formed_sort 0 (T :: e) e eq_refl w T eq_refl) as [s HT].
        apply (extract_typ_wf_sort e T s HT (wf_tail T e w)).
Qed.
