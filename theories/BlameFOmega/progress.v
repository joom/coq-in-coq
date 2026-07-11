(** * BlameFOmega.progress: Progress.

    Proves that well-typed closed terms either are values, step, or are blame,
    for the (kind-regular, [defeq]-converting) target typing judgment.  The
    companion preservation theorem lives in [preservation.v]. *)

From Stdlib Require Import Arith Lia List Relations.
Import ListNotations.
From BlameFOmega Require Import syntax infrastructure semantics
  typing typing_metatheory ty_confluence.

(** ** Convertibility with well-kindedness witness

    [ty_conv_to g A C] records the accumulated [typing_conv] conversions of an
    inversion: either no conversion happened ([A = C]) or the two types are
    [defeq] and the target is well-kinded (exactly [typing_conv]'s premises). *)

Definition ty_conv_to (g : context) (A C : typ) : Prop :=
  A = C \/ (defeq g A C KStar /\ wf_typ g C KStar).

(** [typing_conv] packaged via [ty_conv_to]: retype [e] at [C] given it types at [A]. *)
Lemma apply_ty_conv_to : forall g e A C,
  typing g e A -> ty_conv_to g A C -> typing g e C.
Proof.
  intros g e A C Hty [<- | [Heq Hwf]].
  - exact Hty.
  - eapply typing_conv; eauto.
Qed.

(** [ty_conv_to] is reflexive. *)
Lemma ty_conv_to_refl : forall g A, ty_conv_to g A A.
Proof. left. reflexivity. Qed.

(** [ty_conv_to] composes with an extra [defeq] step, i.e. is transitive. *)
Lemma ty_conv_to_conv : forall g A B C,
  ty_conv_to g A B -> defeq g B C KStar -> wf_typ g C KStar -> ty_conv_to g A C.
Proof.
  intros g A B C [<- | [Heq1 _]] Heq2 Hwf; right; split; auto.
  eapply deq_trans; eauto.
Qed.

(** ** Inversion lemmas with convertibility *)

(** Inversion for [abs], through [typing_conv]. *)
Lemma typing_abs_inv2 : forall g t e C,
  typing g (abs t e) C ->
  exists B, ty_conv_to g (arrow t B) C /\ typing (has_type t :: g) e B
            /\ wf_typ g t KStar.
Proof.
  intros g t e C H. remember (abs t e) as tm eqn:Htm.
  induction H; try discriminate.
  - injection Htm as -> ->. exists t2. split; [left; reflexivity | split; assumption].
  - destruct (IHtyping Htm) as [B0 [Hconv [Hbody Hwft]]].
    exists B0. split; [eapply ty_conv_to_conv; eauto | split; assumption].
Qed.

(** Inversion for [tabs], through [typing_conv]. *)
Lemma typing_tabs_inv2 : forall g K e C,
  typing g (tabs K e) C ->
  exists B, ty_conv_to g (all K B) C /\ typing (has_kind K :: g) e B.
Proof.
  intros g K e C H. remember (tabs K e) as tm eqn:Htm.
  induction H; try discriminate.
  - injection Htm as -> ->. exists t. split; [left; reflexivity | assumption].
  - destruct (IHtyping Htm) as [B0 [Hconv Hbody]].
    exists B0. split; [eapply ty_conv_to_conv; eauto | assumption].
Qed.

(** Inversion for [app], through [typing_conv]. *)
Lemma typing_app_inv2 : forall g e1 e2 C,
  typing g (app e1 e2) C ->
  exists A B, ty_conv_to g B C /\ typing g e1 (arrow A B) /\ typing g e2 A.
Proof.
  intros g e1 e2 C H. remember (app e1 e2) as tm eqn:Htm.
  induction H; try discriminate.
  - injection Htm as -> ->. exists t1, t2. split; [left; reflexivity | split; assumption].
  - destruct (IHtyping Htm) as [A0 [B0 [Hconv [Hty1 Hty2]]]].
    exists A0, B0. split; [eapply ty_conv_to_conv; eauto | split; assumption].
Qed.

(** Inversion for [tapp], through [typing_conv]. *)
Lemma typing_tapp_inv2 : forall g e s C,
  typing g (tapp e s) C ->
  exists K t, ty_conv_to g (tsubst s 0 t) C /\ typing g e (all K t)
              /\ wf_typ g s K.
Proof.
  intros g e s C H. remember (tapp e s) as tm eqn:Htm.
  induction H; try discriminate.
  - injection Htm as -> ->. exists K, t. split; [left; reflexivity | split; assumption].
  - destruct (IHtyping Htm) as [K0 [t0 [Hconv [Hty Hwf]]]].
    exists K0, t0. split; [eapply ty_conv_to_conv; eauto | split; assumption].
Qed.

(** Inversion for [cast], through [typing_conv]. *)
Lemma typing_cast_inv2 : forall g e A B p C,
  typing g (cast e A B p) C ->
  ty_conv_to g B C /\ typing g e A /\ compat A B
  /\ wf_typ g A KStar /\ wf_typ g B KStar.
Proof.
  intros g e A B p C H. remember (cast e A B p) as tm eqn:Htm.
  induction H; try discriminate.
  - injection Htm as -> -> -> ->.
    repeat split; [left; reflexivity | assumption | assumption | assumption | assumption].
  - destruct (IHtyping Htm) as [Hconv [Hty [Hc [HwfA HwfB]]]].
    repeat split;
      [eapply ty_conv_to_conv; eauto | assumption | assumption | assumption | assumption].
Qed.

(** Inversion for [gnd], through [typing_conv]. *)
Lemma typing_gnd_inv2 : forall g e G C,
  typing g (gnd e G) C ->
  ty_conv_to g dyn C /\ typing g e G /\ ground G /\ wf_typ g G KStar.
Proof.
  intros g e G C H. remember (gnd e G) as tm eqn:Htm.
  induction H; try discriminate.
  - injection Htm as -> ->. inversion H0; subst.
    repeat split; [left; reflexivity | assumption | assumption | assumption].
  - destruct (IHtyping Htm) as [Hconv [Hty [Hg Hwf]]].
    repeat split;
      [eapply ty_conv_to_conv; eauto | assumption | assumption | assumption].
Qed.

(** Inversion for [nu], through [typing_conv]. *)
Lemma typing_nu_inv2 : forall g K A e C,
  typing g (nu K A e) C ->
  exists B, ty_conv_to g (tsubst A 0 B) C /\
            typing (has_def K A :: g) e B /\
            wf_typ g A K.
Proof.
  intros g K A e C H. remember (nu K A e) as tm eqn:Htm.
  induction H; try discriminate.
  - injection Htm as -> -> ->. exists B. split; [left; reflexivity | split; assumption].
  - destruct (IHtyping Htm) as [B0 [Hconv [Hty Hwf]]].
    exists B0. split; [eapply ty_conv_to_conv; eauto | split; assumption].
Qed.

(** Inversion for [is_gnd], through [typing_conv]. *)
Lemma typing_is_gnd_inv2 : forall g e G C,
  typing g (is_gnd e G) C ->
  ty_conv_to g (arrow dyn (arrow dyn dyn)) C /\
  typing g e dyn /\ wf_ground g G.
Proof.
  intros g e G C H. remember (is_gnd e G) as tm eqn:Htm.
  induction H; try discriminate.
  - injection Htm as -> ->. split; [left; reflexivity | split; assumption].
  - destruct (IHtyping Htm) as [Hconv [Hty Hground]].
    split; [eapply ty_conv_to_conv; eauto | split; assumption].
Qed.

(** ** Canonical forms

    [canonical_arrow]/[canonical_all] live in [typing_metatheory.v] (they only
    need the typing inversions and the [defeq] head-distinctness facts proved
    there); [canonical_dyn] is their [dyn]-typed sibling. *)

Lemma canonical_dyn : forall g v,
  value v -> typing g v dyn ->
  exists w G, v = gnd w G /\ value w /\ ground G.
Proof.
  intros g v Hv Hty. destruct Hv.
  - apply typing_abs_inv in Hty. destruct Hty as [B0 [Hconv _]].
    destruct Hconv as [Heq | Hdq];
      [discriminate | exfalso; eapply defeq_dyn_arrow; apply deq_sym; eauto].
  - apply typing_tabs_inv in Hty. destruct Hty as [B0 [Hconv _]].
    destruct Hconv as [Heq | Hdq];
      [discriminate | exfalso; eapply defeq_dyn_all; apply deq_sym; eauto].
  - apply typing_gnd_inv in Hty. destruct Hty as [_ [Hty' Hg]].
    eexists; eexists; repeat split; eauto.
Qed.

(** ** Context refinement: [has_kind] → [has_def]

    Refining a [has_kind K] binding into [has_def K A] preserves typing (the
    kinding/[defeq]/lookup transport lemmas live in [typing_metatheory.v]).
    The reverse direction is *false* for this judgment: erasing a definition
    forgets the [deq_def] equations [typing_conv] may have used. *)

Lemma typing_kind_to_def : forall G1 g K A e B,
  typing (G1 ++ has_kind K :: g) e B ->
  typing (G1 ++ has_def K A :: g) e B.
Proof.
  intros G1 g K A e B H.
  remember (G1 ++ has_kind K :: g) as g0 eqn:Hg. revert G1 Hg.
  induction H; intros G1 Hg; subst.
  - apply typing_var. rewrite <- lookup_term_kind_to_def. auto.
  - apply typing_abs;
      [ apply wf_typ_kind_to_def; auto
      | apply (IHtyping (has_type t1 :: G1)); reflexivity ].
  - eapply typing_app; eauto.
  - apply typing_tabs. apply (IHtyping (has_kind K0 :: G1)). reflexivity.
  - eapply typing_tapp; eauto. apply wf_typ_kind_to_def; auto.
  - eapply typing_cast; eauto; apply wf_typ_kind_to_def; auto.
  - apply typing_gnd; eauto.
    inversion H0; subst; constructor; [auto | apply wf_typ_kind_to_def; auto].
  - apply typing_is_gnd; eauto.
    inversion H0; subst; constructor; [auto | apply wf_typ_kind_to_def; auto].
  - apply typing_blame. apply wf_typ_kind_to_def; auto.
  - apply typing_nu.
    + apply (IHtyping (has_def K0 A0 :: G1)). reflexivity.
    + apply wf_typ_kind_to_def; auto.
  - eapply typing_conv;
      [ eauto
      | apply defeq_kind_to_def; auto
      | apply wf_typ_kind_to_def; auto ].
Qed.

(** ** Deciding executable compatibility (for COLLAPSE vs CONFLICT)

    Progress inverts [compat] for most cast cases; only the COLLAPSE/CONFLICT
    split (a [gnd]-wrapped value cast out of [dyn]) needs to *decide*
    [compat G B] for ground [G].  We build that from a few focused decision
    procedures. *)

(** Deciding [cast_form]. *)
Lemma cast_form_dec: forall A, {cast_form A} + {~ cast_form A}.
Proof.
  destruct A.
  - left; apply cf_neutral; apply neutral_tvar.
  - left; apply cf_arrow.
  - left; apply cf_all.
  - right; intro H; inversion H; subst;
      match goal with Hn: neutral _ |- _ => inversion Hn end.
  - destruct (neutral_dec (tyapp A1 A2)) as [Hn | Hn].
    + left; apply cf_neutral; exact Hn.
    + right; intro H; inversion H; subst; contradiction.
  - left; apply cf_dyn.
Qed.

(** Deciding [compat dyn B] (COLLAPSE from a [dyn] source). *)
Lemma compat_dyn_l_dec: forall B, {compat dyn B} + {~ compat dyn B}.
Proof.
  intro B. destruct (typ_eq_dec B dyn) as [->|Hnd]; [left; apply compat_refl|].
  destruct (cast_form_dec B) as [Hcf | Hncf].
  - left; apply compat_from_dyn; assumption.
  - right; intro Hc; inversion Hc; subst; try congruence; contradiction.
Qed.

(** Deciding [compat A dyn] (GROUND to [dyn]); recursion is on [ty_size] for
    the INSTANTIATE case ([tsubst dyn] preserves size). *)
Lemma compat_dyn_r_dec_aux: forall n A, ty_size A <= n -> {compat A dyn} + {~ compat A dyn}.
Proof.
  induction n as [|n IHn]; intros A Hn.
  - exfalso; pose proof (ty_size_pos A); lia.
  - destruct (typ_eq_dec A dyn) as [->|Hnd]; [left; apply compat_refl|].
    destruct A as [m | A1 A2 | K A0 | K A0 | A1 A2 | ].
    + left; eapply compat_to_dyn;
        [discriminate | intros K C; discriminate | apply gt_neutral; apply neutral_tvar | apply compat_refl].
    + (* arrow: need compat (arrow A1 A2) (arrow dyn dyn) *)
      destruct (compat_dyn_l_dec A1) as [Hc1|Hnc1].
      * assert (Hsz2: ty_size A2 <= n) by (simpl in Hn; pose proof (ty_size_pos A1); pose proof (ty_size_pos A2); lia).
        destruct (IHn A2 Hsz2) as [Hc2|Hnc2].
        -- left; eapply compat_to_dyn;
             [discriminate | intros K C; discriminate | apply gt_arrow | apply compat_arrow; assumption].
        -- right; intro Hc; inversion Hc; subst; try congruence.
           apply Hnc2.
           inversion H1; subst;
             [| exfalso; match goal with Hn': neutral (arrow _ _) |- _ => inversion Hn' end].
           inversion H2; subst; [apply compat_refl | assumption].
      * right; intro Hc; inversion Hc; subst; try congruence.
        apply Hnc1.
        inversion H1; subst;
          [| exfalso; match goal with Hn': neutral (arrow _ _) |- _ => inversion Hn' end].
        inversion H2; subst; [apply compat_refl | assumption].
    + destruct (kind_eq_dec K KStar) as [->|HK].
      * destruct (IHn (tsubst dyn 0 A0)) as [Hc|Hnc];
          [ rewrite tsubst_dyn_size; simpl in Hn; lia | | ].
        -- left; apply compat_instantiate; [intros K' B'; discriminate | exact Hc].
        -- right; intro Hc; inversion Hc; subst; try congruence;
             match goal with H: forall _ _, all _ _ <> all _ _ |- _ =>
               solve [eapply H; reflexivity] end.
      * right; intro Hc; inversion Hc; subst; try congruence;
          match goal with H: forall _ _, all _ _ <> all _ _ |- _ =>
            solve [eapply H; reflexivity] end.
    + right; intro Hc; inversion Hc; subst; try congruence;
        match goal with H: ground_tag (tyabs _ _) _ |- _ =>
          inversion H; subst; match goal with Hn': neutral _ |- _ => inversion Hn' end end.
    + destruct (neutral_dec (tyapp A1 A2)) as [Hne | Hnne].
      * left; eapply compat_to_dyn;
          [discriminate | intros K C; discriminate | apply gt_neutral; exact Hne | apply compat_refl].
      * right; intro Hc; inversion Hc; subst; try congruence;
          match goal with H: ground_tag (tyapp _ _) _ |- _ =>
            inversion H; subst; contradiction end.
    + exfalso; apply Hnd; reflexivity.
Qed.

(** Deciding [compat A dyn], unwrapping the fuel from [compat_dyn_r_dec_aux]. *)
Lemma compat_dyn_r_dec: forall A, {compat A dyn} + {~ compat A dyn}.
Proof. intro A. apply (compat_dyn_r_dec_aux (ty_size A)); lia. Qed.

(** Deciding [compat N B] for neutral [N] (recursion on [B]).  A neutral source
    relates only by [compat_refl] (to itself), [compat_to_dyn] (to [dyn]), or
    [compat_generalize] (to a [∀]); every other derivation forces [N] into a
    non-neutral shape, contradicting [neutral N].  [refute] discharges those. *)
Lemma compat_neutral_dec: forall B N, neutral N -> {compat N B} + {~ compat N B}.
Proof.
  (* after [inversion]/[subst], any surviving bad case rewrites [N] to a
     concrete non-neutral head, so [neutral N] becomes absurd. *)
  induction B as [m | B1 _ B2 _ | K B0 IHB0 | K B0 _ | B1 _ B2 _ | ];
    intros N HN.
  - (* B = tvar m *) destruct (typ_eq_dec N (tvar m)) as [->|Hne]; [left; apply compat_refl|].
    right; intro Hc; inversion Hc; subst; try congruence;
      match goal with H: neutral _ |- _ => solve [inversion H] end.
  - (* B = arrow B1 B2 *)
    right; intro Hc; inversion Hc; subst;
      match goal with H: neutral _ |- _ => solve [inversion H] end.
  - (* B = all K B0: generalize *)
    destruct (IHB0 (tlift 1 0 N)) as [Hc|Hnc]; [apply neutral_tlift; exact HN | | ].
    + left; apply compat_generalize;
        [ apply neutral_not_dyn; exact HN | intros K' C; eapply neutral_not_all; exact HN | exact Hc ].
    + right; intro Hc; inversion Hc; subst;
        try (match goal with H: neutral _ |- _ => solve [inversion H] end);
        contradiction.
  - (* B = tyabs: only refl (N=tyabs impossible) *)
    right; intro Hc; inversion Hc; subst;
      match goal with H: neutral _ |- _ => solve [inversion H] end.
  - (* B = tyapp *)
    destruct (typ_eq_dec N (tyapp B1 B2)) as [->|Hne]; [left; apply compat_refl|].
    right; intro Hc; inversion Hc; subst; try congruence;
      match goal with H: neutral _ |- _ => solve [inversion H] end.
  - (* B = dyn: to_dyn *)
    left; eapply compat_to_dyn;
      [ apply neutral_not_dyn; exact HN
      | intros K C; eapply neutral_not_all; exact HN
      | apply gt_neutral; exact HN
      | apply compat_refl ].
Qed.

(** Deciding [compat (arrow dyn dyn) B] (recursion on [B]). *)
Lemma compat_arrow_dyn_dyn_dec: forall B,
  {compat (arrow dyn dyn) B} + {~ compat (arrow dyn dyn) B}.
Proof.
  induction B as [m | B1 _ B2 _ | K B0 IHB0 | K B0 _ | B1 _ B2 _ | ].
  - right; intro Hc; inversion Hc.
  - (* arrow B1 B2 *)
    destruct (compat_dyn_r_dec B1) as [Hc1 | Hnc1];
    destruct (compat_dyn_l_dec B2) as [Hc2 | Hnc2];
    try (left; apply compat_arrow; assumption).
    all: right; intro Hc; inversion Hc; subst;
         solve [ apply Hnc1; (apply compat_refl || assumption)
               | apply Hnc2; (apply compat_refl || assumption) ].
  - (* all K B0: generalize *)
    destruct IHB0 as [Hc | Hnc].
    + left; apply compat_generalize;
        [ discriminate | intros K' C; discriminate | simpl; exact Hc ].
    + right; intro Hc; inversion Hc; subst; try congruence;
        apply Hnc; simpl in *; assumption.
  - right; intro Hc; inversion Hc.
  - right; intro Hc; inversion Hc.
  - (* dyn: to_dyn *)
    left; eapply compat_to_dyn;
      [ discriminate | intros K C; discriminate | apply gt_arrow | apply compat_refl ].
Qed.

(** Deciding [compat G B] for ground [G].  ([ground] has two constructors now,
    so we case on [neutral_dec] rather than inverting it into a [Set] goal.) *)
Lemma compat_ground_dec: forall G B, ground G -> {compat G B} + {~ compat G B}.
Proof.
  intros G B HG. destruct (neutral_dec G) as [Hn | Hn].
  - apply compat_neutral_dec; exact Hn.
  - assert (HG' : G = arrow dyn dyn) by (inversion HG; subst; [reflexivity | contradiction]).
    subst. apply compat_arrow_dyn_dyn_dec.
Qed.

(** No term variables are bound in a context consisting only of type bindings. *)
Lemma lookup_term_no_terms : forall g n,
  (forall b, In b g -> exists K, b = has_kind K \/ exists A, b = has_def K A) ->
  lookup_term g n = None.
Proof.
  induction g as [|b g IH]; intros n Hall; simpl.
  - reflexivity.
  - assert (Hb: exists K, b = has_kind K \/ exists A, b = has_def K A).
    { apply Hall. left. reflexivity. }
    destruct Hb as [K [-> | [A ->]]]; simpl.
    + rewrite IH; auto. intros b0 Hin. apply Hall. right. exact Hin.
    + rewrite IH; auto. intros b0 Hin. apply Hall. right. exact Hin.
Qed.

(** ** Progress *)

(** A context has no term bindings: every entry is [has_kind] or [has_def]. *)
Definition no_term_bindings (g : context) : Prop :=
  forall b, In b g -> exists K, b = has_kind K \/ exists A, b = has_def K A.

(** The empty context has no term bindings. *)
Lemma no_term_nil : no_term_bindings nil.
Proof. intros b H. inversion H. Qed.

(** Prepending a [has_kind] binding preserves [no_term_bindings]. *)
Lemma no_term_kind : forall K g,
  no_term_bindings g -> no_term_bindings (has_kind K :: g).
Proof.
  intros K g Hg b [<- | Hin].
  - exists K. left. reflexivity.
  - apply Hg. exact Hin.
Qed.

(** Prepending a [has_def] binding preserves [no_term_bindings]. *)
Lemma no_term_def : forall K A g,
  no_term_bindings g -> no_term_bindings (has_def K A :: g).
Proof.
  intros K A g Hg b [<- | Hin].
  - exists K. right. exists A. reflexivity.
  - apply Hg. exact Hin.
Qed.

(** Generalized progress: in a context with no term bindings, a well-typed term is a value, steps, or is blame. *)
Lemma progress_gen : forall g e A,
  typing g e A -> no_term_bindings g ->
  value e \/ (exists e', step e e') \/ (exists p, e = blame p).
Proof.
  intros g e A Hty.
  induction Hty; intros Hntb.

  - (* var: impossible — no term bindings *)
    exfalso. rewrite (lookup_term_no_terms g n Hntb) in H. discriminate.

  - (* abs *)
    left. constructor.

  - (* app *)
    destruct IHHty1 as [Hv1 | [[e1' Hs1] | [p1 ->]]]; auto.
    + destruct IHHty2 as [Hv2 | [[e2' Hs2] | [p2 ->]]]; auto.
      * destruct (canonical_arrow g _ _ _ Hv1 Hty1) as [t' [b' ->]].
        right. left. eexists. apply step_beta. exact Hv2.
      * right. left. eexists. apply step_app_right; eauto.
      * right. left. eexists. apply step_app_blame_r; eauto.
    + right. left. eexists. apply step_app_left; eauto.
    + right. left. eexists. apply step_app_blame_l.

  - (* tabs *)
    destruct IHHty as [Hv | [[e' Hs] | [p ->]]].
    + apply no_term_kind. exact Hntb.
    + left. constructor. exact Hv.
    + right. left. eexists. apply step_tabs_congr. exact Hs.
    + right. left. eexists. apply step_tabs_blame.

  - (* tapp *)
    destruct IHHty as [Hv | [[e' Hs] | [p ->]]]; auto.
    + destruct (canonical_all g _ _ _ Hv Hty) as [K' [b' ->]].
      inversion Hv; subst.
      right. left. eexists. apply step_tbeta. assumption.
    + right. left. eexists. apply step_tapp_congr. exact Hs.
    + right. left. eexists. apply step_tapp_blame.

  - (* cast: invert executable [compat A B]; each constructor gives a step *)
    destruct IHHty as [Hv | [[e' Hs] | [p1 ->]]]; auto.
    + (* value: case on the derivation of [compat A B] (hypothesis [H]) *)
      inversion H; subst.
      * (* compat_refl: A = B *)
        right. left. eexists. apply step_id. exact Hv.
      * (* compat_arrow: WRAP (or ID if the arrows coincide) *)
        destruct (typ_eq_dec (arrow A1 A2) (arrow B1 B2)) as [Heq | Hne].
        -- right. left. rewrite Heq. eexists. apply step_id. exact Hv.
        -- right. left. eexists. apply step_wrap; [exact Hv | exact Hne].
      * (* compat_all: ALL/ALL (or ID if the bodies coincide) *)
        destruct (typ_eq_dec A0 B0) as [-> | Hne].
        -- right. left. eexists. apply step_id. exact Hv.
        -- right. left. eexists. apply step_all_all; [exact Hv | exact Hne].
      * (* compat_generalize: GENERALIZE *)
        right. left. eexists. apply step_generalize; [exact Hv | assumption | assumption].
      * (* compat_instantiate: INSTANTIATE *)
        right. left. eexists. apply step_instantiate; [exact Hv | assumption].
      * (* compat_to_dyn: GROUND (or GROUND-ID if the source is already ground) *)
        match goal with Ht: ground_tag A ?G |- _ =>
          destruct (typ_eq_dec A G) as [Heq | Hne] end.
        -- (* A is its own tag: A is ground *)
           right. left. eexists. apply step_ground_id;
             [ exact Hv
             | rewrite Heq; eapply ground_tag_ground; eassumption
             | assumption ].
        -- right. left. eexists. eapply step_ground;
             [ exact Hv | assumption | assumption | eassumption | assumption | exact Hne ].
      * (* compat_from_dyn: A = dyn, so the value is [gnd w G] → COLLAPSE/CONFLICT *)
        destruct (canonical_dyn _ _ Hv Hty) as [w [G [-> [Hw HG]]]].
        destruct (compat_ground_dec G B HG) as [Hc | Hnc].
        -- right. left. eexists. eapply step_collapse; [exact Hw | exact HG | assumption | exact Hc].
        -- right. left. eexists. eapply step_conflict; [exact Hw | exact HG | assumption | exact Hnc].
    + right. left. eexists. apply step_cast_congr. exact Hs.
    + right. left. eexists. apply step_cast_blame.

  - (* gnd *)
    destruct IHHty as [Hv | [[e' Hs] | [p ->]]]; auto.
    + left. constructor. exact Hv.
    + right. left. eexists. apply step_gnd_congr. exact Hs.
    + right. left. eexists. apply step_gnd_blame.

  - (* is_gnd *)
    destruct IHHty as [Hv | [[e' Hs] | [p ->]]]; auto.
    + destruct (canonical_dyn _ _ Hv Hty) as [w [G' [-> [Hw HG']]]].
      right. left.
      destruct G' as [n | G1 G2 | KG GG | KG GG | G1 G2 | ].
      * (* tvar tag: neutral → tamper *)
        eexists. apply step_is_tamper; [exact Hw | apply neutral_tvar].
      * (* arrow tag: not neutral *)
        destruct (typ_eq_dec G (arrow G1 G2)) as [-> | Hne].
        -- eexists. apply step_is_true; [exact Hw | intro Hn; inversion Hn].
        -- eexists. apply step_is_false; [exact Hw | exact Hne | intro Hn; inversion Hn].
      * (* all: not ground *)
        exfalso; inversion HG'; subst;
          match goal with Hn: neutral _ |- _ => inversion Hn end.
      * (* tyabs: not ground *)
        exfalso; inversion HG'; subst;
          match goal with Hn: neutral _ |- _ => inversion Hn end.
      * (* tyapp tag: neutral → tamper *)
        inversion HG'; subst.
        eexists. apply step_is_tamper; [exact Hw | assumption].
      * (* dyn: not ground *) exfalso; eapply ground_not_dyn; [exact HG' | reflexivity].
    + right. left. eexists. apply step_is_gnd_congr. exact Hs.
    + right. left. eexists. apply step_is_gnd_blame.

  - (* blame *)
    right. right. eexists. reflexivity.

  - (* nu *)
    destruct IHHty as [Hv | [[e' Hs] | [p ->]]].
    + apply no_term_def. exact Hntb.
    + (* value body *)
      inversion Hv; subst; clear Hv.
      * right. left. eexists. apply step_nu_abs.
      * right. left. eexists. apply step_nu_tabs. assumption.
      * (* gnd v G inside nu — decide whether G mentions the sealed variable *)
        apply typing_gnd_inv in Hty.
        destruct Hty as [_ [_ HgG]].
        destruct (tvar_occurs 0 G) eqn:Eocc.
        -- right. left. eexists. apply step_nu_tamper; [assumption | exact HgG | exact Eocc].
        -- right. left. eexists. apply step_nu_gnd; [assumption | exact HgG | exact Eocc].
    + right. left. eexists. apply step_nu_congr. exact Hs.
    + right. left. eexists. apply step_nu_blame.

  - (* conv *)
    auto.
Qed.

(** Progress for closed terms: specializes [progress_gen] to the empty context. *)
Theorem progress : forall e A,
  typing nil e A ->
  value e \/ (exists e', step e e') \/ (exists p, e = blame p).
Proof.
  intros e A Hty. eapply progress_gen; eauto. apply no_term_nil.
Qed.
