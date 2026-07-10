(** * BlameFOmega.preservation: Subject reduction for the target's kind-regular
    typing.

    ** Which theorem is proved, and why (read before the rest of the file)

    [.claude/preservation_plan.md]'s two candidate statements were both tried
    against the *permissive* [typing] judgment of [typing.v] first, and both
    are actually FALSE for it, not merely hard: [typing_abs] and
    [typing_tapp]/[typing_nu] never require their type annotations to be
    well-kinded, so [typing_conv] can promote an ill-kinded [abs] domain (via
    an unconditional β-expansion on the *type* level, [ty_step]'s
    [tystep_beta], which never checks kinds) to a well-kinded arrow type,
    let the abstraction be applied to a genuine value of that arrow type, and
    β-reduce to a term that is then provably untypable at any type. (Sketch:
    with [g := [has_type (arrow t t); has_kind KStar]], [t := tyapp
    (tyabs (KArr KStar KStar) (tvar 0)) (arrow (tvar 0) (tvar 0))] — a
    genuinely unkindable type [t] that nonetheless [ty_step]-reduces in one
    step to the well-kinded [Y := arrow (tvar 0) (tvar 0)] — the closed term
    [app (abs t (app (var 1) (var 0))) (abs (tvar 0) (var 0))] is well-typed
    at the well-kinded type [Y] but [step_beta]-reduces to [app (var 0) (abs
    (tvar 0) (var 0))], which forces its second argument to type at the
    literal (unkindable) [t] and hence has *no* typing derivation at any
    type.) This is exactly the phenomenon the plan's "core technical
    obstacle" section describes, sharpened to a genuine counterexample rather
    than "merely" an intractable proof: no theorem phrased purely in terms of
    kinding of *outer/final* types (whether [wf_ctx g], [wf_typ g A KStar] on
    the redex's own type, or anything of that shape) can be true here,
    because [typing_abs]'s own domain annotation is never checked and can
    leak into a later position (an [app]'s domain slot) where it is load
    -bearing for typability.

    So the plan's main-approach diagnosis was correct that an invariant
    tracking "every type annotation actually used is well-kinded" is
    *necessary*, not merely convenient. Rather than defining a free-standing
    [wf_term : context -> term -> Prop] mirroring the term grammar (the
    plan's literal suggestion), this file takes a cleaner route to the same
    invariant: a new, separate **kind-regular typing** judgment [typing_kr],
    mirroring [typing]'s ten introduction rules exactly but adding the
    missing [wf_typ] premises ([typing.v] itself is untouched, per the
    task's rules). The reason this is more tractable than a term-indexed
    [wf_term] is that [wf_term] alone cannot know *which* kind a [tapp]'s
    type argument needs (a term's type, and hence the kind of a bound type
    variable it instantiates, is a property of a *typing derivation*, not of
    the term's syntax alone — e.g. [blame p] is typable at [all K t] for
    literally any [K]) whereas a typing judgment naturally carries that
    information at every node.

    [typing_kr] is proved sound for [typing] ([typing_kr_sound]), and
    [typing_regular] (every [typing_kr]-derivable type is well-kinded, given
    a well-formed context) is proved exactly as the plan's step 4 asks.

    ** [step_nu_abs]/[step_nu_tabs]: a second, genuine counterexample

    Even with [typing_kr]/[wf_ctx] in hand, the plan's exact main-approach
    statement (unrestricted [step]) is *still false* — for an entirely
    different reason than the one above, and one that no amount of
    kind-regularity can fix, because it has nothing to do with kinding.
    [step_nu_abs] reorders a [has_type T] binding to sit *below* a newly
    introduced [has_def K A] binding (pushing [nu K A] under an [abs]). Any
    *other*, independent annotation deeper in the [abs]'s body that pins the
    bound variable's type down exactly (e.g. a [cast]'s source-type
    annotation, which must match the operand's type up to [ty_equiv], not
    merely "the same after substitution") stops matching once that reordering
    happens, because the variable's lookup now crosses the intervening
    [has_def] and silently picks up an extra [tlift 1 0]. This is formally
    witnessed below, directly against [typing_kr] (the strongest judgment in
    this file, so [wf_ctx]/kind-regularity provably does not save it either):
    see [step_nu_abs_breaks_preservation] in [NuAbsCounterexample] for the
    full witness and proof. [step_nu_tabs] fails for the structurally
    identical reason (it moves a context binding past a *new* [has_kind]
    introduced by the [tabs] being pushed under).

    ** The theorem actually proved

    Given this, preservation is proved for [step_ok], defined below as an
    exact copy of [semantics.v]'s [step] with only [step_nu_abs] and
    [step_nu_tabs] removed (renamed [sok_*]), where every congruence
    constructor recurses into [step_ok] rather than [step], so the exclusion
    of the two bad rules holds at *every* nesting depth, not just at the top
    of a single step (a whole-term-relation subtlety: a congruence rule can
    otherwise smuggle a bad redex in arbitrarily deep):

    [[
    Theorem preservation : forall g e A e',
      wf_ctx g -> typing_kr g e A -> step_ok e e' -> typing_kr g e' A.
    ]]

    This is the strongest true, non-fabricated statement reachable from the
    plan's two candidates: same-type (not merely up-to-[ty_equiv]) single-step
    preservation, for the kind-regular judgment [typing_kr], for every [step]
    constructor except the two that are formally proved to break it.
    [typing_regular] plus [preservation]'s conclusion immediately gives back
    [wf_typ g A KStar] for the reduct, so a multi-step corollary is a one-line
    induction if ever needed (not required here, so not included).

    ** Status

    All 32 [step] constructors were attempted; 2 ([step_nu_abs],
    [step_nu_tabs]) are formally proved to break preservation (not merely
    hard to prove — see above) and are excluded via [step_ok]; the remaining
    30 [step_ok] constructors are proved with zero admitted goals, zero
    aborted proofs, and no new axioms. *)

From Stdlib Require Import Arith Lia List Relations.
Import ListNotations.
From BlameFOmega Require Import syntax infrastructure semantics
  typing typing_metatheory ty_confluence progress.

(** ** A few more [ty_equiv] congruences

    [ty_confluence.v] proves [ty_equiv] is preserved by [tlift]/[tsubst] and
    proves the head-inversions; it does not state the elementary "pointwise"
    congruences for [arrow]/[all], needed below to rebuild an outer type from
    a converted sub-derivation.  These follow the same
    reflexive-symmetric-transitive-closure induction as [ty_equiv_tlift]. *)

Lemma ty_equiv_arrow_congr_l : forall A A' B,
  ty_equiv A A' -> ty_equiv (arrow A B) (arrow A' B).
Proof.
  unfold ty_equiv. induction 1.
  - apply rst_step. apply tystep_arrow_l. assumption.
  - apply rst_refl.
  - apply rst_sym. assumption.
  - eapply rst_trans; eauto.
Qed.

Lemma ty_equiv_arrow_congr_r : forall A B B',
  ty_equiv B B' -> ty_equiv (arrow A B) (arrow A B').
Proof.
  unfold ty_equiv. induction 1.
  - apply rst_step. apply tystep_arrow_r. assumption.
  - apply rst_refl.
  - apply rst_sym. assumption.
  - eapply rst_trans; eauto.
Qed.

Lemma ty_equiv_arrow_congr : forall A A' B B',
  ty_equiv A A' -> ty_equiv B B' -> ty_equiv (arrow A B) (arrow A' B').
Proof.
  intros. eapply ty_equiv_trans;
    [apply ty_equiv_arrow_congr_l; eauto | apply ty_equiv_arrow_congr_r; eauto].
Qed.

Lemma ty_equiv_all_congr : forall K A A',
  ty_equiv A A' -> ty_equiv (all K A) (all K A').
Proof.
  unfold ty_equiv. induction 1.
  - apply rst_step. apply tystep_all. assumption.
  - apply rst_refl.
  - apply rst_sym. assumption.
  - eapply rst_trans; eauto.
Qed.

(** ** Well-formed contexts

    [wf_ctx]/[wf_ctx_lookup_term] now live in [typing_metatheory.v] (needed
    there by [lookup_def_wf]/[defeq_regular]); re-exported by that import. *)

(** ** Kind-regular typing *)

(** [typing_kr] mirrors [typing]'s ten introduction rules exactly, adding the
    [wf_typ]/[wf_ground] premises [typing.v]'s permissive judgment omits:
    [kr_abs] pins the domain annotation, [kr_tapp] pins the type-application
    argument at the polymorphic variable's own kind, [kr_cast] pins both cast
    endpoints, [kr_gnd] uses the kind-aware [wf_ground] instead of the bare
    syntactic [ground], and [kr_blame] pins [blame]'s type. [kr_nu] already
    had its [wf_typ] premise in [typing]. Everything else ([kr_var],
    [kr_app], [kr_tabs], [kr_is_gnd], [kr_conv]) is unchanged. *)
Inductive typing_kr : context -> term -> typ -> Prop :=
  | kr_var: forall g n t,
    lookup_term g n = Some t ->
    typing_kr g (var n) t
  | kr_abs: forall g t1 t2 e,
    wf_typ g t1 KStar ->
    typing_kr (has_type t1 :: g) e t2 ->
    typing_kr g (abs t1 e) (arrow t1 t2)
  | kr_app: forall g t1 t2 e1 e2,
    typing_kr g e1 (arrow t1 t2) ->
    typing_kr g e2 t1 ->
    typing_kr g (app e1 e2) t2
  | kr_tabs: forall g K e t,
    typing_kr (has_kind K :: g) e t ->
    typing_kr g (tabs K e) (all K t)
  | kr_tapp: forall g e t s K,
    typing_kr g e (all K t) ->
    wf_typ g s K ->
    typing_kr g (tapp e s) (tsubst s 0 t)
  | kr_cast: forall g e A B p,
    typing_kr g e A ->
    compat A B ->
    wf_typ g A KStar ->
    wf_typ g B KStar ->
    typing_kr g (cast e A B p) B
  | kr_gnd: forall g e G,
    typing_kr g e G ->
    ground G ->
    wf_typ g G KStar ->
    typing_kr g (gnd e G) dyn
  | kr_is_gnd: forall g e G,
    typing_kr g e dyn ->
    typing_kr g (is_gnd e G) (arrow dyn (arrow dyn dyn))
  | kr_blame: forall g p A,
    wf_typ g A KStar ->
    typing_kr g (blame p) A
  | kr_nu: forall g K A e B,
    typing_kr (has_def K A :: g) e B ->
    wf_typ g A K ->
    typing_kr g (nu K A e) (tsubst A 0 B)
  | kr_conv: forall g e A B,
    typing_kr g e A ->
    ty_equiv A B ->
    wf_typ g B KStar ->
    typing_kr g e B.

Hint Constructors typing_kr : blame.

(** [typing_kr] is sound for the permissive [typing] (dropping the extra
    [wf_typ] premises is always legal). *)
Lemma typing_kr_sound : forall g e A, typing_kr g e A -> typing g e A.
Proof.
  induction 1; eauto with blame.
Qed.

(** ** Regularity: every [typing_kr]-derivable type is well-kinded *)

Lemma typing_regular : forall g e A,
  wf_ctx g -> typing_kr g e A -> wf_typ g A KStar.
Proof.
  intros g e A Hwf H. revert Hwf. induction H; intros Hwf.
  - eapply wf_ctx_lookup_term; eauto.
  - apply wf_arrow; auto.
    apply (wf_typ_strengthen_type nil g t1 t2 KStar).
    apply IHtyping_kr. constructor; assumption.
  - specialize (IHtyping_kr1 Hwf). inversion IHtyping_kr1; subst; assumption.
  - apply wf_all. apply IHtyping_kr. constructor; assumption.
  - specialize (IHtyping_kr Hwf). inversion IHtyping_kr; subst.
    eapply (wf_typ_tsubst nil g K s t KStar); eauto.
  - assumption.
  - apply wf_dyn.
  - apply wf_arrow; [apply wf_dyn |]. apply wf_arrow; apply wf_dyn.
  - assumption.
  - specialize (IHtyping_kr (wf_ctx_def g K A Hwf H0)).
    pose proof (wf_typ_def_to_kind nil g K A B KStar IHtyping_kr) as IHtyping_kr'.
    clear IHtyping_kr. rename IHtyping_kr' into IHtyping_kr.
    pose proof (wf_typ_tsubst nil g K A B KStar IHtyping_kr H0) as P.
    simpl in P. exact P.
  - assumption.
Qed.

(** ** Inversion lemmas with convertibility, for [typing_kr]

    Same shape/proof pattern as [progress.v]'s [typing_*_inv2] lemmas (using
    the same [ty_conv_to]), just for [typing_kr]. *)

Lemma kr_var_inv2 : forall g n C,
  typing_kr g (var n) C ->
  exists t, ty_conv_to g t C /\ lookup_term g n = Some t.
Proof.
  intros g n C H. remember (var n) as tm eqn:Htm.
  induction H; try discriminate.
  - injection Htm as ->. exists t. split; [left; reflexivity | assumption].
  - destruct (IHtyping_kr Htm) as [t0 [Hconv Hlk]].
    exists t0. split; [eapply ty_conv_to_conv; eauto | assumption].
Qed.

Lemma kr_abs_inv2 : forall g t e C,
  typing_kr g (abs t e) C ->
  exists B, ty_conv_to g (arrow t B) C /\ typing_kr (has_type t :: g) e B /\ wf_typ g t KStar.
Proof.
  intros g t e C H. remember (abs t e) as tm eqn:Htm.
  induction H; try discriminate.
  - injection Htm as -> ->. exists t2. split; [left; reflexivity | split; assumption].
  - destruct (IHtyping_kr Htm) as [B0 [Hconv [Hbody Hwft]]].
    exists B0. split; [eapply ty_conv_to_conv; eauto | split; assumption].
Qed.

Lemma kr_tabs_inv2 : forall g K e C,
  typing_kr g (tabs K e) C ->
  exists B, ty_conv_to g (all K B) C /\ typing_kr (has_kind K :: g) e B.
Proof.
  intros g K e C H. remember (tabs K e) as tm eqn:Htm.
  induction H; try discriminate.
  - injection Htm as -> ->. exists t. split; [left; reflexivity | assumption].
  - destruct (IHtyping_kr Htm) as [B0 [Hconv Hbody]].
    exists B0. split; [eapply ty_conv_to_conv; eauto | assumption].
Qed.

Lemma kr_app_inv2 : forall g e1 e2 C,
  typing_kr g (app e1 e2) C ->
  exists A B, ty_conv_to g B C /\ typing_kr g e1 (arrow A B) /\ typing_kr g e2 A.
Proof.
  intros g e1 e2 C H. remember (app e1 e2) as tm eqn:Htm.
  induction H; try discriminate.
  - injection Htm as -> ->. exists t1, t2. split; [left; reflexivity | split; assumption].
  - destruct (IHtyping_kr Htm) as [A0 [B0 [Hconv [Hty1 Hty2]]]].
    exists A0, B0. split; [eapply ty_conv_to_conv; eauto | split; assumption].
Qed.

Lemma kr_tapp_inv2 : forall g e s C,
  typing_kr g (tapp e s) C ->
  exists K t, ty_conv_to g (tsubst s 0 t) C /\ typing_kr g e (all K t) /\ wf_typ g s K.
Proof.
  intros g e s C H. remember (tapp e s) as tm eqn:Htm.
  induction H; try discriminate.
  - injection Htm as -> ->. exists K, t. split; [left; reflexivity | split; assumption].
  - destruct (IHtyping_kr Htm) as [K0 [t0 [Hconv [Hty Hwf]]]].
    exists K0, t0. split; [eapply ty_conv_to_conv; eauto | split; assumption].
Qed.

Lemma kr_cast_inv2 : forall g e A B p C,
  typing_kr g (cast e A B p) C ->
  ty_conv_to g B C /\ typing_kr g e A /\ compat A B /\ wf_typ g A KStar /\ wf_typ g B KStar.
Proof.
  intros g e A B p C H. remember (cast e A B p) as tm eqn:Htm.
  induction H; try discriminate.
  - injection Htm as -> -> -> ->.
    repeat split; [left; reflexivity | assumption | assumption | assumption | assumption ].
  - destruct (IHtyping_kr Htm) as [Hconv [Hty [Hc [Hwa Hwb]]]].
    repeat split; [eapply ty_conv_to_conv; eauto | assumption | assumption | assumption | assumption].
Qed.

Lemma kr_gnd_inv2 : forall g e G C,
  typing_kr g (gnd e G) C ->
  ty_conv_to g dyn C /\ typing_kr g e G /\ ground G /\ wf_typ g G KStar.
Proof.
  intros g e G C H. remember (gnd e G) as tm eqn:Htm.
  induction H; try discriminate.
  - injection Htm as -> ->. repeat split; [left; reflexivity | assumption | assumption | assumption].
  - destruct (IHtyping_kr Htm) as [Hconv [Hty [Hg Hwf]]].
    repeat split; [eapply ty_conv_to_conv; eauto | assumption | assumption | assumption].
Qed.

Lemma kr_nu_inv2 : forall g K A e C,
  typing_kr g (nu K A e) C ->
  exists B, ty_conv_to g (tsubst A 0 B) C /\
            typing_kr (has_def K A :: g) e B /\
            wf_typ g A K.
Proof.
  intros g K A e C H. remember (nu K A e) as tm eqn:Htm.
  induction H; try discriminate.
  - injection Htm as -> -> ->. exists B. split; [left; reflexivity | split; assumption].
  - destruct (IHtyping_kr Htm) as [B0 [Hconv [Hty Hwf]]].
    exists B0. split; [eapply ty_conv_to_conv; eauto | split; assumption].
Qed.

Lemma kr_is_gnd_inv2 : forall g e G C,
  typing_kr g (is_gnd e G) C ->
  ty_conv_to g (arrow dyn (arrow dyn dyn)) C /\ typing_kr g e dyn.
Proof.
  intros g e G C H. remember (is_gnd e G) as tm eqn:Htm.
  induction H; try discriminate.
  - injection Htm as -> ->. split; [left; reflexivity | assumption].
  - destruct (IHtyping_kr Htm) as [Hconv Hty].
    split; [eapply ty_conv_to_conv; eauto | assumption].
Qed.

(** [apply_ty_conv_to], specialized to [typing_kr]. *)
Lemma apply_ty_conv_to_kr : forall g e A C,
  typing_kr g e A -> ty_conv_to g A C -> typing_kr g e C.
Proof.
  intros g e A C Hty [<- | [Heq Hwf]].
  - exact Hty.
  - eapply kr_conv; eauto.
Qed.

(** ** Canonical forms, for [typing_kr] (same statements/proofs as
    [typing_metatheory.v]/[progress.v], just against [typing_kr]). *)

Lemma kr_abs_inv : forall g t e C,
  typing_kr g (abs t e) C ->
  exists B, ty_equiv (arrow t B) C /\ typing_kr (has_type t :: g) e B.
Proof.
  intros g t e C H. remember (abs t e) as tm eqn:Htm.
  induction H; try discriminate.
  - injection Htm as -> ->. exists t2; split; [apply ty_equiv_refl | assumption].
  - destruct (IHtyping_kr Htm) as [B0 [Heq Hty]].
    exists B0; split; [ eapply ty_equiv_trans; eauto | assumption ].
Qed.

Lemma kr_tabs_inv : forall g K e C,
  typing_kr g (tabs K e) C ->
  exists B, ty_equiv (all K B) C /\ typing_kr (has_kind K :: g) e B.
Proof.
  intros g K e C H. remember (tabs K e) as tm eqn:Htm.
  induction H; try discriminate.
  - injection Htm as -> ->. exists t; split; [apply ty_equiv_refl | assumption].
  - destruct (IHtyping_kr Htm) as [B0 [Heq Hty]].
    exists B0; split; [ eapply ty_equiv_trans; eauto | assumption ].
Qed.

Lemma kr_gnd_inv : forall g e G C,
  typing_kr g (gnd e G) C ->
  ty_equiv dyn C /\ typing_kr g e G /\ ground G.
Proof.
  intros g e G C H. remember (gnd e G) as tm eqn:Htm.
  induction H; try discriminate.
  - injection Htm as -> ->. repeat split; [apply ty_equiv_refl | assumption | assumption].
  - destruct (IHtyping_kr Htm) as [Heq [Hty Hg]].
    repeat split; [ eapply ty_equiv_trans; eauto | assumption | assumption ].
Qed.

Lemma kr_canonical_arrow : forall g v A B,
  value v -> typing_kr g v (arrow A B) -> exists t e, v = abs t e.
Proof.
  intros g v A B Hv Hty. destruct Hv.
  - eauto.
  - apply kr_tabs_inv in Hty. destruct Hty as [B0 [Heq _]].
    exfalso. eapply ty_equiv_arrow_all. apply ty_equiv_sym; exact Heq.
  - apply kr_gnd_inv in Hty. destruct Hty as [Heq _].
    exfalso. eapply ty_equiv_dyn_arrow; exact Heq.
Qed.

Lemma kr_canonical_all : forall g v K B,
  value v -> typing_kr g v (all K B) -> exists K' e, v = tabs K' e.
Proof.
  intros g v K B Hv Hty. destruct Hv.
  - apply kr_abs_inv in Hty. destruct Hty as [B0 [Heq _]].
    exfalso. eapply ty_equiv_arrow_all; exact Heq.
  - eauto.
  - apply kr_gnd_inv in Hty. destruct Hty as [Heq _].
    exfalso. eapply ty_equiv_dyn_all; exact Heq.
Qed.

Lemma kr_canonical_dyn : forall g v,
  value v -> typing_kr g v dyn ->
  exists w G, v = gnd w G /\ value w /\ ground G.
Proof.
  intros g v Hv Hty. destruct Hv.
  - apply kr_abs_inv in Hty. destruct Hty as [B0 [Heq _]].
    exfalso. eapply ty_equiv_dyn_arrow. apply ty_equiv_sym. exact Heq.
  - apply kr_tabs_inv in Hty. destruct Hty as [B0 [Heq _]].
    exfalso. eapply ty_equiv_dyn_all. apply ty_equiv_sym. exact Heq.
  - apply kr_gnd_inv in Hty. destruct Hty as [Heq [Hty' Hg]].
    eexists; eexists; repeat split; eauto.
Qed.

(** ** Weakening and substitution for [typing_kr]

    Mirrors [typing_metatheory.v]'s weakening/substitution chain exactly, one
    lemma per lemma, for [typing_kr] instead of [typing]. Every extra
    [wf_typ]/[wf_ground] side-condition [typing_kr]'s constructors carry over
    [typing]'s is closed by the *same* [wf_typ] weakening/substitution lemmas
    already proved in [typing_metatheory.v] (kinding doesn't care which
    judgment is asking), so no new kinding lemmas are needed here — only the
    typing-shaped wrapper lemmas that thread them through [typing_kr]'s
    constructors. *)

Lemma typing_kr_weaken_term : forall G1 g e A C,
  typing_kr (G1 ++ g) e A ->
  typing_kr (G1 ++ has_type C :: g) (lift 1 (nterm G1) e) A.
Proof.
  intros G1 g e A C H. remember (G1 ++ g) as g0 eqn:Hg. revert G1 Hg.
  induction H; intros G1 Hg; subst.
  - rewrite lift1_var. apply kr_var. rewrite lookup_term_weaken. auto.
  - simpl. apply kr_abs; [apply wf_typ_weaken_type; auto | apply (IHtyping_kr (has_type t1 :: G1)); reflexivity].
  - simpl. eapply kr_app; eauto.
  - simpl. apply kr_tabs. apply (IHtyping_kr (has_kind K :: G1)). reflexivity.
  - simpl. eapply kr_tapp; eauto. apply wf_typ_weaken_type; auto.
  - simpl. eapply kr_cast; eauto; apply wf_typ_weaken_type; auto.
  - simpl. apply kr_gnd; auto. apply wf_typ_weaken_type; auto.
  - simpl. apply kr_is_gnd; auto.
  - simpl. apply kr_blame. apply wf_typ_weaken_type; auto.
  - simpl. apply kr_nu.
    + apply (IHtyping_kr (has_def K A :: G1)). reflexivity.
    + apply wf_typ_weaken_type; auto.
  - simpl. eapply kr_conv; [apply IHtyping_kr; reflexivity | exact H0 | apply wf_typ_weaken_type; auto].
Qed.

Corollary typing_kr_weaken_term0 : forall g e A C,
  typing_kr g e A -> typing_kr (has_type C :: g) (lift 1 0 e) A.
Proof. intros g e A C H. exact (typing_kr_weaken_term nil g e A C H). Qed.

Lemma typing_kr_weaken_kind : forall G1 g e A K,
  typing_kr (G1 ++ g) e A ->
  typing_kr (tlift_ctx G1 ++ has_kind K :: g) (term_tlift 1 (ntype G1) e) (tlift 1 (ntype G1) A).
Proof.
  intros G1 g e A K H. remember (G1 ++ g) as g0 eqn:Hg. revert G1 Hg.
  induction H; intros G1 Hg; subst.
  - simpl. apply kr_var. rewrite lookup_term_weaken_kind. rewrite H. reflexivity.
  - simpl. apply kr_abs; [apply wf_typ_weaken_kind; auto | apply (IHtyping_kr (has_type t1 :: G1)); reflexivity].
  - simpl. eapply kr_app; [apply (IHtyping_kr1 G1) | apply (IHtyping_kr2 G1)]; reflexivity.
  - simpl. apply kr_tabs. apply (IHtyping_kr (has_kind K0 :: G1)). reflexivity.
  - simpl.
    replace (tlift 1 (ntype G1) (tsubst s 0 t))
      with (tsubst (tlift 1 (ntype G1) s) 0 (tlift 1 (S (ntype G1)) t))
      by (symmetry; apply distribute_tlift_tsubst).
    eapply kr_tapp; [apply (IHtyping_kr G1); reflexivity | apply wf_typ_weaken_kind; auto].
  - simpl. eapply kr_cast; [apply (IHtyping_kr G1); reflexivity | apply compat_tlift; auto
      | apply wf_typ_weaken_kind; auto | apply wf_typ_weaken_kind; auto].
  - simpl. apply kr_gnd; [apply (IHtyping_kr G1); reflexivity | apply ground_tlift; auto | apply wf_typ_weaken_kind; auto].
  - simpl. apply kr_is_gnd. apply (IHtyping_kr G1). reflexivity.
  - simpl. apply kr_blame. apply wf_typ_weaken_kind; auto.
  - simpl.
    replace (tlift 1 (ntype G1) (tsubst A 0 B))
      with (tsubst (tlift 1 (ntype G1) A) 0 (tlift 1 (S (ntype G1)) B))
      by (symmetry; apply distribute_tlift_tsubst).
    apply kr_nu.
    + apply (IHtyping_kr (has_def K0 A :: G1)). reflexivity.
    + apply wf_typ_weaken_kind; auto.
  - simpl. eapply kr_conv;
      [ apply (IHtyping_kr G1); reflexivity
      | apply ty_equiv_tlift; auto
      | apply wf_typ_weaken_kind; auto ].
Qed.

Corollary typing_kr_weaken_kind0 : forall g e A K,
  typing_kr g e A -> typing_kr (has_kind K :: g) (term_tlift 1 0 e) (tlift 1 0 A).
Proof. intros g e A K H. exact (typing_kr_weaken_kind nil g e A K H). Qed.

Lemma typing_kr_weaken_def : forall G1 g e A K C,
  typing_kr (G1 ++ g) e A ->
  typing_kr (tlift_ctx G1 ++ has_def K C :: g) (term_tlift 1 (ntype G1) e) (tlift 1 (ntype G1) A).
Proof.
  intros G1 g e A K C H. remember (G1 ++ g) as g0 eqn:Hg. revert G1 Hg.
  induction H; intros G1 Hg; subst.
  - simpl. apply kr_var. rewrite lookup_term_weaken_def. rewrite H. reflexivity.
  - simpl. apply kr_abs; [apply wf_typ_weaken_def; auto | apply (IHtyping_kr (has_type t1 :: G1)); reflexivity].
  - simpl. eapply kr_app; [apply (IHtyping_kr1 G1) | apply (IHtyping_kr2 G1)]; reflexivity.
  - simpl. apply kr_tabs. apply (IHtyping_kr (has_kind K0 :: G1)). reflexivity.
  - simpl.
    replace (tlift 1 (ntype G1) (tsubst s 0 t))
      with (tsubst (tlift 1 (ntype G1) s) 0 (tlift 1 (S (ntype G1)) t))
      by (symmetry; apply distribute_tlift_tsubst).
    eapply kr_tapp; [apply (IHtyping_kr G1); reflexivity | apply wf_typ_weaken_def; auto].
  - simpl. eapply kr_cast; [apply (IHtyping_kr G1); reflexivity | apply compat_tlift; auto
      | apply wf_typ_weaken_def; auto | apply wf_typ_weaken_def; auto].
  - simpl. apply kr_gnd; [apply (IHtyping_kr G1); reflexivity | apply ground_tlift; auto | apply wf_typ_weaken_def; auto].
  - simpl. apply kr_is_gnd. apply (IHtyping_kr G1). reflexivity.
  - simpl. apply kr_blame. apply wf_typ_weaken_def; auto.
  - simpl.
    replace (tlift 1 (ntype G1) (tsubst A 0 B))
      with (tsubst (tlift 1 (ntype G1) A) 0 (tlift 1 (S (ntype G1)) B))
      by (symmetry; apply distribute_tlift_tsubst).
    apply kr_nu.
    + apply (IHtyping_kr (has_def K0 A :: G1)). reflexivity.
    + apply wf_typ_weaken_def; auto.
  - simpl. eapply kr_conv;
      [ apply (IHtyping_kr G1); reflexivity
      | apply ty_equiv_tlift; auto
      | apply wf_typ_weaken_def; auto ].
Qed.

Corollary typing_kr_weaken_def0 : forall g e A K C,
  typing_kr g e A -> typing_kr (has_def K C :: g) (term_tlift 1 0 e) (tlift 1 0 A).
Proof. intros g e A K C H. exact (typing_kr_weaken_def nil g e A K C H). Qed.

Lemma typing_kr_weaken_prefix : forall Gtm g u A,
  typing_kr g u A ->
  typing_kr (Gtm ++ g)
         (lift (nterm Gtm) 0 (term_tlift (ntype Gtm) 0 u))
         (tlift (ntype Gtm) 0 A).
Proof.
  induction Gtm as [|b Gtm IH]; intros g u A H; simpl.
  - rewrite term_tlift_zero, lift_zero_term, tlift_zero. exact H.
  - destruct b as [C | K | K C]; simpl.
    + specialize (IH g u A H).
      apply typing_kr_weaken_term0 with (C := C) in IH.
      rewrite (simplify_lift_term (term_tlift (ntype Gtm) 0 u) 1 (nterm Gtm) 0) in IH.
      replace (1 + nterm Gtm) with (S (nterm Gtm)) in IH by lia. exact IH.
    + specialize (IH g u A H).
      apply (typing_kr_weaken_kind0 (Gtm ++ g)) with (K := K) in IH.
      rewrite term_tlift_lift_comm in IH. rewrite term_tlift_comp in IH.
      rewrite (simplify_tlift_rec A (ntype Gtm) 0 1 0) in IH by lia.
      replace (1 + ntype Gtm) with (S (ntype Gtm)) in IH by lia. exact IH.
    + specialize (IH g u A H).
      apply (typing_kr_weaken_def0 (Gtm ++ g)) with (K := K) (C := C) in IH.
      rewrite term_tlift_lift_comm in IH. rewrite term_tlift_comp in IH.
      rewrite (simplify_tlift_rec A (ntype Gtm) 0 1 0) in IH by lia.
      replace (1 + ntype Gtm) with (S (ntype Gtm)) in IH by lia. exact IH.
Qed.

Lemma typing_kr_subst : forall G1 g e u T B,
  typing_kr (G1 ++ has_type T :: g) e B ->
  typing_kr g u T ->
  typing_kr (G1 ++ g) (subst (term_tlift (ntype G1) 0 u) (nterm G1) e) B.
Proof.
  intros G1 g e u T B He Hu.
  remember (G1 ++ has_type T :: g) as g0 eqn:Hg. revert G1 Hg.
  induction He; intros G1 Hg; subst; simpl.
  - destruct (lt_eq_lt_dec (nterm G1) n) as [[Hlt|Heq]|Hgt].
    + apply kr_var.
      replace n with (sh (nterm G1) (pred n)) in H
        by (unfold sh; destruct (le_gt_dec (nterm G1) (pred n)); lia).
      rewrite lookup_term_weaken in H. exact H.
    + subst. rewrite lookup_term_mid in H. injection H as <-.
      apply typing_kr_weaken_prefix. exact Hu.
    + apply kr_var. rewrite <- (lookup_term_below G1 g T n Hgt). exact H.
  - apply kr_abs; [eapply wf_typ_strengthen_type; eauto | apply (IHHe (has_type t1 :: G1)); reflexivity].
  - eapply kr_app; eauto.
  - apply kr_tabs.
    replace (term_tlift 1 0 (term_tlift (ntype G1) 0 u))
      with (term_tlift (S (ntype G1)) 0 u)
      by (rewrite term_tlift_comp;
          replace (1 + ntype G1) with (S (ntype G1)) by lia; reflexivity).
    apply (IHHe (has_kind K :: G1)). reflexivity.
  - eapply kr_tapp; eauto. eapply wf_typ_strengthen_type; eauto.
  - eapply kr_cast; eauto; eapply wf_typ_strengthen_type; eauto.
  - apply kr_gnd; eauto. eapply wf_typ_strengthen_type; eauto.
  - apply kr_is_gnd; eauto.
  - apply kr_blame. eapply wf_typ_strengthen_type; eauto.
  - replace (term_tlift 1 0 (term_tlift (ntype G1) 0 u))
      with (term_tlift (S (ntype G1)) 0 u)
      by (rewrite term_tlift_comp;
          replace (1 + ntype G1) with (S (ntype G1)) by lia; reflexivity).
    apply kr_nu.
    + apply (IHHe (has_def K A :: G1)). reflexivity.
    + eapply wf_typ_strengthen_type; eauto.
  - eapply kr_conv; [ eauto | auto |].
    eapply wf_typ_strengthen_type; eauto.
Qed.

Corollary typing_kr_subst0 : forall g e u T B,
  typing_kr (has_type T :: g) e B ->
  typing_kr g u T ->
  typing_kr g (subst u 0 e) B.
Proof.
  intros. pose proof (typing_kr_subst nil g e u T B H H0) as P.
  simpl in P. rewrite term_tlift_zero in P. exact P.
Qed.

Lemma typing_kr_tsubst : forall G1 g e S K A,
  typing_kr (G1 ++ has_kind K :: g) e A ->
  wf_typ g S K -> neutral S ->
  typing_kr (tsubst_ctx S G1 ++ g) (term_tsubst S (ntype G1) e) (tsubst S (ntype G1) A).
Proof.
  intros G1 g e S K A He Hs Hns.
  remember (G1 ++ has_kind K :: g) as g0 eqn:Hg. revert G1 Hg.
  induction He; intros G1 Hg; subst; simpl.
  - apply kr_var. rewrite (lookup_term_tsubst G1 g K). rewrite H. reflexivity.
  - apply kr_abs; [eapply wf_typ_tsubst; eauto | apply (IHHe (has_type t1 :: G1)); reflexivity].
  - eapply kr_app; eauto.
  - apply kr_tabs. apply (IHHe (has_kind K0 :: G1)). reflexivity.
  - pose proof (distribute_tsubst_rec t s S (ntype G1) 0) as Hd. simpl in Hd.
    rewrite Hd. eapply kr_tapp; [apply (IHHe G1); reflexivity | eapply wf_typ_tsubst; eauto].
  - eapply kr_cast; [ apply (IHHe G1); reflexivity | apply compat_tsubst; assumption
      | eapply wf_typ_tsubst; eauto | eapply wf_typ_tsubst; eauto ].
  - apply kr_gnd; [ apply (IHHe G1); reflexivity | apply ground_tsubst; assumption | eapply wf_typ_tsubst; eauto ].
  - apply kr_is_gnd. apply (IHHe G1). reflexivity.
  - apply kr_blame. eapply wf_typ_tsubst; eauto.
  - pose proof (distribute_tsubst_rec B A S (ntype G1) 0) as Hd. simpl in Hd.
    rewrite Hd.
    apply kr_nu.
    + apply (IHHe (has_def K0 A :: G1)). reflexivity.
    + eapply wf_typ_tsubst; eauto.
  - eapply kr_conv;
      [ apply (IHHe G1); reflexivity
      | apply ty_equiv_tsubst; auto
      | eapply wf_typ_tsubst; eauto ].
Qed.

Corollary typing_kr_tsubst0 : forall g e s K A,
  typing_kr (has_kind K :: g) e A ->
  wf_typ g s K -> neutral s ->
  typing_kr g (term_tsubst s 0 e) (tsubst s 0 A).
Proof.
  intros. pose proof (typing_kr_tsubst nil g e s K A H H0 H1) as P.
  simpl in P. exact P.
Qed.

Lemma ty_conv_to_equiv : forall g A B, ty_conv_to g A B -> ty_equiv A B.
Proof. intros g A B [<- | [Heq _]]; [apply ty_equiv_refl | exact Heq]. Qed.

(** [typing_kind_to_def]/[typing_def_to_kind], for [typing_kr]: [has_kind K]
    and [has_def K A] occupy the same lookup namespace, so a [typing_kr]
    derivation can move between them (with [wf_typ_kind_to_def]/
    [wf_typ_def_to_kind] closing every extra [wf_typ] side-condition). *)
Lemma typing_kr_kind_to_def : forall G1 g K A e B,
  typing_kr (G1 ++ has_kind K :: g) e B ->
  typing_kr (G1 ++ has_def K A :: g) e B.
Proof.
  intros G1 g K A e B H.
  remember (G1 ++ has_kind K :: g) as g0 eqn:Hg. revert G1 Hg.
  induction H; intros G1 Hg; subst.
  - apply kr_var. rewrite <- lookup_term_kind_to_def. auto.
  - apply kr_abs; [apply wf_typ_kind_to_def; auto | apply (IHtyping_kr (has_type t1 :: G1)); reflexivity].
  - eapply kr_app; eauto.
  - apply kr_tabs. apply (IHtyping_kr (has_kind K0 :: G1)). reflexivity.
  - eapply kr_tapp; eauto. apply wf_typ_kind_to_def; auto.
  - eapply kr_cast; eauto; apply wf_typ_kind_to_def; auto.
  - apply kr_gnd; eauto. apply wf_typ_kind_to_def; auto.
  - apply kr_is_gnd; eauto.
  - apply kr_blame. apply wf_typ_kind_to_def; auto.
  - apply kr_nu.
    + apply (IHtyping_kr (has_def K0 A0 :: G1)). reflexivity.
    + apply wf_typ_kind_to_def; auto.
  - eapply kr_conv; [ eauto | auto | apply wf_typ_kind_to_def; auto ].
Qed.

Lemma typing_kr_def_to_kind : forall G1 g K A e B,
  typing_kr (G1 ++ has_def K A :: g) e B ->
  typing_kr (G1 ++ has_kind K :: g) e B.
Proof.
  intros G1 g K A e B H.
  remember (G1 ++ has_def K A :: g) as g0 eqn:Hg. revert G1 Hg.
  induction H; intros G1 Hg; subst.
  - apply kr_var. rewrite (lookup_term_kind_to_def _ _ _ A). auto.
  - apply kr_abs; [eapply wf_typ_def_to_kind; eauto | apply (IHtyping_kr (has_type t1 :: G1)); reflexivity].
  - eapply kr_app; eauto.
  - apply kr_tabs. apply (IHtyping_kr (has_kind K0 :: G1)). reflexivity.
  - eapply kr_tapp; eauto. eapply wf_typ_def_to_kind; eauto.
  - eapply kr_cast; eauto; eapply wf_typ_def_to_kind; eauto.
  - apply kr_gnd; eauto. eapply wf_typ_def_to_kind; eauto.
  - apply kr_is_gnd; eauto.
  - apply kr_blame. eapply wf_typ_def_to_kind; eauto.
  - apply kr_nu.
    + apply (IHtyping_kr (has_def K0 A0 :: G1)). reflexivity.
    + eapply wf_typ_def_to_kind; eauto.
  - eapply kr_conv; [ eauto | auto | eapply wf_typ_def_to_kind; eauto ].
Qed.

(** ** [step_nu_abs] genuinely breaks preservation: a formal counterexample

    Every attempt above to reorder a [has_type T] binding below a
    [has_def K A] binding (as [step_nu_abs]/[step_nu_tabs] require) runs into
    the same wall: [step_nu_abs] pushes [nu K A] under an [abs], transplanting
    the [abs]'s *own* annotation [T] to [tsubst A 0 T], but it does nothing to
    any *other*, independent type annotation inside the [abs]'s body that
    happens to mention the [abs]'s bound term variable at a type that
    syntactically coincides with [T] (e.g. a [cast]'s source-type annotation,
    which [typing]/[typing_kr] require to match the operand's type *exactly*,
    up to [ty_equiv], not merely "the same after substitution"). Once the
    [abs] moves outside the [nu], that operand's lookup crosses the
    now-intervening [has_def K A] and therefore gets an extra [tlift 1 0],
    which is essentially never [ty_equiv] to the cast's fixed annotation. This
    is not a limitation of this file's proof technique: it is a genuine
    failure of subject reduction for [step_nu_abs], reproducible against
    [typing_kr] itself (so [wf_ctx]/kind-regularity, i.e. the plan's "main
    approach", does not save it either — kind-regularity is a property of
    *types*, and every type involved here is perfectly well-kinded; the
    problem is that a *term*-level annotation stops matching after the
    binder is moved past a def).

    Concretely: let [g := has_type (tvar 0) :: has_def KStar dyn :: nil],
    [e_inner := cast (var 0) (tvar 0) (all KStar (tvar 1)) p] (typable: [var
    0 : tvar 0] matches the cast's own annotation exactly, and [compat (tvar
    0) (all KStar (tvar 1))] holds by [compat_generalize] since [compat (tvar
    1) (tvar 1)] is [compat_refl]). Then [nu KStar dyn (abs (tvar 0)
    e_inner)] is well-typed (at [arrow dyn (all KStar dyn)]), and
    [step_nu_abs] reduces it to [abs dyn (nu KStar dyn e_inner)] — which is
    untypable at *any* type, because inside it, [var 0]'s type is now
    [tlift 1 0 dyn = dyn], not [ty_equiv] to the cast's fixed annotation
    [tvar 0]. [step_nu_abs_breaks_preservation] proves this formally (against
    [typing_kr], the strongest judgment in this file); [step_nu_tabs] fails
    for the structurally identical reason (moving a [has_kind]/[has_def]
    binding past a *new* [has_kind] introduced by the [tabs] being pushed
    under, via [term_tswap]).

    Given this, the theorem below is proved for [step_ok], the restriction of
    [step] that drops exactly these two constructors (its congruence rules
    recurse into [step_ok], so the exclusion holds at every nesting depth,
    not just at the top of a single step). This is the strongest true,
    non-fabricated statement reachable from the plan's two candidates; see
    the header comment for the full accounting. *)

Section NuAbsCounterexample.

  Let g0 := has_def KStar dyn :: nil.
  Let e_inner (p : label) := cast (var 0) (tvar 0) (all KStar (tvar 1)) p.
  Let abs_e (p : label) := abs (tvar 0) (e_inner p).
  Let e0 (p : label) := nu KStar dyn (abs_e p).
  Let e0' (p : label) := abs dyn (nu KStar dyn (e_inner p)).

  Lemma compat_witness : compat (tvar 0) (all KStar (tvar 1)).
  Proof.
    apply compat_generalize.
    - discriminate.
    - intros K' C H; discriminate.
    - simpl. apply compat_refl.
  Qed.

  Lemma e_inner_typing_kr : forall p,
    typing_kr (has_type (tvar 0) :: g0) (e_inner p) (all KStar (tvar 1)).
  Proof.
    intros p. unfold e_inner. eapply kr_cast.
    - apply kr_var. reflexivity.
    - apply compat_witness.
    - apply wf_tvar. reflexivity.
    - apply wf_all. apply wf_tvar. reflexivity.
  Qed.

  Lemma e0_typing_kr : forall p,
    typing_kr nil (e0 p) (tsubst dyn 0 (arrow (tvar 0) (all KStar (tvar 1)))).
  Proof.
    intros p. unfold e0. apply kr_nu.
    - apply kr_abs; [apply wf_tvar; reflexivity | apply e_inner_typing_kr].
    - apply wf_dyn.
  Qed.

  Lemma e0_wf : wf_ctx nil.
  Proof. constructor. Qed.

  Lemma e0_steps : forall p, step (e0 p) (e0' p).
  Proof. intros p. unfold e0, e0', abs_e. apply step_nu_abs. Qed.

  Lemma e0'_not_typable_kr : forall p C, ~ typing_kr nil (e0' p) C.
  Proof.
    intros p C Hty. unfold e0' in Hty.
    apply kr_abs_inv2 in Hty. destruct Hty as [B [_ [Hbody _]]].
    apply kr_nu_inv2 in Hbody. destruct Hbody as [B0 [_ [Hinner _]]].
    unfold e_inner in Hinner.
    apply kr_cast_inv2 in Hinner. destruct Hinner as [_ [Hvar _]].
    apply kr_var_inv2 in Hvar. destruct Hvar as [t [Hconv Hlk]].
    simpl in Hlk. injection Hlk as <-.
    destruct Hconv as [Heq | [Hequiv _]].
    - discriminate.
    - eapply ty_equiv_dyn_tvar. exact Hequiv.
  Qed.

  (** [step_nu_abs] falsifies preservation for [typing_kr]: no strengthening
      of the *type-level* invariant (kind-regularity, well-formed contexts,
      or anything phrased purely in terms of [wf_typ]) can restore it. *)
  Theorem step_nu_abs_breaks_preservation :
    ~ (forall g e A e', wf_ctx g -> typing_kr g e A -> step e e' -> typing_kr g e' A).
  Proof.
    intro Hpres.
    pose (p := mk_label 2 true).
    exact (e0'_not_typable_kr p _
             (Hpres nil (e0 p) _ (e0' p) e0_wf (e0_typing_kr p) (e0_steps p))).
  Qed.

End NuAbsCounterexample.

(** ** [step_ok]: [step] restricted away from [step_nu_abs]/[step_nu_tabs]

    A literal copy of [semantics.v]'s [step], with those two constructors
    dropped and every congruence constructor's recursive premise changed
    from [step] to [step_ok], so that the exclusion propagates to every
    nesting depth (see the counterexample above for why a shallow
    "[e] does not syntactically match the redex" hypothesis would not be
    enough — the bad redex can appear arbitrarily deep under congruence). *)
Inductive step_ok : term -> term -> Prop :=
  | sok_beta: forall t b x,
    value x -> step_ok (app (abs t b) x) (subst x 0 b)
  | sok_tbeta: forall K b t,
    value b -> step_ok (tapp (tabs K b) t) (nu K t b)
  | sok_wrap: forall v A B A' B' p,
    value v -> arrow A B <> arrow A' B' ->
    step_ok (cast v (arrow A B) (arrow A' B') p)
      (abs A' (cast (app (lift 1 0 v) (cast (var 0) A' A (negate p))) B B' p))
  | sok_id: forall v A p,
    value v -> step_ok (cast v A A p) v
  | sok_ground: forall v A G p,
    value v -> A <> dyn -> (forall K A', A <> all K A') ->
    ground_tag A G -> compat A G -> A <> G ->
    step_ok (cast v A dyn p) (gnd (cast v A G p) G)
  | sok_ground_id: forall v G p,
    value v -> ground G -> G <> dyn -> step_ok (cast v G dyn p) (gnd v G)
  | sok_collapse: forall v G A p,
    value v -> ground G -> A <> dyn -> compat G A ->
    step_ok (cast (gnd v G) dyn A p) (cast v G A p)
  | sok_conflict: forall v G A p,
    value v -> ground G -> A <> dyn -> ~ compat G A ->
    step_ok (cast (gnd v G) dyn A p) (blame p)
  | sok_is_true: forall v G,
    value v -> ~ neutral G -> step_ok (is_gnd (gnd v G) G) (abs dyn (abs dyn (var 1)))
  | sok_is_false: forall v G H,
    value v -> G <> H -> ~ neutral H -> step_ok (is_gnd (gnd v H) G) (abs dyn (abs dyn (var 0)))
  | sok_is_tamper: forall v H G,
    value v -> neutral H -> step_ok (is_gnd (gnd v H) G) (blame is_tamper_label)
  | sok_tabs_congr: forall K e e',
    step_ok e e' -> step_ok (tabs K e) (tabs K e')
  | sok_tabs_blame: forall K p, step_ok (tabs K (blame p)) (blame p)
  | sok_nu_var: forall K A n, step_ok (nu K A (var n)) (var n)
  | sok_nu_gnd: forall K A v G,
    value v -> ground G -> tvar_occurs 0 G = false ->
    step_ok (nu K A (gnd v G)) (gnd (nu K A v) (tsubst A 0 G))
  | sok_nu_tamper: forall K A v G,
    value v -> ground G -> tvar_occurs 0 G = true ->
    step_ok (nu K A (gnd v G)) (blame nu_tamper_label)
  | sok_nu_congr: forall K A e e',
    step_ok e e' -> step_ok (nu K A e) (nu K A e')
  | sok_nu_blame: forall K A p, step_ok (nu K A (blame p)) (blame p)
  | sok_generalize: forall v A K B p,
    value v -> A <> dyn -> (forall K' C, A <> all K' C) ->
    step_ok (cast v A (all K B) p) (tabs K (cast (term_tlift 1 0 v) (tlift 1 0 A) B p))
  | sok_instantiate: forall v A B p,
    value v -> (forall K' B', B <> all K' B') ->
    step_ok (cast v (all KStar A) B p) (cast (tapp v dyn) (tsubst dyn 0 A) B p)
  | sok_all_all: forall v K A B p,
    value v -> A <> B ->
    step_ok (cast v (all K A) (all K B) p)
      (tabs K (cast (tapp (term_tlift 1 0 v) (tvar 0)) A B p))
  | sok_app_left: forall e1 e2 x,
    step_ok e1 e2 -> step_ok (app e1 x) (app e2 x)
  | sok_app_right: forall v x1 x2,
    value v -> step_ok x1 x2 -> step_ok (app v x1) (app v x2)
  | sok_tapp_congr: forall e1 e2 t,
    step_ok e1 e2 -> step_ok (tapp e1 t) (tapp e2 t)
  | sok_cast_congr: forall e1 e2 A B p,
    step_ok e1 e2 -> step_ok (cast e1 A B p) (cast e2 A B p)
  | sok_gnd_congr: forall e1 e2 G,
    step_ok e1 e2 -> step_ok (gnd e1 G) (gnd e2 G)
  | sok_is_gnd_congr: forall e1 e2 G,
    step_ok e1 e2 -> step_ok (is_gnd e1 G) (is_gnd e2 G)
  | sok_app_blame_l: forall p x, step_ok (app (blame p) x) (blame p)
  | sok_app_blame_r: forall v p, value v -> step_ok (app v (blame p)) (blame p)
  | sok_tapp_blame: forall p t, step_ok (tapp (blame p) t) (blame p)
  | sok_cast_blame: forall p A B q, step_ok (cast (blame p) A B q) (blame p)
  | sok_gnd_blame: forall p G, step_ok (gnd (blame p) G) (blame p)
  | sok_is_gnd_blame: forall p G, step_ok (is_gnd (blame p) G) (blame p).

Hint Constructors step_ok : blame.

(** ** A [neutral s] hypothesis is not needed to preserve [ground]/[neutral]
    when the substituted variable does not occur at all: substitution at an
    index that is never hit by any [tvar] in the target is just an index
    shift, independent of the replacement type. This is exactly the
    situation in [step_nu_gnd]'s [tvar_occurs 0 G = false] guard. *)
Lemma neutral_tsubst_shift : forall N s,
  neutral N -> tvar_occurs 0 N = false -> neutral (tsubst s 0 N).
Proof.
  induction 1; intros Hocc; simpl in *.
  - destruct n as [ | n' ].
    + simpl in Hocc. discriminate.
    + apply neutral_tvar.
  - apply Bool.orb_false_iff in Hocc as [HF HA].
    apply neutral_tyapp. apply IHneutral. exact HF.
Qed.

Lemma ground_tsubst_shift : forall G s,
  ground G -> tvar_occurs 0 G = false -> ground (tsubst s 0 G).
Proof.
  intros G s Hg Hocc; inversion Hg; subst; simpl.
  - apply ground_arrow.
  - apply ground_neutral. apply neutral_tsubst_shift; assumption.
Qed.

(** ** [compat] inversion helpers for the three ∀-cast [step_ok] rules
    ([sok_generalize], [sok_instantiate], [sok_all_all]): each rule's guards
    pin down exactly one of [compat]'s seven constructors as the only
    possibility; every other constructor either forces an outer head-shape
    contradiction ([discriminate]) or forces the guarded side back into an
    [all]/[dyn] shape that the guard itself already excludes. *)
Lemma compat_generalize_inv : forall A K C,
  A <> dyn -> (forall K' C', A <> all K' C') ->
  compat A (all K C) -> compat (tlift 1 0 A) C.
Proof.
  intros A K C Hnd Hna Hc.
  inversion Hc as [A0 | A1 A2 B1 B2 Hc1 Hc2 | K0 A0 B0 Hc0 | A0 K0 B0 Hd Hforall Hc0
                   | A0 B0 Hforall Hc0 | A0 G0 Hd Hforall Hgt Hc0 | B0 Hd Hcf];
    subst; try discriminate.
  - exfalso; eapply Hna; reflexivity.
  - exfalso; eapply Hna; reflexivity.
  - assumption.
  - exfalso; eapply Hna; reflexivity.
  - exfalso; eapply Hnd; reflexivity.
Qed.

Lemma compat_instantiate_inv : forall A B,
  (forall K' B', B <> all K' B') ->
  compat (all KStar A) B -> compat (tsubst dyn 0 A) B.
Proof.
  intros A B Hnb Hc.
  inversion Hc as [A0 | A1 A2 B1 B2 Hc1 Hc2 | K0 A0 B0 Hc0 | A0 K0 B0 Hd Hforall Hc0
                   | A0 B0 Hforall Hc0 | A0 G0 Hd Hforall Hgt Hc0 | B0 Hd Hcf];
    subst; try discriminate.
  - exfalso; eapply Hnb; reflexivity.
  - exfalso; eapply Hnb; reflexivity.
  - exfalso; eapply Hnb; reflexivity.
  - assumption.
  - exfalso; eapply (Hforall KStar A); reflexivity.
Qed.

(** Instantiating a type freshly weakened one binder up, at the very
    variable that weakening just introduced, is the identity. Needed for
    [sok_all_all]'s eta-style reconstruction [tapp (tlift v) (tvar 0)]. *)
Lemma tsubst_tvar0_tlift_gen : forall A k,
  tsubst (tvar 0) k (tlift 1 (S k) A) = A.
Proof.
  induction A; intros k.
  - unfold tlift; fold tlift.
    destruct (le_gt_dec (S k) n) as [Hge | Hlt];
      unfold tsubst; fold tsubst.
    + destruct (lt_eq_lt_dec k (1 + n)) as [[Hlt2 | Heq2] | Hgt2];
        simpl; try (exfalso; lia); f_equal; lia.
    + destruct (lt_eq_lt_dec k n) as [[Hlt2 | Heq2] | Hgt2];
        simpl; try (exfalso; lia); try reflexivity.
      subst. f_equal. lia.
  - simpl. f_equal; auto.
  - simpl. f_equal. apply IHA.
  - simpl. f_equal. apply IHA.
  - simpl. f_equal; auto.
  - reflexivity.
Qed.

Corollary tsubst_tvar0_tlift1 : forall A, tsubst (tvar 0) 0 (tlift 1 1 A) = A.
Proof. intros A. exact (tsubst_tvar0_tlift_gen A 0). Qed.

Lemma compat_all_inv : forall K A B,
  A <> B -> compat (all K A) (all K B) -> compat A B.
Proof.
  intros K A B Hne Hc.
  inversion Hc as [A0 | A1 A2 B1 B2 Hc1 Hc2 | K0 A0 B0 Hc0 | A0 K0 B0 Hd Hforall Hc0
                   | A0 B0 Hforall Hc0 | A0 G0 Hd Hforall Hgt Hc0 | B0 Hd Hcf];
    subst; try discriminate.
  - exfalso; apply Hne; reflexivity.
  - assumption.
  - exfalso; eapply Hforall; reflexivity.
  - exfalso; eapply Hforall; reflexivity.
Qed.

(** ** The preservation theorem *)

Theorem preservation : forall g e A e',
  wf_ctx g -> typing_kr g e A -> step_ok e e' -> typing_kr g e' A.
Proof.
  intros g e A e' Hwf Hty Hstep. revert g A Hwf Hty.
  induction Hstep; intros g Aout Hwf Hty.

  - (* step_beta *)
    rename t into t1, b into body, x into x0.
    pose proof (typing_regular g _ Aout Hwf Hty) as HwfAout.
    apply kr_app_inv2 in Hty. destruct Hty as [A0 [B0 [Hconv [Htyf Htyx]]]].
    apply kr_abs_inv2 in Htyf. destruct Htyf as [B1 [Hconv2 [Htybody Hwft1]]].
    apply ty_conv_to_equiv in Hconv2.
    apply ty_equiv_arrow_inv in Hconv2. destruct Hconv2 as [HeqDom HeqCod].
    assert (Htyx' : typing_kr g x0 t1)
      by (eapply kr_conv; [exact Htyx | apply ty_equiv_sym; exact HeqDom | exact Hwft1]).
    pose proof (typing_kr_subst0 g body x0 t1 B1 Htybody Htyx') as Hsub.
    eapply kr_conv; [exact Hsub | | exact HwfAout].
    eapply ty_equiv_trans; [exact HeqCod |].
    apply ty_conv_to_equiv in Hconv. exact Hconv.

  - (* step_tbeta *)
    rename b into body.
    pose proof (typing_regular g _ Aout Hwf Hty) as HwfAout.
    apply kr_tapp_inv2 in Hty. destruct Hty as [K1 [t1 [Hconv [Htyf Hwft]]]].
    apply kr_tabs_inv2 in Htyf. destruct Htyf as [B1 [Hconv2 Htybody]].
    apply ty_conv_to_equiv in Hconv2. apply ty_equiv_all_inv in Hconv2.
    destruct Hconv2 as [-> HeqB].
    pose proof (typing_kr_kind_to_def nil g K1 t body B1 Htybody) as Htybody'.
    simpl in Htybody'.
    pose proof (kr_nu g K1 t body B1 Htybody' Hwft) as Hnu.
    eapply kr_conv; [exact Hnu | | exact HwfAout].
    eapply ty_equiv_trans; [apply ty_equiv_tsubst; exact HeqB |].
    apply ty_conv_to_equiv in Hconv. exact Hconv.

  - (* step_wrap *)
    pose proof (typing_regular g _ Aout Hwf Hty) as HwfAout.
    apply kr_cast_inv2 in Hty.
    destruct Hty as [Hconv [Htyv [Hcomp [HwfArrAB HwfArrAB']]]].
    inversion HwfArrAB as [ | HwfA HwfB | | | | ]; subst.
    inversion HwfArrAB' as [ | HwfA' HwfB' | | | | ]; subst.
    apply compat_arrow_inv in Hcomp. destruct Hcomp as [HcompA'A HcompBB'].
    assert (HwfA0 : wf_typ (has_type A' :: g) A KStar) by (apply (wf_typ_weaken_type nil g A' A KStar); auto).
    assert (HwfB0 : wf_typ (has_type A' :: g) B KStar) by (apply (wf_typ_weaken_type nil g A' B KStar); auto).
    assert (HwfB'0 : wf_typ (has_type A' :: g) B' KStar) by (apply (wf_typ_weaken_type nil g A' B' KStar); auto).
    assert (HwfA'0 : wf_typ (has_type A' :: g) A' KStar) by (apply (wf_typ_weaken_type nil g A' A' KStar); auto).
    assert (Hv0 : typing_kr (has_type A' :: g) (lift 1 0 v) (arrow A B))
      by (apply typing_kr_weaken_term0; exact Htyv).
    assert (Hvar0 : typing_kr (has_type A' :: g) (var 0) A')
      by (apply kr_var; reflexivity).
    assert (Hcastvar : typing_kr (has_type A' :: g) (cast (var 0) A' A (negate p)) A)
      by (eapply kr_cast; eauto).
    assert (Happ : typing_kr (has_type A' :: g) (app (lift 1 0 v) (cast (var 0) A' A (negate p))) B)
      by (eapply kr_app; eauto).
    assert (Hcastapp : typing_kr (has_type A' :: g)
              (cast (app (lift 1 0 v) (cast (var 0) A' A (negate p))) B B' p) B')
      by (eapply kr_cast; eauto).
    assert (Habs : typing_kr g
              (abs A' (cast (app (lift 1 0 v) (cast (var 0) A' A (negate p))) B B' p))
              (arrow A' B'))
      by (apply kr_abs; auto).
    eapply apply_ty_conv_to_kr; eauto.

  - (* step_id *)
    apply kr_cast_inv2 in Hty. destruct Hty as [Hconv [Htyv _]].
    eapply apply_ty_conv_to_kr; eauto.

  - (* step_ground *)
    apply kr_cast_inv2 in Hty.
    destruct Hty as [Hconv [Htyv [Hcomp [HwfA _]]]].
    assert (HwfG : wf_typ g G KStar).
    { inversion H2 as [A0 B0 | N HN]; subst.
      - apply wf_arrow; apply wf_dyn.
      - exfalso; apply H4; reflexivity. }
    assert (Hcast : typing_kr g (cast v A G p) G)
      by (eapply kr_cast; eauto).
    assert (Hgnd : typing_kr g (gnd (cast v A G p) G) dyn)
      by (apply kr_gnd; eauto using ground_tag_ground).
    eapply apply_ty_conv_to_kr; eauto.

  - (* step_ground_id *)
    apply kr_cast_inv2 in Hty.
    destruct Hty as [Hconv [Htyv [_ [HwfG _]]]].
    assert (Hgnd : typing_kr g (gnd v G) dyn) by (apply kr_gnd; auto).
    eapply apply_ty_conv_to_kr; eauto.

  - (* step_collapse *)
    apply kr_cast_inv2 in Hty.
    destruct Hty as [Hconv [Htygnd [_ [_ HwfA]]]].
    apply (kr_gnd_inv2 g v G dyn) in Htygnd.
    destruct Htygnd as [_ [Htyv [_ HwfG]]].
    assert (Hcast : typing_kr g (cast v G A p) A)
      by (eapply kr_cast; eauto).
    eapply apply_ty_conv_to_kr; eauto.

  - (* step_conflict *)
    apply kr_cast_inv2 in Hty.
    destruct Hty as [Hconv [_ [_ [_ HwfA]]]].
    assert (Hblame : typing_kr g (blame p) A) by (apply kr_blame; exact HwfA).
    eapply apply_ty_conv_to_kr; eauto.

  - (* step_is_true *)
    apply kr_is_gnd_inv2 in Hty. destruct Hty as [Hconv _].
    assert (Habs : typing_kr g (abs dyn (abs dyn (var 1))) (arrow dyn (arrow dyn dyn))).
    { apply kr_abs; [apply wf_dyn |]. apply kr_abs; [apply wf_dyn |].
      apply kr_var. reflexivity. }
    eapply apply_ty_conv_to_kr; eauto.

  - (* step_is_false *)
    apply kr_is_gnd_inv2 in Hty. destruct Hty as [Hconv _].
    assert (Habs : typing_kr g (abs dyn (abs dyn (var 0))) (arrow dyn (arrow dyn dyn))).
    { apply kr_abs; [apply wf_dyn |]. apply kr_abs; [apply wf_dyn |].
      apply kr_var. reflexivity. }
    eapply apply_ty_conv_to_kr; eauto.

  - (* step_is_tamper *)
    pose proof (typing_regular g _ Aout Hwf Hty) as HwfAout.
    apply kr_blame. exact HwfAout.

  - (* step_tabs_congr *)
    apply kr_tabs_inv2 in Hty. destruct Hty as [B [Hconv Hbody]].
    assert (Hbody' : typing_kr (has_kind K :: g) e' B)
      by (apply (IHHstep (has_kind K :: g) B); [constructor; assumption | exact Hbody]).
    assert (Htabs : typing_kr g (tabs K e') (all K B)) by (apply kr_tabs; exact Hbody').
    eapply apply_ty_conv_to_kr; eauto.

  - (* step_tabs_blame *)
    pose proof (typing_regular g _ Aout Hwf Hty) as HwfAout.
    apply kr_blame. exact HwfAout.

  - (* step_nu_var *)
    pose proof (typing_regular g _ Aout Hwf Hty) as HwfAout.
    apply kr_nu_inv2 in Hty. destruct Hty as [B [Hconv [Htybody Hwft]]].
    apply kr_var_inv2 in Htybody. destruct Htybody as [t [Hconv2 Hlk]].
    simpl in Hlk.
    case_eq (lookup_term g n); [intros t0 Hlk0 | intros Hlk0]; rewrite Hlk0 in Hlk;
      simpl in Hlk; try discriminate.
    injection Hlk as <-.
    apply ty_conv_to_equiv in Hconv2.
    assert (Hvar : typing_kr g (var n) t0) by (apply kr_var; exact Hlk0).
    eapply kr_conv; [exact Hvar | | exact HwfAout].
    eapply ty_equiv_trans; [ | exact (ty_conv_to_equiv g _ _ Hconv)].
    pose proof (tsubst_tlift_cancel t0 A) as Hcancel.
    pose proof (ty_equiv_tsubst (tlift 1 0 t0) B Hconv2 A 0) as Hres.
    rewrite Hcancel in Hres. exact Hres.

  - (* sok_nu_gnd *)
    pose proof (typing_regular g _ Aout Hwf Hty) as HwfAout.
    apply kr_nu_inv2 in Hty. destruct Hty as [B [Hconv [Htybody Hwft]]].
    apply kr_gnd_inv2 in Htybody. destruct Htybody as [Hconv2 [Htyv [Hg HwfG]]].
    assert (Hnu : typing_kr g (nu K A v) (tsubst A 0 G)) by (eapply kr_nu; eauto).
    assert (HwfG' : wf_typ g (tsubst A 0 G) KStar).
    { eapply (wf_typ_tsubst nil g K A G KStar); eauto.
      apply (wf_typ_def_to_kind nil g K A G KStar). exact HwfG. }
    assert (Hground' : ground (tsubst A 0 G)) by (apply ground_tsubst_shift; assumption).
    assert (Hgndnu : typing_kr g (gnd (nu K A v) (tsubst A 0 G)) dyn)
      by (eapply kr_gnd; eauto).
    eapply kr_conv; [exact Hgndnu | | exact HwfAout].
    apply ty_conv_to_equiv in Hconv2.
    pose proof (ty_equiv_tsubst dyn B Hconv2 A 0) as Hres. simpl in Hres.
    eapply ty_equiv_trans; [exact Hres |]. apply ty_conv_to_equiv in Hconv. exact Hconv.

  - (* sok_nu_tamper *)
    pose proof (typing_regular g _ Aout Hwf Hty) as HwfAout.
    apply kr_blame. exact HwfAout.

  - (* sok_nu_congr *)
    pose proof (typing_regular g _ Aout Hwf Hty) as HwfAout.
    apply kr_nu_inv2 in Hty. destruct Hty as [B [Hconv [Htybody Hwft]]].
    assert (Htybody' : typing_kr (has_def K A :: g) e' B)
      by (apply (IHHstep (has_def K A :: g) B); [constructor; assumption | exact Htybody]).
    assert (Hnu : typing_kr g (nu K A e') (tsubst A 0 B)) by (eapply kr_nu; eauto).
    eapply apply_ty_conv_to_kr; eauto.

  - (* sok_nu_blame *)
    pose proof (typing_regular g _ Aout Hwf Hty) as HwfAout.
    apply kr_blame. exact HwfAout.

  - (* sok_generalize *)
    pose proof (typing_regular g _ Aout Hwf Hty) as HwfAout.
    apply kr_cast_inv2 in Hty.
    destruct Hty as [Hconv [Htyv [Hcomp [HwfA HwfAllKB]]]].
    inversion HwfAllKB as [ | | HwfB | | | ]; subst.
    assert (Hcompgen : compat (tlift 1 0 A) B) by (apply (compat_generalize_inv A K B); assumption).
    assert (Hv' : typing_kr (has_kind K :: g) (term_tlift 1 0 v) (tlift 1 0 A))
      by (apply typing_kr_weaken_kind0; exact Htyv).
    assert (HwfA' : wf_typ (has_kind K :: g) (tlift 1 0 A) KStar)
      by (apply (wf_typ_weaken_kind nil g K A KStar); exact HwfA).
    assert (Hcast' : typing_kr (has_kind K :: g) (cast (term_tlift 1 0 v) (tlift 1 0 A) B p) B)
      by (eapply kr_cast; eauto).
    assert (Htabs : typing_kr g (tabs K (cast (term_tlift 1 0 v) (tlift 1 0 A) B p)) (all K B))
      by (apply kr_tabs; exact Hcast').
    eapply apply_ty_conv_to_kr; eauto.

  - (* sok_instantiate *)
    pose proof (typing_regular g _ Aout Hwf Hty) as HwfAout.
    apply kr_cast_inv2 in Hty.
    destruct Hty as [Hconv [Htyv [Hcomp [HwfAllA HwfB]]]].
    inversion HwfAllA as [ | | HwfA0 | | | ]; subst.
    assert (Hcompinst : compat (tsubst dyn 0 A) B) by (apply compat_instantiate_inv; assumption).
    assert (Htapp : typing_kr g (tapp v dyn) (tsubst dyn 0 A))
      by (eapply kr_tapp; [exact Htyv | apply wf_dyn]).
    assert (HwfAsub : wf_typ g (tsubst dyn 0 A) KStar)
      by (eapply (wf_typ_tsubst nil g KStar dyn A KStar); eauto; apply wf_dyn).
    assert (Hcast' : typing_kr g (cast (tapp v dyn) (tsubst dyn 0 A) B p) B)
      by (eapply kr_cast; eauto).
    eapply apply_ty_conv_to_kr; eauto.

  - (* sok_all_all *)
    pose proof (typing_regular g _ Aout Hwf Hty) as HwfAout.
    apply kr_cast_inv2 in Hty.
    destruct Hty as [Hconv [Htyv [Hcomp [HwfAllA HwfAllB]]]].
    inversion HwfAllA as [ | | HwfA | | | ]; subst.
    inversion HwfAllB as [ | | HwfB | | | ]; subst.
    assert (Hcompab : compat A B) by (apply (compat_all_inv K A B); assumption).
    assert (Hv' : typing_kr (has_kind K :: g) (term_tlift 1 0 v) (all K (tlift 1 1 A))).
    { pose proof (typing_kr_weaken_kind0 g v (all K A) K Htyv) as Hw. simpl in Hw. exact Hw. }
    assert (Happ : typing_kr (has_kind K :: g) (tapp (term_tlift 1 0 v) (tvar 0)) A).
    { pose proof (kr_tapp (has_kind K :: g) (term_tlift 1 0 v) (tlift 1 1 A) (tvar 0) K Hv')
        as Htp.
      rewrite tsubst_tvar0_tlift1 in Htp.
      apply Htp. apply wf_tvar. reflexivity. }
    assert (Hcast' : typing_kr (has_kind K :: g) (cast (tapp (term_tlift 1 0 v) (tvar 0)) A B p) B)
      by (eapply kr_cast; eauto).
    assert (Htabs : typing_kr g (tabs K (cast (tapp (term_tlift 1 0 v) (tvar 0)) A B p)) (all K B))
      by (apply kr_tabs; exact Hcast').
    eapply apply_ty_conv_to_kr; eauto.

  - (* sok_app_left *)
    pose proof (typing_regular g _ Aout Hwf Hty) as HwfAout.
    apply kr_app_inv2 in Hty. destruct Hty as [A0 [B0 [Hconv [Hty1 Hty2]]]].
    assert (Hty1' : typing_kr g e2 (arrow A0 B0))
      by (apply (IHHstep g (arrow A0 B0)); [exact Hwf | exact Hty1]).
    assert (Happ : typing_kr g (app e2 x) B0) by (eapply kr_app; eauto).
    eapply apply_ty_conv_to_kr; eauto.

  - (* sok_app_right *)
    pose proof (typing_regular g _ Aout Hwf Hty) as HwfAout.
    apply kr_app_inv2 in Hty. destruct Hty as [A0 [B0 [Hconv [Hty1 Hty2]]]].
    assert (Hty2' : typing_kr g x2 A0)
      by (apply (IHHstep g A0); [exact Hwf | exact Hty2]).
    assert (Happ : typing_kr g (app v x2) B0) by (eapply kr_app; eauto).
    eapply apply_ty_conv_to_kr; eauto.

  - (* sok_tapp_congr *)
    pose proof (typing_regular g _ Aout Hwf Hty) as HwfAout.
    apply kr_tapp_inv2 in Hty. destruct Hty as [K0 [t0 [Hconv [Hty1 Hwft]]]].
    assert (Hty1' : typing_kr g e2 (all K0 t0))
      by (apply (IHHstep g (all K0 t0)); [exact Hwf | exact Hty1]).
    assert (Htapp : typing_kr g (tapp e2 t) (tsubst t 0 t0)) by (eapply kr_tapp; eauto).
    eapply apply_ty_conv_to_kr; eauto.

  - (* sok_cast_congr *)
    pose proof (typing_regular g _ Aout Hwf Hty) as HwfAout.
    apply kr_cast_inv2 in Hty. destruct Hty as [Hconv [Hty1 [Hcomp [HwfA HwfB]]]].
    assert (Hty1' : typing_kr g e2 A) by (apply (IHHstep g A); [exact Hwf | exact Hty1]).
    assert (Hcast' : typing_kr g (cast e2 A B p) B) by (eapply kr_cast; eauto).
    eapply apply_ty_conv_to_kr; eauto.

  - (* sok_gnd_congr *)
    pose proof (typing_regular g _ Aout Hwf Hty) as HwfAout.
    apply kr_gnd_inv2 in Hty. destruct Hty as [Hconv [Hty1 [Hg HwfG]]].
    assert (Hty1' : typing_kr g e2 G) by (apply (IHHstep g G); [exact Hwf | exact Hty1]).
    assert (Hgnd' : typing_kr g (gnd e2 G) dyn) by (eapply kr_gnd; eauto).
    eapply apply_ty_conv_to_kr; eauto.

  - (* sok_is_gnd_congr *)
    pose proof (typing_regular g _ Aout Hwf Hty) as HwfAout.
    apply kr_is_gnd_inv2 in Hty. destruct Hty as [Hconv Hty1].
    assert (Hty1' : typing_kr g e2 dyn) by (apply (IHHstep g dyn); [exact Hwf | exact Hty1]).
    assert (Hisgnd' : typing_kr g (is_gnd e2 G) (arrow dyn (arrow dyn dyn)))
      by (apply kr_is_gnd; exact Hty1').
    eapply apply_ty_conv_to_kr; eauto.

  - (* sok_app_blame_l *)
    pose proof (typing_regular g _ Aout Hwf Hty) as HwfAout.
    apply kr_blame. exact HwfAout.

  - (* sok_app_blame_r *)
    pose proof (typing_regular g _ Aout Hwf Hty) as HwfAout.
    apply kr_blame. exact HwfAout.

  - (* sok_tapp_blame *)
    pose proof (typing_regular g _ Aout Hwf Hty) as HwfAout.
    apply kr_blame. exact HwfAout.

  - (* sok_cast_blame *)
    pose proof (typing_regular g _ Aout Hwf Hty) as HwfAout.
    apply kr_blame. exact HwfAout.

  - (* sok_gnd_blame *)
    pose proof (typing_regular g _ Aout Hwf Hty) as HwfAout.
    apply kr_blame. exact HwfAout.

  - (* sok_is_gnd_blame *)
    pose proof (typing_regular g _ Aout Hwf Hty) as HwfAout.
    apply kr_blame. exact HwfAout.
Qed.
