(** * BlameFOmega.subtyping: Subtyping relations and their metatheory.

    Defines ordinary subtyping [A <: B], positive subtyping [A <:+ B], and
    negative subtyping [A <:- B] (adapted from Figure 5 of Blame for All),
    together with the mutual
    induction scheme, preservation under type lifting, inversion lemmas,
    and interactions with compatibility and ground types.

    In this Fω setting the [_all_l]/[_all_r] rules are *guarded* (target/source
    not a [∀]) and a [∀]-congruence rule ([_all_cong]) is added, so that a
    [∀]/[∀] relation is derivable only congruently.  This is what makes the
    structural [∀]/[∀] cast ([step_all_all]) blame-sound: [(∀K.A) <:+ (∀K.B)]
    inverts to [A <:+ B]. *)

From Stdlib Require Import Arith.
From Stdlib Require Import Compare_dec.
From Stdlib Require Import Lia.
From BlameFOmega Require Import syntax.
From BlameFOmega Require Import infrastructure.

(** ** Subtyping relations *)

(** Ordinary subtyping [A <: B] (Figure 5): reflexive, structural, with [dyn] as
    top via ground types. *)
Inductive subtype: typ -> typ -> Prop :=
  | sub_refl: forall A, subtype A A
  | sub_dyn: forall A G, subtype A G -> ground G -> subtype A dyn
  | sub_arrow: forall A B A' B',
    subtype A' A -> subtype B B' ->
    subtype (arrow A B) (arrow A' B')
  | sub_all_l: forall A B,
    (forall K' B', B <> all K' B') ->
    subtype (tsubst dyn 0 A) B ->
    subtype (all KStar A) B
  | sub_all_r: forall K A B,
    (forall K' C, A <> all K' C) ->
    subtype (tlift 1 0 A) B ->
    subtype A (all K B)
  | sub_all_cong: forall K A B,
    subtype A B ->
    subtype (all K A) (all K B).

(** Positive subtyping [A <:+ B] (Figure 5, mutually defined with [neg_subtype]):
    tracks subtyping in covariant positions; [dyn] is always a supertype. *)
Inductive pos_subtype: typ -> typ -> Prop :=
  | psub_refl: forall A, pos_subtype A A
  | psub_dyn: forall A, pos_subtype A dyn
  | psub_arrow: forall A B A' B',
    neg_subtype A' A -> pos_subtype B B' ->
    pos_subtype (arrow A B) (arrow A' B')
  | psub_all_l: forall A B,
    (forall K' B', B <> all K' B') ->
    pos_subtype (tsubst dyn 0 A) B ->
    pos_subtype (all KStar A) B
  | psub_all_r: forall K A B,
    (forall K' C, A <> all K' C) ->
    pos_subtype (tlift 1 0 A) B ->
    pos_subtype A (all K B)
  | psub_all_cong: forall K A B,
    pos_subtype A B ->
    pos_subtype (all K A) (all K B)
(** Negative subtyping [A <:- B]: tracks subtyping in contravariant positions; [dyn] is always a subtype. *)
with neg_subtype: typ -> typ -> Prop :=
  | nsub_refl: forall A, neg_subtype A A
  | nsub_dyn_l: forall B, neg_subtype dyn B
  | nsub_dyn_r: forall A G, neg_subtype A G -> ground G -> neg_subtype A dyn
  | nsub_arrow: forall A B A' B',
    pos_subtype A' A -> neg_subtype B B' ->
    neg_subtype (arrow A B) (arrow A' B')
  | nsub_all_l: forall A B,
    (forall K' B', B <> all K' B') ->
    neg_subtype (tsubst dyn 0 A) B ->
    neg_subtype (all KStar A) B
  | nsub_all_r: forall K A B,
    (forall K' C, A <> all K' C) ->
    neg_subtype (tlift 1 0 A) B ->
    neg_subtype A (all K B)
  | nsub_all_cong: forall K A B,
    neg_subtype A B ->
    neg_subtype (all K A) (all K B).

Hint Constructors subtype pos_subtype neg_subtype: blame.

(** ** Mutual induction scheme for pos/neg subtyping *)

(** Generated mutual induction scheme for [pos_subtype] and [neg_subtype]. *)
Scheme pos_subtype_ind2 := Induction for pos_subtype Sort Prop
  with neg_subtype_ind2 := Induction for neg_subtype Sort Prop.

(** Combined scheme to prove properties of both [pos_subtype] and [neg_subtype] simultaneously. *)
Combined Scheme pos_neg_subtype_ind from pos_subtype_ind2, neg_subtype_ind2.

(** ** [∀]-guard helpers

    The guards on [_all_l]/[_all_r] are "the type is not a [∀]".  [tlift] and
    [tswap] preserve non-[∀]-ness (they don't create or destroy a top-level
    [∀]), so the guards survive those operations — needed for preservation. *)

Lemma tswap_not_all: forall A,
  (forall K C, A <> all K C) -> forall k K C, tswap k A <> all K C.
Proof.
  intros A Hna k K C Heq.
  destruct A; simpl in Heq; try (repeat destruct (Nat.eq_dec _ _)); try discriminate.
  injection Heq; intros; subst. eapply Hna; reflexivity.
Qed.

(** ** Ground / ground-tag bridges to subtyping *)

(** Every arrow type positively subtypes [? → ?], the unique arrow ground type. *)
Lemma pos_subtype_arrow_arrow_dyn: forall A1 A2,
  pos_subtype (arrow A1 A2) (arrow dyn dyn).
Proof. intros. apply psub_arrow; [apply nsub_dyn_l | apply psub_dyn]. Qed.

(** If [A <:- G] for some ground [G], then [A <:- ?]. *)
Lemma neg_subtype_to_dyn: forall A G, ground G -> neg_subtype A G -> neg_subtype A dyn.
Proof. intros. apply nsub_dyn_r with (G := G); auto. Qed.

(** A ground type has a ground tag. *)
Lemma ground_has_tag: forall G, ground G -> exists G', ground_tag G G'.
Proof.
  intros G HG. inversion HG; subst.
  - eexists; apply gt_arrow.
  - eexists; apply gt_neutral; assumption.
Qed.

(** [all]/[dyn] are not ground (convenience absurdity forms). *)
Lemma ground_all_absurd: forall K A, ~ ground (all K A).
Proof. intros K A H. exact (ground_not_all _ H K A eq_refl). Qed.
Lemma ground_dyn_absurd: ~ ground dyn.
Proof. intro H. exact (ground_not_dyn _ H eq_refl). Qed.

(** The GROUND reduct's inner cast [cast v A G] carries positive evidence:
    an arrow injects at [? → ?] (covariantly [dyn]), a neutral at itself. *)
Lemma ground_tag_pos: forall A G, ground_tag A G -> pos_subtype A G.
Proof.
  intros A G H. inversion H; subst.
  - apply pos_subtype_arrow_arrow_dyn.
  - apply psub_refl.
Qed.

(** No arrow type negatively subtypes a neutral type (heads differ). *)
Lemma neg_subtype_arrow_not_neutral: forall A1 A2 N,
  neutral N -> ~ neg_subtype (arrow A1 A2) N.
Proof.
  intros A1 A2 N HN Hn. inversion Hn; subst; try discriminate;
    match goal with H: neutral _ |- _ => solve [inversion H] end.
Qed.

(** Invert [arrow A1 A2 <:- ?] into [arrow A1 A2 <:- ? → ?]. *)
Lemma neg_subtype_arrow_dyn_inv: forall A1 A2,
  neg_subtype (arrow A1 A2) dyn -> neg_subtype (arrow A1 A2) (arrow dyn dyn).
Proof.
  intros A1 A2 H. inversion H; subst; try discriminate.
  match goal with Hn: neg_subtype (arrow A1 A2) ?G, Hg: ground ?G |- _ =>
    inversion Hg; subst;
    [ exact Hn
    | exfalso; eapply neg_subtype_arrow_not_neutral; eauto ]
  end.
Qed.

(** For neutral tags the inner cast carries negative evidence for free; for the
    arrow tag it follows from the outer [A <:- ?] evidence. *)
Lemma neg_subtype_ground_tag_from_dyn: forall A G,
  ground_tag A G -> neg_subtype A dyn -> neg_subtype A G.
Proof.
  intros A G Htag Hdyn. inversion Htag; subst.
  - apply neg_subtype_arrow_dyn_inv. exact Hdyn.
  - apply nsub_refl.
Qed.

(** ** [?]-on-the-left bridges (COLLAPSE / CONFLICT) *)

(** If [? <:+ A], then [G <:+ A] for every ground [G] (grounds are never [∀],
    so the guarded [psub_all_r] applies).  Replaces the old fully-universal
    form; the ground restriction is all COLLAPSE needs. *)
Lemma pos_subtype_dyn_ground:
  forall A, pos_subtype dyn A -> forall G, ground G -> pos_subtype G A.
Proof.
  intros A H. remember dyn as d eqn:Hd. revert Hd.
  induction H; intros Hd G Hg; subst; try discriminate.
  - apply psub_dyn.
  - apply psub_dyn.
  - apply psub_all_r.
    + intros K' C. eapply ground_not_all; eauto.
    + apply IHpos_subtype; [reflexivity | apply ground_tlift; assumption].
Qed.

(** If [? <:+ A], then every ground type [G] is compatible with [A]. Used to
    derive contradictions in the CONFLICT case. *)
Lemma pos_subtype_dyn_compat_ground:
  forall A, pos_subtype dyn A -> forall G, ground G -> compat G A.
Proof.
  intros A H. remember dyn as d eqn:Hd. revert Hd.
  induction H; intros Hd G Hg; subst; try discriminate.
  - (* A = dyn *) eapply compat_to_dyn;
      [ apply ground_not_dyn; assumption
      | intros K C; eapply ground_not_all; eauto
      | inversion Hg; subst; [apply gt_arrow | apply gt_neutral; assumption]
      | apply compat_refl ].
  - (* A = dyn *) eapply compat_to_dyn;
      [ apply ground_not_dyn; assumption
      | intros K C; eapply ground_not_all; eauto
      | inversion Hg; subst; [apply gt_arrow | apply gt_neutral; assumption]
      | apply compat_refl ].
  - (* A = all K B *) apply compat_generalize.
    + apply ground_not_dyn; assumption.
    + intros K' C; eapply ground_not_all; eauto.
    + apply IHpos_subtype; [reflexivity | apply ground_tlift; assumption].
Qed.

(** A ground type compatible with [A] negatively subtypes [A]. *)
Lemma neg_subtype_ground_compat:
  forall G A, ground G -> compat G A -> neg_subtype G A.
Proof.
  intros G A Hg Hc. revert Hg. induction Hc; intros Hg.
  - (* refl *) apply nsub_refl.
  - (* arrow: G = arrow dyn dyn *)
    inversion Hg; subst;
      [| match goal with H: neutral (arrow _ _) |- _ => inversion H end].
    apply nsub_arrow; [apply psub_dyn | apply nsub_dyn_l].
  - (* all: ground is never all *)
    exfalso; eapply ground_not_all; eauto.
  - (* generalize: target all K B *)
    apply nsub_all_r.
    + intros K' C; eapply ground_not_all; eauto.
    + apply IHHc. apply ground_tlift. assumption.
  - (* instantiate: source all KStar, ground never all *)
    exfalso; eapply ground_not_all; eauto.
  - (* to_dyn: target dyn *)
    eapply nsub_dyn_r; [apply nsub_refl | assumption].
  - (* from_dyn: source dyn, not ground *)
    exfalso; apply (ground_not_dyn _ Hg); reflexivity.
Qed.

(** ** Preservation under type lifting *)

(** Positive and negative subtyping are preserved by type lifting. *)
Lemma pos_neg_subtype_tlift:
  (forall A B, pos_subtype A B -> forall i k, pos_subtype (tlift i k A) (tlift i k B)) /\
  (forall A B, neg_subtype A B -> forall i k, neg_subtype (tlift i k A) (tlift i k B)).
Proof.
  apply pos_neg_subtype_ind; intros; simpl; eauto with blame.
  - apply psub_all_l; [apply tlift_not_all; assumption |].
    rewrite <- tlift_tsubst_dyn. auto.
  - apply psub_all_r; [apply tlift_not_all; assumption |].
    rewrite tlift_comm_10. auto.
  - apply nsub_dyn_r with (G := tlift i k G); auto. apply ground_tlift. auto.
  - apply nsub_all_l; [apply tlift_not_all; assumption |].
    rewrite <- tlift_tsubst_dyn. auto.
  - apply nsub_all_r; [apply tlift_not_all; assumption |].
    rewrite tlift_comm_10. auto.
Qed.

(** Positive subtyping is preserved by type lifting. *)
Definition pos_subtype_tlift := proj1 pos_neg_subtype_tlift.
(** Negative subtyping is preserved by type lifting. *)
Definition neg_subtype_tlift := proj2 pos_neg_subtype_tlift.

(** ** Inversion lemmas for positive/negative subtyping *)

(** If [A <:+ ∀B] and [A] is not itself a [∀], then [↑A <:+ B]. Used for GENERALIZE. *)
Lemma pos_subtype_all_r_inv:
  forall K A B, pos_subtype A (all K B) -> (forall K' C, A <> all K' C) ->
  pos_subtype (tlift 1 0 A) B.
Proof.
  intros K A B H Hna. inversion H; subst;
    try (exfalso; eapply Hna; reflexivity); try assumption.
Qed.

(** If [A <:- ∀B] and [A] is not itself a [∀], then [↑A <:- B]. Used for GENERALIZE. *)
Lemma neg_subtype_all_r_inv:
  forall K A B, neg_subtype A (all K B) -> (forall K' C, A <> all K' C) ->
  neg_subtype (tlift 1 0 A) B.
Proof.
  intros K A B H Hna. inversion H; subst;
    try (exfalso; eapply Hna; reflexivity); try assumption;
    simpl; apply nsub_dyn_l.
Qed.

(** If [∀A <:+ B] and [B] is not [∀], then [A[?/0] <:+ B]. Used for INSTANTIATE. *)
Lemma pos_subtype_all_l_inv:
  forall K A B, pos_subtype (all K A) B -> (forall K' B', B <> all K' B') ->
  pos_subtype (tsubst dyn 0 A) B.
Proof.
  intros K A B H Hna. inversion H; subst;
    try (exfalso; eapply Hna; reflexivity); try assumption; apply psub_dyn.
Qed.

(** If [∀A <:- B] and [B] is not [∀], then [A[?/0] <:- B]. Used for INSTANTIATE. *)
Lemma neg_subtype_all_l_inv:
  forall K A B, neg_subtype (all K A) B -> (forall K' B', B <> all K' B') ->
  neg_subtype (tsubst dyn 0 A) B.
Proof.
  intros K A B H Hna. inversion H; subst;
    try (exfalso; eapply Hna; reflexivity); try assumption.
  (* remaining: nsub_dyn_r with B = dyn *)
  all: match goal with
  | Hn: neg_subtype (all _ _) ?G, Hg: ground ?G |- _ =>
    apply nsub_dyn_r with (G := G); [| exact Hg];
    inversion Hn; subst;
      try assumption;
      try (exfalso; match goal with Hgr: ground (all _ _) |- _ =>
             eapply ground_all_absurd; exact Hgr end);
      try (exfalso; match goal with Hgr: ground dyn |- _ =>
             exact (ground_dyn_absurd Hgr) end)
  end.
Qed.

(** [∀]-congruence inverts to body subtyping. Used for the structural [∀]/[∀]
    cast (step_all_all): only [psub_refl] and [psub_all_cong] can derive a
    [∀]/[∀] pair (the guards exclude [psub_all_l]/[psub_all_r]). *)
Lemma pos_subtype_all_cong_inv:
  forall K A B, pos_subtype (all K A) (all K B) -> pos_subtype A B.
Proof.
  intros K A B H. inversion H; subst;
    try apply psub_refl; try assumption;
    exfalso; match goal with Hg: forall _ _, _ <> all _ _ |- _ => eapply Hg; reflexivity end.
Qed.

Lemma neg_subtype_all_cong_inv:
  forall K A B, neg_subtype (all K A) (all K B) -> neg_subtype A B.
Proof.
  intros K A B H. inversion H; subst;
    try apply nsub_refl; try assumption;
    exfalso; match goal with Hg: forall _ _, _ <> all _ _ |- _ => eapply Hg; reflexivity end.
Qed.

(** Extract components from a positive arrow subtyping. *)
Lemma pos_subtype_arrow_inv: forall A B A' B',
  pos_subtype (arrow A B) (arrow A' B') ->
  neg_subtype A' A /\ pos_subtype B B'.
Proof.
  intros A B A' B' H. inversion H; subst.
  - split; auto with blame.
  - auto.
Qed.

(** Extract components from a negative arrow subtyping. *)
Lemma neg_subtype_arrow_inv: forall A B A' B',
  neg_subtype (arrow A B) (arrow A' B') ->
  pos_subtype A' A /\ neg_subtype B B'.
Proof.
  intros A B A' B' H. inversion H; subst.
  - split; auto with blame.
  - auto.
Qed.

(** ** Preservation under adjacent type-variable swap *)

(** Neutrality is preserved by adjacent type-variable swap. *)
Lemma neutral_tswap: forall N k, neutral N -> neutral (tswap k N).
Proof.
  intros N k HN. revert k. induction HN; intros k; simpl.
  - destruct (Nat.eq_dec n k); [apply neutral_tvar |].
    destruct (Nat.eq_dec n (S k)); apply neutral_tvar.
  - apply neutral_tyapp. apply IHHN.
Qed.

(** Groundness is preserved by adjacent type-variable swap. *)
Lemma ground_tswap: forall G k, ground G -> ground (tswap k G).
Proof.
  intros G k HG. inversion HG; subst; simpl.
  - apply ground_arrow.
  - apply ground_neutral. apply neutral_tswap. assumption.
Qed.

(** Positive and negative subtyping are preserved by adjacent type-variable swap. *)
Lemma pos_neg_subtype_tswap:
  (forall A B, pos_subtype A B -> forall k, pos_subtype (tswap k A) (tswap k B)) /\
  (forall A B, neg_subtype A B -> forall k, neg_subtype (tswap k A) (tswap k B)).
Proof.
  apply pos_neg_subtype_ind; intros; simpl; eauto with blame.
  - apply psub_all_l; [apply tswap_not_all; assumption |].
    rewrite <- tswap_tsubst_dyn. auto.
  - apply psub_all_r; [apply tswap_not_all; assumption |].
    rewrite <- tswap_tlift_10. auto.
  - apply nsub_dyn_r with (G := tswap k G); [auto | apply ground_tswap; assumption].
  - apply nsub_all_l; [apply tswap_not_all; assumption |].
    rewrite <- tswap_tsubst_dyn. auto.
  - apply nsub_all_r; [apply tswap_not_all; assumption |].
    rewrite <- tswap_tlift_10. auto.
Qed.

Definition pos_subtype_tswap := proj1 pos_neg_subtype_tswap.
Definition neg_subtype_tswap := proj2 pos_neg_subtype_tswap.

(** ** Ordinary subtyping metatheory *)

(** Ordinary subtyping is preserved by type lifting. *)
Lemma subtype_tlift: forall A B, subtype A B -> forall i k, subtype (tlift i k A) (tlift i k B).
Proof.
  induction 1; intros; simpl; eauto with blame.
  - apply sub_dyn with (G := tlift i k G); auto. apply ground_tlift. auto.
  - apply sub_all_l; [apply tlift_not_all; assumption |].
    rewrite <- tlift_tsubst_dyn. auto.
  - apply sub_all_r; [apply tlift_not_all; assumption |].
    rewrite tlift_comm_10. auto.
Qed.

(** Ordinary subtyping is preserved by adjacent type-variable swap. *)
Lemma subtype_tswap: forall A B, subtype A B -> forall k, subtype (tswap k A) (tswap k B).
Proof.
  induction 1; intros k; simpl; eauto with blame.
  - apply sub_dyn with (G := tswap k G); [auto | apply ground_tswap; assumption].
  - apply sub_all_l; [apply tswap_not_all; assumption |].
    rewrite <- tswap_tsubst_dyn. auto.
  - apply sub_all_r; [apply tswap_not_all; assumption |].
    rewrite <- tswap_tlift_10. auto.
Qed.

(** If [? <: A], then every ground type is compatible with [A]. Used to derive
    contradictions in CONFLICT cases. *)
Lemma subtype_dyn_compat:
  forall A, subtype dyn A -> forall G, ground G -> compat G A.
Proof.
  intros A H. remember dyn as d eqn:Hd. revert Hd.
  induction H; intros Hd Gc Hg; subst; try discriminate.
  - (* sub_refl: A = dyn *) eapply compat_to_dyn;
      [ apply ground_not_dyn; assumption
      | intros K C; eapply ground_not_all; eauto
      | inversion Hg; subst; [apply gt_arrow | apply gt_neutral; assumption]
      | apply compat_refl ].
  - (* sub_dyn: A = dyn *) eapply compat_to_dyn;
      [ apply ground_not_dyn; assumption
      | intros K C; eapply ground_not_all; eauto
      | inversion Hg; subst; [apply gt_arrow | apply gt_neutral; assumption]
      | apply compat_refl ].
  - (* sub_all_r: A = all K B *) apply compat_generalize.
    + apply ground_not_dyn; assumption.
    + intros K' C; eapply ground_not_all; eauto.
    + apply IHsubtype; [reflexivity | apply ground_tlift; assumption].
Qed.

(** If [? <: A] then [G <: A] for ground [G]. Used in COLLAPSE. *)
Lemma subtype_dyn_ground:
  forall A, subtype dyn A -> forall G, ground G -> subtype G A.
Proof.
  intros A H. remember dyn as d eqn:Hd. revert Hd.
  induction H; intros Hd G' Hg; subst; try discriminate.
  - (* sub_refl *) apply sub_dyn with (G := G'); [apply sub_refl | assumption].
  - (* sub_dyn *) apply sub_dyn with (G := G'); [apply sub_refl | assumption].
  - (* sub_all_r *) apply sub_all_r.
    + intros K' C; eapply ground_not_all; eauto.
    + apply IHsubtype; [reflexivity | apply ground_tlift; assumption].
Qed.

(** If [? <: A] and ground [G] is compatible with [A], then [G <: A]. Used in
    COLLAPSE.  Kept for [subtyping_safety]; follows from [subtype_dyn_ground]. *)
Lemma subtype_from_dyn:
  forall A, subtype dyn A -> forall G, ground G -> compat G A -> subtype G A.
Proof.
  intros A H G Hg _. apply subtype_dyn_ground; assumption.
Qed.

(** No arrow type ordinarily subtypes a neutral type. *)
Lemma subtype_arrow_not_neutral: forall A1 A2 N,
  neutral N -> ~ subtype (arrow A1 A2) N.
Proof.
  intros A1 A2 N HN H. inversion H; subst; try discriminate;
    match goal with Hh: neutral _ |- _ => solve [inversion Hh] end.
Qed.

(** Invert [arrow A1 A2 <: ?] into [arrow A1 A2 <: ? → ?]. *)
Lemma subtype_arrow_dyn_inv: forall A1 A2,
  subtype (arrow A1 A2) dyn -> subtype (arrow A1 A2) (arrow dyn dyn).
Proof.
  intros A1 A2 H. inversion H; subst; try discriminate.
  match goal with Hw: subtype (arrow A1 A2) ?G, Hg: ground ?G |- _ =>
    inversion Hg; subst;
    [ exact Hw | exfalso; eapply subtype_arrow_not_neutral; eauto ]
  end.
Qed.

(** The GROUND reduct's inner cast carries ordinary subtyping evidence, given
    the outer [A <: ?].  (For neutral tags it is reflexivity; for the arrow tag
    it is [subtype_arrow_dyn_inv].) *)
Lemma subtype_ground_tag_from_dyn: forall A G,
  ground_tag A G -> subtype A dyn -> subtype A G.
Proof.
  intros A G Ht Hd. inversion Ht; subst.
  - apply subtype_arrow_dyn_inv. exact Hd.
  - apply sub_refl.
Qed.

(** If [A <: ?] and [A] has ground tag [G] (with [A] not [?]/[G]/[∀]), then
    [A <: G]. Used in GROUND. *)
Lemma subtype_ground_from_dyn:
  forall A G, subtype A dyn -> ground G -> compat A G ->
  A <> dyn -> A <> G -> (forall K C, A <> all K C) ->
  subtype A G.
Proof.
  intros A G Hsub Hg Hc Hnd Hng Hna.
  (* [compat A G] with [G] ground and [A] not [?]/[all] forces [A] to have a
     ground tag; that tag is [G] up to the shape of [G]. *)
  inversion Hc; subst.
  - (* refl: A = G *) exfalso; apply Hng; reflexivity.
  - (* arrow: A = arrow A1 A2, G = arrow B1 B2 *)
    inversion Hg; subst; [| match goal with H: neutral (arrow _ _) |- _ => inversion H end].
    apply subtype_arrow_dyn_inv. exact Hsub.
  - (* all target: G = all, impossible for ground *)
    exfalso; eapply ground_not_all; eauto.
  - (* generalize: G = all, impossible *)
    exfalso; eapply ground_not_all; eauto.
  - (* instantiate: A = all, excluded by Hna *)
    exfalso; eapply Hna; reflexivity.
  - (* to_dyn: G = dyn, impossible for ground *)
    exfalso; apply (ground_not_dyn _ Hg); reflexivity.
  - (* from_dyn: A = dyn, excluded *)
    exfalso; apply Hnd; reflexivity.
Qed.

(** If [A <: ∀B] and [A] is not a [∀], then [↑A <: B]. Used in GENERALIZE. *)
Lemma subtype_all_r_inv:
  forall K A B, subtype A (all K B) -> (forall K' C, A <> all K' C) -> subtype (tlift 1 0 A) B.
Proof.
  intros K A B H Hna. inversion H; subst;
    try (exfalso; eapply Hna; reflexivity); try assumption.
Qed.

(** If [∀A <: B] and [B] is not [∀], then [A[?/0] <: B]. Used in INSTANTIATE. *)
Lemma subtype_all_l_inv:
  forall K A B, subtype (all K A) B -> (forall K' B', B <> all K' B') ->
  subtype (tsubst dyn 0 A) B.
Proof.
  intros K A B H Hna. inversion H; subst;
    try (exfalso; eapply Hna; reflexivity); try assumption.
  (* remaining: sub_dyn with B = dyn *)
  all: match goal with
  | Hn: subtype (all _ _) ?G, Hg: ground ?G |- _ =>
    apply sub_dyn with (G := G); [| exact Hg];
    inversion Hn; subst;
      try assumption;
      try (exfalso; match goal with Hgr: ground (all _ _) |- _ =>
             eapply ground_all_absurd; exact Hgr end);
      try (exfalso; match goal with Hgr: ground dyn |- _ =>
             exact (ground_dyn_absurd Hgr) end)
  end.
Qed.

(** Ordinary [∀]-congruence inverts to body subtyping. *)
Lemma subtype_all_cong_inv:
  forall K A B, subtype (all K A) (all K B) -> subtype A B.
Proof.
  intros K A B H. inversion H; subst;
    try apply sub_refl; try assumption;
    exfalso; match goal with Hg: forall _ _, _ <> all _ _ |- _ => eapply Hg; reflexivity end.
Qed.
