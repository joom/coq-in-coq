(** * Source-side normal-form and strong-normalization facts

    These lemmas depend only on [CoC.*] (not on the target calculus or the
    extraction translation itself). *)

From Stdlib Require Import Arith Lia List Relations Bool Program.Equality.
Import ListNotations.
From CoC Require terms.
From CoC Require typing.
From CoC Require Import confluence.
From CoC Require Import inference.
From CoC Require Import strong_normalization.
From CoC Require Import decidable_conversion.

Import terms.
Import CoC.typing.

(** [lift_rec] reflects one-step reduction: every reduct of a lifted term is
    itself the lift of a reduct of the original.  ([lift_rec]'s definition is
    structurally head-preserving -- its output has the same top constructor as
    its input -- which is what lets each case invert cleanly.) *)
Lemma reduces_once_lift_inv : forall n k t u,
  reduces_once (lift_rec n t k) u ->
  {t' : term & ((u = lift_rec n t' k) * reduces_once t t')%type}.
Proof.
  intros n k t. revert k.
  induction t as [s | v | T IHT M IHM | M1 IHM1 M2 IHM2 | T1 IHT1 T2 IHT2];
    intros k u Hr.
  - simpl in Hr. inversion Hr.
  - simpl in Hr. destruct (le_gt_dec k v); inversion Hr.
  - simpl in Hr. dependent destruction Hr.
    + destruct (IHT k _ Hr) as [T' [-> Hr']].
      exists (lam T' M). split; [reflexivity | apply abs_reduces_left; exact Hr'].
    + destruct (IHM (S k) _ Hr) as [M'' [-> Hr'']].
      exists (lam T M''). split; [reflexivity | apply abs_reduces_right; exact Hr''].
  - (* app M1 M2 *)
    simpl in Hr.
    dependent destruction Hr.
    + (* beta: lift_rec n M1 k = lam T M0 *)
      destruct M1 as [s | v | T1' M1' | N1' N2' | P1' P2']; simpl in *.
      * discriminate.
      * destruct (le_gt_dec k v); discriminate.
      * match goal with Heq: lam _ _ = lam _ _ |- _ => injection Heq as -> -> end.
        exists (subst M2 M1'). split.
        -- symmetry. apply distribute_lift_subst.
        -- apply beta.
      * discriminate.
      * discriminate.
    + (* app_reduces_left: reduces_once (lift_rec n M1 k) N *)
      destruct (IHM1 k _ Hr) as [M1r [Heq Hr']].
      eexists. split.
      2: { apply app_reduces_left. exact Hr'. }
      simpl. rewrite Heq. reflexivity.
    + (* app_reduces_right: reduces_once (lift_rec n M2 k) N *)
      destruct (IHM2 k _ Hr) as [M2r [Heq Hr']].
      eexists. split.
      2: { apply app_reduces_right. exact Hr'. }
      simpl. rewrite Heq. reflexivity.
  - simpl in Hr. dependent destruction Hr.
    + destruct (IHT1 k _ Hr) as [T1' [-> Hr']].
      exists (prod T1' T2). split; [reflexivity | apply prod_reduces_left; exact Hr'].
    + destruct (IHT2 (S k) _ Hr) as [T2' [-> Hr']].
      exists (prod T1 T2'). split; [reflexivity | apply prod_reduces_right; exact Hr'].
Qed.

(** ** Normal-form function

    A total normal-form function on strongly-normalizing terms (every well-typed
    type is SN via [strong_normalization]).  Its two defining properties are that
    it is independent of the SN proof ([nf_pi]) and INVARIANT under reduction
    ([nf_stable_once]).  Composing the existing syntactic type extraction with [nf]
    yields a reduction-stable extraction that still reuses all the computable
    machinery: on the normal form the syntactic [classifier] is exactly right
    ([classifier_iff_is_large_nf]). *)

(** The normal form of a strongly-normalizing term, computed via [compute_normal_form]. *)
Definition nf (t: terms.term) (sn: strongly_normalizing t) : terms.term :=
  let (u, _, _) := compute_normal_form t sn in u.

(** [nf t] is a normal form of [t]: reachable by reduction and itself normal. *)
Lemma nf_spec : forall t sn, (reduces t (nf t sn) * normal (nf t sn))%type.
Proof.
  intros t sn. unfold nf.
  destruct (compute_normal_form t sn) as [u ru nu]. split; assumption.
Qed.

(** [t] reduces to its normal form [nf t]. *)
Lemma nf_reduces : forall t sn, reduces t (nf t sn).
Proof. intros t sn. apply (nf_spec t sn). Qed.

(** [nf t] is normal. *)
Lemma nf_normal : forall t sn, normal (nf t sn).
Proof. intros t sn. apply (nf_spec t sn). Qed.

(** [t] is convertible to its normal form. *)
Lemma nf_conv : forall t sn, convertible t (nf t sn).
Proof. intros t sn. apply reduces_convertible. apply nf_reduces. Qed.

(** The normal form is independent of the strong-normalization witness. *)
Lemma nf_pi : forall t sn1 sn2, nf t sn1 = nf t sn2.
Proof.
  intros t sn1 sn2. apply normal_form_uniqueness.
  - apply trans_convertible_convertible with t.
    + apply sym_convertible. apply nf_conv.
    + apply nf_conv.
  - apply nf_normal.
  - apply nf_normal.
Qed.

(** [lift_rec] preserves normality (it can only reflect a reduct back to an
    unlifted reduct of the original, by [reduces_once_lift_inv], contradicting
    normality of the original). *)
Lemma normal_lift : forall t, normal t -> forall n k, normal (lift_rec n t k).
Proof.
  intros t Ht n k u Hr.
  destruct (reduces_once_lift_inv n k t u Hr) as [t' [_ Hr']].
  exact (Ht t' Hr').
Qed.

(** [nf] commutes with lifting: normalizing a lifted term gives the same
    result as lifting the normal form. *)
Lemma nf_lift : forall t sn n k sn', nf (lift_rec n t k) sn' = lift_rec n (nf t sn) k.
Proof.
  intros t sn n k sn'. apply normal_form_uniqueness.
  - apply trans_convertible_convertible with (lift_rec n t k).
    + apply sym_convertible. apply nf_conv.
    + apply convertible_convertible_lift. apply nf_conv.
  - apply nf_normal.
  - apply normal_lift. apply nf_normal.
Qed.

(** Reduction-invariance: a step in the source does not change the normal form.
    This is what makes [nf]-then-extract reduction-stable. *)
Lemma nf_stable_once : forall t t' snt snt',
  reduces_once t t' -> nf t snt = nf t' snt'.
Proof.
  intros t t' snt snt' Hr. apply normal_form_uniqueness.
  - apply trans_convertible_convertible with t.
    + apply sym_convertible. apply nf_conv.
    + apply trans_convertible_convertible with t'.
      * apply sym_convertible. apply one_step_convertible_expansion. exact Hr.
      * apply nf_conv.
  - apply nf_normal.
  - apply nf_normal.
Qed.

(** Multi-step reduction is preserved by substitution on the right. *)
Lemma reduces_subst_right : forall t t' a k,
  reduces t t' -> reduces (subst_rec a t k) (subst_rec a t' k).
Proof.
  intros t t' a k Hr. induction Hr.
  - constructor.
  - eapply red_trans. apply reduces_once_subst_right. exact r. exact IHHr.
Qed.

(** Convertible-by-reduction terms have the same normal form (witness-independent). *)
Lemma nf_stable_star : forall t t' snt snt',
  reduces t t' -> nf t snt = nf t' snt'.
Proof.
  intros t t' snt snt' Hr. apply normal_form_uniqueness.
  - apply trans_convertible_convertible with t.
    + apply sym_convertible. apply nf_conv.
    + apply trans_convertible_convertible with t'.
      * apply reduces_convertible. exact Hr.
      * apply nf_conv.
  - apply nf_normal.
  - apply nf_normal.
Qed.


(** ** [nf] commutes with type constructors

    The normal form of a type constructor is that constructor applied to the
    normal forms of its parts (for [prod]/[lam]; [app] is different since a
    normalized head may fire a beta redex).  These let a nf-then-extract extraction
    decompose exactly like the existing syntactic extraction, so type preservation
    goes through unchanged, while classification is now taken on the (reduction-
    invariant) normal form. *)

(** Sorts are normal. *)
Lemma normal_sort : forall s, normal (sort_term s).
Proof. intros s u H. inversion H. Qed.

(** A product of normal components is normal. *)
Lemma normal_prod : forall A B, normal A -> normal B -> normal (prod A B).
Proof.
  intros A B nA nB u H. inversion H; subst; [eapply nA | eapply nB]; eassumption.
Qed.

(** [nf] of an already-normal term is itself. *)
Lemma nf_normal_eq : forall t sn, normal t -> nf t sn = t.
Proof.
  intros t sn Hn. symmetry. apply reduces_normal; [apply nf_reduces | exact Hn].
Qed.

(** [nf] leaves a sort unchanged. *)
Lemma nf_sort : forall s sn, nf (sort_term s) sn = sort_term s.
Proof. intros s sn. apply nf_normal_eq. apply normal_sort. Qed.

(** [nf] distributes over products. *)
Lemma nf_prod : forall A B snAB snA snB,
  nf (prod A B) snAB = prod (nf A snA) (nf B snB).
Proof.
  intros A B snAB snA snB. apply normal_form_uniqueness.
  - apply trans_convertible_convertible with (prod A B).
    + apply sym_convertible. apply nf_conv.
    + apply convertible_convertible_product; apply nf_conv.
  - apply nf_normal.
  - apply normal_prod; apply nf_normal.
Qed.

(** ** [nf] respects conversion (master lemma)

    Normal forms of convertible terms are equal.  This subsumes proof-irrelevance
    ([nf_pi]) and reduction-invariance ([nf_stable_once]/[nf_stable_star]), and --
    via [convertible_convertible_subst] -- gives the substitution congruence the
    beta case of the simulation needs (source substitution changes annotations
    only up to conversion, which [nf] then collapses). *)
Lemma nf_respects_conv : forall s t sns snt,
  convertible s t -> nf s sns = nf t snt.
Proof.
  intros s t sns snt Hconv. apply normal_form_uniqueness.
  - apply trans_convertible_convertible with s.
    + apply sym_convertible. apply nf_conv.
    + apply trans_convertible_convertible with t; [ exact Hconv | apply nf_conv ].
  - apply nf_normal.
  - apply nf_normal.
Qed.

(** Conversion congruence over application. *)
Lemma convertible_convertible_app :
  forall a b c d, convertible a b -> convertible c d ->
  convertible (terms.app a c) (terms.app b d).
Proof.
  intros a b c d H1 H2.
  apply trans_convertible_convertible with (terms.app a d).
  - induction H2; auto with coc core arith sets.
    + apply trans_conv_red with (terms.app a P); auto with coc core arith sets.
    + apply trans_conv_exp with (terms.app a P); auto with coc core arith sets.
  - induction H1; auto with coc core arith sets.
    + apply trans_conv_red with (terms.app P d); auto with coc core arith sets.
    + apply trans_conv_exp with (terms.app P d); auto with coc core arith sets.
Qed.

(** A non-lam-headed application of normal parts is normal. *)
Lemma normal_app_not_lam : forall M N,
  normal M -> normal N -> (forall T b, M <> lam T b) -> normal (terms.app M N).
Proof.
  intros M N HM HN Hnl u Hred. dependent destruction Hred.
  - eapply Hnl; reflexivity.
  - eapply HM; eassumption.
  - eapply HN; eassumption.
Qed.

(** Conversion congruence over lambda. *)
Lemma convertible_convertible_lam :
  forall a b c d, convertible a b -> convertible c d ->
  convertible (lam a c) (lam b d).
Proof.
  intros a b c d H1 H2.
  apply trans_convertible_convertible with (lam a d).
  - induction H2; auto with coc core arith sets.
    + apply trans_conv_red with (lam a P); auto with coc core arith sets.
    + apply trans_conv_exp with (lam a P); auto with coc core arith sets.
  - induction H1; auto with coc core arith sets.
    + apply trans_conv_red with (lam P d); auto with coc core arith sets.
    + apply trans_conv_exp with (lam P d); auto with coc core arith sets.
Qed.

(** A lambda of normal parts is normal. *)
Lemma normal_lam : forall A B, normal A -> normal B -> normal (lam A B).
Proof.
  intros A B HA HB u Hred. dependent destruction Hred.
  - eapply HA; eassumption.
  - eapply HB; eassumption.
Qed.

(** [nf] distributes over a lambda. *)
Lemma nf_lam : forall A B snAB snA snB,
  nf (lam A B) snAB = lam (nf A snA) (nf B snB).
Proof.
  intros A B snAB snA snB. apply normal_form_uniqueness.
  - apply trans_convertible_convertible with (lam A B).
    + apply sym_convertible. apply nf_conv.
    + apply convertible_convertible_lam; apply nf_conv.
  - apply nf_normal.
  - apply normal_lam; apply nf_normal.
Qed.

(** [nf] distributes over an application whose function normalizes to a non-lam. *)
Lemma nf_app_neutral : forall M N snMN snM snN,
  (forall T b, nf M snM <> lam T b) ->
  nf (terms.app M N) snMN = terms.app (nf M snM) (nf N snN).
Proof.
  intros M N snMN snM snN Hnl.
  apply normal_form_uniqueness.
  - apply trans_convertible_convertible with (terms.app M N).
    + apply sym_convertible. apply nf_conv.
    + apply convertible_convertible_app; apply nf_conv.
  - apply nf_normal.
  - apply normal_app_not_lam; [ apply nf_normal | apply nf_normal | exact Hnl ].
Qed.

(** ** SN witnesses for types

    To extract a type through [nf]/[extract_typ] inside the term extraction we need
    its strong-normalization witness.  Every type appearing in a derivation is
    the type of a well-typed term, and such types are strongly normalizing. *)

Lemma sn_normal : forall t, normal t -> strongly_normalizing t.
Proof.
  intros t Hn. apply Acc_intro. intros y Hy. red in Hy. destruct Hy as [Hy]. exfalso. exact (Hn y Hy).
Qed.

(** The type of a well-typed term is strongly normalizing (well-sorted types are
    SN by [strong_normalization]; the top sort [kind] is normal). *)
Lemma sn_of_type : forall e t T, has_type e t T -> strongly_normalizing T.
Proof.
  intros e t T H. destruct (type_case e t T H) as [[s Hs] | Hkind].
  - apply (strong_normalization e T (sort_term s) Hs).
  - subst T. apply sn_normal. apply normal_sort.
Qed.


(** ** "typing implies well-formed context"

    Used to define the reduction-stable context extraction by recursion on
    well-formedness (each binding is well-sorted, hence has an SN witness).  Since
    [has_type]/[well_formed] are [Type]-valued, this is just the CoC-library
    [has_type_well_formed]. *)
Definition has_type_t_well_formed_t := has_type_well_formed.


(** ** Context extraction

    Extractors from a well-formed cons context, then the context extraction by
    structural recursion on the environment (threading the well-formedness proof
    to supply each binding's SN witness).  Classification uses the decidable,
    reduction-stable [is_large_dec]; binding types/kinds go through the
    reduction-stable [extract_typ]/[extract_kind]. *)

(** Dropping the head binder of a well-formed context leaves it well-formed. *)
Lemma wf_tail : forall T e, well_formed (T :: e) -> well_formed e.
Proof.
  intros T e H. inversion_clear H.
  apply has_type_well_formed with T (sort_term s); assumption.
Qed.

(** Each binding of a well-formed context is strongly normalizing. *)
Lemma sn_of_binding : forall T e, well_formed (T :: e) -> strongly_normalizing T.
Proof.
  intros T e H. inversion_clear H.
  eapply strong_normalization; eassumption.
Qed.

(** ** Index suppliers for the term extraction *)

(** SN of a product codomain. *)
Lemma sn_of_prod_cod : forall e u V Ur,
  has_type e u (prod V Ur) -> strongly_normalizing Ur.
Proof.
  intros e u V Ur H.
  destruct (type_case e u (prod V Ur) H) as [[s Hs] | Hbad]; [| discriminate Hbad].
  apply (inversion_has_type_prod (strongly_normalizing Ur) e V Ur (sort_term s) Hs).
  intros s1 s2 HV HUr Hconv. eapply strong_normalization; eassumption.
Qed.
