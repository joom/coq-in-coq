(** * BlameFOmega.typing_metatheory: Weakening and substitution for the target.

    Structural lemmas for the [typing] and [wf_typ] judgments of the target
    calculus: weakening (inserting a term or type binding) and substitution
    (term-for-term and type-for-type).  These are intended prerequisites for
    a future subject-reduction theorem.

    The context is a single list carrying both term bindings ([has_type]) and
    type bindings ([has_kind]/[has_def]); term variables index the [has_type]
    entries ([lookup_term]) and type variables the [has_kind]/[has_def] entries
    ([lookup_kind]).  Weakening therefore shifts one namespace while leaving the
    other fixed, tracked by the counts [nterm]/[ntype] below. *)

From Stdlib Require Import Arith Lia List Relations.
From BlameFOmega Require Import syntax infrastructure typing ty_confluence.

(** Number of term-/type-variable bindings in a context prefix. *)
Fixpoint nterm (g : context) : nat :=
  match g with
  | nil => 0
  | has_type _ :: g' => S (nterm g')
  | _ :: g' => nterm g'
  end.

(** Number of type-variable bindings ([has_kind]/[has_def]) in a context prefix; the [nterm] counterpart. *)
Fixpoint ntype (g : context) : nat :=
  match g with
  | nil => 0
  | has_kind _ :: g' => S (ntype g')
  | has_def _ _ :: g' => S (ntype g')
  | has_type _ :: g' => ntype g'
  end.

(** Shift used by term weakening: indices [>= k] move up by one, others are unchanged. *)
Definition sh (k n : nat) : nat := if le_gt_dec k n then S n else n.

(** Unfolds [lift 1 k] on a variable in terms of [sh]. *)
Lemma lift1_var : forall k n, lift 1 k (var n) = var (sh k n).
Proof. intros; simpl; unfold sh; destruct (le_gt_dec k n); [f_equal; lia | reflexivity]. Qed.

(** ** Term weakening: inserting a [has_type] binding *)

(** Inserting a [has_type] binding at prefix [G1] shifts term-variable lookups
    by [sh (nterm G1)]: only the term namespace is affected. *)
Lemma lookup_term_weaken : forall G1 g C n,
  lookup_term (G1 ++ has_type C :: g) (sh (nterm G1) n) = lookup_term (G1 ++ g) n.
Proof.
  induction G1 as [|b G1 IH]; intros g C n; simpl.
  - unfold sh; simpl. destruct (le_gt_dec 0 n); [reflexivity | lia].
  - destruct b as [D | K | K D]; simpl.
    + (* has_type D *) unfold sh; simpl. destruct n as [|n']; simpl.
      * reflexivity.
      * destruct (le_gt_dec (nterm G1) n') eqn:E.
        -- specialize (IH g C n'). unfold sh in IH. rewrite E in IH. exact IH.
        -- specialize (IH g C n'). unfold sh in IH. rewrite E in IH. exact IH.
    + (* has_kind K *) rewrite IH. reflexivity.
    + (* has_def K D *) rewrite IH. reflexivity.
Qed.

(** Inserting a [has_type] binding leaves type-variable lookups unchanged
    (dual to [lookup_term_weaken]): the type namespace doesn't see term bindings. *)
Lemma lookup_kind_weaken_type : forall G1 g C n,
  lookup_kind (G1 ++ has_type C :: g) n = lookup_kind (G1 ++ g) n.
Proof.
  induction G1 as [|b G1 IH]; intros g C n; simpl.
  - reflexivity.
  - destruct b as [D | K | K D]; simpl.
    + apply IH.
    + destruct n; [reflexivity | apply IH].
    + destruct n; [reflexivity | apply IH].
Qed.

(** [wf_typ] is preserved by inserting a term binding (kinding ignores [has_type]). *)
Lemma wf_typ_weaken_type : forall G1 g C A K,
  wf_typ (G1 ++ g) A K -> wf_typ (G1 ++ has_type C :: g) A K.
Proof.
  intros G1 g C A K H. remember (G1 ++ g) as g0 eqn:Hg. revert G1 Hg.
  induction H; intros G1 Hg; subst.
  - apply wf_tvar. rewrite lookup_kind_weaken_type. auto.
  - apply wf_arrow; auto.
  - apply wf_all. apply (IHwf_typ (has_kind K :: G1)). reflexivity.
  - apply wf_tyabs. apply (IHwf_typ (has_kind K1 :: G1)). reflexivity.
  - eapply wf_tyapp; eauto.
  - apply wf_dyn.
Qed.

(** General term weakening at an arbitrary prefix. *)
Lemma lookup_def_weaken_type : forall G1 g C n,
  lookup_def (G1 ++ has_type C :: g) n = lookup_def (G1 ++ g) n.
Proof.
  induction G1 as [|b G1 IH]; intros g C n; simpl.
  - reflexivity.
  - destruct b as [D | K | K D]; simpl.
    + apply IH.
    + destruct n as [|n']; [reflexivity|]. rewrite IH. reflexivity.
    + destruct n as [|n']; [reflexivity|]. rewrite IH. reflexivity.
Qed.

Lemma defeq_weaken_type : forall G1 g C A B K,
  defeq (G1 ++ g) A B K -> defeq (G1 ++ has_type C :: g) A B K.
Proof.
  intros G1 g C A B K H. remember (G1 ++ g) as g0 eqn:Hg. revert G1 Hg.
  induction H; intros G1 Hg; subst.
  - apply deq_refl. apply wf_typ_weaken_type; auto.
  - apply deq_sym. apply IHdefeq. reflexivity.
  - eapply deq_trans; [apply IHdefeq1 | apply IHdefeq2]; reflexivity.
  - apply deq_ty_equiv; auto; apply wf_typ_weaken_type; auto.
  - eapply deq_def; eauto. rewrite lookup_def_weaken_type; auto.
    apply wf_typ_weaken_type; auto.
  - apply deq_arrow; [apply IHdefeq1 | apply IHdefeq2]; reflexivity.
  - apply deq_all. apply (IHdefeq (has_kind K :: G1)). reflexivity.
  - apply deq_tyabs. apply (IHdefeq (has_kind K1 :: G1)). reflexivity.
  - eapply deq_tyapp; [apply IHdefeq1 | apply IHdefeq2]; reflexivity.
Qed.

Lemma typing_weaken_term : forall G1 g e A C,
  typing (G1 ++ g) e A ->
  typing (G1 ++ has_type C :: g) (lift 1 (nterm G1) e) A.
Proof.
  intros G1 g e A C H. remember (G1 ++ g) as g0 eqn:Hg. revert G1 Hg.
  induction H; intros G1 Hg; subst.
  - (* var *) rewrite lift1_var. apply typing_var. rewrite lookup_term_weaken. auto.
  - (* abs *) simpl. apply typing_abs.
    + apply wf_typ_weaken_type; auto.
    + apply (IHtyping (has_type t1 :: G1)). reflexivity.
  - (* app *) simpl. eapply typing_app; eauto.
  - (* tabs *) simpl. apply typing_tabs. apply (IHtyping (has_kind K :: G1)). reflexivity.
  - (* tapp *) simpl. eapply typing_tapp; eauto. apply wf_typ_weaken_type; auto.
  - (* cast *) simpl. eapply typing_cast; eauto; apply wf_typ_weaken_type; auto.
  - (* gnd *) simpl. apply typing_gnd.
    + apply IHtyping; reflexivity.
    + inversion H0 as [g1 G' HGnd HWf]; subst. constructor.
      * exact HGnd.
      * apply wf_typ_weaken_type; exact HWf.
  - (* is_gnd *) simpl. apply typing_is_gnd; auto.
  - (* blame *) simpl. apply typing_blame. apply wf_typ_weaken_type; auto.
  - (* nu *) simpl. apply typing_nu.
    + apply (IHtyping (has_def K A :: G1)). reflexivity.
    + apply wf_typ_weaken_type; auto.
  - (* conv *) simpl. eapply typing_conv; [ apply IHtyping; reflexivity | | ].
    + apply defeq_weaken_type; exact H0.
    + apply wf_typ_weaken_type; auto.
Qed.

(** Front term weakening (the common case). *)
Corollary typing_weaken_term0 : forall g e A C,
  typing g e A -> typing (has_type C :: g) (lift 1 0 e) A.
Proof. intros g e A C H. exact (typing_weaken_term nil g e A C H). Qed.

(** [typing_abs_inv]/[typing_tabs_inv]/[typing_gnd_inv] (inversion of [typing]
    through [typing_conv]) are defined further below, once [typing_regular]
    is available (they need it to supply the [wf_typ] witnesses [defeq]'s
    [deq_refl]/[deq_ty_equiv] now require). *)

(** ** Canonical forms

    A value at a given head type has the corresponding introduction shape.  The
    proofs use the inversion lemmas above together with the head-distinctness
    facts from [ty_confluence] to rule out the other value shapes. *)

(** [canonical_arrow]/[canonical_all] are restated further below (after the
    [q_par]/[q_equiv] development and the restored [typing_abs_inv]/
    [typing_tabs_inv]/[typing_gnd_inv]), using [defeq]-level head-distinctness
    facts instead of the old [ty_equiv]-level ones. *)

(** ** [tlift] preserves the auxiliary judgments *)

(** [ty_step] commutes with [tlift]: reduction is stable under weakening the ambient context. *)
Lemma ty_step_tlift : forall A B, ty_step A B -> forall i k, ty_step (tlift i k A) (tlift i k B).
Proof.
  induction 1; intros i k; simpl; try (constructor; auto; fail).
  - rewrite distribute_tlift_tsubst. apply tystep_beta.
Qed.

(** [ty_equiv] is preserved by [tlift], lifted pointwise from [ty_step_tlift]. *)
Lemma ty_equiv_tlift : forall A B, ty_equiv A B -> forall i k, ty_equiv (tlift i k A) (tlift i k B).
Proof.
  unfold ty_equiv; induction 1; intros i k.
  - apply rst_step, ty_step_tlift; auto.
  - apply rst_refl.
  - apply rst_sym; auto.
  - eapply rst_trans; eauto.
Qed.

(** [compat] is preserved by [tlift]: weakening both sides of a cast preserves
    compatibility.  [tlift] keeps the head-constructor shape, so every guard
    ([A <> dyn], [A] not a [∀], [ground_tag], [cast_form]) survives it. *)
Lemma compat_tlift : forall A B, compat A B -> forall i k, compat (tlift i k A) (tlift i k B).
Proof.
  induction 1; intros i k; simpl.
  - apply compat_refl.
  - apply compat_arrow; auto.
  - apply compat_all; auto.
  - (* generalize *) apply compat_generalize.
    + apply tlift_not_dyn; assumption.
    + intros K' C; apply tlift_not_all; assumption.
    + rewrite (permute_tlift_rec A i k 1 0) by lia. apply (IHcompat i (S k)).
  - (* instantiate *) apply compat_instantiate.
    + intros K' B'; apply tlift_not_all; assumption.
    + rewrite <- tlift_tsubst_dyn. apply IHcompat.
  - (* to_dyn *) apply compat_to_dyn with (G := tlift i k G).
    + apply tlift_not_dyn; assumption.
    + intros K B; apply tlift_not_all; assumption.
    + apply ground_tag_tlift; assumption.
    + apply IHcompat.
  - (* from_dyn *) apply compat_from_dyn.
    + apply tlift_not_dyn; assumption.
    + apply cast_form_tlift; assumption.
Qed.

(** ** Type weakening: inserting a [has_kind] binding

    Inserting a fresh type variable shifts the type-variable namespace by one and
    tlifts the types stored in the more-recent (prefix) bindings.  [tlift_ctx]
    applies that shift to a prefix. *)

(** Apply [tlift i k] to the type(s) stored in a single binding, leaving [has_kind]'s bare kind untouched. *)
Definition tlift_binding (i k : nat) (b : binding) : binding :=
  match b with
  | has_type A => has_type (tlift i k A)
  | has_kind K => has_kind K
  | has_def K A => has_def K (tlift i k A)
  end.

(** Weaken every binding in a context prefix by the fresh type variable
    inserted at its own tail: binding [b] at depth [G'] is lifted by 1 at
    cutoff [ntype G'], since it sees exactly the type variables bound in [G']. *)
Fixpoint tlift_ctx (G : context) : context :=
  match G with
  | nil => nil
  | b :: G' => tlift_binding 1 (ntype G') b :: tlift_ctx G'
  end.

(** Inserting a [has_kind] binding at prefix [G1] (after [tlift_ctx]-weakening
    [G1] itself) shifts type-variable lookups by [sh (ntype G1)]. *)
Lemma lookup_kind_weaken_kind : forall G1 g K n,
  lookup_kind (tlift_ctx G1 ++ has_kind K :: g) (sh (ntype G1) n)
    = lookup_kind (G1 ++ g) n.
Proof.
  induction G1 as [|b G1 IH]; intros g K n; simpl.
  - unfold sh; simpl. destruct (le_gt_dec 0 n); [reflexivity | lia].
  - destruct b as [D | K' | K' D]; simpl.
    + apply IH.
    + unfold sh; simpl. destruct n as [|n']; simpl.
      * reflexivity.
      * specialize (IH g K n'). unfold sh in IH.
        destruct (le_gt_dec (ntype G1) n') eqn:E; simpl; exact IH.
    + unfold sh; simpl. destruct n as [|n']; simpl.
      * reflexivity.
      * specialize (IH g K n'). unfold sh in IH.
        destruct (le_gt_dec (ntype G1) n') eqn:E; simpl; exact IH.
Qed.

(** Dual to [lookup_kind_weaken_kind]: term-variable lookups are unaffected by
    the extra [has_kind] binding, but their stored types must be lifted to
    account for the type variable it introduces. *)
Lemma lookup_term_weaken_kind : forall G1 g K n,
  lookup_term (tlift_ctx G1 ++ has_kind K :: g) n
    = option_map (tlift 1 (ntype G1)) (lookup_term (G1 ++ g) n).
Proof.
  induction G1 as [|b G1 IH]; intros g K n; simpl.
  - reflexivity.
  - destruct b as [D | K' | K' D]; simpl.
    + destruct n as [|n']; simpl; [reflexivity | apply IH].
    + rewrite IH. destruct (lookup_term (G1 ++ g) n) as [x|]; simpl; [| reflexivity].
      f_equal. rewrite (permute_tlift_rec x 1 (ntype G1) 1 0) by lia. reflexivity.
    + rewrite IH. destruct (lookup_term (G1 ++ g) n) as [x|]; simpl; [| reflexivity].
      f_equal. rewrite (permute_tlift_rec x 1 (ntype G1) 1 0) by lia. reflexivity.
Qed.

(** Unfolds [tlift 1 k] on a variable in terms of [sh]; the type-level analogue of [lift1_var]. *)
Lemma tlift1_tvar : forall k n, tlift 1 k (tvar n) = tvar (sh k n).
Proof. intros; simpl; unfold sh; destruct (le_gt_dec k n); [f_equal; lia | reflexivity]. Qed.

Lemma wf_typ_weaken_kind : forall G1 g K A K0,
  wf_typ (G1 ++ g) A K0 ->
  wf_typ (tlift_ctx G1 ++ has_kind K :: g) (tlift 1 (ntype G1) A) K0.
Proof.
  intros G1 g K A K0 H. remember (G1 ++ g) as g0 eqn:Hg. revert G1 Hg.
  induction H; intros G1 Hg; subst.
  - rewrite tlift1_tvar. apply wf_tvar. rewrite lookup_kind_weaken_kind. auto.
  - simpl. apply wf_arrow; auto.
  - simpl. apply wf_all. apply (IHwf_typ (has_kind K0 :: G1)). reflexivity.
  - simpl. apply wf_tyabs. apply (IHwf_typ (has_kind K1 :: G1)). reflexivity.
  - simpl. eapply wf_tyapp; eauto.
  - simpl. apply wf_dyn.
Qed.

Lemma lookup_def_weaken_kind : forall G1 g K n,
  lookup_def (tlift_ctx G1 ++ has_kind K :: g) (sh (ntype G1) n)
    = match lookup_def (G1 ++ g) n with
      | None => None
      | Some (K', A) => Some (K', tlift 1 (ntype G1) A)
      end.
Proof.
  induction G1 as [|b G1 IH]; intros g K n; simpl.
  - unfold sh; simpl. destruct (lookup_def g n) as [[K' A]|]; reflexivity.
  - destruct b as [D | K' | K' D]; simpl.
    + apply IH.
    + unfold sh; simpl. destruct n as [|n']; simpl.
      * reflexivity.
      * specialize (IH g K n'). unfold sh in IH.
        destruct (le_gt_dec (ntype G1) n') eqn:E; simpl; rewrite IH;
          destruct (lookup_def (G1 ++ g) n') as [[K'' A]|]; simpl; try reflexivity;
          f_equal; f_equal; rewrite (permute_tlift_rec A 1 (ntype G1) 1 0) by lia; replace (1 + ntype G1) with (S (ntype G1)) by lia; reflexivity.
    + unfold sh; simpl. destruct n as [|n']; simpl.
      * f_equal; f_equal.
        rewrite (permute_tlift_rec D 1 (ntype G1) 1 0) by lia.
        replace (1 + ntype G1) with (S (ntype G1)) by lia. reflexivity.
      * specialize (IH g K n'). unfold sh in IH.
        destruct (le_gt_dec (ntype G1) n') eqn:E; simpl; rewrite IH;
          destruct (lookup_def (G1 ++ g) n') as [[K'' A]|]; simpl; try reflexivity;
          f_equal; f_equal; rewrite (permute_tlift_rec A 1 (ntype G1) 1 0) by lia; replace (1 + ntype G1) with (S (ntype G1)) by lia; reflexivity.
Qed.

Corollary lookup_def_weaken_kind0 : forall g K n,
  lookup_def (has_kind K :: g) (S n)
    = match lookup_def g n with
      | None => None
      | Some (K', A) => Some (K', tlift 1 0 A)
      end.
Proof.
  intros g K n. pose proof (lookup_def_weaken_kind nil g K n) as H.
  simpl in H. unfold sh in H. simpl in H. exact H.
Qed.

(** ** Context-aware parallel reduction [q_par] and its confluence

    [defeq] mixes [ty_step]-based conversion ([deq_ty_equiv]) with revealing a
    [nu]-sealed abstract type variable ([deq_def]), closed under symmetry and
    transitivity.  To show that a rigid head shape (e.g. [arrow]) can never be
    [defeq] to a different rigid head shape (e.g. [all]), we mirror the
    [ty_par]/[tydev] Church-Rosser development of [ty_confluence.v], but
    parameterized by a context [g]: [q_par g] is [ty_par] extended with one
    extra "reveal" constructor that unfolds a literal [tvar n] to its
    [lookup_def g n] payload, mirroring exactly how [defeq]'s own [deq_all]/
    [deq_tyabs]/[deq_tyapp] (and hence [q_par]'s [qpar_all]/[qpar_tyabs]/
    [qpar_beta]) extend [g] with [has_kind] when recursing under a binder.
    This is a diamond-property confluence argument, not a normalization
    argument: it works regardless of whether [q_par] terminates. *)
Inductive q_par (g : context) : typ -> typ -> Prop :=
  | qpar_tvar : forall n, q_par g (tvar n) (tvar n)
  | qpar_reveal : forall n K A, lookup_def g n = Some (K, A) -> q_par g (tvar n) A
  | qpar_dyn : q_par g dyn dyn
  | qpar_arrow : forall A A' B B',
      q_par g A A' -> q_par g B B' -> q_par g (arrow A B) (arrow A' B')
  | qpar_all : forall K A A',
      q_par (has_kind K :: g) A A' -> q_par g (all K A) (all K A')
  | qpar_tyabs : forall K A A',
      q_par (has_kind K :: g) A A' -> q_par g (tyabs K A) (tyabs K A')
  | qpar_tyapp : forall A A' B B',
      q_par g A A' -> q_par g B B' -> q_par g (tyapp A B) (tyapp A' B')
  | qpar_beta : forall K A A' B B',
      q_par (has_kind K :: g) A A' -> q_par g B B' ->
      q_par g (tyapp (tyabs K A) B) (tsubst B' 0 A').

Hint Constructors q_par : blame.

Lemma q_par_refl : forall g t, q_par g t t.
Proof.
  intros g t. revert g. induction t; intros g; simpl.
  - apply qpar_tvar.
  - apply qpar_arrow; auto.
  - apply qpar_all; auto.
  - apply qpar_tyabs; auto.
  - apply qpar_tyapp; auto.
  - apply qpar_dyn.
Qed.

Hint Resolve q_par_refl : blame.

(** Every [ty_par] step is (trivially) a [q_par] step: [q_par] just adds the
    [qpar_reveal] constructor on top of [ty_par]'s congruence/beta shape. *)
Lemma ty_par_q_par : forall A B, ty_par A B -> forall g, q_par g A B.
Proof. induction 1; intros g; eauto with blame. Qed.

(** *** Weakening [q_par] by inserting a single [has_kind] binding *)

Lemma q_par_weaken_kind : forall G1 g K B1 B2,
  q_par (G1 ++ g) B1 B2 ->
  q_par (tlift_ctx G1 ++ has_kind K :: g) (tlift 1 (ntype G1) B1) (tlift 1 (ntype G1) B2).
Proof.
  intros G1 g K B1 B2 H. remember (G1 ++ g) as g0 eqn:Hg. revert G1 Hg.
  induction H; intros G1 Hg; subst.
  - rewrite tlift1_tvar. apply qpar_tvar.
  - rewrite tlift1_tvar. unfold sh.
    eapply qpar_reveal.
    pose proof (lookup_def_weaken_kind G1 g K n) as HL.
    unfold sh in HL. rewrite H in HL. exact HL.
  - simpl. apply qpar_dyn.
  - simpl. apply qpar_arrow; auto.
  - simpl. apply qpar_all. apply (IHq_par (has_kind K0 :: G1)). reflexivity.
  - simpl. apply qpar_tyabs. apply (IHq_par (has_kind K0 :: G1)). reflexivity.
  - simpl. apply qpar_tyapp; auto.
  - simpl.
    replace (tlift 1 (ntype G1) (tsubst B' 0 A'))
      with (tsubst (tlift 1 (ntype G1) B') 0 (tlift 1 (S (ntype G1)) A'))
      by (symmetry; apply distribute_tlift_tsubst).
    eapply qpar_beta.
    + apply (IHq_par1 (has_kind K0 :: G1)). reflexivity.
    + apply (IHq_par2 G1). reflexivity.
Qed.

(** Weakening [q_par] by inserting a whole prefix of fresh [has_kind]
    bindings in front, all at once (peeling [q_par_weaken_kind] one binder
    at a time; only ever applied to [has_kind]-only prefixes in this
    development, so no [tlift_ctx] bookkeeping is needed on the prefix
    itself). *)
Fixpoint kctx (ks : list kind) : context :=
  match ks with
  | nil => nil
  | K :: ks' => has_kind K :: kctx ks'
  end.

Lemma ntype_kctx : forall ks, ntype (kctx ks) = length ks.
Proof. induction ks; simpl; auto. Qed.

Lemma tlift_ctx_kctx : forall ks, tlift_ctx (kctx ks) = kctx ks.
Proof. induction ks; simpl; [reflexivity | f_equal; auto]. Qed.

Lemma q_par_weaken_front : forall ks g B1 B2,
  q_par g B1 B2 -> q_par (kctx ks ++ g) (tlift (length ks) 0 B1) (tlift (length ks) 0 B2).
Proof.
  induction ks as [|K ks IH]; intros g B1 B2 H; simpl.
  - rewrite tlift_zero, tlift_zero. exact H.
  - pose proof (q_par_weaken_kind nil (kctx ks ++ g) K _ _ (IH g B1 B2 H)) as H2.
    simpl in H2.
    rewrite (tlift_tlift B1 1 (length ks) 0) in H2.
    rewrite (tlift_tlift B2 1 (length ks) 0) in H2.
    replace (1 + length ks) with (S (length ks)) in H2 by lia.
    exact H2.
Qed.

(** A [has_kind] binding at the very end of a [kctx] prefix contributes
    nothing to [lookup_def]: it is a [has_kind], not a [has_def]. *)
Lemma lookup_def_kctx_none_at_len : forall ks K g,
  lookup_def (kctx ks ++ has_kind K :: g) (length ks) = None.
Proof.
  induction ks as [|K0 ks IH]; intros K g; simpl.
  - reflexivity.
  - pose proof (lookup_def_weaken_kind0 (kctx ks ++ has_kind K :: g) K0 (length ks)) as HL.
    rewrite (IH K g) in HL. exact HL.
Qed.

(** *** The substitution lemma [q_par] needs: eliminating a [has_kind]
    binding via a related pair [(B1, B2)].  Stated with an explicit
    [ks : list kind] prefix (rather than an arbitrary [context] prefix)
    since every use in this development only ever accumulates [has_kind]
    bindings by recursing under [all]/[tyabs]/[tyapp]'s left branch. *)
Lemma q_par_subst_gen : forall ks g K B1 B2,
  q_par g B1 B2 ->
  forall A1 A2, q_par (kctx ks ++ has_kind K :: g) A1 A2 ->
  q_par (kctx ks ++ g) (tsubst B1 (length ks) A1) (tsubst B2 (length ks) A2).
Proof.
  intros ks g K B1 B2 HB A1 A2 H.
  remember (kctx ks ++ has_kind K :: g) as g0 eqn:Hg. revert ks Hg.
  induction H as [ m | m K0 A0 Hlook | | A A' B B' HA IHA HB' IHB | K0 A A' HA IHA | K0 A A' HA IHA | A A' B B' HA IHA HB' IHB | K0 A A' B B' HA IHA HB' IHB ]; intros ks Hg; subst.
  - (* qpar_tvar *)
    destruct (lt_eq_lt_dec (length ks) m) as [[Hlt|Heq]|Hgt].
    + rewrite (tsubst_ref_gt B1 m (length ks)) by lia.
      rewrite (tsubst_ref_gt B2 m (length ks)) by lia.
      apply qpar_tvar.
    + subst m. rewrite !tsubst_ref_eq. apply q_par_weaken_front. exact HB.
    + rewrite (tsubst_ref_lt B1 m (length ks)) by lia.
      rewrite (tsubst_ref_lt B2 m (length ks)) by lia.
      apply qpar_tvar.
  - (* qpar_reveal m K0 A0 Hlook : lookup_def (kctx ks ++ has_kind K :: g) m = Some (K0, A0) *)
    destruct (lt_eq_lt_dec (length ks) m) as [[Hlt|Heq]|Hgt].
    + (* m > length ks: m = S m', peel the [has_kind K] binder off via
         [lookup_def_weaken_kind] at [G1 := kctx ks], [n := m'] (using
         [sh (length ks) m' = S m'] since [m' >= length ks]). *)
      destruct m as [|m']; [lia|]. assert (Hm' : length ks <= m') by lia.
      rewrite (tsubst_ref_gt B1 (S m') (length ks)) by lia.
      pose proof (lookup_def_weaken_kind (kctx ks) g K m') as HL.
      rewrite tlift_ctx_kctx, ntype_kctx in HL. unfold sh in HL.
      destruct (le_gt_dec (length ks) m'); [| lia].
      rewrite Hlook in HL.
      destruct (lookup_def (kctx ks ++ g) m') as [[K0' A0']|] eqn:E; [| discriminate].
      injection HL as HK HA. subst K0'.
      rewrite (tsubst_ref_gt B2 (S m') (length ks)) by lia.
      rewrite HA. rewrite (simplify_tsubst_rec A0' B2 0 (length ks) (length ks)) by lia.
      apply qpar_reveal. exact E.
    + (* m = length ks: this is exactly the [has_kind K] binder itself, which
         has no [lookup_def] entry — contradicts [Hlook]. *)
      subst m. rewrite (lookup_def_kctx_none_at_len ks K g) in Hlook. discriminate.
    + (* m < length ks: [tsubst] at [length ks] doesn't touch [tvar m], and
         [lookup_def_weaken_kind] (with [sh (length ks) m = m]) relates the
         lookup directly, modulo the same [tlift]/[tsubst] cancellation. *)
      rewrite (tsubst_ref_lt B1 m (length ks)) by lia.
      pose proof (lookup_def_weaken_kind (kctx ks) g K m) as HL.
      rewrite tlift_ctx_kctx, ntype_kctx in HL. unfold sh in HL.
      destruct (le_gt_dec (length ks) m); [lia |].
      rewrite Hlook in HL.
      destruct (lookup_def (kctx ks ++ g) m) as [[K0' A0']|] eqn:E; [| discriminate].
      injection HL as HK HA. subst K0'.
      rewrite HA. rewrite (simplify_tsubst_rec A0' B2 0 (length ks) (length ks)) by lia.
      apply qpar_reveal. exact E.
  - simpl. apply qpar_dyn.
  - simpl. apply qpar_arrow; auto.
  - simpl. apply qpar_all. apply (IHA (K0 :: ks)). reflexivity.
  - simpl. apply qpar_tyabs. apply (IHA (K0 :: ks)). reflexivity.
  - simpl. apply qpar_tyapp; auto.
  - simpl.
    replace (tsubst B0' (length ks) (tsubst B' 0 A'))
      with (tsubst (tsubst B0' (length ks) B') 0 (tsubst B0' (S (length ks)) A'))
      by (symmetry; apply distribute_tsubst).
    eapply qpar_beta.
    + apply (IHA (K0 :: ks)). reflexivity.
    + apply (IHB' ks). reflexivity.
Qed.

(** The [ks = nil] corollary actually needed downstream: eliminating the
    outermost [has_kind K] binding of [g] via a related pair [(B1, B2)]. *)
Corollary q_par_subst : forall g K B1 B2,
  q_par g B1 B2 ->
  forall A1 A2, q_par (has_kind K :: g) A1 A2 ->
  q_par g (tsubst B1 0 A1) (tsubst B2 0 A2).
Proof. intros g K B1 B2 HB A1 A2 H. exact (q_par_subst_gen nil g K B1 B2 HB A1 A2 H). Qed.

Lemma defeq_weaken_kind : forall G1 g K A B K0,
  defeq (G1 ++ g) A B K0 ->
  defeq (tlift_ctx G1 ++ has_kind K :: g) (tlift 1 (ntype G1) A) (tlift 1 (ntype G1) B) K0.
Proof.
  intros G1 g K A B K0 H. remember (G1 ++ g) as g0 eqn:Hg. revert G1 Hg.
  induction H; intros G1 Hg; subst.
  - apply deq_refl. apply wf_typ_weaken_kind; auto.
  - apply deq_sym. apply IHdefeq. reflexivity.
  - eapply deq_trans; [apply IHdefeq1 | apply IHdefeq2]; reflexivity.
  - apply deq_ty_equiv; auto using ty_equiv_tlift, wf_typ_weaken_kind.
  - rewrite tlift1_tvar. eapply deq_def.
    + rewrite lookup_def_weaken_kind. rewrite H. reflexivity.
    + rewrite <- tlift1_tvar. apply wf_typ_weaken_kind; auto.
  - simpl. apply deq_arrow; [apply IHdefeq1 | apply IHdefeq2]; reflexivity.
  - simpl. apply deq_all. apply (IHdefeq (has_kind K0 :: G1)). reflexivity.
  - simpl. apply deq_tyabs. apply (IHdefeq (has_kind K1 :: G1)). reflexivity.
  - simpl. eapply deq_tyapp; [apply IHdefeq1 | apply IHdefeq2]; reflexivity.
Qed.

Corollary defeq_weaken_kind0 : forall g K A B K0,
  defeq g A B K0 -> defeq (has_kind K :: g) (tlift 1 0 A) (tlift 1 0 B) K0.
Proof. intros g K A B K0 H. exact (defeq_weaken_kind nil g K A B K0 H). Qed.

Lemma typing_weaken_kind : forall G1 g e A K,
  typing (G1 ++ g) e A ->
  typing (tlift_ctx G1 ++ has_kind K :: g) (term_tlift 1 (ntype G1) e) (tlift 1 (ntype G1) A).
Proof.
  intros G1 g e A K H. remember (G1 ++ g) as g0 eqn:Hg. revert G1 Hg.
  induction H; intros G1 Hg; subst.
  - (* var *) simpl. apply typing_var. rewrite lookup_term_weaken_kind. rewrite H. reflexivity.
  - (* abs *) simpl. apply typing_abs. apply (IHtyping (has_type t1 :: G1)). reflexivity.
  - (* app *) simpl. eapply typing_app; [ apply (IHtyping1 G1) | apply (IHtyping2 G1) ]; reflexivity.
  - (* tabs *) simpl. apply typing_tabs. apply (IHtyping (has_kind K0 :: G1)). reflexivity.
  - (* tapp *) simpl.
    replace (tlift 1 (ntype G1) (tsubst s 0 t))
      with (tsubst (tlift 1 (ntype G1) s) 0 (tlift 1 (S (ntype G1)) t))
      by (symmetry; apply distribute_tlift_tsubst).
    eapply typing_tapp. apply (IHtyping G1). reflexivity.
  - (* cast *) simpl. eapply typing_cast; [ apply (IHtyping G1); reflexivity | apply compat_tlift; auto ].
  - (* gnd *) simpl. apply typing_gnd; [ apply (IHtyping G1); reflexivity | apply ground_tlift; auto ].
  - (* is_gnd *) simpl. apply (typing_is_gnd _ _ (tlift 1 (ntype G1) G)). apply (IHtyping G1). reflexivity.
  - (* blame *) simpl. apply typing_blame.
  - (* nu *) simpl.
    replace (tlift 1 (ntype G1) (tsubst A 0 B))
      with (tsubst (tlift 1 (ntype G1) A) 0 (tlift 1 (S (ntype G1)) B))
      by (symmetry; apply distribute_tlift_tsubst).
    apply typing_nu.
    + apply (IHtyping (has_def K0 A :: G1)). reflexivity.
    + apply wf_typ_weaken_kind; auto.
  - (* conv *) simpl. eapply typing_conv;
      [ apply (IHtyping G1); reflexivity
      | apply ty_equiv_tlift; auto
      | apply wf_typ_weaken_kind; auto ].
Qed.

(** Front type weakening (the common case). *)
Corollary typing_weaken_kind0 : forall g e A K,
  typing g e A -> typing (has_kind K :: g) (term_tlift 1 0 e) (tlift 1 0 A).
Proof. intros g e A K H. exact (typing_weaken_kind nil g e A K H). Qed.

(** ** Type weakening: inserting a [has_def] binding
    [has_def K C] occupies the same namespace as [has_kind K], so the lookup
    lemmas and weakening proofs are structurally identical. *)

Lemma lookup_kind_weaken_def : forall G1 g K C n,
  lookup_kind (tlift_ctx G1 ++ has_def K C :: g) (sh (ntype G1) n)
    = lookup_kind (G1 ++ g) n.
Proof.
  induction G1 as [|b G1 IH]; intros g K C n; simpl.
  - unfold sh; simpl. destruct (le_gt_dec 0 n); [reflexivity | lia].
  - destruct b as [D | K' | K' D]; simpl.
    + apply IH.
    + unfold sh; simpl. destruct n as [|n']; simpl.
      * reflexivity.
      * specialize (IH g K C n'). unfold sh in IH.
        destruct (le_gt_dec (ntype G1) n') eqn:E; simpl; exact IH.
    + unfold sh; simpl. destruct n as [|n']; simpl.
      * reflexivity.
      * specialize (IH g K C n'). unfold sh in IH.
        destruct (le_gt_dec (ntype G1) n') eqn:E; simpl; exact IH.
Qed.

Lemma lookup_term_weaken_def : forall G1 g K C n,
  lookup_term (tlift_ctx G1 ++ has_def K C :: g) n
    = option_map (tlift 1 (ntype G1)) (lookup_term (G1 ++ g) n).
Proof.
  induction G1 as [|b G1 IH]; intros g K C n; simpl.
  - reflexivity.
  - destruct b as [D | K' | K' D]; simpl.
    + destruct n as [|n']; simpl; [reflexivity | apply IH].
    + rewrite IH. destruct (lookup_term (G1 ++ g) n) as [x|]; simpl; [| reflexivity].
      f_equal. rewrite (permute_tlift_rec x 1 (ntype G1) 1 0) by lia. reflexivity.
    + rewrite IH. destruct (lookup_term (G1 ++ g) n) as [x|]; simpl; [| reflexivity].
      f_equal. rewrite (permute_tlift_rec x 1 (ntype G1) 1 0) by lia. reflexivity.
Qed.

Lemma wf_typ_weaken_def : forall G1 g K C A K0,
  wf_typ (G1 ++ g) A K0 ->
  wf_typ (tlift_ctx G1 ++ has_def K C :: g) (tlift 1 (ntype G1) A) K0.
Proof.
  intros G1 g K C A K0 H. remember (G1 ++ g) as g0 eqn:Hg. revert G1 Hg.
  induction H; intros G1 Hg; subst.
  - rewrite tlift1_tvar. apply wf_tvar. rewrite lookup_kind_weaken_def. auto.
  - simpl. apply wf_arrow; auto.
  - simpl. apply wf_all. apply (IHwf_typ (has_kind K0 :: G1)). reflexivity.
  - simpl. apply wf_tyabs. apply (IHwf_typ (has_kind K1 :: G1)). reflexivity.
  - simpl. eapply wf_tyapp; eauto.
  - simpl. apply wf_dyn.
Qed.

(** ** [lookup_def] weakening (mirrors the [lookup_kind]/[lookup_term] lemmas above) *)

Lemma lookup_def_weaken_def : forall G1 g K C n,
  lookup_def (tlift_ctx G1 ++ has_def K C :: g) (sh (ntype G1) n)
    = match lookup_def (G1 ++ g) n with
      | None => None
      | Some (K', A) => Some (K', tlift 1 (ntype G1) A)
      end.
Proof.
  induction G1 as [|b G1 IH]; intros g K C n; simpl.
  - unfold sh; simpl. destruct (lookup_def g n) as [[K' A]|]; reflexivity.
  - destruct b as [D | K' | K' D]; simpl.
    + apply IH.
    + unfold sh; simpl. destruct n as [|n']; simpl.
      * reflexivity.
      * specialize (IH g K C n'). unfold sh in IH.
        destruct (le_gt_dec (ntype G1) n') eqn:E; simpl; rewrite IH;
          destruct (lookup_def (G1 ++ g) n') as [[K'' A]|]; simpl; try reflexivity;
          f_equal; f_equal; rewrite (permute_tlift_rec A 1 (ntype G1) 1 0) by lia; replace (1 + ntype G1) with (S (ntype G1)) by lia; reflexivity.
    + unfold sh; simpl. destruct n as [|n']; simpl.
      * f_equal; f_equal.
        rewrite (permute_tlift_rec D 1 (ntype G1) 1 0) by lia.
        replace (1 + ntype G1) with (S (ntype G1)) by lia. reflexivity.
      * specialize (IH g K C n'). unfold sh in IH.
        destruct (le_gt_dec (ntype G1) n') eqn:E; simpl; rewrite IH;
          destruct (lookup_def (G1 ++ g) n') as [[K'' A]|]; simpl; try reflexivity;
          f_equal; f_equal; rewrite (permute_tlift_rec A 1 (ntype G1) 1 0) by lia; replace (1 + ntype G1) with (S (ntype G1)) by lia; reflexivity.
Qed.

(** Front-insertion corollaries (the common case, [G1 = nil]). *)
Corollary lookup_def_weaken_def0 : forall g K C n,
  lookup_def (has_def K C :: g) (S n)
    = match lookup_def g n with
      | None => None
      | Some (K', A) => Some (K', tlift 1 0 A)
      end.
Proof.
  intros g K C n. pose proof (lookup_def_weaken_def nil g K C n) as H.
  simpl in H. unfold sh in H. simpl in H. exact H.
Qed.

(** [wf_typ] on the tag [lookup_def] returns is exactly [wf_ctx]-regularity of
    the [has_def] binding it reads off: the payload of a [has_def K A] entry
    is always well-kinded at [K] in the ambient context (weakened through
    whatever's above it), so [lookup_def] itself never needs a separate
    well-formedness side condition threaded in — it's available whenever the
    context itself was built by [wf_typ]-checked [nu]s. *)

(** ** [defeq] weakening *)

Lemma defeq_weaken_def : forall G1 g K C A B K0,
  defeq (G1 ++ g) A B K0 ->
  defeq (tlift_ctx G1 ++ has_def K C :: g) (tlift 1 (ntype G1) A) (tlift 1 (ntype G1) B) K0.
Proof.
  intros G1 g K C A B K0 H. remember (G1 ++ g) as g0 eqn:Hg. revert G1 Hg.
  induction H; intros G1 Hg; subst.
  - apply deq_refl. apply wf_typ_weaken_def; auto.
  - apply deq_sym. apply IHdefeq. reflexivity.
  - eapply deq_trans; [apply IHdefeq1 | apply IHdefeq2]; reflexivity.
  - apply deq_ty_equiv; auto using ty_equiv_tlift, wf_typ_weaken_def.
  - rewrite tlift1_tvar. eapply deq_def.
    + rewrite lookup_def_weaken_def. rewrite H. reflexivity.
    + rewrite <- tlift1_tvar. apply wf_typ_weaken_def; auto.
  - simpl. apply deq_arrow; [apply IHdefeq1 | apply IHdefeq2]; reflexivity.
  - simpl. apply deq_all. apply (IHdefeq (has_kind K0 :: G1)). reflexivity.
  - simpl. apply deq_tyabs. apply (IHdefeq (has_kind K1 :: G1)). reflexivity.
  - simpl. eapply deq_tyapp; [apply IHdefeq1 | apply IHdefeq2]; reflexivity.
Qed.

Corollary defeq_weaken_def0 : forall g K C A B K0,
  defeq g A B K0 -> defeq (has_def K C :: g) (tlift 1 0 A) (tlift 1 0 B) K0.
Proof. intros g K C A B K0 H. exact (defeq_weaken_def nil g K C A B K0 H). Qed.

(** ** Well-formed contexts

    Moved here (from [preservation.v]) so [lookup_def_wf]/[defeq_regular]/the
    kind-regular [typing] rewrite can all use it; [preservation.v] now just
    imports it. *)

Inductive wf_ctx : context -> Prop :=
  | wf_ctx_nil : wf_ctx nil
  | wf_ctx_type : forall g T,
      wf_ctx g -> wf_typ g T KStar -> wf_ctx (has_type T :: g)
  | wf_ctx_kind : forall g K,
      wf_ctx g -> wf_ctx (has_kind K :: g)
  | wf_ctx_def : forall g K A,
      wf_ctx g -> wf_typ g A K -> wf_ctx (has_def K A :: g).

Hint Constructors wf_ctx : blame.

Lemma wf_ctx_lookup_term : forall g n t,
  wf_ctx g -> lookup_term g n = Some t -> wf_typ g t KStar.
Proof.
  induction g as [| b g IH]; intros n t Hwf Hlk; simpl in Hlk.
  - discriminate.
  - destruct b as [T | K | K A]; inversion Hwf; subst.
    + destruct n as [| n'].
      * injection Hlk as <-. apply (wf_typ_weaken_type nil g T T KStar); assumption.
      * apply (wf_typ_weaken_type nil g T t KStar). eapply IH; eauto.
    + destruct (lookup_term g n) as [t0 |] eqn:Elk; simpl in Hlk; try discriminate.
      injection Hlk as <-.
      apply (wf_typ_weaken_kind nil g K t0 KStar). eapply IH; eauto.
    + destruct (lookup_term g n) as [t0 |] eqn:Elk; simpl in Hlk; try discriminate.
      injection Hlk as <-.
      apply (wf_typ_weaken_def nil g K A t0 KStar). eapply IH; eauto.
Qed.

(** The payload of a [has_def K A] binding read off by [lookup_def] is always
    well-kinded at [K] (weakened through whatever's above it) — the
    [wf_ctx]-regularity counterpart of [wf_ctx_lookup_term]. *)
Lemma lookup_def_wf : forall g n K A,
  wf_ctx g -> lookup_def g n = Some (K, A) -> wf_typ g A K.
Proof.
  induction g as [| b g IH]; intros n K A Hwf Hlk; simpl in Hlk.
  - discriminate.
  - destruct b as [T | K' | K' D]; inversion Hwf; subst.
    + apply (wf_typ_weaken_type nil g T A K). eapply IH; eauto.
    + destruct n as [| n'].
      * discriminate.
      * destruct (lookup_def g n') as [[K0 A0] |] eqn:Elk; simpl in Hlk; try discriminate.
        injection Hlk as HK HA. subst K A. apply (wf_typ_weaken_kind nil g K' A0 K0). eapply IH; eauto.
    + destruct n as [| n'].
      * injection Hlk as HK HA. subst K A. apply (wf_typ_weaken_def nil g K' D D K'); assumption.
      * destruct (lookup_def g n') as [[K0 A0] |] eqn:Elk; simpl in Hlk; try discriminate.
        injection Hlk as HK HA. subst K A. apply (wf_typ_weaken_def nil g K' D A0 K0). eapply IH; eauto.
Qed.

(** Regularity: both sides of a [defeq] are well-kinded. This is free by
    induction since every constructor either carries [wf_typ] witnesses
    directly or is built from [defeq] premises that already have them. *)
(** [defeq]'s [deq_def] case reveals a [has_def] binding's payload, which is
    only known well-kinded via [lookup_def_wf] — that in turn needs [wf_ctx];
    so, unlike [wf_typ], [defeq]'s regularity needs [wf_ctx g] as a hypothesis
    (matching the plan's noted alternative signature). *)
Lemma defeq_regular : forall g A B K, wf_ctx g -> defeq g A B K -> wf_typ g A K /\ wf_typ g B K.
Proof.
  intros g A B K Hwf H. revert Hwf. induction H; intros Hwf.
  - split; assumption.
  - destruct (IHdefeq Hwf) as [HA HB]; split; assumption.
  - destruct (IHdefeq1 Hwf) as [HA HB]. destruct (IHdefeq2 Hwf) as [HB' HC].
    split; assumption.
  - split; assumption.
  - split.
    + assumption.
    + eapply lookup_def_wf; eauto.
  - destruct (IHdefeq1 Hwf) as [HA HA']. destruct (IHdefeq2 Hwf) as [HB HB'].
    split; constructor; assumption.
  - assert (Hwf' : wf_ctx (has_kind K :: g)) by (constructor; assumption).
    destruct (IHdefeq Hwf') as [HA HA'].
    split; constructor; assumption.
  - assert (Hwf' : wf_ctx (has_kind K1 :: g)) by (constructor; assumption).
    destruct (IHdefeq Hwf') as [HA HA'].
    split; constructor; assumption.
  - destruct (IHdefeq1 Hwf) as [HF HF']. destruct (IHdefeq2 Hwf) as [HA HA'].
    split; econstructor; eauto.
Qed.

Lemma defeq_regular_l : forall g A B K, wf_ctx g -> defeq g A B K -> wf_typ g A K.
Proof. intros g A B K Hwf H; apply (defeq_regular g A B K Hwf H). Qed.

Lemma defeq_regular_r : forall g A B K, wf_ctx g -> defeq g A B K -> wf_typ g B K.
Proof. intros g A B K Hwf H; apply (defeq_regular g A B K Hwf H). Qed.

(** [lookup_def] at a [has_def K A] binding's own index (after some prefix
    [G1]) returns [K] paired with [A] lifted through everything above it
    (the [G1]-generalized form of the [n = 0] clause of [lookup_def]'s own
    definition), by induction on [G1]. *)
Lemma lookup_kind_def_self : forall G1 g K A,
  lookup_kind (G1 ++ has_def K A :: g) (ntype G1) = Some K.
Proof.
  induction G1 as [|b G1 IH]; intros g K A; simpl.
  - reflexivity.
  - destruct b as [D | K' | K' D]; simpl; auto.
Qed.

Lemma lookup_def_self : forall G1 g K A,
  lookup_def (G1 ++ has_def K A :: g) (ntype G1) = Some (K, tlift (S (ntype G1)) 0 A).
Proof.
  induction G1 as [|b G1 IH]; intros g K A; simpl.
  - reflexivity.
  - destruct b as [D | K' | K' D]; simpl.
    + apply IH.
    + rewrite IH.
      f_equal; f_equal.
      rewrite (simplify_tlift_rec A (S (ntype G1)) 0 1 0) by lia.
      reflexivity.
    + rewrite IH.
      f_equal; f_equal.
      rewrite (simplify_tlift_rec A (S (ntype G1)) 0 1 0) by lia.
      reflexivity.
Qed.

(** The "reveal" lemma: at any depth [ntype G1] above a [has_def K A]
    binding, a well-kinded type [T] is [defeq] to the result of transparently
    unfolding all its occurrences of the sealed variable [tvar (ntype G1)] by
    its concealed implementation [A] — computed as [tsubst]-then-[tlift] so
    the context (and hence the [has_def] binder itself) is left unchanged,
    only the *type* is rewritten.  [G1 = nil] is the [defeq_reveal_subst]
    corollary actually needed by [preservation]'s [step_nu_tabs] case. *)
Lemma defeq_reveal_subst_gen : forall G1 g K A T J,
  wf_typ (G1 ++ has_def K A :: g) T J ->
  defeq (G1 ++ has_def K A :: g) T (tlift 1 (ntype G1) (tsubst A (ntype G1) T)) J.
Proof.
  intros G1 g K A T J H. remember (G1 ++ has_def K A :: g) as g0 eqn:Hg. revert G1 Hg.
  induction H; intros G1 Hg; subst.
  - (* tvar *) rename n into m. destruct (lt_eq_lt_dec (ntype G1) m) as [[Hlt|Heq]|Hgt].
    + (* m > ntype G1: substitution/lift cancel *)
      rewrite (tsubst_ref_gt A m (ntype G1)) by lia.
      rewrite (tlift_ref_ge 1 (pred m) (ntype G1)) by lia.
      replace (1 + pred m) with m by lia.
      apply deq_refl. apply wf_tvar. assumption.
    + (* m = ntype G1: reveal via [deq_def] *)
      subst m. rewrite (lookup_kind_def_self G1 g K A) in H. injection H as ->.
      rewrite (tsubst_ref_eq A (ntype G1)).
      rewrite (simplify_tlift_rec A (ntype G1) 0 1 (ntype G1)) by lia.
      replace (1 + ntype G1) with (S (ntype G1)) by lia.
      eapply deq_def.
      * apply lookup_def_self.
      * apply wf_tvar. apply lookup_kind_def_self.
    + (* m < ntype G1: substitution/lift are no-ops *)
      rewrite (tsubst_ref_lt A m (ntype G1)) by lia.
      rewrite (tlift_ref_lt 1 m (ntype G1)) by lia.
      apply deq_refl. apply wf_tvar. assumption.
  - (* arrow *) simpl. apply deq_arrow; [apply IHwf_typ1 | apply IHwf_typ2]; reflexivity.
  - (* all *) simpl. apply deq_all. apply (IHwf_typ (has_kind K0 :: G1)). reflexivity.
  - (* tyabs *) simpl. apply deq_tyabs. apply (IHwf_typ (has_kind K1 :: G1)). reflexivity.
  - (* tyapp *) simpl. eapply deq_tyapp; [apply IHwf_typ1 | apply IHwf_typ2]; reflexivity.
  - (* dyn *) simpl. apply deq_refl. apply wf_dyn.
Qed.

Corollary defeq_reveal_subst : forall g K A T J,
  wf_ctx g -> wf_typ g A K -> wf_typ (has_def K A :: g) T J ->
  defeq (has_def K A :: g) T (tlift 1 0 (tsubst A 0 T)) J.
Proof.
  intros g K A T J _ _ H. exact (defeq_reveal_subst_gen nil g K A T J H).
Qed.

Lemma typing_weaken_def : forall G1 g e A K C,
  typing (G1 ++ g) e A ->
  typing (tlift_ctx G1 ++ has_def K C :: g) (term_tlift 1 (ntype G1) e) (tlift 1 (ntype G1) A).
Proof.
  intros G1 g e A K C H. remember (G1 ++ g) as g0 eqn:Hg. revert G1 Hg.
  induction H; intros G1 Hg; subst.
  - simpl. apply typing_var. rewrite lookup_term_weaken_def. rewrite H. reflexivity.
  - simpl. apply typing_abs. apply (IHtyping (has_type t1 :: G1)). reflexivity.
  - simpl. eapply typing_app; [ apply (IHtyping1 G1) | apply (IHtyping2 G1) ]; reflexivity.
  - simpl. apply typing_tabs. apply (IHtyping (has_kind K0 :: G1)). reflexivity.
  - simpl.
    replace (tlift 1 (ntype G1) (tsubst s 0 t))
      with (tsubst (tlift 1 (ntype G1) s) 0 (tlift 1 (S (ntype G1)) t))
      by (symmetry; apply distribute_tlift_tsubst).
    eapply typing_tapp. apply (IHtyping G1). reflexivity.
  - simpl. eapply typing_cast; [ apply (IHtyping G1); reflexivity | apply compat_tlift; auto ].
  - simpl. apply typing_gnd; [ apply (IHtyping G1); reflexivity | apply ground_tlift; auto ].
  - simpl. apply (typing_is_gnd _ _ (tlift 1 (ntype G1) G)). apply (IHtyping G1). reflexivity.
  - simpl. apply typing_blame.
  - simpl.
    replace (tlift 1 (ntype G1) (tsubst A 0 B))
      with (tsubst (tlift 1 (ntype G1) A) 0 (tlift 1 (S (ntype G1)) B))
      by (symmetry; apply distribute_tlift_tsubst).
    apply typing_nu.
    + apply (IHtyping (has_def K0 A :: G1)). reflexivity.
    + apply wf_typ_weaken_def; auto.
  - simpl. eapply typing_conv;
      [ apply (IHtyping G1); reflexivity
      | apply ty_equiv_tlift; auto
      | apply wf_typ_weaken_def; auto ].
Qed.

(** Front type weakening by a [has_def] binding (the common case). *)
Corollary typing_weaken_def0 : forall g e A K C,
  typing g e A -> typing (has_def K C :: g) (term_tlift 1 0 e) (tlift 1 0 A).
Proof. intros g e A K C H. exact (typing_weaken_def nil g e A K C H). Qed.

Lemma wf_typ_strengthen_type : forall G1 g C A K,
  wf_typ (G1 ++ has_type C :: g) A K -> wf_typ (G1 ++ g) A K.
Proof.
  intros G1 g C A K H. remember (G1 ++ has_type C :: g) as g0 eqn:Hg. revert G1 Hg.
  induction H; intros G1 Hg; subst.
  - apply wf_tvar. rewrite lookup_kind_weaken_type in H. auto.
  - apply wf_arrow; auto.
  - apply wf_all. apply (IHwf_typ (has_kind K :: G1)). reflexivity.
  - apply wf_tyabs. apply (IHwf_typ (has_kind K1 :: G1)). reflexivity.
  - eapply wf_tyapp; eauto.
  - apply wf_dyn.
Qed.


(** ** Term-level lift/term_tlift commutation and composition

    Needed to prove the substitution lemma, whose substituted term is
    [term_tlift (ntype Gtm) 0 u]: crossing a type binder in the term applies one
    more [term_tlift 1 0], and this must line up with the prefix count. *)

(** Shifting by 0 is the identity, for terms (the [tlift_zero] counterpart). *)
Lemma lift_zero_term : forall e k, lift 0 k e = e.
Proof.
  induction e; intros k; simpl; try (f_equal; auto; fail).
  - destruct (le_gt_dec k n); [f_equal; lia | reflexivity].
Qed.

(** Shifting type variables by 0 inside a term is the identity. *)
Lemma term_tlift_zero : forall e k, term_tlift 0 k e = e.
Proof.
  induction e; intros k; simpl; try (f_equal; auto using tlift_zero; fail).
Qed.

(** Two consecutive term-variable shifts at the same cutoff compose additively (the [tlift_tlift] counterpart). *)
Lemma simplify_lift_term : forall e i j k, lift i k (lift j k e) = lift (i + j) k e.
Proof.
  induction e; intros i j k; simpl; try (f_equal; eauto; fail).
  - destruct (le_gt_dec k n); simpl.
    + destruct (le_gt_dec k (j + n)); [f_equal; lia | lia].
    + destruct (le_gt_dec k n); [lia | reflexivity].
Qed.

(** Two consecutive type-variable shifts inside a term at the same cutoff compose additively. *)
Lemma term_tlift_comp : forall e i j k, term_tlift i k (term_tlift j k e) = term_tlift (i + j) k e.
Proof.
  induction e; intros i j k; simpl; f_equal;
    auto; try apply simplify_tlift_rec; lia.
Qed.

(** Term-variable shifting and type-variable shifting inside a term commute (they act on disjoint namespaces). *)
Lemma term_tlift_lift_comm : forall e i kt j ke,
  term_tlift i kt (lift j ke e) = lift j ke (term_tlift i kt e).
Proof.
  induction e; intros i kt j ke; simpl; try (f_equal; eauto; fail).
  - destruct (le_gt_dec ke n); reflexivity.
Qed.

(** ** Weakening by a whole context prefix

    A term well-typed in [g] is well-typed in [Gtm ++ g] after being shifted by
    the [nterm Gtm] term binders and [ntype Gtm] type binders of the prefix; its
    type is correspondingly [tlift]-shifted. Proved by iterating the single-binder
    weakenings. *)

Lemma typing_weaken_prefix : forall Gtm g u A,
  typing g u A ->
  typing (Gtm ++ g)
         (lift (nterm Gtm) 0 (term_tlift (ntype Gtm) 0 u))
         (tlift (ntype Gtm) 0 A).
Proof.
  induction Gtm as [|b Gtm IH]; intros g u A H; simpl.
  - rewrite term_tlift_zero, lift_zero_term, tlift_zero. exact H.
  - destruct b as [C | K | K C]; simpl.
    + (* has_type C : term binder *)
      specialize (IH g u A H).
      apply typing_weaken_term0 with (C := C) in IH.
      rewrite (simplify_lift_term (term_tlift (ntype Gtm) 0 u) 1 (nterm Gtm) 0) in IH.
      replace (1 + nterm Gtm) with (S (nterm Gtm)) in IH by lia. exact IH.
    + (* has_kind K : type binder *)
      specialize (IH g u A H).
      apply (typing_weaken_kind0 (Gtm ++ g)) with (K := K) in IH.
      rewrite term_tlift_lift_comm in IH. rewrite term_tlift_comp in IH.
      rewrite (simplify_tlift_rec A (ntype Gtm) 0 1 0) in IH by lia.
      replace (1 + ntype Gtm) with (S (ntype Gtm)) in IH by lia. exact IH.
    + (* has_def K C : type binder — same namespace as has_kind *)
      specialize (IH g u A H).
      apply (typing_weaken_def0 (Gtm ++ g)) with (K := K) (C := C) in IH.
      rewrite term_tlift_lift_comm in IH. rewrite term_tlift_comp in IH.
      rewrite (simplify_tlift_rec A (ntype Gtm) 0 1 0) in IH by lia.
      replace (1 + ntype Gtm) with (S (ntype Gtm)) in IH by lia. exact IH.
Qed.

(** ** Term substitution lemma *)

(** Substituting for the variable just introduced by [lift 1 k] cancels the
    lift; the term-level counterpart of [infrastructure.tsubst_tlift_cancel]
    (this file later shadows that name at [k = 0] with its own specialized
    [tsubst_tlift_cancel] below). *)
Lemma subst_lift_cancel : forall u e k, subst u k (lift 1 k e) = e.
Proof.
  intros u e; revert u; induction e; intros u k; simpl;
    try (f_equal; eauto; fail).
  - destruct (le_gt_dec k n); simpl.
    + destruct (lt_eq_lt_dec k (S n)) as [[?|?]|?]; [f_equal; lia | lia | lia].
    + destruct (lt_eq_lt_dec k n) as [[?|?]|?]; [lia | lia | reflexivity].
Qed.

(** [wf_typ] doesn't depend on term bindings, so removing one (the converse of [wf_typ_weaken_type]) preserves it. *)
(** Looking up the just-inserted [has_type A] binding itself returns [A],
    lifted for the type variables in [G1] that scope over it. *)
Lemma lookup_term_mid : forall G1 g A,
  lookup_term (G1 ++ has_type A :: g) (nterm G1) = Some (tlift (ntype G1) 0 A).
Proof.
  induction G1 as [|b G1 IH]; intros g A; simpl.
  - rewrite tlift_zero. reflexivity.
  - destruct b as [C | K | K C]; simpl.
    + apply IH.
    + rewrite IH. simpl. f_equal. rewrite (simplify_tlift_rec A (ntype G1) 0 1 0) by lia.
      replace (1 + ntype G1) with (S (ntype G1)) by lia. reflexivity.
    + rewrite IH. simpl. f_equal. rewrite (simplify_tlift_rec A (ntype G1) 0 1 0) by lia.
      replace (1 + ntype G1) with (S (ntype G1)) by lia. reflexivity.
Qed.

(** [lookup_term_weaken], restated with the shift on the lookup side: a
    binding above the insertion point (index [>= nterm G1] before insertion)
    is found at its shifted index afterward. *)
Lemma lookup_term_above : forall G1 g A n,
  lookup_term (G1 ++ g) n = lookup_term (G1 ++ has_type A :: g) (sh (nterm G1) n).
Proof.
  intros. rewrite lookup_term_weaken. reflexivity.
Qed.

(** A binding below the insertion point ([n < nterm G1]) is unaffected by inserting [has_type A] further in. *)
Lemma lookup_term_below : forall G1 g A n,
  n < nterm G1 ->
  lookup_term (G1 ++ has_type A :: g) n = lookup_term (G1 ++ g) n.
Proof.
  induction G1 as [|b G1 IH]; intros g A n Hn; simpl in *.
  - lia.
  - destruct b as [C | K | K' C]; simpl in *.
    + destruct n as [|n']; [reflexivity |]. apply IH. lia.
    + rewrite IH; [reflexivity | lia].
    + rewrite IH; [reflexivity | lia].
Qed.

Lemma typing_subst : forall G1 g e u T B,
  typing (G1 ++ has_type T :: g) e B ->
  typing g u T ->
  typing (G1 ++ g) (subst (term_tlift (ntype G1) 0 u) (nterm G1) e) B.
Proof.
  intros G1 g e u T B He Hu.
  remember (G1 ++ has_type T :: g) as g0 eqn:Hg. revert G1 Hg.
  induction He; intros G1 Hg; subst; simpl.
  - (* var *) destruct (lt_eq_lt_dec (nterm G1) n) as [[Hlt|Heq]|Hgt].
    + (* n > nterm G1: variable from g, shifted *)
      apply typing_var.
      replace n with (sh (nterm G1) (pred n)) in H
        by (unfold sh; destruct (le_gt_dec (nterm G1) (pred n)); lia).
      rewrite lookup_term_weaken in H. exact H.
    + (* n = nterm G1: the substituted variable *)
      subst. rewrite lookup_term_mid in H. injection H as <-.
      apply typing_weaken_prefix. exact Hu.
    + (* n < nterm G1: variable from G1, unchanged *)
      apply typing_var. rewrite <- (lookup_term_below G1 g T n Hgt). exact H.
  - (* abs *) apply typing_abs. apply (IHHe (has_type t1 :: G1)). reflexivity.
  - (* app *) eapply typing_app; eauto.
  - (* tabs *)
    apply typing_tabs.
    replace (term_tlift 1 0 (term_tlift (ntype G1) 0 u))
      with (term_tlift (S (ntype G1)) 0 u)
      by (rewrite term_tlift_comp;
          replace (1 + ntype G1) with (S (ntype G1)) by lia; reflexivity).
    apply (IHHe (has_kind K :: G1)). reflexivity.
  - (* tapp *)
    eapply typing_tapp. apply (IHHe G1). reflexivity.
  - (* cast *) eapply typing_cast; eauto.
  - (* gnd *) apply typing_gnd; eauto.
  - (* is_gnd *) apply (typing_is_gnd _ _ G); eauto.
  - (* blame *) apply typing_blame.
  - (* nu *)
    replace (term_tlift 1 0 (term_tlift (ntype G1) 0 u))
      with (term_tlift (S (ntype G1)) 0 u)
      by (rewrite term_tlift_comp;
          replace (1 + ntype G1) with (S (ntype G1)) by lia; reflexivity).
    apply typing_nu.
    + apply (IHHe (has_def K A :: G1)). reflexivity.
    + eapply wf_typ_strengthen_type; eauto.
  - (* conv *) eapply typing_conv; [ eauto | auto |].
    eapply wf_typ_strengthen_type; eauto.
Qed.

(** Front term substitution (the common case): substituting for the outermost bound variable. *)
Corollary typing_subst0 : forall g e u T B,
  typing (has_type T :: g) e B ->
  typing g u T ->
  typing g (subst u 0 e) B.
Proof.
  intros. pose proof (typing_subst nil g e u T B H H0) as P.
  simpl in P. rewrite term_tlift_zero in P. exact P.
Qed.

(** ** Type substitution: auxiliary preservation lemmas *)

(** [ty_step] commutes with [tsubst]: reduction is stable under type substitution. *)
Lemma ty_step_tsubst : forall A B, ty_step A B ->
  forall s k, ty_step (tsubst s k A) (tsubst s k B).
Proof.
  induction 1; intros s k; simpl; try (constructor; auto; fail).
  - rewrite distribute_tsubst. apply tystep_beta.
Qed.

(** [ty_equiv] is preserved by [tsubst], lifted pointwise from [ty_step_tsubst]. *)
Lemma ty_equiv_tsubst : forall A B, ty_equiv A B ->
  forall s k, ty_equiv (tsubst s k A) (tsubst s k B).
Proof.
  unfold ty_equiv; induction 1; intros s k.
  - apply rst_step, ty_step_tsubst; auto.
  - apply rst_refl.
  - apply rst_sym; auto.
  - eapply rst_trans; eauto.
Qed.

(** [compat] is preserved by substituting an abstract (neutral) type name.
    The [neutral s] hypothesis is the ν-aware restriction: substituting a
    non-neutral type could turn a neutral ground into a redex and break the
    [ground_tag]/guard side-conditions.  See [neutral_tsubst] and friends. *)
Lemma compat_tsubst : forall A B, compat A B ->
  forall s k, neutral s -> compat (tsubst s k A) (tsubst s k B).
Proof.
  induction 1; intros s k Hs; simpl.
  - apply compat_refl.
  - apply compat_arrow; auto.
  - apply compat_all; auto.
  - (* generalize *) apply compat_generalize.
    + apply tsubst_neutral_not_dyn; assumption.
    + intros K' C; apply tsubst_neutral_not_all; assumption.
    + rewrite (commute_tlift_tsubst_rec A s 1 k 0) by lia.
      replace (1 + k) with (S k) by lia. apply (IHcompat s (S k) Hs).
  - (* instantiate *) apply compat_instantiate.
    + intros K' B'; apply tsubst_neutral_not_all; assumption.
    + pose proof (distribute_tsubst_rec A dyn s k 0) as Hd.
      simpl in Hd. rewrite <- Hd. apply IHcompat; assumption.
  - (* to_dyn *) apply compat_to_dyn with (G := tsubst s k G).
    + apply tsubst_neutral_not_dyn; assumption.
    + intros K B; apply tsubst_neutral_not_all; assumption.
    + apply ground_tag_tsubst; assumption.
    + apply IHcompat; assumption.
  - (* from_dyn *) apply compat_from_dyn.
    + apply tsubst_neutral_not_dyn; assumption.
    + apply cast_form_tsubst; assumption.
Qed.

(** ** Type substitution lemma *)

(** Apply [tsubst s k] to the type(s) stored in a single binding; the [tsubst] analogue of [tlift_binding]. *)
Definition tsubst_binding (s : typ) (k : nat) (b : binding) : binding :=
  match b with
  | has_type A => has_type (tsubst s k A)
  | has_kind K => has_kind K
  | has_def K A => has_def K (tsubst s k A)
  end.

(** Substitute [s] for the type variable removed at a context's own tail
    throughout a prefix's stored types, at each binding's own cutoff
    (mirrors [tlift_ctx], for removing rather than inserting a type variable). *)
Fixpoint tsubst_ctx (s : typ) (G : context) : context :=
  match G with
  | nil => nil
  | b :: G' => tsubst_binding s (ntype G') b :: tsubst_ctx s G'
  end.

(** [tsubst_ctx] doesn't change the number of type-variable bindings (it only rewrites their stored types). *)
Lemma ntype_tsubst_ctx : forall s G, ntype (tsubst_ctx s G) = ntype G.
Proof.
  intros s G; induction G as [|b G IH]; simpl; auto.
  destruct b; simpl; auto.
Qed.

(** [tsubst_ctx] doesn't change the number of term-variable bindings. *)
Lemma nterm_tsubst_ctx : forall s G, nterm (tsubst_ctx s G) = nterm G.
Proof.
  intros s G; induction G as [|b G IH]; simpl; auto.
  destruct b; simpl; auto.
Qed.

(** A [has_kind] binding below the substitution point ([n < ntype G1]) is unaffected by removing the [has_kind K] binding further in and [tsubst_ctx]-rewriting the prefix. *)
Lemma lookup_kind_tsubst_below : forall G1 g K s n,
  n < ntype G1 ->
  lookup_kind (tsubst_ctx s G1 ++ g) n = lookup_kind (G1 ++ has_kind K :: g) n.
Proof.
  induction G1 as [|b G1 IH]; intros g K s n Hn; simpl in *; [lia |].
  destruct b as [D | K' | K' D]; simpl in *.
  - apply IH; lia.
  - destruct n; [reflexivity |]. apply IH; lia.
  - destruct n; [reflexivity |]. apply IH; lia.
Qed.

(** Looking up the [has_kind K] binding removed by substitution returns its kind [K], at its own index [ntype G1]. *)
Lemma lookup_kind_tsubst_eq : forall G1 g K,
  lookup_kind (G1 ++ has_kind K :: g) (ntype G1) = Some K.
Proof.
  induction G1 as [|b G1 IH]; intros g K; simpl.
  - reflexivity.
  - destruct b as [D | K' | K' D]; simpl; auto.
Qed.

(** A [has_kind]/[has_def] binding above the substitution point ([n > ntype G1]) shifts down by one, since the [has_kind K] binding it referenced is gone. *)
Lemma lookup_kind_tsubst_above : forall G1 g K s n,
  n > ntype G1 ->
  lookup_kind (tsubst_ctx s G1 ++ g) (pred n) = lookup_kind (G1 ++ has_kind K :: g) n.
Proof.
  induction G1 as [|b G1 IH]; intros g K s n Hn; simpl in *.
  - destruct n; [lia |]. simpl. reflexivity.
  - destruct b as [D | K' | K' D]; simpl in *.
    + apply IH. lia.
    + destruct n as [|n']; [lia |]. simpl.
      destruct n' as [|n'']; [lia |]. simpl.
      apply (IH g K s (S n'')). lia.
    + destruct n as [|n']; [lia |]. simpl.
      destruct n' as [|n'']; [lia |]. simpl.
      apply (IH g K s (S n'')). lia.
Qed.

(** [k = 0] specialization of [infrastructure.tsubst_tlift_cancel], re-proved
    directly from [simplify_tsubst_rec]/[tlift_zero]; shadows the imported
    name for the rest of this file. *)
Lemma tsubst_tlift_cancel : forall t s, tsubst s 0 (tlift 1 0 t) = t.
Proof.
  intros. rewrite (simplify_tsubst_rec t s 0 0 0) by lia. apply tlift_zero.
Qed.

(** [option_map] composes. *)
Lemma option_map_compose : forall {A B C} (f : B -> C) (g : A -> B) o,
  option_map f (option_map g o) = option_map (fun x => f (g x)) o.
Proof. intros. destruct o; reflexivity. Qed.

(** [option_map] respects pointwise-equal functions. *)
Lemma option_map_ext : forall {A B} (f g : A -> B) o,
  (forall x, f x = g x) -> option_map f o = option_map g o.
Proof. intros. destruct o; simpl; [f_equal; auto | reflexivity]. Qed.

(** Term-variable lookups after removing the [has_kind K] binding at [ntype
    G1] have their stored types substituted at the vacated index, mirroring
    how [lookup_term_weaken_kind] lifted them on insertion. *)
Lemma lookup_term_tsubst : forall G1 g K s n,
  lookup_term (tsubst_ctx s G1 ++ g) n
    = option_map (tsubst s (ntype G1)) (lookup_term (G1 ++ has_kind K :: g) n).
Proof.
  induction G1 as [|b G1 IH]; intros g K s n; simpl.
  - destruct (lookup_term g n) as [x|]; simpl; [| reflexivity].
    f_equal. symmetry. apply tsubst_tlift_cancel.
  - destruct b as [D | K' | K' D]; simpl.
    + destruct n as [|n']; simpl; [reflexivity |]. apply IH.
    + rewrite (IH g K). rewrite !option_map_compose. apply option_map_ext.
      intros x. apply commute_tlift_tsubst_rec; lia.
    + rewrite (IH g K). rewrite !option_map_compose. apply option_map_ext.
      intros x. apply commute_tlift_tsubst_rec; lia.
Qed.

(** A type well-kinded in the tail [g] is still well-kinded after both
    [tsubst_ctx]-rewriting a prefix [G1] and correspondingly [tlift]-ing the
    type itself; the [tvar]-at-the-substitution-point case of [wf_typ_tsubst]. *)
Lemma wf_typ_weaken_tsubst_prefix : forall G1 g s A K,
  wf_typ g A K ->
  wf_typ (tsubst_ctx s G1 ++ g) (tlift (ntype G1) 0 A) K.
Proof.
  induction G1 as [|b G1 IH]; intros g s A K H; simpl.
  - rewrite tlift_zero. exact H.
  - destruct b as [C | K' | K' C]; simpl.
    + apply (wf_typ_weaken_type nil). apply IH. exact H.
    + pose proof (wf_typ_weaken_kind nil (tsubst_ctx s G1 ++ g) K'
                    (tlift (ntype G1) 0 A) K (IH g s A K H)) as P.
      simpl in P.
      rewrite (simplify_tlift_rec A (ntype G1) 0 1 0) in P by lia.
      replace (1 + ntype G1) with (S (ntype G1)) in P by lia. exact P.
    + pose proof (wf_typ_weaken_def nil (tsubst_ctx s G1 ++ g) K' (tsubst s (ntype G1) C)
                    (tlift (ntype G1) 0 A) K (IH g s A K H)) as P.
      simpl in P.
      rewrite (simplify_tlift_rec A (ntype G1) 0 1 0) in P by lia.
      replace (1 + ntype G1) with (S (ntype G1)) in P by lia. exact P.
Qed.

(** Type substitution preserves kinding: substituting a kind-[K] type [s] for
    the type variable bound by [has_kind K] yields a type of the same kind
    [K0] in the correspondingly [tsubst_ctx]-rewritten context. *)
Lemma wf_typ_tsubst : forall G1 g K s A K0,
  wf_typ (G1 ++ has_kind K :: g) A K0 ->
  wf_typ g s K ->
  wf_typ (tsubst_ctx s G1 ++ g) (tsubst s (ntype G1) A) K0.
Proof.
  intros G1 g K s A K0 H. remember (G1 ++ has_kind K :: g) as g0 eqn:Hg. revert G1 Hg.
  induction H; intros G1 Hg Hs; subst.
  - (* tvar *) simpl. destruct (lt_eq_lt_dec (ntype G1) n) as [[Hlt|Heq]|Hgt].
    + apply wf_tvar. rewrite (lookup_kind_tsubst_above G1 g K s n) by lia. exact H.
    + subst. rewrite lookup_kind_tsubst_eq in H. injection H as <-.
      apply wf_typ_weaken_tsubst_prefix. exact Hs.
    + apply wf_tvar. rewrite (lookup_kind_tsubst_below G1 g K s n) by lia. exact H.
  - simpl. apply wf_arrow; auto.
  - simpl. apply wf_all. apply (IHwf_typ (has_kind K0 :: G1)); [reflexivity | exact Hs].
  - simpl. apply wf_tyabs. apply (IHwf_typ (has_kind K1 :: G1)); [reflexivity | exact Hs].
  - simpl. eapply wf_tyapp; eauto.
  - simpl. apply wf_dyn.
Qed.

(** [ground] is preserved by substituting an abstract (neutral) type name.
    With neutral ground tags this needs [neutral s]: substituting an arbitrary
    type for a neutral ground's head variable could destroy groundness. *)
Lemma ground_tsubst : forall G s k, neutral s -> ground G -> ground (tsubst s k G).
Proof.
  intros G s k Hs Hg; inversion Hg; subst; simpl.
  - apply ground_arrow.
  - apply ground_neutral. apply neutral_tsubst; assumption.
Qed.

(** ν-aware type substitution lemma.  Substituting an abstract (neutral) type
    name [S] for a type variable preserves typing.  The [neutral S] hypothesis
    is what keeps the [gnd] and [cast] cases sound now that ground tags include
    neutral types (see [ground_tsubst], [compat_tsubst]): a sealed variable
    always stands for an abstract name, so this is the fragment ν-elimination
    needs.  Substituting a non-neutral type is the remaining open work. *)
Lemma typing_tsubst : forall G1 g e S K A,
  typing (G1 ++ has_kind K :: g) e A ->
  wf_typ g S K -> neutral S ->
  typing (tsubst_ctx S G1 ++ g) (term_tsubst S (ntype G1) e) (tsubst S (ntype G1) A).
Proof.
  intros G1 g e S K A He Hs Hns.
  remember (G1 ++ has_kind K :: g) as g0 eqn:Hg. revert G1 Hg.
  induction He; intros G1 Hg; subst; simpl.
  - (* var *) apply typing_var. rewrite (lookup_term_tsubst G1 g K). rewrite H. reflexivity.
  - (* abs *) apply typing_abs. apply (IHHe (has_type t1 :: G1)). reflexivity.
  - (* app *) eapply typing_app; eauto.
  - (* tabs *) apply typing_tabs. apply (IHHe (has_kind K0 :: G1)). reflexivity.
  - (* tapp *)
    pose proof (distribute_tsubst_rec t s S (ntype G1) 0) as Hd. simpl in Hd.
    rewrite Hd. eapply typing_tapp. apply (IHHe G1). reflexivity.
  - (* cast *) eapply typing_cast; [ apply (IHHe G1); reflexivity | apply compat_tsubst; assumption ].
  - (* gnd *) apply typing_gnd; [ apply (IHHe G1); reflexivity | apply ground_tsubst; assumption ].
  - (* is_gnd *) apply (typing_is_gnd _ _ (tsubst S (ntype G1) G)). apply (IHHe G1). reflexivity.
  - (* blame *) apply typing_blame.
  - (* nu *)
    pose proof (distribute_tsubst_rec B A S (ntype G1) 0) as Hd. simpl in Hd.
    rewrite Hd.
    apply typing_nu.
    + apply (IHHe (has_def K0 A :: G1)). reflexivity.
    + eapply wf_typ_tsubst; eauto.
  - (* conv *) eapply typing_conv;
      [ apply (IHHe G1); reflexivity
      | apply ty_equiv_tsubst; auto
      | eapply wf_typ_tsubst; eauto ].
Qed.

Corollary typing_tsubst0 : forall g e s K A,
  typing (has_kind K :: g) e A ->
  wf_typ g s K -> neutral s ->
  typing g (term_tsubst s 0 e) (tsubst s 0 A).
Proof.
  intros. pose proof (typing_tsubst nil g e s K A H H0 H1) as P.
  simpl in P. exact P.
Qed.
