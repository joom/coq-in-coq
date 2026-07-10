From Stdlib Require Import Arith Lia List Relations Bool Program.Equality.
Import ListNotations.
From CoC Require terms.
From CoC Require typing.
From CoC Require Import confluence.
From CoC Require Import inference.
From CoC Require Import strong_normalization.
From CoC Require Import decidable_conversion.
From BlameFOmega Require syntax infrastructure semantics typing typing_metatheory
  subtyping safety blame subtyping_safety simulation.
From Extraction Require extraction.
From Extraction Require Import common.
From Extraction Require Import source_facts.
From Extraction Require Import translation.

Import terms.
Import CoC.typing.
Import extraction.

Lemma typing_dyn_token : forall g,
  typing.typing g dyn_token syntax.dyn.
Proof.
  intro g. unfold dyn_token, dyn_fun.
  apply typing.typing_gnd.
  - apply typing.typing_abs.
    + apply typing.wf_dyn.
    + apply typing.typing_var. reflexivity.
  - constructor.
    + apply syntax.ground_arrow.
    + apply typing.wf_arrow; apply typing.wf_dyn.
Qed.

(** [coerce s A B] is well-typed at [B] whenever [s : A].  When [compat A B]
    holds, a real cast is emitted (typed by [typing_cast]).  When it does not,
    [blame internal_label] is emitted, which is typable at any type. *)
Lemma typing_coerce : forall g s A B,
  typing_metatheory.wf_ctx g ->
  typing.typing g s A ->
  typing.wf_typ g B syntax.KStar ->
  typing.typing g (coerce s A B) B.
Proof.
  intros g s A B Hg Hs HwfB. unfold coerce.
  destruct (syntax.typ_eq_dec A B) as [-> | Hneq].
  - exact Hs.
  - destruct (infrastructure.compat_dec A B) as [Hc | _].
    + eapply typing.typing_cast; eauto.
      exact (typing_metatheory.typing_regular g s A Hg Hs).
    + apply typing.typing_blame. exact HwfB.
Qed.

(** [dyn_token] contains no cast blaming an external label. *)
Lemma safe_dyn_token : forall p,
  safety.safe_pos_neg p dyn_token.
Proof.
  intro p. unfold dyn_token.
  apply safety.spn_gnd.
  apply safety.spn_abs.
  apply safety.spn_var.
Qed.

(** [coerce]'s casts use the internal label, so it stays safe for any external label. *)
Lemma safe_coerce_external : forall p s A B,
  syntax.lbl_id p >= 2 ->
  safety.safe_pos_neg p s ->
  safety.safe_pos_neg p (coerce s A B).
Proof.
  intros p s A B Hge Hs. unfold coerce.
  destruct (syntax.typ_eq_dec A B) as [_ | _].
  - exact Hs.
  - destruct (infrastructure.compat_dec A B) as [_ | _].
    + apply safety.spn_cast_other.
      * unfold internal_label. simpl. lia.
      * exact Hs.
    + apply safety.spn_blame. intro Heq. rewrite <- Heq in Hge.
      unfold internal_label in Hge. simpl in Hge. lia.
Qed.


(** [dyn_token] is closed, so target lifting and substitution leave it fixed. *)
Lemma lift_dyn_token : forall i k,
  infrastructure.lift i k dyn_token = dyn_token.
Proof.
  intros i k. unfold dyn_token, dyn_fun. simpl.
  destruct (le_gt_dec (S k) 0); [lia | reflexivity].
Qed.

(** Term substitution leaves the closed [dyn_token] fixed. *)
Lemma subst_dyn_token : forall s k,
  infrastructure.subst s k dyn_token = dyn_token.
Proof.
  intros s k. unfold dyn_token, dyn_fun. simpl.
  destruct (lt_eq_lt_dec (S k) 0) as [[Hlt | Heq] | Hgt]; [lia | lia | reflexivity].
Qed.

(** Treat [dyn_token] as atomic so [simpl] does not unfold it. *)
Opaque dyn_token.

(** [sim_star] congruence for [abs]. *)
Lemma sim_star_abs : forall A s t,
  simulation.sim_star s t ->
  simulation.sim_star (syntax.abs A s) (syntax.abs A t).
Proof.
  intros A s t H. induction H.
  - apply simulation.sim_star_step.
    apply simulation.sim_abs; assumption.
  - apply simulation.sim_star_refl.
  - eapply simulation.sim_star_trans; eassumption.
Qed.

(** [abs] congruence for [sim_star], ignoring the (irrelevant) domain annotations. *)
Lemma sim_star_abs_gen : forall A A' s t,
  simulation.sim_star s t ->
  simulation.sim_star (syntax.abs A s) (syntax.abs A' t).
Proof.
  intros A A' s t H.
  eapply simulation.sim_star_trans.
  - exact (sim_star_abs A s t H).
  - apply simulation.sim_star_step.
    apply simulation.sim_abs.
    apply simulation.sim_refl.
Qed.

(** [sim_star] congruence in the function position of an application. *)
Lemma sim_star_app_l : forall s s' t,
  simulation.sim_star s s' ->
  simulation.sim_star (syntax.app s t) (syntax.app s' t).
Proof.
  intros s s' t H. induction H.
  - apply simulation.sim_star_step.
    apply simulation.sim_app; [assumption | apply simulation.sim_refl].
  - apply simulation.sim_star_refl.
  - eapply simulation.sim_star_trans; eassumption.
Qed.

(** [sim_star] congruence in the argument position of an application. *)
Lemma sim_star_app_r : forall s t t',
  simulation.sim_star t t' ->
  simulation.sim_star (syntax.app s t) (syntax.app s t').
Proof.
  intros s t t' H. induction H.
  - apply simulation.sim_star_step.
    apply simulation.sim_app; [apply simulation.sim_refl | assumption].
  - apply simulation.sim_star_refl.
  - eapply simulation.sim_star_trans; eassumption.
Qed.

(** [app] congruence for [sim_star] in both positions. *)
Lemma sim_star_app : forall s s' t t',
  simulation.sim_star s s' ->
  simulation.sim_star t t' ->
  simulation.sim_star (syntax.app s t) (syntax.app s' t').
Proof.
  intros s s' t t' Hs Ht.
  eapply simulation.sim_star_trans.
  - apply sim_star_app_l. exact Hs.
  - apply sim_star_app_r. exact Ht.
Qed.


(** ** Optimism: the [F_omega]-typed fragment extracts without [dyn]

    The translation is optimistic: it only falls back to [dyn] where the source
    genuinely leaves the [F_omega] type discipline (a sort used as a type, a
    term variable used as a type, or a type application whose head is not a
    type family).  We make this precise for type expressions.

    [typ_dyn_free A] holds when the target type [A] contains no [dyn]. *)
Fixpoint typ_dyn_free (A: syntax.typ) : Prop :=
  match A with
  | syntax.dyn => False
  | syntax.tvar _ => True
  | syntax.arrow A B => typ_dyn_free A /\ typ_dyn_free B
  | syntax.all K A => typ_dyn_free A
  | syntax.tyabs _ A => typ_dyn_free A
  | syntax.tyapp A B => typ_dyn_free A /\ typ_dyn_free B
  end.

(** ** Reduction-stable classification

    The abs/tabs, arrow/all, and KStar/KArr decisions must not flip under
    source reduction; [is_large] (being a kind) is the reduction-stable
    notion that drives the extraction,
    and the old [classifier] is shown to be a sound-but-incomplete approximation
    of it.  These lemmas are the crux enabling a simulation about the real
    [extract] under full beta. *)

(** [is_large] is preserved by a single reduction step: this is exactly the
    stability that the syntactic [classifier] lacks. *)
Lemma is_large_stable : forall e T T',
  is_large e T -> reduces_once T T' -> is_large e T'.
Proof.
  intros e T T' H Hr. unfold is_large in *.
  eapply subject_reduction; eassumption.
Qed.

(** ... and by multi-step reduction. *)
Lemma is_large_stable_star : forall e T T',
  is_large e T -> reduces T T' -> is_large e T'.
Proof.
  intros e T T' H Hr. unfold is_large in *.
  eapply subject_reduction_theorem; eassumption.
Qed.

(** The syntactic [classifier] is SOUND for [is_large]: whenever a well-sorted
    type is syntactically a classifier, its sort really is [kind].  (It is not
    complete -- e.g. [(fun x:set => set) y] is large but not a syntactic
    classifier -- and that incompleteness under reduction is what the redesign
    must eliminate.) *)
Lemma classifier_sound : forall T e s,
  has_type e T (sort_term s) -> classifier T = true -> s = kind.
Proof.
  intros T.
  induction T as [s0 | n | T1 IHT1 T2 IHT2 | T1 IHT1 T2 IHT2 | T1 IHT1 T2 IHT2];
    intros e s Hty Hcl; simpl in Hcl; try discriminate.
  - (* sort_term s0; constructor order is kind, prop, set *)
    destruct s0.
    + exfalso. eapply inversion_has_type_kind. exact Hty.
    + apply inversion_has_type_prop in Hty. apply convertible_sort in Hty. exact Hty.
    + apply inversion_has_type_set in Hty. apply convertible_sort in Hty. exact Hty.
  - (* prod T1 T2 *)
    apply (inversion_has_type_prod (s = kind) e T1 T2 (sort_term s) Hty).
    intros s1 s2 HT1 HT2 Hconv.
    apply convertible_sort in Hconv.
    assert (Hs2: s2 = kind) by (eapply IHT2; [exact HT2 | exact Hcl]).
    congruence.
Qed.

(** The syntactic [classifier] is also COMPLETE for [is_large] on NORMAL forms:
    a normal, large (kind-sorted) type is syntactically a classifier.  The only
    normal kinds are sorts and products ending in a kind; a normal [var], [lam],
    or [app] can never have sort [kind].  Together with [classifier_sound] this
    gives full agreement [classifier T = true <-> is_large e T] on normal
    well-sorted types -- the correctness justification for a normalize-then-extract
    implementation (normalize the type, then the cheap syntactic [classifier] is
    exactly right, and is reduction-stable because the normal form is). *)
Lemma classifier_complete_nf : forall T e,
  is_large e T -> normal T -> classifier T = true.
Proof.
  intros T.
  induction T as [s0 | n | A IHA M IHM | u IHu v IHv | A IHA B IHB];
    intros e HL Hnorm; unfold is_large in HL.
  - (* sort_term: always a classifier *) reflexivity.
  - (* var: a variable can never have sort kind *)
    exfalso.
    apply (inversion_has_type_ref False e (sort_term kind) n HL).
    intros U Hnth Hconv.
    assert (Hwf: well_formed e) by (apply has_type_well_formed with (var n) (sort_term kind); exact HL).
    assert (Hil: item_lift (lift (S n) U) e n)
      by (refine (existT2 _ _ U _ _); [reflexivity | exact Hnth]).
    destruct (well_formed_sort_lift n e (lift (S n) U) Hwf Hil) as [s Hs].
    apply (inversion_has_type_convertible_kind e (lift (S n) U) (sort_term s));
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
    destruct (type_case e u (prod V Ur) Hu) as [[s Hs] | Hbad]; [| discriminate Hbad].
    apply (inversion_has_type_prod False e V Ur (sort_term s) Hs).
    intros s1 s2 HV HUr Hconv2.
    assert (Hsub: has_type e (subst v Ur) (subst v (sort_term s2)))
      by (apply substitution with (t := V); [exact HUr | exact Hv]).
    simpl in Hsub.
    apply (inversion_has_type_convertible_kind e (subst v Ur) (sort_term s2));
      [ apply sym_convertible; exact Hconv | exact Hsub ].
  - (* prod A B: large iff codomain large; recurse on the (normal) codomain *)
    simpl. apply (IHB (A :: e)).
    + (* is_large (A::e) B, inlined from the product characterization *)
      apply (inversion_has_type_prod (has_type (A :: e) B (sort_term kind))
               e A B (sort_term kind) HL).
      intros s1 s2 HA HB Hconv. apply convertible_sort in Hconv. subst s2. exact HB.
    + intros w Hw. apply (Hnorm (prod A w)). apply prod_reduces_right. exact Hw.
Qed.

(** Full agreement on normal, well-sorted types. *)
Lemma classifier_iff_is_large_nf : forall T e s,
  has_type e T (sort_term s) -> normal T ->
  ((classifier T = true -> is_large e T) * (is_large e T -> classifier T = true))%type.
Proof.
  intros T e s Hty Hnorm. split.
  - intro Hcl. unfold is_large. rewrite (classifier_sound T e s Hty Hcl) in Hty. exact Hty.
  - intro HL. apply (classifier_complete_nf T e HL Hnorm).
Qed.

(** Backward stability: largeness is also reflected by reduction.  If [T] is
    well-sorted and reduces to a large [T'], then [T] was already large.  Uses
    subject reduction plus uniqueness of types ([has_type_unique_sort]): the two
    sorts of [T'] ([s] and [kind]) must be convertible, hence equal. *)
Lemma is_large_expand : forall e T T' s,
  has_type e T (sort_term s) -> reduces_once T T' -> is_large e T' -> is_large e T.
Proof.
  intros e T T' s HT Hr HL. unfold is_large in *.
  assert (HT': has_type e T' (sort_term s)) by (eapply subject_reduction; eassumption).
  assert (Hconv: convertible (sort_term s) (sort_term kind))
    by (apply (has_type_unique_sort e T' (sort_term s) HT' (sort_term kind) HL)).
  apply convertible_sort in Hconv. subst s. exact HT.
Qed.

(** Largeness is preserved by multi-step expansion of a well-sorted type. *)
Lemma is_large_expand_star : forall e T T' s,
  has_type e T (sort_term s) -> reduces T T' -> is_large e T' -> is_large e T.
Proof.
  intros e T T' s HT Hr HL. unfold is_large in *.
  assert (HT': has_type e T' (sort_term s)) by (eapply subject_reduction_theorem; eassumption).
  assert (Hconv: convertible (sort_term s) (sort_term kind))
    by (apply (has_type_unique_sort e T' (sort_term s) HT' (sort_term kind) HL)).
  apply convertible_sort in Hconv. subst s. exact HT.
Qed.

(** The linchpin for the simulation redesign: for a well-sorted type, largeness
    is INVARIANT under reduction (both directions).  Consequently every extraction
    decision that branches on largeness makes the SAME choice for a source term
    and any reduct of it -- which is exactly what removes the [abs]/[tabs] and
    [arrow]/[all] flips that made a simulation about the precise extraction false. *)
Lemma is_large_iff : forall e T T' s,
  has_type e T (sort_term s) -> reduces_once T T' ->
  ((is_large e T -> is_large e T') * (is_large e T' -> is_large e T))%type.
Proof.
  intros e T T' s HT Hr. split.
  - intro H. eapply is_large_stable; eassumption.
  - intro H. eapply is_large_expand; eassumption.
Qed.

(** Largeness is invariant under multi-step reduction of a well-sorted type. *)
Lemma is_large_iff_star : forall e T T' s,
  has_type e T (sort_term s) -> reduces T T' ->
  iffT (is_large e T) (is_large e T').
Proof.
  intros e T T' s HT Hr. split.
  - intro H. eapply is_large_stable_star; eassumption.
  - intro H. eapply is_large_expand_star; eassumption.
Qed.


(** Conversion-invariance: convertible types extract equally. *)
Lemma extract_kind_conv : forall T T' sn sn',
  convertible T T' -> extract_kind T sn = extract_kind T' sn'.
Proof.
  intros T T' sn sn' Hc. unfold extract_kind.
  rewrite (nf_respects_conv T T' sn sn' Hc). reflexivity.
Qed.

(** Reduction-stability (a special case of conversion-invariance). *)
Lemma extract_kind_stable : forall T T' sn sn',
  reduces_once T T' -> extract_kind T sn = extract_kind T' sn'.
Proof.
  intros T T' sn sn' Hr. apply extract_kind_conv.
  apply one_step_convertible_expansion in Hr. apply sym_convertible. exact Hr.
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


(** ** [is_large] is invariant under conversion of well-sorted types

    The semantic linchpin behind context-conversion-invariance of [extract_typ_L]:
    convertible well-sorted types are both large or both small.  Proof: take a
    common reduct (Church-Rosser); both sorts are preserved to it (subject
    reduction), so they are convertible, hence equal ([convertible_sort]). *)
Lemma is_large_conv : forall e T T' sT',
  convertible T T' -> has_type e T' (sort_term sT') ->
  is_large e T -> is_large e T'.
Proof.
  intros e T T' sT' Hconv HT' HL. unfold is_large in *.
  destruct (church_rosser_theorem T T' Hconv) as [W HTW HT'W].
  assert (HWk: has_type e W (sort_term kind))
    by (exact (subject_reduction_theorem e T W HTW (sort_term kind) HL)).
  assert (HWs: has_type e W (sort_term sT'))
    by (exact (subject_reduction_theorem e T' W HT'W (sort_term sT') HT')).
  assert (Hcs: convertible (sort_term kind) (sort_term sT'))
    by (exact (has_type_unique_sort e W (sort_term kind) HWk (sort_term sT') HWs)).
  apply convertible_sort in Hcs. subst sT'. exact HT'.
Qed.

(** Symmetric packaging: for two well-sorted convertible types, largeness agrees. *)
Lemma is_large_conv_iff : forall e T T' sT sT',
  convertible T T' ->
  has_type e T (sort_term sT) -> has_type e T' (sort_term sT') ->
  iffT (is_large e T) (is_large e T').
Proof.
  intros e T T' sT sT' Hconv HT HT'. split.
  - intro. eapply is_large_conv; eassumption.
  - intro. eapply is_large_conv; [ apply sym_convertible; eassumption | eassumption | assumption ].
Qed.


(** ** Typing / [is_large] invariance under reducing a context binder

    Building toward the context-swap lemma: reducing the head binder of a context
    preserves typing (iterate the library's one-step [has_type_reduces_environment]
    over a multi-step binder reduction, pushing well-formedness forward). *)

(** ** Binder reduction at arbitrary context depth

    Generalizes the head-binder invariance to a binder under any prefix [D],
    which is what the context-swap induction needs (the swapped binder sinks
    deeper as [extract_typ_L] recurses under binders). *)

Lemma red_env_at : forall D t u e, reduces_once t u ->
  reduces_once_in_environment (D ++ t :: e) (D ++ u :: e).
Proof.
  induction D as [|a D IH]; intros t u e Hr; simpl.
  - apply red_env_hd; exact Hr.
  - apply red_env_tl; apply IH; exact Hr.
Qed.

(** Well-formedness is preserved when a context binder takes one reduction step. *)
Lemma wf_ctx_red_at_once : forall D T T' e,
  well_formed (D ++ T :: e) -> reduces_once T T' -> well_formed (D ++ T' :: e).
Proof.
  induction D as [|a D IH]; intros T T' e Hwf Hr; simpl in *.
  - inversion_clear Hwf. apply wf_var with s. eapply subject_reduction; eassumption.
  - inversion_clear Hwf. apply wf_var with s.
    apply has_type_reduces_environment with (D ++ T :: e).
    + exact H.
    + apply red_env_at; exact Hr.
    + apply IH with T; [ apply has_type_well_formed with a (sort_term s); exact H | exact Hr ].
Qed.

(** Well-formedness is preserved when a context binder reduces. *)
Lemma wf_ctx_red_at : forall D T T' e,
  well_formed (D ++ T :: e) -> reduces T T' -> well_formed (D ++ T' :: e).
Proof.
  intros D T T' e Hwf Hr. induction Hr as [| P N Hstep Hrec IH IHIH].
  - exact Hwf.
  - apply wf_ctx_red_at_once with N; [ exact (IHIH Hwf) | exact Hrec ].
Qed.

(** Typing is preserved when a context binder at any depth reduces. *)
Lemma has_type_ctx_red_at : forall D T T' e,
  reduces T T' -> forall u X, has_type (D ++ T :: e) u X -> well_formed (D ++ T :: e) ->
  has_type (D ++ T' :: e) u X.
Proof.
  intros D T T' e Hr. induction Hr as [| P N Hstep Hrec IH IHIH]; intros u X Hu Hwf.
  - exact Hu.
  - apply has_type_reduces_environment with (D ++ N :: e).
    + apply IHIH; assumption.
    + apply red_env_at; exact Hrec.
    + apply wf_ctx_red_at with P; [ exact Hwf | apply trans_red with N; [ exact IH | exact Hrec ] ].
Qed.

(** Largeness is invariant under swapping a context binder at any depth for a reduct. *)
Lemma is_large_swap_at : forall D T T' e u s,
  reduces T T' -> well_formed (D ++ T :: e) -> has_type (D ++ T :: e) u (sort_term s) ->
  iffT (is_large (D ++ T :: e) u) (is_large (D ++ T' :: e) u).
Proof.
  intros D T T' e u s Hr Hwf Hs. split.
  - intro HL. unfold is_large in *. eapply has_type_ctx_red_at; eassumption.
  - intro HL. unfold is_large in *.
    assert (Hs' : has_type (D ++ T' :: e) u (sort_term s))
      by (eapply has_type_ctx_red_at; eassumption).
    assert (Hc : convertible (sort_term s) (sort_term kind))
      by (exact (has_type_unique_sort (D ++ T' :: e) u (sort_term s) Hs' (sort_term kind) HL)).
    apply convertible_sort in Hc. subst s. exact Hs.
Qed.


(** ** Classification is invariant under swapping a context binder for a reduct *)

Lemma type_binding_cons : forall a g n,
  type_binding (a :: g) (S n) = type_binding g n.
Proof. intros a g n. unfold type_binding. reflexivity. Qed.

(** [type_binding] is invariant under swapping a context binder for a reduct. *)
Lemma type_binding_swap : forall D T T' e n,
  reduces T T' -> well_formed (D ++ T :: e) ->
  type_binding (D ++ T :: e) n = type_binding (D ++ T' :: e) n.
Proof.
  induction D as [|a D IH]; intros T T' e n Hr Hwf.
  - destruct n as [|n'].
    + unfold type_binding; simpl.
      inversion_clear Hwf.
      assert (Hiff : iffT (is_large e T) (is_large e T')) by (eapply is_large_iff_star; eassumption).
      destruct (is_large_dec e T) as [HA|HA]; destruct (is_large_dec e T') as [HB|HB];
        try reflexivity; [ exfalso; apply HB, (fst Hiff), HA | exfalso; apply HA, (snd Hiff), HB ].
    + unfold type_binding; simpl. reflexivity.
  - destruct n as [|n'].
    + simpl (( a :: D) ++ _). unfold type_binding; simpl.
      inversion_clear Hwf.
      assert (Hiff : iffT (is_large (D ++ T :: e) a) (is_large (D ++ T' :: e) a)).
      { eapply is_large_swap_at;
          [ exact Hr | apply has_type_well_formed with a (sort_term s); exact H | exact H ]. }
      destruct (is_large_dec (D ++ T :: e) a) as [HA|HA];
      destruct (is_large_dec (D ++ T' :: e) a) as [HB|HB];
        try reflexivity; [ exfalso; apply HB, (fst Hiff), HA | exfalso; apply HA, (snd Hiff), HB ].
    + simpl ((a :: D) ++ _). rewrite !type_binding_cons.
      inversion_clear Hwf.
      apply IH; [ exact Hr | apply has_type_well_formed with a (sort_term s); exact H ].
Qed.

(** [type_index] is invariant under swapping a context binder for a reduct. *)
Lemma type_index_swap : forall D T T' e n,
  reduces T T' -> well_formed (D ++ T :: e) ->
  type_index (D ++ T :: e) n = type_index (D ++ T' :: e) n.
Proof.
  induction D as [|a D IH]; intros T T' e n Hr Hwf.
  - destruct n as [|n']; [reflexivity|]. simpl.
    inversion_clear Hwf.
    assert (Hiff : iffT (is_large e T) (is_large e T')) by (eapply is_large_iff_star; eassumption).
    destruct (is_large_dec e T) as [HA|HA]; destruct (is_large_dec e T') as [HB|HB];
      try reflexivity;
      [ exfalso; apply HB, (fst Hiff), HA | exfalso; apply HA, (snd Hiff), HB ].
  - destruct n as [|n']; [reflexivity|]. simpl (( a :: D) ++ _). simpl.
    inversion_clear Hwf.
    assert (Hwf' : well_formed (D ++ T :: e)) by (apply has_type_well_formed with a (sort_term s); exact H).
    assert (Hiff : iffT (is_large (D ++ T :: e) a) (is_large (D ++ T' :: e) a))
      by (eapply is_large_swap_at; [ exact Hr | exact Hwf' | exact H ]).
    assert (Hidx : type_index (D ++ T :: e) n' = type_index (D ++ T' :: e) n')
      by (apply IH; [ exact Hr | exact Hwf' ]).
    destruct (is_large_dec (D ++ T :: e) a) as [HA|HA];
    destruct (is_large_dec (D ++ T' :: e) a) as [HB|HB];
      try (rewrite Hidx; reflexivity);
      [ exfalso; apply HB, (fst Hiff), HA | exfalso; apply HA, (snd Hiff), HB ].
Qed.

(** [term_index] is invariant under swapping a context binder for a reduct. *)
Lemma term_index_swap : forall D T T' e n,
  reduces T T' -> well_formed (D ++ T :: e) ->
  term_index (D ++ T :: e) n = term_index (D ++ T' :: e) n.
Proof.
  induction D as [|a D IH]; intros T T' e n Hr Hwf.
  - destruct n as [|n']; [reflexivity|]. simpl.
    inversion_clear Hwf.
    assert (Hiff : iffT (is_large e T) (is_large e T')) by (eapply is_large_iff_star; eassumption).
    destruct (is_large_dec e T) as [HA|HA]; destruct (is_large_dec e T') as [HB|HB];
      try reflexivity;
      [ exfalso; apply HB, (fst Hiff), HA | exfalso; apply HA, (snd Hiff), HB ].
  - destruct n as [|n']; [reflexivity|]. simpl (( a :: D) ++ _). simpl.
    inversion_clear Hwf.
    assert (Hwf' : well_formed (D ++ T :: e)) by (apply has_type_well_formed with a (sort_term s); exact H).
    assert (Hiff : iffT (is_large (D ++ T :: e) a) (is_large (D ++ T' :: e) a))
      by (eapply is_large_swap_at; [ exact Hr | exact Hwf' | exact H ]).
    assert (Hidx : term_index (D ++ T :: e) n' = term_index (D ++ T' :: e) n')
      by (apply IH; [ exact Hr | exact Hwf' ]).
    destruct (is_large_dec (D ++ T :: e) a) as [HA|HA];
    destruct (is_large_dec (D ++ T' :: e) a) as [HB|HB];
      try (rewrite Hidx; reflexivity);
      [ exfalso; apply HB, (fst Hiff), HA | exfalso; apply HA, (snd Hiff), HB ].
Qed.

(** ** [extract_typ_L] is invariant under swapping a context binder for a reduct *)

(** Type-level-headedness is invariant under swapping a context binder for a reduct. *)
Lemma type_expr_swap : forall T T', reduces T T' ->
  forall X D e A, has_type (D ++ T :: e) X A ->
  type_expr (D ++ T :: e) X = type_expr (D ++ T' :: e) X.
Proof.
  intros T T' Hr X.
  induction X as [s0 | n | X1 IHX1 X2 IHX2 | X1 IHX1 X2 IHX2 | X1 IHX1 X2 IHX2];
    intros D e A HX; simpl.
  - reflexivity.
  - apply type_binding_swap; [ exact Hr | apply has_type_well_formed with (var n) A; exact HX ].
  - (* lam X1 X2 *)
    apply (inversion_has_type_abs
             (type_expr (X1 :: D ++ T :: e) X2 = type_expr (X1 :: D ++ T' :: e) X2)
             (D ++ T :: e) X1 X2 A HX).
    intros s1 s2 T'' HA HM HT'' Hconv.
    exact (IHX2 (X1 :: D) e T'' HM).
  - (* app X1 X2 *)
    apply (inversion_has_type_app
             (type_expr (D ++ T :: e) X1 = type_expr (D ++ T' :: e) X1)
             (D ++ T :: e) X1 X2 A HX).
    intros V Ur Hu Hv Hconv.
    exact (IHX1 D e (prod V Ur) Hu).
  - reflexivity.
Qed.


(** Context-conversion-invariance of [extract_typ_L]: swapping a context binder for
    a reduct (of a well-typed type) leaves the extraction unchanged.  Dissolves the
    abs-codomain obstruction. *)
Lemma extract_typ_L_swap : forall T T', reduces T T' ->
  forall X D e A, has_type (D ++ T :: e) X A ->
  extract_typ_L (D ++ T :: e) X = extract_typ_L (D ++ T' :: e) X.
Proof.
  intros T T' Hr X.
  induction X as [s0 | n | X1 IHX1 X2 IHX2 | X1 IHX1 X2 IHX2 | X1 IHX1 X2 IHX2];
    intros D e A HX.
  - reflexivity.
  - simpl.
    assert (wf : well_formed (D ++ T :: e)) by (apply has_type_well_formed with (var n) A; exact HX).
    rewrite (type_binding_swap D T T' e n Hr wf).
    rewrite (type_index_swap D T T' e n Hr wf).
    reflexivity.
  - (* lam X1 X2 *)
    apply (inversion_has_type_abs _ _ _ _ _ HX).
    intros s1 s2 T'' HA HM HT'' Hconv.
    simpl.
    pose proof (IHX2 (X1 :: D) e T'' HM) as HM'. simpl in HM'. rewrite HM'.
    reflexivity.
  - (* app X1 X2 *)
    apply (inversion_has_type_app _ _ _ _ _ HX).
    intros V Ur Hu Hv Hconv.
    simpl.
    rewrite (type_expr_swap T T' Hr X1 D e (prod V Ur) Hu).
    rewrite (type_expr_swap T T' Hr X2 D e V Hv).
    rewrite (IHX1 D e (prod V Ur) Hu).
    rewrite (IHX2 D e V Hv).
    reflexivity.
  - (* prod X1 X2 *)
    apply (inversion_has_type_prod _ _ _ _ _ HX).
    intros s1 s2 HX1 HX2 Hconv.
    simpl.
    rewrite (IHX1 D e (sort_term s1) HX1).
    pose proof (IHX2 (X1 :: D) e (sort_term s2) HX2) as HM'. simpl in HM'. rewrite HM'.
    reflexivity.
Qed.




(** ** Context lookup for [extract_ctx] *)
Lemma extract_ctx_lookup_term : forall e v u,
  nth_error e v = Some u -> (is_large (skipn (S v) e) u -> False) ->
  forall w, typing.lookup_term (extract_ctx e w) (term_index e v)
            = Some (extract_lookup_type e w v).
Proof.
  induction e as [|T e' IH]; intros v u Hnth Hnl w.
  - destruct v; discriminate.
  - destruct v as [|v'].
    + simpl in Hnth. injection Hnth as <-. simpl in Hnl.
      simpl (term_index _ _). simpl (extract_lookup_type _ _ _).
      simpl (extract_ctx _ _).
      destruct (is_large_dec e' T) as [HL|HL].
      * exfalso. apply Hnl. exact HL.
      * reflexivity.
    + simpl in Hnth. simpl in Hnl.
      simpl (term_index _ _). simpl (extract_lookup_type _ _ _).
      simpl (extract_ctx _ _).
      destruct (is_large_dec e' T) as [HL|HL]; simpl.
      * rewrite (IH v' u Hnth Hnl (wf_tail T e' w)). reflexivity.
      * exact (IH v' u Hnth Hnl (wf_tail T e' w)).
Qed.


(** Context lookup in the TYPE namespace: a large (kind-level) source binding
    maps to a [has_kind] entry at the compressed type-index, carrying the
    extracted kind of that binding.  This is the kind-namespace analogue of
    [extract_ctx_lookup_term]; it is the first building block for a future
    kind-regularity proof of the extraction (that [extract_typ] emits well-kinded
    target types).  See the note in the module header / README limitation #5. *)
Lemma extract_ctx_lookup_kind : forall e v u,
  nth_error e v = Some u ->
  is_large (skipn (S v) e) u ->
  forall w (snu: strongly_normalizing u),
    typing.lookup_kind (extract_ctx e w) (type_index e v)
      = Some (extract_kind u snu).
Proof.
  induction e as [|T e' IH]; intros v u Hnth HL w snu.
  - destruct v; discriminate.
  - destruct v as [|v'].
    + simpl in Hnth. injection Hnth as <-. simpl in HL.
      simpl (type_index _ _). simpl (extract_ctx _ _).
      destruct (is_large_dec e' T) as [HL'|HL'].
      * simpl. rewrite (extract_kind_pi T (sn_of_binding T e' w) snu). reflexivity.
      * exfalso. apply HL'. exact HL.
    + simpl in Hnth. simpl in HL.
      simpl (type_index _ _). simpl (extract_ctx _ _).
      destruct (is_large_dec e' T) as [HL'|HL']; simpl.
      * rewrite (IH v' u Hnth HL (wf_tail T e' w) snu). reflexivity.
      * exact (IH v' u Hnth HL (wf_tail T e' w) snu).
Qed.


(** ** Largeness of a variable's type matches its binding *)
Lemma is_large_item_lift : forall e v u,
  well_formed e -> nth_error e v = Some u ->
  iffT (is_large e (lift (S v) u)) (is_large (skipn (S v) e) u).
Proof.
  intros e v u Hwf Hnth.
  destruct (well_formed_sort v e (skipn (S v) e) eq_refl Hwf u Hnth) as [s' Hu].
  assert (Hlift : has_type e (lift (S v) u) (sort_term s')).
  { replace (sort_term s') with (lift (S v) (sort_term s')) by (unfold lift; reflexivity).
    apply weakening_at with (skipn (S v) e);
      [ reflexivity | exact (nth_error_S_le _ e v u Hnth) | exact Hu | exact Hwf ]. }
  unfold is_large. split.
  - intro HL.
    assert (Hc : convertible (sort_term s') (sort_term kind))
      by (exact (has_type_unique_sort e (lift (S v) u) (sort_term s') Hlift (sort_term kind) HL)).
    apply convertible_sort in Hc. subst s'. exact Hu.
  - intro HL.
    assert (Hc : convertible (sort_term s') (sort_term kind))
      by (exact (has_type_unique_sort (skipn (S v) e) u (sort_term s') Hu (sort_term kind) HL)).
    apply convertible_sort in Hc. subst s'. exact Hlift.
Qed.


(** ** Syntactic [classifier] on [nf T] agrees with [is_large] *)
Lemma classifier_nf_is_large : forall e T sn s,
  has_type e T (sort_term s) -> iffT (classifier (nf T sn) = true) (is_large e T).
Proof.
  intros e T sn s HT.
  assert (Hnf : has_type e (nf T sn) (sort_term s))
    by (eapply subject_reduction_theorem; [apply nf_reduces | exact HT]).
  pose proof (classifier_iff_is_large_nf (nf T sn) e s Hnf (nf_normal T sn)) as H1.
  pose proof (is_large_iff_star e T (nf T sn) s HT (nf_reduces T sn)) as H2.
  split; intro H.
  - exact (snd H2 (fst H1 H)).
  - exact (snd H1 (fst H2 H)).
Qed.


(** ** Type preservation for [extract] *)


(** Type extraction is invariant under convertible context binders and
    convertible extracted types.  Requires typing in both environments to feed
    [extract_typ_L_swap] through the Church-Rosser common reduct. *)
Lemma extract_typ_ctx_conv : forall V0 V2, convertible V0 V2 ->
  forall X1 X2, convertible X1 X2 ->
  forall D e sn1 sn2 A A',
  has_type (D ++ V0 :: e) X1 A ->
  has_type (D ++ V2 :: e) X2 A' ->
  extract_typ (D ++ V0 :: e) X1 sn1 = extract_typ (D ++ V2 :: e) X2 sn2.
Proof.
  intros V0 V2 HconvV X1 X2 HconvX D e sn1 sn2 A A' HX HX'.
  unfold extract_typ.
  destruct (church_rosser_theorem V0 V2 HconvV) as [W HV0W HV2W].
  rewrite (nf_respects_conv X1 X2 sn1 sn2 HconvX).
  transitivity (extract_typ_L (D ++ W :: e) (nf X2 sn2)).
  - apply extract_typ_L_swap with A.
    + exact HV0W.
    + rewrite <- (nf_respects_conv X1 X2 sn1 sn2 HconvX).
      eapply subject_reduction_theorem; [exact (nf_reduces X1 sn1) | exact HX].
  - symmetry. apply extract_typ_L_swap with A'.
    + exact HV2W.
    + eapply subject_reduction_theorem; [exact (nf_reduces X2 sn2) | exact HX'].
Qed.

(** Type extraction is invariant under swapping a context binder for a reduct. *)
Lemma extract_typ_ctx_swap : forall T T', reduces_once T T' ->
  forall X D e sn1 sn2 A, has_type (D ++ T :: e) X A ->
  extract_typ (D ++ T :: e) X sn1 = extract_typ (D ++ T' :: e) X sn2.
Proof.
  intros T T' Hr X D e sn1 sn2 A HX.
  unfold extract_typ. rewrite (nf_pi X sn1 sn2).
  apply extract_typ_L_swap with A.
  - exact (one_step_reduces _ _ Hr).
  - eapply subject_reduction_theorem; [exact (nf_reduces X sn2) | exact HX ].
Qed.

(** [extract_lookup_type] is invariant under swapping a context binder for a reduct. *)
Lemma extract_lookup_type_ctx_swap : forall T T', reduces_once T T' ->
  forall D e w1 w2 v,
  well_formed (D ++ T :: e) ->
  extract_lookup_type (D ++ T :: e) w1 v = extract_lookup_type (D ++ T' :: e) w2 v.
Proof.
  intros T T' Hr.
  induction D as [|X D' IH]; intros e w1 w2 v Hwf.
  - simpl. destruct v as [|v'].
    + unfold extract_typ.
      rewrite (nf_respects_conv T T' (sn_of_binding T e w1) (sn_of_binding T' e w2)
                 (sym_convertible _ _ (one_step_convertible_expansion T T' Hr))).
      reflexivity.
    + inversion_clear Hwf.
      assert (HT' : has_type e T' (sort_term s))
        by (eapply subject_reduction; [exact H | exact Hr]).
      assert (Hlarge_iff : iffT (is_large e T) (is_large e T')).
      { split.
        - intro HL. eapply is_large_stable; [exact HL | exact Hr].
        - intro HL'. unfold is_large in *.
          assert (Heqs : s = kind)
            by (apply convertible_sort; eapply has_type_unique_sort; [exact HT' | exact HL']).
          subst. exact H. }
      destruct (is_large_dec e T); destruct (is_large_dec e T');
        try (iffT_contra Hlarge_iff).
      * f_equal. apply extract_lookup_type_pi.
      * apply extract_lookup_type_pi.
  - change ((X :: D') ++ T :: e) with (X :: D' ++ T :: e) in *.
    change ((X :: D') ++ T' :: e) with (X :: D' ++ T' :: e).
    simpl. destruct v as [|v'].
    + inversion_clear Hwf.
      eapply (extract_typ_ctx_swap T T' Hr X (D') e); exact H.
    + assert (Hwf_tail : well_formed (D' ++ T :: e)) by (eapply wf_tail; exact Hwf).
      inversion_clear Hwf.
      assert (HX_sort : has_type (D' ++ T :: e) X (sort_term s)) by exact H.
      assert (Hlarge_iff : iffT (is_large (D' ++ T :: e) X) (is_large (D' ++ T' :: e) X))
        by (eapply is_large_swap_at;
            [ exact (one_step_reduces _ _ Hr) | exact Hwf_tail | exact HX_sort ]).
      destruct (is_large_dec (D' ++ T :: e) X);
        destruct (is_large_dec (D' ++ T' :: e) X);
        try (iffT_contra Hlarge_iff).
      * f_equal. apply IH. exact Hwf_tail.
      * apply IH. exact Hwf_tail.
Qed.

(** ** [extract_typ] of a product decomposes (abs/app cases)

    Centralizes [nf_prod] + [classifier_nf_is_large] + [extract_typ_L_swap]. *)
Lemma extract_typ_prod_large : forall e T0 U s1 s2
  (HT0: has_type e T0 (sort_term s1)) (HU: has_type (T0 :: e) U (sort_term s2)) sn snT0 snU,
  is_large e T0 ->
  extract_typ e (prod T0 U) sn = syntax.all (extract_kind T0 snT0) (extract_typ (T0 :: e) U snU).
Proof.
  intros e T0 U s1 s2 HT0 HU sn snT0 snU HL.
  unfold extract_typ, extract_kind.
  rewrite (nf_prod T0 U sn snT0 snU).
  simpl (extract_typ_L _ (prod _ _)).
  assert (Hcl : classifier (nf T0 snT0) = true)
    by (apply (classifier_nf_is_large e T0 snT0 s1 HT0); exact HL).
  rewrite Hcl. f_equal.
  symmetry.
  apply (extract_typ_L_swap T0 (nf T0 snT0) (nf_reduces T0 snT0) (nf U snU) nil e (sort_term s2)).
  simpl. eapply subject_reduction_theorem; [ apply nf_reduces | exact HU ].
Qed.

(** Type extraction of a product with small domain is the target arrow of the parts' extractions. *)
Lemma extract_typ_prod_small : forall e T0 U s1 s2
  (HT0: has_type e T0 (sort_term s1)) (HU: has_type (T0 :: e) U (sort_term s2)) sn snT0 snU,
  (is_large e T0 -> False) ->
  extract_typ e (prod T0 U) sn
    = syntax.arrow (extract_typ e T0 snT0) (extract_typ (T0 :: e) U snU).
Proof.
  intros e T0 U s1 s2 HT0 HU sn snT0 snU HL.
  unfold extract_typ.
  rewrite (nf_prod T0 U sn snT0 snU).
  simpl (extract_typ_L _ (prod _ _)).
  assert (Hcl : classifier (nf T0 snT0) = false).
  { destruct (classifier (nf T0 snT0)) eqn:E; [| reflexivity].
    exfalso. apply HL. apply (classifier_nf_is_large e T0 snT0 s1 HT0). exact E. }
  rewrite Hcl. f_equal.
  symmetry.
  apply (extract_typ_L_swap T0 (nf T0 snT0) (nf_reduces T0 snT0) (nf U snU) nil e (sort_term s2)).
  simpl. eapply subject_reduction_theorem; [ apply nf_reduces | exact HU ].
Qed.

(** Type extraction of a sort is [dyn]. *)
Lemma extract_typ_sort : forall e s sn, extract_typ e (sort_term s) sn = syntax.dyn.
Proof. intros. unfold extract_typ. rewrite (nf_sort s sn). reflexivity. Qed.

(** A variable is normal. *)
Lemma normal_var : forall j, normal (terms.var j).
Proof. intros j u H. dependent destruction H. Qed.

(** Type extraction of a variable. *)
Lemma extract_typ_var : forall e j sn,
  extract_typ e (terms.var j) sn
  = if type_binding e j then syntax.tvar (type_index e j) else syntax.dyn.
Proof.
  intros. unfold extract_typ. rewrite (nf_normal_eq (terms.var j) sn (normal_var j)).
  reflexivity.
Qed.

(** Type extraction of a lambda with large domain is a type abstraction. *)
Lemma extract_typ_lam_large : forall e T M U
  (HM: has_type (T :: e) M U) s1 (HT: has_type e T (sort_term s1)) sn snT snM,
  is_large e T ->
  extract_typ e (lam T M) sn = syntax.tyabs (extract_kind T snT) (extract_typ (T :: e) M snM).
Proof.
  intros e T M U HM s1 HT sn snT snM HL.
  unfold extract_typ, extract_kind.
  rewrite (nf_lam T M sn snT snM).
  simpl (extract_typ_L _ (lam _ _)).
  assert (Hcl : classifier (nf T snT) = true)
    by (apply (classifier_nf_is_large e T snT s1 HT); exact HL).
  rewrite Hcl. f_equal.
  symmetry.
  apply (extract_typ_L_swap T (nf T snT) (nf_reduces T snT) (nf M snM) nil e U).
  simpl. eapply subject_reduction_theorem; [ apply nf_reduces | exact HM ].
Qed.

(** Type extraction of a lambda with small domain drops the binder. *)
Lemma extract_typ_lam_small : forall e T M U
  (HM: has_type (T :: e) M U) s1 (HT: has_type e T (sort_term s1)) sn snM,
  (is_large e T -> False) ->
  extract_typ e (lam T M) sn = extract_typ (T :: e) M snM.
Proof.
  intros e T M U HM s1 HT sn snM HL.
  unfold extract_typ.
  pose (snT := strong_normalization e T (sort_term s1) HT).
  rewrite (nf_lam T M sn snT snM).
  simpl (extract_typ_L _ (lam _ _)).
  assert (Hcl : classifier (nf T snT) = false).
  { destruct (classifier (nf T snT)) eqn:E; [| reflexivity].
    exfalso. apply HL. apply (classifier_nf_is_large e T snT s1 HT). exact E. }
  rewrite Hcl.
  symmetry.
  apply (extract_typ_L_swap T (nf T snT) (nf_reduces T snT) (nf M snM) nil e U).
  simpl. eapply subject_reduction_theorem; [ apply nf_reduces | exact HM ].
Qed.


(** A product with a kind codomain is a kind. *)
Lemma is_large_prod_cod : forall e T U s1,
  has_type e T (sort_term s1) -> is_large (T :: e) U -> is_large e (prod T U).
Proof.
  intros e T U s1 HT HU. unfold is_large in *.
  apply (type_prod e T s1 HT U kind HU).
Qed.

(** The codomain of a product-kind is a kind. *)
Lemma is_large_prod_cod_inv : forall e T U,
  is_large e (prod T U) -> is_large (T :: e) U.
Proof.
  intros e T U H. unfold is_large in *.
  apply (inversion_has_type_prod _ e T U (sort_term kind) H).
  intros s1 s2 HT HU Hconv.
  apply confluence.convertible_sort in Hconv. subst s2. exact HU.
Qed.

(** [type_expr] characterizes exactly the type-level source terms: a term extracts
    to a target type (rather than being erased) iff its type is a sort or a kind. *)
Lemma type_expr_iff : forall e W B (HW: has_type e W B),
  iffT (type_expr e W = true) ({s : sort & B = sort_term s} + is_large e B).
Proof.
  intros e W B HW.
  induction HW as
    [ e0 Hwf0
    | e0 Hwf0
    | e0 Hwf0 v t0 Hitem
    | e0 T0 s1 HT IHT M0 U0 s2 HU IHU HM IHM
    | e0 v0 V Hv IHv u0 Ur Hu IHu
    | e0 T0 s1 HT IHT U0 s2 HU IHU
    | e0 t0 U0 V Ht0 IHt0 Hconv s Hs IHs ].
  - split; intro; [ left; exists kind; reflexivity | reflexivity ].
  - split; intro; [ left; exists kind; reflexivity | reflexivity ].
  - (* var v : t0, item_lift t0 e0 v *)
    destruct Hitem as [u Hequ Hnth].
    simpl (type_expr e0 (terms.var v)). unfold type_binding. rewrite Hnth.
    assert (Hstar : iffT (is_large e0 (lift (S v) u)) (is_large (skipn (S v) e0) u))
      by (apply is_large_item_lift; assumption).
    split.
    + intro Htb. right. subst t0.
      destruct (is_large_dec (skipn (S v) e0) u) as [Hl|Hs]; [| discriminate].
      apply (snd Hstar). exact Hl.
    + intro HB. subst t0.
      destruct (is_large_dec (skipn (S v) e0) u) as [Hl|Hs]; [reflexivity | exfalso].
      destruct HB as [[s Hs']|Hlg].
      * assert (Hu_sort : u = sort_term s).
        { destruct u as [su | nu | uT uM | uF uA | uT uU]; simpl in Hs'; try discriminate.
          injection Hs' as ->. reflexivity. }
        subst u.
        destruct (well_formed_sort v e0 (skipn (S v) e0) eq_refl Hwf0 (sort_term s) Hnth) as [s' Hs'k].
        apply Hs. unfold is_large.
        destruct s.
        -- exfalso. exact (inversion_has_type_kind _ _ Hs'k).
        -- apply type_prop. exact (has_type_well_formed _ _ _ Hs'k).
        -- apply type_set. exact (has_type_well_formed _ _ _ Hs'k).
      * apply Hs. apply (fst Hstar). exact Hlg.
  - (* abs: W = lam T0 M0 : prod T0 U0 *)
    simpl (type_expr e0 (lam T0 M0)).
    split.
    + intro Hte. right.
      apply (is_large_prod_cod e0 T0 U0 s1 HT).
      destruct (fst IHM Hte) as [[sx Hsx]|Hl]; [| exact Hl].
      subst U0. unfold is_large. destruct sx.
      * exfalso. exact (inversion_has_type_kind _ _ HU).
      * apply type_prop. exact (has_type_well_formed _ _ _ HU).
      * apply type_set. exact (has_type_well_formed _ _ _ HU).
    + intro HB. apply (snd IHM). right.
      destruct HB as [[s Hs']|Hlg]; [discriminate |].
      apply (is_large_prod_cod_inv e0 T0 U0). exact Hlg.
  - (* app: W = app u0 v0 : subst v0 Ur *)
    simpl (type_expr e0 (terms.app u0 v0)).
    destruct (type_case _ _ _ Hu) as [[sp Hsp] | Hbad]; [| discriminate Hbad].
    apply (inversion_has_type_prod _ e0 V Ur (sort_term sp) Hsp).
    intros s1p s2p HVp HUrp Hconvp.
    apply confluence.convertible_sort in Hconvp. subst sp.
    assert (Hsub_sort : has_type e0 (subst v0 Ur) (sort_term s2p)).
    { change (sort_term s2p) with (subst v0 (sort_term s2p)).
      exact (substitution e0 V Ur (sort_term s2p) HUrp v0 Hv). }
    split.
    + intro Hte.
      destruct (fst IHu Hte) as [[sx Hsx]|Hlprod]; [discriminate |].
      right. apply (is_large_prod_cod_inv e0 V Ur) in Hlprod.
      unfold is_large.
      change (sort_term kind) with (subst v0 (sort_term kind)).
      exact (substitution e0 V Ur (sort_term kind) Hlprod v0 Hv).
    + intro HB.
      assert (Hs2k : s2p = kind).
      { destruct HB as [[s Hs']|Hlg].
        - rewrite Hs' in Hsub_sort.
          destruct s.
          + exfalso. exact (inversion_has_type_kind _ _ Hsub_sort).
          + apply confluence.convertible_sort.
            exact (inversion_has_type_prop e0 (sort_term s2p) Hsub_sort).
          + apply confluence.convertible_sort.
            exact (inversion_has_type_set e0 (sort_term s2p) Hsub_sort).
        - apply confluence.convertible_sort.
          exact (has_type_unique_sort e0 (subst v0 Ur) (sort_term s2p) Hsub_sort
                   (sort_term kind) Hlg). }
      subst s2p.
      apply (snd IHu). right.
      apply (is_large_prod_cod e0 V Ur s1p HVp). exact HUrp.
  - (* prod: W = prod T0 U0 : sort s2 *)
    simpl (type_expr e0 (prod T0 U0)).
    split; intro; [ left; exists s2; reflexivity | reflexivity ].
  - (* conv: W = t0 : V, from t0 : U0, U0 ≅ V, V : sort s *)
    assert (HU0sort : {su & has_type e0 U0 (sort_term su)} + {U0 = sort_term kind})
      by (apply (type_case e0 t0 U0 Ht0)).
    split.
    + intro Hte. right.
      assert (HlU0 : is_large e0 U0).
      { destruct (fst IHt0 Hte) as [[su Hsu]|HlU0].
        - subst U0. unfold is_large. destruct su.
          + exfalso. exact (inversion_has_type_convertible_kind e0 V (sort_term s)
                              (sym_convertible _ _ Hconv) Hs).
          + apply type_prop. exact (has_type_well_formed _ _ _ Hs).
          + apply type_set. exact (has_type_well_formed _ _ _ Hs).
        - exact HlU0. }
      exact (is_large_conv e0 U0 V s Hconv Hs HlU0).
    + intro HB. apply (snd IHt0). right.
      assert (HlV : is_large e0 V).
      { destruct HB as [[s' Hs']|HlV].
        - subst V. unfold is_large. destruct s'.
          + exfalso. exact (inversion_has_type_kind e0 (sort_term s) Hs).
          + apply type_prop. exact (has_type_well_formed _ _ _ Ht0).
          + apply type_set. exact (has_type_well_formed _ _ _ Ht0).
        - exact HlV. }
      destruct HU0sort as [[su Hsu]|Hk].
      * exact (is_large_conv e0 V U0 su (sym_convertible _ _ Hconv) Hsu HlV).
      * subst U0. exfalso.
        exact (inversion_has_type_convertible_kind e0 V (sort_term s)
                 (sym_convertible _ _ Hconv) Hs).
Qed.

(** [type_expr] is stable under normalization: reducing a term preserves the
    syntactic type-expression test because the typing class (sort vs large vs small)
    is invariant under reduction. *)
Lemma type_expr_nf : forall e t B sn,
  has_type e t B -> type_expr e (nf t sn) = type_expr e t.
Proof.
  intros e t B sn Ht.
  assert (Ht' : has_type e (nf t sn) B)
    by (eapply subject_reduction_theorem; [apply nf_reduces | exact Ht]).
  destruct (type_expr e t) eqn:Hte; destruct (type_expr e (nf t sn)) eqn:Hte';
    try reflexivity; exfalso.
  - pose proof (fst (type_expr_iff e t B Ht) Hte) as Hclass.
    rewrite (snd (type_expr_iff e (nf t sn) B Ht') Hclass) in Hte'. discriminate.
  - pose proof (fst (type_expr_iff e (nf t sn) B Ht') Hte') as Hclass.
    rewrite (snd (type_expr_iff e t B Ht) Hclass) in Hte. discriminate.
Qed.

(** Context-extraction cons case for a large (type-level) binding: a [has_kind] entry. *)
Lemma extract_ctx_cons_large : forall T e (w: well_formed (T :: e)) (w': well_formed e) snT,
  is_large e T ->
  extract_ctx (T :: e) w
    = typing.has_kind (extract_kind T snT) :: extract_ctx e w'.
Proof.
  intros T e w w' snT HL. simpl. destruct (is_large_dec e T) as [Hd|Hd].
  - f_equal; [ f_equal; apply extract_kind_pi | apply extract_ctx_pi ].
  - exfalso. apply Hd. exact HL.
Qed.

(** Context-extraction cons case for a small (term-level) binding: a [has_type] entry. *)
Lemma extract_ctx_cons_small : forall T e (w: well_formed (T :: e)) (w': well_formed e) snT,
  (is_large e T -> False) ->
  extract_ctx (T :: e) w
    = typing.has_type (extract_typ e T snT) :: extract_ctx e w'.
Proof.
  intros T e w w' snT HL. simpl. destruct (is_large_dec e T) as [Hd|Hd].
  - exfalso. apply HL. exact Hd.
  - f_equal; [ f_equal; apply extract_typ_pi | apply extract_ctx_pi ].
Qed.
