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


Lemma subst_coerce : forall p k s A B,
  infrastructure.subst p k (coerce s A B) =
  coerce (infrastructure.subst p k s) A B.
Proof.
  intros p k s A B. unfold coerce.
  destruct (syntax.typ_eq_dec A B); [reflexivity |].
  destruct (infrastructure.compat_dec A B); simpl; reflexivity.
Qed.

(** Target term-substitution push-through equalities (all definitional). *)
Lemma subst_abs_t : forall p k A s,
  infrastructure.subst p k (syntax.abs A s) = syntax.abs A (infrastructure.subst p (S k) s).
Proof. reflexivity. Qed.

Lemma subst_app_t : forall p k s t,
  infrastructure.subst p k (syntax.app s t)
  = syntax.app (infrastructure.subst p k s) (infrastructure.subst p k t).
Proof. reflexivity. Qed.

Lemma subst_tabs_t : forall p k K s,
  infrastructure.subst p k (syntax.tabs K s)
  = syntax.tabs K (infrastructure.subst (infrastructure.term_tlift 1 0 p) k s).
Proof. reflexivity. Qed.

Lemma subst_tapp_t : forall p k s A,
  infrastructure.subst p k (syntax.tapp s A) = syntax.tapp (infrastructure.subst p k s) A.
Proof. reflexivity. Qed.

Lemma subst_blame_t : forall p k q,
  infrastructure.subst p k (syntax.blame q) = syntax.blame q.
Proof. reflexivity. Qed.

Lemma subst_var_t : forall p k n,
  infrastructure.subst p k (syntax.var n)
  = match lt_eq_lt_dec k n with
    | inleft (left _) => syntax.var (pred n)
    | inleft (right _) => infrastructure.lift k 0 p
    | inright _ => syntax.var n
    end.
Proof. reflexivity. Qed.

(** Two type-lifts at the same cutoff compose additively. *)
Lemma term_tlift_compose : forall t a b k,
  infrastructure.term_tlift a k (infrastructure.term_tlift b k t) =
  infrastructure.term_tlift (a + b) k t.
Proof.
  induction t; intros a b k; simpl; f_equal; auto;
    try apply infrastructure.tlift_tlift.
Qed.

(** A large well-sorted type has sort [kind]. *)
Lemma is_large_sort_eq : forall e T s,
  has_type e T (sort_term s) -> is_large e T -> s = kind.
Proof.
  intros e T s HT Hl. unfold is_large in Hl.
  assert (Hconv : convertible (sort_term s) (sort_term kind)).
  { apply (has_type_unique_sort e T); [exact (HT) | exact Hl]. }
  exact (confluence.convertible_sort _ _ Hconv).
Qed.

(** Substituting a variable reflects largeness (Prop-hypothesis form). *)
Lemma is_large_substitute_inv_prop : forall g v V (Hv: has_type g v V)
  e T (HT: { s & has_type e T (sort_term s) })
  f n (Hse: substitute_in_environment v V n e f) (wff: well_formed f)
  (Hskip: skipn n f = g),
  is_large f (terms.subst_rec v T n) -> is_large e T.
Proof.
  intros g v V Hv e T [s HT] f n Hse wff Hskip Hlarge. unfold is_large in *.
  pose proof (has_type_substitute_weakening g v V (Hv)
                e T (sort_term s) HT f n Hse (wff) Hskip) as HT_sub.
  change (terms.subst_rec v (sort_term s) n) with (sort_term s) in HT_sub.
  assert (Hconv : convertible (sort_term kind) (sort_term s)).
  { apply (has_type_unique_sort f (terms.subst_rec v T n));
    [exact Hlarge | exact HT_sub]. }
  apply confluence.convertible_sort in Hconv. subst s.
  exact HT.
Qed.

(** Substituting a variable reflects largeness of a type. *)
Lemma is_large_substitute_inv : forall g v V (Hv: has_type g v V)
  e T s (HT: has_type e T (sort_term s))
  f n (Hse: substitute_in_environment v V n e f) (wff: well_formed f)
  (Hskip: skipn n f = g),
  is_large f (terms.subst_rec v T n) -> is_large e T.
Proof.
  intros g v V Hv e T s HT f n Hse wff Hskip Hlarge. unfold is_large in *.
  pose proof (has_type_substitute_weakening_t g v V Hv e T (sort_term s) HT f n Hse wff Hskip) as HT_sub.
  assert (Hconv : convertible (sort_term kind) (sort_term s)).
  { apply (has_type_unique_sort f (terms.subst_rec v T n));
    [exact Hlarge | exact (HT_sub)]. }
  apply confluence.convertible_sort in Hconv. subst s.
  exact (HT).
Qed.

(** [skipn (S n)] of the source context equals [skipn n] of the substituted one. *)
Lemma skipn_succ_substitute : forall v V n e f,
  substitute_in_environment v V n e f ->
  skipn (S n) e = skipn n f.
Proof.
  intros v V n e f Hse. induction Hse.
  - reflexivity.
  - simpl. exact IHHse.
Qed.

(** Transport an [item_lift] above the substitution point through a substitution. *)
Lemma item_lift_substitute_above : forall v V n e f,
  substitute_in_environment v V n e f ->
  forall v0 t0, n < v0 -> item_lift t0 e v0 ->
  item_lift (terms.subst_rec v t0 n) f (Nat.pred v0).
Proof.
  intros v V n e f Hse v0 t0 Hlt [u0 Heq Hnth].
  exists u0.
  - rewrite Heq. rewrite simplify_subst by lia.
    f_equal. lia.
  - apply (nth_substitute_above v V n e f Hse (Nat.pred v0) ltac:(lia)).
    replace (S (Nat.pred v0)) with v0 by lia. exact Hnth.
Qed.

(** Transport an [item_lift] below the substitution point through a substitution. *)
Lemma item_lift_substitute_below : forall v V n e f,
  substitute_in_environment v V n e f ->
  forall v0 t0, n > v0 -> item_lift t0 e v0 ->
  item_lift (terms.subst_rec v t0 n) f v0.
Proof.
  intros v V n e f Hse v0 t0 Hgt il.
  exact (nth_substitute_below v V n e f Hse v0 Hgt _ il).
Qed.

(** One-step unfolding of [term_index] past a large head binder (index unchanged). *)
Lemma term_index_succ_large : forall T e n,
  is_large e T -> term_index (T :: e) (S n) = term_index e n.
Proof.
  intros T e n Hl. simpl. destruct (is_large_dec e T); [reflexivity | contradiction].
Qed.

(** One-step unfolding of [term_index] past a small head binder (index incremented). *)
Lemma term_index_succ_small : forall T e n,
  (is_large e T -> False) -> term_index (T :: e) (S n) = S (term_index e n).
Proof.
  intros T e n Hs. simpl. destruct (is_large_dec e T); [contradiction | reflexivity].
Qed.

(** [term_index] is monotone in its index argument. *)
Lemma term_index_mono : forall e v0 n,
  v0 <= n -> term_index e v0 <= term_index e n.
Proof.
  induction e as [| T e' IH]; intros v0 n Hle.
  - simpl. lia.
  - destruct v0 as [| v0']; [simpl; lia |].
    destruct n as [| n']; [lia |].
    simpl. destruct (is_large_dec e' T).
    + apply IH. lia.
    + apply le_n_S. apply IH. lia.
Qed.

(** Below the substitution point, [term_index] is unchanged by a substitution. *)
Lemma term_index_substitute_below :
  forall g v V (Hv: has_type g v V) (wfg: well_formed g),
  forall n e f,
  substitute_in_environment v V n e f ->
  well_formed e -> well_formed f ->
  skipn n f = g ->
  forall v0, v0 < n -> term_index f v0 = term_index e v0.
Proof.
  intros g v V Hv wfg n e f Hse.
  induction Hse as [| e0 f0 n' T Hse' IH]; intros wfe wff Hskip v0 Hlt.
  - lia.
  - destruct v0 as [| v0']; [reflexivity |].
    simpl (term_index (T :: e0) (S v0')).
    simpl (term_index (terms.subst_rec v T n' :: f0) (S v0')).
    dependent destruction wfe. rename h into HT_sort.
    dependent destruction wff. rename h into HT_sort_f.
    simpl in Hskip.
    assert (IH' : term_index f0 v0' = term_index e0 v0')
      by (apply IH; [exact (has_type_t_well_formed_t _ _ _ HT_sort)
                     | exact (has_type_t_well_formed_t _ _ _ HT_sort_f)
                     | exact Hskip | lia]).
    destruct (is_large_dec e0 T) as [Hlarge | Hsmall];
      destruct (is_large_dec f0 (terms.subst_rec v T n')) as [Hlarge_f | Hsmall_f].
    + exact IH'.
    + exfalso. apply Hsmall_f.
      apply (has_type_substitute_weakening g v V (Hv)
               e0 T (sort_term kind) Hlarge f0 n' Hse'
               ((has_type_t_well_formed_t _ _ _ HT_sort_f)) Hskip).
    + exfalso. apply Hsmall.
      exact (is_large_substitute_inv g v V Hv e0 T s HT_sort f0 n' Hse'
               (has_type_t_well_formed_t _ _ _ HT_sort_f) Hskip Hlarge_f).
    + f_equal. exact IH'.
Qed.

(** At the substitution point, [term_index] agrees between source and substituted contexts. *)
Lemma term_index_substitute_top :
  forall g v V (Hv: has_type g v V),
  forall n e f,
  substitute_in_environment v V n e f ->
  well_formed e -> well_formed f ->
  skipn n f = g ->
  term_index f n = term_index e n.
Proof.
  intros g v V Hv n e f Hse.
  induction Hse as [e_z | e0 f0 n' T Hse' IH]; intros wfe wff Hskip.
  - destruct e_z; reflexivity.
  - simpl (term_index (T :: e0) (S n')).
    simpl (term_index (terms.subst_rec v T n' :: f0) (S n')).
    dependent destruction wfe. rename h into HT_sort.
    dependent destruction wff. rename h into HT_sort_f.
    simpl in Hskip.
    assert (IH' : term_index f0 n' = term_index e0 n')
      by (apply IH; [exact (has_type_t_well_formed_t _ _ _ HT_sort)
                     | exact (has_type_t_well_formed_t _ _ _ HT_sort_f) | exact Hskip]).
    destruct (is_large_dec e0 T) as [Hlarge | Hsmall];
      destruct (is_large_dec f0 (terms.subst_rec v T n')) as [Hlarge_f | Hsmall_f].
    + exact IH'.
    + exfalso. apply Hsmall_f.
      apply (has_type_substitute_weakening g v V (Hv)
               e0 T (sort_term kind) Hlarge f0 n' Hse'
               ((has_type_t_well_formed_t _ _ _ HT_sort_f)) Hskip).
    + exfalso. apply Hsmall.
      exact (is_large_substitute_inv g v V Hv e0 T s HT_sort f0 n' Hse'
               (has_type_t_well_formed_t _ _ _ HT_sort_f) Hskip Hlarge_f).
    + f_equal. exact IH'.
Qed.


(** Largeness is invariant under insertion (weakening) of a binder. *)
Lemma is_large_insert : forall A n e f,
  insert_in_environment A n e f -> well_formed f ->
  forall T s, has_type e T (sort_term s) ->
  iffT (is_large e T) (is_large f (lift_rec 1 T n)).
Proof.
  intros A n e f Hins wff T s HT. unfold is_large. split.
  - intro HL.
    pose proof (has_type_weakening_weak A e T (sort_term kind) HL n f Hins wff) as HW.
    simpl in HW. exact HW.
  - intro HL.
    pose proof (has_type_weakening_weak A e T (sort_term s) HT n f Hins wff) as HW.
    simpl in HW.
    assert (Hconv : convertible (sort_term s) (sort_term kind))
      by (exact (has_type_unique_sort f (lift_rec 1 T n) (sort_term s) HW (sort_term kind) HL)).
    apply convertible_sort in Hconv. subst s. exact HT.
Qed.

(** Below an inserted binder, [term_index] is unchanged. *)
Lemma term_index_insert_lt : forall A n e f,
  insert_in_environment A n e f -> well_formed e -> well_formed f ->
  forall k, k < n -> term_index f k = term_index e k.
Proof.
  intros A n e f Hins. induction Hins as [e0 | n' e0 f0 t Hins' IH].
  - intros wfe wff k Hk. lia.
  - intros wfe wff k Hk.
    destruct k as [| k']; [reflexivity |].
    simpl (term_index (lift_rec 1 t n' :: f0) (S k')).
    simpl (term_index (t :: e0) (S k')).
    inversion_clear wfe as [| ? ? se Hte]. rename Hte into Ht_e.
    inversion_clear wff as [| ? ? sf Htf]. rename Htf into Ht_f.
    assert (wfe0 : well_formed e0) by (apply has_type_well_formed with t (sort_term se); exact Ht_e).
    assert (wff0 : well_formed f0) by (apply has_type_well_formed with (lift_rec 1 t n') (sort_term sf); exact Ht_f).
    assert (Hagree : iffT (is_large e0 t) (is_large f0 (lift_rec 1 t n')))
      by (exact (is_large_insert A n' e0 f0 Hins' wff0 t se Ht_e)).
    destruct (is_large_dec e0 t) as [Hl | Hs];
      destruct (is_large_dec f0 (lift_rec 1 t n')) as [Hlf | Hsf].
    + apply IH; [exact wfe0 | exact wff0 | lia].
    + exfalso. apply Hsf. apply (fst Hagree). exact Hl.
    + exfalso. apply Hs. apply (snd Hagree). exact Hlf.
    + f_equal. apply IH; [exact wfe0 | exact wff0 | lia].
Qed.

(** Above a large inserted binder, [term_index] is unchanged. *)
Lemma term_index_insert_ge_large : forall A n e f,
  insert_in_environment A n e f -> well_formed e -> well_formed f ->
  is_large (skipn n e) A ->
  forall k, n <= k -> term_index f (S k) = term_index e k.
Proof.
  intros A n e f Hins. induction Hins as [e0 | n' e0 f0 t Hins' IH].
  - intros wfe wff HlA k Hk.
    simpl (skipn 0 e0) in HlA.
    simpl (term_index (A :: e0) (S k)).
    destruct (is_large_dec e0 A) as [_ | Hns]; [reflexivity | contradiction].
  - intros wfe wff HlA k Hk.
    destruct k as [| k']; [lia |].
    simpl (term_index (lift_rec 1 t n' :: f0) (S (S k'))).
    simpl (term_index (t :: e0) (S k')).
    simpl (skipn (S n') (t :: e0)) in HlA.
    inversion_clear wfe as [| ? ? se Hte]. rename Hte into Ht_e.
    inversion_clear wff as [| ? ? sf Htf]. rename Htf into Ht_f.
    assert (wfe0 : well_formed e0) by (apply has_type_well_formed with t (sort_term se); exact Ht_e).
    assert (wff0 : well_formed f0) by (apply has_type_well_formed with (lift_rec 1 t n') (sort_term sf); exact Ht_f).
    assert (Hagree : iffT (is_large e0 t) (is_large f0 (lift_rec 1 t n')))
      by (exact (is_large_insert A n' e0 f0 Hins' wff0 t se Ht_e)).
    destruct (is_large_dec e0 t) as [Hl | Hs];
      destruct (is_large_dec f0 (lift_rec 1 t n')) as [Hlf | Hsf].
    + apply IH; [exact wfe0 | exact wff0 | assumption | lia].
    + exfalso. apply Hsf. apply (fst Hagree). exact Hl.
    + exfalso. apply Hs. apply (snd Hagree). exact Hlf.
    + f_equal. apply IH; [exact wfe0 | exact wff0 | assumption | lia].
Qed.

(** Above a small inserted binder, [term_index] increments by one. *)
Lemma term_index_insert_ge_small : forall A n e f,
  insert_in_environment A n e f -> well_formed e -> well_formed f ->
  (is_large (skipn n e) A -> False) ->
  forall k, n <= k -> term_index f (S k) = S (term_index e k).
Proof.
  intros A n e f Hins. induction Hins as [e0 | n' e0 f0 t Hins' IH].
  - intros wfe wff HnlA k Hk.
    simpl (skipn 0 e0) in HnlA.
    simpl (term_index (A :: e0) (S k)).
    destruct (is_large_dec e0 A) as [Hl | _]; [contradiction | reflexivity].
  - intros wfe wff HnlA k Hk.
    destruct k as [| k']; [lia |].
    simpl (term_index (lift_rec 1 t n' :: f0) (S (S k'))).
    simpl (term_index (t :: e0) (S k')).
    simpl (skipn (S n') (t :: e0)) in HnlA.
    inversion_clear wfe as [| ? ? se Hte]. rename Hte into Ht_e.
    inversion_clear wff as [| ? ? sf Htf]. rename Htf into Ht_f.
    assert (wfe0 : well_formed e0) by (apply has_type_well_formed with t (sort_term se); exact Ht_e).
    assert (wff0 : well_formed f0) by (apply has_type_well_formed with (lift_rec 1 t n') (sort_term sf); exact Ht_f).
    assert (Hagree : iffT (is_large e0 t) (is_large f0 (lift_rec 1 t n')))
      by (exact (is_large_insert A n' e0 f0 Hins' wff0 t se Ht_e)).
    destruct (is_large_dec e0 t) as [Hl | Hs];
      destruct (is_large_dec f0 (lift_rec 1 t n')) as [Hlf | Hsf].
    + apply IH; [exact wfe0 | exact wff0 | assumption | lia].
    + exfalso. apply Hsf. apply (fst Hagree). exact Hl.
    + exfalso. apply Hs. apply (snd Hagree). exact Hlf.
    + f_equal. apply IH; [exact wfe0 | exact wff0 | assumption | lia].
Qed.

(** Below an inserted binder, [type_binding] is unchanged. *)
Lemma type_binding_insert_lt : forall A n e f,
  insert_in_environment A n e f -> well_formed e -> well_formed f ->
  forall k, k < n -> type_binding f k = type_binding e k.
Proof.
  intros A n e f Hins. induction Hins as [e0 | n' e0 f0 t Hins' IH].
  - intros wfe wff k Hk. lia.
  - intros wfe wff k Hk.
    destruct k as [| k'].
    + unfold type_binding; simpl.
      inversion_clear wfe as [| ? ? se Hte]. rename Hte into Ht_e.
      inversion_clear wff as [| ? ? sf Htf]. rename Htf into Ht_f.
      assert (wfe0 : well_formed e0) by (apply has_type_well_formed with t (sort_term se); exact Ht_e).
      assert (wff0 : well_formed f0) by (apply has_type_well_formed with (lift_rec 1 t n') (sort_term sf); exact Ht_f).
      assert (Hagree : iffT (is_large e0 t) (is_large f0 (lift_rec 1 t n')))
        by (exact (is_large_insert A n' e0 f0 Hins' wff0 t se Ht_e)).
      destruct (is_large_dec e0 t) as [Hl | Hs];
        destruct (is_large_dec f0 (lift_rec 1 t n')) as [Hlf | Hsf];
        try reflexivity.
      * exfalso. apply Hsf. apply (fst Hagree). exact Hl.
      * exfalso. apply Hs. apply (snd Hagree). exact Hlf.
    + simpl (type_binding (lift_rec 1 t n' :: f0) (S k')).
      simpl (type_binding (t :: e0) (S k')).
      inversion_clear wfe as [| ? ? se Hte]. rename Hte into Ht_e.
      inversion_clear wff as [| ? ? sf Htf]. rename Htf into Ht_f.
      assert (wfe0 : well_formed e0) by (apply has_type_well_formed with t (sort_term se); exact Ht_e).
      assert (wff0 : well_formed f0) by (apply has_type_well_formed with (lift_rec 1 t n') (sort_term sf); exact Ht_f).
      apply IH; [exact wfe0 | exact wff0 | lia].
Qed.

(** Above an inserted binder, [type_binding] lands one deeper. *)
Lemma type_binding_insert_ge : forall A n e f,
  insert_in_environment A n e f -> well_formed e -> well_formed f ->
  forall k, n <= k -> type_binding f (S k) = type_binding e k.
Proof.
  intros A n e f Hins. induction Hins as [e0 | n' e0 f0 t Hins' IH].
  - intros wfe wff k Hk.
    simpl (type_binding (A :: e0) (S k)). reflexivity.
  - intros wfe wff k Hk.
    destruct k as [| k']; [lia |].
    simpl (type_binding (lift_rec 1 t n' :: f0) (S (S k'))).
    simpl (type_binding (t :: e0) (S k')).
    inversion_clear wfe as [| ? ? se Hte]. rename Hte into Ht_e.
    inversion_clear wff as [| ? ? sf Htf]. rename Htf into Ht_f.
    assert (wfe0 : well_formed e0) by (apply has_type_well_formed with t (sort_term se); exact Ht_e).
    assert (wff0 : well_formed f0) by (apply has_type_well_formed with (lift_rec 1 t n') (sort_term sf); exact Ht_f).
    apply IH; [exact wfe0 | exact wff0 | lia].
Qed.

(** Below an inserted binder, [type_index] is unchanged. *)
Lemma type_index_insert_lt : forall A n e f,
  insert_in_environment A n e f -> well_formed e -> well_formed f ->
  forall k, k < n -> type_index f k = type_index e k.
Proof.
  intros A n e f Hins. induction Hins as [e0 | n' e0 f0 t Hins' IH].
  - intros wfe wff k Hk. lia.
  - intros wfe wff k Hk.
    destruct k as [| k']; [reflexivity |].
    simpl (type_index (lift_rec 1 t n' :: f0) (S k')).
    simpl (type_index (t :: e0) (S k')).
    inversion_clear wfe as [| ? ? se Hte]. rename Hte into Ht_e.
    inversion_clear wff as [| ? ? sf Htf]. rename Htf into Ht_f.
    assert (wfe0 : well_formed e0) by (apply has_type_well_formed with t (sort_term se); exact Ht_e).
    assert (wff0 : well_formed f0) by (apply has_type_well_formed with (lift_rec 1 t n') (sort_term sf); exact Ht_f).
    assert (Hagree : iffT (is_large e0 t) (is_large f0 (lift_rec 1 t n')))
      by (exact (is_large_insert A n' e0 f0 Hins' wff0 t se Ht_e)).
    destruct (is_large_dec e0 t) as [Hl | Hs];
      destruct (is_large_dec f0 (lift_rec 1 t n')) as [Hlf | Hsf].
    + f_equal. apply IH; [exact wfe0 | exact wff0 | lia].
    + exfalso. apply Hsf. apply (fst Hagree). exact Hl.
    + exfalso. apply Hs. apply (snd Hagree). exact Hlf.
    + apply IH; [exact wfe0 | exact wff0 | lia].
Qed.

(** Above a large inserted binder, [type_index] increments by one. *)
Lemma type_index_insert_ge_large : forall A n e f,
  insert_in_environment A n e f -> well_formed e -> well_formed f ->
  is_large (skipn n e) A ->
  forall k, n <= k -> type_index f (S k) = S (type_index e k).
Proof.
  intros A n e f Hins. induction Hins as [e0 | n' e0 f0 t Hins' IH].
  - intros wfe wff HlA k Hk.
    simpl (skipn 0 e0) in HlA.
    simpl (type_index (A :: e0) (S k)).
    destruct (is_large_dec e0 A) as [_ | Hns]; [reflexivity | contradiction].
  - intros wfe wff HlA k Hk.
    destruct k as [| k']; [lia |].
    simpl (type_index (lift_rec 1 t n' :: f0) (S (S k'))).
    simpl (type_index (t :: e0) (S k')).
    simpl (skipn (S n') (t :: e0)) in HlA.
    inversion_clear wfe as [| ? ? se Hte]. rename Hte into Ht_e.
    inversion_clear wff as [| ? ? sf Htf]. rename Htf into Ht_f.
    assert (wfe0 : well_formed e0) by (apply has_type_well_formed with t (sort_term se); exact Ht_e).
    assert (wff0 : well_formed f0) by (apply has_type_well_formed with (lift_rec 1 t n') (sort_term sf); exact Ht_f).
    assert (Hagree : iffT (is_large e0 t) (is_large f0 (lift_rec 1 t n')))
      by (exact (is_large_insert A n' e0 f0 Hins' wff0 t se Ht_e)).
    destruct (is_large_dec e0 t) as [Hl | Hs];
      destruct (is_large_dec f0 (lift_rec 1 t n')) as [Hlf | Hsf].
    + f_equal. apply IH; [exact wfe0 | exact wff0 | assumption | lia].
    + exfalso. apply Hsf. apply (fst Hagree). exact Hl.
    + exfalso. apply Hs. apply (snd Hagree). exact Hlf.
    + apply IH; [exact wfe0 | exact wff0 | assumption | lia].
Qed.

(** Above a small inserted binder, [type_index] is unchanged. *)
Lemma type_index_insert_ge_small : forall A n e f,
  insert_in_environment A n e f -> well_formed e -> well_formed f ->
  (is_large (skipn n e) A -> False) ->
  forall k, n <= k -> type_index f (S k) = type_index e k.
Proof.
  intros A n e f Hins. induction Hins as [e0 | n' e0 f0 t Hins' IH].
  - intros wfe wff HnlA k Hk.
    simpl (skipn 0 e0) in HnlA.
    simpl (type_index (A :: e0) (S k)).
    destruct (is_large_dec e0 A) as [Hl | _]; [contradiction | reflexivity].
  - intros wfe wff HnlA k Hk.
    destruct k as [| k']; [lia |].
    simpl (type_index (lift_rec 1 t n' :: f0) (S (S k'))).
    simpl (type_index (t :: e0) (S k')).
    simpl (skipn (S n') (t :: e0)) in HnlA.
    inversion_clear wfe as [| ? ? se Hte]. rename Hte into Ht_e.
    inversion_clear wff as [| ? ? sf Htf]. rename Htf into Ht_f.
    assert (wfe0 : well_formed e0) by (apply has_type_well_formed with t (sort_term se); exact Ht_e).
    assert (wff0 : well_formed f0) by (apply has_type_well_formed with (lift_rec 1 t n') (sort_term sf); exact Ht_f).
    assert (Hagree : iffT (is_large e0 t) (is_large f0 (lift_rec 1 t n')))
      by (exact (is_large_insert A n' e0 f0 Hins' wff0 t se Ht_e)).
    destruct (is_large_dec e0 t) as [Hl | Hs];
      destruct (is_large_dec f0 (lift_rec 1 t n')) as [Hlf | Hsf].
    + f_equal. apply IH; [exact wfe0 | exact wff0 | assumption | lia].
    + exfalso. apply Hsf. apply (fst Hagree). exact Hl.
    + exfalso. apply Hs. apply (snd Hagree). exact Hlf.
    + apply IH; [exact wfe0 | exact wff0 | assumption | lia].
Qed.

(** [classifier] is purely syntactic (no context lookups), so it is trivially
    invariant under lifting. *)
Lemma classifier_lift : forall T n k, classifier (lift_rec n T k) = classifier T.
Proof.
  induction T as [s | v | T1 IHT1 T2 IHT2 | T1 IHT1 T2 IHT2 | T1 IHT1 T2 IHT2];
    intros n k; simpl; try destruct (le_gt_dec k v); simpl; auto.
Qed.

(** [extract_kind_L] is purely syntactic, so it too is invariant under lifting. *)
Lemma extract_kind_L_lift : forall T n k, extract_kind_L (lift_rec n T k) = extract_kind_L T.
Proof.
  induction T as [s | v | T1 IHT1 T2 IHT2 | T1 IHT1 T2 IHT2 | T1 IHT1 T2 IHT2];
    intros n k; simpl; try destruct (le_gt_dec k v); simpl; auto.
  rewrite classifier_lift. destruct (classifier T1); [f_equal|]; auto.
Qed.


(** [type_expr] is invariant under weakening: inserting a fresh binder and
    correspondingly lifting the argument leaves the type-level classification
    of a well-typed term unchanged. *)
Lemma type_expr_weaken : forall X, forall A p ctx f B, insert_in_environment A p ctx f ->
  has_type ctx X B -> well_formed f ->
  type_expr f (lift_rec 1 X p) = type_expr ctx X.
Proof.
  induction X as [s0 | n | X1 IHX1 X2 IHX2 | X1 IHX1 X2 IHX2 | X1 IHX1 X2 IHX2];
    intros A p ctx f B Hins HX wff; simpl.
  - reflexivity.
  - assert (wfctx : well_formed ctx) by (apply has_type_well_formed with (var n) B; exact HX).
    destruct (le_gt_dec p n) as [Hle | Hgt].
    + exact (type_binding_insert_ge A p ctx f Hins wfctx wff n Hle).
    + exact (type_binding_insert_lt A p ctx f Hins wfctx wff n Hgt).
  - (* lam X1 X2 *)
    apply (inversion_has_type_abs
             (type_expr (lift_rec 1 X1 p :: f) (lift_rec 1 X2 (S p)) = type_expr (X1 :: ctx) X2)
             ctx X1 X2 B HX).
    intros s1 s2 T'' HA HM HT'' Hconv.
    assert (wff' : well_formed (lift_rec 1 X1 p :: f))
      by (apply wf_var with s1;
          change (sort_term s1) with (lift_rec 1 (sort_term s1) p);
          exact (has_type_weakening_weak A ctx X1 (sort_term s1) HA p f Hins wff)).
    exact (IHX2 A (S p) (X1 :: ctx) (lift_rec 1 X1 p :: f) T'' (ins_succ A p ctx f X1 Hins) HM wff').
  - (* app X1 X2 *)
    apply (inversion_has_type_app
             (type_expr f (lift_rec 1 X1 p) = type_expr ctx X1)
             ctx X1 X2 B HX).
    intros V Ur Hu Hv Hconv.
    exact (IHX1 A p ctx f (prod V Ur) Hins Hu wff).
  - reflexivity.
Qed.


(** [extract_typ_L] is invariant under weakening (inserting a fresh binder and
    correspondingly lifting the argument), up to a single type-level [tlift] at
    the point where the inserted binder introduces a new target type
    quantifier.  This is the extraction-weakening fact needed to relate
    [extract_lookup_type] (context lookup) to [extract_typ] on an
    [item_lift]-derived type, and to weaken a whole extracted term by one
    binder. *)
Lemma type_index_mono : forall e p n, p <= n -> type_index e p <= type_index e n.
Proof.
  induction e as [| T e' IH]; intros p n Hpn; [simpl; lia |].
  destruct p as [| p']; destruct n as [| n']; try lia.
  - simpl. apply Nat.le_0_l.
  - simpl. destruct (is_large_dec e' T) as [Hl | Hs].
    + apply le_n_S. apply IH. lia.
    + apply IH. lia.
Qed.

Lemma type_index_zero : forall e, type_index e 0 = 0.
Proof. intros [| ? ?]; reflexivity. Qed.

Lemma type_index_succ : forall e n,
  type_index e (S n) = if type_binding e n then S (type_index e n) else type_index e n.
Proof.
  induction e as [| T e' IH]; intros n.
  - simpl. destruct n; reflexivity.
  - destruct n as [| n'].
    + simpl (type_index (T :: e') 1). rewrite type_index_zero.
      unfold type_binding; simpl. destruct (is_large_dec e' T); reflexivity.
    + simpl (type_index (T :: e') (S (S n'))).
      simpl (type_index (T :: e') (S n')).
      change (type_binding (T :: e') (S n')) with (type_binding e' n').
      rewrite IH.
      destruct (is_large_dec e' T); destruct (type_binding e' n'); reflexivity.
Qed.

Lemma type_index_gt_of_type_binding : forall e n p,
  n < p -> type_binding e n = true -> type_index e p > type_index e n.
Proof.
  intros e n p Hnp Htb.
  assert (Hsucc : type_index e (S n) = S (type_index e n)).
  { rewrite type_index_succ. rewrite Htb. reflexivity. }
  assert (Hmono : type_index e (S n) <= type_index e p) by (apply type_index_mono; lia).
  lia.
Qed.

(** Below the substitution point, [type_binding] is unchanged by a substitution. *)
Lemma type_binding_substitute_below :
  forall g v V (Hv: has_type g v V) (wfg: well_formed g),
  forall n e f, substitute_in_environment v V n e f ->
  well_formed e -> well_formed f -> skipn n f = g ->
  forall v0, v0 < n -> type_binding f v0 = type_binding e v0.
Proof.
  intros g v V Hv wfg n e f Hse.
  induction Hse as [| e0 f0 n' T Hse' IH]; intros wfe wff Hskip v0 Hlt.
  - lia.
  - dependent destruction wfe. rename h into HT_sort.
    dependent destruction wff. rename h into HT_sort_f.
    simpl in Hskip.
    destruct v0 as [| v0'].
    + unfold type_binding; simpl.
      destruct (is_large_dec e0 T) as [Hl|Hs];
        destruct (is_large_dec f0 (terms.subst_rec v T n')) as [Hlf|Hsf]; try reflexivity.
      * exfalso. apply Hsf.
        exact (has_type_substitute_weakening g v V Hv e0 T (sort_term kind) Hl f0 n' Hse'
                 (has_type_t_well_formed_t _ _ _ HT_sort_f) Hskip).
      * exfalso. apply Hs.
        exact (is_large_substitute_inv g v V Hv e0 T s HT_sort f0 n' Hse'
                 (has_type_t_well_formed_t _ _ _ HT_sort_f) Hskip Hlf).
    + change (type_binding (T :: e0) (S v0')) with (type_binding e0 v0').
      change (type_binding (terms.subst_rec v T n' :: f0) (S v0')) with (type_binding f0 v0').
      apply IH; [ exact (has_type_t_well_formed_t _ _ _ HT_sort)
                | exact (has_type_t_well_formed_t _ _ _ HT_sort_f) | exact Hskip | lia ].
Qed.

(** Above the substitution point, [type_binding] lands one shallower. *)
Lemma type_binding_substitute_above :
  forall g v V (Hv: has_type g v V) (wfg: well_formed g),
  forall n e f, substitute_in_environment v V n e f ->
  well_formed e -> well_formed f -> skipn n f = g ->
  forall v0, n < v0 -> type_binding f (Nat.pred v0) = type_binding e v0.
Proof.
  intros g v V Hv wfg n e f Hse.
  induction Hse as [e_z | e0 f0 n' T Hse' IH]; intros wfe wff Hskip v0 Hlt.
  - destruct v0 as [|v0']; [lia|]. simpl (Nat.pred (S v0')).
    unfold type_binding; simpl. reflexivity.
  - destruct v0 as [|v0']; [lia|]. simpl (Nat.pred (S v0')).
    dependent destruction wfe. rename h into HT_sort.
    dependent destruction wff. rename h into HT_sort_f.
    simpl in Hskip.
    destruct v0' as [|v0'']; [lia|].
    change (type_binding (T :: e0) (S (S v0''))) with (type_binding e0 (S v0'')).
    simpl (Nat.pred (S v0'')) in IH.
    change (type_binding (terms.subst_rec v T n' :: f0) (S v0'')) with (type_binding f0 v0'').
    exact (IH (has_type_t_well_formed_t _ _ _ HT_sort)
             (has_type_t_well_formed_t _ _ _ HT_sort_f) Hskip (S v0'') ltac:(lia)).
Qed.

(** Below the substitution point, [type_index] is unchanged. *)
Lemma type_index_substitute_below :
  forall g v V (Hv: has_type g v V) (wfg: well_formed g),
  forall n e f, substitute_in_environment v V n e f ->
  well_formed e -> well_formed f -> skipn n f = g ->
  forall v0, v0 < n -> type_index f v0 = type_index e v0.
Proof.
  intros g v V Hv wfg n e f Hse.
  induction Hse as [| e0 f0 n' T Hse' IH]; intros wfe wff Hskip v0 Hlt.
  - lia.
  - destruct v0 as [| v0']; [reflexivity |].
    simpl (type_index (T :: e0) (S v0')).
    simpl (type_index (terms.subst_rec v T n' :: f0) (S v0')).
    dependent destruction wfe. rename h into HT_sort.
    dependent destruction wff. rename h into HT_sort_f.
    simpl in Hskip.
    assert (IH' : type_index f0 v0' = type_index e0 v0')
      by (apply IH; [ exact (has_type_t_well_formed_t _ _ _ HT_sort)
                    | exact (has_type_t_well_formed_t _ _ _ HT_sort_f) | exact Hskip | lia ]).
    destruct (is_large_dec e0 T) as [Hl|Hs];
      destruct (is_large_dec f0 (terms.subst_rec v T n')) as [Hlf|Hsf].
    + f_equal. exact IH'.
    + exfalso. apply Hsf.
      exact (has_type_substitute_weakening g v V Hv e0 T (sort_term kind) Hl f0 n' Hse'
               (has_type_t_well_formed_t _ _ _ HT_sort_f) Hskip).
    + exfalso. apply Hs.
      exact (is_large_substitute_inv g v V Hv e0 T s HT_sort f0 n' Hse'
               (has_type_t_well_formed_t _ _ _ HT_sort_f) Hskip Hlf).
    + exact IH'.
Qed.

(** At the substitution point itself, [type_index] is unchanged (this holds
    regardless of whether [V] is large or small: [type_index n] only inspects
    positions strictly below [n], which are exactly the untouched prefix
    shared by [e] and [f]). *)
Lemma type_index_substitute_at :
  forall g v V (Hv: has_type g v V) (wfg: well_formed g),
  forall n e f, substitute_in_environment v V n e f ->
  well_formed e -> well_formed f -> skipn n f = g ->
  type_index f n = type_index e n.
Proof.
  intros g v V Hv wfg n e f Hse.
  induction Hse as [| e0 f0 n' T Hse' IH]; intros wfe wff Hskip.
  - rewrite !type_index_zero. reflexivity.
  - simpl (type_index (T :: e0) (S n')).
    simpl (type_index (terms.subst_rec v T n' :: f0) (S n')).
    dependent destruction wfe. rename h into HT_sort.
    dependent destruction wff. rename h into HT_sort_f.
    simpl in Hskip.
    assert (IH' : type_index f0 n' = type_index e0 n')
      by (apply IH; [ exact (has_type_t_well_formed_t _ _ _ HT_sort)
                    | exact (has_type_t_well_formed_t _ _ _ HT_sort_f) | exact Hskip ]).
    destruct (is_large_dec e0 T) as [Hl|Hs];
      destruct (is_large_dec f0 (terms.subst_rec v T n')) as [Hlf|Hsf].
    + f_equal. exact IH'.
    + exfalso. apply Hsf.
      exact (has_type_substitute_weakening g v V Hv e0 T (sort_term kind) Hl f0 n' Hse'
               (has_type_t_well_formed_t _ _ _ HT_sort_f) Hskip).
    + exfalso. apply Hs.
      exact (is_large_substitute_inv g v V Hv e0 T s HT_sort f0 n' Hse'
               (has_type_t_well_formed_t _ _ _ HT_sort_f) Hskip Hlf).
    + exact IH'.
Qed.

(** Above the substitution point, [type_index] lands one shallower (small [V]). *)
Lemma type_index_substitute_above :
  forall g v V (Hv: has_type g v V) (wfg: well_formed g),
  (is_large g V -> False) ->
  forall n e f, substitute_in_environment v V n e f ->
  well_formed e -> well_formed f -> skipn n f = g ->
  forall v0, n < v0 -> type_index f (Nat.pred v0) = type_index e v0.
Proof.
  intros g v V Hv wfg Hsm n e f Hse.
  induction Hse as [e_z | e0 f0 n' T Hse' IH]; intros wfe wff Hskip v0 Hlt.
  - destruct v0 as [|v0']; [lia|]. simpl (Nat.pred (S v0')).
    simpl (type_index (V :: e_z) (S v0')).
    assert (Hsm' : is_large e_z V -> False)
      by (intro Hl; apply Hsm; simpl in Hskip; rewrite <- Hskip; exact Hl).
    destruct (is_large_dec e_z V) as [Hl|_]; [exfalso; exact (Hsm' Hl) | reflexivity].
  - destruct v0 as [|v0']; [lia|]. simpl (Nat.pred (S v0')).
    dependent destruction wfe. rename h into HT_sort.
    dependent destruction wff. rename h into HT_sort_f.
    simpl in Hskip.
    destruct v0' as [|v0'']; [lia|].
    simpl (type_index (T :: e0) (S (S v0''))).
    simpl (Nat.pred (S v0'')) in IH.
    simpl (type_index (terms.subst_rec v T n' :: f0) (S v0'')).
    assert (IH' : type_index f0 v0'' = type_index e0 (S v0''))
      by (exact (IH (has_type_t_well_formed_t _ _ _ HT_sort)
                   (has_type_t_well_formed_t _ _ _ HT_sort_f) Hskip (S v0'') ltac:(lia))).
    destruct (is_large_dec e0 T) as [Hl|Hs];
      destruct (is_large_dec f0 (terms.subst_rec v T n')) as [Hlf|Hsf].
    + f_equal. exact IH'.
    + exfalso. apply Hsf.
      exact (has_type_substitute_weakening g v V Hv e0 T (sort_term kind) Hl f0 n' Hse'
               (has_type_t_well_formed_t _ _ _ HT_sort_f) Hskip).
    + exfalso. apply Hs.
      exact (is_large_substitute_inv g v V Hv e0 T s HT_sort f0 n' Hse'
               (has_type_t_well_formed_t _ _ _ HT_sort_f) Hskip Hlf).
    + exact IH'.
Qed.

(** [type_index] under large substitution: removing a large binder at position [n]
    shifts the target type index by −1 for source positions above [n]. *)
Lemma type_index_substitute_above_large :
  forall g v V (Hv: has_type g v V),
  is_large g V ->
  forall n e f, substitute_in_environment v V n e f ->
  well_formed e -> well_formed f -> skipn n f = g ->
  forall v0, n < v0 -> Nat.pred (type_index e v0) = type_index f (Nat.pred v0).
Proof.
  intros g v V Hv Hlarge n e f Hse.
  induction Hse as [e_z | e0 f0 n' T Hse' IH]; intros wfe wff Hskip v0 Hlt.
  - destruct v0 as [|v0']; [lia|]. simpl (Nat.pred (S v0')).
    simpl (type_index (V :: e_z) (S v0')).
    assert (HlV : is_large e_z V)
      by (simpl in Hskip; rewrite Hskip; exact Hlarge).
    destruct (is_large_dec e_z V) as [_|Habs]; [| exfalso; exact (Habs HlV)].
    simpl. reflexivity.
  - destruct v0 as [|v0']; [lia|]. simpl (Nat.pred (S v0')).
    dependent destruction wfe. rename h into HT_sort.
    dependent destruction wff. rename h into HT_sort_f.
    simpl in Hskip.
    destruct v0' as [|v0'']; [lia|].
    simpl (type_index (T :: e0) (S (S v0''))).
    simpl (type_index (terms.subst_rec v T n' :: f0) (S v0'')).
    assert (IH' : Nat.pred (type_index e0 (S v0'')) = type_index f0 v0'')
      by (exact (IH (has_type_t_well_formed_t _ _ _ HT_sort)
                   (has_type_t_well_formed_t _ _ _ HT_sort_f) Hskip (S v0'') ltac:(lia))).
    destruct (is_large_dec e0 T) as [Hl|Hs];
      destruct (is_large_dec f0 (terms.subst_rec v T n')) as [Hlf|Hsf].
    + assert (Htb : type_binding e0 n' = true).
      { unfold type_binding.
        rewrite (nth_substitute_eq v V n' e0 f0 Hse').
        rewrite (skipn_succ_substitute v V n' e0 f0 Hse'). rewrite Hskip.
        destruct (is_large_dec g V) as [_|Hc]; [reflexivity | exfalso; exact (Hc Hlarge)]. }
      assert (Hpos : type_index e0 (S v0'') > type_index e0 n')
        by (apply type_index_gt_of_type_binding; [lia | exact Htb]).
      simpl. lia.
    + exfalso. apply Hsf.
      exact (has_type_substitute_weakening g v V Hv e0 T (sort_term kind) Hl f0 n' Hse'
               (has_type_t_well_formed_t _ _ _ HT_sort_f) Hskip).
    + exfalso. apply Hs.
      exact (is_large_substitute_inv g v V Hv e0 T s HT_sort f0 n' Hse'
               (has_type_t_well_formed_t _ _ _ HT_sort_f) Hskip Hlf).
    + exact IH'.
Qed.

(** At the (small) substitution point, the binder is not a type binding. *)
Lemma type_binding_at_subst_false :
  forall g v0 V0 (Hsm: is_large g V0 -> False)
  n e f (Hse: substitute_in_environment v0 V0 n e f) (Hskip: skipn n f = g),
  type_binding e n = false.
Proof.
  intros g v0 V0 Hsm n e f Hse Hskip.
  unfold type_binding. rewrite (nth_substitute_eq v0 V0 n e f Hse).
  destruct (is_large_dec (skipn (S n) e) V0) as [Hl | _]; [| reflexivity].
  exfalso. apply Hsm.
  rewrite (skipn_succ_substitute v0 V0 n e f Hse) in Hl. rewrite Hskip in Hl. exact Hl.
Qed.

(** At the (large) substitution point, the binder IS a type binding. *)
Lemma type_binding_at_subst_true :
  forall g v0 V0 (Hlarge: is_large g V0)
  n e f (Hse: substitute_in_environment v0 V0 n e f) (Hskip: skipn n f = g),
  type_binding e n = true.
Proof.
  intros g v0 V0 Hlarge n e f Hse Hskip.
  unfold type_binding. rewrite (nth_substitute_eq v0 V0 n e f Hse).
  destruct (is_large_dec (skipn (S n) e) V0) as [_ | Habs]; [reflexivity |].
  exfalso. apply Habs.
  rewrite (skipn_succ_substitute v0 V0 n e f Hse). rewrite Hskip. exact Hlarge.
Qed.

(** The normal form of a small substitution into a type-level neutral is not a
    lambda: the (variable) head survives the substitution because it is a type
    binder distinct from the small substituted variable. *)
Lemma nf_subst_not_lam :
  forall g v0 V0 (Hsm: is_large g V0 -> False)
    n e f (Hse: substitute_in_environment v0 V0 n e f) (Hskip: skipn n f = g),
  forall u, normal u -> (forall T b, u <> lam T b) -> type_expr e u = true ->
  forall snsub T b, nf (subst_rec v0 u n) snsub <> lam T b.
Proof.
  intros g v0 V0 Hsm n e f Hse Hskip.
  assert (Htbn : type_binding e n = false)
    by (exact (type_binding_at_subst_false g v0 V0 Hsm n e f Hse Hskip)).
  induction u as [s0 | k | uT _ uM _ | u' IHu' a' _ | uT _ uU _];
    intros Hnorm Hnl Hte snsub T b Habs.
  - (* sort *) revert snsub Habs.
    change (subst_rec v0 (sort_term s0) n) with (sort_term s0). intros snsub Habs.
    rewrite (nf_sort s0 snsub) in Habs. discriminate.
  - (* var k *)
    assert (Hkn : k <> n).
    { intro. subst k. simpl in Hte. rewrite Htbn in Hte. discriminate. }
    revert snsub Habs.
    destruct (lt_eq_lt_dec n k) as [[Hlt | Heq] | Hgt].
    + rewrite (subst_ref_gt v0 k n Hlt). intros snsub Habs.
      rewrite (nf_normal_eq _ snsub (normal_var (Nat.pred k))) in Habs. discriminate.
    + lia.
    + rewrite (subst_ref_lt v0 k n Hgt). intros snsub Habs.
      rewrite (nf_normal_eq _ snsub (normal_var k)) in Habs. discriminate.
  - (* lam: excluded by Hnl *)
    exfalso. eapply Hnl. reflexivity.
  - (* app u' a' *)
    simpl in Hte.
    assert (Hnu' : normal u') by (intros x Hx; eapply Hnorm; apply app_reduces_left; exact Hx).
    assert (Hnlu' : forall T0 b0, u' <> lam T0 b0)
      by (intros T0 b0 Heq; rewrite Heq in Hnorm; eapply Hnorm; apply beta).
    revert snsub Habs.
    change (subst_rec v0 (terms.app u' a') n)
      with (terms.app (subst_rec v0 u' n) (subst_rec v0 a' n)). intros snsub Habs.
    assert (snu' : strongly_normalizing (subst_rec v0 u' n)).
    { apply (subterm_sn _ snsub).
      apply sub_no_bind. apply sub_no_binder_app_l. }
    assert (sna' : strongly_normalizing (subst_rec v0 a' n)).
    { apply (subterm_sn _ snsub).
      apply sub_no_bind. apply sub_no_binder_app_r. }
    rewrite (nf_app_neutral (subst_rec v0 u' n) (subst_rec v0 a' n) snsub snu' sna')
      in Habs by (exact (IHu' Hnu' Hnlu' Hte snu')).
    discriminate.
  - (* prod *) revert snsub Habs.
    change (subst_rec v0 (prod uT uU) n)
      with (prod (subst_rec v0 uT n) (subst_rec v0 uU (S n))). intros snsub Habs.
    assert (snT : strongly_normalizing (subst_rec v0 uT n)).
    { apply (subterm_sn _ snsub).
      apply sub_no_bind. apply sub_no_binder_prod. }
    assert (snU : strongly_normalizing (subst_rec v0 uU (S n))).
    { apply (subterm_sn _ snsub).
      apply sub_bind with (subst_rec v0 uT n). apply sub_binder_prod. }
    rewrite (nf_prod (subst_rec v0 uT n) (subst_rec v0 uU (S n)) snsub snT snU) in Habs.
    discriminate.
Qed.

(** [extract_kind_L] is invariant under small substitution + normalization:
    the kind skeleton of a normal sort-typed term is preserved. *)
Lemma extract_kind_L_small_subst : forall W,
  forall g v0 V0 (Hv0: has_type g v0 V0) (wfg: well_formed g) (Hsm: is_large g V0 -> False),
  forall n e f s, substitute_in_environment v0 V0 n e f ->
  has_type e W (sort_term s) -> well_formed e -> well_formed f -> skipn n f = g ->
  normal W -> type_expr e W = true ->
  forall snsub, extract_kind_L (nf (subst_rec v0 W n) snsub) = extract_kind_L W.
Proof.
  induction W as [s0 | k | X1 IHX1 X2 IHX2 | X1 IHX1 X2 IHX2 | X1 IHX1 X2 IHX2];
    intros g v0 V0 Hv0 wfg Hsm n e f s Hse HW wfe wff Hskip Hnorm Hte; simpl.
  - (* sort *) intro snsub. simpl. rewrite nf_sort. reflexivity.
  - (* var *) intro snsub. simpl.
    revert snsub. destruct (lt_eq_lt_dec n k) as [[Hlt | Heq] | Hgt]; intro snsub.
    + simpl. rewrite (nf_normal_eq _ snsub (normal_var _)). reflexivity.
    + subst k. exfalso.
      assert (Htb : type_binding e n = false)
        by (exact (type_binding_at_subst_false g v0 V0 Hsm n e f Hse Hskip)).
      simpl in Hte. rewrite Htb in Hte. discriminate.
    + simpl. rewrite (nf_normal_eq _ snsub (normal_var _)). reflexivity.
  - (* lam *)
    intro snsub.
    change (subst_rec v0 (lam X1 X2) n) with
      (lam (subst_rec v0 X1 n) (subst_rec v0 X2 (S n))) in snsub |- *.
    assert (snX1 : strongly_normalizing (subst_rec v0 X1 n))
      by (apply (subterm_sn _ snsub); apply sub_no_bind; apply sub_no_binder_lam).
    assert (snX2 : strongly_normalizing (subst_rec v0 X2 (S n)))
      by (apply (subterm_sn _ snsub); apply sub_bind with (subst_rec v0 X1 n); apply sub_binder_lam).
    rewrite (nf_lam (subst_rec v0 X1 n) (subst_rec v0 X2 (S n)) snsub snX1 snX2).
    reflexivity.
  - (* app *)
    intro snsub.
    assert (HnX1 : normal X1)
      by (intros u Hu; exact (Hnorm _ (app_reduces_left X1 u Hu X2))).
    assert (HnX2 : normal X2)
      by (intros u Hu; exact (Hnorm _ (app_reduces_right X2 u Hu X1))).
    assert (HnlX1 : forall T b, X1 <> lam T b)
      by (intros T b Heq; rewrite Heq in Hnorm; eapply Hnorm; apply beta).
    change (subst_rec v0 (terms.app X1 X2) n) with
      (terms.app (subst_rec v0 X1 n) (subst_rec v0 X2 n)) in snsub |- *.
    assert (snX1 : strongly_normalizing (subst_rec v0 X1 n))
      by (apply (subterm_sn _ snsub); apply sub_no_bind; apply sub_no_binder_app_l).
    assert (snX2 : strongly_normalizing (subst_rec v0 X2 n))
      by (apply (subterm_sn _ snsub); apply sub_no_bind; apply sub_no_binder_app_r).
    apply (inversion_has_type_app
             (extract_kind_L (nf (terms.app (subst_rec v0 X1 n) (subst_rec v0 X2 n)) snsub) = syntax.KStar)
             e X1 X2 (sort_term s) HW).
    intros V Ur Hu Hv Hconv.
    assert (Hte1 : type_expr e X1 = true) by exact Hte.
    pose proof (nf_subst_not_lam g v0 V0 Hsm n e f Hse Hskip X1 HnX1 HnlX1 Hte1) as Hnl_sub.
    rewrite (nf_app_neutral (subst_rec v0 X1 n) (subst_rec v0 X2 n) snsub snX1 snX2
               (Hnl_sub snX1)).
    reflexivity.
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
        { exact (is_large_substitute_inv g v0 V0 Hv0 e X1 s1 HX1 f n Hse wff Hskip
                   (fst Hcl_sub eq_refl)). }
        pose proof (snd Hcl_orig Hlarge_e) as Habs. discriminate. }
    rewrite Hcl_eq.
    assert (Hte1 : type_expr e X1 = true).
    { apply (snd (type_expr_iff e X1 (sort_term s1) HX1)). left. exists s1. reflexivity. }
    assert (wff' : well_formed (subst_rec v0 X1 n :: f))
      by (apply wf_var with s1; exact HX1_f).
    assert (wfe' : well_formed (X1 :: e))
      by (apply wf_var with s1; exact HX1).
    assert (Hte2 : type_expr (X1 :: e) X2 = true).
    { apply (snd (type_expr_iff (X1 :: e) X2 (sort_term s2) HX2)).
      left. exists s2. reflexivity. }
    destruct (classifier X1).
    + f_equal.
      * exact (IHX1 g v0 V0 Hv0 wfg Hsm n e f s1 Hse HX1 wfe wff Hskip HnX1 Hte1 snX1).
      * exact (IHX2 g v0 V0 Hv0 wfg Hsm (S n) (X1 :: e) (subst_rec v0 X1 n :: f) s2
                 (@sub_succ v0 V0 e f n X1 Hse) HX2 wfe' wff' Hskip HnX2 Hte2 snX2).
    + exact (IHX2 g v0 V0 Hv0 wfg Hsm (S n) (X1 :: e) (subst_rec v0 X1 n :: f) s2
               (@sub_succ v0 V0 e f n X1 Hse) HX2 wfe' wff' Hskip HnX2 Hte2 snX2).
Qed.

Lemma type_expr_subst : forall X,
  forall g v0 V0 (Hv0: has_type g v0 V0) (wfg: well_formed g) (Hsm: is_large g V0 -> False),
  forall n e f B, substitute_in_environment v0 V0 n e f ->
  has_type e X B -> well_formed e -> well_formed f -> skipn n f = g ->
  type_expr f (subst_rec v0 X n) = type_expr e X.
Proof.
  induction X as [s0 | k | X1 IHX1 X2 IHX2 | X1 IHX1 X2 IHX2 | X1 IHX1 X2 IHX2];
    intros g v0 V0 Hv0 wfg Hsm n e f B Hse HX wfe wff Hskip.
  - reflexivity.
  - (* var k *)
    simpl (subst_rec v0 (terms.var k) n).
    destruct (lt_eq_lt_dec n k) as [[Hlt | Heq] | Hgt].
    + simpl. exact (type_binding_substitute_above g v0 V0 Hv0 wfg n e f Hse wfe wff Hskip k Hlt).
    + subst k. simpl (type_expr e (terms.var n)).
      rewrite (type_binding_at_subst_false g v0 V0 Hsm n e f Hse Hskip).
      (* Goal: false = type_expr f (lift n v0) *)
      destruct (type_expr f (lift n v0)) eqn:Hte; [|reflexivity].
      exfalso.
      (* Get typing for lift n v0 in f via weakening *)
      assert (Hlift_ty : has_type f (lift n v0) (lift n V0)).
      { change (lift n V0) with (lift n V0).
        apply weakening_at with g; auto.
        exact (substitute_length_le v0 V0 n e f Hse). }
      (* Get the sort of V0 in g *)
      assert (Hnth : nth_error e n = Some V0) by (exact (nth_substitute_eq v0 V0 n e f Hse)).
      assert (HV0sort : {s_V0 : sort & has_type g V0 (sort_term s_V0)}).
      { assert (Htmp := well_formed_sort n e (skipn (S n) e) eq_refl wfe V0 Hnth).
        destruct Htmp as [s_V0 Hs_V0].
        exists s_V0. rewrite <- Hskip. rewrite <- (skipn_succ_substitute v0 V0 n e f Hse). exact Hs_V0. }
      destruct HV0sort as [s_V0 HV0_g].
      (* Weaken V0's sort typing to f *)
      assert (HV0_f : has_type f (lift n V0) (sort_term s_V0)).
      { change (sort_term s_V0) with (lift n (sort_term s_V0)).
        apply weakening_at with g; auto.
        exact (substitute_length_le v0 V0 n e f Hse). }
      (* Apply type_expr_iff *)
      destruct (fst (type_expr_iff f (lift n v0) (lift n V0) Hlift_ty) Hte) as [[s_eq Hseq] | Hlarge_f].
      * (* lift n V0 = sort_term s_eq → V0 = sort_term s_eq *)
        destruct V0; simpl in Hseq; try discriminate.
        injection Hseq as <-.
        destruct s.
        -- exact (inversion_has_type_kind g (sort_term s_V0) HV0_g).
        -- apply Hsm. unfold is_large.
           assert (Hck := inversion_has_type_prop g (sort_term s_V0) HV0_g).
           apply convertible_sort in Hck. subst s_V0. exact HV0_g.
        -- apply Hsm. unfold is_large.
           assert (Hck := inversion_has_type_set g (sort_term s_V0) HV0_g).
           apply convertible_sort in Hck. subst s_V0. exact HV0_g.
      * (* is_large f (lift n V0) → sort of V0 is kind → contradiction *)
        unfold is_large in Hlarge_f.
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
    assert (wfe_X1 : well_formed e) by (exact (has_type_well_formed _ _ _ HX1)).
    assert (HX1f : has_type f (subst_rec v0 X1 n) (sort_term s1)).
    { change (sort_term s1) with (subst_rec v0 (sort_term s1) n).
      exact (has_type_substitute_weakening g v0 V0 Hv0 e X1 (sort_term s1) HX1 f n Hse wff Hskip). }
    assert (wff' : well_formed (subst_rec v0 X1 n :: f)) by (apply wf_var with s1; exact HX1f).
    assert (wfe_X1e : well_formed (X1 :: e)) by (apply wf_var with s1; exact HX1).
    exact (IHX2 g v0 V0 Hv0 wfg Hsm (S n) (X1 :: e) (subst_rec v0 X1 n :: f) T''
             (@sub_succ v0 V0 e f n X1 Hse) HX2 wfe_X1e wff' Hskip).
  - (* app X1 X2 *)
    simpl (subst_rec v0 (terms.app X1 X2) n). simpl (type_expr _ (terms.app _ _)).
    apply (inversion_has_type_app
             (type_expr f (subst_rec v0 X1 n) = type_expr e X1)
             e X1 X2 B HX).
    intros V Ur Hu Hv Hconv.
    exact (IHX1 g v0 V0 Hv0 wfg Hsm n e f (prod V Ur) Hse Hu wfe wff Hskip).
  - (* prod *) reflexivity.
Qed.

(** Core: [extract_typ_L] is invariant under small substitution for normal terms.
    Generalized over [substitute_in_environment] at arbitrary depth [n].
    The [type_expr] guard excludes the var-hit case (where V0 is small). *)
(** [extract_kind_L] is invariant under substitution for any [v0]/[V0]
    (regardless of size), provided the term [W] is itself syntactically a
    classifier ([classifier W = true]): a classifier is built purely from
    [sort_term]/[prod] constructors, so [var]/[lam]/[app] never arise, and the
    residual argument (the classifier-invariance-under-substitution fact for
    domains) does not depend on the size of the substituted variable. *)
Lemma extract_kind_L_large_subst : forall W,
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
      * exact (IHX1 g v0 V0 Hv0 wfg n e f s1 Hse HX1 wfe wff Hskip HnX1 eq_refl snX1).
      * exact (IHX2 g v0 V0 Hv0 wfg (S n) (X1 :: e) (subst_rec v0 X1 n :: f) s2
                 (@sub_succ v0 V0 e f n X1 Hse) HX2 wfe' wff' Hskip HnX2 Hcw2 snX2).
    + exact (IHX2 g v0 V0 Hv0 wfg (S n) (X1 :: e) (subst_rec v0 X1 n :: f) s2
               (@sub_succ v0 V0 e f n X1 Hse) HX2 wfe' wff' Hskip HnX2 Hcw2 snX2).
Qed.

Lemma extract_typ_L_small_subst : forall W,
  forall g v0 V0 (Hv0: has_type g v0 V0) (wfg: well_formed g) (Hsm: is_large g V0 -> False),
  forall n e f B, substitute_in_environment v0 V0 n e f ->
  has_type e W B -> well_formed e -> well_formed f -> skipn n f = g ->
  normal W -> type_expr e W = true ->
  forall snsub, extract_typ_L e W = extract_typ_L f (nf (subst_rec v0 W n) snsub).
Proof.
  induction W as [s0 | k | X1 IHX1 X2 IHX2 | X1 IHX1 X2 IHX2 | X1 IHX1 X2 IHX2];
    intros g v0 V0 Hv0 wfg Hsm n e f B Hse HW wfe wff Hskip Hnorm Hte snsub.
  - (* sort *)
    change (subst_rec v0 (sort_term s0) n) with (sort_term s0).
    rewrite (nf_sort s0 snsub). reflexivity.
  - (* var k *)
    simpl in Hte. (* type_expr e (var k) = type_binding e k *)
    revert snsub.
    simpl (subst_rec v0 (terms.var k) n).
    destruct (lt_eq_lt_dec n k) as [[Hlt | Heq] | Hgt]; intro snsub.
    + (* k > n *)
      rewrite (nf_normal_eq _ snsub (normal_var (Nat.pred k))).
      simpl. rewrite (type_binding_substitute_above g v0 V0 Hv0 wfg n e f Hse wfe wff Hskip k Hlt).
      rewrite Hte. f_equal. symmetry.
      exact (type_index_substitute_above g v0 V0 Hv0 wfg Hsm n e f Hse wfe wff Hskip k Hlt).
    + (* k = n: impossible since V0 small → type_binding e n = false *)
      subst k. exfalso.
      rewrite (type_binding_at_subst_false g v0 V0 Hsm n e f Hse Hskip) in Hte.
      discriminate.
    + (* k < n *)
      rewrite (nf_normal_eq _ snsub (normal_var k)).
      simpl. rewrite (type_binding_substitute_below g v0 V0 Hv0 wfg n e f Hse wfe wff Hskip k Hgt).
      rewrite Hte. f_equal. symmetry.
      exact (type_index_substitute_below g v0 V0 Hv0 wfg n e f Hse wfe wff Hskip k Hgt).
  - (* lam X1 X2 *)
    assert (HnX1 : normal X1)
      by (intros u Hu; exact (Hnorm _ (abs_reduces_left X1 u Hu X2))).
    assert (HnX2 : normal X2)
      by (intros u Hu; exact (Hnorm _ (abs_reduces_right X2 u Hu X1))).
    apply (inversion_has_type_abs
             (extract_typ_L e (lam X1 X2) =
              extract_typ_L f (nf (subst_rec v0 (lam X1 X2) n) snsub))
             e X1 X2 B HW).
    intros s1 s2 T'' HX1 HX2 HT'' Hconv.
    change (subst_rec v0 (lam X1 X2) n)
      with (lam (subst_rec v0 X1 n) (subst_rec v0 X2 (S n))) in snsub |- *.
    assert (snX1 : strongly_normalizing (subst_rec v0 X1 n))
      by (apply (subterm_sn _ snsub); apply sub_no_bind; apply sub_no_binder_lam).
    assert (snX2 : strongly_normalizing (subst_rec v0 X2 (S n)))
      by (apply (subterm_sn _ snsub); apply sub_bind with (subst_rec v0 X1 n); apply sub_binder_lam).
    rewrite (nf_lam (subst_rec v0 X1 n) (subst_rec v0 X2 (S n)) snsub snX1 snX2).
    simpl (extract_typ_L _ (lam _ _)).
    (* classifier invariance *)
    assert (Hcl_eq : classifier (nf (subst_rec v0 X1 n) snX1) = classifier X1).
    { assert (Hcl_orig : iffT (classifier X1 = true) (is_large e X1)).
      { exact (classifier_iff_is_large_nf X1 e s1 HX1 HnX1). }
      assert (HX1_f : has_type f (subst_rec v0 X1 n) (sort_term s1)).
      { change (sort_term s1) with (subst_rec v0 (sort_term s1) n).
        exact (has_type_substitute_weakening g v0 V0 Hv0 e X1 (sort_term s1) HX1 f n Hse wff Hskip). }
      assert (HX1_nf : has_type f (nf (subst_rec v0 X1 n) snX1) (sort_term s1)).
      { eapply subject_reduction_theorem; [apply nf_reduces | exact HX1_f]. }
      assert (Hcl_sub : iffT (classifier (nf (subst_rec v0 X1 n) snX1) = true) (is_large f (subst_rec v0 X1 n))).
      { exact (classifier_nf_is_large f (subst_rec v0 X1 n) snX1 s1 HX1_f). }
      destruct (classifier X1) eqn:HclX1; destruct (classifier (nf (subst_rec v0 X1 n) snX1)) eqn:HclS;
        try reflexivity; exfalso.
      - (* true/false: X1 large, but classifier of subst is false *)
        assert (Hlarge_f : is_large f (subst_rec v0 X1 n)).
        { apply (has_type_substitute_weakening g v0 V0 Hv0 e X1 (sort_term kind)
                   (fst Hcl_orig eq_refl) f n Hse wff Hskip). }
        pose proof (snd Hcl_sub Hlarge_f) as Habs. discriminate.
      - (* false/true: classifier of subst is true, but X1 not large *)
        assert (Hlarge_e : is_large e X1).
        { exact (is_large_substitute_inv g v0 V0 Hv0 e X1 s1 HX1 f n Hse wff Hskip
                   (fst Hcl_sub eq_refl)). }
        pose proof (snd Hcl_orig Hlarge_e) as Habs. discriminate. }
    rewrite Hcl_eq.
    (* Extract_kind_L invariance *)
    assert (HX1_f : has_type f (subst_rec v0 X1 n) (sort_term s1)).
    { change (sort_term s1) with (subst_rec v0 (sort_term s1) n).
      exact (has_type_substitute_weakening g v0 V0 Hv0 e X1 (sort_term s1) HX1 f n Hse wff Hskip). }
    assert (Hkind_eq : extract_kind_L (nf (subst_rec v0 X1 n) snX1) = extract_kind_L X1).
    { assert (Hte1 : type_expr e X1 = true).
      { apply (snd (type_expr_iff e X1 (sort_term s1) HX1)). left. exists s1. reflexivity. }
      exact (extract_kind_L_small_subst X1 g v0 V0 Hv0 wfg Hsm n e f s1 Hse HX1 wfe wff Hskip HnX1 Hte1 snX1). }
    assert (wff' : well_formed (subst_rec v0 X1 n :: f))
      by (apply wf_var with s1; exact HX1_f).
    assert (wfe' : well_formed (X1 :: e))
      by (apply wf_var with s1; exact HX1).
    assert (Hte2 : type_expr (X1 :: e) X2 = true) by exact Hte.
    assert (IH2 := IHX2 g v0 V0 Hv0 wfg Hsm (S n) (X1 :: e) (subst_rec v0 X1 n :: f) T''
             (@sub_succ v0 V0 e f n X1 Hse) HX2 wfe' wff' Hskip HnX2 Hte2 snX2).
    assert (HX2_body_f : has_type (subst_rec v0 X1 n :: f) (subst_rec v0 X2 (S n))
              (subst_rec v0 T'' (S n))).
    { exact (has_type_substitute_weakening g v0 V0 Hv0 (X1 :: e) X2 T'' HX2
               (subst_rec v0 X1 n :: f) (S n) (@sub_succ v0 V0 e f n X1 Hse) wff' Hskip). }
    assert (Hbody_ty : has_type (subst_rec v0 X1 n :: f)
              (nf (subst_rec v0 X2 (S n)) snX2) (subst_rec v0 T'' (S n))).
    { eapply subject_reduction_theorem; [apply nf_reduces | exact HX2_body_f]. }
    destruct (classifier X1).
    + rewrite Hkind_eq. f_equal. rewrite IH2.
      apply (extract_typ_L_swap (subst_rec v0 X1 n) (nf (subst_rec v0 X1 n) snX1)
               (nf_reduces _ snX1) (nf (subst_rec v0 X2 (S n)) snX2) nil f
               (subst_rec v0 T'' (S n))).
      simpl. exact Hbody_ty.
    + rewrite IH2.
      apply (extract_typ_L_swap (subst_rec v0 X1 n) (nf (subst_rec v0 X1 n) snX1)
               (nf_reduces _ snX1) (nf (subst_rec v0 X2 (S n)) snX2) nil f
               (subst_rec v0 T'' (S n))).
      simpl. exact Hbody_ty.
  - (* app X1 X2 *)
    assert (HnX1 : normal X1)
      by (intros u Hu; exact (Hnorm _ (app_reduces_left X1 u Hu X2))).
    assert (HnX2 : normal X2)
      by (intros u Hu; exact (Hnorm _ (app_reduces_right X2 u Hu X1))).
    assert (HnlX1 : forall T b, X1 <> lam T b)
      by (intros T b Heq; rewrite Heq in Hnorm; eapply Hnorm; apply beta).
    apply (inversion_has_type_app
             (extract_typ_L e (terms.app X1 X2) =
              extract_typ_L f (nf (subst_rec v0 (terms.app X1 X2) n) snsub))
             e X1 X2 B HW).
    intros V Ur Hu Hv Hconv.
    change (subst_rec v0 (terms.app X1 X2) n)
      with (terms.app (subst_rec v0 X1 n) (subst_rec v0 X2 n)) in snsub |- *.
    assert (snX1 : strongly_normalizing (subst_rec v0 X1 n))
      by (apply (subterm_sn _ snsub); apply sub_no_bind; apply sub_no_binder_app_l).
    assert (snX2 : strongly_normalizing (subst_rec v0 X2 n))
      by (apply (subterm_sn _ snsub); apply sub_no_bind; apply sub_no_binder_app_r).
    (* type_expr e (app X1 X2) = type_expr e X1 = true *)
    assert (Hte1 : type_expr e X1 = true) by exact Hte.
    pose proof (nf_subst_not_lam g v0 V0 Hsm n e f Hse Hskip X1 HnX1 HnlX1 Hte1) as Hnl_sub.
    rewrite (nf_app_neutral (subst_rec v0 X1 n) (subst_rec v0 X2 n) snsub snX1 snX2
               (Hnl_sub snX1)).
    simpl (extract_typ_L _ (terms.app _ _)).
    (* type_expr invariance: type_expr f (nf (subst Xi)) = type_expr e Xi *)
    assert (HX1_f : has_type f (subst_rec v0 X1 n) (subst_rec v0 (prod V Ur) n))
      by (exact (has_type_substitute_weakening g v0 V0 Hv0 e X1 (prod V Ur) Hu f n Hse wff Hskip)).
    assert (HX2_f : has_type f (subst_rec v0 X2 n) (subst_rec v0 V n))
      by (exact (has_type_substitute_weakening g v0 V0 Hv0 e X2 V Hv f n Hse wff Hskip)).
    rewrite (type_expr_nf f (subst_rec v0 X1 n) _ snX1 HX1_f).
    rewrite (type_expr_nf f (subst_rec v0 X2 n) _ snX2 HX2_f).
    rewrite (type_expr_subst X1 g v0 V0 Hv0 wfg Hsm n e f (prod V Ur) Hse Hu wfe wff Hskip).
    rewrite (type_expr_subst X2 g v0 V0 Hv0 wfg Hsm n e f V Hse Hv wfe wff Hskip).
    (* IH — only the head needs type_expr = true, the arg may be false *)
    pose proof (IHX1 g v0 V0 Hv0 wfg Hsm n e f (prod V Ur) Hse Hu wfe wff Hskip HnX1 Hte1 snX1) as IH1.
    destruct (type_expr e X1) eqn:HeX1; [| discriminate Hte1].
    destruct (type_expr e X2) eqn:HeX2.
    + pose proof (IHX2 g v0 V0 Hv0 wfg Hsm n e f V Hse Hv wfe wff Hskip HnX2 HeX2 snX2) as IH2.
      rewrite IH1. rewrite IH2. reflexivity.
    + rewrite IH1. reflexivity.
  - (* prod X1 X2 *)
    assert (HnX1 : normal X1)
      by (intros u Hu; exact (Hnorm _ (prod_reduces_left X1 u Hu X2))).
    assert (HnX2 : normal X2)
      by (intros u Hu; exact (Hnorm _ (prod_reduces_right X2 u Hu X1))).
    apply (inversion_has_type_prod
             (extract_typ_L e (prod X1 X2) =
              extract_typ_L f (nf (subst_rec v0 (prod X1 X2) n) snsub))
             e X1 X2 B HW).
    intros s1 s2 HX1 HX2 Hconv.
    change (subst_rec v0 (prod X1 X2) n)
      with (prod (subst_rec v0 X1 n) (subst_rec v0 X2 (S n))) in snsub |- *.
    assert (snX1 : strongly_normalizing (subst_rec v0 X1 n))
      by (apply (subterm_sn _ snsub); apply sub_no_bind; apply sub_no_binder_prod).
    assert (snX2 : strongly_normalizing (subst_rec v0 X2 (S n)))
      by (apply (subterm_sn _ snsub); apply sub_bind with (subst_rec v0 X1 n); apply sub_binder_prod).
    rewrite (nf_prod (subst_rec v0 X1 n) (subst_rec v0 X2 (S n)) snsub snX1 snX2).
    simpl (extract_typ_L _ (prod _ _)).
    (* classifier invariance — same as lam case *)
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
        { exact (is_large_substitute_inv g v0 V0 Hv0 e X1 s1 HX1 f n Hse wff Hskip
                   (fst Hcl_sub eq_refl)). }
        pose proof (snd Hcl_orig Hlarge_e) as Habs. discriminate. }
    rewrite Hcl_eq.
    assert (wff' : well_formed (subst_rec v0 X1 n :: f))
      by (apply wf_var with s1; exact HX1_f).
    assert (wfe' : well_formed (X1 :: e))
      by (apply wf_var with s1; exact HX1).
    (* type_expr for X2: type_expr (X1::e) X2 is needed for IH2 *)
    assert (Hte2 : type_expr (X1 :: e) X2 = true).
    { apply (snd (type_expr_iff (X1 :: e) X2 (sort_term s2) HX2)).
      left. exists s2. reflexivity. }
    pose proof (IHX2 g v0 V0 Hv0 wfg Hsm (S n) (X1 :: e) (subst_rec v0 X1 n :: f) (sort_term s2)
                 (@sub_succ v0 V0 e f n X1 Hse) HX2 wfe' wff' Hskip HnX2 Hte2 snX2) as IH2.
    assert (HX2_body_f : has_type (subst_rec v0 X1 n :: f) (subst_rec v0 X2 (S n)) (sort_term s2)).
    { change (sort_term s2) with (subst_rec v0 (sort_term s2) (S n)).
      exact (has_type_substitute_weakening g v0 V0 Hv0 (X1 :: e) X2 (sort_term s2) HX2
               (subst_rec v0 X1 n :: f) (S n) (@sub_succ v0 V0 e f n X1 Hse) wff' Hskip). }
    assert (Hte1 : type_expr e X1 = true).
    { apply (snd (type_expr_iff e X1 (sort_term s1) HX1)). left. exists s1. reflexivity. }
    destruct (classifier X1) eqn:HclX1.
    + (* large domain: all *)
      assert (Hkind_eq : extract_kind_L (nf (subst_rec v0 X1 n) snX1) = extract_kind_L X1)
        by (exact (extract_kind_L_small_subst X1 g v0 V0 Hv0 wfg Hsm n e f s1 Hse HX1 wfe wff Hskip HnX1 Hte1 snX1)).
      rewrite Hkind_eq. f_equal.
      rewrite IH2.
      apply (extract_typ_L_swap (subst_rec v0 X1 n) (nf (subst_rec v0 X1 n) snX1)
               (nf_reduces _ snX1) (nf (subst_rec v0 X2 (S n)) snX2) nil f (sort_term s2)).
      simpl. eapply subject_reduction_theorem; [apply nf_reduces | exact HX2_body_f].
    + (* small domain: arrow *)
      pose proof (IHX1 g v0 V0 Hv0 wfg Hsm n e f (sort_term s1) Hse HX1 wfe wff Hskip HnX1 Hte1 snX1)
        as IH1.
      f_equal.
      * exact IH1.
      * transitivity (extract_typ_L (subst_rec v0 X1 n :: f) (nf (subst_rec v0 X2 (S n)) snX2)).
        -- exact IH2.
        -- apply (extract_typ_L_swap (subst_rec v0 X1 n) (nf (subst_rec v0 X1 n) snX1)
                    (nf_reduces _ snX1) (nf (subst_rec v0 X2 (S n)) snX2) nil f
                    (subst_rec v0 (sort_term s2) (S n))).
           simpl. eapply subject_reduction_theorem; [apply nf_reduces | exact HX2_body_f].
Qed.

(** ** Congruence closure of [ty_equiv] under the target type constructors. *)

Lemma ty_equiv_arrow_l_cong : forall A A' B, infrastructure.ty_equiv A A' ->
  infrastructure.ty_equiv (syntax.arrow A B) (syntax.arrow A' B).
Proof.
  intros A A' B H. unfold infrastructure.ty_equiv in H |- *. induction H.
  - apply rst_step. apply infrastructure.tystep_arrow_l. assumption.
  - apply rst_refl.
  - apply rst_sym. assumption.
  - eapply rst_trans; eassumption.
Qed.

Lemma ty_equiv_arrow_r_cong : forall A B B', infrastructure.ty_equiv B B' ->
  infrastructure.ty_equiv (syntax.arrow A B) (syntax.arrow A B').
Proof.
  intros A B B' H. unfold infrastructure.ty_equiv in H |- *. induction H.
  - apply rst_step. apply infrastructure.tystep_arrow_r. assumption.
  - apply rst_refl.
  - apply rst_sym. assumption.
  - eapply rst_trans; eassumption.
Qed.

Lemma ty_equiv_arrow_cong : forall A A' B B', infrastructure.ty_equiv A A' ->
  infrastructure.ty_equiv B B' ->
  infrastructure.ty_equiv (syntax.arrow A B) (syntax.arrow A' B').
Proof.
  intros A A' B B' HA HB.
  eapply infrastructure.ty_equiv_trans; [apply ty_equiv_arrow_l_cong; exact HA |].
  apply ty_equiv_arrow_r_cong. exact HB.
Qed.

Lemma ty_equiv_all_cong : forall K A A', infrastructure.ty_equiv A A' ->
  infrastructure.ty_equiv (syntax.all K A) (syntax.all K A').
Proof.
  intros K A A' H. unfold infrastructure.ty_equiv in H |- *. induction H.
  - apply rst_step. apply infrastructure.tystep_all. assumption.
  - apply rst_refl.
  - apply rst_sym. assumption.
  - eapply rst_trans; eassumption.
Qed.

Lemma ty_equiv_tyabs_cong : forall K A A', infrastructure.ty_equiv A A' ->
  infrastructure.ty_equiv (syntax.tyabs K A) (syntax.tyabs K A').
Proof.
  intros K A A' H. unfold infrastructure.ty_equiv in H |- *. induction H.
  - apply rst_step. apply infrastructure.tystep_tyabs. assumption.
  - apply rst_refl.
  - apply rst_sym. assumption.
  - eapply rst_trans; eassumption.
Qed.

Lemma ty_equiv_tyapp_l_cong : forall F F' A, infrastructure.ty_equiv F F' ->
  infrastructure.ty_equiv (syntax.tyapp F A) (syntax.tyapp F' A).
Proof.
  intros F F' A H. unfold infrastructure.ty_equiv in H |- *. induction H.
  - apply rst_step. apply infrastructure.tystep_tyapp_l. assumption.
  - apply rst_refl.
  - apply rst_sym. assumption.
  - eapply rst_trans; eassumption.
Qed.

Lemma ty_equiv_tyapp_r_cong : forall F A A', infrastructure.ty_equiv A A' ->
  infrastructure.ty_equiv (syntax.tyapp F A) (syntax.tyapp F A').
Proof.
  intros F A A' H. unfold infrastructure.ty_equiv in H |- *. induction H.
  - apply rst_step. apply infrastructure.tystep_tyapp_r. assumption.
  - apply rst_refl.
  - apply rst_sym. assumption.
  - eapply rst_trans; eassumption.
Qed.

Lemma ty_equiv_tyapp_cong : forall F F' A A', infrastructure.ty_equiv F F' ->
  infrastructure.ty_equiv A A' ->
  infrastructure.ty_equiv (syntax.tyapp F A) (syntax.tyapp F' A').
Proof.
  intros F F' A A' HF HA.
  eapply infrastructure.ty_equiv_trans; [apply ty_equiv_tyapp_l_cong; exact HF |].
  apply ty_equiv_tyapp_r_cong. exact HA.
Qed.

(** [extract_typ] is invariant under small substitution at position 0. *)
Lemma extract_typ_small_subst_eq :
  forall e V0 v0 (Hv0 : has_type e v0 V0) (Hsmall : is_large e V0 -> False)
  (wfe : well_formed e)
  Ur s (HUr : has_type (V0 :: e) Ur (sort_term s)) snUr snSub,
  extract_typ (V0 :: e) Ur snUr = extract_typ e (terms.subst v0 Ur) snSub.
Proof.
  intros e V0 v0 Hv0 Hsmall wfe Ur s HUr snUr snSub.
  unfold extract_typ.
  pose proof (strong_normalization _ _ _ HUr) as snUr'.
  rewrite (nf_pi Ur snUr snUr').
  assert (HUr_sub : has_type e (terms.subst v0 Ur) (sort_term s)).
  { change (sort_term s) with (terms.subst v0 (sort_term s)).
    exact (substitution e V0 Ur (sort_term s) HUr v0 Hv0). }
  pose proof (strong_normalization _ _ _ HUr_sub) as snSub'.
  rewrite (nf_pi (terms.subst v0 Ur) snSub snSub').
  assert (HnfUr_ty : has_type (V0 :: e) (nf Ur snUr') (sort_term s))
    by (eapply subject_reduction_theorem; [apply nf_reduces | exact HUr]).
  assert (wfe' : well_formed (V0 :: e)) by (exact (has_type_well_formed _ _ _ HUr)).
  assert (Hte_nf : type_expr (V0 :: e) (nf Ur snUr') = true).
  { apply (snd (type_expr_iff (V0 :: e) (nf Ur snUr') (sort_term s) HnfUr_ty)).
    left. exists s. reflexivity. }
  assert (HnfUr_sub_ty : has_type e (subst_rec v0 (nf Ur snUr') 0) (sort_term s)).
  { change (sort_term s) with (subst_rec v0 (sort_term s) 0).
    exact (substitution _ V0 (nf Ur snUr') (sort_term s) HnfUr_ty v0 Hv0). }
  pose proof (strong_normalization _ _ _ HnfUr_sub_ty) as snNfSub.
  rewrite (extract_typ_L_small_subst (nf Ur snUr') e v0 V0 Hv0 wfe Hsmall
             0 (V0 :: e) e (sort_term s) (sub_zero v0 V0 e) HnfUr_ty wfe' wfe eq_refl
             (nf_normal Ur snUr') Hte_nf snNfSub).
  f_equal. symmetry. apply nf_stable_star.
  apply reduces_subst_right. apply nf_reduces.
Qed.

Lemma extract_typ_coerce_compat_small :
  forall e V0 v0 (Hv0 : has_type e v0 V0) (Hsmall : is_large e V0 -> False)
  Ur s (HUr : has_type (V0 :: e) Ur (sort_term s)) snUr snSub,
  infrastructure.compat
    (extract_typ (V0 :: e) Ur snUr)
    (extract_typ e (terms.subst v0 Ur) snSub).
Proof.
  intros e V0 v0 Hv0 Hsmall Ur s HUr snUr snSub.
  assert (wfe : well_formed e) by (eapply has_type_well_formed; exact Hv0).
  rewrite (extract_typ_small_subst_eq e V0 v0 Hv0 Hsmall wfe Ur s HUr snUr snSub).
  apply infrastructure.compat_refl.
Qed.

Lemma extract_typ_L_weaken : forall X, forall A p ctx f B, insert_in_environment A p ctx f ->
  has_type ctx X B -> well_formed f -> normal X ->
  extract_typ_L f (lift_rec 1 X p) =
    if is_large_dec (skipn p ctx) A
    then infrastructure.tlift 1 (type_index ctx p) (extract_typ_L ctx X)
    else extract_typ_L ctx X.
Proof.
  induction X as [s0 | n | X1 IHX1 X2 IHX2 | X1 IHX1 X2 IHX2 | X1 IHX1 X2 IHX2];
    intros A p ctx f B Hins HX wff Hnorm; simpl.
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
    assert (HnX1 : normal X1)
      by (intros u Hu; exact (Hnorm _ (abs_reduces_left X1 u Hu X2))).
    assert (HnX2 : normal X2)
      by (intros u Hu; exact (Hnorm _ (abs_reduces_right X2 u Hu X1))).
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
                  (ins_succ A p ctx f X1 Hins) HX2 wff' HnX2) as IH2.
    assert (Hskip : skipn (S p) (X1 :: ctx) = skipn p ctx) by reflexivity.
    rewrite Hskip in IH2.
    (* For normal X1: is_large ctx X1 <-> classifier X1 = true *)
    assert (Hcl_large : type_index (X1 :: ctx) (S p) =
              if classifier X1 then S (type_index ctx p) else type_index ctx p).
    { change (type_index (X1 :: ctx) (S p)) with
        (if is_large_dec ctx X1 then S (type_index ctx p) else type_index ctx p).
      destruct (classifier X1) eqn:Hcl.
      - destruct (is_large_dec ctx X1) as [_ | HNL]; [reflexivity |].
        exfalso. apply HNL. unfold is_large.
        rewrite <- (classifier_sound X1 ctx s1 HX1 Hcl). exact HX1.
      - destruct (is_large_dec ctx X1) as [HL | _]; [| reflexivity].
        exfalso. rewrite (snd (classifier_iff_is_large_nf X1 ctx s1 HX1 HnX1) HL) in Hcl.
        discriminate. }
    rewrite Hcl_large in IH2.
    destruct (classifier X1) eqn:Hcl.
    + rewrite (extract_kind_L_lift X1 1 p).
      destruct (is_large_dec (skipn p ctx) A) as [HlA | HnlA].
      * rewrite IH2. reflexivity.
      * rewrite IH2. reflexivity.
    + destruct (is_large_dec (skipn p ctx) A) as [HlA | HnlA].
      * rewrite IH2. reflexivity.
      * rewrite IH2. reflexivity.
  - (* app X1 X2 *)
    assert (HnX1 : normal X1)
      by (intros u Hu; exact (Hnorm _ (app_reduces_left X1 u Hu X2))).
    assert (HnX2 : normal X2)
      by (intros u Hu; exact (Hnorm _ (app_reduces_right X2 u Hu X1))).
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
    pose proof (IHX1 A p ctx f (prod V Ur) Hins Hu wff HnX1) as IH1.
    pose proof (IHX2 A p ctx f V Hins Hv wff HnX2) as IH2.
    destruct (type_expr ctx X1) eqn:He1; destruct (type_expr ctx X2) eqn:He2;
      destruct (is_large_dec (skipn p ctx) A) as [HlA | HnlA];
      try (rewrite IH1); try (rewrite IH2); reflexivity.
  - (* prod X1 X2 *)
    assert (HnX1 : normal X1)
      by (intros u Hu; exact (Hnorm _ (prod_reduces_left X1 u Hu X2))).
    assert (HnX2 : normal X2)
      by (intros u Hu; exact (Hnorm _ (prod_reduces_right X2 u Hu X1))).
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
        exfalso. apply HNL. unfold is_large.
        rewrite <- (classifier_sound X1 ctx s1 HX1 Hcl). exact HX1.
      - destruct (is_large_dec ctx X1) as [HL | _]; [| reflexivity].
        exfalso. rewrite (snd (classifier_iff_is_large_nf X1 ctx s1 HX1 HnX1) HL) in Hcl.
        discriminate. }
    destruct (classifier X1) eqn:Hcl.
    + rewrite (extract_kind_L_lift X1 1 p).
      pose proof (IHX2 A (S p) (X1 :: ctx) (lift_rec 1 X1 p :: f) (sort_term s2)
                    (ins_succ A p ctx f X1 Hins) HX2 wff' HnX2) as IH2.
      assert (Hskip : skipn (S p) (X1 :: ctx) = skipn p ctx) by reflexivity.
      rewrite Hskip in IH2. rewrite Hcl_large in IH2.
      destruct (is_large_dec (skipn p ctx) A) as [HlA | HnlA].
      * destruct (is_large_dec (skipn p ctx) A) as [_|Hc] in IH2; [| contradiction].
        rewrite IH2. reflexivity.
      * destruct (is_large_dec (skipn p ctx) A) as [Hc|_] in IH2; [contradiction |].
        rewrite IH2. reflexivity.
    + pose proof (IHX1 A p ctx f (sort_term s1) Hins HX1 wff HnX1) as IH1.
      pose proof (IHX2 A (S p) (X1 :: ctx) (lift_rec 1 X1 p :: f) (sort_term s2)
                    (ins_succ A p ctx f X1 Hins) HX2 wff' HnX2) as IH2.
      assert (Hskip : skipn (S p) (X1 :: ctx) = skipn p ctx) by reflexivity.
      rewrite Hskip in IH2. rewrite Hcl_large in IH2.
      destruct (is_large_dec (skipn p ctx) A) as [HlA | HnlA].
      * destruct (is_large_dec (skipn p ctx) A) as [_|Hc] in IH2; [|contradiction].
        rewrite IH1, IH2. reflexivity.
      * destruct (is_large_dec (skipn p ctx) A) as [Hc|_] in IH2; [contradiction|].
        rewrite IH1, IH2. reflexivity.
Qed.

(** Weakening [extract_typ_L] across [n] arbitrary bindings prepended on top of
    the (large-typed) source variable's own context: the extraction of the
    [n]-fold lift equals the extraction of the un-lifted term, tlifted by
    exactly the number of large bindings among the [n] prepended binders. *)
Lemma extract_typ_L_lift_n_large : forall n f g, n <= length f -> skipn n f = g ->
  well_formed f ->
  forall v0 V0 (Hv0 : has_type g v0 V0),
  forall snlift snv0,
  extract_typ_L f (nf (lift n v0) snlift)
    = infrastructure.tlift (type_index f n) 0 (extract_typ_L g (nf v0 snv0)).
Proof.
  induction n as [| n' IH]; intros f g Hlen Hskip wff v0 V0 Hv0 snlift snv0.
  - simpl in Hskip. subst g. rewrite type_index_zero. rewrite infrastructure.tlift_zero.
    revert snlift. rewrite lift_zero. intro snlift. f_equal. apply nf_pi.
  - destruct f as [| T f']; [simpl in Hlen; lia |].
    simpl in Hskip. simpl in Hlen.
    assert (Hlen' : n' <= length f') by lia.
    assert (wff' : well_formed f') by (exact (wf_tail T f' wff)).
    assert (Hty : has_type f' (lift n' v0) (lift n' V0))
      by (apply weakening_at with g; auto).
    assert (snlift' : strongly_normalizing (lift n' v0))
      by (exact (strong_normalization _ _ _ Hty)).
    pose proof (IH f' g Hlen' Hskip wff' v0 V0 Hv0 snlift' snv0) as IHeq.
    assert (HtyNf : has_type f' (nf (lift n' v0) snlift') (lift n' V0))
      by (eapply subject_reduction_theorem; [apply nf_reduces | exact Hty]).
    pose proof (extract_typ_L_weaken (nf (lift n' v0) snlift') T 0 f' (T :: f') (lift n' V0)
                  (ins_zero T f') HtyNf wff (nf_normal _ _)) as Hw.
    simpl (skipn 0 f') in Hw.
    change (lift_rec 1 (nf (lift n' v0) snlift') 0) with (lift 1 (nf (lift n' v0) snlift')) in Hw.
    assert (Hnf_eq : nf (lift (S n') v0) snlift = lift 1 (nf (lift n' v0) snlift')).
    { revert snlift. rewrite (simplify_lift v0 n'). intro snlift. unfold lift at 1.
      rewrite (nf_lift (lift n' v0) snlift' 1 0 snlift). reflexivity. }
    rewrite Hnf_eq.
    simpl (type_index (T :: f') (S n')).
    destruct (is_large_dec f' T) as [Hl | Hs].
    + rewrite Hw. rewrite IHeq. rewrite type_index_zero.
      rewrite infrastructure.tlift_tlift. f_equal; lia.
    + rewrite Hw. exact IHeq.
Qed.

(** [extract_typ] (the [nf]-normalizing extraction) inherits weakening from
    [extract_typ_L_weaken] via [nf_lift]. *)
Lemma extract_typ_weaken : forall X, forall A p ctx f B sn sn', insert_in_environment A p ctx f ->
  has_type ctx X B -> well_formed f ->
  extract_typ f (lift_rec 1 X p) sn' =
    if is_large_dec (skipn p ctx) A
    then infrastructure.tlift 1 (type_index ctx p) (extract_typ ctx X sn)
    else extract_typ ctx X sn.
Proof.
  intros X A p ctx f B sn sn' Hins HX wff.
  unfold extract_typ.
  rewrite (nf_lift X sn 1 p sn').
  apply (extract_typ_L_weaken (nf X sn) A p ctx f B Hins).
  - eapply subject_reduction_theorem; [apply nf_reduces | exact HX].
  - exact wff.
  - apply nf_normal.
Qed.

(** The type ascribed to a variable by [extract_lookup_type] (context lookup)
    agrees with extracting its [item_lift]-derived type directly via
    [extract_typ], provided that type is not itself large (the large case is a
    "type variable used as a term" and is never routed through
    [extract_lookup_type]).  This is [extract_typ_weaken] specialized to
    self-insertion at the head of the environment, composed along the lookup
    recursion. *)
Lemma extract_lookup_type_eq_extract_typ : forall e v u T0,
  nth_error e v = Some u -> T0 = lift (S v) u ->
  (is_large (skipn (S v) e) u -> False) ->
  forall (w: well_formed e) sn,
  extract_lookup_type e w v = extract_typ e T0 sn.
Proof.
  induction e as [|T e' IH]; intros v u T0 Hnth HT0 Hnl w sn.
  - destruct v; discriminate.
  - destruct v as [|v'].
    + simpl in Hnth. injection Hnth as <-. simpl in Hnl. subst T0.
      simpl (extract_lookup_type _ _ _).
      inversion_clear w as [|? ? s Ht].
      pose proof (extract_typ_weaken T T 0 e' (T :: e') (sort_term s)
                    (sn_of_binding T e' (wf_var e' T s Ht)) sn
                    (ins_zero T e') Ht (wf_var e' T s Ht)) as Hw.
      simpl (skipn 0 e') in Hw.
      destruct (is_large_dec e' T) as [Hl | Hs] in Hw.
      * exfalso. apply Hnl. exact Hl.
      * fold (lift 1 T) in Hw. rewrite Hw. apply extract_typ_pi.
    + simpl in Hnth. simpl in Hnl.
      subst T0.
      assert (HT0' : lift (S (S v')) u = lift 1 (lift (S v') u)) by apply simplify_lift.
      assert (il' : item_lift (lift (S v') u) e' v') by (exists u; [reflexivity | exact Hnth]).
      (* Simplify lookup BEFORE inverting w, so wf_tail T e' w stays intact *)
      simpl (extract_lookup_type (T :: e') w (S v')).
      inversion_clear w as [|? ? s Ht].
      pose (wfe' := wf_tail T e' (wf_var e' T s Ht)).
      destruct (well_formed_sort_lift v' e' (lift (S v') u) wfe' il') as [s0 Hs0].
      pose (sn0 := sn_of_type e' (var v') (lift (S v') u) (type_var e' wfe' v' (lift (S v') u) il')).
      pose proof (IH v' u (lift (S v') u) Hnth eq_refl Hnl wfe' sn0) as IHeq.
      unfold wfe' in IHeq.
      revert sn. rewrite HT0'.
      change (lift 1 (lift (S v') u)) with (lift_rec 1 (lift (S v') u) 0).
      intro sn.
      pose proof (extract_typ_weaken (lift (S v') u) T 0 e' (T :: e') (sort_term s0)
                    sn0 sn (ins_zero T e') Hs0 (wf_var e' T s Ht)) as Hw.
      simpl (skipn 0 e') in Hw.
      rewrite type_index_zero in Hw.
      rewrite Hw.
      rewrite (extract_lookup_type_pi e' (wf_tail T e' w) (wf_tail T e' (wf_var e' T s Ht)) v').
      destruct (is_large_dec e' T).
      * f_equal. exact IHeq.
      * exact IHeq.
Qed.

(** A substitution shrinks the context by exactly one binder. *)
Lemma substitute_length_e : forall t T n e f,
  substitute_in_environment t T n e f -> length e = S (length f).
Proof.
  intros t T n e f Hse. induction Hse.
  - reflexivity.
  - simpl. f_equal. exact IHHse.
Qed.

(** The step at a small binding increments [term_index]. *)
Lemma term_index_step_not_large : forall e v0 u,
  nth_error e v0 = Some u -> (is_large (skipn (S v0) e) u -> False) ->
  term_index e (S v0) = S (term_index e v0).
Proof.
  induction e as [| T e' IH]; intros v0 u Hnth Hsmall.
  - destruct v0; discriminate.
  - destruct v0 as [| v0'].
    + simpl in Hnth. assert (HuT: u = T) by congruence. subst u.
      simpl (term_index (T :: e') (S 0)).
      assert (term_index (T :: e') 0 = 0) by (destruct e'; reflexivity).
      destruct (is_large_dec e' T); [contradiction |].
      assert (term_index e' 0 = 0) by (destruct e'; reflexivity). lia.
    + simpl in Hnth. simpl. destruct (is_large_dec e' T).
      * exact (IH v0' u Hnth Hsmall).
      * f_equal. exact (IH v0' u Hnth Hsmall).
Qed.

(** A term variable's target index lies strictly below the substitution depth. *)
Lemma term_index_lt_of_item_small :
  forall e v0 t,
  well_formed e -> item_lift t e v0 -> (is_large e t -> False) ->
  forall n, v0 < n -> n <= length e -> term_index e v0 < term_index e n.
Proof.
  intros e v0 t Hwf [u Heq Hnth] Hsmall n Hlt Hlen.
  assert (Hstep : term_index e (S v0) = S (term_index e v0)).
  { apply term_index_step_not_large with u; [exact Hnth |].
    intro Hl. apply Hsmall. rewrite Heq.
    apply (is_large_item_lift e v0 u Hwf Hnth). exact Hl. }
  assert (Hmono : term_index e (S v0) <= term_index e n)
    by (apply term_index_mono; lia).
  lia.
Qed.

(** Above the substitution point (small removed binder), [term_index] decrements by one. *)
Lemma term_index_substitute_above :
  forall g v V (Hv: has_type g v V) (wfg: well_formed g),
  (is_large g V -> False) ->
  forall n e f,
  substitute_in_environment v V n e f ->
  well_formed e -> well_formed f -> skipn n f = g ->
  forall v0, n < v0 -> v0 <= length e ->
  term_index e v0 = S (term_index f (Nat.pred v0)).
Proof.
  intros g v V Hv wfg Hnlarge n e f Hse.
  induction Hse as [e0 | e0 f0 n' T Hse' IH].
  - intros wfe wff Hskip v0 Hlt Hlen.
    destruct v0 as [| v0']; [lia |]. simpl (Nat.pred (S v0')).
    assert (Hsmall : (is_large e0 V -> False)).
    { intro Hl. apply Hnlarge. simpl in Hskip. rewrite <- Hskip. exact Hl. }
    rewrite (term_index_succ_small V e0 v0' Hsmall). reflexivity.
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
    (* v0' > n' >= 0, so v0' = S v0'' *)
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

(** ** Target-language de Bruijn commutation *)

Lemma lift_lift_le : forall q ii jj kk pp,
  pp <= kk ->
  infrastructure.lift ii pp (infrastructure.lift jj kk q)
  = infrastructure.lift jj (ii + kk) (infrastructure.lift ii pp q).
Proof.
  induction q; intros ii jj kk pp Hle;
    try (simpl; f_equal; solve [auto | apply IHq; lia
      | replace (S (ii+kk)) with (ii + S kk) by lia; apply IHq; lia ]).
  simpl. destruct (le_gt_dec kk n); destruct (le_gt_dec pp n); simpl;
    repeat (match goal with |- context[le_gt_dec ?a ?b] => destruct (le_gt_dec a b) end);
    try reflexivity; try (f_equal; lia); lia.
Qed.

(** Target lift below the cutoff leaves a variable unchanged. *)
Lemma target_lift_var_lt : forall ii kk n, n < kk -> infrastructure.lift ii kk (syntax.var n) = syntax.var n.
Proof. intros. cbn [infrastructure.lift]. destruct (le_gt_dec kk n); [lia|reflexivity]. Qed.

(** Target term-lift and type-lift commute (disjoint index spaces). *)
Lemma lift_term_tlift_comm : forall q a b ii kk,
  infrastructure.lift ii kk (infrastructure.term_tlift a b q)
  = infrastructure.term_tlift a b (infrastructure.lift ii kk q).
Proof.
  induction q; intros a b ii kk; simpl; f_equal; auto.
  destruct (le_gt_dec kk n); reflexivity.
Qed.

(** Target term-lift commutes with term-substitution. *)
Lemma lift_subst_gen : forall q pp ii jj kk,
  infrastructure.lift ii (jj + kk) (infrastructure.subst pp kk q)
  = infrastructure.subst (infrastructure.lift ii jj pp) kk
      (infrastructure.lift ii (S (jj + kk)) q).
Proof.
  induction q; intros pp ii jj kk;
    try (cbn [infrastructure.lift infrastructure.subst]; f_equal; solve [ auto
      | rewrite <- lift_term_tlift_comm; apply IHq
      | replace (S (jj + kk)) with (jj + S kk) by lia; rewrite <- IHq; f_equal; lia ]).
  cbn [infrastructure.subst]. destruct (lt_eq_lt_dec kk n) as [[Hlt|Heq]|Hgt].
  - destruct n as [|n']; [lia|].
    repeat (cbn [infrastructure.lift infrastructure.subst]; match goal with
            | |- context[le_gt_dec ?a ?b] => destruct (le_gt_dec a b)
            | |- context[lt_eq_lt_dec ?a ?b] => destruct (lt_eq_lt_dec a b) as [[?|?]|?]
            end); cbn [infrastructure.lift infrastructure.subst];
      solve [ reflexivity | f_equal; lia | exfalso; lia ].
  - subst kk. rewrite target_lift_var_lt by lia. cbn [infrastructure.subst].
    destruct (lt_eq_lt_dec n n) as [[?|?]|?]; try lia.
    rewrite (lift_lift_le pp n ii jj 0 (Nat.le_0_l jj)). f_equal. lia.
  - repeat (cbn [infrastructure.lift infrastructure.subst]; match goal with
            | |- context[le_gt_dec ?a ?b] => destruct (le_gt_dec a b)
            | |- context[lt_eq_lt_dec ?a ?b] => destruct (lt_eq_lt_dec a b) as [[?|?]|?]
            end); cbn [infrastructure.lift infrastructure.subst];
      solve [ reflexivity | f_equal; lia | exfalso; lia ].
Qed.

(** Target term-lift commutes with type-substitution into a term. *)
Lemma lift_term_tsubst_gen : forall b AA ii kk jj,
  infrastructure.lift ii kk (infrastructure.term_tsubst AA jj b)
  = infrastructure.term_tsubst AA jj (infrastructure.lift ii kk b).
Proof.
  induction b; intros AA ii kk jj; simpl; f_equal; auto.
  destruct (le_gt_dec kk n); reflexivity.
Qed.

(** Specialization of [lift_subst_gen] at substitution cutoff 0 (the beta case). *)
Lemma lift_subst0 : forall b x i k,
  infrastructure.lift i k (infrastructure.subst x 0 b)
  = infrastructure.subst (infrastructure.lift i k x) 0 (infrastructure.lift i (S k) b).
Proof. intros. pose proof (lift_subst_gen b x i k 0) as H. rewrite Nat.add_0_r in H. exact H. Qed.

(** [sim] (hence [sim_star]) is preserved by target term-lifting. *)
Lemma sim_lift : forall s t, simulation.sim s t ->
  forall i k, simulation.sim (infrastructure.lift i k s) (infrastructure.lift i k t).
Proof.
  intros s t H. induction H; intros ii kk; cbn [infrastructure.lift];
    try (solve [ constructor; auto; try apply simulation.typ_sim_refl; auto ]).
  - rewrite lift_subst0. apply simulation.sim_beta.
  - rewrite lift_term_tsubst_gen. apply simulation.sim_tbeta.
  - destruct (le_gt_dec kk n); apply simulation.sim_var.
Qed.

(** [sim_star] is preserved by target term-lifting. *)
Lemma sim_star_lift : forall s t, simulation.sim_star s t ->
  forall i k, simulation.sim_star (infrastructure.lift i k s) (infrastructure.lift i k t).
Proof.
  intros s t H. induction H; intros ii kk.
  - apply simulation.sim_star_step. apply sim_lift. assumption.
  - apply simulation.sim_star_refl.
  - eapply simulation.sim_star_trans; eauto.
Qed.

(** Same-cutoff lift composition. *)
Lemma lift_lift_same : forall q a b k,
  infrastructure.lift a k (infrastructure.lift b k q) = infrastructure.lift (a + b) k q.
Proof.
  induction q; intros a b k; try (simpl; f_equal; solve [auto | apply IHq]).
  simpl. destruct (le_gt_dec k n); simpl;
    repeat (match goal with |- context[le_gt_dec ?a ?b] => destruct (le_gt_dec a b) end);
    try reflexivity; try (f_equal; lia); lia.
Qed.

(** Target type-lifting fixes [dyn_token] (it is type-closed). *)
Lemma term_tlift_dyn_token : forall i k, infrastructure.term_tlift i k dyn_token = dyn_token.
Proof.
  intros. Transparent dyn_token. unfold dyn_token, dyn_fun. cbn [infrastructure.term_tlift].
  reflexivity. Opaque dyn_token.
Qed.

(** Type-lifting a [coerce] simulates (down to) type-lifting its scrutinee. *)
Lemma coerce_term_tlift_sim_l : forall s t A B i k,
  simulation.sim_star (infrastructure.term_tlift i k s) t ->
  simulation.sim_star (infrastructure.term_tlift i k (coerce s A B)) t.
Proof.
  intros s t A B i k H. unfold coerce.
  destruct (syntax.typ_eq_dec A B).
  - cbn [infrastructure.term_tlift]. exact H.
  - destruct (infrastructure.compat_dec A B);
    cbn [infrastructure.term_tlift].
    + eapply simulation.sim_star_trans;
        [ apply simulation.sim_star_step; apply simulation.sim_left_sc;
          apply simulation.sim_refl |].
      exact H.
    + eapply simulation.sim_star_trans;
        [ apply simulation.sim_star_step; apply simulation.sim_blame |].
      exact H.
Qed.

(** [sim_star (term_tlift s) s] lifts through a coerce: both sides share the same A,B
    so the ¬compat case gives blame on BOTH sides. *)
Lemma coerce_self_tlift_sim : forall s A B i k,
  simulation.sim_star (infrastructure.term_tlift i k s) s ->
  simulation.sim_star (infrastructure.term_tlift i k (coerce s A B)) (coerce s A B).
Proof.
  intros s A B i k H. unfold coerce.
  destruct (syntax.typ_eq_dec A B) as [-> | Hne].
  - cbn [infrastructure.term_tlift]. exact H.
  - destruct (infrastructure.compat_dec A B) as [Hc | Hnc]; cbn [infrastructure.term_tlift].
    + eapply simulation.sim_star_trans.
      * apply simulation.sim_star_step. apply simulation.sim_left_sc. apply simulation.sim_refl.
      * eapply simulation.sim_star_trans.
        -- exact H.
        -- apply simulation.sim_star_step. apply simulation.sim_right_sc. apply simulation.sim_refl.
    + apply simulation.sim_star_refl.
Qed.

(** [sim_star (term_tsubst s)] lifts through a coerce: the compat check uses the
    original A,B so both sides share the same coerce shell. *)
Lemma coerce_self_tsubst_sim : forall e A B AA k,
  simulation.sim_star (infrastructure.term_tsubst AA k e) e ->
  simulation.sim_star (infrastructure.term_tsubst AA k (coerce e A B)) (coerce e A B).
Proof.
  intros e A B AA k H. unfold coerce.
  destruct (syntax.typ_eq_dec A B) as [-> | Hne].
  - cbn [infrastructure.term_tsubst]. exact H.
  - destruct (infrastructure.compat_dec A B) as [Hc | Hnc]; cbn [infrastructure.term_tsubst].
    + eapply simulation.sim_star_trans.
      * apply simulation.sim_star_step. apply simulation.sim_left_sc. apply simulation.sim_refl.
      * eapply simulation.sim_star_trans.
        -- exact H.
        -- apply simulation.sim_star_step. apply simulation.sim_right_sc. apply simulation.sim_refl.
    + apply simulation.sim_star_refl.
Qed.

(** Type-lifting is invisible to [sim_star] on extractions (it only touches type
    annotations, which every [sim_star] congruence ignores). *)
Lemma term_tlift_extract_sim : forall e u U (H: has_type e u U) i k,
  simulation.sim_star (infrastructure.term_tlift i k (extract e u U H))
    (extract e u U H).
Proof.
  fix IH 4. intros e u U H i k.
  destruct H as [ e0 w0 | e0 w0
                | e0 w0 v T0 il
                | e0 T0 s1 HT M U s2 HU HM
                | e0 v0 V0 Hv u Ur Hu
                | e0 T0 s1 HT U s2 HU
                | e0 t0 U0 V0 Htu Hconv s0 HV ].
  - cbn [extract]. rewrite term_tlift_dyn_token. apply simulation.sim_star_refl.
  - cbn [extract]. rewrite term_tlift_dyn_token. apply simulation.sim_star_refl.
  - (* type_var *)
    cbn [extract].
    destruct (is_large_dec e0 T0) as [Hlarge | Hsmall].
    + apply coerce_self_tlift_sim. cbn [infrastructure.term_tlift]. apply simulation.sim_star_refl.
    + destruct il as [u0 Heq0 Hnth0].
      assert (Hnu : is_large (skipn (S v) e0) u0 -> False)
        by (intro Hil; apply Hsmall; rewrite Heq0;
            exact (snd (is_large_item_lift e0 v u0 w0 Hnth0) Hil)).
      pose (snT := sn_of_type e0 (terms.var v) T0
                     (type_var e0 w0 v T0 (existT2 _ _ u0 Heq0 Hnth0))).
      rewrite (extract_lookup_type_eq_extract_typ e0 v u0 T0 Hnth0 Heq0 Hnu w0 snT).
      rewrite coerce_id.
      cbn [infrastructure.term_tlift]. apply simulation.sim_star_refl.
  - (* type_abs *)
    cbn [extract].
    destruct (is_large_dec e0 T0).
    + cbn [infrastructure.term_tlift]. apply sim_star_tabs_gen. apply (IH _ _ _ HM).
    + cbn [infrastructure.term_tlift]. apply sim_star_abs_gen. apply (IH _ _ _ HM).
  - (* type_app *)
    cbn [extract].
    destruct (is_large_dec e0 V0).
    + cbn [infrastructure.term_tlift].
      apply sim_star_tapp_gen. apply (IH _ _ _ Hu).
    + apply coerce_self_tlift_sim. cbn [infrastructure.term_tlift].
      apply sim_star_app; [apply (IH _ _ _ Hu) | apply (IH _ _ _ Hv)].
  - cbn [extract]. rewrite term_tlift_dyn_token. apply simulation.sim_star_refl.
  - (* type_conv *)
    cbn [extract].
    apply coerce_self_tlift_sim. apply (IH _ _ _ Htu).
Qed.

(** Target lifting by zero is the identity. *)
Lemma target_lift0 : forall q k, infrastructure.lift 0 k q = q.
Proof.
  induction q; intros k; simpl; f_equal; auto.
  destruct (le_gt_dec k n); reflexivity.
Qed.

(** [coerce (blame p) A B] reduces to some blame term. *)
Lemma coerce_blame_reduces : forall p A B t,
  simulation.sim_star (coerce (syntax.blame p) A B) t.
Proof.
  intros p A B t. unfold coerce.
  destruct (syntax.typ_eq_dec A B) as [-> | Hne].
  - apply simulation.sim_star_step. apply simulation.sim_blame.
  - destruct (infrastructure.compat_dec A B).
    + apply simulation.sim_star_step. apply simulation.sim_left_sc. apply simulation.sim_blame.
    + apply simulation.sim_star_step. apply simulation.sim_blame.
Qed.

(** Target lift pushes through a [coerce] (type annotations are unaffected). *)
Lemma lift_coerce : forall i k s A B,
  infrastructure.lift i k (coerce s A B) = coerce (infrastructure.lift i k s) A B.
Proof.
  intros. unfold coerce.
  destruct (syntax.typ_eq_dec A B); [reflexivity|].
  destruct (infrastructure.compat_dec A B); simpl; reflexivity.
Qed.

(** Target term-lift push-through equalities (all definitional). *)
Lemma lift_tabs : forall i k K s,
  infrastructure.lift i k (syntax.tabs K s) = syntax.tabs K (infrastructure.lift i k s).
Proof. reflexivity. Qed.

Lemma lift_abs : forall i k A s,
  infrastructure.lift i k (syntax.abs A s) = syntax.abs A (infrastructure.lift i (S k) s).
Proof. reflexivity. Qed.

Lemma lift_app_t : forall i k s t,
  infrastructure.lift i k (syntax.app s t)
  = syntax.app (infrastructure.lift i k s) (infrastructure.lift i k t).
Proof. reflexivity. Qed.

Lemma lift_tapp_t : forall i k s A,
  infrastructure.lift i k (syntax.tapp s A) = syntax.tapp (infrastructure.lift i k s) A.
Proof. reflexivity. Qed.

Lemma lift_blame_t : forall i k q,
  infrastructure.lift i k (syntax.blame q) = syntax.blame q.
Proof. reflexivity. Qed.

Lemma lift_var_t : forall i k n,
  infrastructure.lift i k (syntax.var n)
  = syntax.var (if le_gt_dec k n then i + n else n).
Proof. intros. simpl. destruct (le_gt_dec k n); reflexivity. Qed.

(** The insertion depth is within the source context's length. *)
Lemma insert_le_length : forall A p e f, insert_in_environment A p e f -> p <= length e.
Proof. intros A p e f H. induction H; simpl; lia. Qed.

(** [term_index] at index 0 is 0 in any context. *)
Lemma term_index_zero : forall e, term_index e 0 = 0.
Proof. destruct e; reflexivity. Qed.

(** Past a small binder at position [v], [term_index] increments by one. *)
Lemma term_index_succ_small_at : forall e v u,
  nth_error e v = Some u -> (is_large (skipn (S v) e) u -> False) ->
  term_index e (S v) = S (term_index e v).
Proof.
  induction e as [|T e' IH]; intros v u Hnth Hsmall.
  - destruct v; discriminate.
  - destruct v as [|v'].
    + simpl in Hnth. injection Hnth as <-. simpl in Hsmall.
      simpl (term_index (T :: e') 1).
      destruct (is_large_dec e' T) as [Hl|Hs];
        [exfalso; apply Hsmall; exact Hl |].
      rewrite !term_index_zero. reflexivity.
    + simpl in Hnth. simpl in Hsmall.
      simpl (term_index (T :: e') (S (S v'))). simpl (term_index (T :: e') (S v')).
      rewrite (IH v' u Hnth Hsmall).
      destruct (is_large_dec e' T); reflexivity.
Qed.

(** A small (term-level) variable strictly below the insertion point has a
    strictly smaller [term_index]: the small binder it names is itself counted in
    the index at the (higher) insertion point. *)
Lemma term_index_small_lt : forall e v u,
  nth_error e v = Some u -> (is_large (skipn (S v) e) u -> False) ->
  forall p, v < p -> term_index e v < term_index e p.
Proof.
  intros e v u Hnth Hsmall p Hlt.
  apply Nat.lt_le_trans with (term_index e (S v)).
  - rewrite (term_index_succ_small_at e v u Hnth Hsmall). lia.
  - apply term_index_mono. lia.
Qed.

(** Above the insertion point, a lifted item is preserved (one index deeper). *)
Lemma item_lift_insert_ge : forall A p e f, insert_in_environment A p e f ->
  forall v T0, p <= v -> item_lift T0 e v -> item_lift (lift_rec 1 T0 p) f (S v).
Proof.
  intros A p e f Hins v T0 Hle il. destruct il as [x Heq Hnth].
  exists x.
  - rewrite Heq. unfold lift. rewrite simplify_lift_rec; simpl;
      auto with coc core arith datatypes; lia.
  - apply insert_item_ge with A p e; auto with coc core arith datatypes.
Qed.

(** Single-binder weakening commutes with extraction up to [sim_star] (term-variable indices shift accordingly; type binders leave them fixed). *)
Lemma extract_weaken1 :
  forall ctx u U (Hu: has_type ctx u U),
  forall p A f sh
    (Hins: insert_in_environment A p ctx f)
    (wfctx: well_formed ctx) (wff: well_formed f)
    (Hsh: sh = if is_large_dec (skipn p ctx) A then 0 else 1)
    (Hlift: has_type f (lift_rec 1 u p) (lift_rec 1 U p)),
    simulation.sim_star (infrastructure.lift sh (term_index ctx p) (extract ctx u U Hu))
             (extract f (lift_rec 1 u p) (lift_rec 1 U p) Hlift).
Proof.
  fix IH 4.
  intros ctx u U Hu.
  dependent destruction Hu; intros p A f sh Hins wfctx wff Hsh Hlift.
  - (* type_prop *)
    cbn [extract]. rewrite lift_dyn_token.
    exact (extract_deriv_indep _ _ _ (type_prop f wff) Hlift).
  - (* type_set *)
    cbn [extract]. rewrite lift_dyn_token.
    exact (extract_deriv_indep _ _ _ (type_set f wff) Hlift).
  - (* type_var *)
    cbn [extract].
    destruct (is_large_dec e t) as [Hlarge_t | Hsmall_t].
    + (* large: a type variable used as a term extracts to blame *)
      rewrite lift_coerce. apply coerce_sim_star_l. rewrite lift_blame_t.
      apply simulation.sim_star_step. apply simulation.sim_blame.
    + (* small: the coerce is the identity on the variable; index arithmetic *)
      destruct (well_formed_sort_lift v e t w i) as [st HT_t].
      assert (Hnl_f : is_large f (lift_rec 1 t p) -> False)
        by (intro Hl; apply Hsmall_t;
            exact (snd (is_large_insert A p e f Hins wff t st HT_t) Hl)).
      (* collapse the source-side coerce to the bare variable *)
      destruct i as [x Heqx Hnthx].
      assert (Hnu_e : is_large (skipn (S v) e) x -> False)
        by (intro H; apply Hsmall_t; rewrite Heqx;
            exact (snd (is_large_item_lift e v x w Hnthx) H)).
      pose (sn_e := sn_of_type e (terms.var v) t
                      (type_var e w v t (existT2 _ _ x Heqx Hnthx))).
      rewrite (extract_lookup_type_eq_extract_typ e v x t Hnthx Heqx Hnu_e w sn_e).
      rewrite coerce_id.
      destruct (le_gt_dec p v) as [Hpv | Hvp].
      * (* p <= v: lifted variable is [S v] *)
        pose (il' := item_lift_insert_ge A p e f Hins v t Hpv
                       (existT2 _ _ x Heqx Hnthx)).
        revert Hlift. rewrite (lift_ref_ge 1 v p Hpv). intro Hlift.
        eapply simulation.sim_star_trans;
          [| exact (extract_deriv_indep _ _ _
                      (type_var f wff (S v) (lift_rec 1 t p) il') Hlift)].
        cbn [extract].
        destruct (is_large_dec f (lift_rec 1 t p)) as [Habs | _]; [contradiction |].
        destruct il' as [x_f Heqx_f Hnthx_f].
        assert (Hnu_f : is_large (skipn (S (S v)) f) x_f -> False)
          by (intro H; apply Hnl_f; rewrite Heqx_f;
              exact (snd (is_large_item_lift f (S v) x_f wff Hnthx_f) H)).
        pose (sn_f := sn_of_type f (terms.var (S v)) (lift_rec 1 t p)
                        (type_var f wff (S v) _ (existT2 _ _ x_f Heqx_f Hnthx_f))).
        rewrite (extract_lookup_type_eq_extract_typ f (S v) x_f (lift_rec 1 t p)
                   Hnthx_f Heqx_f Hnu_f wff sn_f).
        rewrite coerce_id.
        rewrite lift_var_t.
        destruct (le_gt_dec (term_index e p) (term_index e v)) as [_ | Hgt];
          [| exfalso; pose proof (term_index_mono e p v); lia].
        destruct (is_large_dec (skipn p e) A) as [HlA | HsA]; subst sh.
        -- rewrite (term_index_insert_ge_large A p e f Hins wfctx wff HlA v Hpv).
           simpl. apply simulation.sim_star_refl.
        -- rewrite (term_index_insert_ge_small A p e f Hins wfctx wff HsA v Hpv).
           simpl. apply simulation.sim_star_refl.
      * (* p > v: variable index unchanged *)
        pose (il' := insert_item_lt A p e f Hins v Hvp t (existT2 _ _ x Heqx Hnthx)).
        revert Hlift. rewrite (lift_ref_lt 1 v p Hvp). intro Hlift.
        eapply simulation.sim_star_trans;
          [| exact (extract_deriv_indep _ _ _
                      (type_var f wff v (lift_rec 1 t p) il') Hlift)].
        cbn [extract].
        destruct (is_large_dec f (lift_rec 1 t p)) as [Habs | _]; [contradiction |].
        destruct il' as [x_f Heqx_f Hnthx_f].
        assert (Hnu_f : is_large (skipn (S v) f) x_f -> False)
          by (intro H; apply Hnl_f; rewrite Heqx_f;
              exact (snd (is_large_item_lift f v x_f wff Hnthx_f) H)).
        pose (sn_f := sn_of_type f (terms.var v) (lift_rec 1 t p)
                        (type_var f wff v _ (existT2 _ _ x_f Heqx_f Hnthx_f))).
        rewrite (extract_lookup_type_eq_extract_typ f v x_f (lift_rec 1 t p)
                   Hnthx_f Heqx_f Hnu_f wff sn_f).
        rewrite coerce_id.
        rewrite lift_var_t.
        rewrite (term_index_insert_lt A p e f Hins wfctx wff v Hvp).
        destruct (le_gt_dec (term_index e p) (term_index e v)) as [Hle | _].
        -- exfalso.
           pose proof (term_index_small_lt e v x Hnthx Hnu_e p Hvp). lia.
        -- apply simulation.sim_star_refl.
  - (* type_abs *)
    cbn [extract].
    pose (HT' := has_type_weakening_weak A e T (sort_term s1) Hu1 p f Hins wff).
    change (lift_rec 1 (sort_term s1) p) with (sort_term s1) in HT'.
    pose (wff' := wf_var f (lift_rec 1 T p) s1 HT').
    pose (Hins' := ins_succ A p e f T Hins).
    pose (Hu2' := has_type_weakening_weak A (T :: e) U (sort_term s2) Hu2 (S p)
                    (lift_rec 1 T p :: f) Hins' wff').
    change (lift_rec 1 (sort_term s2) (S p)) with (sort_term s2) in Hu2'.
    pose (Hu3' := has_type_weakening_weak A (T :: e) M U Hu3 (S p)
                    (lift_rec 1 T p :: f) Hins' wff').
    eapply simulation.sim_star_trans;
      [| exact (extract_deriv_indep _ _ _
                  (type_abs f (lift_rec 1 T p) s1 HT'
                     (lift_rec 1 M (S p)) (lift_rec 1 U (S p)) s2 Hu2' Hu3') Hlift)].
    cbn [extract].
    destruct (is_large_dec e T) as [Hlarge_e | Hsmall_e];
      destruct (is_large_dec f (lift_rec 1 T p)) as [Hlarge_f | Hsmall_f].
    + rewrite lift_tabs. apply sim_star_tabs_gen.
      rewrite <- (term_index_succ_large T e p Hlarge_e).
      exact (IH (T :: e) M U Hu3 (S p) A (lift_rec 1 T p :: f) sh Hins'
               (wf_var e T s1 Hu1) wff' Hsh Hu3').
    + exfalso. apply Hsmall_f.
      exact (fst (is_large_insert A p e f Hins wff T s1 Hu1) Hlarge_e).
    + exfalso. apply Hsmall_e.
      exact (snd (is_large_insert A p e f Hins wff T s1 Hu1) Hlarge_f).
    + rewrite lift_abs. apply sim_star_abs_gen.
      rewrite <- (term_index_succ_small T e p Hsmall_e).
      exact (IH (T :: e) M U Hu3 (S p) A (lift_rec 1 T p :: f) sh Hins'
               (wf_var e T s1 Hu1) wff' Hsh Hu3').
  - (* type_app *)
    cbn [extract].
    pose (Hv' := has_type_weakening_weak A e v V Hu1 p f Hins wff).
    pose (Hu'' := has_type_weakening_weak A e u (terms.prod V Ur) Hu2 p f Hins wff).
    change (lift_rec 1 (terms.prod V Ur) p) with
      (terms.prod (lift_rec 1 V p) (lift_rec 1 Ur (S p))) in Hu''.
    (* invert the product type of [u] to recover the sorts of [V] and [Ur] *)
    destruct (type_case e u (terms.prod V Ur) Hu2) as [[su Hsu] | Hbad]; [| discriminate Hbad].
    destruct (inversion_has_type_prod_t e V Ur (sort_term su) Hsu)
      as [s1V [s2V [[HV HUr] _]]].
    pose (HV' := has_type_weakening_weak A e V (sort_term s1V) HV p f Hins wff).
    change (lift_rec 1 (sort_term s1V) p) with (sort_term s1V) in HV'.
    pose (wffV := wf_var f (lift_rec 1 V p) s1V HV').
    pose (HUr' := has_type_weakening_weak A (V :: e) Ur (sort_term s2V) HUr (S p)
                    (lift_rec 1 V p :: f) (ins_succ A p e f V Hins) wffV).
    change (lift_rec 1 (sort_term s2V) (S p)) with (sort_term s2V) in HUr'.
    pose (Happ := type_app f (lift_rec 1 v p) (lift_rec 1 V p) Hv'
                    (lift_rec 1 u p) (lift_rec 1 Ur (S p)) Hu'').
    eapply simulation.sim_star_trans;
      [| apply (extract_deriv_indep_conv _ _ _ _ Happ Hlift);
         rewrite <- distribute_lift_subst; apply refl_convertible].
    unfold Happ. cbn [extract].
    destruct (is_large_dec e V) as [Hlarge_e | Hsmall_e];
      destruct (is_large_dec f (lift_rec 1 V p)) as [Hlarge_f | Hsmall_f].
    + (* large/large: raw tapp on both sides (no coerce) *)
      rewrite lift_tapp_t. apply sim_star_tapp_gen.
      exact (IH e u (terms.prod V Ur) Hu2 p A f sh Hins wfctx wff Hsh Hu'').
    + exfalso. apply Hsmall_f.
      exact (fst (is_large_insert A p e f Hins wff V s1V HV) Hlarge_e).
    + exfalso. apply Hsmall_e.
      exact (snd (is_large_insert A p e f Hins wff V s1V HV) Hlarge_f).
    + (* small/small: strip LHS coerce, compat closes the f-side coerce *)
      rewrite lift_coerce, lift_app_t. apply coerce_sim_star_l.
      eapply simulation.sim_star_trans.
      * apply sim_star_app;
          [ exact (IH e u (terms.prod V Ur) Hu2 p A f sh Hins wfctx wff Hsh Hu'')
          | exact (IH e v V Hu1 p A f sh Hins wfctx wff Hsh Hv') ].
      * apply sim_star_self_coerce_compat.
        exact (extract_typ_coerce_compat_small f (lift_rec 1 V p) (lift_rec 1 v p) Hv'
                 Hsmall_f (lift_rec 1 Ur (S p)) s2V HUr' _ _).
  - (* type_prod *)
    cbn [extract]. rewrite lift_dyn_token.
    pose (HT' := has_type_weakening_weak A e T (sort_term s1) Hu1 p f Hins wff).
    change (lift_rec 1 (sort_term s1) p) with (sort_term s1) in HT'.
    pose (wff' := wf_var f (lift_rec 1 T p) s1 HT').
    pose (HU' := has_type_weakening_weak A (T :: e) U (sort_term s2) Hu2 (S p)
                   (lift_rec 1 T p :: f) (ins_succ A p e f T Hins) wff').
    change (lift_rec 1 (sort_term s2) (S p)) with (sort_term s2) in HU'.
    exact (extract_deriv_indep _ _ _
             (type_prod f (lift_rec 1 T p) s1 HT' (lift_rec 1 U (S p)) s2 HU') Hlift).
  - (* type_conv *)
    cbn [extract]. rewrite lift_coerce.
    destruct (type_case e t U Hu1) as [[su Hsu] | Hkind];
      [| subst U; exfalso;
         exact (inversion_has_type_convertible_kind e V (sort_term s)
                  (sym_convertible _ _ c) Hu2)].
    pose (Htu' := has_type_weakening_weak A e t U Hu1 p f Hins wff).
    pose (HV' := has_type_weakening_weak A e V (sort_term s) Hu2 p f Hins wff).
    change (lift_rec 1 (sort_term s) p) with (sort_term s) in HV'.
    pose proof (IH e t U Hu1 p A f sh Hins wfctx wff Hsh Htu') as IHt.
    eapply simulation.sim_star_trans;
      [| exact (extract_deriv_indep _ _ _
                  (type_conv f (lift_rec 1 t p) (lift_rec 1 U p) (lift_rec 1 V p) Htu'
                     (convertible_convertible_lift U V 1 p c) s HV') Hlift)].
    cbn [extract].
    rewrite (extract_typ_weaken U A p e f (sort_term su)
               (sn_of_type e t U Hu1) _ Hins Hsu wff).
    rewrite (extract_typ_weaken V A p e f (sort_term s)
               (strong_normalization e V (sort_term s) Hu2) _ Hins Hu2 wff).
    destruct (is_large_dec (skipn p e) A) as [HlA | HsA].
    + apply coerce_sim_star_both_tlift. exact IHt.
    + apply coerce_sim_star_both. exact IHt.
Qed.

(** Block weakening (a whole inserted context) commutes with extraction up to [sim_star], iterating [extract_weaken1]. *)
Lemma extract_weaken_block :
  forall n g v V (Hv: has_type g v V) (wfg: well_formed g),
  forall f (wff: well_formed f) (Hskip: skipn n f = g) (Hlen: n <= length f)
    (Hlift: has_type f (lift_rec n v 0) (lift_rec n V 0)),
    simulation.sim_star
      (infrastructure.lift (term_index f n) 0 (extract g v V Hv))
      (extract f (lift_rec n v 0) (lift_rec n V 0) Hlift).
Proof.
  induction n as [|n' IHn]; intros g v V Hv wfg f wff Hskip Hlen Hlift.
  - (* n = 0 *)
    simpl in Hskip. subst g.
    assert (T0f : term_index f 0 = 0) by (destruct f; reflexivity).
    rewrite T0f. rewrite target_lift0.
    revert Hlift. rewrite !lift_rec_zero. intro Hlift.
    apply extract_deriv_indep.
  - (* n = S n' *)
    destruct f as [|A f']; [simpl in Hlen; lia|].
    simpl in Hskip.
    assert (Hlen' : n' <= length f') by (simpl in Hlen; lia).
    dependent destruction wff. rename h into HA. rename s into sA.
    assert (wff' : well_formed f') by (exact (has_type_t_well_formed_t _ _ _ HA)).
    assert (Hlift' : has_type f' (lift_rec n' v 0) (lift_rec n' V 0))
      by (exact (weakening_at_t n' f' g Hskip Hlen' v V Hv wff')).
    (* massage the given Hlift to the (S n') = 1 ∘ n' shape *)
    assert (Heqv : lift_rec (S n') v 0 = lift_rec 1 (lift_rec n' v 0) 0)
      by (change (lift_rec (S n') v 0) with (lift (S n') v);
          change (lift_rec 1 (lift_rec n' v 0) 0) with (lift 1 (lift n' v));
          apply simplify_lift).
    assert (HeqV : lift_rec (S n') V 0 = lift_rec 1 (lift_rec n' V 0) 0)
      by (change (lift_rec (S n') V 0) with (lift (S n') V);
          change (lift_rec 1 (lift_rec n' V 0) 0) with (lift 1 (lift n' V));
          apply simplify_lift).
    revert Hlift. rewrite Heqv, HeqV. intro Hlift.
    (* term index: term_index (A::f') (S n') = sh + term_index f' n' *)
    pose (sh := if is_large_dec (skipn 0 f') A then 0 else 1).
    assert (Hidx : term_index (A :: f') (S n') = sh + term_index f' n').
    { unfold sh. simpl (skipn 0 f'). cbn [term_index].
      destruct (is_large_dec f' A); reflexivity. }
    rewrite Hidx.
    rewrite <- lift_lift_same.
    eapply simulation.sim_star_trans.
    + apply sim_star_lift.
      exact (IHn g v V Hv wfg f' wff' Hskip Hlen' Hlift').
    + assert (T0f' : term_index f' 0 = 0) by (destruct f'; reflexivity).
      pose proof (extract_weaken1 f' (lift_rec n' v 0) (lift_rec n' V 0) Hlift'
                    0 A (A :: f') sh (ins_zero A f')
                    (wff') (wf_var f' A sA HA)
                    eq_refl Hlift) as Hw1.
      rewrite T0f' in Hw1. exact Hw1.
Qed.

(** Weakening commutation for [extract], specialised to the hit case of the
    substitution lemma.  The substituted value [v] lives in [g = skipn n f]; the
    context [f] is [g] with a block of [n] binders inserted on top ([m] of which are
    type-level, [n - m] term-level, per [Hti]).  Erasing the weakened value
    [lift n v] in [f] is simulated by the extraction of [v] in [g], target-weakened by
    the block: [lift (n-m) 0] for the term binders and [term_tlift m 0] for the type
    binders.  (Both wrappers are absorbed by [sim] at every node except term
    variables, where the index arithmetic is governed by [term_index] under
    insertion — see [term_index_insert_lt/ge_large/ge_small].) *)
Lemma extract_weaken_hit :
  forall n m g v V (Hv: has_type g v V) (wfg: well_formed g),
  (is_large g V -> False) -> m <= n ->
  forall e f (Hse: substitute_in_environment v V n e f)
    (wfe: well_formed e) (wff: well_formed f) (Hskip: skipn n f = g)
    (Hti: term_index e n = n - m)
    t (i: item_lift t e n)
    (Hsub: has_type f (terms.lift n v) (terms.subst_rec v t n)),
    simulation.sim_star
      (infrastructure.lift (n - m) 0
         (infrastructure.term_tlift m 0 (extract g v V Hv)))
      (extract f (terms.lift n v) (terms.subst_rec v t n) Hsub).
Proof.
  intros n m g v V Hv wfg Hnlarge Hle e f Hse wfe wff Hskip Hti t i Hsub.
  assert (Ht : t = terms.lift (S n) V).
  { destruct i as [u0 Heq0 Hnth0]. rewrite (nth_substitute_eq v V n e f Hse) in Hnth0.
    injection Hnth0 as <-. exact Heq0. }
  assert (Htype : terms.subst_rec v t n = terms.lift n V)
    by (rewrite Ht; apply simplify_subst; lia).
  assert (Hfn : term_index f n = n - m)
    by (rewrite <- Hti; exact (term_index_substitute_top g v V Hv n e f Hse wfe wff Hskip)).
  assert (Hlen : n <= length f) by (exact (substitute_length_le v V n e f Hse)).
  assert (Hlift_b : has_type f (terms.lift_rec n v 0) (terms.lift_rec n V 0)).
  { change (terms.lift_rec n v 0) with (terms.lift n v).
    change (terms.lift_rec n V 0) with (terms.lift n V).
    rewrite <- Htype. exact Hsub. }
  eapply simulation.sim_star_trans.
  - apply sim_star_lift. apply (term_tlift_extract_sim g v V Hv m 0).
  - rewrite <- Hfn.
    eapply simulation.sim_star_trans;
      [ exact (extract_weaken_block n g v V Hv wfg f wff Hskip Hlen Hlift_b) |].
    apply (extract_deriv_indep_conv f (terms.lift n v)
             (terms.lift_rec n V 0) (terms.subst_rec v t n) Hlift_b Hsub).
    rewrite Htype. apply refl_convertible.
Qed.

(** Generalized substitution commutation for [extract] (small/term-level case).
    Parameters: [n] = source depth of the substituted variable,
    [m] = count of large (type-level) binders passed so far.
    Target term-level depth = [n - m]. *)
Lemma extract_subst_sim_gen :
  forall n m g v V (Hv: has_type g v V) (wfg: well_formed g),
  (is_large g V -> False) -> m <= n ->
  forall e u Ur (HM: has_type e u Ur)
    f (Hse: substitute_in_environment v V n e f) (wff: well_formed f)
    (Hskip: skipn n f = g)
    (Hti: term_index e n = n - m),
  forall (Hsub: has_type f (terms.subst_rec v u n) (terms.subst_rec v Ur n)),
  simulation.sim_star
    (infrastructure.subst (infrastructure.term_tlift m 0 (extract g v V Hv)) (n - m)
       (extract e u Ur HM))
    (extract f (terms.subst_rec v u n) (terms.subst_rec v Ur n) Hsub).
Proof.
  fix IH 13.
  intros n m g v V Hv wfg Hnl Hle e u Ur HM.
  dependent destruction HM; intros f Hse wff Hskip Hti Hsub.
  - (* prop *)
    cbn [extract]. rewrite subst_dyn_token.
    change (terms.subst_rec v (sort_term prop) n) with (sort_term prop) in Hsub |- *.
    change (terms.subst_rec v (sort_term terms.kind) n) with (sort_term terms.kind) in Hsub |- *.
    exact (extract_deriv_indep _ _ _ (type_prop f wff) Hsub).
  - (* set *)
    cbn [extract]. rewrite subst_dyn_token.
    change (terms.subst_rec v (sort_term set) n) with (sort_term set) in Hsub |- *.
    change (terms.subst_rec v (sort_term terms.kind) n) with (sort_term terms.kind) in Hsub |- *.
    exact (extract_deriv_indep _ _ _ (type_set f wff) Hsub).
  - (* var *)
    rename t into Tv. rename i into il. rename w into wfe_t.
    cbn [extract].
    destruct (is_large_dec e Tv) as [Hlarge_e | Hsmall_e].
    + rewrite subst_coerce. apply coerce_sim_star_l. rewrite subst_blame_t.
      apply simulation.sim_star_step. apply simulation.sim_blame.
    + assert (Hsmall_f : (is_large f (terms.subst_rec v Tv n) -> False)).
      { intro Hlf. apply Hsmall_e.
        exact (is_large_substitute_inv_prop g v V Hv e Tv
                 (well_formed_sort_lift v0 e Tv wfe_t il) f n Hse wff Hskip Hlf). }
      assert (Hlen_v : v0 < length e)
        by (destruct il as [u0 _ Hnth0]; apply (proj1 (nth_error_Some e v0)); rewrite Hnth0; discriminate).
      destruct il as [x Heqx Hnthx].
      assert (Hnu_e : is_large (skipn (S v0) e) x -> False)
        by (intro H; apply Hsmall_e; rewrite Heqx;
            exact (snd (is_large_item_lift e v0 x wfe_t Hnthx) H)).
      pose (sn_e := sn_of_type e (terms.var v0) Tv
                      (type_var e wfe_t v0 Tv (existT2 _ _ x Heqx Hnthx))).
      rewrite (extract_lookup_type_eq_extract_typ e v0 x Tv Hnthx Heqx Hnu_e wfe_t sn_e).
      rewrite (coerce_conv_id _ e Tv Tv sn_e _ (refl_convertible Tv)).
      destruct (lt_eq_lt_dec n v0) as [[Hlt | Heq] | Hgt].
      * (* above: n < v0 *)
        assert (Hvar : terms.subst_rec v (terms.var v0) n = terms.var (Nat.pred v0))
          by (apply subst_ref_gt; lia).
        revert Hsub. rewrite Hvar. intro Hsub.
        eapply simulation.sim_star_trans;
          [| exact (extract_deriv_indep _ _ _
                      (type_var f wff (Nat.pred v0) (terms.subst_rec v Tv n)
                         (item_lift_substitute_above v V n e f Hse v0 Tv Hlt
                            (existT2 _ _ x Heqx Hnthx))) Hsub)].
        cbn [extract].
        destruct (is_large_dec f (terms.subst_rec v Tv n)) as [Habs | _]; [contradiction |].
        pose (il_f := item_lift_substitute_above v V n e f Hse v0 Tv Hlt
                        (existT2 _ _ x Heqx Hnthx)).
        destruct il_f as [x_f Heqx_f Hnthx_f].
        assert (Hnu_f : is_large (skipn (S (Nat.pred v0)) f) x_f -> False)
          by (intro H; apply Hsmall_f; rewrite Heqx_f;
              exact (snd (is_large_item_lift f (Nat.pred v0) x_f wff Hnthx_f) H)).
        pose (sn_f := sn_of_type f (terms.var (Nat.pred v0)) (terms.subst_rec v Tv n)
                        (type_var f wff (Nat.pred v0) _ (existT2 _ _ x_f Heqx_f Hnthx_f))).
        rewrite (extract_lookup_type_eq_extract_typ f (Nat.pred v0) x_f
                   (terms.subst_rec v Tv n) Hnthx_f Heqx_f Hnu_f wff sn_f).
        rewrite (coerce_conv_id _ f (terms.subst_rec v Tv n) (terms.subst_rec v Tv n)
                   sn_f _ (refl_convertible _)).
        rewrite subst_var_t.
        assert (HidxV : nth_error e n = Some V) by (apply (nth_substitute_eq v V n e f Hse)).
        assert (HnlV : is_large (skipn (S n) e) V -> False)
          by (rewrite (skipn_succ_substitute v V n e f Hse); rewrite Hskip; exact Hnl).
        assert (Habove : term_index e v0 = S (term_index f (Nat.pred v0)))
          by (exact (term_index_substitute_above g v V Hv wfg Hnl n e f Hse wfe_t wff Hskip
                       v0 Hlt (Nat.lt_le_incl _ _ Hlen_v))).
        assert (Hgt_idx : n - m < term_index e v0)
          by (rewrite <- Hti; exact (term_index_small_lt e n V HidxV HnlV v0 Hlt)).
        destruct (lt_eq_lt_dec (n - m) (term_index e v0)) as [[_ | Hbad] | Hbad];
          [| lia | lia].
        rewrite Habove. simpl (Nat.pred (S _)). apply simulation.sim_star_refl.
      * (* hit: n = v0 *)
        subst v0.
        rewrite subst_var_t. rewrite Hti.
        destruct (lt_eq_lt_dec (n - m) (n - m)) as [[Hbad | _] | Hbad]; [lia | | lia].
        revert Hsub. rewrite (subst_ref_eq v n). intro Hsub.
        exact (extract_weaken_hit n m g v V Hv wfg Hnl Hle e f Hse wfe_t wff Hskip Hti
                 Tv (existT2 _ _ x Heqx Hnthx) Hsub).
      * (* below: n > v0 *)
        assert (Hvar : terms.subst_rec v (terms.var v0) n = terms.var v0)
          by (apply subst_ref_lt; lia).
        revert Hsub. rewrite Hvar. intro Hsub.
        eapply simulation.sim_star_trans;
          [| exact (extract_deriv_indep _ _ _
                      (type_var f wff v0 (terms.subst_rec v Tv n)
                         (item_lift_substitute_below v V n e f Hse v0 Tv Hgt
                            (existT2 _ _ x Heqx Hnthx))) Hsub)].
        cbn [extract].
        destruct (is_large_dec f (terms.subst_rec v Tv n)) as [Habs | _]; [contradiction |].
        pose (il_f := item_lift_substitute_below v V n e f Hse v0 Tv Hgt
                        (existT2 _ _ x Heqx Hnthx)).
        destruct il_f as [x_f Heqx_f Hnthx_f].
        assert (Hnu_f : is_large (skipn (S v0) f) x_f -> False)
          by (intro H; apply Hsmall_f; rewrite Heqx_f;
              exact (snd (is_large_item_lift f v0 x_f wff Hnthx_f) H)).
        pose (sn_f := sn_of_type f (terms.var v0) (terms.subst_rec v Tv n)
                        (type_var f wff v0 _ (existT2 _ _ x_f Heqx_f Hnthx_f))).
        rewrite (extract_lookup_type_eq_extract_typ f v0 x_f
                   (terms.subst_rec v Tv n) Hnthx_f Heqx_f Hnu_f wff sn_f).
        rewrite (coerce_conv_id _ f (terms.subst_rec v Tv n) (terms.subst_rec v Tv n)
                   sn_f _ (refl_convertible _)).
        rewrite subst_var_t.
        assert (Hlt_idx : term_index e v0 < n - m)
          by (rewrite <- Hti; exact (term_index_small_lt e v0 x Hnthx Hnu_e n Hgt)).
        destruct (lt_eq_lt_dec (n - m) (term_index e v0)) as [[Hbad | Hbad] | _];
          [lia | lia |].
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
    cbn [extract].
    eapply simulation.sim_star_trans;
      [| exact (extract_deriv_indep _ _ _
                  (type_abs f (terms.subst_rec v T n) s1 HT_sub
                     (terms.subst_rec v M (S n)) (terms.subst_rec v U (S n)) s2 HU_sub HM_sub) Hsub)].
    cbn [extract].
    destruct (is_large_dec e T) as [Hlarge_e | Hsmall_e];
      destruct (is_large_dec f (terms.subst_rec v T n)) as [Hlarge_f | Hsmall_f].
    + rewrite subst_tabs_t. rewrite term_tlift_compose. apply sim_star_tabs_gen.
      assert (Hti' : term_index (T :: e) (S n) = S n - S m).
      { rewrite (term_index_succ_large T e n Hlarge_e). rewrite Hti. lia. }
      exact (IH (S n) (S m) g v V Hv wfg Hnl ltac:(lia) (T :: e) M U HM3
               (terms.subst_rec v T n :: f) Hse' wff' Hskip Hti' HM_sub).
    + exfalso. apply Hsmall_f.
      pose proof (is_large_sort_eq e T s1 HM1 Hlarge_e) as Heq. subst s1.
      exact (HT_sub).
    + exfalso. apply Hsmall_e.
      exact (is_large_substitute_inv g v V Hv e T s1 HM1 f n Hse wff Hskip Hlarge_f).
    + rewrite subst_abs_t. apply sim_star_abs_gen.
      assert (Hti' : term_index (T :: e) (S n) = S n - m).
      { rewrite (term_index_succ_small T e n Hsmall_e). rewrite Hti. lia. }
      replace (S (n - m)) with (S n - m) by lia.
      exact (IH (S n) m g v V Hv wfg Hnl ltac:(lia) (T :: e) M U HM3
               (terms.subst_rec v T n :: f) Hse' wff' Hskip Hti' HM_sub).
  - (* app *)
    change (terms.subst_rec v (terms.app u v0) n) with
      (terms.app (terms.subst_rec v u n) (terms.subst_rec v v0 n)) in Hsub |- *.
    pose (Hv0_sub := has_type_substitute_weakening_t g v V Hv e v0 V0 HM1 f n Hse wff Hskip).
    pose (Hu_sub := has_type_substitute_weakening_t g v V Hv e u (terms.prod V0 Ur) HM2 f n Hse wff Hskip).
    pose (Happ := type_app f (terms.subst_rec v v0 n) (terms.subst_rec v V0 n) Hv0_sub
                    (terms.subst_rec v u n) (terms.subst_rec v Ur (S n)) Hu_sub).
    cbn [extract].
    eapply simulation.sim_star_trans;
      [| apply (extract_deriv_indep_conv _ _ _ _ Happ Hsub);
         rewrite <- distribute_subst; apply refl_convertible].
    unfold Happ. cbn [extract].
    destruct (is_large_dec e V0) as [Hlarge_e | Hsmall_e];
      destruct (is_large_dec f (terms.subst_rec v V0 n)) as [Hlarge_f | Hsmall_f].
    + (* large/large: raw tapp on both sides (no coerce) *)
      rewrite subst_tapp_t. apply sim_star_tapp_gen.
      exact (IH n m g v V Hv wfg Hnl Hle e u (terms.prod V0 Ur) HM2 f Hse wff Hskip Hti Hu_sub).
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
    + (* small/small *)
      rewrite subst_coerce, subst_app_t. apply coerce_sim_star_l.
      eapply simulation.sim_star_trans.
      * apply sim_star_app;
          [ exact (IH n m g v V Hv wfg Hnl Hle e u (terms.prod V0 Ur) HM2 f Hse wff Hskip Hti Hu_sub)
          | exact (IH n m g v V Hv wfg Hnl Hle e v0 V0 HM1 f Hse wff Hskip Hti Hv0_sub) ].
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
    cbn [extract]. rewrite subst_dyn_token.
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
    rewrite subst_coerce.
    eapply simulation.sim_star_trans.
    + apply coerce_sim_star_l.
      exact (IH n m g v V Hv wfg Hnl Hle e t U HM1 f Hse wff Hskip Hti Hsub_U).
    + apply (extract_deriv_indep_conv _ _ _ _ Hsub_U Hsub).
      apply convertible_convertible_subst; [apply refl_convertible | exact c].
Qed.

(** Term-substitution commutes with extraction up to [sim_star] when the substituted variable is term-level (small). *)
Lemma extract_subst_sim : forall e V u Ur (HM: has_type (V :: e) u Ur)
  v (Hv: has_type e v V) (wfe: well_formed e),
  (is_large e V -> False) ->
  forall (Hsub: has_type e (terms.subst v u) (terms.subst v Ur)),
  simulation.sim_star
    (infrastructure.subst (extract e v V Hv) 0
       (extract (V :: e) u Ur HM))
    (extract e (terms.subst v u) (terms.subst v Ur) Hsub).
Proof.
  intros e V u Ur HM v Hv wfe Hnlarge Hsub.
  unfold terms.subst in *.
  pose proof (extract_subst_sim_gen 0 0 e v V Hv wfe Hnlarge (le_n 0)
           (V :: e) u Ur HM e (sub_zero v V e) wfe eq_refl eq_refl Hsub) as H.
  assert (Htl : forall t' k, infrastructure.term_tlift 0 k t' = t').
  { induction t'; intros; simpl; f_equal; auto; apply infrastructure.tlift_zero. }
  rewrite Htl in H. exact H.
Qed.
