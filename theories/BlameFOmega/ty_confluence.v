(** * BlameFOmega.ty_confluence: Confluence of type-level reduction.

    The target's type language has a [beta] rule ([ty_step], in infrastructure.v)
    for the type-operator redex [(Λα:K.A) B].  Because the typing judgment is
    closed under the induced definitional equality [ty_equiv] (rule
    [typing_conv]), reasoning about typing "up to conversion" requires
    Church--Rosser for [ty_step].  We prove it by the standard parallel-reduction
    (Tait--Martin-Löf / Takahashi) method and derive the head-constructor
    inversion lemmas ([ty_equiv] respects and reflects [arrow]/[all]/[dyn]/[tvar]
    heads) that subject reduction and progress need.

    The [tlift]/[tsubst] operations follow the same convention as the CoC layer
    (Barras' Coq-in-Coq), so the substitution-lemma chain below mirrors the one
    in [CoC.terms]. *)

From Stdlib Require Import Arith Lia Relations.
From BlameFOmega Require Import syntax infrastructure.

(** ** Reference lemmas for [tlift]/[tsubst] on variables

    Unfold [tlift]/[tsubst] on a bare [tvar] for each branch of the internal
    [le_gt_dec]/[lt_eq_lt_dec] case split, giving named equations the
    substitution-lemma chain below can [rewrite] with instead of re-deriving
    the case split each time. *)

(** [tlift] leaves indices [>= k] shifted up by [i]. *)
Lemma tlift_ref_ge : forall i n k, k <= n -> tlift i k (tvar n) = tvar (i + n).
Proof. intros; simpl; destruct (le_gt_dec k n); [reflexivity | lia]. Qed.

(** [tlift] leaves indices [< k] untouched. *)
Lemma tlift_ref_lt : forall i n k, n < k -> tlift i k (tvar n) = tvar n.
Proof. intros; simpl; destruct (le_gt_dec k n); [lia | reflexivity]. Qed.

(** [tsubst] leaves indices [< k] untouched. *)
Lemma tsubst_ref_lt : forall s n k, n < k -> tsubst s k (tvar n) = tvar n.
Proof. intros; simpl; destruct (lt_eq_lt_dec k n) as [[?|?]|?]; [lia|lia|reflexivity]. Qed.

(** [tsubst] shifts indices [> k] down by one, closing the gap left by the substituted variable. *)
Lemma tsubst_ref_gt : forall s n k, k < n -> tsubst s k (tvar n) = tvar (pred n).
Proof. intros; simpl; destruct (lt_eq_lt_dec k n) as [[?|?]|?]; [reflexivity|lia|lia]. Qed.

(** [tsubst] replaces the target index [k] itself with the (correspondingly lifted) substituted type. *)
Lemma tsubst_ref_eq : forall s k, tsubst s k (tvar k) = tlift k 0 s.
Proof. intros; simpl; destruct (lt_eq_lt_dec k k) as [[?|?]|?]; [lia|reflexivity|lia]. Qed.

(** ** Substitution-lemma chain (mirrors [CoC.terms])

    Each lemma below is a generalized ([_rec]) form carrying an extra offset
    needed for the induction, together with (where used elsewhere) a [k = 0]
    /[p = 0] corollary.  The chain culminates in [distribute_tsubst] and
    [distribute_tlift_tsubst], which are what the [ty_par]/[ty_step]
    substitutivity lemmas further down actually need. *)

(** Two shifts at nested cutoffs ([i] inside the window opened by [k], shift [n]) collapse into one shift by [p + n]. *)
Lemma simplify_tlift_rec :
  forall t n k p i, i <= k + n -> k <= i ->
  tlift p i (tlift n k t) = tlift (p + n) k t.
Proof.
  induction t as [m | A IHA B IHB | K A IHA | K A IHA | A IHA B IHB | ];
    intros n k p i H1 H2.
  - destruct (le_gt_dec k m) as [Hle|Hgt].
    + rewrite (tlift_ref_ge n m k) by lia. rewrite (tlift_ref_ge p (n+m) i) by lia.
      rewrite (tlift_ref_ge (p+n) m k) by lia. f_equal; lia.
    + rewrite (tlift_ref_lt n m k) by lia. rewrite (tlift_ref_lt p m i) by lia.
      rewrite (tlift_ref_lt (p+n) m k) by lia. reflexivity.
  - simpl. rewrite IHA, IHB; auto.
  - simpl. f_equal. apply IHA; lia.
  - simpl. f_equal. apply IHA; lia.
  - simpl. rewrite IHA, IHB; auto.
  - reflexivity.
Qed.

(** Two shifts at cutoffs [i <= k] commute, up to swapping which offset moves. *)
Lemma permute_tlift_rec :
  forall t n k p i, i <= k ->
  tlift p i (tlift n k t) = tlift n (p + k) (tlift p i t).
Proof.
  induction t as [m | A IHA B IHB | K A IHA | K A IHA | A IHA B IHB | ];
    intros n k p i H1.
  - destruct (le_gt_dec k m) as [Hkm|Hkm]; destruct (le_gt_dec i m) as [Him|Him].
    + rewrite (tlift_ref_ge n m k) by lia. rewrite (tlift_ref_ge p (n+m) i) by lia.
      rewrite (tlift_ref_ge p m i) by lia. rewrite (tlift_ref_ge n (p+m) (p+k)) by lia.
      f_equal; lia.
    + lia.
    + rewrite (tlift_ref_lt n m k) by lia. rewrite (tlift_ref_ge p m i) by lia.
      rewrite (tlift_ref_lt n (p+m) (p+k)) by lia. reflexivity.
    + rewrite (tlift_ref_lt n m k) by lia. rewrite (tlift_ref_lt p m i) by lia.
      rewrite (tlift_ref_lt n m (p+k)) by lia. reflexivity.
  - simpl. rewrite IHA, IHB; auto.
  - simpl. f_equal. replace (S (p + k)) with (p + S k) by lia. apply IHA; lia.
  - simpl. f_equal. replace (S (p + k)) with (p + S k) by lia. apply IHA; lia.
  - simpl. rewrite IHA, IHB; auto.
  - reflexivity.
Qed.

(** Substituting into a shift-by-[S n] at an index [p] inside the shifted
    window undoes one layer of the shift, leaving a plain shift by [n]. *)
Lemma simplify_tsubst_rec :
  forall t s n p k, p <= n + k -> k <= p ->
  tsubst s p (tlift (S n) k t) = tlift n k t.
Proof.
  induction t as [m | A IHA B IHB | K A IHA | K A IHA | A IHA B IHB | ];
    intros s n p k H1 H2.
  - destruct (le_gt_dec k m) as [Hle|Hgt].
    + rewrite (tlift_ref_ge (S n) m k) by lia. rewrite (tsubst_ref_gt s (S n + m) p) by lia.
      rewrite (tlift_ref_ge n m k) by lia. f_equal; lia.
    + rewrite (tlift_ref_lt (S n) m k) by lia. rewrite (tsubst_ref_lt s m p) by lia.
      rewrite (tlift_ref_lt n m k) by lia. reflexivity.
  - simpl. rewrite IHA, IHB; auto.
  - simpl. f_equal. apply IHA; lia.
  - simpl. f_equal. apply IHA; lia.
  - simpl. rewrite IHA, IHB; auto.
  - reflexivity.
Qed.

(** A shift below the substitution point ([k <= p]) commutes with the substitution, shifting its target index correspondingly. *)
Lemma commute_tlift_tsubst_rec :
  forall t s n p k, k <= p ->
  tlift n k (tsubst s p t) = tsubst s (n + p) (tlift n k t).
Proof.
  induction t as [m | A IHA B IHB | K A IHA | K A IHA | A IHA B IHB | ];
    intros s n p k H1.
  - destruct (lt_eq_lt_dec p m) as [[Hlt|Heq]|Hgt].
    + rewrite (tsubst_ref_gt s m p) by lia. destruct m as [|m']; [lia|]. simpl (pred _).
      rewrite (tlift_ref_ge n m' k) by lia. rewrite (tlift_ref_ge n (S m') k) by lia.
      rewrite (tsubst_ref_gt s (n + S m') (n+p)) by lia. f_equal; lia.
    + subst. rewrite tsubst_ref_eq. rewrite (tlift_ref_ge n m k) by lia.
      rewrite tsubst_ref_eq. unfold tlift at 2. rewrite simplify_tlift_rec; auto; lia.
    + rewrite (tsubst_ref_lt s m p) by lia. destruct (le_gt_dec k m) as [Hkm|Hkm].
      * rewrite (tlift_ref_ge n m k) by lia. rewrite (tsubst_ref_lt s (n+m) (n+p)) by lia.
        reflexivity.
      * rewrite (tlift_ref_lt n m k) by lia. rewrite (tsubst_ref_lt s m (n+p)) by lia.
        reflexivity.
  - simpl. rewrite IHA, IHB; auto.
  - simpl. f_equal. replace (S (n + p)) with (n + S p) by lia. apply IHA; lia.
  - simpl. f_equal. replace (S (n + p)) with (n + S p) by lia. apply IHA; lia.
  - simpl. rewrite IHA, IHB; auto.
  - reflexivity.
Qed.

(** Substituting [r] at [p + n] after substituting [s] at [p] equals substituting
    [s]'s image (itself substituted) at [p], after substituting [r] one level
    deeper.  The key commutation fact behind [distribute_tsubst]. *)
Lemma distribute_tsubst_rec :
  forall t s r n p,
  tsubst r (p + n) (tsubst s p t) = tsubst (tsubst r n s) p (tsubst r (S (p + n)) t).
Proof.
  induction t as [m | A IHA B IHB | K A IHA | K A IHA | A IHA B IHB | ];
    intros s r n p.
  - destruct (lt_eq_lt_dec p m) as [[Hlt|Heq]|Hgt].
    + (* p < m *)
      rewrite (tsubst_ref_gt s m p) by lia.
      destruct (lt_eq_lt_dec (S (p+n)) m) as [[HA|HA]|HA].
      * (* S(p+n) < m *)
        rewrite (tsubst_ref_gt r m (S (p+n))) by lia.
        rewrite (tsubst_ref_gt r (pred m) (p+n)) by lia.
        rewrite (tsubst_ref_gt (tsubst r n s) (pred m) p) by lia. reflexivity.
      * (* S(p+n) = m *)
        assert (Hm: m = S (p+n)) by lia. subst m. simpl (pred (S (p+n))).
        rewrite (tsubst_ref_eq r (p+n)).
        rewrite (tsubst_ref_eq r (S (p+n))).
        rewrite (simplify_tsubst_rec r (tsubst r n s) (p+n) p 0) by lia. reflexivity.
      * (* m < S(p+n) *)
        rewrite (tsubst_ref_lt r (pred m) (p+n)) by lia.
        rewrite (tsubst_ref_lt r m (S (p+n))) by lia.
        rewrite (tsubst_ref_gt (tsubst r n s) m p) by lia. reflexivity.
    + (* p = m *)
      assert (Hm: m = p) by lia. subst m.
      rewrite (tsubst_ref_eq s p).
      rewrite (tsubst_ref_lt r p (S (p+n))) by lia.
      rewrite (tsubst_ref_eq (tsubst r n s) p).
      rewrite (commute_tlift_tsubst_rec s r p n 0) by lia. reflexivity.
    + (* m < p *)
      rewrite (tsubst_ref_lt s m p) by lia. rewrite (tsubst_ref_lt r m (p+n)) by lia.
      rewrite (tsubst_ref_lt r m (S (p+n))) by lia. rewrite (tsubst_ref_lt (tsubst r n s) m p) by lia.
      reflexivity.
  - simpl. rewrite IHA, IHB; auto.
  - simpl. f_equal. replace (S (p + n)) with (S p + n) by lia. apply (IHA s r n (S p)).
  - simpl. f_equal. replace (S (p + n)) with (S p + n) by lia. apply (IHA s r n (S p)).
  - simpl. rewrite IHA, IHB; auto.
  - reflexivity.
Qed.

(** Top-level substitution distributes over substitution (index 0). *)
Lemma distribute_tsubst :
  forall t s r k,
  tsubst r k (tsubst s 0 t) = tsubst (tsubst r k s) 0 (tsubst r (S k) t).
Proof.
  intros t s r k.
  change (tsubst r (0 + k) (tsubst s 0 t)
          = tsubst (tsubst r k s) 0 (tsubst r (S (0 + k)) t)).
  apply distribute_tsubst_rec.
Qed.

(** Shifting after substituting equals substituting the shifted replacement
    after shifting one level deeper.  The key commutation fact behind
    [distribute_tlift_tsubst]. *)
Lemma distribute_tlift_tsubst_rec :
  forall t s n p k,
  tlift n (p + k) (tsubst s p t) = tsubst (tlift n k s) p (tlift n (S (p + k)) t).
Proof.
  induction t as [m | A IHA B IHB | K A IHA | K A IHA | A IHA B IHB | ];
    intros s n p k.
  - destruct (lt_eq_lt_dec p m) as [[Hlt|Heq]|Hgt].
    + rewrite (tsubst_ref_gt s m p) by lia.
      destruct (le_gt_dec (p+k) (pred m)) as [HA|HA].
      * rewrite (tlift_ref_ge n (pred m) (p+k)) by lia.
        rewrite (tlift_ref_ge n m (S (p+k))) by lia.
        rewrite (tsubst_ref_gt (tlift n k s) (n+m) p) by lia. f_equal; lia.
      * rewrite (tlift_ref_lt n (pred m) (p+k)) by lia.
        rewrite (tlift_ref_lt n m (S (p+k))) by lia.
        rewrite (tsubst_ref_gt (tlift n k s) m p) by lia. reflexivity.
    + subst m. rewrite (tsubst_ref_eq s p).
      rewrite (tlift_ref_lt n p (S (p+k))) by lia.
      rewrite (tsubst_ref_eq (tlift n k s) p).
      rewrite (permute_tlift_rec s n k p 0) by lia. reflexivity.
    + rewrite (tsubst_ref_lt s m p) by lia. rewrite (tlift_ref_lt n m (p+k)) by lia.
      rewrite (tlift_ref_lt n m (S (p+k))) by lia. rewrite (tsubst_ref_lt (tlift n k s) m p) by lia.
      reflexivity.
  - simpl. rewrite IHA, IHB; auto.
  - simpl. f_equal. replace (S (p + k)) with (S p + k) by lia. apply (IHA s n (S p) k).
  - simpl. f_equal. replace (S (p + k)) with (S p + k) by lia. apply (IHA s n (S p) k).
  - simpl. rewrite IHA, IHB; auto.
  - reflexivity.
Qed.

(** p=0 corollaries of the distribution lemmas. *)
Lemma distribute_tlift_tsubst : forall t s n k,
  tlift n k (tsubst s 0 t) = tsubst (tlift n k s) 0 (tlift n (S k) t).
Proof.
  intros t s n k.
  change (tlift n (0 + k) (tsubst s 0 t)
          = tsubst (tlift n k s) 0 (tlift n (S (0 + k)) t)).
  apply distribute_tlift_tsubst_rec.
Qed.

(** ** Parallel reduction (Tait--Martin-Löf)

    [ty_par] reduces zero or more independent redexes of [ty_step] at once
    (every subterm, congruently, plus optionally the top-level beta redex).
    Unlike [ty_step], it enjoys a genuine diamond property ([ty_par_diamond]
    below), which [ty_step]'s sequential, one-redex-at-a-time reduction does
    not.  This is the standard Tait--Martin-Löf / Takahashi device for proving
    confluence of a non-diamond rewriting relation from a diamond one that
    has the same reflexive-transitive closure ([ty_par_ty_star],
    [ty_star_incl_par_star]). *)
Inductive ty_par : typ -> typ -> Prop :=
  | tpar_tvar : forall n, ty_par (tvar n) (tvar n)
  | tpar_dyn : ty_par dyn dyn
  | tpar_arrow : forall A A' B B',
      ty_par A A' -> ty_par B B' -> ty_par (arrow A B) (arrow A' B')
  | tpar_all : forall K A A', ty_par A A' -> ty_par (all K A) (all K A')
  | tpar_tyabs : forall K A A', ty_par A A' -> ty_par (tyabs K A) (tyabs K A')
  | tpar_tyapp : forall A A' B B',
      ty_par A A' -> ty_par B B' -> ty_par (tyapp A B) (tyapp A' B')
  | tpar_beta : forall K A A' B B',
      ty_par A A' -> ty_par B B' ->
      ty_par (tyapp (tyabs K A) B) (tsubst B' 0 A').

Hint Constructors ty_par : blame.

(** [ty_par] is reflexive: reducing "zero" redexes is always allowed. *)
Lemma ty_par_refl : forall t, ty_par t t.
Proof. induction t; auto with blame. Qed.

Hint Resolve ty_par_refl : blame.

(** Parallel reduction is preserved by lifting. *)
Lemma ty_par_tlift : forall A A', ty_par A A' -> forall i k, ty_par (tlift i k A) (tlift i k A').
Proof.
  induction 1; intros i k; simpl; auto with blame.
  - rewrite distribute_tlift_tsubst. apply tpar_beta; [apply IHty_par1 | apply IHty_par2].
Qed.

(** Parallel reduction is preserved by substitution. *)
Lemma ty_par_subst :
  forall A A', ty_par A A' -> forall B B', ty_par B B' ->
  forall k, ty_par (tsubst B k A) (tsubst B' k A').
Proof.
  induction 1; intros B0 B0' HB k; simpl; auto with blame.
  - destruct (lt_eq_lt_dec k n) as [[?|?]|?].
    + apply ty_par_refl.
    + apply ty_par_tlift; auto.
    + apply ty_par_refl.
  - rewrite distribute_tsubst. apply tpar_beta; [apply IHty_par1 | apply IHty_par2]; auto.
Qed.

(** ** Relationship between [ty_step] and [ty_par] *)

(** Every [ty_step] is (trivially) a [ty_par] that reduces just that one redex. *)
Lemma ty_step_ty_par : forall A B, ty_step A B -> ty_par A B.
Proof. induction 1; auto with blame. Qed.

(** [ty_step*]: the reflexive-transitive closure of [ty_step]. *)
Definition ty_star := clos_refl_trans typ ty_step.

Lemma ty_star_refl : forall A, ty_star A A.
Proof. intro; apply rt_refl. Qed.
Lemma ty_star_step : forall A B, ty_step A B -> ty_star A B.
Proof. intros; apply rt_step; auto. Qed.
Lemma ty_star_trans : forall A B C, ty_star A B -> ty_star B C -> ty_star A C.
Proof. intros; eapply rt_trans; eauto. Qed.
Hint Resolve ty_star_refl ty_star_step : blame.

(** Lifts a single [ty_step] congruence constructor [c] (e.g. [tystep_arrow_l])
    to the corresponding congruence for [ty_star], by induction on the
    reflexive-transitive closure. *)
Ltac ty_star_congr c :=
  induction 1;
  [ apply ty_star_step; apply c; assumption
  | apply ty_star_refl
  | eapply ty_star_trans; eassumption ].

(** [ty_star] is a congruence for every type former, componentwise
    ([_l]/[_r] reduce the left/right subterm of a binary former). *)
Lemma ty_star_arrow_l : forall A A' B, ty_star A A' -> ty_star (arrow A B) (arrow A' B).
Proof. intros A A' B; ty_star_congr (fun x y (h:ty_step x y) => tystep_arrow_l x y B h). Qed.
Lemma ty_star_arrow_r : forall A B B', ty_star B B' -> ty_star (arrow A B) (arrow A B').
Proof. intros A B B'; ty_star_congr (fun x y (h:ty_step x y) => tystep_arrow_r A x y h). Qed.
Lemma ty_star_all : forall K A A', ty_star A A' -> ty_star (all K A) (all K A').
Proof. intros K A A'; ty_star_congr (fun x y (h:ty_step x y) => tystep_all K x y h). Qed.
Lemma ty_star_tyabs : forall K A A', ty_star A A' -> ty_star (tyabs K A) (tyabs K A').
Proof. intros K A A'; ty_star_congr (fun x y (h:ty_step x y) => tystep_tyabs K x y h). Qed.
Lemma ty_star_tyapp_l : forall A A' B, ty_star A A' -> ty_star (tyapp A B) (tyapp A' B).
Proof. intros A A' B; ty_star_congr (fun x y (h:ty_step x y) => tystep_tyapp_l x y B h). Qed.
Lemma ty_star_tyapp_r : forall A B B', ty_star B B' -> ty_star (tyapp A B) (tyapp A B').
Proof. intros A B B'; ty_star_congr (fun x y (h:ty_step x y) => tystep_tyapp_r A x y h). Qed.

(** Combine the [_l]/[_r] congruences to reduce both subterms of a binary former at once. *)
Lemma ty_star_arrow : forall A A' B B', ty_star A A' -> ty_star B B' -> ty_star (arrow A B) (arrow A' B').
Proof. intros; eapply ty_star_trans; [apply ty_star_arrow_l | apply ty_star_arrow_r]; eauto. Qed.
Lemma ty_star_tyapp : forall A A' B B', ty_star A A' -> ty_star B B' -> ty_star (tyapp A B) (tyapp A' B').
Proof. intros; eapply ty_star_trans; [apply ty_star_tyapp_l | apply ty_star_tyapp_r]; eauto. Qed.

(** Every [ty_par] step is realized by finitely many [ty_step]s: the
    congruence cases recurse structurally, and [tpar_beta] additionally
    fires the one beta redex the [ty_par] step reduced. *)
Lemma ty_par_ty_star : forall A B, ty_par A B -> ty_star A B.
Proof.
  induction 1; auto with blame.
  - apply ty_star_arrow; auto.
  - apply ty_star_all; auto.
  - apply ty_star_tyabs; auto.
  - apply ty_star_tyapp; auto.
  - eapply ty_star_trans.
    + apply ty_star_tyapp; [apply ty_star_tyabs; exact IHty_par1 | exact IHty_par2].
    + apply ty_star_step. apply tystep_beta.
Qed.

(** ** Complete development and the Takahashi triangle *)

(** Takahashi's "complete development": contract every beta redex present in
    [t] simultaneously (recursively developing subterms first).  Used only as
    the common reduct witness in [ty_par_triangle]/[ty_par_diamond]; nothing
    outside this file depends on its definition, only on the triangle
    property it satisfies. *)
Fixpoint tydev (t : typ) : typ :=
  match t with
  | tvar n => tvar n
  | dyn => dyn
  | arrow A B => arrow (tydev A) (tydev B)
  | all K A => all K (tydev A)
  | tyabs K A => tyabs K (tydev A)
  | tyapp A B =>
      match A with
      | tyabs K A0 => tsubst (tydev B) 0 (tydev A0)
      | _ => tyapp (tydev A) (tydev B)
      end
  end.

(** Takahashi's triangle: [tydev A] is a common reduct of everything [A] parallel-reduces to. *)
Lemma ty_par_triangle : forall A B, ty_par A B -> ty_par B (tydev A).
Proof.
  induction 1 as
    [ n | | A A' B B' HA IHA HB IHB | K A A' HA IHA | K A A' HA IHA
    | A A' B B' HA IHA HB IHB | K A A' B B' HA IHA HB IHB ].
  - simpl. apply tpar_tvar.
  - simpl. apply tpar_dyn.
  - simpl. apply tpar_arrow; auto.
  - simpl. apply tpar_all; auto.
  - simpl. apply tpar_tyabs; auto.
  - (* tpar_tyapp: contract iff the head A is a tyabs *)
    destruct A as [ | | | K0 A0 | | ]; try (apply tpar_tyapp; auto; fail).
    inversion HA; subst. simpl in IHA. inversion IHA; subst.
    apply tpar_beta; auto.
  - (* tpar_beta *) simpl. apply ty_par_subst; auto.
Qed.

(** Diamond property for [ty_par]. *)
Lemma ty_par_diamond : forall A B C, ty_par A B -> ty_par A C ->
  exists D, ty_par B D /\ ty_par C D.
Proof.
  intros A B C HB HC. exists (tydev A). split; apply ty_par_triangle; auto.
Qed.

(** ** Confluence of parallel reduction, then of [ty_step] *)

(** [ty_par*]: the reflexive-transitive closure of [ty_par]. *)
Definition ty_par_star := clos_refl_trans typ ty_par.

Lemma ty_par_star_refl : forall A, ty_par_star A A. Proof. apply rt_refl. Qed.
Lemma ty_par_star_trans : forall A B C, ty_par_star A B -> ty_par_star B C -> ty_par_star A C.
Proof. intros; eapply rt_trans; eauto. Qed.

(** Strip lemma: a single parallel step and a parallel-reduction sequence from the
    same source can be joined. *)
Lemma ty_par_strip : forall A C, ty_par_star A C ->
  forall B, ty_par A B -> exists D, ty_par_star B D /\ ty_par C D.
Proof.
  intros A C H. apply clos_rt_rt1n_iff in H.
  induction H as [A | A A1 C H1 Hrest IH]; intros B HB.
  - exists B; split; [apply ty_par_star_refl | exact HB].
  - destruct (ty_par_diamond A A1 B H1 HB) as [E [HA1E HBE]].
    destruct (IH E HA1E) as [D [HED HCD]].
    exists D; split; [ eapply ty_par_star_trans; [ apply rt_step; exact HBE | exact HED ] | exact HCD ].
Qed.

(** Confluence of parallel reduction. *)
Lemma ty_par_star_confluent : forall A B, ty_par_star A B ->
  forall C, ty_par_star A C -> exists D, ty_par_star B D /\ ty_par_star C D.
Proof.
  intros A B H. apply clos_rt_rt1n_iff in H.
  induction H as [A | A A1 B H1 Hrest IH]; intros C HC.
  - exists C; split; [exact HC | apply ty_par_star_refl].
  - destruct (ty_par_strip A C HC A1 H1) as [E [HA1E HCE]].
    destruct (IH E HA1E) as [D [HBD HED]].
    exists D; split; [ exact HBD | eapply ty_par_star_trans; [ apply rt_step; exact HCE | exact HED ] ].
Qed.

(** [ty_step*] and [ty_par*] have the same closure: every [ty_step*] is a [ty_par*] ... *)
Lemma ty_star_incl_par_star : forall A B, ty_star A B -> ty_par_star A B.
Proof.
  induction 1; [ apply rt_step; apply ty_step_ty_par; auto | apply rt_refl | eapply rt_trans; eauto ].
Qed.

(** ... and conversely, so confluence transfers from [ty_par] (which has it, [ty_par_star_confluent]) to [ty_step] ([ty_star_confluent] below). *)
Lemma ty_par_star_incl_star : forall A B, ty_par_star A B -> ty_star A B.
Proof.
  induction 1; [ apply ty_par_ty_star; auto | apply ty_star_refl | eapply ty_star_trans; eauto ].
Qed.

(** Confluence of [ty_step]. *)
Lemma ty_star_confluent : forall A B, ty_star A B ->
  forall C, ty_star A C -> exists D, ty_star B D /\ ty_star C D.
Proof.
  intros A B HB C HC.
  destruct (ty_par_star_confluent A B (ty_star_incl_par_star _ _ HB)
              C (ty_star_incl_par_star _ _ HC)) as [D [HBD HCD]].
  exists D; split; apply ty_par_star_incl_star; auto.
Qed.

(** ** Church--Rosser for [ty_equiv] *)

(** Church--Rosser: two [ty_equiv]-related types (which may involve arbitrarily
    interleaved forward/backward/symmetric steps) always have a common
    [ty_step*] reduct.  The symmetric-step case is where [ty_star_confluent]
    is actually needed, to join the two branches introduced by transitivity. *)
Lemma ty_equiv_church_rosser : forall A B, ty_equiv A B ->
  exists C, ty_star A C /\ ty_star B C.
Proof.
  unfold ty_equiv. induction 1.
  - exists y; split; [apply ty_star_step; auto | apply ty_star_refl].
  - exists x; split; apply ty_star_refl.
  - destruct IHclos_refl_sym_trans as [C [H1 H2]]. exists C; split; auto.
  - destruct IHclos_refl_sym_trans1 as [C1 [H1a H1b]].
    destruct IHclos_refl_sym_trans2 as [C2 [H2a H2b]].
    destruct (ty_star_confluent y C1 H1b C2 H2a) as [D [HD1 HD2]].
    exists D; split; eapply ty_star_trans; eauto.
Qed.

(** Every [ty_step*] reduction is in particular a [ty_equiv]. *)
Lemma ty_star_incl_equiv : forall A B, ty_star A B -> ty_equiv A B.
Proof.
  induction 1; [ apply ty_step_equiv; auto | apply ty_equiv_refl | eapply ty_equiv_trans; eauto ].
Qed.

(** ** Head-constructor shape preservation under [ty_step*] *)

Lemma ty_star_dyn_inv : forall C, ty_star dyn C -> C = dyn.
Proof.
  intros C H. apply clos_rt_rt1n_iff in H. inversion H; subst.
  - reflexivity.
  - match goal with Hs : ty_step dyn _ |- _ => inversion Hs end.
Qed.

Lemma ty_star_tvar_inv : forall n C, ty_star (tvar n) C -> C = tvar n.
Proof.
  intros n C H. apply clos_rt_rt1n_iff in H. inversion H; subst.
  - reflexivity.
  - match goal with Hs : ty_step (tvar _) _ |- _ => inversion Hs end.
Qed.

Lemma ty_star_arrow_inv : forall A B C, ty_star (arrow A B) C ->
  exists A' B', C = arrow A' B' /\ ty_star A A' /\ ty_star B B'.
Proof.
  intros A B C H. apply clos_rt_rt1n_iff in H.
  remember (arrow A B) as T eqn:HeqT. revert A B HeqT.
  induction H as [ T | T U C Hstep Hrest IH]; intros A B HeqT; subst T.
  - exists A, B; repeat split; apply ty_star_refl.
  - inversion Hstep; subst.
    + destruct (IH A' B eq_refl) as [A2 [B2 [-> [HA HB]]]].
      exists A2, B2; repeat split; auto. eapply ty_star_trans; [apply ty_star_step; eauto | auto].
    + destruct (IH A B' eq_refl) as [A2 [B2 [-> [HA HB]]]].
      exists A2, B2; repeat split; auto. eapply ty_star_trans; [apply ty_star_step; eauto | auto].
Qed.

Lemma ty_star_all_inv : forall K A C, ty_star (all K A) C ->
  exists A', C = all K A' /\ ty_star A A'.
Proof.
  intros K A C H. apply clos_rt_rt1n_iff in H.
  remember (all K A) as T eqn:HeqT. revert K A HeqT.
  induction H as [ T | T U C Hstep Hrest IH]; intros K A HeqT; subst T.
  - exists A; split; [reflexivity | apply ty_star_refl].
  - inversion Hstep; subst.
    destruct (IH K A' eq_refl) as [A2 [-> HA]].
    exists A2; split; auto. eapply ty_star_trans; [apply ty_star_step; eauto | auto].
Qed.

Lemma ty_star_tyabs_inv : forall K A C, ty_star (tyabs K A) C ->
  exists A', C = tyabs K A' /\ ty_star A A'.
Proof.
  intros K A C H. apply clos_rt_rt1n_iff in H.
  remember (tyabs K A) as T eqn:HeqT. revert K A HeqT.
  induction H as [ T | T U C Hstep Hrest IH]; intros K A HeqT; subst T.
  - exists A; split; [reflexivity | apply ty_star_refl].
  - inversion Hstep; subst.
    destruct (IH K A' eq_refl) as [A2 [-> HA]].
    exists A2; split; auto. eapply ty_star_trans; [apply ty_star_step; eauto | auto].
Qed.

(** ** [ty_equiv] head inversions (needed for subject reduction / canonical forms) *)

Lemma ty_equiv_arrow_inv : forall A B A' B',
  ty_equiv (arrow A B) (arrow A' B') -> ty_equiv A A' /\ ty_equiv B B'.
Proof.
  intros A B A' B' H. destruct (ty_equiv_church_rosser _ _ H) as [C [H1 H2]].
  destruct (ty_star_arrow_inv A B C H1) as [A1 [B1 [-> [HA1 HB1]]]].
  destruct (ty_star_arrow_inv A' B' _ H2) as [A2 [B2 [Heq [HA2 HB2]]]].
  injection Heq as -> ->. split.
  - eapply ty_equiv_trans; [apply ty_star_incl_equiv; exact HA1 | apply ty_equiv_sym, ty_star_incl_equiv; exact HA2].
  - eapply ty_equiv_trans; [apply ty_star_incl_equiv; exact HB1 | apply ty_equiv_sym, ty_star_incl_equiv; exact HB2].
Qed.

Lemma ty_equiv_all_inv : forall K A K' A',
  ty_equiv (all K A) (all K' A') -> K = K' /\ ty_equiv A A'.
Proof.
  intros K A K' A' H. destruct (ty_equiv_church_rosser _ _ H) as [C [H1 H2]].
  destruct (ty_star_all_inv K A C H1) as [A1 [-> HA1]].
  destruct (ty_star_all_inv K' A' _ H2) as [A2 [Heq HA2]].
  injection Heq as -> ->. split; [reflexivity |].
  eapply ty_equiv_trans; [apply ty_star_incl_equiv; exact HA1 | apply ty_equiv_sym, ty_star_incl_equiv; exact HA2].
Qed.

(** Distinctness of the head constructors up to [ty_equiv]. *)
Lemma ty_equiv_dyn_arrow : forall A B, ~ ty_equiv dyn (arrow A B).
Proof.
  intros A B H. destruct (ty_equiv_church_rosser _ _ H) as [C [H1 H2]].
  rewrite (ty_star_dyn_inv C H1) in H2.
  destruct (ty_star_arrow_inv A B dyn H2) as [? [? [Hd _]]]. discriminate.
Qed.

Lemma ty_equiv_dyn_all : forall K A, ~ ty_equiv dyn (all K A).
Proof.
  intros K A H. destruct (ty_equiv_church_rosser _ _ H) as [C [H1 H2]].
  rewrite (ty_star_dyn_inv C H1) in H2.
  destruct (ty_star_all_inv K A dyn H2) as [? [Hd _]]. discriminate.
Qed.

Lemma ty_equiv_arrow_all : forall A B K A', ~ ty_equiv (arrow A B) (all K A').
Proof.
  intros A B K A' H. destruct (ty_equiv_church_rosser _ _ H) as [C [H1 H2]].
  destruct (ty_star_arrow_inv A B C H1) as [? [? [-> _]]].
  destruct (ty_star_all_inv K A' _ H2) as [? [Hd _]]. discriminate.
Qed.

Lemma ty_equiv_dyn_tvar : forall n, ~ ty_equiv dyn (tvar n).
Proof.
  intros n H. destruct (ty_equiv_church_rosser _ _ H) as [C [H1 H2]].
  pose proof (ty_star_dyn_inv C H1) as ->.
  pose proof (ty_star_tvar_inv n dyn H2). discriminate.
Qed.

Lemma ty_equiv_arrow_tvar : forall A B n, ~ ty_equiv (arrow A B) (tvar n).
Proof.
  intros A B n H. destruct (ty_equiv_church_rosser _ _ H) as [C [H1 H2]].
  destruct (ty_star_arrow_inv A B C H1) as [? [? [-> _]]].
  pose proof (ty_star_tvar_inv n _ H2). discriminate.
Qed.

Lemma ty_equiv_all_tvar : forall K A n, ~ ty_equiv (all K A) (tvar n).
Proof.
  intros K A n H. destruct (ty_equiv_church_rosser _ _ H) as [C [H1 H2]].
  destruct (ty_star_all_inv K A C H1) as [? [-> _]].
  pose proof (ty_star_tvar_inv n _ H2). discriminate.
Qed.

Lemma ty_equiv_dyn_tyabs : forall K A, ~ ty_equiv dyn (tyabs K A).
Proof.
  intros K A H. destruct (ty_equiv_church_rosser _ _ H) as [C [H1 H2]].
  rewrite (ty_star_dyn_inv C H1) in H2.
  destruct (ty_star_tyabs_inv K A dyn H2) as [? [Hd _]]. discriminate.
Qed.

Lemma ty_equiv_arrow_tyabs : forall A B K A', ~ ty_equiv (arrow A B) (tyabs K A').
Proof.
  intros A B K A' H. destruct (ty_equiv_church_rosser _ _ H) as [C [H1 H2]].
  destruct (ty_star_arrow_inv A B C H1) as [? [? [-> _]]].
  destruct (ty_star_tyabs_inv K A' _ H2) as [? [Hd _]]. discriminate.
Qed.

Lemma ty_equiv_all_tyabs : forall K A K' A', ~ ty_equiv (all K A) (tyabs K' A').
Proof.
  intros K A K' A' H. destruct (ty_equiv_church_rosser _ _ H) as [C [H1 H2]].
  destruct (ty_star_all_inv K A C H1) as [? [-> _]].
  destruct (ty_star_tyabs_inv K' A' _ H2) as [? [Hd _]]. discriminate.
Qed.

(** ** A head-shape classifier for [typ].

    [dyn]/[arrow]/[all]/[tyabs] never change their outer constructor under
    [ty_step] (already witnessed by [ty_star_dyn_inv]/[ty_star_arrow_inv]/
    [ty_star_all_inv]/[ty_star_tyabs_inv] above), and neither does a bare
    [tvar] (it has no [ty_step] rule at all, so [ty_star_tvar_inv] pins its
    reduct to itself).  So these five shapes get a determinate, [ty_equiv]-
    stable tag.  A general [tyapp] does NOT get a determinate tag: an
    application with a [tyabs] hiding under further structure can beta-
    reduce all the way down to any of the other four shapes (e.g.
    [tyapp (tyabs K dyn) X] is actually [ty_equiv] to [dyn]), so classifying
    all [tyapp]s together would be unsound.  We simply leave [tyapp] tagged
    [None]; the lemmas below only compare tags when both sides are
    determinate, which is exactly what the [defeq] head-tag argument
    needs (that argument uses [deq_ty_equiv] steps between literal
    [dyn]/[arrow]/[all]/[tyabs]/[tvar] terms — the intermediate points a
    [deq_def] edge can attach to are always literal [tvar]s, never
    arbitrary [tyapp]s). *)

(** A determinate outermost type-constructor tag, or none for [tyapp]. *)
Inductive head_tag : Set := HTag_dyn | HTag_arrow | HTag_all | HTag_tyabs | HTag_tvar (n : nat).

(** The head tag of a type, or [None] when the head is an (unevaluated) [tyapp]. *)
Definition head_tag_of (A : typ) : option head_tag :=
  match A with
  | dyn => Some HTag_dyn
  | arrow _ _ => Some HTag_arrow
  | all _ _ => Some HTag_all
  | tyabs _ _ => Some HTag_tyabs
  | tvar n => Some (HTag_tvar n)
  | tyapp _ _ => None
  end.

(** [tyabs] and [tvar] are never [ty_equiv]. *)
Lemma ty_equiv_tyabs_tvar : forall K A n, ~ ty_equiv (tyabs K A) (tvar n).
Proof.
  intros K A n H. destruct (ty_equiv_church_rosser _ _ H) as [C [H1 H2]].
  destruct (ty_star_tyabs_inv K A C H1) as [? [-> _]].
  apply ty_star_tvar_inv in H2. discriminate.
Qed.

(** The base compatibility fact: [ty_equiv] preserves a determinate head tag. *)
Lemma ty_equiv_head_tag : forall A B t1 t2,
  ty_equiv A B -> head_tag_of A = Some t1 -> head_tag_of B = Some t2 -> t1 = t2.
Proof.
  intros A B t1 t2 H HA HB.
  destruct A; simpl in HA; try discriminate; injection HA as <-;
  destruct B; simpl in HB; try discriminate; injection HB as <-; auto;
  match goal with
  | H : ty_equiv (tvar _) dyn |- _ => exfalso; eapply ty_equiv_dyn_tvar; eapply ty_equiv_sym; eauto
  | H : ty_equiv (tvar _) (arrow _ _) |- _ => exfalso; eapply ty_equiv_arrow_tvar; eapply ty_equiv_sym; eauto
  | H : ty_equiv (tvar _) (all _ _) |- _ => exfalso; eapply ty_equiv_all_tvar; eapply ty_equiv_sym; eauto
  | H : ty_equiv (tvar _) (tyabs _ _) |- _ => exfalso; eapply ty_equiv_tyabs_tvar; eapply ty_equiv_sym; eauto
  | H : ty_equiv (tvar ?n) (tvar ?n0) |- HTag_tvar ?n = HTag_tvar ?n0 =>
      destruct (ty_equiv_church_rosser _ _ H) as [C [H1 H2]];
      apply ty_star_tvar_inv in H1; apply ty_star_tvar_inv in H2; congruence
  | H : ty_equiv dyn (tvar _) |- _ => exfalso; eapply ty_equiv_dyn_tvar; eauto
  | H : ty_equiv dyn (arrow _ _) |- _ => exfalso; eapply ty_equiv_dyn_arrow; eauto
  | H : ty_equiv dyn (all _ _) |- _ => exfalso; eapply ty_equiv_dyn_all; eauto
  | H : ty_equiv dyn (tyabs _ _) |- _ => exfalso; eapply ty_equiv_dyn_tyabs; eauto
  | H : ty_equiv (arrow _ _) (tvar _) |- _ => exfalso; eapply ty_equiv_arrow_tvar; eauto
  | H : ty_equiv (arrow _ _) dyn |- _ => exfalso; eapply ty_equiv_dyn_arrow; eapply ty_equiv_sym; eauto
  | H : ty_equiv (arrow _ _) (all _ _) |- _ => exfalso; eapply ty_equiv_arrow_all; eauto
  | H : ty_equiv (arrow _ _) (tyabs _ _) |- _ => exfalso; eapply ty_equiv_arrow_tyabs; eauto
  | H : ty_equiv (all _ _) (tvar _) |- _ => exfalso; eapply ty_equiv_all_tvar; eauto
  | H : ty_equiv (all _ _) dyn |- _ => exfalso; eapply ty_equiv_dyn_all; eapply ty_equiv_sym; eauto
  | H : ty_equiv (all _ _) (arrow _ _) |- _ => exfalso; eapply ty_equiv_arrow_all; eapply ty_equiv_sym; eauto
  | H : ty_equiv (all _ _) (tyabs _ _) |- _ => exfalso; eapply ty_equiv_all_tyabs; eauto
  | H : ty_equiv (tyabs _ _) (tvar _) |- _ => exfalso; eapply ty_equiv_tyabs_tvar; eauto
  | H : ty_equiv (tyabs _ _) dyn |- _ => exfalso; eapply ty_equiv_dyn_tyabs; eapply ty_equiv_sym; eauto
  | H : ty_equiv (tyabs _ _) (arrow _ _) |- _ => exfalso; eapply ty_equiv_arrow_tyabs; eapply ty_equiv_sym; eauto
  | H : ty_equiv (tyabs _ _) (all _ _) |- _ => exfalso; eapply ty_equiv_all_tyabs; eapply ty_equiv_sym; eauto
  end.
Qed.
