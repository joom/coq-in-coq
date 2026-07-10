(* This program is free software; you can redistribute it and/or      *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2.1   *)
(* of the License, or (at your option) any later version.             *)
(*                                                                    *)
(* This program is distributed in the hope that it will be useful,    *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of     *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the      *)
(* GNU General Public License for more details.                       *)
(*                                                                    *)
(* You should have received a copy of the GNU Lesser General Public   *)
(* License along with this program; if not, write to the Free         *)
(* Software Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA *)
(* 02110-1301 USA                                                     *)

(** Syntax of the Calculus of Constructions: terms, de Bruijn operations
    (lifting and substitution), beta-reduction, conversion, and strong
    normalization. *)

From Stdlib Require Export PeanoNat.
From Stdlib Require Export Compare_dec.
From Stdlib Require Export Relations.
From Stdlib Require Export Lia.

Implicit Types i k m n p : nat.

Section terms.

  (** The three sorts of the Calculus of Constructions. *)
  Inductive sort : Set :=
    | kind : sort
    | prop : sort
    | set : sort.

  Implicit Type s : sort.

  (** A sort is a "proposition-level" sort if it is [prop] or [set]. *)
  Definition is_prop s := sum (s = prop) (s = set).

  (** Induction principle that splits [kind] from the proposition-level sorts. *)
  Lemma sort_induction :
    forall P : sort -> Prop,
    P kind -> (forall s, is_prop s -> P s) -> forall s, P s.
  Proof.
    unfold is_prop in |- *.
    destruct s.
    - auto.
    - apply H0; left; auto.
    - apply H0; right; auto.
  Qed.

  (** Terms of the Calculus of Constructions in de Bruijn notation. *)
  Inductive term : Set :=
    | sort_term : sort -> term
    | var : nat -> term
    | lam : term -> term -> term
    | app : term -> term -> term
    | prod : term -> term -> term.

  Implicit Types A B M N T t u v : term.

  (** Lifts free variables >= [k] in [t] by [n]. *)
  Fixpoint lift_rec n t {struct t} : nat -> term :=
    fun k =>
    match t with
    | sort_term s => sort_term s
    | var i =>
        match le_gt_dec k i with
        | left _ => var (n + i)
        | right _ => var i
        end
    | lam T M => lam (lift_rec n T k) (lift_rec n M (S k))
    | app u v => app (lift_rec n u k) (lift_rec n v k)
    | prod A B => prod (lift_rec n A k) (lift_rec n B (S k))
    end.

  (** Lifts all free variables in [t] by [n]. *)
  Definition lift n t := lift_rec n t 0.

  (** Substitutes [N] for variable [k] in [M], adjusting indices. *)
  Fixpoint subst_rec N M {struct M} : nat -> term :=
    fun k =>
    match M with
    | sort_term s => sort_term s
    | var i =>
        match lt_eq_lt_dec k i with
        | inleft C =>
            match C with
            | left _ => var (pred i)
            | right _ => lift k N
            end
        | inright _ => var i
        end
    | lam A B => lam (subst_rec N A k) (subst_rec N B (S k))
    | app u v => app (subst_rec N u k) (subst_rec N v k)
    | prod T U => prod (subst_rec N T k) (subst_rec N U (S k))
    end.

  (** Substitutes [N] for variable 0 in [M]. *)
  Definition subst N M := subst_rec N M 0.

  (** [free_db_below n t] holds when all free variables in [t] are < [n]. *)
  Inductive free_db_below : nat -> term -> Prop :=
    | db_sort : forall n s, free_db_below n (sort_term s)
    | db_var : forall k n, k > n -> free_db_below k (var n)
    | db_lam :
        forall k A M, free_db_below k A -> free_db_below (S k) M -> free_db_below k (lam A M)
    | db_app :
        forall k u v, free_db_below k u -> free_db_below k v -> free_db_below k (app u v)
    | db_prod :
        forall k A B, free_db_below k A -> free_db_below (S k) B -> free_db_below k (prod A B).

  (** [subterm_under_binder T M t] holds when [t] is a binder ([lam] or [prod]) with
      type annotation [T] and body [M]. *)
  Inductive subterm_under_binder T M : term -> Prop :=
    | sub_binder_lam : subterm_under_binder T M (lam T M)
    | sub_binder_prod : subterm_under_binder T M (prod T M).

  (** [subterm_no_binder m t] holds when [m] is an immediate non-binding subterm of [t]. *)
  Inductive subterm_no_binder (m : term) : term -> Prop :=
    | sub_no_binder_lam : forall n : term, subterm_no_binder m (lam m n)
    | sub_no_binder_app_l : forall v, subterm_no_binder m (app m v)
    | sub_no_binder_app_r : forall u, subterm_no_binder m (app u m)
    | sub_no_binder_prod : forall n : term, subterm_no_binder m (prod m n).

  (** [subterm m n] holds when [m] is an immediate subterm of [n]. *)
  Inductive subterm (m n : term) : Prop :=
    | sub_bind : forall t, subterm_under_binder t m n -> subterm m n
    | sub_no_bind : subterm_no_binder m n -> subterm m n.

  (** [sort_occurs_in s t] holds when the sort [s] occurs syntactically in [t]. *)
  Inductive sort_occurs_in s : term -> Prop :=
    | mem_eq : sort_occurs_in s (sort_term s)
    | mem_prod_l : forall u v, sort_occurs_in s u -> sort_occurs_in s (prod u v)
    | mem_prod_r : forall u v, sort_occurs_in s v -> sort_occurs_in s (prod u v)
    | mem_abs_l : forall u v, sort_occurs_in s u -> sort_occurs_in s (lam u v)
    | mem_abs_r : forall u v, sort_occurs_in s v -> sort_occurs_in s (lam u v)
    | mem_app_l : forall u v, sort_occurs_in s u -> sort_occurs_in s (app u v)
    | mem_app_r : forall u v, sort_occurs_in s v -> sort_occurs_in s (app u v).

End terms.

Implicit Type s : sort.
Implicit Types A B M N T t u v : term.

Hint Resolve db_sort db_var db_lam db_app db_prod: coc.
Hint Resolve sub_binder_lam sub_binder_prod sub_no_binder_lam sub_no_binder_app_l sub_no_binder_app_r
  sub_no_binder_prod: coc.
Hint Resolve sub_no_bind: coc.
Hint Resolve mem_eq mem_prod_l mem_prod_r mem_abs_l mem_abs_r mem_app_l
  mem_app_r: coc.


Section Beta_Reduction.

  (** One-step beta reduction. *)
  Inductive reduces_once : term -> term -> Type :=
    | beta : forall M N T, reduces_once (app (lam T M) N) (subst N M)
    | abs_reduces_left :
        forall M M', reduces_once M M' -> forall N, reduces_once (lam M N) (lam M' N)
    | abs_reduces_right :
        forall M M', reduces_once M M' -> forall N, reduces_once (lam N M) (lam N M')
    | app_reduces_left :
        forall M1 N1, reduces_once M1 N1 -> forall M2, reduces_once (app M1 M2) (app N1 M2)
    | app_reduces_right :
        forall M2 N2, reduces_once M2 N2 -> forall M1, reduces_once (app M1 M2) (app M1 N2)
    | prod_reduces_left :
        forall M1 N1, reduces_once M1 N1 -> forall M2, reduces_once (prod M1 M2) (prod N1 M2)
    | prod_reduces_right :
        forall M2 N2, reduces_once M2 N2 -> forall M1, reduces_once (prod M1 M2) (prod M1 N2).

  (** Reflexive-transitive closure of [reduces_once], at Type level. *)
  Inductive reduces : term -> term -> Type :=
    | red_refl : forall M, reduces M M
    | red_trans : forall M P N, reduces_once P N -> reduces M P -> reduces M N.

  Definition refl_reduces : forall M, reduces M M := red_refl.

  Definition trans_red : forall M (P : term) N, reduces M P -> reduces_once P N -> reduces M N :=
    fun M P N H1 H2 => red_trans M P N H2 H1.

  (** Conversion: reflexive-symmetric-transitive closure of [reduces_once], at Type level. *)
  Inductive convertible : term -> term -> Type :=
    | conv_refl : forall M, convertible M M
    | conv_red : forall M P N, reduces_once P N -> convertible M P -> convertible M N
    | conv_exp : forall M P N, reduces_once N P -> convertible M P -> convertible M N.

  Definition refl_convertible : forall M, convertible M M := conv_refl.

  Definition trans_conv_red : forall M (P : term) N, convertible M P -> reduces_once P N -> convertible M N :=
    fun M P N H1 H2 => conv_red M P N H2 H1.

  Definition trans_conv_exp : forall M (P : term) N, convertible M P -> reduces_once N P -> convertible M N :=
    fun M P N H1 H2 => conv_exp M P N H2 H1.

  (** One-step parallel beta reduction. *)
  Inductive parallel_reduces_once : term -> term -> Type :=
    | par_beta :
        forall M M',
        parallel_reduces_once M M' ->
        forall N N',
        parallel_reduces_once N N' -> forall T, parallel_reduces_once (app (lam T M) N) (subst N' M')
    | sort_par_red : forall s, parallel_reduces_once (sort_term s) (sort_term s)
    | ref_par_red : forall n, parallel_reduces_once (var n) (var n)
    | abs_par_red :
        forall M M',
        parallel_reduces_once M M' ->
        forall T T', parallel_reduces_once T T' -> parallel_reduces_once (lam T M) (lam T' M')
    | app_par_red :
        forall M M',
        parallel_reduces_once M M' ->
        forall N N', parallel_reduces_once N N' -> parallel_reduces_once (app M N) (app M' N')
    | prod_par_red :
        forall M M',
        parallel_reduces_once M M' ->
        forall N N', parallel_reduces_once N N' -> parallel_reduces_once (prod M N) (prod M' N').

  (** Transitive closure of parallel reduction, at Type level. *)
  Inductive parallel_reduces : term -> term -> Type :=
    | t_step : forall M N, parallel_reduces_once M N -> parallel_reduces M N
    | t_trans : forall M P N, parallel_reduces M P -> parallel_reduces P N -> parallel_reduces M N.

End Beta_Reduction.

Hint Resolve beta abs_reduces_left abs_reduces_right app_reduces_left app_reduces_right prod_reduces_left
  prod_reduces_right: coc.
Hint Resolve refl_reduces refl_convertible red_refl: coc.
Hint Resolve par_beta sort_par_red ref_par_red abs_par_red app_par_red
  prod_par_red: coc.
Hint Resolve t_step: coc.


Section Strong_Normalization.

  (** A term is normal when no reduction step is possible. *)
  Definition normal t : Prop := forall u, reduces_once t u -> False.

  (** Prop-level wrapper for reduces_once, used for Acc-based strong normalization. *)
  Definition reduces_once_prop (t u : term) : Prop := inhabited (reduces_once t u).

  (** Strong normalization: well-foundedness of reverse [reduces_once_prop]. *)
  Definition strongly_normalizing : term -> Prop := Acc (transp _ reduces_once_prop).

End Strong_Normalization.

Hint Unfold strongly_normalizing: coc.


(** Lifting a variable reference at or above the cutoff increases the index. *)
Lemma lift_ref_ge :
  forall k n p, p <= n -> lift_rec k (var n) p = var (k + n).
Proof.
  intros; simpl in |- *.
  elim (le_gt_dec p n); auto with coc core arith sets.
  intro; absurd (p <= n); auto with coc core arith sets.
Qed.

(** Lifting a variable reference below the cutoff is the identity. *)
Lemma lift_ref_lt : forall k n p, p > n -> lift_rec k (var n) p = var n.
Proof.
  intros; simpl in |- *.
  elim (le_gt_dec p n); auto with coc core arith sets.
  intro; absurd (p <= n); auto with coc core arith sets.
Qed.

(** Substituting into a variable below the substitution point is the identity. *)
Lemma subst_ref_lt : forall u n k, k > n -> subst_rec u (var n) k = var n.
Proof.
  simpl in |- *; intros.
  elim (lt_eq_lt_dec k n); [ intro a | intro b; auto with coc core arith sets ].
  intuition lia.
Qed.

(** Substituting into a variable above the substitution point decrements the index. *)
Lemma subst_ref_gt :
  forall u n k, n > k -> subst_rec u (var n) k = var (pred n).
Proof.
  simpl in |- *; intros.
  elim (lt_eq_lt_dec k n); intuition lia.
Qed.

(** Substituting at the exact variable index lifts the substituted term. *)
Lemma subst_ref_eq : forall u n, subst_rec u (var n) n = lift n u.
Proof.
  intros; simpl in |- *.
  elim (lt_eq_lt_dec n n); intuition lia.
Qed.

(** Lifting by 0 is the identity. *)
Lemma lift_rec_zero : forall M k, lift_rec 0 M k = M.
Proof.
  simple induction M; simpl in |- *; intros; auto with coc core arith sets.
  elim (le_gt_dec k n); auto with coc core arith sets.
  rewrite H; rewrite H0; auto with coc core arith sets.
  rewrite H; rewrite H0; auto with coc core arith sets.
  rewrite H; rewrite H0; auto with coc core arith sets.
Qed.

(** [lift 0] is the identity. *)
Lemma lift_zero : forall M, lift 0 M = M.
Proof.
  intros; unfold lift in |- *.
  apply lift_rec_zero; auto with coc core arith sets.
Qed.

(** Two consecutive lifts can be combined into one. *)
Lemma simplify_lift_rec :
  forall M n k p i,
  i <= k + n ->
  k <= i -> lift_rec p (lift_rec n M k) i = lift_rec (p + n) M k.
Proof.
  simple induction M; simpl in |- *; intros; auto with coc core arith sets.
  elim (le_gt_dec k n); intros.
  rewrite lift_ref_ge; solve [auto with coc core arith sets | lia].
  rewrite lift_ref_lt; auto with coc core arith sets. lia.
  all : rewrite H; auto with coc core arith sets; rewrite H0; simpl in |- *;
    auto with coc core arith sets.
Qed.

(** [lift (S n)] decomposes as [lift 1] after [lift n]. *)
Lemma simplify_lift : forall M n, lift (S n) M = lift 1 (lift n M).
Proof.
  intros; unfold lift in |- *.
  rewrite simplify_lift_rec; auto with coc core arith sets.
Qed.

(** Lifting commutes with itself under appropriate index conditions. *)
Lemma permute_lift_rec :
  forall M n k p i,
  i <= k ->
  lift_rec p (lift_rec n M k) i = lift_rec n (lift_rec p M i) (p + k).
Proof.
  simple induction M; simpl in |- *; intros; auto with coc core arith sets.
  elim (le_gt_dec k n); elim (le_gt_dec i n); intros.
  rewrite lift_ref_ge; auto with coc core arith sets.
  rewrite lift_ref_ge; auto with coc core arith sets.
  f_equal. lia.
  apply Nat.le_trans with n; auto with coc core arith sets.
  absurd (i <= n); auto with coc core arith sets.
  apply Nat.le_trans with k; auto with coc core arith sets.
  rewrite lift_ref_ge; auto with coc core arith sets.
  rewrite lift_ref_lt; auto with coc core arith sets.
  rewrite lift_ref_lt; auto with coc core arith sets.
  rewrite lift_ref_lt; auto with coc core arith sets.
  lia.
  rewrite H; auto with coc core arith sets; rewrite H0;
    auto with coc core arith sets.
  rewrite plus_n_Sm; auto with coc core arith sets.
  rewrite H; auto with coc core arith sets; rewrite H0;
    auto with coc core arith sets.
  rewrite H; auto with coc core arith sets; rewrite H0;
    auto with coc core arith sets.
  rewrite plus_n_Sm; auto with coc core arith sets.
Qed.

(** Special case of [permute_lift_rec] for lifts by 1. *)
Lemma permute_lift :
  forall M k, lift 1 (lift_rec 1 M k) = lift_rec 1 (lift 1 M) (S k).
Proof.
  intros.
  change (lift_rec 1 (lift_rec 1 M k) 0 = lift_rec 1 (lift_rec 1 M 0) (1 + k))
    in |- *.
  apply permute_lift_rec; auto with coc core arith sets.
Qed.

(** Substituting into a sufficiently-lifted term cancels the lift. *)
Lemma simplify_subst_rec :
  forall N M n p k,
  p <= n + k ->
  k <= p -> subst_rec N (lift_rec (S n) M k) p = lift_rec n M k.
Proof.
  simple induction M; simpl in |- *; intros; auto with coc core arith sets.
  elim (le_gt_dec k n); intros.
  rewrite subst_ref_gt; auto with coc core arith sets.
  red in |- *; red in |- *.
  apply Nat.le_trans with (S (n0 + k)); auto with coc core arith sets.
  rewrite subst_ref_lt; auto with coc core arith sets.
  lia.
  rewrite H; auto with coc core arith sets; rewrite H0;
    auto with coc core arith sets.
  elim plus_n_Sm with n k; auto with coc core arith sets.
  rewrite H; auto with coc core arith sets; rewrite H0;
    auto with coc core arith sets.
  rewrite H; auto with coc core arith sets; rewrite H0;
    auto with coc core arith sets.
  elim plus_n_Sm with n k; auto with coc core arith sets.
Qed.

(** Substituting into a lifted term yields the original lift. *)
Lemma simplify_subst :
  forall N M n p, p <= n -> subst_rec N (lift (S n) M) p = lift n M.
Proof.
  intros; unfold lift in |- *.
  apply simplify_subst_rec; auto with coc core arith sets.
Qed.

(** Lifting commutes with substitution. *)
Lemma commute_lift_subst_rec :
  forall M N n p k,
  k <= p ->
  lift_rec n (subst_rec N M p) k = subst_rec N (lift_rec n M k) (n + p).
Proof.
  simple induction M; intros; auto with coc core arith sets.
  unfold subst_rec at 1, lift_rec at 2 in |- *.
  elim (lt_eq_lt_dec p n);
    [ intro Hlt_eq; elim (le_gt_dec k n); [ intro Hle | intro Hgt ]
    | intro Hlt; elim (le_gt_dec k n); [ intro Hle | intro Hgt ] ].
  elim Hlt_eq; clear Hlt_eq.
  case n; [ intro Hlt | intros ].
  inversion_clear Hlt.
  unfold pred in |- *.
  rewrite lift_ref_ge; auto with coc core arith sets.
  rewrite subst_ref_gt; auto with coc core arith sets.
  elim plus_n_Sm with n0 n1.
  auto with coc core arith sets.
  apply Nat.le_trans with p; auto with coc core arith sets.
  simple induction 1.
  rewrite subst_ref_eq.
  unfold lift in |- *.
  rewrite simplify_lift_rec; auto with coc core arith sets.
  absurd (k <= n); auto with coc core arith sets.
  apply Nat.le_trans with p; auto with coc core arith sets.
  elim Hlt_eq; auto with coc core arith sets.
  simple induction 1; auto with coc core arith sets.
  rewrite lift_ref_ge; auto with coc core arith sets.
  rewrite subst_ref_lt; auto with coc core arith sets.
  rewrite lift_ref_lt; auto with coc core arith sets.
  rewrite subst_ref_lt; auto with coc core arith sets.
  lia.
  simpl in |- *.
  rewrite plus_n_Sm.
  rewrite H; auto with coc core arith sets; rewrite H0;
    auto with coc core arith sets.
  simpl in |- *; rewrite H; auto with coc core arith sets; rewrite H0;
    auto with coc core arith sets.
  simpl in |- *; rewrite plus_n_Sm.
  rewrite H; auto with coc core arith sets; rewrite H0;
    auto with coc core arith sets.
Qed.

(** Special case: lifting by 1 commutes with substitution at successor index. *)
Lemma commute_lift_subst :
  forall M N k, subst_rec N (lift 1 M) (S k) = lift 1 (subst_rec N M k).
Proof.
  intros; unfold lift in |- *.
  rewrite commute_lift_subst_rec; auto with coc core arith sets.
Qed.

(** Lifting distributes over substitution. *)
Lemma distribute_lift_subst_rec :
  forall M N n p k,
  lift_rec n (subst_rec N M p) (p + k) =
  subst_rec (lift_rec n N k) (lift_rec n M (S (p + k))) p.
Proof.
  simple induction M; intros; auto with coc core arith sets.
  unfold subst_rec at 1 in |- *.
  elim (lt_eq_lt_dec p n); [ intro a | intro b ].
  elim a; clear a.
  case n; [ intro a | intros n1 b ].
  inversion_clear a.
  unfold pred, lift_rec at 1 in |- *.
  elim (le_gt_dec (p + k) n1); intro.
  rewrite lift_ref_ge; auto with coc core arith sets.
  elim plus_n_Sm with n0 n1.
  rewrite subst_ref_gt; auto with coc core arith sets.
  red in |- *; red in |- *; apply le_n_S.
  apply Nat.le_trans with (n0 + (p + k)); auto with coc core arith sets.
  apply Nat.le_trans with (p + k); auto with coc core arith sets.
  rewrite lift_ref_lt; auto with coc core arith sets.
  rewrite subst_ref_gt; auto with coc core arith sets.
  simple induction 1.
  unfold lift in |- *.
  rewrite <- permute_lift_rec; auto with coc core arith sets.
  rewrite lift_ref_lt; auto with coc core arith sets.
  rewrite subst_ref_eq; auto with coc core arith sets.
  rewrite lift_ref_lt; auto with coc core arith sets.
  rewrite lift_ref_lt; auto with coc core arith sets.
  rewrite subst_ref_lt; auto with coc core arith sets.
  simpl in |- *; replace (S (p + k)) with (S p + k);
    auto with coc core arith sets.
  rewrite H; rewrite H0; auto with coc core arith sets.
  simpl in |- *; rewrite H; rewrite H0; auto with coc core arith sets.
  simpl in |- *; replace (S (p + k)) with (S p + k);
    auto with coc core arith sets.
  rewrite H; rewrite H0; auto with coc core arith sets.
Qed.

(** Lifting distributes over top-level substitution. *)
Lemma distribute_lift_subst :
  forall M N n k,
  lift_rec n (subst N M) k = subst (lift_rec n N k) (lift_rec n M (S k)).
Proof.
  intros; unfold subst in |- *.
  pattern k at 1 3 in |- *.
  replace k with (0 + k); auto with coc core arith sets.
  apply distribute_lift_subst_rec.
Qed.

(** Substitution distributes over substitution. *)
Lemma distribute_subst_rec :
  forall M N (P : term) n p,
  subst_rec P (subst_rec N M p) (p + n) =
  subst_rec (subst_rec P N n) (subst_rec P M (S (p + n))) p.
Proof.
  simple induction M; auto with coc core arith sets; intros.
  unfold subst_rec at 2 in |- *.
  elim (lt_eq_lt_dec p n); [ intro Hlt_eq | intro Hlt ].
  elim Hlt_eq; clear Hlt_eq.
  case n; [ intro Hlt | intros n1 Heq1 ].
  inversion_clear Hlt.
  unfold pred, subst_rec at 1 in |- *.
  elim (lt_eq_lt_dec (p + n0) n1); [ intro Hlt_eq | intro Hlt ].
  elim Hlt_eq; clear Hlt_eq.
  case n1; [ intro Hlt | intros n2 Heq2 ].
  inversion_clear Hlt.
  rewrite subst_ref_gt; auto with coc core arith sets.
  rewrite subst_ref_gt; auto with coc core arith sets.
  lia.
  simple induction 1.
  rewrite subst_ref_eq; auto with coc core arith sets.
  rewrite simplify_subst; auto with coc core arith sets.
  rewrite subst_ref_lt; auto with coc core arith sets.
  rewrite subst_ref_gt; auto with coc core arith sets.
  simple induction 1.
  rewrite subst_ref_lt; auto with coc core arith sets.
  rewrite subst_ref_eq.
  unfold lift in |- *.
  rewrite commute_lift_subst_rec; auto with coc core arith sets.
  do 3 (rewrite subst_ref_lt; auto with coc core arith sets).
  simpl in |- *; replace (S (p + n)) with (S p + n);
    auto with coc core arith sets.
  rewrite H; auto with coc core arith sets; rewrite H0;
    auto with coc core arith sets.
  simpl in |- *; rewrite H; rewrite H0; auto with coc core arith sets.
  simpl in |- *; replace (S (p + n)) with (S p + n);
    auto with coc core arith sets.
  rewrite H; rewrite H0; auto with coc core arith sets.
Qed.

(** Top-level substitution distributes over substitution. *)
Lemma distribute_subst :
  forall (P : term) N M k,
  subst_rec P (subst N M) k = subst (subst_rec P N k) (subst_rec P M (S k)).
Proof.
  intros; unfold subst in |- *.
  pattern k at 1 3 in |- *.
  replace k with (0 + k); auto with coc core arith sets.
  apply distribute_subst_rec.
Qed.

(** A single reduction step embeds into the reflexive-transitive closure. *)
Lemma one_step_reduces : forall M N, reduces_once M N -> reduces M N.
Proof.
  intros.
  apply trans_red with M; auto with coc core arith sets.
Qed.

Hint Resolve one_step_reduces: coc.

(** Induction on [reduces] from the source side. *)
Lemma reduces_reverse_ind :
  forall N (P : term -> Prop),
  P N ->
  (forall M (R : term), reduces_once M R -> reduces R N -> P R -> P M) ->
  forall M, reduces M N -> P M.
Proof.
  intros N0 P0 HN Hstep M0 Hred.
  assert (Hgen : forall Q : term -> Prop,
     Q N0 -> (forall M (R : term), reduces_once M R -> reduces R N0 -> Q R -> Q M) -> Q M0).
  { clear HN Hstep P0.
    induction Hred as [| M0 P1 N1 Hr Hred IHHred]; intros; auto.
    apply IHHred.
    - apply H0 with N1; auto with coc core arith sets.
    - intros. apply H0 with R; auto.
      apply trans_red with P1; auto. }
  apply Hgen; auto.
Qed.

(** Reduction is transitive. *)
Lemma trans_reduces_reduces : forall M N (P : term), reduces M N -> reduces N P -> reduces M P.
Proof.
  intros M N P0 H1 H2.
  induction H2 as [| ? P1 ? Hstep Hred IH]; auto.
  apply trans_red with P1; auto.
Qed.

(** Reduction is compatible with [app]. *)
Lemma reduces_reduces_application :
  forall u u0 v v0, reduces u u0 -> reduces v v0 -> reduces (app u v) (app u0 v0).
Proof.
  intros u u0 v v0 H1 H2.
  induction H1 as [M0 | M0 P1 N0 Hstep Hred IH].
  - induction H2 as [M1 | M1 P2 N1 Hstep2 Hred2 IH2]; auto with coc core arith sets.
    apply trans_red with (app M0 P2); auto with coc core arith sets.
  - apply trans_red with (app P1 v0); auto with coc core arith sets.
Qed.

(** Reduction is compatible with [lam]. *)
Lemma reduces_reduces_lambda :
  forall u u0 v v0, reduces u u0 -> reduces v v0 -> reduces (lam u v) (lam u0 v0).
Proof.
  intros u u0 v v0 H1 H2.
  induction H1 as [M0 | M0 P1 N0 Hstep Hred IH].
  - induction H2 as [M1 | M1 P2 N1 Hstep2 Hred2 IH2]; auto with coc core arith sets.
    apply trans_red with (lam M0 P2); auto with coc core arith sets.
  - apply trans_red with (lam P1 v0); auto with coc core arith sets.
Qed.

(** Reduction is compatible with [prod]. *)
Lemma reduces_reduces_product :
  forall u u0 v v0, reduces u u0 -> reduces v v0 -> reduces (prod u v) (prod u0 v0).
Proof.
  intros u u0 v v0 H1 H2.
  induction H1 as [M0 | M0 P1 N0 Hstep Hred IH].
  - induction H2 as [M1 | M1 P2 N1 Hstep2 Hred2 IH2]; auto with coc core arith sets.
    apply trans_red with (prod M0 P2); auto with coc core arith sets.
  - apply trans_red with (prod P1 v0); auto with coc core arith sets.
Qed.

Hint Resolve reduces_reduces_application reduces_reduces_lambda reduces_reduces_product: coc.

(** One-step reduction is preserved by lifting. *)
Lemma reduces_once_lift :
  forall u v, reduces_once u v -> forall n k, reduces_once (lift_rec n u k) (lift_rec n v k).
Proof.
  simple induction 1; simpl in |- *; intros; auto with coc core arith sets.
  rewrite distribute_lift_subst; auto with coc core arith sets.
Qed.

Hint Resolve reduces_once_lift: coc.

(** One-step reduction is preserved by substitution on the right. *)
Lemma reduces_once_subst_right :
  forall t u,
  reduces_once t u -> forall (a : term) k, reduces_once (subst_rec a t k) (subst_rec a u k).
Proof.
  simple induction 1; simpl in |- *; intros; auto with coc core arith sets.
  rewrite distribute_subst; auto with coc core arith sets.
Qed.

(** Reduction on the substituted term propagates through substitution. *)
Lemma reduces_once_subst_left :
  forall (a : term) t u k,
  reduces_once t u -> reduces (subst_rec t a k) (subst_rec u a k).
Proof.
  simple induction a; simpl in |- *; auto with coc core arith sets.
  intros.
  elim (lt_eq_lt_dec k n);
    [ intro a0 | intro b; auto with coc core arith sets ].
  elim a0; auto with coc core arith sets.
  unfold lift in |- *; auto with coc core arith sets.
Qed.

Hint Resolve reduces_once_subst_left reduces_once_subst_right: coc.

(** A prod reduces only to a prod. *)
Lemma reduces_product_product :
  forall u v t,
  reduces (prod u v) t ->
  forall Q : Type,
  (forall a b : term, t = prod a b -> reduces u a -> reduces v b -> Q) -> Q.
Proof.
  intros u v t Hred.
  remember (prod u v) as puv eqn:Hpuv.
  induction Hred as [M0 | M0 P0 N0 Hstep Hred IHHred];
    intros Q Hcont.
  - subst. apply Hcont with u v; auto with coc core arith sets.
  - apply IHHred; auto; intros a b Heq Ha Hb.
    subst. inversion Hstep; subst.
    + apply Hcont with N1 b; auto with coc core arith sets.
      apply trans_red with a; auto with coc core arith sets.
    + apply Hcont with a N2; auto with coc core arith sets.
      apply trans_red with b; auto with coc core arith sets.
Qed.

(** A sort does not reduce to a different term. *)
Lemma reduces_sort_sort : forall s t, reduces (sort_term s) t -> t <> sort_term s -> False.
Proof.
  intros s t Hred Hneq.
  remember (sort_term s) as ss eqn:Hss.
  induction Hred; auto.
  apply IHHred; auto; intro; subst.
  apply Hneq.
  inversion r.
Qed.

(** A single expansion step embeds into conversion. *)
Lemma one_step_convertible_expansion : forall M N, reduces_once M N -> convertible N M.
Proof.
  intros.
  apply trans_conv_exp with N; auto with coc core arith sets.
Qed.

(** Reduction embeds into conversion. *)
Lemma reduces_convertible : forall M N, reduces M N -> convertible M N.
Proof.
  intros M N H; induction H; auto with coc core arith sets.
  apply trans_conv_red with P; auto with coc core arith sets.
Qed.

Hint Resolve one_step_convertible_expansion reduces_convertible: coc.

(** Conversion is transitive. *)
Lemma trans_convertible_convertible :
  forall M N (P : term), convertible M N -> convertible N P -> convertible M P.
Proof.
  intros M N P0 H1 H2; induction H2 as [| ? Q ? Hstep ? IH | ? Q ? Hstep ? IH].
  exact H1.
  apply conv_red with Q; auto.
  apply conv_exp with Q; auto.
Qed.

(** Conversion is symmetric. *)
Lemma sym_convertible : forall M N, convertible M N -> convertible N M.
Proof.
  intros M N H. induction H as [M0 | M0 P0 N0 Hr Hconv IH | M0 P0 N0 Hr Hconv IH].
  exact (conv_refl M0).
  apply trans_convertible_convertible with P0.
    exact (conv_exp N0 N0 P0 Hr (conv_refl N0)).
    exact IH.
  apply trans_convertible_convertible with P0.
    exact (conv_red N0 N0 P0 Hr (conv_refl N0)).
    exact IH.
Qed.

Hint Immediate sym_convertible: coc.

(** Conversion is compatible with [prod]. *)
Lemma convertible_convertible_product :
  forall a b c d : term, convertible a b -> convertible c d -> convertible (prod a c) (prod b d).
Proof.
  intros a b c d H1 H2.
  apply trans_convertible_convertible with (prod a d).
  - induction H2; auto with coc core arith sets.
    + apply trans_conv_red with (prod a P); auto with coc core arith sets.
    + apply trans_conv_exp with (prod a P); auto with coc core arith sets.
  - induction H1; auto with coc core arith sets.
    + apply trans_conv_red with (prod P d); auto with coc core arith sets.
    + apply trans_conv_exp with (prod P d); auto with coc core arith sets.
Qed.

(** Conversion is preserved by lifting. *)
Lemma convertible_convertible_lift :
  forall (a b : term) n k,
  convertible a b -> convertible (lift_rec n a k) (lift_rec n b k).
Proof.
  intros a b n k H.
  induction H; auto with coc core arith sets.
  - apply trans_conv_red with (lift_rec n P k); auto with coc core arith sets.
  - apply trans_conv_exp with (lift_rec n P k); auto with coc core arith sets.
Qed.

(** Conversion is preserved by substitution on both sides. *)
Lemma convertible_convertible_subst :
  forall (a b c d : term) k,
  convertible a b -> convertible c d -> convertible (subst_rec a c k) (subst_rec b d k).
Proof.
  intros a b c d k H1 H2.
  apply trans_convertible_convertible with (subst_rec a d k).
  - induction H2; auto with coc core arith sets.
    + apply trans_conv_red with (subst_rec a P k); auto with coc core arith sets.
    + apply trans_conv_exp with (subst_rec a P k); auto with coc core arith sets.
  - induction H1; auto with coc core arith sets.
    + apply trans_convertible_convertible with (subst_rec P d k); auto with coc core arith sets.
    + apply trans_convertible_convertible with (subst_rec P d k); auto with coc core arith sets.
      apply sym_convertible; auto with coc core arith sets.
Qed.

Hint Resolve convertible_convertible_product convertible_convertible_lift convertible_convertible_subst: coc.

(** Every term parallel-reduces to itself in one step. *)
Lemma refl_parallel_reduces_once : forall M, parallel_reduces_once M M.
Proof.
  simple induction M; auto with coc core arith sets.
Qed.

Hint Resolve refl_parallel_reduces_once: coc.

(** One-step reduction embeds into one-step parallel reduction. *)
Lemma reduces_once_parallel_reduces_once : forall M N, reduces_once M N -> parallel_reduces_once M N.
Proof.
  simple induction 1; auto with coc core arith sets; intros.
Qed.

Hint Resolve reduces_once_parallel_reduces_once: coc.

(** Reduction embeds into parallel reduction. *)
Lemma reduces_parallel_reduces : forall M N, reduces M N -> parallel_reduces M N.
Proof.
  intros M N H; induction H; auto with coc core arith sets.
  apply t_trans with P; auto with coc core arith sets.
Qed.

(** Parallel reduction embeds back into reduction. *)
Lemma parallel_reduces_reduces : forall M N, parallel_reduces M N -> reduces M N.
Proof.
  intros M N H; induction H as [M0 N0 Hpar | M0 P0 N0 H1 IH1 H2 IH2].
  - induction Hpar; auto with coc core arith sets.
    apply trans_red with (app (lam T M') N'); auto with coc core arith sets.
  - apply trans_reduces_reduces with P0; auto with coc core arith sets.
Qed.

Hint Resolve reduces_parallel_reduces parallel_reduces_reduces: coc.

(** Parallel reduction is preserved by lifting. *)
Lemma parallel_reduces_once_lift :
  forall n (a b : term),
  parallel_reduces_once a b -> forall k, parallel_reduces_once (lift_rec n a k) (lift_rec n b k).
Proof.
  simple induction 1; simpl in |- *; auto with coc core arith sets.
  intros.
  rewrite distribute_lift_subst; auto with coc core arith sets.
Qed.

(** Parallel reduction is preserved by substitution. *)
Lemma parallel_reduces_once_subst :
  forall c d : term,
  parallel_reduces_once c d ->
  forall a b : term,
  parallel_reduces_once a b -> forall k, parallel_reduces_once (subst_rec a c k) (subst_rec b d k).
Proof.
  simple induction 1; simpl in |- *; auto with coc core arith sets; intros.
  rewrite distribute_subst; auto with coc core arith sets.
  elim (lt_eq_lt_dec k n); auto with coc core arith sets; intro a0.
  elim a0; intros; auto with coc core arith sets.
  unfold lift in |- *.
  apply parallel_reduces_once_lift; auto with coc core arith sets.
Qed.

(** Inversion: a parallel reduct of [lam T U] is [lam T' U']. *)
Lemma inversion_parallel_reduces_lambda :
  forall (P : Prop) T (U x : term),
  parallel_reduces_once (lam T U) x ->
  (forall T' (U' : term), x = lam T' U' -> parallel_reduces_once U U' -> P) -> P.
Proof.
  do 5 intro.
  inversion_clear H; intros.
  apply H with T' M'; auto with coc core arith sets.
Qed.

Hint Resolve parallel_reduces_once_lift parallel_reduces_once_subst: coc.

(** The body of an [lam] is a subterm. *)
Lemma subterm_lambda : forall t (m : term), subterm m (lam t m).
Proof.
  intros.
  apply sub_bind with t; auto with coc core arith sets.
Qed.

(** The body of a [prod] is a subterm. *)
Lemma subterm_product : forall t (m : term), subterm m (prod t m).
Proof.
  intros.
  apply sub_bind with t; auto with coc core arith sets.
Qed.

Hint Resolve subterm_lambda subterm_product: coc.

(** Sort occurrence is preserved by un-lifting. *)
Lemma sort_occurs_in_lift :
  forall t n k s, sort_occurs_in s (lift_rec n t k) -> sort_occurs_in s t.
Proof.
  simple induction t; simpl in |- *; intros; auto with coc core arith sets.
  generalize H; elim (le_gt_dec k n); intros; auto with coc core arith sets.
  inversion_clear H0.
  inversion_clear H1.
  apply mem_abs_l; apply H with n k; auto with coc core arith sets.
  apply mem_abs_r; apply H0 with n (S k); auto with coc core arith sets.
  inversion_clear H1.
  apply mem_app_l; apply H with n k; auto with coc core arith sets.
  apply mem_app_r; apply H0 with n k; auto with coc core arith sets.
  inversion_clear H1.
  apply mem_prod_l; apply H with n k; auto with coc core arith sets.
  apply mem_prod_r; apply H0 with n (S k); auto with coc core arith sets.
Qed.

(** Sort occurrence in a substitution comes from one of the two parts. *)
Lemma sort_occurs_in_subst :
  forall (b a : term) n s,
  sort_occurs_in s (subst_rec a b n) -> sort_occurs_in s a \/ sort_occurs_in s b.
Proof.
  simple induction b; simpl in |- *; intros; auto with coc core arith sets.
  generalize H; elim (lt_eq_lt_dec n0 n); [ intro a0 | intro b0 ].
  elim a0; intros.
  inversion_clear H0.
  left.
  apply sort_occurs_in_lift with n0 0; auto with coc core arith sets.
  intros.
  inversion_clear H0.
  inversion_clear H1.
  elim H with a n s; auto with coc core arith sets.
  elim H0 with a (S n) s; auto with coc core arith sets.
  inversion_clear H1.
  elim H with a n s; auto with coc core arith sets.
  elim H0 with a n s; auto with coc core arith sets.
  inversion_clear H1.
  elim H with a n s; auto with coc core arith sets.
  elim H0 with a (S n) s; intros; auto with coc core arith sets.
Qed.

(** Sort occurrence is preserved backward across a single reduction step. *)
Lemma sort_occurs_reduces_once_back :
  forall M N s, reduces_once M N -> sort_occurs_in s N -> sort_occurs_in s M.
Proof.
  intros M N s Hstep.
  induction Hstep as
    [ M0 N0 T0
    | M0 M0' N0 Hstep0 IH0
    | M0 N0 N0' Hstep0 IH0
    | M0 M0' N0 Hstep0 IH0
    | M0 N0 N0' Hstep0 IH0
    | M0 M0' N0 Hstep0 IH0
    | M0 N0 N0' Hstep0 IH0 ]; intros Hocc.
  - (* beta *)
    destruct (sort_occurs_in_subst M0 N0 0 s Hocc) as [HN | HM];
      auto with coc core arith sets.
  - inversion_clear Hocc; auto with coc core arith sets.
  - inversion_clear Hocc; auto with coc core arith sets.
  - inversion_clear Hocc; auto with coc core arith sets.
  - inversion_clear Hocc; auto with coc core arith sets.
  - inversion_clear Hocc; auto with coc core arith sets.
  - inversion_clear Hocc; auto with coc core arith sets.
Qed.

(** If a term reduces to a sort, that sort occurs in the original term. *)
Lemma reduces_sort_occurs : forall t s, reduces t (sort_term s) -> sort_occurs_in s t.
Proof.
  intros.
  pattern t in |- *.
  apply reduces_reverse_ind with (sort_term s); auto with coc core arith sets.
  intros M0 R Hstep Hred Hocc.
  apply sort_occurs_reduces_once_back with R; auto with coc core arith sets.
Qed.

(** A normal term is a fixed point of reduction. *)
Lemma reduces_normal : forall u v, reduces u v -> normal u -> u = v.
Proof.
  intros u v H Hn; induction H as [| M0 P0 N0 Hstep Hred IH]; auto.
  assert (M0 = P0) as Heq by auto.
  subst P0. elim (Hn N0); auto.
Qed.

(** Strong normalization is preserved by reduction. *)
Lemma strongly_normalizing_reduces : forall a b : term, strongly_normalizing a -> reduces a b -> strongly_normalizing b.
Proof.
  unfold strongly_normalizing in |- *.
  intros a b Hsn Hred; induction Hred; auto with coc core arith sets.
  apply Acc_inv with P; auto with coc core arith sets.
  constructor; auto.
Qed.

(** One-step reduction commutes with the subterm relation. *)
Lemma commute_reduces_once_subterm : commut _ subterm (transp _ reduces_once_prop).
Proof.
  red in |- *.
  intros x y Hsub z Hred.
  destruct Hred as [Hred].
  destruct Hsub as [t Hbind | Hnobind].
  - inversion_clear Hbind.
    + exists (lam t z); auto with coc core arith sets. constructor; constructor; auto with coc core arith sets.
    + exists (prod t z); auto with coc core arith sets. constructor; constructor; auto with coc core arith sets.
  - inversion_clear Hnobind.
    + exists (lam z n); auto with coc core arith sets. constructor; constructor; auto with coc core arith sets.
    + exists (app z v); auto with coc core arith sets. constructor; constructor; auto with coc core arith sets.
    + exists (app u z); auto with coc core arith sets. constructor; constructor; auto with coc core arith sets.
    + exists (prod z n); auto with coc core arith sets. constructor; constructor; auto with coc core arith sets.
Qed.

(** Strong normalization of a term implies strong normalization of all subterms. *)
Lemma subterm_sn :
  forall a : term, strongly_normalizing a -> forall b : term, subterm b a -> strongly_normalizing b.
Proof.
  unfold strongly_normalizing in |- *.
  simple induction 1; intros.
  apply Acc_intro; intros.
  elim commute_reduces_once_subterm with x b y; intros; auto with coc core arith sets.
  apply H1 with x0; auto with coc core arith sets.
Qed.

(** A [prod] is strongly normalizing when both components are. *)
Lemma strongly_normalizing_product : forall A, strongly_normalizing A -> forall B, strongly_normalizing B -> strongly_normalizing (prod A B).
Proof.
  unfold strongly_normalizing.
  intros A HA. induction HA as [a Ha IHa].
  intros B HB. induction HB as [b Hb IHb].
  apply Acc_intro. intros y [Hy].
  inversion_clear Hy.
  - apply IHa; auto.
    + constructor; auto.
    + apply Acc_intro; auto.
  - apply IHb; auto.
    constructor; auto.
Qed.

(** If [subst T M] is strongly normalizing, then [M] is. *)
Lemma strongly_normalizing_subst : forall T M, strongly_normalizing (subst T M) -> strongly_normalizing M.
Proof.
  intros.
  cut (forall t, strongly_normalizing t -> forall m : term, t = subst T m -> strongly_normalizing m).
  intros.
  apply H0 with (subst T M); auto with coc core arith sets.
  unfold strongly_normalizing in |- *.
  simple induction 1; intros.
  apply Acc_intro; intros.
  destruct H4 as [H4].
  apply H2 with (subst T y); auto with coc core arith sets.
  rewrite H3.
  unfold subst in |- *. constructor; auto with coc core arith sets.
Qed.
