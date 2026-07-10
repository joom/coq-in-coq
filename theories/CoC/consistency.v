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


From Stdlib Require Import Lia.

From CoC Require Import confluence.
From CoC Require Import typing.
From CoC Require Import decidable_conversion.
From CoC Require Import strong_normalization.
From CoC Require Import terms.

(** Apply a list of arguments to a term, rightmost argument applied first. *)
Fixpoint applist (l : list term) : term -> term :=
  fun t =>
  match l with
  | nil => t
  | arg :: args => app (applist args t) arg
  end.

(** Appending argument lists distributes over applist. *)
Lemma applist_app :
 forall t e e', applist (e ++ e') t = applist e (applist e' t).
Proof.
  simple induction e; simpl in |- *; intros; auto.
  rewrite H; trivial.
Qed.

(** The head of an applist-applied term is typable. *)
Lemma inversion_has_type_applist_head :
 forall e t l T, has_type e (applist l t) T -> {U : _ & has_type e t U}.
Proof.
  simple induction l; simpl in |- *; intros.
  exists T; trivial.

  apply inversion_has_type_app with (1 := H0); intros.
  eauto.
Qed.

(** A term is atomic if it is a variable applied to a list of arguments. *)
Definition is_atom (e : environment) t :=
  exists2 n : _, n < length e & (exists l : _, t = applist l (var n)).

(** A sort is never atomic. *)
Lemma sort_not_atom : forall e s, ~ is_atom e (sort_term s).
Proof.
  intros e s (n, lt_n, ([| t l], eq_atom)); discriminate eq_atom.
Qed.

(** A prod is never atomic. *)
Lemma prod_not_atom : forall e T M, ~ is_atom e (prod T M).
Proof.
  intros e T M (n, lt_n, ([| t l], eq_atom)); discriminate eq_atom.
Qed.

(** Applying an atomic term preserves atomicity. *)
Lemma is_atom_app : forall e a b, is_atom e a -> is_atom e (app a b).
Proof.
  intros e a b (n, lt_n, (l, eq_atom)).
  rewrite eq_atom.
  split with n; trivial.
  split with (b :: l); trivial.
Qed.

(** Reduction preserves atomicity. *)
Lemma atom_red1 : forall e t u, reduces_once t u -> is_atom e t -> is_atom e u.
Proof.
  intros e t u Hr (n, lt_n, (l, eq_atom)).
  rewrite eq_atom in Hr.
  split with n; trivial.
  generalize u Hr; clear u Hr eq_atom.
  induction l as [| a0 l0 IHl]; simpl in |- *.
  - intros z0 Hst; inversion Hst.
  - intros z0 Hst.
    inversion Hst.
    + subst; exfalso.
      match goal with
      | H : _ = lam _ _ |- _ => destruct l0; simpl in H; discriminate
      | H : lam _ _ = _ |- _ => destruct l0; simpl in H; discriminate
      end.
    + subst.
      match goal with Hred : reduces_once _ _ |- _ =>
        destruct (IHl _ Hred) as [x Heq]; rewrite Heq;
        split with (a0 :: x); reflexivity end.
    + subst.
      split with (N2 :: l0); reflexivity.
Qed.

(** Reduction preserves atomicity. *)
Lemma atom_reduction : forall e t u, reduces t u -> is_atom e t -> is_atom e u.
Proof.
  intros e t u Hred; induction Hred; intros; trivial.
  apply atom_red1 with P; auto.
Qed.

(** A sort cannot be convertible with an atomic term. *)
Lemma convertible_sort_atom : forall (s : sort) e u, is_atom e u -> convertible (sort_term s) u -> False.
Proof.
  intros.
  elim church_rosser_theorem with (1 := H0); intros x p q.
  rewrite <- reduces_normal with (1 := p) in q.
  apply (sort_not_atom e s).
  apply atom_reduction with (1 := q) (2 := H).
  red in |- *; intros u0 Hu0; inversion Hu0.
Qed.

(** A prod cannot be convertible with an atomic term. *)
Lemma convertible_product_atom : forall a b e u, is_atom e u -> convertible (prod a b) u -> False.
Proof.
  intros.
  elim church_rosser_theorem with (1 := H0); intros x p q.
  apply reduces_product_product with (1 := p); intros a0 b0 Heq redu redv.
  rewrite Heq in q.
  apply (prod_not_atom e a0 b0).
  apply atom_reduction with (1 := q) (2 := H).
Qed.

(** Normal proofs of products are either atomic or an abstraction. *)
Lemma product_inhabitants :
 forall e t u,
 has_type e t u ->
 forall a b,
 convertible u (prod a b) ->
 normal t -> is_atom e t \/ (exists a' : _, (exists m : _, t = lam a' m)).
Proof.
  simple induction 1; intros; eauto.
  elim convertible_sort_product with (1 := H0).

  elim convertible_sort_product with (1 := H0).

  left.
  exists v.
  match goal with H : item_lift _ _ _ |- _ => inversion_clear H end.
  match goal with H : nth_error _ v = Some _ |- _ =>
    apply (proj1 (nth_error_Some _ v)); rewrite H; discriminate end.

  exists (nil (A:=term)); simpl in |- *; auto.

  rename H3 into H5. rename H2 into H4. rename H1 into H3.
  rename H0 into H2. rename h into H1.
  left.
  apply is_atom_app.
  elim H3 with V Ur; intros; auto with coc.
  inversion_clear H0.
  inversion_clear H6.
  rewrite H0 in H5.
  elim H5 with (subst v x0); auto with coc.

  unfold normal; intros u1 Hu1.
  elim H5 with (app u1 v); auto with coc.

  elim convertible_sort_product with (1 := H2).

  apply H0 with a b; auto.
  apply trans_convertible_convertible with V; auto.
Qed.

(** Head-normal-form predicate: applications must be atomic. *)
Definition hnf_proofs (e : environment) (t : term) : Prop :=
  match t with
  | app _ _ => is_atom e t
  | _ => True
  end.

(** A well-typed normal term satisfies hnf_proofs. *)
Lemma hnf_proofs_sound :
 forall e t T, has_type e t T -> normal t -> hnf_proofs e t.
Proof.
  simple induction 1; simpl in |- *; intros; auto.
  apply is_atom_app.
  elim product_inhabitants with (1 := h0) (a := V) (b := Ur); intros;
   auto with coc.
  inversion_clear H3.
  inversion_clear H4.
  rewrite H3 in H2.
  elim H2 with (subst v x0); auto with coc.

  unfold normal; intros u0 Hu0.
  elim H2 with (app u0 v); auto with coc.
Qed.

(** Normal proofs of atomic types are themselves atomic. *)
Lemma atom_inhabitants :
 forall e t u u',
 has_type e t u -> convertible u u' -> is_atom e u' -> hnf_proofs e t -> is_atom e t.
Proof.
  simple induction 1; simpl in |- *; intros; auto.
  elim convertible_sort_atom with (1 := H1) (2 := H0).

  elim convertible_sort_atom with (1 := H1) (2 := H0).

  split with v.
  match goal with H : item_lift _ _ _ |- _ => inversion_clear H end.
  match goal with H : nth_error _ v = Some _ |- _ =>
    apply (proj1 (nth_error_Some _ v)); rewrite H; discriminate end.

  split with (nil (A:=term)); auto.

  elim convertible_product_atom with (1 := H4) (2 := H3).

  elim convertible_sort_atom with (1 := H3) (2 := H2).

  apply H0; auto.
  apply trans_convertible_convertible with V; auto with coc.
Qed.

(** Encoding of False as (P:Prop)P. *)
Definition absurd_prop := prod (sort_term prop) (var 0).

(** False has no proof in normal form. *)
Lemma coc_consistency_normal_form : forall t, normal t -> (has_type nil t absurd_prop -> False).
Proof.
  unfold absurd_prop in |- *.
  intros.
  elim product_inhabitants with (1 := H0) (a := sort_term prop) (b := var 0) (3 := H);
   auto with coc.
  (* Case 1: t atomic impossible because context is empty *)
  intros.
  inversion_clear H1.
  inversion H2.

  (* Case 2: t is an abstraction (lam ty M) *)
  intros (ty, (M, eq_abs)).
  rewrite eq_abs in H0.
  apply inversion_has_type_abs with (1 := H0); intros.
  specialize inversion_convertible_product_left with (1 := H4); intro conv_ty.
  specialize inversion_convertible_product_right with (1 := H4); intro conv_P.
  clear H0 H4 H3 H1.
  (* Then M is an atomic proof *)
  cut (is_atom (ty :: nil) M).
  intros (n, lt_n, (l, eq_atom)).
  simpl in lt_n.
  generalize eq_atom.
  clear eq_atom.
  replace n with 0; try lia.
  rewrite <- (rev_involutive l).
  case (rev l); simpl in |- *; intros; rewrite eq_atom in H2.
  (* Case 2.1: the head var of M is not applied *)
  apply inversion_has_type_ref with (1 := H2).
  intros U itm_U conv_T.
  simpl in itm_U; injection itm_U as <-.
  (* Impossible because var has type prop instead of (var O) *)
  cut (var 0 = sort_term prop); try discriminate.
  apply normal_form_uniqueness.
  apply trans_convertible_convertible with T; auto with coc.
  apply trans_convertible_convertible with (lift 1 ty); auto with coc.
  change (convertible (lift_rec 1 ty 0) (lift_rec 1 (sort_term prop) 0)) in |- *.
  apply convertible_convertible_lift; auto with coc.

  red in |- *; intros r red_n; inversion red_n.

  red in |- *; intros r red_n; inversion red_n.

  (* Case 2.2: the head var of M is applied *)
  rewrite applist_app in H2.
  simpl in H2.
  elim inversion_has_type_applist_head with (1 := H2); intros.
  clear H2 eq_atom.
  apply inversion_has_type_app with (1 := p); intros.
  apply inversion_has_type_ref with (1 := H0); intros U Hnth Hconv.
  simpl in Hnth; injection Hnth as <-.
  (* Impossible because head var has type prop and cannot be applied *)
  apply convertible_sort_product with prop V Ur.
  apply trans_convertible_convertible with (lift 1 ty); auto with coc.
  apply sym_convertible.
  change (convertible (lift_rec 1 ty 0) (lift_rec 1 (sort_term prop) 0)) in |- *.
  apply convertible_convertible_lift; auto with coc.

  (* Proof of M atomic *)
  apply atom_inhabitants with (1 := H2) (2 := conv_P).
  split with 0; simpl in |- *; auto with arith; split with (nil (A:=term));
   trivial.

  apply hnf_proofs_sound with (1 := H2).
  rewrite eq_abs in H.
  red in |- *; intros u0 Hu0.
  elim H with (lam ty u0); auto with coc.
Qed.

(** The calculus of constructions is consistent: False has no proof. *)
Theorem coc_consistency_theorem : forall t, (has_type nil t absurd_prop -> False).
Proof.
  intros.
  elim compute_normal_form with t; intros.
  specialize subject_reduction_theorem with (1 := p) (2 := H).
  apply coc_consistency_normal_form; trivial.

  apply strong_normalization with (1 := H).
Qed.
