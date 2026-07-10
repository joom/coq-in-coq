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

(** Utility lemmas and definitions for lists:
    positional insertion, truncation, and decidable named lookup. *)

From Stdlib Require Import Arith Lia.
From Stdlib Require Export List.

Global Set Asymmetric Patterns.

Hint Resolve in_eq in_cons: coc.

(** [insert x n l1 l2] holds when [l2] is [l1] with [x] inserted at position [n]. *)
Definition insert {A : Type} (x : A) (n : nat) (l1 l2 : list A) : Prop :=
  l2 = firstn n l1 ++ x :: skipn n l1 /\ n <= length l1.

(** Inserting at position 0 prepends the element. *)
Lemma insert_head {A : Type} (x : A) (l : list A) : insert x 0 l (x :: l).
Proof.
  unfold insert; simpl; auto with arith.
Qed.

(** Insertion at [S n] in [y :: l] reduces to insertion at [n] in [l]. *)
Lemma insert_tail {A : Type} (x : A) (n : nat) (l il : list A) (y : A) :
  insert x n l il -> insert x (S n) (y :: l) (y :: il).
Proof.
  unfold insert; intros [Heq Hle]; split.
  - simpl. f_equal. exact Heq.
  - simpl. lia.
Qed.

(** [first_item x l n] holds when [x] first occurs at position [n] in [l]:
    [nth_error l n = Some x] and [x] does not occur in [firstn n l]. *)
Definition first_item {A : Set} (x : A) (l : list A) (n : nat) : Prop :=
  nth_error l n = Some x /\ ~ In x (firstn n l).

(** Backward-compat: x is first at index 0 in x :: l. *)
Lemma first_item_head {A : Set} (x : A) (l : list A) : first_item x (x :: l) 0.
Proof.
  unfold first_item; simpl; auto.
Qed.

(** Backward-compat: if x is first at n in l and x <> y, then first at S n in y :: l. *)
Lemma first_item_tail {A : Set} (x : A) (l : list A) (y : A) (n : nat) :
  first_item x l n -> x <> y -> first_item x (y :: l) (S n).
Proof.
  unfold first_item; intros [Hnth Hnotin] Hne.
  split; [exact Hnth | simpl; intros [Heq | Hin]; [exact (Hne (eq_sym Heq)) | exact (Hnotin Hin)]].
Qed.

Hint Resolve first_item_head first_item_tail: coc.

(** The position of the first occurrence is unique. *)
Lemma first_item_unique {A : Set} :
  forall (x : A) (l : list A) (n : nat),
  first_item x l n -> forall m : nat, first_item x l m -> m = n.
Proof.
  unfold first_item.
  intros x l n [Hn Hnotin] m [Hm Hmnotin].
  revert l n m Hn Hnotin Hm Hmnotin.
  induction l as [|h l' IH]; intros n m Hn Hnotin Hm Hmnotin.
  - destruct n; simpl in Hn; discriminate.
  - destruct n as [|n'], m as [|m'].
    + reflexivity.
    + simpl in Hn; injection Hn as Hn; subst h.
      exfalso; apply Hmnotin. simpl. left. reflexivity.
    + simpl in Hm; injection Hm as Hm; subst h.
      exfalso; apply Hnotin. simpl. left. reflexivity.
    + f_equal. apply IH with (n := n') (m := m').
      * exact Hn.
      * simpl in Hnotin. intros Hin; apply Hnotin; right; exact Hin.
      * exact Hm.
      * simpl in Hmnotin. intros Hin; apply Hmnotin; right; exact Hin.
Qed.

(** Decidable first-occurrence lookup using equality decision. *)
Definition list_index {A : Set} (eq_dec : forall x y : A, {x = y} + {x <> y}) :
  forall (x : A) (l : list A), {n : nat | first_item x l n} + {~ In x l}.
Proof.
  refine
    (fix list_index (x : A) (l : list A) {struct l} :
      {n : nat | first_item x l n} + {~ In x l} :=
      match l return ({n : nat | first_item x l n} + {~ In x l}) with
      | nil => inright _ _
      | y :: l1 =>
          match eq_dec x y with
          | left found => inleft _ (exist _ 0 _)
          | right notfound =>
              match list_index x l1 with
              | inleft (exist k in_tail) => inleft _ (exist _ (S k) _)
              | inright not_tail => inright _ _
              end
          end
      end).
  - simpl; tauto.
  - subst y. apply first_item_head.
  - apply first_item_tail; [exact in_tail | exact notfound].
  - simpl; intros [-> | H]; [exact (notfound eq_refl) | exact (not_tail H)].
Defined.

Hint Resolve insert_head insert_tail: coc.
Hint Resolve in_eq in_cons first_item_head first_item_tail: coc.
Hint Unfold incl: coc.

(** [insert x n l1 l2] preserves list length. *)
Lemma insert_length {A : Type} (x : A) (n : nat) (l1 l2 : list A) :
  insert x n l1 l2 -> length l2 = S (length l1).
Proof.
  unfold insert; intros [Heq Hle]; subst l2.
  rewrite length_app; simpl.
  rewrite firstn_length_le by lia.
  rewrite length_skipn. lia.
Qed.

(** Insertion preserves [nth] at indices >= the insertion point. *)
Lemma insert_nth_ge {A : Type} :
  forall (k : nat) (f g : list A) (d x : A),
  insert x k f g ->
  forall n : nat, k <= n -> nth n f d = nth (S n) g d.
Proof.
  unfold insert; intros k f g d x [Heq Hle] n Hkn; subst g.
  revert k f Hle Hkn; induction n as [|n' IH]; intros k f Hle Hkn.
  - assert (k = 0) by lia; subst k. simpl. destruct f; simpl; auto.
  - destruct k as [|k'].
    + simpl. destruct f; simpl; auto.
    + simpl. destruct f as [|h f'].
      * simpl in Hle; lia.
      * simpl. apply IH; simpl in Hle; lia.
Qed.

(** Insertion preserves [nth] at indices strictly below the insertion point. *)
Lemma insert_nth_lt {A : Type} :
  forall (k : nat) (f g : list A) (d x : A),
  insert x k f g -> forall n : nat, k > n -> nth n f d = nth n g d.
Proof.
  unfold insert; intros k f g d x [Heq Hle] n Hkn; subst g.
  revert n f Hle Hkn; induction k as [|k' IH]; intros n f Hle Hkn.
  - lia.
  - destruct f as [|h f']; [simpl in Hle; lia|].
    destruct n as [|n'].
    + simpl. auto.
    + simpl. apply IH; simpl in Hle; lia.
Qed.

(** The element at the insertion index is the inserted element. *)
Lemma insert_nth_eq {A : Type} :
  forall (k : nat) (f g : list A) (d x : A),
  insert x k f g -> nth k g d = x.
Proof.
  unfold insert; intros k f g d x [Heq Hle]; subst g.
  revert k f Hle; induction k as [|k' IH]; intros f Hle.
  - simpl. destruct f; simpl; auto.
  - destruct f as [|h f']; [simpl in Hle; lia|].
    simpl. apply IH; simpl in Hle; lia.
Qed.
Hint Resolve Forall_nil Forall_cons: coc.
Hint Resolve Forall2_nil Forall2_cons: coc.
