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


From CoqInCoq Require Import confluence.
From CoqInCoq Require Import typing.
From CoqInCoq Require Import classification.
From CoqInCoq Require Import terms.

  (** Reducibility candidates indexed by skeletons. *)
  Fixpoint candidate (K : skeleton) : Type :=
    match K with
    | prop_skel => term -> Prop
    | prod_skel s1 s2 => candidate s1 -> candidate s2
    end.


  (** Extensional equality on base-level candidates. *)
  Definition eq_candidate (X Y : term -> Prop) : Prop :=
    forall t : term, X t <-> Y t.


  Hint Unfold eq_candidate: coc.

  (** Equality on candidates lifted to arbitrary skeletons. *)
  Fixpoint eq_can (s : skeleton) : candidate s -> candidate s -> Prop :=
    match s as s0 return (candidate s0 -> candidate s0 -> Prop) with
    | prop_skel => eq_candidate
    | prod_skel s1 s2 =>
        fun C1 C2 : candidate (prod_skel s1 s2) =>
        forall X1 X2 : candidate s1,
        eq_can s1 X1 X2 ->
        eq_can s1 X1 X1 -> eq_can s1 X2 X2 -> eq_can s2 (C1 X1) (C2 X2)
    end.

  Hint Unfold iff: coc.


  (** Candidate equality is symmetric. *)
  Lemma eq_can_sym :
   forall (s : skeleton) (X Y : candidate s), eq_can s X Y -> eq_can s Y X.
  Proof.
    simple induction s; simpl in |- *; intros; auto with coc core arith datatypes.
    unfold eq_candidate in |- *; intros.
    elim H with t; auto with coc core arith datatypes.
  Qed.

  (** Candidate equality is transitive. *)
  Lemma eq_can_trans :
   forall (s : skeleton) (a b c : candidate s),
   eq_can s a b -> eq_can s b b -> eq_can s b c -> eq_can s a c.
  Proof.
    simple induction s; simpl in |- *; intros.
    unfold eq_candidate in |- *; intros.
    elim H with t; elim H1 with t; auto with coc core arith datatypes.

    apply H0 with (b X1); auto with coc core arith datatypes.
  Qed.


  (** Candidate equality implies inclusion at base level. *)
  Lemma eq_candidate_inclusion :
   forall (t : term) (X Y : candidate prop_skel), eq_can prop_skel X Y -> X t -> Y t.
  Proof.
    intros.
    elim H with t; auto with coc core arith datatypes.
  Qed.


  (** A term is neutral if it is not a lam abstraction. *)
  Definition neutral (t : term) : Prop := forall u v : term, t <> lam u v.

  (** A set of terms forms a valid candidate of reducibility. *)
  Record is_candidate (X : term -> Prop) : Prop :=
    {incl_sn : forall t : term, X t -> strongly_normalizing t;
     clos_red : forall t : term, X t -> forall u : term, reduces_once t u -> X u;
     clos_exp :
      forall t : term, neutral t -> (forall u : term, reduces_once t u -> X u) -> X t}.


  (** Variables belong to every candidate. *)
  Lemma var_in_candidate :
   forall (n : nat) (X : term -> Prop), is_candidate X -> X (var n).
  Proof.
    intros.
    apply (clos_exp X); auto with coc core arith datatypes.
    unfold neutral in |- *; intros; discriminate.

    intros.
    inversion H0.
  Qed.


  (** Candidates are closed under transitive reduction. *)
  Lemma closure_reduces_star :
   forall R : term -> Prop,
   is_candidate R -> forall a b : term, R a -> reduces a b -> R b.
  Proof.
    intros R Hcand a b Ha Hred; induction Hred; auto with coc core arith datatypes.
    apply (clos_red R) with y; auto with coc core arith datatypes.
  Qed.


  (** Beta redexes with strongly normalizing components belong to candidates. *)
  Lemma candidate_saturated :
   forall X : term -> Prop,
   is_candidate X ->
   forall T : term,
   strongly_normalizing T ->
   forall u : term,
   strongly_normalizing u -> forall m : term, X (subst u m) -> X (app (lam T m) u).
  Proof.
    unfold strongly_normalizing in |- *.
    simple induction 2.
    simple induction 3.
    intros.
    generalize H6.
    cut (strongly_normalizing m); [intros H'; elim H' | ]; intros.
    apply (clos_exp X); intros; auto with coc core arith datatypes.
    red in |- *; intros; discriminate.

    inversion_clear H10; auto with coc core arith datatypes.
    inversion_clear H11.
    apply H2; auto with coc core arith datatypes.
    apply Acc_intro; auto with coc core arith datatypes.

    apply H8; auto with coc core arith datatypes.
    apply (clos_red X) with (subst x0 x1); auto with coc core arith datatypes.
    unfold subst in |- *; auto with coc core arith datatypes.

    apply H5; auto with coc core arith datatypes.
    apply closure_reduces_star with (subst x0 x1); auto with coc core arith datatypes.
    unfold subst in |- *; auto with coc core arith datatypes.

    apply strongly_normalizing_subst with x0.
    apply (incl_sn X); auto with coc core arith datatypes.
  Qed.


  (** A higher-order candidate is valid at every skeleton level. *)
  Fixpoint is_can (s : skeleton) : candidate s -> Prop :=
    match s as s0 return (candidate s0 -> Prop) with
    | prop_skel => fun X : term -> Prop => is_candidate X
    | prod_skel s1 s2 =>
        fun C : candidate s1 -> candidate s2 =>
        forall X : candidate s1, is_can s1 X -> eq_can s1 X X -> is_can s2 (C X)
    end.


  (** Validity of a base-level candidate is just is_candidate. *)
  Lemma is_can_prop : forall X : term -> Prop, is_can prop_skel X -> is_candidate X.
  Proof.
    auto with coc core arith datatypes.
  Qed.

  Hint Resolve is_can_prop: coc.


  (** Default candidate at each skeleton level using strong normalization. *)
  Fixpoint default_can (s : skeleton) : candidate s :=
    match s as ss return (candidate ss) with
    | prop_skel => strongly_normalizing
    | prod_skel s1 s2 => fun _ : candidate s1 => default_can s2
    end.


  (** Strong normalization forms a valid candidate. *)
  Lemma candidate_strongly_normalizing : is_candidate strongly_normalizing.
  Proof.
    apply Build_is_candidate; intros; auto with coc core arith datatypes.

    apply strongly_normalizing_reduces with t; auto with coc core arith datatypes.

    red in |- *; apply Acc_intro; auto with coc core arith datatypes.
  Qed.

  Hint Resolve candidate_strongly_normalizing: coc.


  (** The default candidate is valid at every skeleton. *)
  Lemma default_candidate_cr : forall s : skeleton, is_can s (default_can s).
  Proof.
    simple induction s; simpl in |- *; intros; auto with coc core arith datatypes.
  Qed.


  (** The default candidate is self-equal at every skeleton. *)
  Lemma default_invariant : forall s : skeleton, eq_can s (default_can s) (default_can s).
  Proof.
    simple induction s; simpl in |- *; intros; auto with coc core arith datatypes.
  Qed.


  Hint Resolve default_invariant default_candidate_cr: coc.


  (** Dependent prod candidate: universally quantifies over arguments. *)
  Definition Pi (s : skeleton) (X : term -> Prop) (F : candidate (prod_skel s prop_skel))
    (t : term) : Prop :=
    forall u : term,
    X u -> forall C : candidate s, is_can s C -> eq_can s C C -> F C (app t u).


  (** Pi preserves candidate equality. *)
  Lemma eq_can_Pi :
   forall (s : skeleton) (X Y : term -> Prop) (F1 F2 : candidate (prod_skel s prop_skel)),
   eq_can prop_skel X Y ->
   eq_can (prod_skel s prop_skel) F1 F2 -> eq_can prop_skel (Pi s X F1) (Pi s Y F2).
  Proof.
    simpl in |- *; intros; unfold iff, Pi in |- *.
    split; intros.
    elim H0 with C C (app t u); elim H with u; auto with coc core arith datatypes.

    elim H0 with C C (app t u); elim H with u; auto with coc core arith datatypes.
  Qed.


  (** Pi applied to a valid candidate and valid function yields a valid candidate. *)
  Lemma is_can_Pi :
   forall (s : skeleton) (X : term -> Prop),
   is_candidate X ->
   forall F : candidate (prod_skel s prop_skel), is_can (prod_skel s prop_skel) F -> is_candidate (Pi s X F).
  Proof.
    simpl in |- *; unfold Pi in |- *; intros.
    apply Build_is_candidate; intros.
    apply subterm_sn with (app t (var 0)); auto with coc core arith datatypes.
    apply (incl_sn (F (default_can s))); auto with coc core arith datatypes.
    apply H1; auto with coc core arith datatypes.
    apply (var_in_candidate 0 X); auto with coc core arith datatypes.

    apply (clos_red (F C)) with (app t u0); auto with coc core arith datatypes.

    apply (clos_exp (F C)); auto with coc core arith datatypes.
    red in |- *; intros; discriminate.

    generalize H3.
    cut (strongly_normalizing u).
    simple induction 1; intros.
    generalize H1.
    inversion_clear H10; intros; auto with coc core arith datatypes.
    elim H10 with T M; auto with coc core arith datatypes.

    apply (clos_exp (F C)); intros; auto with coc core arith datatypes.
    red in |- *; intros; discriminate.

    apply H8 with N2; auto with coc core arith datatypes.
    apply (clos_red X) with x; auto with coc core arith datatypes.

    apply (incl_sn X); auto with coc core arith datatypes.
  Qed.


  (** Soundness of abstraction: lam terms inhabit Pi candidates. *)
  Lemma Abs_sound :
   forall (A : term -> Prop) (s : skeleton) (F : candidate s -> term -> Prop)
     (T m : term),
   is_can prop_skel A ->
   is_can (prod_skel s prop_skel) F ->
   (forall n : term,
    A n -> forall C : candidate s, is_can s C -> eq_can s C C -> F C (subst n m)) ->
   strongly_normalizing T -> Pi s A F (lam T m).
  Proof.
    unfold Pi in |- *; simpl in |- *; intros.
    cut (is_candidate (F C)); intros; auto with coc core arith datatypes.
    apply (clos_exp (F C)); intros; auto with coc core arith datatypes.
    red in |- *; intros; discriminate.

    apply clos_red with (app (lam T m) u); auto with coc core arith datatypes.
    apply (candidate_saturated (F C)); auto with coc core arith datatypes.
    apply (incl_sn A); auto with coc core arith datatypes.
  Qed.
