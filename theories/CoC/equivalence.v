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


From CoC Require Import confluence.
From CoC Require Import eta_reduction.
From CoC Require Import typing.
From CoC Require Import eta_typing.
From CoC Require Import decidable_conversion.
From CoC Require Import strong_normalization.
From CoC Require Import terms.
From CoC Require Import inference.

(** A term is a lam abstraction. *)
Definition is_lambda (t : term) :=
  exists T : term, (exists M : term, t = lam T M).

(** A normal type and normal body yield a normal lam. *)
Lemma normal_normal_abs :
 forall T M : term, normal T -> normal M -> normal (lam T M).
Proof.
  intros T M HT HM; unfold normal, not in |- *; intros N Hred.
  inversion_clear Hred.
  elim HT with M'; auto with coc.
  elim HM with M'; auto with coc.
Qed.

(** Normal head and argument with non-lam head yield a normal app. *)
Lemma normal_normal_app :
 forall M N : term, normal M -> normal N -> ~ is_lambda M -> normal (app M N).
Proof.
  intros; unfold normal, not in |- *; intros.
  generalize H H1; clear H H1; inversion_clear H2.
  intros.
  apply H1.
  unfold is_lambda in |- *; split with T; split with M0; trivial.
  intros H1; elim H1 with N1; auto with coc.
  elim H0 with N2; auto with coc.
Qed.


(** Normal domain and codomain yield a normal prod. *)
Lemma normal_normal_prod :
 forall T U : term, normal T -> normal U -> normal (prod T U).
Proof.
  intros T U HT HU; unfold normal, not in |- *; intros N Hred.
  inversion_clear Hred.
  elim HT with N1; auto with coc.
  elim HU with N2; auto with coc.
Qed.

Hint Resolve normal_normal_abs normal_normal_app normal_normal_prod: ecoc.

(** A normal lam has normal type and body components. *)
Lemma normal_abs_inv :
 forall T M : term, normal (lam T M) -> normal T /\ normal M.
Proof.
  unfold normal in |- *; intuition.
  apply H with (lam u M); auto with coc.
  apply H with (lam T u); auto with coc.
Qed.

(** A normal app has normal head, normal argument, and non-lam head. *)
Lemma normal_app_inv :
 forall M N : term, normal (app M N) -> normal M /\ normal N /\ ~ is_lambda M.
Proof.
  unfold normal in |- *; intuition.
  apply H with (app u N); auto with coc.
  apply H with (app M u); auto with coc.
  generalize H0; clear H0; unfold is_lambda in |- *; intros (T, (x0, H0)).
  rewrite H0 in H; apply H with (subst N x0); auto with coc.
Qed.

(** A normal prod has normal domain and codomain. *)
Lemma normal_prod_inv :
 forall T U : term, normal (prod T U) -> normal T /\ normal U.
Proof.
  unfold normal in |- *; intuition.
  apply H with (prod u U); auto with coc.
  apply H with (prod T u); auto with coc.
Qed.


(** Conversion on normal forms up to type erasure. *)
Inductive normal_form_eta_convertible : term -> term -> Prop :=
  | nf_conv_var : forall n : nat, normal_form_eta_convertible (var n) (var n)
  | nf_conv_app :
      forall M M' N N' : term,
      normal_form_eta_convertible M M' ->
      ~ is_lambda M -> normal_form_eta_convertible N N' -> normal_form_eta_convertible (app M N) (app M' N')
  | nf_conv_lam :
      forall T T' M M' : term,
      normal_form_eta_convertible M M' ->
      normal T -> normal T' -> normal_form_eta_convertible (lam T M) (lam T' M')
  | nf_conv_sort : forall s : sort, normal_form_eta_convertible (sort_term s) (sort_term s)
  | nf_conv_prod :
      forall T T' U U' : term,
      normal_form_eta_convertible T T' -> normal_form_eta_convertible U U' -> normal_form_eta_convertible (prod T U) (prod T' U').

Hint Resolve nf_conv_var nf_conv_app nf_conv_lam nf_conv_sort nf_conv_prod: ecoc.

(** The sort prop is normal. *)
Lemma normal_prop : normal (sort_term prop).
Proof.
  unfold normal, not in |- *; intros.
  inversion H.
Qed.
Hint Resolve normal_prop: ecoc.


(** Erasure reduction preserves the non-lam property. *)
Lemma not_is_lambda_eta_reduces_once :
 forall M N : term, eta_reduces_once M N -> normal M -> ~ is_lambda M -> ~ is_lambda N.
Proof.
  simple induction 1; intros.
  elim H0 with (subst N0 M0); auto with coc.
  elim H1; unfold is_lambda in |- *; split with T; split with M0; trivial.
  elim H3; unfold is_lambda in |- *; split with M0; split with N0; trivial.
  elim H3; unfold is_lambda in |- *; split with N0; split with M0; trivial.
  unfold not in |- *; unfold is_lambda in |- *; intros (x, (x0, H4)); discriminate.
  unfold not in |- *; unfold is_lambda in |- *; intros (x, (x0, H4)); discriminate.
  unfold not in |- *; unfold is_lambda in |- *; intros (x, (x0, H4)); discriminate.
  unfold not in |- *; unfold is_lambda in |- *; intros (x, (x0, H4)); discriminate.
Qed.

Hint Resolve not_is_lambda_eta_reduces_once: ecoc.

(** One-step erasure reduction preserves normality. *)
Lemma eta_reduces_once_normal_normal :
 forall M N : term, eta_reduces_once M N -> normal M -> normal N.
Proof.
  simple induction 1; intros.
  elim H0 with (subst N0 M0); auto with coc.
  elim (normal_abs_inv T M0 H0); auto with ecoc.
  elim (normal_abs_inv M0 N0 H2); auto with ecoc.
  elim (normal_abs_inv N0 M0 H2); auto with ecoc.
  elim (normal_app_inv M1 M2 H2); intros.
  elim H4; eauto with ecoc.
  elim (normal_app_inv M1 M2 H2); intros.
  elim H4; eauto with ecoc.
  elim (normal_prod_inv M1 M2 H2); auto with ecoc.
  elim (normal_prod_inv M1 M2 H2); auto with ecoc.
Qed.

Hint Resolve eta_reduces_once_normal_normal: ecoc.

(** Normal forms are normal_form_eta_convertible-reflexive. *)
Lemma refl_normal_form_eta_convertible : forall t : term, normal t -> normal_form_eta_convertible t t.
Proof.
  simple induction t; auto with ecoc; intros.
  elim (normal_abs_inv t0 t1 H1); auto with ecoc.
  elim (normal_app_inv t0 t1 H1); intros.
  elim H3; auto with ecoc.
  elim (normal_prod_inv t0 t1 H1); auto with ecoc.
Qed.

Hint Resolve refl_normal_form_eta_convertible: ecoc.

(** normal_form_eta_convertible preserves the non-lam property. *)
Lemma normal_form_eta_convertible_not_lambda :
 forall M N : term, normal_form_eta_convertible M N -> ~ is_lambda M -> ~ is_lambda N.
Proof.
  intros M N H; inversion_clear H; auto; intros.
  unfold is_lambda, not in |- *; intros (x, (x0, H3)); discriminate.
  elim H; unfold is_lambda in |- *; split with T; split with M0; trivial.
  unfold is_lambda, not in |- *; intros (x, (x0, H3)); discriminate.
Qed.

Hint Resolve normal_form_eta_convertible_not_lambda: ecoc.

(** normal_form_eta_convertible is symmetric. *)
Lemma sym_normal_form_eta_convertible : forall M N : term, normal_form_eta_convertible M N -> normal_form_eta_convertible N M.
Proof.
  simple induction 1; eauto with ecoc; eauto with ecoc.
Qed.

Hint Resolve sym_normal_form_eta_convertible: ecoc.

(** normal_form_eta_convertible is transitive. *)
Lemma trans_normal_form_eta_convertible :
 forall M N : term,
 normal_form_eta_convertible M N -> forall P : term, normal_form_eta_convertible N P -> normal_form_eta_convertible M P.
Proof.
  simple induction 1; auto with ecoc; intros.
  inversion H5; auto with ecoc.
  inversion H4; auto with ecoc.
  inversion H4; auto with ecoc.
Qed.

(** One-step erasure reduction on a normal term yields normal_form_eta_convertible. *)
Lemma eta_reduces_once_normal_form_convertible :
 forall T T' : term, eta_reduces_once T T' -> normal T -> normal_form_eta_convertible T T'.
Proof.
  simple induction 1; intros.
  elim H0 with (subst N M); auto with coc.
  elim (normal_abs_inv T0 M H0); intros.
  apply trans_normal_form_eta_convertible with (lam (sort_term prop) M); auto with ecoc.
  elim (normal_abs_inv M N H2); eauto with ecoc.
  elim (normal_abs_inv N M H2); eauto with ecoc.
  elim (normal_app_inv M1 M2 H2); intros.
  elim H4; eauto with ecoc.
  elim (normal_app_inv M1 M2 H2); intros.
  elim H4; eauto with ecoc.
  elim (normal_prod_inv M1 M2 H2); auto with ecoc.
  elim (normal_prod_inv M1 M2 H2); auto with ecoc.
Qed.

Hint Resolve eta_reduces_once_normal_form_convertible: ecoc.

(** Multi-step erasure reduction on a normal term yields normal_form_eta_convertible. *)
Lemma eta_reduces_normal_form_convertible :
 forall T T' : term, eta_reduces T T' -> normal T -> normal_form_eta_convertible T T'.
Proof.
  intros T T' H.
  pattern T in |- *.
  apply eta_reduces_reverse_ind with T'; auto with ecoc sets.
  intros.
  apply trans_normal_form_eta_convertible with R; eauto with ecoc.
Qed.

Hint Resolve eta_reduces_normal_form_convertible: ecoc.

(** Normal forms related by eta_convertible are related by normal_form_eta_convertible. *)
Lemma normal_eta_convertible_normal_form :
 forall T T' : term, eta_convertible T T' -> normal T -> normal T' -> normal_form_eta_convertible T T'.
Proof.
  intros T T' H.
  elim eta_church_rosser with T T'; auto with ecoc; intros.
  apply trans_normal_form_eta_convertible with x; eauto with ecoc.
Qed.

Hint Resolve normal_eta_convertible_normal_form: ecoc.


(** normal_form_eta_convertible implies eta_convertible. *)
Lemma normal_form_eta_convertible_eta_convertible : forall M N : term, normal_form_eta_convertible M N -> eta_convertible M N.
Proof.
  simple induction 1; auto with ecoc.
Qed.
Hint Resolve normal_form_eta_convertible_eta_convertible: ecoc.

(** Pointwise equivalence of environments under a relation. *)
Inductive equiv_env (P : term -> term -> Prop) : environment -> environment -> Prop :=
  | equiv_env_nil : equiv_env P nil nil
  | equiv_env_cons :
      forall (t t' : term) (e e' : environment),
      P t t' -> equiv_env P e e' -> equiv_env P (t :: e) (t' :: e').

(** Equivalent environments map the same position to related items. *)
Lemma equiv_env_item :
 forall (P : term -> term -> Prop) (n : nat) (e e' : environment) (A B : term),
 nth_error e n = Some A -> nth_error e' n = Some B -> equiv_env P e e' -> P A B.
Proof.
  intro P; induction n as [|n0 IHn].
  - intros e e' A B HA HB Heq.
    destruct e as [|h e'']; simpl in HA; [discriminate|].
    destruct e' as [|h' e''']; simpl in HB; [discriminate|].
    injection HA as <-. injection HB as <-.
    inversion Heq; trivial.
  - intros e e' A B HA HB Heq.
    destruct e as [|h e'']; simpl in HA; [discriminate|].
    destruct e' as [|h' e''']; simpl in HB; [discriminate|].
    inversion_clear Heq. eapply IHn; eauto.
Qed.


(** normal_form_eta_convertible-related non-lam terms in equivalent environments have eta_convertible types. *)
Lemma eta_has_type_normal_form_convertible :
 forall M M' : term,
 normal_form_eta_convertible M M' ->
 ~ is_lambda M ->
 forall (e e' : environment) (A B : term),
 equiv_env eta_convertible e e' -> eta_has_type e M A -> eta_has_type e' M' B -> eta_convertible A B.
Proof.
  simple induction 1; intros.
  apply inversion_eta_has_type_ref with e A n; trivial; intros.
  apply inversion_eta_has_type_ref with e' B n; trivial; intros.
  apply trans_eta_convertible with (lift (S n) U); trivial.
  apply trans_eta_convertible with (lift (S n) U0); auto with ecoc.
  unfold lift in |- *; apply eta_convertible_lift.
  apply equiv_env_item with n e e'; trivial.

  apply inversion_eta_has_type_application with e M0 N A; trivial.
  intros.
  apply inversion_eta_has_type_application with e' M'0 N' B; trivial.
  intros.
  apply trans_eta_convertible with (subst N Ur); trivial.
  apply sym_eta_convertible; apply trans_eta_convertible with (subst N' Ur0); trivial.
  unfold subst in |- *; apply eta_convertible_subst.
  apply sym_eta_convertible; apply normal_form_eta_convertible_eta_convertible; trivial.

  cut (eta_convertible (prod V Ur) (prod V0 Ur0)).
  intros.
  apply sym_eta_convertible.
  eapply inversion_eta_convertible_product_right; eauto.

  apply H1 with e e'; trivial.

  elim H4; unfold is_lambda in |- *; split with T; split with M0; trivial.

  generalize H2 H3; clear H2 H3; case s; intros.
  elim (inversion_eta_has_type_kind e A H2).

  apply trans_eta_convertible with (sort_term kind).
  eapply inversion_eta_has_type_prop; eauto.

  apply sym_eta_convertible; eapply inversion_eta_has_type_prop; eauto.

  apply trans_eta_convertible with (sort_term kind).
  eapply inversion_eta_has_type_set; eauto.

  apply sym_eta_convertible; eapply inversion_eta_has_type_set; eauto.

  apply inversion_eta_has_type_product with e T U A; trivial; intros.
  apply inversion_eta_has_type_product with e' T' U' B; trivial; intros.
  apply trans_eta_convertible with (sort_term s2); auto with ecoc.
  apply trans_eta_convertible with (sort_term s3); auto with ecoc.
  apply H3 with (T :: e) (T' :: e'); trivial.
  unfold not, is_lambda in |- *; intros (x, (x0, H14)).
  rewrite H14 in H9.
  apply inversion_eta_has_type_lambda with (T :: e) x x0 (sort_term s2); trivial.
  intros.
  elim (eta_convertible_sort_product s2 x T0); auto with ecoc.

  constructor; auto with ecoc.
Qed.

(** Every environment is eta_convertible-equivalent to itself. *)
Lemma refl_equiv_env : forall e : environment, equiv_env eta_convertible e e.
Proof.
  simple induction e; constructor; auto with ecoc.
Qed.
Hint Resolve refl_equiv_env: ecoc.

(** normal_form_eta_convertible-related terms with convertible types in the same environment are equal. *)
Lemma eta_convertible_eq :
 forall (e : environment) (a Ta : term),
 eta_has_type e a Ta ->
 forall b Tb : term, eta_has_type e b Tb -> normal_form_eta_convertible a b -> eta_convertible Ta Tb -> a = b.
Proof.
  simple induction 1; intros.
  (* sort et var *)
  inversion H2; trivial.
  inversion H2; trivial.
  inversion H3; trivial.

  (* lam *)
  inversion H7.
  rewrite <- H13 in H6.
  apply inversion_eta_has_type_lambda with e0 T' M' Tb; trivial.
  intros; cut (T = T'); intros.
  rewrite H19; cut (M = M'); intros.
  rewrite H20; trivial.
  apply H5 with T1; trivial.
  rewrite H19; trivial.
  apply inversion_eta_convertible_product_right with T T'.
  apply trans_eta_convertible with Tb; auto with ecoc.
  apply H1 with (sort_term s0); trivial.
  apply normal_eta_convertible_normal_form; trivial.
  apply inversion_eta_convertible_product_left with U T1.
  apply trans_eta_convertible with Tb; auto with ecoc.
  cut (eta_convertible T T').
  intros; apply eta_has_type_normal_form_convertible with T T' e0 e0; auto with ecoc.
  unfold not, is_lambda in |- *; intros (x, (x0, H20)).
  rewrite H20 in H0.
  apply inversion_eta_has_type_lambda with e0 x x0 (sort_term s1); trivial.
  intros.
  elim (eta_convertible_sort_product s1 x T2); auto with ecoc.
  apply inversion_eta_convertible_product_left with U T1.
  apply trans_eta_convertible with Tb; auto with ecoc.

  (* app *)
  inversion H5.
  rewrite <- H11 in H4.
  apply inversion_eta_has_type_application with e0 M' N' Tb; trivial.

  intros; cut (u = M').
  intros; cut (v = N').
  intros; rewrite H16; rewrite H17; trivial.

  apply H1 with V0; trivial.
  apply inversion_eta_convertible_product_left with Ur Ur0.
  apply eta_has_type_normal_form_convertible with u M' e0 e0; auto with ecoc.

  apply H3 with (prod V0 Ur0); trivial.
  apply eta_has_type_normal_form_convertible with u M' e0 e0; auto with ecoc.

  (* prod *)
  inversion H5.
  rewrite <- H10 in H4.
  apply inversion_eta_has_type_product with e0 T' U' Tb; trivial.
  intros; cut (T = T').
  intros; cut (U = U').
  intros; rewrite H15; rewrite H16; trivial.

  apply H3 with (sort_term s3); auto.
  rewrite H15; trivial.

  apply trans_eta_convertible with Tb; auto with ecoc.

  apply H1 with (sort_term s0); auto.
  apply eta_has_type_normal_form_convertible with T T' e0 e0; auto with ecoc.
  unfold not, is_lambda in |- *; intros (x, (x0, H15)).
  rewrite H15 in H0.
  apply inversion_eta_has_type_lambda with e0 x x0 (sort_term s1); trivial.
  intros.
  elim (eta_convertible_sort_product s1 x T1); auto with ecoc.

  (* Conv *)
  apply H1 with Tb; trivial.
  apply trans_eta_convertible with V; auto with ecoc.
Qed.


(** Every typed term reduces to a normal form that is also typed. *)
Lemma has_type_is_normal_form :
 forall (e : environment) (a Ta : term),
 has_type e a Ta -> { a' : term & ((reduces a a') * (normal a' * has_type e a' Ta))%type }.
Proof.
  intros.
  elim (compute_normal_form a).
  intros x Hred Hnorm; exists x; repeat split; trivial.
  apply subject_reduction_theorem with a; trivial.
  apply strong_normalization with e Ta; trivial.
Qed.


(** Erasure-convertible typed terms are convertible. *)
Lemma eta_convertible_convertible :
 forall (e : environment) (a b Ta Tb : term),
 has_type e a Ta -> has_type e b Tb -> eta_convertible a b -> eta_convertible Ta Tb -> convertible a b.
Proof.
  intros.
  generalize (has_type_is_normal_form e a Ta H).
  generalize (has_type_is_normal_form e b Tb H0).
  intros [x [H3a [H3b H3c]]] [x0 [H4a [H4b H4c]]].
  cut (x = x0).
  intros Heq.
  rewrite <- Heq in H4a.
  apply trans_convertible_convertible with x; auto with coc.
  apply sym_convertible; auto with coc.
  apply eta_convertible_eq with e Tb Ta; auto with coc ecoc.
  apply has_type_eta_has_type; trivial.
  apply has_type_eta_has_type; trivial.
  apply normal_eta_convertible_normal_form; trivial.
  apply trans_eta_convertible with b.
  apply sym_eta_convertible; apply eta_reduces_eta_convertible; auto with ecoc.
  apply trans_eta_convertible with a; auto with ecoc.
  apply eta_reduces_eta_convertible; auto with ecoc.
Qed.

(** eta_convertible-related terms typed by sorts have eta_convertible-related sort types. *)
Lemma has_type_sort_eta_convertible :
 forall (e : environment) (V U : term) (r s : sort),
 has_type e V (sort_term s) -> has_type e U (sort_term r) -> eta_convertible U V -> eta_convertible (sort_term s) (sort_term r).
Proof.
  intros.
  generalize (has_type_is_normal_form e V (sort_term s) H).
  generalize (has_type_is_normal_form e U (sort_term r) H0).
  intros [x [H2a [H2b H2c]]] [x0 [H3a [H3b H3c]]].
  apply eta_has_type_normal_form_convertible with x0 x e e; eauto with ecoc.
  apply normal_eta_convertible_normal_form; auto with ecoc.
  apply trans_eta_convertible with U; auto with ecoc.
  apply sym_eta_convertible.
  apply trans_eta_convertible with V; trivial.
  apply eta_reduces_eta_convertible; auto with ecoc.

  apply eta_reduces_eta_convertible; auto with ecoc.

  unfold not in |- *; unfold is_lambda in |- *; intros (x1, (x2, H6)).
  rewrite H6 in H3c.
  apply inversion_eta_has_type_lambda with e x1 x2 (sort_term s); trivial.
  apply has_type_eta_has_type; trivial.

  intros.
  elim (eta_convertible_sort_product s x1 T); auto with ecoc.

  apply has_type_eta_has_type; trivial.

  apply has_type_eta_has_type; trivial.
Qed.


(** Mutual induction principle for the expansion-based typing judgments. *)
Scheme eta_ht_mut := Induction for eta_has_type Sort Prop
  with eta_wf_mut := Induction for eta_well_formed Sort Prop.

(** [has_type] is decidable, so it suffices to show that a term with an
    expansion-based typing cannot fail to have a standard type.  We prove the
    double-negated statement by induction over the (propositional)
    expansion-based judgments, materialising the standard-typing derivations of
    the sub-terms through decidability whenever we need them. *)

(** Materialise a standard typing derivation from its double negation, using
    decidability of typing. *)
Lemma has_type_of_nn :
 forall (e : environment) (M t : term),
 ((has_type e M t -> False) -> False) -> has_type e M t.
Proof.
  intros e M t Hnn.
  destruct (decide_type e M t) as [Hyes | Hno].
  - exact Hyes.
  - exfalso; apply Hnn; exact Hno.
Qed.

(** Materialise a well-formedness derivation from its double negation. *)
Lemma well_formed_of_nn :
 forall e : environment,
 ((well_formed e -> False) -> False) -> well_formed e.
Proof.
  intros e Hnn.
  destruct (decide_well_formed e) as [Hyes | Hno].
  - exact Hyes.
  - exfalso; apply Hnn; exact Hno.
Qed.

(** Double-negated version of the equivalence, proved by mutual induction. *)
Lemma eta_has_type_has_type_nn :
 forall (e : environment) (M t : term),
 eta_has_type e M t -> (has_type e M t -> False) -> False.
Proof.
  intros e M t H.
  apply
   (eta_ht_mut
      (fun e M t (_ : eta_has_type e M t) => (has_type e M t -> False) -> False)
      (fun e (_ : eta_well_formed e) => (well_formed e -> False) -> False));
   try exact H.
  (* eta_type_prop *)
  - intros e0 w IHw Hnot.
    apply Hnot; apply type_prop; apply well_formed_of_nn; exact IHw.
  (* eta_type_set *)
  - intros e0 w IHw Hnot.
    apply Hnot; apply type_set; apply well_formed_of_nn; exact IHw.
  (* eta_type_var *)
  - intros e0 w IHw v t0 Hitem Hnot.
    apply Hnot; apply type_var; [ apply well_formed_of_nn; exact IHw | exact Hitem ].
  (* eta_type_abs *)
  - intros e0 T s1 dT IHT M0 U0 s2 dU IHU dM IHM Hnot.
    apply Hnot; apply type_abs with s1 s2;
      apply has_type_of_nn; [ exact IHT | exact IHU | exact IHM ].
  (* eta_type_app *)
  - intros e0 v V dv IHv u0 Ur du IHu Hnot.
    apply Hnot; apply type_app with V;
      apply has_type_of_nn; [ exact IHv | exact IHu ].
  (* eta_type_prod *)
  - intros e0 T s1 dT IHT U0 s2 dU IHU Hnot.
    apply Hnot; apply type_prod with s1;
      apply has_type_of_nn; [ exact IHT | exact IHU ].
  (* eta_type_eta_convertible *)
  - intros e0 t0 U0 V dt0 IHt0 Hconv s dV IHV Hnot.
    assert (Ht0 : has_type e0 t0 U0) by (apply has_type_of_nn; exact IHt0).
    assert (HV : has_type e0 V (sort_term s)) by (apply has_type_of_nn; exact IHV).
    generalize (type_case e0 t0 U0 Ht0).
    intros [(x, H5)| H6].
    + apply Hnot; apply type_conv with U0 s; trivial.
      apply eta_convertible_convertible with e0 (sort_term x) (sort_term s); trivial.
      apply has_type_sort_eta_convertible with e0 U0 V; auto with ecoc.
    + rewrite H6 in Hconv.
      apply (inversion_eta_has_type_convertible_kind e0 V (sort_term s)).
      * apply sym_eta_convertible; exact Hconv.
      * exact dV.
  (* eta_well_formed_nil *)
  - intros Hnot; apply Hnot; apply wf_nil.
  (* eta_well_formed_var *)
  - intros e0 T s dT IHT Hnot.
    apply Hnot; apply wf_var with s; apply has_type_of_nn; exact IHT.
Qed.

(** Erasure typing implies standard typing. *)
Lemma eta_has_type_has_type : forall (e : environment) (M t : term), eta_has_type e M t -> has_type e M t.
Proof.
  intros e M t H.
  apply has_type_of_nn.
  apply eta_has_type_has_type_nn; exact H.
Qed.
