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
From CoqInCoq Require Import eta_reduction.
From CoqInCoq Require Export list_utils.
From CoqInCoq Require Import typing.
From CoqInCoq Require Import terms.


Section Typage.

  (** Well-formedness and typing judgments using expansion-based conversion. *)
  Inductive eta_well_formed : environment -> Prop :=
    | eta_well_formed_nil : eta_well_formed nil
    | eta_well_formed_var :
        forall (e : environment) (T : term) (s : sort),
        eta_has_type e T (sort_term s) -> eta_well_formed (T :: e)
  with eta_has_type : environment -> term -> term -> Prop :=
    | eta_type_prop : forall e : environment, eta_well_formed e -> eta_has_type e (sort_term prop) (sort_term kind)
    | eta_type_set : forall e : environment, eta_well_formed e -> eta_has_type e (sort_term set) (sort_term kind)
    | eta_type_var :
        forall e : environment,
        eta_well_formed e ->
        forall (v : nat) (t : term), item_lift t e v -> eta_has_type e (var v) t
    | eta_type_abs :
        forall (e : environment) (T : term) (s1 : sort),
        eta_has_type e T (sort_term s1) ->
        forall (M U : term) (s2 : sort),
        eta_has_type (T :: e) U (sort_term s2) ->
        eta_has_type (T :: e) M U -> eta_has_type e (lam T M) (prod T U)
    | eta_type_app :
        forall (e : environment) (v V : term),
        eta_has_type e v V ->
        forall u Ur : term,
        eta_has_type e u (prod V Ur) -> eta_has_type e (app u v) (subst v Ur)
    | eta_type_prod :
        forall (e : environment) (T : term) (s1 : sort),
        eta_has_type e T (sort_term s1) ->
        forall (U : term) (s2 : sort),
        eta_has_type (T :: e) U (sort_term s2) -> eta_has_type e (prod T U) (sort_term s2)
    | eta_type_eta_convertible :
        forall (e : environment) (t U V : term),
        eta_has_type e t U ->
        eta_convertible U V -> forall s : sort, eta_has_type e V (sort_term s) -> eta_has_type e t V.

  Hint Resolve eta_well_formed_nil eta_type_prop eta_type_set eta_type_var: ecoc.


(** Standard typing implies expansion-based typing. *)
Lemma has_type_eta_has_type : forall (e : environment) (a Ta : term), has_type e a Ta -> eta_has_type e a Ta.
Proof.
  fix has_type_eta_has_type 4.
  intros.
  case H; intros.
  apply eta_type_prop.
  case H0.
  apply eta_well_formed_nil.

  intros; apply eta_well_formed_var with s.
  apply has_type_eta_has_type; trivial.

  apply eta_type_set.
  case H0.
  apply eta_well_formed_nil.

  intros; apply eta_well_formed_var with s; auto.

  apply eta_type_var.
  case H0.
  apply eta_well_formed_nil.

  intros; apply eta_well_formed_var with s.
  apply has_type_eta_has_type; trivial.

  trivial.

  apply eta_type_abs with s1 s2; auto.

  apply eta_type_app with V; auto.

  apply eta_type_prod with s1; auto.

  apply eta_type_eta_convertible with U s; auto.
  apply convertible_eta_convertible; trivial.
Qed.

(** Typing of prop or set sorts in a well-formed environment. *)
  Lemma eta_type_prop_set :
   forall s : sort,
   is_prop s -> forall e : environment, eta_well_formed e -> eta_has_type e (sort_term s) (sort_term kind).
  Proof.
    simple destruct 1; intros; rewrite H0.
    apply eta_type_prop; trivial.
    apply eta_type_set; trivial.
  Qed.

  (** Typed terms have de Bruijn indices within the environment length. *)
  Lemma eta_has_type_free_db_below :
   forall (e : environment) (t T : term), eta_has_type e t T -> free_db_below (length e) t.
  Proof.
    simple induction 1; intros; auto with coc ecoc core arith datatypes.
    inversion_clear H1.
    apply db_var.
    match goal with H : nth_error ?env ?idx = Some _ |- _ =>
      apply (proj1 (nth_error_Some env idx)); rewrite H; discriminate end.
  Qed.


  (** A typed term implies its environment is well-formed. *)
  Lemma eta_has_type_well_formed : forall (e : environment) (t T : term), eta_has_type e t T -> eta_well_formed e.
  Proof.
    simple induction 1; auto with coc core arith datatypes.
  Qed.


  (** Environment items have sort types in well-formed environments. *)
  Lemma eta_well_formed_sort :
   forall (n : nat) (e f : environment),
   skipn (S n) e = f ->
   eta_well_formed e ->
   forall t : term, nth_error e n = Some t -> exists s : sort, eta_has_type f t (sort_term s).
  Proof.
    induction n as [|n0 IHn]; intros e f Htr Hewf t Hn.
    - destruct e as [|h e']; simpl in *; [discriminate|].
      injection Hn as <-. subst f. inversion_clear Hewf.
      exists s; auto with coc core arith datatypes.
    - destruct e as [|h e']; simpl in *; [discriminate|].
      inversion_clear Hewf.
      destruct (IHn e' f Htr (eta_has_type_well_formed _ _ _ H) t Hn) as [s0 Hs0].
      exists s0; exact Hs0.
  Qed.


  (** Inversion predicate for expansion-based typing. *)
  Definition inversion_eta_type (P : Prop) (e : environment) (t T : term) : Prop :=
    match t with
    | sort_term prop => eta_convertible T (sort_term kind) -> P
    | sort_term set => eta_convertible T (sort_term kind) -> P
    | sort_term kind => True
    | var n => forall x : term, nth_error e n = Some x -> eta_convertible T (lift (S n) x) -> P
    | lam A M =>
        forall (s1 s2 : sort) (U : term),
        eta_has_type e A (sort_term s1) ->
        eta_has_type (A :: e) M U ->
        eta_has_type (A :: e) U (sort_term s2) -> eta_convertible T (prod A U) -> P
    | app u v =>
        forall Ur V : term,
        eta_has_type e v V -> eta_has_type e u (prod V Ur) -> eta_convertible T (subst v Ur) -> P
    | prod A B =>
        forall s1 s2 : sort,
        eta_has_type e A (sort_term s1) ->
        eta_has_type (A :: e) B (sort_term s2) -> eta_convertible T (sort_term s2) -> P
    end.

  (** Inversion of typing is stable under expansion-based conversion. *)
  Lemma inversion_eta_type_convertible :
   forall (P : Prop) (e : environment) (t U V : term),
   eta_convertible U V -> inversion_eta_type P e t U -> inversion_eta_type P e t V.
  Proof.
    do 6 intro.
    cut (forall x : term, eta_convertible V x -> eta_convertible U x).
    intro.
    case t; simpl in |- *; intros.
    generalize H1.
    elim s; auto with coc ecoc core arith datatypes; intros.

    apply H1 with x; auto with coc core arith datatypes.

    apply H1 with s1 s2 U0; auto with coc core arith datatypes.

    apply H1 with Ur V0; auto with coc core arith datatypes.

    apply H1 with s1 s2; auto with coc core arith datatypes.

    intros; apply trans_eta_convertible with V; auto with coc core arith datatypes.
  Qed.


  (** Inversion principle for expansion-based typing. *)
  Theorem eta_has_type_inversion :
   forall (P : Prop) (e : environment) (t T : term),
   eta_has_type e t T -> inversion_eta_type P e t T -> P.
  Proof.
    simple induction 1; simpl in |- *; intros.
    auto with coc ecoc core arith datatypes.

    auto with coc ecoc core arith datatypes.

    elim H1; intros.
    apply H2 with x; auto with coc ecoc core arith datatypes.
    rewrite H3; auto with coc ecoc core arith datatypes.

    apply H6 with s1 s2 U; auto with coc ecoc core arith datatypes.

    apply H4 with Ur V; auto with coc ecoc core arith datatypes.

    apply H4 with s1 s2; auto with coc ecoc core arith datatypes.

    apply H1.
    apply inversion_eta_type_convertible with V; auto with coc ecoc core arith datatypes.
  Qed.


  (** The kind sort is not typable. *)
  Lemma inversion_eta_has_type_kind : forall (e : environment) (t : term), ~ eta_has_type e (sort_term kind) t.
  Proof.
    red in |- *; intros.
    apply eta_has_type_inversion with e (sort_term kind) t; simpl in |- *;
     auto with coc ecoc core arith datatypes.
  Qed.

  (** Prop is typed by kind up to conversion. *)
  Lemma inversion_eta_has_type_prop :
   forall (e : environment) (T : term), eta_has_type e (sort_term prop) T -> eta_convertible T (sort_term kind).
  Proof.
    intros.
    apply eta_has_type_inversion with e (sort_term prop) T; simpl in |- *;
     auto with ecoc coc core arith datatypes.
  Qed.

  (** Set is typed by kind up to conversion. *)
  Lemma inversion_eta_has_type_set :
   forall (e : environment) (T : term), eta_has_type e (sort_term set) T -> eta_convertible T (sort_term kind).
  Proof.
    intros.
    apply eta_has_type_inversion with e (sort_term set) T; simpl in |- *;
     auto with coc ecoc core arith datatypes.
  Qed.

  (** Inversion for variable typing. *)
  Lemma inversion_eta_has_type_ref :
   forall (P : Prop) (e : environment) (T : term) (n : nat),
   eta_has_type e (var n) T ->
   (forall U : term, nth_error e n = Some U -> eta_convertible T (lift (S n) U) -> P) -> P.
  Proof.
    intros.
    apply eta_has_type_inversion with e (var n) T; simpl in |- *; intros;
     auto with coc ecoc core arith datatypes.
    apply H0 with x; auto with coc ecoc core arith datatypes.
  Qed.

  (** Inversion for lam typing. *)
  Lemma inversion_eta_has_type_lambda :
   forall (P : Prop) (e : environment) (A M U : term),
   eta_has_type e (lam A M) U ->
   (forall (s1 s2 : sort) (T : term),
    eta_has_type e A (sort_term s1) ->
    eta_has_type (A :: e) M T -> eta_has_type (A :: e) T (sort_term s2) -> eta_convertible (prod A T) U -> P) ->
   P.
  Proof.
    intros.
    apply eta_has_type_inversion with e (lam A M) U; simpl in |- *;
     auto with coc ecoc core arith datatypes; intros.
    apply H0 with s1 s2 U0; auto with coc ecoc core arith datatypes.
  Qed.

  (** Inversion for app typing. *)
  Lemma inversion_eta_has_type_application :
   forall (P : Prop) (e : environment) (u v T : term),
   eta_has_type e (app u v) T ->
   (forall V Ur : term,
    eta_has_type e u (prod V Ur) -> eta_has_type e v V -> eta_convertible T (subst v Ur) -> P) -> P.
  Proof.
    intros.
    apply eta_has_type_inversion with e (app u v) T; simpl in |- *;
     auto with coc ecoc core arith datatypes; intros.
    apply H0 with V Ur; auto with coc ecoc core arith datatypes.
  Qed.

  (** Inversion for prod typing. *)
  Lemma inversion_eta_has_type_product :
   forall (P : Prop) (e : environment) (T U s : term),
   eta_has_type e (prod T U) s ->
   (forall s1 s2 : sort,
    eta_has_type e T (sort_term s1) -> eta_has_type (T :: e) U (sort_term s2) -> eta_convertible (sort_term s2) s -> P) ->
   P.
  Proof.
    intros.
    apply eta_has_type_inversion with e (prod T U) s; simpl in |- *;
     auto with coc ecoc core arith datatypes; intros.
    apply H0 with s1 s2; auto with coc ecoc core arith datatypes.
  Qed.


  (** Terms containing the kind sort are not typable. *)
  Lemma eta_has_type_sort_occurs_kind :
   forall (e : environment) (t T : term), sort_occurs_in kind t -> ~ eta_has_type e t T.
  Proof.
    red in |- *; intros.
    apply eta_has_type_inversion with e t T; auto with coc core arith datatypes.
    generalize e T.
    clear H0.
    elim H; simpl in |- *; auto with coc core arith datatypes; intros.
    apply eta_has_type_inversion with e0 u (sort_term s1); auto with coc core arith datatypes.

    apply eta_has_type_inversion with (u :: e0) v (sort_term s2);
     auto with coc core arith datatypes.

    apply eta_has_type_inversion with e0 u (sort_term s1); auto with coc core arith datatypes.

    apply eta_has_type_inversion with (u :: e0) v U; auto with coc core arith datatypes.

    apply eta_has_type_inversion with e0 u (prod V Ur);
     auto with coc core arith datatypes.

    apply eta_has_type_inversion with e0 v V; auto with coc core arith datatypes.
  Qed.


(** Terms convertible to kind are not typable. *)
Lemma inversion_eta_has_type_convertible_kind :
 forall (e : environment) (t T : term), eta_convertible t (sort_term kind) -> ~ eta_has_type e t T.
Proof.
  intros.
  apply eta_has_type_sort_occurs_kind.
  apply eta_reduces_sort_occurs.
  elim eta_church_rosser with t (sort_term kind); intros;
   auto with ecoc coc core arith datatypes.
  rewrite (eta_reduces_eta_normal (sort_term kind) x); auto with ecoc coc core arith datatypes.
  red in |- *; red in |- *; intros.
  inversion_clear H2.
Qed.

End Typage.
