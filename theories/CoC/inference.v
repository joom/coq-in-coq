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
From CoC Require Import typing.
From CoC Require Import strong_normalization.
From CoC Require Import decidable_conversion.
From CoC Require Import terms.

Implicit Types i k m n p : nat.
Implicit Type s : sort.
Implicit Types A B M N T t u v : term.
Implicit Types e f g : environment.

(** Decide whether a strongly normalizing term reduces to a sort. *)
  Definition reduces_to_sort :
   forall t,
   strongly_normalizing t -> {s : sort & reduces t (sort_term s)} + {(forall s, convertible t (sort_term s) -> False)}.
  Proof.
    intros t snt.
    elim compute_normal_form with (1 := snt); intros [s| n| T b| u v| T U] redt nt.
    left.
    exists s; trivial.

    right; intros.
    elim church_rosser_theorem with (sort_term s) (var n).
    intros x H0 H1.
    generalize H0.
    elim (reduces_normal (var n) x); auto with coc; intros.
    apply reduces_sort_sort with s (var n); auto with coc.
    discriminate.

    apply trans_convertible_convertible with t; auto with coc.

    right; intros.
    elim church_rosser_theorem with (sort_term s) (lam T b).
    intros x H0 H1.
    generalize H0.
    elim (reduces_normal (lam T b) x); auto with coc; intros.
    apply reduces_sort_sort with s (lam T b); auto with coc.
    discriminate.

    apply trans_convertible_convertible with t; auto with coc.

    right; intros.
    elim church_rosser_theorem with (sort_term s) (app u v).
    intros x H0 H1.
    generalize H0.
    elim (reduces_normal (app u v) x); auto with coc; intros.
    apply reduces_sort_sort with s (app u v); auto with coc.
    discriminate.

    apply trans_convertible_convertible with t; auto with coc.

    right; intros.
    elim church_rosser_theorem with (sort_term s) (prod T U).
    intros x H0 H1.
    generalize H0.
    elim (reduces_normal (prod T U) x); auto with coc; intros.
    apply reduces_sort_sort with s (prod T U); auto with coc.
    discriminate.

    apply trans_convertible_convertible with t; auto with coc.
  Defined.


(** Decide whether a strongly normalizing term reduces to a prod. *)
  Definition reduces_to_prod :
   forall t,
   strongly_normalizing t ->
   {p : term * term & match p with
                      | (u, v) => reduces t (prod u v)
                      end} + {(forall u v, convertible t (prod u v) -> False)}.
  Proof.
    intros t snt.
    elim compute_normal_form with (1 := snt); intros [s| n| T b| u v| T U] redt nt.
    right; intros.
    elim church_rosser_theorem with (prod u v) (sort_term s).
    intros x H0 H1.
    generalize H0.
    elim (reduces_normal (sort_term s) x); auto with coc; intros.
    apply reduces_product_product with u v (sort_term s); auto with coc; intros.
    discriminate H3.

    apply trans_convertible_convertible with t; auto with coc.

    right; intros.
    elim church_rosser_theorem with (prod u v) (var n).
    intros x H0 H1.
    generalize H0.
    elim (reduces_normal (var n) x); auto with coc; intros.
    apply reduces_product_product with u v (var n); auto with coc; intros.
    discriminate H3.

    apply trans_convertible_convertible with t; auto with coc.

    right; intros.
    elim church_rosser_theorem with (prod u v) (lam T b).
    intros x H0 H1.
    generalize H0.
    elim (reduces_normal (lam T b) x); auto with coc; intros.
    apply reduces_product_product with u v (lam T b); auto with coc; intros.
    discriminate H3.

    apply trans_convertible_convertible with t; auto with coc.

    right; intros.
    elim church_rosser_theorem with (prod u0 v0) (app u v).
    intros x H0 H1.
    generalize H0.
    elim (reduces_normal (app u v) x); auto with coc; intros.
    apply reduces_product_product with u0 v0 (app u v); auto with coc; intros.
    discriminate H3.

    apply trans_convertible_convertible with t; auto with coc.

    left; exists (T, U); trivial.
  Defined.

Section TypeChecker.


(** Type errors returned by the type checker. *)
  Inductive type_error : Set :=
    | err_under : term -> type_error -> type_error
    | err_expected_type : term -> term -> term -> type_error
    | err_kind_ill_typed : type_error
    | err_db : nat -> type_error
    | err_lambda_kind : term -> type_error
    | err_not_a_type : term -> term -> type_error
    | err_not_a_fun : term -> term -> type_error
    | err_apply : term -> term -> term -> term -> type_error.


(** Semantic explanation of type errors in an environment. *)
(* meaning of errors *)
  Inductive explanation : environment -> type_error -> Type :=
    | expl_under :
        forall e t (err : type_error),
        explanation (t :: e) err -> explanation e (err_under t err)
    | expl_expected_type :
        forall e (m at_ et : term),
        has_type e m at_ ->
        (has_type e m et -> False) ->
        free_db_below (length e) et -> explanation e (err_expected_type m at_ et)
    | expl_kind :
        forall e,
        well_formed e -> (forall t, has_type e (sort_term kind) t -> False) -> explanation e err_kind_ill_typed
    | expl_db : forall e n, well_formed e -> length e <= n -> explanation e (err_db n)
    | expl_lam_kind :
        forall e (m : term) t,
        has_type (t :: e) m (sort_term kind) -> explanation e (err_lambda_kind (lam t m))
    | expl_type :
        forall e (m : term) t,
        has_type e m t ->
        (forall s, has_type e m (sort_term s) -> False) -> explanation e (err_not_a_type m t)
    | Exp_fun :
        forall e (m : term) t,
        has_type e m t ->
        (forall a b : term, has_type e m (prod a b) -> False) -> explanation e (err_not_a_fun m t)
    | expl_apply :
        forall e u v (a b tv : term),
        has_type e u (prod a b) ->
        has_type e v tv -> (has_type e v a -> False) -> explanation e (err_apply u (prod a b) v tv).

  Hint Resolve expl_under expl_expected_type expl_kind expl_db expl_lam_kind expl_type
    Exp_fun expl_apply: coc.

(** Well-formedness of the environment follows from an explained error. *)
  Lemma explanation_well_formed : forall e (err : type_error), explanation e err -> well_formed e.
  Proof.
    induction 1 as [e0 t err0 Hexp IH|e0 m at_ et Hty Hnty Hfree|e0 Hwf Hnk|e0 n Hwf Hlen
                    |e0 m t Hty|e0 m t Hty Hnty2|e0 m t Hty Hnty3|e0 u v a b tv Hty1 Hty2 Hnty4];
     intros; auto with coc arith.
    inversion_clear IH as [ | e1 T s Hty0 ].
    apply has_type_well_formed with t (sort_term s); auto with coc arith.

    apply has_type_well_formed with m at_; auto with coc arith.

    cut (well_formed (t :: e0)); intros.
    inversion_clear H as [ | e1 T s Hty0 ].
    apply has_type_well_formed with t (sort_term s); auto with coc arith.

    apply has_type_well_formed with m (sort_term kind); auto with coc arith.

    apply has_type_well_formed with m t; auto with coc arith.

    apply has_type_well_formed with m t; auto with coc arith.

    apply has_type_well_formed with v tv; auto with coc arith.
  Qed.

(** Structural relation between a term and its inference error. *)
  Inductive infer_error : term -> type_error -> Prop :=
    | infer_err_sub :
        forall (m n : term) (err : type_error),
        subterm_no_binder m n -> infer_error m err -> infer_error n err
    | infer_err_under :
        forall (m n : term) T (err : type_error),
        subterm_under_binder T m n -> infer_error m err -> infer_error n (err_under T err)
    | infer_err_kind : infer_error (sort_term kind) err_kind_ill_typed
    | infer_err_db : forall n, infer_error (var n) (err_db n)
    | infer_err_lam_kind : forall M T, infer_error (lam T M) (err_lambda_kind (lam T M))
    | infer_err_type_abs :
        forall (m n : term) t, infer_error (lam m n) (err_not_a_type m t)
    | Infe_fun : forall (m n : term) t, infer_error (app m n) (err_not_a_fun m t)
    | infer_err_apply :
        forall m n tf ta : term, infer_error (app m n) (err_apply m tf n ta)
    | infer_err_type_prod_l :
        forall (m n : term) t, infer_error (prod m n) (err_not_a_type m t)
    | infer_err_type_prod_r :
        forall (m n : term) t,
        infer_error (prod m n) (err_under m (err_not_a_type n t)).

  Hint Resolve infer_err_kind infer_err_db infer_err_lam_kind infer_err_type_abs Infe_fun
    infer_err_apply infer_err_type_prod_l infer_err_type_prod_r: coc.


(** An inference error implies the term has no type. *)
  Lemma infer_error_no_type :
   forall (m : term) (err : type_error),
   infer_error m err -> forall e, explanation e err -> forall t, has_type e m t -> False.
  Proof.
    simple induction 1; intros.
    revert t H4; inversion_clear H0; intros.
    apply inversion_has_type_abs with e m0 n0 t; intros; auto with coc arith.
    elim H2 with e (sort_term s1); auto with coc arith.

    apply inversion_has_type_app with e m0 v t; intros; auto with coc arith.
    elim H2 with e (prod V Ur); auto with coc arith.

    apply inversion_has_type_app with e u m0 t; intros; auto with coc arith.
    elim H2 with e V; auto with coc arith.

    apply inversion_has_type_prod with e m0 n0 t; intros; auto with coc arith.
    elim H2 with e (sort_term s1); auto with coc arith.

    inversion_clear H3.
    revert t H4; inversion_clear H0; intros.
    apply inversion_has_type_abs with e T m0 t; intros; auto with coc arith.
    elim H2 with (T :: e) T0; auto with coc arith.

    apply inversion_has_type_prod with e T m0 t; intros; auto with coc arith.
    elim H2 with (T :: e) (sort_term s2); auto with coc arith.

    inversion_clear H0; eauto with coc arith.

    intros.
    apply inversion_has_type_ref with e t n; intros; auto with coc arith.
    match goal with H : explanation _ (err_db _) |- _ => inversion_clear H end.
    match goal with Hle : _ <= _, Hnth : nth_error _ _ = Some _ |- _ =>
      apply nth_error_None in Hle; congruence end.

    inversion_clear H0.
    intros.
    apply inversion_has_type_abs with e T M t; intros; auto with coc arith.
    elim inversion_has_type_convertible_kind with (T :: e) T0 (sort_term s2); auto with coc arith.
    apply has_type_unique_sort with (T :: e) M; auto with coc arith.

    inversion_clear H0.
    intros.
    apply inversion_has_type_abs with e m0 n t0; intros; auto with coc arith.
    elim H3 with s1; auto with coc arith.

    inversion_clear H0.
    intros.
    apply inversion_has_type_app with e m0 n t0; intros; auto with coc arith.
    elim H3 with V Ur; auto with coc arith.

    inversion_clear H0.
    intros.
    apply inversion_has_type_app with e m0 n t; intros; auto with coc arith.
    destruct (type_case e m0 (prod a b) H2) as [[x H7]|H7]; auto with coc arith.
    apply inversion_has_type_prod with e a b (sort_term x); intros; auto with coc arith.
    apply H4.
    apply type_conv with V s1; auto with coc arith.
    apply inversion_convertible_product_left with Ur b.
    apply has_type_unique_sort with e m0; auto with coc arith.

    discriminate H7.

    inversion_clear H0.
    intros.
    apply inversion_has_type_prod with e m0 n t0; intros; auto with coc arith.
    elim H3 with s1; auto with coc arith.

    inversion_clear H0.
    inversion_clear H2.
    intros.
    apply inversion_has_type_prod with e m0 n t0; intros; auto with coc arith.
    elim H3 with s2; auto with coc arith.
  Qed.


(** Bidirectional type inference for a term in a well-formed environment. *)
  Definition infer :
   forall e t,
   well_formed e ->
   {T : term & has_type e t T} +
   {err : type_error & explanation e err &  infer_error t err}.
  Proof.
    do 2 intro.
    generalize t e.
    clear e t.
    fix infer 1.
    intros t e wfe.
    case t.
    simple destruct s.
    right.
    exists err_kind_ill_typed; auto with coc arith.
    apply expl_kind; intros; auto with coc arith.
    apply inversion_has_type_kind with (1 := H).

    left.
    exists (sort_term kind).
    apply type_prop; auto with coc arith.

    left.
    exists (sort_term kind).
    apply type_set; auto with coc arith.

    intros.
    destruct (nth_error e n) as [T|] eqn:Hn.
    left.
    exists (lift (S n) T).
    apply type_var; auto with coc arith.
    exists T; auto with coc arith.

    right.
    exists (err_db n); auto with coc arith.
    apply expl_db; auto with coc arith.
    apply nth_error_None in Hn. lia.

    intros a b.
    elim (infer a e); trivial with coc arith.
    intros (T, ty_a).
    elim (reduces_to_sort T); trivial with coc arith.
    intros (s, srt_T).
    cut (well_formed (a :: e)); intros.
    elim (infer b (a :: e)); trivial with coc arith.
    intros (B, ty_b).
    elim (term_eq_dec (sort_term kind) B).
    intro eq_kind.
    right.
    exists (err_lambda_kind (lam a b)); auto with coc arith.
    apply expl_lam_kind; auto with coc arith.
    rewrite eq_kind; auto with coc arith.

    intro not_kind.
    left.
    exists (prod a B).
    elim type_case with (1 := ty_b).
    intros (s2, knd_b).
    apply type_abs with s s2; auto with coc arith.
    apply type_reduction with T; auto with coc arith.

    intros; elim not_kind; auto.

    intros (err, expl_err, inf_err).
    right.
    exists (err_under a err); auto with coc arith.
    apply infer_err_under with b; auto with coc arith.

    apply wf_var with s.
    apply type_reduction with T; auto with coc arith.

    intro not_type.
    right.
    exists (err_not_a_type a T); auto with coc arith.
    apply expl_type; auto with coc arith.
    intros.
    elim not_type with s.
    apply has_type_unique_sort with e a; auto with coc arith.

    apply type_strongly_normalizing with e a; auto with coc arith.

    intros (err, expl_err, inf_err).
    right.
    exists err; auto with coc arith.
    apply infer_err_sub with a; auto with coc arith.

    intros u v.
    elim infer with u e; trivial with coc arith.
    intros (T, ty_u).
    elim reduces_to_prod with T.
    intros ((V, Ur), red_prod).
    cut (has_type e u (prod V Ur)); intros.
    elim infer with v e; trivial with coc arith.
    intros (B, ty_v).
    elim is_convertible with V B.
    intros domain_conv.
    left.
    exists (subst v Ur).
    apply type_app with V; auto with coc arith.
    elim type_case with e u (prod V Ur); auto with coc arith.
    intros (s, ty_prod).
    apply inversion_has_type_prod with (1 := ty_prod); auto with coc arith; intros.
    apply type_conv with B s1; auto with coc arith.

    intro not_prod; discriminate not_prod.

    intro dom_not_conv.
    right.
    exists (err_apply u (prod V Ur) v B); auto with coc arith.
    apply expl_apply; auto with coc arith.
    intros.
    apply dom_not_conv.
    apply has_type_unique_sort with e v; auto with coc arith.

    apply subterm_sn with (prod V Ur); auto with coc arith.
    apply strongly_normalizing_reduces with T; auto with coc arith.
    apply type_strongly_normalizing with e u; auto with coc arith.

    apply type_strongly_normalizing with e v; auto with coc arith.

    intros (err, expl_err, inf_err).
    right.
    exists err; auto with coc arith.
    apply infer_err_sub with v; auto with coc arith.

    apply type_reduction with T; auto with coc arith.

    intros not_prod.
    right.
    exists (err_not_a_fun u T); auto with coc arith.
    apply Exp_fun; auto with coc arith.
    intros.
    elim not_prod with a b.
    apply has_type_unique_sort with e u; auto with coc arith.

    apply type_strongly_normalizing with e u; auto with coc arith.

    intros (err, expl_err, inf_err).
    right.
    exists err; auto with coc arith.
    apply infer_err_sub with u; auto with coc arith.

    intros a b.
    elim infer with a e; trivial with coc arith.
    intros (T, ty_a).
    elim reduces_to_sort with T.
    intros (s, red_sort).
    cut (well_formed (a :: e)); intros.
    elim infer with b (a :: e); trivial with coc arith.
    intros (B, ty_b).
    elim reduces_to_sort with B.
    intros (s2, red_s2).
    left.
    exists (sort_term s2).
    apply type_prod with s; auto with coc arith.
    apply type_reduction with T; auto with coc arith.

    apply type_reduction with B; auto with coc arith.

    intros b_not_type.
    right.
    exists (err_under a (err_not_a_type b B)); auto with coc arith.
    apply expl_under; auto with coc arith.
    apply expl_type; auto with coc arith.
    intros.
    elim b_not_type with s0.
    apply has_type_unique_sort with (a :: e) b; auto with coc arith.

    apply type_strongly_normalizing with (a :: e) b; auto with coc arith.

    intros (err, expl_err, inf_err).
    right.
    exists (err_under a err); auto with coc arith.
    apply infer_err_under with b; auto with coc arith.

    apply wf_var with s.
    apply type_reduction with T; auto with coc arith.

    intros a_not_type.
    right.
    exists (err_not_a_type a T); auto with coc arith.
    apply expl_type; auto with coc arith.
    intros.
    elim a_not_type with s.
    apply has_type_unique_sort with e a; auto with coc arith.

    apply type_strongly_normalizing with e a; auto with coc arith.

    intros (err, expl_err, inf_err).
    right.
    exists err; auto with coc arith.
    apply infer_err_sub with a; auto with coc arith.
  Defined.


(** Check errors: inference failure, type-of-type failure, or type mismatch. *)
  Inductive check_error (m : term) t : type_error -> Prop :=
    | check_err_subj :
        forall err : type_error, infer_error m err -> check_error m t err
    | check_err_type :
        forall err : type_error,
        infer_error t err -> t <> sort_term kind -> check_error m t err
    | check_err_expected : forall at_ : term, check_error m t (err_expected_type m at_ t).

  Hint Resolve check_err_subj check_err_type check_err_expected: coc.


(** A check error implies the term does not have the given type. *)
  Lemma check_error_no_type :
   forall e (m : term) t (err : type_error),
   check_error m t err -> explanation e err -> (has_type e m t -> False).
  Proof.
    destruct 1 as [err0 Hinf|err0 Hinf Hnk|at_]; intros.
    apply infer_error_no_type with (m := m) (err := err0) (e := e) (t := t); auto with coc arith.

    destruct (type_case e m t H0) as [[x H1]|H1].
    apply infer_error_no_type with (m := t) (err := err0) (e := e) (t := sort_term x);
      auto with coc arith.

    apply Hnk; assumption.

    inversion_clear H; auto with coc arith.
  Qed.


(** Type-check a term against an expected type in a well-formed environment. *)
  Definition check_type :
   forall e t (tp : term),
   well_formed e ->
   {err : type_error & explanation e err &  check_error t tp err} + (has_type e t tp).
  Proof.
    intros.
    elim infer with e t; auto with coc arith.
    intros (tp', typ_t).
    elim term_eq_dec with (sort_term kind) tp.
    intros cast_kind.
    elim term_eq_dec with (sort_term kind) tp'.
    intros inf_kind.
    right.
    elim cast_kind; rewrite inf_kind; trivial.

    intros inf_not_kind.
    left.
    exists (err_expected_type t tp' tp); auto with coc.
    apply expl_expected_type; auto with coc arith.
    intros; apply inf_not_kind.
    symmetry  in |- *.
    apply type_kind_not_convertible with e t; auto with coc arith.
    rewrite cast_kind; trivial.

    elim cast_kind; auto with coc.

    intros cast_not_kind.
    elim infer with e tp; auto with coc.
    intros (k, ty_tp).
    elim is_convertible with tp tp'.
    intros cast_ok.
    right.
    elim reduces_to_sort with k; auto with coc.
    intros (s, red_sort).
    apply type_conv with tp' s; auto with coc.
    apply type_reduction with k; auto with coc.

    intros not_sort.
    elim type_case with (1 := typ_t).
    intros (s, kind_inf).
    elim not_sort with s.
    apply has_type_convertible_convertible with e tp tp'; auto with coc arith.

    intros is_kind.
    elim inversion_has_type_convertible_kind with e tp k; auto with coc arith.
    elim is_kind; auto with coc arith.

    apply type_strongly_normalizing with e tp; auto with coc arith.

    intros cast_err.
    left.
    exists (err_expected_type t tp' tp); auto with coc arith.
    apply expl_expected_type; auto with coc arith.
    intros; apply cast_err; apply has_type_unique_sort with e t;
     auto with coc arith.

    apply has_type_free_db_below with k; auto with coc arith.

    apply strong_normalization with e k; auto with coc arith.

    apply type_strongly_normalizing with e t; auto with coc arith.

    intros (err, expl_err, inf_err).
    left.
    exists err; auto with coc arith.

    intros (err, expl_err, inf_err).
    left.
    exists err; auto with coc arith.
  Defined.


(** Declaration errors: inference failure or the term is not a type. *)
  Inductive declare_error (m : term) : type_error -> Prop :=
    | decl_err_ill :
        forall err : type_error, infer_error m err -> declare_error m err
    | decl_err_type : forall t, declare_error m (err_not_a_type m t).

  Hint Resolve decl_err_ill decl_err_type: coc.


(** A declaration error prevents extending the environment. *)
  Lemma declare_error_not_well_formed :
   forall e t (err : type_error),
   declare_error t err -> explanation e err -> (well_formed (t :: e) -> False).
  Proof.
    destruct 1 as [err0 Hinf|t0]; intros Hexp Hwf.
    inversion_clear Hwf.
    apply infer_error_no_type with (m := t) (err := err0) (e := e) (t := sort_term s);
      auto with coc arith.

    inversion_clear Hexp.
    inversion_clear Hwf.
    elim H0 with s; auto with coc arith.
  Qed.


(** Try to extend an environment with a new declaration. *)
  Definition add_type :
   forall e t,
   well_formed e ->
   {err : type_error & explanation e err &  declare_error t err} + (well_formed (t :: e)).
  Proof.
    intros.
    elim infer with e t; auto with coc.
    intros (T, typ_t).
    elim reduces_to_sort with T.
    intros (s, red_sort).
    right.
    apply wf_var with s.
    apply type_reduction with T; auto with coc.

    intros not_sort.
    left.
    exists (err_not_a_type t T); auto with coc.
    apply expl_type; auto with coc.
    intros.
    elim not_sort with s.
    apply has_type_unique_sort with e t; auto with coc.

    apply type_strongly_normalizing with e t; auto with coc.

    intros (err, expl_err, inf_err).
    left.
    exists err; auto with coc arith.
  Defined.


End TypeChecker.

Section Decidabilite_typage.

(** Decidability of well-formedness for environments. *)
  Lemma decide_well_formed : forall e, (well_formed e) + (well_formed e -> False).
  Proof.
    induction e as [|a l IH]; intros.
    left.
    apply wf_nil.

    elim IH.
    intros wf_l.
    elim add_type with l a; trivial.
    intros (err, expl_err, decl_err).
    right.
    apply declare_error_not_well_formed with (1 := decl_err) (2 := expl_err).

    left; trivial.

    intros not_wf_l.
    right; intros Hwfa.
    apply not_wf_l.
    inversion_clear Hwfa.
    apply has_type_well_formed with (1 := H).
  Qed.


(** Decidability of typing judgments. *)
  Lemma decide_type : forall e t (tp : term), (has_type e t tp) + (has_type e t tp -> False).
  Proof.
    intros e t tp.
    elim decide_well_formed with e.
    intros wf_e.
    elim check_type with e t tp; trivial.
    intros (err, expl_err, chk_err).
    right.
    apply check_error_no_type with (1 := chk_err) (2 := expl_err).

    left; trivial.

    intros not_wf_e.
    right; intros Hty.
    apply not_wf_e.
    apply has_type_well_formed with (1 := Hty).
  Qed.

End Decidabilite_typage.
