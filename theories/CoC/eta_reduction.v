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


From CoC Require Import terms.
From CoC Require Import confluence.

(** A Prop-valued relation is strongly confluent when it commutes with its
    transpose. This is the classic (Prop) notion, used here for the
    eta-erasure relations, which remain Prop-sorted. *)
Definition strongly_confluent (R : term -> term -> Prop) :=
  commut _ R (transp _ R).

(** One-step erasure reduction on terms. *)
Inductive eta_reduces_once : term -> term -> Prop :=
  | eta_beta : forall M N T : term, eta_reduces_once (app (lam T M) N) (subst N M)
  | eta_erase_abs : forall M T : term, eta_reduces_once (lam T M) (lam (sort_term prop) M)
  | eta_abs_red_l :
      forall M M' : term,
      eta_reduces_once M M' -> forall N : term, eta_reduces_once (lam M N) (lam M' N)
  | eta_abs_red_r :
      forall M M' : term,
      eta_reduces_once M M' -> forall N : term, eta_reduces_once (lam N M) (lam N M')
  | eta_app_red_l :
      forall M1 N1 : term,
      eta_reduces_once M1 N1 -> forall M2 : term, eta_reduces_once (app M1 M2) (app N1 M2)
  | eta_app_red_r :
      forall M2 N2 : term,
      eta_reduces_once M2 N2 -> forall M1 : term, eta_reduces_once (app M1 M2) (app M1 N2)
  | eta_prod_red_l :
      forall M1 N1 : term,
      eta_reduces_once M1 N1 -> forall M2 : term, eta_reduces_once (prod M1 M2) (prod N1 M2)
  | eta_prod_red_r :
      forall M2 N2 : term,
      eta_reduces_once M2 N2 -> forall M1 : term, eta_reduces_once (prod M1 M2) (prod M1 N2).

(** Reflexive-transitive closure of erasure reduction, via stdlib. *)
Definition eta_reduces := clos_refl_trans_n1 term eta_reduces_once.

(** Reflexivity of erasure reduction. *)
Definition eta_refl : forall M, eta_reduces M M := @rtn1_refl term eta_reduces_once.

(** Extending an erasure reduction by one step. *)
Lemma eta_trans_reduces : forall M (P N : term), eta_reduces M P -> eta_reduces_once P N -> eta_reduces M N.
Proof.
  intros M P N H1 H2; exact (@Relation_Operators.rtn1_trans term eta_reduces_once M P N H2 H1).
Qed.

(** Conversion relation for erasure reduction, via stdlib. *)
Definition eta_convertible := clos_refl_sym_trans_n1 term eta_reduces_once.

(** Reflexivity of erasure conversion. *)
Definition eta_refl_convertible : forall M, eta_convertible M M := @rstn1_refl term eta_reduces_once.

(** Extending an erasure conversion by a forward reduction step. *)
Lemma eta_trans_convertible_reduces : forall M (P N : term), eta_convertible M P -> eta_reduces_once P N -> eta_convertible M N.
Proof.
  intros M P N H1 H2; exact (@Relation_Operators.rstn1_trans term eta_reduces_once M P N (or_introl H2) H1).
Qed.

(** Extending an erasure conversion by a backward reduction step. *)
Lemma eta_trans_convertible_expansion : forall M (P N : term), eta_convertible M P -> eta_reduces_once N P -> eta_convertible M N.
Proof.
  intros M P N H1 H2; exact (@Relation_Operators.rstn1_trans term eta_reduces_once M P N (or_intror H2) H1).
Qed.

(** Parallel one-step erasure reduction. *)
Inductive eta_parallel_reduces_once : term -> term -> Prop :=
  | eta_par_beta :
      forall M M' : term,
      eta_parallel_reduces_once M M' ->
      forall N N' : term,
      eta_parallel_reduces_once N N' ->
      forall T : term, eta_parallel_reduces_once (app (lam T M) N) (subst N' M')
  | eta_par_erase_abs :
      forall M M' : term,
      eta_parallel_reduces_once M M' ->
      forall T : term, eta_parallel_reduces_once (lam T M) (lam (sort_term prop) M')
  | eta_par_sort : forall s : sort, eta_parallel_reduces_once (sort_term s) (sort_term s)
  | eta_par_var : forall n : nat, eta_parallel_reduces_once (var n) (var n)
  | eta_par_abs :
      forall M M' : term,
      eta_parallel_reduces_once M M' ->
      forall T T' : term, eta_parallel_reduces_once T T' -> eta_parallel_reduces_once (lam T M) (lam T' M')
  | eta_par_app :
      forall M M' : term,
      eta_parallel_reduces_once M M' ->
      forall N N' : term, eta_parallel_reduces_once N N' -> eta_parallel_reduces_once (app M N) (app M' N')
  | eta_par_prod :
      forall M M' : term,
      eta_parallel_reduces_once M M' ->
      forall N N' : term, eta_parallel_reduces_once N N' -> eta_parallel_reduces_once (prod M N) (prod M' N').

(** Transitive closure of parallel erasure reduction. *)
Definition eta_parallel_reduces := clos_trans term eta_parallel_reduces_once.

(** A term is E-normal if it has no erasure redex. *)
Definition eta_normal (t : term) : Prop := forall u : term, ~ eta_reduces_once t u.

Hint Resolve eta_refl eta_beta eta_erase_abs eta_abs_red_l eta_abs_red_r eta_app_red_l eta_app_red_r
  eta_prod_red_l eta_prod_red_r: ecoc.

Hint Resolve eta_trans_reduces: ecoc.
Hint Resolve eta_refl_convertible eta_trans_convertible_reduces eta_trans_convertible_expansion: ecoc.
Hint Resolve eta_par_beta eta_par_erase_abs eta_par_sort eta_par_var eta_par_abs
  eta_par_app eta_par_prod: ecoc.

(** Standard one-step reduction embeds into erasure one-step reduction. *)
Lemma reduces_once_eta_reduces_once : forall M N : term, reduces_once M N -> eta_reduces_once M N.
Proof.
  simple induction 1; auto with ecoc.
Qed.

Hint Resolve reduces_once_eta_reduces_once: ecoc.

(** Standard reduction embeds into erasure reduction. *)
Lemma reduces_eta_reduces : forall M N : term, reduces M N -> eta_reduces M N.
Proof.
  intros M N H; induction H; eauto with ecoc.
Qed.

Hint Resolve reduces_eta_reduces: ecoc.

(** Standard conversion embeds into erasure conversion. *)
Lemma convertible_eta_convertible : forall M N : term, convertible M N -> eta_convertible M N.
Proof.
  intros M N H.
  induction H as [ M0 | M0 P0 N0 Hstep0 Hconv0 IH0 | M0 P0 N0 Hstep0 Hconv0 IH0 ];
    eauto with ecoc.
Qed.

Hint Resolve convertible_eta_convertible: ecoc.

(** Transitivity of erasure reduction. *)
Lemma trans_eta_reduces : forall M N P : term, eta_reduces M N -> eta_reduces N P -> eta_reduces M P.
Proof.
  intros M N P H1 H2.
  induction H2; auto.
  apply eta_trans_reduces with y; auto.
Qed.

(** Every term parallel-reduces to itself. *)
Lemma refl_eta_parallel_reduces_once : forall M : term, eta_parallel_reduces_once M M.
Proof.
  simple induction M; auto with coc ecoc core arith sets.
Qed.

Hint Resolve refl_eta_parallel_reduces_once: ecoc.

(** A single parallel step embeds into the transitive closure. *)
Lemma eta_parallel_once_parallel : forall M N : term, eta_parallel_reduces_once M N -> eta_parallel_reduces M N.
Proof.
  intros; unfold eta_parallel_reduces in |- *; apply Relation_Operators.t_trans with M; auto with ecoc sets.
Qed.

Hint Resolve eta_parallel_once_parallel: ecoc.

(** Parallel erasure reduction is stable under lifting. *)
Lemma eta_parallel_reduces_once_lift :
 forall (n : nat) (a b : term),
 eta_parallel_reduces_once a b -> forall k : nat, eta_parallel_reduces_once (lift_rec n a k) (lift_rec n b k).
Proof.
  simple induction 1; simpl in |- *; eauto with coc ecoc core arith sets.
  intros.
  rewrite distribute_lift_subst; auto with coc ecoc core arith sets.
Qed.

Hint Resolve eta_parallel_reduces_once_lift: ecoc.

(** Parallel erasure reduction is stable under substitution. *)
Lemma eta_parallel_reduces_once_subst :
 forall c d : term,
 eta_parallel_reduces_once c d ->
 forall a b : term,
 eta_parallel_reduces_once a b ->
 forall k : nat, eta_parallel_reduces_once (subst_rec a c k) (subst_rec b d k).
Proof.
  simple induction 1; simpl in |- *; eauto with coc ecoc core arith sets;
   intros.
  rewrite distribute_subst; auto with coc ecoc core arith sets.

  elim (lt_eq_lt_dec k n); auto with coc ecoc core arith sets; intro a0.
  elim a0; intros; auto with coc ecoc core arith sets.
  unfold lift in |- *; auto with ecoc.
Qed.

Hint Resolve eta_parallel_reduces_once_subst: ecoc.

(** Inversion principle for parallel reduction of a lam. *)
Lemma inversion_eta_parallel_reduces_lambda :
 forall (P : Prop) (T U x : term),
 eta_parallel_reduces_once (lam T U) x ->
 (forall T' U' : term, x = lam T' U' -> eta_parallel_reduces_once U U' -> P) -> P.
Proof.
  intros P T U x Hpar.
  inversion_clear Hpar; intros Hcont.
  apply Hcont with (sort_term prop) M'; auto with ecoc.
  apply Hcont with T' M'; auto with ecoc.
Qed.

(** One-step erasure reduction embeds into parallel erasure reduction. *)
Lemma eta_reduces_once_parallel_once : forall M N : term, eta_reduces_once M N -> eta_parallel_reduces_once M N.
Proof.
  simple induction 1; eauto with ecoc coc core arith sets; intros.
Qed.

Hint Resolve eta_reduces_once_parallel_once: ecoc.

(** Erasure reduction embeds into parallel erasure reduction. *)
Lemma eta_reduces_parallel : forall M N : term, eta_reduces M N -> eta_parallel_reduces M N.
Proof.
  intros M N H; red in |- *; induction H; auto with ecoc coc core arith sets.
  apply Relation_Operators.t_trans with y; auto with ecoc coc core arith sets.
Qed.

(** Erasure reduction is compatible with app. *)
Lemma eta_reduces_application :
 forall u u0 v v0 : term,
 eta_reduces u u0 -> eta_reduces v v0 -> eta_reduces (app u v) (app u0 v0).
Proof.
  intros u u0 v v0 H1 H2.
  induction H1.
  - induction H2; auto with ecoc coc core arith sets.
    apply eta_trans_reduces with (app u y); auto with ecoc coc core arith sets.
  - apply eta_trans_reduces with (app y v0); auto with ecoc coc core arith sets.
Qed.

(** Erasure reduction is compatible with lam abstraction. *)
Lemma eta_reduces_lambda :
 forall u u0 v v0 : term,
 eta_reduces u u0 -> eta_reduces v v0 -> eta_reduces (lam u v) (lam u0 v0).
Proof.
  intros u u0 v v0 H1 H2.
  induction H1.
  - induction H2; auto with ecoc coc core arith sets.
    apply eta_trans_reduces with (lam u y); auto with ecoc coc core arith sets.
  - apply eta_trans_reduces with (lam y v0); auto with ecoc coc core arith sets.
Qed.

(** Erasure reduction is compatible with dependent prod. *)
Lemma eta_reduces_product :
 forall u u0 v v0 : term,
 eta_reduces u u0 -> eta_reduces v v0 -> eta_reduces (prod u v) (prod u0 v0).
Proof.
  intros u u0 v v0 H1 H2.
  induction H1.
  - induction H2; auto with ecoc coc core arith sets.
    apply eta_trans_reduces with (prod u y); auto with ecoc coc core arith sets.
  - apply eta_trans_reduces with (prod y v0); auto with ecoc coc core arith sets.
Qed.

Hint Resolve eta_reduces_application eta_reduces_lambda eta_reduces_product: ecoc.

(** Parallel erasure reduction implies erasure reduction. *)
Lemma eta_parallel_reduces_reduces : forall M N : term, eta_parallel_reduces M N -> eta_reduces M N.
Proof.
  intros M N H; induction H.
  - induction H; eauto with ecoc coc core arith sets.
  - apply trans_eta_reduces with y; auto with ecoc coc core arith sets.
Qed.

Hint Resolve eta_reduces_parallel eta_parallel_reduces_reduces: ecoc.

(** Erasure one-step reduction is stable under lifting. *)
Lemma eta_reduces_once_lift :
 forall u v : term,
 eta_reduces_once u v -> forall n k : nat, eta_reduces_once (lift_rec n u k) (lift_rec n v k).
Proof.
  simple induction 1; simpl in |- *; intros; auto with ecoc coc core arith sets.
  rewrite distribute_lift_subst; auto with ecoc coc core arith sets.
Qed.

Hint Resolve eta_reduces_once_lift: ecoc.

(** Erasure one-step reduction on the body is stable under substitution. *)
Lemma eta_reduces_once_subst_right :
 forall t u : term,
 eta_reduces_once t u ->
 forall (a : term) (k : nat), eta_reduces_once (subst_rec a t k) (subst_rec a u k).
Proof.
  simple induction 1; simpl in |- *; intros; auto with ecoc coc core arith sets.
  rewrite distribute_subst; auto with ecoc coc core arith sets.
Qed.

(** Erasure one-step reduction on the substituted term yields multi-step reduction. *)
Lemma eta_reduces_once_subst_left :
 forall (a t u : term) (k : nat),
 eta_reduces_once t u -> eta_reduces (subst_rec t a k) (subst_rec u a k).
Proof.
  simple induction a; simpl in |- *; auto with ecoc coc core arith sets.
  intros.
  elim (lt_eq_lt_dec k n);
   [ intro a0 | intro b; auto with ecoc coc core arith sets ].
  elim a0; auto with ecoc coc core arith sets.
  unfold lift in |- *; auto with ecoc coc core arith sets.
Qed.

Hint Resolve eta_reduces_once_subst_left eta_reduces_once_subst_right: ecoc.

(** Substitution preserves erasure one-step reduction on the right. *)
Lemma subst_rec_eta_reduces_once_right :
 forall N M M' : term,
 eta_reduces_once M M' -> forall k : nat, eta_reduces_once (subst_rec N M k) (subst_rec N M' k).
Proof.
  simple induction 1; simpl in |- *; intros; auto with ecoc.
  rewrite distribute_subst.
  auto with ecoc.
Qed.

(** Top-level substitution preserves erasure one-step reduction. *)
Lemma subst_eta_reduces_once_right :
 forall N M M' : term, eta_reduces_once M M' -> eta_reduces_once (subst N M) (subst N M').
Proof.
  unfold subst in |- *; intros; apply subst_rec_eta_reduces_once_right; trivial.
Qed.

(** Strong confluence of parallel erasure reduction. *)
Lemma strong_confluence_eta_parallel_once : strongly_confluent eta_parallel_reduces_once.
Proof.
  red in |- *; red in |- *.
  simple induction 1; intros.
  inversion_clear H4.
  elim H1 with M'0; auto with ecoc coc core arith sets; intros.
  elim H3 with N'0; auto with ecoc coc core arith sets; intros.
  split with (subst x1 x0); unfold subst in |- *;
   auto with coc ecoc core arith sets.

  inversion_clear H5.
  elim H1 with M'1; auto with ecoc coc core arith sets; intros.
  elim H3 with N'0; auto with ecoc coc core arith sets; intros.
  split with (subst x1 x0); auto with ecoc coc core arith sets.
  unfold subst in |- *; auto with ecoc coc core arith sets.

  elim H1 with M'1; auto with ecoc coc core arith sets; intros.
  elim H3 with N'0; auto with ecoc coc core arith sets; intros.
  split with (subst x1 x0); auto with ecoc coc core arith sets.
  unfold subst in |- *; auto with ecoc coc core arith sets.

  inversion_clear H2.
  elim H1 with M'0; auto with ecoc coc core arith sets; intros.
  split with (lam (sort_term prop) x0); eauto with ecoc coc core arith sets; intros.

  elim H1 with M'0; auto with ecoc coc core arith sets; intros.
  split with (lam (sort_term prop) x0); eauto with ecoc coc core arith sets.

  inversion_clear H0.
  split with (sort_term s); auto with ecoc coc core arith sets.

  inversion_clear H0.
  split with (var n); auto with ecoc coc core arith sets.

  inversion_clear H4.
  elim H1 with M'0; auto with ecoc coc core arith sets; intros.
  split with (lam (sort_term prop) x0); eauto with ecoc coc core arith sets.

  elim H1 with M'0; auto with ecoc coc core arith sets; intros.
  elim H3 with T'0; auto with ecoc coc core arith sets; intros.
  split with (lam x1 x0); auto with ecoc coc core arith sets.

  generalize H0 H1.
  clear H0 H1.
  inversion_clear H4.
  intro.
  inversion_clear H4.
  intros.
  elim H4 with (lam (sort_term prop) M'0); auto with coc core arith sets; intros.
  elim H3 with N'0; auto with coc core arith sets; intros.
  apply inversion_eta_parallel_reduces_lambda with (sort_term prop) M'1 x0; intros;
   auto with coc core arith sets.
  rewrite H10 in H7; inversion_clear H7.
  split with (subst x1 U'); auto with ecoc sets.
  unfold subst in |- *; auto with ecoc coc core arith sets.

  split with (subst x1 U'); auto with ecoc sets.
  unfold subst in |- *; auto with ecoc coc core arith sets.

  auto with ecoc sets.

  intros.
  elim H3 with N'0; auto with ecoc sets; intros.
  elim H4 with (lam T' M'0); auto with ecoc sets; intros.
  apply inversion_eta_parallel_reduces_lambda with T' M'0 x1; intros; auto with coc core arith sets.
  rewrite H11 in H9; inversion_clear H9.
  split with (subst x0 U'); auto with ecoc sets.
  unfold subst in |- *; auto with ecoc coc core arith sets.

  split with (subst x0 U'); auto with ecoc sets.
  unfold subst in |- *; auto with ecoc coc core arith sets.

  intros.
  elim H5 with M'0; auto with ecoc sets; intros.
  elim H3 with N'0; auto with ecoc sets; intros.
  split with (app x0 x1); auto with ecoc sets.

  inversion_clear H4.
  elim H1 with M'0; auto with coc ecoc sets; intros.
  elim H3 with N'0; auto with coc ecoc sets; intros.
  split with (prod x0 x1); auto with ecoc sets.
Qed.

(** Strip lemma for parallel erasure reduction. *)
Lemma strip_lemma_eta_parallel_once : commut _ eta_parallel_reduces (transp _ eta_parallel_reduces_once).
Proof.
  unfold commut, eta_parallel_reduces in |- *; simple induction 1; intros.
  elim strong_confluence_eta_parallel_once with z x0 y0;
   auto with ecoc coc core arith sets; intros.
  split with x1; auto with ecoc coc core arith sets.

  elim H1 with z0; auto with ecoc coc core arith sets; intros.
  elim H3 with x1; intros; auto with ecoc coc core arith sets.
  split with x2; auto with ecoc coc core arith sets.
  apply Relation_Operators.t_trans with x1; auto with ecoc coc core arith sets.
Qed.

(** Confluence of parallel erasure reduction. *)
Lemma confluence_eta_parallel : strongly_confluent eta_parallel_reduces.
Proof.
  red in |- *; red in |- *.
  simple induction 1; intros.
  elim strip_lemma_eta_parallel_once with z x0 y0; intros;
   auto with ecoc coc core arith sets.
  split with x1; auto with ecoc coc core arith sets.

  elim H1 with z0; intros; auto with ecoc coc core arith sets.
  elim H3 with x1; intros; auto with ecoc coc core arith sets.
  split with x2; auto with ecoc coc core arith sets.
  red in |- *; apply Relation_Operators.t_trans with x1; auto with ecoc coc core arith sets.
Qed.

(** Confluence of erasure reduction. *)
Lemma confluence_eta_reduces : strongly_confluent eta_reduces.
Proof.
  red in |- *; red in |- *.
  intros.
  elim confluence_eta_parallel with x y z; auto with ecoc coc core arith sets;
   intros.
  exists x0; auto with ecoc coc core arith sets.
Qed.

(** Church-Rosser property for erasure conversion. *)
Theorem eta_church_rosser :
 forall u v : term,
 eta_convertible u v -> ex2 (fun t : term => eta_reduces u t) (fun t : term => eta_reduces v t).
Proof.
  intros u v H; induction H as [| y z [Hfwd|Hbwd] Huy [x Hux Hyx]].
  exists u; auto with ecoc coc core arith sets.

  elim confluence_eta_reduces with x y z; auto with ecoc coc core arith sets; intros.
  exists x0; auto with ecoc coc core arith sets.
  apply trans_eta_reduces with x; auto with ecoc coc core arith sets.

  exists x; auto with ecoc coc core arith sets.
  apply trans_eta_reduces with y; auto with ecoc coc core arith sets.
Qed.

(** A single erasure expansion step yields a conversion. *)
Lemma one_step_eta_convertible_expansion : forall M N : term, eta_reduces_once M N -> eta_convertible N M.
Proof.
  intros.
  apply eta_trans_convertible_expansion with N; auto with ecoc coc core arith sets.
Qed.

(** Erasure reduction implies erasure conversion. *)
Lemma eta_reduces_eta_convertible : forall M N : term, eta_reduces M N -> eta_convertible M N.
Proof.
  intros M N H; induction H as [| y z Hyz Hmy IH]; auto with ecoc coc core arith sets.
  apply eta_trans_convertible_reduces with y; auto with ecoc coc core arith sets.
Qed.

Hint Resolve one_step_eta_convertible_expansion eta_reduces_eta_convertible: coc.

(** Erasure conversion is symmetric. *)
Lemma sym_eta_convertible : forall M N : term, eta_convertible M N -> eta_convertible N M.
Proof.
  intros M N H.
  change (clos_refl_sym_trans_n1 term eta_reduces_once N M).
  apply (proj1 (clos_rst_rstn1_iff term eta_reduces_once N M)).
  apply rst_sym.
  apply (proj2 (clos_rst_rstn1_iff term eta_reduces_once M N)).
  exact H.
Qed.

Hint Immediate sym_eta_convertible: coc.

(** Erasure conversion is transitive. *)
Lemma trans_eta_convertible :
 forall M N P : term, eta_convertible M N -> eta_convertible N P -> eta_convertible M P.
Proof.
  intros M N P H H0.
  change (clos_refl_sym_trans_n1 term eta_reduces_once M P).
  apply clos_rstn1_trans with N; assumption.
Qed.

(** Erasure conversion is compatible with dependent prod. *)
Lemma eta_convertible_product :
 forall a b c d : term, eta_convertible a b -> eta_convertible c d -> eta_convertible (prod a c) (prod b d).
Proof.
  intros.
  apply trans_eta_convertible with (prod a d).
  induction H0 as [| y z [Hfwd|Hbwd] Hay IH]; auto with ecoc coc core arith sets.
  apply eta_trans_convertible_reduces with (prod a y); auto with ecoc coc core arith sets.
  apply eta_trans_convertible_expansion with (prod a y); auto with ecoc coc core arith sets.

  induction H as [| y z [Hfwd|Hbwd] Hay IH]; auto with ecoc coc core arith sets.
  apply eta_trans_convertible_reduces with (prod y d); auto with ecoc coc core arith sets.
  apply eta_trans_convertible_expansion with (prod y d); auto with ecoc coc core arith sets.
Qed.

(** Erasure conversion is compatible with app. *)
Lemma eta_convertible_application :
 forall a b c d : term, eta_convertible a b -> eta_convertible c d -> eta_convertible (app a c) (app b d).
Proof.
  intros.
  apply trans_eta_convertible with (app a d).
  induction H0 as [| y z [Hfwd|Hbwd] Hay IH]; auto with ecoc coc core arith sets.
  apply eta_trans_convertible_reduces with (app a y); auto with ecoc coc core arith sets.
  apply eta_trans_convertible_expansion with (app a y); auto with ecoc coc core arith sets.

  induction H as [| y z [Hfwd|Hbwd] Hay IH]; auto with ecoc coc core arith sets.
  apply eta_trans_convertible_reduces with (app y d); auto with ecoc coc core arith sets.
  apply eta_trans_convertible_expansion with (app y d); auto with ecoc coc core arith sets.
Qed.

Hint Resolve eta_convertible_product eta_convertible_application: ecoc.

(** An E-normal term is a fixed point of erasure reduction. *)
Lemma eta_reduces_eta_normal : forall u v : term, eta_reduces u v -> eta_normal u -> u = v.
Proof.
  intros u v H Hn; induction H as [| y z Hyz Huy IH]; auto with ecoc coc core arith sets.
  assert (u = y) as Heq by auto.
  subst y; elim (Hn z); auto with ecoc coc core arith sets.
Qed.

(** Inversion of erasure reduction on a prod. *)
Lemma eta_reduces_product_product :
 forall u v t : term,
 eta_reduces (prod u v) t ->
 forall P : Prop,
 (forall a b : term, t = prod a b -> eta_reduces u a -> eta_reduces v b -> P) -> P.
Proof.
  intros u v t H; induction H as [| y z Hyz Huy IH]; intros P0 HP.
  apply HP with u v; auto with ecoc coc core arith sets.

  apply IH; intros.
  match goal with H1 : _ = prod _ _ |- _ => rewrite H1 in Hyz end.
  inversion Hyz; subst.
  apply HP with N1 b; auto with ecoc coc core arith sets.
  apply eta_trans_reduces with a; auto with ecoc coc core arith sets.

  apply HP with a N2; auto with ecoc coc core arith sets.
  apply eta_trans_reduces with b; auto with ecoc coc core arith sets.
Qed.

(** A sort and a prod are never E-convertible. *)
Lemma eta_convertible_sort_product :
 forall (s : sort) (t u : term), ~ eta_convertible (sort_term s) (prod t u).
Proof.
  red in |- *; intros s t u Hconv.
  elim eta_church_rosser with (sort_term s) (prod t u);
   auto with ecoc coc core arith sets.
  intros x Hsx.
  elim eta_reduces_eta_normal with (sort_term s) x; auto with ecoc coc core arith sets.
  intro Hpx.
  apply eta_reduces_product_product with t u (sort_term s); auto with ecoc coc core arith sets;
   intros a b Heq Hta Hub.
  discriminate Heq.

  red in |- *; red in |- *; intros y Hy.
  inversion_clear Hy.
Qed.

(** Erasure conversion is compatible with lam under same type annotation. *)
Lemma eta_convertible_lambda : forall a b T : term, eta_convertible a b -> eta_convertible (lam T a) (lam T b).
Proof.
  intros.
  induction H as [| y z [Hfwd|Hbwd] Hay IH]; auto with ecoc coc core arith sets.
  apply eta_trans_convertible_reduces with (lam T y); auto with ecoc coc core arith sets.
  apply eta_trans_convertible_expansion with (lam T y); auto with ecoc coc core arith sets.
Qed.

Hint Resolve eta_convertible_lambda: ecoc.

(** Erasure conversion under lam with possibly different type annotations. *)
Lemma eta_convertible_type_lambda :
 forall a b T T' : term, eta_convertible a b -> eta_convertible (lam T a) (lam T' b).
Proof.
  intros.
  apply trans_eta_convertible with (lam (sort_term prop) a); eauto with ecoc.
Qed.

Hint Resolve eta_convertible_type_lambda: ecoc.

(** Erasure conversion is stable under lifting. *)
Lemma eta_convertible_lift :
 forall (a b : term) (n k : nat),
 eta_convertible a b -> eta_convertible (lift_rec n a k) (lift_rec n b k).
Proof.
  intros.
  induction H as [| y z [Hfwd|Hbwd] Hay IH]; auto with ecoc coc core arith sets.
  apply eta_trans_convertible_reduces with (lift_rec n y k);
   auto with ecoc coc core arith sets.

  apply eta_trans_convertible_expansion with (lift_rec n y k);
   auto with ecoc coc core arith sets.
Qed.

(** Erasure conversion is stable under substitution. *)
Lemma eta_convertible_subst :
 forall (a b c d : term) (k : nat),
 eta_convertible a b -> eta_convertible c d -> eta_convertible (subst_rec a c k) (subst_rec b d k).
Proof.
  intros.
  apply trans_eta_convertible with (subst_rec a d k).
  induction H0 as [| y z [Hfwd|Hbwd] Hay IH]; auto with ecoc coc core arith sets.
  apply eta_trans_convertible_reduces with (subst_rec a y k);
   auto with ecoc coc core arith sets.

  apply eta_trans_convertible_expansion with (subst_rec a y k);
   auto with ecoc coc core arith sets.

  induction H as [| y z [Hfwd|Hbwd] Hay IH]; auto with ecoc coc core arith sets.
  apply trans_eta_convertible with (subst_rec y d k);
   auto with ecoc coc core arith sets.

  apply trans_eta_convertible with (subst_rec y d k);
   auto with ecoc coc core arith sets.
  apply sym_eta_convertible; auto with ecoc coc core arith sets.
Qed.

(** Left projection of erasure conversion on products. *)
Lemma inversion_eta_convertible_product_left :
 forall a b c d : term, eta_convertible (prod a c) (prod b d) -> eta_convertible a b.
Proof.
  intros.
  elim eta_church_rosser with (prod a c) (prod b d); intros;
   auto with ecoc coc core arith sets.
  apply eta_reduces_product_product with a c x; intros; auto with ecoc coc core arith sets.
  apply eta_reduces_product_product with b d x; intros; auto with ecoc coc core arith sets.
  apply trans_eta_convertible with a0; auto with ecoc coc core arith sets.
  apply sym_eta_convertible.
  generalize H2.
  rewrite H5; intro.
  injection H8.
  simple induction 2; auto with ecoc coc core arith sets.
Qed.

(** Right projection of erasure conversion on products. *)
Lemma inversion_eta_convertible_product_right :
 forall a b c d : term, eta_convertible (prod a c) (prod b d) -> eta_convertible c d.
Proof.
  intros.
  elim eta_church_rosser with (prod a c) (prod b d); intros;
   auto with ecoc coc core arith sets.
  apply eta_reduces_product_product with a c x; intros; auto with ecoc coc core arith sets.
  apply eta_reduces_product_product with b d x; intros; auto with ecoc coc core arith sets.
  apply trans_eta_convertible with b0; auto with ecoc coc core arith sets.
  apply sym_eta_convertible.
  generalize H2.
  rewrite H5; intro.
  injection H8.
  simple induction 1; auto with ecoc coc core arith sets.
Qed.

Hint Resolve sym_eta_convertible trans_eta_convertible eta_convertible_product eta_convertible_lift
  eta_convertible_subst: ecoc.

(** Well-founded induction principle for erasure reduction. *)
Lemma eta_reduces_reverse_ind :
 forall (N : term) (P : term -> Prop),
 P N ->
 (forall M R : term, eta_reduces_once M R -> eta_reduces R N -> P R -> P M) ->
 forall M : term, eta_reduces M N -> P M.
Proof.
  cut
   (forall M N : term,
    eta_reduces M N ->
    forall P : term -> Prop,
    P N -> (forall M R : term, eta_reduces_once M R -> eta_reduces R N -> P R -> P M) -> P M).
  intros.
  apply (H M N); auto with ecoc coc core arith sets.

  intros M0 N0 H; induction H as [| y z Hyz Hmy IH]; intros P0 HP0 HP1; auto with ecoc coc core arith sets.
  apply IH; auto with ecoc coc core arith sets.
  apply HP1 with z; auto with ecoc coc core arith sets.

  intros.
  apply HP1 with R; auto with ecoc coc core arith sets.
  apply eta_trans_reduces with y; auto with ecoc coc core arith sets.
Qed.

(** Inversion of erasure reduction on a lam. *)
Lemma inversion_eta_reduces_lambda :
 forall T U x : term,
 eta_reduces (lam T U) x -> exists T' : term, (exists U' : term, x = lam T' U').
Proof.
  intros T U x H; induction H as [| y z Hyz Hxy [T' [U' Heq]]].
  split with T; split with U; trivial.
  rewrite Heq in Hyz.
  inversion Hyz.
  split with (sort_term prop); split with U'; trivial.
  split with M'; split with U'; trivial.
  split with T'; split with M'; trivial.
Qed.

(** A lam cannot E-reduce to a sort. *)
Lemma not_eta_reduces_lambda_sort :
 forall (T M : term) (s : sort), ~ eta_reduces (lam T M) (sort_term s).
Proof.
  unfold not in |- *; intros.
  destruct (inversion_eta_reduces_lambda T M (sort_term s) H) as [T' [U' Heq]].
  discriminate Heq.
Qed.

(** If a term E-reduces to a sort, the sort occurs in the term. *)
Lemma eta_reduces_once_sort_occurs :
 forall (t : term) (s : sort), eta_reduces_once t (sort_term s) -> sort_occurs_in s t.
Proof.
  intros t s Hred.
  inversion Hred.
  match goal with
  | Heq : subst _ _ = sort_term s |- _ =>
      elim sort_occurs_in_subst with M N 0 s; intros; auto with coc core arith sets;
      unfold subst in Heq; rewrite Heq; auto with coc
  end.
Qed.

(** Sort membership predicate extended with all term constructors. *)
Inductive sort_occurs_in_eta (s : sort) : term -> Prop :=
  | mem_eta_eq : sort_occurs_in_eta s (sort_term s)
  | mem_eta_prod_l : forall u v : term, sort_occurs_in_eta s u -> sort_occurs_in_eta s (prod u v)
  | mem_eta_prod_r : forall u v : term, sort_occurs_in_eta s v -> sort_occurs_in_eta s (prod u v)
  | mem_eta_abs_r : forall u v : term, sort_occurs_in_eta s v -> sort_occurs_in_eta s (lam u v)
  | mem_eta_app_l : forall u v : term, sort_occurs_in_eta s u -> sort_occurs_in_eta s (app u v)
  | mem_eta_app_r : forall u v : term, sort_occurs_in_eta s v -> sort_occurs_in_eta s (app u v).

Hint Resolve mem_eta_eq mem_eta_prod_l mem_eta_prod_r mem_eta_abs_r mem_eta_app_l
  mem_eta_app_r: ecoc.

(** Extended sort membership is stable under lifting. *)
Lemma sort_occurs_in_eta_lift :
 forall (t : term) (n k : nat) (s : sort),
 sort_occurs_in_eta s (lift_rec n t k) -> sort_occurs_in_eta s t.
Proof.
  induction t as [so|n0|t0 IH0 t1 IH1|t0 IH0 t1 IH1|t0 IH0 t1 IH1];
    simpl in |- *; intros n k s Hocc; auto with ecoc coc core arith sets.
  generalize Hocc; elim (le_gt_dec k n0); intros a Hocc';
   auto with ecoc coc core arith sets.
  inversion_clear Hocc'.

  inversion_clear Hocc.
  apply mem_eta_abs_r; apply IH1 with n (S k); auto with ecoc coc core arith sets.

  inversion_clear Hocc.
  apply mem_eta_app_l; apply IH0 with n k; auto with ecoc coc core arith sets.

  apply mem_eta_app_r; apply IH1 with n k; auto with ecoc coc core arith sets.

  inversion_clear Hocc.
  apply mem_eta_prod_l; apply IH0 with n k; auto with ecoc coc core arith sets.

  apply mem_eta_prod_r; apply IH1 with n (S k); auto with ecoc coc core arith sets.
Qed.

(** Extended sort membership is stable under substitution. *)
Lemma sort_occurs_in_eta_subst :
 forall (b a : term) (n : nat) (s : sort),
 sort_occurs_in_eta s (subst_rec a b n) -> sort_occurs_in_eta s a \/ sort_occurs_in_eta s b.
Proof.
  simple induction b; simpl in |- *; intros; auto with ecoc coc core arith sets.
  generalize H; elim (lt_eq_lt_dec n0 n); [ intro a0 | intro b0 ].
  elim a0; intros.
  inversion_clear H0.

  left.
  apply sort_occurs_in_eta_lift with n0 0; auto with ecoc coc core arith sets.

  intros.
  inversion_clear H0.

  inversion_clear H1.
  elim H0 with a (S n) s; auto with ecoc coc core arith sets.

  inversion_clear H1.
  elim H with a n s; auto with ecoc coc core arith sets.

  elim H0 with a n s; auto with ecoc coc core arith sets.

  inversion_clear H1.
  elim H with a n s; auto with ecoc coc core arith sets.

  elim H0 with a (S n) s; intros; auto with ecoc coc core arith sets.
Qed.

(** If a term E-reduces to a sort, the sort occurs in the term (extended). *)
Lemma eta_reduces_sort_occurs_eta :
 forall (t : term) (s : sort), eta_reduces t (sort_term s) -> sort_occurs_in_eta s t.
Proof.
  intros.
  pattern t in |- *.
  apply eta_reduces_reverse_ind with (sort_term s); auto with ecoc coc core arith sets.
  do 4 intro.
  elim H0; intros.
  elim sort_occurs_in_eta_subst with M0 N 0 s; intros;
   auto with ecoc coc core arith sets.

  inversion H2; auto with ecoc.

  inversion H4; auto with ecoc.

  inversion H4; auto with ecoc.

  inversion H4; auto with ecoc.

  inversion H4; auto with ecoc.

  inversion H4; auto with ecoc.

  inversion H4; auto with ecoc.
Qed.

(** Extended sort membership implies standard sort membership. *)
Lemma sort_occurs_in_eta_sort_occurs :
 forall (t : term) (s : sort), sort_occurs_in_eta s t -> sort_occurs_in s t.
Proof.
  simple induction 1; auto with coc.
Qed.

(** If a term E-reduces to a sort, the sort occurs in the term (standard). *)
Lemma eta_reduces_sort_occurs :
 forall (t : term) (s : sort), eta_reduces t (sort_term s) -> sort_occurs_in s t.
Proof.
  intros; apply sort_occurs_in_eta_sort_occurs; apply eta_reduces_sort_occurs_eta; trivial.
Qed.
