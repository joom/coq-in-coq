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

(** Confluence of beta-reduction via the Church-Rosser theorem.
    Uses Tait-Martin-Löf's method with parallel reduction. *)

From CoqInCoq Require Import terms.

Implicit Types i k m n p : nat.
Implicit Type s : sort.
Implicit Types A B M N T t u v : term.

Section Church_Rosser.

  (** A relation is strongly confluent when it commutes with its transpose. *)
  Definition strongly_confluent (R : term -> term -> Prop) :=
    commut _ R (transp _ R).

  (** One-step parallel reduction is strongly confluent. *)
  Lemma strong_confluence_parallel_reduces_once : strongly_confluent parallel_reduces_once.
  Proof.
    red in |- *; red in |- *.
    simple induction 1; intros.
    inversion_clear H4.
    elim H1 with M'0; auto with coc core arith sets; intros.
    elim H3 with N'0; auto with coc core arith sets; intros.
    exists (subst x1 x0); unfold subst in |- *; auto with coc core arith sets.

    inversion_clear H5.
    elim H1 with M'1; auto with coc core arith sets; intros.
    elim H3 with N'0; auto with coc core arith sets; intros.
    exists (subst x1 x0); auto with coc core arith sets; unfold subst in |- *;
     auto with coc core arith sets.

    inversion_clear H0.
    exists (sort_term s); auto with coc core arith sets.

    inversion_clear H0.
    exists (var n); auto with coc core arith sets.

    inversion_clear H4.
    elim H1 with M'0; auto with coc core arith sets; intros.
    elim H3 with T'0; auto with coc core arith sets; intros.
    exists (lam x1 x0); auto with coc core arith sets.

    generalize H0 H1.
    clear H0 H1.
    inversion_clear H4.
    intro.
    inversion_clear H4.
    intros.
    elim H4 with (lam T M'0); auto with coc core arith sets; intros.
    elim H3 with N'0; auto with coc core arith sets; intros.
    apply inversion_parallel_reduces_lambda with T' M'1 x0; intros; auto with coc core arith sets.
    generalize H7 H8.
    rewrite H11.
    clear H7 H8; intros.
    inversion_clear H7.
    inversion_clear H8.
    exists (subst x1 U'); auto with coc core arith sets.
    unfold subst in |- *; auto with coc core arith sets.

    intros.
    elim H5 with M'0; auto with coc core arith sets; intros.
    elim H3 with N'0; auto with coc core arith sets; intros.
    exists (app x0 x1); auto with coc core arith sets.

    intros.
    inversion_clear H4.
    elim H1 with M'0; auto with coc core arith sets; intros.
    elim H3 with N'0; auto with coc core arith sets; intros.
    exists (prod x0 x1); auto with coc core arith sets.
  Qed.

  (** The strip lemma: parallel reduction commutes with one-step parallel reduction. *)
  Lemma strip_lemma : commut _ parallel_reduces (transp _ parallel_reduces_once).
  Proof.
    unfold commut, parallel_reduces in |- *; simple induction 1; intros.
    elim strong_confluence_parallel_reduces_once with z x0 y0; auto with coc core arith sets;
     intros.
    exists x1; auto with coc core arith sets.

    elim H1 with z0; auto with coc core arith sets; intros.
    elim H3 with x1; intros; auto with coc core arith sets.
    exists x2; auto with coc core arith sets.
    apply t_trans with x1; auto with coc core arith sets.
  Qed.

  (** Multi-step parallel reduction is strongly confluent. *)
  Lemma confluence_parallel_reduces : strongly_confluent parallel_reduces.
  Proof.
    red in |- *; red in |- *.
    simple induction 1; intros.
    elim strip_lemma with z x0 y0; intros; auto with coc core arith sets.
    exists x1; auto with coc core arith sets.

    elim H1 with z0; intros; auto with coc core arith sets.
    elim H3 with x1; intros; auto with coc core arith sets.
    exists x2; auto with coc core arith sets.
    red in |- *.
    apply t_trans with x1; auto with coc core arith sets.
  Qed.

  (** Beta-reduction is strongly confluent. *)
  Lemma confluence_reduces : strongly_confluent reduces.
  Proof.
    red in |- *; red in |- *.
    intros.
    elim confluence_parallel_reduces with x y z; auto with coc core arith sets; intros.
    exists x0; auto with coc core arith sets.
  Qed.

  (** The Church-Rosser theorem: convertible terms have a common reduct. *)
  Theorem church_rosser_theorem :
   forall u v, convertible u v -> ex2 (fun t => reduces u t) (fun t => reduces v t).
  Proof.
    intros u v H; induction H as [| y z Hstep Huy [x Hux Hyx]].
    - exists u; auto with coc core arith sets.
    - destruct Hstep as [Hfwd | Hbwd].
      + elim confluence_reduces with x y z; auto with coc core arith sets; intros.
        exists x0; auto with coc core arith sets.
        apply trans_reduces_reduces with x; auto with coc core arith sets.
      + exists x; auto with coc core arith sets.
        apply trans_reduces_reduces with y; auto with coc core arith sets.
  Qed.

  (** If two products are convertible, their domains are convertible. *)
  Lemma inversion_convertible_product_left :
   forall a b c d : term, convertible (prod a c) (prod b d) -> convertible a b.
  Proof.
    intros.
    elim church_rosser_theorem with (prod a c) (prod b d); intros;
     auto with coc core arith sets.
    apply reduces_product_product with a c x; intros; auto with coc core arith sets.
    apply reduces_product_product with b d x; intros; auto with coc core arith sets.
    apply trans_convertible_convertible with a0; auto with coc core arith sets.
    apply sym_convertible.
    generalize H2.
    rewrite H5; intro.
    injection H8.
    simple induction 2; auto with coc core arith sets.
  Qed.

  (** If two products are convertible, their codomains are convertible. *)
  Lemma inversion_convertible_product_right :
   forall a b c d : term, convertible (prod a c) (prod b d) -> convertible c d.
  Proof.
    intros.
    elim church_rosser_theorem with (prod a c) (prod b d); intros;
     auto with coc core arith sets.
    apply reduces_product_product with a c x; intros; auto with coc core arith sets.
    apply reduces_product_product with b d x; intros; auto with coc core arith sets.
    apply trans_convertible_convertible with b0; auto with coc core arith sets.
    apply sym_convertible.
    generalize H2.
    rewrite H5; intro.
    injection H8.
    simple induction 1; auto with coc core arith sets.
  Qed.

  (** Normal forms are unique up to conversion. *)
  Lemma normal_form_uniqueness : forall u v, convertible u v -> normal u -> normal v -> u = v.
  Proof.
    intros.
    elim church_rosser_theorem with u v; intros; auto with coc core arith sets.
    rewrite (reduces_normal u x); auto with coc core arith sets.
    elim reduces_normal with v x; auto with coc core arith sets.
  Qed.

  (** Convertible sorts must be equal. *)
  Lemma convertible_sort : forall s1 s2, convertible (sort_term s1) (sort_term s2) -> s1 = s2.
  Proof.
    intros.
    cut (sort_term s1 = sort_term s2); intros.
    injection H0; auto with coc core arith sets.

    apply normal_form_uniqueness; auto with coc core arith sets.
    red in |- *; red in |- *; intros.
    inversion_clear H0.

    red in |- *; red in |- *; intros.
    inversion_clear H0.
  Qed.

  (** Kind and prop are not convertible. *)
  Lemma convertible_kind_prop : ~ convertible (sort_term kind) (sort_term prop).
  Proof.
    red in |- *; intro.
    absurd (kind = prop).
    discriminate.

    apply convertible_sort; auto with coc core arith sets.
  Qed.

  (** A sort is never convertible with a prod. *)
  Lemma convertible_sort_product : forall s t u, ~ convertible (sort_term s) (prod t u).
  Proof.
    red in |- *; intros.
    elim church_rosser_theorem with (sort_term s) (prod t u); auto with coc core arith sets.
    do 2 intro.
    elim reduces_normal with (sort_term s) x; auto with coc core arith sets.
    intro.
    apply reduces_product_product with t u (sort_term s); auto with coc core arith sets; intros.
    discriminate H2.

    red in |- *; red in |- *; intros.
    inversion_clear H1.
  Qed.

End Church_Rosser.
