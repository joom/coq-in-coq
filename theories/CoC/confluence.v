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

From CoC Require Import terms.

Implicit Types i k m n p : nat.
Implicit Type s : sort.
Implicit Types A B M N T t u v : term.

Section Church_Rosser.

  (** A Type-valued relation is strongly confluent when any two one-step
      divergent reducts can be joined again. *)
  Definition strongly_confluent_ty (R : term -> term -> Type) :=
    forall x y, R x y -> forall z, R x z -> sigT2 (R y) (R z).

  (** One-step parallel reduction is strongly confluent. *)
  Lemma strong_confluence_parallel_reduces_once : strongly_confluent_ty parallel_reduces_once.
  Proof.
    unfold strongly_confluent_ty.
    induction 1 as
      [ M0 M0' HstepM IHM N0 N0' HstepN IHN T0
      | s0
      | n0
      | M0 M0' HstepM IHM T0 T0' HstepT IHT
      | M0 M0' HstepM IHM N0 N0' HstepN IHN
      | M0 M0' HstepM IHM N0 N0' HstepN IHN ];
    intros z Hz.
    - (* par_beta : app (lam T0 M0) N0 ~> subst N0' M0' *)
      inversion Hz as
        [ Ma Ma' HstepMa Na Na' HstepNa Ta Heq1 Heq2
        | sa Heq1
        | na Heq1
        | Ma Ma' HstepMa Ta Ta' HstepTa Heq1 Heq2
        | Ma Ma' HstepMa Na Na' HstepNa Heq1 Heq2
        | Ma Ma' HstepMa Na Na' HstepNa Heq1 Heq2 ]; subst.
      + (* z obtained via par_beta as well *)
        destruct (IHM Ma' HstepMa) as [x Hx1 Hx2].
        destruct (IHN Na' HstepNa) as [y Hy1 Hy2].
        exists (subst y x); unfold subst;
          apply parallel_reduces_once_subst; auto with coc core arith sets.
      + (* z obtained via app_par_red applied to (lam T0 M0) and N0 *)
        inversion HstepMa as
          [ | | | Mb Mb' HstepMb Tb Tb' HstepTb Heq3 Heq4 | | ]; subst.
        destruct (IHM Mb' HstepMb) as [x Hx1 Hx2].
        destruct (IHN Na' HstepNa) as [y Hy1 Hy2].
        exists (subst y x); unfold subst.
        * apply parallel_reduces_once_subst; auto with coc core arith sets.
        * apply par_beta; auto with coc core arith sets.
    - (* sort_par_red *)
      inversion Hz as [ | sa Heq1 | | | | ]; subst.
      exists (sort_term s0); auto with coc core arith sets.
    - (* ref_par_red *)
      inversion Hz as [ | | na Heq1 | | | ]; subst.
      exists (var n0); auto with coc core arith sets.
    - (* abs_par_red *)
      inversion Hz as
        [ | | | Ma Ma' HstepMa Ta Ta' HstepTa Heq1 Heq2 | | ]; subst.
      destruct (IHM Ma' HstepMa) as [x Hx1 Hx2].
      destruct (IHT Ta' HstepTa) as [y Hy1 Hy2].
      exists (lam y x); auto with coc core arith sets.
    - (* app_par_red *)
      inversion Hz as
        [ Ma Ma' HstepMa Na Na' HstepNa Ta Heq1 Heq2
        | | |
        | Ma Ma' HstepMa Na Na' HstepNa Heq1 Heq2
        | ]; subst.
      + (* z obtained via par_beta: M0 must be a lambda *)
        inversion HstepM as
          [ | | | Mb Mb' HstepMb Tb Tb' HstepTb Heq3 Heq4 | | ]; subst.
        destruct (IHM (lam Ta Ma')
                    (abs_par_red _ _ HstepMa _ _ (refl_parallel_reduces_once Ta)))
          as [x Hx1 Hx2].
        destruct (IHN Na' HstepNa) as [y Hy1 Hy2].
        inversion Hx1 as
          [ | | | Mc Mc' HstepMc Tc Tc' HstepTc Heq5 Heq6 | | ]; subst.
        inversion Hx2 as
          [ | | | Md Md' HstepMd Td Td' HstepTd Heq7 Heq8 | | ]; subst.
        exists (subst y Mc'); unfold subst.
        * apply par_beta; auto with coc core arith sets.
        * apply parallel_reduces_once_subst; auto with coc core arith sets.
      + destruct (IHM Ma' HstepMa) as [x Hx1 Hx2].
        destruct (IHN Na' HstepNa) as [y Hy1 Hy2].
        exists (app x y); auto with coc core arith sets.
    - (* prod_par_red *)
      inversion Hz as
        [ | | | | | Ma Ma' HstepMa Na Na' HstepNa Heq1 Heq2 ]; subst.
      destruct (IHM Ma' HstepMa) as [x Hx1 Hx2].
      destruct (IHN Na' HstepNa) as [y Hy1 Hy2].
      exists (prod x y); auto with coc core arith sets.
  Qed.

  (** The strip lemma: parallel reduction commutes with one-step parallel reduction. *)
  Lemma strip_lemma :
    forall x y, parallel_reduces x y ->
    forall z, parallel_reduces_once x z -> sigT2 (parallel_reduces_once y) (parallel_reduces z).
  Proof.
    induction 1 as [x y Hxy | x p y Hxp IHxp Hpy IHpy]; intros z Hz.
    - destruct (strong_confluence_parallel_reduces_once x y Hxy z Hz) as [t Ht1 Ht2].
      exists t; auto with coc core arith sets.
    - destruct (IHxp z Hz) as [q Hq1 Hq2].
      destruct (IHpy q Hq1) as [t Ht1 Ht2].
      exists t; auto with coc core arith sets.
      apply t_trans with q; auto with coc core arith sets.
  Qed.

  (** Multi-step parallel reduction is strongly confluent. *)
  Lemma confluence_parallel_reduces : strongly_confluent_ty parallel_reduces.
  Proof.
    unfold strongly_confluent_ty.
    induction 1 as [x y Hxy | x p y Hxp IHxp Hpy IHpy]; intros z Hz.
    - destruct (strip_lemma x z Hz y Hxy) as [t Ht1 Ht2].
      exists t; auto with coc core arith sets.
    - destruct (IHxp z Hz) as [q Hq1 Hq2].
      destruct (IHpy q Hq1) as [t Ht1 Ht2].
      exists t; auto with coc core arith sets.
      apply t_trans with q; auto with coc core arith sets.
  Qed.

  (** Beta-reduction is strongly confluent. *)
  Lemma confluence_reduces : strongly_confluent_ty reduces.
  Proof.
    unfold strongly_confluent_ty.
    intros x y Hxy z Hxz.
    destruct (confluence_parallel_reduces x y (reduces_parallel_reduces x y Hxy)
                z (reduces_parallel_reduces x z Hxz)) as [t Ht1 Ht2].
    exists t; apply parallel_reduces_reduces; auto with coc core arith sets.
  Qed.

  (** The Church-Rosser theorem: convertible terms have a common reduct. *)
  Theorem church_rosser_theorem :
   forall u v, convertible u v -> sigT2 (reduces u) (reduces v).
  Proof.
    intros u v H; induction H as [ M0 | M0 P0 N0 Hstep0 Hconv0 IH | M0 P0 N0 Hstep0 Hconv0 IH ].
    - exists M0; auto with coc core arith sets.
    - destruct IH as [x Hux Hyx].
      destruct (confluence_reduces P0 x Hyx N0 (one_step_reduces P0 N0 Hstep0)) as [x0 Hx1 Hx2].
      exists x0; auto with coc core arith sets.
      apply trans_reduces_reduces with x; auto with coc core arith sets.
    - destruct IH as [x Hux Hyx].
      exists x; auto with coc core arith sets.
      apply trans_reduces_reduces with P0; auto with coc core arith sets.
  Qed.

  (** If two products are convertible, their domains are convertible. *)
  Lemma inversion_convertible_product_left :
   forall a b c d : term, convertible (prod a c) (prod b d) -> convertible a b.
  Proof.
    intros a b c d H.
    destruct (church_rosser_theorem (prod a c) (prod b d) H) as [t Ht1 Ht2].
    apply (reduces_product_product a c t Ht1 (convertible a b)); intros a0 c0 Heq1 Ha0 Hc0.
    apply (reduces_product_product b d t Ht2 (convertible a b)); intros b0 d0 Heq2 Hb0 Hd0.
    apply trans_convertible_convertible with a0; auto with coc core arith sets.
    apply sym_convertible.
    rewrite Heq2 in Heq1.
    injection Heq1 as Heqa Heqc; subst.
    auto with coc core arith sets.
  Qed.

  (** If two products are convertible, their codomains are convertible. *)
  Lemma inversion_convertible_product_right :
   forall a b c d : term, convertible (prod a c) (prod b d) -> convertible c d.
  Proof.
    intros a b c d H.
    destruct (church_rosser_theorem (prod a c) (prod b d) H) as [t Ht1 Ht2].
    apply (reduces_product_product a c t Ht1 (convertible c d)); intros a0 c0 Heq1 Ha0 Hc0.
    apply (reduces_product_product b d t Ht2 (convertible c d)); intros b0 d0 Heq2 Hb0 Hd0.
    apply trans_convertible_convertible with c0; auto with coc core arith sets.
    apply sym_convertible.
    rewrite Heq2 in Heq1.
    injection Heq1 as Heqa Heqc; subst.
    auto with coc core arith sets.
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
    red in |- *; intros.
    inversion_clear H0.

    red in |- *; intros.
    inversion_clear H0.
  Qed.

  (** Kind and prop are not convertible. *)
  Lemma convertible_kind_prop : convertible (sort_term kind) (sort_term prop) -> False.
  Proof.
    intro.
    absurd (kind = prop).
    discriminate.

    apply convertible_sort; auto with coc core arith sets.
  Qed.

  (** A sort is never convertible with a prod. *)
  Lemma convertible_sort_product : forall s t u, convertible (sort_term s) (prod t u) -> False.
  Proof.
    intros s t u H.
    destruct (church_rosser_theorem (sort_term s) (prod t u) H) as [x Hx1 Hx2].
    assert (Heq : sort_term s = x).
    { apply reduces_normal; auto with coc core arith sets.
      red; intros v Hv; inversion_clear Hv. }
    rewrite <- Heq in Hx2.
    apply (reduces_product_product t u (sort_term s) Hx2 False); intros a b Heqab Ha Hb.
    discriminate Heqab.
  Qed.

End Church_Rosser.
