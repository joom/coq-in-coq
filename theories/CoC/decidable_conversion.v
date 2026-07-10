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


From Stdlib Require Import Transitive_Closure.
From Stdlib Require Import Union.

From CoC Require Import terms.
From CoC Require Import confluence.

(** One-step normalization order: subterm or reverse reduction. *)
Definition normalization_order_once := union _ subterm (transp _ reduces_once_prop).

(** Transitive closure of the one-step normalization order. *)
Definition normalization_order := clos_trans _ normalization_order_once.

Hint Unfold normalization_order_once normalization_order: coc.

(** The subterm relation is contained in the normalization order. *)
Lemma subterm_normalization_order : forall a b : term, subterm a b -> normalization_order a b.
Proof.
  auto 10 with coc sets.
Qed.

Hint Resolve subterm_normalization_order: coc.

(** A reduction sequence followed by a one-step reduction yields a normalization order step. *)
Lemma reduces_reduces_once_normalization_order :
 forall a b : term, reduces a b -> forall c : term, reduces_once b c -> normalization_order c a.
Proof.
  intros a b H.
  induction H as [ M0 | M0 P0 N0 Hstep0 Hred0 IH0 ]; intros c Hc.
  - apply Relation_Operators.t_step; right; constructor; exact Hc.
  - apply Relation_Operators.t_trans with N0.
    + apply Relation_Operators.t_step; right; constructor; exact Hc.
    + apply IH0; exact Hstep0.
Qed.

(** The subterm relation is well-founded. *)
Lemma well_founded_subterm : well_founded subterm.
Proof.
  red in |- *.
  simple induction a; intros; apply Acc_intro; intros.
  inversion_clear H; inversion_clear H0.
  inversion_clear H; inversion_clear H0.
  inversion_clear H1; inversion_clear H2; auto with coc sets.
  inversion_clear H1; inversion_clear H2; auto with coc sets.
  inversion_clear H1; inversion_clear H2; auto with coc sets.
Qed.

(** Strongly normalizing terms are accessible for the one-step normalization order. *)
Lemma well_founded_normalization_order_once : forall t : term, strongly_normalizing t -> Acc normalization_order_once t.
Proof.
  unfold normalization_order_once in |- *.
  intros.
  apply Acc_union; auto with coc sets.
  exact commute_reduces_once_subterm.
  intros.
  apply well_founded_subterm.
Qed.

(** Strongly normalizing terms are accessible for the normalization order. *)
Theorem well_founded_normalization_order : forall t : term, strongly_normalizing t -> Acc normalization_order t.
Proof.
  unfold normalization_order in |- *.
  intros.
  apply Acc_clos_trans.
  apply well_founded_normalization_order_once; auto with coc sets.
Qed.

(** Recursive body for computing normal forms by case analysis on the term. *)
Definition normalization_body (a : term) (norm : term -> term) :=
  match a with
  | sort_term s => sort_term s
  | var n => var n
  | lam T t => lam (norm T) (norm t)
  | app u v =>
      match norm u return term with
      | lam _ b => norm (subst (norm v) b)
      | t => app t (norm v)
      end
  | prod T U => prod (norm T) (norm U)
  end.

(** Computes the normal form of a strongly normalizing term. *)
Definition compute_normal_form :
 forall t : term, strongly_normalizing t -> {u : term & reduces t u & normal u}.
Proof.
  intros.
  cut (Acc normalization_order t); [intros _H'; elim _H' |].
  clear _H' H t.
  intros [s| n| T t| u v| T U] _ norm_rec.
  exists (sort_term s); auto with coc.
  red in |- *; intros.
  inversion_clear H.
  exists (var n); auto with coc.
  red in |- *; intros.
  inversion_clear H.
  elim norm_rec with T; auto with coc; intros T' redT nT.
  elim norm_rec with t; auto with coc; intros t' redt nt.
  exists (lam T' t'); auto with coc.
  red in |- *; intros.
  inversion_clear H.
  elim nT with M'; trivial.
  elim nt with M'; trivial.
  elim norm_rec with v; auto with coc; intros v' redv nv.
  elim norm_rec with u; auto with coc.
  intros [s| n| T t| a b| T U] redu nu.
  exists (app (sort_term s) v'); auto with coc.
  red in |- *; intros.
  inversion_clear H.
  inversion_clear H0.
  elim nv with N2; trivial.
  exists (app (var n) v'); auto with coc.
  red in |- *; intros.
  inversion_clear H.
  inversion_clear H0.
  elim nv with N2; trivial.
  elim norm_rec with (subst v' t).
  intros t' redt nt.
  exists t'; trivial.
  apply trans_reduces_reduces with (subst v' t); auto with coc.
  apply trans_red with (app (lam T t) v'); auto with coc.
  apply reduces_reduces_once_normalization_order with (app (lam T t) v'); auto with coc.
  exists (app (app a b) v'); auto with coc.
  red in |- *; intros.
  inversion_clear H.
  elim nu with N1; trivial.
  elim nv with N2; trivial.
  exists (app (prod T U) v'); auto with coc.
  red in |- *; intros.
  inversion_clear H.
  elim nu with N1; trivial.
  elim nv with N2; trivial.
  elim norm_rec with T; auto with coc; intros T' redT nT.
  elim norm_rec with U; auto with coc; intros U' redU nU.
  exists (prod T' U'); auto with coc.
  red in |- *; intros.
  inversion_clear H.
  elim nT with N1; trivial.
  elim nU with N2; trivial.
  apply well_founded_normalization_order; auto with coc.
Defined.

(** Decidable syntactic equality of terms. *)
Definition term_eq_dec : forall u v : term, {u = v} + {u <> v}.
Proof.
  decide equality.
  decide equality.
  apply Nat.eq_dec.
Defined.

(** Decidable conversion for strongly normalizing terms. *)
Definition is_convertible :
 forall u v : term, strongly_normalizing u -> strongly_normalizing v ->
   convertible u v + (convertible u v -> False).
Proof.
  intros u v snu snv.
  elim compute_normal_form with (1 := snu); intros u' redu nu.
  elim compute_normal_form with (1 := snv); intros v' redv nv.
  elim term_eq_dec with u' v'; [ intros same_nf | intros diff_nf ].
  left.
  apply trans_convertible_convertible with u'; auto with coc.
  rewrite same_nf; apply sym_convertible; auto with coc.
  right; intro Hconv; apply diff_nf.
  assert (Hconv' : convertible u' v').
  { apply trans_convertible_convertible with v; auto with coc.
    apply trans_convertible_convertible with u; auto with coc.
    apply sym_convertible; auto with coc. }
  destruct (church_rosser_theorem u' v' Hconv') as [x Hx1 Hx2]; auto with coc.
  rewrite (reduces_normal u' x); auto with coc.
  rewrite (reduces_normal v' x); auto with coc.
Defined.
