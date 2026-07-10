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

(** Type of interpretations mapping naturals to terms. *)
Definition term_interpretation := nat -> term.

(** Extends an interpretation with a new binding at index 0. *)
Definition shift_term_interpretation (i : term_interpretation) (t : term) : term_interpretation :=
  fun n : nat => match n with
                 | O => t
                 | S k => i k
                 end.

(** Interprets a term under an interpretation and a depth counter. *)
Fixpoint interpret_term (t : term) : term_interpretation -> nat -> term :=
  fun (I : term_interpretation) (k : nat) =>
  match t with
  | sort_term s => sort_term s
  | var n =>
      match le_gt_dec k n with
      | left _ => lift k (I (n - k))
      | right _ => var n
      end
  | lam A t => lam (interpret_term A I k) (interpret_term t I (S k))
  | app u v => app (interpret_term u I k) (interpret_term v I k)
  | prod A B => prod (interpret_term A I k) (interpret_term B I (S k))
  end.

Opaque le_gt_dec.

(** Substitution commutes with term interpretation. *)
Lemma interpret_term_subst :
 forall (t : term) (it : term_interpretation) (k : nat) (x : term),
 subst_rec x (interpret_term t it (S k)) k = interpret_term t (shift_term_interpretation it x) k.
Proof.
  simple induction t; simpl in |- *; intros; auto with coc core arith sets.
  elim (le_gt_dec (S k) n); intros.
  elim (le_gt_dec k n); intros.
  rewrite simplify_subst; auto with coc core arith sets.
  replace (n - k) with (S (n - S k)); auto with coc core arith sets.
  lia.

  elim (lt_eq_lt_dec k n); [ intro Hlt_eq | intro Hlt ].
  elim Hlt_eq; clear Hlt_eq. lia.

  intros ?; subst.
  replace (n - n) with 0; auto with coc core arith sets. simpl.
  elim (le_gt_dec n n); [ intro Hle | intro Hgt ];
   auto with coc core arith sets; try lia.
  elim (lt_eq_lt_dec n n); [|];
   auto with coc core arith sets; try lia.
  intuition lia.
  elim (le_gt_dec k n); intros; auto with coc core arith sets; [lia|].
  simpl.
  elim (lt_eq_lt_dec k n); try intuition lia.

  rewrite H; rewrite H0; auto with coc core arith sets.

  rewrite H; rewrite H0; auto with coc core arith sets.

  rewrite H; rewrite H0; auto with coc core arith sets.
Qed.
