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


From Stdlib Require Import Lia.
From CoqInCoq Require Import terms.
From CoqInCoq Require Import confluence.
From CoqInCoq Require Import typing.
From CoqInCoq Require Import classification.
From CoqInCoq Require Import candidates.
From CoqInCoq Require Import interpretation_type.

(** Equivalent interpretations yield equal canonical inhabitants. *)
Lemma interpret_equiv_interpret_type :
 forall (T : term) (i i' : interpretation_env),
 interpretation_eq_can i i' ->
 forall s : skeleton, eq_can s (interpret_type T i s) (interpret_type T i' s).
Proof.
  simple induction T; simpl in |- *; intros; auto with coc core arith datatypes.
  generalize n.
  elim H; auto with coc core arith datatypes.
  intros.
  rewrite nth_overflow by (simpl; lia).
  apply eq_can_extract.
  simpl in |- *; auto with coc core arith datatypes.

  simple destruct n0; intros; auto with coc core arith datatypes.
  inversion_clear H0; apply eq_can_extract || simpl in |- *;
   auto with coc core arith datatypes.

  simpl in |- *; auto with coc core arith datatypes.

  unfold default_cons, interpretation_cons, extend_interpretation_kind in |- *.
  elim interpretation_eq_can_classes with i i'; auto with coc core arith datatypes.
  elim (classify_term t (classes_of_interpretation i)); simpl in |- *;
   auto with coc core arith datatypes.
  case s; simpl in |- *; auto with coc core arith datatypes.

  unfold skeleton_interpretation in |- *.
  elim interpretation_eq_can_classes with i i'; auto with coc core arith datatypes.
  elim (classify_term t0 (classes_of_interpretation i)); auto with coc core arith datatypes.
  intros.
  generalize (H i i' H1 (prod_skel s0 s)).
  unfold skeleton_interpretation in |- *.
  simpl in |- *; intros.
  apply H2; auto with coc core arith datatypes.
  apply H0; auto with coc core arith datatypes.
  elim H1; intros; auto with coc core arith datatypes.
  inversion_clear H3; auto with coc core arith datatypes.

  apply H0; auto with coc core arith datatypes.
  elim H1; intros; auto with coc core arith datatypes.
  inversion_clear H3; auto with coc core arith datatypes.

  case s; simpl in |- *; auto with coc core arith datatypes.
  unfold interpretation_cons, extend_interpretation_kind in |- *.
  elim interpretation_eq_can_classes with i i'; auto with coc core arith datatypes.
  apply eq_can_Pi; auto with coc core arith datatypes.
  simpl in |- *; intros.
  replace eq_candidate with (eq_can prop_skel); auto with coc core arith datatypes.
  apply H0.
  pattern (classify_term t (classes_of_interpretation i)) at 1 3 in |- *.
  elim (classify_term t (classes_of_interpretation i)); auto with coc core arith datatypes.
Qed.

Hint Resolve interpret_equiv_interpret_type: coc.


(** Characterizes well-formed interpretation entries. *)
Inductive can_interpret : interpretation_kind -> Prop :=
  | can_interp_knd :
      forall (s : skeleton) (C : candidate s),
      is_can s C -> eq_can s C C -> can_interpret (interp_knd s C)
  | can_interp_typ : can_interpret interp_typ.

Hint Resolve can_interp_knd can_interp_typ: coc.

(** All entries in the interpretation are canonical. *)
Definition can_adapt : interpretation_env -> Prop := Forall can_interpret.

Hint Unfold can_adapt: coc.


(** A canonical interpretation satisfies the invariant. *)
Lemma adapt_interpretation_invariant : forall ip : interpretation_env, can_adapt ip -> interpretation_invariant ip.
Proof.
  simple induction 1; simpl in |- *; auto with coc core arith datatypes.
  simple induction 1; auto with coc core arith datatypes.
Qed.

Hint Resolve adapt_interpretation_invariant: coc.


(** Interpretation of a typed term yields a canonical inhabitant. *)
Lemma interpret_type_cr :
 forall (t : term) (ip : interpretation_env),
 can_adapt ip -> forall s : skeleton, is_can s (interpret_type t ip _).
Proof.
  simple induction t; simpl in |- *; intros; auto with coc core arith datatypes.
  generalize n.
  elim H; intros.
  rewrite nth_overflow by (simpl; lia).
  apply is_can_coerce; apply candidate_strongly_normalizing.

  case n0; simpl in |- *; auto with coc core arith datatypes.
  inversion_clear H0; auto with coc; simpl in |- *; auto with coc.

  unfold default_cons, interpretation_cons, extend_interpretation_kind in |- *.
  elim (classify_term t0 (classes_of_interpretation ip)); auto with coc core arith datatypes.
  case s; simpl in |- *; auto with coc core arith datatypes.

  elim (classify_term t1 (classes_of_interpretation ip)); auto with coc core arith datatypes.
  intros.
  generalize (H ip H1 (prod_skel s0 s)); simpl in |- *;
   auto with coc core arith datatypes.

  case s; simpl in |- *; auto with coc core arith datatypes.
  apply is_can_Pi; simpl in |- *; intros; auto with coc core arith datatypes.
  unfold default_cons, interpretation_cons, extend_interpretation_kind in |- *.
  generalize X H2 H3.
  elim (classify_term t0 (classes_of_interpretation ip)); auto with coc core arith datatypes.
  simpl in |- *.
  intros.
  change (is_can prop_skel (interpret_type t1 (cons (interp_knd s0 X0) ip) prop_skel)) in |- *;
   auto with coc core arith datatypes.
Qed.
(*
  Hints Resolve interpret_type_cr : coc.
*)


(** Lifting a variable reference past an insertion preserves interpretation. *)
Lemma nth_lift_interpretation :
 forall (y : interpretation_kind) (s0 : skeleton) (ipe ipf : interpretation_env) (n k : nat),
 insert y k ipe ipf ->
 interpret_type (lift_rec 1 (var n) k) ipf s0 = interpret_type (var n) ipe s0.
Proof.
  intros y s0 ipe ipf n k H.
  simpl.
  destruct (le_gt_dec k n) as [Hkn | Hkn].
  - (* n >= k: lift gives 1+n in ipf = n in ipe *)
    rewrite (insert_nth_ge k ipe ipf _ y H n Hkn); auto.
  - (* n < k: lift gives n in ipf = n in ipe *)
    rewrite (insert_nth_lt k ipe ipf _ y H n Hkn); auto.
Qed.


(** Lifting a term preserves its interpretation up to canonical equality. *)
Lemma lift_interpret_type :
 forall (y : interpretation_kind) (T : term) (k : nat) (ipe ipf : interpretation_env),
 insert y k ipe ipf ->
 interpretation_invariant ipf ->
 forall s : skeleton,
 eq_can s (interpret_type T ipe s) (interpret_type (lift_rec 1 T k) ipf s).
Proof.
  simple induction T.
  simpl in |- *; auto with coc core arith datatypes.

  intros.
  elim nth_lift_interpretation with y s ipe ipf n k; intros;
   auto with coc core arith datatypes.

  simpl in |- *; intros.
  unfold default_cons, interpretation_cons, extend_interpretation_kind in |- *.
  elim classify_term_lift with (class_of_interpretation_kind y) t k (classes_of_interpretation ipe) (classes_of_interpretation ipf);
   auto with coc core arith datatypes.
  elim (classify_term t (classes_of_interpretation ipe)); auto with coc core arith datatypes.
  case s; simpl in |- *; intros; auto with coc core arith datatypes.
  apply
   eq_can_trans with (interpret_type (lift_rec 1 t0 (S k)) (cons (interp_knd s0 X1) ipf) s1);
   auto 10 with coc core arith datatypes.

  apply insert_in_classes with y; auto with coc core arith datatypes.

  simpl in |- *; intros.
  elim classify_term_lift with (class_of_interpretation_kind y) t k (classes_of_interpretation ipe) (classes_of_interpretation ipf);
   auto with coc core arith datatypes.
  elim classify_term_lift with (class_of_interpretation_kind y) t0 k (classes_of_interpretation ipe) (classes_of_interpretation ipf);
   auto with coc core arith datatypes.
  elim (classify_term t0 (classes_of_interpretation ipe)); auto with coc core arith datatypes.
  intros.
  generalize (H k ipe ipf H1 H2 (prod_skel s0 s)).
  simpl in |- *; intros.
  apply H3; auto with coc core arith datatypes.
  apply interpret_equiv_interpret_type.
  apply interpretation_invariant_eq_can.
  apply insert_interpretation_invariant with ipf k y; auto with coc core arith datatypes.

  apply insert_in_classes with y; auto with coc core arith datatypes.

  apply insert_in_classes with y; auto with coc core arith datatypes.

  simpl in |- *; intros.
  case s; simpl in |- *; intros; auto with coc core arith datatypes.
  unfold default_cons, interpretation_cons, extend_interpretation_kind in |- *.
  elim classify_term_lift with (class_of_interpretation_kind y) t k (classes_of_interpretation ipe) (classes_of_interpretation ipf);
   auto with coc core arith datatypes.
  apply eq_can_Pi; auto with coc core arith datatypes.
  simpl in |- *; intros.
  replace eq_candidate with (eq_can prop_skel); auto with coc core arith datatypes.
  pattern (classify_term t (classes_of_interpretation ipe)) at 1 3 in |- *.
  elim (classify_term t (classes_of_interpretation ipe)); auto with coc core arith datatypes; intros.
  apply
   eq_can_trans with (interpret_type (lift_rec 1 t0 (S k)) (cons (interp_knd _ X1) ipf) prop_skel);
   auto 10 with coc core arith datatypes.

  apply insert_in_classes with y; auto with coc core arith datatypes.
Qed.


(** Relates a term's classification to its interpretation entry. *)
Inductive interpret_var_sound (t : term) (ip : interpretation_env) : interpretation_kind -> Prop :=
  | interp_var_knd :
      forall s : skeleton,
      classify_term t (classes_of_interpretation ip) = typ s ->
      interpret_var_sound t ip (interp_knd _ (interpret_type t ip s))
  | interp_var_typ : classify_term t (classes_of_interpretation ip) = trm -> interpret_var_sound t ip interp_typ.


(** Soundness of interpret_var_sound implies type_class compatibility. *)
Lemma interpret_var_sound_lift :
 forall (t : term) (ip : interpretation_env) (i : interpretation_kind),
 interpret_var_sound t ip i ->
 type_class (classify_term t (classes_of_interpretation ip)) (class_of_interpretation_kind i).
Proof.
  intros.
  elim H; simpl in |- *; intros; rewrite H0; auto with coc core arith datatypes.
Qed.

Hint Resolve interp_var_knd interp_var_typ interpret_var_sound_lift: coc.


(** Substitution commutes with interpretation up to canonical equality. *)
Lemma subst_interpret_type :
 forall (v : term) (ipg : interpretation_env) (i : interpretation_kind),
 interpret_var_sound v ipg i ->
 forall (e : environment) (T K : term),
 has_type e T K ->
 forall (k : nat) (ipe ipf : interpretation_env),
 insert i k ipf ipe ->
 ipg = skipn k ipf ->
 classes_of_interpretation ipe = classify_environment e ->
 interpretation_invariant ipe ->
 classify_term T (classes_of_interpretation ipe) <> trm ->
 eq_can (skeleton_interpretation T ipe) (interpret_type T ipe _)
   (interpret_type (subst_rec v T k) ipf _).
Proof.
  simple induction 2; intros.
  simpl in |- *; auto with coc core arith datatypes.

  simpl in |- *; auto with coc core arith datatypes.

  unfold subst_rec in |- *.
  elim (lt_eq_lt_dec k v0); [ intro Hlt_eq | intro Hlt ].
  elim Hlt_eq; clear Hlt_eq; [ idtac | intro Heq ].
  case v0; [ intro Hlt | intros n Hlt ].
  inversion_clear Hlt.

  unfold pred in |- *.
  elim nth_lift_interpretation with i (skeleton_interpretation (var (S n)) ipe) ipf ipe n k;
   auto with coc core arith datatypes.
  rewrite lift_ref_ge; auto with coc core arith datatypes.

  generalize H H3 H4 H5 H6 H7.
  elim Heq.
  clear H H3 H4 H5 H6 H7 Heq.
  clear H1 H2.
  (* Induct on k to handle the k = v0 case *)
  { revert ipf ipe ipg e0.
  induction k as [|k' IHkins].
  - (* k = 0 *)
    intros ipf ipe ipg e0 H H3 H4 H5 H6 H7.
    destruct H3 as [Hipe Hle].
    subst ipg.
    subst ipe.
    simpl in *.
    rewrite lift_zero.
    unfold skeleton_interpretation; simpl.
    inversion H as [s0 Hcls | Hcls]; subst.
    + (* interp_var_knd *)
      unfold class_of_interpretation_kind, type_skeleton.
      apply extract_eq with (P := fun s c => eq_can s c (interpret_type v ipf s)).
      unfold interpretation_invariant, interpretation_eq_can in H6.
      inversion H6 as [|h1 h2 t1 t2 Hik Htail]; subst.
      inversion_clear Hik; auto with coc core arith datatypes.
    + (* interp_var_typ *)
      exfalso. apply H7. simpl. reflexivity.
  - (* k = S k' *)
    intros ipf ipe ipg e0 H H3 H4 H5 H6 H7.
    destruct H3 as [Hipe Hle].
    subst ipg.
    subst ipe.
    destruct ipf as [|y ipf']; [simpl in Hle; lia|].
    change (skeleton_interpretation (var (S k')) (y :: firstn k' ipf' ++ i :: skipn k' ipf'))
      with (skeleton_interpretation (var k') (firstn k' ipf' ++ i :: skipn k' ipf')).
    change (nth (S k') (y :: firstn k' ipf' ++ i :: skipn k' ipf') (interp_knd prop_skel strongly_normalizing))
      with (nth k' (firstn k' ipf' ++ i :: skipn k' ipf') (interp_knd prop_skel strongly_normalizing)).
    destruct e0 as [|h0 e0'].
    + discriminate H5.
    + injection H5 as Hhy H5'.
      apply eq_can_trans with (interpret_type (lift k' v) ipf' (skeleton_interpretation (var k') (firstn k' ipf' ++ i :: skipn k' ipf'))).
      * eapply (IHkins ipf' (firstn k' ipf' ++ i :: skipn k' ipf') (skipn k' ipf') e0').
        -- exact H.
        -- unfold insert; split; [reflexivity | auto with arith].
        -- reflexivity.
        -- exact H5'.
        -- apply (insert_interpretation_invariant (firstn k' ipf' ++ i :: skipn k' ipf')
                             (y :: firstn k' ipf' ++ i :: skipn k' ipf') 0 y);
           [apply insert_head | exact H6].
        -- intro Hc; apply H7; exact Hc.
      * (* eq_can sk' X X - self-compatibility via interpretation_invariant ipf' *)
        assert (Hinvy : interpretation_invariant (y :: ipf')).
        { apply (insert_interpretation_invariant (y :: ipf') (y :: firstn k' ipf' ++ i :: skipn k' ipf') (S k') i).
          - unfold insert; simpl; split; [reflexivity | exact Hle].
          - exact H6. }
        assert (Hinvipf' : interpretation_invariant ipf') by
          (apply (insert_interpretation_invariant ipf' (y :: ipf') 0 y); [apply insert_head | exact Hinvy]).
        apply interpret_equiv_interpret_type.
        exact (interpretation_invariant_eq_can ipf' Hinvipf').
      * (* eq_can sk' X RHS - from lift_interpret_type *)
        assert (Hinvy : interpretation_invariant (y :: ipf')).
        { apply (insert_interpretation_invariant (y :: ipf') (y :: firstn k' ipf' ++ i :: skipn k' ipf') (S k') i).
          - unfold insert; simpl; split; [reflexivity | exact Hle].
          - exact H6. }
        rewrite simplify_lift.
        exact (lift_interpret_type y _ 0 ipf' (y :: ipf') (insert_head y ipf') Hinvy _). }

  elim nth_lift_interpretation with i (skeleton_interpretation (var v0) ipe) ipf ipe v0 k;
   auto with coc core arith datatypes.
  rewrite lift_ref_lt; auto with coc core arith datatypes.

  unfold skeleton_interpretation in |- *.
  simpl in |- *.
  replace
   (classify_term M (cons (classify_term T0 (classes_of_interpretation ipe)) (classes_of_interpretation ipe))) with
   (typ (type_skeleton (classify_term M (classify_environment (T0 :: e0))))).
  unfold default_cons, interpretation_cons, extend_interpretation_kind in |- *.
  elim
   classify_subst
    with
      (class_of_interpretation_kind i)
      (classes_of_interpretation ipg)
      v
      T0
      k
      (classes_of_interpretation ipf)
      (classes_of_interpretation ipe); auto with coc core arith datatypes.
  generalize H11.
  simpl in |- *.
  generalize (refl_equal (classify_term T0 (classify_environment e0))).
  rewrite H9.
  pattern (classify_term T0 (classify_environment e0)) at 1 in |- *.
  apply class_type_ord with s1; auto with coc core arith datatypes;
   simple induction 1; auto with coc core arith datatypes.
  simpl in |- *.
  rewrite H12.
  replace
   (type_skeleton (classify_term M (cons (classify_term T0 (classify_environment e0)) (classify_environment e0))))
   with (skeleton_interpretation M (cons interp_typ ipe)).
  intros.
  apply H6; auto with coc core arith datatypes.
  simpl in |- *.
  elim H12.
  elim skeleton_sound with e0 T0 (sort_term s1); auto with coc core arith datatypes.
  unfold classes_of_interpretation in |- *; simpl in |- *; elim H9;
   auto with coc core arith datatypes.

  unfold classes_of_interpretation in |- *.
  simpl in |- *.
  red in |- *; intros; apply H13.
  elim H12.
  elim skeleton_sound with e0 T0 (sort_term s1); simpl in |- *;
   auto with coc core arith datatypes.
  elim H9.
  unfold classes_of_interpretation in |- *.
  rewrite H14.
  auto with coc core arith datatypes.

  elim H12.
  elim skeleton_sound with e0 T0 (sort_term s1); simpl in |- *;
   auto with coc core arith datatypes.
  unfold skeleton_interpretation, classes_of_interpretation in |- *; simpl in |- *;
   auto with coc core arith datatypes; elim H9;
   auto with coc core arith datatypes.

  simpl in |- *.
  intros.
  replace
   (type_skeleton
      (classify_term M
         (cons (knd (covariant_skeleton (classify_term T0 (classify_environment e0)))) (classify_environment e0))))
   with (skeleton_interpretation M (cons (interp_knd _ X2) ipe)).
  apply
   eq_can_trans
    with (interpret_type M (cons (interp_knd _ X2) ipe) (skeleton_interpretation M (cons (interp_knd _ X2) ipe)));
   auto with coc core arith datatypes.
  apply H6; auto with coc core arith datatypes.
  unfold classes_of_interpretation in |- *.
  simpl in |- *.
  elim H12.
  elim H9; auto with coc core arith datatypes.

  unfold classes_of_interpretation in |- *.
  simpl in |- *.
  elim H9.
  unfold classes_of_interpretation in |- *.
  red in |- *; intros; apply H13.
  elim H9.
  unfold classes_of_interpretation in |- *.
  rewrite H17; auto with coc core arith datatypes.

  unfold skeleton_interpretation in |- *.
  unfold classes_of_interpretation in |- *.
  simpl in |- *.
  elim H9; auto with coc core arith datatypes.

  apply insert_in_classes with i; auto with coc core arith datatypes.

  exact (skipn_interpretation_classes k ipf ipg H8).

  generalize H11.
  simpl in |- *.
  rewrite H9.
  replace (cons (classify_term T0 (classify_environment e0)) (classify_environment e0)) with
   (classify_environment (T0 :: e0)); auto with coc core arith datatypes.
  elim class_sound with (T0 :: e0) M U (sort_term s2);
   auto with coc core arith datatypes; intros.
  elim H12; auto with coc core arith datatypes.

  elim type_case with e0 u (prod V Ur); intros;
   auto with coc core arith datatypes.
  inversion_clear H10.
  apply inversion_has_type_prod with e0 V Ur (sort_term x); auto with coc core arith datatypes;
   intros.
  unfold skeleton_interpretation in |- *.
  simpl in |- *.
  elim
   classify_subst
    with
      (class_of_interpretation_kind i)
      (classes_of_interpretation ipg)
      v
      u
      k
      (classes_of_interpretation ipf)
      (classes_of_interpretation ipe); auto with coc core arith datatypes.
  cut
   (classify_term u (classes_of_interpretation ipe) = typ (type_skeleton (classify_term u (classes_of_interpretation ipe)))).
  intro.
  rewrite H14.
  elim
   classify_subst
    with
      (class_of_interpretation_kind i)
      (classes_of_interpretation ipg)
      v
      v0
      k
      (classes_of_interpretation ipf)
      (classes_of_interpretation ipe); auto with coc core arith datatypes.
  rewrite H7.
  generalize (refl_equal (classify_term v0 (classify_environment e0))).
  pattern (classify_term v0 (classify_environment e0)) at 1, (classify_term V (classify_environment e0)) in |- *.
  elim class_sound with e0 v0 V (sort_term s1); auto with coc core arith datatypes;
   intros.
  elim H15.
  replace
   (type_skeleton
      match type_skeleton (classify_term u (classify_environment e0)) with
      | prop_skel => typ (type_skeleton (classify_term u (classify_environment e0)))
      | prod_skel _ _ => typ (type_skeleton (classify_term u (classify_environment e0)))
      end) with (skeleton_interpretation u ipe).
  apply H4; auto with coc core arith datatypes.
  rewrite H14.
  discriminate.

  unfold skeleton_interpretation in |- *.
  elim H7.
  case (type_skeleton (classify_term u (classes_of_interpretation ipe)));
   auto with coc core arith datatypes.

  elim H15.
  elim skeleton_sound with e0 u (prod V Ur); auto with coc core arith datatypes.
  cut (classify_term V (classify_environment e0) = knd s); intros.
  cut
   (classify_term Ur (cons (classify_term V (classify_environment e0)) (classify_environment e0)) =
    knd (covariant_skeleton (classify_term Ur (classify_environment (V :: e0)))));
   intros.
  simpl in |- *.
  rewrite H17.
  rewrite H16.
  simpl in |- *.
  generalize (H4 k ipe ipf H5 H6 H7 H8).
  replace (skeleton_interpretation u ipe) with
   (prod_skel s
      (covariant_skeleton
         (classify_term Ur (cons (classify_term V (classify_environment e0)) (classify_environment e0))))).
  simpl in |- *; intros.
  apply H18; auto with coc core arith datatypes.
  rewrite H14.
  discriminate.

  replace s with (skeleton_interpretation v0 ipe).
  apply H2; auto with coc core arith datatypes.
  rewrite H7.
  elim H15.
  discriminate.

  unfold skeleton_interpretation in |- *.
  rewrite H7.
  elim H15; simpl in |- *; auto with coc core arith datatypes.

  apply interpret_equiv_interpret_type.
  apply interpretation_invariant_eq_can.
  apply insert_interpretation_invariant with ipe k i; auto with coc core arith datatypes.

  unfold skeleton_interpretation in |- *.
  rewrite H7.
  elim skeleton_sound with e0 u (prod V Ur); auto with coc core arith datatypes.
  simpl in |- *.
  rewrite H17.
  rewrite H16.
  simpl in |- *; auto with coc core arith datatypes.

  generalize (class_sound e0 u (prod V Ur) H3 (sort_term x) H11).
  simpl in |- *.
  rewrite H16.
  elim H7.
  rewrite H14.
  elim (classify_term Ur (cons (knd s) (classes_of_interpretation ipe))); simpl in |- *; intros;
   auto with coc core arith datatypes.
  inversion_clear H17.

  inversion_clear H17.

  replace s with (covariant_skeleton (classify_term V (classify_environment e0))).
  generalize H15.
  elim class_sound with e0 v0 V (sort_term s1); simpl in |- *;
   auto with coc core arith datatypes; intros.
  inversion_clear H16.

  generalize H15.
  rewrite (skeleton_sound e0 v0 V); auto with coc core arith datatypes.
  elim (classify_term v0 (classify_environment e0)); simpl in |- *; intros.
  discriminate H16.

  injection H16; auto with coc core arith datatypes.

  discriminate H16.

  apply insert_in_classes with i; auto with coc core arith datatypes.

  exact (skipn_interpretation_classes k ipf ipg H6).

  generalize H9.
  rewrite H7.
  simpl in |- *.
  elim class_sound with e0 u (prod V Ur) (sort_term x); simpl in |- *;
   auto with coc core arith datatypes; intros.
  elim H14; auto with coc core arith datatypes.

  apply insert_in_classes with i; auto with coc core arith datatypes.

  exact (skipn_interpretation_classes k ipf ipg H6).

  discriminate H10.

  replace (skeleton_interpretation (prod T0 U) ipe) with prop_skel.
  simpl; fold candidate.
  elim classify_subst
    with (class_of_interpretation_kind i) (classes_of_interpretation ipg) v T0 k
       (classes_of_interpretation ipf) (classes_of_interpretation ipe); auto with coc core arith datatypes.
  apply eq_can_Pi; simpl in |- *; intros; auto with coc core arith datatypes.
  replace eq_candidate with (eq_can prop_skel); auto with coc core arith datatypes.
  replace prop_skel with (skeleton_interpretation T0 ipe).
  apply H2; auto with coc core arith datatypes.
  rewrite H7.
  apply class_type_ord with s1; auto with coc core arith datatypes.
  discriminate.

  discriminate.

  unfold skeleton_interpretation in |- *.
  rewrite H7.
  elim skeleton_sound with e0 T0 (sort_term s1); simpl in |- *;
   auto with coc core arith datatypes.

  replace eq_candidate with (eq_can prop_skel); auto with coc core arith datatypes.
  apply
   eq_can_trans
    with
      (interpret_type U (interpretation_cons T0 ipe (covariant_skeleton (classify_term T0 (classes_of_interpretation ipe))) X2)
         prop_skel); auto with coc core arith datatypes.
  apply interpret_equiv_interpret_type.
  unfold interpretation_cons, extend_interpretation_kind in |- *.
  pattern (classify_term T0 (classes_of_interpretation ipe)) at 1 3 in |- *.
  elim (classify_term T0 (classes_of_interpretation ipe)); auto with coc core arith datatypes.

  apply interpret_equiv_interpret_type.
  unfold interpretation_cons, extend_interpretation_kind in |- *.
  pattern (classify_term T0 (classes_of_interpretation ipe)) at 1 3 in |- *.
  elim (classify_term T0 (classes_of_interpretation ipe)); auto with coc core arith datatypes.

  replace prop_skel with
   (skeleton_interpretation U (interpretation_cons T0 ipe (covariant_skeleton (classify_term T0 (classes_of_interpretation ipe))) X2)).
  apply H4; auto with coc core arith datatypes.
  unfold interpretation_cons, extend_interpretation_kind in |- *.
  elim
   classify_subst
    with
      (class_of_interpretation_kind i)
      (classes_of_interpretation ipg)
      v
      T0
      k
      (classes_of_interpretation ipf)
      (classes_of_interpretation ipe); auto with coc core arith datatypes.
  apply insert_in_classes with i; auto with coc core arith datatypes.

  exact (skipn_interpretation_classes k ipf ipg H6).

  unfold interpretation_cons in |- *; auto with coc core arith datatypes.

  unfold interpretation_cons, extend_interpretation_kind in |- *.
  unfold classes_of_interpretation at 1 in |- *.
  simpl in |- *.
  cut (type_skeleton (classify_term T0 (classify_environment e0)) = prop_skel).
  generalize X2.
  rewrite H7.
  pattern (classify_term T0 (classify_environment e0)) in |- *.
  apply class_type_ord with s1; simpl in |- *;
   auto with coc core arith datatypes.
  intros.
  rewrite H13.
  elim H7; auto with coc core arith datatypes.

  intros.
  elim H7; auto with coc core arith datatypes.

  elim skeleton_sound with e0 T0 (sort_term s1); simpl in |- *;
   auto with coc core arith datatypes.

  unfold interpretation_cons, extend_interpretation_kind in |- *.
  pattern (classify_term T0 (classes_of_interpretation ipe)) at 1 in |- *.
  elim (classify_term T0 (classes_of_interpretation ipe)); auto with coc core arith datatypes.

  replace
   (classes_of_interpretation (interpretation_cons T0 ipe (covariant_skeleton (classify_term T0 (classes_of_interpretation ipe))) X2))
   with (classify_environment (T0 :: e0)).
  apply class_type_ord with s2; auto with coc core arith datatypes.
  discriminate.

  discriminate.

  unfold classes_of_interpretation, interpretation_cons, extend_interpretation_kind in |- *.
  unfold interpretation_cons, extend_interpretation_kind in |- *.
  simpl in |- *.
  rewrite H7.
  cut (type_skeleton (classify_term T0 (classify_environment e0)) = prop_skel).
  generalize X2.
  unfold classes_of_interpretation in |- *.
  replace (map class_of_interpretation_kind ipe) with (classes_of_interpretation ipe);
   auto with coc core arith datatypes.
  rewrite H7.
  pattern (classify_term T0 (classify_environment e0)) in |- *.
  apply class_type_ord with s1; simpl in |- *;
   auto with coc core arith datatypes.
  intros.
  rewrite H13; auto with coc core arith datatypes.

  elim skeleton_sound with e0 T0 (sort_term s1); simpl in |- *;
   auto with coc core arith datatypes.

  unfold skeleton_interpretation in |- *.
  replace
   (classes_of_interpretation (interpretation_cons T0 ipe (covariant_skeleton (classify_term T0 (classes_of_interpretation ipe))) X2))
   with (classify_environment (T0 :: e0)).
  elim skeleton_sound with (T0 :: e0) U (sort_term s2); simpl in |- *;
   auto with coc core arith datatypes.

  unfold interpretation_cons, extend_interpretation_kind in |- *.
  unfold classes_of_interpretation at 1 in |- *.
  simpl in |- *.
  cut (type_skeleton (classify_term T0 (classify_environment e0)) = prop_skel).
  generalize X2.
  rewrite H7.
  pattern (classify_term T0 (classify_environment e0)) in |- *.
  apply class_type_ord with s1; simpl in |- *;
   auto with coc core arith datatypes.
  intros.
  rewrite H13.
  elim H7; auto with coc core arith datatypes.

  intros.
  elim H7; auto with coc core arith datatypes.

  elim skeleton_sound with e0 T0 (sort_term s1); simpl in |- *;
   auto with coc core arith datatypes.

  apply insert_in_classes with i; auto with coc core arith datatypes.

  exact (skipn_interpretation_classes k ipf ipg H6).

  unfold skeleton_interpretation.
  generalize (skeleton_sound (T0 :: e0) U (sort_term s2) H3).
  simpl in |- *.
  rewrite H7.
  elim (classify_term U (cons (classify_term T0 (classify_environment e0)) (classify_environment e0)));
   simpl in |- *; auto with coc core arith datatypes.
  elim (classify_term T0 (classify_environment e0)); simpl in |- *;
   auto with coc core arith datatypes.

  apply H2; auto with coc core arith datatypes.
Qed.


(** Interpretation is compatible with environment extension. *)
Lemma interpretation_cons_equal :
 forall (ip : interpretation_env) (e : environment),
 classes_of_interpretation ip = classify_environment e ->
 forall (N : term) (s1 : sort),
 has_type e N (sort_term s1) ->
 forall C : candidate (covariant_skeleton (classify_term N (classify_environment e))),
 classes_of_interpretation (interpretation_cons N ip _ C) = classify_environment (N :: e).
Proof.
  intros.
  unfold interpretation_cons, extend_interpretation_kind in |- *.
  rewrite H.
  simpl in |- *.
  generalize C.
  pattern (classify_term N (classify_environment e)) in |- *.
  apply class_type_ord with s1; auto with coc core arith datatypes.
  simpl in |- *; intros.
  elim skeleton_sound with e N (sort_term s1); simpl in |- *; intros;
   auto with coc core arith datatypes.
  unfold classes_of_interpretation in |- *; simpl in |- *; elim H;
   auto with coc core arith datatypes.

  unfold classes_of_interpretation in |- *; simpl in |- *; elim H;
   auto with coc core arith datatypes.
Qed.


(** One-step reduction preserves interpretation up to canonical equality. *)
Lemma interpret_type_reduces_once :
 forall U V : term,
 reduces_once U V ->
 forall (e : environment) (K : term),
 has_type e U K ->
 forall ip : interpretation_env,
 classes_of_interpretation ip = classify_environment e ->
 interpretation_invariant ip ->
 classify_term U (classes_of_interpretation ip) <> trm ->
 eq_can (skeleton_interpretation U ip) (interpret_type U ip _) (interpret_type V ip _).
Proof.
  simple induction 1; intros.
  unfold skeleton_interpretation in |- *.
  apply inversion_has_type_app with e (lam T M) N K; intros;
   auto with coc core arith datatypes.
  elim type_case with e (lam T M) (prod V0 Ur); intros;
   auto with coc core arith datatypes.
  inversion_clear H7.
  apply inversion_has_type_prod with e V0 Ur (sort_term x); intros;
   auto with coc core arith datatypes.
  apply inversion_has_type_abs with e T M (prod V0 Ur); intros;
   auto with coc core arith datatypes.
  cut (has_type e N T); intros.
  cut
   (classify_term M (cons (classify_term T (classes_of_interpretation ip)) (classes_of_interpretation ip)) =
    typ (type_skeleton (classify_term M (classify_environment (T :: e))))).
  cut (interpret_var_sound N ip (extend_interpretation_kind T ip _ (interpret_type N ip (skeleton_interpretation N ip)))).
  simpl in |- *; unfold default_cons, interpretation_cons, extend_interpretation_kind in |- *; simpl in |- *;
   rewrite H1.
  cut (classify_term T (classes_of_interpretation ip) = classify_term T (classify_environment e)).
  elim class_sound with e N T (sort_term s0); intros;
   auto with coc core arith datatypes; rewrite H18.
  simpl in |- *.
  replace
   (type_skeleton
      match type_skeleton (classify_term M (cons (typ prop_skel) (classify_environment e))) with
      | prop_skel => typ (type_skeleton (classify_term M (cons (typ prop_skel) (classify_environment e))))
      | _ => typ (type_skeleton (classify_term M (cons (typ prop_skel) (classify_environment e))))
      end) with (skeleton_interpretation M (cons interp_typ ip)).
  unfold subst in |- *.
  apply subst_interpret_type with ip interp_typ (T :: e) T0;
   auto with coc core arith datatypes.
  unfold classes_of_interpretation in |- *.
  simpl in |- *.
  elim H16.
  elim H1; auto with coc core arith datatypes.

  red in |- *; intro; apply H3.
  simpl in |- *.
  replace (cons (classify_term T (classes_of_interpretation ip)) (classes_of_interpretation ip)) with
   (classes_of_interpretation (cons interp_typ ip)).
  rewrite H19; auto with coc core arith datatypes.

  unfold classes_of_interpretation at 1 in |- *.
  simpl in |- *.
  elim H16; auto with coc core arith datatypes.

  unfold skeleton_interpretation in |- *.
  unfold classes_of_interpretation in |- *.
  simpl in |- *.
  elim H1.
  unfold classes_of_interpretation in |- *.
  elim
   (type_skeleton
      (classify_term M (cons (typ prop_skel) (map class_of_interpretation_kind ip))));
   auto with coc core arith datatypes.

  elim H18.
  unfold subst in |- *.
  replace (type_skeleton (classify_term M (cons (knd s) (classify_environment e)))) with
   (skeleton_interpretation M (cons (interp_knd s (interpret_type N ip s)) ip)).
  apply subst_interpret_type with ip (interp_knd s (interpret_type N ip s)) (T :: e) T0;
   auto with coc core arith datatypes.
  apply interp_var_knd.
  generalize H16.
  rewrite H1.
  elim class_sound with e N T (sort_term s0); auto with coc core arith datatypes;
   intros.
  discriminate H19.

  inversion_clear H19; auto with coc core arith datatypes.

  unfold classes_of_interpretation in |- *.
  simpl in |- *.
  elim H1.
  rewrite H16; auto with coc core arith datatypes.

  auto 10 with coc core arith datatypes.

  unfold classes_of_interpretation in |- *.
  simpl in |- *.
  red in |- *; intro; apply H3.
  simpl in |- *.
  rewrite H16.
  unfold classes_of_interpretation in |- *.
  rewrite H19; auto with coc core arith datatypes.

  unfold skeleton_interpretation in |- *.
  unfold classes_of_interpretation in |- *.
  simpl in |- *.
  elim H1; auto with coc core arith datatypes.

  elim H1; auto with coc core arith datatypes.

  unfold extend_interpretation_kind in |- *.
  unfold skeleton_interpretation in |- *.
  generalize (interp_var_typ N ip) (interp_var_knd N ip).
  rewrite H1.
  elim class_sound with e N T (sort_term s0); auto with coc core arith datatypes;
   intros.

  generalize H3.
  simpl in |- *.
  rewrite H1.
  replace (cons (classify_term T (classify_environment e)) (classify_environment e)) with
   (classify_environment (T :: e)); auto with coc core arith datatypes.
  elim class_sound with (T :: e) M T0 (sort_term s3);
   auto with coc core arith datatypes.
  simple induction 1; auto with coc core arith datatypes.

  apply type_conv with V0 s0; auto with coc core arith datatypes.
  apply inversion_convertible_product_left with Ur T0; auto with coc core arith datatypes.

  discriminate H7.

  apply inversion_has_type_abs with e M N K; intros; auto with coc core arith datatypes.
  unfold skeleton_interpretation in |- *.
  rewrite H3.
  simpl in |- *.
  unfold default_cons in |- *.
  replace (cons (classify_term M (classify_environment e)) (classify_environment e)) with
   (classify_environment (M :: e)); auto with coc core arith datatypes.
  elim class_sound with (M :: e) N T (sort_term s2);
   auto with coc core arith datatypes.
  simpl in |- *.
  unfold interpretation_cons in |- *.
  unfold extend_interpretation_kind in |- *.
  rewrite H3.
  elim class_red with e M M' (sort_term s1); auto with coc core arith datatypes.

  unfold interpretation_cons, extend_interpretation_kind in |- *.
  rewrite H3.
  elim class_red with e M M' (sort_term s1); auto with coc core arith datatypes.
  cut (classify_term M (classes_of_interpretation ip) = classify_term M (classify_environment e)).
  elim (classify_term M (classify_environment e)); simpl in |- *; intros;
   auto with coc core arith datatypes.

  elim H3; auto with coc core arith datatypes.

  apply inversion_has_type_abs with e N M K; intros; auto with coc core arith datatypes.
  unfold skeleton_interpretation in |- *.
  simpl in |- *.
  rewrite H3.
  replace (cons (classify_term M (classify_environment e)) (classify_environment e)) with
   (classify_environment (M :: e)); auto with coc core arith datatypes.
  replace (classify_term M (cons (classify_term N (classify_environment e)) (classify_environment e))) with
   (typ (type_skeleton (classify_term M (classify_environment (N :: e))))).
  cut (classify_term N (classes_of_interpretation ip) = classify_term N (classify_environment e)).
  pattern (classify_term N (classify_environment e)) in |- *.
  apply class_type_ord with s1; intros; auto with coc core arith datatypes.
  simpl in |- *.
  replace
   (type_skeleton (classify_term M (cons (classify_term N (classify_environment e)) (classify_environment e))))
   with (skeleton_interpretation M (default_cons N ip)).
  apply H1 with (N :: e) T; auto with coc core arith datatypes.
  unfold default_cons, interpretation_cons, extend_interpretation_kind in |- *.
  simpl in |- *.
  rewrite H3.
  unfold classes_of_interpretation in |- *.
  simpl in |- *.
  pattern (classify_term N (classify_environment e)) in |- *.
  apply class_type_ord with s1; intros; auto with coc core arith datatypes.
  simpl in |- *.
  elim skeleton_sound with e N (sort_term s1); simpl in |- *;
   auto with coc core arith datatypes.
  elim H3; auto with coc core arith datatypes.

  simpl in |- *.
  elim H3; auto with coc core arith datatypes.

  unfold default_cons, interpretation_cons, extend_interpretation_kind in |- *.
  rewrite H3.
  pattern (classify_term N (classify_environment e)) in |- *.
  apply class_type_ord with s1; auto with coc core arith datatypes.

  unfold default_cons in |- *.
  red in |- *; intro; apply H5.
  simpl in |- *.
  replace (cons (classify_term N (classes_of_interpretation ip)) (classes_of_interpretation ip)) with
   (classes_of_interpretation
      (interpretation_cons N ip (covariant_skeleton (classify_term N (classes_of_interpretation ip)))
         (default_can (covariant_skeleton (classify_term N (classes_of_interpretation ip)))))).
  rewrite H11; auto with coc core arith datatypes.

  replace (cons (classify_term N (classes_of_interpretation ip)) (classes_of_interpretation ip)) with
   (classify_environment (N :: e)); auto with coc core arith datatypes.
  rewrite H3.
  apply interpretation_cons_equal with s1; auto with coc core arith datatypes.

  rewrite H3; auto with coc core arith datatypes.

  unfold skeleton_interpretation in |- *.
  replace (classes_of_interpretation (default_cons N ip)) with
   (cons (classify_term N (classify_environment e)) (classify_environment e)).
  auto with coc core arith datatypes.

  symmetry  in |- *.
  unfold default_cons in |- *.
  replace (cons (classify_term N (classify_environment e)) (classify_environment e)) with
   (classify_environment (N :: e)); auto with coc core arith datatypes.
  rewrite H3.
  apply interpretation_cons_equal with s1; auto with coc core arith datatypes.

  simpl in |- *.
  intros.
  replace
   (type_skeleton (classify_term M (cons (classify_term N (classify_environment e)) (classify_environment e))))
   with (skeleton_interpretation M (cons (interp_knd (covariant_skeleton (classify_term N (classify_environment e))) X2) ip)).
  apply
   eq_can_trans
    with (interpret_type M (cons (interp_knd _ X2) ip) (skeleton_interpretation M (cons (interp_knd _ X2) ip)));
   auto with coc core arith datatypes.
  apply H1 with (N :: e) T; auto with coc core arith datatypes.
  elim interpretation_cons_equal with ip e N s1 X2; auto with coc core arith datatypes.
  unfold classes_of_interpretation in |- *.
  simpl in |- *.
  unfold extend_interpretation_kind in |- *.
  rewrite H10; simpl in |- *; auto with coc core arith datatypes.

  unfold classes_of_interpretation in |- *.
  simpl in |- *.
  red in |- *; intros; apply H5.
  simpl in |- *.
  rewrite H10.
  simpl in |- *.
  unfold classes_of_interpretation in |- *.
  rewrite H14; auto with coc core arith datatypes.

  unfold skeleton_interpretation in |- *.
  unfold classes_of_interpretation in |- *.
  simpl in |- *.
  elim H3.
  rewrite H10; auto with coc core arith datatypes.

  elim H3; auto with coc core arith datatypes.

  generalize H5.
  simpl in |- *.
  rewrite H3.
  replace (cons (classify_term N (classify_environment e)) (classify_environment e)) with
   (classify_environment (N :: e)); auto with coc core arith datatypes.
  elim class_sound with (N :: e) M T (sort_term s2); simpl in |- *; intros;
   auto with coc core arith datatypes.
  elim H10; auto with coc core arith datatypes.

  apply inversion_has_type_app with e M1 M2 K; intros; auto with coc core arith datatypes.
  elim type_case with e M1 (prod V0 Ur); intros;
   auto with coc core arith datatypes.
  inversion_clear H9.
  apply inversion_has_type_prod with e V0 Ur (sort_term x); intros;
   auto with coc core arith datatypes.
  unfold skeleton_interpretation in |- *.
  simpl in |- *.
  rewrite H3.
  elim class_red with e M1 N1 (prod V0 Ur); auto with coc core arith datatypes.
  cut (classify_term M1 (classify_environment e) = typ (type_skeleton (classify_term M1 (classify_environment e)))).
  intro.
  rewrite H13.
  cut (classify_term M2 (classes_of_interpretation ip) = classify_term M2 (classify_environment e)).
  elim class_sound with e M2 V0 (sort_term s1); auto with coc core arith datatypes;
   intros.
  replace
   (type_skeleton
      match type_skeleton (classify_term M1 (classify_environment e)) return class with
      | prop_skel => typ (type_skeleton (classify_term M1 (classify_environment e)))
      | prod_skel _ _ => typ (type_skeleton (classify_term M1 (classify_environment e)))
      end) with (skeleton_interpretation M1 ip).
  apply H1 with e (prod V0 Ur); auto with coc core arith datatypes.
  red in |- *; intro; apply H5.
  simpl in |- *.
  rewrite H15; auto with coc core arith datatypes.

  unfold skeleton_interpretation in |- *.
  elim H3.
  elim (type_skeleton (classify_term M1 (classes_of_interpretation ip)));
   auto with coc core arith datatypes.

  generalize (H1 e (prod V0 Ur) H6 ip H3 H4).
  replace (skeleton_interpretation M1 ip) with
   (prod_skel s
      (type_skeleton
         match type_skeleton (classify_term M1 (classify_environment e)) with
         | prop_skel => typ (type_skeleton (classify_term M1 (classify_environment e)))
         | prod_skel _ s2 => typ s2
         end)).
  simpl in |- *; intros.
  apply H15; auto with coc core arith datatypes.
  red in |- *; intro; apply H5.
  simpl in |- *.
  rewrite H16; auto with coc core arith datatypes.

  unfold skeleton_interpretation in |- *.
  rewrite H3.
  elim skeleton_sound with e M1 (prod V0 Ur); auto with coc core arith datatypes.
  simpl in |- *.
  cut (classify_term V0 (classify_environment e) = knd s); intros.
  cut
   (classify_term Ur (cons (classify_term V0 (classify_environment e)) (classify_environment e)) =
    knd (covariant_skeleton (classify_term Ur (classify_environment (V0 :: e)))));
   intros.
  rewrite H16.
  rewrite H15; simpl in |- *; auto with coc core arith datatypes.

  generalize (class_sound e M1 (prod V0 Ur) H6 (sort_term x) H10).
  simpl in |- *.
  rewrite H15.
  rewrite H13.
  elim (classify_term Ur (cons (knd s) (classify_environment e))); intros;
   auto with coc core arith datatypes.
  inversion_clear H16.

  inversion_clear H16.

  generalize H14.
  rewrite H3.
  elim class_sound with e M2 V0 (sort_term s1); intros;
   auto with coc core arith datatypes.
  discriminate H15.

  inversion_clear H15; auto with coc core arith datatypes.

  elim H3; auto with coc core arith datatypes.

  generalize H5.
  simpl in |- *.
  rewrite H3.
  elim class_sound with e M1 (prod V0 Ur) (sort_term x); intros;
   auto with coc core arith datatypes.
  elim H13; auto with coc core arith datatypes.

  discriminate H9.

  cut (classify_term M1 (classes_of_interpretation ip) <> trm); intros.
  apply inversion_has_type_app with e M1 M2 K; intros; auto with coc core arith datatypes.
  elim type_case with e M1 (prod V0 Ur); intros;
   auto with coc core arith datatypes.
  inversion_clear H10.
  apply inversion_has_type_prod with e V0 Ur (sort_term x); intros;
   auto with coc core arith datatypes.
  unfold skeleton_interpretation in |- *.
  simpl in |- *.
  rewrite H3.
  elim class_red with e M2 N2 V0; auto with coc core arith datatypes.
  cut (classify_term M1 (classify_environment e) = typ (type_skeleton (classify_term M1 (classify_environment e)))).
  intro.
  rewrite H14.
  cut (classify_term M2 (classes_of_interpretation ip) = classify_term M2 (classify_environment e)).
  elim class_sound with e M2 V0 (sort_term s1); auto with coc core arith datatypes;
   intros.
  cut
   (eq_can _
      (interpret_type M1 ip
         (prod_skel s
            (type_skeleton
               match type_skeleton (classify_term M1 (classify_environment e)) with
               | prop_skel => typ (type_skeleton (classify_term M1 (classify_environment e)))
               | prod_skel _ s2 => typ s2
               end)))
      (interpret_type M1 ip
         (prod_skel s
            (type_skeleton
               match type_skeleton (classify_term M1 (classify_environment e)) with
               | prop_skel => typ (type_skeleton (classify_term M1 (classify_environment e)))
               | prod_skel _ s2 => typ s2
               end)))).
  simpl in |- *; intros.
  apply H16; auto with coc core arith datatypes.
  replace s with (skeleton_interpretation M2 ip).
  apply H1 with e V0; auto with coc core arith datatypes.
  rewrite H15.
  discriminate.

  unfold skeleton_interpretation in |- *.
  generalize H15.
  rewrite H3.
  elim class_sound with e M2 V0 (sort_term s1); intros;
   auto with coc core arith datatypes.
  discriminate H17.

  inversion_clear H17; auto with coc core arith datatypes.

  auto with coc core arith datatypes.

  elim H3; auto with coc core arith datatypes.

  generalize H6.
  rewrite H3.
  elim class_sound with e M1 (prod V0 Ur) (sort_term x);
   auto with coc core arith datatypes; intros.
  elim H14; auto with coc core arith datatypes.

  discriminate H10.

  red in |- *; intros; apply H5.
  simpl in |- *.
  rewrite H6; auto with coc core arith datatypes.

  apply inversion_has_type_prod with e M1 M2 K; intros; auto with coc core arith datatypes.
  unfold skeleton_interpretation in |- *.
  simpl in |- *.
  rewrite H3.
  elim class_red with e M1 N1 (sort_term s1); auto with coc core arith datatypes.
  replace (cons (classify_term M1 (classify_environment e)) (classify_environment e)) with
   (classify_environment (M1 :: e)); auto with coc core arith datatypes.
  cut (skeleton_interpretation M1 ip = prop_skel); intros.
  pattern (classify_term M2 (classify_environment (M1 :: e))) in |- *.
  apply class_type_ord with s2; auto with coc core arith datatypes.
  elim skeleton_sound with (M1 :: e) M2 (sort_term s2); simpl in |- *;
   auto with coc core arith datatypes.
  apply eq_can_Pi; auto with coc core arith datatypes.
  elim H9.
  apply H1 with e (sort_term s1); auto with coc core arith datatypes.
  rewrite H3.
  apply class_type_ord with s1; auto with coc core arith datatypes.
  discriminate.

  discriminate.

  simpl in |- *; intros.
  unfold interpretation_cons, extend_interpretation_kind in |- *.
  rewrite H3.
  elim class_red with e M1 N1 (sort_term s1); auto with coc core arith datatypes.
  pattern (classify_term M1 (classify_environment e)) at 1 3 in |- *.
  elim (classify_term M1 (classify_environment e)); auto with coc core arith datatypes.
  intros.
  replace eq_candidate with (eq_can prop_skel); auto with coc core arith datatypes.

  pattern (classify_term M1 (classify_environment e)) in |- *.
  apply class_type_ord with s1; auto with coc core arith datatypes.
  simpl in |- *.
  apply eq_can_Pi; auto with coc core arith datatypes.
  elim H9.
  apply H1 with e (sort_term s1); auto with coc core arith datatypes.
  rewrite H3.
  apply class_type_ord with s1; auto with coc core arith datatypes.
  discriminate.

  discriminate.

  simpl in |- *; intros.
  replace eq_candidate with (eq_can prop_skel); auto with coc core arith datatypes.
  apply interpret_equiv_interpret_type.
  unfold interpretation_cons, extend_interpretation_kind in |- *.
  rewrite H3.
  elim class_red with e M1 N1 (sort_term s1); auto with coc core arith datatypes.
  elim (classify_term M1 (classify_environment e)); auto with coc core arith datatypes.

  simpl in |- *.
  apply eq_can_Pi; auto with coc core arith datatypes.
  elim H9.
  apply H1 with e (sort_term s1); auto with coc core arith datatypes.
  rewrite H3.
  apply class_type_ord with s1; auto with coc core arith datatypes.
  discriminate.

  discriminate.

  simpl in |- *; intros.
  change
    (eq_can prop_skel
       (interpret_type M2 (interpretation_cons M1 ip (covariant_skeleton (classify_term M1 (classify_environment e))) X1)
          prop_skel)
       (interpret_type M2 (interpretation_cons N1 ip (covariant_skeleton (classify_term M1 (classify_environment e))) X2)
          prop_skel)) in |- *.
  unfold interpretation_cons, extend_interpretation_kind in |- *.
  rewrite H3.
  elim class_red with e M1 N1 (sort_term s1); auto with coc core arith datatypes.
  pattern (classify_term M1 (classify_environment e)) at 1 3 in |- *.
  elim (classify_term M1 (classify_environment e)); auto with coc core arith datatypes.

  unfold skeleton_interpretation in |- *.
  rewrite H3.
  elim skeleton_sound with e M1 (sort_term s1); simpl in |- *;
   auto with coc core arith datatypes.

  apply inversion_has_type_prod with e M1 M2 K; intros; auto with coc core arith datatypes.
  unfold skeleton_interpretation in |- *.
  simpl in |- *.
  rewrite H3.
  elim class_red with (M1 :: e) M2 N2 (sort_term s2);
   auto with coc core arith datatypes.
  replace (cons (classify_term M1 (classify_environment e)) (classify_environment e)) with
   (classify_environment (M1 :: e)); auto with coc core arith datatypes.
  pattern (classify_term M2 (classify_environment (M1 :: e))) in |- *.
  apply class_type_ord with s2; auto with coc core arith datatypes.
  elim skeleton_sound with (M1 :: e) M2 (sort_term s2); simpl in |- *;
   auto with coc core arith datatypes.
  apply eq_can_Pi; auto with coc core arith datatypes.
  simpl in |- *; intros.
  replace eq_candidate with (eq_can prop_skel); auto with coc core arith datatypes.
  apply
   eq_can_trans
    with
      (interpret_type M2 (interpretation_cons M1 ip (covariant_skeleton (classify_term M1 (classify_environment e))) X2) prop_skel);
   auto with coc core arith datatypes.
  unfold interpretation_cons, extend_interpretation_kind in |- *.
  elim (classify_term M1 (classes_of_interpretation ip)); auto with coc core arith datatypes.

  unfold interpretation_cons, extend_interpretation_kind in |- *.
  elim (classify_term M1 (classes_of_interpretation ip)); auto with coc core arith datatypes.

  replace prop_skel with
   (skeleton_interpretation M2 (interpretation_cons M1 ip (covariant_skeleton (classify_term M1 (classify_environment e))) X2)).
  apply H1 with (M1 :: e) (sort_term s2); auto with coc core arith datatypes.
  apply interpretation_cons_equal with s1; auto with coc core arith datatypes.

  unfold interpretation_cons, extend_interpretation_kind in |- *.
  elim (classify_term M1 (classes_of_interpretation ip)); auto with coc core arith datatypes.

  red in |- *; intros.
  apply H5.
  simpl in |- *.
  replace (cons (classify_term M1 (classes_of_interpretation ip)) (classes_of_interpretation ip)) with
   (classes_of_interpretation (interpretation_cons M1 ip (covariant_skeleton (classify_term M1 (classify_environment e))) X2)).
  rewrite H12; auto with coc core arith datatypes.

  rewrite H3.
  replace (cons (classify_term M1 (classify_environment e)) (classify_environment e)) with
   (classify_environment (M1 :: e)); auto with coc core arith datatypes.
  apply interpretation_cons_equal with s1; auto with coc core arith datatypes.

  unfold skeleton_interpretation in |- *.
  replace (classes_of_interpretation (interpretation_cons M1 ip (covariant_skeleton (classify_term M1 (classify_environment e))) X2))
   with (classify_environment (M1 :: e)).
  elim skeleton_sound with (M1 :: e) M2 (sort_term s2);
   auto with coc core arith datatypes.

  replace (cons (classify_term M1 (classify_environment e)) (classify_environment e)) with
   (classify_environment (M1 :: e)); auto with coc core arith datatypes.
  symmetry  in |- *.
  apply interpretation_cons_equal with s1; auto with coc core arith datatypes.

  cut (classify_term M1 (classes_of_interpretation ip) = classify_term M1 (classify_environment e)).
  pattern (classify_term M1 (classify_environment e)) in |- *.
  apply class_type_ord with s1; auto with coc core arith datatypes.
  simpl in |- *; intros.
  apply eq_can_Pi; auto with coc core arith datatypes.
  simpl in |- *; intros.
  replace eq_candidate with (eq_can prop_skel); auto with coc core arith datatypes.
  apply eq_can_trans with (interpret_type M2 (interpretation_cons M1 ip prop_skel X2) prop_skel);
   auto with coc core arith datatypes.
  unfold interpretation_cons, extend_interpretation_kind in |- *.
  elim (classify_term M1 (classes_of_interpretation ip)); auto with coc core arith datatypes.

  unfold interpretation_cons, extend_interpretation_kind in |- *.
  elim (classify_term M1 (classes_of_interpretation ip)); auto with coc core arith datatypes.

  pattern prop_skel at 1 3 5 in |- *.
  replace prop_skel with (skeleton_interpretation M2 (interpretation_cons M1 ip prop_skel X2)).
  cut (covariant_skeleton (classify_term M1 (classify_environment e)) = prop_skel); intros.
  apply H1 with (M1 :: e) (sort_term s2); auto with coc core arith datatypes.
  generalize X2 H12.
  change
    (forall X2 : candidate prop_skel,
     eq_can prop_skel X2 X2 ->
     classes_of_interpretation (interpretation_cons M1 ip prop_skel X2) = classify_environment (M1 :: e))
   in |- *.
  elim H13.
  intros.
  apply interpretation_cons_equal with s1; auto with coc core arith datatypes.

  unfold interpretation_cons, extend_interpretation_kind in |- *.
  elim (classify_term M1 (classes_of_interpretation ip)); auto with coc core arith datatypes.

  replace (classes_of_interpretation (interpretation_cons M1 ip prop_skel X2)) with (classify_environment (M1 :: e)).
  red in |- *; intros; apply H5.
  simpl in |- *.
  rewrite H3.
  replace (cons (classify_term M1 (classify_environment e)) (classify_environment e)) with
   (classify_environment (M1 :: e)); auto with coc core arith datatypes.
  rewrite H14; auto with coc core arith datatypes.

  generalize X2 H12.
  change
    (forall X2 : candidate prop_skel,
     eq_can prop_skel X2 X2 ->
     classify_environment (M1 :: e) = classes_of_interpretation (interpretation_cons M1 ip prop_skel X2))
   in |- *.
  elim H13.
  intros.
  symmetry  in |- *.
  apply interpretation_cons_equal with s1; auto with coc core arith datatypes.

  elim H3.
  rewrite H9; simpl in |- *; auto with coc core arith datatypes.

  unfold skeleton_interpretation in |- *.
  replace (classes_of_interpretation (interpretation_cons M1 ip prop_skel X2)) with (classify_environment (M1 :: e)).
  elim skeleton_sound with (M1 :: e) M2 (sort_term s2);
   auto with coc core arith datatypes.

  generalize X2 H12.
  change
    (forall X2 : candidate prop_skel,
     eq_can prop_skel X2 X2 ->
     classify_environment (M1 :: e) = classes_of_interpretation (interpretation_cons M1 ip prop_skel X2))
   in |- *.
  replace prop_skel with (covariant_skeleton (classify_term M1 (classify_environment e))).
  intros.
  symmetry  in |- *.
  apply interpretation_cons_equal with s1; auto with coc core arith datatypes.

  elim H3.
  rewrite H9; auto with coc core arith datatypes.

  intros.
  simpl in |- *.
  apply eq_can_Pi; auto with coc core arith datatypes.
  simpl in |- *; intros.
  replace eq_candidate with (eq_can prop_skel); auto with coc core arith datatypes.
  apply
   eq_can_trans
    with
      (interpret_type M2 (interpretation_cons M1 ip (covariant_skeleton (classify_term M1 (classify_environment e))) X2) prop_skel);
   auto with coc core arith datatypes.
  unfold interpretation_cons, extend_interpretation_kind in |- *.
  elim (classify_term M1 (classes_of_interpretation ip)); auto with coc core arith datatypes.

  unfold interpretation_cons, extend_interpretation_kind in |- *.
  elim (classify_term M1 (classes_of_interpretation ip)); auto with coc core arith datatypes.

  replace prop_skel with
   (skeleton_interpretation M2 (interpretation_cons M1 ip (covariant_skeleton (classify_term M1 (classify_environment e))) X2)).
  apply H1 with (M1 :: e) (sort_term s2); auto with coc core arith datatypes.
  apply interpretation_cons_equal with s1; auto with coc core arith datatypes.

  unfold interpretation_cons, extend_interpretation_kind in |- *.
  elim (classify_term M1 (classes_of_interpretation ip)); auto with coc core arith datatypes.

  red in |- *; intros.
  apply H5.
  simpl in |- *.
  replace (cons (classify_term M1 (classes_of_interpretation ip)) (classes_of_interpretation ip)) with
   (classes_of_interpretation (interpretation_cons M1 ip (covariant_skeleton (classify_term M1 (classify_environment e))) X2)).
  rewrite H13; auto with coc core arith datatypes.

  rewrite H3.
  replace (cons (classify_term M1 (classify_environment e)) (classify_environment e)) with
   (classify_environment (M1 :: e)); auto with coc core arith datatypes.
  apply interpretation_cons_equal with s1; auto with coc core arith datatypes.

  unfold skeleton_interpretation in |- *.
  replace (classes_of_interpretation (interpretation_cons M1 ip (covariant_skeleton (classify_term M1 (classify_environment e))) X2))
   with (classify_environment (M1 :: e)).
  elim skeleton_sound with (M1 :: e) M2 (sort_term s2);
   auto with coc core arith datatypes.

  replace (cons (classify_term M1 (classify_environment e)) (classify_environment e)) with
   (classify_environment (M1 :: e)); auto with coc core arith datatypes.
  symmetry  in |- *.
  apply interpretation_cons_equal with s1; auto with coc core arith datatypes.

  elim H3; auto with coc core arith datatypes.
Qed.


(** Multi-step reduction preserves interpretation up to canonical equality. *)
Lemma reduces_interpret_type :
 forall (e : environment) (U K : term),
 has_type e U K ->
 forall ip : interpretation_env,
 classes_of_interpretation ip = classify_environment e ->
 interpretation_invariant ip ->
 classify_term U (classify_environment e) <> trm ->
 forall V : term,
 reduces U V -> eq_can (skeleton_interpretation U ip) (interpret_type U ip _) (interpret_type V ip _).
Proof.
  intros e U K HT ip Hcls Hinv Hcl V Hred.
  induction Hred; auto with coc core arith datatypes.
  apply eq_can_trans with (interpret_type y ip (skeleton_interpretation U ip));
   auto with coc core arith datatypes.
  replace (skeleton_interpretation U ip) with (skeleton_interpretation y ip).
  apply interpret_type_reduces_once with e K; auto with coc core arith datatypes.
  apply subject_reduction_theorem with U; auto with coc core arith datatypes.

  rewrite Hcls.
  elim class_red with e U y K; auto with coc core arith datatypes.

  unfold skeleton_interpretation in |- *.
  rewrite Hcls.
  elim skeleton_sound with e U K; auto with coc core arith datatypes.
  elim skeleton_sound with e y K; auto with coc core arith datatypes.
  apply subject_reduction_theorem with U; auto with coc core arith datatypes.
Qed.


(** Convertible terms have equal interpretations. *)
Lemma convertible_interpret_type :
 forall (e : environment) (U V K : term),
 convertible U V ->
 has_type e U K ->
 has_type e V K ->
 forall ip : interpretation_env,
 classes_of_interpretation ip = classify_environment e ->
 interpretation_invariant ip ->
 classify_term U (classify_environment e) <> trm ->
 eq_can (skeleton_interpretation U ip) (interpret_type U ip _) (interpret_type V ip _).
Proof.
  intros.
  elim church_rosser_theorem with U V; intros; auto with coc core arith datatypes.
  apply eq_can_trans with (interpret_type x ip (skeleton_interpretation U ip));
   auto with coc core arith datatypes.
  apply reduces_interpret_type with e K; auto with coc core arith datatypes.

  apply eq_can_sym.
  replace (skeleton_interpretation U ip) with (skeleton_interpretation V ip).
  apply reduces_interpret_type with e K; auto with coc core arith datatypes.
  rewrite (class_red e V x K); auto with coc core arith datatypes.
  elim class_red with e U x K; auto with coc core arith datatypes.

  unfold skeleton_interpretation in |- *.
  rewrite H2.
  elim skeleton_sound with e U K; auto with coc core arith datatypes.
  elim skeleton_sound with e V K; auto with coc core arith datatypes.
Qed.
