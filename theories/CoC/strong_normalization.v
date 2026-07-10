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


From Stdlib Require Import PeanoNat.

From CoC Require Import terms.
From CoC Require Import confluence.
From CoC Require Import typing.
From CoC Require Import classification.
From CoC Require Import candidates.
From CoC Require Import interpretation_term.
From CoC Require Import interpretation_type.
From CoC Require Import interpretation_stability.

Implicit Types i k m n p : nat.
Implicit Type s : sort.
Implicit Types A B M N T t u v : term.
Implicit Types e f g : environment.

(** Predicate stating that a term interpretation matches an environment. *)
Inductive term_in_interpretation : environment -> interpretation_env -> term_interpretation -> Prop :=
  | int_nil : forall itt : term_interpretation, term_in_interpretation nil nil itt
  | int_cs :
      forall e (ip : interpretation_env) (itt : term_interpretation),
      term_in_interpretation e ip itt ->
      forall (y : interpretation_kind) t T,
      interpret_type T ip prop_skel t ->
      term_in_interpretation (T :: e) (cons y ip) (shift_term_interpretation itt t).

  Hint Resolve int_nil int_cs: coc.


  (** Record bundling term_in_interpretation with canonicity and class equality. *)
  Record interpretation_adapted e (ip : interpretation_env) (itt : term_interpretation) : Prop :=
    {adapt_trm_in_int : term_in_interpretation e ip itt;
     int_can_adapt : can_adapt ip;
     adapt_class_equal : classes_of_interpretation ip = classify_environment e}.


  (** Helper for var case of interpretation_sound: each env variable is in its type's candidate. *)
  Lemma var_sound :
   forall e ip it,
   term_in_interpretation e ip it ->
   can_adapt ip ->
   forall n x,
   nth_error e n = Some x ->
   interpret_type (lift (S n) x) ip prop_skel (it n).
  Proof.
    induction 1; intros Hcan n x Hn.
    - destruct n; simpl in Hn; discriminate.
    - destruct n as [|n'].
      + simpl in Hn. injection Hn as <-.
        apply eq_candidate_inclusion with (interpret_type T ip prop_skel).
        * exact (lift_interpret_type y T 0 ip (y :: ip) (insert_head y ip)
                   (adapt_interpretation_invariant _ Hcan) prop_skel).
        * simpl; exact H0.
      + simpl in Hn.
        apply eq_candidate_inclusion with (interpret_type (lift (S n') x) ip prop_skel).
        * rewrite (simplify_lift x (S n')).
          exact (lift_interpret_type y (lift (S n') x) 0 ip (y :: ip) (insert_head y ip)
                   (adapt_interpretation_invariant _ Hcan) prop_skel).
        * apply IHterm_in_interpretation.
          -- apply Forall_inv_tail in Hcan; exact Hcan.
          -- exact Hn.
  Qed.

  (** Soundness of the interpretation: well-typed terms inhabit their type's candidate. *)
  Lemma interpretation_sound :
   forall e t T,
   has_type e t T ->
   forall (ip : interpretation_env) (it : term_interpretation),
   interpretation_adapted e ip it -> interpret_type T ip prop_skel (interpret_term t it 0).
  Proof.
    simple induction 1; simpl in |- *; intros.
    red in |- *; apply Acc_intro; intros y Hstep.
    unfold transp, reduces_once_prop in Hstep; destruct Hstep as [Hstep]; inversion Hstep.

    red in |- *; apply Acc_intro; intros y Hstep.
    unfold transp, reduces_once_prop in Hstep; destruct Hstep as [Hstep]; inversion Hstep.

    elim (le_gt_dec 0 v); [ intro Hle | intro Hgt ].
    rewrite lift_zero.
    rewrite Nat.sub_0_r.
    match goal with H : item_lift _ _ _ |- _ =>
      elim H; intros x H3 H4; rewrite H3 end.
    match goal with H : interpretation_adapted _ _ _ |- _ =>
      exact (var_sound e0 ip it (adapt_trm_in_int e0 ip it H) (int_can_adapt e0 ip it H) v x H4) end.

    inversion_clear Hgt.

    match goal with H : interpretation_adapted _ _ _ |- _ =>
      destruct H as [in_interp ip_can_adapted same_classes] end.
    apply (Abs_sound
      (interpret_type T0 ip prop_skel)
      (covariant_skeleton (classify_term T0 (classes_of_interpretation ip)))
      (fun C => interpret_type U (interpretation_cons T0 ip (covariant_skeleton (classify_term T0 (classes_of_interpretation ip))) C) prop_skel)
      (interpret_term T0 it 0)
      (interpret_term M it 1)).
    { (* is_can prop_skel (interpret_type T0 ip prop_skel) *)
      exact (interpret_type_cr T0 ip ip_can_adapted prop_skel). }
    { (* is_can (prod_skel s prop_skel) F *)
      intro X; intro HX_can; intro HX_eq.
      change
        (is_can prop_skel
           (interpret_type U (interpretation_cons T0 ip (covariant_skeleton (classify_term T0 (classes_of_interpretation ip))) X)
              prop_skel)) in |- *.
      apply interpret_type_cr.
      unfold interpretation_cons, extend_interpretation_kind in |- *.
      set (c := classify_term T0 (classes_of_interpretation ip)) in *.
      generalize dependent X.
      elim c; auto with coc core arith datatypes. }
    { (* body *)
      intro n; intro Hn; intro C; intro HC; intro HCeq.
      unfold subst in |- *.
      rewrite interpret_term_subst; auto with coc core arith datatypes.
      apply H2.
      unfold interpretation_cons, extend_interpretation_kind in |- *.
      apply Build_interpretation_adapted; auto with coc core arith datatypes.
      { (* can_adapt *)
        generalize dependent C.
        elim (classify_term T0 (classes_of_interpretation ip)); auto with coc core arith datatypes. }
      { (* classes_of_interpretation *)
        simpl in |- *.
        pattern (classes_of_interpretation ip) at 1 in |- *.
        rewrite same_classes.
        unfold classes_of_interpretation in |- *.
        pattern (classify_term T0 (classify_environment e0)) in |- *.
        apply class_type_ord with s1; elim same_classes; simpl in |- *;
         auto with coc core arith datatypes.
        rewrite same_classes.
        elim skeleton_sound with e0 T0 (sort_term s1); simpl in |- *;
         auto with coc core arith datatypes.
        elim same_classes; auto with coc core arith datatypes. } }
    { (* strongly_normalizing *)
      exact (H0 ip it (Build_interpretation_adapted e0 ip it in_interp ip_can_adapted same_classes)). }

    match goal with H : interpretation_adapted _ _ _ |- _ =>
      destruct H as [in_interp ip_can_adapted same_classes] end.
    destruct (type_case e0 u (prod V Ur) h0) as [[x Hpr]|Hpr];
     auto with coc core arith datatypes.
    apply inversion_has_type_prod with e0 V Ur (sort_term x); auto with coc core arith datatypes;
     intros.
    apply
     eq_candidate_inclusion
      with
        (interpret_type Ur
           (interpretation_cons V ip (covariant_skeleton (classify_term V (classes_of_interpretation ip))) (interpret_type v ip _))
           prop_skel).
    replace prop_skel with
     (skeleton_interpretation Ur
        (interpretation_cons V ip (covariant_skeleton (classify_term V (classes_of_interpretation ip)))
           (interpret_type v ip (covariant_skeleton (classify_term V (classes_of_interpretation ip)))))).
    unfold subst, interpretation_cons in |- *.
    apply
     subst_interpret_type
      with
        ip
        (extend_interpretation_kind V ip (covariant_skeleton (classify_term V (classes_of_interpretation ip)))
           (interpret_type v ip (covariant_skeleton (classify_term V (classes_of_interpretation ip)))))
        (V :: e0)
        (sort_term s2); auto with coc core arith datatypes.
    unfold extend_interpretation_kind in |- *.
    rewrite same_classes.
    cut (classify_term v (classes_of_interpretation ip) = classify_term v (classify_environment e0)).
    elim class_sound with e0 v V (sort_term s1); intros;
     auto with coc core arith datatypes.

    elim same_classes; auto with coc core arith datatypes.

    simpl in |- *.
    unfold extend_interpretation_kind in |- *.
    rewrite same_classes.
    unfold classes_of_interpretation in |- *.
    apply class_type_ord with s1; elim same_classes; simpl in |- *;
     auto with coc core arith datatypes.
    rewrite same_classes.
    elim skeleton_sound with e0 V (sort_term s1); simpl in |- *;
     auto with coc core arith datatypes.
    elim same_classes; auto with coc core arith datatypes.

    unfold extend_interpretation_kind in |- *.
    red in |- *; red in |- *; auto with coc core arith datatypes.
    apply Forall2_cons; auto with coc core arith datatypes.
    elim (classify_term V (classes_of_interpretation ip)); auto with coc core arith datatypes.

    change (interpretation_invariant ip) in |- *.
    apply adapt_interpretation_invariant; auto with coc core arith datatypes.

    replace
     (classes_of_interpretation
        (cons
           (extend_interpretation_kind V ip (covariant_skeleton (classify_term V (classes_of_interpretation ip)))
              (interpret_type v ip (covariant_skeleton (classify_term V (classes_of_interpretation ip))))) ip)) with
     (classify_environment (V :: e0)).
    apply class_type_ord with s2; auto with coc core arith datatypes.
    discriminate.

    discriminate.

    simpl in |- *.
    unfold extend_interpretation_kind in |- *.
    rewrite same_classes.
    pattern (classify_term V (classify_environment e0)) in |- *.
    apply class_type_ord with s1; elim same_classes; simpl in |- *;
     auto with coc core arith datatypes.
    rewrite same_classes.
    elim skeleton_sound with e0 V (sort_term s1); simpl in |- *;
     auto with coc core arith datatypes.
    elim same_classes; auto with coc core arith datatypes.

    unfold interpretation_cons, skeleton_interpretation in |- *.
    replace
     (classes_of_interpretation
        (cons
           (extend_interpretation_kind V ip _ (interpret_type v ip (covariant_skeleton (classify_term V (classes_of_interpretation ip)))))
           ip)) with (classify_environment (V :: e0)).
    elim skeleton_sound with (V :: e0) Ur (sort_term s2); simpl in |- *;
     auto with coc core arith datatypes.

    simpl in |- *.
    unfold extend_interpretation_kind in |- *.
    rewrite same_classes.
    unfold classes_of_interpretation in |- *.
    elim class_sound with e0 v V (sort_term s1); auto with coc core arith datatypes.
    simpl in |- *.
    elim same_classes; auto with coc core arith datatypes.

    simpl in |- *.
    elim same_classes; auto with coc core arith datatypes.

    generalize (H1 ip it (Build_interpretation_adapted e0 ip it in_interp ip_can_adapted same_classes)).
    simpl in |- *; unfold Pi in |- *; intro HPi.
    apply HPi.
    { exact (H0 ip it (Build_interpretation_adapted e0 ip it in_interp ip_can_adapted same_classes)). }
    { apply interpret_type_cr; auto with coc core arith datatypes. }
    { auto with coc core arith datatypes. }

    match goal with H : prod _ _ = sort_term kind |- _ => discriminate H end.

    apply strongly_normalizing_product.
    apply H0 with ip; auto with coc core arith datatypes.

    apply strongly_normalizing_subst with (var 0).
    unfold subst in |- *.
    rewrite interpret_term_subst.
    match goal with H : interpretation_adapted _ _ _ |- _ =>
      destruct H as [in_interp ip_can_adapted same_classes] end.
    apply H1 with (default_cons T0 ip).
    unfold default_cons, interpretation_cons in |- *.
    apply Build_interpretation_adapted.
    apply int_cs; auto with coc core arith datatypes.
    apply (var_in_candidate 0 (interpret_type T0 ip prop_skel));
     auto with coc core arith datatypes.
    exact (interpret_type_cr T0 ip ip_can_adapted prop_skel).

    red in |- *.
    constructor; auto with coc core arith datatypes.
    unfold extend_interpretation_kind in |- *.
    elim (classify_term T0 (classes_of_interpretation ip)); auto with coc core arith datatypes.

    unfold extend_interpretation_kind in |- *.
    rewrite same_classes.
    unfold classes_of_interpretation in |- *.
    simpl in |- *.
    pattern (classify_term T0 (classify_environment e0)) in |- *.
    apply class_type_ord with s1; simpl in |- *; elim same_classes;
     auto with coc core arith datatypes.
    rewrite same_classes.
    elim skeleton_sound with e0 T0 (sort_term s1); simpl in |- *;
     auto with coc core arith datatypes.
    elim same_classes; auto with coc core arith datatypes.

    cut (has_type e0 U (sort_term s)); auto with coc core arith datatypes.
    intros.
    apply eq_candidate_inclusion with (interpret_type U ip prop_skel);
     auto with coc core arith datatypes.
    replace prop_skel with (skeleton_interpretation U ip).
    match goal with H : interpretation_adapted _ _ _ |- _ =>
      destruct H as [in_interp ip_can_adapted same_classes] end.
    apply convertible_interpret_type with e0 (sort_term s); auto with coc core arith datatypes.
    apply class_type_ord with s; auto with coc core arith datatypes.
    discriminate.

    discriminate.

    unfold skeleton_interpretation in |- *.
    match goal with H : interpretation_adapted _ _ _ |- _ =>
      destruct H as [in_interp ip_can_adapted same_classes] end.
    rewrite same_classes.
    elim skeleton_sound with e0 U (sort_term s); simpl in |- *;
     auto with coc core arith datatypes.

    destruct (type_case e0 t0 U h) as [[x H6]|H6]; auto with coc core arith datatypes.
    elim convertible_sort with x s; auto with coc core arith datatypes.
    apply has_type_convertible_convertible with e0 U V; auto with coc core arith datatypes.

    elim inversion_has_type_convertible_kind with e0 V (sort_term s); auto with coc core arith datatypes.
    elim H6; auto with coc core arith datatypes.
  Qed.


  (** Default interpretation of types in an environment. *)
  Fixpoint default_interpretation e : interpretation_env :=
    match e with
    | nil => nil
    | t :: f => default_cons t (default_interpretation f)
    end.


  (** Default term interpretation mapping variables to themselves. *)
  Fixpoint default_term_interpretation e : nat -> term_interpretation :=
    fun k =>
    match e with
    | nil => fun p => var (k + p)
    | _ :: f => shift_term_interpretation (default_term_interpretation f (S k)) (var k)
    end.


  (** The default type interpretation satisfies canonicity. *)
  Lemma default_interpretation_can : forall e, can_adapt (default_interpretation e).
  Proof.
    simple induction e; simpl in |- *; auto with coc core arith datatypes; intros.
    unfold default_cons, interpretation_cons, extend_interpretation_kind in |- *.
    elim (classify_term a (classes_of_interpretation (default_interpretation l)));
     auto with coc core arith datatypes.
  Qed.


  (** The default interpretations form a valid interpretation_adapted for well-formed environments. *)
  Lemma default_adapted :
   forall e, well_formed e -> forall k, interpretation_adapted e (default_interpretation e) (default_term_interpretation e k).
  Proof.
    simple induction e; simpl in |- *; intros.
    apply Build_interpretation_adapted; auto with coc core arith datatypes.

    inversion_clear H0.
    cut (well_formed l); intros.
    destruct (H ltac:(trivial) (S k)) as [in_interp ip_can_adapted same_classes].
    unfold default_cons, interpretation_cons in |- *.
    apply Build_interpretation_adapted; auto with coc core arith datatypes.
    apply int_cs; auto with coc core arith datatypes.
    apply (var_in_candidate k (interpret_type a (default_interpretation l) prop_skel));
     auto with coc core arith datatypes.
    change (is_can prop_skel (interpret_type a (default_interpretation l) prop_skel)) in |- *.
    apply interpret_type_cr; auto with coc core arith datatypes.

    unfold extend_interpretation_kind in |- *.
    rewrite same_classes.
    pattern (classify_term a (classify_environment l)) in |- *.
    apply class_type_ord with s; auto with coc core arith datatypes.

    simpl in |- *.
    unfold extend_interpretation_kind in |- *.
    rewrite same_classes.
    pattern (classify_term a (classify_environment l)) in |- *.
    apply class_type_ord with s; unfold classes_of_interpretation in |- *; elim same_classes;
     auto with coc core arith datatypes.
    simpl in |- *.
    rewrite same_classes.
    elim skeleton_sound with l a (sort_term s); auto with coc core arith datatypes.
    simpl in |- *; auto with coc core arith datatypes.

    apply has_type_well_formed with a (sort_term s); auto with coc core arith datatypes.
  Qed.

  Hint Resolve default_interpretation_can default_adapted: coc.


  (** The default term interpretation acts as the identity on variable indices. *)
  Lemma default_term_interpretation_id : forall n e k, default_term_interpretation e k n = var (k + n).
  Proof.
    simple induction n; simple destruct e; simpl in |- *;
     auto with coc core arith datatypes; intros.
    replace (k + 0) with k; auto with coc core arith datatypes.

    rewrite H.
    replace (k + S n0) with (S (k + n0)); auto with coc core arith datatypes.
  Qed.


  (** Interpreting a term with the default interpretation yields the term itself. *)
  Lemma id_interpret_term : forall e t k, interpret_term t (default_term_interpretation e 0) k = t.
  Proof.
    simple induction t; simpl in |- *; intros; auto with coc core arith datatypes.
    elim (le_gt_dec k n); intros; auto with coc core arith datatypes.
    rewrite default_term_interpretation_id.
    simpl in |- *; unfold lift in |- *.
    rewrite lift_ref_ge; auto with coc core arith datatypes.


    rewrite H; rewrite H0; auto with coc core arith datatypes.

    rewrite H; rewrite H0; auto with coc core arith datatypes.

    rewrite H; rewrite H0; auto with coc core arith datatypes.
  Qed.


  (** Strong normalization: every well-typed term is strongly normalizing. *)
  Theorem strong_normalization : forall e t T, has_type e t T -> strongly_normalizing t.
  Proof.
    intros.
    cut (is_can prop_skel (interpret_type T (default_interpretation e) prop_skel));
     auto with coc core arith datatypes.
    simpl in |- *; intros.
    cut (interpret_type T (default_interpretation e) prop_skel t).
    elim H0; auto with coc core arith datatypes.

    elim id_interpret_term with e t 0.
    apply interpretation_sound with e; auto with coc core arith datatypes.
    apply default_adapted.
    apply has_type_well_formed with t T; auto with coc core arith datatypes.

    apply interpret_type_cr; auto with coc core arith datatypes.
  Qed.


  (** The type of a well-typed term is also strongly normalizing. *)
  Lemma type_strongly_normalizing : forall e t T, has_type e t T -> strongly_normalizing T.
  Proof.
    intros.
    destruct (type_case e t T H) as [[x Hs]|Hkind]; auto with coc core arith datatypes.
    apply strong_normalization with e (sort_term x); auto with coc core arith datatypes.

    rewrite Hkind.
    red in |- *; apply Acc_intro; intros y Hstep.
    unfold transp, reduces_once_prop in Hstep; destruct Hstep as [Hstep]; inversion Hstep.
  Qed.
