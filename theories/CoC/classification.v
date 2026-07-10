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
From CoC Require Export list_utils.
From CoC Require Import terms.

  (* Kind skeletons *)

  (** Skeleton type classifying kinds by their arity structure. *)
  Inductive skeleton : Type :=
    | prop_skel : skeleton
    | prod_skel : skeleton -> skeleton -> skeleton.

  (** Decidable equality on skeletons. *)
  Lemma skeleton_eq_dec : forall a b : skeleton, {a = b} + {a <> b}.
  Proof.
    induction a as [| s H s0 H0]; simple destruct b; intros.
    left; auto with core.

    right; red in |- *; intros neq; discriminate neq.

    right; red in |- *; intros neq; discriminate neq.

    elim H with s1; [ intro Heq1 | intro Hneq1 ].
    elim Heq1.
    elim H0 with s2; [ intro Heq2 | intro Hneq2 ].
    elim Heq2.
    left; auto with core.

    right; red in |- *; intros; apply Hneq2.
    injection H1; trivial.

    right; red in |- *; intros; apply Hneq1.
    injection H1; trivial.
  Qed.


  (* Classes *)

  (** Classification of terms as term-level, type-level, or kind-level. *)
  Inductive class : Type :=
    | trm : class
    | typ : skeleton -> class
    | knd : skeleton -> class.

  (** Lists of classes, used as class environments. *)
  Definition class_list := list class.


  (** Extract the skeleton from a kind-level class, defaulting to prop_skel. *)
  Definition covariant_skeleton (c : class) : skeleton :=
    match c with
    | knd s => s
    | _ => prop_skel
    end.

  (** Extract the skeleton from a type-level class, defaulting to prop_skel. *)
  Definition type_skeleton (c : class) : skeleton :=
    match c with
    | typ s => s
    | _ => prop_skel
    end.


  (** A function commutes with case analysis on a class value. *)
  Lemma commute_case_skeleton :
   forall (A B : Type) (f : A -> B) (c : class) (bt : A) (bT bK : skeleton -> A),
   f match c with
     | trm => bt
     | typ s => bT s
     | knd s => bK s
     end =
   match c with
   | trm => f bt
   | typ _ => f (bT (type_skeleton c))
   | knd _ => f (bK (covariant_skeleton c))
   end.
  Proof.
    simple destruct c; auto with coc core arith datatypes.
  Qed.


  (** Compute the class of a term in a given class environment. *)
  Fixpoint classify_term (t : term) : class_list -> class :=
    fun i : class_list =>
    match t with
    | sort_term _ => knd prop_skel
    | var n => match nth n i trm with
               | knd s => typ s
               | _ => trm
               end
    | lam A B =>
        let j := cons (classify_term A i) i in
        match classify_term B j, classify_term A i with
        | typ s2, knd s1 => typ (prod_skel s1 s2)
        | typ s, _ => typ s
        | knd _, _ => knd prop_skel
        | trm, _ => trm
        end
    | app u v =>
        match classify_term u i, classify_term v i with
        | typ (prod_skel s1 s2), typ s => typ s2
        | typ s, _ => typ s
        | knd _, _ => knd prop_skel
        | trm, _ => trm
        end
    | prod T U =>
        let j := cons (classify_term T i) i in
        match classify_term U j, classify_term T i with
        | knd s2, knd s1 => knd (prod_skel s1 s2)
        | knd s, _ => knd s
        | typ s, _ => typ s
        | c1, _ => c1
        end
    end.


  (** Compute the class environment corresponding to a typing environment. *)
  Fixpoint classify_environment (e : environment) : class_list :=
    match e with
    | nil => nil
    | t :: f => cons (classify_term t (classify_environment f)) (classify_environment f)
    end.


  (** Looking up a term in the environment agrees with the class environment. *)
  Lemma nth_classify_environment :
   forall (t : term) (e f : environment) (n : nat),
   nth_error e n = Some t ->
   skipn (S n) e = f ->
   classify_term t (classify_environment f) = nth n (classify_environment e) trm.
  Proof.
    intros t e f n Hn Htr. revert t e f Hn Htr.
    induction n as [|n' IHn]; intros t e f Hn Htr.
    - destruct e as [|h e']; simpl in *; [discriminate|].
      injection Hn as <-. subst f. reflexivity.
    - destruct e as [|h e']; simpl in *; [discriminate|].
      apply IHn; auto.
  Qed.


  (** Class computation is stable under lifting. *)
  Lemma classify_term_lift :
   forall (x : class) (t : term) (k : nat) (f g : class_list),
   insert x k f g -> classify_term t f = classify_term (lift_rec 1 t k) g.
  Proof.
    intros x t; induction t; intros;
     auto with coc core arith datatypes.

    simpl.
    elim (le_gt_dec k n); intros.
    rewrite (insert_nth_ge k f g trm x H n a); auto.
    rewrite (insert_nth_lt k f g trm x H n b); auto.

    simpl.
    rewrite (IHt2 (S k) (classify_term t1 f :: f) (classify_term t1 f :: g));
     auto with coc core arith datatypes.
    rewrite (IHt1 k f g H); auto.

    simpl.
    rewrite (IHt1 k f g H).
    rewrite (IHt2 k f g H); auto.

    simpl.
    rewrite (IHt2 (S k) (classify_term t1 f :: f) (classify_term t1 f :: g));
     auto with coc core arith datatypes.
    rewrite (IHt1 k f g H); auto.
  Qed.


  (** Truncating a typing environment yields a truncated class environment. *)
  Lemma classify_environment_skipn :
   forall (k : nat) (e f : environment),
   skipn k e = f -> k <= length e ->
   classify_environment f = skipn k (classify_environment e).
  Proof.
    induction k as [|k' IHk]; intros e f Hf Hlen.
    - simpl in Hf. subst f. simpl. reflexivity.
    - destruct e as [|h e']; simpl in Hlen; [lia|].
      simpl in Hf. subst f. simpl.
      f_equal. apply IHk; [reflexivity | lia].
  Qed.

  Hint Resolve classify_environment_skipn: coc.


  (** Helper: when the lift cutoff is >= list length, classify_term is invariant under lift_rec. *)
  Lemma classify_lift_long_environment : forall (t : term) (n : nat) (e : class_list) (k : nat),
    k >= length e ->
    classify_term (lift_rec n t k) e = classify_term t e.
  Proof.
    induction t as [s | m | t1 IHt1 t2 IHt2 | t1 IHt1 t2 IHt2 | t1 IHt1 t2 IHt2];
      intros n e k Hk; simpl; auto.
    - (* var m *)
      destruct (le_gt_dec k m) as [Hle|Hgt]; simpl; auto.
      (* m >= k >= length e, so nth m e trm = trm and Tnth_def trm e (m+n) = trm *)
      assert (Hm : m >= length e) by lia.
      enough (Heq : nth (n + m) e trm = nth m e trm) by (rewrite Heq; auto).
      rewrite !nth_overflow by lia; auto.
    - (* lam *)
      rewrite (IHt1 n e k Hk).
      rewrite (IHt2 n (cons (classify_term t1 e) e) (S k)); [auto | simpl; lia].
    - (* app *)
      rewrite (IHt1 n e k Hk). rewrite (IHt2 n e k Hk). auto.
    - (* prod *)
      rewrite (IHt1 n e k Hk).
      rewrite (IHt2 n (cons (classify_term t1 e) e) (S k)); [auto | simpl; lia].
  Qed.

  (** Helper: classify_term of a lifted term in an empty env equals classify_term in empty env. *)
  Lemma classify_skipn_nil : forall (t : term) (k : nat),
    classify_term (lift k t) nil = classify_term t nil.
  Proof.
    intros t k.
    unfold lift.
    apply classify_lift_long_environment; simpl; lia.
  Qed.

  (** Class of a lifted term equals the class of the original in a truncated environment. *)
  Lemma classify_skipn :
   forall (n : nat) (e f : class_list),
   f = skipn n e -> forall t : term, classify_term (lift n t) e = classify_term t f.
  Proof.
    induction n as [|k IHk]; intros e f Hf t; subst f.
    - rewrite lift_zero; auto with coc core arith datatypes.
    - destruct e as [|x e0]; simpl.
      + apply (classify_skipn_nil t (S k)).
      + rewrite <- (IHk e0 (skipn k e0) eq_refl t).
        rewrite simplify_lift.
        unfold lift at 1 in |- *.
        simpl in |- *.
        elim classify_term_lift with x (lift k t) 0 e0 (cons x e0);
         auto with coc core arith datatypes.
  Qed.


  (* Loose stability results *)

  (** Loose equality on classes: agrees on constructor, ignores type skeletons. *)
  Inductive loose_eqc : class -> class -> Prop :=
    | loose_eqc_trm : loose_eqc trm trm
    | loose_eqc_typ : forall s1 s2 : skeleton, loose_eqc (typ s1) (typ s2)
    | loose_eqc_knd : forall s : skeleton, loose_eqc (knd s) (knd s).

  Hint Resolve loose_eqc_trm loose_eqc_typ loose_eqc_knd: coc.

  (** Loose class equality is reflexive. *)
  Lemma refl_loose_eq_class : forall c : class, loose_eqc c c.
  Proof.
    simple induction c; auto with coc core arith datatypes.
  Qed.

  Hint Resolve refl_loose_eq_class: coc.

  (** Loose class equality lifts pointwise to class lists. *)
  Lemma refl_loose_eq_class_list : forall c : class_list, Forall2 loose_eqc c c.
  Proof.
    simple induction c; auto with coc core arith datatypes.
  Qed.

  Hint Resolve refl_loose_eq_class_list: coc.


  (** Loose class equality is transitive. *)
  Lemma loose_eq_class_trans :
   forall c1 c2 : class,
   loose_eqc c1 c2 -> forall c3 : class, loose_eqc c2 c3 -> loose_eqc c1 c3.
  Proof.
    simple induction 1; intros; inversion_clear H0;
     auto with coc core arith datatypes.
  Qed.


  (** Adjacency relation between classes: trm < typ < knd. *)
  Inductive adjacent_class : class -> class -> Prop :=
    | adj_trm_typ : forall s : skeleton, adjacent_class trm (typ s)
    | adj_typ_knd : forall s1 s2 : skeleton, adjacent_class (typ s1) (knd s2).

  Hint Resolve adj_trm_typ adj_typ_knd: coc.


  (** Class computation is stable under loose-equal class environments. *)
  Lemma loose_eq_class_stable :
   forall (t : term) (cl1 cl2 : class_list),
   Forall2 loose_eqc cl1 cl2 ->
   loose_eqc (classify_term t cl1) (classify_term t cl2).
  Proof.
    simple induction t; simpl in |- *; intros; auto with coc core arith datatypes.
    generalize n.
    elim H; simpl in |- *; intros; auto with coc core arith datatypes.
    case n0; auto with coc core arith datatypes.
    inversion_clear H0; auto with coc core arith datatypes.

    elim
     H0 with (cons (classify_term t0 cl1) cl1) (cons (classify_term t0 cl2) cl2);
     auto with coc core arith datatypes.
    elim H with cl1 cl2; auto with coc core arith datatypes.

    elim H with cl1 cl2; auto with coc core arith datatypes; intros.
    elim s1; elim s2; elim H0 with cl1 cl2; auto with coc core arith datatypes.

    elim
     H0 with (cons (classify_term t0 cl1) cl1) (cons (classify_term t0 cl2) cl2);
     auto with coc core arith datatypes.
    elim H with cl1 cl2; auto with coc core arith datatypes.
  Qed.

  Hint Resolve loose_eq_class_stable: coc.


  (** Substitution preserves classes up to loose equality. *)
  Lemma classify_term_subst :
   forall (a : class) (G : class_list) (x : term),
   adjacent_class (classify_term x G) a ->
   forall (t : term) (k : nat) (E F : class_list),
   insert a k E F ->
   G = skipn k E -> loose_eqc (classify_term t F) (classify_term (subst_rec x t k) E).
  Proof.
    simple induction t; simpl in |- *; intros; auto with coc core arith datatypes.
    elim (lt_eq_lt_dec k n); simpl in |- *; [ intro Hlt_eq | intro lt ].
    elim Hlt_eq; clear Hlt_eq.
    case n; simpl in |- *; [ intro Hlt | intros n0 Heq ].
    inversion_clear Hlt.

    elim insert_nth_ge with k E F trm a n0; auto with coc core arith datatypes.

    simple induction 1.
    rewrite (insert_nth_eq k E F trm a); auto with coc core arith datatypes.
    apply loose_eq_class_trans with (classify_term x G).
    inversion_clear H; auto with coc core arith datatypes.

    elim classify_skipn with k E G x; auto with coc core arith datatypes.

    elim insert_nth_lt with k E F trm a n; auto with coc core arith datatypes.

    cut (loose_eqc (classify_term t0 F) (classify_term (subst_rec x t0 k) E)); intros;
     auto with coc core arith datatypes.
    cut
     (loose_eqc (classify_term t1 (cons (classify_term t0 F) F))
        (classify_term (subst_rec x t1 (S k))
           (cons (classify_term (subst_rec x t0 k) E) E)));
     intros.
    elim H5; auto with coc core arith datatypes; intros.
    elim H4; auto with coc core arith datatypes.

    apply
     loose_eq_class_trans with (classify_term t1 (cons (classify_term (subst_rec x t0 k) E) F));
     auto with coc core arith datatypes.

    elim H0 with k E F; auto with coc core arith datatypes; intros.
    elim s1; elim s2; elim H1 with k E F; auto with coc core arith datatypes.

    cut (loose_eqc (classify_term t0 F) (classify_term (subst_rec x t0 k) E)); intros;
     auto with coc core arith datatypes.
    cut
     (loose_eqc (classify_term t1 (cons (classify_term t0 F) F))
        (classify_term (subst_rec x t1 (S k))
           (cons (classify_term (subst_rec x t0 k) E) E)));
     intros.
    elim H5; auto with coc core arith datatypes; intros.
    elim H4; auto with coc core arith datatypes.

    apply
     loose_eq_class_trans with (classify_term t1 (cons (classify_term (subst_rec x t0 k) E) F));
     auto with coc core arith datatypes.
  Qed.


  (** A term typed by kind is classified as knd. *)
  Lemma class_kind :
   forall (e : environment) (t T : term),
   has_type e t T ->
   T = sort_term kind ->
   classify_term t (classify_environment e) = knd (covariant_skeleton (classify_term t (classify_environment e))).
  Proof.
    intros e t T Hty.
    induction Hty as
      [ e0 Hwf0
      | e0 Hwf0
      | e0 Hwf0 v t0 Hitem
      | e0 T0 s1 HT IHT M0 U0 s2 HU IHU HM IHM
      | e0 v0 V Hv IHv u0 Ur Hu IHu
      | e0 T0 s1 HT IHT U0 s2 HU IHU
      | e0 t0 U0 V Ht0 IHt0 Hconv s Hs IHs ];
      intros Heq.
    - simpl in |- *; auto with coc core arith datatypes.
    - simpl in |- *; auto with coc core arith datatypes.
    - destruct Hitem as [x0 Heq0 Hnth0].
      destruct (well_formed_sort v e0 (skipn (S v) e0) eq_refl Hwf0 x0 Hnth0) as [x1 Hx1].
      assert (Hkind : x0 = sort_term kind) by
        (assert (Hlift : lift (S v) x0 = sort_term kind) by (rewrite <- Heq0; exact Heq);
         destruct x0; simpl in Hlift; try discriminate; exact Hlift).
      subst x0.
      elim inversion_has_type_kind with (skipn (S v) e0) (sort_term x1); exact Hx1.
    - discriminate Heq.
    - destruct (type_case e0 u0 (prod V Ur) Hu) as [[x Hx] | Hbad]; [| discriminate Hbad].
      apply inversion_has_type_prod with e0 V Ur (sort_term x); auto with coc core arith datatypes;
        intros s1' s2' HV HUr Hcv.
      elim inversion_has_type_kind with e0 (sort_term s2'); auto with coc core arith datatypes.
      rewrite <- Heq.
      replace (sort_term s2') with (subst v0 (sort_term s2')); auto with coc core arith datatypes.
      apply substitution with V; auto with coc core arith datatypes.
    - injection Heq as Heqs2; subst s2.
      simpl in |- *.
      change (classify_environment (T0 :: e0))
        with (classify_term T0 (classify_environment e0) :: classify_environment e0)
        in IHU.
      rewrite (IHU eq_refl).
      elim (classify_term T0 (classify_environment e0)); auto with coc core arith datatypes.
    - elim inversion_has_type_kind with e0 (sort_term s); auto with coc core arith datatypes.
      rewrite <- Heq; exact Hs.
  Qed.


  (** A term whose type is typed by kind is classified as typ. *)
  Lemma class_type :
   forall (e : environment) (t T : term),
   has_type e t T ->
   has_type e T (sort_term kind) ->
   classify_term t (classify_environment e) = typ (type_skeleton (classify_term t (classify_environment e))).
  Proof.
    intros e t T Hty.
    induction Hty as
      [ e0 Hwf0
      | e0 Hwf0
      | e0 Hwf0 v t0 Hitem
      | e0 T0 s1 HT IHT M0 U0 s2 HU IHU HM IHM
      | e0 v0 V Hv IHv u0 Ur Hu IHu
      | e0 T0 s1 HT IHT U0 s2 HU IHU
      | e0 t0 U0 V Ht0 IHt0 Hconv s Hs IHs ];
      intros HtK.
    - elim inversion_has_type_kind with e0 (sort_term kind); auto with coc core arith datatypes.
    - elim inversion_has_type_kind with e0 (sort_term kind); auto with coc core arith datatypes.
    - destruct Hitem as [x0 Heq0 Hnth0].
      simpl in |- *.
      assert (Hvl : v < length e0) by
        (apply (proj1 (nth_error_Some e0 v)); rewrite Hnth0; discriminate).
      elim nth_classify_environment with x0 e0 (skipn (S v) e0) v; auto with coc core arith datatypes.
      elim classify_skipn with (S v) (classify_environment e0) (classify_environment (skipn (S v) e0)) x0;
       [| apply classify_environment_skipn; [reflexivity | lia]].
      elim Heq0.
      rewrite (class_kind e0 t0 (sort_term kind)); auto with coc core arith datatypes.
    - simpl in |- *.
      apply inversion_has_type_prod with e0 T0 U0 (sort_term kind); auto with coc core arith datatypes;
        intros s1' s2' HT1 HU1 Hcv.
      assert (Heqk : s2' = kind) by (apply convertible_sort; auto with coc core arith datatypes).
      subst s2'.
      change (classify_environment (T0 :: e0))
        with (classify_term T0 (classify_environment e0) :: classify_environment e0)
        in IHM.
      rewrite (IHM HU1).
      elim (classify_term T0 (classify_environment e0)); intros; auto with coc core arith datatypes.
    - simpl in |- *.
      destruct (type_case e0 u0 (prod V Ur) Hu) as [[x Hx] | Hbad]; [| discriminate Hbad].
      apply inversion_has_type_prod with e0 V Ur (sort_term x); auto with coc core arith datatypes;
        intros s1' s2' HV HUr Hcvx.
      assert (HsubUr : has_type e0 (subst v0 Ur) (sort_term s2')).
      { replace (sort_term s2') with (subst v0 (sort_term s2'));
          auto with coc core arith datatypes.
        apply substitution with V; auto with coc core arith datatypes. }
      assert (Heqk1 : s2' = kind)
        by (apply convertible_sort; apply (has_type_unique_sort e0 (subst v0 Ur) (sort_term s2') HsubUr); auto with coc core arith datatypes).
      subst s2'.
      assert (Heqx : x = kind) by
        (apply convertible_sort; apply sym_convertible; auto with coc core arith datatypes).
      subst x.
      rewrite (IHu Hx).
      case (type_skeleton (classify_term u0 (classify_environment e0)));
        auto with coc core arith datatypes.
      intros; elim (classify_term v0 (classify_environment e0)); auto with coc core arith datatypes.
    - assert (Hwf' : well_formed (T0 :: e0)) by (apply wf_var with s1; auto with coc core arith datatypes).
      assert (HtK' : has_type (T0 :: e0) (sort_term s2) (sort_term kind)).
      { replace (sort_term s2) with (lift 1 (sort_term s2)); auto with coc core arith datatypes.
        replace (sort_term kind) with (lift 1 (sort_term kind)); auto with coc core arith datatypes.
        apply weakening; auto with coc core arith datatypes. }
      simpl in |- *.
      change (classify_environment (T0 :: e0))
        with (classify_term T0 (classify_environment e0) :: classify_environment e0)
        in IHU.
      rewrite (IHU HtK').
      simpl; auto with coc core arith datatypes.
    - apply IHt0.
      destruct (type_case e0 t0 U0 Ht0) as [[x Hx] | Hbad].
      + assert (Heqxk : x = kind).
        { apply convertible_sort.
          apply (has_type_convertible_convertible e0 U0 (sort_term x) V (sort_term kind) Hx HtK Hconv). }
        rewrite <- Heqxk; auto with coc core arith datatypes.
      + elim inversion_has_type_convertible_kind with e0 V (sort_term kind); auto with coc core arith datatypes.
        rewrite <- Hbad; apply sym_convertible; auto with coc core arith datatypes.
  Qed.


  (** Case analysis on class of a typed term: either typ or knd depending on the sort. *)
  Lemma class_type_ord :
   forall (e : environment) (T : term) (s : sort),
   has_type e T (sort_term s) ->
   forall P : class -> Prop,
   P (typ (type_skeleton (classify_term T (classify_environment e)))) ->
   P (knd (covariant_skeleton (classify_term T (classify_environment e)))) -> P (classify_term T (classify_environment e)).
  Proof.
    simple destruct s; intros.
    rewrite (class_kind e T (sort_term kind)); auto with coc core arith datatypes.

    rewrite (class_type e T (sort_term prop)); auto with coc core arith datatypes.
    apply type_prop.
    apply has_type_well_formed with T (sort_term prop); auto with coc core arith datatypes.

    rewrite (class_type e T (sort_term set)); auto with coc core arith datatypes.
    apply type_set.
    apply has_type_well_formed with T (sort_term set); auto with coc core arith datatypes.
  Qed.


  (** A term inhabiting a proper type is classified as trm. *)
  Lemma class_term :
   forall (e : environment) (t T : term) (s : sort),
   is_prop s -> has_type e t T -> has_type e T (sort_term s) -> classify_term t (classify_environment e) = trm.
  Proof.
    intros e t T s is_p Hty.
    induction Hty as
      [ e0 Hwf0
      | e0 Hwf0
      | e0 Hwf0 v t0 Hitem
      | e0 T0 s1 HT IHT M0 U0 s2 HU IHU HM IHM
      | e0 v0 V Hv IHv u0 Ur Hu IHu
      | e0 T0 s1 HT IHT U0 s2 HU IHU
      | e0 t0 U0 V Ht0 IHt0 Hconv s' Hs IHs ];
      intros HtK.
    - elim inversion_has_type_kind with e0 (sort_term s); auto with coc core arith datatypes.
    - elim inversion_has_type_kind with e0 (sort_term s); auto with coc core arith datatypes.
    - destruct Hitem as [x0 Heq0 Hnth0].
      simpl in |- *.
      assert (Hvl : v < length e0) by
        (apply (proj1 (nth_error_Some e0 v)); rewrite Hnth0; discriminate).
      elim nth_classify_environment with x0 e0 (skipn (S v) e0) v; auto with coc core arith datatypes.
      elim classify_skipn with (S v) (classify_environment e0) (classify_environment (skipn (S v) e0)) x0;
       [| apply classify_environment_skipn; [reflexivity | lia]].
      elim Heq0.
      rewrite (class_type e0 t0 (sort_term s)); auto with coc core arith datatypes.
      apply type_prop_set; auto with coc core arith datatypes.
    - simpl in |- *.
      apply inversion_has_type_prod with e0 T0 U0 (sort_term s); auto with coc core arith datatypes;
        intros s1' s2' HT1 HU1 Hcv.
      assert (Heqk : s2' = s) by (apply convertible_sort; auto with coc core arith datatypes).
      subst s2'.
      change (classify_environment (T0 :: e0))
        with (classify_term T0 (classify_environment e0) :: classify_environment e0)
        in IHM.
      rewrite (IHM HU1).
      elim (classify_term T0 (classify_environment e0)); intros; auto with coc core arith datatypes.
    - simpl in |- *.
      destruct (type_case e0 u0 (prod V Ur) Hu) as [[x Hx] | Hbad]; [| discriminate Hbad].
      apply inversion_has_type_prod with e0 V Ur (sort_term x); auto with coc core arith datatypes;
        intros s1' s2' HV HUr Hcvx.
      assert (HsubUr : has_type e0 (subst v0 Ur) (sort_term s2')).
      { replace (sort_term s2') with (subst v0 (sort_term s2'));
          auto with coc core arith datatypes.
        apply substitution with V; auto with coc core arith datatypes. }
      assert (Heqk1 : s2' = s)
        by (apply convertible_sort; apply (has_type_unique_sort e0 (subst v0 Ur) (sort_term s2') HsubUr); auto with coc core arith datatypes).
      subst s2'.
      assert (Heqx : x = s) by
        (apply convertible_sort; apply sym_convertible; auto with coc core arith datatypes).
      subst x.
      rewrite (IHu Hx).
      elim (classify_term v0 (classify_environment e0)); auto with coc core arith datatypes.
    - assert (Hwf' : well_formed (T0 :: e0)) by (apply wf_var with s1; auto with coc core arith datatypes).
      assert (HtK' : has_type (T0 :: e0) (sort_term s2) (sort_term s)).
      { replace (sort_term s2) with (lift 1 (sort_term s2)); auto with coc core arith datatypes.
        replace (sort_term s) with (lift 1 (sort_term s)); auto with coc core arith datatypes.
        apply weakening; auto with coc core arith datatypes. }
      simpl in |- *.
      change (classify_environment (T0 :: e0))
        with (classify_term T0 (classify_environment e0) :: classify_environment e0)
        in IHU.
      rewrite (IHU HtK').
      simpl; auto with coc core arith datatypes.
    - apply IHt0.
      destruct (type_case e0 t0 U0 Ht0) as [[x Hx] | Hbad].
      + assert (Heqxk : x = s).
        { apply convertible_sort.
          apply (has_type_convertible_convertible e0 U0 (sort_term x) V (sort_term s) Hx HtK Hconv). }
        rewrite <- Heqxk; auto with coc core arith datatypes.
      + elim inversion_has_type_convertible_kind with e0 V (sort_term s); auto with coc core arith datatypes.
        rewrite <- Hbad; apply sym_convertible; auto with coc core arith datatypes.
  Qed.


  (** A well-typed term has adjacent classes with its type. *)
  Lemma classify_term_sound :
   forall (e : environment) (t T : term),
   has_type e t T ->
   forall K : term,
   has_type e T K -> adjacent_class (classify_term t (classify_environment e)) (classify_term T (classify_environment e)).
  Proof.
    intros e t T Hty K HK.
    destruct (type_case e t T Hty) as [[x Hx] | Hbad].
    - generalize Hx; clear Hx; pattern x; apply sort_induction; intros.
      + rewrite (class_kind e T (sort_term kind)); auto with coc core arith datatypes.
        rewrite (class_type e t T); auto with coc core arith datatypes.
      + rewrite (class_type e T (sort_term s)); auto with coc core arith datatypes.
        rewrite (class_term e t T s); auto with coc core arith datatypes.
        apply type_prop_set; trivial.
        apply has_type_well_formed with t T; auto with coc core arith datatypes.
    - elim inversion_has_type_kind with e K; auto with coc core arith datatypes.
      rewrite <- Hbad; auto with coc core arith datatypes.
  Qed.


  (** One-step reduction preserves classes up to loose equality. *)
  Lemma classify_term_reduces_once :
   forall (e : environment) (A T : term),
   has_type e A T ->
   forall B : term,
   reduces_once A B -> loose_eqc (classify_term A (classify_environment e)) (classify_term B (classify_environment e)).
  Proof.
    intros e A T Hty.
    induction Hty as
      [ e0 Hwf0
      | e0 Hwf0
      | e0 Hwf0 v t0 Hitem
      | e0 T0 s1 HT IHT M0 U0 s2 HU IHU HM IHM
      | e0 v0 V Hv IHv u0 Ur Hu IHu
      | e0 T0 s1 HT IHT U0 s2 HU IHU
      | e0 t0 U0 V Ht0 IHt0 Hconv s Hs IHs ];
      intros B Hstep.
    - inversion_clear Hstep.
    - inversion_clear Hstep.
    - inversion_clear Hstep.
    - inversion Hstep as
        [ | T1 T1' HstepT N1 Heq1 Heq2 | M1 M1' HstepM N1 Heq1 Heq2 | | | | ]; subst.
      + (* domain reduces *)
        simpl in |- *.
        assert (Hstable : loose_eqc
                  (classify_term M0 (cons (classify_term T0 (classify_environment e0)) (classify_environment e0)))
                  (classify_term M0 (cons (classify_term T1' (classify_environment e0)) (classify_environment e0)))).
        { apply loose_eq_class_stable.
          constructor; [ apply IHT; auto with coc core arith datatypes | ].
          clear; induction (classify_environment e0); constructor; auto with coc core arith datatypes. }
        destruct
          (classify_term M0 (cons (classify_term T0 (classify_environment e0)) (classify_environment e0)))
          eqn:E1;
        destruct
          (classify_term M0 (cons (classify_term T1' (classify_environment e0)) (classify_environment e0)))
          eqn:E2;
        inversion Hstable; subst; simpl;
        try (destruct (classify_term T0 (classify_environment e0));
             destruct (classify_term T1' (classify_environment e0)));
        auto with coc core arith datatypes.
      + (* body reduces *)
        simpl in |- *.
        replace (cons (classify_term T0 (classify_environment e0)) (classify_environment e0)) with
          (classify_environment (T0 :: e0)); trivial.
        elim (IHM M1' HstepM); intros; auto with coc core arith datatypes.
        elim (classify_term T0 (classify_environment e0)); auto with coc core arith datatypes.
    - inversion Hstep as
        [ M1 N1 T1 Heq1 Heq2
        | | | u1 u1' HstepU M2 Heq1 Heq2 | v1 v1' HstepV M2 Heq1 Heq2 | | ]; subst.
      + (* beta: u0 must be a lambda *)
        destruct (type_case e0 (lam T1 M1) (prod V Ur) Hu) as [[x Hx] | Hbad]; [| discriminate Hbad].
        apply inversion_has_type_prod with e0 V Ur (sort_term x); auto with coc core arith datatypes;
          intros s1' s2' HV HUr Hcv.
        apply inversion_has_type_abs with e0 T1 M1 (prod V Ur); auto with coc core arith datatypes;
          intros s1'' s2'' T1' HT1 HM1 HT1' Hcv2.
        simpl in |- *.
        change (classify_environment (T1 :: e0))
          with (classify_term T1 (classify_environment e0) :: classify_environment e0).
        apply loose_eq_class_trans
          with (classify_term M1 (cons (classify_term T1 (classify_environment e0)) (classify_environment e0))).
        * pose proof (classify_term_sound (T1 :: e0) M1 T1' HM1 (sort_term s2'') HT1') as Hadj.
          change (classify_environment (T1 :: e0))
            with (classify_term T1 (classify_environment e0) :: classify_environment e0)
            in Hadj.
          destruct (classify_term M1 (cons (classify_term T1 (classify_environment e0)) (classify_environment e0)))
            eqn:EM1;
          destruct (classify_term T1' (cons (classify_term T1 (classify_environment e0)) (classify_environment e0)))
            eqn:ET1';
          try (inversion Hadj; fail);
          destruct (classify_term T1 (classify_environment e0)) eqn:ET1;
          simpl;
          match goal with
          | |- context [ match ?s0 with prop_skel => _ | prod_skel _ _ => _ end ] =>
              destruct s0
          | _ => idtac
          end;
          simpl;
          try (destruct (classify_term v0 (classify_environment e0)); constructor);
          auto with coc core arith datatypes.
        * unfold subst in |- *.
          apply classify_term_subst
            with (classify_term T1 (classify_environment e0)) (classify_environment e0);
            auto with coc core arith datatypes.
          apply classify_term_sound with (sort_term s1''); auto with coc core arith datatypes.
          apply type_conv with V s1''; auto with coc core arith datatypes.
          apply sym_convertible.
          apply inversion_convertible_product_left with T1' Ur; auto with coc core arith datatypes.
      + (* function reduces *)
        simpl in |- *.
        elim (IHu u1' HstepU); intros; auto with coc core arith datatypes.
        case s1; case s2; elim (classify_term v0 (classify_environment e0));
          auto with coc core arith datatypes.
      + (* argument reduces *)
        simpl in |- *.
        elim (classify_term u0 (classify_environment e0)); intros; auto with coc core arith datatypes.
        destruct s; auto with coc core arith datatypes.
        elim (IHv v1' HstepV); auto with coc core arith datatypes.
    - inversion Hstep as
        [ | | | | | T1 T1' HstepT U1 Heq1 Heq2 | U1 U1' HstepU T1 Heq1 Heq2 ]; subst.
      + (* domain reduces *)
        simpl in |- *.
        assert (HTrel : loose_eqc
                  (classify_term T0 (classify_environment e0))
                  (classify_term T1' (classify_environment e0)))
          by (apply IHT; auto with coc core arith datatypes).
        assert (Hstable : loose_eqc
                  (classify_term U0 (cons (classify_term T0 (classify_environment e0)) (classify_environment e0)))
                  (classify_term U0 (cons (classify_term T1' (classify_environment e0)) (classify_environment e0)))).
        { apply loose_eq_class_stable.
          constructor; [ exact HTrel | ].
          clear; induction (classify_environment e0); constructor; auto with coc core arith datatypes. }
        destruct (classify_term U0 (cons (classify_term T0 (classify_environment e0)) (classify_environment e0)))
          eqn:EU1;
        destruct (classify_term U0 (cons (classify_term T1' (classify_environment e0)) (classify_environment e0)))
          eqn:EU2;
        destruct (classify_term T0 (classify_environment e0)) eqn:ET1;
        destruct (classify_term T1' (classify_environment e0)) eqn:ET2;
        inversion Hstable; subst; inversion HTrel; subst; simpl; auto with coc core arith datatypes.
      + (* codomain reduces *)
        simpl in |- *.
        replace (cons (classify_term T0 (classify_environment e0)) (classify_environment e0)) with
          (classify_environment (T0 :: e0)); auto with coc core arith datatypes.
        elim (IHU U1' HstepU); auto with coc core arith datatypes.
    - apply IHt0; auto with coc core arith datatypes.
  Qed.


  (** Multi-step reduction preserves classes up to loose equality. *)
  Lemma classify_term_reduces :
   forall T U : term,
   reduces T U ->
   forall (e : environment) (K : term),
   has_type e T K -> loose_eqc (classify_term T (classify_environment e)) (classify_term U (classify_environment e)).
  Proof.
    intros T U H.
    induction H as [ M0 | M0 P0 N0 Hstep0 Hred0 IH0 ]; intros e K Hty.
    - auto with coc core arith datatypes.
    - apply loose_eq_class_trans with (classify_term P0 (classify_environment e)).
      + apply (IH0 e K Hty).
      + apply classify_term_reduces_once with K; auto with coc core arith datatypes.
        apply subject_reduction_theorem with M0; auto with coc core arith datatypes.
  Qed.

  (** Convertible terms have loosely equal classes. *)
  Lemma classify_term_convertible :
   forall (e : environment) (T U K1 K2 : term),
   has_type e T K1 ->
   has_type e U K2 ->
   convertible T U -> loose_eqc (classify_term T (classify_environment e)) (classify_term U (classify_environment e)).
  Proof.
    intros e T U K1 K2 HtyT HtyU Hconv.
    destruct (church_rosser_theorem T U Hconv) as [x Hx1 Hx2].
    apply loose_eq_class_trans with (classify_term x (classify_environment e)).
    - apply classify_term_reduces with K1; auto with coc core arith datatypes.
    - assert (Hloose : loose_eqc (classify_term U (classify_environment e)) (classify_term x (classify_environment e)))
        by (apply classify_term_reduces with K2; auto with coc core arith datatypes).
      destruct Hloose; constructor.
  Qed.


  (** Helper: the skeleton of a lifted env entry equals the skeleton of the var. *)
  Lemma skeleton_var_helper :
   forall (v : nat) (e0 : environment),
   well_formed e0 ->
   forall (x : term),
   nth_error e0 v = Some x ->
   covariant_skeleton (classify_term (lift (S v) x) (classify_environment e0)) =
   type_skeleton (match nth v (classify_environment e0) trm with knd s => typ s | _ => trm end).
  Proof.
    intros v e0 Hwf x Hn.
    assert (Hlen : v < length e0) by
      (apply (proj1 (nth_error_Some e0 v)); rewrite Hn; discriminate).
    assert (Htrunc : classify_environment (skipn (S v) e0) = skipn (S v) (classify_environment e0)) by
      (apply classify_environment_skipn; [reflexivity | lia]).
    rewrite (classify_skipn (S v) (classify_environment e0) (classify_environment (skipn (S v) e0)) Htrunc x).
    rewrite (nth_classify_environment x e0 (skipn (S v) e0) v Hn eq_refl).
    destruct (nth v (classify_environment e0) trm); auto with coc core arith datatypes.
  Qed.

  (** The skeleton of a type equals the skeleton of its inhabitant. *)
  Lemma skeleton_sound :
   forall (e : environment) (t T : term),
   has_type e t T ->
   covariant_skeleton (classify_term T (classify_environment e)) = type_skeleton (classify_term t (classify_environment e)).
  Proof.
    intros e t T Hty.
    induction Hty as
      [ e0 Hwf0
      | e0 Hwf0
      | e0 Hwf0 v t0 Hitem
      | e0 T0 s1 HT IHT M0 U0 s2 HU IHU HM IHM
      | e0 v0 V Hv IHv u0 Ur Hu IHu
      | e0 T0 s1 HT IHT U0 s2 HU IHU
      | e0 t0 U0 V Ht0 IHt0 Hconv s Hs IHs ].
    - auto with coc core arith datatypes.
    - auto with coc core arith datatypes.
    - destruct Hitem as [x Heq Hnth].
      rewrite Heq.
      simpl in |- *.
      apply skeleton_var_helper; auto.
    - simpl in |- *.
      replace (cons (classify_term T0 (classify_environment e0)) (classify_environment e0)) with
       (classify_environment (T0 :: e0)); auto with coc core arith datatypes.
      rewrite
       (commute_case_skeleton _ _ covariant_skeleton)
                             with
                             (bK :=
                               fun s0 =>
                               match classify_term T0 (classify_environment e0) with
                               | trm => knd s0
                               | typ _ => knd s0
                               | knd s3 => knd (prod_skel s3 s0)
                               end).
      rewrite
       (commute_case_skeleton _ _ type_skeleton)
                              with
                              (bT :=
                                fun s0 =>
                                match classify_term T0 (classify_environment e0) with
                                | trm => typ s0
                                | typ _ => typ s0
                                | knd s3 => typ (prod_skel s3 s0)
                                end)
                             (bK := fun s0 : skeleton => knd prop_skel).
      simpl in |- *.
      replace (cons (classify_term T0 (classify_environment e0)) (classify_environment e0)) with
       (classify_environment (T0 :: e0)); auto with coc core arith datatypes.
      pattern (classify_term M0 (classify_environment (T0 :: e0))) at 1,
       (classify_term U0 (classify_environment (T0 :: e0))) at 1 in |- *.
      elim (classify_term_sound (T0 :: e0) M0 U0 HM (sort_term s2) HU); intros;
        auto with coc core arith datatypes.
      rewrite
       (commute_case_skeleton _ _ covariant_skeleton)
                             with
                             (bT :=
                               fun s0 : skeleton =>
                               knd (covariant_skeleton (classify_term U0 (classify_environment (T0 :: e0)))))
                            (bK :=
                              fun s0 =>
                              knd
                                (prod_skel s0
                                   (covariant_skeleton (classify_term U0 (classify_environment (T0 :: e0)))))).
      rewrite
       (commute_case_skeleton _ _ type_skeleton)
                              with
                              (bT :=
                                fun s0 : skeleton =>
                                typ
                                  (type_skeleton (classify_term M0 (classify_environment (T0 :: e0)))))
                             (bK :=
                               fun s0 =>
                               typ
                                 (prod_skel s0
                                    (type_skeleton
                                       (classify_term M0 (classify_environment (T0 :: e0)))))).
      change (classify_environment (T0 :: e0))
        with (classify_term T0 (classify_environment e0) :: classify_environment e0)
        in IHM.
      elim (classify_term T0 (classify_environment e0)); simpl; intros;
        try rewrite IHM; auto with coc core arith datatypes.
    - destruct (type_case e0 u0 (prod V Ur) Hu) as [[x Hx] | Hbad]; [| discriminate Hbad].
      apply inversion_has_type_prod with e0 V Ur (sort_term x); auto with coc core arith datatypes;
        intros s1' s2' HV HUr Hcv.
      unfold subst in |- *.
      generalize IHu.
      cut (adjacent_class (classify_term u0 (classify_environment e0))
             (classify_term (prod V Ur) (classify_environment e0))).
      simpl in |- *.
      elim classify_term_subst with
        (classify_term V (classify_environment e0))
        (classify_environment e0) v0 Ur 0 (classify_environment e0)
        (cons (classify_term V (classify_environment e0)) (classify_environment e0));
        simpl in |- *; auto with coc core arith datatypes.
      + intros Hadj Heq; inversion Hadj.
      + intros sk1 sk2 Hadj Heq; inversion_clear Hadj; auto with coc core arith datatypes.
      + intros sk Hadj Hcov.
        pose proof (classify_term_sound e0 v0 V Hv (sort_term s1') HV) as Hav.
        destruct (classify_term V (classify_environment e0)) eqn:EV;
          destruct (classify_term u0 (classify_environment e0)) eqn:EU;
          destruct (classify_term v0 (classify_environment e0)) eqn:EVv;
          simpl in *; try (inversion Hadj; fail); try (inversion Hav; fail);
          try congruence; auto with coc core arith datatypes.
        { destruct s0; simpl in *; congruence. }
        { rewrite <- Hcov; simpl; auto with coc core arith datatypes. }
      + apply classify_term_sound with (sort_term s1'); auto with coc core arith datatypes.
      + apply classify_term_sound with (sort_term x); auto with coc core arith datatypes.
    - simpl in |- *.
      simpl in IHU.
      simpl in IHT.
      rewrite
       (commute_case_skeleton _ _ type_skeleton)
                              with
                              (bK :=
                                fun s0 =>
                                match classify_term T0 (classify_environment e0) with
                                | trm => knd s0
                                | typ _ => knd s0
                                | knd s3 => knd (prod_skel s3 s0)
                                end).
      simpl in |- *.
      elim IHU.
      elim (classify_term U0 (cons (classify_term T0 (classify_environment e0)) (classify_environment e0)));
        auto with coc core arith datatypes.
      elim (classify_term T0 (classify_environment e0)); auto with coc core arith datatypes.
    - elim IHt0.
      elim classify_term_convertible with e0 U0 V (sort_term s) (sort_term s);
        auto with coc core arith datatypes.
      destruct (type_case e0 t0 U0 Ht0) as [[x Hx] | Hbad].
      + assert (Hxs : x = s).
        { apply convertible_sort.
          exact (has_type_convertible_convertible e0 U0 (sort_term x) V (sort_term s) Hx Hs Hconv). }
        rewrite Hxs in Hx; exact Hx.
      + elim inversion_has_type_convertible_kind with e0 V (sort_term s); auto with coc core arith datatypes.
        rewrite <- Hbad; apply sym_convertible; auto with coc core arith datatypes.
  Qed.


  (* Strict stability results *)

  (** Strict typing relation on classes: trm types to typ, typ types to knd. *)
  Inductive type_class : class -> class -> Prop :=
    | type_class_trm : type_class trm (typ prop_skel)
    | type_class_typ : forall s : skeleton, type_class (typ s) (knd s).

  Hint Resolve type_class_trm type_class_typ: coc.


  (** Substitution preserves classes exactly under strict typing. *)
  Lemma classify_subst :
   forall (a : class) (G : class_list) (x : term),
   type_class (classify_term x G) a ->
   forall (t : term) (k : nat) (E F : class_list),
   insert a k E F ->
   G = skipn k E -> classify_term t F = classify_term (subst_rec x t k) E.
  Proof.
    simple induction t; simpl in |- *; intros; auto with coc core arith datatypes.
    elim (lt_eq_lt_dec k n); simpl in |- *; [ intro Hlt_eq | intro Hlt ].
    elim Hlt_eq; clear Hlt_eq.
    case n; simpl in |- *; [ intro Hlt | intros n0 Heq ].
    inversion_clear Hlt.

    elim insert_nth_ge with k E F trm a n0; auto with coc core arith datatypes.

    simple induction 1.
    rewrite (insert_nth_eq k E F trm a); auto with coc core arith datatypes.
    replace (classify_term (lift k x) E) with (classify_term x G).
    inversion_clear H; auto with coc core arith datatypes.

    symmetry  in |- *.
    apply classify_skipn; auto with coc core arith datatypes.

    elim insert_nth_lt with k E F trm a n; auto with coc core arith datatypes.

    elim H0 with k E F; auto with coc core arith datatypes.
    elim H1 with (S k) (cons (classify_term t0 F) E) (cons (classify_term t0 F) F);
     auto with coc core arith datatypes.

    elim H0 with k E F; auto with coc core arith datatypes.
    elim H1 with k E F; auto with coc core arith datatypes.

    elim H0 with k E F; auto with coc core arith datatypes.
    elim H1 with (S k) (cons (classify_term t0 F) E) (cons (classify_term t0 F) F);
     auto with coc core arith datatypes.
  Qed.


  (** Well-typed terms have strictly adjacent classes with their types. *)
  Lemma class_sound :
   forall (e : environment) (t T : term),
   has_type e t T ->
   forall K : term,
   has_type e T K -> type_class (classify_term t (classify_environment e)) (classify_term T (classify_environment e)).
  Proof.
    intros.
    elim type_case with (1 := H); intros.
    - elim a.
      intro x; elim x using sort_induction; intros.
      + rewrite (class_kind e T (sort_term kind)); trivial.
        rewrite (class_type e t T); trivial.
        elim skeleton_sound with (1 := H); auto with coc.
      + rewrite (class_type e T (sort_term s)); trivial.
        rewrite (class_term e t T s); trivial.
        elim skeleton_sound with (1 := p); simpl in |- *; auto with coc.
        apply type_prop_set; trivial.
        apply has_type_well_formed with t T; auto with coc.
    - elim inversion_has_type_kind with e K.
      elim b; auto with coc core arith datatypes.
  Qed.


  (** Reduction preserves classes exactly. *)
  Lemma class_red :
   forall (e : environment) (T U K : term),
   has_type e T K -> reduces T U -> classify_term T (classify_environment e) = classify_term U (classify_environment e).
  Proof.
    intros.
    cut (type_skeleton (classify_term T (classify_environment e)) = type_skeleton (classify_term U (classify_environment e))).
    elim classify_term_reduces with (1 := H0) (2 := H); simpl in |- *; intros; trivial.
    elim H1; trivial.

    elim skeleton_sound with (1 := H); trivial.
    apply skeleton_sound.
    apply subject_reduction_theorem with (1 := H0) (2 := H).
  Qed.
