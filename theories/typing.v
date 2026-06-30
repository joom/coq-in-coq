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
From CoqInCoq Require Export list_utils.
From CoqInCoq Require Import terms.

Implicit Types i k m n p : nat.
Implicit Type s : sort.
Implicit Types A B M N T t u v : term.

  (** Typing environments as lists of terms. *)
  Definition environment := list term.

  Implicit Types e f g : environment.

  (** A term in the environment at position n, lifted to the current context. *)
  Definition item_lift t e n :=
    ex2 (fun u => t = lift (S n) u) (fun u => nth_error (e:list term) n = Some u).


Section Typage.

  (** Mutually inductive well-formedness and typing judgments for CoC. *)
  Inductive well_formed : environment -> Prop :=
    | wf_nil : well_formed nil
    | wf_var : forall e T s, has_type e T (sort_term s) -> well_formed (T :: e)
  with has_type : environment -> term -> term -> Prop :=
    | type_prop : forall e, well_formed e -> has_type e (sort_term prop) (sort_term kind)
    | type_set : forall e, well_formed e -> has_type e (sort_term set) (sort_term kind)
    | type_var :
        forall e,
        well_formed e -> forall (v : nat) t, item_lift t e v -> has_type e (var v) t
    | type_abs :
        forall e T s1,
        has_type e T (sort_term s1) ->
        forall M (U : term) s2,
        has_type (T :: e) U (sort_term s2) ->
        has_type (T :: e) M U -> has_type e (lam T M) (prod T U)
    | type_app :
        forall e v (V : term),
        has_type e v V ->
        forall u (Ur : term),
        has_type e u (prod V Ur) -> has_type e (app u v) (subst v Ur)
    | type_prod :
        forall e T s1,
        has_type e T (sort_term s1) ->
        forall (U : term) s2,
        has_type (T :: e) U (sort_term s2) -> has_type e (prod T U) (sort_term s2)
    | type_conv :
        forall e t (U V : term),
        has_type e t U -> convertible U V -> forall s, has_type e V (sort_term s) -> has_type e t V.

  Hint Resolve wf_nil type_prop type_set type_var: coc.


  (** Prop and Set both have type Kind. *)
  Lemma type_prop_set :
   forall s, is_prop s -> forall e, well_formed e -> has_type e (sort_term s) (sort_term kind).
  Proof.
    simple destruct 1; intros; rewrite H0.
    apply type_prop; trivial.
    apply type_set; trivial.
  Qed.

  (** A well-typed term has all de Bruijn indices within bounds. *)
  Lemma has_type_free_db_below : forall e t T, has_type e t T -> free_db_below (length e) t.
  Proof.
    simple induction 1; intros; auto with coc core arith datatypes.
    elim H1; intros x H2 H3.
    apply db_var.
    enough (v < length e0) by lia.
    apply (proj1 (nth_error_Some e0 v)); rewrite H3; discriminate.
  Qed.


  (** A typable term lives in a well-formed environment. *)
  Lemma has_type_well_formed : forall e t T, has_type e t T -> well_formed e.
  Proof.
    simple induction 1; auto with coc core arith datatypes.
  Qed.


  (** Every item in a well-formed environment is typable by some sort. *)
  Lemma well_formed_sort :
   forall n e f,
   skipn (S n) e = f ->
   well_formed e -> forall t, nth_error e n = Some t -> exists s : sort, has_type f t (sort_term s).
  Proof.
    induction n as [|n IHn]; intros e f Htr Hwf t Ht.
    - destruct e as [|T l]; simpl in *; [discriminate|].
      injection Ht as <-. subst f.
      inversion_clear Hwf.
      exists s; auto with coc core arith datatypes.
    - destruct e as [|T l]; simpl in *; [discriminate|].
      inversion_clear Hwf.
      apply IHn with l; auto with coc core arith datatypes.
      apply has_type_well_formed with T (sort_term s); auto with coc core arith datatypes.
  Qed.


  (** Inversion principle: extract typing information from a term's shape. *)
  Definition inversion_type (P : Prop) e t T : Prop :=
    match t with
    | sort_term prop => convertible T (sort_term kind) -> P
    | sort_term set => convertible T (sort_term kind) -> P
    | sort_term kind => True
    | var n => forall x : term, nth_error e n = Some x -> convertible T (lift (S n) x) -> P
    | lam A M =>
        forall s1 s2 (U : term),
        has_type e A (sort_term s1) ->
        has_type (A :: e) M U -> has_type (A :: e) U (sort_term s2) -> convertible T (prod A U) -> P
    | app u v =>
        forall Ur V : term,
        has_type e v V -> has_type e u (prod V Ur) -> convertible T (subst v Ur) -> P
    | prod A B =>
        forall s1 s2,
        has_type e A (sort_term s1) -> has_type (A :: e) B (sort_term s2) -> convertible T (sort_term s2) -> P
    end.

  (** inversion_type is stable under convertible types. *)
  Lemma inversion_type_convertible :
   forall (P : Prop) e t (U V : term),
   convertible U V -> inversion_type P e t U -> inversion_type P e t V.
  Proof.
    do 6 intro.
    cut (forall x : term, convertible V x -> convertible U x).
    intro.
    case t; simpl in |- *; intros.
    generalize H1.
    elim s; auto with coc core arith datatypes; intros.

    apply H1 with x; auto with coc core arith datatypes.

    apply H1 with s1 s2 U0; auto with coc core arith datatypes.

    apply H1 with Ur V0; auto with coc core arith datatypes.

    apply H1 with s1 s2; auto with coc core arith datatypes.

    intros.
    apply trans_convertible_convertible with V; auto with coc core arith datatypes.
  Qed.


  (** Typing can be inverted according to the shape of the term. *)
  Theorem has_type_inversion :
   forall (P : Prop) e t T, has_type e t T -> inversion_type P e t T -> P.
  Proof.
    simple induction 1; simpl in |- *; intros.
    auto with coc core arith datatypes.

    auto with coc core arith datatypes.

    elim H1; intros.
    apply H2 with x; auto with coc core arith datatypes.
    rewrite H3; auto with coc core arith datatypes.

    apply H6 with s1 s2 U; auto with coc core arith datatypes.

    apply H4 with Ur V; auto with coc core arith datatypes.

    apply H4 with s1 s2; auto with coc core arith datatypes.

    apply H1.
    apply inversion_type_convertible with V; auto with coc core arith datatypes.
  Qed.


  (** Kind is not typable. *)
  Lemma inversion_has_type_kind : forall e t, ~ has_type e (sort_term kind) t.
  Proof.
    red in |- *; intros.
    apply has_type_inversion with e (sort_term kind) t; simpl in |- *;
     auto with coc core arith datatypes.
  Qed.

  (** Prop has type Kind. *)
  Lemma inversion_has_type_prop : forall e T, has_type e (sort_term prop) T -> convertible T (sort_term kind).
  Proof.
    intros.
    apply has_type_inversion with e (sort_term prop) T; simpl in |- *;
     auto with coc core arith datatypes.
  Qed.

  (** Set has type Kind. *)
  Lemma inversion_has_type_set : forall e T, has_type e (sort_term set) T -> convertible T (sort_term kind).
  Proof.
    intros.
    apply has_type_inversion with e (sort_term set) T; simpl in |- *;
     auto with coc core arith datatypes.
  Qed.

  (** Inversion for variable references. *)
  Lemma inversion_has_type_ref :
   forall (P : Prop) e T n,
   has_type e (var n) T ->
   (forall U : term, nth_error e n = Some U -> convertible T (lift (S n) U) -> P) -> P.
  Proof.
    intros.
    apply has_type_inversion with e (var n) T; simpl in |- *; intros;
     auto with coc core arith datatypes.
    apply H0 with x; auto with coc core arith datatypes.
  Qed.

  (** Inversion for lam abstractions. *)
  Lemma inversion_has_type_abs :
   forall (P : Prop) e A M (U : term),
   has_type e (lam A M) U ->
   (forall s1 s2 T,
    has_type e A (sort_term s1) ->
    has_type (A :: e) M T -> has_type (A :: e) T (sort_term s2) -> convertible (prod A T) U -> P) ->
   P.
  Proof.
    intros.
    apply has_type_inversion with e (lam A M) U; simpl in |- *;
     auto with coc core arith datatypes; intros.
    apply H0 with s1 s2 U0; auto with coc core arith datatypes.
  Qed.

  (** Inversion for applications. *)
  Lemma inversion_has_type_app :
   forall (P : Prop) e u v T,
   has_type e (app u v) T ->
   (forall V Ur : term,
    has_type e u (prod V Ur) -> has_type e v V -> convertible T (subst v Ur) -> P) -> P.
  Proof.
    intros.
    apply has_type_inversion with e (app u v) T; simpl in |- *;
     auto with coc core arith datatypes; intros.
    apply H0 with V Ur; auto with coc core arith datatypes.
  Qed.

  (** Inversion for prod types. *)
  Lemma inversion_has_type_prod :
   forall (P : Prop) e T (U s : term),
   has_type e (prod T U) s ->
   (forall s1 s2,
    has_type e T (sort_term s1) -> has_type (T :: e) U (sort_term s2) -> convertible (sort_term s2) s -> P) -> P.
  Proof.
    intros.
    apply has_type_inversion with e (prod T U) s; simpl in |- *;
     auto with coc core arith datatypes; intros.
    apply H0 with s1 s2; auto with coc core arith datatypes.
  Qed.


  (** A term containing Kind as a subterm is not typable. *)
  Lemma has_type_sort_occurs_kind : forall e t T, sort_occurs_in kind t -> ~ has_type e t T.
  Proof.
    red in |- *; intros.
    apply has_type_inversion with e t T; auto with coc core arith datatypes.
    generalize e T.
    clear H0.
    elim H; simpl in |- *; auto with coc core arith datatypes; intros.
    apply has_type_inversion with e0 u (sort_term s1); auto with coc core arith datatypes.

    apply has_type_inversion with (u :: e0) v (sort_term s2);
     auto with coc core arith datatypes.

    apply has_type_inversion with e0 u (sort_term s1); auto with coc core arith datatypes.

    apply has_type_inversion with (u :: e0) v U; auto with coc core arith datatypes.

    apply has_type_inversion with e0 u (prod V Ur); auto with coc core arith datatypes.

    apply has_type_inversion with e0 v V; auto with coc core arith datatypes.
  Qed.


  (** A term convertible to Kind is not typable. *)
  Lemma inversion_has_type_convertible_kind : forall e t T, convertible t (sort_term kind) -> ~ has_type e t T.
  Proof.
    intros.
    apply has_type_sort_occurs_kind.
    apply reduces_sort_occurs.
    elim church_rosser_theorem with t (sort_term kind); intros;
     auto with coc core arith datatypes.
    rewrite (reduces_normal (sort_term kind) x); auto with coc core arith datatypes.
    red in |- *; red in |- *; intros.
    inversion_clear H2.
  Qed.


  (** Inserting a type into the environment at position n. *)
  Inductive insert_in_environment A : nat -> environment -> environment -> Prop :=
    | ins_zero : forall e, insert_in_environment A 0 e (A :: e)
    | ins_succ :
        forall n e f t,
        insert_in_environment A n e f ->
        insert_in_environment A (S n) (t :: e) (lift_rec 1 t n :: f).

  Hint Resolve ins_zero ins_succ: coc.

  (** Insertion preserves items at positions >= n. *)
  Lemma insert_item_ge :
   forall A n e f,
   insert_in_environment A n e f ->
   forall v : nat, n <= v -> forall t, nth_error e v = Some t -> nth_error f (S v) = Some t.
  Proof.
    induction 1; intros v Hle u Hu.
    - simpl. exact Hu.
    - destruct v as [|v']; [lia|].
      simpl. apply IHinsert_in_environment; [lia | exact Hu].
  Qed.

  (** Insertion preserves lifted items at positions < n. *)
  Lemma insert_item_lt :
   forall A n e f,
   insert_in_environment A n e f ->
   forall v : nat,
   n > v -> forall t, item_lift t e v -> item_lift (lift_rec 1 t n) f v.
  Proof.
    induction 1; intros v Hlt t0 Hil.
    - lia.
    - destruct v as [|n1].
      + elim Hil; intros u Heq Hnth.
        simpl in Hnth. injection Hnth as <-.
        rewrite Heq.
        exists (lift_rec 1 t n).
        * symmetry. apply permute_lift.
        * simpl. reflexivity.
      + elim Hil; intros u Heq Hnth.
        rewrite Heq. simpl in Hnth.
        assert (Hil2 : item_lift (lift (S n1) u) e n1) by (exists u; auto with coc core arith datatypes).
        destruct (IHinsert_in_environment n1 ltac:(lia) (lift (S n1) u) Hil2) as [x0 H_eq H_nth].
        exists x0.
        * rewrite simplify_lift; auto with coc core arith datatypes.
          pattern (lift (S (S n1)) x0) at 1 in |- *.
          rewrite simplify_lift; auto with coc core arith datatypes.
          rewrite <- H_eq.
          rewrite (permute_lift (lift (S n1) u) n).
          reflexivity.
        * simpl. exact H_nth.
  Qed.


  (** Weakening: typing is preserved when inserting a type into the environment. *)
  Lemma has_type_weakening_weak :
   forall A e t T,
   has_type e t T ->
   forall n f,
   insert_in_environment A n e f -> well_formed f -> has_type f (lift_rec 1 t n) (lift_rec 1 T n).
  Proof.
    simple induction 1; simpl in |- *; intros; auto with coc core arith datatypes.
    elim (le_gt_dec n v); intros; apply type_var;
     auto with coc core arith datatypes.
    elim H1; intros.
    exists x.
    rewrite H4.
    unfold lift in |- *.
    rewrite simplify_lift_rec; simpl in |- *; auto with coc core arith datatypes.

    apply insert_item_ge with A n e0; auto with coc core arith datatypes.

    apply insert_item_lt with A e0; auto with coc core arith datatypes.

    cut (well_formed (lift_rec 1 T0 n :: f)).
    intro.
    apply type_abs with s1 s2; auto with coc core arith datatypes.

    apply wf_var with s1; auto with coc core arith datatypes.

    rewrite distribute_lift_subst.
    apply type_app with (lift_rec 1 V n); auto with coc core arith datatypes.

    cut (well_formed (lift_rec 1 T0 n :: f)).
    intro.
    apply type_prod with s1; auto with coc core arith datatypes.

    apply wf_var with s1; auto with coc core arith datatypes.

    apply type_conv with (lift_rec 1 U n) s; auto with coc core arith datatypes.
  Qed.


  (** Thinning: adding a well-typed binding on top preserves typing. *)
  Theorem weakening :
   forall e t T,
   has_type e t T -> forall A, well_formed (A :: e) -> has_type (A :: e) (lift 1 t) (lift 1 T).
  Proof.
    unfold lift in |- *.
    intros.
    inversion_clear H0.
    apply has_type_weakening_weak with A e; auto with coc core arith datatypes.
    apply wf_var with s; auto with coc core arith datatypes.
  Qed.


  (** A successful [nth_error] lookup implies the index is strictly within the list length. *)
  Lemma nth_error_S_le : forall (A : Type) (l : list A) n x, nth_error l n = Some x -> S n <= length l.
  Proof.
    intros. apply (proj1 (nth_error_Some l n)); rewrite H; discriminate.
  Qed.
  Hint Resolve nth_error_S_le: coc.

  (** Iterated weakening: lifting by n preserves typing across n bindings. *)
  Lemma weakening_at :
   forall n e f,
   skipn n e = f ->
   n <= length e ->
   forall t T, has_type f t T -> well_formed e -> has_type e (lift n t) (lift n T).
  Proof.
    induction n as [|n0 IHn]; intros e f Htr Hlen t T Htyp Hwf.
    - rewrite lift_zero. rewrite lift_zero.
      simpl in Htr. subst f. exact Htyp.
    - destruct e as [|x l]; simpl in Htr; [simpl in Hlen; lia|].
      rewrite simplify_lift; auto with coc core arith datatypes.
      pattern (lift (S n0) T) in |- *.
      rewrite simplify_lift; auto with coc core arith datatypes.
      assert (Hlen' : n0 <= length l) by (simpl in Hlen; lia).
      assert (Hwfl : well_formed l) by
        (inversion_clear Hwf; apply has_type_well_formed with x (sort_term s); auto with coc core arith datatypes).
      apply weakening; auto with coc core arith datatypes.
      apply IHn with f; auto with coc core arith datatypes.
  Qed.


  (** Every item in a well-formed environment has a sort when lifted. *)
  Lemma well_formed_sort_lift :
   forall n e t, well_formed e -> item_lift t e n -> exists s : sort, has_type e t (sort_term s).
  Proof.
    induction n as [|n0 IHn]; intros e t Hwf Hil.
    - elim Hil; intros x Heq Hn.
      destruct e as [|h l]; simpl in Hn; [discriminate|].
      injection Hn as Hn; subst x. rewrite Heq.
      inversion_clear Hwf.
      exists s.
      replace (sort_term s) with (lift 1 (sort_term s)); auto with coc core arith datatypes.
      apply weakening; auto with coc core arith datatypes.
      apply wf_var with s; auto with coc core arith datatypes.
    - elim Hil; intros x Heq Hn.
      rewrite Heq.
      destruct e as [|y l]; simpl in Hn; [discriminate|].
      inversion_clear Hwf.
      rewrite simplify_lift; auto with coc core arith datatypes.
      assert (Hwfl : well_formed l) by
        (apply has_type_well_formed with y (sort_term s); auto with coc core arith datatypes).
      assert (Hil2 : item_lift (lift (S n0) x) l n0) by
        (exists x; auto with coc core arith datatypes).
      destruct (IHn l (lift (S n0) x) Hwfl Hil2) as [x0 Htyp].
      exists x0.
      change (has_type (y :: l) (lift 1 (lift (S n0) x)) (lift 1 (sort_term x0))) in |- *.
      apply weakening; auto with coc core arith datatypes.
      apply wf_var with s; auto with coc core arith datatypes.
  Qed.


  (** Substituting a term at position n in the environment. *)
  Inductive substitute_in_environment t T : nat -> environment -> environment -> Prop :=
    | sub_zero : forall e, substitute_in_environment t T 0 (T :: e) e
    | sub_succ :
        forall e f n u,
        substitute_in_environment t T n e f ->
        substitute_in_environment t T (S n) (u :: e) (subst_rec t u n :: f).

  Hint Resolve sub_zero sub_succ: coc.

  (** The substitution index is within the length of the resulting environment. *)
  Lemma substitute_length_le : forall t T n e f, substitute_in_environment t T n e f -> n <= length f.
  Proof.
    induction 1; simpl; lia.
  Qed.
  Hint Resolve substitute_length_le: coc.

  (** Substitution preserves items at positions > n. *)
  Lemma nth_substitute_above :
   forall t T n e f,
   substitute_in_environment t T n e f ->
   forall v : nat, n <= v -> forall u, nth_error e (S v) = Some u -> nth_error f v = Some u.
  Proof.
    induction 1; intros v Hle w Hw.
    - exact Hw.
    - destruct v; [lia|]. simpl in Hw. simpl.
      apply IHsubstitute_in_environment; [lia | exact Hw].
  Qed.


  (** The substituted type is the item at position n. *)
  Lemma nth_substitute_eq : forall t T n e f, substitute_in_environment t T n e f -> nth_error e n = Some T.
  Proof.
    induction 1; simpl; auto with coc core arith datatypes.
  Qed.


  (** Substitution preserves lifted items at positions < n. *)
  Lemma nth_substitute_below :
   forall t T n e f,
   substitute_in_environment t T n e f ->
   forall v : nat,
   n > v -> forall u, item_lift u e v -> item_lift (subst_rec t u n) f v.
  Proof.
    induction 1; intros v Hlt w Hil.
    - lia.
    - destruct v as [|n1].
      + elim Hil; intros x Heq Hn.
        simpl in Hn; injection Hn as Hn; subst x.
        rewrite Heq.
        exists (subst_rec t u n); auto with coc core arith datatypes.
        apply commute_lift_subst; auto with coc core arith datatypes.
      + elim Hil; intros x Heq Hn.
        rewrite Heq. simpl in Hn.
        assert (Hil2 : item_lift (lift (S n1) x) e n1) by
          (exists x; auto with coc core arith datatypes).
        destruct (IHsubstitute_in_environment n1 ltac:(lia) _ Hil2) as [x0 H4 H5].
        exists x0; auto with coc core arith datatypes.
        rewrite simplify_lift; auto with coc core arith datatypes.
        pattern (lift (S (S n1)) x0) in |- *.
        rewrite simplify_lift; auto with coc core arith datatypes.
        rewrite <- H4.
        change
          (subst_rec t (lift 1 (lift (S n1) x)) (S n) =
           lift 1 (subst_rec t (lift (S n1) x) n)) in |- *.
        apply commute_lift_subst; auto with coc core arith datatypes.
  Qed.


  (** Typing is preserved under substitution in the environment. *)
  Lemma has_type_substitute_weakening :
   forall g (d : term) t,
   has_type g d t ->
   forall e u (U : term),
   has_type e u U ->
   forall f n,
   substitute_in_environment d t n e f ->
   well_formed f -> skipn n f = g -> has_type f (subst_rec d u n) (subst_rec d U n).
  Proof.
    simple induction 2; simpl in |- *; intros; auto with coc core arith datatypes.
    elim (lt_eq_lt_dec n v); [ intro Hlt_eq | intro Hlt ].
    elim Hlt_eq; clear Hlt_eq; intro Hcomp.
    destruct v as [|v0]. { lia. }
    apply type_var; auto with coc core arith datatypes.
    elim H2; intros x_raw Hx_eq Hx_nth.
    exists x_raw.
    rewrite Hx_eq; apply simplify_subst; lia.
    apply nth_substitute_above with d t n e0. exact H3. lia. exact Hx_nth.

    subst v.
    elim H2; intros x_raw Hx_eq Hx_nth.
    assert (Hx_is_t : x_raw = t) by
      (assert (Hn_t : nth_error e0 n = Some t) by
         (apply nth_substitute_eq with d f; auto with coc core arith datatypes);
       rewrite Hx_nth in Hn_t; injection Hn_t as <-; reflexivity).
    subst x_raw. rewrite Hx_eq. rewrite simplify_subst by lia.
    apply weakening_at with g;
      [auto with coc core arith datatypes |
       exact (substitute_length_le d t n e0 f H3) |
       auto with coc core arith datatypes |
       auto with coc core arith datatypes].

    apply type_var; auto with coc core arith datatypes.
    apply nth_substitute_below with t e0; auto with coc core arith datatypes.

    cut (well_formed (subst_rec d T n :: f)); intros.
    apply type_abs with s1 s2; auto with coc core arith datatypes.

    apply wf_var with s1; auto with coc core arith datatypes.

    rewrite distribute_subst.
    apply type_app with (subst_rec d V n); auto with coc core arith datatypes.

    cut (well_formed (subst_rec d T n :: f)); intros.
    apply type_prod with s1; auto with coc core arith datatypes.

    apply wf_var with s1; auto with coc core arith datatypes.

    apply type_conv with (subst_rec d U0 n) s; auto with coc core arith datatypes.
  Qed.


  (** Substitution lemma: replacing the head variable preserves typing. *)
  Theorem substitution :
   forall e t u (U : term),
   has_type (t :: e) u U ->
   forall d : term, has_type e d t -> has_type e (subst d u) (subst d U).
  Proof.
    intros.
    unfold subst in |- *.
    apply has_type_substitute_weakening with e t (t :: e); auto with coc core arith datatypes.
    apply has_type_well_formed with d t; auto with coc core arith datatypes.
  Qed.


  (** Types are unique up to conversion. *)
  Theorem has_type_unique_sort :
   forall e t T, has_type e t T -> forall U : term, has_type e t U -> convertible T U.
  Proof.
    simple induction 1; intros.
    apply sym_convertible.
    apply inversion_has_type_prop with e0; auto with coc core arith datatypes.

    apply sym_convertible.
    apply inversion_has_type_set with e0; auto with coc core arith datatypes.

    apply inversion_has_type_ref with e0 U v; auto with coc core arith datatypes;
     intros U0 Hnth0 Hconv0.
    elim H1; intros x_raw Heq_raw Hnth_raw.
    assert (Hxu : x_raw = U0) by congruence; subst x_raw.
    rewrite Heq_raw.
    apply sym_convertible; exact Hconv0.

    apply inversion_has_type_abs with e0 T0 M U0; auto with coc core arith datatypes; intros.
    apply trans_convertible_convertible with (prod T0 T1); auto with coc core arith datatypes.

    apply inversion_has_type_app with e0 u v U; auto with coc core arith datatypes; intros.
    apply trans_convertible_convertible with (subst v Ur0); auto with coc core arith datatypes.
    unfold subst in |- *; apply convertible_convertible_subst;
     auto with coc core arith datatypes.
    apply inversion_convertible_product_right with V V0; auto with coc core arith datatypes.

    apply inversion_has_type_prod with e0 T0 U U0; auto with coc core arith datatypes;
     intros.
    apply trans_convertible_convertible with (sort_term s3); auto with coc core arith datatypes.

    apply trans_convertible_convertible with U; auto with coc core arith datatypes.
  Qed.


  (** Every well-typed term has a sort or its type is Kind. *)
  Theorem type_case :
   forall e t T,
   has_type e t T -> (exists s : sort, has_type e T (sort_term s)) \/ T = sort_term kind.
  Proof.
    simple induction 1; intros; auto with coc core arith datatypes.
    left.
    elim well_formed_sort_lift with v e0 t0; auto with coc core arith datatypes; intros.
    exists x; auto with coc core arith datatypes.

    left.
    exists s2.
    apply type_prod with s1; auto with coc core arith datatypes.

    left.
    elim H3; intros.
    elim H4; intros.
    apply inversion_has_type_prod with e0 V Ur (sort_term x); auto with coc core arith datatypes;
     intros.
    exists s2.
    replace (sort_term s2) with (subst v (sort_term s2)); auto with coc core arith datatypes.
    apply substitution with V; auto with coc core arith datatypes.

    discriminate H4.

    case s2; auto with coc core arith datatypes.
    left.
    exists kind.
    apply type_prop.
    apply has_type_well_formed with T0 (sort_term s1); auto with coc core arith datatypes.

    left.
    exists kind.
    apply type_set.
    apply has_type_well_formed with T0 (sort_term s1); auto with coc core arith datatypes.

    left.
    exists s; auto with coc core arith datatypes.
  Qed.


  (** If a term also types as Kind, its type must be Kind. *)
  Lemma type_kind_not_convertible :
   forall e t T, has_type e t T -> has_type e t (sort_term kind) -> T = sort_term kind.
  Proof.
    intros.
    elim type_case with e t T; intros; auto with coc core arith datatypes.
    elim H1; intros.
    elim inversion_has_type_convertible_kind with e T (sort_term x); auto with coc core arith datatypes.
    apply has_type_unique_sort with e t; auto with coc core arith datatypes.
  Qed.


  (** The type of a well-typed term has bounded de Bruijn indices. *)
  Lemma type_free_db_below : forall e t T, has_type e t T -> free_db_below (length e) T.
  Proof.
    intros.
    elim type_case with e t T; intros; auto with coc core arith datatypes.
    inversion_clear H0.
    apply has_type_free_db_below with (sort_term x); auto with coc core arith datatypes.

    rewrite H0; auto with coc core arith datatypes.
  Qed.


  (** One-step reduction in the environment. *)
  Inductive reduces_once_in_environment : environment -> environment -> Prop :=
    | red_env_hd : forall e t u, reduces_once t u -> reduces_once_in_environment (t :: e) (u :: e)
    | red_env_tl :
        forall e f t, reduces_once_in_environment e f -> reduces_once_in_environment (t :: e) (t :: f).

  Hint Resolve red_env_hd red_env_tl: coc.

  (** Items are preserved or reduced under one-step environment reduction. *)
  Lemma reduces_item :
   forall n t e,
   item_lift t e n ->
   forall f,
   reduces_once_in_environment e f ->
   item_lift t f n \/
   (forall g, skipn (S n) e = g -> skipn (S n) f = g) /\
   ex2 (fun u => reduces_once t u) (fun u => item_lift u f n).
  Proof.
    induction n as [|n0 IHn]; intros t e Hil f Hred.
    - elim Hil; intros x Heq Hn.
      destruct e as [|h e']; simpl in Hn; [discriminate|].
      injection Hn as Hn; subst x. rewrite Heq.
      inversion_clear Hred.
      + right.
        split; intros.
        * simpl in *. assumption.
        * exists (lift 1 u).
          unfold lift in |- *; auto with coc core arith datatypes.
          exists u; auto with coc core arith datatypes.
      + left.
        exists h; auto with coc core arith datatypes.
    - elim Hil; intros x Heq Hn.
      rewrite Heq.
      destruct e as [|h l]; simpl in Hn; [discriminate|].
      inversion_clear Hred.
      + left.
        exists x; auto with coc core arith datatypes.
      + assert (Hil2 : item_lift (lift (S n0) x) l n0) by
          (exists x; auto with coc core arith datatypes).
        destruct (IHn (lift (S n0) x) l Hil2 f0 H) as [Hleft | [Htrunc Hright]].
        * left.
          elim Hleft; intros x0 H4 H5.
          exists x0; auto with coc core arith datatypes.
          rewrite simplify_lift.
          pattern (lift (S (S n0)) x0) in |- *.
          rewrite simplify_lift.
          rewrite H4; auto with coc core arith datatypes.
        * right.
          split.
          -- intros g Hg. simpl in *. apply Htrunc. exact Hg.
          -- elim Hright; intros x1 Hred1 Hil3.
             elim Hil3; intros z Heqz Hnthz.
             exists (lift (S (S n0)) z).
             { rewrite simplify_lift.
               pattern (lift (S (S n0)) z) in |- *.
               rewrite simplify_lift.
               rewrite <- Heqz.
               apply (reduces_once_lift _ _ Hred1 1 0). }
             { exists z; auto with coc core arith datatypes. }
  Qed.


  (** Typing is preserved when the environment reduces by one step. *)
  Lemma has_type_reduces_environment :
   forall e t T, has_type e t T -> forall f, reduces_once_in_environment e f -> well_formed f -> has_type f t T.
  Proof.
    simple induction 1; intros.
    auto with coc core arith datatypes.

    auto with coc core arith datatypes.

    elim reduces_item with v t0 e0 f; auto with coc core arith datatypes; intros.
    inversion_clear H4.
    inversion_clear H6.
    elim H1; intros x0 H6 H8.
    destruct (well_formed_sort v e0 (skipn (S v) e0) eq_refl H0 x0 H8) as [x2 Hx2].
    apply type_conv with x x2; auto with coc core arith datatypes.
    rewrite H6.
    replace (sort_term x2) with (lift (S v) (sort_term x2));
     auto with coc core arith datatypes.
    assert (Hvl : v < length e0) by
      (apply (proj1 (nth_error_Some e0 v)); rewrite H8; discriminate).
    assert (Hskipn : skipn (S v) f = skipn (S v) e0) by (apply H5; reflexivity).
    assert (Hvlf : S v <= length f) by
      (assert (Hlen : length f = length e0) by
        (clear - H2; induction H2; simpl; lia);
       lia).
    assert (Hx2f : has_type (skipn (S v) f) x0 (sort_term x2)) by
      (rewrite Hskipn; exact Hx2).
    apply weakening_at with (skipn (S v) f);
      [reflexivity | exact Hvlf | exact Hx2f | exact H3].

    cut (well_formed (T0 :: f)); intros.
    apply type_abs with s1 s2; auto with coc core arith datatypes.

    apply wf_var with s1; auto with coc core arith datatypes.

    apply type_app with V; auto with coc core arith datatypes.

    cut (well_formed (T0 :: f)); intros.
    apply type_prod with s1; auto with coc core arith datatypes.

    apply wf_var with s1; auto with coc core arith datatypes.

    apply type_conv with U s; auto with coc core arith datatypes.
  Qed.


  (** Subject reduction for one-step reduction. *)
  Lemma subject_reduction : forall e t T, has_type e t T -> forall u, reduces_once t u -> has_type e u T.
  Proof.
    simple induction 1; intros.
    inversion_clear H1.

    inversion_clear H1.

    inversion_clear H2.

    inversion_clear H6.
    cut (well_formed (M' :: e0)); intros.
    apply type_conv with (prod M' U) s2; auto with coc core arith datatypes.
    apply type_abs with s1 s2; auto with coc core arith datatypes.
    apply has_type_reduces_environment with (T0 :: e0); auto with coc core arith datatypes.

    apply has_type_reduces_environment with (T0 :: e0); auto with coc core arith datatypes.

    apply type_prod with s1; auto with coc core arith datatypes.

    apply wf_var with s1; auto with coc core arith datatypes.

    apply type_abs with s1 s2; auto with coc core arith datatypes.

    elim type_case with e0 u (prod V Ur); intros;
     auto with coc core arith datatypes.
    inversion_clear H5.
    apply inversion_has_type_prod with e0 V Ur (sort_term x); intros;
     auto with coc core arith datatypes.
    generalize H2 H3.
    clear H2 H3.
    inversion_clear H4; intros.
    apply inversion_has_type_abs with e0 T0 M (prod V Ur); intros;
     auto with coc core arith datatypes.
    apply type_conv with (subst v T1) s2; auto with coc core arith datatypes.
    apply substitution with T0; auto with coc core arith datatypes.
    apply type_conv with V s0; auto with coc core arith datatypes.
    apply inversion_convertible_product_left with Ur T1; auto with coc core arith datatypes.

    unfold subst in |- *.
    apply convertible_convertible_subst; auto with coc core arith datatypes.
    apply inversion_convertible_product_right with T0 V; auto with coc core arith datatypes.

    replace (sort_term s2) with (subst v (sort_term s2)); auto with coc core arith datatypes.
    apply substitution with V; auto with coc core arith datatypes.

    apply type_app with V; auto with coc core arith datatypes.

    apply type_conv with (subst N2 Ur) s2; auto with coc core arith datatypes.
    apply type_app with V; auto with coc core arith datatypes.

    unfold subst in |- *.
    apply convertible_convertible_subst; auto with coc core arith datatypes.

    replace (sort_term s2) with (subst v (sort_term s2)); auto with coc core arith datatypes.
    apply substitution with V; auto with coc core arith datatypes.

    discriminate H5.

    inversion_clear H4.
    apply type_prod with s1; auto with coc core arith datatypes.
    apply has_type_reduces_environment with (T0 :: e0); auto with coc core arith datatypes.
    apply wf_var with s1; auto with coc core arith datatypes.

    apply type_prod with s1; auto with coc core arith datatypes.

    apply type_conv with U s; auto with coc core arith datatypes.
  Qed.


  (** Subject reduction: typing is preserved under multi-step reduction. *)
  Theorem subject_reduction_theorem :
   forall e t u, reduces t u -> forall T, has_type e t T -> has_type e u T.
  Proof.
    intros e t u H; induction H; intros; auto with coc core arith datatypes.
    apply subject_reduction with y; intros; auto with coc core arith datatypes.
  Qed.


  (** Typing is preserved when the type reduces. *)
  Lemma type_reduction :
   forall e t T (U : term), reduces T U -> has_type e t T -> has_type e t U.
  Proof.
    intros.
    elim type_case with e t T; intros; auto with coc core arith datatypes.
    inversion_clear H1.
    apply type_conv with T x; auto with coc core arith datatypes.
    apply subject_reduction_theorem with T; auto with coc core arith datatypes.

    elim reduces_normal with T U; auto with coc core arith datatypes.
    rewrite H1.
    red in |- *; red in |- *; intros.
    inversion_clear H2.
  Qed.


  (** Convertible terms have convertible types. *)
  Lemma has_type_convertible_convertible :
   forall e u (U : term) v (V : term),
   has_type e u U -> has_type e v V -> convertible u v -> convertible U V.
  Proof.
    intros.
    elim church_rosser_theorem with u v; auto with coc core arith datatypes; intros.
    apply has_type_unique_sort with e x.
    apply subject_reduction_theorem with u; auto with coc core arith datatypes.

    apply subject_reduction_theorem with v; auto with coc core arith datatypes.
  Qed.

End Typage.

  Hint Resolve ins_zero ins_succ: coc.
  Hint Resolve sub_zero sub_succ: coc.
  Hint Resolve red_env_hd red_env_tl: coc.
