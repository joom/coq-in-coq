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


From CoqInCoq Require Import list_utils.
From CoqInCoq Require Import terms.
From CoqInCoq Require Export names.

  (** Named expression syntax for the Calculus of Constructions *)
  Inductive expr : Set :=
    | expr_sort : sort -> expr
    | expr_ref : name -> expr
    | expr_abs : name -> expr -> expr -> expr
    | expr_app : expr -> expr -> expr
    | expr_prod : name -> expr -> expr -> expr.


  (** Free variable occurrence in an expression *)
  Inductive expression_variables (x : name) : expr -> Prop :=
    | ev_ref : expression_variables x (expr_ref x)
    | ev_abs_l :
        forall (y : name) (T M : expr),
        expression_variables x T -> expression_variables x (expr_abs y T M)
    | ev_abs_r :
        forall (y : name) (T M : expr),
        x <> y -> expression_variables x M -> expression_variables x (expr_abs y T M)
    | ev_app_l : forall u v : expr, expression_variables x u -> expression_variables x (expr_app u v)
    | ev_app_r : forall u v : expr, expression_variables x v -> expression_variables x (expr_app u v)
    | ev_prod_l :
        forall (y : name) (T U : expr),
        expression_variables x T -> expression_variables x (expr_prod y T U)
    | ev_prod_r :
        forall (y : name) (T U : expr),
        x <> y -> expression_variables x U -> expression_variables x (expr_prod y T U).

  Hint Resolve ev_ref ev_abs_l ev_abs_r ev_app_l ev_app_r ev_prod_l
    ev_prod_r: coc.


  (** Decide whether a name occurs free in an expression *)
  Definition is_free_var :
   forall (x : name) (e : expr), {expression_variables x e} + {~ expression_variables x e}.
  Proof.
    simple induction e.
    right; red in |- *; intros; inversion H.

    intro y; case (name_dec x y); intros; [ left | right ].
    rewrite e0; auto with coc.
    red in |- *; intros A; inversion A; auto.

    intros y t H u H1.
    elim H; intros;
     [ idtac | elim (name_dec x y); intros; [ idtac | elim H1; intros ] ];
     auto with coc; right; red in |- *; intros A; inversion A;
     auto.

    intros u H v H1.
    elim H; intros; [ idtac | elim H1; intros ]; auto with coc; right;
     red in |- *; intros A; inversion A; auto.

    intros y t H u H1.
    elim H; intros;
     [ idtac | elim (name_dec x y); intros; [ idtac | elim H1; intros ] ];
     auto with coc; right; red in |- *; intros A; inversion A;
     auto.
  Defined.


  (** Name translation between two parallel name lists *)
  Inductive translate_name : list name -> name -> list name -> name -> Prop :=
    | tr_nil : forall x : name, translate_name nil x nil x
    | tr_hd :
        forall (x y : name) (l1 l2 : list name),
        translate_name (x :: l1) x (y :: l2) y
    | tr_tl :
        forall (x x0 y y0 : name) (l1 l2 : list name),
        x <> x0 ->
        y <> y0 ->
        translate_name l1 x l2 y -> translate_name (x0 :: l1) x (y0 :: l2) y.


  (** Alpha-equivalence of expressions under name contexts *)
  Inductive alpha : list name -> expr -> list name -> expr -> Prop :=
    | alp_sort :
        forall (l1 l2 : list name) (s : sort), alpha l1 (expr_sort s) l2 (expr_sort s)
    | alp_ref :
        forall (l1 l2 : list name) (x y : name),
        translate_name l1 x l2 y -> alpha l1 (expr_ref x) l2 (expr_ref y)
    | alp_abs :
        forall (l1 l2 : list name) (x y : name) (A A' M M' : expr),
        alpha l1 A l2 A' ->
        alpha (x :: l1) M (y :: l2) M' ->
        alpha l1 (expr_abs x A M) l2 (expr_abs y A' M')
    | alp_app :
        forall (l1 l2 : list name) (A A' M M' : expr),
        alpha l1 A l2 A' ->
        alpha l1 M l2 M' -> alpha l1 (expr_app A M) l2 (expr_app A' M')
    | alp_prod :
        forall (l1 l2 : list name) (x y : name) (A A' M M' : expr),
        alpha l1 A l2 A' ->
        alpha (x :: l1) M (y :: l2) M' ->
        alpha l1 (expr_prod x A M) l2 (expr_prod y A' M').


  (** Equivalence between de Bruijn terms and named expressions *)
  Inductive term_expression_equivalent : partial_names -> term -> expr -> Prop :=
    | eqv_sort :
        forall (l : partial_names) (s : sort), term_expression_equivalent l (sort_term s) (expr_sort s)
    | eqv_ref :
        forall (l : partial_names) (x : name) (n : nat),
        first_item x l n -> term_expression_equivalent l (var n) (expr_ref x)
    | eqv_abs :
        forall (l : partial_names) (A M : term) (B N : expr) (x : name),
        term_expression_equivalent l A B ->
        term_expression_equivalent (x :: l) M N ->
        term_expression_equivalent l (lam A M) (expr_abs x B N)
    | eqv_app :
        forall (l : partial_names) (u v : term) (a b : expr),
        term_expression_equivalent l u a ->
        term_expression_equivalent l v b -> term_expression_equivalent l (app u v) (expr_app a b)
    | eqv_prod :
        forall (l : partial_names) (A M : term) (B N : expr) (x : name),
        term_expression_equivalent l A B ->
        term_expression_equivalent (x :: l) M N ->
        term_expression_equivalent l (prod A M) (expr_prod x B N).


  (** An equivalent expression has a well-scoped de Bruijn term *)
  Lemma equivalent_free_db :
   forall (l : partial_names) (t : term) (e : expr),
   term_expression_equivalent l t e -> free_db_below (length l) t.
  Proof.
    simple induction 1; simpl in |- *; intros; auto with coc core arith datatypes.
    apply db_var.
    unfold first_item in H0; destruct H0 as [Hnth _].
    apply nth_error_Some; rewrite Hnth; discriminate.
  Qed.


  (** The de Bruijn term of an equivalence is unique *)
  Lemma equivalent_unique :
   forall (l : partial_names) (t : term) (e : expr),
   term_expression_equivalent l t e -> forall u : term, term_expression_equivalent l u e -> t = u.
  Proof.
    simple induction 1; intros.
    inversion_clear H0; auto with coc core arith datatypes.

    inversion_clear H1.
    elim first_item_unique with x l0 n n0;
     auto with coc core arith datatypes.

    inversion_clear H4.
    elim H1 with A0; auto with coc core arith datatypes.
    elim H3 with M0; auto with coc core arith datatypes.

    inversion_clear H4.
    elim H1 with u1; auto with coc core arith datatypes.
    elim H3 with v0; auto with coc core arith datatypes.

    inversion_clear H4.
    elim H1 with A0; auto with coc core arith datatypes.
    elim H3 with M0; auto with coc core arith datatypes.
  Qed.


  (** If x is first at index n in l1 and y is first at index n in l2, then
      translate_name l1 x l2 y holds. *)
  Lemma first_item_translate :
    forall (n : nat) (l1 l2 : partial_names) (x y : name),
    first_item x l1 n -> first_item y l2 n -> translate_name l1 x l2 y.
  Proof.
    unfold first_item.
    induction n as [|n' IH]; intros l1 l2 x y [Hn1 Hni1] [Hn2 Hni2].
    - destruct l1 as [|h1 l1']; [simpl in Hn1; discriminate|].
      destruct l2 as [|h2 l2']; [simpl in Hn2; discriminate|].
      simpl in Hn1; injection Hn1 as Hn1; subst h1.
      simpl in Hn2; injection Hn2 as Hn2; subst h2.
      apply tr_hd.
    - destruct l1 as [|h1 l1']; [simpl in Hn1; discriminate|].
      destruct l2 as [|h2 l2']; [simpl in Hn2; discriminate|].
      simpl in Hn1. simpl in Hn2.
      simpl in Hni1. simpl in Hni2.
      apply tr_tl.
      + intros Heq; apply Hni1; left; exact (eq_sym Heq).
      + intros Heq; apply Hni2; left; exact (eq_sym Heq).
      + apply IH.
        * split; [exact Hn1 | intros Hin; apply Hni1; right; exact Hin].
        * split; [exact Hn2 | intros Hin; apply Hni2; right; exact Hin].
  Qed.

  (** Two equivalent expressions of the same term are alpha-equivalent *)
  Lemma unique_alpha :
   forall (l1 : partial_names) (t : term) (e : expr),
   term_expression_equivalent l1 t e ->
   forall (l2 : partial_names) (f : expr),
   term_expression_equivalent l2 t f -> alpha l1 e l2 f.
  Proof.
    simple induction 1; intros.
    inversion_clear H0.
    apply alp_sort.

    inversion_clear H1.
    apply alp_ref.
    exact (first_item_translate n l l2 x x0 H0 H2).

    inversion_clear H4.
    apply alp_abs; auto with coc core arith datatypes.

    inversion_clear H4.
    apply alp_app; auto with coc core arith datatypes.

    inversion_clear H4.
    apply alp_prod; auto with coc core arith datatypes.
  Qed.


  (** Convert a de Bruijn term to a named expression given a name context *)
  Definition expression_of_term :
   forall (t : term) (l : partial_names),
   name_unique l ->
   free_db_below (length l) t -> {e : expr | term_expression_equivalent l t e}.
  Proof.
    simple induction t; intros.
    exists (expr_sort s).
    apply eqv_sort.

    destruct (nth_error l n) as [x|] eqn:Hn.
    exists (expr_ref x).
    apply eqv_ref.
    apply name_unique_first; auto with coc core arith datatypes.

    exfalso.
    inversion_clear H0.
    apply nth_error_None in Hn. lia.

    elim H with l; intros; auto with coc core arith datatypes.
    elim find_free_var with l; intros.
    elim H0 with (x0 :: l); intros.
    exists (expr_abs x0 x x1).
    apply eqv_abs; auto with coc core arith datatypes.

    apply free_var_extension; auto with coc core arith datatypes.

    inversion_clear H2; auto with coc core arith datatypes.

    inversion_clear H2; auto with coc core arith datatypes.

    elim H with l; intros; auto with coc core arith datatypes.
    elim H0 with l; intros; auto with coc core arith datatypes.
    exists (expr_app x x0).
    apply eqv_app; auto with coc core arith datatypes.

    inversion_clear H2; auto with coc core arith datatypes.

    inversion_clear H2; auto with coc core arith datatypes.

    elim H with l; intros; auto with coc core arith datatypes.
    elim find_free_var with l; intros.
    elim H0 with (x0 :: l); intros.
    exists (expr_prod x0 x x1).
    apply eqv_prod; auto with coc core arith datatypes.

    apply free_var_extension; auto with coc core arith datatypes.

    inversion_clear H2; auto with coc core arith datatypes.

    inversion_clear H2; auto with coc core arith datatypes.
  Defined.


  (** Undefined variables: names disjoint from context that occur free *)
  Definition undef_vars (e : expr) (def undef : partial_names) : Prop :=
    (forall x : name, In x def -> In x undef -> False) /\
    (forall x : name, In x undef -> expression_variables x e).

  (** Undefined variables are preserved under inclusion *)
  Lemma undefined_vars_incl :
   forall (e : expr) (l u1 u2 : partial_names),
   incl u1 u2 -> undef_vars e l u2 -> undef_vars e l u1.
  Proof.
    unfold undef_vars in |- *; split.
    inversion_clear H0; intros.
    apply H1 with x; auto with coc core arith datatypes.

    inversion_clear H0; auto with coc core arith datatypes.
  Qed.


  (** Undefined variables propagate through abstractions *)
  Lemma undefined_vars_lambda :
   forall (x : name) (e1 e2 : expr) (l u1 u2 : partial_names),
   undef_vars e1 l u1 ->
   undef_vars e2 (x :: l) u2 -> undef_vars (expr_abs x e1 e2) l (u1 ++ u2).
  Proof.
    intros x e1 e2 l u1 u2 H H0.
    destruct H as [Hdisj1 Hfv1]; destruct H0 as [Hdisj2 Hfv2].
    split.
    - intros x0 Hdef Hundef.
      destruct (in_app_or u1 u2 x0 Hundef) as [H7 | H7].
      + exact (Hdisj1 x0 Hdef H7).
      + exact (Hdisj2 x0 (or_intror Hdef) H7).
    - intros x0 Hundef.
      destruct (in_app_or u1 u2 x0 Hundef) as [H7 | H7].
      + auto with coc core arith datatypes.
      + apply ev_abs_r; [| exact (Hfv2 x0 H7)].
        intro Heq; subst x0; exact (Hdisj2 x (in_eq x l) H7).
  Qed.


  (** Undefined variables propagate through applications *)
  Lemma undefined_vars_application :
   forall (e1 e2 : expr) (l u1 u2 : partial_names),
   undef_vars e1 l u1 ->
   undef_vars e2 l u2 -> undef_vars (expr_app e1 e2) l (u1 ++ u2).
  Proof.
    intros e1 e2 l u1 u2 H H0.
    destruct H as [Hdisj1 Hfv1]; destruct H0 as [Hdisj2 Hfv2].
    split.
    - intros x Hdef Hundef.
      destruct (in_app_or u1 u2 x Hundef) as [H7 | H7].
      + exact (Hdisj1 x Hdef H7).
      + exact (Hdisj2 x Hdef H7).
    - intros x Hundef.
      destruct (in_app_or u1 u2 x Hundef) as [H7 | H7].
      + auto with coc core arith datatypes.
      + auto with coc core arith datatypes.
  Qed.

  (** Undefined variables propagate through products *)
  Lemma undefined_vars_product :
   forall (x : name) (e1 e2 : expr) (l u1 u2 : partial_names),
   undef_vars e1 l u1 ->
   undef_vars e2 (x :: l) u2 -> undef_vars (expr_prod x e1 e2) l (u1 ++ u2).
  Proof.
    intros x e1 e2 l u1 u2 H H0.
    destruct H as [Hdisj1 Hfv1]; destruct H0 as [Hdisj2 Hfv2].
    split.
    - intros x0 Hdef Hundef.
      destruct (in_app_or u1 u2 x0 Hundef) as [H7 | H7].
      + exact (Hdisj1 x0 Hdef H7).
      + exact (Hdisj2 x0 (or_intror Hdef) H7).
    - intros x0 Hundef.
      destruct (in_app_or u1 u2 x0 Hundef) as [H7 | H7].
      + auto with coc core arith datatypes.
      + apply ev_prod_r; [| exact (Hfv2 x0 H7)].
        intro Heq; subst x0; exact (Hdisj2 x (in_eq x l) H7).
  Qed.


  (** An equivalent expression has no undefined variables *)
  Lemma equivalent_no_undefined :
   forall (l : partial_names) (t : term) (e : expr),
   term_expression_equivalent l t e ->
   forall undef : partial_names, undef_vars e l undef -> undef = nil.
  Proof.
    assert (abs_inv : forall h x B N, expression_variables h (expr_abs x B N) ->
      expression_variables h B \/ (h <> x /\ expression_variables h N)).
    { intros h x B N Hev; inversion Hev; subst; [left | right; split]; assumption. }
    assert (prod_inv : forall h x B N, expression_variables h (expr_prod x B N) ->
      expression_variables h B \/ (h <> x /\ expression_variables h N)).
    { intros h x B N Hev; inversion Hev; subst; [left | right; split]; assumption. }
    assert (app_inv : forall h a b, expression_variables h (expr_app a b) ->
      expression_variables h a \/ expression_variables h b).
    { intros h a b Hev; inversion Hev; subst; [left | right]; assumption. }
    induction 1 as [l s | l x n Hfi | l A M B N x HAB IHA HMN IHM | l u v a b Hu IHu Hv IHv | l A M B N x HAB IHA HMN IHM].
    all: intros [| h rest] [Hdisj Hvars]; auto.
    - (* expr_sort: no constructor matches expression_variables h (expr_sort s) *)
      pose proof (Hvars h (in_eq h rest)) as Hev; inversion Hev.
    - (* expr_ref: h = x and x in l, but h disjoint from l *)
      pose proof (Hvars h (in_eq h rest)) as Hev.
      inversion Hev; subst.
      exfalso.
      assert (Hxl : In x l) by (unfold first_item in Hfi; destruct Hfi as [Hnth _]; exact (nth_error_In l n Hnth)).
      exact (Hdisj x Hxl (in_eq x rest)).
    - (* expr_abs *)
      destruct (abs_inv h x B N (Hvars h (in_eq h rest))) as [Hevl | [Hneq Hevr]].
      + assert (Hnil : h :: nil = nil).
        { apply IHA. split.
          - intros y Hyl Hin. simpl in Hin. destruct Hin as [<- | []].
            exact (Hdisj h Hyl (in_eq h rest)).
          - intros y Hin. simpl in Hin. destruct Hin as [<- | []]. exact Hevl. }
        discriminate.
      + assert (Hnil : h :: nil = nil).
        { apply IHM. split.
          - intros y Hyl Hin. simpl in Hyl, Hin. destruct Hin as [<- | []].
            destruct Hyl as [Heq' | Hyl'].
            * exact (Hneq (eq_sym Heq')).
            * exact (Hdisj h Hyl' (in_eq h rest)).
          - intros y Hin. simpl in Hin. destruct Hin as [<- | []]. exact Hevr. }
        discriminate.
    - (* expr_app *)
      destruct (app_inv h a b (Hvars h (in_eq h rest))) as [Heva | Hevb].
      + assert (Hnil : h :: nil = nil).
        { apply IHu. split.
          - intros y Hyl Hin. simpl in Hin. destruct Hin as [<- | []].
            exact (Hdisj h Hyl (in_eq h rest)).
          - intros y Hin. simpl in Hin. destruct Hin as [<- | []]. exact Heva. }
        discriminate.
      + assert (Hnil : h :: nil = nil).
        { apply IHv. split.
          - intros y Hyl Hin. simpl in Hin. destruct Hin as [<- | []].
            exact (Hdisj h Hyl (in_eq h rest)).
          - intros y Hin. simpl in Hin. destruct Hin as [<- | []]. exact Hevb. }
        discriminate.
    - (* expr_prod *)
      destruct (prod_inv h x B N (Hvars h (in_eq h rest))) as [Hevl | [Hneq Hevr]].
      + assert (Hnil : h :: nil = nil).
        { apply IHA. split.
          - intros y Hyl Hin. simpl in Hin. destruct Hin as [<- | []].
            exact (Hdisj h Hyl (in_eq h rest)).
          - intros y Hin. simpl in Hin. destruct Hin as [<- | []]. exact Hevl. }
        discriminate.
      + assert (Hnil : h :: nil = nil).
        { apply IHM. split.
          - intros y Hyl Hin. simpl in Hyl, Hin. destruct Hin as [<- | []].
            destruct Hyl as [Heq' | Hyl'].
            * exact (Hneq (eq_sym Heq')).
            * exact (Hdisj h Hyl' (in_eq h rest)).
          - intros y Hin. simpl in Hin. destruct Hin as [<- | []]. exact Hevr. }
        discriminate.
  Qed.


  (** Convert a named expression to a de Bruijn term, or return undefined variables *)
  Definition term_of_expression :
   forall (e : expr) (l : partial_names),
   {t : term | term_expression_equivalent l t e} +
   {undef : partial_names | undef_vars e l undef &  undef <> nil}.
  Proof.
(*Realizer Fix term_of_expression
  {term_of_expression/1: expr->partial_names->(sum term partial_names) :=
    [e:expr][l:partial_names]Cases e of
      (expr_sort s) => (inl term partial_names (sort_term s))
    | (expr_ref x) => Cases (list_index name name_dec x l) of
             (inleft n) => (inl term partial_names (var n))
           | inright => (inr term partial_names (cons x (nil name)))
           end
    | (expr_abs x e1 e2) =>
           Cases (term_of_expression e1 l) (term_of_expression e2 (cons x l)) of
             (inl a) (inl m) => (inl term partial_names (lam a m))
           | (inr u1) (inr u2) => (inr term partial_names u1^u2)
           | (inr u) _ => (inr term partial_names u)
           | _ (inr u) => (inr term partial_names u)
           end
    | (expr_app e1 e2) =>
           Cases (term_of_expression e1 l) (term_of_expression e2 l) of
             (inl u) (inl v) => (inl term partial_names (app u v))
           | (inr u1) (inr u2) => (inr term partial_names u1^u2)
           | (inr u) _ => (inr term partial_names u)
           | _ (inr u) => (inr term partial_names u)
           end
    | (expr_prod x e1 e2) =>
           Cases (term_of_expression e1 l) (term_of_expression e2 (cons x l)) of
             (inl a) (inl b) => (inl term partial_names (prod a b))
           | (inr u1) (inr u2) => (inr term partial_names u1^u2)
           | (inr u) _ => (inr term partial_names u)
           | _ (inr u) => (inr term partial_names u)
           end
    end}.
*)
    simple induction e; intros.
    left.
    exists (sort_term s).
    apply eqv_sort.

    elim (list_index name_dec n l); intros.
    left.
    inversion_clear a.
    exists (var x).
    apply eqv_ref; auto with coc core arith datatypes.

    right.
    exists (n :: nil).
    split.
    intros.
    destruct H0 as [<- | []].
    exact (b H).

    intros.
    simpl in H.
    destruct H as [<- | []].
    apply ev_ref.

    discriminate.

    elim H with l; intros.
    elim H0 with (n :: l); intros.
    left.
    inversion_clear a.
    inversion_clear a0.
    exists (lam x x0).
    apply eqv_abs; auto with coc core arith datatypes.

    inversion_clear b.
    right.
    exists x.
    replace x with (nil ++ x); auto with coc core arith datatypes.
    apply undefined_vars_lambda; auto with coc core arith datatypes.
    split; intros.
    intros.
    inversion_clear H4.

    inversion_clear H3.

    auto with coc core arith datatypes.

    inversion_clear b.
    elim H0 with (n :: l); intros.
    right.
    exists x; auto with coc core arith datatypes.
    apply undefined_vars_incl with (x ++ nil).
    red in |- *; intros z Hz; apply in_or_app; left; exact Hz.

    apply undefined_vars_lambda; auto with coc core arith datatypes.
    split; intros.
    intros.
    inversion_clear H4.

    inversion_clear H3.

    inversion_clear b.
    right.
    exists (x ++ x0); intros.
    apply undefined_vars_lambda; auto with coc core arith datatypes.

    generalize H2.
    case x; simpl in |- *; intros.
    contradiction.

    discriminate.

    elim H with l; intros.
    elim H0 with l; intros.
    left.
    inversion_clear a.
    inversion_clear a0.
    exists (app x x0).
    apply eqv_app; auto with coc core arith datatypes.

    inversion_clear b.
    right.
    exists x.
    replace x with (nil ++ x); auto with coc core arith datatypes.
    apply undefined_vars_application; auto with coc core arith datatypes.
    split; intros.
    intros.
    inversion H4.

    inversion H3.

    auto with coc core arith datatypes.

    inversion_clear b.
    elim H0 with l; intros.
    right.
    exists x; auto with coc core arith datatypes.
    apply undefined_vars_incl with (x ++ nil).
    red in |- *; intros z Hz; apply in_or_app; left; exact Hz.

    apply undefined_vars_application; auto with coc core arith datatypes.
    split; intros.
    intros.
    inversion_clear H4.

    inversion_clear H3.

    inversion_clear b.
    right.
    exists (x ++ x0); intros.
    apply undefined_vars_application; auto with coc core arith datatypes.

    generalize H2.
    case x; simpl in |- *; intros.
    contradiction.

    discriminate.

    elim H with l; intros.
    elim H0 with (n :: l); intros.
    left.
    inversion_clear a.
    inversion_clear a0.
    exists (prod x x0).
    apply eqv_prod; auto with coc core arith datatypes.

    inversion_clear b.
    right.
    exists x.
    replace x with (nil ++ x); auto with coc core arith datatypes.
    apply undefined_vars_product; auto with coc core arith datatypes.
    split; intros.
    intros.
    inversion H4.

    inversion H3.

    auto with coc core arith datatypes.

    inversion_clear b.
    elim H0 with (n :: l); intros.
    right.
    exists x; auto with coc core arith datatypes.
    apply undefined_vars_incl with (x ++ nil).
    red in |- *; intros z Hz; apply in_or_app; left; exact Hz.

    apply undefined_vars_product; auto with coc core arith datatypes.
    split; intros.
    intros.
    inversion H4.

    inversion H3.

    inversion_clear b.
    right.
    exists (x ++ x0); intros.
    apply undefined_vars_product; auto with coc core arith datatypes.

    generalize H2.
    case x; simpl in |- *; intros.
    contradiction.

    discriminate.
  Defined.
