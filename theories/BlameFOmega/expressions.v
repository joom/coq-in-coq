(** * BlameFOmega.expressions: Named surface syntax for System Fω + blame.

    Mirrors CoC/expressions.v but for the two-namespace (type variables /
    term variables) structure of System Fω.  Provides named types and terms,
    equivalence relations to the de Bruijn representations in
    BlameFOmega/syntax.v, hint-aware conversion functions from de Bruijn to
    named form, and their correctness lemmas (well-scopedness and uniqueness).

    The name infrastructure ([name], [partial_names], [first_item],
    [name_unique], [pick_name], [find_free_var]) is shared with the CoC
    development and imported from [CoC.names] / [CoC.list_utils]. *)

From Stdlib Require Import List Lia.
From CoC Require Import list_utils ml_types names.
From BlameFOmega Require Import syntax.

Import ListNotations.


(** ** Named type expressions *)

Inductive ftyp_expr : Set :=
  | ftyp_var : name -> ftyp_expr
  | ftyp_arrow : ftyp_expr -> ftyp_expr -> ftyp_expr
  | ftyp_all : name -> kind -> ftyp_expr -> ftyp_expr
  | ftyp_tyabs : name -> kind -> ftyp_expr -> ftyp_expr
  | ftyp_tyapp : ftyp_expr -> ftyp_expr -> ftyp_expr
  | ftyp_dyn : ftyp_expr.


(** ** Named term expressions *)

Inductive fterm_expr : Set :=
  | fterm_var : name -> fterm_expr
  | fterm_abs : name -> ftyp_expr -> fterm_expr -> fterm_expr
  | fterm_app : fterm_expr -> fterm_expr -> fterm_expr
  | fterm_tabs : name -> kind -> fterm_expr -> fterm_expr
  | fterm_tapp : fterm_expr -> ftyp_expr -> fterm_expr
  | fterm_cast : fterm_expr -> ftyp_expr -> ftyp_expr -> label -> fterm_expr
  | fterm_gnd : fterm_expr -> ftyp_expr -> fterm_expr
  | fterm_is_gnd : fterm_expr -> ftyp_expr -> fterm_expr
  | fterm_blame : label -> fterm_expr
  | fterm_nu : name -> kind -> ftyp_expr -> fterm_expr -> fterm_expr.


(** ** Well-scoped de Bruijn predicates

    [free_db_below_typ b t] holds when every free type variable of [t] is
    below [b]; [free_db_below_term tb vb e] holds when every free type
    variable of [e] is below [tb] and every free term variable below [vb].
    These are the analogues of CoC's [free_db_below] for the two namespaces. *)

Fixpoint free_db_below_typ (bound : nat) (t : typ) : Prop :=
  match t with
  | tvar n => n < bound
  | arrow t1 t2 => free_db_below_typ bound t1 /\ free_db_below_typ bound t2
  | all K t => free_db_below_typ (S bound) t
  | tyabs K t => free_db_below_typ (S bound) t
  | tyapp t1 t2 => free_db_below_typ bound t1 /\ free_db_below_typ bound t2
  | dyn => True
  end.

Fixpoint free_db_below_term (tbound vbound : nat) (e : syntax.term) : Prop :=
  match e with
  | var n => n < vbound
  | abs t e => free_db_below_typ tbound t /\ free_db_below_term tbound (S vbound) e
  | app e1 e2 => free_db_below_term tbound vbound e1 /\ free_db_below_term tbound vbound e2
  | tabs K e => free_db_below_term (S tbound) vbound e
  | tapp e t => free_db_below_term tbound vbound e /\ free_db_below_typ tbound t
  | cast e A B p => free_db_below_term tbound vbound e /\ free_db_below_typ tbound A /\ free_db_below_typ tbound B
  | gnd e G => free_db_below_term tbound vbound e /\ free_db_below_typ tbound G
  | is_gnd e G => free_db_below_term tbound vbound e /\ free_db_below_typ tbound G
  | blame p => True
  | nu K A e => free_db_below_typ tbound A /\ free_db_below_term (S tbound) vbound e
  end.


(** ** Equivalence: de Bruijn types ↔ named type expressions

    [ftyp_expr_equiv tl t e] relates a de Bruijn type [t] to a named type
    expression [e] under the type-variable context [tl].  A [tvar n] matches a
    [ftyp_var x] exactly when [x] first occurs at position [n] in [tl]. *)

Inductive ftyp_expr_equiv : partial_names -> typ -> ftyp_expr -> Prop :=
  | ftyp_eqv_var : forall tl x n,
      first_item x tl n -> ftyp_expr_equiv tl (tvar n) (ftyp_var x)
  | ftyp_eqv_arrow : forall tl t1 t2 e1 e2,
      ftyp_expr_equiv tl t1 e1 -> ftyp_expr_equiv tl t2 e2 ->
      ftyp_expr_equiv tl (arrow t1 t2) (ftyp_arrow e1 e2)
  | ftyp_eqv_all : forall tl K t e x,
      ftyp_expr_equiv (x :: tl) t e ->
      ftyp_expr_equiv tl (all K t) (ftyp_all x K e)
  | ftyp_eqv_tyabs : forall tl K t e x,
      ftyp_expr_equiv (x :: tl) t e ->
      ftyp_expr_equiv tl (tyabs K t) (ftyp_tyabs x K e)
  | ftyp_eqv_tyapp : forall tl t1 t2 e1 e2,
      ftyp_expr_equiv tl t1 e1 -> ftyp_expr_equiv tl t2 e2 ->
      ftyp_expr_equiv tl (tyapp t1 t2) (ftyp_tyapp e1 e2)
  | ftyp_eqv_dyn : forall tl,
      ftyp_expr_equiv tl dyn ftyp_dyn.


(** ** Equivalence: de Bruijn terms ↔ named term expressions

    [fterm_expr_equiv tl vl e ee] relates a de Bruijn term [e] to a named term
    expression [ee] under the type-variable context [tl] and term-variable
    context [vl].  Type subcomponents are related by [ftyp_expr_equiv tl]. *)

Inductive fterm_expr_equiv :
    partial_names -> partial_names -> syntax.term -> fterm_expr -> Prop :=
  | fterm_eqv_var : forall tl vl x n,
      first_item x vl n -> fterm_expr_equiv tl vl (var n) (fterm_var x)
  | fterm_eqv_abs : forall tl vl t e te ee x,
      ftyp_expr_equiv tl t te ->
      fterm_expr_equiv tl (x :: vl) e ee ->
      fterm_expr_equiv tl vl (abs t e) (fterm_abs x te ee)
  | fterm_eqv_app : forall tl vl e1 e2 ee1 ee2,
      fterm_expr_equiv tl vl e1 ee1 -> fterm_expr_equiv tl vl e2 ee2 ->
      fterm_expr_equiv tl vl (app e1 e2) (fterm_app ee1 ee2)
  | fterm_eqv_tabs : forall tl vl K e ee x,
      fterm_expr_equiv (x :: tl) vl e ee ->
      fterm_expr_equiv tl vl (tabs K e) (fterm_tabs x K ee)
  | fterm_eqv_tapp : forall tl vl e t ee te,
      fterm_expr_equiv tl vl e ee -> ftyp_expr_equiv tl t te ->
      fterm_expr_equiv tl vl (tapp e t) (fterm_tapp ee te)
  | fterm_eqv_cast : forall tl vl e A B p ee eA eB,
      fterm_expr_equiv tl vl e ee ->
      ftyp_expr_equiv tl A eA -> ftyp_expr_equiv tl B eB ->
      fterm_expr_equiv tl vl (cast e A B p) (fterm_cast ee eA eB p)
  | fterm_eqv_gnd : forall tl vl e G ee eG,
      fterm_expr_equiv tl vl e ee -> ftyp_expr_equiv tl G eG ->
      fterm_expr_equiv tl vl (gnd e G) (fterm_gnd ee eG)
  | fterm_eqv_is_gnd : forall tl vl e G ee eG,
      fterm_expr_equiv tl vl e ee -> ftyp_expr_equiv tl G eG ->
      fterm_expr_equiv tl vl (is_gnd e G) (fterm_is_gnd ee eG)
  | fterm_eqv_blame : forall tl vl p,
      fterm_expr_equiv tl vl (blame p) (fterm_blame p)
  | fterm_eqv_nu : forall tl vl K A e eA ee x,
      ftyp_expr_equiv tl A eA -> fterm_expr_equiv (x :: tl) vl e ee ->
      fterm_expr_equiv tl vl (nu K A e) (fterm_nu x K eA ee).


(** ** Conversion: de Bruijn → named, reusing hints

    [ftyp_expression_of] / [fterm_expression_of] convert a well-scoped de Bruijn
    type/term into named form, threading source-provided display hints down the
    binder spine.  As on the CoC side, [pick_name] guarantees each chosen name is
    fresh for its context, so the result is capture-free; the equivalence proof is
    carried in the result type. *)

Definition ftyp_expression_of :
  forall (t : typ) (tl : partial_names) (hints : list name),
  name_unique tl ->
  free_db_below_typ (length tl) t ->
  {p : ftyp_expr * list name | ftyp_expr_equiv tl t (fst p)}.
Proof.
  induction t; intros tl hints Huniq Hfree; simpl in Hfree.

  - (* tvar *)
    destruct (nth_error tl n) as [x|] eqn:Hn.
    + exists (ftyp_var x, hints). simpl.
      apply ftyp_eqv_var. apply name_unique_first; auto.
    + exfalso. apply nth_error_None in Hn. lia.

  - (* arrow *)
    destruct Hfree as [H1 H2].
    destruct (IHt1 tl hints Huniq H1) as [[e1 hints1] p1]; simpl in p1.
    destruct (IHt2 tl hints1 Huniq H2) as [[e2 hints2] p2]; simpl in p2.
    exists (ftyp_arrow e1 e2, hints2). simpl.
    apply ftyp_eqv_arrow; auto.

  - (* all *)
    destruct (pick_name hints tl) as [[x Hx] hints'].
    destruct (IHt (x :: tl) hints' (free_var_extension tl Huniq x Hx) Hfree) as [[e hints2] p]; simpl in p.
    exists (ftyp_all x K e, hints2). simpl.
    apply ftyp_eqv_all; auto.

  - (* tyabs *)
    destruct (pick_name hints tl) as [[x Hx] hints'].
    destruct (IHt (x :: tl) hints' (free_var_extension tl Huniq x Hx) Hfree) as [[e hints2] p]; simpl in p.
    exists (ftyp_tyabs x K e, hints2). simpl.
    apply ftyp_eqv_tyabs; auto.

  - (* tyapp *)
    destruct Hfree as [H1 H2].
    destruct (IHt1 tl hints Huniq H1) as [[e1 hints1] p1]; simpl in p1.
    destruct (IHt2 tl hints1 Huniq H2) as [[e2 hints2] p2]; simpl in p2.
    exists (ftyp_tyapp e1 e2, hints2). simpl.
    apply ftyp_eqv_tyapp; auto.

  - (* dyn *)
    exists (ftyp_dyn, hints). simpl.
    apply ftyp_eqv_dyn.
Defined.


Definition fterm_expression_of :
  forall (e : syntax.term) (tl vl : partial_names) (hints : list name),
  name_unique tl -> name_unique vl ->
  free_db_below_term (length tl) (length vl) e ->
  {p : fterm_expr * list name | fterm_expr_equiv tl vl e (fst p)}.
Proof.
  fix go 1.
  intros e; destruct e as [n | ty body | e1 e2 | K body | body ty
    | body A B p | body G | body G | p | K A body];
    intros tl vl hints Htuniq Hvuniq Hfree; simpl in Hfree.

  - (* var *)
    destruct (nth_error vl n) as [x|] eqn:Hn.
    + exists (fterm_var x, hints). simpl.
      apply fterm_eqv_var. apply name_unique_first; auto.
    + exfalso. apply nth_error_None in Hn. lia.

  - (* abs *)
    destruct Hfree as [Ht He].
    destruct (ftyp_expression_of ty tl hints Htuniq Ht) as [[te hints1] pt]; simpl in pt.
    destruct (pick_name hints1 vl) as [[x Hx] hints2].
    destruct (go body tl (x :: vl) hints2 Htuniq (free_var_extension vl Hvuniq x Hx) He) as [[ee hints3] pe]; simpl in pe.
    exists (fterm_abs x te ee, hints3). simpl.
    apply fterm_eqv_abs; auto.

  - (* app *)
    destruct Hfree as [H1 H2].
    destruct (go e1 tl vl hints Htuniq Hvuniq H1) as [[ee1 hints1] p1]; simpl in p1.
    destruct (go e2 tl vl hints1 Htuniq Hvuniq H2) as [[ee2 hints2] p2]; simpl in p2.
    exists (fterm_app ee1 ee2, hints2). simpl.
    apply fterm_eqv_app; auto.

  - (* tabs *)
    destruct (pick_name hints tl) as [[x Hx] hints'].
    destruct (go body (x :: tl) vl hints' (free_var_extension tl Htuniq x Hx) Hvuniq Hfree) as [[ee hints2] pe]; simpl in pe.
    exists (fterm_tabs x K ee, hints2). simpl.
    apply fterm_eqv_tabs; auto.

  - (* tapp *)
    destruct Hfree as [He Ht].
    destruct (go body tl vl hints Htuniq Hvuniq He) as [[ee hints1] pe]; simpl in pe.
    destruct (ftyp_expression_of ty tl hints1 Htuniq Ht) as [[te hints2] pt]; simpl in pt.
    exists (fterm_tapp ee te, hints2). simpl.
    apply fterm_eqv_tapp; auto.

  - (* cast *)
    destruct Hfree as [He [HA HB]].
    destruct (go body tl vl hints Htuniq Hvuniq He) as [[ee hints1] pe]; simpl in pe.
    destruct (ftyp_expression_of A tl hints1 Htuniq HA) as [[eA hints2] pA]; simpl in pA.
    destruct (ftyp_expression_of B tl hints2 Htuniq HB) as [[eB hints3] pB]; simpl in pB.
    exists (fterm_cast ee eA eB p, hints3). simpl.
    apply fterm_eqv_cast; auto.

  - (* gnd *)
    destruct Hfree as [He HG].
    destruct (go body tl vl hints Htuniq Hvuniq He) as [[ee hints1] pe]; simpl in pe.
    destruct (ftyp_expression_of G tl hints1 Htuniq HG) as [[eG hints2] pG]; simpl in pG.
    exists (fterm_gnd ee eG, hints2). simpl.
    apply fterm_eqv_gnd; auto.

  - (* is_gnd *)
    destruct Hfree as [He HG].
    destruct (go body tl vl hints Htuniq Hvuniq He) as [[ee hints1] pe]; simpl in pe.
    destruct (ftyp_expression_of G tl hints1 Htuniq HG) as [[eG hints2] pG]; simpl in pG.
    exists (fterm_is_gnd ee eG, hints2). simpl.
    apply fterm_eqv_is_gnd; auto.

  - (* blame *)
    exists (fterm_blame p, hints). simpl.
    apply fterm_eqv_blame.

  - (* nu *)
    destruct Hfree as [HA He].
    destruct (ftyp_expression_of A tl hints Htuniq HA) as [[eA hints1] pA]; simpl in pA.
    destruct (pick_name hints1 tl) as [[x Hx] hints2].
    destruct (go body (x :: tl) vl hints2 (free_var_extension tl Htuniq x Hx) Hvuniq He) as [[ee hints3] pe]; simpl in pe.
    exists (fterm_nu x K eA ee, hints3). simpl.
    apply fterm_eqv_nu; auto.
Defined.


(** ** Correctness: well-scopedness

    A named expression can only be equivalent to a de Bruijn preimage whose
    free variables lie within the given contexts.  These are the Fω analogues
    of CoC's [equivalent_free_db]. *)

Lemma ftyp_expr_equiv_free_db :
  forall tl t e, ftyp_expr_equiv tl t e -> free_db_below_typ (length tl) t.
Proof.
  induction 1; simpl; auto.
  - (* var *) unfold first_item in H; destruct H as [Hnth _].
    apply nth_error_Some; rewrite Hnth; discriminate.
Qed.

Lemma fterm_expr_equiv_free_db :
  forall tl vl e ee, fterm_expr_equiv tl vl e ee ->
  free_db_below_term (length tl) (length vl) e.
Proof.
  induction 1; simpl;
    repeat match goal with
    | H : ftyp_expr_equiv _ _ _ |- _ =>
        apply ftyp_expr_equiv_free_db in H
    end; auto.
  - (* var *) unfold first_item in H; destruct H as [Hnth _].
    apply nth_error_Some; rewrite Hnth; discriminate.
Qed.


(** ** Correctness: uniqueness of the de Bruijn preimage

    A named expression determines its de Bruijn preimage uniquely under a fixed
    context.  These are the Fω analogues of CoC's [equivalent_unique]; combined
    with the conversion functions above they show the named form is a faithful,
    lossless rendering of the de Bruijn term. *)

Lemma ftyp_expr_equiv_unique :
  forall tl t e, ftyp_expr_equiv tl t e ->
  forall t', ftyp_expr_equiv tl t' e -> t = t'.
Proof.
  induction 1; intros t' Ht'; inversion_clear Ht'; try reflexivity.
  - (* var *) f_equal. apply (first_item_unique x tl n0 H0 n H).
  - (* arrow *) f_equal; [apply IHftyp_expr_equiv1 | apply IHftyp_expr_equiv2]; auto.
  - (* all *) f_equal. apply IHftyp_expr_equiv; auto.
  - (* tyabs *) f_equal. apply IHftyp_expr_equiv; auto.
  - (* tyapp *) f_equal; [apply IHftyp_expr_equiv1 | apply IHftyp_expr_equiv2]; auto.
Qed.

Lemma fterm_expr_equiv_unique :
  forall tl vl e ee, fterm_expr_equiv tl vl e ee ->
  forall e', fterm_expr_equiv tl vl e' ee -> e = e'.
Proof.
  induction 1; intros e' He'; inversion_clear He'; try reflexivity.
  - (* var *) f_equal. apply (first_item_unique x vl n0 H0 n H).
  - (* abs *) f_equal;
      [ apply (ftyp_expr_equiv_unique tl t te H _ H1)
      | apply IHfterm_expr_equiv; auto ].
  - (* app *) f_equal; [apply IHfterm_expr_equiv1 | apply IHfterm_expr_equiv2]; auto.
  - (* tabs *) f_equal. apply IHfterm_expr_equiv; auto.
  - (* tapp *) f_equal;
      [ apply IHfterm_expr_equiv; auto
      | apply (ftyp_expr_equiv_unique tl t te H0 _ H2) ].
  - (* cast *) f_equal;
      [ apply IHfterm_expr_equiv; auto
      | apply (ftyp_expr_equiv_unique tl A eA H0 _ H3)
      | apply (ftyp_expr_equiv_unique tl B eB H1 _ H4) ].
  - (* gnd *) f_equal;
      [ apply IHfterm_expr_equiv; auto
      | apply (ftyp_expr_equiv_unique tl G eG H0 _ H2) ].
  - (* is_gnd *) f_equal;
      [ apply IHfterm_expr_equiv; auto
      | apply (ftyp_expr_equiv_unique tl G eG H0 _ H2) ].
  - (* nu *) f_equal;
      [ apply (ftyp_expr_equiv_unique tl A eA H _ H1)
      | apply IHfterm_expr_equiv; auto ].
Qed.
