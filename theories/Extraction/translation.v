(** * The CoC-to-System-F_omega extraction translation

    The object being studied: kind/type/context/term extraction, plus
    witness-independence ([_pi]) for each. *)

From Stdlib Require Import Arith Lia List Relations Bool Program.Equality.
Import ListNotations.
From CoC Require terms.
From CoC Require typing.
From CoC Require Import confluence.
From CoC Require Import inference.
From CoC Require Import strong_normalization.
From CoC Require Import decidable_conversion.
From BlameFOmega Require syntax infrastructure semantics typing subtyping safety blame subtyping_safety simulation.
From Extraction Require extraction.
From Extraction Require Import common.
From Extraction Require Import source_facts.

Import terms.
Import CoC.typing.
Import extraction.

(** Kind extraction: the raw [extract_kind_L] applied to the argument's normal form. *)
Definition extract_kind (T: terms.term)
  (sn: strongly_normalizing T) : syntax.kind :=
  extract_kind_L (nf T sn).

(** Independent of the SN witness. *)
Lemma extract_kind_pi : forall T sn1 sn2, extract_kind T sn1 = extract_kind T sn2.
Proof. intros T sn1 sn2. unfold extract_kind. rewrite (nf_pi T sn1 sn2). reflexivity. Qed.

(** Reduction-stable de Bruijn compression (is_large-based namespace indices
    using [is_large_dec] instead of [classifier]; total, no well-formedness needed
    since [is_large_dec] is total). *)
(** Compress a source de Bruijn index into the target type namespace, skipping term-level binders. *)
Fixpoint type_index (e: environment) (n: nat) : nat :=
  match e, n with
  | nil, _ => 0
  | _ :: _, 0 => 0
  | T :: e', S n' => if is_large_dec e' T then S (type_index e' n') else type_index e' n'
  end.

(** Compress a source de Bruijn index into the target term namespace, skipping type-level binders. *)
Fixpoint term_index (e: environment) (n: nat) : nat :=
  match e, n with
  | nil, _ => 0
  | _ :: _, 0 => 0
  | T :: e', S n' => if is_large_dec e' T then term_index e' n' else S (term_index e' n')
  end.


(** ** Type extraction ([extract_typ_L])

    Context bindings are classified with the semantic, conversion-invariant
    [is_large_dec] (via [type_binding]/[type_index]), not the syntactic
    [classifier] (which is not stable under conversion of the context).
    Combined with [nf] for the type's own structure, the result is fully
    conversion-invariant -- at the cost of being typing-dependent (it calls the
    type checker), so it no longer reduces under [reflexivity]. *)

(** A context binding denotes a type-level (large) object when its declared type,
    in its own suffix context, is a kind. *)
Definition type_binding (e: environment) (n: nat) : bool :=
  match nth_error e n with
  | Some u => if is_large_dec (skipn (S n) e) u then true else false
  | None => false
  end.

(** Whether a source term occupies the type-level namespace. This is a
    one-way dependency of [extract_typ_L], so it is defined separately rather
    than as an unnecessary mutual fixpoint. *)
Fixpoint type_expr (e: environment) (t: terms.term) : bool :=
  match t with
  | sort_term _ => true
  | terms.var n => type_binding e n
  | terms.prod _ _ => true
  | terms.lam T M => type_expr (T :: e) M
  | terms.app u _ => type_expr e u
  end.

(** Raw is_large-based type extraction (assumes an already-normal argument); [extract_typ] normalizes first. *)
Fixpoint extract_typ_L (e: environment) (t: terms.term) : syntax.typ :=
  match t with
  | sort_term _ => syntax.dyn
  | terms.var n =>
      if type_binding e n then syntax.tvar (type_index e n) else syntax.dyn
  | terms.prod T U =>
      if classifier T
      then syntax.all (extract_kind_L T) (extract_typ_L (T :: e) U)
      else syntax.arrow (extract_typ_L e T) (extract_typ_L (T :: e) U)
  | terms.lam T M =>
      if classifier T
      then syntax.tyabs (extract_kind_L T) (extract_typ_L (T :: e) M)
      else extract_typ_L (T :: e) M
  | terms.app u v =>
      if type_expr e u
      then if type_expr e v
           then syntax.tyapp (extract_typ_L e u) (extract_typ_L e v)
           else extract_typ_L e u
      else syntax.dyn
  end.

(** ** Term extraction ([extract])

    Same shape as the [_rs] versions but types go through the [is_large]-based
    [extract_typ_L] (so classification is context-conversion-invariant) composed
    with [nf] (so it is also structure-conversion-invariant). *)
Definition extract_typ (e: environment) (T: terms.term)
  (sn: strongly_normalizing T) : syntax.typ :=
  extract_typ_L e (nf T sn).

(** Extracted type of the [n]-th term binding of a context. *)
Fixpoint extract_lookup_type (e: environment) {struct e}
  : well_formed e -> nat -> syntax.typ :=
  match e with
  | nil => fun _ _ => syntax.dyn
  | T :: e' => fun w n =>
      match n with
      | 0 => extract_typ e' T (sn_of_binding T e' w)
      | S n' =>
          if is_large_dec e' T
          then infrastructure.tlift 1 0 (extract_lookup_type e' (wf_tail T e' w) n')
          else extract_lookup_type e' (wf_tail T e' w) n'
      end
  end.

(** Context extraction into Fω's separate term/type namespaces (via [is_large_dec]). *)
Fixpoint extract_ctx (e: environment) (w: well_formed e) {struct e}
  : typing.context :=
  match e return well_formed e -> typing.context with
  | nil => fun _ => nil
  | T :: e' => fun w =>
      if is_large_dec e' T
      then typing.has_kind (extract_kind T (sn_of_binding T e' w))
             :: extract_ctx e' (wf_tail T e' w)
      else typing.has_type (extract_typ e' T (sn_of_binding T e' w))
             :: extract_ctx e' (wf_tail T e' w)
  end w.


(** The final term extraction: derivation-recursive; every type/kind goes through the
    context-conversion-invariant [extract_typ]/[extract_lookup_type]. *)
Fixpoint extract (e: typing.environment) (t T: terms.term)
  (H: has_type e t T) {struct H} : syntax.term :=
  match H with
  | type_prop _ _ => dyn_token
  | type_set _ _ => dyn_token
  | type_var e0 w v T0 il =>
      let snT0 := sn_of_type e0 (terms.var v) T0
                    (typing.type_var e0 (w) v T0 il) in
      if is_large_dec e0 T0
      then coerce (syntax.blame internal_label) syntax.dyn (extract_typ e0 T0 snT0)
      else coerce (syntax.var (term_index e0 v))
             (extract_lookup_type e0 (w) v)
             (extract_typ e0 T0 snT0)
  | type_abs e0 T0 s1 HT M U s2 HU HM =>
      let snT0 := strong_normalization e0 T0 (sort_term s1)
                    (HT) in
      if is_large_dec e0 T0
      then syntax.tabs (extract_kind T0 snT0) (extract _ _ _ HM)
      else syntax.abs (extract_typ e0 T0 snT0) (extract _ _ _ HM)
  | type_app e0 v0 V0 Hv u Ur Hu =>
      let snv0 := strong_normalization e0 v0 V0 (Hv) in
      let snUr := sn_of_prod_cod e0 u V0 Ur
                    (Hu) in
      let snSub := sn_of_type e0 (terms.app u v0) (terms.subst v0 Ur)
                     (typing.type_app e0 v0 V0 (Hv)
                        u Ur (Hu)) in
      if is_large_dec e0 V0
      then
        (* Large (type) argument: a target type application.  Its natural type
           [tsubst (extract v0) 0 (extract (V0::e0) Ur)] is [ty_equiv] to the
           expected [extract (subst v0 Ur)] (see [extract_typ_tsubst_coc_equiv]),
           so no runtime [coerce] is needed -- the target [typing_conv] rule
           mediates this static Fω definitional equality. *)
        syntax.tapp (extract _ _ _ Hu) (extract_typ e0 v0 snv0)
      else
        coerce (syntax.app (extract _ _ _ Hu) (extract _ _ _ Hv))
               (extract_typ (V0 :: e0) Ur snUr)
               (extract_typ e0 (terms.subst v0 Ur) snSub)
  | type_prod _ _ _ _ _ _ _ => dyn_token
  | type_conv e0 t0 U0 V0 Htu Hconv s HV =>
      let snU0 := sn_of_type e0 t0 U0 (Htu) in
      let snV0 := strong_normalization e0 V0 (sort_term s)
                    (HV) in
      coerce (extract _ _ _ Htu) (extract_typ e0 U0 snU0) (extract_typ e0 V0 snV0)
  end.

(** ** Witness-independence of type/context extraction *)

(** [extract_typ] is independent of the SN witness. *)
Lemma extract_typ_pi : forall e T sn1 sn2, extract_typ e T sn1 = extract_typ e T sn2.
Proof. intros e T sn1 sn2. unfold extract_typ. rewrite (nf_pi T sn1 sn2). reflexivity. Qed.

(** [extract_lookup_type] is independent of the well-formedness witness. *)
Lemma extract_lookup_type_pi : forall e w1 w2 n,
  extract_lookup_type e w1 n = extract_lookup_type e w2 n.
Proof.
  induction e as [|T e' IH]; intros w1 w2 n; simpl.
  - reflexivity.
  - destruct n.
    + apply extract_typ_pi.
    + destruct (is_large_dec e' T); [f_equal|]; apply IH.
Qed.

(** [extract_ctx] is independent of the well-formedness witness. *)
Lemma extract_ctx_pi : forall e w1 w2, extract_ctx e w1 = extract_ctx e w2.
Proof.
  induction e as [|T e' IH]; intros w1 w2; simpl.
  - reflexivity.
  - destruct (is_large_dec e' T).
    + f_equal; [ f_equal; apply extract_kind_pi | apply IH ].
    + f_equal; [ f_equal; apply extract_typ_pi | apply IH ].
Qed.
