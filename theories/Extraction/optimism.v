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
From Extraction Require Import translation.

Import terms.
Import CoC.typing.
Import extraction.

From Extraction Require Import context_facts.
From Extraction Require Import type_extraction_facts.
From Extraction Require Import typing_proof.
From Extraction Require Import simulation_facts.
From Extraction Require Import derivation_independence.
From Extraction Require Import substitution_simulation.
From Extraction Require Import reduction_simulation.


Fixpoint fo_typ_L (e: environment) (t: terms.term) : Prop :=
  match t with
  | sort_term _ => False
  | terms.var n => type_binding e n = true
  | terms.prod T U =>
      if classifier T then fo_typ_L (T :: e) U
      else fo_typ_L e T /\ fo_typ_L (T :: e) U
  | terms.lam T M => fo_typ_L (T :: e) M
  | terms.app u v =>
      type_expr e u = true /\ fo_typ_L e u /\
      (if type_expr e v then fo_typ_L e v else True)
  end.

(** Optimism: a source type in the [fo_typ_L] fragment extracts (via [extract_typ_L]) to a [dyn]-free target type. *)
Theorem extract_typ_L_dyn_free : forall t e,
  fo_typ_L e t -> typ_dyn_free (extract_typ_L e t).
Proof.
  intros t. induction t; intros e Hfo; simpl in *.
  - contradiction.
  - rewrite Hfo. exact I.
  - destruct (classifier t1); apply IHt2; exact Hfo.
  - destruct Hfo as [Hte1 [Hfo1 Hrest]]. rewrite Hte1.
    destruct (type_expr e t2).
    + split; [apply IHt1 | apply IHt2]; assumption.
    + apply IHt1. exact Hfo1.
  - destruct (classifier t1).
    + apply IHt2. exact Hfo.
    + destruct Hfo as [Hfo1 Hfo2]. split; [apply IHt1 | apply IHt2]; assumption.
Qed.

(** Converse: if the target type is [dyn]-free, then the source type lies in
    [fo_typ_L].  Together with [extract_typ_L_dyn_free] this gives an exact
    characterization of when this extractor produces [dyn]. *)
Theorem extract_typ_L_dyn_free_inv : forall t e,
  typ_dyn_free (extract_typ_L e t) -> fo_typ_L e t.
Proof.
  intros t. induction t; intros e Hdf; simpl in *.
  - (* sort *) exact Hdf.
  - (* var *) destruct (type_binding e n); simpl in *;
      [reflexivity | contradiction].
  - (* lam *) destruct (classifier t1); simpl in *;
      apply IHt2; exact Hdf.
  - (* app *)
    destruct (type_expr e t1) eqn:Hte1; simpl in *.
    + destruct (type_expr e t2) eqn:Hte2; simpl in *.
      * destruct Hdf as [Hdf1 Hdf2].
        split; [| split]; [reflexivity | apply IHt1; exact Hdf1 | apply IHt2; exact Hdf2].
      * split; [| split]; [reflexivity | apply IHt1; exact Hdf | exact I].
    + contradiction.
  - (* prod *)
    destruct (classifier t1); simpl in *.
    + apply IHt2. exact Hdf.
    + destruct Hdf as [Hdf1 Hdf2].
      split; [apply IHt1; exact Hdf1 | apply IHt2; exact Hdf2].
Qed.

(** Exact characterization: [extract_typ_L] is [dyn]-free iff the source type
    lies in [fo_typ_L]. *)
Theorem extract_typ_L_dyn_free_iff : forall t e,
  typ_dyn_free (extract_typ_L e t) <-> fo_typ_L e t.
Proof.
  intros t e. split.
  - apply extract_typ_L_dyn_free_inv.
  - apply extract_typ_L_dyn_free.
Qed.

(** ... hence the final (normalize-then-extract) type extraction is [dyn]-free iff
    the normal form lies in [fo_typ_L]. *)
Theorem extract_typ_dyn_free : forall e t sn,
  fo_typ_L e (nf t sn) -> typ_dyn_free (extract_typ e t sn).
Proof. intros e t sn Hfo. unfold extract_typ. apply extract_typ_L_dyn_free. exact Hfo. Qed.

Theorem extract_typ_dyn_free_iff : forall e t sn,
  typ_dyn_free (extract_typ e t sn) <-> fo_typ_L e (nf t sn).
Proof. intros e t sn. unfold extract_typ. apply extract_typ_L_dyn_free_iff. Qed.

