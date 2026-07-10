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


(** [extract_well_typed] (target well-typedness of the extraction) is proved
    downstream in [well_typed.v]: its [app]/large case needs
    [extract_typ_tsubst_coc_equiv], which in turn relies on the type-namespace
    substitution machinery of [substitution_simulation.v] (downstream of this
    file).  See [well_typed.v]. *)


(** ** Blame freedom for [extract] *)
Lemma extracted_safe : forall e t T (H: has_type e t T) p,
  syntax.lbl_id p >= 2 -> safety.safe_pos_neg p (extract e t T H).
Proof.
  fix IH 4.
  intros e t T H p Hge.
  destruct H as [ e0 w0 | e0 w0 | e0 w0 v T0 il
                | e0 T0 s1 HT M U s2 HU HM | e0 v0 V0 Hv u Ur Hu
                | e0 T0 s1 HT U s2 HU | e0 t0 U0 V0 Htu Hconv s0 HV ]; cbn [extract].
  - apply safe_dyn_token.
  - apply safe_dyn_token.
  - destruct (is_large_dec e0 T0); (apply safe_coerce_external; [exact Hge |]).
    + apply safety.spn_blame. intro Heq. rewrite <- Heq in Hge.
      unfold internal_label in Hge. simpl in Hge. lia.
    + apply safety.spn_var.
  - destruct (is_large_dec e0 T0).
    + apply safety.spn_tabs. exact (IH _ _ _ HM p Hge).
    + apply safety.spn_abs. exact (IH _ _ _ HM p Hge).
  - destruct (is_large_dec e0 V0).
    + apply safety.spn_tapp. exact (IH _ _ _ Hu p Hge).
    + apply safe_coerce_external; [exact Hge |].
      apply safety.spn_app; [exact (IH _ _ _ Hu p Hge) | exact (IH _ _ _ Hv p Hge)].
  - apply safe_dyn_token.
  - apply safe_coerce_external; [exact Hge | exact (IH _ _ _ Htu p Hge)].
Qed.

(** The extraction never reduces to blame on an external label (its own casts use the internal label). *)
Theorem extraction_blame_free :
  forall e t T (H: has_type e t T),
  forall p, syntax.lbl_id p >= 2 ->
  ~ semantics.star (extract e t T H) (syntax.blame p).
Proof.
  intros e t T H p Hge.
  exact (blame.blame_theorem _ _ Hge (extracted_safe e t T H p Hge)).
Qed.


(** ** Simulation infrastructure for [extract] *)
