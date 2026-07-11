(** * Proofs for optimistic CoC-to-System-F_omega extraction

    Naming conventions:
    - [_L] suffix: "raw/pre-normalization" — the function operates on its argument
      directly; the unsuffixed version normalizes first (e.g. [extract_typ_L] vs
      [extract_typ = extract_typ_L ∘ nf]).  [fo_typ_L] likewise describes the
      raw, pre-normalization syntax inspected by [extract_typ_L].
    - [_gen] suffix: "generalized" — the lemma is stated with extra generality.
      [extract_typ_L_swap_gen] generalizes over context depth; [sim_star_tapp_gen]
      generalizes over both type arguments. *)

(** This file is now a compatibility facade: all content has been split into
    topically-named files below. [From Extraction Require Import proofs.]
    continues to expose every definition/lemma unqualified, as before. *)

From Extraction Require Export common.
From Extraction Require Export source_facts.
From Extraction Require Export translation.
From Extraction Require Export context_facts.
From Extraction Require Export type_extraction_facts.
From Extraction Require Export typing_proof.
From Extraction Require Export simulation_facts.
From Extraction Require Export derivation_independence.
From Extraction Require Export substitution_simulation.
From Extraction Require Export reduction_simulation.
From Extraction Require Export optimism.
From Extraction Require Export instantiation.
From Extraction Require Export well_typed.
