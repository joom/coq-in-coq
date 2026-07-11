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
From Extraction Require Import optimism.


(** Syntactic specialization of [cast_instantiation_sim] to extracted type
    annotations.  [C] and [A] need only normalize; this statement deliberately
    makes no source-typing or contextual-approximation claim. *)
Theorem extraction_instantiation_sim :
  forall e M s A B (H: has_type e M (terms.prod (sort_term s) A)) C p
    (snC: strongly_normalizing C) (snA: strongly_normalizing A),
  simulation.sim
    (syntax.cast
       (syntax.tapp (extract e M _ H) (extract_typ e C snC))
       (infrastructure.tsubst (extract_typ e C snC) 0
          (extract_typ (sort_term s :: e) A snA)) B p)
    (syntax.cast
       (syntax.tapp (extract e M _ H) syntax.dyn)
       (infrastructure.tsubst syntax.dyn 0
          (extract_typ (sort_term s :: e) A snA)) B p).
Proof.
  intros. apply simulation.cast_instantiation_sim.
Qed.
