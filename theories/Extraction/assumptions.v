(** Assumption audit for the headline results.

    Compiling this file prints, for each main theorem, the axioms it depends on.
    The audited core theorem set should use at most [eq_rect_eq], introduced by
    dependent case analysis. Name-rendering theorems, which use primitive names,
    are outside this file. Any other axiom in this listed set is a regression;
    [check-assumptions.sh] also scans all theory sources for proof holes and
    axiom declarations. *)

From Extraction Require Import proofs.
From BlameFOmega Require Import blame ty_confluence typing_metatheory progress.
From BlameFOmega Require Import subtyping_safety.
From BlameFOmega Require Import preservation.
From BlameFOmega Require Import nonnormalization.

(* Extraction metatheory *)
Print Assumptions extract_well_typed.
Print Assumptions extract_typ_wf_sort.  (* kind-regularity: fully axiom-free *)
Print Assumptions extract_typ_tsubst_coc_equiv.  (* large-App conversion lemma *)
Print Assumptions extracted_safe.
Print Assumptions typing_coerce.
Print Assumptions extract_reduces_once.
Print Assumptions extract_reduces.
Print Assumptions extract_deriv_indep.
Print Assumptions extraction_blame_free.
Print Assumptions extraction_instantiation_sim.
Print Assumptions extract_typ_dyn_free.
Print Assumptions extract_typ_dyn_free_iff.

(* Target metatheory *)
Print Assumptions blame_theorem.
Print Assumptions semantics.step_deterministic.

(* Target type-level confluence and typing structural lemmas *)
Print Assumptions ty_star_confluent.
Print Assumptions ty_equiv_church_rosser.
Print Assumptions ty_equiv_arrow_inv.
Print Assumptions ty_equiv_all_inv.
Print Assumptions typing_weaken_term.
Print Assumptions typing_weaken_kind.
Print Assumptions typing_weaken_def.
Print Assumptions typing_weaken_prefix.
Print Assumptions typing_subst.
Print Assumptions canonical_arrow.
Print Assumptions canonical_all.
Print Assumptions ty_step_tsubst.
Print Assumptions ty_equiv_tsubst.
Print Assumptions typing_tsubst.
Print Assumptions wf_typ_tsubst.
Print Assumptions compat_tsubst.
Print Assumptions ground_tsubst.

(* Target type safety *)
Print Assumptions progress.

(* Target preservation for the unified kind-regular typing judgment and the
   full [step] relation, including the two [nu] binder-commuting rules. *)
Print Assumptions preservation.
Print Assumptions preservation_star.
Print Assumptions typing_regular.
Print Assumptions typing_annotations_regular.
Print Assumptions typing_swap_type_def.
Print Assumptions typing_swap_kind_def.

(* Subtyping / blame safety corollary *)
Print Assumptions subtyping_theorem.
Print Assumptions subtyping_cast_blame_free.
Print Assumptions blame_theorem_pos.
Print Assumptions typing_does_not_imply_strong_normalization.
