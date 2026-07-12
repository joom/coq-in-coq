Require Extraction.
Extraction Language OCaml.

(* Newman's lemma lives entirely in Prop: everything is erased by extraction.
   We port the statements; the proof content is irrelevant to the extraction
   question, so we exhibit the erasure on the inductive predicates and a
   representative Prop-level definition. *)

Section Newman.
Variable A : Set.
Variable R : A -> A -> Prop.

Inductive Rstar : A -> A -> Prop :=
| Rstar_refl : forall x, Rstar x x
| Rstar_step : forall x y z, R x y -> Rstar y z -> Rstar x z.

Inductive coherence : A -> A -> Prop :=
| coh_intro : forall x y z, Rstar x z -> Rstar y z -> coherence x y.

Definition coherence_refl (x : A) : coherence x x :=
  coh_intro x x x (Rstar_refl x) (Rstar_refl x).

Definition coherence_sym (x y : A) (h : coherence x y) : coherence y x :=
  match h in coherence u v return coherence v u with
  | coh_intro x0 y0 z p q => coh_intro y0 x0 z q p
  end.

End Newman.

Extraction "ex_newman.ml" coherence_refl coherence_sym.
