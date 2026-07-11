(* Newman's Lemma: a well-founded locally confluent relation is confluent.
   Formalized in the Calculus of Constructions.

   The axioms below are exactly what native inductive definitions would
   provide: [Rstar] (reflexive-transitive closure) and [coherence]
   (joinability) are inductive predicates presented by their constructors,
   induction principle, and inversion principle.  [Hyp1] (well-founded
   induction over [R]) and [Hyp2] (local confluence) are the hypotheses of
   the lemma.  Every proof step is an ordinary [Definition]. *)

Axiom A : Set.
Axiom R : A -> A -> Prop.


(* Reflexive-transitive closure of R, as an inductive predicate:
   constructors, induction principle, and head-step inversion. *)

Inductive Rstar : A -> A -> Prop :=
  | Rstar_refl : forall (x : A), Rstar x x
  | Rstar_step : forall (x y z : A), R x y -> Rstar y z -> Rstar x z.

(* [Rstar_rec], the generated recursor, is the induction principle.  Head-step
   inversion [Rstar_case] exposes the first step, which a fold cannot, so it is
   kept axiomatic. *)
Axiom Rstar_case :
  forall (x y : A) (P : A -> A -> Prop),
  P x x ->
  (forall (u : A), R x u -> Rstar u y -> P x y) ->
  Rstar x y -> P x y.


(* Coherence (joinability): two terms share a common reduct.
   An inductive predicate with one constructor and its eliminator. *)

Inductive coherence : A -> A -> Prop :=
  | coh_intro : forall (x y z : A), Rstar x z -> Rstar y z -> coherence x y.

(* Elimination as inversion (recover the common reduct z), kept axiomatic. *)
Axiom coh_elim :
  forall (x y : A), coherence x y ->
  forall (P : Prop), (forall (z : A), Rstar x z -> Rstar y z -> P) -> P.


(* Main hypotheses of Newman's Lemma:
   Hyp1 = well-founded induction over R
   Hyp2 = local confluence of R *)

Axiom Hyp1 :
  forall (x : A) (P : A -> Prop),
  (forall (y : A), (forall (z : A), R y z -> P z) -> P y) -> P x.

Axiom Hyp2 :
  forall (x y z : A), R x y -> R x z -> coherence y z.


(* The proof *)

Definition Rstar_trans (x y z : A) (h1 : Rstar x y) : Rstar y z -> Rstar x z :=
  Rstar_rec (fun (a b : A) => Rstar b z -> Rstar a z)
    (fun (u : A) (k : Rstar u z) => k)
    (fun (u v w : A) (r : R u v)
         (rec : Rstar w z -> Rstar v z) (k : Rstar w z) =>
     Rstar_step u v z r (rec k))
    x y h1.

Definition Rstar_coherence (x y : A) (h : Rstar x y) : coherence x y :=
  coh_intro x y y h (Rstar_refl y).

Definition coherence_sym (x y : A) (h : coherence x y) : coherence y x :=
  coh_elim x y h (coherence y x)
    (fun (z : A) (h1 : Rstar x z) (h2 : Rstar y z) => coh_intro y x z h2 h1).

(* The diamond-completion step: both one-step reducts of x join, using local
   confluence at x and the inductive hypothesis at each reduct. *)

Definition Diagram (x : A)
  (IH : forall (u : A), R x u ->
        forall (y z : A), Rstar u y -> Rstar u z -> coherence y z)
  (y z u : A) (t1 : R x u) (t2 : Rstar u y)
  (v : A) (u1 : R x v) (u2 : Rstar v z) : coherence y z :=
  coh_elim u v (Hyp2 x u v t1 u1) (coherence y z)
    (fun (z0 : A) (h : Rstar u z0) (h0 : Rstar v z0) =>
     coh_elim y z0 (IH u t1 y z0 t2 h) (coherence y z)
       (fun (z1 : A) (h1 : Rstar y z1) (h2 : Rstar z0 z1) =>
        coh_elim z z1 (IH v u1 z z1 u2 (Rstar_trans v z0 z1 h0 h2))
          (coherence y z)
          (fun (z2 : A) (h3 : Rstar z z2) (h4 : Rstar z1 z2) =>
           coh_intro y z z2 (Rstar_trans y z1 z2 h1 h4) h3))).

Definition caseRxy (x : A)
  (IH : forall (u : A), R x u ->
        forall (y z : A), Rstar u y -> Rstar u z -> coherence y z)
  (y z : A) (h1 : Rstar x y) (h2 : Rstar x z)
  (u : A) (t1 : R x u) (t2 : Rstar u y) : coherence y z :=
  Rstar_case x z (fun (_ : A) (a : A) => coherence y a)
    (coherence_sym x y (Rstar_coherence x y h1))
    (fun (v : A) (u1 : R x v) (u2 : Rstar v z) =>
     Diagram x IH y z u t1 t2 v u1 u2)
    h2.

Definition Ind_proof (x : A)
  (IH : forall (u : A), R x u ->
        forall (y z : A), Rstar u y -> Rstar u z -> coherence y z)
  (y z : A) (h1 : Rstar x y) (h2 : Rstar x z) : coherence y z :=
  Rstar_case x y (fun (_ : A) (a : A) => coherence a z)
    (Rstar_coherence x z h2)
    (fun (u : A) (t1 : R x u) (t2 : Rstar u y) =>
     caseRxy x IH y z h1 h2 u t1 t2)
    h1.

Definition newman (x : A) :
  forall (y z : A), Rstar x y -> Rstar x z -> coherence y z :=
  Hyp1 x
    (fun (a : A) =>
     forall (y z : A), Rstar a y -> Rstar a z -> coherence y z)
    Ind_proof.


(* Check the final theorem statement. *)

Check newman : forall (x y z : A), Rstar x y -> Rstar x z -> coherence y z.
