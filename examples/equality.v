(* Propositional equality and transport in the Calculus of Constructions.

   [Eq A x y] is Leibniz equality; [refl] proves [x = x]; [eq_rect] is
   transport: a proof that [x = y] lets us move a [P x] to a [P y].  In a
   dependently-typed language transport is the *coercion* mechanism -- it is
   how one crosses between two types that are provably equal.

   The current extractor does not implement Coq-style Prop erasure.  Instead,
   the equality endpoints [x] and [y] are erased from the target type
   [Eq A x y], so equality appears at the simpler target type [Eq A].
   However, proof arguments such as [h] and proof constants such as [eq_rect]
   remain as ordinary term-level components of the extracted program.  This
   example therefore demonstrates index erasure from types, not proof erasure.
   A future proof-erasing optimization could eliminate these residual proof
   terms.

   The axioms are exactly the inductive kit of equality: the family [Eq],
   its constructor [refl], and its induction principle [eq_rect]. *)


Axiom Eq : forall (A : Set), A -> A -> Prop.
Axiom refl : forall (A : Set) (x : A), Eq A x x.

(* transport / Leibniz substitution: the induction principle *)
Axiom eq_rect :
  forall (A : Set) (x : A) (P : A -> Prop),
  P x -> forall (y : A), Eq A x y -> P y.


(* symmetry: from x = y build y = x, by transporting refl along the proof. *)

Infer fun (A : Set) (x y : A) (h : Eq A x y) =>
  eq_rect A x (fun (z : A) => Eq A z x) (refl A x) y h.

Extract fun (A : Set) (x y : A) (h : Eq A x y) =>
  eq_rect A x (fun (z : A) => Eq A z x) (refl A x) y h.


(* transitivity: chain x = y and y = z into x = z. *)

Extract fun (A : Set) (x y z : A) (hxy : Eq A x y) (hyz : Eq A y z) =>
  eq_rect A y (fun (w : A) => Eq A x w) hxy z hyz.


(* congruence: equal inputs give equal outputs of any function. *)

Extract fun (A B : Set) (f : A -> B) (x y : A) (h : Eq A x y) =>
  eq_rect A x (fun (z : A) => Eq B (f x) (f z)) (refl B (f x)) y h.


(* Transport a value across a proven type-family equality.
   Given p : P x and a proof x = y, obtain a P y.  In the extracted target
   the dependent index disappears from the type of P, but the proof argument
   h and the eliminator eq_rect remain as ordinary residual terms. *)

Extract fun (A : Set) (P : A -> Prop) (x y : A) (h : Eq A x y) (p : P x) =>
  eq_rect A x P p y h.
