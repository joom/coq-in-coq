(* Dimension-indexed matrices in the Calculus of Constructions.

   [Mat m n] is the type of m-by-n matrices.  The dimensions are part of the
   type, so [mmul : Mat m n -> Mat n p -> Mat m p] STATICALLY rejects any
   product whose inner dimensions do not agree -- the classic "shape error at
   compile time, not at run time".

   Extraction erases dimensions from the target matrix type: [Mat m n] becomes
   [Mat].  Dimension arguments such as [m] and [n] may still remain as ordinary
   term arguments because the axiomatized matrix operations take them explicitly.
   The extraction inserts no dynamic shape checks; the static shape invariant is
   what disappears from the target type. *)


Axiom Nat : Set.
Axiom Real : Set.

Axiom Mat : Nat -> Nat -> Set.

Axiom madd  : forall (m n : Nat), Mat m n -> Mat m n -> Mat m n.
Axiom mmul  : forall (m n p : Nat), Mat m n -> Mat n p -> Mat m p.
Axiom trans : forall (m n : Nat), Mat m n -> Mat n m.
Axiom ident : forall (n : Nat), Mat n n.
Axiom scale : forall (m n : Nat), Real -> Mat m n -> Mat m n.


(* matrix product: inner dimension n must match, enforced by the types. *)

Infer fun (m n p : Nat) (a : Mat m n) (b : Mat n p) => mmul m n p a b.

Extract fun (m n p : Nat) (a : Mat m n) (b : Mat n p) => mmul m n p a b.


(* the Gram matrix A^T A : always well-formed, of shape n x n. *)

Extract fun (m n : Nat) (a : Mat m n) => mmul n m n (trans m n a) a.


(* a similarity-style triple product P B P^T, shapes chained through. *)

Extract fun (m n : Nat) (p : Mat m n) (b : Mat n n) =>
  mmul m n m (mmul m n n p b) (trans m n p).


(* affine-style update  M := s.(A B) + I  on a square block of size n.
   Only type-checks because every intermediate shape lines up. *)

Extract fun (n : Nat) (s : Real) (a b : Mat n n) =>
  madd n n (scale n n s (mmul n n n a b)) (ident n).


(* The boundary.  The operations above erased their shape indices for free.
   But the family [Mat] ITSELF, as a function from dimensions to a type, is a
   value in type position with no Fomega image -- extraction emits the dynamic
   type [?] and an internal blame. *)

Extract fun (m n : Nat) => Mat m n.
