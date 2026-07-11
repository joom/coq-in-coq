(* Dimension-indexed matrices in the Calculus of Constructions.

   [Mat m n] is the type of m-by-n matrices.  The dimensions are part of the
   type, so [mmul : Mat m n -> Mat n p -> Mat m p] STATICALLY rejects any
   product whose inner dimensions do not agree -- the classic "shape error at
   compile time, not at run time".

   Axioms declare only the inductive kit: [Nat], [Bool], and [Fin] with their
   eliminators, and the matrix family [Mat] with constructor [mat] (build a
   matrix from its entry function [Fin m -> Fin n -> Nat]) and eliminator
   [mat_rec].  Every operation -- entry lookup, addition, multiplication
   (with a summation over an inner index), transpose, identity (with a
   decidable index equality), scaling -- is an ordinary [Definition].
   Entries are [Nat]s to keep the example self-contained.

   Extraction erases dimensions from the target matrix type: [Mat m n]
   becomes [Mat].  Dimension arguments such as [m] and [n] may still remain
   as ordinary term arguments.  The extraction inserts no dynamic shape
   checks; the static shape invariant is what disappears from the target
   type. *)


(* Natural numbers, with eliminator. *)

Axiom Nat : Set.
Axiom NZ : Nat.
Axiom NS : Nat -> Nat.

Axiom Nat_rec : forall (P : Nat -> Set),
  P NZ ->
  (forall (m : Nat), P m -> P (NS m)) ->
  forall (n : Nat), P n.

Definition add (a b : Nat) : Nat :=
  Nat_rec (fun (_ : Nat) => Nat) b (fun (_ : Nat) (r : Nat) => NS r) a.

Definition mul (a b : Nat) : Nat :=
  Nat_rec (fun (_ : Nat) => Nat) NZ (fun (_ : Nat) (r : Nat) => add b r) a.


(* Booleans, with (non-dependent) case analysis. *)

Axiom Bool : Set.
Axiom btrue : Bool.
Axiom bfalse : Bool.
Axiom bool_case : forall (C : Set), C -> C -> Bool -> C.


(* Bounded indices, with induction and successor case analysis. *)

Axiom Fin : Nat -> Set.
Axiom fz : forall (n : Nat), Fin (NS n).
Axiom fs : forall (n : Nat), Fin n -> Fin (NS n).

Axiom fin_case :
  forall (n : Nat) (C : Set), C -> (Fin n -> C) -> Fin (NS n) -> C.

Axiom fin_rec :
  forall (P : forall (n : Nat), Fin n -> Set),
  (forall (n : Nat), P (NS n) (fz n)) ->
  (forall (n : Nat) (i : Fin n), P n i -> P (NS n) (fs n i)) ->
  forall (n : Nat) (i : Fin n), P n i.


(* Decidable equality of indices, by induction on the first index. *)

Definition fin_eq (n : Nat) (i : Fin n) : Fin n -> Bool :=
  fin_rec (fun (m : Nat) (_ : Fin m) => Fin m -> Bool)
    (fun (m : Nat) (j : Fin (NS m)) =>
     fin_case m Bool btrue (fun (_ : Fin m) => bfalse) j)
    (fun (m : Nat) (_ : Fin m) (rec : Fin m -> Bool) (j : Fin (NS m)) =>
     fin_case m Bool bfalse rec j)
    n i.


(* Summation of an indexed family over all of Fin n, by induction on n. *)

Definition sumf (n : Nat) (f : Fin n -> Nat) : Nat :=
  Nat_rec (fun (m : Nat) => (Fin m -> Nat) -> Nat)
    (fun (_ : Fin NZ -> Nat) => NZ)
    (fun (m : Nat) (rec : (Fin m -> Nat) -> Nat) (g : Fin (NS m) -> Nat) =>
     add (g (fz m)) (rec (fun (i : Fin m) => g (fs m i))))
    n f.


(* Matrices: an inductive family over both dimensions, built from and
   eliminated to the entry function. *)

Axiom Mat : Nat -> Nat -> Set.
Axiom mat : forall (m n : Nat), (Fin m -> Fin n -> Nat) -> Mat m n.
Axiom mat_rec :
  forall (m n : Nat) (C : Set),
  ((Fin m -> Fin n -> Nat) -> C) -> Mat m n -> C.

Definition entry (m n : Nat) (a : Mat m n) (i : Fin m) (j : Fin n) : Nat :=
  mat_rec m n Nat (fun (f : Fin m -> Fin n -> Nat) => f i j) a.

Definition madd (m n : Nat) (a b : Mat m n) : Mat m n :=
  mat m n (fun (i : Fin m) (j : Fin n) =>
    add (entry m n a i j) (entry m n b i j)).

Definition mmul (m n p : Nat) (a : Mat m n) (b : Mat n p) : Mat m p :=
  mat m p (fun (i : Fin m) (k : Fin p) =>
    sumf n (fun (j : Fin n) => mul (entry m n a i j) (entry n p b j k))).

Definition trans (m n : Nat) (a : Mat m n) : Mat n m :=
  mat n m (fun (j : Fin n) (i : Fin m) => entry m n a i j).

Definition ident (n : Nat) : Mat n n :=
  mat n n (fun (i j : Fin n) =>
    bool_case Nat (NS NZ) NZ (fin_eq n i j)).

Definition scale (m n : Nat) (s : Nat) (a : Mat m n) : Mat m n :=
  mat m n (fun (i : Fin m) (j : Fin n) => mul s (entry m n a i j)).


(* matrix product: inner dimension n must match, enforced by the types. *)

Check mmul.

Extract fun (m n p : Nat) (a : Mat m n) (b : Mat n p) => mmul m n p a b.


(* the Gram matrix A^T A : always well-formed, of shape n x n. *)

Extract fun (m n : Nat) (a : Mat m n) => mmul n m n (trans m n a) a.


(* a similarity-style triple product P B P^T, shapes chained through. *)

Extract fun (m n : Nat) (p : Mat m n) (b : Mat n n) =>
  mmul m n m (mmul m n n p b) (trans m n p).


(* affine-style update  M := s.(A B) + I  on a square block of size n.
   Only type-checks because every intermediate shape lines up. *)

Extract fun (n : Nat) (s : Nat) (a b : Mat n n) =>
  madd n n (scale n n s (mmul n n n a b)) (ident n).


(* The boundary.  The operations above erased their shape indices for free.
   But the family [Mat] ITSELF, as a function from dimensions to a type, is a
   value in type position with no Fomega image -- extraction emits the dynamic
   type [?] and an internal blame. *)

Extract fun (m n : Nat) => Mat m n.
