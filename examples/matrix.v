(* Dimension-indexed matrices in the Calculus of Constructions.

   [Mat m n] is the type of m-by-n matrices.  The dimensions are part of the
   type, so [mmul : Mat m n -> Mat n p -> Mat m p] STATICALLY rejects any
   product whose inner dimensions do not agree -- the classic "shape error at
   compile time, not at run time".

   Axioms declare only the inductive kit: [nat], [bool], and [Fin] with their
   eliminators, and the matrix family [Mat] with constructor [mat] (build a
   matrix from its entry function [Fin m -> Fin n -> nat]) and eliminator
   [mat_rec].  Every operation -- entry lookup, addition, multiplication
   (with a summation over an inner index), transpose, identity (with a
   decidable index equality), scaling -- is an ordinary [Definition].
   Entries are [nat]s to keep the example self-contained.

   Extraction erases dimensions from the target matrix type: [Mat m n]
   becomes [Mat].  Dimension arguments such as [m] and [n] may still remain
   as ordinary term arguments.  The extraction inserts no dynamic shape
   checks; the static shape invariant is what disappears from the target
   type. *)


(* Natural numbers, with eliminator. *)

(* Like [stlc.v], this file is kept axiomatic.  [nat], [bool], [Fin], and [Mat]
   are all genuine inductives and DO encode via [Inductive], but the heavy
   operations here -- [mmul] nests [entry] (a [Mat_rec]) inside [sumf] inside
   [mat] -- substitute the [Fin]/[Mat] encodings deeply, and the extractor's
   normalizer blows up (minutes per [Extract]).  So the encoding is impractical
   here, and the inductive kit stays axiomatic.  [sumf] additionally needs the
   value-dependent [nat_rec] (large elimination), which no impredicative
   encoding provides at all. *)

Axiom nat : Set.
Axiom O : nat.
Axiom S : nat -> nat.

Axiom nat_rec : forall (P : nat -> Set),
  P O ->
  (forall (m : nat), P m -> P (S m)) ->
  forall (n : nat), P n.

Definition add (a b : nat) : nat :=
  nat_rec (fun (_ : nat) => nat) b (fun (_ : nat) (r : nat) => S r) a.

Definition mul (a b : nat) : nat :=
  nat_rec (fun (_ : nat) => nat) O (fun (_ : nat) (r : nat) => add b r) a.


(* Booleans, with (non-dependent) case analysis. *)

Axiom bool : Set.
Axiom true : bool.
Axiom false : bool.
Axiom bool_rec : forall (C : Set), C -> C -> bool -> C.


(* Bounded indices, with induction and successor case analysis. *)

Axiom Fin : nat -> Set.
Axiom F1 : forall (n : nat), Fin (S n).
Axiom FS : forall (n : nat), Fin n -> Fin (S n).

Axiom fin_case :
  forall (n : nat) (C : Set), C -> (Fin n -> C) -> Fin (S n) -> C.

Axiom fin_rec :
  forall (P : forall (n : nat), Fin n -> Set),
  (forall (n : nat), P (S n) (F1 n)) ->
  (forall (n : nat) (i : Fin n), P n i -> P (S n) (FS n i)) ->
  forall (n : nat) (i : Fin n), P n i.


(* Decidable equality of indices, by induction on the first index. *)

Definition fin_eq (n : nat) (i : Fin n) : Fin n -> bool :=
  fin_rec (fun (m : nat) (_ : Fin m) => Fin m -> bool)
    (fun (m : nat) (j : Fin (S m)) =>
     fin_case m bool true (fun (_ : Fin m) => false) j)
    (fun (m : nat) (_ : Fin m) (rec : Fin m -> bool) (j : Fin (S m)) =>
     fin_case m bool false rec j)
    n i.


(* Summation of an indexed family over all of Fin n, by induction on n. *)

Definition sumf (n : nat) (f : Fin n -> nat) : nat :=
  nat_rec (fun (m : nat) => (Fin m -> nat) -> nat)
    (fun (_ : Fin O -> nat) => O)
    (fun (m : nat) (rec : (Fin m -> nat) -> nat) (g : Fin (S m) -> nat) =>
     add (g (F1 m)) (rec (fun (i : Fin m) => g (FS m i))))
    n f.


(* Matrices: an inductive family over both dimensions, built from and
   eliminated to the entry function. *)

Axiom Mat : nat -> nat -> Set.
Axiom mat : forall (m n : nat), (Fin m -> Fin n -> nat) -> Mat m n.
Axiom mat_rec :
  forall (m n : nat) (C : Set),
  ((Fin m -> Fin n -> nat) -> C) -> Mat m n -> C.

Definition entry (m n : nat) (a : Mat m n) (i : Fin m) (j : Fin n) : nat :=
  mat_rec m n nat (fun (f : Fin m -> Fin n -> nat) => f i j) a.

Definition madd (m n : nat) (a b : Mat m n) : Mat m n :=
  mat m n (fun (i : Fin m) (j : Fin n) =>
    add (entry m n a i j) (entry m n b i j)).

Definition mmul (m n p : nat) (a : Mat m n) (b : Mat n p) : Mat m p :=
  mat m p (fun (i : Fin m) (k : Fin p) =>
    sumf n (fun (j : Fin n) => mul (entry m n a i j) (entry n p b j k))).

Definition trans (m n : nat) (a : Mat m n) : Mat n m :=
  mat n m (fun (j : Fin n) (i : Fin m) => entry m n a i j).

Definition ident (n : nat) : Mat n n :=
  mat n n (fun (i j : Fin n) =>
    bool_rec nat (S O) O (fin_eq n i j)).

Definition scale (m n : nat) (s : nat) (a : Mat m n) : Mat m n :=
  mat m n (fun (i : Fin m) (j : Fin n) => mul s (entry m n a i j)).


(* matrix product: inner dimension n must match, enforced by the types. *)

Check mmul.

Extract fun (m n p : nat) (a : Mat m n) (b : Mat n p) => mmul m n p a b.


(* the Gram matrix A^T A : always well-formed, of shape n x n. *)

Extract fun (m n : nat) (a : Mat m n) => mmul n m n (trans m n a) a.


(* a similarity-style triple product P B P^T, shapes chained through. *)

Extract fun (m n : nat) (p : Mat m n) (b : Mat n n) =>
  mmul m n m (mmul m n n p b) (trans m n p).


(* affine-style update  M := s.(A B) + I  on a square block of size n.
   Only type-checks because every intermediate shape lines up. *)

Extract fun (n : nat) (s : nat) (a b : Mat n n) =>
  madd n n (scale n n s (mmul n n n a b)) (ident n).


(* The boundary.  The operations above erased their shape indices for free.
   But the family [Mat] ITSELF, as a function from dimensions to a type, is a
   value in type position with no Fomega image -- extraction emits the dynamic
   type [?] and an internal blame. *)

Extract fun (m n : nat) => Mat m n.
