(* Bounds-checked array access in the Calculus of Constructions.

   [Fin n] is the type of natural numbers strictly below [n] -- a static
   proof that an index is in range.  [vnth] indexes a [Vec A n] with a
   [Fin n], so an out-of-bounds access is a *type* error, not a runtime one.

   The interesting part is what survives extraction to System Fomega + blame:
   the dependency on the length index [n] is erased from target types.
   [Vec A n] becomes the plain polymorphic type [Vec A], and [Fin n] becomes
   [Fin].  The term [n] itself remains when the source program passes it to
   [vnth], and the value [i : Fin n] remains because it is the actual index.
   What the target forgets is the invariant tying [i] to [n].  The verified
   extraction guarantees the erased program still simulates the source. *)


(* Natural numbers *)

Axiom Nat : Set.
Axiom NZ : Nat.
Axiom NS : Nat -> Nat.


(* Length-indexed vectors *)

Axiom Vec : Set -> Nat -> Set.
Axiom vnil : forall (A : Set), Vec A NZ.
Axiom vcons : forall (A : Set) (n : Nat), A -> Vec A n -> Vec A (NS n).


(* Bounded indices: Fin n has exactly n inhabitants (0, .., n-1) *)

Axiom Fin : Nat -> Set.
Axiom fz : forall (n : Nat), Fin (NS n).
Axiom fs : forall (n : Nat), Fin n -> Fin (NS n).


(* Total, bounds-checked lookup: the Fin n witness rules out overflow. *)

Axiom vnth : forall (A : Set) (n : Nat), Vec A n -> Fin n -> A.


(* Safe indexing.  Extracted type: forall a. Vec a -> Fin -> a
   -- the length index n has vanished, but the code is unchanged. *)

Infer fun (A : Set) (n : Nat) (xs : Vec A n) (i : Fin n) => vnth A n xs i.

Extract fun (A : Set) (n : Nat) (xs : Vec A n) (i : Fin n) => vnth A n xs i.


(* head of a provably non-empty vector: the (NS n) index guarantees an
   element exists, so no option type is needed.  At runtime this is just
   "read slot 0". *)

Extract fun (A : Set) (n : Nat) (xs : Vec A (NS n)) =>
  vnth A (NS n) xs (fz n).


(* second element of a vector of length at least two. *)

Extract fun (A : Set) (n : Nat) (xs : Vec A (NS (NS n))) =>
  vnth A (NS (NS n)) xs (fs (NS n) (fz n)).


(* weakening an index into a longer vector: Fin n embeds into Fin (NS n).
   Used when growing a buffer without re-checking bounds. *)

Extract fun (n : Nat) (i : Fin n) => fs n i.


(* The boundary.  Everything above erased the index cleanly.  But the family
   [Fin] ITSELF, viewed as a function from a Nat to a type, is a value in type
   position -- it has no Fomega image.  Extraction is honest: it emits the
   dynamic type [?] and an internal blame.  This is where dependency stops
   being free. *)

Extract fun (n : Nat) => Fin n.
