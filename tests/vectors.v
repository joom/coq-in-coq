(* Length-indexed vectors in the Calculus of Constructions.

   Demonstrates verified extraction to System Fω + blame:
   the computational content (map, fold, replicate) is preserved,
   while the dependent length index is erased from target vector types:
   [Vec A n] becomes [Vec A].  Term variables such as [n] remain when the
   source program uses them computationally.

   All data types and their eliminators are axiomatized — Church
   encoding them would require native let-reduction to stay readable.
   The functions built from these axioms are ordinary CoC terms whose
   extraction is verified by the project's metatheory. *)


(* Natural numbers *)

Axiom Nat : Set.
Axiom NZ : Nat.
Axiom NS : Nat -> Nat.

Axiom Nat_rec : forall (P : Nat -> Set),
  P NZ ->
  (forall (m : Nat), P m -> P (NS m)) ->
  forall (n : Nat), P n.


(* Length-indexed vectors *)

Axiom Vec : Set -> Nat -> Set.
Axiom vnil : forall (A : Set), Vec A NZ.
Axiom vcons : forall (A : Set) (n : Nat), A -> Vec A n -> Vec A (NS n).

Axiom vrec : forall (A : Set) (P : Nat -> Set),
  P NZ ->
  (forall (m : Nat), A -> P m -> P (NS m)) ->
  forall (n : Nat), Vec A n -> P n.


(* vmap : apply a function to every element.

   Extracted type: ∀α β. (α→β) → ?→ Vec(α) → Vec(β)
   The length argument (Nat) becomes ?, but the mapped function
   α→β and the vector structure are preserved. *)

Infer fun (A B : Set) (f : A -> B) (n : Nat) (xs : Vec A n) =>
  vrec A (fun (m : Nat) => Vec B m)
    (vnil B)
    (fun (m : Nat) (a : A) (acc : Vec B m) => vcons B m (f a) acc)
    n xs.

Extract fun (A B : Set) (f : A -> B) (n : Nat) (xs : Vec A n) =>
  vrec A (fun (m : Nat) => Vec B m)
    (vnil B)
    (fun (m : Nat) (a : A) (acc : Vec B m) => vcons B m (f a) acc)
    n xs.


(* vfoldr : right fold, collapsing the vector to a single value.

   The motive ignores the index: P _ = B, so the extracted type
   has no length dependency at all — a clean ∀α β. (α→β→β) → β → ?→ Vec(α) → β.
   Contrast with vmap where the result type still mentions Vec. *)

Infer fun (A B : Set) (f : A -> B -> B) (z : B)
          (n : Nat) (xs : Vec A n) =>
  vrec A (fun (_ : Nat) => B)
    z
    (fun (m : Nat) (a : A) (acc : B) => f a acc)
    n xs.

Extract fun (A B : Set) (f : A -> B -> B) (z : B)
            (n : Nat) (xs : Vec A n) =>
  vrec A (fun (_ : Nat) => B)
    z
    (fun (m : Nat) (a : A) (acc : B) => f a acc)
    n xs.


(* vreplicate : build a vector of n copies of x.

   Uses Nat_rec (recursion on the index) rather than vrec
   (recursion on a vector). The extracted term is a pure loop
   that conses x onto vnil n times. *)

Check fun (A : Set) (x : A) (n : Nat) =>
  Nat_rec (fun (m : Nat) => Vec A m)
    (vnil A)
    (fun (m : Nat) (acc : Vec A m) => vcons A m x acc)
    n
: forall (A : Set), A -> forall (n : Nat), Vec A n.

Extract fun (A : Set) (x : A) (n : Nat) =>
  Nat_rec (fun (m : Nat) => Vec A m)
    (vnil A)
    (fun (m : Nat) (acc : Vec A m) => vcons A m x acc)
    n.


(* vlength : recover the length as a term-level Nat.

   The motive ignores the index (P _ = Nat), so the extracted
   code simply counts elements — no dyn in the result type. *)

Infer fun (A : Set) (n : Nat) (xs : Vec A n) =>
  vrec A (fun (_ : Nat) => Nat)
    NZ
    (fun (m : Nat) (_ : A) (acc : Nat) => NS acc)
    n xs.

Extract fun (A : Set) (n : Nat) (xs : Vec A n) =>
  vrec A (fun (_ : Nat) => Nat)
    NZ
    (fun (m : Nat) (_ : A) (acc : Nat) => NS acc)
    n xs.


(* vsingleton : wrap a single element. *)

Check fun (A : Set) (x : A) => vcons A NZ x (vnil A)
  : forall (A : Set), A -> Vec A (NS NZ).

Extract fun (A : Set) (x : A) => vcons A NZ x (vnil A).


(* map-then-fold : fuse vmap and vfoldr into a single pass.

   Extracts cleanly to Λα β γ. λf g z n xs. vrec z (λ_ a acc. g (f a) acc) n xs
   — a standard fold with a pre-applied transformation, no intermediate vector. *)

Extract fun (A B C : Set) (f : A -> B) (g : B -> C -> C) (z : C)
            (n : Nat) (xs : Vec A n) =>
  vrec A (fun (_ : Nat) => C)
    z
    (fun (m : Nat) (a : A) (acc : C) => g (f a) acc)
    n xs.
