(* Length-indexed vectors in the Calculus of Constructions.

   Demonstrates verified extraction to System Fω + blame:
   the computational content (map, fold, replicate) is preserved,
   while the dependent length index is erased from target vector types:
   [Vec A n] becomes [Vec A].  Term variables such as [n] remain when the
   source program uses them computationally.

   Axioms declare only what native inductive types would provide: the type
   formers, constructors, and eliminators of [Nat] and [Vec].  Every
   function is an ordinary [Definition] built from the eliminators. *)


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

Definition vmap (A B : Set) (f : A -> B) (n : Nat) (xs : Vec A n)
  : Vec B n :=
  vrec A (fun (m : Nat) => Vec B m)
    (vnil B)
    (fun (m : Nat) (a : A) (acc : Vec B m) => vcons B m (f a) acc)
    n xs.

Check vmap.

Extract vmap.


(* vfoldr : right fold, collapsing the vector to a single value.

   The motive ignores the index: P _ = B, so the extracted type
   has no length dependency at all — a clean ∀α β. (α→β→β) → β → ?→ Vec(α) → β.
   Contrast with vmap where the result type still mentions Vec. *)

Definition vfoldr (A B : Set) (f : A -> B -> B) (z : B)
  (n : Nat) (xs : Vec A n) : B :=
  vrec A (fun (_ : Nat) => B)
    z
    (fun (m : Nat) (a : A) (acc : B) => f a acc)
    n xs.

Check vfoldr.

Extract vfoldr.


(* vreplicate : build a vector of n copies of x.

   Uses Nat_rec (recursion on the index) rather than vrec
   (recursion on a vector). The extracted term is a pure loop
   that conses x onto vnil n times. *)

Definition vreplicate (A : Set) (x : A) (n : Nat) : Vec A n :=
  Nat_rec (fun (m : Nat) => Vec A m)
    (vnil A)
    (fun (m : Nat) (acc : Vec A m) => vcons A m x acc)
    n.

Check vreplicate : forall (A : Set), A -> forall (n : Nat), Vec A n.

Extract vreplicate.


(* vlength : recover the length as a term-level Nat.

   The motive ignores the index (P _ = Nat), so the extracted
   code simply counts elements — no dyn in the result type. *)

Definition vlength (A : Set) (n : Nat) (xs : Vec A n) : Nat :=
  vrec A (fun (_ : Nat) => Nat)
    NZ
    (fun (m : Nat) (_ : A) (acc : Nat) => NS acc)
    n xs.

Check vlength.

Extract vlength.


(* vsingleton : wrap a single element. *)

Definition vsingleton (A : Set) (x : A) : Vec A (NS NZ) :=
  vcons A NZ x (vnil A).

Check vsingleton : forall (A : Set), A -> Vec A (NS NZ).

Extract vsingleton.


(* map-then-fold : fuse vmap and vfoldr into a single pass.

   Extracts cleanly to a standard fold with a pre-applied transformation,
   no intermediate vector. *)

Definition vmapfold (A B C : Set) (f : A -> B) (g : B -> C -> C) (z : C)
  (n : Nat) (xs : Vec A n) : C :=
  vrec A (fun (_ : Nat) => C)
    z
    (fun (m : Nat) (a : A) (acc : C) => g (f a) acc)
    n xs.

Extract vmapfold.
