(* Provably-sorted lists via the Inductive command -- an inductive PREDICATE
   ([le]) threaded through an indexed family ([OList]).

   Both are declared with [Inductive].  [le] desugars to

     le n m  =  forall (X : nat -> Prop), X n -> (forall k, X k -> X (S k)) -> X m

   so [le_trans] is a genuine proof by [le_rec] (induction on a [le]
   derivation), and it COMPUTES.  [OList b] is sorted with every element >= b.

   Note on course-of-values: [le_rec]/[OList_rec] are folds (the recursive
   argument arrives already folded).  A function needing the original
   substructure -- e.g. rebalancing that reuses the tail unchanged -- is a
   paramorphism, not a catamorphism, and the plain fold does not expose it
   (Mendler-style encodings do; see the paper). *)


Inductive nat : Set := | O : nat | S : nat -> nat.

Inductive le (n : nat) : nat -> Prop :=
  | le_n : le n n
  | le_S : forall (m : nat), le n m -> le n (S m).


(* transitivity, by induction on the second derivation. *)

Definition le_trans (a b c : nat) (hab : le a b) (hbc : le b c) : le a c :=
  le_rec b (fun (m : nat) => le a m)
    hab
    (fun (m : nat) (r : le a m) => le_S a m r)
    c hbc.

Check le_trans.


(* Sorted lists with a lower bound. *)

Inductive OList : nat -> Set :=
  | onil : forall (b : nat), OList b
  | ocons : forall (b x : nat), le b x -> OList x -> OList b.


(* length: motive ignores the bound index. *)

Definition olen (b : nat) (xs : OList b) : nat :=
  OList_rec (fun (_ : nat) => nat)
    (fun (b0 : nat) => O)
    (fun (b0 x : nat) (h : le b0 x) (r : nat) => S r)
    b xs.

Check olen.
Extract olen.


(* A certified-sorted literal  [1, 2]  with global lower bound 0.  The [le]
   proofs are what make it type-check. *)

Definition oneTwo : OList O :=
  ocons O (S O) (le_S O O (le_n O))
    (ocons (S O) (S (S O)) (le_S (S O) (S O) (le_n (S O)))
      (onil (S (S O)))).

Check oneTwo : OList O.

(* its length computes to 2. *)
Compute olen O oneTwo.


(* The boundary: [OList] as a value in type position -> Dyn + internal blame. *)

Extract fun (b : nat) => OList b.
