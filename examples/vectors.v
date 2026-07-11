(* Length-indexed vectors via the Inductive command.

   [Inductive t (A : Set) : nat -> Set := ...] desugars to the INDEXED
   Boehm-Berarducci encoding: the motive is parameterized by the index,

     t A n  =  forall (X : nat -> Set),
                   X O -> (forall m, A -> X m -> X (S m)) -> X n

   so the generated [t_rec] is the index-dependent recursor and the data
   COMPUTES.  This is what makes an indexed family expressible as a lambda-term
   at all (Boehm-Berarducci 1985; Pfenning-Paulin 1990).

   The dependency on the length is still erased from target types under
   extraction, while functions come out as ordinary folds. *)


Inductive nat : Set := | O : nat | S : nat -> nat.

Inductive t (A : Set) : nat -> Set :=
  | nil : t A O
  | cons : forall (n : nat), A -> t A n -> t A (S n).


(* map: the result type depends on the index n (motive [X m = t B m]). *)

Definition map (A B : Set) (f : A -> B) (n : nat) (xs : t A n) : t B n :=
  t_rec A (fun (m : nat) => t B m)
    (nil B)
    (fun (m : nat) (a : A) (acc : t B m) => cons B m (f a) acc)
    n xs.

Check map.
Extract map.


(* fold: the motive ignores the index, so this is a clean fold to [B]. *)

Definition fold_right (A B : Set) (f : A -> B -> B) (z : B)
  (n : nat) (xs : t A n) : B :=
  t_rec A (fun (_ : nat) => B)
    z
    (fun (m : nat) (a : A) (acc : B) => f a acc)
    n xs.

Extract fold_right.


(* length as a term-level nat. *)

Definition length (A : Set) (n : nat) (xs : t A n) : nat :=
  t_rec A (fun (_ : nat) => nat)
    O
    (fun (m : nat) (_ : A) (acc : nat) => S acc)
    n xs.

Extract length.


(* a one-element vector. *)

Definition vsingleton (A : Set) (x : A) : t A (S O) :=
  cons A O x (nil A).

Check vsingleton : forall (A : Set), A -> t A (S O).
Extract vsingleton.


(* map-then-fold in one pass. *)

Definition vmapfold (A B C : Set) (f : A -> B) (g : B -> C -> C) (z : C)
  (n : nat) (xs : t A n) : C :=
  t_rec A (fun (_ : nat) => C)
    z
    (fun (m : nat) (a : A) (acc : C) => g (f a) acc)
    n xs.

Extract vmapfold.


(* Compute: map the successor over the vector [0, 1] : t nat 2, forcing the
   indexed encoding to actually reduce. *)

Compute map nat nat (fun (x : nat) => S x) (S (S O))
  (cons nat (S O) (S O) (cons nat O O (nil nat))).


(* Note on the boundary: [vreplicate : forall n, t A n] -- build a vector of
   n copies -- would recurse on a nat producing a value whose TYPE depends on
   that nat value.  That is large elimination / value-dependent induction on
   nat, which the impredicative encoding cannot provide (Geuvers 2001): the
   generated [nat_rec] is non-dependent.  It stays out of reach here. *)
