Require Extraction.
Extraction Language OCaml.

Inductive nat : Set := O : nat | S : nat -> nat.

Inductive t (A : Set) : nat -> Set :=
| nil : t A O
| cons : forall n, A -> t A n -> t A (S n).
Arguments nil {A}. Arguments cons {A} n.

Fixpoint map {A B : Set} (f : A -> B) {n} (xs : t A n) : t B n :=
  match xs with
  | nil => nil
  | cons m a v => cons m (f a) (map f v)
  end.

Fixpoint fold_right {A B : Set} (f : A -> B -> B) (z : B) {n} (xs : t A n) : B :=
  match xs with nil => z | cons _ a v => f a (fold_right f z v) end.

Fixpoint length {A : Set} {n} (xs : t A n) : nat :=
  match xs with nil => O | cons _ _ v => S (length v) end.

Definition vsingleton {A : Set} (x : A) : t A (S O) := cons O x nil.

Fixpoint vmapfold {A B C : Set} (f : A -> B) (g : B -> C -> C) (z : C)
  {n} (xs : t A n) : C :=
  match xs with nil => z | cons _ a v => g (f a) (vmapfold f g z v) end.

Extraction "ex_vectors.ml" map fold_right length vsingleton vmapfold.
