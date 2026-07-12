Require Extraction.
Extraction Language OCaml.

Inductive nat : Set := O : nat | S : nat -> nat.
Inductive bool : Set := true : bool | false : bool.
Inductive list (A : Set) : Set := nil : list A | cons : A -> list A -> list A.
Arguments nil {A}. Arguments cons {A}.

Fixpoint app {A : Set} (xs ys : list A) : list A :=
  match xs with nil => ys | cons x r => cons x (app r ys) end.

Fixpoint map {A B : Set} (f : A -> B) (xs : list A) : list B :=
  match xs with nil => nil | cons x r => cons (f x) (map f r) end.

Fixpoint fold_right {A B : Set} (f : A -> B -> B) (z : B) (xs : list A) : B :=
  match xs with nil => z | cons x r => f x (fold_right f z r) end.

Fixpoint length {A : Set} (xs : list A) : nat :=
  match xs with nil => O | cons _ r => S (length r) end.

Fixpoint rev_app {A : Set} (xs acc : list A) : list A :=
  match xs with nil => acc | cons x r => rev_app r (cons x acc) end.
Definition rev {A : Set} (xs : list A) : list A := rev_app xs nil.

Fixpoint filter {A : Set} (p : A -> bool) (xs : list A) : list A :=
  match xs with
  | nil => nil
  | cons x r => match p x with true => cons x (filter p r) | false => filter p r end
  end.

Fixpoint flat_map {A B : Set} (f : A -> list B) (xs : list A) : list B :=
  match xs with nil => nil | cons x r => app (f x) (flat_map f r) end.

Extraction "ex_lists.ml" app map fold_right length rev filter flat_map.
