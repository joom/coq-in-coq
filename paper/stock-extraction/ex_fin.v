Require Extraction.
Extraction Language OCaml.

Inductive nat : Set := O : nat | S : nat -> nat.

Inductive t (A : Set) : nat -> Set :=
| nil : t A O
| cons : forall n, A -> t A n -> t A (S n).
Arguments nil {A}. Arguments cons {A} n.

Inductive Fin : nat -> Set :=
| F1 : forall n, Fin (S n)
| FS : forall n, Fin n -> Fin (S n).

Definition fin0 (C : Set) (i : Fin O) : C :=
  match i in Fin k return match k with O => C | S _ => unit end with
  | F1 _ => tt
  | FS _ _ => tt
  end.

Definition fin_case (n : nat) (C : Set) (z : C) (s : Fin n -> C) (i : Fin (S n)) : C :=
  match i in Fin k return match k with O => unit | S m => (Fin m -> C) -> C end with
  | F1 _ => fun _ => z
  | FS _ j => fun s' => s' j
  end s.

Fixpoint nth {A : Set} {n} (xs : t A n) : Fin n -> A :=
  match xs in t _ m return Fin m -> A with
  | nil => fun i => fin0 A i
  | cons m a v => fun i => fin_case m A a (nth v) i
  end.

Definition head {A : Set} {n} (xs : t A (S n)) : A := nth xs (F1 n).
Definition second {A : Set} {n} (xs : t A (S (S n))) : A := nth xs (FS (S n) (F1 n)).
Definition weak {n} (i : Fin n) : Fin (S n) := FS n i.

Extraction "ex_fin.ml" nth head second weak.
