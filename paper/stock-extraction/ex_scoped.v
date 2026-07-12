Require Extraction.
Extraction Language OCaml.

Inductive nat : Set := O : nat | S : nat -> nat.

Fixpoint add (a b : nat) : nat :=
  match a with O => b | S r => S (add r b) end.

Inductive Fin : nat -> Set :=
| F1 : forall n, Fin (S n)
| FS : forall n, Fin n -> Fin (S n).

Definition fin_case (n : nat) (C : Set) (z : C) (s : Fin n -> C) (i : Fin (S n)) : C :=
  match i in Fin k return match k with O => unit | S m => (Fin m -> C) -> C end with
  | F1 _ => fun _ => z
  | FS _ j => fun s' => s' j
  end s.

Inductive Tm : nat -> Set :=
| tvar : forall n, Fin n -> Tm n
| tapp : forall n, Tm n -> Tm n -> Tm n
| tlam : forall n, Tm (S n) -> Tm n.

Fixpoint size {n} (t : Tm n) : nat :=
  match t with
  | tvar _ _ => S O
  | tapp _ f a => S (add (size f) (size a))
  | tlam _ b => S (size b)
  end.

Definition ext (m n : nat) (r : Fin m -> Fin n) : Fin (S m) -> Fin (S n) :=
  fun j => fin_case m (Fin (S n)) (F1 n) (fun i => FS n (r i)) j.

Fixpoint rename {m} (t : Tm m) : forall n, (Fin m -> Fin n) -> Tm n :=
  match t in Tm m0 return forall n, (Fin m0 -> Fin n) -> Tm n with
  | tvar _ i => fun n r => tvar n (r i)
  | tapp _ f a => fun n r => tapp n (rename f n r) (rename a n r)
  | tlam m0 b => fun n r => tlam n (rename b (S n) (ext m0 n r))
  end.

Definition weaken (n : nat) (t : Tm n) : Tm (S n) := rename t (S n) (FS n).

Definition tI : Tm O := tlam O (tvar (S O) (F1 O)).

Extraction "ex_scoped.ml" size ext rename weaken tI.
