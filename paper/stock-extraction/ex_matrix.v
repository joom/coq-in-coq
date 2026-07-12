Require Extraction.
Extraction Language OCaml.

Inductive nat : Set := O : nat | S : nat -> nat.
Inductive bool : Set := true : bool | false : bool.

Fixpoint add (a b : nat) : nat :=
  match a with O => b | S r => S (add r b) end.
Fixpoint mul (a b : nat) : nat :=
  match a with O => O | S r => add b (mul r b) end.

Inductive Fin : nat -> Set :=
| F1 : forall n, Fin (S n)
| FS : forall n, Fin n -> Fin (S n).

Definition fin_case (n : nat) (C : Set) (z : C) (s : Fin n -> C) (i : Fin (S n)) : C :=
  match i in Fin k return match k with O => unit | S m => (Fin m -> C) -> C end with
  | F1 _ => fun _ => z
  | FS _ j => fun s' => s' j
  end s.

Fixpoint fin_eq {n} (i : Fin n) : Fin n -> bool :=
  match i in Fin k return Fin k -> bool with
  | F1 m => fun j => fin_case m bool true (fun _ => false) j
  | FS m i' => fun j => fin_case m bool false (fin_eq i') j
  end.

Fixpoint sumf (n : nat) : (Fin n -> nat) -> nat :=
  match n with
  | O => fun _ => O
  | S m => fun g => add (g (F1 m)) (sumf m (fun i => g (FS m i)))
  end.

Inductive Mat (m n : nat) : Set :=
| mat : (Fin m -> Fin n -> nat) -> Mat m n.
Arguments mat {m n}.

Definition entry {m n} (a : Mat m n) (i : Fin m) (j : Fin n) : nat :=
  match a with mat f => f i j end.

Definition madd {m n} (a b : Mat m n) : Mat m n :=
  mat (fun i j => add (entry a i j) (entry b i j)).

Definition mmul {m n p} (a : Mat m n) (b : Mat n p) : Mat m p :=
  mat (fun i k => sumf n (fun j => mul (entry a i j) (entry b j k))).

Definition trans {m n} (a : Mat m n) : Mat n m :=
  mat (fun j i => entry a i j).

Definition ident (n : nat) : Mat n n :=
  mat (fun i j => match fin_eq i j with true => S O | false => O end).

Definition scale {m n} (s : nat) (a : Mat m n) : Mat m n :=
  mat (fun i j => mul s (entry a i j)).

Definition gram {m n} (a : Mat m n) : Mat n n := mmul (trans a) a.

Definition similar {m n} (p : Mat m n) (b : Mat n n) : Mat m m :=
  mmul (mmul p b) (trans p).

Definition affine (n : nat) (s : nat) (a b : Mat n n) : Mat n n :=
  madd (scale s (mmul a b)) (ident n).

Extraction "ex_matrix.ml" entry madd mmul trans ident scale gram similar affine.
