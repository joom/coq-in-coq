Require Extraction.
Extraction Language OCaml.

Inductive bool : Set := true : bool | false : bool.
Definition negb (b : bool) : bool := match b with true => false | false => true end.

Inductive nat : Set := O : nat | S : nat -> nat.
Fixpoint add (m n : nat) : nat := match m with O => n | S r => S (add r n) end.
Fixpoint mul (m n : nat) : nat := match m with O => O | S r => add n (mul r n) end.

Inductive list (A : Set) : Set := nil : list A | cons : A -> list A -> list A.
Arguments nil {A}. Arguments cons {A}.
Fixpoint length {A : Set} (xs : list A) : nat :=
  match xs with nil => O | cons _ r => S (length r) end.

Inductive Tree : Set := leaf : Tree | node : Tree -> Tree -> Tree.
Fixpoint leaves (t : Tree) : nat :=
  match t with leaf => S O | node l r => add (leaves l) (leaves r) end.

Inductive Vec (A : Set) : nat -> Set :=
| vnil : Vec A O
| vcons : forall n, A -> Vec A n -> Vec A (S n).
Arguments vnil {A}. Arguments vcons {A} n.

Fixpoint vmap {A B : Set} (f : A -> B) {n} (v : Vec A n) : Vec B n :=
  match v with
  | vnil => vnil
  | vcons m a r => vcons m (f a) (vmap f r)
  end.

Extraction "ex_inductive.ml" negb add mul length leaves vmap.
