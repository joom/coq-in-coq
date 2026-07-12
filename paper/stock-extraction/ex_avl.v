Require Extraction.
Extraction Language OCaml.

Inductive nat : Set := O : nat | S : nat -> nat.

Fixpoint add (a b : nat) : nat :=
  match a with O => b | S r => S (add r b) end.

Section AVL.
Variable Elem : Set.

Inductive Tree : nat -> Set :=
| leaf : Tree O
| node : forall h, Elem -> Tree h -> Tree h -> Tree (S h).

Definition example_tree (x : Elem) : Tree (S (S O)) :=
  node (S O) x (node O x leaf leaf) (node O x leaf leaf).

Fixpoint mirror {h} (t : Tree h) : Tree h :=
  match t with
  | leaf => leaf
  | node k x l r => node k x (mirror r) (mirror l)
  end.

Fixpoint count {h} (t : Tree h) : nat :=
  match t with
  | leaf => O
  | node _ _ l r => S (add (count l) (count r))
  end.

End AVL.

Extraction "ex_avl.ml" example_tree mirror count.
