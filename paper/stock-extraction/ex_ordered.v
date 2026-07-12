Require Extraction.
Extraction Language OCaml.

Inductive nat : Set := O : nat | S : nat -> nat.

Inductive le (n : nat) : nat -> Prop :=
| le_n : le n n
| le_S : forall m, le n m -> le n (S m).

Fixpoint le_trans_aux (a b c : nat) (hbc : le b c) : le a b -> le a c :=
  match hbc in le _ m return le a b -> le a m with
  | le_n _ => fun hab => hab
  | le_S _ m r => fun hab => le_S a m (le_trans_aux a b m r hab)
  end.
Definition le_trans (a b c : nat) (hab : le a b) (hbc : le b c) : le a c :=
  le_trans_aux a b c hbc hab.

Inductive OList : nat -> Set :=
| onil : forall b, OList b
| ocons : forall b x, le b x -> OList x -> OList b.

Fixpoint olen {b} (xs : OList b) : nat :=
  match xs with
  | onil _ => O
  | ocons _ _ _ r => S (olen r)
  end.

Definition oneTwo : OList O :=
  ocons O (S O) (le_S O O (le_n O))
    (ocons (S O) (S (S O)) (le_S (S O) (S O) (le_n (S O)))
      (onil (S (S O)))).

Extraction "ex_ordered.ml" olen oneTwo.
