Require Extraction.
Extraction Language OCaml.

Inductive Dim : Set :=
| one : Dim
| dmul : Dim -> Dim -> Dim
| dinv : Dim -> Dim.

Inductive nat : Set := O : nat | S : nat -> nat.

Fixpoint add (a b : nat) : nat :=
  match a with O => b | S r => S (add r b) end.
Fixpoint mul (a b : nat) : nat :=
  match a with O => O | S r => add b (mul r b) end.

Inductive Qty : Dim -> Set :=
| qty : forall d : Dim, nat -> Qty d.

Definition unqty {d} (x : Qty d) : nat := match x with qty _ a => a end.

Definition qmul (d e : Dim) (x : Qty d) (y : Qty e) : Qty (dmul d e) :=
  qty (dmul d e) (mul (unqty x) (unqty y)).

Definition qadd (d : Dim) (x y : Qty d) : Qty d :=
  qty d (add (unqty x) (unqty y)).

Definition qinv (d : Dim) (x : Qty d) : Qty (dinv d) :=
  qty (dinv d) (unqty x).

Definition speed (len time : Dim) (d : Qty len) (t : Qty time)
  : Qty (dmul len (dinv time)) :=
  qmul len (dinv time) d (qinv time t).

Definition kinetic (mass vel : Dim) (m : Qty mass) (v : Qty vel)
  : Qty (dmul (dmul mass vel) vel) :=
  qmul (dmul mass vel) vel (qmul mass vel m v) v.

Definition ratio (d : Dim) (x y : Qty d) : Qty (dmul d (dinv d)) :=
  qmul d (dinv d) x (qinv d y).

Extraction "ex_units.ml" speed kinetic qadd ratio.
