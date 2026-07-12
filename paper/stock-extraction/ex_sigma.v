Require Extraction.
Extraction Language OCaml.

Inductive nat : Set := O : nat | S : nat -> nat.

Inductive t (A : Set) : nat -> Set :=
| nil : t A O
| cons : forall n, A -> t A n -> t A (S n).
Arguments nil {A}. Arguments cons {A} n.

Inductive sigT (A : Set) (B : A -> Set) : Set :=
| existT : forall x : A, B x -> sigT A B.
Arguments existT {A B}.

Definition mk (A : Set) (B : A -> Set) (x : A) (y : B x) : sigT A B := existT x y.

Definition projT1 {A : Set} {B : A -> Set} (p : sigT A B) : A :=
  match p with existT x _ => x end.

Definition projT2 {A : Set} {B : A -> Set} (p : sigT A B) : B (projT1 p) :=
  match p return B (projT1 p) with existT _ y => y end.

Definition pack {A : Set} (n : nat) (v : t A n) : sigT nat (fun m => t A m) :=
  existT n v.

Extraction "ex_sigma.ml" mk projT1 projT2 pack.
