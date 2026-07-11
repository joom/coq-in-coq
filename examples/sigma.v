(* Dependent pairs (Sigma types) via the Inductive command.

   [Inductive sigT (A : Set) (B : A -> Set) : Set := existT : forall (x:A), B x -> sigT A B]
   desugars to the impredicative existential encoding

     sigT A B  =  forall (X : Set), (forall (x : A), B x -> X) -> X

   The generated [sigT_rec] is the non-dependent eliminator, which gives the
   first projection.  The DEPENDENT second projection [snd : forall p, B (fst p)]
   needs a motive over the VALUE [p] -- value-dependent elimination, which the
   impredicative encoding cannot provide (Geuvers 2001).  It is not definable
   here; that is the price of the encoding. *)


Inductive nat : Set := | O : nat | S : nat -> nat.

Inductive t (A : Set) : nat -> Set :=
  | nil : t A O
  | cons : forall (n : nat), A -> t A n -> t A (S n).

Inductive sigT (A : Set) (B : A -> Set) : Set :=
  | existT : forall (x : A), B x -> sigT A B.


(* build a dependent existT. *)

Extract fun (A : Set) (B : A -> Set) (x : A) (y : B x) => existT A B x y.


(* first projection, via the generated [sigT_rec]. *)

Definition projT1 (A : Set) (B : A -> Set) (p : sigT A B) : A :=
  sigT_rec A B A (fun (x : A) (_ : B x) => x) p.

Check projT1.
Extract projT1.


(* existential over a length: "a vector of SOME size".  Packing hides the
   index behind the existT. *)

Extract fun (A : Set) (n : nat) (v : t A n) =>
  existT nat (fun (m : nat) => t A m) n v.
