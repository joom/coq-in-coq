Require Extraction.
Extraction Language OCaml.

Inductive nat : Set := O : nat | S : nat -> nat.
Inductive bool : Set := true : bool | false : bool.

Inductive U : Set :=
| nat_c : U
| bool_c : U
| arr_c : U -> U -> U.

(* In CIC, El is definable by large elimination (the REPL had to axiomatize it). *)
Fixpoint El (c : U) : Set :=
  match c with
  | nat_c => nat
  | bool_c => bool
  | arr_c a b => El a -> El b
  end.

Definition mkarr (a b : U) : U := arr_c (arr_c a b) a.

Inductive Dynamic : Set := box : forall c : U, El c -> Dynamic.

Definition tag (d : Dynamic) : U := match d with box c _ => c end.

Definition mkbox (c : U) (x : El c) : Dynamic := box c x.

(* dependent projection: read the payload back at its decoded type *)
Definition payload (d : Dynamic) : El (tag d) :=
  match d return El (tag d) with box _ x => x end.

Extraction "ex_universe.ml" mkarr tag mkbox payload.
