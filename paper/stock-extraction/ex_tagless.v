Require Extraction.
Extraction Language OCaml.

Inductive nat : Set := O : nat | S : nat -> nat.
Inductive bool : Set := true : bool | false : bool.

Fixpoint add (m n : nat) : nat :=
  match m with O => n | S r => S (add r n) end.

Fixpoint eqb (m n : nat) : bool :=
  match m, n with
  | O, O => true
  | S m', S n' => eqb m' n'
  | _, _ => false
  end.

Inductive ty : Set := TNat : ty | TBool : ty.

(* the computed meaning of an object type: large elimination over ty *)
Definition tyDen (t : ty) : Set :=
  match t with TNat => nat | TBool => bool end.

Inductive expr : ty -> Set :=
| ENat : nat -> expr TNat
| EBool : bool -> expr TBool
| EAdd : expr TNat -> expr TNat -> expr TNat
| EEq : expr TNat -> expr TNat -> expr TBool
| EIf : forall t, expr TBool -> expr t -> expr t -> expr t.

(* the evaluator with a COMPUTED return type *)
Fixpoint eval {t} (e : expr t) : tyDen t :=
  match e in expr t0 return tyDen t0 with
  | ENat n => n
  | EBool b => b
  | EAdd a b => add (eval a) (eval b)
  | EEq a b => eqb (eval a) (eval b)
  | EIf _ c th el => match eval c with true => eval th | false => eval el end
  end.

(* if 1 = 2 then 0 else 1 + 2 *)
Definition sample : expr TNat :=
  EIf TNat (EEq (ENat (S O)) (ENat (S (S O))))
      (ENat O)
      (EAdd (ENat (S O)) (ENat (S (S O)))).

Definition run : nat := eval sample.

Extraction "ex_tagless.ml" eval sample run.
