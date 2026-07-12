Require Extraction.
Extraction Language OCaml.

Inductive Str : Set := sempty : Str | smark : Str -> Str.

Fixpoint append (a b : Str) : Str :=
  match b with sempty => a | smark r => smark (append a r) end.

Inductive nat : Set := O : nat | S : nat -> nat.

Fixpoint show_nat (n : nat) : Str :=
  match n with O => sempty | S r => smark (show_nat r) end.

Inductive Fmt : Set -> Type :=
| fstop : Fmt Str
| flit : forall A : Set, Str -> Fmt A -> Fmt A
| fint : forall A : Set, Fmt A -> Fmt (nat -> A)
| fstr : forall A : Set, Fmt A -> Fmt (Str -> A).
Arguments flit {A}. Arguments fint {A}. Arguments fstr {A}.

Fixpoint sprintf_acc {A : Set} (f : Fmt A) : Str -> A :=
  match f in Fmt B return Str -> B with
  | fstop => fun acc => acc
  | flit s k => fun acc => sprintf_acc k (append acc s)
  | fint k => fun acc n => sprintf_acc k (append acc (show_nat n))
  | fstr k => fun acc s => sprintf_acc k (append acc s)
  end.

Definition sprintf {A : Set} (f : Fmt A) : A := sprintf_acc f sempty.

(* "%d" *)
Definition ex_d : nat -> Str := sprintf (fint fstop).
(* "%s%d" *)
Definition ex_sd : Str -> nat -> Str := sprintf (fstr (fint fstop)).
(* "%d<sep>%s" *)
Definition ex_dlit (sep : Str) : nat -> Str -> Str :=
  sprintf (fint (flit sep (fstr fstop))).

Extraction "ex_printf.ml" sprintf ex_d ex_sd ex_dlit.
