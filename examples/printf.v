(* Type-safe sprintf via the Inductive command.

   A [Fmt A] is a format whose index [A] records the type of the variadic
   function it denotes.  [Fmt] is declared with [Inductive] as a family indexed
   by a [Set] (arity [Set -> Set]), so the generated fold [Fmt_rec] takes a
   motive [X : Set -> Set] and computes.  [sprintf] folds the format at the
   motive [X Y = Str -> Y]; the "computed arity" is an ordinary Fomega arrow
   type after extraction.  Strings and naturals are ordinary [Inductive]s. *)


Inductive Str : Set := | sempty : Str | smark : Str -> Str.

Definition append (a b : Str) : Str :=
  Str_rec Str a (fun (r : Str) => smark r) b.


Inductive nat : Set := | O : nat | S : nat -> nat.

Definition show_nat (n : nat) : Str :=
  nat_rec Str sempty (fun (r : Str) => smark r) n.


(* Formats, indexed by the denoted type. *)

Inductive Fmt : Set -> Set :=
  | fstop : Fmt Str                                      (* ""  : just the string *)
  | flit  : forall (A : Set), Str -> Fmt A -> Fmt A      (* literal text, no arg  *)
  | fint  : forall (A : Set), Fmt A -> Fmt (nat -> A)    (* "%d": expect a nat    *)
  | fstr  : forall (A : Set), Fmt A -> Fmt (Str -> A).   (* "%s": expect a Str    *)


(* Fold the format in accumulator style at the motive [X Y = Str -> Y]. *)

Definition sprintf (A : Set) (f : Fmt A) : A :=
  Fmt_rec (fun (Y : Set) => Str -> Y)
    (fun (acc : Str) => acc)
    (fun (Y : Set) (s : Str) (rec : Str -> Y) (acc : Str) => rec (append acc s))
    (fun (Y : Set) (rec : Str -> Y) (acc : Str) (n : nat) =>
       rec (append acc (show_nat n)))
    (fun (Y : Set) (rec : Str -> Y) (acc : Str) (s : Str) => rec (append acc s))
    A f sempty.


(* "%d" : one nat, yielding a Str. *)

Check sprintf (nat -> Str) (fint Str fstop).
Extract sprintf (nat -> Str) (fint Str fstop).


(* "%s%d" : a Str then a nat. *)

Extract sprintf (Str -> nat -> Str) (fstr (nat -> Str) (fint Str fstop)).


(* "%d<sep>%s" : a nat, a literal separator, then a Str. *)

Extract fun (sep : Str) =>
  sprintf (nat -> Str -> Str)
    (fint (Str -> Str) (flit (Str -> Str) sep (fstr Str fstop))).
