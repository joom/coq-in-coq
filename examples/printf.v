(* Type-safe sprintf in the Calculus of Constructions.

   A [Fmt A] is a format string whose type index [A] records the type of the
   *variadic* function it denotes: the number and types of the arguments a
   format expects are computed from the format value itself.  [fint] adds a
   [Nat] argument, [fstr] adds a [Str] argument, [flit] splices literal text,
   and the type of [sprintf] maps a format to its computed function type.

   This is the textbook example of a dependent type earning its keep: the arity
   of [sprintf] is not fixed, it is DERIVED from the format.  A malformed call
   (too few or wrongly typed arguments) is a type error.

   Axioms declare only the inductive kit: strings (a unary-mark model --
   [sempty], [smark], [str_rec] -- enough to render output while staying
   self-contained), naturals, and the format family with its constructors
   and eliminator [Fmt_rec].  [append], [show_nat], and [sprintf] itself are
   ordinary [Definition]s; [sprintf] folds the format in accumulator style
   at the motive [P X = Str -> X].

   Extraction keeps [A] as an ordinary type parameter of [Fmt] and erases the
   dependency: the "computed" function type is just a normal Fomega arrow
   type, and [sprintf] has a normal polymorphic target signature. *)


(* Strings, as unary marks. *)

Axiom Str : Set.
Axiom sempty : Str.
Axiom smark : Str -> Str.

Axiom str_rec : forall (P : Str -> Set),
  P sempty ->
  (forall (s : Str), P s -> P (smark s)) ->
  forall (s : Str), P s.

Definition append (a b : Str) : Str :=
  str_rec (fun (_ : Str) => Str) a (fun (_ : Str) (r : Str) => smark r) b.


(* Naturals, rendered into strings one mark per unit. *)

Axiom Nat : Set.
Axiom NZ : Nat.
Axiom NS : Nat -> Nat.

Axiom Nat_rec : forall (P : Nat -> Set),
  P NZ ->
  (forall (m : Nat), P m -> P (NS m)) ->
  forall (n : Nat), P n.

Definition show_nat (n : Nat) : Str :=
  Nat_rec (fun (_ : Nat) => Str) sempty (fun (_ : Nat) (r : Str) => smark r) n.


(* Formats: a family indexed by the type of function the format denotes,
   with its eliminator over the index. *)

Axiom Fmt : Set -> Set.

Axiom fstop : Fmt Str.                                   (* "" : just the string *)
Axiom flit  : forall (A : Set), Str -> Fmt A -> Fmt A.   (* literal text, no arg *)
Axiom fint  : forall (A : Set), Fmt A -> Fmt (Nat -> A). (* "%d": expect a Nat  *)
Axiom fstr  : forall (A : Set), Fmt A -> Fmt (Str -> A). (* "%s": expect a Str  *)

Axiom Fmt_rec :
  forall (P : Set -> Set),
  P Str ->
  (forall (A : Set), Str -> P A -> P A) ->
  (forall (A : Set), P A -> P (Nat -> A)) ->
  (forall (A : Set), P A -> P (Str -> A)) ->
  forall (A : Set), Fmt A -> P A.

(* Fold the format in accumulator style: a format denoting [A] becomes a
   function [Str -> A] awaiting the output accumulated so far. *)

Definition sprintf (A : Set) (f : Fmt A) : A :=
  Fmt_rec (fun (X : Set) => Str -> X)
    (fun (acc : Str) => acc)
    (fun (X : Set) (s : Str) (rec : Str -> X) (acc : Str) =>
     rec (append acc s))
    (fun (X : Set) (rec : Str -> X) (acc : Str) (n : Nat) =>
     rec (append acc (show_nat n)))
    (fun (X : Set) (rec : Str -> X) (acc : Str) (s : Str) =>
     rec (append acc s))
    A f sempty.


(* "%d" : the format expecting one Nat, yielding a Str.
   Inferred type of sprintf on it is exactly Nat -> Str. *)

Check sprintf (Nat -> Str) (fint Str fstop).

Extract sprintf (Nat -> Str) (fint Str fstop).


(* "%s%d" : expect a Str then a Nat.  sprintf yields Str -> Nat -> Str. *)

Check sprintf (Str -> Nat -> Str) (fstr (Nat -> Str) (fint Str fstop)).

Extract sprintf (Str -> Nat -> Str) (fstr (Nat -> Str) (fint Str fstop)).


(* "%d<sep>%s" : a Nat, a literal separator, then a Str.
   The whole thing extracts to a plain curried function of type
   Nat -> Str -> Str, with the format value threaded as ordinary data. *)

Extract fun (sep : Str) =>
  sprintf (Nat -> Str -> Str)
    (fint (Str -> Str) (flit (Str -> Str) sep (fstr Str fstop))).


(* A reusable "labelled value" formatter, abstract in its label:
   given a label string, it prints  <label>: %d . *)

Extract fun (label : Str) (colon : Str) =>
  sprintf (Nat -> Str)
    (flit (Nat -> Str) label
      (flit (Nat -> Str) colon (fint Str fstop))).
