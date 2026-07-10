(* Type-safe sprintf in the Calculus of Constructions.

   A [Fmt A] is a format string whose type index [A] records the type of the
   *variadic* function it denotes: the number and types of the arguments a
   format expects are computed from the format value itself.  [fint] adds a
   [Nat] argument, [fstr] adds a [Str] argument, [flit] splices literal text,
   and [sprintf] runs a format, producing a function of the computed type.

   This is the textbook example of a dependent type earning its keep: the arity
   of [sprintf] is not fixed, it is DERIVED from the format.  A malformed call
   (too few or wrongly typed arguments) is a type error.

   Extraction keeps [A] as an ordinary type parameter of [Fmt] and erases the
   dependency: the "computed" function type is just a normal Fomega arrow type,
   and [sprintf] becomes a normal polymorphic function.  The varargs magic was
   entirely static. *)


Axiom Str : Set.
Axiom Nat : Set.

(* A format denoting a value of type [A]. *)
Axiom Fmt : Set -> Set.

Axiom fstop : Fmt Str.                                   (* "" : just the string *)
Axiom flit  : forall (A : Set), Str -> Fmt A -> Fmt A.   (* literal text, no arg *)
Axiom fint  : forall (A : Set), Fmt A -> Fmt (Nat -> A). (* "%d": expect a Nat  *)
Axiom fstr  : forall (A : Set), Fmt A -> Fmt (Str -> A). (* "%s": expect a Str  *)

Axiom sprintf : forall (A : Set), Fmt A -> A.


(* "%d" : the format expecting one Nat, yielding a Str.
   Inferred type of sprintf on it is exactly Nat -> Str. *)

Infer sprintf (Nat -> Str) (fint Str fstop).

Extract sprintf (Nat -> Str) (fint Str fstop).


(* "%s%d" : expect a Str then a Nat.  sprintf yields Str -> Nat -> Str. *)

Infer sprintf (Str -> Nat -> Str) (fstr (Nat -> Str) (fint Str fstop)).

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
