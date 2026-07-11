(* Dependent pairs (Sigma types) and first-class modules in CoC.

   [Sig A B] packages a witness [x : A] together with a payload [B x] whose
   type DEPENDS on that witness.  This single construct models existentials,
   dependent records, and -- when [A] is [Set] -- first-class modules and a
   poor man's typeclass: a value paired with operations over it.

   Extraction erases the dependency.  The payload type [B x] mentions the term
   [x], which is dropped, so a [Sig A B] becomes a plain pair type [Sig A B]
   over the *type* arguments only.  When the witness is itself a type (the
   module case), packing a type as a value is exactly the full-dependency
   boundary: it extracts through the target's [?] and [blame] -- the honest
   image of "a type used as data".

   The axioms are the inductive kit of the (negative) Sigma type: the family
   [Sig], its constructor [pair], and its eliminators -- the projections
   [fst] and [snd].  ([snd]'s type mentions [fst], which is exactly why the
   projections must be primitive here: deriving them from a recursor needs
   the iota-conversion a bare PTS lacks.) *)


Axiom Nat : Set.
Axiom Vec : Set -> Nat -> Set.

Axiom Sig : forall (A : Set), (A -> Set) -> Set.
Axiom pair : forall (A : Set) (B : A -> Set) (x : A), B x -> Sig A B.
Axiom fst : forall (A : Set) (B : A -> Set), Sig A B -> A.
Axiom snd : forall (A : Set) (B : A -> Set) (p : Sig A B), B (fst A B p).


(* build a dependent pair: the second component's type depends on the first. *)

Infer fun (A : Set) (B : A -> Set) (x : A) (y : B x) => pair A B x y.

Extract fun (A : Set) (B : A -> Set) (x : A) (y : B x) => pair A B x y.


(* the dependent second projection: its result type B (fst p) is computed
   from the value being projected.  Extraction erases that computation. *)

Extract fun (A : Set) (B : A -> Set) (p : Sig A B) => snd A B p.


(* re-pack: project then rebuild -- an eta-like round trip through the pair. *)

Extract fun (A : Set) (B : A -> Set) (p : Sig A B) =>
  pair A B (fst A B p) (snd A B p).


(* Existential over a length: "a vector of SOME size".  Packing hides the
   index [n] behind the pair, the classic use of Sigma to forget a static
   quantity.  Extraction erases the index entirely: the witness is an ordinary
   [Nat] and the payload an ordinary [Vec A]. *)

Extract fun (A : Set) (n : Nat) (v : Vec A n) =>
  pair Nat (fun (m : Nat) => Vec A m) n v.
