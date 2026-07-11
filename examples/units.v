(* Units of measure / dimensional analysis in the Calculus of Constructions.

   A physical [Dim]ension is a formal expression over a (multiplicatively
   written) group signature: [one] is the dimensionless unit, [dmul] combines
   dimensions, [dinv] inverts.  These three are the CONSTRUCTORS of the
   inductive syntax of dimension expressions.  A [Qty d] is a quantity
   carrying dimension [d]: an inductive family with constructor [qty]
   (a number tagged with a dimension) and eliminator [qty_rec].  Addition
   DEMANDS equal dimensions -- so "3 metres + 5 seconds" is a type error,
   while "distance / time : Qty (length / time)" type-checks as a speed.

   The numeric carrier is a placeholder ([Nat], with [add]/[mul] defined by
   recursion; [qinv] is the identity on the carrier since Nat has no
   inverses) -- the point of the example is the dimension discipline in the
   INDICES, which the carrier never sees.

   Extraction erases the dimension index from the target type: [Qty d]
   becomes the plain type [Qty].  Dimension values that the source passes to
   operations remain as ordinary term arguments.  The target no longer types
   quantities by dimension, and the extraction inserts no dynamic unit
   checks. *)


(* Dimension expressions: an inductive syntax with three constructors. *)

Axiom Dim : Set.
Axiom one : Dim.
Axiom dmul : Dim -> Dim -> Dim.
Axiom dinv : Dim -> Dim.


(* The numeric carrier. *)

Axiom Nat : Set.
Axiom NZ : Nat.
Axiom NS : Nat -> Nat.

Axiom Nat_rec : forall (P : Nat -> Set),
  P NZ ->
  (forall (m : Nat), P m -> P (NS m)) ->
  forall (n : Nat), P n.

Definition add (a b : Nat) : Nat :=
  Nat_rec (fun (_ : Nat) => Nat) b (fun (_ : Nat) (r : Nat) => NS r) a.

Definition mul (a b : Nat) : Nat :=
  Nat_rec (fun (_ : Nat) => Nat) NZ (fun (_ : Nat) (r : Nat) => add b r) a.


(* Quantities: an inductive family over dimensions, with constructor and
   eliminator. *)

Axiom Qty : Dim -> Set.
Axiom qty : forall (d : Dim), Nat -> Qty d.
Axiom qty_rec : forall (d : Dim) (C : Set), (Nat -> C) -> Qty d -> C.

Definition unqty (d : Dim) (x : Qty d) : Nat :=
  qty_rec d Nat (fun (a : Nat) => a) x.

Definition qmul (d e : Dim) (x : Qty d) (y : Qty e) : Qty (dmul d e) :=
  qty (dmul d e) (mul (unqty d x) (unqty e y)).

Definition qadd (d : Dim) (x y : Qty d) : Qty d :=      (* same dimension! *)
  qty d (add (unqty d x) (unqty d y)).

Definition qinv (d : Dim) (x : Qty d) : Qty (dinv d) :=
  qty (dinv d) (unqty d x).


(* division as multiplication by an inverse: distance / time = speed. *)

Definition speed (len time : Dim) (d : Qty len) (t : Qty time)
  : Qty (dmul len (dinv time)) :=
  qmul len (dinv time) d (qinv time t).

Check speed
  : forall (len time : Dim), Qty len -> Qty time -> Qty (dmul len (dinv time)).

Extract speed.


(* kinetic-energy-shaped product  m * v * v : dimensions multiply through. *)

Extract fun (mass vel : Dim) (m : Qty mass) (v : Qty vel) =>
  qmul (dmul mass vel) vel (qmul mass vel m v) v.


(* adding two quantities is only allowed at the SAME dimension d. *)

Extract fun (d : Dim) (x y : Qty d) => qadd d x y.


(* a dimensionless ratio  x / y : Qty (d / d) -- same dimension cancels. *)

Extract fun (d : Dim) (x y : Qty d) => qmul d (dinv d) x (qinv d y).


(* The boundary.  Dimension indices erased for free above.  But [Qty] ITSELF,
   as a map from a dimension to a type, is a value in type position -- no
   Fomega image, so extraction emits the dynamic type [?] and an internal
   blame. *)

Extract fun (d : Dim) => Qty d.
