(* Units of measure / dimensional analysis in the Calculus of Constructions.

   A physical [Dim]ension is a formal expression over a (multiplicatively
   written) group signature: [one] is the dimensionless unit, [dmul] combines
   dimensions, [dinv] inverts.  These three are the CONSTRUCTORS of the
   inductive syntax of dimension expressions.  A [Qty d] is a quantity
   carrying dimension [d]: an inductive family with constructor [qty]
   (a number tagged with a dimension) and eliminator [qty_rec].  Addition
   DEMANDS equal dimensions -- so "3 metres + 5 seconds" is a type error,
   while "distance / time : Qty (length / time)" type-checks as a speed.

   The numeric carrier is a placeholder ([nat], with [add]/[mul] defined by
   recursion; [qinv] is the identity on the carrier since nat has no
   inverses) -- the point of the example is the dimension discipline in the
   INDICES, which the carrier never sees.

   Extraction erases the dimension index from the target type: [Qty d]
   becomes the plain type [Qty].  Dimension values that the source passes to
   operations remain as ordinary term arguments.  The target no longer types
   quantities by dimension, and the extraction inserts no dynamic unit
   checks. *)


(* Dimension expressions: an inductive syntax with three constructors. *)

Inductive Dim : Set :=
  | one : Dim
  | dmul : Dim -> Dim -> Dim
  | dinv : Dim -> Dim.


(* The numeric carrier. *)

Inductive nat : Set := | O : nat | S : nat -> nat.

Definition add (a b : nat) : nat :=
  nat_rec nat b (fun (r : nat) => S r) a.

Definition mul (a b : nat) : nat :=
  nat_rec nat O (fun (r : nat) => add b r) a.


(* Quantities: an inductive family over dimensions. *)

Inductive Qty : Dim -> Set :=
  | qty : forall (d : Dim), nat -> Qty d.

Definition unqty (d : Dim) (x : Qty d) : nat :=
  Qty_rec (fun (_ : Dim) => nat) (fun (d0 : Dim) (a : nat) => a) d x.

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
