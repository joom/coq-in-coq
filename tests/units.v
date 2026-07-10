(* Units of measure / dimensional analysis in the Calculus of Constructions.

   A physical [Dim]ension is an element of a (multiplicatively written) abelian
   group: [one] is the dimensionless unit, [dmul] combines dimensions, [dinv]
   inverts.  A [Qty d] is a quantity carrying dimension [d].  Multiplication
   multiplies dimensions, division subtracts them, and addition DEMANDS equal
   dimensions -- so "3 metres + 5 seconds" is a type error, while
   "distance / time : Qty (length / time)" type-checks as a speed.

   Extraction erases the dimension index from the target type: [Qty d] becomes
   the plain type [Qty].  Dimension values that the source passes to operations
   remain as ordinary term arguments.  The target no longer types quantities by
   dimension, and the extraction inserts no dynamic unit checks. *)


Axiom Dim : Set.
Axiom one : Dim.
Axiom dmul : Dim -> Dim -> Dim.
Axiom dinv : Dim -> Dim.

Axiom Qty : Dim -> Set.

Axiom qmul : forall (d e : Dim), Qty d -> Qty e -> Qty (dmul d e).
Axiom qadd : forall (d : Dim), Qty d -> Qty d -> Qty d.       (* same dimension! *)
Axiom qinv : forall (d : Dim), Qty d -> Qty (dinv d).


(* division as multiplication by an inverse: distance / time = speed. *)

Infer fun (len time : Dim) (d : Qty len) (t : Qty time) =>
  qmul len (dinv time) d (qinv time t).

Extract fun (len time : Dim) (d : Qty len) (t : Qty time) =>
  qmul len (dinv time) d (qinv time t).


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
