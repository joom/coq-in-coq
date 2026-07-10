(* A Tarski universe and a hand-built dynamic type, in the Calculus of
   Constructions -- the example that meets System Fomega + blame head on.

   [U] is a universe of type CODES ([nat_c], [bool_c], [arr_c]), and [El]
   DECODES a code into an actual type.  With these we can build [Dyn], a
   dependent pair of a code and a value of the decoded type: literally a
   dynamically-typed value ("a value tagged with its type") expressed inside a
   dependently-typed language.

   Most of this extracts cleanly -- codes are ordinary data, [box]/[unbox]
   thread them around.  But [El] itself, used as [fun c => El c], is a function
   from data to TYPES: a value in type position.  This is the one construct
   with no image in Fomega, and the extraction is honest about it -- it emits
   the target's dynamic type [?] and an internal [blame].  This is exactly the
   residue the Blame Theorem sets aside (internal label 0), and it pinpoints
   where the dependently-typed source and the polymorphic target genuinely
   part ways. *)


Axiom U : Set.
Axiom nat_c  : U.
Axiom bool_c : U.
Axiom arr_c  : U -> U -> U.

(* decode a code to a type: a value-indexed family of types *)
Axiom El : U -> Set.


(* building codes is ordinary first-order data: extracts to plain calls. *)

Infer fun (a b : U) => arr_c (arr_c a b) a.

Extract fun (a b : U) => arr_c (arr_c a b) a.


(* a dynamically-typed value: a code together with a value it decodes to.
   This is [Dyn = Sigma (c : U). El c] -- a self-describing datum. *)

Axiom Dyn : Set.
Axiom box : forall (c : U), El c -> Dyn.
Axiom tag : Dyn -> U.

(* packing a value with its type tag.  El c is a term-indexed type, so the
   index c is erased and box becomes an ordinary two-argument constructor. *)

Extract fun (c : U) (x : El c) => box c x.


(* reading back the type tag of a dynamic value: plain data again. *)

Extract fun (d : Dyn) => tag d.


(* THE boundary: [El] as a function from codes to types -- a value used in
   TYPE position.  There is no Fomega counterpart, so the extraction falls
   back to the dynamic type [?] and an internal blame.  Contrast this with
   every other example, where the dependency was erasable. *)

Infer fun (c : U) => El c.

Extract fun (c : U) => El c.
