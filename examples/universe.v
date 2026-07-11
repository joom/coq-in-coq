(* A Tarski universe and a hand-built dynamic type, in the Calculus of
   Constructions -- the example that meets System Fomega + blame head on.

   [U] is a universe of type CODES ([nat_c], [bool_c], [arr_c]), and [El]
   DECODES a code into an actual type.  With these we can build [Dynamic], a
   dependent pair of a code and a value of the decoded type: literally a
   dynamically-typed value ("a value tagged with its type") expressed inside a
   dependently-typed language.

   Most of this extracts cleanly -- codes are ordinary data, [box]/[unbox]
   thread them around.  But [El] itself, used as [fun c => El c], is a function
   from data to TYPES: a value in type position.  The current translation uses
   the target's dynamic type [?] and internal [blame] for this case.  The
   label-safety theorem sets that extraction-failure label (id 2) aside; it does
   not claim that this fallback is semantically maximal. *)


Inductive U : Set :=
  | nat_c  : U
  | bool_c : U
  | arr_c  : U -> U -> U.

(* decode a code to a type: a value-indexed family of types.  [El] would be
   defined by large elimination over [U] (computing a type from data), which
   the bare PTS cannot express -- it stays abstract, and is exactly the
   value-as-type boundary this example exists to exhibit. *)
Axiom El : U -> Set.


(* building codes is ordinary first-order data: extracts to plain calls. *)

Infer fun (a b : U) => arr_c (arr_c a b) a.

Extract fun (a b : U) => arr_c (arr_c a b) a.


(* a dynamically-typed value: a code together with a value it decodes to.
   This is [Dynamic = Sigma (c : U). El c] -- a self-describing datum. *)

(* The package type: constructor [box] pairs a code with a value it decodes
   to; projection [tag] recovers the code, derived from the recursor. *)
Inductive Dynamic : Set :=
  | box : forall (c : U), El c -> Dynamic.

Definition tag (d : Dynamic) : U :=
  Dynamic_rec U (fun (c : U) (_ : El c) => c) d.

(* packing a value with its type tag.  El c is a term-indexed type, so the
   index c is erased and box becomes an ordinary two-argument constructor. *)

Extract fun (c : U) (x : El c) => box c x.


(* reading back the type tag of a dynamic value: plain data again. *)

Extract fun (d : Dynamic) => tag d.


(* THE boundary: [El] as a function from codes to types -- a value used in
   TYPE position.  There is no Fomega counterpart, so the extraction falls
   back to the dynamic type [?] and an internal blame.  Contrast this with
   every other example, where the dependency was erasable. *)

Infer fun (c : U) => El c.

Extract fun (c : U) => El c.


(* A type used as ordinary DATA -- not even applied to anything, just
   returned.  A term of type Set has no Fomega image at all, so extraction
   produces the inert placeholder at the dynamic type: the one way a
   NON-blame value of type [?] appears in extracted code.  (The El boundary
   above inhabits [?] only via internal blame.) *)

Extract U -> U.
