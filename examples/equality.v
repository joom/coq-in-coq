(* Propositional (Leibniz) equality via the Inductive command.

   [Inductive eq (A : Set) (x : A) : A -> Prop := eq_refl : eq A x x] desugars to
   the indexed Boehm-Berarducci encoding

     eq A x y  =  forall (P : A -> Prop), P x -> P y

   -- exactly Leibniz equality.  The generated recursor [eq_rec] IS transport
   (eq_rect): its motive [P : A -> Prop] depends on the INDEX [y], which the
   indexed encoding supports.  So, unlike the axiom version, transport here is a
   real definition that COMPUTES.

   (Full dependent elimination -- a motive over the proof itself -- is still not
   derivable; but eq_rect never needs that.) *)


Inductive eq (A : Set) (x : A) : A -> Prop := | eq_refl : eq A x x.

(* transport / Leibniz substitution -- this is the generated [eq_rec]. *)
Definition transport (A : Set) (P : A -> Prop) (x y : A) (h : eq A x y) (p : P x)
  : P y :=
  eq_rec A x P p y h.

Check transport.
Extract transport.


(* symmetry: transport [eq_refl] along the proof. *)

Definition eq_sym (A : Set) (x y : A) (h : eq A x y) : eq A y x :=
  eq_rec A x (fun (z : A) => eq A z x) (eq_refl A x) y h.

Extract eq_sym.


(* transitivity. *)

Definition eq_trans (A : Set) (x y z : A) (hxy : eq A x y) (hyz : eq A y z)
  : eq A x z :=
  eq_rec A y (fun (w : A) => eq A x w) hxy z hyz.

Extract eq_trans.


(* congruence: equal inputs give equal outputs. *)

Definition f_equal (A B : Set) (f : A -> B) (x y : A) (h : eq A x y)
  : eq B (f x) (f y) :=
  eq_rec A x (fun (z : A) => eq B (f x) (f z)) (eq_refl B (f x)) y h.

Extract f_equal.
