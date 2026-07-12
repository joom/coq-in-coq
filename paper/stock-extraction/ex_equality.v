Require Extraction.
Extraction Language OCaml.

Inductive eq (A : Set) (x : A) : A -> Prop := eq_refl : eq A x x.

Definition transport (A : Set) (P : A -> Prop) (x y : A) (h : eq A x y) (p : P x) : P y :=
  match h in eq _ _ z return P z with eq_refl _ _ => p end.

Definition eq_sym (A : Set) (x y : A) (h : eq A x y) : eq A y x :=
  match h in eq _ _ z return eq A z x with eq_refl _ _ => eq_refl A x end.

Definition eq_trans (A : Set) (x y z : A) (hxy : eq A x y) (hyz : eq A y z) : eq A x z :=
  match hyz in eq _ _ w return eq A x w with eq_refl _ _ => hxy end.

Definition f_equal (A B : Set) (f : A -> B) (x y : A) (h : eq A x y)
  : eq B (f x) (f y) :=
  match h in eq _ _ z return eq B (f x) (f z) with eq_refl _ _ => eq_refl B (f x) end.

(* the same programs, used computationally (P : A -> Set), as a Rocq user
   would with eq_rect: *)
Inductive eqS (A : Set) (x : A) : A -> Set := eqS_refl : eqS A x x.

Definition transportS (A : Set) (P : A -> Set) (x y : A) (h : eqS A x y) (p : P x) : P y :=
  match h in eqS _ _ z return P z with eqS_refl _ _ => p end.

Extraction "ex_equality.ml" transport eq_sym eq_trans f_equal transportS.
