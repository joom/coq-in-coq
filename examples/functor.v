(* Higher-kinded extraction: functors and tagless-final DSLs.

   These examples demonstrate extraction of terms abstracted over type
   constructors (Set -> Set).  In the target, such binders become
   higher-kinded type variables of kind * => *, directly exercising the
   Fω part of the target type system.

   [Functor], [Sym], and [Monad] are typeclass-style records over a type
   constructor; [fmap], [lit], [add], [ret], and [bind] are their field
   projections (the records' eliminators).  Like all record kits here they
   are axiomatized; the example terms are ordinary programs against those
   signatures. *)


(* --- Functors ---------------------------------------------------------- *)

Axiom Functor : (Set -> Set) -> Set.

Axiom fmap :
  forall (F : Set -> Set),
  Functor F ->
  forall (A : Set),
  forall (B : Set),
  (A -> B) -> F A -> F B.

(* Compose two maps: fmap g . fmap f *)

Extract
  fun (F : Set -> Set) =>
  fun (FF : Functor F) =>
  fun (A : Set) =>
  fun (B : Set) =>
  fun (C : Set) =>
  fun (f : A -> B) =>
  fun (g : B -> C) =>
  fun (xs : F A) =>
    fmap F FF B C g (fmap F FF A B f xs).


(* --- Tagless-final DSL ------------------------------------------------- *)

Axiom Nat : Set.

Axiom Sym : (Set -> Set) -> Set.

Axiom lit :
  forall (R : Set -> Set),
  Sym R -> Nat -> R Nat.

Axiom add :
  forall (R : Set -> Set),
  Sym R -> R Nat -> R Nat -> R Nat.

(* Double a literal: add n n *)

Extract
  fun (R : Set -> Set) =>
  fun (S : Sym R) =>
  fun (n : Nat) =>
    add R S (lit R S n) (lit R S n).


(* --- Monad bind -------------------------------------------------------- *)

Axiom Monad : (Set -> Set) -> Set.

Axiom ret :
  forall (M : Set -> Set),
  Monad M ->
  forall (A : Set),
  A -> M A.

Axiom bind :
  forall (M : Set -> Set),
  Monad M ->
  forall (A : Set),
  forall (B : Set),
  M A -> (A -> M B) -> M B.

(* Kleisli composition: bind (bind ma f) g *)

Extract
  fun (M : Set -> Set) =>
  fun (MM : Monad M) =>
  fun (A : Set) =>
  fun (B : Set) =>
  fun (C : Set) =>
  fun (ma : M A) =>
  fun (f : A -> M B) =>
  fun (g : B -> M C) =>
    bind M MM B C (bind M MM A B ma f) g.
