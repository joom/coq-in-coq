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

(* A typeclass is a single-constructor record, i.e. a one-clause inductive; its
   field projection [fmap] is derived from the generated recursor. *)
Inductive Functor (F : Set -> Set) : Set :=
  | mkFunctor : (forall (A B : Set), (A -> B) -> F A -> F B) -> Functor F.

Definition fmap (F : Set -> Set) (FF : Functor F)
  (A B : Set) (f : A -> B) (x : F A) : F B :=
  Functor_rec F (forall (A B : Set), (A -> B) -> F A -> F B)
    (fun (m : forall (A B : Set), (A -> B) -> F A -> F B) => m) FF A B f x.

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

Axiom nat : Set.

Inductive Sym (R : Set -> Set) : Set :=
  | mkSym : (nat -> R nat) -> (R nat -> R nat -> R nat) -> Sym R.

Definition lit (R : Set -> Set) (s : Sym R) (n : nat) : R nat :=
  Sym_rec R (nat -> R nat)
    (fun (l : nat -> R nat) (a : R nat -> R nat -> R nat) => l) s n.

Definition add (R : Set -> Set) (s : Sym R) (x y : R nat) : R nat :=
  Sym_rec R (R nat -> R nat -> R nat)
    (fun (l : nat -> R nat) (a : R nat -> R nat -> R nat) => a) s x y.

(* Double a literal: add n n *)

Extract
  fun (R : Set -> Set) =>
  fun (S : Sym R) =>
  fun (n : nat) =>
    add R S (lit R S n) (lit R S n).


(* --- Monad bind -------------------------------------------------------- *)

Inductive Monad (M : Set -> Set) : Set :=
  | mkMonad :
      (forall (A : Set), A -> M A) ->
      (forall (A B : Set), M A -> (A -> M B) -> M B) ->
      Monad M.

Definition ret (M : Set -> Set) (MM : Monad M) (A : Set) (x : A) : M A :=
  Monad_rec M (forall (A : Set), A -> M A)
    (fun (r : forall (A : Set), A -> M A)
         (b : forall (A B : Set), M A -> (A -> M B) -> M B) => r) MM A x.

Definition bind (M : Set -> Set) (MM : Monad M) (A B : Set)
  (ma : M A) (f : A -> M B) : M B :=
  Monad_rec M (forall (A B : Set), M A -> (A -> M B) -> M B)
    (fun (r : forall (A : Set), A -> M A)
         (b : forall (A B : Set), M A -> (A -> M B) -> M B) => b) MM A B ma f.

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
