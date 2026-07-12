Require Extraction.
Extraction Language OCaml.

Inductive nat : Set := O : nat | S : nat -> nat.

(* typeclass-style records over a type constructor F : Set -> Set *)
Inductive Functor (F : Set -> Set) : Type :=
| mkFunctor : (forall A B : Set, (A -> B) -> F A -> F B) -> Functor F.

Definition fmap {F : Set -> Set} (FF : Functor F)
  {A B : Set} (f : A -> B) (x : F A) : F B :=
  match FF with mkFunctor _ m => m A B f x end.

Definition mapmap {F : Set -> Set} (FF : Functor F) {A B C : Set}
  (f : A -> B) (g : B -> C) (xs : F A) : F C :=
  fmap FF g (fmap FF f xs).

Inductive Sym (R : Set -> Set) : Type :=
| mkSym : (nat -> R nat) -> (R nat -> R nat -> R nat) -> Sym R.

Definition lit {R : Set -> Set} (s : Sym R) (n : nat) : R nat :=
  match s with mkSym _ l _ => l n end.

Definition add {R : Set -> Set} (s : Sym R) (x y : R nat) : R nat :=
  match s with mkSym _ _ a => a x y end.

Definition double {R : Set -> Set} (s : Sym R) (n : nat) : R nat :=
  add s (lit s n) (lit s n).

Inductive Monad (M : Set -> Set) : Type :=
| mkMonad :
    (forall A : Set, A -> M A) ->
    (forall A B : Set, M A -> (A -> M B) -> M B) ->
    Monad M.

Definition ret {M : Set -> Set} (MM : Monad M) {A : Set} (x : A) : M A :=
  match MM with mkMonad _ r _ => r A x end.

Definition bind {M : Set -> Set} (MM : Monad M) {A B : Set}
  (ma : M A) (f : A -> M B) : M B :=
  match MM with mkMonad _ _ b => b A B ma f end.

Definition kleisli {M : Set -> Set} (MM : Monad M) {A B C : Set}
  (ma : M A) (f : A -> M B) (g : B -> M C) : M C :=
  bind MM (bind MM ma f) g.

Extraction "ex_functor.ml" fmap mapmap lit add double ret bind kleisli.
