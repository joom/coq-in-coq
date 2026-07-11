(* Polymorphic lists via the Inductive command.

   The non-indexed baseline: [Inductive list (A : Set) : Set := ...] desugars to
   the impredicative Boehm-Berarducci encoding, so every function is an ordinary
   fold over the generated recursor [list_rec] and the data COMPUTES.  There is
   no dependent index to erase, so extraction preserves the structure exactly.

   [list_rec : forall (A : Set) (X : Set), X -> (A -> X -> X) -> list A -> X]
   is the catamorphism (the recursive argument is already folded to [X]). *)


Inductive bool : Set := | true : bool | false : bool.

Inductive nat : Set := | O : nat | S : nat -> nat.

Inductive list (A : Set) : Set :=
  | nil : list A
  | cons : A -> list A -> list A.


(* app: concatenation. *)

Definition app (A : Set) (xs ys : list A) : list A :=
  list_rec A (list A) ys (fun (x : A) (r : list A) => cons A x r) xs.

Check app.
Extract app.


(* map. *)

Definition map (A B : Set) (f : A -> B) (xs : list A) : list B :=
  list_rec A (list B) (nil B) (fun (x : A) (r : list B) => cons B (f x) r) xs.

Check map.
Extract map.


(* fold_right. *)

Definition fold_right (A B : Set) (f : A -> B -> B) (z : B) (xs : list A) : B :=
  list_rec A B z (fun (x : A) (r : B) => f x r) xs.

Extract fold_right.


(* length. *)

Definition length (A : Set) (xs : list A) : nat :=
  list_rec A nat O (fun (_ : A) (r : nat) => S r) xs.

Compute length nat (cons nat O (cons nat (S O) (nil nat))).


(* rev, via the difference-list trick (motive [list A -> list A]). *)

Definition rev (A : Set) (xs : list A) : list A :=
  list_rec A (list A -> list A)
    (fun (acc : list A) => acc)
    (fun (x : A) (r : list A -> list A) (acc : list A) => r (cons A x acc))
    xs
    (nil A).

Check rev.
Extract rev.


(* filter: [bool_rec] is the generated case principle for [bool]. *)

Definition filter (A : Set) (p : A -> bool) (xs : list A) : list A :=
  list_rec A (list A) (nil A)
    (fun (x : A) (r : list A) => bool_rec (list A) (cons A x r) r (p x))
    xs.

Extract filter.


(* flat_map (list bind): map then concatenate. *)

Definition flat_map (A B : Set) (f : A -> list B) (xs : list A) : list B :=
  list_rec A (list B) (nil B) (fun (x : A) (r : list B) => app B (f x) r) xs.

Extract flat_map.
