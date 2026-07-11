(* Heterogeneous lists via the Inductive command.

   [TList] (a list of [Set]s) is declared with [Inductive].  [HList] is indexed
   by a [TList]; its projections need one-step INVERSION on a [tcons]-shaped
   list, which is not the fold and is not derivable from the impredicative
   encoding.  So [HList] and its inversion principles [hhead]/[htail] are kept
   axiomatic, while [nat], [bool], and [TList] use [Inductive]. *)


Inductive nat : Set := | O : nat | S : nat -> nat.

Inductive bool : Set := | true : bool | false : bool.

Inductive TList : Set := | tnil : TList | tcons : Set -> TList -> TList.

(* Heterogeneous lists.  [HList] and its recursor are generated; only the
   one-step projections [hhead]/[htail], which invert a [tcons] shape rather
   than fold, stay axiomatic. *)
Inductive HList : TList -> Set :=
  | hnil : HList tnil
  | hcons : forall (A : Set) (ts : TList), A -> HList ts -> HList (tcons A ts).

Axiom hhead : forall (A : Set) (ts : TList), HList (tcons A ts) -> A.
Axiom htail : forall (A : Set) (ts : TList), HList (tcons A ts) -> HList ts.


(* first projection: read the head element at its own type. *)

Definition first (A : Set) (ts : TList) (h : HList (tcons A ts)) : A :=
  hhead A ts h.

Check first.
Extract first.


(* second projection: skip the head, read the next element. *)

Definition second (A B : Set) (ts : TList)
  (h : HList (tcons A (tcons B ts))) : B :=
  hhead B ts (htail A (tcons B ts) h).

Check second.
Extract second.


(* A concrete heterogeneous pair  [O ; true] : HList [nat, bool]. *)

Definition sample : HList (tcons nat (tcons bool tnil)) :=
  hcons nat (tcons bool tnil) O
    (hcons bool tnil true hnil).

Check sample : HList (tcons nat (tcons bool tnil)).
Extract sample.

Extract first nat (tcons bool tnil) sample.


(* The boundary: [HList] as a value in type position -> Dyn + internal blame. *)

Extract fun (ts : TList) => HList ts.
