Require Extraction.
Extraction Language OCaml.

Inductive nat : Set := O : nat | S : nat -> nat.
Inductive bool : Set := true : bool | false : bool.

Inductive TList : Type := tnil : TList | tcons : Set -> TList -> TList.

Inductive HList : TList -> Type :=
| hnil : HList tnil
| hcons : forall (A : Set) (ts : TList), A -> HList ts -> HList (tcons A ts).

Definition hhead {A : Set} {ts : TList} (h : HList (tcons A ts)) : A :=
  match h in HList l return match l with tnil => unit | tcons B _ => B end with
  | hnil => tt
  | hcons _ _ a _ => a
  end.

Definition htail {A : Set} {ts : TList} (h : HList (tcons A ts)) : HList ts :=
  match h in HList l return match l with tnil => unit | tcons _ ts' => HList ts' end with
  | hnil => tt
  | hcons _ _ _ r => r
  end.

Definition first (A : Set) (ts : TList) (h : HList (tcons A ts)) : A := hhead h.

Definition second (A B : Set) (ts : TList) (h : HList (tcons A (tcons B ts))) : B :=
  hhead (htail h).

Definition sample : HList (tcons nat (tcons bool tnil)) :=
  hcons nat (tcons bool tnil) O (hcons bool tnil true hnil).

Definition first_of_sample : nat := first nat (tcons bool tnil) sample.

Extraction "ex_hlist.ml" first second sample first_of_sample.
