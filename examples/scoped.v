(* Intrinsically well-scoped lambda terms via the Inductive command.

   [Tm] is declared with [Inductive] as a family indexed by the number of free
   variables, so the generated indexed fold [Tm_rec] (motive [X : nat -> Set])
   computes.  Capture-avoiding [rename] recurses at the index-dependent motive
   [X m = forall n, (Fin m -> Fin n) -> Tm n], which the indexed encoding
   supports.

   [Fin] (and its inversion [fin_case]) is kept axiomatic, as in [fin.v]: the
   fold does not give one-step inversion. *)


Inductive nat : Set := | O : nat | S : nat -> nat.

(* [Fin] is kept axiomatic here: [rename] recurses over [Tm] (indexed by nat)
   and also uses [fin_case] inversion, and making [Fin] inductive too makes the
   substituted encodings in [rename] blow up the extractor.  [Tm] uses
   [Inductive]. *)
Axiom Fin : nat -> Set.
Axiom F1 : forall (n : nat), Fin (S n).
Axiom FS : forall (n : nat), Fin n -> Fin (S n).
Axiom fin_case :
  forall (n : nat) (C : Set), C -> (Fin n -> C) -> Fin (S n) -> C.


Inductive Tm : nat -> Set :=
  | tvar : forall (n : nat), Fin n -> Tm n
  | tapp : forall (n : nat), Tm n -> Tm n -> Tm n
  | tlam : forall (n : nat), Tm (S n) -> Tm n.


(* size: node count (motive ignores the index). *)

Definition size (n : nat) (t : Tm n) : nat :=
  Tm_rec (fun (_ : nat) => nat)
    (fun (n0 : nat) (_ : Fin n0) => S O)
    (fun (n0 : nat) (rf ra : nat) => S (nat_rec nat rf (fun (r : nat) => S r) ra))
    (fun (n0 : nat) (rb : nat) => S rb)
    n t.

Check size.
Extract size.


(* ext: extend a renaming under a binder. *)

Definition ext (m n : nat) (r : Fin m -> Fin n) : Fin (S m) -> Fin (S n) :=
  fun (j : Fin (S m)) =>
    fin_case m (Fin (S n)) (F1 n) (fun (i : Fin m) => FS n (r i)) j.

Extract ext.


(* rename: apply a variable renaming throughout a term, at the index-dependent
   motive [X m = forall n, (Fin m -> Fin n) -> Tm n]. *)

Definition rename (m : nat) (t : Tm m)
  : forall (n : nat), (Fin m -> Fin n) -> Tm n :=
  Tm_rec (fun (m0 : nat) => forall (n : nat), (Fin m0 -> Fin n) -> Tm n)
    (fun (m0 : nat) (i : Fin m0) (n : nat) (r : Fin m0 -> Fin n) =>
       tvar n (r i))
    (fun (m0 : nat)
         (rf : forall (n : nat), (Fin m0 -> Fin n) -> Tm n)
         (ra : forall (n : nat), (Fin m0 -> Fin n) -> Tm n)
         (n : nat) (r : Fin m0 -> Fin n) =>
       tapp n (rf n r) (ra n r))
    (fun (m0 : nat)
         (rb : forall (n : nat), (Fin (S m0) -> Fin n) -> Tm n)
         (n : nat) (r : Fin m0 -> Fin n) =>
       tlam n (rb (S n) (ext m0 n r)))
    m t.

Check rename.
Extract rename.


(* weaken: shift every free variable up by one. *)

Definition weaken (n : nat) (t : Tm n) : Tm (S n) :=
  rename n t (S n) (FS n).

Check weaken : forall (n : nat), Tm n -> Tm (S n).
Extract weaken.


(* the identity  \x. x  as a closed term (index O). *)

Definition tI : Tm O :=
  tlam O (tvar (S O) (F1 O)).

Extract tI.


(* The boundary: [Tm] as a value in type position -> Dyn + internal blame. *)

Extract fun (n : nat) => Tm n.
