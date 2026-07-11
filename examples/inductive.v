(* The [Inductive] command and [Compute], in the Calculus of Constructions.

   [Inductive] is sugar for the impredicative Church / Boehm-Berarducci
   encoding.  It generates ordinary DEFINITIONS -- the type former, the
   constructors, and a non-dependent recursor [<T>_rec] (a fold) -- so, unlike
   the axiomatized inductive kit used elsewhere in these examples, the data
   actually COMPUTES.  [Compute] shows that: it prints the beta-delta normal
   form of a term (definitions are inlined, then beta-normalized by the
   verified normalizer).

   Because the constructors are Church encodings, a computed value is the
   ENCODED normal form -- the constructors unfold into the fold they denote
   (e.g. the numeral 3 becomes  fun (X : Set) (fNZ : X) (fNS : X -> X) =>
   fNS (fNS (fNS fNZ))).

   Scope: [Inductive] supports parameters AND indices via the indexed
   Boehm-Berarducci encoding (the motive is index-parameterized), with
   first-order strictly-positive constructors.  The generated recursor is the
   INDEX-dependent recursor -- not value-dependent induction, which no
   impredicative encoding can provide (Geuvers 2001); large elimination and
   one-step inversion therefore remain out of reach.  See the indexed section
   below and the paper for the full typeability/computability story. *)


(* Booleans. *)

Inductive bool : Set := | true : bool | false : bool.

Definition negb (b : bool) : bool :=
  bool_rec bool false true b.

Compute negb true.
Compute negb false.


(* Natural numbers.  We bar every constructor uniformly; a leading bar before
   the first constructor is optional in the grammar, but we include it. *)

Inductive nat : Set :=
  | O : nat
  | S : nat -> nat.

(* nat_rec : forall (X : Set), X -> (X -> X) -> nat -> X   (the iterator). *)

Definition add (m n : nat) : nat :=
  nat_rec nat n (fun (r : nat) => S r) m.

Definition mul (m n : nat) : nat :=
  nat_rec nat O (fun (r : nat) => add n r) m.

(* 2 + 1 = 3, shown as the Church numeral 3. *)
Compute add (S (S O)) (S O).

(* 2 * 2 = 4. *)
Compute mul (S (S O)) (S (S O)).


(* Polymorphic lists (a parameterized inductive). *)

Inductive list (A : Set) : Set :=
  | nil : list A
  | cons : A -> list A -> list A.

Definition length (A : Set) (xs : list A) : nat :=
  list_rec A nat O (fun (_ : A) (r : nat) => S r) xs.

Definition app (A : Set) (xs ys : list A) : list A :=
  list_rec A (list A) ys (fun (x : A) (r : list A) => cons A x r) xs.

(* length [O, 1] = 2. *)
Compute length nat (cons nat O (cons nat (S O) (nil nat))).


(* Binary trees: a constructor with two recursive arguments. *)

Inductive Tree : Set :=
  | leaf : Tree
  | node : Tree -> Tree -> Tree.

(* count the leaves. *)
Definition leaves (t : Tree) : nat :=
  Tree_rec nat (S O) (fun (l r : nat) => add l r) t.

Compute leaves (node (node leaf leaf) leaf).


(* Compute also works on ordinary terms (plain beta reduction). *)

Compute (fun (A : Set) (x : A) => x) nat O.


(* Extraction still works on the generated definitions: the constructors
   erase to their Church encodings in System F-omega + blame. *)

Extract S.


(* --- Indexed families ------------------------------------------------------

   The indexed Boehm-Berarducci encoding: the motive is parameterized by the
   index, so an indexed family is a lambda-term whose recursor computes. *)

(* length-indexed vectors *)
Inductive Vec (A : Set) : nat -> Set :=
  | vnil : Vec A O
  | vcons : forall (n : nat), A -> Vec A n -> Vec A (S n).

Definition vmap (A B : Set) (f : A -> B) (n : nat) (v : Vec A n) : Vec B n :=
  Vec_rec A (fun (m : nat) => Vec B m)
    (vnil B)
    (fun (m : nat) (a : A) (acc : Vec B m) => vcons B m (f a) acc)
    n v.

(* map the successor over [0, 1] : Vec nat 2 -- the indexed encoding computes. *)
Compute vmap nat nat (fun (x : nat) => S x) (S (S O))
  (vcons nat (S O) (S O) (vcons nat O O (vnil nat))).

(* Leibniz equality: the generated [eq_rec] IS transport, and it computes. *)
Inductive eq (A : Set) (x : A) : A -> Prop := | eq_refl : eq A x x.

Definition eq_sym (A : Set) (x y : A) (h : eq A x y) : eq A y x :=
  eq_rec A x (fun (z : A) => eq A z x) (eq_refl A x) y h.

Extract eq_sym.
