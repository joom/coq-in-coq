(* Height-indexed balanced trees in the Calculus of Constructions.

   [Tree h] is a binary search tree whose type records its height [h].  The
   [node] constructor only accepts two subtrees of the SAME height, so the
   balancing invariant is enforced by the type: an unbalanced tree is
   ill-typed and cannot be built.  (This is the AVL/Braun-style "make illegal
   states unrepresentable" idea in its purest form.)

   Extraction erases the height: [Tree h] becomes the plain type [Tree], and
   constructors/operations become ordinary data.  The invariant that guided
   construction has no run-time footprint, yet the extracted program is
   certified to simulate the source.  [height] shows the dual direction --
   recovering the erased index as an honest run-time [Nat] via the eliminator. *)


Axiom Nat : Set.
Axiom NZ : Nat.
Axiom NS : Nat -> Nat.
Axiom add : Nat -> Nat -> Nat.

Axiom Elem : Set.

(* Perfectly balanced trees indexed by height. *)
Axiom Tree : Nat -> Set.
Axiom leaf : Tree NZ.
Axiom node : forall (h : Nat), Elem -> Tree h -> Tree h -> Tree (NS h).

(* Dependent eliminator (fold) over height-indexed trees. *)
Axiom tree_rec :
  forall (P : Nat -> Set),
  P NZ ->
  (forall (h : Nat), Elem -> P h -> P h -> P (NS h)) ->
  forall (h : Nat), Tree h -> P h.


(* Build a balanced tree of height 2 from a single element.  Only type-checks
   because both subtrees at each level have matching heights. *)

Infer fun (x : Elem) =>
  node (NS NZ) x
    (node NZ x leaf leaf)
    (node NZ x leaf leaf).

Extract fun (x : Elem) =>
  node (NS NZ) x
    (node NZ x leaf leaf)
    (node NZ x leaf leaf).


(* mirror: swap left and right subtrees, preserving the height index. *)

Extract fun (h : Nat) (t : Tree h) =>
  tree_rec (fun (k : Nat) => Tree k)
    leaf
    (fun (k : Nat) (x : Elem) (l r : Tree k) => node k x r l)
    h t.


(* count the nodes: fold into a plain Nat, ignoring the height motive.
   The result type does not mention h, so it extracts cleanly to Tree -> Nat. *)

Extract fun (h : Nat) (t : Tree h) =>
  tree_rec (fun (_ : Nat) => Nat)
    NZ
    (fun (k : Nat) (x : Elem) (cl cr : Nat) => NS (add cl cr))
    h t.
