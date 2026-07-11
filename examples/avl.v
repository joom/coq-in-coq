(* Height-indexed balanced trees via the Inductive command.

   [Tree h] is a binary tree whose type records its height [h].  [node] only
   accepts two subtrees of the SAME height, so the balancing invariant is
   enforced by the type: an unbalanced tree is ill-typed.

   [nat] and [Tree] are declared with [Inductive] (indexed Boehm-Berarducci),
   so their recursors are generated and the data computes.  [Elem] is an
   abstract element type, so it stays an [Axiom].  Extraction erases the
   height: [Tree h] becomes the plain type [Tree]. *)


Inductive nat : Set := | O : nat | S : nat -> nat.

Definition add (a b : nat) : nat :=
  nat_rec nat b (fun (r : nat) => S r) a.

Axiom Elem : Set.

(* Perfectly balanced trees indexed by height. *)
Inductive Tree : nat -> Set :=
  | leaf : Tree O
  | node : forall (h : nat), Elem -> Tree h -> Tree h -> Tree (S h).


(* Build a balanced tree of height 2 from a single element.  Only type-checks
   because both subtrees at each level have matching heights. *)

Definition example_tree (x : Elem) : Tree (S (S O)) :=
  node (S O) x
    (node O x leaf leaf)
    (node O x leaf leaf).

Check example_tree.

Extract example_tree.


(* mirror: swap left and right subtrees, preserving the height index. *)

Definition mirror (h : nat) (t : Tree h) : Tree h :=
  Tree_rec (fun (k : nat) => Tree k)
    leaf
    (fun (k : nat) (x : Elem) (l r : Tree k) => node k x r l)
    h t.

Extract mirror.


(* count the nodes: fold into a plain nat, ignoring the height motive.
   The result type does not mention h, so it extracts cleanly to Tree -> nat. *)

Definition count (h : nat) (t : Tree h) : nat :=
  Tree_rec (fun (_ : nat) => nat)
    O
    (fun (k : nat) (x : Elem) (cl cr : nat) => S (add cl cr))
    h t.

Extract count.
