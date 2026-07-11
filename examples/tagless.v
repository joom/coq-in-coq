(* An intrinsically typed expression language whose evaluator has a
   COMPUTED return type -- CIC's

     Fixpoint eval {t} (e : expr t)
       : match t with TNat => nat | TBool => bool end := ...

   -- expressed in bare CoC with NO inductive types, NO universes, and NO
   large elimination.  This is the example one expects to force the dynamic
   type: the return type depends on a run-time tag.  It does not.

   The trick is to Church-encode the object types ONE LEVEL UP, as type-level
   booleans of kind  Set -> Set -> Set:
       TNat = fun (a b : Set) => a       TBool = fun (a b : Set) => b
   CIC's large elimination  [match t with TNat => nat | TBool => bool]
   becomes type-level APPLICATION  [t CNat CBool],  discharged by ordinary
   beta conversion -- and the whole file extracts with NO dyn, NO casts, and
   NO blame: the F-omega target expresses the computed type natively, at the
   higher kind  * => * => *.

   Contrast the two bare-CoC neighbours of this program:
   - term-level codes with an axiomatized decoder ([El : ty -> Set],
     stlc.v): eval extracts at the RIGID abstract type [El] -- every
     computed type collapses into one opaque target type, and the source
     cannot even use the result (no [El TNat = nat] conversion);
   - true CIC [match t ... : Set] -- a term-headed type computation that
     survives normalization -- is what would land in the translation's
     dyn fallback.  That requires large elimination in the SOURCE, i.e. the
     CIC extension discussed in the paper.

   Since REPL definitions are opaque (no delta in the PTS), every encoded
   TYPE is written out literally; only TERMS get names. *)

(* Church booleans:  CBool = forall (X : Set), X -> X -> X *)

Definition ctrue : forall (X : Set), X -> X -> X :=
  fun (X : Set) (t f : X) => t.
Definition cfalse : forall (X : Set), X -> X -> X :=
  fun (X : Set) (t f : X) => f.
Definition andb (a b : forall (X : Set), X -> X -> X)
  : forall (X : Set), X -> X -> X :=
  a (forall (X : Set), X -> X -> X) b cfalse.

(* Church naturals:  CNat = forall (X : Set), (X -> X) -> X -> X *)

Definition czero : forall (X : Set), (X -> X) -> X -> X :=
  fun (X : Set) (s : X -> X) (z : X) => z.
Definition csucc (n : forall (X : Set), (X -> X) -> X -> X)
  : forall (X : Set), (X -> X) -> X -> X :=
  fun (X : Set) (s : X -> X) (z : X) => s (n X s z).
Definition cone : forall (X : Set), (X -> X) -> X -> X := csucc czero.
Definition ctwo : forall (X : Set), (X -> X) -> X -> X := csucc cone.

Definition cadd (m n : forall (X : Set), (X -> X) -> X -> X)
  : forall (X : Set), (X -> X) -> X -> X :=
  fun (X : Set) (s : X -> X) (z : X) => m X s (n X s z).

(* Equality of Church naturals, via pairs / pred / truncated subtraction. *)

Definition mkpair (a b : forall (X : Set), (X -> X) -> X -> X)
  : forall (Z : Set),
    ((forall (X : Set), (X -> X) -> X -> X) ->
     (forall (X : Set), (X -> X) -> X -> X) -> Z) -> Z :=
  fun (Z : Set)
      (k : (forall (X : Set), (X -> X) -> X -> X) ->
           (forall (X : Set), (X -> X) -> X -> X) -> Z) => k a b.

Definition cpred (n : forall (X : Set), (X -> X) -> X -> X)
  : forall (X : Set), (X -> X) -> X -> X :=
  n (forall (Z : Set),
     ((forall (X : Set), (X -> X) -> X -> X) ->
      (forall (X : Set), (X -> X) -> X -> X) -> Z) -> Z)
    (fun (p : forall (Z : Set),
              ((forall (X : Set), (X -> X) -> X -> X) ->
               (forall (X : Set), (X -> X) -> X -> X) -> Z) -> Z) =>
     p (forall (Z : Set),
        ((forall (X : Set), (X -> X) -> X -> X) ->
         (forall (X : Set), (X -> X) -> X -> X) -> Z) -> Z)
       (fun (a b : forall (X : Set), (X -> X) -> X -> X) =>
        mkpair b (csucc b)))
    (mkpair czero czero)
    (forall (X : Set), (X -> X) -> X -> X)
    (fun (a b : forall (X : Set), (X -> X) -> X -> X) => a).

Definition csub (m n : forall (X : Set), (X -> X) -> X -> X)
  : forall (X : Set), (X -> X) -> X -> X :=
  n (forall (X : Set), (X -> X) -> X -> X) cpred m.

Definition iszero (n : forall (X : Set), (X -> X) -> X -> X)
  : forall (X : Set), X -> X -> X :=
  n (forall (X : Set), X -> X -> X)
    (fun (_ : forall (X : Set), X -> X -> X) => cfalse)
    ctrue.

Definition ceqb (m n : forall (X : Set), (X -> X) -> X -> X)
  : forall (X : Set), X -> X -> X :=
  andb (iszero (csub m n)) (iszero (csub n m)).

(* The indexed family  expr : (Set -> Set -> Set) -> Set,  Church-encoded.
   An [expr t] is its own fold: give a motive P over type codes and one
   case per constructor, receive  P t. *)

Definition ENat (n : forall (X : Set), (X -> X) -> X -> X)
  : forall (P : (forall (a b : Set), Set) -> Set),
    ((forall (X : Set), (X -> X) -> X -> X) -> P (fun (a b : Set) => a)) ->
    ((forall (X : Set), X -> X -> X) -> P (fun (a b : Set) => b)) ->
    (P (fun (a b : Set) => a) -> P (fun (a b : Set) => a) -> P (fun (a b : Set) => a)) ->
    (P (fun (a b : Set) => a) -> P (fun (a b : Set) => a) -> P (fun (a b : Set) => b)) ->
    (forall (u : forall (a b : Set), Set),
     P (fun (a b : Set) => b) -> P u -> P u -> P u) ->
    P (fun (a b : Set) => a) :=
  fun (P : (forall (a b : Set), Set) -> Set)
      (cnat : (forall (X : Set), (X -> X) -> X -> X) -> P (fun (a b : Set) => a))
      (cbool : (forall (X : Set), X -> X -> X) -> P (fun (a b : Set) => b))
      (cadd0 : P (fun (a b : Set) => a) -> P (fun (a b : Set) => a) -> P (fun (a b : Set) => a))
      (ceq0 : P (fun (a b : Set) => a) -> P (fun (a b : Set) => a) -> P (fun (a b : Set) => b))
      (cif0 : forall (u : forall (a b : Set), Set),
              P (fun (a b : Set) => b) -> P u -> P u -> P u) =>
  cnat n.

Definition EBool (v : forall (X : Set), X -> X -> X)
  : forall (P : (forall (a b : Set), Set) -> Set),
    ((forall (X : Set), (X -> X) -> X -> X) -> P (fun (a b : Set) => a)) ->
    ((forall (X : Set), X -> X -> X) -> P (fun (a b : Set) => b)) ->
    (P (fun (a b : Set) => a) -> P (fun (a b : Set) => a) -> P (fun (a b : Set) => a)) ->
    (P (fun (a b : Set) => a) -> P (fun (a b : Set) => a) -> P (fun (a b : Set) => b)) ->
    (forall (u : forall (a b : Set), Set),
     P (fun (a b : Set) => b) -> P u -> P u -> P u) ->
    P (fun (a b : Set) => b) :=
  fun (P : (forall (a b : Set), Set) -> Set)
      (cnat : (forall (X : Set), (X -> X) -> X -> X) -> P (fun (a b : Set) => a))
      (cbool : (forall (X : Set), X -> X -> X) -> P (fun (a b : Set) => b))
      (cadd0 : P (fun (a b : Set) => a) -> P (fun (a b : Set) => a) -> P (fun (a b : Set) => a))
      (ceq0 : P (fun (a b : Set) => a) -> P (fun (a b : Set) => a) -> P (fun (a b : Set) => b))
      (cif0 : forall (u : forall (a b : Set), Set),
              P (fun (a b : Set) => b) -> P u -> P u -> P u) =>
  cbool v.

Definition EAdd
  (x : forall (P : (forall (a b : Set), Set) -> Set),
       ((forall (X : Set), (X -> X) -> X -> X) -> P (fun (a b : Set) => a)) ->
       ((forall (X : Set), X -> X -> X) -> P (fun (a b : Set) => b)) ->
       (P (fun (a b : Set) => a) -> P (fun (a b : Set) => a) -> P (fun (a b : Set) => a)) ->
       (P (fun (a b : Set) => a) -> P (fun (a b : Set) => a) -> P (fun (a b : Set) => b)) ->
       (forall (u : forall (a b : Set), Set),
        P (fun (a b : Set) => b) -> P u -> P u -> P u) ->
       P (fun (a b : Set) => a))
  (y : forall (P : (forall (a b : Set), Set) -> Set),
       ((forall (X : Set), (X -> X) -> X -> X) -> P (fun (a b : Set) => a)) ->
       ((forall (X : Set), X -> X -> X) -> P (fun (a b : Set) => b)) ->
       (P (fun (a b : Set) => a) -> P (fun (a b : Set) => a) -> P (fun (a b : Set) => a)) ->
       (P (fun (a b : Set) => a) -> P (fun (a b : Set) => a) -> P (fun (a b : Set) => b)) ->
       (forall (u : forall (a b : Set), Set),
        P (fun (a b : Set) => b) -> P u -> P u -> P u) ->
       P (fun (a b : Set) => a))
  : forall (P : (forall (a b : Set), Set) -> Set),
    ((forall (X : Set), (X -> X) -> X -> X) -> P (fun (a b : Set) => a)) ->
    ((forall (X : Set), X -> X -> X) -> P (fun (a b : Set) => b)) ->
    (P (fun (a b : Set) => a) -> P (fun (a b : Set) => a) -> P (fun (a b : Set) => a)) ->
    (P (fun (a b : Set) => a) -> P (fun (a b : Set) => a) -> P (fun (a b : Set) => b)) ->
    (forall (u : forall (a b : Set), Set),
     P (fun (a b : Set) => b) -> P u -> P u -> P u) ->
    P (fun (a b : Set) => a) :=
  fun (P : (forall (a b : Set), Set) -> Set)
      (cnat : (forall (X : Set), (X -> X) -> X -> X) -> P (fun (a b : Set) => a))
      (cbool : (forall (X : Set), X -> X -> X) -> P (fun (a b : Set) => b))
      (cadd0 : P (fun (a b : Set) => a) -> P (fun (a b : Set) => a) -> P (fun (a b : Set) => a))
      (ceq0 : P (fun (a b : Set) => a) -> P (fun (a b : Set) => a) -> P (fun (a b : Set) => b))
      (cif0 : forall (u : forall (a b : Set), Set),
              P (fun (a b : Set) => b) -> P u -> P u -> P u) =>
  cadd0 (x P cnat cbool cadd0 ceq0 cif0) (y P cnat cbool cadd0 ceq0 cif0).

Definition EEq
  (x : forall (P : (forall (a b : Set), Set) -> Set),
       ((forall (X : Set), (X -> X) -> X -> X) -> P (fun (a b : Set) => a)) ->
       ((forall (X : Set), X -> X -> X) -> P (fun (a b : Set) => b)) ->
       (P (fun (a b : Set) => a) -> P (fun (a b : Set) => a) -> P (fun (a b : Set) => a)) ->
       (P (fun (a b : Set) => a) -> P (fun (a b : Set) => a) -> P (fun (a b : Set) => b)) ->
       (forall (u : forall (a b : Set), Set),
        P (fun (a b : Set) => b) -> P u -> P u -> P u) ->
       P (fun (a b : Set) => a))
  (y : forall (P : (forall (a b : Set), Set) -> Set),
       ((forall (X : Set), (X -> X) -> X -> X) -> P (fun (a b : Set) => a)) ->
       ((forall (X : Set), X -> X -> X) -> P (fun (a b : Set) => b)) ->
       (P (fun (a b : Set) => a) -> P (fun (a b : Set) => a) -> P (fun (a b : Set) => a)) ->
       (P (fun (a b : Set) => a) -> P (fun (a b : Set) => a) -> P (fun (a b : Set) => b)) ->
       (forall (u : forall (a b : Set), Set),
        P (fun (a b : Set) => b) -> P u -> P u -> P u) ->
       P (fun (a b : Set) => a))
  : forall (P : (forall (a b : Set), Set) -> Set),
    ((forall (X : Set), (X -> X) -> X -> X) -> P (fun (a b : Set) => a)) ->
    ((forall (X : Set), X -> X -> X) -> P (fun (a b : Set) => b)) ->
    (P (fun (a b : Set) => a) -> P (fun (a b : Set) => a) -> P (fun (a b : Set) => a)) ->
    (P (fun (a b : Set) => a) -> P (fun (a b : Set) => a) -> P (fun (a b : Set) => b)) ->
    (forall (u : forall (a b : Set), Set),
     P (fun (a b : Set) => b) -> P u -> P u -> P u) ->
    P (fun (a b : Set) => b) :=
  fun (P : (forall (a b : Set), Set) -> Set)
      (cnat : (forall (X : Set), (X -> X) -> X -> X) -> P (fun (a b : Set) => a))
      (cbool : (forall (X : Set), X -> X -> X) -> P (fun (a b : Set) => b))
      (cadd0 : P (fun (a b : Set) => a) -> P (fun (a b : Set) => a) -> P (fun (a b : Set) => a))
      (ceq0 : P (fun (a b : Set) => a) -> P (fun (a b : Set) => a) -> P (fun (a b : Set) => b))
      (cif0 : forall (u : forall (a b : Set), Set),
              P (fun (a b : Set) => b) -> P u -> P u -> P u) =>
  ceq0 (x P cnat cbool cadd0 ceq0 cif0) (y P cnat cbool cadd0 ceq0 cif0).

Definition EIf (t : forall (a b : Set), Set)
  (c : forall (P : (forall (a b : Set), Set) -> Set),
       ((forall (X : Set), (X -> X) -> X -> X) -> P (fun (a b : Set) => a)) ->
       ((forall (X : Set), X -> X -> X) -> P (fun (a b : Set) => b)) ->
       (P (fun (a b : Set) => a) -> P (fun (a b : Set) => a) -> P (fun (a b : Set) => a)) ->
       (P (fun (a b : Set) => a) -> P (fun (a b : Set) => a) -> P (fun (a b : Set) => b)) ->
       (forall (u : forall (a b : Set), Set),
        P (fun (a b : Set) => b) -> P u -> P u -> P u) ->
       P (fun (a b : Set) => b))
  (th : forall (P : (forall (a b : Set), Set) -> Set),
        ((forall (X : Set), (X -> X) -> X -> X) -> P (fun (a b : Set) => a)) ->
        ((forall (X : Set), X -> X -> X) -> P (fun (a b : Set) => b)) ->
        (P (fun (a b : Set) => a) -> P (fun (a b : Set) => a) -> P (fun (a b : Set) => a)) ->
        (P (fun (a b : Set) => a) -> P (fun (a b : Set) => a) -> P (fun (a b : Set) => b)) ->
        (forall (u : forall (a b : Set), Set),
         P (fun (a b : Set) => b) -> P u -> P u -> P u) ->
        P t)
  (el : forall (P : (forall (a b : Set), Set) -> Set),
        ((forall (X : Set), (X -> X) -> X -> X) -> P (fun (a b : Set) => a)) ->
        ((forall (X : Set), X -> X -> X) -> P (fun (a b : Set) => b)) ->
        (P (fun (a b : Set) => a) -> P (fun (a b : Set) => a) -> P (fun (a b : Set) => a)) ->
        (P (fun (a b : Set) => a) -> P (fun (a b : Set) => a) -> P (fun (a b : Set) => b)) ->
        (forall (u : forall (a b : Set), Set),
         P (fun (a b : Set) => b) -> P u -> P u -> P u) ->
        P t)
  : forall (P : (forall (a b : Set), Set) -> Set),
    ((forall (X : Set), (X -> X) -> X -> X) -> P (fun (a b : Set) => a)) ->
    ((forall (X : Set), X -> X -> X) -> P (fun (a b : Set) => b)) ->
    (P (fun (a b : Set) => a) -> P (fun (a b : Set) => a) -> P (fun (a b : Set) => a)) ->
    (P (fun (a b : Set) => a) -> P (fun (a b : Set) => a) -> P (fun (a b : Set) => b)) ->
    (forall (u : forall (a b : Set), Set),
     P (fun (a b : Set) => b) -> P u -> P u -> P u) ->
    P t :=
  fun (P : (forall (a b : Set), Set) -> Set)
      (cnat : (forall (X : Set), (X -> X) -> X -> X) -> P (fun (a b : Set) => a))
      (cbool : (forall (X : Set), X -> X -> X) -> P (fun (a b : Set) => b))
      (cadd0 : P (fun (a b : Set) => a) -> P (fun (a b : Set) => a) -> P (fun (a b : Set) => a))
      (ceq0 : P (fun (a b : Set) => a) -> P (fun (a b : Set) => a) -> P (fun (a b : Set) => b))
      (cif0 : forall (u : forall (a b : Set), Set),
              P (fun (a b : Set) => b) -> P u -> P u -> P u) =>
  cif0 t (c P cnat cbool cadd0 ceq0 cif0)
         (th P cnat cbool cadd0 ceq0 cif0)
         (el P cnat cbool cadd0 ceq0 cif0).

(* eval: the fold at motive  P u = u CNat CBool.  CIC's
   [match t with TNat => nat | TBool => bool]  is the type-level
   application  [t CNat CBool]  -- no large elimination, no universes. *)

Definition eval (t : forall (a b : Set), Set)
  (e : forall (P : (forall (a b : Set), Set) -> Set),
       ((forall (X : Set), (X -> X) -> X -> X) -> P (fun (a b : Set) => a)) ->
       ((forall (X : Set), X -> X -> X) -> P (fun (a b : Set) => b)) ->
       (P (fun (a b : Set) => a) -> P (fun (a b : Set) => a) -> P (fun (a b : Set) => a)) ->
       (P (fun (a b : Set) => a) -> P (fun (a b : Set) => a) -> P (fun (a b : Set) => b)) ->
       (forall (u : forall (a b : Set), Set),
        P (fun (a b : Set) => b) -> P u -> P u -> P u) ->
       P t)
  : t (forall (X : Set), (X -> X) -> X -> X) (forall (X : Set), X -> X -> X) :=
  e (fun (u : forall (a b : Set), Set) =>
       u (forall (X : Set), (X -> X) -> X -> X) (forall (X : Set), X -> X -> X))
    (fun (n : forall (X : Set), (X -> X) -> X -> X) => n)
    (fun (v : forall (X : Set), X -> X -> X) => v)
    (fun (x y : forall (X : Set), (X -> X) -> X -> X) => cadd x y)
    (fun (x y : forall (X : Set), (X -> X) -> X -> X) => ceqb x y)
    (fun (u : forall (a b : Set), Set)
         (c : forall (X : Set), X -> X -> X)
         (th el : u (forall (X : Set), (X -> X) -> X -> X)
                    (forall (X : Set), X -> X -> X)) =>
     c (u (forall (X : Set), (X -> X) -> X -> X)
          (forall (X : Set), X -> X -> X))
       th el).

(*  if 1 = 2 then 0 else 1 + 2  :  expr TNat  *)

Definition sample : forall (P : (forall (a b : Set), Set) -> Set),
    ((forall (X : Set), (X -> X) -> X -> X) -> P (fun (a b : Set) => a)) ->
    ((forall (X : Set), X -> X -> X) -> P (fun (a b : Set) => b)) ->
    (P (fun (a b : Set) => a) -> P (fun (a b : Set) => a) -> P (fun (a b : Set) => a)) ->
    (P (fun (a b : Set) => a) -> P (fun (a b : Set) => a) -> P (fun (a b : Set) => b)) ->
    (forall (u : forall (a b : Set), Set),
     P (fun (a b : Set) => b) -> P u -> P u -> P u) ->
    P (fun (a b : Set) => a) :=
  EIf (fun (a b : Set) => a)
    (EEq (ENat cone) (ENat ctwo))
    (ENat czero)
    (EAdd (ENat cone) (ENat ctwo)).

(* The computed type, in isolation: the identity function at [t CNat CBool].
   In CIC this type is [match t with ...]; here it is a static F-omega
   type-level application, and the extraction is dyn-free. *)

Definition id_at (t : forall (a b : Set), Set)
  (x : t (forall (X : Set), (X -> X) -> X -> X) (forall (X : Set), X -> X -> X))
  : t (forall (X : Set), (X -> X) -> X -> X) (forall (X : Set), X -> X -> X) :=
  x.

Extract id_at.


(* Evaluating a TNat expression yields a Church natural; a TBool one a
   Church boolean.  Both by pure beta conversion of the type-level codes. *)

Check eval (fun (a b : Set) => a) sample
  : forall (X : Set), (X -> X) -> X -> X.

Check eval (fun (a b : Set) => b) (EBool ctrue)
  : forall (X : Set), X -> X -> X.

Check eval.

Extract eval.
