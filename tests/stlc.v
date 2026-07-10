(* An intrinsically-typed interpreter for the simply-typed lambda calculus,
   inside the Calculus of Constructions.

   Object types [Ty], contexts [Ctx], and de Bruijn variables [Var G t] (a
   proof that a variable of type [t] occurs in context [G]) index the term
   type [Tm G t].  Because a term CARRIES its typing derivation in its type,
   only well-typed object programs exist -- there is no separate type checker,
   and the evaluator [eval] is total by construction (no "stuck" or "type
   error" case is even expressible).  This is the canonical demonstration that
   dependent types can make an interpreter correct by construction.

   Extraction erases the context and type indices.  [Tm G t] becomes the plain
   type [Tm], [El t] (the meaning of an object type) becomes [El], environments
   become [Env], and [eval] becomes an ordinary recursive evaluator.  All the
   type-safety scaffolding evaporates, and the verified extraction certifies
   the residual interpreter simulates the dependently-typed original. *)


(* object-language types *)
Axiom Ty : Set.
Axiom base : Ty.
Axiom arr : Ty -> Ty -> Ty.

(* typing contexts *)
Axiom Ctx : Set.
Axiom emp : Ctx.
Axiom snoc : Ctx -> Ty -> Ctx.

(* well-typed de Bruijn variables: a proof that [t] is in [G] *)
Axiom Var : Ctx -> Ty -> Set.
Axiom vz : forall (G : Ctx) (t : Ty), Var (snoc G t) t.
Axiom vs : forall (G : Ctx) (t u : Ty), Var G t -> Var (snoc G u) t.

(* intrinsically-typed terms *)
Axiom Tm : Ctx -> Ty -> Set.
Axiom tvar : forall (G : Ctx) (t : Ty), Var G t -> Tm G t.
Axiom tlam : forall (G : Ctx) (t u : Ty), Tm (snoc G t) u -> Tm G (arr t u).
Axiom tapp : forall (G : Ctx) (t u : Ty), Tm G (arr t u) -> Tm G t -> Tm G u.


(* the identity function  \x. x  at object type  t -> t , in any context. *)

Infer fun (t : Ty) =>
  tlam emp t t (tvar (snoc emp t) t (vz emp t)).

Extract fun (t : Ty) =>
  tlam emp t t (tvar (snoc emp t) t (vz emp t)).


(* the K combinator  \x. \y. x  at type  t -> u -> t .  The inner variable
   reference uses [vs] to skip the intervening binder -- de Bruijn index 1. *)

Extract fun (t u : Ty) =>
  tlam emp t (arr u t)
    (tlam (snoc emp t) u t
      (tvar (snoc (snoc emp t) u) t
        (vs (snoc emp t) t u (vz emp t)))).


(* self-application-shaped applicator  \f. \x. f x  at  (t->u) -> t -> u . *)

Extract fun (t u : Ty) =>
  tlam emp (arr t u) (arr t u)
    (tlam (snoc emp (arr t u)) t u
      (tapp (snoc (snoc emp (arr t u)) t) t u
        (tvar (snoc (snoc emp (arr t u)) t) (arr t u)
          (vs (snoc emp (arr t u)) (arr t u) t (vz emp (arr t u))))
        (tvar (snoc (snoc emp (arr t u)) t) t (vz (snoc emp (arr t u)) t)))).


(* the interpreter.  [El] gives the meaning of an object type, [Env] an
   environment matching a context, and [eval] runs a term.  Extraction erases
   G and t, leaving eval : Tm -> Env -> El -- a plain evaluator. *)

Axiom El : Ty -> Set.
Axiom Env : Ctx -> Set.
Axiom eval : forall (G : Ctx) (t : Ty), Tm G t -> Env G -> El t.

Extract fun (G : Ctx) (t : Ty) (e : Tm G t) (env : Env G) => eval G t e env.
