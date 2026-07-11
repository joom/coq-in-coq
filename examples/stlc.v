(* Signatures for an intrinsically typed simply typed lambda calculus inside
   the Calculus of Constructions.

   Object types [Ty], contexts [Ctx], and de Bruijn variables [Var G t] (a
   proof that a variable of type [t] occurs in context [G]) index the term
   type [Tm G t].  Because a term CARRIES its typing derivation in its type,
   only well-typed object programs can inhabit the signature.  The declarations
   below, including [El], [Env], and [eval], are axioms: this file does not
   implement an evaluator or prove its totality.

   Extraction erases the context and type indices.  [Tm G t] becomes the plain
   type [Tm], [El t] (the meaning of an object type) becomes [El], environments
   become [Env], and [eval] receives an unindexed target signature.  The file
   demonstrates index removal and name recovery, not evaluator execution. *)


(* This file is the one case kept entirely axiomatic.  [Ty], [Ctx], [Var], and
   [Tm] are genuine inductive families, but [Var]/[Tm] are indexed by [Ctx]
   (itself inductive) and are mutually referential; under the indexed
   Boehm-Berarducci encoding the type-formers are unfolded by substitution, and
   the deeply-nested context/type terms this example builds ([snoc (snoc ...)],
   [arr (arr ...)]) make the extractor's normalizer blow up (even a single
   identity term takes many seconds).  So here the encoding is impractical, not
   impossible, and we keep the whole signature axiomatic -- an honest limit of
   lambda-encoding deeply-nested indexed families through a normalizing target. *)

(* object-language types *)
Axiom Ty : Set.
Axiom base : Ty.
Axiom arr : Ty -> Ty -> Ty.

(* typing contexts *)
Axiom Ctx : Set.
Axiom emp : Ctx.
Axiom snoc : Ctx -> Ty -> Ctx.

(* well-typed de Bruijn variables and intrinsically-typed terms *)
Axiom Var : Ctx -> Ty -> Set.
Axiom vz : forall (G : Ctx) (t : Ty), Var (snoc G t) t.
Axiom vs : forall (G : Ctx) (t u : Ty), Var G t -> Var (snoc G u) t.

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


(* Assumed semantic interface.  [El] assigns a host type to an object type,
   [Env] assigns an environment type to a context, and [eval] is an assumed
   interpreter.  These three CANNOT be defined in the bare PTS: [El] computes
   a type from data (large elimination over [Ty]), and [eval]'s result type
   goes through [El] -- this is precisely the value-as-type boundary, so they
   stay abstract deliberately.  Extraction erases G and t from eval's target
   signature. *)

Axiom El : Ty -> Set.
Axiom Env : Ctx -> Set.
Axiom eval : forall (G : Ctx) (t : Ty), Tm G t -> Env G -> El t.

Extract fun (G : Ctx) (t : Ty) (e : Tm G t) (env : Env G) => eval G t e env.
