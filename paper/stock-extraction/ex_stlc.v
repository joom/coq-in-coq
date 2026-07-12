Require Extraction.
Extraction Language OCaml.

Inductive nat : Set := O : nat | S : nat -> nat.
Inductive unitS : Set := ttS : unitS.
Inductive prodS (A B : Set) : Set := pairS : A -> B -> prodS A B.
Arguments pairS {A B}.

Inductive Ty : Set := base : Ty | arr : Ty -> Ty -> Ty.

(* the meaning of an object type: large elimination over Ty
   (the REPL had to axiomatize El). *)
Fixpoint El (t : Ty) : Set :=
  match t with base => nat | arr a b => El a -> El b end.

Inductive Ctx : Set := emp : Ctx | snoc : Ctx -> Ty -> Ctx.

Fixpoint Env (G : Ctx) : Set :=
  match G with emp => unitS | snoc G' t => prodS (Env G') (El t) end.

Inductive Var : Ctx -> Ty -> Set :=
| vz : forall G t, Var (snoc G t) t
| vs : forall G t u, Var G t -> Var (snoc G u) t.

Inductive Tm : Ctx -> Ty -> Set :=
| tvar : forall G t, Var G t -> Tm G t
| tlam : forall G t u, Tm (snoc G t) u -> Tm G (arr t u)
| tapp : forall G t u, Tm G (arr t u) -> Tm G t -> Tm G u.

Fixpoint lookup {G t} (v : Var G t) : Env G -> El t :=
  match v in Var G0 t0 return Env G0 -> El t0 with
  | vz _ _ => fun e => match e with pairS _ x => x end
  | vs _ _ _ v' => fun e => match e with pairS e' _ => lookup v' e' end
  end.

Fixpoint eval {G t} (e : Tm G t) : Env G -> El t :=
  match e in Tm G0 t0 return Env G0 -> El t0 with
  | tvar _ _ v => fun env => lookup v env
  | tlam _ _ _ b => fun env x => eval b (pairS env x)
  | tapp _ _ _ f a => fun env => (eval f env) (eval a env)
  end.

(* \x. x  at t -> t *)
Definition tid (t : Ty) : Tm emp (arr t t) :=
  tlam emp t t (tvar (snoc emp t) t (vz emp t)).

(* \x. \y. x  at t -> u -> t *)
Definition tK (t u : Ty) : Tm emp (arr t (arr u t)) :=
  tlam emp t (arr u t)
    (tlam (snoc emp t) u t
      (tvar (snoc (snoc emp t) u) t (vs (snoc emp t) t u (vz emp t)))).

Definition run_id : El (arr base base) := eval (tid base) ttS.

Extraction "ex_stlc.ml" lookup eval tid tK run_id.
