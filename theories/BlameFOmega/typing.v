(** * BlameFOmega.typing: Typing contexts and typing judgment.

    Defines contexts (lists of term-type, kind, and definition bindings),
    namespace-separated lookup, and the typing judgment [Γ ⊢ e : A] for the
    polymorphic blame calculus (Figure 1 of the paper). *)

From Stdlib Require Import List.
Import ListNotations.
From BlameFOmega Require Import syntax.
From BlameFOmega Require Import infrastructure.

(** ** Typing contexts *)

(** Context entries: term type binding or kind (for type variables). *)
Inductive binding: Set :=
  | has_type (t: typ)
  | has_kind (K: kind)
  | has_def (K: kind) (A: typ).

(** A typing context is a list of bindings (de Bruijn: index 0 is the most recent). *)
Definition context := list binding.

(** Lookup in the term-variable namespace.  Type/kind bindings are skipped,
    so term variables and type variables use separate de Bruijn namespaces even
    though we store both in one context list. *)
Fixpoint lookup_term (g: context) (n: nat) : option typ :=
  match g with
  | nil => None
  | has_type A :: g' =>
      match n with
      | 0 => Some A
      | S n' => lookup_term g' n'
      end
  | has_kind _ :: g' => option_map (tlift 1 0) (lookup_term g' n)
  | has_def _ _ :: g' => option_map (tlift 1 0) (lookup_term g' n)
  end.

(** Lookup in the type-variable namespace.  Term bindings are skipped. *)
Fixpoint lookup_kind (g: context) (n: nat) : option kind :=
  match g with
  | nil => None
  | has_type _ :: g' => lookup_kind g' n
  | has_kind K :: g' =>
      match n with
      | 0 => Some K
      | S n' => lookup_kind g' n'
      end
  | has_def K _ :: g' =>
      match n with
      | 0 => Some K
      | S n' => lookup_kind g' n'
      end
  end.

(** Lookup in the type-definition namespace: for a [has_def K A] binding,
    returns the concealed implementation type [A] (lifted through every
    intervening kind/def binding it's looked up through, mirroring
    [lookup_kind]/[lookup_term]'s lifting pattern). *)
Fixpoint lookup_def (g: context) (n: nat) : option (kind * typ) :=
  match g with
  | nil => None
  | has_type _ :: g' => lookup_def g' n
  | has_kind _ :: g' =>
      match n with
      | 0 => None
      | S n' =>
          match lookup_def g' n' with
          | None => None
          | Some (K, A) => Some (K, tlift 1 0 A)
          end
      end
  | has_def K A :: g' =>
      match n with
      | 0 => Some (K, tlift 1 0 A)
      | S n' =>
          match lookup_def g' n' with
          | None => None
          | Some (K', A') => Some (K', tlift 1 0 A')
          end
      end
  end.

(** ** Kinding *)

(** Well-formed types with kind assignment. *)
Inductive wf_typ : context -> typ -> kind -> Prop :=
  | wf_tvar : forall g n K,
    lookup_kind g n = Some K -> wf_typ g (tvar n) K
  | wf_arrow : forall g A B,
    wf_typ g A KStar -> wf_typ g B KStar -> wf_typ g (arrow A B) KStar
  | wf_all : forall g K A,
    wf_typ (has_kind K :: g) A KStar -> wf_typ g (all K A) KStar
  | wf_tyabs : forall g K1 K2 A,
    wf_typ (has_kind K1 :: g) A K2 -> wf_typ g (tyabs K1 A) (KArr K1 K2)
  | wf_tyapp : forall g F A K1 K2,
    wf_typ g F (KArr K1 K2) -> wf_typ g A K1 -> wf_typ g (tyapp F A) K2
  | wf_dyn : forall g, wf_typ g dyn KStar.

Hint Constructors wf_typ: blame.

(** Well-formed ground types for the kind-regular typing judgment.

    The operational [ground] predicate in syntax.v is syntactic: it contains
    [arrow dyn dyn] ([ground_arrow]) and every neutral Fω type name
    ([ground_neutral]: a type variable [α] or a type-family application
    [α B1 ... Bn]).  [wf_ground] is the kind-aware analogue intended for a
    kind-regular [typing_gnd]: a ground tag must additionally have kind
    [KStar] in the current context. *)
Inductive wf_ground : context -> typ -> Prop :=
  | wf_ground_intro : forall g G,
    ground G -> wf_typ g G KStar -> wf_ground g G.

Hint Constructors wf_ground: blame.

(** ** Context-indexed definitional equality *)

(** [defeq g A B K] is the congruence/equivalence closure of [ty_equiv]
    (ordinary F-omega beta-conversion) extended with one extra axiom,
    [deq_def]: a [ν]-sealed abstract type variable (a [has_def K A]
    binding) is definitionally equal, *in that context*, to its concealed
    implementation type [A] (shifted to account for the binder). This is
    what lets [typing_conv] see through a [nu]-seal when needed while still
    treating the sealed variable as fully abstract everywhere else (since
    [ty_equiv]/[wf_typ] never look inside a [has_def] binding's payload). *)
Inductive defeq : context -> typ -> typ -> kind -> Prop :=
  | deq_refl : forall g A K,
    wf_typ g A K -> defeq g A A K
  | deq_sym : forall g A B K,
    defeq g A B K -> defeq g B A K
  | deq_trans : forall g A B C K,
    defeq g A B K -> defeq g B C K -> defeq g A C K
  | deq_ty_equiv : forall g A B K,
    wf_typ g A K -> wf_typ g B K -> ty_equiv A B -> defeq g A B K
  | deq_def : forall g n K A,
    lookup_def g n = Some (K, A) ->
    wf_typ g (tvar n) K ->
    defeq g (tvar n) A K
  | deq_arrow : forall g A A' B B',
    defeq g A A' KStar -> defeq g B B' KStar ->
    defeq g (arrow A B) (arrow A' B') KStar
  | deq_all : forall g K A A',
    defeq (has_kind K :: g) A A' KStar ->
    defeq g (all K A) (all K A') KStar
  | deq_tyabs : forall g K1 K2 A A',
    defeq (has_kind K1 :: g) A A' K2 ->
    defeq g (tyabs K1 A) (tyabs K1 A') (KArr K1 K2)
  | deq_tyapp : forall g F F' A A' K1 K2,
    defeq g F F' (KArr K1 K2) -> defeq g A A' K1 ->
    defeq g (tyapp F A) (tyapp F' A') K2.

Hint Constructors defeq: blame.

(** ** Typing rules *)

(** Target term typing used by extraction.

    This judgment is kind-regular: every constructor that introduces or
    inspects a type annotation carries the [wf_typ]/[wf_ground] premises
    needed to keep every type occurring in a derivation well-kinded, and
    [typing_conv] uses the context-indexed [defeq] (rather than the
    context-free [ty_equiv]) so it can also see through [nu]-sealed abstract
    type variables via [deq_def]. *)
Reserved Notation "[ g |- e : t ]"
  (at level 0, g at level 99, e at level 99, t at level 99).

Inductive typing: context -> term -> typ -> Prop :=
  | typing_var: forall g n t,
    lookup_term g n = Some t ->
    [g |- var n : t]
  | typing_abs: forall g t1 t2 e,
    wf_typ g t1 KStar ->
    [has_type t1 :: g |- e : t2] ->
    [g |- abs t1 e : arrow t1 t2]
  | typing_app: forall g t1 t2 e1 e2,
    [g |- e1 : arrow t1 t2] ->
    [g |- e2 : t1] ->
    [g |- app e1 e2 : t2]
  | typing_tabs: forall g K e t,
    [has_kind K :: g |- e : t] ->
    [g |- tabs K e : all K t]
  | typing_tapp: forall g e t s K,
    [g |- e : all K t] ->
    wf_typ g s K ->
    [g |- tapp e s : tsubst s 0 t]
  | typing_cast: forall g e A B p,
    [g |- e : A] ->
    compat A B ->
    wf_typ g A KStar ->
    wf_typ g B KStar ->
    [g |- cast e A B p : B]
  | typing_gnd: forall g e G,
    [g |- e : G] ->
    wf_ground g G ->
    [g |- gnd e G : dyn]
  | typing_is_gnd: forall g e G,
    [g |- e : dyn] ->
    wf_ground g G ->
    [g |- is_gnd e G : arrow dyn (arrow dyn dyn)]
  | typing_blame: forall g p A,
    wf_typ g A KStar ->
    [g |- blame p : A]
  | typing_nu: forall g K A e B,
    [has_def K A :: g |- e : B] ->
    wf_typ g A K ->
    [g |- nu K A e : tsubst A 0 B]
  (* Type-level definitional equality: a term keeps its type up to [defeq]
     (F-omega conversion, plus transparency of [nu]-sealed abstract type
     variables). The [wf_typ] premise keeps the target type well kinded. *)
  | typing_conv: forall g e A B,
    [g |- e : A] ->
    defeq g A B KStar ->
    wf_typ g B KStar ->
    [g |- e : B]
where "[ g |- e : t ]" := (typing g e t): type_scope.

Hint Constructors typing: blame.

(** Every type annotation occurring in a term is well formed in the context
    at that syntactic position.  This is stronger than result-type regularity:
    in particular it records the annotations inspected by [gnd]/[is_gnd],
    even though those annotations do not occur in the result type. *)
Fixpoint term_annotations_wf (g : context) (e : term) : Prop :=
  match e with
  | var _ => True
  | abs A e1 =>
      wf_typ g A KStar /\ term_annotations_wf (has_type A :: g) e1
  | app e1 e2 => term_annotations_wf g e1 /\ term_annotations_wf g e2
  | tabs K e1 => term_annotations_wf (has_kind K :: g) e1
  | tapp e1 A =>
      term_annotations_wf g e1 /\ exists K, wf_typ g A K
  | cast e1 A B _ =>
      term_annotations_wf g e1 /\ wf_typ g A KStar /\ wf_typ g B KStar
  | gnd e1 G => term_annotations_wf g e1 /\ wf_ground g G
  | is_gnd e1 G => term_annotations_wf g e1 /\ wf_ground g G
  | blame _ => True
  | nu K A e1 =>
      wf_typ g A K /\ term_annotations_wf (has_def K A :: g) e1
  end.
