(** * Optimistic extraction from CoC to System Fω + blame.
    Preserves the non-dependent polymorphic fragment and type-family structure;
    term indices in dependent types are dropped and type indices kept, so a CoC
    family application [vec A n] extracts to the type application [tyapp vec A]. *)

From CoC Require terms.
From CoC Require typing.
From BlameFOmega Require syntax infrastructure semantics typing subtyping safety blame subtyping_safety simulation.

Import terms.
Import CoC.typing.

(** A source type is a classifier when it classifies a type-level object: a
    universe/sort, or a product whose final codomain is a classifier.  Thus
    [Type], [Type -> Type], and [nat -> Type] are classifiers; [A -> A] is not
    a classifier when [A] is an ordinary term-level type.

    WARNING: [classifier] is purely syntactic and is NOT stable under reduction:
    e.g. [(fun x : set => set) y] has [classifier = false] yet reduces to [set]
    with [classifier = true].  This unsoundness under reduction is exactly what
    breaks a simulation theorem about the precise extraction.  The reduction-stable
    replacement is [is_large] below (see [proofs.is_large_stable]); [classifier]
    is a sound-but-incomplete approximation of it (see [proofs.classifier_sound]). *)
Fixpoint classifier (t: terms.term) : bool :=
  match t with
  | sort_term _ => true
  | terms.prod _ U => classifier U
  | _ => false
  end.

(** Reduction-stable classification (foundation for the typed extraction).  A source
    type [T] is "large" -- a kind that classifies types, and hence must extract to a
    type-level binder/quantifier ([tabs]/[all]) -- exactly when it has sort [kind].
    Small types (sort [prop] or [set]) classify terms and extract to term-level
    formers ([abs]/[arrow]).  Unlike [classifier], this is preserved by reduction
    (subject reduction), so every extraction decision based on it is reduction-stable. *)
Definition is_large (e: environment) (T: terms.term) : Type :=
  has_type e T (sort_term kind).

(** Extract the source type of a classifier to a target kind.  Classifier domains
    become kind arrows; term domains are dropped.  Hence
    [Type -> nat -> Type] becomes [KStar -> KStar], exactly what we want for
    [vec]. *)
Fixpoint extract_kind_L (t: terms.term) : syntax.kind :=
  match t with
  | sort_term _ => syntax.KStar
  | terms.prod T U =>
      if classifier T
      then syntax.KArr (extract_kind_L T) (extract_kind_L U)
      else extract_kind_L U
  | _ => syntax.KStar
  end.

(** The blame label carried by every cast the extraction introduces.
    Label id scheme:
    - id 0 is reserved for internal target failures, including extraction
      casts and ν-tampering (see [nu_tamper_label] in syntax.v);
    - id 1 is reserved for is_gnd tampering (see [is_tamper_label]);
    - ids >= 2 are external labels tracked by the blame-freedom theorem. *)
Definition internal_label : syntax.label := syntax.mk_label 0 true.

(** The dynamic function type [? -> ?]. *)
Definition dyn_fun : syntax.typ := syntax.arrow syntax.dyn syntax.dyn.

(** Inert well-typed term placeholder (a ground-wrapped identity), used where a
    source sort (prop/set) or product appears in term position.  Note: a source
    type VARIABLE used as a term extracts to [blame internal_label], not [dyn_token];
    see [extract] in proofs.v. *)
Definition dyn_token : syntax.term :=
  syntax.gnd (syntax.abs syntax.dyn (syntax.var 0)) dyn_fun.

(** Coerce [s : A] to type [B].  When [A = B], the identity.  When [compat A B]
    holds (decidable via [compat_dec]), a real executable cast.  Otherwise the
    target calculus cannot express the coercion, so we emit reserved internal
    blame immediately — an honest representation of target-inexpressible
    coercions (e.g. higher-kinded type-family instantiation).  The simulation
    theorem records this as a disjunction: either the extraction simulates the
    source, or it reduces to internal blame. *)
Definition coerce (s: syntax.term) (A B: syntax.typ) : syntax.term :=
  if syntax.typ_eq_dec A B then s
  else match infrastructure.compat_dec A B with
       | left _ => syntax.cast s A B internal_label
       | right _ => syntax.blame internal_label
       end.

(** ** Typing derivations drive extraction directly

    [typing.has_type]/[typing.well_formed] are [Type]-valued, so [extract] (in
    proofs.v) can recurse on a typing derivation directly: it pattern-matches on
    the derivation and extracts sub-derivations for the recursive calls.  No
    separate [Type]-sorted mirror of the typing rules is required. *)
