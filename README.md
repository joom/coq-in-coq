# Extracting Blame

A fully mechanized verified extraction from the Calculus of
Constructions (CoC) to a higher-order polymorphic blame calculus (System Fω + blame),
with proofs of well-typed extraction, syntactic source-reduction simulation,
and external-label safety.

The target is an explicit dynamic/blame calculus. The repository does not
define a gradual surface language, cast insertion, a precision relation, or a
gradual guarantee.

### Historical positioning

This project is not the first extraction from CoC to an Fω-like language:
Paulin-Mohring's 1989 POPL paper ("Extracting Fω's Programs from Proofs in
the Calculus of Constructions") established that foundational direction.
This repository instead studies a mechanized optimistic extraction into an
Fω-style blame calculus, preserving an Fω-expressible skeleton and marking the
remaining dependency with `dyn`, casts, and internal blame.

## Background

### System Fω + blame

System Fω + blame is a polymorphic blame calculus: System Fω (the
higher-order polymorphic lambda calculus) extended with a dynamic type `?`,
casts between static and dynamic types, and labeled cast failures. The
language combines ideas from:

- **System Fω** (Girard, 1972) — polymorphism with higher-kinded types
- **Gradual typing** (Siek and Taha, 2006) — the use of a dynamic type and
  type-directed casts; this artifact formalizes only the explicit target
- **Blame tracking** (Wadler and Findler, 2009; Ahmed, Findler, Siek, and
  Wadler, 2011) — labeling casts so that when a cast fails at runtime, the
  responsible boundary is identified

The formalization (`theories/BlameFOmega/`) defines the syntax, a small-step
operational semantics (proved **deterministic**, `step_deterministic`), a kinding
relation, type-level β-reduction with its definitional-equality closure
(`ty_equiv`), context-indexed definitional equality (`defeq`), and a typing
conversion rule (`typing_conv`), a target typing
judgment used by the extraction theorem, the subtyping/blame-safety metatheory,
and the `sim`/`sim_star` simulation relation used to state the extraction
theorems. `dyn` lives at kind `*`, and the rules that instantiate a quantifier
with `dyn` are restricted to `∀α:*` accordingly. Target **progress** is now
mechanized (`progress`, `progress.v`): every closed, well-typed term is a
value, steps, or is `blame`. Target **preservation** is also mechanized
(`preservation`, `preservation_star`, `preservation.v`) for the same
kind-regular `typing` judgment, a well-formed-context invariant `wf_ctx`, and
the full `step` relation, including `step_nu_abs` and `step_nu_tabs`.
The target is not strongly normalizing: `nonnormalization.v` gives a closed,
well-typed reduction cycle.
The key types are:

| Layer  | Constructors |
|--------|-------------|
| Kinds  | `*`, `K₁ ⇒ K₂` |
| Types  | `α`, `A → B`, `∀α:K. A`, `Λα:K. A`, `A B`, `?` (the dynamic type, at kind `*`) |
| Terms  | `x`, `λx:A. e`, `e₁ e₂`, `Λα:K. e`, `e [A]`, `⟨A ⇒ B⟩ᵖ e`, `gnd(e, G)`, `is_gnd(e, G)`, `blame(p)`, `ν α:K := A. e` (type sealing) |

### The extraction

The extraction translates CoC terms into System Fω + blame. It classifies each
binder as type-level or term-level: a binder whose type has sort `Kind`
(e.g., `A : Set`) becomes a type abstraction `Λα:K. ...` in the target; a
binder whose type has sort `Prop` or `Set` (e.g., `x : Nat`) becomes a term
abstraction `λx:A. ...`. The dynamic type `?` absorbs type-level residue that has no counterpart in the
polymorphic target. Term-indexed dependencies are erased from target types:
for example, `Vec A n` becomes `Vec A`. Type arguments are preserved as target
type applications. A type-level source object used as a term extracts to the
reserved internal blame placeholder.

The extraction function (`extract`) is defined by structural recursion on a
`Type`-valued typing derivation. Making `has_type` live in `Type` (rather
than `Prop`) is essential: Rocq forbids eliminating `Prop` inductives into
`Type`-returning functions, so the derivation must carry computational
content. This required moving the entire reduction/conversion infrastructure
to `Type` as well.

## Attribution

The CoC formalization in `theories/CoC/` is based on Bruno Barras'
[Coq-in-Coq](https://github.com/rocq-archive/coq-in-coq) (1999).
It includes terms, typing, confluence,
strong normalization, decidable type-checking and conversion, and a REPL
with Rocq extraction to OCaml. The code is licensed under the LGPL (see file
headers).

**Changes for the extraction:**

- `has_type` / `well_formed` moved from `Prop` to `Type` (in `typing.v`),
  enabling the extraction function to pattern-match on typing derivations. This
  required making `reduces_once`, `reduces`, `convertible`,
  `parallel_reduces_once`, and `parallel_reduces` all `Type`-valued (in
  `terms.v`), replacing their Stdlib `clos_*` bases with hand-rolled `Type`
  inductives. Strong normalization bridges the gap with a `Prop` wrapper
  (`reduces_once_prop`).
- `is_prop` changed from `\/` to `sum`; `type_case` return type changed from
  `exists ... \/` to `sigT ... +`; many `exists` changed to `sigT`
  throughout the CoC library (~20 files affected).
- The REPL (`tests/`) was added, with Rocq extraction of the type checker and
  extraction to OCaml, a Menhir parser for named CoC syntax, and pretty-printing
  for both CoC and Fω+blame terms. De Bruijn → named conversion is verified on
  both sides: `expression_of_term_with_hints` (CoC, in `expressions.v`) and
  `fterm_expression_of` (Fω, in `BlameFOmega/expressions.v`). Both reuse the
  user's original binder names via `pick_name` (in `names.v`), which only accepts
  a hint that is fresh for the current context — so the recovered names are
  capture-free by construction. The OCaml side no longer does any renaming; the
  `Infer` path threads hints through `interpret_ast`/`translate_message_string`
  in `machine.v`.

All changes preserve the zero-admit property of the original formalization.

## Building

Requires Rocq 9.0, OCaml, Menhir, and dune.

```
dune build
```

This builds the Rocq theories, extracts the type checker and extraction to
OCaml, and compiles the REPL.

## REPL

The REPL lets you type-check CoC terms and extract them to System Fω + blame.

```
dune exec tests/top.exe
```

Or, after `dune install`:

```
coc
```

Commands (each terminated by `.`):

- `Infer <expr>` — infer the type of an expression
- `Check <expr> : <expr>` — check that a term has a given type
- `Compute <expr>` — reduce an expression to its normal form
- `Extract <expr>` — extract to System Fω + blame
- `Axiom <name> : <expr>` — add an axiom to the context
- `Inductive T (a : A) : arity := | C1 : … | C2 : …` — add an inductive type
  (desugars to its indexed impredicative Boehm–Berarducci encoding: the type,
  constructors, and an index-dependent recursor `T_rec`, all computing)
- `Print Axioms` — show the current axioms
- `Help` — show help
- `Quit` — exit

Example:

```
Coc < Extract fun (A : Set) (x : A) => x.
Extracted: Λα:*. λx:α. x

Coc < Extract fun (A B : Set) (f : A -> B) (x : A) => f x.
Extracted: Λα:*. Λβ:*. λx:α -> β. λy:α. (x y)
```

You can also run a batch file:

```
dune exec tests/top.exe < examples/newman.v
```

## Structure

```
.
├── dune-project                          Dune config (lang dune 3.8, coq 0.8, menhir 2.1)
├── extracting-blame.opam                 OPAM package metadata
│
├── theories/
│   ├── CoC/                              Calculus of Constructions (Barras 1999, Type-valued)
│   │   ├── ml_types.v                      Primitive types: name (strings), decidable equality
│   │   ├── names.v                         Named variables, partial name lists, var_of_nat
│   │   ├── terms.v                         Sorts, terms, de Bruijn ops, reduction — all Type-valued
│   │   ├── list_utils.v                    List insertion predicate and lemmas
│   │   ├── typing.v                        Environments, well_formed, has_type (Type-valued)
│   │   ├── classification.v                Skeletons, classes, type classification for SN
│   │   ├── candidates.v                    Reducibility candidates for strong normalization
│   │   ├── strong_normalization.v          Strong normalization via reducibility candidates
│   │   ├── confluence.v                    Parallel reduction, strong confluence, Church–Rosser
│   │   ├── consistency.v                   Logical consistency: no closed ∀A:Prop. A
│   │   ├── decidable_conversion.v          Decidable conversion using normalization
│   │   ├── equivalence.v                   Normal forms, eta-expanded equivalence
│   │   ├── eta_reduction.v                 Eta-reduction and its confluence
│   │   ├── eta_typing.v                    Subject reduction for eta
│   │   ├── expressions.v                   Named surface syntax (expr), free vars, hint-aware naming
│   │   ├── interpretation_type.v           interpretation_kind, interpretation_env, helpers
│   │   ├── interpretation_term.v           Named → de Bruijn translation
│   │   ├── interpretation_stability.v      Stability of interpretation under env changes
│   │   ├── inference.v                     Decidable type inference
│   │   └── machine.v                       REPL state, interpret_ast, synthesis
│   │
│   ├── BlameFOmega/                      System Fω + blame (Ahmed, Findler, Siek, Wadler 2011)
│   │   ├── syntax.v                        Kinds, types, terms, labels, ground types, values
│   │   ├── infrastructure.v                Lifting, substitution, compatibility, commutation
│   │   ├── semantics.v                     One-step reduction (step), multi-step (star)
│   │   ├── typing.v                        Typing contexts, kinding, typing judgment
│   │   ├── subtyping.v                     Subtype, pos/neg subtype, mutual induction, inversion
│   │   ├── safety.v                        safe_pos_neg / safe_sub predicates and preservation
│   │   ├── blame.v                         Positive/negative label-safety preservation
│   │   ├── subtyping_safety.v              Subtyping-label safety preservation
│   │   ├── simulation.v                    Syntactic sim / typ_sim and sim_star
│   │   ├── ty_confluence.v                 Type-level β confluence, Church–Rosser, head inversions
│   │   ├── typing_metatheory.v             Weakening, substitution (term/type), inversion, canonical forms
│   │   ├── progress.v                      Progress for closed, well-typed target terms
│   │   ├── preservation.v                  One-step and multi-step preservation
│   │   ├── nonnormalization.v              A closed, well-typed target reduction cycle
│   │   └── expressions.v                   Checked named conversion, alpha-equivalence, uniqueness
│   │
│   └── Extraction/                       Verified extraction from CoC to Fω + blame
│       ├── extraction.v                    Shared defs: classifier, is_large, extract_kind_L, coerce, labels
│       ├── common.v                        Shared infra: iffT, is_large_dec
│       ├── source_facts.v                  Source-side normal-form (nf) and strong-normalization facts
│       ├── translation.v                   The translation: extract_kind/typ/ctx and extract (term) + witness-independence
│       ├── context_facts.v                 Classification stability, context lookup, type-preservation building blocks
│       ├── type_extraction_facts.v         Kind-regularity + substitution-commutation for the large-App typing_conv
│       ├── typing_proof.v                  External-label non-generation
│       ├── well_typed.v                     extract_well_typed + the large-App conversion lemma (extract_typ_tsubst_coc_equiv)
│       ├── simulation_facts.v              Simulation infrastructure + target typing/weakening/subst lemmas it uses
│       ├── substitution_simulation.v       extract weakening/substitution commutation (formerly the six admits)
│       ├── reduction_simulation.v          One-step and multi-step simulation (extract_reduces_once, extract_reduces)
│       ├── derivation_independence.v       extract_deriv_indep
│       ├── optimism.v                      Exact syntactic characterization of dyn-free extracted types
│       ├── instantiation.v                 Syntactic instantiation simulation
│       ├── proofs.v                        Compatibility facade: Require Export of the modules above
│       └── assumptions.v                   Print Assumptions audit of the headline theorems
│
├── tests/                                OCaml REPL
│   ├── Extract.v                           Rocq extraction commands → core.ml
│   ├── lexer.mll                           Menhir/ocamllex lexer for named CoC syntax
│   ├── parser.mly                          Menhir parser for exprs and REPL commands
│   ├── top.ml                              REPL main loop and Fω+blame pretty-printer
│   ├── naming.v                            Name-hint regression test
│   ├── bad-semantic.v                      Batch error/exit-status regression
│   └── bad-syntax.v                        Lexer source-position regression
│
├── examples/                             Showcase CoC command batches
│   ├── newman.v                            Newman's lemma over inductive-predicate axioms
│   ├── vectors.v                           Length-indexed vectors (map/fold/replicate)
│   ├── fin.v                               Bounds-checked indexing; vnth implemented
│   ├── equality.v                          Propositional equality + transport
│   ├── sigma.v                             Dependent pairs / existentials
│   ├── printf.v                            Type-safe printf; sprintf implemented
│   ├── matrix.v                            Dimension-indexed matrices, fully implemented
│   ├── units.v                             Units of measure over a qty carrier
│   ├── avl.v                               Height-indexed balanced trees
│   ├── session.v                           Session-typed protocols (echo model)
│   ├── stlc.v                              Intrinsically-typed interpreter signature
│   ├── universe.v                          Tarski universe / dynamic type (dyn + blame)
│   ├── functor.v                           Higher-kinded (functors, tagless-final, monads)
│   ├── tagless.v                           Computed return types via type-level codes; dyn-free
│   ├── lists.v                             Polymorphic list library; fully static baseline
│   ├── scoped.v                            Well-scoped de Bruijn terms; capture-avoiding renaming
│   ├── hlist.v                             Heterogeneous lists indexed by a type-level list
│   ├── ordered.v                           Provably-sorted lists over the Le inductive predicate
│   └── inductive.v                         The Inductive command + Compute (Church encodings)
│
└── paper/                                 POPL-style paper (LaTeX, acmart)
    ├── main.tex                            The paper
    ├── references.bib                      Bibliography
    └── Makefile                            `make` → main.pdf
```

The `Axiom` commands in `examples/*.v` are inputs to the object-language REPL;
they extend the object-language context and are not Rocq axioms used by the
mechanized metatheory.

The showcase files are self-contained CoC command batches, each run with
`dune exec tests/top.exe < examples/<file>.v`.  They showcase what the
extraction keeps (polymorphic structure), erases (many term indices from
target types), and dynamizes (the translation's type-level fallback → `?` +
internal `blame`). Object-language `Axiom` commands introduce only what native
inductive definitions would provide — type formers, constructors, and
elimination/induction principles — plus the deliberate value-as-type
boundaries (`El`, `eval`) that need large elimination, which the bare PTS
lacks. Every other function (`vnth`, matrix multiplication, `sprintf`,
Newman's-lemma proof steps, ...) is an ordinary REPL `Definition`, expanded by
let at its use sites (the bare PTS has no delta rule, so definitions are
opaque at uses; each is built from the axiomatized eliminators). The current
extractor does not implement Coq-style proof erasure; proof terms are treated
as ordinary residual terms.

## Main results

**The entire development is admit-free**: the source scan rejects proof-hole
and axiom-declaration commands across `theories/`. The audited headline theorem
set depends only on the standard-library axiom `eq_rect_eq` (introduced by
dependent case analysis); nothing in that set depends on a project-local axiom.

The two type-extraction lemmas that discharge the large-`App` case's
`typing_conv` premises are both now proved:

- `extract_typ_wf_sort` (kind regularity — type extraction is well kinded at
  `KStar`), **fully axiom-free** ("Closed under the global context"), via a
  stronger induction (`extract_typ_L_wf_kind`) that threads the target kind
  through the CoC kinding derivation restricted to genuinely type-level subterms
  (`type_expr`).
- `extract_typ_tsubst_coc_equiv` (type extraction commutes with the application
  rule's source type substitution *up to* `ty_equiv`, Fω definitional equality),
  in `well_typed.v`. Its proof factors as a raw structural substitution-commutation
  lemma (`extract_typ_L_large_subst_raw`) plus reduction-invariance of
  `extract_typ_L` up to `ty_equiv` (`extract_typ_L_reduces_nf_equiv`, itself a
  single-step lemma chained over `W →* nf W`). A naive syntactic-equality version
  is provably false — the two sides differ by a target β-redex and by `nf`
  annotation drift — which is exactly why the statement is up to `ty_equiv` and
  the extractor defers to the target `typing_conv` rule.

The six former simulation admits (`term_tlift_extract_sim`,
`term_tsubst_extract_sim`, `extract_weaken1`, `extract_subst_sim_gen`,
`extract_tsubst_gen`, and — transitively — `extract_reduces_once`) are likewise
proved (in `substitution_simulation.v`/`reduction_simulation.v`).

`theories/Extraction/assumptions.v` runs `Print Assumptions` on the headline
theorem set; compiling it shows that audited set depends only on `eq_rect_eq`
(`extract_typ_wf_sort` is even free of that). The script `./check-assumptions.sh`
rebuilds that file and rejects unexpected assumptions, proof-hole commands, and
axiom-like declarations. The same audit runs under `dune test`. The REPL name-recovery lemmas
additionally depend on the standard library's primitive-string/integer axioms,
since they manipulate variable `name`s; the core metatheory does not.

- **`extract`** (`proofs.v`): The canonical extraction, defined by recursion on a
  `Type`-valued typing derivation (`typing.has_type`). Classification of
  binders as type-level or term-level uses `is_large` (= has sort `kind`),
  which is reduction-stable by subject reduction. Types are normalized before
  extraction (`extract_typ = extract_typ_L ∘ nf`).

- **`extract_well_typed`**: Well-typed extraction — the extraction of a well-typed
  CoC term is well-typed in the target.

- **`extract_reduces_once`**: One-step simulation — if `t` reduces to `v` in
  CoC's canonical `reduces_once` relation, then `extract(t)` simulates
  `extract(v)` under `sim_star`; `extract_reduces` consumes CoC's canonical
  reflexive-transitive `reduces` relation.

- **`extracted_safe` / `extraction_blame_free`**: external-label non-generation
  under reduction of an extracted term in isolation. External labels satisfy
  `external_label` (currently ids at least `first_external_label_id = 3`). This
  is not a theorem about arbitrary linking contexts or programmer boundaries.

- **`extract_deriv_indep`**: Derivation independence — two derivations of the
  same judgment produce `sim_star`-related extractions.

- **`extraction_instantiation_sim`**: for strongly normalizing source terms
  used as type annotations, concrete and `dyn` instantiations are related by
  the extraction's syntactic `sim`. This is not Ahmed et al.'s contextual
  Jack-of-All-Trades principle.

- **`extract_typ_dyn_free_iff`**: the recursive predicate `fo_typ_L` exactly
  characterizes which source-type normal forms this translation maps to target
  types containing no `dyn`. This is a syntactic characterization, not a
  semantic optimality result.

- **`step_deterministic`** (`semantics.v`): the target operational semantics is
  deterministic — each term steps to at most one result.

- **`progress`** (`progress.v`): target progress — every closed, well-typed
  term is a value, steps, or is `blame p`. The cast case falls directly out of
  `compat_dec`, the decision procedure for the *executable* compatibility
  judgment `compat`: every `compat` constructor corresponds to a concrete
  reduction rule (ID, WRAP, the structural `∀`/`∀` step `step_all_all`,
  GENERALIZE, INSTANTIATE, GROUND, COLLAPSE/CONFLICT), so there is no
  catch-all "stuck cast" rule. `compat_to_dyn` additionally requires
  `compat A G` at the chosen ground tag `G`, so GROUND only ever manufactures a
  cast the rest of `compat` already accepts.

- **`preservation` / `preservation_star`** (`preservation.v`): target typing is
  preserved by the full one-step and multi-step semantics. `typing_regular` and
  `typing_annotations_regular` establish kind regularity of result types and of
  every embedded term annotation, respectively.

- **`typing_does_not_imply_strong_normalization`** (`nonnormalization.v`): the
  dynamic target has a closed, well-typed reduction cycle. Target type safety
  does not imply termination; source CoC strong normalization is the separate
  fact used to define `nf` during extraction.

## Known limitations

1. **Internal blame is reachable.** The extraction maps type-variables-used-as-terms
   to `blame internal_label`. This placeholder is well-typed at any type and
   is related to anything by the syntactic bookkeeping rule `sim_blame`, but it is a runtime error — programs
   that exercise dependent-type features at runtime will blame internally.
   The external-label theorem (`extraction_blame_free`) only covers
   `external_label`s. The reserved ids are 0 for `nu` tampering, 1 for
   `is_gnd` tampering, and 2 for extraction/coercion failure.

2. **Non-computable extraction.** The `extract` function uses `is_large_dec` (which
   invokes the type inference decision procedure) and `nf` (which computes
   normal forms via strong normalization). Both are well-defined but not
   extractable to efficient code. The extraction exists as a mathematical function,
   not a practical compiler pass.

3. **Simulation is not observational approximation.** The simulation
   (`extract_reduces_once`, `extract_reduces`) is stated in terms of `sim_star`,
   which deliberately contains rules that are false as untyped behavioral
   principles. No contextual-approximation relation or containment theorem is
   formalized. A future result needs typed program contexts, observations that
   include blame, and a new typed relation with a CIU/logical-relations proof.

4. **Syntactically characterized dyn-freedom.** The optimism result
   (`extract_typ_dyn_free_iff`) exactly characterizes when this extractor avoids
   `dyn`, using the recursive source predicate `fo_typ_L`. This is a property of
   the current translation's syntax, not a semantic maximality or
   full-abstraction result; accepting more source forms without `dyn` would
   require changing the translation or target.

5. **No irrelevance/proof erasure.** The extractor does not perform irrelevance
   erasure. Term indices are erased from target types, but the corresponding
   source term arguments remain as ordinary target term arguments whenever the
   source program uses them computationally. A future proof/irrelevance-erasing
   optimization could be layered on top of the present translation.

6. **Syntactic compatibility and definitional equality are separate.**
   `compat` is executable and syntax-directed, while typing also admits
   context-indexed `defeq`. Identity casts may carry identical non-normal
   annotations; non-identity clients must normalize annotations before choosing
   `compat`. No coherence theorem modulo `defeq` is claimed.

7. **The OCaml executable crosses an opacity boundary.** Rocq extraction warns
   that it accesses opaque proof bodies used by computational, `Type`-valued
   decision procedures. The kernel-checked mathematical theorems remain as
   stated, but the generated executable is not a separately verified compiler
   with a small transparent algorithmic trusted base.

8. **Rocq 9.0 pins the legacy Dune language.** Dune 3.22's new Rocq language
   invokes `rocq --config`, which Rocq 9.0 does not provide (`rocq c --config`
   is the supported form). The package therefore bounds Dune below 3.24, where
   the legacy language is removed; upgrading both tools is required before
   migrating to `rocq.theory`.

## References

- B. Barras. *Auto-validation d'un systeme de preuves avec familles
  inductives.* PhD thesis, Universite Paris 7, 1999.
- A. Ahmed, R. B. Findler, J. G. Siek, P. Wadler. Blame for All.
  *POPL 2011.*
- P. Wadler, R. B. Findler. Well-Typed Programs Can't Be Blamed.
  *ESOP 2009.*
- J. G. Siek, W. Taha. Gradual Typing for Functional Languages.
  *Scheme and Functional Programming Workshop, 2006.*
