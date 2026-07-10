# Extracting Blame

A fully mechanized verified extraction from the Calculus of
Constructions (CoC) to a higher-order polymorphic blame calculus (System Fω + blame),
with proofs of well-typed extraction, simulation, and blame safety.

This is, to our knowledge, the first definition and the first mechanization of a
higher-order polymorphic blame calculus, and the first
verified extraction from a dependently-typed language to a gradually-typed
target.

### Historical positioning

This project is not the first extraction from CoC to an Fω-like language:
Paulin-Mohring's 1989 POPL paper ("Extracting Fω's Programs from Proofs in
the Calculus of Constructions") established that foundational direction.
This repository instead studies a mechanized optimistic extraction into an
Fω-style blame calculus, preserving the Fω-expressible skeleton and containing
the remaining dependency with `dyn`, casts, and internal blame.

## Background

### System Fω + blame

System Fω + blame is a polymorphic blame calculus: System Fω (the
higher-order polymorphic lambda calculus) extended with a dynamic type `?`,
casts between static and dynamic types, and blame tracking that identifies
which cast boundary is responsible when a runtime type error occurs. The
language combines ideas from:

- **System Fω** (Girard, 1972) — polymorphism with higher-kinded types
- **Gradual typing** (Siek and Taha, 2006) — seamless mixing of static and
  dynamic typing via the dynamic type `?` and type-directed casts
- **Blame tracking** (Wadler and Findler, 2009; Ahmed, Findler, Siek, and
  Wadler, 2011) — labeling casts so that when a cast fails at runtime, the
  responsible boundary is identified

The formalization (`theories/BlameFOmega/`) defines the syntax, a small-step
operational semantics (proved **deterministic**, `step_deterministic`), a kinding
relation, type-level β-reduction with its definitional-equality closure
(`ty_equiv`) and a typing conversion rule (`typing_conv`), a target typing
judgment used by the extraction theorem, the subtyping/blame-safety metatheory,
and the `sim`/`sim_star` simulation relation used to state the extraction
theorems. `dyn` lives at kind `*`, and the rules that instantiate a quantifier
with `dyn` are restricted to `∀α:*` accordingly. Target **progress** is now
mechanized (`progress`, `progress.v`): every closed, well-typed term is a
value, steps, or is `blame`. Target **preservation** is also mechanized
(`preservation`, `preservation.v`), for a separate kind-regular judgment
`typing_kr` and a well-formed-context invariant `wf_ctx`, and for `step_ok`
(`step` minus two constructors, `step_nu_abs`/`step_nu_tabs`, that are
formally proved to break preservation — see "Known limitations").
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
- `Extract <expr>` — extract to System Fω + blame
- `Axiom <name> : <expr>` — add an axiom to the context
- `Delete` — remove the last axiom
- `List` — list current axioms
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
dune exec tests/top.exe < tests/newman.v
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
│   │   ├── blame.v                         Blame Theorem (Thm 14), Corollary 15
│   │   ├── subtyping_safety.v              Subtyping Theorem (Cor 18)
│   │   ├── simulation.v                    sim / typ_sim, sim_star, Jack-of-All-Trades (Thm 7)
│   │   ├── ty_confluence.v                 Type-level β confluence, Church–Rosser, head inversions
│   │   ├── typing_metatheory.v             Weakening, substitution (term/type), inversion, canonical forms
│   │   └── expressions.v                   Named Fω syntax, de Bruijn → named conversion + proofs
│   │
│   └── Extraction/                       Verified extraction from CoC to Fω + blame
│       ├── extraction.v                    Shared defs: classifier, is_large, extract_kind_L, coerce, labels
│       ├── common.v                        Shared infra: iffT, is_large_dec
│       ├── source_facts.v                  Source-side normal-form (nf) and strong-normalization facts
│       ├── translation.v                   The translation: extract_kind/typ/ctx and extract (term) + witness-independence
│       ├── context_facts.v                 Classification stability, context lookup, type-preservation building blocks
│       ├── type_extraction_facts.v         Kind-regularity + substitution-commutation for the large-App typing_conv
│       ├── typing_proof.v                  blame freedom (extracted_safe, extraction_blame_free)
│       ├── well_typed.v                     extract_well_typed + the large-App conversion lemma (extract_typ_tsubst_coc_equiv)
│       ├── simulation_facts.v              Simulation infrastructure + target typing/weakening/subst lemmas it uses
│       ├── substitution_simulation.v       extract weakening/substitution commutation (formerly the six admits)
│       ├── reduction_simulation.v          One-step and multi-step simulation (extract_reduces_once, extract_reduces)
│       ├── derivation_independence.v       extract_deriv_indep
│       ├── optimism.v                      dyn-freedom on the first-order fragment (extract_typ_dyn_free)
│       ├── jack.v                          Jack-of-All-Trades (extraction_simulates_any_instantiation)
│       ├── proofs.v                        Compatibility facade: Require Export of the modules above
│       └── Assumptions.v                   Print Assumptions audit of the headline theorems
│
├── tests/                                OCaml REPL
│   ├── Extract.v                           Rocq extraction commands → core.ml
│   ├── lexer.mll                           Menhir/ocamllex lexer for named CoC syntax
│   ├── parser.mly                          Menhir parser for exprs and REPL commands
│   ├── top.ml                              REPL main loop and Fω+blame pretty-printer
│   ├── newman.v                            Example: Newman's lemma (type-checking)
│   ├── vectors.v                           Example: length-indexed vectors
│   ├── fin.v                               Example: bounds-checked indexing (Fin n)
│   ├── equality.v                          Example: propositional equality + transport
│   ├── sigma.v                             Example: dependent pairs / existentials
│   ├── printf.v                            Example: type-safe printf (dependent arity)
│   ├── matrix.v                            Example: dimension-indexed matrices
│   ├── units.v                             Example: units of measure
│   ├── avl.v                               Example: height-indexed balanced trees
│   ├── session.v                           Example: session-typed protocols
│   ├── stlc.v                              Example: intrinsically-typed interpreter
│   ├── universe.v                          Example: Tarski universe / dynamic type (dyn + blame)
│   └── functor.v                           Example: higher-kinded (functors, tagless-final, monads)
│
└── paper/                                 POPL-style paper (LaTeX, acmart)
    ├── main.tex                            The paper
    ├── references.bib                      Bibliography
    └── Makefile                            `make` → main.pdf
```

The `Axiom` commands in `tests/*.v` are inputs to the object-language REPL;
they extend the object-language context and are not Rocq axioms used by the
mechanized metatheory.

The example files are self-contained CoC programs, each run with
`dune exec tests/top.exe < tests/<file>.v`.  They showcase what the extraction
keeps (polymorphic structure), erases (many term indices from target types),
and dynamizes (target-inexpressible type-level residue → `?` + internal
`blame`).  The current extractor does not implement Coq-style proof erasure;
proof terms are treated as ordinary residual terms.

## Main results

**The entire development is admit-free** — zero `Admitted` lemmas across
`theories/`. Every headline theorem (well-typed extraction, simulation,
derivation independence, blame freedom, Jack-of-All-Trades, dyn-freedom, the
Blame Theorem, determinism, and progress) depends only on the standard-library
axiom `eq_rect_eq` (introduced by dependent case analysis); nothing depends on a
project-local axiom.

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

`theories/Extraction/Assumptions.v` runs `Print Assumptions` on every headline
theorem; compiling it shows the whole set depends only on `eq_rect_eq`
(`extract_typ_wf_sort` is even free of that). The script `./check-assumptions.sh`
rebuilds that file and fails if any unexpected axiom or `Admitted` goal appears —
a CI-friendly check of the admit-free claim. The REPL name-recovery lemmas
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
  CoC, then `extract(t)` simulates `extract(v)` under `sim_star`.

- **`extracted_safe` / `extraction_blame_free`**: Blame safety — the extraction never
  blames an external label (labels with id >= 2).

- **`extract_deriv_indep`**: Derivation independence — two derivations of the
  same judgment produce `sim_star`-related extractions.

- **`extraction_simulates_any_instantiation`**: Jack-of-All-Trades — for any
  type `C`, the `C`-instantiated extraction simulates the `dyn`-instantiated
  one.

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

## Known limitations

1. **Internal blame is reachable.** The extraction maps type-variables-used-as-terms
   to `blame internal_label`. This placeholder is well-typed at any type and
   simulates anything (via `sim_blame`), but it is a runtime error — programs
   that exercise dependent-type features at runtime will blame internally.
   The external-blame-freedom theorem (`extraction_blame_free`) only covers labels
   with id >= 2; `internal_label` (id 0) is excluded by design.

2. **Non-computable extraction.** The `extract` function uses `is_large_dec` (which
   invokes the type inference decision procedure) and `nf` (which computes
   normal forms via strong normalization). Both are well-defined but not
   extractable to efficient code. The extraction exists as a mathematical function,
   not a practical compiler pass.

3. **Simulation /= observational approximation (yet).** The simulation
   (`extract_reduces_once`, `extract_reduces`) is stated in terms of `sim_star`,
   not `approximates`. The bridge `sim s t -> approximates s t` requires a
   CIU-style or logical-relations argument that is not yet formalized. Two of
   its three prerequisites are now proved — typed progress (`progress`) and
   determinism (`step_deterministic`, which subsumes the weaker
   "determinism-up-to-blame" this bridge needs) — leaving context
   compatibility of `sim` as the remaining gap. See the OPEN note in
   `simulation.v`.

4. **Fragment-restricted dyn-freedom.** The optimism result
   (`extract_typ_dyn_free`) — that type extraction avoids `dyn` — holds only for the
   first-order polymorphic fragment (`fo_typ_L`): types built from variables,
   arrows, and type application, with no dependent types or higher kinds beyond
   `Type -> ... -> Type`. Full CoC types may extract to types containing `dyn`.

5. **Term typing is not kind-regular; preservation holds for a separate
   kind-regular judgment, restricted to `step` minus two constructors that
   are formally proved to break it.**
   The target `typing` judgment (`typing.v`) used by `extract_well_typed` does
   not embed `wf_typ` premises, so it certifies term formation rather than
   full kind-regularity. Preservation is *not* provable for this permissive
   judgment as literally stated — this is a genuine counterexample, not
   merely a hard proof: an ill-kinded `abs` domain (reachable because
   `typing_conv` can promote it via an unconditional, kind-unaware type-level
   β-step) can leak into a later position where it is load-bearing for
   typability, then β-reduce to a term with no typing derivation at any type
   (see `preservation.v`'s header for the concrete witness).

   **Design decision (deliberate, now carried out):** `preservation.v` defines
   a separate kind-regular judgment `typing_kr` (mirroring `typing`'s ten
   rules but adding the missing `wf_typ`/`wf_ground` premises — `typing.v`
   itself is untouched) and a well-formed-context invariant `wf_ctx`, proves
   `typing_kr` sound for `typing` (`typing_kr_sound`) and regular
   (`typing_regular`: every `typing_kr`-derivable type is well-kinded), and
   proves preservation for it:
   ```coq
   Theorem preservation : forall g e A e',
     wf_ctx g -> typing_kr g e A -> step_ok e e' -> typing_kr g e' A.
   ```
   `step_ok` is `step` with exactly two constructors removed,
   `step_nu_abs`/`step_nu_tabs`, which push a `nu` binder under an `abs`/
   `tabs`. This exclusion is *not* a proof-effort shortfall: both are
   formally proved to break preservation, even against `typing_kr`/`wf_ctx`
   (`step_nu_abs_breaks_preservation`, `preservation.v`), for a reason
   orthogonal to kinding — reordering a context binding underneath a moved
   binder can silently invalidate an unrelated, exactly-pinned type
   annotation elsewhere in the term (e.g. inside a nested `cast`). No
   invariant phrased in terms of type-kinding can fix this, because every
   type involved in the counterexample is already well-kinded; the failure is
   about term-level annotation identity, not kinding.

   The extraction-side obstacle to kind-regularity is now **resolved**. Emitting
   well-kinded types is subtle because the naive kind index (`extract_typ e T`
   has kind `extract_kind_L U` for `T`'s CoC type `U`) is *false*
   (`extract_kind_L` does not commute with the application rule's substitution —
   substituting a type for a variable can flip a domain's syntactic
   `classifier`). The fix threads the target kind through the CoC kinding
   derivation, restricted to genuinely type-level subterms (`type_expr`), which
   makes the index correct: `extract_typ_wf_sort` (type extraction is well kinded
   at `KStar`) is proved **axiom-free** via the stronger induction
   `extract_typ_L_wf_kind` (`type_extraction_facts.v`). It, together with the
   kind-namespace context-lookup lemma (`extract_ctx_lookup_kind`) and the
   compatibility inversions (`compat_arrow_inv`, `compat_all_l_inv`,
   `compat_all_r_inv`, for the structural cast rules WRAP/GENERALIZE/INSTANTIATE),
   are the building blocks for a target subject-reduction proof. The *conversion*
   companion of kind-regularity, `extract_typ_tsubst_coc_equiv`, is also now
   proved (in `well_typed.v`), so the extraction side of the large-`App`
   `typing_conv` step is fully discharged and admit-free (see "Main results").

   A substantial target metatheory library is now in place (all axiom-free):
   - `ty_confluence.v`: the full type-level substitution-lemma chain for `typ`,
     parallel reduction, **confluence** and **Church–Rosser** for `ty_step`,
     the `ty_equiv` head inversions (`ty_equiv_arrow_inv`, `ty_equiv_all_inv`),
     and head-distinctness lemmas for every pair of type-former heads
     (`tvar`/`tyabs` included, needed by `progress`'s canonical-forms cases).
   - `typing_metatheory.v`: **term weakening** and **type weakening** (with the
     two-namespace context-shift bookkeeping), **term substitution**
     (`typing_subst`) and **neutral type substitution** (`typing_tsubst`,
     which requires the substituted type to be `neutral`; also
     `wf_typ_tsubst`, `compat_tsubst`, `ground_tsubst`),
     `tlift`-preservation of `compat` and `ty_equiv`,
     **inversion through `typing_conv`** (`typing_abs_inv`,
     `typing_tabs_inv`, `typing_gnd_inv`), and **canonical forms**
     (`canonical_arrow`, `canonical_all`).
   - Determinism (`step_deterministic`), the type-level equational theory
     (`ty_equiv`/`typing_conv`), the `dyn:*` instantiation restriction, and
     now **progress** (`progress`, `progress.v`) itself.

   The operational `ground` predicate now contains `arrow dyn dyn` and any
   `neutral` type (`α` or `α B₁ ... Bₙ` — a type variable, or a type-family
   application headed by one), generalizing Blame-for-All's bare
   type-variable ground tag to Fω's type-level applications. The
   `wf_ground` kinding relation in `typing.v` is the kind-aware analogue used
   by a future kind-regular typing judgment; the current `typing_gnd` uses the
   syntactic `ground`/`neutral` predicates, which is what keeps
   `ground_tsubst` and `typing_tsubst` provable without threading kinding
   through every substitution.

   What remains for full target type-safety, in order: (a) rewire `typing` to
   the kind-regular form (embed `wf_typ`/`wf_ground` premises); (b) prove
   preservation for it (the weakening, substitution, inversion, and
   canonical-forms lemmas already proved are the intended prerequisites). The
   extraction side is already complete and admit-free: both the kind-indexed
   invariant (`extract_typ_wf_sort`) and the conversion companion
   (`extract_typ_tsubst_coc_equiv`) that discharge the large-`App` `typing_conv`
   step are proved, so only the target-judgment rewiring and its preservation
   proof (pure target metatheory) remain.

6. **No irrelevance/proof erasure.** The extractor does not perform irrelevance
   erasure. Term indices are erased from target types, but the corresponding
   source term arguments remain as ordinary target term arguments whenever the
   source program uses them computationally. A future proof/irrelevance-erasing
   optimization could be layered on top of the present translation.

## References

- B. Barras. *Auto-validation d'un systeme de preuves avec familles
  inductives.* PhD thesis, Universite Paris 7, 1999.
- A. Ahmed, R. B. Findler, J. G. Siek, P. Wadler. Blame for All.
  *POPL 2011.*
- P. Wadler, R. B. Findler. Well-Typed Programs Can't Be Blamed.
  *ESOP 2009.*
- J. G. Siek, W. Taha. Gradual Typing for Functional Languages.
  *Scheme and Functional Programming Workshop, 2006.*
