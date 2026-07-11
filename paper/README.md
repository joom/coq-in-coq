# Paper

A POPL-style draft describing the verified extraction from the Calculus of
Constructions to System Fω + blame.

- `main.tex` — the paper (acmart, `acmsmall` / PACMPL format).
- `references.bib` — bibliography.
- `Makefile` — `make` builds `main.pdf` with `latexmk`; `make clean` removes
  build artifacts.

## Building

```
make
```

Requires a TeX distribution with `acmart`, `mathpartir`, `listings`, and
`booktabs` (all standard in TeX Live).

## Relationship to the development

Every `Extract` output comment in the paper is transcribed from a checked-in
REPL golden (with ASCII binder glyphs and redundant parentheses normalized for
the listing), and every theorem cited in §6 names a Rocq result in `theories/`:

| Paper | Rocq |
|-------|------|
| Well-typed extraction | `extract_well_typed` (`Extraction/proofs.v`) |
| Simulation | `extract_reduces_once`, `extract_reduces` |
| Derivation independence | `extract_deriv_indep` |
| External-label non-generation | `extraction_blame_free` |
| Syntactic instantiation | `extraction_instantiation_sim` |
| Exact syntactic dyn-freedom | `extract_typ_dyn_free_iff` |
| Label-safety invariant | `blame_theorem` (`BlameFOmega/blame.v`) |
| Type-level confluence | `ty_star_confluent`, `ty_equiv_church_rosser` |
| Determinism | `step_deterministic` |
| Progress | `progress` |
| Preservation | `preservation`, `preservation_star` |
| Typing regularity | `typing_regular`, `typing_annotations_regular` |
| Target non-normalization | `typing_does_not_imply_strong_normalization` |

The assumption audit is `theories/Extraction/Assumptions.v`. The whole
development is admit-free. The listed headline theorem set carries complete
proofs and depends only on the standard-library `eq_rect_eq` axiom; a separate
source scan rejects proof-hole and axiom-declaration commands. The large-`App` conversion lemma
`extract_typ_tsubst_coc_equiv` (type extraction commutes with the application
rule's type substitution up to Fω definitional equality) is proved in
`Extraction/well_typed.v` — see the paper's Mechanization section and the
top-level `README.md`.

The thirteen showcased files are in `tests/` (`newman.v`, `vectors.v`, `fin.v`,
`equality.v`, `sigma.v`, `printf.v`, `matrix.v`, `units.v`, `avl.v`,
`session.v`, `stlc.v`, `universe.v`, `functor.v`). Most domain primitives are
object-language axioms, so these are typing and symbolic-extraction examples.
`naming.v`, `bad-semantic.v`, and `bad-syntax.v` are executable regressions.
