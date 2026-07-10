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

Every `Extract` output shown in the paper is produced by the REPL
(`dune exec tests/top.exe`), and every theorem cited in §6 (Metatheory) names a
Rocq result in `theories/`:

| Paper | Rocq |
|-------|------|
| Well-typed extraction | `extract_well_typed` (`Extraction/proofs.v`) |
| Simulation | `extract_reduces_once`, `extract_reduces` |
| Derivation independence | `extract_deriv_indep` |
| External blame freedom | `extraction_blame_free` |
| Jack-of-All-Trades | `extraction_simulates_any_instantiation` |
| Optimism / dyn-freedom | `extract_typ_dyn_free` |
| Blame Theorem | `blame_theorem` (`BlameFOmega/blame.v`) |

The assumption audit is `theories/Extraction/Assumptions.v`. The whole
development is admit-free — well-typed extraction, simulation, derivation
independence, external blame freedom, Jack-of-All-Trades, and the Blame Theorem
all carry complete proofs, and every headline theorem depends only on the
standard-library `eq_rect_eq` axiom. The large-`App` conversion lemma
`extract_typ_tsubst_coc_equiv` (type extraction commutes with the application
rule's type substitution up to Fω definitional equality) is proved in
`Extraction/well_typed.v` — see the paper's Mechanization section and the
top-level `README.md`.

The eleven example files are in `tests/` (`fin.v`, `equality.v`, `sigma.v`,
`printf.v`, `matrix.v`, `units.v`, `avl.v`, `session.v`, `stlc.v`,
`universe.v`, `functor.v`).
