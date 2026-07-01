# coq-in-coq

A formalization in the [Rocq Prover](https://rocq-prover.org/) (formerly Coq)
of the metatheory of the Calculus of Constructions, together with a standalone
proof-checker produced by extraction.

**Author:** Bruno Barras, INRIA-Rocquencourt, October 1997

## Building

Requires [Rocq](https://rocq-prover.org/) >= 9.0, OCaml >= 4.14, and
[menhir](http://gallium.inria.fr/~fpottier/menhir/).

```sh
make          # builds theories and the extracted proof-checker
make test     # runs the Newman lemma test
make clean    # removes build artifacts
```

Under the hood this runs `dune build` / `dune build @runtest` / `dune clean`.

To install the package:

```sh
dune install
```

The extracted proof-checker (`coc`) can check a file in batch mode:

```sh
coc < tests/newman.coc
```

Or run interactively:

```sh
coc
```

Type `Help.` at the `Coc <` prompt for available commands.

## Description

The essential step of the formal verification of a proof-checker such as Coq
is the verification of its kernel: a type-checker for the Calculus of Inductive
Constructions (CIC) which is its underlying formalism. The present work is a
first small-scale attempt on a significative fragment of CIC: the Calculus of
Constructions (CC) designed by Huet and Coquand in 1985. It is defined with De
Bruijn indices notation. The whole metatheory of this calculus is proved in the
following order:

1. Confluence of beta-reduction
2. Inversion lemma
3. Thinning lemma
4. Substitution lemma
5. Type Correctness
6. Subject Reduction
7. Strong Normalisation
8. Decidability of Type Inference and Type Checking

From the latter proof, we extract a certified OCaml program which performs type
inference (or type-checking) for an arbitrary typing judgement in CC.
Integrating this program in a larger system, including a parser and
pretty-printer, we obtain a stand-alone proof-checker, called Coc, for the
Calculus of Constructions. As an example, the formal proof of Newman's lemma,
built with Coq, can be re-verified by Coc with reasonable performance.

Upon this kernel, we formalized the interface of a small proof-checker, based
on the type-checking functions above, but it seems the ideas can generalize to
other type systems, as far as they are based on the proofs-as-terms principle.
We suppose that the metatheory of the corresponding type system is proved (up
to type decidability). We specify and certify the toplevel loop, the system
invariant, and the error messages.

## References

- A first description of the proofs can be found as an INRIA technical report
  (in French), number 3026, October 1996.
- The current updated version was described in a paper; see
  [`doc/coqincoq.ps.gz`](doc/coqincoq.ps.gz).
- The proof-checker was formalized in another paper; see
  [`doc/proof-checker.ps.gz`](doc/proof-checker.ps.gz).

## Recent modernization

The original contribution dates from 1997 and targeted Coq v6.1. The following
work was done to bring it up to modern standards:

- Renamed files and definitions to longer, snake case names.
- Modernized proofs and identifiers: used Rocq stdlib types whenever possible,
  added comments, used modern Rocq naming conventions and extraction idioms.
- Replaced the legacy camlp4 stream parser for the extracted CoC checker
  with [ocamllex](https://v2.ocaml.org/api/Ocamllex.html) and
  [menhir](http://gallium.inria.fr/~fpottier/menhir/).
- Switched build to [dune](https://dune.readthedocs.io/) and [opam](https://opam.ocaml.org/).

## License

LGPL 2.1 -- see [LICENSE](LICENSE).
