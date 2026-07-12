# Stock-extraction experiment

Supporting material for the paper's motivation: what Rocq's **stock OCaml
extraction** does to the example programs in `../../examples/`.

Each `ex_<name>.v` is a port of `examples/<name>.v` to idiomatic CIC:

- REPL `Inductive` commands (Boehm–Berarducci encodings) become real Rocq
  `Inductive` declarations;
- inductive kit that the bare PTS had to *axiomatize* becomes genuine
  definitions where CIC can express them — one-step inversions (`fin0`,
  `fin_case`, `hhead`/`htail`) become dependent `match`es, and value-to-type
  decoders (`El : U -> Set`, `El : Ty -> Set`, `tyDen : ty -> Set`) become
  `Fixpoint`s by large elimination;
- `tagless.v`, which Church-encodes CIC's `match`-computed return type one
  level up, is ported as the CIC program its header says it emulates
  (`Fixpoint eval {t} (e : expr t) : tyDen t`);
- `stlc.v`, whose evaluator is axiomatized in the bare PTS, is ported with the
  evaluator implemented.

Running `./run.sh` (needs Rocq ≥ 9.0 and `ocamlopt`) extracts every port and
counts `Obj.magic` / `Obj.t` occurrences outside the unused `__` preamble.
Result with Rocq 9.0:

| unsafe (`Obj.magic` casts and/or `Obj.t` interfaces) | clean |
|---|---|
| `fin`, `hlist`, `printf`, `functor`, `stlc`, `tagless`, `universe` | `newman`, `lists`, `inductive`, `vectors`, `avl`, `equality`, `sigma`, `ordered`, `units`, `session`, `scoped`, `matrix` |

`driver.ml` is the runtime-safety demo: a **well-typed** OCaml client of
`ex_fin.ml` that calls the bounds-checked lookup `nth` on an empty vector.
The length index was erased, so OCaml's types cannot reject the call; `nth`
hits `fin0 = Obj.magic Tt`, the client applies the result as a function, and
the process dies with SIGSEGV — no OCaml exception is raised, so the failure
is not catchable, and nothing attributes it to the boundary that was
violated. This is the failure mode that the paper's typed target replaces
with `blame`.

These files are *not* part of the mechanization; they are an experiment about
Rocq's extractor, checked by `run.sh` only.
