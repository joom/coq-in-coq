# BlameFOmega — the target calculus

System Fω + blame: the higher-order polymorphic blame calculus that the
extraction (`theories/Extraction/`) targets. This note summarizes the design
decisions a reader/reviewer should know; the paper's §3 is the fuller account.

## What is proved (all admit-free)

- **Determinism** of the small-step semantics (`step_deterministic`, `semantics.v`).
- **Type-level confluence / Church–Rosser** for `ty_step` and the `ty_equiv`
  head-inversions (`ty_confluence.v`).
- **Progress** for the target typing judgment (`progress`, `progress.v`).
- **Structural metatheory**: term/type weakening, term substitution, neutral
  type substitution, inversion-through-conversion, canonical forms
  (`typing_metatheory.v`).
- **Preservation** for a kind-regular typing judgment `typing_kr` and a
  well-formed-context invariant `wf_ctx`, for `step_ok` — `step` minus the
  two constructors (`step_nu_abs`, `step_nu_tabs`) that are formally proved
  to break preservation for *any* invariant phrased in terms of type-kinding
  (`preservation`, `typing_regular`, `step_nu_abs_breaks_preservation`,
  `preservation.v`; see that file's header for the counterexample and why the
  exclusion is unavoidable, not merely a proof-effort shortfall).
- **Blame safety**: the Blame Theorem (`blame.v`) and the subtyping/blame-safety
  corollary (`subtyping_safety.v`).

`theories/Extraction/Assumptions.v` audits the axiom footprint; every headline
theorem depends only on the standard-library `eq_rect_eq`.

## Design decisions (and their current scope)

### Executable compatibility (`compat`, `infrastructure.v`)
`compat A B` is not a declarative consistency relation but an **executable**
cast-elaboration judgment: every constructor corresponds to a concrete cast
reduction (ID, WRAP, ALL/ALL, GENERALIZE, INSTANTIATE, GROUND, COLLAPSE/CONFLICT).
This is what makes `progress` hold with **no** "stuck cast" rule — the cast case
falls out of `compat_dec`. `compat` is currently **syntactic/unkinded** (`compat A B`,
not `compat Γ A B`); a kind-regular version would add `wf_typ` premises.
Exception: `compat_refl` (identity) steps without inspecting its annotation; every
other constructor decomposes a canonical cast-form head.

### Permissive term typing (`typing.v`)
The `typing` judgment used by extraction is intentionally **permissive**: it does
not embed `wf_typ`/`wf_ground` premises at every constructor (e.g. `typing_tapp`
has no `wf_typ` premise, `typing_blame` types `blame p` at any type, `typing_gnd`
uses the syntactic `ground`). It certifies term *formation*, and **progress** is
proved for it. Preservation is *not* provable for this permissive judgment as
stated (a genuine counterexample, not just a hard proof: an ill-kinded `abs`
domain can leak into a later position where it is load-bearing for typability
— see `preservation.v`'s header). `preservation.v` instead defines a
kind-regular judgment `typing_kr` (mirroring `typing`'s ten rules but adding
the missing `wf_typ`/`wf_ground` premises) and proves preservation for it,
restricted to `step_ok` (`step` minus `step_nu_abs`/`step_nu_tabs`, which are
*also* formally proved to break preservation — for a different, non-kinding
reason: pushing `nu` under a binder can silently invalidate an unrelated,
exactly-pinned type annotation elsewhere in the term).

### Neutral type substitution (`typing_tsubst`, `typing_metatheory.v`)
Type substitution through target terms is sound **only for neutral type names**
(`neutral S` required), not arbitrary type expressions — because neutral ground
tags must stay ground under substitution. This is a design statement, not a
technicality; it is consistently called *neutral type substitution*.

### Neutral ground tags (`syntax.v`)
Ground types are `arrow dyn dyn` plus any **neutral** type
`N ::= α | N A` (a type variable or a type-family application headed by one),
generalizing Blame-for-All's bare type-variable tag to Fω's type applications.
`ν`-tampering fires on *any* occurrence of the sealed variable in a ground tag
(including as an argument to an outer neutral head), and `is_gnd` treats any
neutral tag as tampering.

## Relationship to the extraction

The extraction emits raw `tapp` for large (type) applications and relies on the
target `typing_conv` (Fω definitional equality `ty_equiv`) to mediate the result
type, rather than a runtime cast. The two facts that discharge that step —
`extract_typ_wf_sort` (kind regularity) and `extract_typ_tsubst_coc_equiv`
(substitution/extraction commutation up to `ty_equiv`) — are proved in
`theories/Extraction/{type_extraction_facts,well_typed}.v`.
