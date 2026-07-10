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
- **Preservation** for the kind-regular `typing` judgment and a
  well-formed-context invariant `wf_ctx`, for the full `step` relation,
  including `step_nu_abs` and `step_nu_tabs` (`preservation`,
  `preservation_star`, `typing_regular`, `preservation.v`).
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

### Kind-regular term typing (`typing.v`)
The `typing` judgment used by extraction embeds the `wf_typ`/`wf_ground`
premises needed for regularity. Its conversion rule uses context-indexed
`defeq`, which contains ordinary Fω `ty_equiv` and can reveal a `nu`-sealed type
variable through its `has_def` binding. This is what makes the two binder
commutations `step_nu_abs` and `step_nu_tabs` type preserving: after the
context entries are reordered, the shifted annotation remains definitionally
equal to its payload-substituted form.

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
target `typing_conv` to mediate the result type rather than a runtime cast.
`extract_typ_wf_sort` supplies kind regularity,
`extract_typ_tsubst_coc_equiv` supplies substitution/extraction commutation up
to `ty_equiv`, and `deq_ty_equiv` embeds that equivalence into `defeq`. These
facts are proved in `theories/Extraction/{type_extraction_facts,well_typed}.v`.
