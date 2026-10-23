# NullStart — building from the void: the degenerate state (T1) — STANDS WHOLE

**Landed 2026-10-22.** Module `ThetLogos.NullStart` (13 theorems,
0 definitions; zero sorry, zero admit; `#print axioms` on all 13
declarations exactly the standard three). Commissioned by Jeff
2026-10-22 21:43 EDT ("let build from the void"), following his
null-start ruling of the same evening ("gravity is before heat — I am
saying from a null start"; the ontology is T5 motivation, recorded on
the charter, never a theorem). Charter:
`whitepaper/null-start-scoping-2026-10-22.md`. Bench ruling: the Ghys
stage-2 finish (filler) was bumped for this build and resumes after.

## What stands

The void of a finite Gibbs box is the **degenerate state**: all sector
energies — equivalently, for the built modular Hamiltonian
`diagModularK`, all log-weights — equal. No gap, no distinguished
sector: the null start of the box.

- **T1 — Silence. STANDS.** At constant weights the built K is
  literally a scalar matrix, `diagModularK (fun _ => c) =
  ((-log c : ℝ) : ℂ) • 1` (`diagModularK_const`); a scalar commutes
  with everything, so the modular flux vanishes for **every** Dirac
  operator D with no hypothesis on D
  (`flux_zero_of_diagModularK_const`, engine
  `modularFlux_smul_one`). Honest note, on the module's face: this
  reproves FluxClassification's one-sector collapse by the scalar
  route the charter names — same statement, new mechanism (K *is* a
  scalar matrix), plus the general form
  `flux_eq_zero_of_diagModularK_eq_smul_one`.
- **T2 — Uniqueness. STANDS.** The void is the only fully silent
  state: if φ = 0 for every D, all log-weights agree
  (`log_eq_of_silent`), the silent K is scalar
  (`diagModularK_eq_smul_one_of_silent`), headline iff
  `silent_iff_log_const`, and at strictly positive weights silence
  ⟺ weights constant (`silent_iff_weights_const_of_pos`). Route:
  the entry computation `modularFlux_diagonal_apply` with a
  single-entry witness D — the center-of-the-algebra argument in
  one-entry form; the landed classification is used only for the
  backward direction. **Fidelity fence, on the face:** at bare
  `diagModularK` the conclusion is about LOG-weights (log identifies
  w and −w) — FluxClassification's standing fence; weight-level
  constancy is claimed under strict positivity, which covers the
  Gibbs/energy case.
- **T3 — β-blindness. STANDS.** At degenerate energies,
  `sepN q E β = (Σᵢ qᵢ)/(card ι)` at **every** real β
  (`sepN_eq_average_of_forall_eq`; Rung 2 proved β = 0 only), with
  the constant-energy and β-independence forms, and the
  contrapositive companion `not_exists_const_of_sepN_ne_average`:
  separation off the flat average at any one β certifies a gap
  exists. (No converse claimed — one charge assignment at one β can
  sit on the average despite gaps; the docstring says so.) One
  cosmetic linter warning ships with the file (unused `[Nonempty ι]`
  section variable on the T3 headline, kept in Rung 2's setting).

## Fences

- **K-V1.** The "void" is the degenerate Gibbs state of a finite
  box — NOT the QFT vacuum, NOT creation ex nihilo, NOT a
  cosmological initial condition. Jeff's null-start ordering (shape
  before heat) is T5 motivation on the charter, never a theorem.
- **K-V2.** No gravity object. "Shape" means the sector structure
  of a finite state, not spacetime geometry; this brick earns
  nothing toward the gravity dial and claims nothing about it.
- **NO CLAIM** beyond the finite identities proved.

## Verification (parent, on the shipped text)

Candidate md5 `241038022647e8fc694646f4b12313b0` (scratch) → shipped
with the STATUS header flipped to landed. In-tree build
`lake build ThetLogos.NullStart`: exit 0, 3,588 jobs, .olean
present. Own recount on the shipped file (nesting-aware comment
strip): 13 strict, 0 same-line `@[simp]` declarations; sorry 0,
admit 0. The module's own `#print axioms` section prints 21 checks,
every one exactly `[propext, Classical.choice, Quot.sound]` — no
sorryAx, no dependence on the quarantined `kms_identity_diagonal`.

**Census: 3,619 → 3,632 strict (3,659 → 3,672 attribute-inclusive);
131 → 132 counted modules.**
