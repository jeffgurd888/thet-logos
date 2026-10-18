# Pre-compensation — dossier (2026-10-18)

Bench line item 2 (ratified by Jeff 2026-10-18, priced S–M). Module:
`lean/ThetLogos/PreCompensation.lean` — **28 strict T1, 4 defs,
0 `@[simp]`, 0 sorry/admit** (comment-stripped recount). Build
green, **3,245 jobs**. `#print axioms` on nine headlines
(`isDensityMatrix_dephase`, `precompensable_iff`,
`precompensable_iff_pos`, `precompensable_zero_iff_diagonal`,
`not_precompensable_pairPlus`, `isDensityMatrix_pairPlus`,
`unitary_precompensable`, `isDensityMatrix_conj`, `dephase_comp`):
each exactly `[propext, Classical.choice, Quot.sound]` — the
standard three. Nothing existing was modified. Program total:
3,229 + 28 = **3,257 strict**.

## Origin

Jeff's pre-deformed gears (2026-10-18): gear teeth are machined
deliberately wrong — tip relief, crowning, twist compensation — so
the *loaded* gear runs true; the trade is his son Caleb's. The
transplant, audited the same day: given a known channel that will
deform a state, prepare a pre-deformed state the channel lands
exactly on target. The audit's fences going in: pre-compensation
cancels a *systematic* deformation exactly; it cannot cancel
fluctuations; a many-to-one channel forgets, so exact
pre-compensation exists only on part of state space. This brick
proves where that part is, at finite level. The question sat on
the ThermalClock shelf; the channel family is built directly on
the decoherence toy's pinching (`DecoherenceToy.lean`, PT-2) and
the corpus's `IsDensityMatrix` (`FlowKernel.lean`).

## Verdicts per deliverable

**D1 — the partial-dephasing family: STANDS, general finite ι.**
`dephase l A = l • A + (1 − l) • pinch A`: diagonal fixed,
off-diagonals scaled by `l`; `l = 1` is the identity
(`dephase_one`), `l = 0` is the toy's pinching (`dephase_zero`).
For `0 ≤ l ≤ 1` it maps density matrices to density matrices
(`isDensityMatrix_dephase`), as the affine combination of two
density-preserving maps; the quadratic form splits the same way
(`dephase_quad`). Supporting algebra, all at general finite index
type: entry formulas (`dephase_diag`, `dephase_apply_off`),
`pinch_dephase`, the multiplicative composition law
`dephase_comp : dephase a ∘ dephase b = dephase (a·b)` (as bare
linear maps, all real levels), two-sided inversion at `l ≠ 0`
(`dephase_inv_cancel`, `dephase_cancel_inv`), trace and
Hermiticity preservation at every real level.

**D2 — the reachability theorem: STANDS, with the full boundary.**
`PreCompensable l ρ := ∃ σ, IsDensityMatrix σ ∧ dephase l σ = ρ`.

- `precompensable_iff` (headline): for `l ≠ 0`, a density matrix
  `ρ` is exactly pre-compensable **iff** the de-amplified
  candidate `dephase l⁻¹ ρ` (diagonal unchanged, off-diagonals
  scaled by `l⁻¹`) is itself a density matrix. The candidate is
  the unique possible pre-image — the family is invertible as
  linear maps — so reachability is exactly "de-amplification
  stays inside the state space."
- `precompensable_iff_pos`: of the candidate's three density
  conditions, Hermiticity and trace are automatic at every level;
  the question is exactly its positivity clause.
- `l = 1`: every target reachable (`precompensable_one`).
- `l = 0`: reachable **iff** diagonal
  (`precompensable_zero_iff`, `precompensable_zero_iff_diagonal`,
  via the toy's `pinch_eq_self_iff`). The channel forgets all
  coherence in one step; a coherent target has no pre-image at
  all — forgetfulness as a proved obstruction, not a metaphor.
- Diagonal targets are reachable at every level
  (`precompensable_of_diagonal`).
- `0 < l < 1`: **proper subset, proved**
  (`not_precompensable_pairPlus`). The counterexample is the
  maximally coherent pair state `pairPlus i j` (rank one,
  populations `1/2, 1/2`, coherence `1/2`; `isDensityMatrix_pairPlus`
  at general `ι`, any two distinct basis states). Its de-amplified
  candidate, tested against `eᵢ − eⱼ`, has quadratic form exactly
  `1 − l⁻¹ < 0`. The states that cannot be pre-compensated are
  the ones whose coherences are too large for their populations.

**In plain terms:** to undo partial dephasing you must amplify
coherences by `1/l` before the channel shrinks them back — and
amplification is only legal while the amplified state is still a
state. Near-maximal coherence cannot be amplified at all: the
tooth can only be pre-cut so far.

**D3 — the systematic case (the gear case proper): STANDS.**
`unitary_precompensable`: for `U ∈ Matrix.unitaryGroup`, every
density matrix `ρ` has the exact pre-image `σ = star U * ρ * U`,
itself a density matrix, with `U * σ * star U = ρ`. Backing lemma
`isDensityMatrix_conj`: conjugation by any isometry
(`star V * V = 1`) preserves density matrices. This is the case
where pre-deformation cancels the deformation completely — and
the contrast with D2 is the content: conjugation forgets
nothing, dephasing forgets, and the reachable sets differ
accordingly (everything vs a positivity-bounded proper subset).

**D4 — fences / named remainder.** Named in the module header and
here, not proved, not hidden: (i) fluctuating (stochastic) noise
admits no exact pre-image trick — D2's obstruction is the finite
shadow of why; no theorem in this module is about fluctuations.
(ii) `dephase l` for `l ∉ [0, 1]` is the same formula as a linear
map only; it is not claimed to be a channel there (the
de-amplification candidate lives at `l⁻¹ > 1`, which is exactly
why it can leave the state space). (iii) Finite level only; no
continuum, no dynamics beyond the two stated channels. (iv) **The
thermal instance is the named remainder, NOT included**: pre-distort
a state so that Gibbs thermalization (the ThermalClock shelf
question) lands it on target. It did not fall out of this
machinery cheaply — thermalization here would act through the
clock's flow, not through a Schur-type family — so it is named,
not papered over; it sits with the ThermalClock matrix
scalar-shift leftover on the housekeeping shelf.

## Deviations from the commission

None of substance. Two notes: (1) the commission allowed a
qubit-only core as a PARTIAL; not needed — every statement landed
at general finite index types, matching the toy's generality.
(2) The optional thermal section (commission deliverable 4's
"include only if it falls out cheaply") did not fall out cheaply
and is named as the remainder per the commission's own terms.

## Surprises

One engineering find, no mathematical ones: elaborating the
unitary witness inline (`isDensityMatrix_conj ?_ hρ` against the
target `star U * ρ * U`) timed out in `whnf` — unification through
matrix multiplication against `star (star U)`. The landed proof
applies the lemma with `V` and `A` fully explicit and rewrites
`star_star` in the resulting type. Recorded here so the pattern is
not rediscovered the hard way; cf. the `Matrix.mulVec_mulVec`
idiom borrowed from the corpus (FluxTwist/LatticeGauge) for the
adjoint step.
