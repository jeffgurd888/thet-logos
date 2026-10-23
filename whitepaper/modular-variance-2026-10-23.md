# ModularVariance — dossier (landed 2026-10-23)

**Module:** `lean/ThetLogos/ModularVariance.lean` (677 lines as
built; 31 strict theorem/lemma declarations, 31 attribute-inclusive,
8 defs, 0 sorry/admit).
**Charter:** `whitepaper/modular-variance-scoping-2026-10-22.md`.
**Commission:** Jeff, 2026-10-22 23:10 EDT — "build this the right
way — no q-toy hacks, no clamping, and no circular Lean axioms."
**Parent verification:** in-tree targeted build exit 0 on the
candidate and again on the shipped text; parent recount (31/31/8/0)
matches the builder's; `#print axioms` on the headlines — exactly
`[propext, Classical.choice, Quot.sound]`.

## Provenance, on the record

This brick is the salvage of two dropped packages audited on
2026-10-22 (verdicts HOLD, audits in the daily log). Both carried a
"modular variance" whose non-negativity was *assumed* — once as a
class field, once as a structure field — and a Python driver whose
q-deformed ρ was not Hermitian at q < 1 (checked by running it).
Jeff took the HOLD verdicts whole and commissioned the statement
rebuilt on corpus-native objects. This module is that rebuild.

## Verdicts (per-target, as pre-registered): STANDS WHOLE (T1)

- **T1 — STANDS.** `varModular_eq : Var_β(K) = β² • Var_β(E)`, by
  affine covariance of the variance applied to the modular
  eigenvalues `β • Eᵢ + log Z`; the scalar `log Z` is discharged by
  the affine theorem, not dropped. The eigenvalues are welded to
  the corpus's matrix `diagModularK` by `modEigen_eq_gibbsK_diag`
  via GibbsSpan's `gibbsK_apply_diag`, unmodified.
- **T2 — STANDS, derived.** Variance is DEFINED in sum-of-squares
  form (`gibbsVar` = the Gibbs expectation of the squared
  deviation) and `gibbsVar_nonneg` is proved from the strict
  positivity of the Gibbs weights (`gibbsProb_pos`, via
  `Real.exp_pos` and the positive partition sum), `sq_nonneg`, and
  `Finset.sum_nonneg`. The second-moment identity `gibbsVar_eq`
  (sum-of-squares = ⟨X²⟩ − ⟨X⟩²) is proved, not stipulated. Nothing
  is postulated: no class field, no structure field, no axiom.
  This is the exact step both dropped stubs assumed away.
- **T3 — STANDS, with one precision recorded below.**
  `varEnergy_eq_zero_iff` (every β): `Var_β(E) = 0 ⟺ ∀ i j,
  E i = E j`; `varEnergy_pos_iff`: positive ⟺ a gap exists. The
  NullStart weld `silent_iff_varModular_eq_zero` (every β, both
  directions): the modular variance vanishes ⟺ the state is silent
  for every probe D — composed from NullStart's
  `silent_iff_weights_const_of_pos` and
  `flux_zero_of_diagModularK_const`, unmodified. The void now has
  a measuring instrument: variance is the distance-from-the-void
  dial, zero exactly at the silent state.
- **T4 — STANDS WHOLE** (the pre-registered stretch; no PARTIAL
  needed). `hasDerivAt_meanEnergy`: `d⟨E⟩/dβ = −Var_β(E)` at every
  β — the finite fluctuation–response identity — by the quotient
  rule on the ratio form with termwise differentiation of the
  finite sums and the second-moment identity.

## The β = 0 precision (on the module's face)

The charter's "Var(K) = 0 ⟺ degenerate" is exact at `β ≠ 0`. At
`β = 0`, T1 itself collapses the modular dial: K is the scalar
`logZ • 1`, and `Var₀(K) = 0` for every energy assignment (proved:
`varModular_zero_beta`). The modular faithfulness theorems
(`varModular_eq_zero_iff`, `varModular_pos_iff`) therefore carry
`β ≠ 0` on their face. The ENERGY dial is faithful at every β, and
the silence weld holds at every β including 0 (at β = 0 the Gibbs
weights are flat — constant — hence silent, and the dial reads 0
on both sides). This is a strengthening of the record, found by
the build: the dial's one blind spot is now a theorem with an
address.

## Fences held

K-MV1 (finite `diagModularK` in GibbsSpan's form only — no
Tomita–Takesaki/von Neumann-algebra content), K-MV2 (no heat-kernel
a-coefficients anywhere; no extracted C_v — `β² • Var_β(E)` is the
only heat-capacity analog, defined here), K-MV3 (genuine state
throughout; no q-deformation, no non-Hermitian operators, no
clamping — a negative variance in this module is impossible by
proof, not by `max(0, ·)`).

## Census

Program: **3,769 strict / 3,818 attribute-inclusive, 134 counted
modules** (was 3,738 / 3,787 / 133).
