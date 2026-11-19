import ThetLogos.ColdHeatDualityPin
/-!
# COLD-1 — STATEMENT FREEZE (DRAFT): cold pull,
# ground-state concentration at the diagonal Gibbs seat

Queue position 28 (bench queue). Source of record:
`cold-heat-duality-scope-2026-11-09.md` §4 (COLD-1 priced
M, est. 10–18 strict). The four target forms below are
NOT restated here: they are the named Props frozen by
the COLD-0 pin (`ThetLogos.ColdHeatDualityPin`, queue 27,
branch cold0 @ 6f1779f) — `Cold1EntropyIdentityForm`,
`Cold1EntropyFloorForm`, `Cold1OffGroundBoundForm`,
`Cold1LimitForm`. This freeze binds them into the single
package the content brick must discharge, unchanged,
and records the proof-route map per form. The content
brick (theorems, est. 10–18 strict) is written against
this freeze when its build slot comes; nothing here is
proved, and NO theorem is stated in this module —
0 theorems BY DESIGN at the freeze, zero sorrys.

## The package

`Cold1PackageForm` is the conjunction of the pin's four
COLD-1 forms, at the pin's own variable context
(`{N : ℕ} [NeZero N]`, diagonal seat `Fin N → ℝ`).

## Proof-route map (from the scoping §4; routes, not
## proofs — each is a build-time verification item)

Consumes: `GibbsSpan.gibbsWeightsE` /
`GibbsSpan.gibbsSum_pos`, `FiniteEntropy.entropyW` and
its `x · log x` conventions (incl. the `0 · log 0 = 0`
edge), the pin's seat vocabulary (`coldPartition`,
`coldWeight`, `coldMeanEnergy`, `coldGround`).

- Form 1 (entropy identity): `log (coldWeight β E i)
  = -(β · E i) - log (coldPartition β E)` pointwise off
  the weight's zeros; sum against the weight and use
  `entropyW`'s definition. Generalizes the Z4 seat's
  `entropyW_z4Weight_eq`. Watch item: `coldWeight` is
  `gibbsWeightsE` at `logZ = log (coldPartition β E)` —
  the identity must be read through that definition,
  not through a fresh normalization.
- Form 2 (entropy floor, `0 ≤ β` ONLY — the pin's
  disclosed reading, STATUS-COLD0 §3: the range is
  frozen at `0 ≤ β`; the β < 0 mirror belongs to the
  maximal set and is NOT part of this brick): shift
  energies by the ground energy (`E' i = E i - E m₀ ≥
  0`); form 1 at `E'` plus `⟨E'⟩_β ≥ 0` gives
  `S(β) = log Z'(β) + β · ⟨E'⟩ ≥ log Z'(β) ≥
  log (card G)`, the last step because every ground
  index contributes `exp 0 = 1` to `Z'`.
- Form 3 (off-ground bound, `0 ≤ β`): `coldWeight β E
  i = exp (-(β · E i)) / coldPartition β E` and the
  partition sum is bounded below by the single ground
  term `exp (-(β · E m₀))`; divide. No β < 0 form is
  frozen (same disclosed reading as form 2).
- Form 4 (cold limits): form 3 sends each off-ground
  weight to 0 as `β → ∞` (exponential decay against
  the fixed gap `E i - E m₀ > 0`); the weights sum to
  1, so the ground-set total → 1; the entropy limit
  then follows from form 1 with `⟨E⟩_β → E m₀` and
  `log (coldPartition β E) + β · E m₀ → log (card G)`
  (factor `exp (-(β · E m₀))` out of the partition
  sum). Squeeze/`Filter.Tendsto` bookkeeping is the
  expected bulk of this form's cost.

## Fences (on the face, inherited from the pin)

Diagonal seat only — Hermitian/matrix transport is
unpriced and NOT included (scoping §4). These are
statements about Gibbs WEIGHTS as β varies — a
comparison across equilibria — not a force, not a
metric, not gravity, and not a claim that a system
spontaneously pulls itself cold (the FA-4b tension,
carried on the pin's face). K-COLD-GRAVITY /
K-COLD-PROXY citations stand as fired on the pin;
nothing here re-opens them. Pre-registered
DIAL-INELIGIBLE; Dial 2 = 0 on every outcome.

NO CLAIM; dials 0/4.
-/


namespace ThetLogos

section Cold1Freeze

variable {N : ℕ} [NeZero N]

/-- COLD-1 package form — the conjunction of the four
target forms frozen by the COLD-0 pin
(`Cold1EntropyIdentityForm`, `Cold1EntropyFloorForm`,
`Cold1OffGroundBoundForm`, `Cold1LimitForm`), at the
pin's variable context. The content brick (queue 28)
discharges exactly this package, unchanged. -/
def Cold1PackageForm : Prop :=
  Cold1EntropyIdentityForm (N := N) ∧ Cold1EntropyFloorForm (N := N) ∧
    Cold1OffGroundBoundForm (N := N) ∧ Cold1LimitForm (N := N)

end Cold1Freeze

end ThetLogos
