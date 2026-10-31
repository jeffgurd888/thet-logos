import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# ThetLogos.ShadowEntropyPost — SE-0: the Shadow Entropy registration pin

**Status: REGISTRATION ONLY — definitions and stated `Prop`s; no proof
attempted. NO CLAIM. No Millennium statement, no ladder rung, no dial
(dials stay 0/4).**

Commission: Jeff, 2026-10-31 ("scope it, rope it, scale it and build
in concrete"). Governing memo:
`routeb-general-scratch/scoping-shadow-entropy-2026-10-31.md`
(§0 provenance/relabeling, §2, §3 arena, §4, §5 targets, §7 fences).
This module is a NEW entry (working label: SE — Shadow Entropy),
registered under the house relabeling rule. The dropped file it
succeeds (`dropped-thermo-shadow-2026-10-30.lean`) is not revived,
not imported, and none of its names carry over; its kill stands
unmodified in the audit record.

## What is registered

The §3 arena, and nothing beyond it: velocity space
`VelocitySpace = Fin 3 → ℝ` under Lebesgue (Pi) measure; the
Maxwell–Boltzmann density `mbDensity τ` at variance `τ` per
component (`τ := k_B·T/m` at the seat; no SI numeral is baked in);
the exponential-quadratic weight family `shadowWeight a b c`
(the constant case `c ∈ (0, 1]` of the dropped file's filter, and
the quadratic case `a·x² + b·x` of its asymmetry factor, acting on
the `v 0` component only); the partition value `partitionZ`; and
the rectified density `rectifiedDensity`, normalized by `Z`. The
`0 < Z` obligation is packaged in `rectifiedDensity`'s hypotheses
(the def takes a `0 < partitionZ τ a b c` proof as an argument), per
the memo §4 pin practice; that `0 < Z` (and `Z` finite) holds in
the arena under `1 + 2aτ > 0` is SE-4's theorem-to-be, not a fact
of this module.

## Statement-form choice (named on the face)

The differential-entropy function `diffEntropy` is SE-1's
definition (`ThetLogos/DiffEntropy.lean`, not yet built): the real
definition `−∫ p·log p` against Lebesgue measure, replacing the
dropped file's constant-`0` placeholder. Because that definition
does not yet exist, the §5 target `Prop`s below CANNOT be stated
against it directly in this brick. Per the memo §4-sanctioned pin
practice, they are therefore registered against an explicit
signature parameter: each target `Prop` takes
`diffEntropy : (VelocitySpace → ℝ) → ℝ` as its first argument, and
states memo §5 verbatim in substance for that parameter, under the
standing hypotheses `0 < τ`, `0 < c ≤ 1`, `1 + 2aτ > 0`. When SE-1
lands, the targets are read with its `diffEntropy` substituted for
the parameter; no statement here is silently re-pointed before
then, and nothing in this module asserts that any function
satisfies these `Prop`s.

Also not registered here: the first-quoted candidate weight
identity handed to scoping was FALSE and was killed at scoping
(memo §2 — it omits the `(E_p − E_q)[log p]` cross term; the
`a = 0, b = 1, c = 1, τ = 1` seat case refutes it). Only the
corrected identity registers, and it registers at SE-2, not here.

## Fences (§7, on the face)

- **NO CLAIM.** Every result this line can produce is T1
  machine-checked mathematics about chosen density functions; the
  Maxwell–Boltzmann closed forms are T4 (textbook); any reading of
  the seat as physics is T5 and is not licensed by anything here.
- **Sibling discipline (T-ENT).** The entropy of this line is
  CONTINUOUS differential entropy over a Lebesgue space. T-ENT's
  entropy is the FINITE von Neumann entropy `−∑ wᵢ log wᵢ` over
  finite weight vectors — a sibling entry, NOT the same
  definition. This line neither cites nor gates T-ENT, and T-ENT
  neither cites nor gates this line; neither line's entropy may be
  cited in the other's dossiers. Every module face in this line
  must say which entropy it means; this module means the
  continuous one (via the parameter above).
- **"Shadow" is a working label only.** It is retained from Jeff's
  own dropped-file vocabulary and asserts nothing: there is no
  vacuum and nothing quantum in any definition below. The "shadow
  filter" is the chosen function `v ↦ c ∈ (0, 1]`; "vacuum" and
  "zero-point" name no object here.
- **The killed causal story.** The dropped file's causal story —
  asymmetry plus shadow ⇒ entropy shift — is quoted here ONLY as
  the KILLED claim that target `shadowEntropyH3b` replaces: in the
  arena, the asymmetry `b` and the constant filter `c` contribute
  exactly `0` to the shift; the weight's curvature `a` alone
  shifts it, by `−½·log(1 + 2aτ)` (target `shadowEntropyH2`).
- **Pre-registered kills, named:** K-SE-1 (vacuity guard — if
  `diffEntropy` as built collapses on the arena, or H2 degenerates
  to bookkeeping with no evaluated seat, the line dies at full
  rank); K-SE-2 (seat-value kill — a proved base value or seat
  shift differing from the T4 closed forms of memo §3/§5 kills
  the seat claim at full rank); K-SE-3 (nullity-overreach guard —
  any sentence asserting or implying a shift from `b` or `c`
  alone is killed on sight); K-SE-4 (scope guard — silently
  leaving the §3 arena, e.g. square completion for a non-quadratic
  weight or a "general V" corollary, voids a brick on sight);
  K-SE-S (stall rule — integrability/Fubini/Pi-type overruns are
  stalls and re-prices, never kills by slowness).
- **FRONTIER, named and unpriced:** non-quadratic potentials;
  nonconstant, genuinely `v`-dependent filters; entropy production
  rates and any dynamics; multiparticle/interacting gases.
-/

namespace ThetLogos

/-! ## §1. The arena (§3): velocity space and the base density -/

/-- Velocity space: `Fin 3 → ℝ` (the dropped file's own
`VelocitySpace`, kept so the rebuild is recognizably the same
claim, repaired). Lebesgue (Pi) measure is the ambient measure,
named explicitly in `partitionZ`. -/
abbrev VelocitySpace : Type := Fin 3 → ℝ

/-- The Maxwell–Boltzmann density at variance `τ` per component:
`mbDensity τ v = (2πτ)^(−3/2) · exp(−|v|²/(2τ))`, with
`|v|² = ∑ i, (v i)²` written out over the three components and
the power taken as a real power. A definition only: its
normalization (`∫ v, mbDensity τ v = 1`) is SE-3's target,
assumed nowhere here. -/
noncomputable def mbDensity (τ : ℝ) (v : VelocitySpace) : ℝ :=
  (2 * Real.pi * τ) ^ (-(3 : ℝ) / 2) *
    Real.exp (-(∑ i, (v i) ^ 2) / (2 * τ))

/-! ## §2. The weight family, the partition value, rectification -/

/-- The weight family (the whole arena):
`shadowWeight a b c v = c · exp(−(a·(v 0)² + b·(v 0)))`.
`c` is the constant filter value (admissibility `0 < c ≤ 1` is
carried in the target `Prop`s, not in this def); `a·x² + b·x` is
the quadratic asymmetry factor on the `v 0` component, with
`a` the curvature and `b` the linear (asymmetry) coefficient. -/
noncomputable def shadowWeight (a b c : ℝ) (v : VelocitySpace) : ℝ :=
  c * Real.exp (-(a * (v 0) ^ 2 + b * (v 0)))

/-- The partition value:
`partitionZ τ a b c = ∫ v, mbDensity τ v · shadowWeight a b c v`
against Lebesgue measure (`MeasureTheory.volume` on
`VelocitySpace`). A definition only: finiteness and positivity
of this value in the arena are SE-4's theorems-to-be. -/
noncomputable def partitionZ (τ a b c : ℝ) : ℝ :=
  ∫ v, mbDensity τ v * shadowWeight a b c v ∂MeasureTheory.volume

/-- The rectified density, normalized:
`rectifiedDensity τ a b c hZ v
  = (mbDensity τ v · shadowWeight a b c v) / partitionZ τ a b c`.
The `0 < Z` obligation is packaged in the def's hypotheses: the
argument `_hZ : 0 < partitionZ τ a b c` must be supplied before
the rectified density can be formed (proof-irrelevant — the
value does not depend on which proof is supplied, hence the
underscore name). This is the
repair of the dropped file's unnormalized rectification: entropy
is only ever applied (SE-1 onward) to this normalized form. -/
noncomputable def rectifiedDensity (τ a b c : ℝ)
    (_hZ : 0 < partitionZ τ a b c) (v : VelocitySpace) : ℝ :=
  (mbDensity τ v * shadowWeight a b c v) / partitionZ τ a b c

/-! ## §3. The §5 targets, stated verbatim in substance

Registered against the explicit `diffEntropy` signature parameter
(see the statement-form choice in the module header). Standing
hypotheses throughout (memo §5): `0 < τ`, `0 < c ≤ 1`,
`1 + 2aτ > 0`; `p := mbDensity τ`;
`q := rectifiedDensity τ a b c hZ`. No proof is attempted and no
satisfaction is asserted. -/

/-- **(H1) Base value (memo §5, verbatim in substance).** For the
SE-1 differential entropy (registered here as the parameter
`diffEntropy`) and every `τ` with `0 < τ`:
`diffEntropy (mbDensity τ) = (3/2) · log (2πeτ)`, with
`e = Real.exp 1`. Target of SE-3. -/
def shadowEntropyH1 (diffEntropy : (VelocitySpace → ℝ) → ℝ) : Prop :=
  ∀ τ : ℝ, 0 < τ →
    diffEntropy (mbDensity τ) =
      (3 / 2 : ℝ) * Real.log (2 * Real.pi * Real.exp 1 * τ)

/-- **(H2) Seat identity (memo §5, verbatim in substance) — the
headline.** For every `τ a b c` with `0 < τ`, `0 < c ≤ 1`,
`1 + 2aτ > 0`, and every packaged `0 < Z` witness `hZ`:
`diffEntropy q − diffEntropy p = −(1/2) · log (1 + 2aτ)`,
where `p := mbDensity τ` and `q := rectifiedDensity τ a b c hZ`.
The shift depends on the curvature `a` alone. Target of SE-4. -/
def shadowEntropyH2 (diffEntropy : (VelocitySpace → ℝ) → ℝ) : Prop :=
  ∀ (τ a b c : ℝ), 0 < τ → 0 < c → c ≤ 1 → 0 < 1 + 2 * a * τ →
    ∀ hZ : 0 < partitionZ τ a b c,
      diffEntropy (rectifiedDensity τ a b c hZ) -
          diffEntropy (mbDensity τ) =
        -(1 / 2 : ℝ) * Real.log (1 + 2 * a * τ)

/-- **(H3a) Named nonzero seat (memo §5, verbatim in substance).**
At `a = 1/(2τ)` (i.e. `2aτ = 1`), for every `b` and every
admissible `c` (`0 < c ≤ 1`), and every packaged `0 < Z` witness:
`diffEntropy q − diffEntropy p = −(1/2) · log 2`, and that value
is nonzero. Target of SE-5. -/
def shadowEntropyH3a (diffEntropy : (VelocitySpace → ℝ) → ℝ) : Prop :=
  ∀ (τ b c : ℝ), 0 < τ → 0 < c → c ≤ 1 →
    ∀ hZ : 0 < partitionZ τ (1 / (2 * τ)) b c,
      (diffEntropy (rectifiedDensity τ (1 / (2 * τ)) b c hZ) -
          diffEntropy (mbDensity τ) =
        -(1 / 2 : ℝ) * Real.log 2) ∧
        (-(1 / 2 : ℝ) * Real.log 2 ≠ 0)

/-- **(H3b) Nullity (memo §5, verbatim in substance).** At
`a = 0`, for every `b : ℝ` and every `c ∈ (0, 1]`, and every
packaged `0 < Z` witness: `diffEntropy q = diffEntropy p` —
the shift vanishes regardless of the asymmetry `b` and the
constant filter `c`. This is the theorem that replaces the
dropped file's killed causal story (asymmetry + shadow ⇒ shift):
both advertised causes are entropy-silent in the arena.
Target of SE-5. -/
def shadowEntropyH3b (diffEntropy : (VelocitySpace → ℝ) → ℝ) : Prop :=
  ∀ (τ b c : ℝ), 0 < τ → 0 < c → c ≤ 1 →
    ∀ hZ : 0 < partitionZ τ 0 b c,
      diffEntropy (rectifiedDensity τ 0 b c hZ) =
        diffEntropy (mbDensity τ)

end ThetLogos
