# Non-Gibbs Magnetophase — the last hiding place (2026-10-07)

**Verdict: WEAK STAND.** The flux lives here — non-zero, with genuine
A-dependent structure not reducible to the fixed-K ruled surface — but it is
a 2% effect, smooth and saturating. No amplification, no ridges, no
magnetophase transition. The thermomagnetic question gets its final
finite-triple answer below.

## 1. Why this entry exists

The Gibbs magnetophase died by theorem (`magnetophaseFlux_vanishes`, T1):
K_A = βD_A² + cI commutes with D_A, so φ_{β,A} = 0 identically. The precise
question the theorem leaves open: with a generator K_A^act NOT proportional
to D_A², is φ_A^act ≠ 0, and does it carry A-structure beyond the β-linear
ruled surface? This entry is that question, built and measured.

## 2. Construction (T4 numerical; T5 pinned in Lean)

For the fluctuated triple D_A = D + A₁ + J(A₁) (ρ-real structured 1-forms,
‖A₁‖/‖D‖ ∈ [0, 0.05], seeds 2026/202607 — identical machinery to the killed
Gibbs entry):

- ρ_A^act = proj₊(normalize(thermal_state(D_A², β=1) + p·R)), R = XXᴴ/tr(X Xᴴ)
  the lab's seeded pump (seed 2026, first draw — matches
  `modular_flow_lab.py` draw order exactly)
- K_A^act = −logm(ρ_A^act), hermitized (lab convention)
- φ_A^act = i[K_A^act, D_A]

Grid: drive p ∈ {0, 0.1, 0.2, 0.35, 0.5, 0.75} × 10 fluctuation strengths.
β is GLOBAL (= 1); no β(x) (killed: no manifold).

## 3. Gates

| Gate | Result |
|---|---|
| A=0, p=0.35 reproduces lab active flux | ‖φ‖_F = **1.6416e3** ≈ 1.6e3 — PASS |
| p=0 row (Gibbs collapse) | max 0.000e+00 — PASS |
| p=0 entropy cost | −5.4e-8 ≈ 0 — PASS |

## 4. Landscape headline numbers (T4)

- **A-dependence at p=0.35**: 1641.6 → 1675.6, ratio 1.000 → **1.021**
  monotone, saturating. Genuine but weak.
- **Ruled-surface comparison** (fixed K_lab): A-ratio flat at 1.000 to 3
  decimals. The active flux's A-growth is NOT the ruled surface — the
  A-dependence of K_A^act does real work.
- **Flux-direction rotation** vs A=0: 1.0000 → 0.9991 (tiny, monotone).
  The A-structure lives in the norm, not the direction.
- **Drive scaling at A=0**: 0 → 1593 → 1623 → 1642 → 1651 → 1660 —
  saturating (fixed pump direction).
- **Landscape max**: 1.6772e3 at (p=0.75, t=1.2e-2). No interior ridge.
- **Entropy**: S_act > S_gibbs everywhere — the drive ADDS entropy.
  Production ΔS = +0.87 nats at (0.35, A=0), up to +1.22 nats max.
  The flux is bought with entropy production, not entropy cost.

## 5. Lean (builds green, 3239 jobs)

- T5 pinned: `nonGibbsMagnetophaseFlux` (noncomputable def; matrix-log KMS
  machinery pinned per lab convention).
- T1 proved: `nonGibbsMagnetophase_reduces_at_zero` (= rfl — A=0 is the
  ordinary active flux); `activeFlux_nonzero_of_noncomm` (non-commuting
  generator ⟹ non-zero flux — the reason this entry survives where Gibbs
  died).
- Zero sorrys in the new section; axioms [propext, Classical.choice,
  Quot.sound].

## 6. Kill-or-stand

**STAND, qualified.** Non-zero flux ✓ with A-dependent structure not
reducible to the ruled surface ✓. But: 2.1%, smooth, saturating — a
perturbative dressing, not a new phenomenon. No amplification (landscape max
is pure drive scaling), no ridges, no finite crossover signature.

**Final finite-triple answer to the thermomagnetic question:**
- Gibbs magnetophase flux: dead by theorem.
- Non-Gibbs magnetophase flux: alive, but a 2% effect — no "force field"
  bootstrap, no thermomagnetic amplification.
- The surviving entries: magnetophase ENTROPY (1.18% magnetic imprint,
  stable 4-dim kernel — index stability) and the entropy-production price
  of active flux (+0.87 nats at standard drive).
- Open (named, unbuilt): non-Gibbs families beyond the lab pump; β(x)
  remains canyon (manifold factor).

## 7. Tier ledger

| Item | Tier |
|---|---|
| A=0 reduction, non-vanishing transfer | T1 (proved, zero sorrys) |
| Flux landscape, gates, A-growth 2.1% | T4 (seeded, reproducible) |
| Entropy production +0.87 nats | T4 |
| Active-generator KMS machinery | T5 (pinned, lab convention) |
| "Thermomagnetic force field" | KILLED (no amplification found) |
| β(x), photons, cloaking | KILLED (unchanged) |

## Files

- `scripts/non_gibbs_magnetophase_lab.py`
- `scripts/non-gibbs-magnetophase-results.json` / `.md`
- `whitepaper/figs/non-gibbs-magnetophase/` (fig1 flux landscape, fig2
  active-vs-ruled, fig3 entropy cost)
- `lean/ThetLogos/ModularFlux.lean` (non-Gibbs section)
