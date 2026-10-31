import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import ThetLogos.ShadowEntropySeat

/-!
# ThetLogos.ShadowEntropyVerdict - SE-5: the Shadow Entropy verdict

**Status: VERDICT - Card SE outcome class: FULL. NO CLAIM. No
Millennium statement, no ladder rung, no dial (dials stay 0/4).**

Commission: Jeff, 2026-10-31. Governing pack:
`routeb-general-scratch/pack-se-5.md`; governing memo:
`routeb-general-scratch/scoping-shadow-entropy-2026-10-31.md`
(S5 targets, S7 kills K-SE-1..4, K-SE-S - all standing).
Gates consumed: SE-0 (`ThetLogos.ShadowEntropyPost`: the registered
target Props `shadowEntropyH3a` / `shadowEntropyH3b`, quoted
verbatim there and not restated, narrowed, or re-quantified here),
SE-3 (`ThetLogos.ShadowMBSeat`: `shadowEntropyH1_holds`), SE-4
(`ThetLogos.ShadowEntropySeat`: `shadowEntropyH2_holds`, i.e.
`diffEntropy_rectifiedDensity_sub`, and `partitionZ_pos`).

## The verdict (Card SE: FULL)

Both remaining registered targets discharge as specializations of
SE-4's landed H2, in exactly their registered shapes:

- **H3a - the named nonzero seat.** At `a = 1/(2 * tau)` one has
  `1 + 2 * a * tau = 2`, so H2 gives the seat shift
  `-(1/2) * Real.log 2`, and that value is nonzero because
  `Real.log 2 > 0`. Proved as `shadowEntropyH3a_holds`.
- **H3b - nullity.** At `a = 0` one has `1 + 2 * a * tau = 1`, so
  H2 gives shift `-(1/2) * Real.log 1 = 0`, i.e.
  `diffEntropy q = diffEntropy p` for every `b` and every
  admissible `c`. Proved as `shadowEntropyH3b_holds`. Per K-SE-3:
  `b` and `c` contribute exactly `0` to the shift - the nullity is
  the `a = 0` specialization of H2, whose shift depends on the
  curvature `a` alone; no shift comes from `b` or from `c`.

The closing assembly `shadowEntropy_registered_claims_proved`
collects all four registered claims of the SE line:
H1 (SE-3) and H2 (SE-4) and H3a and H3b (this brick). This closes
the SE line's registered claims. Outcome class: **FULL**.

## Fences

- **NO CLAIM.** Everything here is T1 machine-checked mathematics
  about the chosen densities; the Maxwell-Boltzmann closed forms
  are T4 (textbook); any reading of the seat as physics is T5 and
  is not licensed by anything here.
- **Sibling discipline (T-ENT).** The entropy here is the
  CONTINUOUS differential entropy of SE-1. The finite von Neumann
  entropy of the sibling T-ENT line is a different definition;
  nothing in this module cites it.
- **K-SE-3 (nullity-overreach guard).** No sentence in this module
  asserts or implies a shift from `b` or `c` alone; `b` and `c`
  contribute exactly `0`.
- **K-SE-4 (scope guard).** Everything stays inside the memo S3
  arena: exponential-quadratic weights, constant filters. No
  general-V corollary is stated or proved here.
-/

namespace ThetLogos

/-- **H3a discharged - the named nonzero seat.** SE-0 registered
`shadowEntropyH3a` against an explicit signature parameter;
substituting SE-1's `diffEntropy` for that parameter, the
registered target holds: specialize SE-4's H2 at
`a = 1 / (2 * tau)`, where `1 + 2 * a * tau = 2`, giving the seat
shift `-(1/2) * Real.log 2`; the nonzero conjunct is
`Real.log 2 > 0` (from `1 < 2`). The packaged `0 < Z` witness of
the target is passed to H2 unchanged (proof irrelevance makes the
choice of witness immaterial to the rectified density's value). -/
theorem shadowEntropyH3a_holds : shadowEntropyH3a diffEntropy := by
  intro tau b c htau hc hc1 hZ
  have htau0 : tau ≠ 0 := ne_of_gt htau
  have hSval : 1 + 2 * (1 / (2 * tau)) * tau = 2 := by
    field_simp
    ring
  have hS : 0 < 1 + 2 * (1 / (2 * tau)) * tau := by
    rw [hSval]
    norm_num
  have h2 := shadowEntropyH2_holds tau (1 / (2 * tau)) b c htau hc hc1 hS hZ
  rw [hSval] at h2
  have hlog2 : (0 : ℝ) < Real.log 2 :=
    Real.log_pos (by norm_num)
  refine ⟨h2, ?_⟩
  exact mul_ne_zero (by norm_num) (ne_of_gt hlog2)

/-- **H3b discharged - nullity at `a = 0`.** SE-0 registered
`shadowEntropyH3b` against an explicit signature parameter;
substituting SE-1's `diffEntropy` for that parameter, the
registered target holds: specialize SE-4's H2 at `a = 0`, where
`1 + 2 * a * tau = 1` and `Real.log 1 = 0`, so the shift is `0`
and `diffEntropy q = diffEntropy p`. Per K-SE-3: `b` and `c`
contribute exactly `0` to the shift - this is the `a = 0`
specialization of H2, whose shift depends on the curvature `a`
alone. -/
theorem shadowEntropyH3b_holds : shadowEntropyH3b diffEntropy := by
  intro tau b c htau hc hc1 hZ
  have hS : 0 < 1 + 2 * (0 : ℝ) * tau := by
    simp
  have h2 := shadowEntropyH2_holds tau 0 b c htau hc hc1 hS hZ
  have hrhs : -(1 / 2 : ℝ) * Real.log (1 + 2 * (0 : ℝ) * tau) = 0 := by
    simp
  rw [hrhs] at h2
  exact sub_eq_zero.mp h2

/-- **Closing assembly - Card SE, FULL.** All four registered
claims of the Shadow Entropy line, with SE-1's `diffEntropy`
substituted for SE-0's signature parameter: H1 (discharged at
SE-3), H2 (discharged at SE-4), H3a and H3b (discharged above).
This closes the SE line's registered claims. -/
theorem shadowEntropy_registered_claims_proved :
    shadowEntropyH1 diffEntropy ∧ shadowEntropyH2 diffEntropy ∧
      shadowEntropyH3a diffEntropy ∧ shadowEntropyH3b diffEntropy :=
  ⟨shadowEntropyH1_holds, shadowEntropyH2_holds,
    shadowEntropyH3a_holds, shadowEntropyH3b_holds⟩

end ThetLogos
