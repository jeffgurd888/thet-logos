import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Analysis.SpecialFunctions.Sqrt
import ThetLogos.GoldenRatioPin
import Mathlib.Tactic
/-!
# GOLDEN RATIO — FACE 6 (DRAFT): the nested radical

Zero's commission 2026-11-11 23:54 EST (spec
`golden-ratio-pin-2026-11-11.md`, face 6), analytic
brick (a) of parent enrollment #2, 2026-11-11 23:57
EST: one face per module, banked separately, behind
the algebraic pin brick (`ThetLogos.GoldenRatioPin`).

Statement: the iteration `x₀ = 1`,
`xₙ₊₁ = √(1 + xₙ)` — the finite unrollings of
`√(1 + √(1 + √(1 + ⋯)))` — converges to
`Real.goldenRatio`. Route: the sequence is monotone
and bounded above by φ, hence converges to its
supremum; the limit is a fixed point of
`x ↦ √(1 + x)`, i.e. solves `x² = x + 1`, and is
`≥ 1 > 0`, so it is the positive root φ.

## THE FENCE (absolute, on the face — same words as
## the pin brick)

This module concerns the standard mathematics of the
golden-ratio scalar φ ONLY. The φ-TOWER —
golden-ratio scaling as the law of the fermion mass
hierarchy — is KILLED (Zero's own kill condition,
fired 2026-09-29, re-confirmed 2026-10-19; unkill
refused 2026-09-30 and 2026-10-01). Nothing in this
module revives it, and no physical reading of
anything proved here is licensed. The scalar φ is
kept strictly separate from any flux-operator Φ.
These theorems are about a number, not about masses.

Dial-ineligible; NO CLAIM; dials 0/4.
-/


namespace ThetLogos

open Filter Topology

/-- The nested-radical iteration: `x₀ = 1`,
`xₙ₊₁ = √(1 + xₙ)`. -/
noncomputable def nestedRad : ℕ → ℝ
  | 0 => 1
  | (n + 1) => Real.sqrt (1 + nestedRad n)

theorem nestedRad_zero : nestedRad 0 = 1 := rfl

theorem nestedRad_succ (n : ℕ) :
    nestedRad (n + 1) = Real.sqrt (1 + nestedRad n) := rfl

/-- Every term is nonnegative (in fact ≥ 1 from the
first step on; nonnegativity is what the fixed-point
argument consumes). -/
theorem nestedRad_nonneg (n : ℕ) : 0 ≤ nestedRad n := by
  cases n with
  | zero => norm_num [nestedRad_zero]
  | succ k =>
    rw [nestedRad_succ]
    exact Real.sqrt_nonneg _

/-- Monotonicity: `xₙ ≤ xₙ₊₁` for all `n` — the base
step is `1 ≤ √2`; the induction rides on `√` being
monotone. -/
theorem nestedRad_mono : Monotone nestedRad := by
  apply monotone_nat_of_le_succ
  intro n
  induction n with
  | zero =>
    rw [nestedRad_zero, nestedRad_succ, nestedRad_zero]
    have h : (1 : ℝ) ≤ Real.sqrt 2 := by
      rw [Real.le_sqrt (by norm_num)] <;> norm_num
    convert h using 2 <;> norm_num
  | succ k ih =>
    rw [nestedRad_succ, nestedRad_succ]
    exact Real.sqrt_le_sqrt (by linarith [ih])

/-- Boundedness: every term is `≤ φ` — the induction
rides on `√(1 + φ) = √(φ²) = φ`. -/
theorem nestedRad_le_golden (n : ℕ) : nestedRad n ≤ Real.goldenRatio := by
  induction n with
  | zero =>
    rw [nestedRad_zero]
    have h := Real.goldenRatio_pos
    rw [goldenRatio_eq] at *
    have hs : (1 : ℝ) ≤ Real.sqrt 5 := by
      rw [Real.le_sqrt (by norm_num)] <;> norm_num
    linarith
  | succ k ih =>
    rw [nestedRad_succ]
    have hsq : Real.sqrt (1 + Real.goldenRatio) = Real.goldenRatio := by
      have h := goldenRatio_sq_eq
      have hpos := Real.goldenRatio_pos
      have e : 1 + Real.goldenRatio = Real.goldenRatio ^ 2 := by
        linarith [h]
      rw [e]
      exact Real.sqrt_sq (le_of_lt hpos)
    rw [← hsq]
    exact Real.sqrt_le_sqrt (by linarith [ih])

/-- Convergence: a monotone, bounded sequence tends
to its supremum. -/
theorem nestedRad_tendsto :
    Tendsto nestedRad atTop (𝓝 (⨆ n, nestedRad n)) := by
  apply tendsto_atTop_ciSup nestedRad_mono
  refine ⟨Real.goldenRatio, ?_⟩
  rintro _ ⟨n, rfl⟩
  exact nestedRad_le_golden n

/-- Face 6 — the nested radical converges to φ:
`√(1 + √(1 + √(1 + ⋯))) = φ`. The supremum is a
fixed point of `x ↦ √(1 + x)` (continuity of `√`
plus the shifted sequence having the same limit),
is `≥ 1`, and the only nonnegative fixed point is
φ. -/
theorem nestedRad_tendsto_goldenRatio :
    Tendsto nestedRad atTop (𝓝 Real.goldenRatio) := by
  have htend := nestedRad_tendsto
  have hsup_eq : (⨆ n, nestedRad n) = Real.goldenRatio := by
    have hcont : Tendsto (fun n => Real.sqrt (1 + nestedRad n))
        atTop (𝓝 (Real.sqrt (1 + (⨆ n, nestedRad n)))) :=
      (Real.continuous_sqrt.tendsto _).comp (htend.const_add 1)
    have hshift : Tendsto (fun n => nestedRad (n + 1))
        atTop (𝓝 (⨆ n, nestedRad n)) :=
      htend.comp (tendsto_add_atTop_nat 1)
    have hseq : (fun n => Real.sqrt (1 + nestedRad n))
        = (fun n => nestedRad (n + 1)) := by
      funext n
      exact (nestedRad_succ n).symm
    rw [hseq] at hcont
    have hfix : Real.sqrt (1 + (⨆ n, nestedRad n))
        = (⨆ n, nestedRad n) :=
      tendsto_nhds_unique hcont hshift
    have hge : (1 : ℝ) ≤ (⨆ n, nestedRad n) := by
      have h := le_ciSup (f := nestedRad)
        (⟨Real.goldenRatio, by
          rintro _ ⟨n, rfl⟩
          exact nestedRad_le_golden n⟩ : BddAbove (Set.range nestedRad)) 0
      rwa [nestedRad_zero] at h
    have hsq : (⨆ n, nestedRad n) ^ 2 = (⨆ n, nestedRad n) + 1 := by
      have h : (Real.sqrt (1 + (⨆ n, nestedRad n))) ^ 2
          = ((⨆ n, nestedRad n)) ^ 2 := by
        rw [hfix]
      rw [Real.sq_sqrt (by linarith [hge])] at h
      linarith [h]
    have hφ := goldenRatio_sq_eq
    have hroot : ((⨆ n, nestedRad n) - Real.goldenRatio)
        * ((⨆ n, nestedRad n) + Real.goldenRatio - 1) = 0 := by
      linear_combination hsq - hφ
    rcases mul_eq_zero.mp hroot with h1 | h2
    · exact sub_eq_zero.mp h1
    · exfalso
      have hpos := Real.goldenRatio_pos
      linarith [h2, hge, hpos]
  rwa [hsup_eq] at htend

end ThetLogos
