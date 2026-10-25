/-
# S2-4 (form seat) — the Hamiltonian as a positive quadratic form

Brick S2-4, half (a) ONLY, under the Stage 2 charter
(`whitepaper/stage2-reconstruction-scoping-2026-10-24.md` §4):
`Ĥ` as a positive quadratic form on the S2-2 engine space,
with the contraction semigroup's integer skeleton `T̂^n`
carried alongside, `Ĥ Ω = 0` (as a form: the form vanishes at
the vacuum), `Ĥ ≥ 0` (as a form: every approximant is
nonnegative and the limit form is `ℝ≥0∞`-valued), on every
seat where S2-2/S2-3 landed — conditional at general
`(G, ρ)` under `SliceHPosOne`, unconditional at the U(1)
seat for `β ≥ 0`, and identically zero at `β = 0`.

**Construction (no spectral calculus).** The form of
`-log T̂` is built from the defect `A := 1 - T̂` alone, via
the classical Taylor series, valid on `[0, 1]`,

  `-log λ = ∑' (j ≥ 1), (1 - λ)^j / j`,

whose partial sums are the *approximant forms*

  `q_K(x) = ∑ (j ∈ Icc 1 K), (j:ℝ)⁻¹ * (⟪x, A^[j] x⟫).re`.

Each summand is a nonnegative real: at even `j = 2m` it is
`‖A^[m] x‖² / j`; at odd `j = 2m + 1` it is
`(‖y‖² - ⟪y, T̂ y⟫) / j` with `y = A^[m] x`, nonnegative by
Cauchy–Schwarz and the contraction `‖T̂‖ ≤ 1`. The family
`q_K` is therefore monotone in `K`, and the Hamiltonian
form is its supremum in `ℝ≥0∞`; the form domain is the
finiteness set, proved a submodule and characterized as
the boundedness locus of the approximants. The vacuum lies
in the kernel (`A Ω = 0`), `ker (1 - T̂) ⊆ ker Ĥ-form`, the
discrete energy forms `Q_n(x) = ‖x‖² - ⟪x, T̂^[n] x⟫` are
nonnegative with `Q_n(Ω) = 0`, and `Q_1` is the `j = 1`
approximant, hence sits under the full form.

**Status / fences.** Brick S2-4, form seat — built
2026-10-24 under the Stage 2 charter; parent verification
pending. The OPERATOR seat (charter half (b): `Ĥ` as a
densely defined positive self-adjoint operator with
`exp(-Ĥ) = T̂`) is **OPEN** per Kill K-S2-4 — it is NOT
constructed here, not faked, and not renamed into a
landing: no completion of the pre-Hilbert quotient is
taken and no functional calculus for `T̂` is asserted.
`exp(-tĤ)` for real `t` is operator-brick residue; what
this brick interpolates is the form, from `T̂` alone. No
`osForm` positivity is asserted anywhere; `T̂ ≥ 0` enters
only in the engine's factored form (S2-2b/S2-2c labels
unchanged). This module is NOT a Stage 1b-B discharge.
NO CLAIM. Clay parts closed: 0.
-/

import ThetLogos.LatticeSliceCircle
import ThetLogos.LatticeSliceRegression

namespace ThetLogos

open MeasureTheory Finset
open scoped ENNReal NNReal

section SliceHamiltonian

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ))
  {N : ℕ} [NeZero N]

/-! ## §0. Self-pairing arithmetic on the engine space -/

theorem sliceHam_inner_self_re (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (x : sliceQuotient μG ρ hN2 hρcont hN β hpos) :
    (inner ℂ x x).re = ‖x‖ ^ 2 := by
  rw [inner_self_eq_norm_sq_to_K]
  simp [← Complex.ofReal_pow]

theorem sliceHam_inner_self_im (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (x : sliceQuotient μG ρ hN2 hρcont hN β hpos) :
    (inner ℂ x x).im = 0 := by
  rw [inner_self_eq_norm_sq_to_K]
  simp [← Complex.ofReal_pow]

/-! ## §1. The defect `A = 1 - T̂` and its iterates -/

/-- **The defect operator** `A = 1 - T̂` on the engine
space: the linear map whose powers generate the
Hamiltonian form's approximants. -/
noncomputable def sliceHamDefect (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) :
    sliceQuotient μG ρ hN2 hρcont hN β hpos →ₗ[ℂ]
    sliceQuotient μG ρ hN2 hρcont hN β hpos :=
  LinearMap.id - sliceHat μG ρ hN2 hρcont hN β hpos

theorem sliceHamDefect_apply (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (x : sliceQuotient μG ρ hN2 hρcont hN β hpos) :
    sliceHamDefect μG ρ hN2 hρcont hN β hpos x
      = x - sliceHat μG ρ hN2 hρcont hN β hpos x := by
  simp [sliceHamDefect]

/-- The defect is symmetric, from `T̂`'s symmetry
(S2-2c `sliceHat_isSymmetric`). -/
theorem sliceHamDefect_inner (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (x y : sliceQuotient μG ρ hN2 hρcont hN β hpos) :
    inner ℂ (sliceHamDefect μG ρ hN2 hρcont hN β hpos x) y
      = inner ℂ x (sliceHamDefect μG ρ hN2 hρcont hN β hpos
          y) := by
  rw [sliceHamDefect_apply, sliceHamDefect_apply,
    inner_sub_left, inner_sub_right,
    sliceHat_isSymmetric μG ρ hN2 hρcont hN β hpos x y]

/-- Iterates of the defect move across the inner product. -/
theorem sliceHamDefect_iter_inner (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (j : ℕ)
    (x y : sliceQuotient μG ρ hN2 hρcont hN β hpos) :
    inner ℂ x
        ((⇑(sliceHamDefect μG ρ hN2 hρcont hN β hpos))^[j] y)
      = inner ℂ
          ((⇑(sliceHamDefect μG ρ hN2 hρcont hN β hpos))^[j]
            x) y := by
  induction j generalizing x y with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply, ih,
      ← sliceHamDefect_inner μG ρ hN2 hρcont hN β hpos _ y,
      ← Function.iterate_succ_apply'
        (⇑(sliceHamDefect μG ρ hN2 hρcont hN β hpos)) j x]

/-- Iterates of the defect are additive. -/
theorem sliceHamDefect_iter_add (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (j : ℕ)
    (x y : sliceQuotient μG ρ hN2 hρcont hN β hpos) :
    (⇑(sliceHamDefect μG ρ hN2 hρcont hN β hpos))^[j] (x + y)
      = (⇑(sliceHamDefect μG ρ hN2 hρcont hN β hpos))^[j] x
        + (⇑(sliceHamDefect μG ρ hN2 hρcont hN β hpos))^[j]
          y := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply' _ _ (x + y), ih, map_add,
      Function.iterate_succ_apply' _ _ x,
      Function.iterate_succ_apply' _ _ y]

/-- Iterates of the defect are homogeneous. -/
theorem sliceHamDefect_iter_smul (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (j : ℕ)
    (c : ℂ) (x : sliceQuotient μG ρ hN2 hρcont hN β hpos) :
    (⇑(sliceHamDefect μG ρ hN2 hρcont hN β hpos))^[j] (c • x)
      = c • (⇑(sliceHamDefect μG ρ hN2 hρcont hN β hpos))^[j]
          x := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply' _ _ (c • x), ih, map_smul,
      Function.iterate_succ_apply' _ _ x]

theorem sliceHamDefect_iter_zero (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (j : ℕ) :
    (⇑(sliceHamDefect μG ρ hN2 hρcont hN β hpos))^[j]
        (0 : sliceQuotient μG ρ hN2 hρcont hN β hpos)
      = 0 := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply, map_zero, ih]

/-- The one-step defect pairing is real and nonnegative:
`⟪y, A y⟫ = ‖y‖² - ⟪y, T̂ y⟫`, the `Q₁` core. Reality is
`T̂`'s symmetry; nonnegativity is Cauchy–Schwarz plus the
contraction (S2-2c `sliceHat_norm_le`). Factored-form
labels from S2-2b/2c are untouched: only the *engine's*
`T̂`-pairing is consumed, never an `osForm` statement. -/
theorem sliceHamDefect_self (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (y : sliceQuotient μG ρ hN2 hρcont hN β hpos) :
    (inner ℂ y (sliceHamDefect μG ρ hN2 hρcont hN β hpos
        y)).im = 0
      ∧ 0 ≤ (inner ℂ y
          (sliceHamDefect μG ρ hN2 hρcont hN β hpos y)).re
      ∧ (inner ℂ y (sliceHamDefect μG ρ hN2 hρcont hN β hpos
          y)).re
        = ‖y‖ ^ 2
          - (inner ℂ y (sliceHat μG ρ hN2 hρcont hN β hpos
              y)).re := by
  have hsym : (inner ℂ y
        (sliceHat μG ρ hN2 hρcont hN β hpos y)).im = 0 := by
    have hstar : (starRingEnd ℂ) (inner ℂ y
          (sliceHat μG ρ hN2 hρcont hN β hpos y))
        = inner ℂ y (sliceHat μG ρ hN2 hρcont hN β hpos
          y) := by
      rw [inner_conj_symm]
      exact sliceHat_isSymmetric μG ρ hN2 hρcont hN β hpos y
        y
    exact Complex.conj_eq_iff_im.mp hstar
  refine ⟨?_, ?_, ?_⟩
  · rw [sliceHamDefect_apply, inner_sub_right, Complex.sub_im,
      hsym, sliceHam_inner_self_im μG ρ hN2 hρcont hN β hpos y]
    simp
  · rw [sliceHamDefect_apply, inner_sub_right, Complex.sub_re,
      sliceHam_inner_self_re μG ρ hN2 hρcont hN β hpos y]
    refine sub_nonneg.mpr ?_
    refine le_trans
      (le_trans
        (le_abs_self (inner ℂ y
          (sliceHat μG ρ hN2 hρcont hN β hpos y)).re)
        (Complex.abs_re_le_norm _)) ?_
    refine le_trans (norm_inner_le_norm y _) ?_
    calc ‖y‖ * ‖sliceHat μG ρ hN2 hρcont hN β hpos y‖
        ≤ ‖y‖ * ‖y‖ :=
        mul_le_mul_of_nonneg_left
          (sliceHat_norm_le μG ρ hN2 hρcont hN β hpos y)
          (norm_nonneg y)
      _ = ‖y‖ ^ 2 := by ring
  · rw [sliceHamDefect_apply, inner_sub_right, Complex.sub_re,
      sliceHam_inner_self_re μG ρ hN2 hρcont hN β hpos y]

/-- **Term positivity.** Every Taylor summand's diagonal
pairing is a nonnegative real: even iterates collapse to a
norm square, odd iterates to the one-step defect pairing at
the half-iterate. -/
theorem sliceHamDefect_iter_diag (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (j : ℕ)
    (x : sliceQuotient μG ρ hN2 hρcont hN β hpos) :
    (inner ℂ x
        ((⇑(sliceHamDefect μG ρ hN2 hρcont hN β hpos))^[j]
          x)).im = 0
      ∧ 0 ≤ (inner ℂ x
          ((⇑(sliceHamDefect μG ρ hN2 hρcont hN β hpos))^[j]
            x)).re := by
  rcases Nat.even_or_odd j with ⟨m, hm⟩ | ⟨m, hm⟩
  · -- j = m + m: move m copies across
    have hsplit :
        (⇑(sliceHamDefect μG ρ hN2 hρcont hN β hpos))^[j] x
          = (⇑(sliceHamDefect μG ρ hN2 hρcont hN β
              hpos))^[m]
            ((⇑(sliceHamDefect μG ρ hN2 hρcont hN β
              hpos))^[m] x) := by
      rw [hm, Function.iterate_add_apply]
    rw [hsplit,
      sliceHamDefect_iter_inner μG ρ hN2 hρcont hN β hpos m x
        ((⇑(sliceHamDefect μG ρ hN2 hρcont hN β hpos))^[m] x)]
    exact ⟨sliceHam_inner_self_im μG ρ hN2 hρcont hN β hpos _,
      by rw [sliceHam_inner_self_re μG ρ hN2 hρcont hN β hpos
        _]; exact sq_nonneg _⟩
  · -- j = m + (m + 1): half-iterate, then one defect step
    have hsplit :
        (⇑(sliceHamDefect μG ρ hN2 hρcont hN β hpos))^[j] x
          = (⇑(sliceHamDefect μG ρ hN2 hρcont hN β
              hpos))^[m]
            (sliceHamDefect μG ρ hN2 hρcont hN β hpos
              ((⇑(sliceHamDefect μG ρ hN2 hρcont hN β
                hpos))^[m] x)) := by
      have hjm : j = m + (m + 1) := by omega
      rw [hjm, Function.iterate_add_apply,
        Function.iterate_succ_apply']
    rw [hsplit,
      sliceHamDefect_iter_inner μG ρ hN2 hρcont hN β hpos m x
        (sliceHamDefect μG ρ hN2 hρcont hN β hpos
          ((⇑(sliceHamDefect μG ρ hN2 hρcont hN β
            hpos))^[m] x))]
    exact ⟨(sliceHamDefect_self μG ρ hN2 hρcont hN β hpos
        _).1,
      (sliceHamDefect_self μG ρ hN2 hρcont hN β hpos _).2.1⟩

/-! ## §2. The sesquilinear approximants and the quadratic
forms `q_K` -/

/-- The sesquilinear companion of the `K`-th approximant:
the partial Taylor sum of `-log` applied to the defect,
paired. -/
noncomputable def sliceHamSesqui (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (K : ℕ)
    (x y : sliceQuotient μG ρ hN2 hρcont hN β hpos) : ℂ :=
  ∑ j ∈ Finset.Icc 1 K, (j : ℂ)⁻¹
    * inner ℂ x
      ((⇑(sliceHamDefect μG ρ hN2 hρcont hN β hpos))^[j] y)

/-- The `K`-th approximant quadratic form `q_K(x) ≥ 0`:
partial sums of `-log λ = ∑ (1 - λ)^j / j` read on the
defect `A = 1 - T̂`. -/
noncomputable def sliceHamFormApprox (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (K : ℕ)
    (x : sliceQuotient μG ρ hN2 hρcont hN β hpos) : ℝ :=
  ∑ j ∈ Finset.Icc 1 K, (j : ℝ)⁻¹
    * (inner ℂ x
      ((⇑(sliceHamDefect μG ρ hN2 hρcont hN β hpos))^[j]
        x)).re

theorem sliceHamSesqui_self_re (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (K : ℕ)
    (x : sliceQuotient μG ρ hN2 hρcont hN β hpos) :
    (sliceHamSesqui μG ρ hN2 hρcont hN β hpos K x x).re
      = sliceHamFormApprox μG ρ hN2 hρcont hN β hpos K x := by
  unfold sliceHamSesqui sliceHamFormApprox
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hj : (j : ℂ)⁻¹ = ((j : ℝ)⁻¹ : ℂ) := by simp
  rw [hj]
  simp [Complex.mul_re]

theorem sliceHamFormApprox_nonneg (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (K : ℕ)
    (x : sliceQuotient μG ρ hN2 hρcont hN β hpos) :
    0 ≤ sliceHamFormApprox μG ρ hN2 hρcont hN β hpos K x := by
  unfold sliceHamFormApprox
  refine Finset.sum_nonneg fun j _ => ?_
  refine mul_nonneg (by positivity)
    (sliceHamDefect_iter_diag μG ρ hN2 hρcont hN β hpos j
      x).2

theorem sliceHamFormApprox_mono (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (x : sliceQuotient μG ρ hN2 hρcont hN β hpos) :
    Monotone (sliceHamFormApprox μG ρ hN2 hρcont hN β hpos
      · x) := by
  intro K K' hKK'
  unfold sliceHamFormApprox
  refine Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.Icc_subset_Icc le_rfl hKK') fun j _ _ => ?_
  refine mul_nonneg (by positivity)
    (sliceHamDefect_iter_diag μG ρ hN2 hρcont hN β hpos j
      x).2

/-! ## §3. The approximants are quadratic forms -/

theorem sliceHamDefect_iter_sub (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (j : ℕ)
    (x y : sliceQuotient μG ρ hN2 hρcont hN β hpos) :
    (⇑(sliceHamDefect μG ρ hN2 hρcont hN β hpos))^[j] (x - y)
      = (⇑(sliceHamDefect μG ρ hN2 hρcont hN β hpos))^[j] x
        - (⇑(sliceHamDefect μG ρ hN2 hρcont hN β hpos))^[j]
          y := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply' _ _ (x - y), ih, map_sub,
      Function.iterate_succ_apply' _ _ x,
      Function.iterate_succ_apply' _ _ y]

/-- Per-term parallelogram identity (pure sesquilinearity
of the defect iterates). -/
theorem sliceHamDefect_iter_parallelogram (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (j : ℕ)
    (x y : sliceQuotient μG ρ hN2 hρcont hN β hpos) :
    inner ℂ (x + y)
        ((⇑(sliceHamDefect μG ρ hN2 hρcont hN β hpos))^[j]
          (x + y))
      + inner ℂ (x - y)
        ((⇑(sliceHamDefect μG ρ hN2 hρcont hN β hpos))^[j]
          (x - y))
    = 2 * inner ℂ x
        ((⇑(sliceHamDefect μG ρ hN2 hρcont hN β hpos))^[j] x)
      + 2 * inner ℂ y
        ((⇑(sliceHamDefect μG ρ hN2 hρcont hN β hpos))^[j]
          y) := by
  simp only [sliceHamDefect_iter_add, sliceHamDefect_iter_sub,
    inner_add_left, inner_add_right, inner_sub_left,
    inner_sub_right]
  ring

theorem sliceHamFormApprox_parallelogram (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (K : ℕ)
    (x y : sliceQuotient μG ρ hN2 hρcont hN β hpos) :
    sliceHamFormApprox μG ρ hN2 hρcont hN β hpos K (x + y)
        + sliceHamFormApprox μG ρ hN2 hρcont hN β hpos K
          (x - y)
      = 2 * sliceHamFormApprox μG ρ hN2 hρcont hN β hpos K x
        + 2 * sliceHamFormApprox μG ρ hN2 hρcont hN β hpos K
          y := by
  have hterm : ∀ j ∈ Finset.Icc 1 K,
      (j : ℝ)⁻¹ * (inner ℂ (x + y)
          ((⇑(sliceHamDefect μG ρ hN2 hρcont hN β hpos))^[j]
            (x + y))).re
        + (j : ℝ)⁻¹ * (inner ℂ (x - y)
          ((⇑(sliceHamDefect μG ρ hN2 hρcont hN β hpos))^[j]
            (x - y))).re
      = 2 * ((j : ℝ)⁻¹ * (inner ℂ x
          ((⇑(sliceHamDefect μG ρ hN2 hρcont hN β hpos))^[j]
            x)).re)
        + 2 * ((j : ℝ)⁻¹ * (inner ℂ y
          ((⇑(sliceHamDefect μG ρ hN2 hρcont hN β hpos))^[j]
            y)).re) := by
    intro j _
    rw [sliceHamDefect_iter_add, sliceHamDefect_iter_sub]
    have h := congrArg Complex.re
      (sliceHamDefect_iter_parallelogram μG ρ hN2 hρcont hN
        β hpos j x y)
    norm_num [Complex.add_re, Complex.mul_re] at h
    linear_combination (j : ℝ)⁻¹ * h
  calc sliceHamFormApprox μG ρ hN2 hρcont hN β hpos K (x + y)
          + sliceHamFormApprox μG ρ hN2 hρcont hN β hpos K
            (x - y)
      = ∑ j ∈ Finset.Icc 1 K,
          ((j : ℝ)⁻¹ * (inner ℂ (x + y)
              ((⇑(sliceHamDefect μG ρ hN2 hρcont hN β
                hpos))^[j] (x + y))).re
            + (j : ℝ)⁻¹ * (inner ℂ (x - y)
              ((⇑(sliceHamDefect μG ρ hN2 hρcont hN β
                hpos))^[j] (x - y))).re) := by
        unfold sliceHamFormApprox
        rw [Finset.sum_add_distrib]
    _ = ∑ j ∈ Finset.Icc 1 K,
          (2 * ((j : ℝ)⁻¹ * (inner ℂ x
              ((⇑(sliceHamDefect μG ρ hN2 hρcont hN β
                hpos))^[j] x)).re)
            + 2 * ((j : ℝ)⁻¹ * (inner ℂ y
              ((⇑(sliceHamDefect μG ρ hN2 hρcont hN β
                hpos))^[j] y)).re)) :=
        Finset.sum_congr rfl hterm
    _ = 2 * sliceHamFormApprox μG ρ hN2 hρcont hN β hpos K x
          + 2 * sliceHamFormApprox μG ρ hN2 hρcont hN β hpos
            K y := by
        unfold sliceHamFormApprox
        rw [Finset.sum_add_distrib, Finset.mul_sum,
          Finset.mul_sum]

theorem sliceHamFormApprox_zero (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (K : ℕ) :
    sliceHamFormApprox μG ρ hN2 hρcont hN β hpos K 0 = 0 := by
  unfold sliceHamFormApprox
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [sliceHamDefect_iter_zero]
  simp

theorem sliceHamFormApprox_smul (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (K : ℕ)
    (c : ℂ) (x : sliceQuotient μG ρ hN2 hρcont hN β hpos) :
    sliceHamFormApprox μG ρ hN2 hρcont hN β hpos K (c • x)
      = ‖c‖ ^ 2 * sliceHamFormApprox μG ρ hN2 hρcont hN β
          hpos K x := by
  have hterm : ∀ j : ℕ,
      (inner ℂ (c • x)
          ((⇑(sliceHamDefect μG ρ hN2 hρcont hN β
            hpos))^[j] (c • x))).re
        = ‖c‖ ^ 2 * (inner ℂ x
            ((⇑(sliceHamDefect μG ρ hN2 hρcont hN β
              hpos))^[j] x)).re := by
    intro j
    have hC : (inner ℂ (c • x)
          ((⇑(sliceHamDefect μG ρ hN2 hρcont hN β
            hpos))^[j] (c • x)))
        = ((‖c‖ ^ 2 : ℝ) : ℂ) * inner ℂ x
            ((⇑(sliceHamDefect μG ρ hN2 hρcont hN β
              hpos))^[j] x) := by
      rw [sliceHamDefect_iter_smul, inner_smul_left,
        inner_smul_right, ← mul_assoc, Complex.conj_mul',
        Complex.ofReal_pow]
    rw [hC, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im,
      (sliceHamDefect_iter_diag μG ρ hN2 hρcont hN β hpos j
        x).1]
    simp
  unfold sliceHamFormApprox
  trans (∑ j ∈ Finset.Icc 1 K, ‖c‖ ^ 2 * ((j : ℝ)⁻¹
    * (inner ℂ x ((⇑(sliceHamDefect μG ρ hN2 hρcont hN β
        hpos))^[j] x)).re))
  · exact Finset.sum_congr rfl fun j _ => by
      rw [hterm]; ring
  · rw [Finset.mul_sum]

/-! ## §4. The Hamiltonian form and its domain -/

/-- **The Hamiltonian form** `Ĥ` (form seat): the
`ℝ≥0∞`-valued supremum of the approximant forms — the
quadratic form of `-log T̂`, built from `T̂` alone. -/
noncomputable def sliceHamForm (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (x : sliceQuotient μG ρ hN2 hρcont hN β hpos) : ℝ≥0∞ :=
  ⨆ K : ℕ, ENNReal.ofReal
    (sliceHamFormApprox μG ρ hN2 hρcont hN β hpos K x)

theorem sliceHamFormApprox_le (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (K : ℕ)
    (x : sliceQuotient μG ρ hN2 hρcont hN β hpos) :
    ENNReal.ofReal
        (sliceHamFormApprox μG ρ hN2 hρcont hN β hpos K x)
      ≤ sliceHamForm μG ρ hN2 hρcont hN β hpos x :=
  le_iSup (fun K => ENNReal.ofReal
    (sliceHamFormApprox μG ρ hN2 hρcont hN β hpos K x)) K

/-- Defect iterates kill the vacuum in every positive
degree: `A Ω = 0` since `T̂ Ω = Ω` (S2-2c). -/
theorem sliceHamDefect_iter_vacuum (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (hd : 0 < d)
    {j : ℕ} (hj : 1 ≤ j) :
    (⇑(sliceHamDefect μG ρ hN2 hρcont hN β hpos))^[j]
        (sliceOmega μG ρ hN2 hρcont hN β hpos hd)
      = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  rw [Function.iterate_succ_apply,
    sliceHamDefect_apply,
    sliceHat_sliceOmega μG ρ hN2 hρcont hN β hpos hd,
    sub_self, sliceHamDefect_iter_zero]

theorem sliceHamFormApprox_vacuum (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (hd : 0 < d)
    (K : ℕ) :
    sliceHamFormApprox μG ρ hN2 hρcont hN β hpos K
        (sliceOmega μG ρ hN2 hρcont hN β hpos hd)
      = 0 := by
  unfold sliceHamFormApprox
  refine Finset.sum_eq_zero fun j hj => ?_
  rw [Finset.mem_Icc] at hj
  rw [sliceHamDefect_iter_vacuum μG ρ hN2 hρcont hN β hpos
    hd hj.1]
  simp

/-- **`Ĥ Ω = 0` (form seat):** the Hamiltonian form
vanishes at the vacuum. -/
theorem sliceHamForm_vacuum (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (hd : 0 < d) :
    sliceHamForm μG ρ hN2 hρcont hN β hpos
        (sliceOmega μG ρ hN2 hρcont hN β hpos hd)
      = 0 := by
  have hK : ∀ K : ℕ, ENNReal.ofReal
      (sliceHamFormApprox μG ρ hN2 hρcont hN β hpos K
        (sliceOmega μG ρ hN2 hρcont hN β hpos hd)) = 0 := by
    intro K
    rw [sliceHamFormApprox_vacuum μG ρ hN2 hρcont hN β hpos
      hd K]
    simp
  unfold sliceHamForm
  simp only [hK]
  exact iSup_const

/-- `ker (1 - T̂) ⊆ ker Ĥ-form`: anything the transfer
operator fixes is invisible to the Hamiltonian form. -/
theorem sliceHamForm_eq_zero_of_hat_fixed (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (x : sliceQuotient μG ρ hN2 hρcont hN β hpos)
    (hx : sliceHat μG ρ hN2 hρcont hN β hpos x = x) :
    sliceHamForm μG ρ hN2 hρcont hN β hpos x = 0 := by
  have hA : sliceHamDefect μG ρ hN2 hρcont hN β hpos x
      = 0 := by
    rw [sliceHamDefect_apply, hx, sub_self]
  have hK : ∀ K : ℕ,
      sliceHamFormApprox μG ρ hN2 hρcont hN β hpos K x
        = 0 := by
    intro K
    unfold sliceHamFormApprox
    refine Finset.sum_eq_zero fun j hj => ?_
    rw [Finset.mem_Icc] at hj
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    rw [Function.iterate_succ_apply, hA,
      sliceHamDefect_iter_zero]
    simp
  unfold sliceHamForm
  simp only [hK]
  rw [ENNReal.ofReal_zero]
  exact iSup_const

/-- **Form-domain characterization:** the Hamiltonian
form is finite at `x` iff the approximants are bounded
at `x`. -/
theorem sliceHamForm_ne_top_iff (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (x : sliceQuotient μG ρ hN2 hρcont hN β hpos) :
    sliceHamForm μG ρ hN2 hρcont hN β hpos x ≠ ⊤
      ↔ BddAbove (Set.range fun K =>
          sliceHamFormApprox μG ρ hN2 hρcont hN β hpos K
            x) := by
  constructor
  · intro hfin
    by_contra hnb
    have hunb : ∀ C : ℝ, ∃ K, C
        < sliceHamFormApprox μG ρ hN2 hρcont hN β hpos K
          x := by
      intro C
      by_contra hcon
      push_neg at hcon
      exact hnb ⟨C, fun z hz => by
        obtain ⟨K, rfl⟩ := hz
        exact hcon K⟩
    obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt hfin
    obtain ⟨K, hK⟩ := hunb n
    have h1 : ENNReal.ofReal
          (sliceHamFormApprox μG ρ hN2 hρcont hN β hpos K x)
        ≤ sliceHamForm μG ρ hN2 hρcont hN β hpos x :=
      sliceHamFormApprox_le μG ρ hN2 hρcont hN β hpos K x
    have h2 : (n : ℝ≥0∞) < ENNReal.ofReal
        (sliceHamFormApprox μG ρ hN2 hρcont hN β hpos K
          x) := by
      have h3 : ENNReal.ofReal (n : ℝ) < ENNReal.ofReal
          (sliceHamFormApprox μG ρ hN2 hρcont hN β hpos K
            x) :=
        (ENNReal.ofReal_lt_ofReal_iff_of_nonneg
          (Nat.cast_nonneg n)).mpr hK
      rwa [ENNReal.ofReal_natCast] at h3
    exact absurd (h2.trans_le h1) (not_lt_of_gt hn)
  · rintro ⟨C, hC⟩
    have hle : sliceHamForm μG ρ hN2 hρcont hN β hpos x
        ≤ ENNReal.ofReal C := by
      refine iSup_le fun K => ?_
      exact ENNReal.ofReal_le_ofReal
        (hC (Set.mem_range_self K))
    exact fun htop => ENNReal.ofReal_ne_top
      (top_unique (htop ▸ hle))

/-- **The form domain**: the finiteness locus of the
Hamiltonian form, as a submodule of the engine space
(closed under addition by the parallelogram identity,
under scaling by the form's homogeneity). -/
noncomputable def sliceHamFormDomain (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) :
    Submodule ℂ (sliceQuotient μG ρ hN2 hρcont hN β
      hpos) where
  carrier := {x | BddAbove (Set.range fun K =>
    sliceHamFormApprox μG ρ hN2 hρcont hN β hpos K x)}
  add_mem' := by
    intro x y hx hy
    obtain ⟨Cx, hCx⟩ := hx
    obtain ⟨Cy, hCy⟩ := hy
    refine ⟨2 * (Cx + Cy), fun z hz => ?_⟩
    obtain ⟨K, rfl⟩ := hz
    have hpar := sliceHamFormApprox_parallelogram μG ρ hN2
      hρcont hN β hpos K x y
    have hnn := sliceHamFormApprox_nonneg μG ρ hN2 hρcont
      hN β hpos K (x - y)
    have hbx := hCx (Set.mem_range_self K)
    have hby := hCy (Set.mem_range_self K)
    linarith
  smul_mem' := by
    intro c x hx
    obtain ⟨C, hC⟩ := hx
    refine ⟨‖c‖ ^ 2 * C, fun z hz => ?_⟩
    obtain ⟨K, rfl⟩ := hz
    show sliceHamFormApprox μG ρ hN2 hρcont hN β hpos K
        (c • x) ≤ ‖c‖ ^ 2 * C
    rw [sliceHamFormApprox_smul]
    exact mul_le_mul_of_nonneg_left
      (hC (Set.mem_range_self K)) (sq_nonneg ‖c‖)
  zero_mem' := by
    refine ⟨0, fun z hz => ?_⟩
    obtain ⟨K, rfl⟩ := hz
    show sliceHamFormApprox μG ρ hN2 hρcont hN β hpos K 0
      ≤ 0
    rw [sliceHamFormApprox_zero]

theorem sliceHam_mem_domain_iff (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (x : sliceQuotient μG ρ hN2 hρcont hN β hpos) :
    x ∈ sliceHamFormDomain μG ρ hN2 hρcont hN β hpos
      ↔ sliceHamForm μG ρ hN2 hρcont hN β hpos x ≠ ⊤ :=
  (sliceHamForm_ne_top_iff μG ρ hN2 hρcont hN β hpos
    x).symm

theorem sliceHam_vacuum_mem_domain (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (hd : 0 < d) :
    sliceOmega μG ρ hN2 hρcont hN β hpos hd
      ∈ sliceHamFormDomain μG ρ hN2 hρcont hN β hpos := by
  rw [sliceHam_mem_domain_iff,
    sliceHamForm_vacuum μG ρ hN2 hρcont hN β hpos hd]
  exact ENNReal.zero_ne_top

/-! ## §5. The discrete energy forms `Q_n` -/

theorem sliceHat_iter_inner (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (n : ℕ)
    (x y : sliceQuotient μG ρ hN2 hρcont hN β hpos) :
    inner ℂ x
        ((⇑(sliceHat μG ρ hN2 hρcont hN β hpos))^[n] y)
      = inner ℂ
          ((⇑(sliceHat μG ρ hN2 hρcont hN β hpos))^[n] x)
          y := by
  induction n generalizing x y with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply, ih,
      ← sliceHat_isSymmetric μG ρ hN2 hρcont hN β hpos _ y,
      ← Function.iterate_succ_apply'
        (⇑(sliceHat μG ρ hN2 hρcont hN β hpos)) n x]

theorem sliceHat_iter_diag_im (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (n : ℕ)
    (x : sliceQuotient μG ρ hN2 hρcont hN β hpos) :
    (inner ℂ x
      ((⇑(sliceHat μG ρ hN2 hρcont hN β hpos))^[n]
        x)).im = 0 := by
  have hstar : (starRingEnd ℂ) (inner ℂ x
        ((⇑(sliceHat μG ρ hN2 hρcont hN β hpos))^[n] x))
      = inner ℂ x
        ((⇑(sliceHat μG ρ hN2 hρcont hN β hpos))^[n]
          x) := by
    rw [inner_conj_symm]
    exact (sliceHat_iter_inner μG ρ hN2 hρcont hN β hpos n x
      x).symm
  exact Complex.conj_eq_iff_im.mp hstar

theorem sliceHat_iter_norm_le (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (n : ℕ)
    (x : sliceQuotient μG ρ hN2 hρcont hN β hpos) :
    ‖(⇑(sliceHat μG ρ hN2 hρcont hN β hpos))^[n] x‖
      ≤ ‖x‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact le_trans
      (sliceHat_norm_le μG ρ hN2 hρcont hN β hpos _) ih

/-- **The discrete energy form** `Q_n(x) = ‖x‖² - ⟪x, T̂^n
x⟫`: the one-step form is the Hamiltonian approximants'
first term; at every depth it is nonnegative with the
vacuum in its kernel — the form-level shadow of the
contraction semigroup `T̂^n` interpolated from `T̂`. -/
noncomputable def sliceEnergyForm (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (n : ℕ)
    (x : sliceQuotient μG ρ hN2 hρcont hN β hpos) : ℝ :=
  ‖x‖ ^ 2 - (inner ℂ x
    ((⇑(sliceHat μG ρ hN2 hρcont hN β hpos))^[n] x)).re

theorem sliceEnergyForm_nonneg (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (n : ℕ)
    (x : sliceQuotient μG ρ hN2 hρcont hN β hpos) :
    0 ≤ sliceEnergyForm μG ρ hN2 hρcont hN β hpos n x := by
  unfold sliceEnergyForm
  refine sub_nonneg.mpr ?_
  refine le_trans
    (le_trans
      (le_abs_self (inner ℂ x
        ((⇑(sliceHat μG ρ hN2 hρcont hN β hpos))^[n]
          x)).re)
      (Complex.abs_re_le_norm _)) ?_
  refine le_trans (norm_inner_le_norm x _) ?_
  calc ‖x‖ * ‖(⇑(sliceHat μG ρ hN2 hρcont hN β hpos))^[n]
          x‖
      ≤ ‖x‖ * ‖x‖ :=
      mul_le_mul_of_nonneg_left
        (sliceHat_iter_norm_le μG ρ hN2 hρcont hN β hpos n
          x) (norm_nonneg x)
    _ = ‖x‖ ^ 2 := by ring

theorem sliceEnergyForm_vacuum (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (hd : 0 < d)
    (n : ℕ) :
    sliceEnergyForm μG ρ hN2 hρcont hN β hpos n
        (sliceOmega μG ρ hN2 hρcont hN β hpos hd)
      = 0 := by
  have hfix : (⇑(sliceHat μG ρ hN2 hρcont hN β hpos))^[n]
        (sliceOmega μG ρ hN2 hρcont hN β hpos hd)
      = sliceOmega μG ρ hN2 hρcont hN β hpos hd :=
    Function.iterate_fixed
      (sliceHat_sliceOmega μG ρ hN2 hρcont hN β hpos hd) n
  unfold sliceEnergyForm
  rw [hfix,
    sliceHam_inner_self_re μG ρ hN2 hρcont hN β hpos _]
  exact sub_self _

/-- **Tying identity (discrete):** the depth-one energy
form IS the first Hamiltonian approximant, `Q_1 = q_1`. -/
theorem sliceEnergyForm_one_eq (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (x : sliceQuotient μG ρ hN2 hρcont hN β hpos) :
    sliceEnergyForm μG ρ hN2 hρcont hN β hpos 1 x
      = sliceHamFormApprox μG ρ hN2 hρcont hN β hpos 1
          x := by
  unfold sliceEnergyForm sliceHamFormApprox
  rw [Finset.Icc_self, Finset.sum_singleton]
  have hA1 : (⇑(sliceHamDefect μG ρ hN2 hρcont hN β
        hpos))^[1] x
      = x - sliceHat μG ρ hN2 hρcont hN β hpos x := by
    rw [Function.iterate_one]
    exact sliceHamDefect_apply μG ρ hN2 hρcont hN β hpos x
  have hT1 : (⇑(sliceHat μG ρ hN2 hρcont hN β hpos))^[1] x
      = sliceHat μG ρ hN2 hρcont hN β hpos x := by
    rw [Function.iterate_one]
  rw [hA1, hT1, inner_sub_right, Complex.sub_re,
    sliceHam_inner_self_re μG ρ hN2 hρcont hN β hpos x]
  simp

/-- **Tying inequality:** the depth-one energy form sits
under the full Hamiltonian form. -/
theorem sliceEnergyForm_one_le_hamForm (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (x : sliceQuotient μG ρ hN2 hρcont hN β hpos) :
    ENNReal.ofReal
        (sliceEnergyForm μG ρ hN2 hρcont hN β hpos 1 x)
      ≤ sliceHamForm μG ρ hN2 hρcont hN β hpos x := by
  rw [sliceEnergyForm_one_eq]
  exact sliceHamFormApprox_le μG ρ hN2 hρcont hN β hpos 1 x

/-! ## §6. The bundled package and specializations -/

/-- The depth-zero approximant vanishes (empty sum).
(Approximant monotonicity in `K` is
`sliceHamFormApprox_mono`, §2.) -/
theorem sliceHamFormApprox_zero_depth (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (x : sliceQuotient μG ρ hN2 hρcont hN β hpos) :
    sliceHamFormApprox μG ρ hN2 hρcont hN β hpos 0 x
      = 0 := by
  unfold sliceHamFormApprox
  simp

/-- **The Hamiltonian form package** (form seat): the
full list of form-level properties of `Ĥ` proved in this
brick, as one Prop for the S2-5 weld to consume. -/
def sliceHamiltonianPackage (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (hd : 0 < d) :
    Prop :=
  (∀ K (x : sliceQuotient μG ρ hN2 hρcont hN β hpos),
      0 ≤ sliceHamFormApprox μG ρ hN2 hρcont hN β hpos
        K x)
  ∧ (∀ K (x : sliceQuotient μG ρ hN2 hρcont hN β hpos),
      sliceHamFormApprox μG ρ hN2 hρcont hN β hpos K x
        ≤ sliceHamFormApprox μG ρ hN2 hρcont hN β hpos
            (K + 1) x)
  ∧ (∀ K (x y : sliceQuotient μG ρ hN2 hρcont hN β
        hpos),
      sliceHamFormApprox μG ρ hN2 hρcont hN β hpos K
          (x + y)
        + sliceHamFormApprox μG ρ hN2 hρcont hN β hpos K
            (x - y)
        = 2 * sliceHamFormApprox μG ρ hN2 hρcont hN β
              hpos K x
          + 2 * sliceHamFormApprox μG ρ hN2 hρcont hN β
              hpos K y)
  ∧ (∀ K (c : ℂ) (x : sliceQuotient μG ρ hN2 hρcont hN
        β hpos),
      sliceHamFormApprox μG ρ hN2 hρcont hN β hpos K
          (c • x)
        = ‖c‖ ^ 2 * sliceHamFormApprox μG ρ hN2 hρcont
            hN β hpos K x)
  ∧ (∀ K, sliceHamFormApprox μG ρ hN2 hρcont hN β hpos
      K 0 = 0)
  ∧ (∀ x : sliceQuotient μG ρ hN2 hρcont hN β hpos,
      sliceHamFormApprox μG ρ hN2 hρcont hN β hpos 0 x
        = 0)
  ∧ sliceHamForm μG ρ hN2 hρcont hN β hpos
      (sliceOmega μG ρ hN2 hρcont hN β hpos hd) = 0
  ∧ sliceOmega μG ρ hN2 hρcont hN β hpos hd
      ∈ sliceHamFormDomain μG ρ hN2 hρcont hN β hpos
  ∧ (∀ x : sliceQuotient μG ρ hN2 hρcont hN β hpos,
      x ∈ sliceHamFormDomain μG ρ hN2 hρcont hN β hpos
        ↔ sliceHamForm μG ρ hN2 hρcont hN β hpos x ≠ ⊤)
  ∧ (∀ n (x : sliceQuotient μG ρ hN2 hρcont hN β hpos),
      0 ≤ sliceEnergyForm μG ρ hN2 hρcont hN β hpos n x)
  ∧ (∀ n, sliceEnergyForm μG ρ hN2 hρcont hN β hpos n
      (sliceOmega μG ρ hN2 hρcont hN β hpos hd) = 0)
  ∧ (∀ x : sliceQuotient μG ρ hN2 hρcont hN β hpos,
      sliceEnergyForm μG ρ hN2 hρcont hN β hpos 1 x
        = sliceHamFormApprox μG ρ hN2 hρcont hN β hpos
            1 x)
  ∧ (∀ x : sliceQuotient μG ρ hN2 hρcont hN β hpos,
      ENNReal.ofReal (sliceEnergyForm μG ρ hN2 hρcont hN
          β hpos 1 x)
        ≤ sliceHamForm μG ρ hN2 hρcont hN β hpos x)
  ∧ (∀ x : sliceQuotient μG ρ hN2 hρcont hN β hpos,
      sliceHat μG ρ hN2 hρcont hN β hpos x = x
        → sliceHamForm μG ρ hN2 hρcont hN β hpos x = 0)
  ∧ (∀ K (x : sliceQuotient μG ρ hN2 hρcont hN β hpos),
      ENNReal.ofReal (sliceHamFormApprox μG ρ hN2 hρcont
          hN β hpos K x)
        ≤ sliceHamForm μG ρ hN2 hρcont hN β hpos x)

/-- **S2-4 headline (conditional, general `(G, ρ)`):**
the Hamiltonian form package holds on the S2-2 engine
space at every real `β`, under the engine's one
hypothesis `SliceHPosOne`. Form seat only: no operator
`Ĥ`, no `exp(-Ĥ) = T̂` claim. -/
theorem sliceHamiltonian_package (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (hd : 0 < d) :
    sliceHamiltonianPackage μG ρ hN2 hρcont hN β hpos
      hd :=
  ⟨fun K x => sliceHamFormApprox_nonneg μG ρ hN2 hρcont
      hN β hpos K x,
   fun K x => sliceHamFormApprox_mono μG ρ hN2 hρcont hN
      β hpos x (Nat.le_succ K),
   fun K x y => sliceHamFormApprox_parallelogram μG ρ
      hN2 hρcont hN β hpos K x y,
   fun K c x => sliceHamFormApprox_smul μG ρ hN2 hρcont
      hN β hpos K c x,
   fun K => sliceHamFormApprox_zero μG ρ hN2 hρcont hN β
      hpos K,
   fun x => sliceHamFormApprox_zero_depth μG ρ hN2
      hρcont hN β hpos x,
   sliceHamForm_vacuum μG ρ hN2 hρcont hN β hpos hd,
   sliceHam_vacuum_mem_domain μG ρ hN2 hρcont hN β hpos
      hd,
   fun x => sliceHam_mem_domain_iff μG ρ hN2 hρcont hN
      β hpos x,
   fun n x => sliceEnergyForm_nonneg μG ρ hN2 hρcont hN
      β hpos n x,
   fun n => sliceEnergyForm_vacuum μG ρ hN2 hρcont hN β
      hpos hd n,
   fun x => sliceEnergyForm_one_eq μG ρ hN2 hρcont hN β
      hpos x,
   fun x => sliceEnergyForm_one_le_hamForm μG ρ hN2
      hρcont hN β hpos x,
   fun x hx => sliceHamForm_eq_zero_of_hat_fixed μG ρ
      hN2 hρcont hN β hpos x hx,
   fun K x => sliceHamFormApprox_le μG ρ hN2 hρcont hN
      β hpos K x⟩

/-- **S2-4 at the U(1) seat (unconditional, `β ≥ 0`):**
the full Hamiltonian form package at `(haarProb Circle,
circleRep)`, feeding the hypothesis-free discharge
`sliceHPosOne_circle` (S2-3). Seat only — not a general
`(G, ρ)` result. -/
theorem sliceHamiltonian_circle_package (hN2 : 2 ≤ N)
    (hN : Even N) (β : ℝ) (hβ : 0 ≤ β) :
    sliceHamiltonianPackage (haarProb Circle) circleRep
      hN2 circleRep_continuous hN β
      (sliceHPosOne_circle hN2 hN β hβ) zero_lt_one :=
  sliceHamiltonian_package (haarProb Circle) circleRep
    hN2 circleRep_continuous hN β
    (sliceHPosOne_circle hN2 hN β hβ) zero_lt_one

/-- **β = 0 regression for the form:** at `β = 0` the
engine's `T̂` is the identity (S2-2d), so the defect
vanishes on every vector and every approximant is `0`. -/
theorem sliceHamFormApprox_beta_zero (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (hd : 0 < d) (K : ℕ)
    (x : sliceQuotient μG ρ hN2 hρcont hN 0
      (sliceHPosOne_zero μG ρ hN2 hρcont hN hd)) :
    sliceHamFormApprox μG ρ hN2 hρcont hN 0
        (sliceHPosOne_zero μG ρ hN2 hρcont hN hd) K x
      = 0 := by
  unfold sliceHamFormApprox
  refine Finset.sum_eq_zero fun j hj => ?_
  have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  have hA0 : sliceHamDefect μG ρ hN2 hρcont hN 0
        (sliceHPosOne_zero μG ρ hN2 hρcont hN hd) x
      = 0 := by
    rw [sliceHamDefect_apply]
    have h0 : sliceHat μG ρ hN2 hρcont hN 0
          (sliceHPosOne_zero μG ρ hN2 hρcont hN hd) x
        = x := by
      simp only [sliceRegression_hat_eq_id μG ρ hN2
        hρcont hN hd, LinearMap.id_apply]
    rw [h0]
    exact sub_self x
  have hvan : (⇑(sliceHamDefect μG ρ hN2 hρcont hN 0
        (sliceHPosOne_zero μG ρ hN2 hρcont hN hd)))^[k + 1]
        x = 0 := by
    rw [Function.iterate_succ_apply, hA0]
    exact sliceHamDefect_iter_zero μG ρ hN2 hρcont hN 0
      (sliceHPosOne_zero μG ρ hN2 hρcont hN hd) k
  rw [hvan]
  simp

/-- **β = 0 regression for the form (headline):** the
Hamiltonian form is identically zero at `β = 0`, for
general `(G, ρ)` — the form-level shadow of `T̂ = id`. -/
theorem sliceHamForm_beta_zero (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (hd : 0 < d)
    (x : sliceQuotient μG ρ hN2 hρcont hN 0
      (sliceHPosOne_zero μG ρ hN2 hρcont hN hd)) :
    sliceHamForm μG ρ hN2 hρcont hN 0
        (sliceHPosOne_zero μG ρ hN2 hρcont hN hd) x
      = 0 := by
  simp only [sliceHamForm,
    sliceHamFormApprox_beta_zero μG ρ hN2 hρcont hN hd,
    ENNReal.ofReal_zero, iSup_const]

end SliceHamiltonian

end ThetLogos
