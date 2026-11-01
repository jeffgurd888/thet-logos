/-
# SHELF-8a - the holomorphic (Dunford-Riesz) functional calculus (working label)

Brick SHELF-8a of the SHELF line (scoping map
`routeb-general-scratch/scoping-shelf-map-2026-10-30.md`,
item 8a): the holomorphic (Dunford-Riesz) functional calculus
for complex Banach-algebra elements. NO CLAIM beyond the
theorems below; no dial is touched.

## Step 0 - the pin probe (done first, 2026-11-01)

Pin: Mathlib v4.35.0-rc3 (this tree). What the pin already
owns in this area (file:line at probe time):

* Continuous functional calculus `cfc` / `cfcHom` for
  *normal* elements of C*-algebras (predicate-gated):
  `Mathlib/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Unital.lean`
  (`cfcHom` line 239, `cfc` line 307, spectral mapping
  `cfcHom_map_spectrum` line 254). This is NOT a holomorphic
  calculus: it applies to continuous functions and normal
  elements only.
* `spectrum` / `resolventSet` / `resolvent`:
  `Mathlib/Algebra/Algebra/Spectrum/Basic.lean` (lines 64,
  72, 80).
* Spectrum basics for normed algebras: closedness,
  compactness, boundedness, the spectral radius and
  Gelfand's formula: `Mathlib/Analysis/Normed/Algebra/Spectrum.lean`
  (`spectralRadius` line 82, `spectrum.isCompact` line 203,
  `spectrum.eventually_isUnit_resolvent` line 320) and
  `Mathlib/Analysis/Normed/Algebra/GelfandFormula.lean`
  (`spectrum.nonempty` line 146, resolvent differentiability
  lines 53-84, the POLYNOMIAL spectral mapping theorem
  `spectrum.map_polynomial_aeval` line 175).
* The Cauchy product formula for absolutely summable series
  in a normed ring:
  `Mathlib/Analysis/Normed/Ring/InfiniteSum.lean`
  (`tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm`
  line 118 and the `range` form line 146).
* The circle integral and Cauchy-Goursat / Cauchy integral
  formula for Banach-space-valued functions:
  `Mathlib/MeasureTheory/Integral/CircleIntegral.lean` and
  `Mathlib/Analysis/Complex/CauchyIntegral.lean`
  (annulus Cauchy-Goursat line 352, disk Cauchy integral
  formula line 497).
* The exponential as a convergent power series:
  `Mathlib/Analysis/Normed/Algebra/Exponential.lean`
  (`NormedSpace.expSeries_sum_eq` line 146).

What the pin does NOT own (grep of the full Mathlib tree):
any holomorphic functional calculus, any Dunford / Dunford-
Riesz integral or definition (`Dunford` occurs only in
`Mathlib/LinearAlgebra/JordanChevalley.lean`, for the
finite-dimensional Dunford decomposition of an endomorphism,
and in an unrelated measure-theory file). That absence is
the gap this brick stocks. Nothing above is rebuilt here
(K-SHELF-RENAME respected): the pin's objects are cited and
consumed, not renamed.

## Outcome: PARTIAL at the pack's pre-registered seam

The general Dunford-Riesz definition (integral over a
contour system surrounding `spectrum C a` in an arbitrary
neighbourhood where `f` is holomorphic) is NOT landed: its
honesty requires contour-system independence at a
generality this pin's API does not yet package, and a
forced definition resting on unproved well-definedness is
exactly what the pack forbids. The general contour form is
the named open remainder, stated on this face.

What IS landed is the largest coherent fragment the pin's
API carries, the DISC (power-series) fragment:

* `hfcDisc a c`: the value at `a` of the power series with
  coefficient sequence `c : Nat -> C`, for `a` in a complex
  normed algebra with `NormOneClass` (complete), whenever
  `c` is absolutely summable at a scale `r >= ||a||`
  (`DiscSummable r c`). This is the Dunford calculus of a
  function holomorphic on a disc centred at `0` of radius
  `> r`, presented by its Taylor coefficients at `0`.
* Load-bearing rules proved for the fragment: summability
  and the norm estimate; the values on the zero, constant
  and monomial series; agreement with the polynomial
  calculus (`Polynomial.aeval`); additivity, scalar
  multiplication and negation; multiplicativity under the
  Cauchy (convolution) product of coefficient sequences;
  commutation of `hfcDisc a c` with `a`; the exponential
  series evaluates to `NormedSpace.exp`.
* Spectral mapping at this grade: (i) for polynomials the
  FULL spectral mapping theorem, transferred from the pin's
  `spectrum.map_polynomial_aeval` through the polynomial
  agreement; (ii) for the disc fragment, the forward
  inclusion: a spectral value `lam` of `a` maps to the
  scalar series value `scalarEval c lam` in the spectrum of
  `hfcDisc a c`, proved by the standard factorisation
  `f(z) - f(lam) = (z - lam) * g(z)` at coefficient level.

## Named remainders (never silently dropped)

* The general contour (Dunford-Riesz) definition for `f`
  holomorphic on an arbitrary neighbourhood of the spectrum,
  and independence of the chosen contour system.
* The reverse spectral inclusion for the disc fragment
  (the forward inclusion and the polynomial case are here).
* Sharpening the scale hypothesis from the norm scale
  `||a|| <= r` to the spectral-radius scale
  `spectralRadius C a < r`.
* A bundled algebra-homomorphism package out of a disc
  coefficient algebra type: the homomorphism rules are
  landed as theorems about coefficient sequences.
* The identification of `hfcDisc` with a circle integral
  of `f * resolvent` over `|z| = R`: the pin owns both
  sides' ingredients (see the probe) but the coefficient-
  extraction argument is not landed here.
* SHELF-8b (Riesz projections) gates on the general form
  and is not touched.

This module asserts no physics and no corpus claim; it
stocks a tool the record said was missing.
-/

import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.Normed.Algebra.Exponential

namespace ThetLogos

open Filter Set
open scoped Topology Nat

noncomputable section

variable {A : Type*} [NormedRing A] [NormOneClass A] [NormedAlgebra ℂ A]
  [CompleteSpace A] {a : A}

/-! ## 1. The disc fragment: data and definition -/

/-- Absolute summability of a coefficient sequence
`c : Nat -> C` at scale `r`: `sum' n, ||c n|| * r ^ n`
converges. This is the hypothesis that the power series
with coefficients `c` converges absolutely on the closed
disc of radius `r`. -/
def DiscSummable (r : ℝ) (c : ℕ → ℂ) : Prop :=
  Summable fun n => ‖c n‖ * r ^ n

/-- The disc (power-series) functional calculus: for
`a` in a complex Banach algebra and a coefficient sequence
`c`, `hfcDisc a c = sum' n, c n * a ^ n` (with `c n`
acting by the algebra scalar action). When `c` is not
absolutely summable at a scale `>= ||a||` this is the
junk value of a non-summable `tsum`; every theorem below
carries the summability hypothesis on its face. -/
def hfcDisc (a : A) (c : ℕ → ℂ) : A :=
  ∑' n, c n • a ^ n

/-- The scalar value of the series with coefficients `c`
at a scalar point `z`: `sum' n, c n * z ^ n`. -/
def scalarEval (c : ℕ → ℂ) (z : ℂ) : ℂ :=
  ∑' n, c n * z ^ n

/-! ## 2. Summability and the norm estimate -/

theorem summable_norm_smul_pow {r : ℝ} (hr : ‖a‖ ≤ r) {c : ℕ → ℂ}
    (hc : DiscSummable r c) : Summable fun n => ‖c n • a ^ n‖ := by
  refine Summable.of_norm_bounded hc (fun n => ?_)
  calc ‖‖c n • a ^ n‖‖ = ‖c n • a ^ n‖ := Real.norm_of_nonneg (norm_nonneg _)
    _ ≤ ‖c n‖ * ‖a ^ n‖ := norm_smul_le _ _
    _ ≤ ‖c n‖ * r ^ n :=
        mul_le_mul_of_nonneg_left
          ((norm_pow_le a n).trans (pow_le_pow_left₀ (norm_nonneg a) hr n))
          (norm_nonneg _)

theorem summable_smul_pow {r : ℝ} (hr : ‖a‖ ≤ r) {c : ℕ → ℂ}
    (hc : DiscSummable r c) : Summable fun n => c n • a ^ n :=
  (summable_norm_smul_pow hr hc).of_norm

theorem hfcDisc_norm_le {r : ℝ} (hr : ‖a‖ ≤ r) {c : ℕ → ℂ}
    (hc : DiscSummable r c) : ‖hfcDisc a c‖ ≤ ∑' n, ‖c n‖ * r ^ n := by
  refine (norm_tsum_le_tsum_norm (summable_norm_smul_pow hr hc)).trans ?_
  refine Summable.tsum_le_tsum (fun n => ?_) (summable_norm_smul_pow hr hc) hc
  calc ‖c n • a ^ n‖ ≤ ‖c n‖ * ‖a ^ n‖ := norm_smul_le _ _
    _ ≤ ‖c n‖ * r ^ n :=
        mul_le_mul_of_nonneg_left
          ((norm_pow_le a n).trans (pow_le_pow_left₀ (norm_nonneg a) hr n))
          (norm_nonneg _)

/-! ## 3. Elementary values -/

theorem hfcDisc_zero : hfcDisc a (fun _ => (0 : ℂ)) = 0 := by
  simp [hfcDisc]

theorem hfcDisc_const (z : ℂ) :
    hfcDisc a (fun n => if n = 0 then z else 0) = z • (1 : A) := by
  rw [hfcDisc, tsum_eq_single 0]
  · simp
  · intro n hn
    simp [hn]

theorem hfcDisc_one :
    hfcDisc a (fun n => if n = 0 then (1 : ℂ) else 0) = 1 := by
  rw [hfcDisc_const]; simp

theorem hfcDisc_monomial (n : ℕ) :
    hfcDisc a (fun m => if m = n then (1 : ℂ) else 0) = a ^ n := by
  rw [hfcDisc, tsum_eq_single n]
  · simp
  · intro m hm
    simp [hm]

/-! ## 4. Agreement with the polynomial calculus -/

theorem discSummable_polynomial_coeff (r : ℝ) (p : Polynomial ℂ) :
    DiscSummable r (fun n => p.coeff n) := by
  refine summable_of_ne_finset_zero (s := Finset.range (p.natDegree + 1)) (fun n hn => ?_)
  have hn' : p.natDegree + 1 ≤ n := by
    simpa [Finset.mem_range] using hn
  simp [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : p.natDegree < n)]

theorem hfcDisc_polynomial (p : Polynomial ℂ) :
    hfcDisc a (fun n => p.coeff n) = Polynomial.aeval a p := by
  rw [hfcDisc, tsum_eq_sum (s := Finset.range (p.natDegree + 1)),
    Polynomial.aeval_eq_sum_range]
  · intro n hn
    have hn' : p.natDegree + 1 ≤ n := by
      simpa [Finset.mem_range] using hn
    simp [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : p.natDegree < n)]

/-! ## 5. The homomorphism rules for the disc fragment -/

theorem discSummable_add {r : ℝ} (hr : 0 ≤ r) {c d : ℕ → ℂ}
    (hc : DiscSummable r c) (hd : DiscSummable r d) :
    DiscSummable r (fun n => c n + d n) := by
  refine Summable.of_norm_bounded (hc.add hd) (fun n => ?_)
  calc ‖‖c n + d n‖ * r ^ n‖ = ‖c n + d n‖ * r ^ n := by
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) (pow_nonneg hr n))]
    _ ≤ (‖c n‖ + ‖d n‖) * r ^ n :=
        mul_le_mul_of_nonneg_right (norm_add_le _ _) (pow_nonneg hr n)
    _ = ‖c n‖ * r ^ n + ‖d n‖ * r ^ n := by ring

theorem hfcDisc_add {r : ℝ} (hr : ‖a‖ ≤ r) {c d : ℕ → ℂ}
    (hc : DiscSummable r c) (hd : DiscSummable r d) :
    hfcDisc a (fun n => c n + d n) = hfcDisc a c + hfcDisc a d := by
  have hs := (summable_smul_pow hr hc).hasSum.add (summable_smul_pow hr hd).hasSum
  show ∑' n, (c n + d n) • a ^ n = (∑' n, c n • a ^ n) + ∑' n, d n • a ^ n
  rw [← hs.tsum_eq]
  exact tsum_congr fun n => add_smul _ _ _

theorem discSummable_smul {r : ℝ} (z : ℂ) {c : ℕ → ℂ}
    (hc : DiscSummable r c) : DiscSummable r (fun n => z * c n) :=
  Summable.congr (hc.mul_left ‖z‖) (fun n => by rw [norm_mul]; ring)

theorem hfcDisc_smul {r : ℝ} (hr : ‖a‖ ≤ r) (z : ℂ) {c : ℕ → ℂ}
    (hc : DiscSummable r c) :
    hfcDisc a (fun n => z * c n) = z • hfcDisc a c := by
  show ∑' n, (z * c n) • a ^ n = z • ∑' n, c n • a ^ n
  rw [← (summable_smul_pow hr hc).tsum_const_smul z]
  exact tsum_congr fun n => (smul_smul z (c n) (a ^ n)).symm

/-- The Cauchy (convolution) product of coefficient
sequences: the coefficient sequence of a product of power
series. -/
def discConv (c d : ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑ kl ∈ Finset.antidiagonal n, c kl.1 * d kl.2

theorem discSummable_conv {r : ℝ} (hr : 0 ≤ r) {c d : ℕ → ℂ}
    (hc : DiscSummable r c) (hd : DiscSummable r d) :
    DiscSummable r (discConv c d) := by
  have hc' : Summable fun n => ‖‖c n‖ * r ^ n‖ :=
    Summable.congr hc fun n => by
      rw [Real.norm_eq_abs]
      exact (abs_of_nonneg (mul_nonneg (norm_nonneg _) (pow_nonneg hr n))).symm
  have hd' : Summable fun n => ‖‖d n‖ * r ^ n‖ :=
    Summable.congr hd fun n => by
      rw [Real.norm_eq_abs]
      exact (abs_of_nonneg (mul_nonneg (norm_nonneg _) (pow_nonneg hr n))).symm
  have key := summable_norm_sum_mul_antidiagonal_of_summable_norm hc' hd'
  have hnorm : ∀ n, ‖discConv c d n‖
      ≤ ∑ kl ∈ Finset.antidiagonal n, ‖c kl.1‖ * ‖d kl.2‖ := by
    intro n
    rw [discConv]
    refine (norm_sum_le (Finset.antidiagonal n)
      (fun kl => c kl.1 * d kl.2)).trans (le_of_eq ?_)
    exact Finset.sum_congr rfl fun kl _ => norm_mul _ _
  refine Summable.of_norm_bounded key (fun n => ?_)
  calc ‖‖discConv c d n‖ * r ^ n‖ = ‖discConv c d n‖ * r ^ n := by
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) (pow_nonneg hr n))]
    _ ≤ (∑ kl ∈ Finset.antidiagonal n, ‖c kl.1‖ * ‖d kl.2‖) * r ^ n :=
        mul_le_mul_of_nonneg_right (hnorm n) (pow_nonneg hr n)
    _ = ∑ kl ∈ Finset.antidiagonal n,
          (‖c kl.1‖ * r ^ kl.1) * (‖d kl.2‖ * r ^ kl.2) := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun kl hkl => ?_
        have hsum : kl.1 + kl.2 = n := Finset.mem_antidiagonal.mp hkl
        rw [← hsum, pow_add]; ring
    _ = ‖∑ kl ∈ Finset.antidiagonal n,
          (‖c kl.1‖ * r ^ kl.1) * (‖d kl.2‖ * r ^ kl.2)‖ := by
        rw [Real.norm_of_nonneg (Finset.sum_nonneg fun kl _ =>
          mul_nonneg (mul_nonneg (norm_nonneg _) (pow_nonneg hr _))
            (mul_nonneg (norm_nonneg _) (pow_nonneg hr _)))]

theorem hfcDisc_mul {r : ℝ} (hr : ‖a‖ ≤ r) {c d : ℕ → ℂ}
    (hc : DiscSummable r c) (hd : DiscSummable r d) :
    hfcDisc a (discConv c d) = hfcDisc a c * hfcDisc a d := by
  have hprod := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm
    (f := fun n => c n • a ^ n) (g := fun n => d n • a ^ n)
    (summable_norm_smul_pow hr hc) (summable_norm_smul_pow hr hd)
  show ∑' n, discConv c d n • a ^ n
    = (∑' n, c n • a ^ n) * ∑' n, d n • a ^ n
  rw [hprod]
  refine tsum_congr fun n => ?_
  rw [discConv, Finset.sum_smul]
  refine Finset.sum_congr rfl fun kl hkl => ?_
  have hsum : kl.1 + kl.2 = n := Finset.mem_antidiagonal.mp hkl
  rw [← hsum, pow_add, smul_mul_assoc, mul_smul_comm, smul_smul]

theorem commute_a_hfcDisc (c : ℕ → ℂ) : Commute a (hfcDisc a c) := by
  refine Commute.tsum_right a fun n => ?_
  show Commute a (c n • a ^ n)
  show a * (c n • a ^ n) = (c n • a ^ n) * a
  rw [smul_mul_assoc, mul_smul_comm, ← pow_succ', ← pow_succ]

theorem commute_hfcDisc_hfcDisc (c d : ℕ → ℂ) :
    Commute (hfcDisc a c) (hfcDisc a d) := by
  show Commute (∑' n, c n • a ^ n) (∑' m, d m • a ^ m)
  refine Commute.tsum_left _ fun n => Commute.tsum_right _ fun m => ?_
  show Commute (c n • a ^ n) (d m • a ^ m)
  show (c n • a ^ n) * (d m • a ^ m) = (d m • a ^ m) * (c n • a ^ n)
  calc (c n • a ^ n) * (d m • a ^ m) = (c n * d m) • (a ^ n * a ^ m) := by
        rw [smul_mul_assoc, mul_smul_comm, smul_smul]
    _ = (d m * c n) • (a ^ m * a ^ n) := by
        rw [mul_comm (c n) (d m), ← pow_add, add_comm n m, ← pow_add]
    _ = (d m • a ^ m) * (c n • a ^ n) := by
        rw [smul_mul_assoc, mul_smul_comm, smul_smul]

/-! ## 6. The exponential series -/

theorem discSummable_exp_coeff (r : ℝ) :
    DiscSummable r (fun n => ((n ! : ℂ))⁻¹) := by
  have key := Real.summable_pow_div_factorial |r|
  refine Summable.of_norm_bounded key (fun n => ?_)
  have h1 : ‖((n ! : ℂ))⁻¹‖ = (n ! : ℝ)⁻¹ := by
    rw [norm_inv, Complex.norm_natCast]
  calc ‖‖((n ! : ℂ))⁻¹‖ * r ^ n‖ = (n ! : ℝ)⁻¹ * |r| ^ n := by
        rw [Real.norm_eq_abs, abs_mul, abs_pow, h1,
          abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((n ! : ℝ))⁻¹)]
    _ ≤ |r| ^ n / n ! := le_of_eq (by rw [div_eq_mul_inv, mul_comm])

theorem hfcDisc_exp : hfcDisc a (fun n => ((n ! : ℂ))⁻¹) = NormedSpace.exp a := by
  show ∑' n, ((n ! : ℂ))⁻¹ • a ^ n = NormedSpace.exp a
  rw [NormedSpace.exp_eq_tsum ℂ]

/-! ## 7. Spectral mapping at this grade -/

section Spectral

variable [Nontrivial A]

/-- Spectral mapping for the disc fragment, polynomial
case: the FULL spectral mapping theorem for polynomials,
transferred from the pin's `spectrum.map_polynomial_aeval`
through `hfcDisc_polynomial`. -/
theorem spectrum_hfcDisc_polynomial (p : Polynomial ℂ) :
    spectrum ℂ (hfcDisc a (fun n => p.coeff n))
      = (fun z => Polynomial.eval z p) '' spectrum ℂ a := by
  rw [hfcDisc_polynomial]
  exact spectrum.map_polynomial_aeval a p

/-- The scalar series value is summable at every point of
the closed disc of radius `r` when the coefficients are. -/
theorem summable_scalarEval {r : ℝ} {c : ℕ → ℂ} (hc : DiscSummable r c) {z : ℂ}
    (hz : ‖z‖ ≤ r) : Summable fun n => c n * z ^ n := by
  refine Summable.of_norm (Summable.of_norm_bounded hc (fun n => ?_))
  rw [Real.norm_of_nonneg (norm_nonneg (c n * z ^ n)), norm_mul, norm_pow]
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg z) hz n) (norm_nonneg (c n))

end Spectral

/-! ## 8. Factorisation and the forward spectral inclusion

The standard factorisation `f(z) - f(lam) = (z - lam) g(z)`
at coefficient level, giving the forward spectral
inclusion for the disc fragment. -/

theorem discSummable_mono {R s : ℝ} (hs : 0 ≤ s) (hsR : s ≤ R) {c : ℕ → ℂ}
    (hc : DiscSummable R c) : DiscSummable s c := by
  refine Summable.of_norm_bounded hc (fun n => ?_)
  rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (pow_nonneg hs n))]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hs hsR n) (norm_nonneg (c n))

theorem norm_tail_term_le {R : ℝ} (hR : 0 < R) {c : ℕ → ℂ} {lam : ℂ}
    (hlam : ‖lam‖ ≤ R) (m k : ℕ) :
    ‖c (k + m) * lam ^ k‖ ≤ (R ^ m)⁻¹ * (‖c (k + m)‖ * R ^ (k + m)) := by
  have hRm : (R ^ m) ≠ 0 := pow_ne_zero _ hR.ne'
  rw [norm_mul, norm_pow, pow_add]
  calc ‖c (k + m)‖ * ‖lam‖ ^ k ≤ ‖c (k + m)‖ * R ^ k :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg lam) hlam k)
          (norm_nonneg _)
    _ = (R ^ m)⁻¹ * (‖c (k + m)‖ * (R ^ k * R ^ m)) := by
        field_simp

theorem summable_norm_tail {R : ℝ} (hR : 0 < R) {c : ℕ → ℂ}
    (hc : DiscSummable R c) {lam : ℂ} (hlam : ‖lam‖ ≤ R) (m : ℕ) :
    Summable fun k => ‖c (k + m) * lam ^ k‖ := by
  have hF : Summable fun k => ‖c (k + m)‖ * R ^ (k + m) :=
    (summable_nat_add_iff m).mpr hc
  refine Summable.of_norm_bounded (hF.mul_left (R ^ m)⁻¹) (fun k => ?_)
  rw [Real.norm_of_nonneg (norm_nonneg _)]
  exact norm_tail_term_le hR hlam m k

theorem summable_tail {R : ℝ} (hR : 0 < R) {c : ℕ → ℂ}
    (hc : DiscSummable R c) {lam : ℂ} (hlam : ‖lam‖ ≤ R) (m : ℕ) :
    Summable fun k => c (k + m) * lam ^ k :=
  (summable_norm_tail hR hc hlam m).of_norm

/-- The tail coefficient sequence of the factorisation
`f(z) - f(lam) = (z - lam) * g(z)`: the `n`-th Taylor
coefficient of `g` at `0` is
`sum' k, c (k + n + 1) * lam ^ k`. -/
def discTail (c : ℕ → ℂ) (lam : ℂ) (n : ℕ) : ℂ :=
  ∑' k, c (k + (n + 1)) * lam ^ k

set_option maxHeartbeats 1600000 in
theorem norm_discTail_le {R : ℝ} (hR : 0 < R) {c : ℕ → ℂ}
    (hc : DiscSummable R c) {lam : ℂ} (hlam : ‖lam‖ ≤ R) (n : ℕ) :
    ‖discTail c lam n‖ ≤ (R ^ (n + 1))⁻¹ * ∑' m, ‖c m‖ * R ^ m := by
  show ‖∑' k, c (k + (n + 1)) * lam ^ k‖
    ≤ (R ^ (n + 1))⁻¹ * ∑' m, ‖c m‖ * R ^ m
  have hF : Summable fun k => ‖c (k + (n + 1))‖ * R ^ (k + (n + 1)) :=
    (summable_nat_add_iff (n + 1)).mpr hc
  have hshift : (∑' k, ‖c (k + (n + 1))‖ * R ^ (k + (n + 1)))
      ≤ ∑' m, ‖c m‖ * R ^ m := by
    have h := Summable.sum_add_tsum_nat_add (n + 1) hc
    have hnonneg : 0 ≤ ∑ i ∈ Finset.range (n + 1), ‖c i‖ * R ^ i :=
      Finset.sum_nonneg fun i _ => mul_nonneg (norm_nonneg _) (pow_nonneg hR.le _)
    exact h ▸ le_add_of_nonneg_left hnonneg
  refine (norm_tsum_le_tsum_norm (summable_norm_tail hR hc hlam (n + 1))).trans ?_
  refine (Summable.tsum_le_tsum (fun k => norm_tail_term_le hR hlam (n + 1) k)
    (summable_norm_tail hR hc hlam (n + 1)) (hF.mul_left _)).trans ?_
  rw [tsum_mul_left]
  exact mul_le_mul_of_nonneg_left hshift (inv_nonneg.mpr (pow_nonneg hR.le _))

theorem discSummable_discTail {R s : ℝ} (hR : 0 < R) (hs : 0 ≤ s) (hsR : s < R)
    {c : ℕ → ℂ} (hc : DiscSummable R c) {lam : ℂ} (hlam : ‖lam‖ ≤ R) :
    DiscSummable s (discTail c lam) := by
  have hT : Summable fun n => (R⁻¹ * (∑' m, ‖c m‖ * R ^ m)) * (s / R) ^ n :=
    (summable_geometric_of_lt_one (div_nonneg hs hR.le)
      (by rwa [div_lt_one hR])).mul_left _
  refine Summable.of_norm_bounded hT (fun n => ?_)
  rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (pow_nonneg hs n))]
  calc ‖discTail c lam n‖ * s ^ n
      ≤ ((R ^ (n + 1))⁻¹ * ∑' m, ‖c m‖ * R ^ m) * s ^ n :=
        mul_le_mul_of_nonneg_right (norm_discTail_le hR hc hlam n) (pow_nonneg hs n)
    _ = (R⁻¹ * (∑' m, ‖c m‖ * R ^ m)) * (s / R) ^ n := by
        rw [pow_succ, div_pow]
        field_simp

theorem scalarEval_eq {R : ℝ} (hR : 0 < R) {c : ℕ → ℂ} (hc : DiscSummable R c)
    {lam : ℂ} (hlam : ‖lam‖ ≤ R) :
    scalarEval c lam = c 0 + lam * discTail c lam 0 := by
  have e1 : (∑' i, c (i + 1) * lam ^ (i + 1)) = lam * discTail c lam 0 := by
    rw [discTail, ← tsum_mul_left]
    exact tsum_congr fun i => by rw [pow_succ]; ring
  have h := Summable.sum_add_tsum_nat_add 1 (summable_tail hR hc hlam 0)
  simp only [Finset.sum_range_one, add_zero, pow_zero, mul_one] at h
  rw [scalarEval, ← h, e1]

theorem discTail_pred {R : ℝ} (hR : 0 < R) {c : ℕ → ℂ} (hc : DiscSummable R c)
    {lam : ℂ} (hlam : ‖lam‖ ≤ R) (n : ℕ) :
    discTail c lam n = c (n + 1) + lam * discTail c lam (n + 1) := by
  have e1 : (∑' i, c (i + 1 + (n + 1)) * lam ^ (i + 1))
      = lam * discTail c lam (n + 1) := by
    rw [discTail, ← tsum_mul_left]
    refine tsum_congr fun i => ?_
    have ei : i + 1 + (n + 1) = i + (n + 1 + 1) := by ring
    rw [ei, pow_succ]; ring
  have h := Summable.sum_add_tsum_nat_add 1 (summable_tail hR hc hlam (n + 1))
  simp only [Finset.sum_range_one, zero_add, pow_zero, mul_one] at h
  rw [discTail, ← h, e1]

/-- The coefficient sequence of the polynomial `X - lam`,
as a series: `-lam` at `0`, `1` at `1`, `0` elsewhere. -/
def discFactor (lam : ℂ) : ℕ → ℂ :=
  fun n => if n = 0 then -lam else if n = 1 then 1 else 0

theorem discSummable_discFactor (R : ℝ) (lam : ℂ) :
    DiscSummable R (discFactor lam) :=
  summable_of_ne_finset_zero (s := {0, 1}) (by
    intro n hn
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
    simp [discFactor, hn.1, hn.2])

theorem hfcDisc_discFactor (lam : ℂ) :
    hfcDisc a (discFactor lam) = a - lam • (1 : A) := by
  have hDS1 : DiscSummable ‖a‖ (fun n => if n = 0 then -lam else (0 : ℂ)) :=
    summable_of_ne_finset_zero (s := {0}) (by
      intro n hn
      have hn0 : n ≠ 0 := by simpa using hn
      simp [hn0])
  have hDS2 : DiscSummable ‖a‖ (fun n => if n = 1 then (1 : ℂ) else 0) :=
    summable_of_ne_finset_zero (s := {1}) (by
      intro n hn
      have hn1 : n ≠ 1 := by simpa using hn
      simp [hn1])
  have hfun : discFactor lam
      = (fun n => (if n = 0 then -lam else (0 : ℂ))
        + (if n = 1 then (1 : ℂ) else 0)) := by
    funext n
    rcases (by omega : n = 0 ∨ n = 1 ∨ (n ≠ 0 ∧ n ≠ 1)) with rfl | rfl | ⟨h0, h1⟩
    · simp [discFactor]
    · simp [discFactor]
    · simp [discFactor, h0, h1]
  rw [hfun, hfcDisc_add (le_refl ‖a‖) hDS1 hDS2, hfcDisc_const, hfcDisc_monomial]
  rw [pow_one, neg_smul, sub_eq_add_neg, add_comm]

theorem discConv_discFactor {R : ℝ} (hR : 0 < R) {c : ℕ → ℂ}
    (hc : DiscSummable R c) {lam : ℂ} (hlam : ‖lam‖ ≤ R) (n : ℕ) :
    discConv (discFactor lam) (discTail c lam) n
      = c n - (if n = 0 then scalarEval c lam else 0) := by
  have e : discConv (discFactor lam) (discTail c lam) n
      = ∑ k ∈ Finset.range (n + 1), discFactor lam k * discTail c lam (n - k) :=
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun x y => discFactor lam x * discTail c lam y) n
  rw [e]
  by_cases hn : n = 0
  · subst hn
    rw [Finset.sum_range_one]
    simp only [discFactor, if_pos rfl, Nat.sub_self, if_true]
    rw [scalarEval_eq hR hc hlam]
    ring
  · have h01 : ({0, 1} : Finset ℕ) ⊆ Finset.range (n + 1) := by
      intro k hk
      simp only [Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with rfl | rfl
      · exact Finset.mem_range.mpr (by omega)
      · exact Finset.mem_range.mpr (by omega)
    have hvan : ∀ k ∈ Finset.range (n + 1), k ∉ ({0, 1} : Finset ℕ) →
        discFactor lam k * discTail c lam (n - k) = 0 := by
      intro k _ hk
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
      simp [discFactor, hk.1, hk.2]
    rw [← Finset.sum_subset h01 hvan, Finset.sum_pair (by norm_num : (0 : ℕ) ≠ 1)]
    have e0 : discFactor lam 0 * discTail c lam (n - 0)
        = -lam * discTail c lam n := by simp [discFactor]
    have e1 : discFactor lam 1 * discTail c lam (n - 1)
        = discTail c lam (n - 1) := by simp [discFactor]
    rw [e0, e1, if_neg hn, sub_zero]
    have h := discTail_pred hR hc hlam (n - 1)
    have hn1 : n - 1 + 1 = n := Nat.sub_add_cancel (by omega)
    rw [hn1] at h
    rw [h]; ring

theorem hfcDisc_sub_scalarEval {R : ℝ} (hR : 0 < R) {c : ℕ → ℂ}
    (hc : DiscSummable R c) (haR : ‖a‖ < R) {lam : ℂ} (hlam : ‖lam‖ ≤ R) :
    hfcDisc a c - scalarEval c lam • (1 : A)
      = (a - lam • (1 : A)) * hfcDisc a (discTail c lam) := by
  have hDSa : DiscSummable ‖a‖ c := discSummable_mono (norm_nonneg a) haR.le hc
  have hDSg : DiscSummable ‖a‖ (discTail c lam) :=
    discSummable_discTail hR (norm_nonneg a) haR hc hlam
  have hDSe : DiscSummable ‖a‖ (discFactor lam) := discSummable_discFactor ‖a‖ lam
  have hDSc : DiscSummable ‖a‖
      (fun n => if n = 0 then -scalarEval c lam else (0 : ℂ)) :=
    summable_of_ne_finset_zero (s := {0}) (by
      intro n hn
      have hn0 : n ≠ 0 := by simpa using hn
      simp [hn0])
  have key := hfcDisc_mul (le_refl ‖a‖) hDSe hDSg
  rw [hfcDisc_discFactor] at key
  have hfun : discConv (discFactor lam) (discTail c lam)
      = fun n => c n - (if n = 0 then scalarEval c lam else 0) :=
    funext fun n => discConv_discFactor hR hc hlam n
  have hfun2 : (fun n => c n - (if n = 0 then scalarEval c lam else (0 : ℂ)))
      = (fun n => c n + (if n = 0 then -scalarEval c lam else 0)) := by
    funext n
    by_cases h0 : n = 0 <;> simp [h0, sub_eq_add_neg]
  rw [hfun, hfun2, hfcDisc_add (le_refl ‖a‖) hDSa hDSc, hfcDisc_const] at key
  rw [← key]
  simp [neg_smul, sub_eq_add_neg]

section SpectralInclusion

variable [Nontrivial A]

/-- Forward spectral inclusion for the disc fragment:
a spectral value `lam` of `a` maps to the scalar series
value `scalarEval c lam` in the spectrum of `hfcDisc a c`,
whenever the coefficients are absolutely summable at a
scale `R` strictly larger than `‖a‖`. -/
theorem scalarEval_mem_spectrum {R : ℝ} (hR : 0 < R) {c : ℕ → ℂ}
    (hc : DiscSummable R c) (haR : ‖a‖ < R) {lam : ℂ}
    (hlam : lam ∈ spectrum ℂ a) :
    scalarEval c lam ∈ spectrum ℂ (hfcDisc a c) := by
  have hlamR : ‖lam‖ ≤ R := (spectrum.norm_le_norm_of_mem hlam).trans haR.le
  rw [spectrum.mem_iff] at hlam ⊢
  intro hunit
  apply hlam
  have hfact := hfcDisc_sub_scalarEval hR hc haR hlamR
  have hc1 : Commute (algebraMap ℂ A lam) (hfcDisc a (discTail c lam)) :=
    Algebra.commutes lam _
  have hcomm : Commute (algebraMap ℂ A lam - a) (hfcDisc a (discTail c lam)) :=
    hc1.sub_left (commute_a_hfcDisc _)
  have hunit2 : IsUnit ((algebraMap ℂ A lam - a) * hfcDisc a (discTail c lam)) := by
    have h3 : (algebraMap ℂ A lam - a) * hfcDisc a (discTail c lam)
        = -((a - lam • (1 : A)) * hfcDisc a (discTail c lam)) := by
      rw [Algebra.algebraMap_eq_smul_one,
        show lam • (1 : A) - a = -(a - lam • (1 : A)) from (neg_sub a _).symm,
        neg_mul]
    rw [h3, ← hfact, neg_sub]
    have h2 : algebraMap ℂ A (scalarEval c lam) = scalarEval c lam • (1 : A) :=
      Algebra.algebraMap_eq_smul_one _
    rw [← h2]
    exact hunit
  exact ((hcomm.isUnit_mul_iff).mp hunit2).1

end SpectralInclusion

end

end ThetLogos
