/-
# The Gram clause, Route C: the integrated criterion and the U(1) discharge

Companion brick to `LatticePositivity.lean` (Pitch 4, Stage 1b-B).
Charter: `whitepaper/gram-clause-scoping-2026-10-23.md` (§6, Route C).
Dossier: `whitepaper/pitch-4-stage-1b-b-2026-10-17.md`.

## Honesty ledger

Everything proved in this module is T1 finite-lattice mathematics,
consuming Stage 1b-B's module (`LatticePositivity.lean`) verbatim —
no theorem there is edited or restated; this module only adds. It is
not in the root import list of the library (the corpus pattern for
recent exhibits); it is verified by a targeted build.

* **T0 (anatomy).** The literal hypothesis `hgram` of the proved
  criterion `osForm_nonneg_of_gram` — the Gibbs weight in split
  variables as a *finite pointwise* Gram sum over the strict half —
  is **not satisfiable by the Wilson weight**: at `(G, ρ) =` (U(1),
  defining representation), `N = 2`, any `β ≠ 0`, the weight is not
  even a function of `(restrictPos y, mirrorP u)` — those two maps
  forget the reflection-plane (stratum) links, while the crossing
  (zero) part of the action depends on them. *Status of this half
  of T0: paper proof (finite plaquette-star check at `N = 2`, in
  the brick's verdict memo); it is NOT a theorem of this module.*
  Separately, a finite Gram sum forces
  every section of the kernel into a finite-dimensional span
  (`finite_gram_sections_span`), while the Route C expansion below
  has all Fourier coefficients `> 0` at `β > 0`: the integrated
  kernel's Gram expansion is a *series*, not a finite sum. The
  proved criterion stands; its hypothesis does not hold for the
  Wilson weight. The door that replaces it is T1.

* **T1 (criterion variant, general `(G, ρ)`, any real `β`).**
  `osForm_nonneg_of_gram_integrated`: if the Gibbs weight in split
  variables is a convergent Gram series on the closed halves,
  `exp (-S) = ∑' i, conj (B i u) * A i y`, whose two stratum
  marginals factor through one common strict-half feature `Ξ i`
  with nonnegative real damping factors,
  `∫ A i · f∘restrict = dA i • ∫ Ξ i · f` and
  `∫ B i · f∘mirror = dB i • ∫ Ξ i · f`, `0 ≤ dA i`, `0 ≤ dB i`,
  then the diagonal of the OS form is a nonnegative real:
  `Z⁻¹ • ∑' i, (dA i * dB i) • ‖∫ Ξ i · f‖²`.

* **Route C discharge (`G = U(1)`, defining representation, `β ≥ 0`).**
  `osForm_circle_nonneg`: OS positivity of the U(1) Wilson theory at
  every `β ≥ 0` is T1. The crossing Boltzmann factor of one plaquette
  is expanded in the Fourier–Bessel series
  `exp (β Re w) = ∑' n : ℤ, I n β • w ^ n` (`fourier_exp_circle`),
  with `besselI β n ≥ 0` at `β ≥ 0`; the stratum variables are
  integrated by circle orthogonality
  (`integral_circle_zpow_haarProb`).

Fences (charter §4): fixed finite volume, even `N`; no OS Hilbert
space, no transfer matrix, no limits, no gap. **NO CLAIM** — parts of
any Clay statement closed by this module: 0. Landing label:
"Stage 1b-B positivity T1 for U(1); the clause at general `(G, ρ)`
remains open (Route B)".
-/

import ThetLogos.LatticePositivity
import Mathlib.MeasureTheory.Group.Circle
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.SpecialFunctions.Exponential

namespace ThetLogos

open MeasureTheory Finset
open scoped ComplexConjugate

noncomputable section CircleFacts

/-! ## §A. The corpus circle representation

`circleRep` is the corpus's own defining representation of the
circle (`LatticeGauge.lean`), not a new one: what is added here is
only the three facts the discharge consumes. -/

/-- The matrix of the corpus's defining representation of the circle
is the constant `1 × 1` matrix with entry `z`. -/
theorem repMatrix_circleRep (z : Circle) :
    repMatrix circleRep z = Matrix.of (fun _ _ => (z : ℂ)) :=
  rfl

/-- Its trace is `z` itself. -/
theorem trace_repMatrix_circleRep (z : Circle) :
    Matrix.trace (repMatrix circleRep z) = (z : ℂ) := by
  rw [repMatrix_circleRep]
  simp [Matrix.trace, Matrix.diag]

/-- For the defining representation of the circle, the plaquette
density is `1 - Re (plaquette holonomy)`. -/
theorem plaquetteDensity_circleRep {N : ℕ} (U : Config (Fin 4 → ZMod N) Circle)
    (x : Fin 4 → ZMod N) (μ ν : Fin 4) :
    plaquetteDensity (torusShift N) circleRep U x μ ν
      = 1 - ((plaquette (torusShift N) U x μ ν : Circle) : ℂ).re := by
  unfold plaquetteDensity
  rw [trace_repMatrix_circleRep]
  simp

/-- The coercion of a `zpow` on the circle is the `zpow` of the
coercion. -/
theorem coe_zpow_circle (w : Circle) (e : ℤ) :
    ((w ^ e : Circle) : ℂ) = (w : ℂ) ^ e := by
  rcases Int.eq_nat_or_neg e with ⟨k, rfl | rfl⟩
  · simp [zpow_natCast, Circle.coe_pow]
  · simp [zpow_neg, zpow_natCast, Circle.coe_pow, Circle.coe_inv]

end CircleFacts

noncomputable section Bessel

/-! ## §B. The Fourier–Bessel expansion on the circle

`besselI β n` is the modified Bessel value `I n β`, defined here
directly by its (absolutely convergent) power series so no external
Bessel API is needed:
`I n β = ∑' k, (β/2)^(2k + |n|) / (k! (|n| + k)!)`. -/

/-- One term of the defining series of `besselI`. -/
def besselTerm (β : ℝ) (n : ℤ) (k : ℕ) : ℝ :=
  (β / 2) ^ (2 * k + n.natAbs) / ((Nat.factorial k : ℝ) * (Nat.factorial (n.natAbs + k) : ℝ))

/-- The modified Bessel function `I n β` by its power series. -/
def besselI (β : ℝ) (n : ℤ) : ℝ :=
  ∑' k : ℕ, besselTerm β n k

/-- The defining series of `besselI β n` converges absolutely:
`|term k| ≤ |β/2|^|n| · (β²/4)^k / k!`. -/
theorem summable_besselTerm (β : ℝ) (n : ℤ) : Summable (besselTerm β n) := by
  have hbound : ∀ k : ℕ, ‖besselTerm β n k‖
      ≤ |β / 2| ^ n.natAbs * ((β ^ 2 / 4) ^ k / (Nat.factorial k : ℝ)) := by
    intro k
    have hk : (0 : ℝ) < (Nat.factorial k : ℝ) := by exact_mod_cast Nat.factorial_pos k
    have hnk : (0 : ℝ) < (Nat.factorial (n.natAbs + k) : ℝ) := by
      exact_mod_cast Nat.factorial_pos _
    unfold besselTerm
    rw [Real.norm_eq_abs, abs_div, abs_pow]
    have h1 : |(Nat.factorial k : ℝ) * (Nat.factorial (n.natAbs + k) : ℝ)|
        = (Nat.factorial k : ℝ) * (Nat.factorial (n.natAbs + k) : ℝ) := by
      rw [abs_mul, abs_of_pos hk, abs_of_pos hnk]
    rw [h1]
    have h2 : |β / 2| ^ (2 * k + n.natAbs)
        = (|β / 2| ^ 2) ^ k * |β / 2| ^ n.natAbs := by
      rw [pow_add, pow_mul]
    have h3 : (|β / 2| ^ 2) = β ^ 2 / 4 := by
      rw [sq_abs]; ring
    have hC1 : ((Nat.factorial (n.natAbs + k) : ℝ))⁻¹ ≤ 1 := by
      have h1le : (1 : ℝ) ≤ (Nat.factorial (n.natAbs + k) : ℝ) := by
        exact_mod_cast Nat.factorial_pos _
      exact inv_le_one_of_one_le₀ h1le
    have h5 : |β / 2| ^ (2 * k + n.natAbs) / ((Nat.factorial k : ℝ) * (Nat.factorial (n.natAbs + k) : ℝ))
        = |β / 2| ^ n.natAbs * ((β ^ 2 / 4) ^ k
            * (((Nat.factorial k : ℝ))⁻¹ * ((Nat.factorial (n.natAbs + k) : ℝ))⁻¹)) := by
      rw [h2, h3, div_eq_mul_inv, mul_inv]; ring
    rw [h5]
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg (abs_nonneg _) _)
    rw [div_eq_mul_inv]
    apply mul_le_mul_of_nonneg_left _
      (pow_nonneg (by positivity : (0 : ℝ) ≤ β ^ 2 / 4) _)
    calc ((Nat.factorial k : ℝ))⁻¹ * ((Nat.factorial (n.natAbs + k) : ℝ))⁻¹
        ≤ ((Nat.factorial k : ℝ))⁻¹ * 1 :=
        mul_le_mul_of_nonneg_left hC1 (inv_nonneg.mpr hk.le)
      _ = ((Nat.factorial k : ℝ))⁻¹ := mul_one _
  refine Summable.of_norm_bounded
    ((Real.summable_pow_div_factorial _).mul_left _) hbound

/-- At `β ≥ 0` every Bessel coefficient is nonnegative (termwise). -/
theorem besselI_nonneg {β : ℝ} (hβ : 0 ≤ β) (n : ℤ) : 0 ≤ besselI β n := by
  apply tsum_nonneg
  intro k
  unfold besselTerm
  apply div_nonneg (pow_nonneg (div_nonneg hβ (by norm_num)) _)
  positivity

end Bessel

noncomputable section Fourier

/-- The reindexing bijection `(k, j) ↦ (k - j, min k j)` collecting
the Cauchy product of two exponential series into Fourier modes;
its inverse is `(n, m) ↦ (m + n⁺, m + n⁻)`. -/
def natPairEquivIntNat : ℕ × ℕ ≃ ℤ × ℕ where
  toFun p := ((p.1 : ℤ) - (p.2 : ℤ), min p.1 p.2)
  invFun q := (q.2 + q.1.toNat, q.2 + (-q.1).toNat)
  left_inv p := by
    obtain ⟨k, j⟩ := p
    simp only [Prod.mk.injEq]
    constructor <;> omega
  right_inv q := by
    obtain ⟨n, m⟩ := q
    simp only [Prod.mk.injEq, Nat.cast_add]
    constructor <;> omega

theorem natPairEquivIntNat_symm_apply (q : ℤ × ℕ) :
    natPairEquivIntNat.symm q = (q.2 + q.1.toNat, q.2 + (-q.1).toNat) :=
  rfl

/-- The exponential series with a unit-modulus direction: the
series `∑' k, c^k / k! • z^k` sums to `exp (c * z)`. -/
theorem hasSum_exp_series (c z : ℂ) (hz : ‖z‖ = 1) :
    HasSum (fun k : ℕ => (c ^ k / (Nat.factorial k : ℂ)) * z ^ k)
      (Complex.exp (c * z)) := by
  have hsumm : Summable (fun k : ℕ => (c ^ k / (Nat.factorial k : ℂ)) * z ^ k) := by
    refine Summable.of_norm_bounded (Real.summable_pow_div_factorial ‖c‖)
      (fun k => ?_)
    rw [norm_mul, norm_div, norm_pow, norm_pow, hz, one_pow, mul_one,
      norm_natCast]
  have htsum : (∑' k : ℕ, (c ^ k / (Nat.factorial k : ℂ)) * z ^ k)
      = Complex.exp (c * z) := by
    have h1 : ∀ k : ℕ, (c ^ k / (Nat.factorial k : ℂ)) * z ^ k
        = ((Nat.factorial k : ℂ))⁻¹ • (c * z) ^ k := by
      intro k
      rw [smul_eq_mul, mul_pow, div_eq_mul_inv]
      ring
    rw [tsum_congr h1]
    have h2 : NormedSpace.exp (c * z)
        = ∑' k : ℕ, ((Nat.factorial k : ℂ))⁻¹ • (c * z) ^ k :=
      congrFun (NormedSpace.exp_eq_tsum ℂ) (c * z)
    have h3 : Complex.exp (c * z) = NormedSpace.exp (c * z) :=
      congrFun Complex.exp_eq_exp_ℂ (c * z)
    rw [← h2, ← h3]
  have hh := hsumm.hasSum
  rwa [htsum] at hh

/-- **The Fourier–Bessel expansion on the circle** (HasSum form):
for every real `β` and every `w : Circle`,
`exp (β • Re w) = ∑' n : ℤ, I n β • w ^ n`, absolutely. -/
theorem hasSum_fourier_exp_circle (β : ℝ) (w : Circle) :
    HasSum (fun n : ℤ => (besselI β n : ℂ) * (w : ℂ) ^ n)
      ((Real.exp (β * (w : ℂ).re) : ℝ) : ℂ) := by
  have hw0 : (w : ℂ) ≠ 0 := by
    intro h
    have h1 := Circle.norm_coe w
    rw [h, norm_zero] at h1
    exact zero_ne_one h1
  have hA := hasSum_exp_series ((β / 2 : ℝ) : ℂ) (w : ℂ) (Circle.norm_coe w)
  have hB := hasSum_exp_series ((β / 2 : ℝ) : ℂ) ((w : ℂ)⁻¹) (by
    rw [norm_inv, Circle.norm_coe, inv_one])
  have hnorm : ∀ z : ℂ, ‖z‖ = 1 →
      Summable (fun k : ℕ => ‖(((β / 2 : ℝ) : ℂ) ^ k
        / (Nat.factorial k : ℂ)) * z ^ k‖) := by
    intro z hz
    have heq : (fun k : ℕ => ‖(((β / 2 : ℝ) : ℂ) ^ k
          / (Nat.factorial k : ℂ)) * z ^ k‖)
        = (fun k => ‖((β / 2 : ℝ) : ℂ)‖ ^ k / (Nat.factorial k : ℝ)) := by
      funext k
      rw [norm_mul, norm_div, norm_pow, norm_pow, hz, one_pow, mul_one,
        norm_natCast]
    rw [heq]
    exact Real.summable_pow_div_factorial _
  have hAn := hnorm _ (Circle.norm_coe w)
  have hBn := hnorm ((w : ℂ)⁻¹) (by rw [norm_inv, Circle.norm_coe, inv_one])
  have hsF := summable_mul_of_summable_norm hAn hBn
  have htsumF : (∑' p : ℕ × ℕ,
        ((((β / 2 : ℝ) : ℂ) ^ p.1 / (Nat.factorial p.1 : ℂ)) * (w : ℂ) ^ p.1)
        * ((((β / 2 : ℝ) : ℂ) ^ p.2 / (Nat.factorial p.2 : ℂ))
          * ((w : ℂ)⁻¹) ^ p.2))
      = Complex.exp (((β / 2 : ℝ) : ℂ) * (w : ℂ))
        * Complex.exp (((β / 2 : ℝ) : ℂ) * (w : ℂ)⁻¹) := by
    rw [← tsum_mul_tsum_of_summable_norm hAn hBn, hA.tsum_eq, hB.tsum_eq]
  have htransp : Summable (fun q : ℤ × ℕ => (fun p : ℕ × ℕ =>
        ((((β / 2 : ℝ) : ℂ) ^ p.1 / (Nat.factorial p.1 : ℂ)) * (w : ℂ) ^ p.1)
        * ((((β / 2 : ℝ) : ℂ) ^ p.2 / (Nat.factorial p.2 : ℂ))
          * ((w : ℂ)⁻¹) ^ p.2)) (natPairEquivIntNat.symm q)) :=
    (natPairEquivIntNat.symm.summable_iff).mpr hsF
  have htsumT : (∑' q : ℤ × ℕ, (fun p : ℕ × ℕ =>
        ((((β / 2 : ℝ) : ℂ) ^ p.1 / (Nat.factorial p.1 : ℂ)) * (w : ℂ) ^ p.1)
        * ((((β / 2 : ℝ) : ℂ) ^ p.2 / (Nat.factorial p.2 : ℂ))
          * ((w : ℂ)⁻¹) ^ p.2)) (natPairEquivIntNat.symm q))
      = Complex.exp (((β / 2 : ℝ) : ℂ) * (w : ℂ))
        * Complex.exp (((β / 2 : ℝ) : ℂ) * (w : ℂ)⁻¹) :=
    (natPairEquivIntNat.symm.tsum_eq _).trans htsumF
  have hterm : ∀ q : ℤ × ℕ,
      (fun p : ℕ × ℕ => ((((β / 2 : ℝ) : ℂ) ^ p.1
          / (Nat.factorial p.1 : ℂ)) * (w : ℂ) ^ p.1)
        * ((((β / 2 : ℝ) : ℂ) ^ p.2
          / (Nat.factorial p.2 : ℂ)) * ((w : ℂ)⁻¹) ^ p.2))
        (natPairEquivIntNat.symm q)
      = (besselTerm β q.1 q.2 : ℂ) * (w : ℂ) ^ q.1 := by
    intro q
    obtain ⟨n, m⟩ := q
    rw [natPairEquivIntNat_symm_apply]
    have hab1 : (m + n.toNat) + (m + (-n).toNat) = 2 * m + n.natAbs := by
      omega
    have hab2 : (((m + n.toNat : ℕ) : ℤ)) - (((m + (-n).toNat : ℕ) : ℤ)) = n := by
      push_cast
      omega
    have hfac2 : Nat.factorial (m + n.toNat) * Nat.factorial (m + (-n).toNat)
        = Nat.factorial m * Nat.factorial (n.natAbs + m) := by
      by_cases hn : 0 ≤ n
      · have e1 : n.toNat = n.natAbs := by omega
        have e2 : (-n).toNat = 0 := Int.toNat_of_nonpos (neg_nonpos.mpr hn)
        rw [e1, e2, add_zero,
          mul_comm (Nat.factorial (m + n.natAbs)) (Nat.factorial m),
          Nat.add_comm m n.natAbs]
      · have hn' : n < 0 := lt_of_not_ge hn
        have e1 : n.toNat = 0 := Int.toNat_of_nonpos hn'.le
        have e2 : (-n).toNat = n.natAbs := by omega
        rw [e1, e2, add_zero, Nat.add_comm m n.natAbs]
    have hscal : ((((β / 2 : ℝ) : ℂ) ^ (m + n.toNat)
          / (Nat.factorial (m + n.toNat) : ℂ))
        * (((β / 2 : ℝ) : ℂ) ^ (m + (-n).toNat)
          / (Nat.factorial (m + (-n).toNat) : ℂ)))
        = (besselTerm β n m : ℂ) := by
      have hcast : ((besselTerm β n m : ℝ) : ℂ)
          = ((β / 2 : ℝ) : ℂ) ^ (2 * m + n.natAbs)
            / ((Nat.factorial m : ℂ) * (Nat.factorial (n.natAbs + m) : ℂ)) := by
        rw [besselTerm]
        push_cast
        ring
      rw [hcast, div_mul_div_comm, ← pow_add, hab1]
      congr 1
      exact_mod_cast hfac2
    have hpow : (w : ℂ) ^ (m + n.toNat) * ((w : ℂ)⁻¹) ^ (m + (-n).toNat)
        = (w : ℂ) ^ n := by
      have hexp : (((m + n.toNat : ℕ) : ℤ))
          + (-(((m + (-n).toNat : ℕ) : ℤ))) = n := by
        rw [← sub_eq_add_neg]
        exact hab2
      rw [inv_pow, ← zpow_natCast ((w : ℂ)) (m + n.toNat),
        ← zpow_natCast ((w : ℂ)) (m + (-n).toNat), ← zpow_neg,
        ← zpow_add₀ hw0, hexp]
    calc ((((β / 2 : ℝ) : ℂ) ^ (m + n.toNat)
            / (Nat.factorial (m + n.toNat) : ℂ)) * (w : ℂ) ^ (m + n.toNat))
          * ((((β / 2 : ℝ) : ℂ) ^ (m + (-n).toNat)
            / (Nat.factorial (m + (-n).toNat) : ℂ))
            * ((w : ℂ)⁻¹) ^ (m + (-n).toNat))
        = (((((β / 2 : ℝ) : ℂ) ^ (m + n.toNat)
            / (Nat.factorial (m + n.toNat) : ℂ))
          * (((β / 2 : ℝ) : ℂ) ^ (m + (-n).toNat)
            / (Nat.factorial (m + (-n).toNat) : ℂ)))
          * ((w : ℂ) ^ (m + n.toNat) * ((w : ℂ)⁻¹) ^ (m + (-n).toNat))) := by
          ring
      _ = (besselTerm β n m : ℂ) * (w : ℂ) ^ n := by rw [hscal, hpow]
  have hsF' : Summable (fun q : ℤ × ℕ => (besselTerm β q.1 q.2 : ℂ)
      * (w : ℂ) ^ q.1) := by
    have hfeq := funext hterm
    rw [← hfeq]
    exact htransp
  have htsumF' : (∑' q : ℤ × ℕ, (besselTerm β q.1 q.2 : ℂ) * (w : ℂ) ^ q.1)
      = Complex.exp (((β / 2 : ℝ) : ℂ) * (w : ℂ))
        * Complex.exp (((β / 2 : ℝ) : ℂ) * (w : ℂ)⁻¹) := by
    rw [← htsumT]
    exact tsum_congr (fun q => (hterm q).symm)
  have hF : HasSum (fun q : ℤ × ℕ => (besselTerm β q.1 q.2 : ℂ)
        * (w : ℂ) ^ q.1)
      (Complex.exp (((β / 2 : ℝ) : ℂ) * (w : ℂ))
        * Complex.exp (((β / 2 : ℝ) : ℂ) * (w : ℂ)⁻¹)) := by
    have hh := hsF'.hasSum
    rwa [htsumF'] at hh
  have hfiber : ∀ n : ℤ, HasSum (fun m : ℕ => (besselTerm β n m : ℂ)
        * (w : ℂ) ^ n) ((besselI β n : ℂ) * (w : ℂ) ^ n) := by
    intro n
    have hs : Summable (fun m : ℕ => (besselTerm β n m : ℂ)) :=
      (RCLike.summable_ofReal ℂ).mpr (summable_besselTerm β n)
    have h1 : HasSum (fun m : ℕ => (besselTerm β n m : ℂ))
        (besselI β n : ℂ) := by
      have h2 := hs.hasSum
      have h3 : (∑' m : ℕ, (besselTerm β n m : ℂ)) = (besselI β n : ℂ) := by
        unfold besselI
        exact (RCLike.ofReal_tsum ℂ _).symm
      rwa [h3] at h2
    exact h1.mul_right _
  have hG := hF.prod_fiberwise hfiber
  have hval : Complex.exp (((β / 2 : ℝ) : ℂ) * (w : ℂ))
        * Complex.exp (((β / 2 : ℝ) : ℂ) * (w : ℂ)⁻¹)
      = ((Real.exp (β * (w : ℂ).re) : ℝ) : ℂ) := by
    rw [← Complex.exp_add, Complex.ofReal_exp]
    congr 1
    have hre : ((w : ℂ) + (w : ℂ)⁻¹) / 2 = (((w : ℂ).re : ℝ) : ℂ) := by
      have h := Complex.add_conj (w : ℂ)
      rw [← Circle.coe_inv_eq_conj] at h
      push_cast at h
      linear_combination h / 2
    rw [Complex.ofReal_mul, ← hre]
    push_cast
    ring
  rwa [hval] at hG

/-- The Fourier–Bessel expansion, `tsum` form. -/
theorem fourier_exp_circle (β : ℝ) (w : Circle) :
    ((Real.exp (β * (w : ℂ).re) : ℝ) : ℂ)
      = ∑' n : ℤ, (besselI β n : ℂ) * (w : ℂ) ^ n :=
  (hasSum_fourier_exp_circle β w).tsum_eq.symm

/-- The Bessel coefficients are summable over `ℤ` at every real
`β` (absolute convergence of the Fourier expansion at `w = 1`). -/
theorem summable_besselI_int (β : ℝ) : Summable (besselI β) := by
  have h := (hasSum_fourier_exp_circle β 1).summable
  simp only [Circle.coe_one, one_zpow, mul_one] at h
  exact (RCLike.summable_ofReal ℂ).mp h

/-- `∑' n : ℤ, I n β = exp β` (the generating identity at `w = 1`). -/
theorem tsum_besselI_int (β : ℝ) : ∑' n : ℤ, besselI β n = Real.exp β := by
  have h := fourier_exp_circle β 1
  simp only [Circle.coe_one, Complex.one_re, mul_one, one_zpow] at h
  have key : ((∑' n : ℤ, besselI β n : ℝ) : ℂ) = ((Real.exp β : ℝ) : ℂ) :=
    (RCLike.ofReal_tsum ℂ _).trans h.symm
  exact Complex.ofReal_injective key

end Fourier

noncomputable section GramIntegrated

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ))
  {N : ℕ} [NeZero N]

/-- **T1: the integrated Gram criterion.** Same ambient and same
conclusion as `osForm_nonneg_of_gram`, but the hypothesis is the
*stratum-integrated* one: the Gibbs weight in split variables is a
convergent Gram series on the closed halves,
`exp (-S (unsplit (y, u))) = ∑' i, conj (B i u) * A i y`, with
domination `‖A i y‖ ≤ CA i`, `‖B i u‖ ≤ CB i`,
`Summable (fun i => CA i * CB i)`, whose two stratum marginals
factor through a common strict-half feature `Ξ i` with nonnegative
real damping factors:
`∫ A i · f∘restrict = (dA i) • ∫ Ξ i · f` and
`∫ B i · f∘mirror = (dB i) • ∫ Ξ i · f`.
Then the OS diagonal is the nonnegative real
`Z⁻¹ • ∑' i, (dA i * dB i) • ‖∫ Ξ i · f‖²`. Sign-free in `β`, like
the finite criterion it succeeds. (No measurability hypothesis on
`Ξ` is needed: everything about `Ξ` enters through the two marginal
identities.) -/
theorem osForm_nonneg_of_gram_integrated
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hN : Even N)
    (hd : 0 < d) (β : ℝ)
    (F : Config (Fin 4 → ZMod N) G → ℂ)
    (f : (↥(posLinks (N := N)) → G) → ℂ)
    (hF : ∀ U, F U = f (fun ℓ : ↥(posLinks (N := N)) => U ℓ.1))
    (hfA : AEStronglyMeasurable f
      (Measure.pi fun _ : ↥(posLinks (N := N)) => μG))
    (Cf : ℝ) (hfB : ∀ z, ‖f z‖ ≤ Cf)
    {ι : Type*} [Countable ι]
    (A : ι → (↥(halfLinks (N := N)) → G) → ℂ)
    (B : ι → (↥(negLinks (N := N)) → G) → ℂ)
    (Ξ : ι → (↥(posLinks (N := N)) → G) → ℂ)
    (hAA : ∀ i, AEStronglyMeasurable (A i)
      (Measure.pi fun _ : ↥(halfLinks (N := N)) => μG))
    (hBA : ∀ i, AEStronglyMeasurable (B i)
      (Measure.pi fun _ : ↥(negLinks (N := N)) => μG))
    (CA CB : ι → ℝ) (hCA : ∀ i, 0 ≤ CA i)
    (hAB : ∀ i y, ‖A i y‖ ≤ CA i)
    (hBB : ∀ i u, ‖B i u‖ ≤ CB i)
    (hsum : Summable fun i => CA i * CB i)
    (dA dB : ι → ℝ) (hdA : ∀ i, 0 ≤ dA i) (hdB : ∀ i, 0 ≤ dB i)
    (hgram : ∀ (y : ↥(halfLinks (N := N)) → G)
        (u : ↥(negLinks (N := N)) → G),
      (Real.exp (- wilsonAction (torusShift N) ρ β
        ((splitEquiv (halfLinks (N := N))).symm (y, u))) : ℂ)
      = ∑' i, (starRingEnd ℂ) (B i u) * A i y)
    (hmargA : ∀ i, ∫ y, A i y * f (restrictPos y)
          ∂(Measure.pi fun _ : ↥(halfLinks (N := N)) => μG)
        = (dA i : ℂ) * ∫ z, Ξ i z * f z
          ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG))
    (hmargB : ∀ i, ∫ u, B i u * f (mirrorP hN u)
          ∂(Measure.pi fun _ : ↥(negLinks (N := N)) => μG)
        = (dB i : ℂ) * ∫ z, Ξ i z * f z
          ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG)) :
    0 ≤ (osForm μG ρ β F F).re ∧ (osForm μG ρ β F F).im = 0 := by
  classical
  have hCf : 0 ≤ Cf := (norm_nonneg _).trans (hfB (fun _ => 1))
  have hbd : ∀ (i : ι) (p : (↥(halfLinks (N := N)) → G)
        × (↥(negLinks (N := N)) → G)),
      ‖(A i p.1 * f (restrictPos p.1))
        * (starRingEnd ℂ) (B i p.2 * f (mirrorP hN p.2))‖
      ≤ Cf ^ 2 * (CA i * CB i) := by
    intro i p
    rw [norm_mul, starRingEnd_apply, norm_star, norm_mul, norm_mul]
    refine (mul_le_mul
      (mul_le_mul (hAB i p.1) (hfB _) (norm_nonneg _)
        ((norm_nonneg _).trans (hAB i p.1)))
      (mul_le_mul (hBB i p.2) (hfB _) (norm_nonneg _)
        ((norm_nonneg _).trans (hBB i p.2)))
      (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (mul_nonneg (hCA i) hCf)).trans_eq (by ring)
  have hIntA : ∀ i, Integrable (fun y => A i y * f (restrictPos y))
      (Measure.pi fun _ : ↥(halfLinks (N := N)) => μG) := by
    intro i
    refine Integrable.of_bound
      ((hAA i).mul (hfA.comp_measurePreserving
        (measurePreserving_restrictPos μG)))
      (CA i * Cf) (ae_of_all _ fun y => ?_)
    rw [norm_mul]
    exact mul_le_mul (hAB i y) (hfB _) (norm_nonneg _)
      ((norm_nonneg _).trans (hAB i y))
  have hIntB : ∀ i, Integrable
      (fun u => (starRingEnd ℂ) (B i u * f (mirrorP hN u)))
      (Measure.pi fun _ : ↥(negLinks (N := N)) => μG) := by
    intro i
    refine Integrable.of_bound
      ((RCLike.continuous_conj).comp_aestronglyMeasurable
        ((hBA i).mul (hfA.comp_measurePreserving
          (measurePreserving_mirrorP μG hN))))
      (CB i * Cf) (ae_of_all _ fun u => ?_)
    rw [starRingEnd_apply, norm_star, norm_mul]
    exact mul_le_mul (hBB i u) (hfB _) (norm_nonneg _)
      ((norm_nonneg _).trans (hBB i u))
  have hInt : ∀ i, Integrable
      (fun p : (↥(halfLinks (N := N)) → G) × (↥(negLinks (N := N)) → G) =>
        (A i p.1 * f (restrictPos p.1))
          * (starRingEnd ℂ) (B i p.2 * f (mirrorP hN p.2)))
      ((Measure.pi fun _ : ↥(halfLinks (N := N)) => μG).prod
        (Measure.pi fun _ : ↥(negLinks (N := N)) => μG)) :=
    fun i => (hIntA i).mul_prod (hIntB i)
  have hsumInt : Summable fun i => ∫ p, ‖(A i p.1 * f (restrictPos p.1))
        * (starRingEnd ℂ) (B i p.2 * f (mirrorP hN p.2))‖
      ∂((Measure.pi fun _ : ↥(halfLinks (N := N)) => μG).prod
        (Measure.pi fun _ : ↥(negLinks (N := N)) => μG)) := by
    refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_)
      (hsum.mul_left (Cf ^ 2))
    · exact integral_nonneg_of_ae (ae_of_all _ fun p => norm_nonneg _)
    · refine (integral_mono (hInt i).norm (integrable_const _)
        (fun p => hbd i p)).trans_eq ?_
      rw [integral_const, Measure.real, measure_univ, ENNReal.toReal_one,
        one_smul]
  have hswap : (∑' i, ∫ p, (A i p.1 * f (restrictPos p.1))
        * (starRingEnd ℂ) (B i p.2 * f (mirrorP hN p.2))
      ∂((Measure.pi fun _ : ↥(halfLinks (N := N)) => μG).prod
        (Measure.pi fun _ : ↥(negLinks (N := N)) => μG)))
      = ∫ p, ∑' i, (A i p.1 * f (restrictPos p.1))
        * (starRingEnd ℂ) (B i p.2 * f (mirrorP hN p.2))
      ∂((Measure.pi fun _ : ↥(halfLinks (N := N)) => μG).prod
        (Measure.pi fun _ : ↥(negLinks (N := N)) => μG)) :=
    (hasSum_integral_of_summable_integral_norm hInt hsumInt).tsum_eq
  have hpt : ∀ p : (↥(halfLinks (N := N)) → G)
        × (↥(negLinks (N := N)) → G),
      (∑' i, (A i p.1 * f (restrictPos p.1))
        * (starRingEnd ℂ) (B i p.2 * f (mirrorP hN p.2)))
      = (Real.exp (- wilsonAction (torusShift N) ρ β
          ((splitEquiv (halfLinks (N := N))).symm p)) : ℂ)
        * ((starRingEnd ℂ) (f (mirrorP hN p.2)) * f (restrictPos p.1)) := by
    intro p
    show (∑' i, (A i p.1 * f (restrictPos p.1))
        * (starRingEnd ℂ) (B i p.2 * f (mirrorP hN p.2)))
      = (Real.exp (- wilsonAction (torusShift N) ρ β
          ((splitEquiv (halfLinks (N := N))).symm (p.1, p.2))) : ℂ)
        * ((starRingEnd ℂ) (f (mirrorP hN p.2)) * f (restrictPos p.1))
    have hreg : ∀ i, (A i p.1 * f (restrictPos p.1))
          * (starRingEnd ℂ) (B i p.2 * f (mirrorP hN p.2))
        = ((starRingEnd ℂ) (B i p.2) * A i p.1)
          * ((starRingEnd ℂ) (f (mirrorP hN p.2)) * f (restrictPos p.1)) := by
      intro i
      rw [map_mul]; ring
    rw [tsum_congr hreg, tsum_mul_right, hgram p.1 p.2]
  have hi : ∀ i, ∫ p, (A i p.1 * f (restrictPos p.1))
        * (starRingEnd ℂ) (B i p.2 * f (mirrorP hN p.2))
      ∂((Measure.pi fun _ : ↥(halfLinks (N := N)) => μG).prod
        (Measure.pi fun _ : ↥(negLinks (N := N)) => μG))
      = ((dA i * dB i : ℝ) : ℂ)
        * ((∫ z, Ξ i z * f z
            ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG))
          * (starRingEnd ℂ) (∫ z, Ξ i z * f z
            ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG))) := by
    intro i
    calc ∫ p, (A i p.1 * f (restrictPos p.1))
            * (starRingEnd ℂ) (B i p.2 * f (mirrorP hN p.2))
          ∂((Measure.pi fun _ : ↥(halfLinks (N := N)) => μG).prod
            (Measure.pi fun _ : ↥(negLinks (N := N)) => μG))
        = (∫ y, A i y * f (restrictPos y)
            ∂(Measure.pi fun _ : ↥(halfLinks (N := N)) => μG))
          * (∫ u, (starRingEnd ℂ) (B i u * f (mirrorP hN u))
            ∂(Measure.pi fun _ : ↥(negLinks (N := N)) => μG)) :=
          integral_prod_mul (fun y => A i y * f (restrictPos y))
            (fun u => (starRingEnd ℂ) (B i u * f (mirrorP hN u)))
      _ = ((dA i : ℂ) * ∫ z, Ξ i z * f z
            ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG))
          * (starRingEnd ℂ) ((dB i : ℂ) * ∫ z, Ξ i z * f z
            ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG)) := by
          rw [hmargA i]
          congr 1
          rw [integral_conj, hmargB i]
      _ = ((dA i * dB i : ℝ) : ℂ)
          * ((∫ z, Ξ i z * f z
              ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG))
            * (starRingEnd ℂ) (∫ z, Ξ i z * f z
              ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG))) := by
          rw [map_mul, Complex.conj_ofReal, Complex.ofReal_mul]; ring
  have hZ : 0 < gibbsPartition (torusShift N) μG ρ β :=
    gibbsPartition_pos (torusShift N) μG ρ hρcont hd β
  have hmain : osForm μG ρ β F F
      = ((gibbsPartition (torusShift N) μG ρ β : ℂ))⁻¹
        * ((∑' i, (dA i * dB i) * ‖∫ z, Ξ i z * f z
            ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG)‖ ^ 2 : ℝ) : ℂ) := by
    rw [osForm_eq_kernel μG ρ hρcont hN hd β F f hF]
    congr 1
    calc ∫ p, (Real.exp (- wilsonAction (torusShift N) ρ β
              ((splitEquiv (halfLinks (N := N))).symm p)) : ℂ)
            * ((starRingEnd ℂ) (f (mirrorP hN p.2)) * f (restrictPos p.1))
          ∂((Measure.pi fun _ : ↥(halfLinks (N := N)) => μG).prod
            (Measure.pi fun _ : ↥(negLinks (N := N)) => μG))
        = ∫ p, ∑' i, (A i p.1 * f (restrictPos p.1))
            * (starRingEnd ℂ) (B i p.2 * f (mirrorP hN p.2))
          ∂((Measure.pi fun _ : ↥(halfLinks (N := N)) => μG).prod
            (Measure.pi fun _ : ↥(negLinks (N := N)) => μG)) :=
          integral_congr_ae (ae_of_all _ fun p => (hpt p).symm)
      _ = ∑' i, ∫ p, (A i p.1 * f (restrictPos p.1))
            * (starRingEnd ℂ) (B i p.2 * f (mirrorP hN p.2))
          ∂((Measure.pi fun _ : ↥(halfLinks (N := N)) => μG).prod
            (Measure.pi fun _ : ↥(negLinks (N := N)) => μG)) := hswap.symm
      _ = ∑' i, ((dA i * dB i : ℝ) : ℂ)
            * ((∫ z, Ξ i z * f z
                ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG))
              * (starRingEnd ℂ) (∫ z, Ξ i z * f z
                ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG))) :=
          tsum_congr hi
      _ = ((∑' i, (dA i * dB i) * ‖∫ z, Ξ i z * f z
            ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG)‖ ^ 2 : ℝ) : ℂ) := by
          apply Eq.trans _ (RCLike.ofReal_tsum ℂ _).symm
          apply tsum_congr
          intro i
          have h2 : (∫ z, Ξ i z * f z
                ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG))
              * (starRingEnd ℂ) (∫ z, Ξ i z * f z
                ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG))
            = ((‖∫ z, Ξ i z * f z
                ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG)‖ ^ 2 : ℝ) : ℂ) :=
            (Complex.mul_conj' _).trans (Complex.ofReal_pow _ _).symm
          rw [h2]
          exact (Complex.ofReal_mul _ _).symm
  rw [hmain, ← Complex.ofReal_inv, ← Complex.ofReal_mul]
  constructor
  · rw [Complex.ofReal_re]
    exact mul_nonneg (inv_nonneg.mpr hZ.le)
      (tsum_nonneg fun i => mul_nonneg (mul_nonneg (hdA i) (hdB i))
        (pow_nonneg (norm_nonneg _) _))
  · rw [Complex.ofReal_im]

end GramIntegrated

section ZpowProducts

/-- Powers distribute over finite products in a commutative group. -/
theorem prod_zpow {α : Type*} {M : Type*} [CommGroup M] (s : Finset α)
    (f : α → M) (n : ℤ) :
    (∏ a ∈ s, f a) ^ n = ∏ a ∈ s, (f a) ^ n := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha,
      mul_zpow, ih]

/-- An integer power of a sum of exponents is the product of powers. -/
theorem zpow_sum_prod {α : Type*} {M : Type*} [CommGroup M] (s : Finset α)
    (a : M) (e : α → ℤ) :
    a ^ (∑ x ∈ s, e x) = ∏ x ∈ s, a ^ (e x) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert x s hx ih => rw [Finset.sum_insert hx, zpow_add, ih,
      Finset.prod_insert hx]

end ZpowProducts

section CircleOrthogonality

/-- Fourier orthogonality on the circle for the Haar probability:
the integral of the `e`-th character is `1` if `e = 0` and `0`
otherwise. Proved by rotation invariance. -/
theorem integral_circle_zpow_haarProb (e : ℤ) :
    ∫ w : Circle, ((w ^ e : Circle) : ℂ) ∂(haarProb Circle)
      = if e = 0 then 1 else 0 := by
  by_cases he : e = 0
  · simp only [he, zpow_zero, Circle.coe_one, if_true]
    rw [integral_const, Measure.real, measure_univ, ENNReal.toReal_one,
      one_smul]
  · rw [if_neg he]
    obtain ⟨ζ, hζ⟩ : ∃ ζ : Circle, ((ζ ^ e : Circle) : ℂ) = -1 := by
      refine ⟨Circle.exp (Real.pi / (e.natAbs : ℝ)), ?_⟩
      rw [coe_zpow_circle, Circle.coe_exp, ← Complex.exp_int_mul]
      by_cases hpos : 0 ≤ e
      · have hne : (e : ℝ) ≠ 0 := by
          have h0 : 0 < e := lt_of_le_of_ne hpos (Ne.symm he)
          positivity
        have hcast : ((e.natAbs : ℝ)) = (e : ℝ) := by
          rw [← Int.cast_natCast, Int.natAbs_of_nonneg hpos]
        have h1 : (e : ℝ) * (Real.pi / (e.natAbs : ℝ)) = Real.pi := by
          rw [hcast]
          field_simp
        have harg : (e : ℂ) * (((Real.pi / (e.natAbs : ℝ) : ℝ)) : ℂ)
            = (Real.pi : ℂ) := by
          have h1c : ((e * (Real.pi / (e.natAbs : ℝ)) : ℝ) : ℂ)
              = (Real.pi : ℂ) := by exact_mod_cast h1
          rw [← h1c, Complex.ofReal_mul, Complex.ofReal_intCast]
        rw [← mul_assoc, harg]
        exact Complex.exp_pi_mul_I
      · have hne : (e : ℝ) ≠ 0 := by
          have h0 : e < 0 := lt_of_not_ge hpos
          positivity
        have h2 : ((e.natAbs : ℤ)) = -e := by
          rw [← Int.natAbs_neg e]
          exact Int.natAbs_of_nonneg (show 0 ≤ -e by omega)
        have hcast : ((e.natAbs : ℝ)) = -(e : ℝ) := by
          rw [← Int.cast_natCast, h2]
          push_cast
          ring
        have h1 : (e : ℝ) * (Real.pi / (e.natAbs : ℝ)) = -Real.pi := by
          rw [hcast]
          field_simp
        have harg : (e : ℂ) * (((Real.pi / (e.natAbs : ℝ) : ℝ)) : ℂ)
            = ((-Real.pi : ℝ) : ℂ) := by
          have h1c : ((e * (Real.pi / (e.natAbs : ℝ)) : ℝ) : ℂ)
              = ((-Real.pi : ℝ) : ℂ) := by exact_mod_cast h1
          rw [← h1c, Complex.ofReal_mul, Complex.ofReal_intCast]
        rw [← mul_assoc, harg]
        rw [show (((-Real.pi : ℝ) : ℂ)) * Complex.I
          = -(Real.pi * Complex.I) by push_cast; ring,
          Complex.exp_neg, Complex.exp_pi_mul_I]
        simp
    have hcont : Continuous fun w : Circle => ((w ^ e : Circle) : ℂ) :=
      continuous_subtype_val.comp (continuous_id.zpow e)
    have hrot : (∫ w : Circle, ((w ^ e : Circle) : ℂ) ∂(haarProb Circle))
        = - ∫ w : Circle, ((w ^ e : Circle) : ℂ) ∂(haarProb Circle) := by
      have hmeas : MeasurePreserving (fun w : Circle => ζ * w)
          (haarProb Circle) (haarProb Circle) :=
        measurePreserving_mul_left _ ζ
      have h1 : (∫ w : Circle, ((w ^ e : Circle) : ℂ) ∂(haarProb Circle))
          = ∫ w : Circle, (((ζ * w) ^ e : Circle) : ℂ)
            ∂(haarProb Circle) := by
        conv_lhs => rw [← hmeas.map_eq]
        rw [integral_map hmeas.measurable.aemeasurable
          hcont.aestronglyMeasurable]
      have h2 : ∀ w : Circle, (((ζ * w) ^ e : Circle) : ℂ)
          = - ((w ^ e : Circle) : ℂ) := by
        intro w
        rw [mul_zpow, Circle.coe_mul, hζ, neg_one_mul]
      calc (∫ w : Circle, ((w ^ e : Circle) : ℂ) ∂(haarProb Circle))
          = ∫ w : Circle, (((ζ * w) ^ e : Circle) : ℂ)
              ∂(haarProb Circle) := h1
        _ = ∫ w : Circle, -((w ^ e : Circle) : ℂ) ∂(haarProb Circle) :=
            integral_congr_ae (ae_of_all _ h2)
        _ = - ∫ w : Circle, ((w ^ e : Circle) : ℂ) ∂(haarProb Circle) :=
            integral_neg _
    have h2I : (2 : ℂ) * (∫ w : Circle, ((w ^ e : Circle) : ℂ)
        ∂(haarProb Circle)) = 0 := by linear_combination hrot
    exact (mul_eq_zero.mp h2I).resolve_left (by norm_num)

end CircleOrthogonality

section TsumProd

variable {𝕜 : Type*} [NormedCommRing 𝕜] [CompleteSpace 𝕜] [NormOneClass 𝕜]
  {α ι : Type*} [Nonempty ι] [DecidableEq α]

/-- The tuple-splitting equiv for one inserted index: a tuple on
`insert a s` is a value at `a` together with a tuple on `s`. -/
def insertTupleEquiv (a : α) {s : Finset α} (ha : a ∉ s) :
    (↥(insert a s) → ι) ≃ ι × (↥s → ι) where
  toFun n := (n ⟨a, Finset.mem_insert_self a s⟩,
    fun m => n ⟨m.1, Finset.mem_insert_of_mem m.2⟩)
  invFun p m := if h : m.1 = a then p.1
    else p.2 ⟨m.1, (Finset.mem_insert.mp m.2).resolve_left h⟩
  left_inv n := by
    funext m
    dsimp only
    split_ifs with h
    · congr 1
      exact Subtype.ext h.symm
    · congr 1
  right_inv p := by
    obtain ⟨p₁, p₂⟩ := p
    refine Prod.ext ?_ (funext fun m => ?_)
    · dsimp only
      split_ifs with h
      · rfl
      · exact (h rfl).elim
    · dsimp only
      have hm : m.1 ≠ a := fun h => ha (h ▸ m.2)
      split_ifs with h
      · exact absurd h hm
      · congr 1

/-- The tuple equiv's inverse at the inserted index. -/
theorem insertTupleEquiv_symm_apply_self (a : α) {s : Finset α}
    (ha : a ∉ s) (q : ι × (↥s → ι)) :
    (insertTupleEquiv a ha).symm q ⟨a, Finset.mem_insert_self a s⟩
      = q.1 := by
  show (insertTupleEquiv a ha).invFun q
    ⟨a, Finset.mem_insert_self a s⟩ = q.1
  show (if h : (⟨a, Finset.mem_insert_self a s⟩ : ↥(insert a s)).1 = a
    then q.1
    else q.2 ⟨(⟨a, Finset.mem_insert_self a s⟩ : ↥(insert a s)).1,
      (Finset.mem_insert.mp
        (⟨a, Finset.mem_insert_self a s⟩ : ↥(insert a s)).2).resolve_left
        h⟩) = q.1
  rw [dif_pos rfl]

/-- The tuple equiv's inverse at an index from `s`. -/
theorem insertTupleEquiv_symm_apply_of_mem (a : α) {s : Finset α}
    (ha : a ∉ s) (q : ι × (↥s → ι)) (m : ↥(insert a s)) (hm : m.1 ∈ s) :
    (insertTupleEquiv a ha).symm q m = q.2 ⟨m.1, hm⟩ := by
  show (insertTupleEquiv a ha).invFun q m = q.2 ⟨m.1, hm⟩
  show (if h : m.1 = a then q.1
    else q.2 ⟨m.1, (Finset.mem_insert.mp m.2).resolve_left h⟩)
    = q.2 ⟨m.1, hm⟩
  rw [dif_neg (fun h : ↑m = a => ha (h ▸ hm))]

/-- Splitting a product over `↥(insert a s)` along the tuple equiv:
the factor at `a` separates from the product over `↥s`. -/
theorem prod_subtype_insert_split {M : Type*} [CommMonoid M]
    (a : α) {s : Finset α} (ha : a ∉ s) (F : α → ι → M)
    (q : ι × (↥s → ι)) :
    (∏ x : ↥(insert a s), F x.1 ((insertTupleEquiv a ha).symm q x))
      = F a q.1 * ∏ x : ↥s, F x.1 (q.2 x) := by
  have hprod : (∏ x : ↥(insert a s),
        F x.1 ((insertTupleEquiv a ha).symm q x))
      = ∏ x ∈ insert a s, F x
        (if h : x ∈ insert a s
          then (insertTupleEquiv a ha).symm q ⟨x, h⟩
          else Classical.arbitrary ι) := by
    rw [Finset.prod_subtype (insert a s) (fun _ => Iff.rfl)]
    apply Finset.prod_congr rfl
    intro x _
    rw [dif_pos x.2, Subtype.eta]
  rw [hprod, Finset.prod_insert ha]
  congr 1
  · rw [dif_pos (Finset.mem_insert_self a s),
      insertTupleEquiv_symm_apply_self]
  · have step1 : ∏ x ∈ s, F x
          (if h : x ∈ insert a s
            then (insertTupleEquiv a ha).symm q ⟨x, h⟩
            else Classical.arbitrary ι)
        = ∏ x ∈ s, F x
          (if h : x ∈ s then q.2 ⟨x, h⟩ else Classical.arbitrary ι) := by
      apply Finset.prod_congr rfl
      intro x hx
      rw [dif_pos (Finset.mem_insert_of_mem hx), dif_pos hx,
        insertTupleEquiv_symm_apply_of_mem a ha q
          ⟨x, Finset.mem_insert_of_mem hx⟩ hx]
    rw [step1, Finset.prod_subtype s (fun _ => Iff.rfl)]
    apply Finset.prod_congr rfl
    intro x _
    rw [dif_pos x.2, Subtype.eta]

/-- Summability of a finite product of nonnegative real families,
over the tuple type. -/
theorem summable_prod_subtype (s : Finset α) (g : α → ι → ℝ)
    (hg : ∀ a ∈ s, Summable (g a)) (hgn : ∀ a ∈ s, ∀ n, 0 ≤ g a n) :
    Summable fun m : ↥s → ι => ∏ x : ↥s, g x.1 (m x) := by
  classical
  induction s using Finset.induction with
  | empty => exact Summable.of_finite
  | insert a s ha ih =>
      have hgs : ∀ x ∈ s, Summable (g x) :=
        fun x hx => hg x (Finset.mem_insert_of_mem hx)
      have hgns : ∀ x ∈ s, ∀ n, 0 ≤ g x n :=
        fun x hx => hgn x (Finset.mem_insert_of_mem hx)
      have ih' := ih hgs hgns
      have hpair : Summable fun q : ι × (↥s → ι) =>
          g a q.1 * ∏ x : ↥s, g x.1 (q.2 x) := by
        refine (summable_prod_of_nonneg (f := fun q : ι × (↥s → ι) =>
          g a q.1 * ∏ x : ↥s, g x.1 (q.2 x)) ?_).mpr ⟨?_, ?_⟩
        · intro q
          exact mul_nonneg (hgn a (Finset.mem_insert_self a s) q.1)
            (Finset.prod_nonneg fun x _ =>
              hgn x.1 (Finset.mem_insert_of_mem x.2) (q.2 x))
        · intro x
          refine (ih'.mul_left (g a x)).congr (fun y => ?_)
          rfl
        · have hcongr : Summable fun x : ι =>
                g a x * (∑' y : ↥s → ι, ∏ x' : ↥s, g x'.1 (y x')) :=
              (hg a (Finset.mem_insert_self a s)).mul_right _
          exact hcongr.congr (fun x => (tsum_mul_left).symm)
      exact ((insertTupleEquiv a ha).symm.summable_iff).mp
        (hpair.congr (fun q => (prod_subtype_insert_split a ha g q).symm))

/-- **Finite product of tsums**: the tsum over tuples of a product
of one-coordinate families is the finite product of the tsums.
Needs norm-summability of each family (for the product step) and
plain summability (for regrouping). -/
theorem tsum_prod_subtype (s : Finset α) (F : α → ι → 𝕜)
    (hF : ∀ a ∈ s, Summable (F a))
    (hFn : ∀ a ∈ s, Summable fun n => ‖F a n‖) :
    (∑' n : ↥s → ι, ∏ a : ↥s, F a.1 (n a)) = ∏ a ∈ s, ∑' n, F a n := by
  classical
  induction s using Finset.induction with
  | empty =>
      rw [Finset.prod_empty]
      rw [tsum_eq_sum (s := {(default : ↥(∅ : Finset α) → ι)})
        (fun b hb => (hb (Finset.mem_singleton.mpr
          (Unique.eq_default b))).elim)]
      simp
  | insert a s ha ih =>
      have hFs : ∀ x ∈ s, Summable (F x) :=
        fun x hx => hF x (Finset.mem_insert_of_mem hx)
      have hFns : ∀ x ∈ s, Summable fun n => ‖F x n‖ :=
        fun x hx => hFn x (Finset.mem_insert_of_mem hx)
      have ih' := ih hFs hFns
      have hnorm : Summable fun m : ↥s → ι =>
          ‖∏ x : ↥s, F x.1 (m x)‖ :=
        Summable.of_norm_bounded
          (summable_prod_subtype s (fun x n => ‖F x n‖) hFns
            (fun x _ n => norm_nonneg _))
          (fun m => by
            rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
            exact Finset.norm_prod_le Finset.univ _)
      calc (∑' n : ↥(insert a s) → ι, ∏ x : ↥(insert a s), F x.1 (n x))
          = ∑' q : ι × (↥s → ι),
              ∏ x : ↥(insert a s), F x.1 ((insertTupleEquiv a ha).symm q x) :=
            ((insertTupleEquiv a ha).symm.tsum_eq _).symm
        _ = ∑' q : ι × (↥s → ι), F a q.1 * ∏ x : ↥s, F x.1 (q.2 x) :=
            tsum_congr (fun q => prod_subtype_insert_split a ha F q)
        _ = (∑' n, F a n) * ∑' m : ↥s → ι, ∏ x : ↥s, F x.1 (m x) :=
            (tsum_mul_tsum_of_summable_norm
              (hFn a (Finset.mem_insert_self a s)) hnorm).symm
        _ = ∏ x ∈ insert a s, ∑' n, F x n := by
            rw [ih', Finset.prod_insert ha]

end TsumProd

section CircleAnatomy

variable {N : ℕ} [NeZero N]

/-- The crossing (zero) plaquettes, as a finset: exactly the
summation set of `wilsonActionZero`. -/
def zeroFinset : Finset ((Fin 4 → ZMod N) × Fin 4 × Fin 4) :=
  plaqIndex.filter IsZeroPlaq

theorem zeroFinset_eq :
    zeroFinset (N := N) = plaqIndex.filter IsZeroPlaq := rfl

/-- **Classification of the crossing plaquettes** (even `N`): a
plaquette in the index set is in the zero class iff it is temporal
(`μ = 0`) with base time `N/2 - 1` (the lower plane) or `N - 1`
(the upper plane). -/
theorem isZeroPlaq_iff (hN : Even N)
    (p : (Fin 4 → ZMod N) × Fin 4 × Fin 4) (hp : p ∈ plaqIndex) :
    IsZeroPlaq p ↔ p.2.1 = 0
      ∧ ((p.1 0).val = N / 2 - 1 ∨ (p.1 0).val = N - 1) := by
  obtain ⟨r, hr⟩ := hN
  have ht : (p.1 0).val < N := ZMod.val_lt _
  have hpν : p.2.1 < p.2.2 := mem_plaqIndex hp
  show (¬ plaqTimeHi p.1 p.2.1 < N / 2
      ∧ ¬ (N / 2 ≤ (p.1 0).val ∧ plaqTimeHi p.1 p.2.1 < N)) ↔ _
  by_cases hμ : p.2.1 = 0
  · rw [hμ, plaqTimeHi_zero]
    constructor
    · intro h
      refine ⟨rfl, ?_⟩
      omega
    · intro h
      rcases h.2 with h2 | h2 <;> constructor <;> omega
  · rw [plaqTimeHi_of_ne _ hμ]
    constructor
    · intro h
      exact False.elim (h.2 ⟨by omega, ht⟩)
    · intro h
      exact absurd h.1 hμ

/-- Pointwise value of the split configuration on the `s` side. -/
theorem splitEquiv_symm_apply_mem {G : Type*} [Group G]
    [MeasurableSpace G] {s : Finset (Link (Fin 4 → ZMod N))}
    (y : ↥s → G) (u : ↥sᶜ → G) {ℓ : Link (Fin 4 → ZMod N)}
    (hℓ : ℓ ∈ s) :
    (splitEquiv s).symm (y, u) ℓ = y ⟨ℓ, hℓ⟩ := by
  have h1 : (splitEquiv s) ((splitEquiv s).symm (y, u)) = (y, u) :=
    MeasurableEquiv.apply_symm_apply _ _
  have h2 := congrFun (splitEquiv_fst s ((splitEquiv s).symm (y, u)))
    ⟨ℓ, hℓ⟩
  rw [h1] at h2
  exact h2.symm

/-- Pointwise value of the split configuration on the complement. -/
theorem splitEquiv_symm_apply_not_mem {G : Type*} [Group G]
    [MeasurableSpace G] {s : Finset (Link (Fin 4 → ZMod N))}
    (y : ↥s → G) (u : ↥sᶜ → G) {ℓ : Link (Fin 4 → ZMod N)}
    (hℓ : ℓ ∈ sᶜ) :
    (splitEquiv s).symm (y, u) ℓ = u ⟨ℓ, hℓ⟩ := by
  have h1 : (splitEquiv s) ((splitEquiv s).symm (y, u)) = (y, u) :=
    MeasurableEquiv.apply_symm_apply _ _
  have h2 := congrFun (splitEquiv_snd s ((splitEquiv s).symm (y, u)))
    ⟨ℓ, hℓ⟩
  rw [h1] at h2
  exact h2.symm

/-- Parity obstruction: twice a `ZMod N` element is never `-1` at
even `N`. -/
theorem two_mul_ne_neg_one (hN : Even N) (a : ZMod N) :
    2 * a ≠ -1 := by
  intro h
  have h0 : ((2 * a.val + 1 : ℕ) : ZMod N) = 0 := by
    have h1 : (2 : ZMod N) * a + 1 = 0 := by
      have h' := congrArg (· + 1) h
      simpa using h'
    calc ((2 * a.val + 1 : ℕ) : ZMod N) = 2 * a + 1 := by
          rw [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one,
            ZMod.natCast_zmod_val]
      _ = 0 := h1
  rw [ZMod.natCast_eq_zero_iff] at h0
  obtain ⟨r, hr⟩ := hN
  obtain ⟨k, hk⟩ := h0
  have hEven : Even (2 * a.val + 1) := ⟨r * k, by rw [hk, hr]; ring⟩
  exact absurd hEven (Nat.not_even_iff_odd.mpr ⟨a.val, rfl⟩)

/-- The time coordinate after a time shift, as a value. -/
theorem val_torusShift_zero_apply (hN : 2 ≤ N)
    (x : Fin 4 → ZMod N) :
    ((torusShift N 0 x) 0).val = ((x 0).val + 1) % N := by
  rw [torusShift_apply_coord, Pi.single_eq_same,
    show (1 : ZMod N) = ((1 : ℕ) : ZMod N) by simp, ZMod.val_add,
    ZMod.val_natCast, Nat.mod_eq_of_lt (by omega : 1 < N),
    add_comm 1 ((x 0).val)]

/-- Coordinate-zero computation behind the plane reflections:
at a plane time, `-1 - x 0 = 1 + x 0` in `ZMod N`. -/
theorem neg_one_sub_eq_one_add (hN : Even N) (x : Fin 4 → ZMod N)
    (h : (x 0).val = N / 2 - 1 ∨ (x 0).val = N - 1) :
    -1 - x 0 = 1 + x 0 := by
  obtain ⟨r, hr⟩ := hN
  have hN0 : N ≠ 0 := NeZero.ne N
  have hr2 : N / 2 = r := by omega
  have hR : ((r : ℕ) : ZMod N) * 2 = 0 := by
    have h0 : ((2 * r : ℕ) : ZMod N) = 0 := by
      rw [show 2 * r = N by omega]
      exact ZMod.natCast_self N
    have h0' : (2 : ZMod N) * ((r : ℕ) : ZMod N) = 0 := by
      rw [← Nat.cast_ofNat, ← Nat.cast_mul]
      exact h0
    rw [mul_comm]
    exact h0'
  have hx : (x 0) = (((x 0).val : ℕ) : ZMod N) :=
    (ZMod.natCast_zmod_val _).symm
  rw [hx]
  rcases h with h | h
  · have hc : (((x 0).val : ℕ) : ZMod N) = ((r : ℕ) : ZMod N) - 1 := by
      rw [h, hr2, Nat.cast_sub (by omega : 1 ≤ r), Nat.cast_one]
    rw [hc]
    linear_combination -hR
  · have hc : (((x 0).val : ℕ) : ZMod N) = -1 := by
      rw [h, show N - 1 = 2 * r - 1 by omega, Nat.cast_sub (by omega),
        Nat.cast_one]
      have h0 : ((2 * r : ℕ) : ZMod N) = 0 := by
        rw [show 2 * r = N by omega]
        exact ZMod.natCast_self N
      rw [h0, zero_sub]
    rw [hc]
    ring

/-- At a plane time the site reflection equals the forward time
shift. -/
theorem reflSite_eq_torusShift_zero (hN : Even N)
    (x : Fin 4 → ZMod N)
    (h : (x 0).val = N / 2 - 1 ∨ (x 0).val = N - 1) :
    reflSite x = torusShift N 0 x := by
  funext j
  by_cases hj : j = 0
  · subst hj
    rw [reflSite_apply_self, torusShift_apply_coord, Pi.single_eq_same]
    exact neg_one_sub_eq_one_add hN x h
  · rw [reflSite_apply_of_ne _ hj, torusShift_apply_coord,
      Pi.single_eq_of_ne hj, zero_add]

/-- The two time links of a crossing plaquette are plane links. -/
theorem reflLink_timeLink (hN : Even N) (x : Fin 4 → ZMod N)
    (h : (x 0).val = N / 2 - 1 ∨ (x 0).val = N - 1) :
    reflLink (x, 0) = (x, 0) := by
  rw [reflLink_zero, reflSite_eq_torusShift_zero hN x h,
    Equiv.symm_apply_apply]

theorem reflLink_timeLink_shift (hN : Even N) {ν : Fin 4} (hν : ν ≠ 0)
    (x : Fin 4 → ZMod N)
    (h : (x 0).val = N / 2 - 1 ∨ (x 0).val = N - 1) :
    reflLink (torusShift N ν x, 0) = (torusShift N ν x, 0) := by
  have hsite : reflSite (torusShift N ν x)
      = torusShift N 0 (torusShift N ν x) := by
    funext j
    by_cases hj : j = 0
    · subst hj
      rw [reflSite_apply_self, torusShift_apply_zero_of_ne hν,
        torusShift_apply_coord, Pi.single_eq_same,
        torusShift_apply_zero_of_ne hν]
      exact neg_one_sub_eq_one_add hN x h
    · rw [reflSite_apply_of_ne _ hj]
      have hthis : torusShift N 0 (torusShift N ν x) j
          = (torusShift N ν x) j := by
        rw [torusShift_apply_coord, Pi.single_eq_of_ne hj, zero_add]
      rw [hthis]
  rw [reflLink_zero, hsite, Equiv.symm_apply_apply]

/-- The spatial link of a crossing plaquette at the base site is
never a plane link. -/
theorem reflLink_spatial_ne (hN : Even N) {ν : Fin 4} (hν : ν ≠ 0)
    (x : Fin 4 → ZMod N) :
    reflLink (x, ν) ≠ (x, ν) := by
  intro hbad
  rw [reflLink_of_ne hν] at hbad
  have h0 : reflSite x 0 = x 0 :=
    congrFun (congrArg Prod.fst hbad) 0
  rw [reflSite_apply_self] at h0
  have h2s : (2 : ZMod N) * (x 0) = -1 := by
    have h0' : (x 0) = -1 - (x 0) := h0.symm
    linear_combination h0'
  exact two_mul_ne_neg_one hN _ h2s

/-- The spatial link of a crossing plaquette at the shifted site
is never a plane link. -/
theorem reflLink_spatial_shift_ne (hN : Even N) {ν : Fin 4}
    (hν : ν ≠ 0) (x : Fin 4 → ZMod N) :
    reflLink (torusShift N 0 x, ν) ≠ (torusShift N 0 x, ν) := by
  intro hbad
  rw [reflLink_of_ne hν] at hbad
  have h0 : reflSite (torusShift N 0 x) 0 = (torusShift N 0 x) 0 :=
    congrFun (congrArg Prod.fst hbad) 0
  rw [reflSite_apply_self] at h0
  have h2s : (2 : ZMod N) * ((torusShift N 0 x) 0) = -1 := by
    have h0' : ((torusShift N 0 x) 0) = -1 - ((torusShift N 0 x) 0) :=
      h0.symm
    linear_combination h0'
  exact two_mul_ne_neg_one hN _ h2s

/-- At the lower plane, the reflection sends the strict link `D`
to the shifted spatial link `B`. -/
theorem reflLink_spatial_lower (hN : Even N) {ν : Fin 4} (hν : ν ≠ 0)
    (x : Fin 4 → ZMod N) (h : (x 0).val = N / 2 - 1) :
    reflLink (x, ν) = (torusShift N 0 x, ν) := by
  rw [reflLink_of_ne hν,
    reflSite_eq_torusShift_zero hN x (Or.inl h)]

/-- At the upper plane, the reflection sends the strict link `B`
to the base spatial link `D`. -/
theorem reflLink_spatial_upper (hN : Even N) {ν : Fin 4} (hν : ν ≠ 0)
    (x : Fin 4 → ZMod N) (h : (x 0).val = N - 1) :
    reflSite (torusShift N 0 x) = x := by
  funext j
  by_cases hj : j = 0
  · subst hj
    rw [reflSite_apply_self, torusShift_apply_coord, Pi.single_eq_same]
    have hx : (x 0) = (((x 0).val : ℕ) : ZMod N) :=
      (ZMod.natCast_zmod_val _).symm
    have hc : (x 0) = -1 := by
      obtain ⟨r, hr⟩ := hN
      have hN0 : N ≠ 0 := NeZero.ne N
      rw [hx, h, show N - 1 = 2 * r - 1 by omega, Nat.cast_sub (by omega),
        Nat.cast_one,
        show ((2 * r : ℕ) : ZMod N) = 0 by
          rw [show 2 * r = N by omega]; exact ZMod.natCast_self N,
        zero_sub]
    rw [hc]
    ring
  · rw [reflSite_apply_of_ne _ hj, torusShift_apply_coord,
      Pi.single_eq_of_ne hj, zero_add]

theorem reflLink_spatial_upper_link (hN : Even N) {ν : Fin 4}
    (hν : ν ≠ 0) (x : Fin 4 → ZMod N) (h : (x 0).val = N - 1) :
    reflLink (torusShift N 0 x, ν) = (x, ν) := by
  rw [reflLink_of_ne hν, reflLink_spatial_upper hN hν x h]

end CircleAnatomy

section CircleFactors

variable {N : ℕ} [NeZero N]

/-- Extension of a closed-half configuration by `1`. -/
noncomputable def extHalf (y : ↥(halfLinks (N := N)) → Circle) :
    Config (Fin 4 → ZMod N) Circle :=
  fun ℓ => if h : ℓ ∈ halfLinks then y ⟨ℓ, h⟩ else 1

/-- Extension of a negative-half configuration by `1`. -/
noncomputable def extNeg (u : ↥(negLinks (N := N)) → Circle) :
    Config (Fin 4 → ZMod N) Circle :=
  fun ℓ => if h : ℓ ∈ negLinks then u ⟨ℓ, h⟩ else 1

/-- Extension of a strict-half configuration by `1`
(the corpus's `extendP`). -/
theorem extHalf_apply {y : ↥(halfLinks (N := N)) → Circle}
    {ℓ : Link (Fin 4 → ZMod N)} (hℓ : ℓ ∈ halfLinks) :
    extHalf y ℓ = y ⟨ℓ, hℓ⟩ := dif_pos hℓ

theorem extNeg_apply {u : ↥(negLinks (N := N)) → Circle}
    {ℓ : Link (Fin 4 → ZMod N)} (hℓ : ℓ ∈ negLinks) :
    extNeg u ℓ = u ⟨ℓ, hℓ⟩ := dif_pos hℓ

/-- The four links of a plaquette, in the order they appear in the
holonomy `U (x,0) * U (σ₀x,ν) * (U (σ_νx,0))⁻¹ * (U (x,ν))⁻¹`. -/
def linkA (p : (Fin 4 → ZMod N) × Fin 4 × Fin 4) :
    Link (Fin 4 → ZMod N) := (p.1, 0)

def linkB (p : (Fin 4 → ZMod N) × Fin 4 × Fin 4) :
    Link (Fin 4 → ZMod N) := (torusShift N 0 p.1, p.2.2)

def linkC (p : (Fin 4 → ZMod N) × Fin 4 × Fin 4) :
    Link (Fin 4 → ZMod N) := (torusShift N p.2.2 p.1, 0)

def linkD (p : (Fin 4 → ZMod N) × Fin 4 × Fin 4) :
    Link (Fin 4 → ZMod N) := (p.1, p.2.2)

/-- **The link pattern of a crossing plaquette** (even `N`): at the
lower plane, `A, C` are plane links of the closed half, `D` is
strict, `B` is in the negative half; at the upper plane, `A, C` are
plane links of the negative half, `B` is strict, `D` is in the
negative half. -/
theorem zero_link_pattern (hN : Even N)
    (p : (Fin 4 → ZMod N) × Fin 4 × Fin 4) (hp : p ∈ zeroFinset) :
    ((p.1 0).val = N / 2 - 1
      ∧ linkA p ∈ halfLinks ∧ linkA p ∈ planeLinks
      ∧ linkC p ∈ halfLinks ∧ linkC p ∈ planeLinks
      ∧ linkD p ∈ posLinks ∧ linkB p ∈ negLinks)
    ∨ ((p.1 0).val = N - 1
      ∧ linkA p ∈ negLinks ∧ linkA p ∈ planeLinks
      ∧ linkC p ∈ negLinks ∧ linkC p ∈ planeLinks
      ∧ linkB p ∈ posLinks ∧ linkD p ∈ negLinks) := by
  have hpI : p ∈ plaqIndex := (Finset.mem_filter.mp hp).1
  have hz : IsZeroPlaq p := (Finset.mem_filter.mp hp).2
  obtain ⟨hμ, hval⟩ := (isZeroPlaq_iff hN p hpI).mp hz
  have hν : p.2.2 ≠ 0 := by
    have h12 : p.2.1 < p.2.2 := mem_plaqIndex hpI
    omega
  have ht : (p.1 0).val < N := ZMod.val_lt _
  have hN0 : N ≠ 0 := NeZero.ne N
  obtain ⟨r, hr⟩ := hN
  have hNEv : Even N := ⟨r, hr⟩
  have htimeC : ((torusShift N p.2.2 p.1) 0).val = (p.1 0).val := by
    rw [torusShift_apply_zero_of_ne hν]
  have hplaneA : linkA p ∈ planeLinks := by
    rw [mem_planeLinks]
    exact reflLink_timeLink hNEv p.1 hval
  have hplaneC : linkC p ∈ planeLinks := by
    rw [mem_planeLinks]
    exact reflLink_timeLink_shift hNEv hν p.1 hval
  rcases hval with hval | hval
  · left
    have hvalB : ((torusShift N 0 p.1) 0).val = N / 2 := by
      rw [val_torusShift_zero_apply (by omega)]
      have h1 : (p.1 0).val + 1 = N / 2 := by omega
      rw [h1, Nat.mod_eq_of_lt (by omega)]
    refine ⟨hval, ?_, hplaneA, ?_, hplaneC, ?_, ?_⟩
    · rw [mem_halfLinks]
      show (p.1 0).val < N / 2; omega
    · rw [mem_halfLinks]
      show ((torusShift N p.2.2 p.1) 0).val < N / 2
      rw [htimeC]; omega
    · rw [mem_posLinks]
      refine ⟨?_, ?_⟩
      · show (p.1 0).val < N / 2; omega
      · show reflLink (p.1, p.2.2) ≠ (p.1, p.2.2)
        exact reflLink_spatial_ne hNEv hν p.1
    · rw [mem_negLinks]
      show N / 2 ≤ ((torusShift N 0 p.1) 0).val
      rw [hvalB]
  · right
    have hvalB : ((torusShift N 0 p.1) 0).val = 0 := by
      rw [val_torusShift_zero_apply (by omega)]
      have h1 : (p.1 0).val + 1 = N := by omega
      rw [h1, Nat.mod_self]
    refine ⟨hval, ?_, hplaneA, ?_, hplaneC, ?_, ?_⟩
    · rw [mem_negLinks]
      show N / 2 ≤ (p.1 0).val; omega
    · rw [mem_negLinks]
      show N / 2 ≤ ((torusShift N p.2.2 p.1) 0).val
      rw [htimeC]; omega
    · rw [mem_posLinks]
      refine ⟨?_, ?_⟩
      · show ((torusShift N 0 p.1) 0).val < N / 2
        rw [hvalB]; omega
      · show reflLink (torusShift N 0 p.1, p.2.2)
          ≠ (torusShift N 0 p.1, p.2.2)
        exact reflLink_spatial_shift_ne hNEv hν p.1
    · rw [mem_negLinks]
      show N / 2 ≤ (p.1 0).val; omega

/-- The positive (closed-half) factor of a crossing plaquette:
the product of its link factors on the closed-half side. -/
noncomputable def yPartH (p : (Fin 4 → ZMod N) × Fin 4 × Fin 4)
    (y : ↥(halfLinks (N := N)) → Circle) : Circle :=
  if (p.1 0).val = N / 2 - 1 then
    extHalf y (linkA p) * (extHalf y (linkC p))⁻¹
      * (extHalf y (linkD p))⁻¹
  else extHalf y (linkB p)

/-- The negative factor of a crossing plaquette. -/
noncomputable def uPartH (p : (Fin 4 → ZMod N) × Fin 4 × Fin 4)
    (u : ↥(negLinks (N := N)) → Circle) : Circle :=
  if (p.1 0).val = N / 2 - 1 then extNeg u (linkB p)
  else extNeg u (linkA p) * (extNeg u (linkC p))⁻¹
    * (extNeg u (linkD p))⁻¹

/-- The strict factor of a crossing plaquette, read on the strict
positive half. -/
noncomputable def posFactor (p : (Fin 4 → ZMod N) × Fin 4 × Fin 4)
    (z : ↥(posLinks (N := N)) → Circle) : Circle :=
  if (p.1 0).val = N / 2 - 1 then (extendP z (linkD p))⁻¹
  else extendP z (linkB p)

/-- The stratum factor of a crossing plaquette on the closed-half
side (the two time-link factors at the lower plane; `1` at the
upper plane). -/
noncomputable def stratFactorY (p : (Fin 4 → ZMod N) × Fin 4 × Fin 4)
    (y : ↥(halfLinks (N := N)) → Circle) : Circle :=
  if (p.1 0).val = N / 2 - 1 then
    extHalf y (linkA p) * (extHalf y (linkC p))⁻¹
  else 1

/-- The stratum factor of a crossing plaquette on the negative
side (`1` at the lower plane; the two time-link factors at the
upper plane). -/
noncomputable def stratFactorU (p : (Fin 4 → ZMod N) × Fin 4 × Fin 4)
    (u : ↥(negLinks (N := N)) → Circle) : Circle :=
  if (p.1 0).val = N / 2 - 1 then 1
  else extNeg u (linkA p) * (extNeg u (linkC p))⁻¹

/-- The mirror-read strict factor of a crossing plaquette: the
inverse of `posFactor`, as the mirror computation requires. -/
noncomputable def negFactorZ (p : (Fin 4 → ZMod N) × Fin 4 × Fin 4)
    (z : ↥(posLinks (N := N)) → Circle) : Circle :=
  if (p.1 0).val = N / 2 - 1 then extendP z (linkD p)
  else (extendP z (linkB p))⁻¹

theorem negFactorZ_eq_inv (p : (Fin 4 → ZMod N) × Fin 4 × Fin 4)
    (z : ↥(posLinks (N := N)) → Circle) :
    negFactorZ p z = (posFactor p z)⁻¹ := by
  unfold negFactorZ posFactor
  split_ifs with h
  · rw [inv_inv]
  · rfl

end CircleFactors

section CircleFactorization

variable {N : ℕ} [NeZero N]

/-- **Factorization on the closed-half side**: the positive factor
of a crossing plaquette is the strict factor at the restricted
configuration times the stratum factor. -/
theorem yPartH_factor (hN : Even N)
    (p : (Fin 4 → ZMod N) × Fin 4 × Fin 4) (hp : p ∈ zeroFinset)
    (y : ↥(halfLinks (N := N)) → Circle) :
    yPartH p y = posFactor p (restrictPos y) * stratFactorY p y := by
  rcases zero_link_pattern hN p hp with
    ⟨hval, hAhalf, -, hChalf, -, hDpos, -⟩
    | ⟨hval, -, -, -, -, hBpos, -⟩
  · have hED : extendP (restrictPos y) (linkD p) = extHalf y (linkD p) :=
      (dif_pos hDpos).trans
        (extHalf_apply (posLinks_subset_halfLinks hDpos)).symm
    unfold yPartH posFactor stratFactorY
    rw [if_pos hval, if_pos hval, if_pos hval, hED]
    exact mul_comm _ _
  · have hne : ¬ (p.1 0).val = N / 2 - 1 := by
      obtain ⟨r, hr⟩ := hN
      have hN0 : N ≠ 0 := NeZero.ne N
      omega
    have hEB : extendP (restrictPos y) (linkB p) = extHalf y (linkB p) :=
      (dif_pos hBpos).trans
        (extHalf_apply (posLinks_subset_halfLinks hBpos)).symm
    unfold yPartH posFactor stratFactorY
    rw [if_neg hne, if_neg hne, if_neg hne, hEB, mul_one]

/-- Evaluation of the mirror at a strict link with nonzero
direction: no inversion, read at the reflected link. -/
theorem mirrorP_apply_of_ne (hN : Even N)
    (u : ↥(negLinks (N := N)) → Circle)
    (ℓ : ↥(posLinks (N := N))) (hℓ : ℓ.1.2 ≠ 0) :
    mirrorP hN u ℓ
      = u ⟨reflLink ℓ.1, reflLink_mem_negLinks hN ℓ.2⟩ :=
  if_neg hℓ

/-- **Factorization on the negative side**: the negative factor of
a crossing plaquette is the mirror-read strict factor times the
stratum factor. -/
theorem uPartH_factor (hN : Even N)
    (p : (Fin 4 → ZMod N) × Fin 4 × Fin 4) (hp : p ∈ zeroFinset)
    (u : ↥(negLinks (N := N)) → Circle) :
    uPartH p u = negFactorZ p (mirrorP hN u) * stratFactorU p u := by
  have hpI : p ∈ plaqIndex := (Finset.mem_filter.mp hp).1
  have hz : IsZeroPlaq p := (Finset.mem_filter.mp hp).2
  obtain ⟨hμ, hval0⟩ := (isZeroPlaq_iff hN p hpI).mp hz
  have hν : p.2.2 ≠ 0 := by
    have h12 : p.2.1 < p.2.2 := mem_plaqIndex hpI
    omega
  rcases zero_link_pattern hN p hp with
    ⟨hval, -, -, -, -, hDpos, hBneg⟩
    | ⟨hval, hAneg, -, hCneg, -, hBpos, hDneg⟩
  · have hED : extendP (mirrorP hN u) (linkD p) = extNeg u (linkB p) := by
      rw [show extendP (mirrorP hN u) (linkD p)
          = mirrorP hN u ⟨linkD p, hDpos⟩ from dif_pos hDpos,
        mirrorP_apply_of_ne hN u ⟨linkD p, hDpos⟩ hν]
      exact (congrArg u (Subtype.ext
        (reflLink_spatial_lower hN hν p.1 hval))).trans
        (extNeg_apply hBneg).symm
    unfold uPartH negFactorZ stratFactorU
    rw [if_pos hval, if_pos hval, if_pos hval, hED, mul_one]
  · have hne : ¬ (p.1 0).val = N / 2 - 1 := by
      obtain ⟨r, hr⟩ := hN
      have hN0 : N ≠ 0 := NeZero.ne N
      omega
    have hEB : extendP (mirrorP hN u) (linkB p) = extNeg u (linkD p) := by
      rw [show extendP (mirrorP hN u) (linkB p)
          = mirrorP hN u ⟨linkB p, hBpos⟩ from dif_pos hBpos,
        mirrorP_apply_of_ne hN u ⟨linkB p, hBpos⟩ hν]
      exact (congrArg u (Subtype.ext
        (reflLink_spatial_upper_link hN hν p.1 hval))).trans
        (extNeg_apply hDneg).symm
    unfold uPartH negFactorZ stratFactorU
    rw [if_neg hne, if_neg hne, if_neg hne, hEB]
    exact mul_comm _ _

/-- **The plaquette factorization**: the holonomy of a crossing
plaquette of the unsplit configuration is the product of its
positive and negative factors. -/
theorem plaquette_factor (hN : Even N)
    (p : (Fin 4 → ZMod N) × Fin 4 × Fin 4) (hp : p ∈ zeroFinset)
    (y : ↥(halfLinks (N := N)) → Circle)
    (u : ↥(negLinks (N := N)) → Circle) :
    plaquette (torusShift N) ((splitEquiv halfLinks).symm (y, u))
        p.1 0 p.2.2
      = yPartH p y * uPartH p u := by
  show (splitEquiv halfLinks).symm (y, u) (linkA p)
      * (splitEquiv halfLinks).symm (y, u) (linkB p)
      * ((splitEquiv halfLinks).symm (y, u) (linkC p))⁻¹
      * ((splitEquiv halfLinks).symm (y, u) (linkD p))⁻¹
    = yPartH p y * uPartH p u
  rcases zero_link_pattern hN p hp with
    ⟨hval, hAhalf, -, hChalf, -, hDpos, hBneg⟩
    | ⟨hval, hAneg, -, hCneg, -, hBpos, hDneg⟩
  · have hvA : (splitEquiv halfLinks).symm (y, u) (linkA p)
        = extHalf y (linkA p) :=
      (splitEquiv_symm_apply_mem y u hAhalf).trans
        (extHalf_apply hAhalf).symm
    have hvB : (splitEquiv halfLinks).symm (y, u) (linkB p)
        = extNeg u (linkB p) :=
      (splitEquiv_symm_apply_not_mem y u hBneg).trans
        (extNeg_apply hBneg).symm
    have hvC : (splitEquiv halfLinks).symm (y, u) (linkC p)
        = extHalf y (linkC p) :=
      (splitEquiv_symm_apply_mem y u hChalf).trans
        (extHalf_apply hChalf).symm
    have hvD : (splitEquiv halfLinks).symm (y, u) (linkD p)
        = extHalf y (linkD p) :=
      (splitEquiv_symm_apply_mem y u
        (posLinks_subset_halfLinks hDpos)).trans
        (extHalf_apply (posLinks_subset_halfLinks hDpos)).symm
    rw [hvA, hvB, hvC, hvD]
    unfold yPartH uPartH
    rw [if_pos hval, if_pos hval]
    ac_rfl
  · have hne : ¬ (p.1 0).val = N / 2 - 1 := by
      obtain ⟨r, hr⟩ := hN
      have hN0 : N ≠ 0 := NeZero.ne N
      omega
    have hvA : (splitEquiv halfLinks).symm (y, u) (linkA p)
        = extNeg u (linkA p) :=
      (splitEquiv_symm_apply_not_mem y u hAneg).trans
        (extNeg_apply hAneg).symm
    have hvB : (splitEquiv halfLinks).symm (y, u) (linkB p)
        = extHalf y (linkB p) :=
      (splitEquiv_symm_apply_mem y u
        (posLinks_subset_halfLinks hBpos)).trans
        (extHalf_apply (posLinks_subset_halfLinks hBpos)).symm
    have hvC : (splitEquiv halfLinks).symm (y, u) (linkC p)
        = extNeg u (linkC p) :=
      (splitEquiv_symm_apply_not_mem y u hCneg).trans
        (extNeg_apply hCneg).symm
    have hvD : (splitEquiv halfLinks).symm (y, u) (linkD p)
        = extNeg u (linkD p) :=
      (splitEquiv_symm_apply_not_mem y u hDneg).trans
        (extNeg_apply hDneg).symm
    rw [hvA, hvB, hvC, hvD]
    unfold yPartH uPartH
    rw [if_neg hne, if_neg hne]
    ac_rfl

end CircleFactorization

section CircleFeatures

variable {N : ℕ} [NeZero N]

/-- The monomial of a crossing-plaquette exponent vector on the
closed-half side. -/
noncomputable def monoAY (n : ↥(zeroFinset (N := N)) → ℤ)
    (y : ↥(halfLinks (N := N)) → Circle) : Circle :=
  ∏ p : ↥(zeroFinset (N := N)), (yPartH p.1 y) ^ (n p)

/-- The monomial on the negative side. -/
noncomputable def monoBU (n : ↥(zeroFinset (N := N)) → ℤ)
    (u : ↥(negLinks (N := N)) → Circle) : Circle :=
  ∏ p : ↥(zeroFinset (N := N)), (uPartH p.1 u) ^ (n p)

/-- The monomial of strict factors. -/
noncomputable def mPosZ (n : ↥(zeroFinset (N := N)) → ℤ)
    (z : ↥(posLinks (N := N)) → Circle) : Circle :=
  ∏ p : ↥(zeroFinset (N := N)), (posFactor p.1 z) ^ (n p)

/-- The stratum monomial on the closed-half side. -/
noncomputable def stratY (n : ↥(zeroFinset (N := N)) → ℤ)
    (y : ↥(halfLinks (N := N)) → Circle) : Circle :=
  ∏ p : ↥(zeroFinset (N := N)), (stratFactorY p.1 y) ^ (n p)

/-- The stratum monomial on the negative side. -/
noncomputable def stratU (n : ↥(zeroFinset (N := N)) → ℤ)
    (u : ↥(negLinks (N := N)) → Circle) : Circle :=
  ∏ p : ↥(zeroFinset (N := N)), (stratFactorU p.1 u) ^ (n p)

theorem monoAY_factor (hN : Even N) (n : ↥(zeroFinset (N := N)) → ℤ)
    (y : ↥(halfLinks (N := N)) → Circle) :
    monoAY n y = mPosZ n (restrictPos y) * stratY n y := by
  unfold monoAY mPosZ stratY
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun p _ => by
    rw [yPartH_factor hN p.1 p.2 y, mul_zpow]

theorem monoBU_factor (hN : Even N) (n : ↥(zeroFinset (N := N)) → ℤ)
    (u : ↥(negLinks (N := N)) → Circle) :
    monoBU n u
      = (∏ p : ↥(zeroFinset (N := N)),
          (negFactorZ p.1 (mirrorP hN u)) ^ (n p)) * stratU n u := by
  unfold monoBU stratU
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun p _ => by
    rw [uPartH_factor hN p.1 p.2 u, mul_zpow]

theorem negFactorZ_prod (n : ↥(zeroFinset (N := N)) → ℤ)
    (z : ↥(posLinks (N := N)) → Circle) :
    (∏ p : ↥(zeroFinset (N := N)), (negFactorZ p.1 z) ^ (n p))
      = (mPosZ n z)⁻¹ := by
  unfold mPosZ
  rw [← Finset.prod_inv_distrib]
  exact Finset.prod_congr rfl fun p _ => by
    rw [negFactorZ_eq_inv, inv_zpow]

/-- The product of crossing holonomies is the product of the two
side monomials. -/
theorem plaquette_prod (hN : Even N) (n : ↥(zeroFinset (N := N)) → ℤ)
    (y : ↥(halfLinks (N := N)) → Circle)
    (u : ↥(negLinks (N := N)) → Circle) :
    ∏ p : ↥(zeroFinset (N := N)),
        (plaquette (torusShift N) ((splitEquiv halfLinks).symm (y, u))
          p.1.1 p.1.2.1 p.1.2.2) ^ (n p)
      = monoAY n y * monoBU n u := by
  unfold monoAY monoBU
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun p _ => by
    have hμ : p.1.2.1 = 0 :=
      ((isZeroPlaq_iff hN p.1 (Finset.mem_filter.mp p.2).1).mp
        (Finset.mem_filter.mp p.2).2).1
    rw [hμ, plaquette_factor hN p.1 p.2 y u, mul_zpow]

/-- The Fourier weight of an exponent vector: the product of the
one-plaquette Bessel weights. -/
noncomputable def wR (β : ℝ) (n : ↥(zeroFinset (N := N)) → ℤ) : ℝ :=
  ∏ p : ↥(zeroFinset (N := N)), (Real.exp (-β) * besselI β (n p))

theorem wR_nonneg (hβ : 0 ≤ β) (n : ↥(zeroFinset (N := N)) → ℤ) :
    0 ≤ wR β n :=
  Finset.prod_nonneg fun p _ =>
    mul_nonneg (Real.exp_pos _).le (besselI_nonneg hβ _)

/-- The closed-half feature. -/
noncomputable def featA (β : ℝ) (n : ↥(zeroFinset (N := N)) → ℤ)
    (y : ↥(halfLinks (N := N)) → Circle) : ℂ :=
  ((Real.exp (- halfActionP circleRep β (restrictPos y))
      * Real.sqrt (wR β n) : ℝ) : ℂ) * ((monoAY n y : Circle) : ℂ)

/-- The negative-side feature. -/
noncomputable def featB (hN : Even N) (β : ℝ)
    (n : ↥(zeroFinset (N := N)) → ℤ)
    (u : ↥(negLinks (N := N)) → Circle) : ℂ :=
  ((Real.exp (- halfActionP circleRep β (mirrorP hN u))
      * Real.sqrt (wR β n) : ℝ) : ℂ) * (((monoBU n u)⁻¹ : Circle) : ℂ)

/-- The strict feature on the positive half (the `Ξ` of the
integrated criterion). -/
noncomputable def featXi (β : ℝ) (n : ↥(zeroFinset (N := N)) → ℤ)
    (z : ↥(posLinks (N := N)) → Circle) : ℂ :=
  ((Real.exp (- halfActionP circleRep β z)
      * Real.sqrt (wR β n) : ℝ) : ℂ) * ((mPosZ n z : Circle) : ℂ)

theorem coe_prod_circle {α : Type*} (s : Finset α) (f : α → Circle) :
    ((∏ a ∈ s, f a : Circle) : ℂ) = ∏ a ∈ s, ((f a : Circle) : ℂ) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha,
      Circle.coe_mul, ih]

theorem coe_prod_real {α : Type*} (s : Finset α) (f : α → ℝ) :
    ((∏ a ∈ s, f a : ℝ) : ℂ) = ∏ a ∈ s, ((f a : ℝ) : ℂ) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha,
      Complex.ofReal_mul, ih]

/-- The half-action of the circle theory is nonnegative at
`β ≥ 0`: a positive multiple of a sum of plaquette densities,
each in `[0, 2]`. -/
theorem halfActionP_circle_nonneg (hβ : 0 ≤ β)
    (z : ↥(posLinks (N := N)) → Circle) :
    0 ≤ halfActionP circleRep β z := by
  unfold halfActionP wilsonActionPlus
  exact mul_nonneg hβ (Finset.sum_nonneg fun p _ =>
    (plaquetteDensity_mem_Icc (σ := torusShift N) (ρ := circleRep)
      (show (0 : ℕ) < 1 by norm_num) _ _ _ _).1)

/-- The norm of a one-plaquette Fourier factor. -/
theorem norm_fourier_factor (β : ℝ) (w : Circle) (m : ℤ) :
    ‖((Real.exp (-β) * besselI β m : ℝ) : ℂ) * ((w : ℂ)) ^ m‖
      = Real.exp (-β) * ‖besselI β m‖ := by
  have h1 : ‖((Real.exp (-β) * besselI β m : ℝ) : ℂ)‖
      = Real.exp (-β) * ‖besselI β m‖ :=
    (RCLike.norm_ofReal _).trans ((abs_mul _ _).trans (by
      rw [abs_of_pos (Real.exp_pos _), Real.norm_eq_abs]))
  have h2 : ‖((w : ℂ)) ^ m‖ = 1 := by
    rw [norm_zpow]; simp
  rw [norm_mul, h1, h2, mul_one]

/-- Summability of the one-plaquette Fourier family in `ℂ`. -/
theorem summable_fourier_factor (β : ℝ)
    (w : Circle) :
    Summable fun m : ℤ =>
      ((Real.exp (-β) * besselI β m : ℝ) : ℂ) * ((w : ℂ)) ^ m := by
  refine Summable.of_norm_bounded
    (g := fun m => Real.exp (-β) * ‖besselI β m‖)
    ((summable_besselI_int β).norm.mul_left _) fun m => le_of_eq ?_
  exact norm_fourier_factor β w m

/-- Summability of the norms of a one-plaquette Fourier family. -/
theorem summable_norm_fourier_factor (β : ℝ) (w : Circle) :
    Summable fun m : ℤ =>
      ‖((Real.exp (-β) * besselI β m : ℝ) : ℂ) * ((w : ℂ)) ^ m‖ :=
  Summable.congr ((summable_besselI_int β).norm.mul_left _)
    fun m => (norm_fourier_factor β w m).symm

/-- The crossing Boltzmann factor is a Gram series over exponent
vectors on the crossing plaquettes. -/
theorem exp_neg_zeroAction_tsum (hN : Even N) (β : ℝ)
    (y : ↥(halfLinks (N := N)) → Circle)
    (u : ↥(negLinks (N := N)) → Circle) :
    ((Real.exp (- wilsonActionZero circleRep β
        ((splitEquiv halfLinks).symm (y, u))) : ℝ) : ℂ)
      = ∑' n : ↥(zeroFinset (N := N)) → ℤ,
          ((wR β n : ℝ) : ℂ) * ((monoAY n y * monoBU n u : Circle) : ℂ) := by
  set U := (splitEquiv halfLinks).symm (y, u) with hU
  have h1 : wilsonActionZero circleRep β U
      = β * ∑ p ∈ zeroFinset,
          (1 - ((plaquette (torusShift N) U p.1 p.2.1 p.2.2
            : Circle) : ℂ).re) := by
    unfold wilsonActionZero
    rw [← zeroFinset_eq]
    exact congrArg _ (Finset.sum_congr rfl fun p _ =>
      plaquetteDensity_circleRep U p.1 p.2.1 p.2.2)
  have h2 : Real.exp (- wilsonActionZero circleRep β U)
      = ∏ p ∈ zeroFinset, (Real.exp (-β)
          * Real.exp (β * ((plaquette (torusShift N) U p.1 p.2.1 p.2.2
            : Circle) : ℂ).re)) := by
    rw [h1, Finset.mul_sum, ← Finset.sum_neg_distrib]
    rw [show (∑ p ∈ zeroFinset, - (β
        * (1 - ((plaquette (torusShift N) U p.1 p.2.1 p.2.2
            : Circle) : ℂ).re)))
        = ∑ p ∈ zeroFinset, (-β
          + β * ((plaquette (torusShift N) U p.1 p.2.1 p.2.2
            : Circle) : ℂ).re) from
      Finset.sum_congr rfl fun p _ => by ring, Real.exp_sum]
    exact Finset.prod_congr rfl fun p _ => Real.exp_add _ _
  have h4 : ∀ p ∈ zeroFinset,
      ((Real.exp (-β) * Real.exp (β * ((plaquette (torusShift N) U
          p.1 p.2.1 p.2.2 : Circle) : ℂ).re) : ℝ) : ℂ)
        = ∑' m : ℤ, ((Real.exp (-β) * besselI β m : ℝ) : ℂ)
            * ((plaquette (torusShift N) U p.1 p.2.1 p.2.2
              : Circle) : ℂ) ^ m := by
    intro p _
    rw [Complex.ofReal_mul, fourier_exp_circle, ← tsum_mul_left]
    exact tsum_congr fun m => by rw [Complex.ofReal_mul, mul_assoc]
  rw [h2, coe_prod_real, Finset.prod_congr rfl h4,
    ← tsum_prod_subtype zeroFinset
      (fun q m => ((Real.exp (-β) * besselI β m : ℝ) : ℂ)
        * ((plaquette (torusShift N) U q.1 q.2.1 q.2.2
          : Circle) : ℂ) ^ m)
      (fun a _ => summable_fourier_factor β _)
      (fun a _ => summable_norm_fourier_factor β _)]
  refine tsum_congr fun n => ?_
  have hA : ∏ p : ↥(zeroFinset (N := N)),
        ((Real.exp (-β) * besselI β (n p) : ℝ) : ℂ)
      = ((wR β n : ℝ) : ℂ) :=
    (coe_prod_real Finset.univ _).symm
  have hB : ∏ p : ↥(zeroFinset (N := N)),
        ((plaquette (torusShift N) U p.1.1 p.1.2.1 p.1.2.2
          : Circle) : ℂ) ^ (n p)
      = ((monoAY n y * monoBU n u : Circle) : ℂ) := by
    rw [Finset.prod_congr rfl (fun p _ => (coe_zpow_circle _ _).symm),
      ← coe_prod_circle, plaquette_prod hN n y u]
  exact Finset.prod_mul_distrib.trans (congrArg₂ _ hA hB)

end CircleFeatures

section CircleGramIdentity

variable {N : ℕ} [NeZero N]

/-- Conjugation of an inverted circle value under the coercion. -/
theorem starRingEnd_coe_inv (z : Circle) :
    (starRingEnd ℂ) ((z⁻¹ : Circle) : ℂ) = ((z : Circle) : ℂ) := by
  rw [← Circle.coe_inv_eq_conj, inv_inv]

/-- **The integrated Gram identity for the U(1) Wilson weight**
(even `N`, every real `β` for the identity; the features are
square-summable at `β ≥ 0` where the weights are nonnegative):
the crossing Boltzmann factor, times the two half-action factors,
is a convergent Gram series over crossing-plaquette exponent
vectors. -/
theorem gram_identity_circle (hN : Even N) (hβ : 0 ≤ β)
    (y : ↥(halfLinks (N := N)) → Circle)
    (u : ↥(negLinks (N := N)) → Circle) :
    ((Real.exp (- wilsonAction (torusShift N) circleRep β
        ((splitEquiv halfLinks).symm (y, u))) : ℝ) : ℂ)
      = ∑' n : ↥(zeroFinset (N := N)) → ℤ,
          (starRingEnd ℂ) (featB hN β n u) * featA β n y := by
  have hsplit : wilsonAction (torusShift N) circleRep β
        ((splitEquiv halfLinks).symm (y, u))
      = halfActionP circleRep β (restrictPos y)
        + halfActionP circleRep β (mirrorP hN u)
        + wilsonActionZero circleRep β
            ((splitEquiv halfLinks).symm (y, u)) :=
    wilsonAction_split_half circleRep hN β (y, u)
  have hexp : Real.exp (-(halfActionP circleRep β (restrictPos y)
        + halfActionP circleRep β (mirrorP hN u)
        + wilsonActionZero circleRep β
            ((splitEquiv halfLinks).symm (y, u))))
      = (Real.exp (- halfActionP circleRep β (restrictPos y))
        * Real.exp (- halfActionP circleRep β (mirrorP hN u)))
        * Real.exp (- wilsonActionZero circleRep β
            ((splitEquiv halfLinks).symm (y, u))) := by
    rw [show -(halfActionP circleRep β (restrictPos y)
        + halfActionP circleRep β (mirrorP hN u)
        + wilsonActionZero circleRep β
            ((splitEquiv halfLinks).symm (y, u)))
        = (- halfActionP circleRep β (restrictPos y)
          + - halfActionP circleRep β (mirrorP hN u))
          + - wilsonActionZero circleRep β
              ((splitEquiv halfLinks).symm (y, u)) by ring,
      Real.exp_add, Real.exp_add]
  rw [hsplit, hexp, Complex.ofReal_mul,
    exp_neg_zeroAction_tsum hN β y u, ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  set ea := Real.exp (- halfActionP circleRep β (restrictPos y)) with hea
  set eb := Real.exp (- halfActionP circleRep β (mirrorP hN u)) with heb
  set w := wR β n with hw
  set s := Real.sqrt w with hs
  set AY := monoAY n y with hAY
  set BU := monoBU n u with hBU
  have hsq : s * s = w := Real.mul_self_sqrt (wR_nonneg hβ n)
  have hrealR : (eb * s) * (ea * s) = (ea * eb) * w := by
    rw [show (eb * s) * (ea * s) = (ea * eb) * (s * s) by ring, hsq]
  have hreal : ((eb * s : ℝ) : ℂ) * ((ea * s : ℝ) : ℂ)
      = ((ea * eb : ℝ) : ℂ) * ((w : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, hrealR]
  have hconj : (starRingEnd ℂ) (featB hN β n u)
      = ((eb * s : ℝ) : ℂ) * ((BU : Circle) : ℂ) := by
    have hfull : (starRingEnd ℂ) (featB hN β n u)
        = ((Real.exp (- halfActionP circleRep β (mirrorP hN u))
            * Real.sqrt (wR β n) : ℝ) : ℂ)
          * ((monoBU n u : Circle) : ℂ) := by
      unfold featB
      rw [map_mul, Complex.conj_ofReal, starRingEnd_coe_inv]
    exact hfull
  calc ((ea * eb : ℝ) : ℂ) * (((w : ℝ) : ℂ) * ((AY * BU : Circle) : ℂ))
      = (((ea * eb : ℝ) : ℂ) * ((w : ℝ) : ℂ))
          * (((AY : Circle) : ℂ) * ((BU : Circle) : ℂ)) := by
        rw [Circle.coe_mul]; ring
    _ = (((eb * s : ℝ) : ℂ) * ((ea * s : ℝ) : ℂ))
          * (((AY : Circle) : ℂ) * ((BU : Circle) : ℂ)) := by
        rw [← hreal]
    _ = (starRingEnd ℂ) (featB hN β n u) * featA β n y := by
        rw [hconj]
        show (((eb * s : ℝ) : ℂ) * ((ea * s : ℝ) : ℂ))
            * (((AY : Circle) : ℂ) * ((BU : Circle) : ℂ))
          = (((eb * s : ℝ) : ℂ) * ((BU : Circle) : ℂ))
            * (((ea * s : ℝ) : ℂ) * ((AY : Circle) : ℂ))
        ring

end CircleGramIdentity

section CircleMarginals

variable {N : ℕ} [NeZero N]

/-- The plane coordinates inside a finset of links: the subtype
elements whose underlying link is a plane link. -/
def planeCoordsIn (s : Finset (Link (Fin 4 → ZMod N))) :
    Finset ↥s :=
  Finset.univ.filter (fun ℓ => ℓ.1 ∈ planeLinks)

/-- Extension of a plane-coordinate configuration by `1`. -/
noncomputable def extCoord {s : Finset (Link (Fin 4 → ZMod N))}
    (T : Finset ↥s) (g : ↥T → Circle) : ↥s → Circle :=
  fun ℓ => if h : ℓ ∈ T then g ⟨ℓ, h⟩ else 1

theorem extCoord_apply {s : Finset (Link (Fin 4 → ZMod N))}
    {T : Finset ↥s} (g : ↥T → Circle) {ℓ : ↥s} (hℓ : ℓ ∈ T) :
    extCoord T g ℓ = g ⟨ℓ, hℓ⟩ := dif_pos hℓ

/-- The strict coordinates of the closed half. -/
def strictCoords : Finset ↥(halfLinks (N := N)) :=
  Finset.univ.filter (fun ℓ => ℓ.1 ∈ posLinks)

theorem planeCoordsIn_halfLinks_eq :
    planeCoordsIn (halfLinks (N := N)) = strictCoordsᶜ := by
  ext ℓ
  have hval : (ℓ.1.1 0).val < N / 2 := mem_halfLinks.mp ℓ.2
  constructor
  · intro h
    have hpl : ℓ.1 ∈ planeLinks := (Finset.mem_filter.mp h).2
    rw [Finset.mem_compl]
    intro hs
    have hpos : ℓ.1 ∈ posLinks := (Finset.mem_filter.mp hs).2
    exact (mem_posLinks.mp hpos).2 (mem_planeLinks.mp hpl)
  · intro h
    have hnpos : ℓ.1 ∉ posLinks := by
      intro hpos
      exact (Finset.mem_compl.mp h)
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpos⟩)
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    rw [mem_planeLinks]
    by_contra hne
    exact hnpos (mem_posLinks.mpr ⟨hval, hne⟩)

/-- The strict coordinates of the negative half (the non-plane
links). -/
def strictCoordsN : Finset ↥(negLinks (N := N)) :=
  Finset.univ.filter (fun ℓ => ℓ.1 ∉ planeLinks)

theorem planeCoordsIn_negLinks_eq :
    planeCoordsIn (negLinks (N := N)) = strictCoordsNᶜ := by
  ext ℓ
  simp [planeCoordsIn, strictCoordsN]

/-- **The fiber identity**: the monomial of one link-family over
the crossing plaquettes, read through the plane-coordinate
extension, is the coordinate monomial whose exponents are the
fiber sums. -/
theorem fiber_single {s : Finset (Link (Fin 4 → ZMod N))}
    (ext : (↥s → Circle) → Config (Fin 4 → ZMod N) Circle)
    (hext : ∀ (w : ↥s → Circle) {ℓ : Link (Fin 4 → ZMod N)}
      (hℓ : ℓ ∈ s), ext w ℓ = w ⟨ℓ, hℓ⟩)
    (hN : Even N) (v₀ : ℕ)
    (φ : (Fin 4 → ZMod N) × Fin 4 × Fin 4 → Link (Fin 4 → ZMod N))
    (hφ : ∀ (p : (Fin 4 → ZMod N) × Fin 4 × Fin 4)
      (hp : p ∈ zeroFinset),
      ((p.1 0).val = v₀ → φ p ∈ s ∧ φ p ∈ planeLinks)
        ∧ ((p.1 0).val ≠ v₀ → φ p ∉ s))
    (n : ↥(zeroFinset (N := N)) → ℤ)
    (g : ↥(planeCoordsIn s) → Circle) :
    ∏ p : ↥(zeroFinset (N := N)),
        ((if (p.1.1 0).val = v₀
          then ext (extCoord (planeCoordsIn s) g) (φ p.1)
          else 1)) ^ (n p)
      = ∏ ℓ : ↥(planeCoordsIn s), (g ℓ)
          ^ (∑ p : ↥(zeroFinset (N := N)),
              (if ℓ.1.1 = φ p.1 then n p else 0)) := by
  classical
  have step1 : ∀ ℓ : ↥(planeCoordsIn s),
      (g ℓ) ^ (∑ p : ↥(zeroFinset (N := N)),
          (if ℓ.1.1 = φ p.1 then n p else 0))
        = ∏ p : ↥(zeroFinset (N := N)),
            (if ℓ.1.1 = φ p.1 then (g ℓ) ^ (n p) else 1) := by
    intro ℓ
    rw [zpow_sum_prod]
    exact Finset.prod_congr rfl fun p _ => by
      split_ifs with h
      · rfl
      · rw [zpow_zero]
  rw [Finset.prod_congr rfl (fun ℓ _ => step1 ℓ), Finset.prod_comm]
  refine Finset.prod_congr rfl fun p _ => ?_
  by_cases hv : (p.1.1 0).val = v₀
  · obtain ⟨hφs, hφpl⟩ := (hφ p.1 p.2).1 hv
    set ℓ₀ : ↥(planeCoordsIn s) :=
      ⟨⟨φ p.1, hφs⟩, Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, hφpl⟩⟩ with hℓ₀
    have hfactor : ∏ ℓ : ↥(planeCoordsIn s),
          (if ℓ.1.1 = φ p.1 then (g ℓ) ^ (n p) else 1)
        = (g ℓ₀) ^ (n p) := by
      rw [Finset.prod_congr rfl (g := fun ℓ : ↥(planeCoordsIn s) =>
        (if ℓ = ℓ₀ then (g ℓ) ^ (n p) else 1)) fun ℓ _ => by
        by_cases hc : ℓ.1.1 = φ p.1
        · rw [if_pos hc, if_pos (Subtype.ext (Subtype.ext hc))]
        · rw [if_neg hc,
            if_neg (fun h => hc (congrArg
              (fun m : ↥(planeCoordsIn s) => m.1.1) h))],
        Finset.prod_ite_eq']
      exact if_pos (Finset.mem_univ ℓ₀)
    have hval0 : ext (extCoord (planeCoordsIn s) g) (φ p.1) = g ℓ₀ :=
      (hext _ hφs).trans (extCoord_apply _
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hφpl⟩))
    rw [hfactor, if_pos hv, hval0]
  · have hφns : φ p.1 ∉ s := (hφ p.1 p.2).2 hv
    have hfactor : ∏ ℓ : ↥(planeCoordsIn s),
          (if ℓ.1.1 = φ p.1 then (g ℓ) ^ (n p) else 1) = 1 := by
      refine Finset.prod_eq_one fun ℓ _ => ?_
      rw [if_neg]
      intro hc
      exact hφns (hc ▸ ℓ.1.2)
    rw [hfactor, if_neg hv, one_zpow]

end CircleMarginals

section CircleMarginals2

variable {N : ℕ} [NeZero N]

/-- The exponent of a plane coordinate of the closed half in the
stratum monomial: `A`-link contributions minus `C`-link
contributions over the crossing plaquettes. -/
def E₀ (n : ↥(zeroFinset (N := N)) → ℤ)
    (ℓ : ↥(planeCoordsIn (halfLinks (N := N)))) : ℤ :=
  (∑ p : ↥(zeroFinset (N := N)),
      (if ℓ.1.1 = linkA p.1 then n p else 0))
    - (∑ p : ↥(zeroFinset (N := N)),
        (if ℓ.1.1 = linkC p.1 then n p else 0))

/-- The exponent of a plane coordinate of the negative half. -/
def E₁ (n : ↥(zeroFinset (N := N)) → ℤ)
    (ℓ : ↥(planeCoordsIn (negLinks (N := N)))) : ℤ :=
  (∑ p : ↥(zeroFinset (N := N)),
      (if ℓ.1.1 = linkA p.1 then n p else 0))
    - (∑ p : ↥(zeroFinset (N := N)),
        (if ℓ.1.1 = linkC p.1 then n p else 0))

/-- The marginal weight on the closed-half side: `1` if all plane
exponents vanish, else `0`. -/
def dA (n : ↥(zeroFinset (N := N)) → ℤ) : ℝ :=
  ∏ ℓ : ↥(planeCoordsIn (halfLinks (N := N))),
    (if E₀ n ℓ = 0 then (1 : ℝ) else 0)

/-- The marginal weight on the negative side. -/
def dB (n : ↥(zeroFinset (N := N)) → ℤ) : ℝ :=
  ∏ ℓ : ↥(planeCoordsIn (negLinks (N := N))),
    (if E₁ n ℓ = 0 then (1 : ℝ) else 0)

theorem dA_nonneg (n : ↥(zeroFinset (N := N)) → ℤ) : 0 ≤ dA n :=
  Finset.prod_nonneg fun ℓ _ => by split_ifs <;> norm_num

theorem dB_nonneg (n : ↥(zeroFinset (N := N)) → ℤ) : 0 ≤ dB n :=
  Finset.prod_nonneg fun ℓ _ => by split_ifs <;> norm_num

/-- Restriction of a closed-half configuration to its plane
coordinates. -/
def restrictPlaneH (y : ↥(halfLinks (N := N)) → Circle) :
    ↥(planeCoordsIn (halfLinks (N := N))) → Circle :=
  fun ℓ => y ℓ.1

/-- Restriction of a negative-half configuration to its plane
coordinates. -/
def restrictPlaneN (u : ↥(negLinks (N := N)) → Circle) :
    ↥(planeCoordsIn (negLinks (N := N))) → Circle :=
  fun ℓ => u ℓ.1

theorem hφA (hN : Even N)
    (p : (Fin 4 → ZMod N) × Fin 4 × Fin 4) (hp : p ∈ zeroFinset) :
    ((p.1 0).val = N / 2 - 1
        → linkA p ∈ halfLinks ∧ linkA p ∈ planeLinks)
      ∧ ((p.1 0).val ≠ N / 2 - 1 → linkA p ∉ halfLinks) := by
  rcases zero_link_pattern hN p hp with
    ⟨hval, hAhalf, hAplane, -, -, -, -⟩
    | ⟨hval, hAneg, -, -, -, -, -⟩
  · exact ⟨fun _ => ⟨hAhalf, hAplane⟩, fun hne => absurd hval hne⟩
  · refine ⟨fun hv => ?_, fun _ => Finset.mem_compl.mp hAneg⟩
    obtain ⟨r, hr⟩ := hN
    have hN0 : N ≠ 0 := NeZero.ne N
    omega

theorem hφC (hN : Even N)
    (p : (Fin 4 → ZMod N) × Fin 4 × Fin 4) (hp : p ∈ zeroFinset) :
    ((p.1 0).val = N / 2 - 1
        → linkC p ∈ halfLinks ∧ linkC p ∈ planeLinks)
      ∧ ((p.1 0).val ≠ N / 2 - 1 → linkC p ∉ halfLinks) := by
  rcases zero_link_pattern hN p hp with
    ⟨hval, -, -, hChalf, hCplane, -, -⟩
    | ⟨hval, -, -, hCneg, -, -, -⟩
  · exact ⟨fun _ => ⟨hChalf, hCplane⟩, fun hne => absurd hval hne⟩
  · refine ⟨fun hv => ?_, fun _ => Finset.mem_compl.mp hCneg⟩
    obtain ⟨r, hr⟩ := hN
    have hN0 : N ≠ 0 := NeZero.ne N
    omega

theorem hφA' (hN : Even N)
    (p : (Fin 4 → ZMod N) × Fin 4 × Fin 4) (hp : p ∈ zeroFinset) :
    ((p.1 0).val = N - 1
        → linkA p ∈ negLinks ∧ linkA p ∈ planeLinks)
      ∧ ((p.1 0).val ≠ N - 1 → linkA p ∉ negLinks) := by
  rcases zero_link_pattern hN p hp with
    ⟨hval, hAhalf, -, -, -, -, -⟩
    | ⟨hval, hAneg, hAplane, -, -, -, -⟩
  · refine ⟨fun hv => ?_, fun _ h => (Finset.mem_compl.mp h) hAhalf⟩
    obtain ⟨r, hr⟩ := hN
    have hN0 : N ≠ 0 := NeZero.ne N
    omega
  · exact ⟨fun _ => ⟨hAneg, hAplane⟩, fun hne => absurd hval hne⟩

theorem hφC' (hN : Even N)
    (p : (Fin 4 → ZMod N) × Fin 4 × Fin 4) (hp : p ∈ zeroFinset) :
    ((p.1 0).val = N - 1
        → linkC p ∈ negLinks ∧ linkC p ∈ planeLinks)
      ∧ ((p.1 0).val ≠ N - 1 → linkC p ∉ negLinks) := by
  rcases zero_link_pattern hN p hp with
    ⟨hval, -, -, hChalf, -, -, -⟩
    | ⟨hval, -, -, hCneg, hCplane, -, -⟩
  · refine ⟨fun hv => ?_, fun _ h => (Finset.mem_compl.mp h) hChalf⟩
    obtain ⟨r, hr⟩ := hN
    have hN0 : N ≠ 0 := NeZero.ne N
    omega
  · exact ⟨fun _ => ⟨hCneg, hCplane⟩, fun hne => absurd hval hne⟩


/-- **The stratum monomial as a coordinate monomial** (closed-half
side): the plane-coordinate exponents are the fiber sums `E₀`. -/
theorem stratY_monomial (hN : Even N) (n : ↥(zeroFinset (N := N)) → ℤ)
    (g : ↥(planeCoordsIn (halfLinks (N := N))) → Circle) :
    stratY n (extCoord (planeCoordsIn (halfLinks (N := N))) g)
      = ∏ ℓ : ↥(planeCoordsIn (halfLinks (N := N))),
          (g ℓ) ^ (E₀ n ℓ) := by
  have hfac : ∀ p : ↥(zeroFinset (N := N)),
      stratFactorY p.1 (extCoord (planeCoordsIn (halfLinks (N := N))) g)
        = (if (p.1.1 0).val = N / 2 - 1
            then extHalf (extCoord (planeCoordsIn (halfLinks (N := N))) g)
              (linkA p.1) else 1)
          * ((if (p.1.1 0).val = N / 2 - 1
            then extHalf (extCoord (planeCoordsIn (halfLinks (N := N))) g)
              (linkC p.1) else 1))⁻¹ := by
    intro p
    unfold stratFactorY
    by_cases hv : (p.1.1 0).val = N / 2 - 1
    · rw [if_pos hv, if_pos hv, if_pos hv]
    · rw [if_neg hv, if_neg hv, if_neg hv, inv_one, mul_one]
  unfold stratY
  rw [Finset.prod_congr rfl (fun p _ => congrArg (· ^ (n p)) (hfac p)),
    Finset.prod_congr rfl (fun p _ => by rw [mul_zpow, inv_zpow]),
    Finset.prod_mul_distrib, Finset.prod_inv_distrib,
    fiber_single extHalf (fun w _ℓ hℓ => extHalf_apply hℓ) hN (N / 2 - 1)
      linkA (fun p hp => hφA hN p hp) n g,
    fiber_single extHalf (fun w _ℓ hℓ => extHalf_apply hℓ) hN (N / 2 - 1)
      linkC (fun p hp => hφC hN p hp) n g,
    ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun ℓ _ => ?_
  show (g ℓ) ^ (∑ p : ↥(zeroFinset (N := N)),
        (if ℓ.1.1 = linkA p.1 then n p else 0))
      * ((g ℓ) ^ (∑ p : ↥(zeroFinset (N := N)),
        (if ℓ.1.1 = linkC p.1 then n p else 0)))⁻¹
    = (g ℓ) ^ ((∑ p : ↥(zeroFinset (N := N)),
        (if ℓ.1.1 = linkA p.1 then n p else 0))
      - (∑ p : ↥(zeroFinset (N := N)),
        (if ℓ.1.1 = linkC p.1 then n p else 0)))
  rw [← zpow_sub]

/-- **The stratum monomial as a coordinate monomial** (negative
side). -/
theorem stratU_monomial (hN : Even N) (n : ↥(zeroFinset (N := N)) → ℤ)
    (g : ↥(planeCoordsIn (negLinks (N := N))) → Circle) :
    stratU n (extCoord (planeCoordsIn (negLinks (N := N))) g)
      = ∏ ℓ : ↥(planeCoordsIn (negLinks (N := N))),
          (g ℓ) ^ (E₁ n ℓ) := by
  have hfac : ∀ p : ↥(zeroFinset (N := N)),
      stratFactorU p.1 (extCoord (planeCoordsIn (negLinks (N := N))) g)
        = (if (p.1.1 0).val = N - 1
            then extNeg (extCoord (planeCoordsIn (negLinks (N := N))) g)
              (linkA p.1) else 1)
          * ((if (p.1.1 0).val = N - 1
            then extNeg (extCoord (planeCoordsIn (negLinks (N := N))) g)
              (linkC p.1) else 1))⁻¹ := by
    intro p
    obtain ⟨-, hval⟩ :=
      (isZeroPlaq_iff hN p.1 (Finset.mem_filter.mp p.2).1).mp
        (Finset.mem_filter.mp p.2).2
    unfold stratFactorU
    by_cases hv : (p.1.1 0).val = N - 1
    · have hv' : (p.1.1 0).val ≠ N / 2 - 1 := by
        obtain ⟨r, hr⟩ := hN
        have hN0 : N ≠ 0 := NeZero.ne N
        omega
      rw [if_neg hv', if_pos hv, if_pos hv]
    · have hv' : (p.1.1 0).val = N / 2 - 1 := by
        rcases hval with h1 | h1
        · exact h1
        · exact absurd h1 hv
      rw [if_pos hv', if_neg hv, if_neg hv, inv_one, mul_one]
  unfold stratU
  rw [Finset.prod_congr rfl (fun p _ => congrArg (· ^ (n p)) (hfac p)),
    Finset.prod_congr rfl (fun p _ => by rw [mul_zpow, inv_zpow]),
    Finset.prod_mul_distrib, Finset.prod_inv_distrib,
    fiber_single extNeg (fun w _ℓ hℓ => extNeg_apply hℓ) hN (N - 1)
      linkA (fun p hp => hφA' hN p hp) n g,
    fiber_single extNeg (fun w _ℓ hℓ => extNeg_apply hℓ) hN (N - 1)
      linkC (fun p hp => hφC' hN p hp) n g,
    ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun ℓ _ => ?_
  show (g ℓ) ^ (∑ p : ↥(zeroFinset (N := N)),
        (if ℓ.1.1 = linkA p.1 then n p else 0))
      * ((g ℓ) ^ (∑ p : ↥(zeroFinset (N := N)),
        (if ℓ.1.1 = linkC p.1 then n p else 0)))⁻¹
    = (g ℓ) ^ ((∑ p : ↥(zeroFinset (N := N)),
        (if ℓ.1.1 = linkA p.1 then n p else 0))
      - (∑ p : ↥(zeroFinset (N := N)),
        (if ℓ.1.1 = linkC p.1 then n p else 0)))
  rw [← zpow_sub]

/-- The stratum monomial of a closed-half configuration depends
only on its plane coordinates. -/
theorem stratY_eq (hN : Even N) (n : ↥(zeroFinset (N := N)) → ℤ)
    (y : ↥(halfLinks (N := N)) → Circle) :
    stratY n y
      = stratY n (extCoord (planeCoordsIn (halfLinks (N := N)))
          (restrictPlaneH y)) := by
  unfold stratY
  refine Finset.prod_congr rfl fun p _ => congrArg (· ^ (n p)) ?_
  rcases zero_link_pattern hN p.1 p.2 with
    ⟨hv, hAhalf, hAplane, hChalf, hCplane, -, -⟩
    | ⟨hv, -, -, -, -, -, -⟩
  · have hA : extHalf (extCoord (planeCoordsIn (halfLinks (N := N)))
          (restrictPlaneH y)) (linkA p.1)
        = extHalf y (linkA p.1) :=
      (extHalf_apply hAhalf).trans
        ((extCoord_apply _ (Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, hAplane⟩)).trans
          (extHalf_apply hAhalf).symm)
    have hC : extHalf (extCoord (planeCoordsIn (halfLinks (N := N)))
          (restrictPlaneH y)) (linkC p.1)
        = extHalf y (linkC p.1) :=
      (extHalf_apply hChalf).trans
        ((extCoord_apply _ (Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, hCplane⟩)).trans
          (extHalf_apply hChalf).symm)
    unfold stratFactorY
    rw [if_pos hv, if_pos hv, hA, hC]
  · have hne : (p.1.1 0).val ≠ N / 2 - 1 := by
      obtain ⟨r, hr⟩ := hN
      have hN0 : N ≠ 0 := NeZero.ne N
      omega
    unfold stratFactorY
    rw [if_neg hne, if_neg hne]

/-- The stratum monomial of a negative-half configuration depends
only on its plane coordinates. -/
theorem stratU_eq (hN : Even N) (n : ↥(zeroFinset (N := N)) → ℤ)
    (u : ↥(negLinks (N := N)) → Circle) :
    stratU n u
      = stratU n (extCoord (planeCoordsIn (negLinks (N := N)))
          (restrictPlaneN u)) := by
  unfold stratU
  refine Finset.prod_congr rfl fun p _ => congrArg (· ^ (n p)) ?_
  rcases zero_link_pattern hN p.1 p.2 with
    ⟨hv, -, -, -, -, -, -⟩
    | ⟨hv, hAneg, hAplane, hCneg, hCplane, -, -⟩
  · unfold stratFactorU
    rw [if_pos hv, if_pos hv]
  · have hA : extNeg (extCoord (planeCoordsIn (negLinks (N := N)))
          (restrictPlaneN u)) (linkA p.1)
        = extNeg u (linkA p.1) :=
      (extNeg_apply hAneg).trans
        ((extCoord_apply _ (Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, hAplane⟩)).trans
          (extNeg_apply hAneg).symm)
    have hC : extNeg (extCoord (planeCoordsIn (negLinks (N := N)))
          (restrictPlaneN u)) (linkC p.1)
        = extNeg u (linkC p.1) :=
      (extNeg_apply hCneg).trans
        ((extCoord_apply _ (Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, hCplane⟩)).trans
          (extNeg_apply hCneg).symm)
    have hne : (p.1.1 0).val ≠ N / 2 - 1 := by
      obtain ⟨r, hr⟩ := hN
      have hN0 : N ≠ 0 := NeZero.ne N
      omega
    unfold stratFactorU
    rw [if_neg hne, if_neg hne, hA, hC]

end CircleMarginals2

variable {N : ℕ} [NeZero N]

/-! ## §D5 Marginal integrals (Stage 2) -/

/-- The positive restriction of a closed-half configuration,
read off its strict (non-plane) coordinates. -/
noncomputable def posOfStrict
    (g₀ : ↥((planeCoordsIn (halfLinks (N := N)))ᶜ) → Circle) :
    ↥(posLinks (N := N)) → Circle :=
  fun ℓ => g₀ ⟨⟨ℓ.1, posLinks_subset_halfLinks ℓ.2⟩,
    Finset.mem_compl.mpr (fun hmem =>
      (mem_posLinks.mp ℓ.2).2
        (mem_planeLinks.mp (Finset.mem_filter.mp hmem).2))⟩

theorem restrictPos_eq (y : ↥(halfLinks (N := N)) → Circle) :
    restrictPos y = posOfStrict
      (fun ℓ : ↥((planeCoordsIn (halfLinks (N := N)))ᶜ) => y ℓ.1) :=
  rfl

/-- The mirrored positive configuration, read off the strict
(non-plane) coordinates of a negative-half configuration. -/
noncomputable def mirrorOfStrict (hN : Even N)
    (g₀ : ↥((planeCoordsIn (negLinks (N := N)))ᶜ) → Circle) :
    ↥(posLinks (N := N)) → Circle :=
  fun ℓ => if ℓ.1.2 = 0
    then (g₀ ⟨⟨reflLink ℓ.1, reflLink_mem_negLinks hN ℓ.2⟩,
      Finset.mem_compl.mpr (fun hmem =>
        (mem_posLinks.mp ℓ.2).2
          ((mem_planeLinks.mp (Finset.mem_filter.mp hmem).2).symm.trans
            (reflLink_involutive ℓ.1)))⟩)⁻¹
    else g₀ ⟨⟨reflLink ℓ.1, reflLink_mem_negLinks hN ℓ.2⟩,
      Finset.mem_compl.mpr (fun hmem =>
        (mem_posLinks.mp ℓ.2).2
          ((mem_planeLinks.mp (Finset.mem_filter.mp hmem).2).symm.trans
            (reflLink_involutive ℓ.1)))⟩

theorem mirrorP_eq (hN : Even N) (u : ↥(negLinks (N := N)) → Circle) :
    mirrorP hN u = mirrorOfStrict hN
      (fun ℓ : ↥((planeCoordsIn (negLinks (N := N)))ᶜ) => u ℓ.1) := by
  funext ℓ
  show (if ℓ.1.2 = 0
      then (u ⟨reflLink ℓ.1, reflLink_mem_negLinks hN ℓ.2⟩)⁻¹
      else u ⟨reflLink ℓ.1, reflLink_mem_negLinks hN ℓ.2⟩) = _
  unfold mirrorOfStrict
  split_ifs <;> rfl

/-- **Closed-half integrand factorization.** -/
theorem featA_factor (hN : Even N) (β : ℝ)
    (n : ↥(zeroFinset (N := N)) → ℤ)
    (f : (↥(posLinks (N := N)) → Circle) → ℂ)
    (y : ↥(halfLinks (N := N)) → Circle) :
    featA β n y * f (restrictPos y)
      = (featXi β n (restrictPos y) * f (restrictPos y))
        * ((stratY n y : Circle) : ℂ) := by
  unfold featA featXi
  rw [monoAY_factor hN n y, Circle.coe_mul]
  set ea := ((Real.exp (- halfActionP circleRep β (restrictPos y))
    * Real.sqrt (wR β n) : ℝ) : ℂ)
  set mp := ((mPosZ n (restrictPos y) : Circle) : ℂ)
  set sy := ((stratY n y : Circle) : ℂ)
  ring

/-- **Negative-half integrand factorization.** -/
theorem featB_factor (hN : Even N) (β : ℝ)
    (n : ↥(zeroFinset (N := N)) → ℤ)
    (f : (↥(posLinks (N := N)) → Circle) → ℂ)
    (u : ↥(negLinks (N := N)) → Circle) :
    featB hN β n u * f (mirrorP hN u)
      = (((stratU n u : Circle) : ℂ))⁻¹
        * (featXi β n (mirrorP hN u) * f (mirrorP hN u)) := by
  have hmono : (monoBU n u)⁻¹
      = mPosZ n (mirrorP hN u) * (stratU n u)⁻¹ := by
    rw [monoBU_factor hN n u, negFactorZ_prod n (mirrorP hN u)]
    group
    exact mul_comm _ _
  unfold featB featXi
  rw [hmono, Circle.coe_mul, Circle.coe_inv]
  set eb := ((Real.exp (- halfActionP circleRep β (mirrorP hN u))
    * Real.sqrt (wR β n) : ℝ) : ℂ)
  set mp := ((mPosZ n (mirrorP hN u) : Circle) : ℂ)
  set su := ((stratU n u : Circle) : ℂ)
  ring

/-- The plane-coordinate integral of the closed-half stratum
monomial is the `dA` selector. -/
theorem integral_stratY (hN : Even N)
    (n : ↥(zeroFinset (N := N)) → ℤ) :
    ∫ g₁ : ↥(planeCoordsIn (halfLinks (N := N))) → Circle,
        ((stratY n (extCoord (planeCoordsIn (halfLinks (N := N))) g₁)
          : Circle) : ℂ)
        ∂(Measure.pi fun _ : ↥(planeCoordsIn (halfLinks (N := N)))
          => haarProb Circle)
      = ((dA n : ℝ) : ℂ) := by
  have hprod : ∀ g₁ : ↥(planeCoordsIn (halfLinks (N := N))) → Circle,
      ((stratY n (extCoord (planeCoordsIn (halfLinks (N := N))) g₁)
          : Circle) : ℂ)
        = ∏ ℓ : ↥(planeCoordsIn (halfLinks (N := N))),
            ((g₁ ℓ : ℂ)) ^ (E₀ n ℓ) := by
    intro g₁
    rw [stratY_monomial hN n g₁, coe_prod_circle]
    exact Finset.prod_congr rfl fun ℓ _ => (coe_zpow_circle _ _).symm
  rw [integral_congr_ae (ae_of_all _ hprod),
    MeasureTheory.integral_fintype_prod_eq_prod
      (fun (ℓ : ↥(planeCoordsIn (halfLinks (N := N)))) (w : Circle)
        => ((w : ℂ)) ^ (E₀ n ℓ))]
  have hfac : ∀ ℓ : ↥(planeCoordsIn (halfLinks (N := N))),
      ∫ w : Circle, ((w : ℂ)) ^ (E₀ n ℓ) ∂(haarProb Circle)
        = ((if E₀ n ℓ = 0 then (1 : ℝ) else 0 : ℝ) : ℂ) := by
    intro ℓ
    rw [integral_congr_ae
      (ae_of_all _ (fun w => (coe_zpow_circle w (E₀ n ℓ)).symm)),
      integral_circle_zpow_haarProb]
    by_cases hE : E₀ n ℓ = 0 <;> simp [hE]
  rw [Finset.prod_congr rfl (fun ℓ _ => hfac ℓ), ← coe_prod_real]
  rfl

/-- The plane-coordinate integral of the negative-half stratum
monomial's inverse is the `dB` selector. -/
theorem integral_stratU (hN : Even N)
    (n : ↥(zeroFinset (N := N)) → ℤ) :
    ∫ g₁ : ↥(planeCoordsIn (negLinks (N := N))) → Circle,
        (((stratU n (extCoord (planeCoordsIn (negLinks (N := N))) g₁)
          : Circle) : ℂ))⁻¹
        ∂(Measure.pi fun _ : ↥(planeCoordsIn (negLinks (N := N)))
          => haarProb Circle)
      = ((dB n : ℝ) : ℂ) := by
  have hprod : ∀ g₁ : ↥(planeCoordsIn (negLinks (N := N))) → Circle,
      (((stratU n (extCoord (planeCoordsIn (negLinks (N := N))) g₁)
          : Circle) : ℂ))⁻¹
        = ∏ ℓ : ↥(planeCoordsIn (negLinks (N := N))),
            ((g₁ ℓ : ℂ)) ^ (- E₁ n ℓ) := by
    intro g₁
    rw [stratU_monomial hN n g₁, coe_prod_circle,
      ← Finset.prod_inv_distrib]
    exact Finset.prod_congr rfl fun ℓ _ => by
      rw [coe_zpow_circle]; exact (zpow_neg _ _).symm
  rw [integral_congr_ae (ae_of_all _ hprod),
    MeasureTheory.integral_fintype_prod_eq_prod
      (fun (ℓ : ↥(planeCoordsIn (negLinks (N := N)))) (w : Circle)
        => ((w : ℂ)) ^ (- E₁ n ℓ))]
  have hfac : ∀ ℓ : ↥(planeCoordsIn (negLinks (N := N))),
      ∫ w : Circle, ((w : ℂ)) ^ (- E₁ n ℓ) ∂(haarProb Circle)
        = ((if E₁ n ℓ = 0 then (1 : ℝ) else 0 : ℝ) : ℂ) := by
    intro ℓ
    rw [integral_congr_ae
      (ae_of_all _ (fun w => (coe_zpow_circle w (- E₁ n ℓ)).symm)),
      integral_circle_zpow_haarProb]
    by_cases hE : E₁ n ℓ = 0
    · rw [if_pos (by rw [hE, neg_zero]), if_pos hE]; simp
    · rw [if_neg (fun h => hE (neg_eq_zero.mp h)), if_neg hE]; simp
  rw [Finset.prod_congr rfl (fun ℓ _ => hfac ℓ), ← coe_prod_real]
  rfl

/-- The strict-coordinate integral of the `G`-factor on the closed
half is its positive-half integral (via `integral_restrictPos`). -/
theorem integral_posOfStrict (hN : Even N)
    (G : (↥(posLinks (N := N)) → Circle) → ℂ) :
    ∫ g₀ : ↥((planeCoordsIn (halfLinks (N := N)))ᶜ) → Circle,
        G (posOfStrict g₀)
        ∂(Measure.pi fun _ : ↥((planeCoordsIn (halfLinks (N := N)))ᶜ)
          => haarProb Circle)
      = ∫ z : ↥(posLinks (N := N)) → Circle, G z
        ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => haarProb Circle) := by
  have hsplit := integral_pi_split_mul (μG := haarProb Circle)
    (s := planeCoordsIn (halfLinks (N := N)))
    (f := fun _ : ↥(planeCoordsIn (halfLinks (N := N))) → Circle
      => (1 : ℂ))
    (h := fun g₀ : ↥((planeCoordsIn (halfLinks (N := N)))ᶜ) → Circle
      => G (posOfStrict g₀))
  have hLHS : ∀ y : ↥(halfLinks (N := N)) → Circle,
      ((fun _ : ↥(planeCoordsIn (halfLinks (N := N))) → Circle
          => (1 : ℂ))
        (fun ℓ : ↥(planeCoordsIn (halfLinks (N := N))) => y ℓ.1))
        * ((fun g₀ : ↥((planeCoordsIn (halfLinks (N := N)))ᶜ)
            → Circle => G (posOfStrict g₀))
          (fun ℓ : ↥((planeCoordsIn (halfLinks (N := N)))ᶜ)
            => y ℓ.1))
        = G (restrictPos y) := by
    intro y
    rw [restrictPos_eq]; simp
  rw [integral_congr_ae (ae_of_all _ hLHS)] at hsplit
  rw [integral_const] at hsplit
  simp at hsplit
  rw [← hsplit, ← integral_restrictPos]

/-- The strict-coordinate integral of the `G`-factor on the negative
half is its positive-half integral (via `integral_mirrorP`). -/
theorem integral_mirrorOfStrict (hN : Even N)
    (G : (↥(posLinks (N := N)) → Circle) → ℂ) :
    ∫ g₀ : ↥((planeCoordsIn (negLinks (N := N)))ᶜ) → Circle,
        G (mirrorOfStrict hN g₀)
        ∂(Measure.pi fun _ : ↥((planeCoordsIn (negLinks (N := N)))ᶜ)
          => haarProb Circle)
      = ∫ z : ↥(posLinks (N := N)) → Circle, G z
        ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => haarProb Circle) := by
  have hsplit := integral_pi_split_mul (μG := haarProb Circle)
    (s := planeCoordsIn (negLinks (N := N)))
    (f := fun _ : ↥(planeCoordsIn (negLinks (N := N))) → Circle
      => (1 : ℂ))
    (h := fun g₀ : ↥((planeCoordsIn (negLinks (N := N)))ᶜ) → Circle
      => G (mirrorOfStrict hN g₀))
  have hLHS : ∀ u : ↥(negLinks (N := N)) → Circle,
      ((fun _ : ↥(planeCoordsIn (negLinks (N := N))) → Circle
          => (1 : ℂ))
        (fun ℓ : ↥(planeCoordsIn (negLinks (N := N))) => u ℓ.1))
        * ((fun g₀ : ↥((planeCoordsIn (negLinks (N := N)))ᶜ)
            → Circle => G (mirrorOfStrict hN g₀))
          (fun ℓ : ↥((planeCoordsIn (negLinks (N := N)))ᶜ)
            => u ℓ.1))
        = G (mirrorP hN u) := by
    intro u
    rw [mirrorP_eq]; simp
  rw [integral_congr_ae (ae_of_all _ hLHS)] at hsplit
  rw [integral_const] at hsplit
  simp at hsplit
  rw [← hsplit, ← integral_mirrorP (μG := haarProb Circle) hN G]

/-- **Closed-half marginal (the `dA` identity).** -/
theorem marginalA (hN : Even N) (β : ℝ)
    (n : ↥(zeroFinset (N := N)) → ℤ)
    (f : (↥(posLinks (N := N)) → Circle) → ℂ) :
    ∫ y : ↥(halfLinks (N := N)) → Circle,
        featA β n y * f (restrictPos y)
        ∂(Measure.pi fun _ : ↥(halfLinks (N := N)) => haarProb Circle)
      = ((dA n : ℝ) : ℂ)
        * ∫ z : ↥(posLinks (N := N)) → Circle,
            featXi β n z * f z
            ∂(Measure.pi fun _ : ↥(posLinks (N := N))
              => haarProb Circle) := by
  have hsplit := integral_pi_split_mul (μG := haarProb Circle)
    (s := planeCoordsIn (halfLinks (N := N)))
    (f := fun g₁ : ↥(planeCoordsIn (halfLinks (N := N))) → Circle
      => ((stratY n (extCoord (planeCoordsIn (halfLinks (N := N))) g₁)
          : Circle) : ℂ))
    (h := fun g₀ : ↥((planeCoordsIn (halfLinks (N := N)))ᶜ) → Circle
      => featXi β n (posOfStrict g₀) * f (posOfStrict g₀))
  have hLHS : ∀ y : ↥(halfLinks (N := N)) → Circle,
      ((fun g₁ : ↥(planeCoordsIn (halfLinks (N := N))) → Circle
          => ((stratY n
              (extCoord (planeCoordsIn (halfLinks (N := N))) g₁)
              : Circle) : ℂ))
        (fun ℓ : ↥(planeCoordsIn (halfLinks (N := N))) => y ℓ.1))
        * ((fun g₀ : ↥((planeCoordsIn (halfLinks (N := N)))ᶜ)
            → Circle
            => featXi β n (posOfStrict g₀) * f (posOfStrict g₀))
          (fun ℓ : ↥((planeCoordsIn (halfLinks (N := N)))ᶜ)
            => y ℓ.1))
        = featA β n y * f (restrictPos y) := by
    intro y
    have e1 : stratY n (extCoord (planeCoordsIn (halfLinks (N := N)))
        (fun ℓ : ↥(planeCoordsIn (halfLinks (N := N))) => y ℓ.1))
        = stratY n y := (stratY_eq hN n y).symm
    have e2 : posOfStrict
        (fun ℓ : ↥((planeCoordsIn (halfLinks (N := N)))ᶜ) => y ℓ.1)
        = restrictPos y := (restrictPos_eq y).symm
    show ((stratY n
        (extCoord (planeCoordsIn (halfLinks (N := N)))
          (fun ℓ : ↥(planeCoordsIn (halfLinks (N := N))) => y ℓ.1))
        : Circle) : ℂ)
        * (featXi β n (posOfStrict
            (fun ℓ : ↥((planeCoordsIn (halfLinks (N := N)))ᶜ)
              => y ℓ.1))
          * f (posOfStrict
            (fun ℓ : ↥((planeCoordsIn (halfLinks (N := N)))ᶜ)
              => y ℓ.1)))
      = featA β n y * f (restrictPos y)
    rw [e1, e2]
    exact (mul_comm _ _).trans (featA_factor hN β n f y).symm
  rw [integral_congr_ae (ae_of_all _ hLHS)] at hsplit
  rw [integral_stratY hN n,
    integral_posOfStrict hN (fun z => featXi β n z * f z)] at hsplit
  exact hsplit

/-- **Negative-half marginal (the `dB` identity).** -/
theorem marginalB (hN : Even N) (β : ℝ)
    (n : ↥(zeroFinset (N := N)) → ℤ)
    (f : (↥(posLinks (N := N)) → Circle) → ℂ) :
    ∫ u : ↥(negLinks (N := N)) → Circle,
        featB hN β n u * f (mirrorP hN u)
        ∂(Measure.pi fun _ : ↥(negLinks (N := N)) => haarProb Circle)
      = ((dB n : ℝ) : ℂ)
        * ∫ z : ↥(posLinks (N := N)) → Circle,
            featXi β n z * f z
            ∂(Measure.pi fun _ : ↥(posLinks (N := N))
              => haarProb Circle) := by
  have hsplit := integral_pi_split_mul (μG := haarProb Circle)
    (s := planeCoordsIn (negLinks (N := N)))
    (f := fun g₁ : ↥(planeCoordsIn (negLinks (N := N))) → Circle
      => (((stratU n
          (extCoord (planeCoordsIn (negLinks (N := N))) g₁)
          : Circle) : ℂ))⁻¹)
    (h := fun g₀ : ↥((planeCoordsIn (negLinks (N := N)))ᶜ) → Circle
      => featXi β n (mirrorOfStrict hN g₀) * f (mirrorOfStrict hN g₀))
  have hLHS : ∀ u : ↥(negLinks (N := N)) → Circle,
      ((fun g₁ : ↥(planeCoordsIn (negLinks (N := N))) → Circle
          => (((stratU n
              (extCoord (planeCoordsIn (negLinks (N := N))) g₁)
              : Circle) : ℂ))⁻¹)
        (fun ℓ : ↥(planeCoordsIn (negLinks (N := N))) => u ℓ.1))
        * ((fun g₀ : ↥((planeCoordsIn (negLinks (N := N)))ᶜ)
            → Circle
            => featXi β n (mirrorOfStrict hN g₀)
              * f (mirrorOfStrict hN g₀))
          (fun ℓ : ↥((planeCoordsIn (negLinks (N := N)))ᶜ)
            => u ℓ.1))
        = featB hN β n u * f (mirrorP hN u) := by
    intro u
    have e1 : stratU n (extCoord (planeCoordsIn (negLinks (N := N)))
        (fun ℓ : ↥(planeCoordsIn (negLinks (N := N))) => u ℓ.1))
        = stratU n u := (stratU_eq hN n u).symm
    have e2 : mirrorOfStrict hN
        (fun ℓ : ↥((planeCoordsIn (negLinks (N := N)))ᶜ) => u ℓ.1)
        = mirrorP hN u := (mirrorP_eq hN u).symm
    show (((stratU n
        (extCoord (planeCoordsIn (negLinks (N := N)))
          (fun ℓ : ↥(planeCoordsIn (negLinks (N := N))) => u ℓ.1))
        : Circle) : ℂ))⁻¹
        * (featXi β n (mirrorOfStrict hN
            (fun ℓ : ↥((planeCoordsIn (negLinks (N := N)))ᶜ)
              => u ℓ.1))
          * f (mirrorOfStrict hN
            (fun ℓ : ↥((planeCoordsIn (negLinks (N := N)))ᶜ)
              => u ℓ.1)))
      = featB hN β n u * f (mirrorP hN u)
    rw [e1, e2]
    exact (featB_factor hN β n f u).symm
  rw [integral_congr_ae (ae_of_all _ hLHS)] at hsplit
  rw [integral_stratU hN n,
    integral_mirrorOfStrict hN (fun z => featXi β n z * f z)] at hsplit
  exact hsplit

/-! ## §D6 Continuity, norm bounds, and the U(1) discharge
    (Stages 3–4) -/

/-- The coercion `Circle → ℂ` is continuous. -/
theorem circle_coe_continuous : Continuous fun z : Circle => ((z : ℂ)) := by
  fun_prop

/-- The coercion `ℝ → ℂ` is continuous. -/
theorem ofReal_continuous : Continuous fun r : ℝ => ((r : ℂ)) := by
  fun_prop

/-- `extendP` is continuous in the positive configuration. -/
theorem extendP_continuous :
    Continuous fun z : ↥(posLinks (N := N)) → Circle => extendP z := by
  refine continuous_pi fun ℓ => ?_
  by_cases hℓ : ℓ ∈ posLinks (N := N)
  · have e : (fun z : ↥(posLinks (N := N)) → Circle => extendP z ℓ)
        = fun z => z ⟨ℓ, hℓ⟩ :=
      funext fun z => extendP_apply hℓ
    rw [e]; exact continuous_apply _
  · have e : (fun z : ↥(posLinks (N := N)) → Circle => extendP z ℓ)
        = fun _ => (1 : Circle) :=
      funext fun z => dif_neg hℓ
    rw [e]; exact continuous_const

/-- The circle plaquette (coerced to `ℂ`) is continuous in the
configuration. -/
theorem plaquette_circle_continuous (x : Fin 4 → ZMod N) (μ ν : Fin 4) :
    Continuous fun U : Config (Fin 4 → ZMod N) Circle =>
      ((plaquette (torusShift N) U x μ ν : Circle) : ℂ) := by
  have hplaq : Continuous fun U : Config (Fin 4 → ZMod N) Circle =>
      plaquette (torusShift N) U x μ ν := by
    unfold plaquette
    fun_prop
  exact circle_coe_continuous.comp hplaq

/-- The half-action for the circle representation is continuous. -/
theorem halfActionP_circle_continuous (β : ℝ) :
    Continuous fun z : ↥(posLinks (N := N)) → Circle =>
      halfActionP circleRep β z := by
  have hterm : ∀ p ∈ plaqIndex.filter IsPosPlaq,
      Continuous fun z : ↥(posLinks (N := N)) → Circle =>
        plaquetteDensity (torusShift N) circleRep (extendP z)
          p.1 p.2.1 p.2.2 := by
    intro p _
    have e : (fun z : ↥(posLinks (N := N)) → Circle =>
          plaquetteDensity (torusShift N) circleRep (extendP z)
            p.1 p.2.1 p.2.2)
        = fun z => 1 - ((plaquette (torusShift N) (extendP z)
            p.1 p.2.1 p.2.2 : Circle) : ℂ).re :=
      funext fun z => plaquetteDensity_circleRep _ _ _ _
    rw [e]
    exact continuous_const.sub (Complex.continuous_re.comp
      ((plaquette_circle_continuous _ _ _).comp extendP_continuous))
  have e : (fun z : ↥(posLinks (N := N)) → Circle =>
        halfActionP circleRep β z)
      = fun z => β * ∑ p ∈ plaqIndex.filter IsPosPlaq,
          plaquetteDensity (torusShift N) circleRep (extendP z)
            p.1 p.2.1 p.2.2 :=
    funext fun z => rfl
  rw [e]
  exact continuous_const.mul (continuous_finset_sum _ hterm)

/-- The positive restriction is continuous. -/
theorem restrictPos_continuous :
    Continuous (restrictPos (N := N) (G := Circle)) := by
  refine continuous_pi fun ℓ => ?_
  show Continuous fun y : ↥(halfLinks (N := N)) → Circle =>
    y ⟨ℓ.1, posLinks_subset_halfLinks ℓ.2⟩
  exact continuous_apply _

/-- The mirror map is continuous. -/
theorem mirrorP_continuous (hN : Even N) :
    Continuous (mirrorP hN : (↥(negLinks (N := N)) → Circle)
      → ↥(posLinks (N := N)) → Circle) := by
  refine continuous_pi fun ℓ => ?_
  by_cases hℓ : ℓ.1.2 = 0
  · have e : (fun u : ↥(negLinks (N := N)) → Circle => mirrorP hN u ℓ)
        = fun u => (u ⟨reflLink ℓ.1,
            reflLink_mem_negLinks hN ℓ.2⟩)⁻¹ := by
      funext u
      show (if ℓ.1.2 = 0
          then (u ⟨reflLink ℓ.1, reflLink_mem_negLinks hN ℓ.2⟩)⁻¹
          else u ⟨reflLink ℓ.1, reflLink_mem_negLinks hN ℓ.2⟩) = _
      rw [if_pos hℓ]
    rw [e]; exact (continuous_apply _).inv
  · have e : (fun u : ↥(negLinks (N := N)) → Circle => mirrorP hN u ℓ)
        = fun u => u ⟨reflLink ℓ.1,
            reflLink_mem_negLinks hN ℓ.2⟩ := by
      funext u
      show (if ℓ.1.2 = 0
          then (u ⟨reflLink ℓ.1, reflLink_mem_negLinks hN ℓ.2⟩)⁻¹
          else u ⟨reflLink ℓ.1, reflLink_mem_negLinks hN ℓ.2⟩) = _
      rw [if_neg hℓ]
    rw [e]; exact continuous_apply _

/-- Evaluation of the half-extension is continuous. -/
theorem extHalf_continuous_apply (ℓ : Link (Fin 4 → ZMod N)) :
    Continuous fun y : ↥(halfLinks (N := N)) → Circle =>
      extHalf y ℓ := by
  by_cases hℓ : ℓ ∈ halfLinks (N := N)
  · have e : (fun y : ↥(halfLinks (N := N)) → Circle => extHalf y ℓ)
        = fun y => y ⟨ℓ, hℓ⟩ :=
      funext fun y => extHalf_apply hℓ
    rw [e]; exact continuous_apply _
  · have e : (fun y : ↥(halfLinks (N := N)) → Circle => extHalf y ℓ)
        = fun _ => (1 : Circle) := by
      funext y
      show (if h : ℓ ∈ halfLinks (N := N) then y ⟨ℓ, h⟩ else 1) = 1
      exact dif_neg hℓ
    rw [e]; exact continuous_const

/-- Evaluation of the negative-half extension is continuous. -/
theorem extNeg_continuous_apply (ℓ : Link (Fin 4 → ZMod N)) :
    Continuous fun u : ↥(negLinks (N := N)) → Circle =>
      extNeg u ℓ := by
  by_cases hℓ : ℓ ∈ negLinks (N := N)
  · have e : (fun u : ↥(negLinks (N := N)) → Circle => extNeg u ℓ)
        = fun u => u ⟨ℓ, hℓ⟩ :=
      funext fun u => extNeg_apply hℓ
    rw [e]; exact continuous_apply _
  · have e : (fun u : ↥(negLinks (N := N)) → Circle => extNeg u ℓ)
        = fun _ => (1 : Circle) := by
      funext u
      show (if h : ℓ ∈ negLinks (N := N) then u ⟨ℓ, h⟩ else 1) = 1
      exact dif_neg hℓ
    rw [e]; exact continuous_const

/-- The crossing factor of a positive configuration is
continuous. -/
theorem posFactor_continuous
    (p : (Fin 4 → ZMod N) × Fin 4 × Fin 4) :
    Continuous fun z : ↥(posLinks (N := N)) → Circle =>
      posFactor p z := by
  have hev : ∀ ℓ : Link (Fin 4 → ZMod N),
      Continuous fun z : ↥(posLinks (N := N)) → Circle =>
        extendP z ℓ :=
    fun ℓ => (continuous_pi_iff.mp extendP_continuous) ℓ
  by_cases hv : (p.1 0).val = N / 2 - 1
  · have e : (fun z : ↥(posLinks (N := N)) → Circle => posFactor p z)
        = fun z => (extendP z (linkD p))⁻¹ := by
      funext z
      show (if (p.1 0).val = N / 2 - 1 then (extendP z (linkD p))⁻¹
        else extendP z (linkB p)) = _
      rw [if_pos hv]
    rw [e]; exact (hev (linkD p)).inv
  · have e : (fun z : ↥(posLinks (N := N)) → Circle => posFactor p z)
        = fun z => extendP z (linkB p) := by
      funext z
      show (if (p.1 0).val = N / 2 - 1 then (extendP z (linkD p))⁻¹
        else extendP z (linkB p)) = _
      rw [if_neg hv]
    rw [e]; exact hev (linkB p)

/-- The mirrored crossing factor is continuous. -/
theorem negFactorZ_continuous (hN : Even N)
    (p : (Fin 4 → ZMod N) × Fin 4 × Fin 4) :
    Continuous fun u : ↥(negLinks (N := N)) → Circle =>
      negFactorZ p (mirrorP hN u) := by
  have hev : ∀ ℓ : Link (Fin 4 → ZMod N),
      Continuous fun u : ↥(negLinks (N := N)) → Circle =>
        extendP (mirrorP hN u) ℓ :=
    fun ℓ => (continuous_pi_iff.mp
      (extendP_continuous.comp (mirrorP_continuous hN))) ℓ
  by_cases hv : (p.1 0).val = N / 2 - 1
  · have e : (fun u : ↥(negLinks (N := N)) → Circle =>
          negFactorZ p (mirrorP hN u))
        = fun u => extendP (mirrorP hN u) (linkD p) := by
      funext u
      show (if (p.1 0).val = N / 2 - 1
        then extendP (mirrorP hN u) (linkD p)
        else (extendP (mirrorP hN u) (linkB p))⁻¹) = _
      rw [if_pos hv]
    rw [e]
    exact hev (linkD p)
  · have e : (fun u : ↥(negLinks (N := N)) → Circle =>
          negFactorZ p (mirrorP hN u))
        = fun u => (extendP (mirrorP hN u) (linkB p))⁻¹ := by
      funext u
      show (if (p.1 0).val = N / 2 - 1
        then extendP (mirrorP hN u) (linkD p)
        else (extendP (mirrorP hN u) (linkB p))⁻¹) = _
      rw [if_neg hv]
    rw [e]
    exact (hev (linkB p)).inv

/-- The positive monomial is continuous. -/
theorem mPosZ_continuous (n : ↥(zeroFinset (N := N)) → ℤ) :
    Continuous (mPosZ n) :=
  continuous_finsetProd _ fun p _ =>
    (posFactor_continuous p.1).zpow (n p)

/-- The stratum factor on the closed half is continuous. -/
theorem stratFactorY_continuous
    (p : (Fin 4 → ZMod N) × Fin 4 × Fin 4) :
    Continuous fun y : ↥(halfLinks (N := N)) → Circle =>
      stratFactorY p y := by
  by_cases hv : (p.1 0).val = N / 2 - 1
  · have e : (fun y : ↥(halfLinks (N := N)) → Circle =>
          stratFactorY p y)
        = fun y => extHalf y (linkA p) * (extHalf y (linkC p))⁻¹ := by
      funext y
      show (if (p.1 0).val = N / 2 - 1
        then extHalf y (linkA p) * (extHalf y (linkC p))⁻¹
        else 1) = _
      rw [if_pos hv]
    rw [e]
    exact (extHalf_continuous_apply _).mul
      (extHalf_continuous_apply _).inv
  · have e : (fun y : ↥(halfLinks (N := N)) → Circle =>
          stratFactorY p y)
        = fun _ => (1 : Circle) := by
      funext y
      show (if (p.1 0).val = N / 2 - 1
        then extHalf y (linkA p) * (extHalf y (linkC p))⁻¹
        else 1) = 1
      exact if_neg hv
    rw [e]; exact continuous_const

/-- The stratum factor on the negative half is continuous. -/
theorem stratFactorU_continuous
    (p : (Fin 4 → ZMod N) × Fin 4 × Fin 4) :
    Continuous fun u : ↥(negLinks (N := N)) → Circle =>
      stratFactorU p u := by
  by_cases hv : (p.1 0).val = N / 2 - 1
  · have e : (fun u : ↥(negLinks (N := N)) → Circle =>
          stratFactorU p u)
        = fun _ => (1 : Circle) := by
      funext u
      show (if (p.1 0).val = N / 2 - 1
        then 1
        else extNeg u (linkA p) * (extNeg u (linkC p))⁻¹) = 1
      exact if_pos hv
    rw [e]; exact continuous_const
  · have e : (fun u : ↥(negLinks (N := N)) → Circle =>
          stratFactorU p u)
        = fun u => extNeg u (linkA p) * (extNeg u (linkC p))⁻¹ := by
      funext u
      show (if (p.1 0).val = N / 2 - 1
        then 1
        else extNeg u (linkA p) * (extNeg u (linkC p))⁻¹) = _
      rw [if_neg hv]
    rw [e]
    exact (extNeg_continuous_apply _).mul
      (extNeg_continuous_apply _).inv

/-- The closed-half stratum monomial is continuous. -/
theorem stratY_continuous (n : ↥(zeroFinset (N := N)) → ℤ) :
    Continuous (stratY n) :=
  continuous_finsetProd _ fun p _ =>
    (stratFactorY_continuous p.1).zpow (n p)

/-- The negative-half stratum monomial is continuous. -/
theorem stratU_continuous (n : ↥(zeroFinset (N := N)) → ℤ) :
    Continuous (stratU n) :=
  continuous_finsetProd _ fun p _ =>
    (stratFactorU_continuous p.1).zpow (n p)

/-- The closed-half crossing factor is continuous. -/
theorem yPartH_continuous
    (p : (Fin 4 → ZMod N) × Fin 4 × Fin 4) :
    Continuous fun y : ↥(halfLinks (N := N)) → Circle =>
      yPartH p y := by
  by_cases hv : (p.1 0).val = N / 2 - 1
  · have e : (fun y : ↥(halfLinks (N := N)) → Circle => yPartH p y)
        = fun y => extHalf y (linkA p) * (extHalf y (linkC p))⁻¹
            * (extHalf y (linkD p))⁻¹ := by
      funext y
      show (if (p.1 0).val = N / 2 - 1
        then extHalf y (linkA p) * (extHalf y (linkC p))⁻¹
          * (extHalf y (linkD p))⁻¹
        else extHalf y (linkB p)) = _
      rw [if_pos hv]
    rw [e]
    exact ((extHalf_continuous_apply _).mul
      (extHalf_continuous_apply _).inv).mul
      (extHalf_continuous_apply _).inv
  · have e : (fun y : ↥(halfLinks (N := N)) → Circle => yPartH p y)
        = fun y => extHalf y (linkB p) := by
      funext y
      show (if (p.1 0).val = N / 2 - 1
        then extHalf y (linkA p) * (extHalf y (linkC p))⁻¹
          * (extHalf y (linkD p))⁻¹
        else extHalf y (linkB p)) = _
      rw [if_neg hv]
    rw [e]; exact extHalf_continuous_apply _

/-- The negative-half crossing factor is continuous. -/
theorem uPartH_continuous
    (p : (Fin 4 → ZMod N) × Fin 4 × Fin 4) :
    Continuous fun u : ↥(negLinks (N := N)) → Circle =>
      uPartH p u := by
  by_cases hv : (p.1 0).val = N / 2 - 1
  · have e : (fun u : ↥(negLinks (N := N)) → Circle => uPartH p u)
        = fun u => extNeg u (linkB p) := by
      funext u
      show (if (p.1 0).val = N / 2 - 1
        then extNeg u (linkB p)
        else extNeg u (linkA p) * (extNeg u (linkC p))⁻¹
          * (extNeg u (linkD p))⁻¹) = _
      rw [if_pos hv]
    rw [e]; exact extNeg_continuous_apply _
  · have e : (fun u : ↥(negLinks (N := N)) → Circle => uPartH p u)
        = fun u => extNeg u (linkA p) * (extNeg u (linkC p))⁻¹
            * (extNeg u (linkD p))⁻¹ := by
      funext u
      show (if (p.1 0).val = N / 2 - 1
        then extNeg u (linkB p)
        else extNeg u (linkA p) * (extNeg u (linkC p))⁻¹
          * (extNeg u (linkD p))⁻¹) = _
      rw [if_neg hv]
    rw [e]
    exact ((extNeg_continuous_apply _).mul
      (extNeg_continuous_apply _).inv).mul
      (extNeg_continuous_apply _).inv

/-- The closed-half monomial is continuous. -/
theorem monoAY_continuous (n : ↥(zeroFinset (N := N)) → ℤ) :
    Continuous (monoAY n) :=
  continuous_finsetProd _ fun p _ =>
    (yPartH_continuous p.1).zpow (n p)

/-- The negative-half monomial is continuous. -/
theorem monoBU_continuous (hN : Even N)
    (n : ↥(zeroFinset (N := N)) → ℤ) :
    Continuous (monoBU n) :=
  continuous_finsetProd _ fun p _ =>
    (uPartH_continuous p.1).zpow (n p)

/-- The common feature `Ξ` is continuous. -/
theorem featXi_continuous (β : ℝ) (n : ↥(zeroFinset (N := N)) → ℤ) :
    Continuous (featXi β n) := by
  show Continuous fun z : ↥(posLinks (N := N)) → Circle =>
    ((Real.exp (- halfActionP circleRep β z)
        * Real.sqrt (wR β n) : ℝ) : ℂ) * ((mPosZ n z : Circle) : ℂ)
  exact (ofReal_continuous.comp
    ((Real.continuous_exp.comp (continuous_neg.comp
      (halfActionP_circle_continuous β))).mul
      continuous_const)).mul
    (circle_coe_continuous.comp (mPosZ_continuous n))

/-- The closed-half feature is continuous. -/
theorem featA_continuous (β : ℝ) (n : ↥(zeroFinset (N := N)) → ℤ) :
    Continuous (featA β n) := by
  show Continuous fun y : ↥(halfLinks (N := N)) → Circle =>
    ((Real.exp (- halfActionP circleRep β (restrictPos y))
        * Real.sqrt (wR β n) : ℝ) : ℂ) * ((monoAY n y : Circle) : ℂ)
  exact (ofReal_continuous.comp
    ((Real.continuous_exp.comp (continuous_neg.comp
      ((halfActionP_circle_continuous β).comp
        restrictPos_continuous))).mul
      continuous_const)).mul
    (circle_coe_continuous.comp (monoAY_continuous n))

/-- The negative-half feature is continuous. -/
theorem featB_continuous (hN : Even N) (β : ℝ)
    (n : ↥(zeroFinset (N := N)) → ℤ) :
    Continuous (featB hN β n) := by
  show Continuous fun u : ↥(negLinks (N := N)) → Circle =>
    ((Real.exp (- halfActionP circleRep β (mirrorP hN u))
        * Real.sqrt (wR β n) : ℝ) : ℂ)
      * (((monoBU n u)⁻¹ : Circle) : ℂ)
  exact (ofReal_continuous.comp
    ((Real.continuous_exp.comp (continuous_neg.comp
      ((halfActionP_circle_continuous β).comp
        (mirrorP_continuous hN)))).mul
      continuous_const)).mul
    (circle_coe_continuous.comp ((monoBU_continuous hN n).inv))

/-- **Norm bound for the closed-half feature** (`β ≥ 0`). -/
theorem featA_norm_le (hβ : 0 ≤ β) (n : ↥(zeroFinset (N := N)) → ℤ)
    (y : ↥(halfLinks (N := N)) → Circle) :
    ‖featA β n y‖ ≤ Real.sqrt (wR β n) := by
  have hea : Real.exp (- halfActionP circleRep β (restrictPos y))
      ≤ 1 :=
    (Real.exp_le_exp.mpr (neg_nonpos.mpr
      (halfActionP_circle_nonneg hβ _))).trans_eq Real.exp_zero
  have hnorm : ‖featA β n y‖
      = Real.exp (- halfActionP circleRep β (restrictPos y))
        * Real.sqrt (wR β n) := by
    show ‖((Real.exp (- halfActionP circleRep β (restrictPos y))
        * Real.sqrt (wR β n) : ℝ) : ℂ)
        * ((monoAY n y : Circle) : ℂ)‖ = _
    rw [norm_mul]
    have h1 : ‖((monoAY n y : Circle) : ℂ)‖ = 1 := by simp
    have h2 : ‖((Real.exp (- halfActionP circleRep β (restrictPos y))
        * Real.sqrt (wR β n) : ℝ) : ℂ)‖
        = Real.exp (- halfActionP circleRep β (restrictPos y))
          * Real.sqrt (wR β n) := by
      exact (RCLike.norm_ofReal _).trans
        (abs_of_nonneg (mul_nonneg (Real.exp_nonneg _)
          (Real.sqrt_nonneg _)))
    rw [h1, h2, mul_one]
  rw [hnorm]
  calc Real.exp (- halfActionP circleRep β (restrictPos y))
        * Real.sqrt (wR β n)
      ≤ 1 * Real.sqrt (wR β n) :=
        mul_le_mul_of_nonneg_right hea (Real.sqrt_nonneg _)
    _ = Real.sqrt (wR β n) := one_mul _

/-- **Norm bound for the negative-half feature** (`β ≥ 0`). -/
theorem featB_norm_le (hN : Even N) (hβ : 0 ≤ β)
    (n : ↥(zeroFinset (N := N)) → ℤ)
    (u : ↥(negLinks (N := N)) → Circle) :
    ‖featB hN β n u‖ ≤ Real.sqrt (wR β n) := by
  have hea : Real.exp (- halfActionP circleRep β (mirrorP hN u))
      ≤ 1 :=
    (Real.exp_le_exp.mpr (neg_nonpos.mpr
      (halfActionP_circle_nonneg hβ _))).trans_eq Real.exp_zero
  have hnorm : ‖featB hN β n u‖
      = Real.exp (- halfActionP circleRep β (mirrorP hN u))
        * Real.sqrt (wR β n) := by
    show ‖((Real.exp (- halfActionP circleRep β (mirrorP hN u))
        * Real.sqrt (wR β n) : ℝ) : ℂ)
        * (((monoBU n u)⁻¹ : Circle) : ℂ)‖ = _
    rw [norm_mul]
    have h1 : ‖(((monoBU n u)⁻¹ : Circle) : ℂ)‖ = 1 := by simp
    have h2 : ‖((Real.exp (- halfActionP circleRep β (mirrorP hN u))
        * Real.sqrt (wR β n) : ℝ) : ℂ)‖
        = Real.exp (- halfActionP circleRep β (mirrorP hN u))
          * Real.sqrt (wR β n) := by
      exact (RCLike.norm_ofReal _).trans
        (abs_of_nonneg (mul_nonneg (Real.exp_nonneg _)
          (Real.sqrt_nonneg _)))
    rw [h1, h2, mul_one]
  rw [hnorm]
  calc Real.exp (- halfActionP circleRep β (mirrorP hN u))
        * Real.sqrt (wR β n)
      ≤ 1 * Real.sqrt (wR β n) :=
        mul_le_mul_of_nonneg_right hea (Real.sqrt_nonneg _)
    _ = Real.sqrt (wR β n) := one_mul _

/-- **Route C discharge: OS positivity of the U(1) Wilson theory.**
For every even `N` and every `β ≥ 0`, the Osterwalder–Schrader form
of the circle Wilson theory at coupling `β` is positive on every
continuous positive-type observable `F = f ∘ (positive restriction)`
with `f` bounded. This is Stage 1b-B positivity at T1 for `U(1)`;
the Gram clause at general `(G, ρ)` remains open (Route B). -/
theorem osForm_circle_nonneg (hN : Even N) (β : ℝ) (hβ : 0 ≤ β)
    (F : Config (Fin 4 → ZMod N) Circle → ℂ)
    (f : (↥(posLinks (N := N)) → Circle) → ℂ)
    (hF : ∀ U, F U = f (fun ℓ : ↥(posLinks (N := N)) => U ℓ.1))
    (hf : Continuous f) (Cf : ℝ) (hfB : ∀ z, ‖f z‖ ≤ Cf) :
    0 ≤ (osForm (haarProb Circle) circleRep β F F).re
      ∧ (osForm (haarProb Circle) circleRep β F F).im = 0 := by
  have hwR : Summable fun n : ↥(zeroFinset (N := N)) → ℤ => wR β n := by
    rw [show (fun n : ↥(zeroFinset (N := N)) → ℤ => wR β n)
        = fun n => ∏ x : ↥(zeroFinset (N := N)),
            (Real.exp (-β) * besselI β (n x)) from
      funext fun n => rfl]
    exact summable_prod_subtype zeroFinset
      (fun p n => Real.exp (-β) * besselI β n)
      (fun a _ => (summable_besselI_int β).mul_left (Real.exp (-β)))
      (fun a _ n => mul_nonneg (Real.exp_pos _).le
        (besselI_nonneg hβ n))
  have hsum : Summable fun n : ↥(zeroFinset (N := N)) → ℤ =>
      Real.sqrt (wR β n) * Real.sqrt (wR β n) := by
    have e : (fun n : ↥(zeroFinset (N := N)) → ℤ =>
        Real.sqrt (wR β n) * Real.sqrt (wR β n))
        = fun n => wR β n :=
      funext fun n => Real.mul_self_sqrt (wR_nonneg hβ n)
    rwa [e]
  refine osForm_nonneg_of_gram_integrated
    (μG := haarProb Circle) (ρ := circleRep) (d := 1)
    (ι := ↥(zeroFinset (N := N)) → ℤ)
    circleRep_continuous hN (by norm_num) β F f hF
    hf.aestronglyMeasurable Cf hfB
    (featA β) (featB hN β) (featXi β)
    (fun n => (featA_continuous β n).aestronglyMeasurable)
    (fun n => (featB_continuous hN β n).aestronglyMeasurable)
    (fun n => Real.sqrt (wR β n)) (fun n => Real.sqrt (wR β n))
    (fun n => Real.sqrt_nonneg _)
    (fun n y => featA_norm_le hβ n y)
    (fun n u => featB_norm_le hN hβ n u)
    hsum dA dB dA_nonneg dB_nonneg ?_ ?_ ?_
  · exact fun y u => gram_identity_circle hN hβ y u
  · exact fun n => marginalA hN β n f
  · exact fun n => marginalB hN β n f

/-! ## §T0 companion: the finite-rank obstruction, algebraic core

A *finite* pointwise Gram identity forces every section of the
kernel — as a function of the closed half, at fixed negative half —
into the finite-dimensional span of the features. The stratum-
integrated U(1) kernel of §D has sections spanning an
infinite-dimensional space (its Fourier expansion has full support
with all weights `wR β n > 0` at `β > 0`), so no finite pointwise
`hgram` can represent it. This is obstruction (ii) of the charter
§2, in its algebraic form. -/

theorem finite_gram_sections_span {ι : Type*} [Fintype ι]
    (A : ι → (↥(halfLinks (N := N)) → Circle) → ℂ)
    (B : ι → (↥(negLinks (N := N)) → Circle) → ℂ)
    (u : ↥(negLinks (N := N)) → Circle) :
    (fun y => ∑ i, (starRingEnd ℂ) (B i u) * A i y)
      ∈ Submodule.span ℂ (Set.range A) := by
  have e : (fun y => ∑ i, (starRingEnd ℂ) (B i u) * A i y)
      = ∑ i, (starRingEnd ℂ) (B i u) • A i := by
    funext y
    simp [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [e]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
    (Submodule.subset_span (Set.mem_range_self i))
