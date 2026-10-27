import ThetLogos.SpectralActionBridge

open scoped Kronecker

/-!
# ThetLogos.SpectralActionA2 — a₂ coefficient separation (SA-FLIP-1)

**What this module is.** A coefficient-separation theorem for the
spectral action's a₂ Seeley–DeWitt coefficient, in the product
(almost-commutative) setting of `SpectralAction`: the manifold factor
contributes an abstract scalar-curvature input `scalarR`, the finite
factor contributes the fluctuated square `DFA_sq`. It is a NEW entry
beside `SpectralAction.seely_dewitt_a2_formula` (which stands
untouched, exactly as it was); nothing here edits any earlier module.

**What is proved here (finite linear algebra, complete proofs).**
The Gilkey endomorphism `E_A = (R/4)⊗I₃₂ + I₄⊗(D_F^(A))²` is built
as an actual Kronecker endomorphism on the 128-dimensional product
space `Fin 4 × I32`, and its trace factorization
`Tr₁₂₈(E_A) = 32·R + 4·Tr₃₂((D_F^(A))²)` is *proved* from the
tensor structure (`Matrix.trace_kronecker`), not assumed. From it,
the separated a₂, the nonvanishing of its gravitational coefficient
`160/3·(4π)⁻²`, and the discharge of its matter part by the landed
finite traces (`sa_finite_a2_yukawa`, `sa_finite_a2_fluctuated`).

**What is NOT proved here — the anchors, named.**
- `scalarR` is an abstract scalar *variable*: the curvature slot.
  No manifold, metric, or curvature computation exists in this
  corpus, and none is smuggled in; `R` is an input, honestly typed
  as a complex scalar, where `SpectralAction` kept it as a string.
- The Gilkey universal formula `a₂ = (4π)⁻²·Tr₁₂₈(R/6·1 + E_A)`
  and its `(4π)⁻²` prefactor are taken as the stated input form
  (the literature's formula, T4; axiomatized as scaffolding in
  `SpectralAction`, T5). The heat-kernel derivation behind that
  formula is not formalized here or anywhere in the corpus.

**Label fence (standing).** This is gravity's *coefficient* inside
the spectral action's own expansion, at coefficient grade: the
Einstein–Hilbert slot of the corpus's a₂ is occupied, separated,
and proved nonzero. It is **not** spacetime gravity, not a gravity
object, not a derivation of Einstein's equations, and not a Dial-2
movement. NO CLAIM. Dials 0/4.
-/

namespace ThetLogos

/-! ## The endomorphism E_A as a Kronecker endomorphism -/

/-- The Gilkey endomorphism `E_A = (R/4)⊗I₃₂ + I₄⊗(D_F^(A))²`,
    built as an actual Kronecker (tensor) endomorphism on the
    product index space `Fin 4 × I32` (dimension 4·32 = 128).
    `scalarR` is the abstract scalar-curvature input — a variable,
    not a computed curvature; `DFA_sq` is the fluctuated finite
    Dirac square `(D_F^(A))²` as a 32×32 matrix. -/
noncomputable def endomorphismEA128 (scalarR : ℂ) (DFA_sq : Matrix I32 I32 ℂ) :
    Matrix (Fin 4 × I32) (Fin 4 × I32) ℂ :=
  ((scalarR / 4) • (1 : Matrix (Fin 4) (Fin 4) ℂ)) ⊗ₖ (1 : Matrix I32 I32 ℂ)
    + (1 : Matrix (Fin 4) (Fin 4) ℂ) ⊗ₖ DFA_sq

/-- **Statement 1 — trace factorization, proved.** For the Kronecker
    endomorphism above,
    `Tr₁₂₈(E_A) = 32·R + 4·Tr₃₂((D_F^(A))²)`.
    Pure finite-dimensional linear algebra: the trace of a Kronecker
    product is the product of the traces, applied to each summand.
    The factorization is derived from the tensor structure here;
    it is not assumed anywhere in this module. -/
theorem trace_endomorphismEA (scalarR : ℂ) (DFA_sq : Matrix I32 I32 ℂ) :
    Matrix.trace (endomorphismEA128 scalarR DFA_sq)
      = 32 * scalarR + 4 * Matrix.trace DFA_sq := by
  simp only [endomorphismEA128, Matrix.trace_add, Matrix.trace_kronecker,
    Matrix.trace_smul, Matrix.trace_one, smul_eq_mul, Fintype.card_fin]
  ring

/-! ## The separated a₂ -/

/-- The a₂ Seeley–DeWitt coefficient over the abstract curvature
    input, in Gilkey's stated form:
    `a₂ = (4π)⁻² · Tr₁₂₈(R/6 · 1₁₂₈ + E_A)`.
    The universal formula and the `(4π)⁻²` prefactor are the named
    anchor (literature T4 / corpus scaffolding T5); everything this
    module *proves* about `gilkeyA2` is the separation of this
    trace into its gravitational and matter parts. -/
noncomputable def gilkeyA2 (scalarR : ℂ) (DFA_sq : Matrix I32 I32 ℂ) : ℂ :=
  ((4 * (Real.pi : ℂ)) ^ 2)⁻¹ *
    Matrix.trace ((scalarR / 6) • (1 : Matrix (Fin 4 × I32) (Fin 4 × I32) ℂ)
      + endomorphismEA128 scalarR DFA_sq)

/-- **Statement 2 — the separated a₂ (new entry).**
    `a₂ = (4π)⁻² · [ (160/3)·R + 4·Tr₃₂((D_F^(A))²) ]`.
    The R-coefficient assembles from the two proved trace pieces:
    `Tr₁₂₈(R/6 · 1) = 128·R/6 = (64/3)·R` and Statement 1's `32·R`;
    `64/3 + 32 = 160/3`. This replaces no earlier statement: the
    older scaffolding entry in `SpectralAction` stands as it was. -/
theorem seely_dewitt_a2_separated (scalarR : ℂ) (DFA_sq : Matrix I32 I32 ℂ) :
    gilkeyA2 scalarR DFA_sq
      = ((4 * (Real.pi : ℂ)) ^ 2)⁻¹
          * ((160 / 3 : ℂ) * scalarR + 4 * Matrix.trace DFA_sq) := by
  have htr : Matrix.trace
        ((scalarR / 6) • (1 : Matrix (Fin 4 × I32) (Fin 4 × I32) ℂ))
      = (64 / 3 : ℂ) * scalarR := by
    simp only [Matrix.trace_smul, Matrix.trace_one, smul_eq_mul,
      Fintype.card_prod, Fintype.card_fin]
    ring
  rw [gilkeyA2, Matrix.trace_add, htr, trace_endomorphismEA]
  ring

/-- The gravitational coefficient of the separated a₂:
    `160/3 · (4π)⁻²` — the constant standing in front of the
    curvature input `R` in `seely_dewitt_a2_separated`. -/
noncomputable def a2GravCoeff : ℂ :=
  (160 / 3 : ℂ) * ((4 * (Real.pi : ℂ)) ^ 2)⁻¹

/-- The separated a₂, written as an affine function of the curvature
    input: `a₂ = a2GravCoeff · R + (4π)⁻² · (4 · Tr₃₂((D_F^(A))²))`.
    This makes the phrase "coefficient of R" literal: the first
    summand is exactly `a2GravCoeff` times the curvature slot. -/
theorem seely_dewitt_a2_affine (scalarR : ℂ) (DFA_sq : Matrix I32 I32 ℂ) :
    gilkeyA2 scalarR DFA_sq
      = a2GravCoeff * scalarR
          + ((4 * (Real.pi : ℂ)) ^ 2)⁻¹ * (4 * Matrix.trace DFA_sq) := by
  rw [seely_dewitt_a2_separated, a2GravCoeff]
  ring

/-- **Statement 3 — the gravitational coefficient is nonzero.**
    `160/3 · (4π)⁻² ≠ 0`: the Einstein–Hilbert slot of the corpus's
    own a₂ is occupied with a nonzero coefficient, not silently
    zero. (The coefficient's *value* is convention-carrying — it is
    the coefficient in the Gilkey form stated above; its
    nonvanishing is the convention-robust content.) -/
theorem a2_grav_coeff_ne_zero : a2GravCoeff ≠ 0 := by
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  unfold a2GravCoeff
  exact mul_ne_zero (by norm_num)
    (inv_ne_zero (pow_ne_zero 2 (mul_ne_zero (by norm_num) hpi)))

/-! ## Statement 4 — the matter part, discharged by landed traces -/

/-- **Statement 4a — matter part discharged (unfluctuated).**
    With `DFA_sq = (smDirac …)²`, the matter coefficient
    `Tr₃₂(D_F²)` in the separated a₂ is the explicit Yukawa
    polynomial, by citation of the landed `sa_finite_a2_yukawa`
    (itself the proved `tr_DF_sq_yukawa`); nothing is recomputed. -/
theorem a2_matter_discharged (scalarR : ℂ) (yNu yE yU yD yR : ℂ) :
    gilkeyA2 scalarR ((smDirac yNu yE yU yD yR) ^ 2)
      = ((4 * (Real.pi : ℂ)) ^ 2)⁻¹
          * ((160 / 3 : ℂ) * scalarR
            + 4 * ((4 * (Complex.normSq yNu + Complex.normSq yE
                  + 3 * Complex.normSq yU + 3 * Complex.normSq yD)
                + 2 * Complex.normSq yR : ℝ) : ℂ)) := by
  rw [seely_dewitt_a2_separated, sa_finite_a2_yukawa]

/-- **Statement 4b — matter part discharged (fluctuated).**
    With `DFA_sq = (fluctuatedDirac D_F A)²`, the matter coefficient
    is the landed fluctuation expansion, by citation of
    `sa_finite_a2_fluctuated` (itself the proved `tr_fluctuated_sq`). -/
theorem a2_matter_discharged_fluctuated (scalarR : ℂ)
    (D_F A : Matrix I32 I32 ℂ) :
    gilkeyA2 scalarR ((fluctuatedDirac D_F A) ^ 2)
      = ((4 * (Real.pi : ℂ)) ^ 2)⁻¹
          * ((160 / 3 : ℂ) * scalarR
            + 4 * (Matrix.trace (D_F ^ 2)
                + 2 * Matrix.trace (D_F * (A + oppositeOneForm A))
                + Matrix.trace ((A + oppositeOneForm A) ^ 2))) := by
  rw [seely_dewitt_a2_separated, sa_finite_a2_fluctuated]

/-- **Statement 4c — the matter part vanishes exactly at zero
    coupling.** The matter coefficient `4·Tr₃₂(D_F²)` of the
    separated a₂ is zero iff every Yukawa coupling vanishes: the
    discharged polynomial is a positive combination of the squared
    norms `|yν|², |ye|², 3|yu|², 3|yd|², |yR|²`, so it vanishes
    exactly when each summand does. -/
theorem a2_matter_vanishes_iff (yNu yE yU yD yR : ℂ) :
    (4 : ℂ) * Matrix.trace ((smDirac yNu yE yU yD yR) ^ 2) = 0
      ↔ yNu = 0 ∧ yE = 0 ∧ yU = 0 ∧ yD = 0 ∧ yR = 0 := by
  rw [sa_finite_a2_yukawa]
  constructor
  · intro h
    have hcast : (4 * (Complex.normSq yNu + Complex.normSq yE
          + 3 * Complex.normSq yU + 3 * Complex.normSq yD)
        + 2 * Complex.normSq yR : ℝ) = 0 := by
      rcases mul_eq_zero.mp h with h4 | h4
      · norm_num at h4
      · exact_mod_cast h4
    have hNu : Complex.normSq yNu = 0 := by
      have h0 := Complex.normSq_nonneg yNu
      have h1 := Complex.normSq_nonneg yE
      have h2 := Complex.normSq_nonneg yU
      have h3 := Complex.normSq_nonneg yD
      have h4 := Complex.normSq_nonneg yR
      linarith
    have hE : Complex.normSq yE = 0 := by
      have h0 := Complex.normSq_nonneg yNu
      have h1 := Complex.normSq_nonneg yE
      have h2 := Complex.normSq_nonneg yU
      have h3 := Complex.normSq_nonneg yD
      have h4 := Complex.normSq_nonneg yR
      linarith
    have hU : Complex.normSq yU = 0 := by
      have h0 := Complex.normSq_nonneg yNu
      have h1 := Complex.normSq_nonneg yE
      have h2 := Complex.normSq_nonneg yU
      have h3 := Complex.normSq_nonneg yD
      have h4 := Complex.normSq_nonneg yR
      linarith
    have hD : Complex.normSq yD = 0 := by
      have h0 := Complex.normSq_nonneg yNu
      have h1 := Complex.normSq_nonneg yE
      have h2 := Complex.normSq_nonneg yU
      have h3 := Complex.normSq_nonneg yD
      have h4 := Complex.normSq_nonneg yR
      linarith
    have hR : Complex.normSq yR = 0 := by
      have h0 := Complex.normSq_nonneg yNu
      have h1 := Complex.normSq_nonneg yE
      have h2 := Complex.normSq_nonneg yU
      have h3 := Complex.normSq_nonneg yD
      have h4 := Complex.normSq_nonneg yR
      linarith
    exact ⟨Complex.normSq_eq_zero.mp hNu, Complex.normSq_eq_zero.mp hE,
      Complex.normSq_eq_zero.mp hU, Complex.normSq_eq_zero.mp hD,
      Complex.normSq_eq_zero.mp hR⟩
  · rintro ⟨rfl, rfl, rfl, rfl, rfl⟩
    simp

end ThetLogos
