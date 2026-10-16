import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Diagonal
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Real.Sqrt

/-!
# ThetLogos.WeldDuality — the Weld: Morley spectral projections in duality (T1)

HONESTY LEDGER (read before citing):

- Everything in this file is **T1 finite linear algebra**: matrices over
  `ℂ` on `Fin n` (concrete arena `Fin 4`), one involution `η` with
  `η * η = 1`, its two spectral projections, and the elementary theorems
  they support. Zero sorrys, no new axioms.
- **"2D holography" does NOT survive into this module.** What survives
  of the Morley/holography weld idea is its finite shadow only:
  *dimension counted by traces of spectral projections* — the trace of
  `P₊ = (1 + η)/2` counts the `+1` directions of `η`, and that count is
  the entire "signature" content here. No boundary/bulk duality, no
  continuum, no holography theorem is stated or claimed.
- It is **not** a Yang–Mills rung, not a bridge to spacetime, and it
  does not touch the standing KILL `signature_not_determined`
  (EdgeSignature §4): `η² = 1` does not determine the signature. This
  module *echoes* that kill — in Face B the signature is visibly INPUT
  through the Dirac operator `D` (§4, L1) — it never derives one.
- **The duality (Jeff's dial decision, 2026-10-16: "both in duality").**
  The weld was designed with three dials. Dial 3 is shared (B: the
  concrete `ℂ⁴` arena). Dials 1–2 come in two configurations, and this
  module carries BOTH as two faces of one object, with linker theorems
  (§4) between them:
  - **Face A** (§2): Dial 1-B (curvature as an added *correction term*
    `η ↦ η + A`) + Dial 2-A (the projection is the *grading split*
    `P±` of the involution).
  - **Face B** (§3): Dial 1-C (curvature as the *Dirac operator's
    sign*) + Dial 2-B (the projection is the *gap split* of `H = D²`).
  Dial 1-A (curvature as conjugation) is proved in the common core
  (§1): conjugation moves the projections but never their traces —
  signature is a unitary invariant.
- **Relation to `ThetLogos.EdgeSignature`.** The §1 pair algebra
  (`P±` idempotent, orthogonal, complementary) is EdgeSignature §1's
  edge-pair algebra (`edgePlus`/`edgeMinus`), restated here at
  matrices as `weldPlus`/`weldMinus` with the same proof engine.
  Restated, not imported: `EdgeSignature` imports all of Mathlib and
  costs ~17 minutes to elaborate in this environment, versus ~1 minute
  for this module's targeted imports; nothing is hidden — the
  statements are the same, and the genuinely new content of this
  module is §1's trace formulas, conjugation rigidity, and fixed-set
  characterizations, plus §§2–4 entire.
- **The resting-place pin** (`nested-resting-place-pin-2026-10-16`):
  the welded object must REST. Here "rest" is the fixed set of the
  motion `v ↦ η *ᵥ v`, and §1 proves it is exactly the range of `P₊`;
  for two commuting involutions the joint resting place (intersection
  of the two fixed sets) is the range of the product projection
  `P₊(η₁) * P₊(η₂)` — the pin's intersection-of-fixed-sets, in T1 form.
- **Priced and NOT proved (stretch remainder):** general
  correction-stability — that the finranks of the spectral projections
  stay constant along a general correction path. Only the worked `ℂ⁴`
  example is proved (§4, L2: same traces, different projections). The
  general statement needs spectral-projection continuity/rank
  arguments this finite module does not build.
- Provenance: the Morley/projection weld designed 2026-10-16 over the
  Nested Resting Place pin; Jeff set the dials to "both in duality";
  built as fleet item 2, after `FluxTwist` (fleet item 1).
-/

namespace ThetLogos

open Matrix

variable {n : ℕ}

/-! ## §0. Scalar helpers -/

/-- Scalar engine for matrices over `ℂ`:
    `(a • X) * (b • Y) = (a * b) • (X * Y)`. -/
theorem smul_mul_smul_mat (a b : ℂ) (X Y : Matrix (Fin n) (Fin n) ℂ) :
    (a • X) * (b • Y) = (a * b) • (X * Y) := by
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]

/-- `(2 : ℂ) • X = X + X` for matrices. -/
theorem two_smul_mat (X : Matrix (Fin n) (Fin n) ℂ) : (2 : ℂ) • X = X + X := by
  rw [show (2 : ℂ) = 1 + 1 by norm_num, add_smul, one_smul]

/-- The positive square root of `2`, as a complex number. -/
noncomputable def sqrt2c : ℂ := (Real.sqrt 2 : ℂ)

theorem sqrt2c_mul_self : sqrt2c * sqrt2c = 2 := by
  rw [sqrt2c, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num

theorem sqrt2c_ne_zero : sqrt2c ≠ 0 := by
  intro h0
  have h := sqrt2c_mul_self
  rw [h0, mul_zero] at h
  norm_num at h

theorem sqrt2c_inv_mul_self : sqrt2c⁻¹ * sqrt2c⁻¹ = (2 : ℂ)⁻¹ := by
  rw [← mul_inv, sqrt2c_mul_self]

/-! ## §1. Common core — the spectral projections of an involution

For `η * η = 1`, the two spectral projections are
`P₊ = weldPlus η = (1 + η)/2` and `P₋ = weldMinus η = (1 − η)/2`.
The pair algebra (idempotence, orthogonality, complementarity,
recovery of `η`) is EdgeSignature §1's, restated at matrices; the
trace formulas, conjugation rigidity, and fixed-set theory are new.
-/

/-- The `+` spectral projection of an involution: `P₊ = (1 + η)/2`.
    (EdgeSignature's `edgePlus`, restated at matrices — see header.) -/
noncomputable def weldPlus (η : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  (2 : ℂ)⁻¹ • (1 + η)

/-- The `−` spectral projection of an involution: `P₋ = (1 − η)/2`.
    (EdgeSignature's `edgeMinus`, restated at matrices.) -/
noncomputable def weldMinus (η : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  (2 : ℂ)⁻¹ • (1 - η)

/-- `P₊² = P₊` (T1): idempotence forced by `η² = 1` alone. -/
theorem weldPlus_idem (η : Matrix (Fin n) (Fin n) ℂ) (h : η * η = 1) :
    weldPlus η * weldPlus η = weldPlus η := by
  have expand : (1 + η) * (1 + η) = (1 + η) + (1 + η) := by
    have e : (1 + η) * (1 + η) = 1 + (η + η) + η * η := by
      rw [add_mul, one_mul, mul_add, mul_one]; try abel
    rw [e, h]; abel
  unfold weldPlus
  rw [smul_mul_smul_mat, expand, ← two_smul_mat, smul_smul]
  have hsc : (2 : ℂ)⁻¹ * (2 : ℂ)⁻¹ * 2 = (2 : ℂ)⁻¹ := by
    rw [show (2 : ℂ)⁻¹ * (2 : ℂ)⁻¹ * 2 = (2 : ℂ)⁻¹ * ((2 : ℂ)⁻¹ * 2) by ring,
      inv_mul_cancel₀ (show (2 : ℂ) ≠ 0 by norm_num), mul_one]
  rw [hsc]

/-- `P₋² = P₋` (T1). -/
theorem weldMinus_idem (η : Matrix (Fin n) (Fin n) ℂ) (h : η * η = 1) :
    weldMinus η * weldMinus η = weldMinus η := by
  have expand : (1 - η) * (1 - η) = (1 - η) + (1 - η) := by
    have e : (1 - η) * (1 - η) = 1 - (η + η) + η * η := by
      rw [sub_mul, one_mul, mul_sub, mul_one]; try abel
    rw [e, h]; abel
  unfold weldMinus
  rw [smul_mul_smul_mat, expand, ← two_smul_mat, smul_smul]
  have hsc : (2 : ℂ)⁻¹ * (2 : ℂ)⁻¹ * 2 = (2 : ℂ)⁻¹ := by
    rw [show (2 : ℂ)⁻¹ * (2 : ℂ)⁻¹ * 2 = (2 : ℂ)⁻¹ * ((2 : ℂ)⁻¹ * 2) by ring,
      inv_mul_cancel₀ (show (2 : ℂ) ≠ 0 by norm_num), mul_one]
  rw [hsc]

/-- `P₊ P₋ = 0` (T1): orthogonality of the pair. -/
theorem weld_orth_lr (η : Matrix (Fin n) (Fin n) ℂ) (h : η * η = 1) :
    weldPlus η * weldMinus η = 0 := by
  have expand : (1 + η) * (1 - η) = 0 := by
    have e : (1 + η) * (1 - η) = 1 + (η - η) - η * η := by
      rw [add_mul, one_mul, mul_sub, mul_one]; try abel
    rw [e, h]; abel
  unfold weldPlus weldMinus
  rw [smul_mul_smul_mat, expand, smul_zero]

/-- `P₋ P₊ = 0` (T1). -/
theorem weld_orth_rl (η : Matrix (Fin n) (Fin n) ℂ) (h : η * η = 1) :
    weldMinus η * weldPlus η = 0 := by
  have expand : (1 - η) * (1 + η) = 0 := by
    have e : (1 - η) * (1 + η) = 1 + (η - η) - η * η := by
      rw [sub_mul, one_mul, mul_add, mul_one]; try abel
    rw [e, h]; abel
  unfold weldMinus weldPlus
  rw [smul_mul_smul_mat, expand, smul_zero]

/-- `P₊ + P₋ = 1` (T1): complementarity. -/
theorem weld_compl (η : Matrix (Fin n) (Fin n) ℂ) :
    weldPlus η + weldMinus η = 1 := by
  have hadd : ((1 : Matrix (Fin n) (Fin n) ℂ) + η) + (1 - η) = 1 + 1 := by abel
  unfold weldPlus weldMinus
  rw [← smul_add, hadd, ← two_smul_mat, smul_smul,
    inv_mul_cancel₀ (show (2 : ℂ) ≠ 0 by norm_num), one_smul]

/-- `η = P₊ − P₋` (T1): the involution recovered from its projections. -/
theorem weld_recover (η : Matrix (Fin n) (Fin n) ℂ) :
    weldPlus η - weldMinus η = η := by
  have hsub : ((1 : Matrix (Fin n) (Fin n) ℂ) + η) - (1 - η) = η + η := by abel
  unfold weldPlus weldMinus
  rw [← smul_sub, hsub, ← two_smul_mat, smul_smul,
    inv_mul_cancel₀ (show (2 : ℂ) ≠ 0 by norm_num), one_smul]

/-- `η * P₊ = P₊` (T1): the involution acts as `+1` on its plus-projection. -/
theorem weld_mul_plus (η : Matrix (Fin n) (Fin n) ℂ) (h : η * η = 1) :
    η * weldPlus η = weldPlus η := by
  have e : η * (1 + η) = 1 + η := by
    rw [mul_add, mul_one, h]; abel
  unfold weldPlus
  rw [Matrix.mul_smul, e]

/-- `η * P₋ = −P₋` (T1): the involution acts as `−1` on its minus-projection. -/
theorem weld_mul_minus (η : Matrix (Fin n) (Fin n) ℂ) (h : η * η = 1) :
    η * weldMinus η = -weldMinus η := by
  have e : η * (1 - η) = -(1 - η) := by
    rw [mul_sub, mul_one, h]; abel
  unfold weldMinus
  rw [Matrix.mul_smul, e, smul_neg]

/-- **Trace formula** (T1): `tr P₊ = (n + tr η)/2` as a `ℂ` identity.
    This is the module's "dimension counted by a trace": for an
    involution with eigenvalues `±1`, `tr P₊` is the count of `+1`
    directions. -/
theorem trace_weldPlus (η : Matrix (Fin n) (Fin n) ℂ) :
    Matrix.trace (weldPlus η) = ((n : ℂ) + Matrix.trace η) * (2 : ℂ)⁻¹ := by
  unfold weldPlus
  rw [Matrix.trace_smul, Matrix.trace_add, Matrix.trace_one]
  simp [smul_eq_mul]
  ring

/-- **Trace formula, minus side** (T1): `tr P₋ = (n − tr η)/2`. -/
theorem trace_weldMinus (η : Matrix (Fin n) (Fin n) ℂ) :
    Matrix.trace (weldMinus η) = ((n : ℂ) - Matrix.trace η) * (2 : ℂ)⁻¹ := by
  unfold weldMinus
  rw [Matrix.trace_smul, Matrix.trace_sub, Matrix.trace_one]
  simp [smul_eq_mul]
  ring

/-! ### §1b. Conjugation rigidity (Dial 1-A)

Conjugating the involution conjugates its projections and fixes their
traces: the signature count is an invariant of the whole conjugacy
class, not of any representative. -/

/-- Conjugation preserves the involution property (T1). -/
theorem conj_invol (η U V : Matrix (Fin n) (Fin n) ℂ)
    (hUV : U * V = 1) (hVU : V * U = 1) (h : η * η = 1) :
    (U * η * V) * (U * η * V) = 1 := by
  have h1 : (U * η * V) * (U * η * V) = U * η * (V * U) * η * V := by
    noncomm_ring
  rw [h1, hVU, Matrix.mul_one, Matrix.mul_assoc U η η, h, Matrix.mul_one, hUV]

/-- Conjugation conjugates the plus-projection (T1):
    `P₊(U η U⁻¹) = U P₊(η) U⁻¹`. -/
theorem conj_weldPlus (η U V : Matrix (Fin n) (Fin n) ℂ)
    (hUV : U * V = 1) :
    weldPlus (U * η * V) = U * weldPlus η * V := by
  have key : U * (1 + η) * V = 1 + U * η * V := by
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, hUV]
  show (2 : ℂ)⁻¹ • (1 + U * η * V) = U * ((2 : ℂ)⁻¹ • (1 + η)) * V
  rw [← key, ← Matrix.smul_mul, ← Matrix.mul_smul]

/-- Conjugation conjugates the minus-projection (T1). -/
theorem conj_weldMinus (η U V : Matrix (Fin n) (Fin n) ℂ)
    (hUV : U * V = 1) :
    weldMinus (U * η * V) = U * weldMinus η * V := by
  have key : U * (1 - η) * V = 1 - U * η * V := by
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, hUV]
  show (2 : ℂ)⁻¹ • (1 - U * η * V) = U * ((2 : ℂ)⁻¹ • (1 - η)) * V
  rw [← key, ← Matrix.smul_mul, ← Matrix.mul_smul]

/-- **Signature is a conjugation invariant** (T1): the plus-trace —
    the signature count — does not move under conjugation. -/
theorem trace_conj_weldPlus (η U V : Matrix (Fin n) (Fin n) ℂ)
    (hUV : U * V = 1) (hVU : V * U = 1) :
    Matrix.trace (weldPlus (U * η * V)) = Matrix.trace (weldPlus η) := by
  rw [conj_weldPlus η U V hUV, Matrix.trace_mul_comm (U * weldPlus η) V,
    ← Matrix.mul_assoc, hVU, Matrix.one_mul]

/-- Unitary form of the invariance (T1): for `U` with `U * Uᴴ = 1`
    and `Uᴴ * U = 1`, conjugating by `U` fixes the plus-trace. -/
theorem trace_unitary_conj_weldPlus (η U : Matrix (Fin n) (Fin n) ℂ)
    (hU : U * Uᴴ = 1) (hU' : Uᴴ * U = 1) :
    Matrix.trace (weldPlus (U * η * Uᴴ)) = Matrix.trace (weldPlus η) :=
  trace_conj_weldPlus η U Uᴴ hU hU'

/-! ### §1c. Resting places: fixed sets are ranges of projections

The pin: the resting place of the motion `v ↦ η *ᵥ v` is its fixed
set. Here that fixed set is exactly the range of `P₊` (and the `−1`
fixed set is the range of `P₋`). -/

/-- A fixed vector rests in the range of `P₊` (T1, direction 1). -/
theorem mulVec_weldPlus_of_fixed (η : Matrix (Fin n) (Fin n) ℂ)
    (v : Fin n → ℂ) (hv : η *ᵥ v = v) :
    weldPlus η *ᵥ v = v := by
  have hvv : v + v = (2 : ℂ) • v := by
    rw [show (2 : ℂ) = 1 + 1 by norm_num, add_smul, one_smul]
  show ((2 : ℂ)⁻¹ • (1 + η)) *ᵥ v = v
  rw [Matrix.smul_mulVec, Matrix.add_mulVec, Matrix.one_mulVec, hv, hvv,
    smul_smul, inv_mul_cancel₀ (show (2 : ℂ) ≠ 0 by norm_num), one_smul]

/-- A vector in the range of `P₊` is fixed by `η` (T1, direction 2). -/
theorem fixed_of_range_weldPlus (η : Matrix (Fin n) (Fin n) ℂ)
    (h : η * η = 1) (v w : Fin n → ℂ) (hw : weldPlus η *ᵥ w = v) :
    η *ᵥ v = v := by
  rw [← hw, Matrix.mulVec_mulVec, weld_mul_plus η h]

/-- **The resting place of `η`** (T1): `η *ᵥ v = v` iff `v` lies in
    the range of `P₊`. The fixed set of the motion is the projection's
    range — the pin, proved. -/
theorem fixed_iff_range_weldPlus (η : Matrix (Fin n) (Fin n) ℂ)
    (h : η * η = 1) (v : Fin n → ℂ) :
    η *ᵥ v = v ↔ ∃ w, weldPlus η *ᵥ w = v :=
  ⟨fun hv => ⟨v, mulVec_weldPlus_of_fixed η v hv⟩,
   fun ⟨w, hw⟩ => fixed_of_range_weldPlus η h v w hw⟩

/-- **The `−1` resting place** (T1): `η *ᵥ v = −v` iff `v` lies in the
    range of `P₋`. -/
theorem neg_fixed_iff_range_weldMinus (η : Matrix (Fin n) (Fin n) ℂ)
    (h : η * η = 1) (v : Fin n → ℂ) :
    η *ᵥ v = -v ↔ ∃ w, weldMinus η *ᵥ w = v := by
  constructor
  · intro hv
    refine ⟨v, ?_⟩
    show ((2 : ℂ)⁻¹ • (1 - η)) *ᵥ v = v
    have hvv : v + v = (2 : ℂ) • v := by
      rw [show (2 : ℂ) = 1 + 1 by norm_num, add_smul, one_smul]
    rw [Matrix.smul_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, hv]
    have hneg : v - -v = v + v := by simp [sub_neg_eq_add]
    rw [hneg, hvv, smul_smul,
      inv_mul_cancel₀ (show (2 : ℂ) ≠ 0 by norm_num), one_smul]
  · rintro ⟨w, hw⟩
    rw [← hw, Matrix.mulVec_mulVec, weld_mul_minus η h, Matrix.neg_mulVec]

/-! ### §1d. Two commuting motions: the nested resting place

For two commuting involutions, the projections commute, and the joint
fixed set — the pin's *intersection* of fixed sets — is the range of
the product projection. -/

/-- The plus-projections of two commuting involutions commute (T1). -/
theorem weldPlus_comm (η₁ η₂ : Matrix (Fin n) (Fin n) ℂ)
    (hcomm : η₁ * η₂ = η₂ * η₁) :
    weldPlus η₁ * weldPlus η₂ = weldPlus η₂ * weldPlus η₁ := by
  have e1 : (1 + η₁) * (1 + η₂) = 1 + η₁ + η₂ + η₁ * η₂ := by noncomm_ring
  have e2 : (1 + η₂) * (1 + η₁) = 1 + η₁ + η₂ + η₁ * η₂ := by
    have e2' : (1 + η₂) * (1 + η₁) = 1 + η₂ + η₁ + η₂ * η₁ := by noncomm_ring
    rw [e2', hcomm]; abel
  unfold weldPlus
  rw [smul_mul_smul_mat, smul_mul_smul_mat, e1, e2]

/-- A commuting involution passes through the other's projection (T1). -/
theorem weldPlus_mul_comm (η₁ η₂ : Matrix (Fin n) (Fin n) ℂ)
    (hcomm : η₁ * η₂ = η₂ * η₁) :
    η₂ * weldPlus η₁ = weldPlus η₁ * η₂ := by
  have e1 : η₂ * (1 + η₁) = η₂ + η₂ * η₁ := by
    rw [mul_add, mul_one]
  have e2 : (1 + η₁) * η₂ = η₂ + η₁ * η₂ := by
    rw [add_mul, one_mul]
  unfold weldPlus
  rw [Matrix.mul_smul, Matrix.smul_mul, e1, e2, hcomm]

/-- **The nested resting place** (T1): for commuting involutions
    `η₁, η₂`, a vector is fixed by BOTH motions iff it lies in the
    range of the product projection `P₊(η₁) * P₊(η₂)`. Intersection
    of fixed sets = range of the product — the pin, proved. -/
theorem joint_fixed_iff_range (η₁ η₂ : Matrix (Fin n) (Fin n) ℂ)
    (h₁ : η₁ * η₁ = 1) (h₂ : η₂ * η₂ = 1)
    (hcomm : η₁ * η₂ = η₂ * η₁) (v : Fin n → ℂ) :
    (η₁ *ᵥ v = v ∧ η₂ *ᵥ v = v) ↔
      ∃ w, (weldPlus η₁ * weldPlus η₂) *ᵥ w = v := by
  constructor
  · rintro ⟨hv₁, hv₂⟩
    refine ⟨v, ?_⟩
    rw [← Matrix.mulVec_mulVec, mulVec_weldPlus_of_fixed η₂ v hv₂,
      mulVec_weldPlus_of_fixed η₁ v hv₁]
  · rintro ⟨w, hw⟩
    have hv : v = weldPlus η₁ *ᵥ (weldPlus η₂ *ᵥ w) := by
      rw [← hw, ← Matrix.mulVec_mulVec]
    have sin : η₂ *ᵥ (weldPlus η₂ *ᵥ w) = weldPlus η₂ *ᵥ w := by
      rw [Matrix.mulVec_mulVec, weld_mul_plus η₂ h₂]
    constructor
    · rw [hv]
      exact (Matrix.mulVec_mulVec _ _ _).trans (by rw [weld_mul_plus η₁ h₁])
    · rw [hv]
      exact (Matrix.mulVec_mulVec _ _ _).trans
        ((by rw [weldPlus_mul_comm η₁ η₂ hcomm] :
          (η₂ * weldPlus η₁) *ᵥ (weldPlus η₂ *ᵥ w)
            = (weldPlus η₁ * η₂) *ᵥ (weldPlus η₂ *ᵥ w)).trans
          ((Matrix.mulVec_mulVec _ _ _).symm.trans (by rw [sin])))

/-! ## §2. Face A — correction term + grading split (Dial 1-B + 2-A)

The "curved correction": `η ↦ η + A`. The clean true gadget is an
*anticommuting* correction with `A² = 1`: then `(η + A)² = 2`, and
dividing by any `c` with `c² = 2` gives a genuine new involution.
On the concrete arena the correction can only live on a mixed block
(an anticommuting `A` with `A² = 1` on the whole space would force
signature `(2,2)`), so §2b builds it on the `{2,3}` block of the
`(3,1)` arena: there the corrected involution is the Hadamard block
`(η_block + A)/√2`. -/

/-- The corrected involution, parametrized form: `η' = c⁻¹ • (η + A)`
    with `c² = 2`. -/
noncomputable def corrInv (c : ℂ) (η A : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  c⁻¹ • (η + A)

/-- The unnormalized correction squares to `2` (T1): from `η² = 1`,
    `A² = 1`, and anticommutation `ηA + Aη = 0`, the cross terms die
    and `(η + A)² = (2 : ℂ) • 1`. -/
theorem corr_add_sq (η A : Matrix (Fin n) (Fin n) ℂ)
    (hη : η * η = 1) (hA : A * A = 1) (hac : η * A + A * η = 0) :
    (η + A) * (η + A) = (2 : ℂ) • 1 := by
  have e : (η + A) * (η + A) = η * η + (η * A + A * η) + A * A := by
    noncomm_ring
  rw [e, hη, hA, hac, add_zero, ← two_smul_mat]

/-- The corrected involution is an involution (T1): given `c² = 2`,
    `(c⁻¹ • (η + A))² = 1`. -/
theorem corrInv_sq (c : ℂ) (η A : Matrix (Fin n) (Fin n) ℂ)
    (hc : c * c = 2) (hη : η * η = 1) (hA : A * A = 1)
    (hac : η * A + A * η = 0) :
    corrInv c η A * corrInv c η A = 1 := by
  unfold corrInv
  rw [smul_mul_smul_mat, corr_add_sq η A hη hA hac, smul_smul, ← mul_inv, hc,
    inv_mul_cancel₀ (show (2 : ℂ) ≠ 0 by norm_num), one_smul]

/-- Face A rests (T1): the fixed set of the corrected involution is
    the range of its plus-projection — §1's resting place, applied. -/
theorem corrInv_fixed_iff (c : ℂ) (η A : Matrix (Fin n) (Fin n) ℂ)
    (hc : c * c = 2) (hη : η * η = 1) (hA : A * A = 1)
    (hac : η * A + A * η = 0) (v : Fin n → ℂ) :
    corrInv c η A *ᵥ v = v ↔ ∃ w, weldPlus (corrInv c η A) *ᵥ w = v :=
  fixed_iff_range_weldPlus _ (corrInv_sq c η A hc hη hA hac) v

/-! ### §2b. The concrete arena: a (3,1) involution, corrected on a block

`η = diag(1,1,1,−1)` on `ℂ⁴`. The correction `A` swaps the third
(`+`) and fourth (`−`) directions; it anticommutes with `η`, and
`A²` is the block projection — `A² = 1` *on its block*. The corrected
involution keeps the unmixed directions and puts the Hadamard block
`(1/√2)·[[1, 1], [1, −1]]` on the mixed block. -/

/-- The arena involution: `diag(1, 1, 1, −1)` — signature `(3,1)`,
    as INPUT (cf. `signature_not_determined`). -/
def etaArena : Matrix (Fin 4) (Fin 4) ℂ := Matrix.diagonal ![1, 1, 1, -1]

/-- The unmixed top block: `diag(1, 1, 0, 0)`. -/
def etaTop : Matrix (Fin 4) (Fin 4) ℂ := Matrix.diagonal ![1, 1, 0, 0]

/-- The mixed block's involution part: `diag(0, 0, 1, −1)`. -/
def blockEta : Matrix (Fin 4) (Fin 4) ℂ := Matrix.diagonal ![0, 0, 1, -1]

/-- The mixed block's support projection: `diag(0, 0, 1, 1)`. -/
def blockQ : Matrix (Fin 4) (Fin 4) ℂ := Matrix.diagonal ![0, 0, 1, 1]

/-- The correction: the swap of the two mixed directions. -/
def corrSwap : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.of ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 1], ![0, 0, 1, 0]]

/-- The mixed block, whole: `blockEta + corrSwap`. -/
def blockPart : Matrix (Fin 4) (Fin 4) ℂ := blockEta + corrSwap

/-- The corrected arena involution: unmixed directions untouched,
    Hadamard block `(η_block + A)/√2` on the mixed block. -/
noncomputable def etaCorr : Matrix (Fin 4) (Fin 4) ℂ :=
  etaTop + sqrt2c⁻¹ • blockPart

/-- Entry characterization of the correction swap (T1). -/
theorem corrSwap_apply (i j : Fin 4) :
    corrSwap i j = if (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2) then 1 else 0 := by
  fin_cases i <;> fin_cases j <;> simp [corrSwap]

/-- Diagonal-left multiplication, entry form (T1 helper). -/
theorem diag_mul_apply {m : ℕ} (v : Fin m → ℂ)
    (M : Matrix (Fin m) (Fin m) ℂ) (i j : Fin m) :
    (Matrix.diagonal v * M) i j = v i * M i j := by
  have h0 : ∀ k : Fin m, k ≠ i → (Matrix.diagonal v) i k * M k j = 0 := by
    intro k hk
    rw [Matrix.diagonal_apply_ne _ (Ne.symm hk), zero_mul]
  rw [Matrix.mul_apply,
    Finset.sum_eq_single_of_mem i (Finset.mem_univ i) (fun k _ hk => h0 k hk),
    Matrix.diagonal_apply_eq]

/-- Diagonal-right multiplication, entry form (T1 helper). -/
theorem mul_diag_apply {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ)
    (v : Fin m → ℂ) (i j : Fin m) :
    (M * Matrix.diagonal v) i j = M i j * v j := by
  have h0 : ∀ k : Fin m, k ≠ j → M i k * (Matrix.diagonal v) k j = 0 := by
    intro k hk
    rw [Matrix.diagonal_apply_ne _ hk, mul_zero]
  rw [Matrix.mul_apply,
    Finset.sum_eq_single_of_mem j (Finset.mem_univ j) (fun k _ hk => h0 k hk),
    Matrix.diagonal_apply_eq]

theorem etaArena_sq : etaArena * etaArena = 1 := by
  unfold etaArena
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  fin_cases i <;> simp

/-- The arena splits as unmixed top + mixed block (T1). -/
theorem etaArena_eq : etaArena = etaTop + blockEta := by
  unfold etaArena etaTop blockEta
  rw [Matrix.diagonal_add]
  congr 1
  funext i
  fin_cases i <;> simp

theorem etaTop_sq : etaTop * etaTop = etaTop := by
  unfold etaTop
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  fin_cases i <;> simp

/-- `A² = 1` on its block, honestly stated (T1): the correction
    squared is the block support projection. -/
theorem corrSwap_sq : corrSwap * corrSwap = blockQ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, corrSwap_apply, blockQ,
      Matrix.diagonal]

/-- The block involution squared is the block projection (T1). -/
theorem blockEta_sq : blockEta * blockEta = blockQ := by
  unfold blockEta blockQ
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  fin_cases i <;> simp

/-- The correction anticommutes with the block involution (T1). -/
theorem anticomm_block : blockEta * corrSwap + corrSwap * blockEta = 0 := by
  ext i j
  unfold blockEta
  rw [Matrix.add_apply, diag_mul_apply, mul_diag_apply, Matrix.zero_apply]
  by_cases hA : corrSwap i j = 0
  · rw [hA]; simp
  · have hsupp : (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2) := by
      by_contra hc
      apply hA
      rw [corrSwap_apply, if_neg hc]
    rcases hsupp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [corrSwap_apply]

/-- Top and block are orthogonal, left (T1): disjoint diagonal
    supports, and the correction lives on the block's rows. -/
theorem etaTop_mul_blockPart : etaTop * blockPart = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.add_apply, etaTop,
      blockPart, blockEta, corrSwap_apply, Matrix.diagonal, Matrix.zero_apply]

/-- Top and block are orthogonal, right (T1). -/
theorem blockPart_mul_etaTop : blockPart * etaTop = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.add_apply, etaTop,
      blockPart, blockEta, corrSwap_apply, Matrix.diagonal, Matrix.zero_apply]

/-- The mixed block, corrected and squared, is `2` on its support
    (T1): `(blockEta + A)² = (2 : ℂ) • blockQ` — the arena form of
    `corr_add_sq`, with `blockQ` in the role of `1`. -/
theorem blockPart_sq : blockPart * blockPart = (2 : ℂ) • blockQ := by
  have e : blockPart * blockPart
      = (blockEta * blockEta + corrSwap * corrSwap)
        + (blockEta * corrSwap + corrSwap * blockEta) := by
    unfold blockPart; noncomm_ring
  rw [e, blockEta_sq, corrSwap_sq, anticomm_block, add_zero, ← two_smul_mat]

/-- Top + block support = identity (T1). -/
theorem etaTop_add_blockQ : etaTop + blockQ = 1 := by
  unfold etaTop blockQ
  rw [Matrix.diagonal_add, ← Matrix.diagonal_one]
  congr 1
  funext i
  fin_cases i <;> simp

/-- **The corrected arena involution is an involution** (T1):
    `etaCorr² = 1`. The Hadamard block squares to the identity on its
    block, the top is untouched, and the two are orthogonal. -/
theorem etaCorr_sq : etaCorr * etaCorr = 1 := by
  have e : etaCorr * etaCorr
      = etaTop * etaTop + (sqrt2c⁻¹ * sqrt2c⁻¹) • (blockPart * blockPart) := by
    unfold etaCorr
    simp only [add_mul, mul_add, Matrix.mul_smul, Matrix.smul_mul,
      etaTop_mul_blockPart, blockPart_mul_etaTop, smul_zero, add_zero, zero_add]
    rw [smul_smul]
  rw [e, etaTop_sq, blockPart_sq, smul_smul, sqrt2c_inv_mul_self,
    inv_mul_cancel₀ (show (2 : ℂ) ≠ 0 by norm_num), one_smul, etaTop_add_blockQ]

theorem trace_etaTop : Matrix.trace etaTop = 2 := by
  unfold etaTop
  rw [Matrix.trace_diagonal, Fin.sum_univ_four]
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three]

theorem trace_blockEta : Matrix.trace blockEta = 0 := by
  unfold blockEta
  rw [Matrix.trace_diagonal, Fin.sum_univ_four]
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three]

theorem trace_corrSwap : Matrix.trace corrSwap = 0 := by
  have hdiag : ∀ i : Fin 4, corrSwap i i = 0 := by
    intro i
    fin_cases i <;> simp [corrSwap_apply]
  show (∑ i, corrSwap i i) = 0
  rw [Fin.sum_univ_four, hdiag 0, hdiag 1, hdiag 2, hdiag 3]; simp

theorem trace_blockPart : Matrix.trace blockPart = 0 := by
  unfold blockPart
  rw [Matrix.trace_add, trace_blockEta, trace_corrSwap, add_zero]

theorem trace_etaArena : Matrix.trace etaArena = 2 := by
  unfold etaArena
  rw [Matrix.trace_diagonal, Fin.sum_univ_four]
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three]

/-- The correction does not move the arena's trace (T1):
    `tr etaCorr = 2 = tr etaArena`. (The signature-count consequence
    is linker L2 in §4.) -/
theorem trace_etaCorr : Matrix.trace etaCorr = 2 := by
  unfold etaCorr
  rw [Matrix.trace_add, trace_etaTop, Matrix.trace_smul, trace_blockPart]
  simp

/-- Face A's corrected involution rests (T1): its fixed set is the
    range of its plus-projection. -/
theorem etaCorr_fixed_iff (v : Fin 4 → ℂ) :
    etaCorr *ᵥ v = v ↔ ∃ w, weldPlus etaCorr *ᵥ w = v :=
  fixed_iff_range_weldPlus etaCorr etaCorr_sq v

/-! ## §3. Face B — the Dirac sign and the gap split (Dial 1-C + 2-B)

A different dial setting for the curved input: instead of adding a
correction, read the involution off a Hermitian matrix `D` (the Dirac
operator of the toy): `η_D` = diagonal of signs of `D`'s entries.
The split is then by the SPECTRAL GAP: `H = D²`, and the projection
onto the entries above a threshold `Δ²`. The worked `D` is
`diag(2, 1, −1, −3)`, threshold `Δ² = 2` (between `1` and `4`). -/

/-- The worked spectral data: `D = diag(2, 1, −1, −3)` as a real
    vector — mixed signs, no zeros, gap between `1` and `4` in `D²`. -/
def dR : Fin 4 → ℝ := ![2, 1, -1, -3]

/-- The Dirac matrix: `diag(2, 1, −1, −3)` over `ℂ`. -/
def diracD : Matrix (Fin 4) (Fin 4) ℂ := Matrix.diagonal (fun i => (dR i : ℂ))

/-- The sign vector of `D`'s entries: `(![1, 1, −1, −1] : Fin 4 → ℂ)`. -/
def signVec : Fin 4 → ℂ := ![1, 1, -1, -1]

/-- The sign involution of `D`: `η_D = diag(sign D)`. -/
def etaDirac : Matrix (Fin 4) (Fin 4) ℂ := Matrix.diagonal signVec

/-- The gap Hamiltonian: `H = D * D` — diagonal of squares. -/
def gapH : Matrix (Fin 4) (Fin 4) ℂ := diracD * diracD

/-- The above-gap projection for threshold `Δ² = 2`: selects the
    entries with `dᵢ² ≥ 2`, i.e. indices `{0, 3}` (squares `4, 9`). -/
def gapProj : Matrix (Fin 4) (Fin 4) ℂ := Matrix.diagonal ![1, 0, 0, 1]

/-- The below-gap projection: indices `{1, 2}` (squares `1, 1`). -/
def belowProj : Matrix (Fin 4) (Fin 4) ℂ := Matrix.diagonal ![0, 1, 1, 0]

/-- `signVec` really is the sign of `dR` (T1): entrywise,
    `signVec i = if 0 < dR i then 1 else −1`. -/
theorem signVec_is_sign (i : Fin 4) :
    signVec i = if 0 < dR i then 1 else -1 := by
  fin_cases i <;> simp [signVec, dR]

/-- The sign involution squares to `1` (T1) — so §1 applies to it. -/
theorem etaDirac_sq : etaDirac * etaDirac = 1 := by
  unfold etaDirac signVec
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  fin_cases i <;> simp

/-- The sign involution is Hermitian (T1). -/
theorem etaDirac_hermitian : etaDirac.IsHermitian := by
  unfold etaDirac signVec
  rw [Matrix.isHermitian_diagonal_iff]
  intro i
  fin_cases i <;> simp [IsSelfAdjoint]

/-- `D` itself is Hermitian (T1): its entries are real casts. -/
theorem diracD_hermitian : diracD.IsHermitian := by
  unfold diracD
  rw [Matrix.isHermitian_diagonal_iff]
  intro i
  simp [IsSelfAdjoint, Complex.conj_ofReal]

/-- Face A's machinery, computed on Face B's involution (T1):
    `P₊(η_D)` is exactly the projection onto the POSITIVE spectral
    subspace of `D` — the diagonal `0/1` matrix `diag(1, 1, 0, 0)`. -/
theorem weldPlus_etaDirac :
    weldPlus etaDirac = Matrix.diagonal ![1, 1, 0, 0] := by
  unfold weldPlus etaDirac signVec
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply,
      Matrix.diagonal] <;> ring

/-- `H = D²` is the diagonal of entry squares (T1). -/
theorem gapH_diagonal :
    gapH = Matrix.diagonal (fun i => (dR i : ℂ) * (dR i : ℂ)) := by
  unfold gapH diracD
  rw [Matrix.diagonal_mul_diagonal]

/-- `H` computed: `diag(4, 1, 1, 9)` (T1). No zero eigenvalue —
    the gap of the worked example. -/
theorem gapH_eq : gapH = Matrix.diagonal ![4, 1, 1, 9] := by
  rw [gapH_diagonal]
  congr 1
  funext i
  fin_cases i <;>
    norm_num [dR, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.cons_val_three]

theorem gapProj_idem : gapProj * gapProj = gapProj := by
  unfold gapProj
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  fin_cases i <;> simp

theorem belowProj_idem : belowProj * belowProj = belowProj := by
  unfold belowProj
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  fin_cases i <;> simp

/-- The gap split is complementary (T1): above + below = identity. -/
theorem gapProj_add_below : gapProj + belowProj = 1 := by
  unfold gapProj belowProj
  rw [Matrix.diagonal_add, ← Matrix.diagonal_one]
  congr 1
  funext i
  fin_cases i <;> simp

/-- The two sectors are orthogonal (T1). -/
theorem gapProj_mul_below : gapProj * belowProj = 0 := by
  unfold gapProj belowProj
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_zero]
  congr 1
  funext i
  fin_cases i <;> simp

/-- Scalar on a basis vector moves inside the spike (T1 helper). -/
theorem smul_single_one (c : ℂ) (i : Fin 4) :
    c • Pi.single i (1 : ℂ) = Pi.single i c := by
  funext j
  simp only [Pi.smul_apply, Pi.single_apply]
  split_ifs <;> simp

/-- The gap eigenvalue statement on basis vectors (T1):
    `H eᵢ = dᵢ² • eᵢ`. Every eigenvalue is a square of a nonzero
    entry — `0`-free by computation (`gapH_eq`), and above/below
    the threshold as `gap_dichotomy` says. -/
theorem gap_eigen (i : Fin 4) :
    gapH *ᵥ Pi.single i (1 : ℂ)
      = ((dR i : ℂ) * (dR i : ℂ)) • Pi.single i (1 : ℂ) := by
  rw [gapH_diagonal, Matrix.diagonal_mulVec_single, mul_one, ← smul_single_one]

/-- The dichotomy at threshold `Δ² = 2` (T1): every `dᵢ²` is either
    exactly `1` (below gap) or at least `2` (above gap). Nothing
    lives in between — that emptiness IS the gap of this example. -/
theorem gap_dichotomy (i : Fin 4) :
    (dR i) ^ 2 = 1 ∨ (2 : ℝ) ≤ (dR i) ^ 2 := by
  fin_cases i <;>
    norm_num [dR, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.cons_val_three]

/-- The above-gap projection acts on basis vectors by the threshold
    test itself (T1): `gapProj eᵢ = (1 if dᵢ² ≥ 2 else 0) • eᵢ`. -/
theorem gapProj_single (i : Fin 4) :
    gapProj *ᵥ Pi.single i (1 : ℂ)
      = (if (2 : ℝ) ≤ (dR i) ^ 2 then (1 : ℂ) else 0) • Pi.single i (1 : ℂ) := by
  rw [smul_single_one]
  unfold gapProj
  rw [Matrix.diagonal_mulVec_single, mul_one]
  congr 1
  fin_cases i <;>
    norm_num [dR, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.cons_val_three]

/-! ## §4. The duality linkers — why this is ONE module

The two faces are not two toys in one file: Face B's involution
satisfies Face A's core hypothesis (§1), Face A's correction on the
worked arena provably does not move the trace count that Face B
reads off, and both faces' fixed sets are the same pin's resting
places. Signature enters through the INPUT (`D`, resp. the arena
`η`) in both faces — echoing `signature_not_determined` in
`ThetLogos.EdgeSignature`: never derived, always data. -/

/-! ### L1. Face B is an instance of the core (§1 applies verbatim) -/

theorem trace_etaDirac : Matrix.trace etaDirac = 0 := by
  unfold etaDirac signVec
  rw [Matrix.trace_diagonal, Fin.sum_univ_four]
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three]

/-- L1 (T1): the trace formula of §1, run on Face B's `η_D`, gives
    the `(2,2)` signature count of the worked `D = diag(2,1,−1,−3)`:
    two positive, two negative directions. -/
theorem signature_etaDirac :
    Matrix.trace (weldPlus etaDirac) = 2 ∧
      Matrix.trace (weldMinus etaDirac) = 2 := by
  constructor
  · rw [trace_weldPlus, trace_etaDirac]; norm_num
  · rw [trace_weldMinus, trace_etaDirac]; norm_num

/-- L1 companion (T1): the same formula on Face A's `(3,1)` arena
    gives `3` — the count follows the INPUT (`tr η = +2` versus
    `tr η_D = 0`). A `(3,1)`-shaped `D` would give `(3,1)` here.
    Signature is data in both faces; neither derives it. -/
theorem trace_weldPlus_etaArena : Matrix.trace (weldPlus etaArena) = 3 := by
  rw [trace_weldPlus, trace_etaArena]; norm_num

/-- L1 resting (T1): Face B's involution rests on the range of its
    plus-projection — §1's resting place, second face. -/
theorem etaDirac_fixed_iff (v : Fin 4 → ℂ) :
    etaDirac *ᵥ v = v ↔ ∃ w, weldPlus etaDirac *ᵥ w = v :=
  fixed_iff_range_weldPlus etaDirac etaDirac_sq v

/-! ### L2. Correction stability on the arena (the worked example)

The curved correction of §2b does not move the signature count:
`P₊(etaCorr)` and `P₊(etaArena)` have the SAME trace — even though
the projections themselves genuinely differ (`weldPlus_etaCorr_ne`).
The general finrank-stability theorem behind this example is priced
in the header, not proved. -/

/-- L2 (T1): the corrected and uncorrected plus-projections have
    equal traces on the arena. -/
theorem trace_weldPlus_etaCorr :
    Matrix.trace (weldPlus etaCorr) = Matrix.trace (weldPlus etaArena) := by
  rw [trace_weldPlus, trace_weldPlus, trace_etaCorr, trace_etaArena]

/-- L2, valued (T1): both traces are `3`. -/
theorem trace_weldPlus_etaCorr_value : Matrix.trace (weldPlus etaCorr) = 3 := by
  rw [trace_weldPlus_etaCorr, trace_weldPlus_etaArena]

/-- L2 is not vacuity (T1): the two plus-projections DIFFER as
    matrices — their `(2,3)` entries are `(2:ℂ)⁻¹ * √2⁻¹ ≠ 0`
    (corrected, Hadamard mixing) versus `0` (uncorrected diagonal).
    The correction moves the subspace; it does not move its counted
    dimension. -/
theorem weldPlus_etaCorr_ne : weldPlus etaCorr ≠ weldPlus etaArena := by
  intro hcon
  have h23 : (weldPlus etaCorr) 2 3 = (weldPlus etaArena) 2 3 :=
    congrFun (congrFun hcon 2) 3
  have hEC : etaCorr 2 3 = sqrt2c⁻¹ := by
    show (etaTop + sqrt2c⁻¹ • blockPart) 2 3 = sqrt2c⁻¹
    rw [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    have hT : etaTop 2 3 = 0 := by
      show (Matrix.diagonal ![1, 1, 0, 0] : Matrix (Fin 4) (Fin 4) ℂ) 2 3 = 0
      exact Matrix.diagonal_apply_ne _ (by decide)
    have hB : blockPart 2 3 = 1 := by
      show (blockEta + corrSwap) 2 3 = 1
      rw [Matrix.add_apply]
      have hE : blockEta 2 3 = 0 := by
        show (Matrix.diagonal ![0, 0, 1, -1] : Matrix (Fin 4) (Fin 4) ℂ) 2 3 = 0
        exact Matrix.diagonal_apply_ne _ (by decide)
      rw [hE, corrSwap_apply]
      simp
    rw [hT, hB, zero_add, mul_one]
  have hL : (weldPlus etaCorr) 2 3 = (2 : ℂ)⁻¹ * sqrt2c⁻¹ := by
    show ((2 : ℂ)⁻¹ • (1 + etaCorr)) 2 3 = (2 : ℂ)⁻¹ * sqrt2c⁻¹
    rw [Matrix.smul_apply, smul_eq_mul, Matrix.add_apply,
      Matrix.one_apply_ne (show (2 : Fin 4) ≠ 3 by decide), zero_add, hEC]
  have hR : (weldPlus etaArena) 2 3 = 0 := by
    show ((2 : ℂ)⁻¹ • (1 + etaArena)) 2 3 = 0
    rw [Matrix.smul_apply, Matrix.add_apply,
      Matrix.one_apply_ne (show (2 : Fin 4) ≠ 3 by decide)]
    have hA : etaArena 2 3 = 0 := by
      show (Matrix.diagonal ![1, 1, 1, -1] : Matrix (Fin 4) (Fin 4) ℂ) 2 3 = 0
      exact Matrix.diagonal_apply_ne _ (by decide)
    rw [hA, add_zero, smul_zero]
  rw [hL, hR] at h23
  exact mul_ne_zero (inv_ne_zero (show (2 : ℂ) ≠ 0 by norm_num))
    (inv_ne_zero sqrt2c_ne_zero) h23

/-! ### Axiom audit (house style)

Every headline below depends on exactly the standard three axioms —
`propext`, `Classical.choice`, `Quot.sound` — and nothing else. -/

#print axioms weldPlus_idem
#print axioms trace_weldPlus
#print axioms conj_weldPlus
#print axioms trace_conj_weldPlus
#print axioms fixed_iff_range_weldPlus
#print axioms joint_fixed_iff_range
#print axioms corrInv_sq
#print axioms etaCorr_sq
#print axioms etaDirac_sq
#print axioms weldPlus_etaDirac
#print axioms gap_eigen
#print axioms signature_etaDirac
#print axioms trace_weldPlus_etaCorr

end ThetLogos
