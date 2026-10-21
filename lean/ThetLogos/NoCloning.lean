import Mathlib.Tactic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Sqrt

open scoped Matrix

/-!
# ThetLogos.NoCloning — qubit gates and the no-cloning theorem (T1 target)

HONESTY LEDGER (read before citing):

- This module is the **B12 first attack** of the breakdown ledger
  (`whitepaper/breakdown-ledger-scoping-DRAFT-2026-10-20.md`, entry B12):
  quantum-information primitives — the Pauli gates and Hadamard as
  concrete unitary matrices on `ℂ²`, and the finite no-cloning theorem.
  Expected verdict on landing: LANDED-T1/T2 (stage theorem: true of any
  finite Hilbert space, with the stage assumption cited, per the
  scoping draft's note to the pad).
- **Status: VERIFIED — STANDS WHOLE (T1).**  Compiled green
  2026-10-21 (`lake build ThetLogos.NoCloning`, 3,186 jobs,
  0 errors); parent-verified: `.olean` present, strict recount 18,
  incompleteness census 0 on comment-stripped source, axioms on the
  six checked headline theorems standard only (`propext`,
  `Classical.choice`, `Quot.sound`).  Repairs in the open, none
  touching a statement: one import path, the root-namespace
  `dotProduct`, explicit scalar-field argument `inner ℂ` throughout
  (this pin's `Inner.inner` signature, matching corpus usage),
  `hadamard` marked `noncomputable`, and a `simp`-to-`rw`
  restructure of the matrix-identity proofs (simp matching fails on
  `Matrix.of`-wrapped literals in this pin; the same lemmas succeed
  by rewrite).
- **Formulation choice (composite system).**  The no-cloning core is
  stated abstractly: `V` and `W` are complex inner product spaces, and
  the composite is any map `t : V → V → W` satisfying the single
  property the proof uses, the tensor inner-product law
  `inner ℂ (t a b) (t c d) = inner ℂ a c * inner ℂ b d`.  The "cloning map"
  `U : W → W` is assumed only to preserve inner products (unitarity in
  the form the proof consumes; linearity is not needed and not
  assumed).  This avoids the Mathlib tensor-product API entirely while
  losing nothing: every genuine tensor product supplies such a `t`,
  and the standard three-line proof goes through verbatim.  The
  concrete qubit instance is `EuclideanSpace ℂ (Fin 2)` with the pair
  `|0⟩` and `|+⟩ = H|0⟩`, whose inner product is `1 / √2`.
- **What is proved.**  (i) Any cloning datum forces
  `inner ℂ ψ φ = inner ℂ ψ φ * inner ℂ ψ φ` for every pair, hence the inner
  product of any two states is `0` or `1`; a pair with inner product
  strictly between (e.g. `1 / √2`) therefore kills every cloning
  datum.  (ii) The Pauli matrices `X, Y, Z` and the Hadamard matrix
  `H` on `ℂ²` satisfy `M * M = 1` and are unitary in the form
  `M * Mᴴ = 1 ∧ Mᴴ * M = 1`.  (iii) Gate actions:
  `X|0⟩ = |1⟩`, `X|1⟩ = |0⟩`, `Z|1⟩ = -|1⟩` (phase flip), and
  `H|0⟩ = |+⟩`.
- **Fences.**  Finite-dimensional throughout.  Nothing here is a claim
  about physical devices, laboratories, or implementations.  Spin–
  statistics is not touched (scoping entry B7/B12 fence).  Gate-set
  universality / Solovay–Kitaev is not touched (declared import in
  B12, priced separately).  No-cloning says exactly what it says:
  unitaries on the stage do not clone; nothing more is inferred.
-/

namespace ThetLogos

/-! ## The no-cloning core (abstract inner product spaces) -/

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W]

/-- The inner-product identity forced by any cloning datum: if `t`
builds composites with the tensor inner-product law, `U` preserves
inner products, the blank state `e` satisfies `inner ℂ e e = 1`, and
`U (t ψ e) = t ψ ψ` for all `ψ`, then every pair `ψ, φ` satisfies
`inner ℂ ψ φ = inner ℂ ψ φ * inner ℂ ψ φ`.  This is the whole content of
the no-cloning proof, isolated as an identity. -/
lemma cloning_inner_eq {t : V → V → W} {U : W → W} {e : V}
    (ht : ∀ a b c d, inner ℂ (t a b) (t c d) = inner ℂ a c * inner ℂ b d)
    (hU : ∀ x y, inner ℂ (U x) (U y) = inner ℂ x y)
    (he : inner ℂ e e = (1 : ℂ))
    (hclone : ∀ ψ, U (t ψ e) = t ψ ψ) (ψ φ : V) :
    inner ℂ ψ φ = inner ℂ ψ φ * inner ℂ ψ φ := by
  calc
    inner ℂ ψ φ = inner ℂ ψ φ * inner ℂ e e := by rw [he, mul_one]
    _ = inner ℂ (t ψ e) (t φ e) := (ht ψ e φ e).symm
    _ = inner ℂ (U (t ψ e)) (U (t φ e)) := (hU _ _).symm
    _ = inner ℂ (t ψ ψ) (t φ φ) := by rw [hclone ψ, hclone φ]
    _ = inner ℂ ψ φ * inner ℂ ψ φ := ht ψ ψ φ φ

/-- Consequently the inner product of any two states, under any
cloning datum, is `0` or `1`: cloned states are orthogonal or equal
in inner product. -/
theorem cloning_inner_eq_zero_or_one {t : V → V → W} {U : W → W} {e : V}
    (ht : ∀ a b c d, inner ℂ (t a b) (t c d) = inner ℂ a c * inner ℂ b d)
    (hU : ∀ x y, inner ℂ (U x) (U y) = inner ℂ x y)
    (he : inner ℂ e e = (1 : ℂ))
    (hclone : ∀ ψ, U (t ψ e) = t ψ ψ) (ψ φ : V) :
    inner ℂ ψ φ = 0 ∨ inner ℂ ψ φ = 1 := by
  have h := cloning_inner_eq ht hU he hclone ψ φ
  have h2 : inner ℂ ψ φ * (inner ℂ ψ φ - 1) = 0 := by
    linear_combination -h
  rcases mul_eq_zero.mp h2 with h0 | h1
  · exact Or.inl h0
  · exact Or.inr (sub_eq_zero.mp h1)

/-- **No-cloning, finite case.**  Given any composite map with the
tensor inner-product law, any inner-product-preserving `U`, and a
blank state `e` with `inner ℂ e e = 1`, the cloning property
`U (t ψ e) = t ψ ψ` for all `ψ` is impossible as soon as two states
have inner product different from both `0` and `1`. -/
theorem no_cloning {t : V → V → W} {U : W → W} {e : V}
    (ht : ∀ a b c d, inner ℂ (t a b) (t c d) = inner ℂ a c * inner ℂ b d)
    (hU : ∀ x y, inner ℂ (U x) (U y) = inner ℂ x y)
    (he : inner ℂ e e = (1 : ℂ))
    (hclone : ∀ ψ, U (t ψ e) = t ψ ψ) (ψ φ : V)
    (hz0 : inner ℂ ψ φ ≠ 0) (hz1 : inner ℂ ψ φ ≠ 1) :
    False := by
  rcases cloning_inner_eq_zero_or_one ht hU he hclone ψ φ with h | h
  · exact hz0 h
  · exact hz1 h

/-! ## The scalar `1 / √2` and the concrete qubit pair -/

/-- The scalar `1 / √2`, as a complex number (the cast of the real
inverse).  This is the inner product `⟨0|+⟩` and the Hadamard
entry. -/
noncomputable def invSqrtTwo : ℂ := ((Real.sqrt 2)⁻¹ : ℝ)

/-- The arithmetic heart of Hadamard unitarity: `(1 / √2)² = 1 / 2`
in `ℂ`. -/
lemma invSqrtTwo_mul_self : invSqrtTwo * invSqrtTwo = 1 / 2 := by
  have hr : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = (1 / 2 : ℝ) := by
    rw [← mul_inv, Real.mul_self_sqrt (by norm_num)]; norm_num
  unfold invSqrtTwo
  rw [← Complex.ofReal_mul, hr]
  norm_num

/-- `invSqrtTwo` is real, hence fixed by `star`. -/
lemma star_invSqrtTwo : star invSqrtTwo = invSqrtTwo := by
  unfold invSqrtTwo
  rw [Complex.star_def, Complex.conj_ofReal]

/-- **No-cloning for the qubit pair `|0⟩`, `|+⟩`.**  In
`EuclideanSpace ℂ (Fin 2)`, no composite map with the tensor
inner-product law, no inner-product-preserving `U`, and no blank
state can clone: the pair `|0⟩ = (1, 0)` and
`|+⟩ = (1 / √2, 1 / √2)` has inner product `1 / √2`, which is
neither `0` nor `1`.

Compile-risk note (for the verifying build): the inner-product
computation below goes through `PiLp.inner_apply`; if that simp
route fails on the pinned Mathlib, the fallback is
`EuclideanSpace.inner_eq_star_dot_product` with a `dotProduct`
computation.  The rest of the module does not depend on this
route. -/
theorem no_cloning_euclidean
    (t : EuclideanSpace ℂ (Fin 2) → EuclideanSpace ℂ (Fin 2)
      → EuclideanSpace ℂ (Fin 2))
    (U : EuclideanSpace ℂ (Fin 2) → EuclideanSpace ℂ (Fin 2))
    (e : EuclideanSpace ℂ (Fin 2))
    (ht : ∀ a b c d, inner ℂ (t a b) (t c d) = inner ℂ a c * inner ℂ b d)
    (hU : ∀ x y, inner ℂ (U x) (U y) = inner ℂ x y)
    (he : inner ℂ e e = (1 : ℂ))
    (hclone : ∀ ψ, U (t ψ e) = t ψ ψ) :
    False := by
  have hs0 : invSqrtTwo ≠ 0 := by
    unfold invSqrtTwo
    exact Complex.ofReal_ne_zero.mpr
      (inv_ne_zero (Real.sqrt_ne_zero'.mpr (by norm_num)))
  have hs1 : invSqrtTwo ≠ 1 := by
    intro h
    have h2 : (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) = 1 := h
    have hr : (Real.sqrt 2)⁻¹ = (1 : ℝ) := by exact_mod_cast h2
    have hsqrt : Real.sqrt 2 = 1 := inv_eq_one.mp hr
    have hsq := Real.mul_self_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    rw [hsqrt] at hsq
    norm_num at hsq
  have hinner :
      inner ℂ (!₂[1, 0] : EuclideanSpace ℂ (Fin 2))
          !₂[invSqrtTwo, invSqrtTwo] = invSqrtTwo := by
    simp [PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply]
  refine no_cloning ht hU he hclone
    (!₂[1, 0] : EuclideanSpace ℂ (Fin 2))
    !₂[invSqrtTwo, invSqrtTwo] ?_ ?_
  · rw [hinner]; exact hs0
  · rw [hinner]; exact hs1

/-! ## Qubit gates on `ℂ²` -/

/-- The Pauli `X` gate (bit flip). -/
def pauliX : Matrix (Fin 2) (Fin 2) ℂ := ![![0, 1], ![1, 0]]

/-- The Pauli `Y` gate (bit flip with phase). -/
def pauliY : Matrix (Fin 2) (Fin 2) ℂ :=
  ![![0, -Complex.I], ![Complex.I, 0]]

/-- The Pauli `Z` gate (phase flip). -/
def pauliZ : Matrix (Fin 2) (Fin 2) ℂ := ![![1, 0], ![0, -1]]

/-- The Hadamard gate, with entries `±1 / √2`. -/
noncomputable def hadamard : Matrix (Fin 2) (Fin 2) ℂ :=
  ![![invSqrtTwo, invSqrtTwo], ![invSqrtTwo, -invSqrtTwo]]

/-- The basis state `|0⟩`. -/
def ket0 : Fin 2 → ℂ := ![1, 0]

/-- The basis state `|1⟩`. -/
def ket1 : Fin 2 → ℂ := ![0, 1]

/-- `X² = 1`. -/
theorem pauliX_sq : pauliX * pauliX = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    rw [Matrix.mul_apply, Fin.sum_univ_two] <;> simp [pauliX]

/-- `Y² = 1`. -/
theorem pauliY_sq : pauliY * pauliY = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    rw [Matrix.mul_apply, Fin.sum_univ_two] <;>
    simp [pauliY, Complex.I_mul_I]

/-- `Z² = 1`. -/
theorem pauliZ_sq : pauliZ * pauliZ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    rw [Matrix.mul_apply, Fin.sum_univ_two] <;> simp [pauliZ]

/-- `H² = 1`: the diagonal entries are
`(1 / √2)² + (1 / √2)² = 1` by `invSqrtTwo_mul_self`, and the
off-diagonal entries cancel. -/
theorem hadamard_sq : hadamard * hadamard = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    rw [Matrix.mul_apply, Fin.sum_univ_two] <;> simp [hadamard] <;>
    first
      | linear_combination (2 : ℂ) * invSqrtTwo_mul_self
      | ring

/-- `X` is unitary: `X * Xᴴ = 1 ∧ Xᴴ * X = 1`. -/
theorem pauliX_unitary :
    pauliX * pauliXᴴ = 1 ∧ pauliXᴴ * pauliX = 1 := by
  refine ⟨?_, ?_⟩ <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    rw [Matrix.mul_apply, Fin.sum_univ_two] <;>
    simp only [Matrix.conjTranspose_apply] <;>
    simp [pauliX]

/-- `Y` is unitary: `Y * Yᴴ = 1 ∧ Yᴴ * Y = 1`. -/
theorem pauliY_unitary :
    pauliY * pauliYᴴ = 1 ∧ pauliYᴴ * pauliY = 1 := by
  refine ⟨?_, ?_⟩ <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    rw [Matrix.mul_apply, Fin.sum_univ_two] <;>
    simp only [Matrix.conjTranspose_apply] <;>
    simp [pauliY, Complex.star_def, Complex.conj_I, Complex.I_mul_I]

/-- `Z` is unitary: `Z * Zᴴ = 1 ∧ Zᴴ * Z = 1`. -/
theorem pauliZ_unitary :
    pauliZ * pauliZᴴ = 1 ∧ pauliZᴴ * pauliZ = 1 := by
  refine ⟨?_, ?_⟩ <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    rw [Matrix.mul_apply, Fin.sum_univ_two] <;>
    simp only [Matrix.conjTranspose_apply] <;>
    simp [pauliZ]

/-- `H` is unitary: `H * Hᴴ = 1 ∧ Hᴴ * H = 1`.  The conjugate
transpose contributes no sign because every entry of `H` is real
(`star_invSqrtTwo`). -/
theorem hadamard_unitary :
    hadamard * hadamardᴴ = 1 ∧ hadamardᴴ * hadamard = 1 := by
  refine ⟨?_, ?_⟩ <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    rw [Matrix.mul_apply, Fin.sum_univ_two] <;>
    simp only [Matrix.conjTranspose_apply] <;>
    simp [hadamard, star_invSqrtTwo] <;>
    first
      | linear_combination (2 : ℂ) * invSqrtTwo_mul_self
      | ring

/-- `X|0⟩ = |1⟩`: the bit flip on the first basis state. -/
theorem pauliX_mulVec_ket0 : pauliX *ᵥ ket0 = ket1 := by
  funext i
  fin_cases i <;>
    simp [pauliX, ket0, ket1, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two] <;> norm_num

/-- `X|1⟩ = |0⟩`: the bit flip on the second basis state. -/
theorem pauliX_mulVec_ket1 : pauliX *ᵥ ket1 = ket0 := by
  funext i
  fin_cases i <;>
    simp [pauliX, ket0, ket1, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two] <;> norm_num

/-- `Z|1⟩ = -|1⟩`: the phase flip, on the nose as the vector
`(0, -1)`. -/
theorem pauliZ_mulVec_ket1 : pauliZ *ᵥ ket1 = ![0, -1] := by
  funext i
  fin_cases i <;>
    simp [pauliZ, ket1, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two] <;> norm_num

/-- `H|0⟩ = |+⟩`: Hadamard creates the uniform superposition
`(1 / √2, 1 / √2)` — the same vector whose inner product with
`|0⟩` kills cloning in `no_cloning_euclidean`. -/
theorem hadamard_mulVec_ket0 :
    hadamard *ᵥ ket0 = ![invSqrtTwo, invSqrtTwo] := by
  funext i
  fin_cases i <;>
    simp [hadamard, ket0, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two] <;> norm_num

end ThetLogos
