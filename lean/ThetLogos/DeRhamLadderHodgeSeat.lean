/-
# ThetLogos.DeRhamLadderHodgeSeat — LAD-1: the ℝ Hodge seat at PHI-C

**WORKING LABEL — naming is Jeff's.** The icosidodecahedron chain
complex (PHI-C0/C1, over ℚ: `d1Mat`, `d2Mat`, `d1`, `d2`,
`d1_comp_d2`) carried to ℝ, with per-degree adjoints as linear
maps, the adjoint identity, the three Laplacians
Δ_k = d* d + d d*, and `d² = 0` transported across the cast.
Scoping: `derham-ladder-scoping-2026-11-06.md` §4 (LAD-1);
pin: `DeRhamLadderPin` (LAD-0). Jeff fired 2026-11-06 17:57 EST.

**Seat (K-LAD-SEAT assessed at this brick):** the seat's incidence
is the PHI-C signed face data — content-bearing by construction.
`ladD1_ne_zero` and `ladD2_ne_zero` below prove both boundary maps
are nonzero at this seat while their composition is zero
(`lad_dsq_zero`): `d² = 0` here is a theorem about signed data,
not a vacuity. K-LAD-SEAT does NOT fire.

**Names (K-LAD-NAME):** the `lad*` family in namespace
`ThetLogos.DeRhamLadder` is a fourth, distinct `d`-family — no
collision with PHI-C's `d1/d2`, the partner sector's
`diffOp/supercharge`, or BRST's `d1/d2/brstQ`.

Conventions (house standard for finite ℝ pi-types): the inner
product is `∑ i, x i * y i`; the adjoint of a matrix map is the
transpose-matrix map (spelled `Matrix.transpose`, as PHI-C3's
`d1T` does); Laplacians are stated as matrices, with
`Matrix.mulVecLin` forms where the linear-map statement is the
content. NO CLAIM; dials 0/4; Dial 2 = 0.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Tactic.NormNum
import ThetLogos.IcosidodecaChain
import ThetLogos.IcosidodecaBoundary

namespace ThetLogos
namespace DeRhamLadder

/-- LAD-1: the ∂₁ matrix over ℝ — the cast of PHI-C's `d1Mat`. -/
def ladD1Mat : Matrix (Fin 30) (Fin 60) ℝ :=
  fun v e => Rat.cast (d1Mat v e)

/-- LAD-1: the ∂₂ matrix over ℝ — the cast of PHI-C's `d2Mat`. -/
def ladD2Mat : Matrix (Fin 60) (Fin 32) ℝ :=
  fun e f => Rat.cast (d2Mat e f)

/-- LAD-1: ∂₁ : C¹ → C⁰ over ℝ. -/
noncomputable def ladD1 : (Fin 60 → ℝ) →ₗ[ℝ] (Fin 30 → ℝ) :=
  Matrix.mulVecLin ladD1Mat

/-- LAD-1: ∂₂ : C² → C¹ over ℝ. -/
noncomputable def ladD2 : (Fin 32 → ℝ) →ₗ[ℝ] (Fin 60 → ℝ) :=
  Matrix.mulVecLin ladD2Mat

/-- LAD-1: d₁* : C⁰ → C¹ over ℝ — the transpose-matrix map. -/
noncomputable def ladD1Adj : (Fin 30 → ℝ) →ₗ[ℝ] (Fin 60 → ℝ) :=
  Matrix.mulVecLin (Matrix.transpose ladD1Mat)

/-- LAD-1: d₂* : C¹ → C² over ℝ — the transpose-matrix map. -/
noncomputable def ladD2Adj : (Fin 60 → ℝ) →ₗ[ℝ] (Fin 32 → ℝ) :=
  Matrix.mulVecLin (Matrix.transpose ladD2Mat)

/-- LAD-1: the adjoint identity at degree 1:
    `⟨d₁ x, y⟩ = ⟨x, d₁* y⟩` for the standard inner product. -/
theorem lad_adjoint_identity₁ (x : Fin 60 → ℝ) (y : Fin 30 → ℝ) :
    ∑ v, ladD1 x v * y v = ∑ e, x e * ladD1Adj y e := by
  simp only [ladD1, ladD1Adj, Matrix.mulVecLin_apply, Matrix.mulVec,
    dotProduct, Matrix.transpose_apply, ladD1Mat, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun v _ => ?_
  ring

/-- LAD-1: the adjoint identity at degree 2:
    `⟨d₂ x, y⟩ = ⟨x, d₂* y⟩`. -/
theorem lad_adjoint_identity₂ (x : Fin 32 → ℝ) (y : Fin 60 → ℝ) :
    ∑ e, ladD2 x e * y e = ∑ f, x f * ladD2Adj y f := by
  simp only [ladD2, ladD2Adj, Matrix.mulVecLin_apply, Matrix.mulVec,
    dotProduct, Matrix.transpose_apply, ladD2Mat, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun f _ => Finset.sum_congr rfl fun e _ => ?_
  ring

/-- LAD-1: entry cast lemma — the ℝ ∂₁ matrix at an entry is
    ∂₁ over ℚ read at that entry (every `d1Mat` entry is −1, 0,
    or 1 by its defining case split). -/
theorem ladD1Mat_apply (v : Fin 30) (e : Fin 60) :
    ladD1Mat v e = if v = edgeTail e then -1 else if v = edgeHead e then 1 else 0 := by
  by_cases h1 : v = edgeTail e
  · rw [if_pos h1]
    simp only [ladD1Mat, d1Mat]
    rw [if_pos h1]
    norm_num
  · by_cases h2 : v = edgeHead e
    · rw [if_neg h1, if_pos h2]
      simp only [ladD1Mat, d1Mat]
      rw [if_neg h1, if_pos h2]
      norm_num
    · rw [if_neg h1, if_neg h2]
      simp only [ladD1Mat, d1Mat]
      rw [if_neg h1, if_neg h2]
      norm_num

/-- LAD-1: entry cast lemma at degree 2 — the ℝ ∂₂ entry is the
    signed face incidence cast to ℝ. -/
theorem ladD2Mat_apply (e : Fin 60) (f : Fin 32) :
    ladD2Mat e f = ((faceSign f e : ℚ) : ℝ) := by
  simp only [ladD2Mat, d2Mat]

/-- LAD-1: `d² = 0` at the matrix level over ℝ, transported from
    PHI-C1's `d1Mat_mul_d2Mat` across the cast. -/
theorem ladD1Mat_mul_ladD2Mat : ladD1Mat * ladD2Mat = 0 := by
  have h := d1Mat_mul_d2Mat
  ext v f
  simp only [Matrix.mul_apply, ladD1Mat, ladD2Mat, Matrix.zero_apply]
  have hv : ∀ e : Fin 60, Rat.cast (d1Mat v e) * Rat.cast (d2Mat e f)
      = Rat.cast (d1Mat v e * d2Mat e f) := fun e =>
    (Rat.cast_mul (d1Mat v e) (d2Mat e f) : ((d1Mat v e * d2Mat e f : ℚ) : ℝ)
      = Rat.cast (d1Mat v e) * Rat.cast (d2Mat e f)).symm
  rw [Finset.sum_congr rfl (fun e _ => hv e)]
  have hcast : (Rat.cast (∑ e, d1Mat v e * d2Mat e f) : ℝ)
      = ∑ e, Rat.cast (d1Mat v e * d2Mat e f) := Rat.cast_sum _ _
  rw [← hcast]
  have hsum : ∑ e, d1Mat v e * d2Mat e f = (0 : ℚ) := by
    have h2 := congrFun (congrFun h v) f
    simpa [Matrix.mul_apply] using h2
  rw [hsum]
  simp

/-- LAD-1: `d² = 0` at the linear-map level over ℝ:
    ∂₁ ∘ ∂₂ = 0 (the transport of PHI-C1's `d1_comp_d2`). -/
theorem lad_dsq_zero : ladD1 ∘ₗ ladD2 = 0 := by
  have h : ladD1 ∘ₗ ladD2 = Matrix.mulVecLin (ladD1Mat * ladD2Mat) := by
    simp only [ladD1, ladD2]
    rw [← Matrix.mulVecLin_mul]
  rw [h, ladD1Mat_mul_ladD2Mat]
  ext x v
  simp [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct]

/-- LAD-1 (K-LAD-SEAT witness): ∂₁ over ℝ is NONZERO at this
    seat — edge 0 = (0, 1) has head 1, so `(∂₁ (single 0 1)) 1 = 1`. -/
theorem ladD1_ne_zero : ladD1 ≠ 0 := by
  intro h
  have h1 := LinearMap.congr_fun h (Pi.single (0 : Fin 60) 1)
  simp only [LinearMap.zero_apply] at h1
  have h2 := congrFun h1 (1 : Fin 30)
  simp only [Pi.zero_apply] at h2
  have hval : ladD1 (Pi.single (0 : Fin 60) 1) (1 : Fin 30) = 1 := by
    simp only [ladD1, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct,
      ladD1Mat_apply]
    rw [Finset.sum_eq_single (0 : Fin 60)]
    · have ht : edgeTail (0 : Fin 60) = 0 := by decide
      have hh : edgeHead (0 : Fin 60) = 1 := by decide
      rw [ht, hh]
      norm_num
    · intro b _ hb
      rw [Pi.single_eq_of_ne hb]
      simp
    · intro hcon
      exact absurd (Finset.mem_univ _) hcon
  rw [hval] at h2
  exact one_ne_zero h2

/-- LAD-1 (K-LAD-SEAT witness): ∂₂ over ℝ is NONZERO at this
    seat — face 0's boundary contains edge 0 = (0, 1) with sign
    +1 (face 0 is the triangle (0, 1, 2) by the probe's tables,
    verified by `decide` on the landed PHI-C data). -/
theorem ladD2_ne_zero : ladD2 ≠ 0 := by
  intro h
  have h1 := LinearMap.congr_fun h (Pi.single (0 : Fin 32) 1)
  simp only [LinearMap.zero_apply] at h1
  have h2 := congrFun h1 (0 : Fin 60)
  simp only [Pi.zero_apply] at h2
  have hval : ladD2 (Pi.single (0 : Fin 32) 1) (0 : Fin 60) = 1 := by
    simp only [ladD2, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct,
      ladD2Mat_apply]
    rw [Finset.sum_eq_single (0 : Fin 32)]
    · norm_num [show faceSign (0 : Fin 32) (0 : Fin 60) = 1 from by decide]
    · intro b _ hb
      rw [Pi.single_eq_of_ne hb]
      simp
    · intro hcon
      exact absurd (Finset.mem_univ _) hcon
  rw [hval] at h2
  exact one_ne_zero h2

/-- LAD-1: the degree-0 Laplacian matrix Δ₀ = d₁ d₁*. -/
def ladLap0Mat : Matrix (Fin 30) (Fin 30) ℝ :=
  ladD1Mat * (Matrix.transpose ladD1Mat)

/-- LAD-1: the degree-1 Laplacian matrix
    Δ₁ = d₁* d₁ + d₂ d₂* (up part + down part). -/
def ladLap1Mat : Matrix (Fin 60) (Fin 60) ℝ :=
  (Matrix.transpose ladD1Mat) * ladD1Mat + ladD2Mat * (Matrix.transpose ladD2Mat)

/-- LAD-1: the degree-2 Laplacian matrix Δ₂ = d₂* d₂. -/
def ladLap2Mat : Matrix (Fin 32) (Fin 32) ℝ :=
  (Matrix.transpose ladD2Mat) * ladD2Mat

/-- LAD-1: Δ₀ as a linear map. -/
noncomputable def ladLap0 : (Fin 30 → ℝ) →ₗ[ℝ] (Fin 30 → ℝ) :=
  Matrix.mulVecLin ladLap0Mat

/-- LAD-1: Δ₁ as a linear map. -/
noncomputable def ladLap1 : (Fin 60 → ℝ) →ₗ[ℝ] (Fin 60 → ℝ) :=
  Matrix.mulVecLin ladLap1Mat

/-- LAD-1: Δ₂ as a linear map. -/
noncomputable def ladLap2 : (Fin 32 → ℝ) →ₗ[ℝ] (Fin 32 → ℝ) :=
  Matrix.mulVecLin ladLap2Mat

/-- LAD-1: Δ₀ = d₁ ∘ d₁* as linear maps (the down-part form). -/
theorem ladLap0_eq : ladLap0 = ladD1 ∘ₗ ladD1Adj := by
  simp only [ladLap0, ladD1, ladD1Adj]
  rw [← Matrix.mulVecLin_mul]
  rfl

/-- LAD-1: Δ₂ = d₂* ∘ d₂ as linear maps (the up-part form). -/
theorem ladLap2_eq : ladLap2 = ladD2Adj ∘ₗ ladD2 := by
  simp only [ladLap2, ladD2, ladD2Adj]
  rw [← Matrix.mulVecLin_mul]
  rfl

/-- LAD-1: Δ₁ = d₁* ∘ d₁ + d₂ ∘ d₂* as linear maps — the middle
    degree carries BOTH parts (the friction named in the scoping
    §3(c): the ladder's Δ_k is a sum, unlike the partner sector's
    pure one-sided Hamiltonians). -/
theorem ladLap1_eq :
    ladLap1 = ladD1Adj ∘ₗ ladD1 + ladD2 ∘ₗ ladD2Adj := by
  simp only [ladLap1, ladD1, ladD1Adj, ladD2, ladD2Adj]
  rw [← Matrix.mulVecLin_mul, ← Matrix.mulVecLin_mul,
    ← Matrix.mulVecLin_add]
  rfl

end DeRhamLadder
end ThetLogos
