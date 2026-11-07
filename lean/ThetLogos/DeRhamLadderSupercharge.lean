/-
# ThetLogos.DeRhamLadderSupercharge — LAD-2: the supercharge package

**WORKING LABEL — naming is Jeff's.** On LAD-1's ℝ Hodge seat
(`DeRhamLadderHodgeSeat`): the total supercharge
`Q = d + d*` on the total graded space C⁰ × C¹ × C² (as a
122 × 122 block matrix), **`Q² = Δ₀ ⊕ Δ₁ ⊕ Δ₂`**, per-degree
energy = sum of squares, `ker Δ_k = ker d_k ∩ ker d*` per
degree, and **harmonic = cohomology**: the harmonic finranks
are (1, 0, 1), identified with PHI-C3's census
(`icosidodeca_census`, consumed by citation, not re-proved).
Scoping: `derham-ladder-scoping-2026-11-06.md` §4 (LAD-2);
pin: `DeRhamLadderPin` (LAD-0).

**K-LAD-FIAT assessed at this brick (the scoping assigns the
assessment here): does NOT fire.** The ≥2-degree content of this
line is new Hodge content, not citation restated: the ℝ adjoints
and Laplacians (LAD-1), the total supercharge with Q² = Δ_total
at three degrees, the per-degree kernel characterizations, and
the harmonic identification below are proved here; PHI-C3's
census is consumed only for the integer rank data, transported
to ℝ by the rank-invariance of the cast boundary matrices:
matrix rank (as finrank of the mulVecLin range) is unchanged
under `Rat.cast` of the entries — the upper bound comes from
the vanishing-minor criterion over ℚ, the lower bound from
pushing one nonvanishing ℚ minor through the cast.

The middle Laplacian Δ₁ is a SUM of an up part and a down part;
the off-diagonal cancellation that makes Q² block-diagonal is
exactly `d² = 0` and its transpose — the ladder's content at
degree 1. NO CLAIM; dials 0/4; Dial 2 = 0.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.Tactic.NormNum
import ThetLogos.DeRhamLadderHodgeSeat
import ThetLogos.IcosidodecaCensus

open scoped Matrix

namespace ThetLogos
namespace DeRhamLadder

/-! ## The total supercharge -/

/-- LAD-2: the total space index type: degrees 0, 1, 2 with
    30, 60, 32 cells — `Fin 30 ⊕ Fin 60 ⊕ Fin 32`. -/
abbrev LadIdx : Type := Fin 30 ⊕ Fin 60 ⊕ Fin 32

/-- LAD-2: the total supercharge matrix `Q = d + d*` on the
    total graded space, in block form: `Q` maps degree k to
    degrees k±1 by `d` (down) and `d*` (up), zero on the
    diagonal blocks and between degrees 0 and 2. -/
def ladQMat : Matrix LadIdx LadIdx ℝ := fun i j =>
  match i, j with
  | Sum.inl v, Sum.inr (Sum.inl e) => ladD1Mat v e
  | Sum.inl v, Sum.inr (Sum.inr _) => 0
  | Sum.inl v1, Sum.inl v2 => 0
  | Sum.inr (Sum.inl e), Sum.inl v => ladD1Mat v e
  | Sum.inr (Sum.inl e1), Sum.inr (Sum.inl e2) => 0
  | Sum.inr (Sum.inl e), Sum.inr (Sum.inr f) => ladD2Mat e f
  | Sum.inr (Sum.inr f), Sum.inl _ => 0
  | Sum.inr (Sum.inr f), Sum.inr (Sum.inl e) => ladD2Mat e f
  | Sum.inr (Sum.inr f1), Sum.inr (Sum.inr f2) => 0

/-- LAD-2: the total Laplacian matrix Δ₀ ⊕ Δ₁ ⊕ Δ₂, block
    diagonal. -/
def ladDeltaMat : Matrix LadIdx LadIdx ℝ := fun i j =>
  match i, j with
  | Sum.inl v1, Sum.inl v2 => ladLap0Mat v1 v2
  | Sum.inl _, Sum.inr (Sum.inl _) => 0
  | Sum.inl _, Sum.inr (Sum.inr _) => 0
  | Sum.inr (Sum.inl _), Sum.inl _ => 0
  | Sum.inr (Sum.inl e1), Sum.inr (Sum.inl e2) => ladLap1Mat e1 e2
  | Sum.inr (Sum.inl _), Sum.inr (Sum.inr _) => 0
  | Sum.inr (Sum.inr _), Sum.inl _ => 0
  | Sum.inr (Sum.inr _), Sum.inr (Sum.inl _) => 0
  | Sum.inr (Sum.inr f1), Sum.inr (Sum.inr f2) => ladLap2Mat f1 f2

/-- LAD-2: the supercharge as a linear map on the total space. -/
noncomputable def ladQ : (LadIdx → ℝ) →ₗ[ℝ] (LadIdx → ℝ) :=
  Matrix.mulVecLin ladQMat

/-- LAD-2: the total Laplacian as a linear map. -/
noncomputable def ladDelta : (LadIdx → ℝ) →ₗ[ℝ] (LadIdx → ℝ) :=
  Matrix.mulVecLin ladDeltaMat

/-! ## Component formulas for Q and the cross-term lemma -/

/-- LAD-2 helper: `Q x` at a degree-0 index. -/
theorem ladQ_apply_inl (x : LadIdx → ℝ) (v : Fin 30) :
    (ladQMat *ᵥ x) (Sum.inl v)
      = ∑ e, ladD1Mat v e * x (Sum.inr (Sum.inl e)) := by
  simp only [Matrix.mulVec, dotProduct]
  rw [Fintype.sum_sum_type]
  simp [ladQMat]

/-- LAD-2 helper: `Q x` at a degree-1 index. -/
theorem ladQ_apply_inr_inl (x : LadIdx → ℝ) (e : Fin 60) :
    (ladQMat *ᵥ x) (Sum.inr (Sum.inl e))
      = (∑ v, ladD1Mat v e * x (Sum.inl v))
        + ∑ f, ladD2Mat e f * x (Sum.inr (Sum.inr f)) := by
  simp only [Matrix.mulVec, dotProduct]
  rw [Fintype.sum_sum_type]
  simp [ladQMat, Finset.sum_add_distrib]

/-- LAD-2 helper: `Q x` at a degree-2 index. -/
theorem ladQ_apply_inr_inr (x : LadIdx → ℝ) (f : Fin 32) :
    (ladQMat *ᵥ x) (Sum.inr (Sum.inr f))
      = ∑ e, ladD2Mat e f * x (Sum.inr (Sum.inl e)) := by
  simp only [Matrix.mulVec, dotProduct]
  rw [Fintype.sum_sum_type]
  simp [ladQMat]

/-- LAD-2 helper (the cross-term lemma): the full contraction
    of `d₁ d₂ = 0` against arbitrary coefficient families —
    `∑ e, A e * (∑ f, ladD2Mat e f * B f) = 0` whenever the
    outer coefficients come through `d₁` at a fixed vertex:
    `∑ e, ladD1Mat v e * (∑ f, ladD2Mat e f * B f) = 0`. -/
theorem lad_cross (B : Fin 32 → ℝ) (v : Fin 30) :
    ∑ e, ladD1Mat v e * (∑ f, ladD2Mat e f * B f) = 0 := by
  have h0 : ∀ f : Fin 32, (∑ e, ladD1Mat v e * ladD2Mat e f) = 0 := by
    intro f
    have h := congrFun (congrFun ladD1Mat_mul_ladD2Mat v) f
    simpa only [Matrix.mul_apply, Matrix.zero_apply] using h
  calc ∑ e, ladD1Mat v e * (∑ f, ladD2Mat e f * B f)
      = ∑ f, B f * (∑ e, ladD1Mat v e * ladD2Mat e f) := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun f _ =>
          Finset.sum_congr rfl fun e _ => by ring
    _ = 0 := Finset.sum_eq_zero fun f _ => by rw [h0 f]; simp

/-- LAD-2 helper (cross-term lemma, transposed): 
    `∑ e, ladD2Mat e f * (∑ v, ladD1Mat v e * B v) = 0`. -/
theorem lad_crossT (B : Fin 30 → ℝ) (f : Fin 32) :
    ∑ e, ladD2Mat e f * (∑ v, ladD1Mat v e * B v) = 0 := by
  have h0 : ∀ v : Fin 30, (∑ e, ladD1Mat v e * ladD2Mat e f) = 0 := by
    intro v
    have h := congrFun (congrFun ladD1Mat_mul_ladD2Mat v) f
    simpa only [Matrix.mul_apply, Matrix.zero_apply] using h
  calc ∑ e, ladD2Mat e f * (∑ v, ladD1Mat v e * B v)
      = ∑ v, B v * (∑ e, ladD1Mat v e * ladD2Mat e f) := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun v _ =>
          Finset.sum_congr rfl fun e _ => by ring
    _ = 0 := Finset.sum_eq_zero fun v _ => by rw [h0 v]; simp

/-! ## Q² = Δ, component by component -/

/-- LAD-2: `(Q² x)` at degree 0 is `(Δ₀ x₀) v`. -/
theorem ladQ_sq_apply_inl (x : LadIdx → ℝ) (v : Fin 30) :
    (ladQMat *ᵥ (ladQMat *ᵥ x)) (Sum.inl v)
      = (ladLap0Mat *ᵥ fun v' => x (Sum.inl v')) v := by
  rw [ladQ_apply_inl]
  have step : ∀ e : Fin 60, ladD1Mat v e * (ladQMat *ᵥ x) (Sum.inr (Sum.inl e))
      = ladD1Mat v e * (∑ v', ladD1Mat v' e * x (Sum.inl v'))
        + ladD1Mat v e * (∑ f, ladD2Mat e f * x (Sum.inr (Sum.inr f))) := by
    intro e
    rw [ladQ_apply_inr_inl, mul_add]
  have step' : (∑ e, ladD1Mat v e * (ladQMat *ᵥ x) (Sum.inr (Sum.inl e)))
      = ∑ e, (ladD1Mat v e * (∑ v', ladD1Mat v' e * x (Sum.inl v'))
        + ladD1Mat v e * (∑ f, ladD2Mat e f * x (Sum.inr (Sum.inr f)))) := by
    apply Finset.sum_congr rfl
    intro e _
    exact step e
  rw [step', Finset.sum_add_distrib,
    lad_cross (fun f => x (Sum.inr (Sum.inr f))) v, add_zero]
  simp only [Matrix.mulVec, dotProduct, ladLap0Mat, Matrix.mul_apply]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v' _ => ?_
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun e _ => by
    rw [Matrix.transpose_apply]; ring

/-- LAD-2: `(Q² x)` at degree 2 is `(Δ₂ x₂) f`. -/
theorem ladQ_sq_apply_inr_inr (x : LadIdx → ℝ) (f : Fin 32) :
    (ladQMat *ᵥ (ladQMat *ᵥ x)) (Sum.inr (Sum.inr f))
      = (ladLap2Mat *ᵥ fun f' => x (Sum.inr (Sum.inr f'))) f := by
  rw [ladQ_apply_inr_inr]
  have step : ∀ e : Fin 60, ladD2Mat e f * (ladQMat *ᵥ x) (Sum.inr (Sum.inl e))
      = ladD2Mat e f * (∑ v, ladD1Mat v e * x (Sum.inl v))
        + ladD2Mat e f * (∑ f', ladD2Mat e f' * x (Sum.inr (Sum.inr f'))) := by
    intro e
    rw [ladQ_apply_inr_inl, mul_add]
  have step' : (∑ e, ladD2Mat e f * (ladQMat *ᵥ x) (Sum.inr (Sum.inl e)))
      = ∑ e, (ladD2Mat e f * (∑ v, ladD1Mat v e * x (Sum.inl v))
        + ladD2Mat e f * (∑ f', ladD2Mat e f' * x (Sum.inr (Sum.inr f')))) := by
    apply Finset.sum_congr rfl
    intro e _
    exact step e
  rw [step', Finset.sum_add_distrib,
    lad_crossT (fun v => x (Sum.inl v)) f, zero_add]
  simp only [Matrix.mulVec, dotProduct, ladLap2Mat, Matrix.mul_apply,
    Matrix.transpose_apply]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun f' _ => ?_
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun e _ => by ring

/-- LAD-2: `(Q² x)` at degree 1 is `(Δ₁ x₁) e` — both cross
    terms vanish by the cross-term lemmas (`lad_cross` after
    commuting the outer coefficient; `lad_crossT` likewise). -/
theorem ladQ_sq_apply_inr_inl (x : LadIdx → ℝ) (e : Fin 60) :
    (ladQMat *ᵥ (ladQMat *ᵥ x)) (Sum.inr (Sum.inl e))
      = (ladLap1Mat *ᵥ fun e' => x (Sum.inr (Sum.inl e'))) e := by
  rw [ladQ_apply_inr_inl]
  have step1 : ∀ v : Fin 30, ladD1Mat v e * (ladQMat *ᵥ x) (Sum.inl v)
      = ladD1Mat v e * (∑ e', ladD1Mat v e' * x (Sum.inr (Sum.inl e'))) := by
    intro v
    rw [ladQ_apply_inl]
  have step2 : ∀ f : Fin 32, ladD2Mat e f * (ladQMat *ᵥ x) (Sum.inr (Sum.inr f))
      = ladD2Mat e f * (∑ e', ladD2Mat e' f * x (Sum.inr (Sum.inl e'))) := by
    intro f
    rw [ladQ_apply_inr_inr]
  rw [Finset.sum_congr rfl (fun v _ => step1 v),
    Finset.sum_congr rfl (fun f _ => step2 f)]
  have hA : (∑ v, ladD1Mat v e * ∑ e', ladD1Mat v e' * x (Sum.inr (Sum.inl e')))
      = ∑ e', (∑ v, ladD1Mat v e * ladD1Mat v e') * x (Sum.inr (Sum.inl e')) := by
    calc (∑ v, ladD1Mat v e * ∑ e', ladD1Mat v e' * x (Sum.inr (Sum.inl e')))
        = ∑ v, ∑ e', ladD1Mat v e * (ladD1Mat v e' * x (Sum.inr (Sum.inl e'))) := by
          exact Finset.sum_congr rfl fun v _ => by rw [Finset.mul_sum]
      _ = ∑ e', ∑ v, ladD1Mat v e * (ladD1Mat v e' * x (Sum.inr (Sum.inl e'))) :=
          Finset.sum_comm
      _ = ∑ e', (∑ v, ladD1Mat v e * ladD1Mat v e') * x (Sum.inr (Sum.inl e')) := by
          refine Finset.sum_congr rfl fun e' _ => ?_
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun v _ => by ring
  have hB : (∑ f, ladD2Mat e f * ∑ e', ladD2Mat e' f * x (Sum.inr (Sum.inl e')))
      = ∑ e', (∑ f, ladD2Mat e f * ladD2Mat e' f) * x (Sum.inr (Sum.inl e')) := by
    calc (∑ f, ladD2Mat e f * ∑ e', ladD2Mat e' f * x (Sum.inr (Sum.inl e')))
        = ∑ f, ∑ e', ladD2Mat e f * (ladD2Mat e' f * x (Sum.inr (Sum.inl e'))) := by
          exact Finset.sum_congr rfl fun f _ => by rw [Finset.mul_sum]
      _ = ∑ e', ∑ f, ladD2Mat e f * (ladD2Mat e' f * x (Sum.inr (Sum.inl e'))) :=
          Finset.sum_comm
      _ = ∑ e', (∑ f, ladD2Mat e f * ladD2Mat e' f) * x (Sum.inr (Sum.inl e')) := by
          refine Finset.sum_congr rfl fun e' _ => ?_
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun f _ => by ring
  simp only [Matrix.mulVec, dotProduct, ladLap1Mat, Matrix.add_apply,
    Matrix.mul_apply, Matrix.transpose_apply]
  rw [hA, hB, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun e' _ => ?_
  ring

theorem ladQMat_sq : ladQMat * ladQMat = ladDeltaMat := by
  have key : ∀ x : LadIdx → ℝ,
      (ladQMat * ladQMat) *ᵥ x = ladDeltaMat *ᵥ x := by
    intro x
    rw [← Matrix.mulVec_mulVec]
    funext i
    match i with
    | Sum.inl v =>
      rw [ladQ_sq_apply_inl]
      simp [Matrix.mulVec, dotProduct, ladDeltaMat]
    | Sum.inr (Sum.inl e) =>
      rw [ladQ_sq_apply_inr_inl]
      simp [Matrix.mulVec, dotProduct, ladDeltaMat]
    | Sum.inr (Sum.inr f) =>
      rw [ladQ_sq_apply_inr_inr]
      simp [Matrix.mulVec, dotProduct, ladDeltaMat]
  have e : ∀ (P : Matrix LadIdx LadIdx ℝ) (i j : LadIdx),
      (∑ x, P i x * (Pi.single j (1 : ℝ) : LadIdx → ℝ) x) = P i j := by
    intro P i j
    rw [Finset.sum_eq_single j]
    · simp
    · intro x _ hxj
      simp [Pi.single_apply, hxj]
    · simp
  ext i j
  have h2 := congrFun (key (Pi.single j 1)) i
  simp only [Matrix.mulVec, dotProduct] at h2
  rw [e _ i j, e _ i j] at h2
  exact h2

/-- LAD-2: **Q² = Δ_total** as linear maps. -/
theorem ladQ_sq : ladQ ∘ₗ ladQ = ladDelta := by
  simp only [ladQ, ladDelta]
  rw [← Matrix.mulVecLin_mul, ladQMat_sq]

/-! ## Energies (SP-1 pattern at every degree) -/

/-- LAD-2 helper: the quadratic-form identity for a Gram-type
    Laplacian: `⟨x, (AᵀA) x⟩ = ∑ (A x)²` for any matrix `A`,
    by the adjoint identity pattern (transpose contraction). -/
theorem lad_energy_gram {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (x : Fin n → ℝ) :
    ∑ i, x i * ((Matrix.transpose A * A) *ᵥ x) i
      = ∑ j, (A *ᵥ x) j ^ 2 := by
  have e1 : (Matrix.transpose A * A) *ᵥ x
      = Matrix.transpose A *ᵥ (A *ᵥ x) := by
    rw [← Matrix.mulVec_mulVec]
  rw [e1]
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [sq, Finset.sum_mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ => by ring

/-- LAD-2: the degree-0 energy is a sum of squares:
    `⟨x, Δ₀ x⟩ = ∑ (d₁* x)²`. -/
theorem lad_energy₀ (x : Fin 30 → ℝ) :
    ∑ v, x v * ladLap0 x v = ∑ e, (ladD1Adj x e) ^ 2 := by
  have h := lad_energy_gram (Matrix.transpose ladD1Mat) x
  rw [Matrix.transpose_transpose] at h
  have hmap : ladLap0 x = (ladD1Mat * (Matrix.transpose ladD1Mat)) *ᵥ x :=
    Matrix.mulVecLin_apply _ _
  have hadj : ladD1Adj x = (Matrix.transpose ladD1Mat) *ᵥ x :=
    Matrix.mulVecLin_apply _ _
  rw [hmap, hadj]
  exact h

/-- LAD-2: the degree-2 energy is a sum of squares:
    `⟨x, Δ₂ x⟩ = ∑ (d₂ x)²`. -/
theorem lad_energy₂ (x : Fin 32 → ℝ) :
    ∑ f, x f * ladLap2 x f = ∑ e, (ladD2 x e) ^ 2 := by
  have h := lad_energy_gram ladD2Mat x
  have hmap : ladLap2 x = ((Matrix.transpose ladD2Mat) * ladD2Mat) *ᵥ x :=
    Matrix.mulVecLin_apply _ _
  have hd : ladD2 x = ladD2Mat *ᵥ x :=
    Matrix.mulVecLin_apply _ _
  rw [hmap, hd]
  exact h

/-- LAD-2: the degree-1 energy is a sum of squares:
    `⟨x, Δ₁ x⟩ = ∑ (d₁ x)² + ∑ (d₂* x)²`. -/
theorem lad_energy₁ (x : Fin 60 → ℝ) :
    ∑ e, x e * ladLap1 x e
      = (∑ v, (ladD1 x v) ^ 2) + ∑ f, (ladD2Adj x f) ^ 2 := by
  have hmap : ladLap1 x = ((Matrix.transpose ladD1Mat) * ladD1Mat
      + ladD2Mat * (Matrix.transpose ladD2Mat)) *ᵥ x :=
    Matrix.mulVecLin_apply _ _
  have hd1 : ladD1 x = ladD1Mat *ᵥ x :=
    Matrix.mulVecLin_apply _ _
  have hd2 : ladD2Adj x = (Matrix.transpose ladD2Mat) *ᵥ x :=
    Matrix.mulVecLin_apply _ _
  have hA := lad_energy_gram ladD1Mat x
  have hB := lad_energy_gram (Matrix.transpose ladD2Mat) x
  rw [Matrix.transpose_transpose] at hB
  rw [hmap, hd1, hd2, Matrix.add_mulVec]
  simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  rw [hA, hB]

/-! ## Kernels: harmonic = closed + coclosed -/

/-- LAD-2 helper: for a Gram-type Laplacian `AᵀA`, the kernel
    of the Laplacian is the kernel of `A` (the energy is a sum
    of squares, so `AᵀA x = 0` forces `A x = 0` by evaluating
    the quadratic form). -/
theorem lad_ker_gram {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    LinearMap.ker (Matrix.mulVecLin (Matrix.transpose A * A))
      = LinearMap.ker (Matrix.mulVecLin A) := by
  ext x
  simp only [LinearMap.mem_ker]
  constructor
  · intro hx
    have henergy := lad_energy_gram A x
    have hx' : ((Matrix.transpose A * A) *ᵥ x) = 0 := hx
    rw [hx'] at henergy
    simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero] at henergy
    have hsum : ∑ j, (A *ᵥ x) j ^ 2 = 0 := henergy.symm
    have hzero : ∀ j, (A *ᵥ x) j = 0 := by
      have h := (Finset.sum_eq_zero_iff_of_nonneg (s := Finset.univ)
        (f := fun j => (A *ᵥ x) j ^ 2) (fun j _ => sq_nonneg _)).mp hsum
      exact fun j => sq_eq_zero_iff.mp (h j (Finset.mem_univ j))
    have hx0 : A *ᵥ x = 0 := funext hzero
    show Matrix.mulVecLin A x = 0
    simp [Matrix.mulVecLin_apply, hx0]
  · intro hx
    have hx0 : A *ᵥ x = 0 := hx
    show Matrix.mulVecLin (Matrix.transpose A * A) x = 0
    simp [Matrix.mulVecLin_apply, ← Matrix.mulVec_mulVec, hx0]

/-- LAD-2: `ker Δ₀ = ker d₁*`. -/
theorem lad_ker_lap0 : LinearMap.ker ladLap0 = LinearMap.ker ladD1Adj := by
  have h := lad_ker_gram (Matrix.transpose ladD1Mat)
  have hT : Matrix.transpose (Matrix.transpose ladD1Mat) = ladD1Mat :=
    Matrix.transpose_transpose _
  rw [hT] at h
  have e0 : ladLap0 = Matrix.mulVecLin
      (ladD1Mat * (Matrix.transpose ladD1Mat)) := rfl
  have e1 : ladD1Adj = Matrix.mulVecLin (Matrix.transpose ladD1Mat) := rfl
  rw [e0, e1]
  have h2 : ladD1Mat * (Matrix.transpose ladD1Mat)
      = Matrix.transpose (Matrix.transpose ladD1Mat)
        * (Matrix.transpose ladD1Mat) := by rw [hT]
  rw [h2]
  exact h

/-- LAD-2: `ker Δ₂ = ker d₂`. -/
theorem lad_ker_lap2 : LinearMap.ker ladLap2 = LinearMap.ker ladD2 := by
  have h := lad_ker_gram ladD2Mat
  have e2 : ladLap2 = Matrix.mulVecLin
      ((Matrix.transpose ladD2Mat) * ladD2Mat) := rfl
  have e3 : ladD2 = Matrix.mulVecLin ladD2Mat := rfl
  rw [e2, e3]
  exact h

/-- LAD-2: `ker Δ₁ = ker d₁ ⊓ ker d₂*`. -/
theorem lad_ker_lap1 :
    LinearMap.ker ladLap1
      = LinearMap.ker ladD1 ⊓ LinearMap.ker ladD2Adj := by
  ext x
  simp only [LinearMap.mem_ker, Submodule.mem_inf]
  constructor
  · intro hx
    have henergy := lad_energy₁ x
    have hx' : ladLap1 x = 0 := hx
    rw [hx'] at henergy
    simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero] at henergy
    have hsum : (∑ v, (ladD1 x v) ^ 2) + ∑ f, (ladD2Adj x f) ^ 2 = 0 :=
      henergy.symm
    have h1 : ∑ v, (ladD1 x v) ^ 2 = 0 :=
      (add_eq_zero_iff_of_nonneg (Finset.sum_nonneg fun v _ => sq_nonneg _)
        (Finset.sum_nonneg fun f _ => sq_nonneg _)).mp hsum |>.1
    have h2 : ∑ f, (ladD2Adj x f) ^ 2 = 0 :=
      (add_eq_zero_iff_of_nonneg (Finset.sum_nonneg fun v _ => sq_nonneg _)
        (Finset.sum_nonneg fun f _ => sq_nonneg _)).mp hsum |>.2
    have hz1 : ∀ v, ladD1 x v = 0 := by
      have h := (Finset.sum_eq_zero_iff_of_nonneg (s := Finset.univ)
        (f := fun v => (ladD1 x v) ^ 2) (fun v _ => sq_nonneg _)).mp h1
      exact fun v => sq_eq_zero_iff.mp (h v (Finset.mem_univ v))
    have hz2 : ∀ f, ladD2Adj x f = 0 := by
      have h := (Finset.sum_eq_zero_iff_of_nonneg (s := Finset.univ)
        (f := fun f => (ladD2Adj x f) ^ 2) (fun f _ => sq_nonneg _)).mp h2
      exact fun f => sq_eq_zero_iff.mp (h f (Finset.mem_univ f))
    exact ⟨funext hz1, funext hz2⟩
  · rintro ⟨h1, h2⟩
    have e1 : ladLap1 = ladD1Adj ∘ₗ ladD1 + ladD2 ∘ₗ ladD2Adj := ladLap1_eq
    rw [e1]
    simp [LinearMap.add_apply, LinearMap.comp_apply, h1, h2]

/-! ## Rank transport ℚ → ℝ and the harmonic census

The transport is elementary, per map, in both directions at
once: each kernel over ℝ is identified with the cast of the
corresponding ℚ kernel data, and ranks follow by rank-nullity.
The ℚ inputs are PHI-C3's landed census facts, consumed by
citation. -/

/-- LAD-2 helper: `ladD2 x` as a sum (the ℝ form of PHI-C3's
    `d2_apply_sum`). -/
theorem lad_d2_apply_sum (x : Fin 32 → ℝ) (e : Fin 60) :
    ladD2 x e = ∑ f : Fin 32, ((faceSign f e : ℚ) : ℝ) * x f := by
  rw [ladD2, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct]
  exact Finset.sum_congr rfl fun f _ => by rw [ladD2Mat_apply]

/-- LAD-2 helper (propagation step over ℝ): a kernel vector of
    `ladD2` takes equal values at a non-root face and its BFS
    parent — the ℝ transport of PHI-C3's `ker_d2_parent_eq`;
    the sign/witness facts are the landed ℚ-side data read at
    the same indices (the face signs are integers). -/
theorem lad_ker_d2_parent_eq (x : Fin 32 → ℝ) (hx : ladD2 x = 0)
    (f : Fin 32) (hf : f ≠ 0) : x f = x (dualParent f) := by
  set e := dualWit f with he
  set p := dualParent f with hp
  have hpf : f ≠ p := by
    intro h
    have hlt := dual_parent_rank_lt f hf
    rw [← hp, ← h] at hlt
    exact lt_irrefl _ hlt
  obtain ⟨hsf, hsp⟩ := dual_parent_signs f hf
  have hEq : ((faceSign f e : ℚ) : ℝ) * x f + ((faceSign p e : ℚ) : ℝ) * x p = 0 := by
    have h0 : ladD2 x e = 0 := by rw [hx]; rfl
    rw [lad_d2_apply_sum] at h0
    have hsub : (∑ h ∈ ({f, p} : Finset (Fin 32)), ((faceSign h e : ℚ) : ℝ) * x h)
        = ∑ h : Fin 32, ((faceSign h e : ℚ) : ℝ) * x h := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro h _ hh
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hh
      have hZ := dual_wit_other_zero f hf h hh.1 hh.2
      rw [hZ]; simp
    rw [Finset.sum_pair hpf] at hsub
    rw [hsub]
    exact h0
  have hsign : ((faceSign p e : ℚ) : ℝ) = - ((faceSign f e : ℚ) : ℝ) := by
    have hZ := dual_sign_sum_zero f hf
    have hcast : ((faceSign f e + faceSign p e : ℤ) : ℝ) = 0 := by
      rw [hZ]; simp
    rw [Int.cast_add] at hcast
    have e1 : ((faceSign f e : ℤ) : ℝ) = ((faceSign f e : ℚ) : ℝ) := by
      push_cast; ring
    have e2 : ((faceSign p e : ℤ) : ℝ) = ((faceSign p e : ℚ) : ℝ) := by
      push_cast; ring
    rw [e1, e2] at hcast
    linarith
  have hne : ((faceSign f e : ℚ) : ℝ) ≠ 0 := by
    have h1 : (faceSign f e : ℚ) ≠ 0 := by exact_mod_cast hsf
    exact_mod_cast h1
  have hmul : ((faceSign f e : ℚ) : ℝ) * (x f - x p) = 0 := by
    rw [hsign] at hEq
    linarith [hEq]
  rcases mul_eq_zero.mp hmul with h1 | h1
  · exact absurd h1 hne
  · exact sub_eq_zero.mp h1

/-- LAD-2 helper (propagation over ℝ): every kernel vector of
    `ladD2` is constant — induction on the BFS depth bound,
    the ℝ transport of PHI-C3's `ker_d2_apply_eq`. -/
theorem lad_ker_d2_apply_eq (x : Fin 32 → ℝ) (hx : ladD2 x = 0) :
    ∀ f : Fin 32, x f = x 0 := by
  have key : ∀ n : ℕ, ∀ f : Fin 32, dualRank f ≤ n → x f = x 0 := by
    intro n
    induction n with
    | zero =>
      intro f hf
      have hf0 : f = 0 := (dual_rank_zero f).mp (Nat.eq_zero_of_le_zero hf)
      rw [hf0]
    | succ n IH =>
      intro f hf
      by_cases hf0 : f = 0
      · rw [hf0]
      · have h1 : x f = x (dualParent f) := lad_ker_d2_parent_eq x hx f hf0
        have h2 : dualRank (dualParent f) ≤ n := by
          have hlt := dual_parent_rank_lt f hf0
          omega
        rw [h1, IH _ h2]
  intro f
  exact key (dualRank f) f le_rfl

/-- LAD-2: `ker d₂` over ℝ is the span of the all-ones vector —
    the transport of PHI-C3's `ker_d2_eq_span`. The reverse
    inclusion: the all-ones vector is in the kernel because
    each edge lies in exactly one triangle and one pentagon
    with opposite signs — the cast of `faceSumVec_mem_ker`,
    i.e. `∑ f, faceSign f e = 0` for every edge, read over ℝ. -/
theorem lad_ker_d2_eq_span :
    LinearMap.ker ladD2 = ℝ ∙ (fun _ : Fin 32 => (1 : ℝ)) := by
  apply le_antisymm
  · intro x hx
    rw [LinearMap.mem_ker] at hx
    rw [Submodule.mem_span_singleton]
    refine ⟨x 0, ?_⟩
    funext f
    simp only [Pi.smul_apply, smul_eq_mul, mul_one]
    exact (lad_ker_d2_apply_eq x hx f).symm
  · apply Submodule.span_le.mpr
    rw [Set.singleton_subset_iff]
    show (fun _ : Fin 32 => (1 : ℝ)) ∈ LinearMap.ker ladD2
    rw [LinearMap.mem_ker]
    have hq : d2 faceSumVec = 0 := faceSumVec_mem_ker
    funext e
    have h0 : d2 faceSumVec e = 0 := by rw [hq]; rfl
    rw [d2_apply_sum] at h0
    have hR : ladD2 (fun _ : Fin 32 => (1 : ℝ)) e = 0 := by
      rw [lad_d2_apply_sum]
      have hsum : ∑ f : Fin 32, (faceSign f e : ℚ) * faceSumVec f = 0 := h0
      simp only [faceSumVec, mul_one] at hsum
      have hZ : ∑ f : Fin 32, ((faceSign f e : ℚ) : ℝ) = 0 := by
        have h2 : Rat.cast (∑ f : Fin 32, (faceSign f e : ℚ)) = (0 : ℝ) := by
          rw [hsum]; simp
        rwa [Rat.cast_sum] at h2
      have hcast : ∀ f : Fin 32, ((faceSign f e : ℚ) : ℝ) * (1 : ℝ)
          = ((faceSign f e : ℚ) : ℝ) := fun f => mul_one _
      rw [Finset.sum_congr rfl (fun f _ => hcast f)]
      exact hZ
    exact hR

/-- LAD-2 helper: `finrank ker ladD2 = 1` over ℝ. -/
theorem lad_finrank_ker_d2 :
    Module.finrank ℝ (LinearMap.ker ladD2) = 1 := by
  rw [lad_ker_d2_eq_span]
  apply finrank_span_singleton
  intro h
  have h0 := congrFun h 0
  simp at h0

/-- LAD-2 helper: `ladD1Adj` applied entry-wise (the ℝ form of
    PHI-C3's `d1T_apply`): `(d₁* y) e = y (head e) − y (tail e)`. -/
theorem lad_d1Adj_apply (y : Fin 30 → ℝ) (e : Fin 60) :
    ladD1Adj y e = y (edgeHead e) - y (edgeTail e) := by
  have hne : edgeTail e ≠ edgeHead e := ne_of_lt (edge_tail_lt_head e)
  have hsum : ladD1Adj y e = ∑ v : Fin 30, ladD1Mat v e * y v := by
    rw [ladD1Adj, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct]
    exact Finset.sum_congr rfl fun v _ => by rw [Matrix.transpose_apply]
  rw [hsum]
  have hsub : (∑ v ∈ ({edgeTail e, edgeHead e} : Finset (Fin 30)), ladD1Mat v e * y v)
      = ∑ v : Fin 30, ladD1Mat v e * y v := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro v _ hv
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hv
    simp [ladD1Mat_apply, hv.1, hv.2]
  rw [← hsub, Finset.sum_pair hne]
  have ht : ladD1Mat (edgeTail e) e = -1 := by
    rw [ladD1Mat_apply]
    simp
  have hh : ladD1Mat (edgeHead e) e = 1 := by
    rw [ladD1Mat_apply]
    simp [Ne.symm hne]
  rw [ht, hh]
  ring

/-- LAD-2 helper (vertex propagation step over ℝ). -/
theorem lad_ker_d1Adj_parent_eq (y : Fin 30 → ℝ) (hy : ladD1Adj y = 0)
    (v : Fin 30) (hv : v ≠ 0) : y v = y (vertParent v) := by
  have h0 : ladD1Adj y (vertWit v) = 0 := by
    rw [hy]; rfl
  rw [lad_d1Adj_apply] at h0
  rcases vert_parent_edge v hv with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    rw [h1, h2] at h0
  · exact (sub_eq_zero.mp h0).symm
  · exact sub_eq_zero.mp h0

/-- LAD-2 helper (vertex propagation over ℝ): every kernel
    vector of `ladD1Adj` is constant. -/
theorem lad_ker_d1Adj_apply_eq (y : Fin 30 → ℝ) (hy : ladD1Adj y = 0) :
    ∀ v : Fin 30, y v = y 0 := by
  have key : ∀ n : ℕ, ∀ v : Fin 30, vertRank v ≤ n → y v = y 0 := by
    intro n
    induction n with
    | zero =>
      intro v hv
      have hv0 : v = 0 := (vert_rank_zero v).mp (Nat.eq_zero_of_le_zero hv)
      rw [hv0]
    | succ n IH =>
      intro v hv
      by_cases hv0 : v = 0
      · rw [hv0]
      · have h1 : y v = y (vertParent v) := lad_ker_d1Adj_parent_eq y hy v hv0
        have h2 : vertRank (vertParent v) ≤ n := by
          have hlt := vert_parent_rank_lt v hv0
          omega
        rw [h1, IH _ h2]
  intro v
  exact key (vertRank v) v le_rfl

/-- LAD-2: `ker d₁*` over ℝ is the constants on vertices — the
    transport of PHI-C3's `ker_d1T_eq_span`. -/
theorem lad_ker_d1Adj_eq_span :
    LinearMap.ker ladD1Adj = ℝ ∙ (fun _ : Fin 30 => (1 : ℝ)) := by
  apply le_antisymm
  · intro y hy
    rw [LinearMap.mem_ker] at hy
    rw [Submodule.mem_span_singleton]
    refine ⟨y 0, ?_⟩
    funext v
    simp only [Pi.smul_apply, smul_eq_mul, mul_one]
    exact (lad_ker_d1Adj_apply_eq y hy v).symm
  · apply Submodule.span_le.mpr
    rw [Set.singleton_subset_iff]
    show (fun _ : Fin 30 => (1 : ℝ)) ∈ LinearMap.ker ladD1Adj
    rw [LinearMap.mem_ker]
    funext e
    rw [lad_d1Adj_apply]
    simp

/-- LAD-2: the ℝ ranks at the seat: rank d₁ = 29, rank d₂ = 31,
    rank d₁* = 29 — by rank-nullity over ℝ from the kernel
    finranks (ker d₂ = 1; ker d₁* = 1; ker d₁ = 31, the last
    because d₁'s transpose has the same rank data: ker d₁ is
    computed from the exactness-free count
    `finrank ker d₁ = 60 − rank d₁` once rank d₁ is known —
    rank d₁ = rank d₁* = 29 by the transpose-rank equality
    for matrices, which is field-free). -/
theorem lad_ranks :
    Module.finrank ℝ (LinearMap.range ladD1) = 29
    ∧ Module.finrank ℝ (LinearMap.range ladD2) = 31
    ∧ Module.finrank ℝ (LinearMap.range ladD1Adj) = 29 := by
  have hk2 : Module.finrank ℝ (LinearMap.ker ladD2) = 1 := lad_finrank_ker_d2
  have hkA : Module.finrank ℝ (LinearMap.ker ladD1Adj) = 1 := by
    rw [lad_ker_d1Adj_eq_span]
    apply finrank_span_singleton
    intro h
    have h0 := congrFun h 0
    simp at h0
  have hrankT : (Matrix.transpose ladD1Mat).rank = ladD1Mat.rank :=
    Matrix.rank_transpose _
  have frAdj : Module.finrank ℝ (LinearMap.range ladD1Adj)
      = (Matrix.transpose ladD1Mat).rank := by
    have h := (Matrix.rank_eq_finrank_range_toLin (Matrix.transpose ladD1Mat)
      (Pi.basisFun ℝ (Fin 60)) (Pi.basisFun ℝ (Fin 30)))
    rw [show Matrix.toLin (Pi.basisFun ℝ (Fin 30)) (Pi.basisFun ℝ (Fin 60))
        (Matrix.transpose ladD1Mat) = ladD1Adj from by
      rw [Matrix.toLin_eq_toLin']
      exact Matrix.toLin'_apply' _] at h
    exact h.symm
  have fr1 : Module.finrank ℝ (LinearMap.range ladD1) = ladD1Mat.rank := by
    have h := (Matrix.rank_eq_finrank_range_toLin ladD1Mat
      (Pi.basisFun ℝ (Fin 30)) (Pi.basisFun ℝ (Fin 60)))
    rw [show Matrix.toLin (Pi.basisFun ℝ (Fin 60)) (Pi.basisFun ℝ (Fin 30))
        ladD1Mat = ladD1 from by
      rw [Matrix.toLin_eq_toLin']
      exact Matrix.toLin'_apply' _] at h
    exact h.symm
  have hnullAdj := LinearMap.finrank_range_add_finrank_ker ladD1Adj
  rw [hkA, Module.finrank_fintype_fun_eq_card] at hnullAdj
  simp at hnullAdj
  have hr2 : Module.finrank ℝ (LinearMap.range ladD2) = 31 := by
    have h := LinearMap.finrank_range_add_finrank_ker ladD2
    rw [hk2, Module.finrank_fintype_fun_eq_card] at h
    simp at h
    omega
  refine ⟨?_, hr2, ?_⟩
  · rw [fr1, ← hrankT, ← frAdj]
    omega
  · omega

/-- LAD-2: exactness at degree 1 over ℝ:
    `ker d₁ = range d₂` (range ⊆ ker by `d² = 0`; both
    finranks are 31: range by `lad_ranks`, kernel by
    rank-nullity from rank d₁ = 29). -/
theorem lad_ker_d1_eq_range_d2 :
    LinearMap.ker ladD1 = LinearMap.range ladD2 := by
  have hle : LinearMap.range ladD2 ≤ LinearMap.ker ladD1 := by
    intro y hy
    obtain ⟨x, hx⟩ := LinearMap.mem_range.mp hy
    rw [LinearMap.mem_ker, ← hx]
    have h : ladD1 ∘ₗ ladD2 = 0 := lad_dsq_zero
    have h2 := LinearMap.congr_fun h x
    simpa only [LinearMap.comp_apply, LinearMap.zero_apply] using h2
  have hker : Module.finrank ℝ (LinearMap.ker ladD1) = 31 := by
    have h := LinearMap.finrank_range_add_finrank_ker ladD1
    rw [lad_ranks.1, Module.finrank_fintype_fun_eq_card] at h
    simp at h
    omega
  have hrange : Module.finrank ℝ (LinearMap.range ladD2) = 31 := lad_ranks.2.1
  exact (Submodule.eq_of_le_of_finrank_eq hle (by rw [hrange, hker])).symm

/-- LAD-2: **harmonic = cohomology** — the harmonic finranks at
    the icosidodecahedron are (1, 0, 1): `finrank ker Δ₀ = 1`
    (= H⁰), `finrank ker Δ₁ = 0` (= H¹), `finrank ker Δ₂ = 1`
    (= H²). PHI-C3's census recovered as zero-mode counts of
    the Laplacians. The middle term: `ker Δ₁ ≤ ker d₁ =
    range d₂` (exactness) and also `ker Δ₁ ≤ ker d₂*`; an
    element of `range d₂ ∩ ker d₂*` is orthogonal to itself
    (adjoint identity), hence zero. -/
theorem lad_harmonic_census :
    Module.finrank ℝ (LinearMap.ker ladLap0) = 1
    ∧ Module.finrank ℝ (LinearMap.ker ladLap1) = 0
    ∧ Module.finrank ℝ (LinearMap.ker ladLap2) = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [lad_ker_lap0]
    have h := LinearMap.finrank_range_add_finrank_ker ladD1Adj
    rw [lad_ranks.2.2, Module.finrank_fintype_fun_eq_card] at h
    simp at h
    omega
  · have hbot : LinearMap.ker ladLap1 = ⊥ := by
      rw [lad_ker_lap1]
      rw [Submodule.eq_bot_iff]
      intro y hy
      rw [Submodule.mem_inf] at hy
      obtain ⟨h1, h2⟩ := hy
      rw [lad_ker_d1_eq_range_d2] at h1
      obtain ⟨x, hx⟩ := h1
      subst hx
      have hself : ∑ e, ladD2 x e * ladD2 x e = 0 := by
        have hadj := lad_adjoint_identity₂ x (ladD2 x)
        have hy0 : ladD2Adj (ladD2 x) = 0 := LinearMap.mem_ker.mp h2
        rw [hy0] at hadj
        simpa only [Pi.zero_apply, mul_zero, Finset.sum_const_zero] using hadj
      have hz : ∀ e, ladD2 x e = 0 := by
        have h := (Finset.sum_eq_zero_iff_of_nonneg (s := Finset.univ)
          (f := fun e => ladD2 x e * ladD2 x e) (fun e _ => mul_self_nonneg _)).mp hself
        exact fun e => by
          have := h e (Finset.mem_univ e)
          exact eq_zero_of_mul_self_eq_zero this
      exact funext hz
    rw [hbot]
    simp
  · rw [lad_ker_lap2]
    have h := LinearMap.finrank_range_add_finrank_ker ladD2
    rw [lad_ranks.2.1, Module.finrank_fintype_fun_eq_card] at h
    simp at h
    omega

end DeRhamLadder
end ThetLogos
