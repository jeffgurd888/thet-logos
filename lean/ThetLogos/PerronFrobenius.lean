/-
# ThetLogos.PerronFrobenius - SHELF-5: the finite-dimensional
Perron-Frobenius theorem (positive-matrix case)

Shelf map row SHELF-5
(`routeb-general-scratch/scoping-shelf-map-2026-10-30.md` SS4):
"Perron-Frobenius (finite-dim: spectral radius of a
positive/primitive matrix is an eigenvalue with a positive
eigenvector)", price M, retiring the corpus's prose-level
PF/Jentzsch invocations.

## Pin inventory verdict (checked at dispatch, 2026-10-31)

The pin (Mathlib v4.35.0-rc3) does NOT own the Perron-Frobenius
eigenvalue theorem - this fill is a BUILD, not a strike. What
the pin owns, and what this module consumes:

* `Mathlib/LinearAlgebra/Matrix/Irreducible/Defs.lean`:
  `Matrix.IsIrreducible`, `Matrix.IsPrimitive` (definitions and
  graph interface only - no eigenvalue content; the file's tag
  line mentions perron-frobenius but no such theorem is in it).
* `Mathlib/Analysis/Normed/Algebra/Spectrum.lean` and
  `Mathlib/Analysis/Normed/Algebra/GelfandFormula.lean`:
  `spectralRadius`, `spectrum.exists_nnnorm_eq_spectralRadius`
  (the radius is attained), and Gelfand's formula
  `spectrum.pow_norm_pow_one_div_tendsto_nhds_spectralRadius`.
* `Mathlib/LinearAlgebra/Matrix/Charpoly/Eigs.lean`:
  `Matrix.mem_spectrum_iff_isRoot_charpoly`;
  `Mathlib/LinearAlgebra/Eigenspace/Charpoly.lean`:
  `Module.End.hasEigenvalue_iff_isRoot_charpoly`;
  `Mathlib/LinearAlgebra/Charpoly/ToMatrix.lean`:
  `Matrix.charpoly_toLin'`.
* `Mathlib/LinearAlgebra/Matrix/Gershgorin.lean`:
  Gershgorin discs (a bound, not an existence theorem).

## What lands here - FULL form

For a finite square real matrix `A` all of whose entries are
strictly positive (the positive case as the shelf map scopes
it; such an `A` is in particular `Matrix.IsPrimitive`, see
`isPrimitive_of_pos` below):

(i) there is a real eigenvalue `lam > 0` with a strictly
positive eigenvector;
(ii) `lam` is the spectral radius in the finite sense: every
complex eigenvalue `mu` of `A` satisfies `|mu| <= lam`.

So the FULL scoped form lands; the PARTIAL seam named in the
pack (uniqueness among positive-eigenvector eigenvalues in
place of (ii)) is not needed.

## Relation to the three prose invocation sites

`LatticeTransferCompact`, `LatticeVacuumSimple`, and
`LatticeUniformGap` invoke Perron-Frobenius / Jentzsch in
docstrings for infinite-dimensional transfer operators on
function spaces. This module retires the prose at the
finite-dimensional level: any finite positive (e.g.
finite-state transfer / Gibbs) matrix appearing at those
sites can now cite `perronFrobenius` below instead of the
classical name. The infinite-dimensional Jentzsch content
itself is not claimed here and stays with those modules.

## Proof route

Let `mu` attain the spectral radius of the complexification
`Ac` (pin: attainment + Gelfand). Put `rho = |mu|` and
`u i = |v i|` for a complex eigenvector `v`. The triangle
inequality gives `rho * u <= A *|v| u` entrywise; applying
`A` once more gives a strictly positive vector
`y = A *|v| u` with `rho * y <= A *|v| y`. If the inequality
were strict anywhere, one more application of `A` would
give `A *|v| z >= (rho + delta) * z` for a strictly positive
`z` and some `delta > 0`, hence `beta^k <= ||Ac^k||` for
`beta = rho + delta` and all `k` (the growth lemma), which
Gelfand's formula forbids. So `y` is a positive eigenvector
for `rho`, and `rho > 0` since `A *|v| y > 0`. Part (ii) is
the definition of the spectral radius via the pin's
spectrum / charpoly interface.

NO CLAIM beyond the stated finite-dimensional theorem;
dials 0/4.
-/

import Mathlib

open scoped Matrix ENNReal NNReal
open scoped Matrix.Norms.Operator
open Filter Topology

namespace ThetLogos

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
variable {A : Matrix n n ℝ}

/-- The complexification of a real matrix. -/
noncomputable def complexify (A : Matrix n n ℝ) : Matrix n n ℂ :=
  A.map Complex.ofReal

/-! ## Real cone lemmas -/

/-- A strictly positive matrix is monotone on the entrywise
order. -/
theorem mulVec_mono (hA : ∀ i j, 0 < A i j) {p q : n → ℝ} (hpq : ∀ j, p j ≤ q j) (i : n) :
    (A *ᵥ p) i ≤ (A *ᵥ q) i := by
  rw [Matrix.mulVec, Matrix.mulVec]
  exact Finset.sum_le_sum fun j _ =>
    mul_le_mul_of_nonneg_left (hpq j) (hA i j).le

/-- A strictly positive matrix sends a nonzero nonnegative
vector to a strictly positive vector. -/
theorem mulVec_pos_of_nonneg (hA : ∀ i j, 0 < A i j) {p : n → ℝ} (hp : ∀ j, 0 ≤ p j)
    (hp0 : p ≠ 0) (i : n) : 0 < (A *ᵥ p) i := by
  obtain ⟨j0, hj0⟩ : ∃ j, p j ≠ 0 := by
    by_contra h
    push_neg at h
    exact hp0 (funext h)
  have hterm : ∀ j ∈ (Finset.univ : Finset n), 0 ≤ A i j * p j :=
    fun j _ => mul_nonneg (hA i j).le (hp j)
  rw [Matrix.mulVec]
  exact (Finset.sum_pos_iff_of_nonneg hterm).mpr
    ⟨j0, Finset.mem_univ j0, mul_pos (hA i j0) (lt_of_le_of_ne (hp j0) (Ne.symm hj0))⟩

/-- Iteration: `A *ᵥ x >= beta * x` iterates to
`A^k *ᵥ x >= beta^k * x`. -/
theorem mulVec_pow_ge (hA : ∀ i j, 0 < A i j) {x : n → ℝ} {beta : ℝ} (hbeta : 0 ≤ beta)
    (hx : ∀ i, beta * x i ≤ (A *ᵥ x) i) (k : ℕ) (i : n) :
    beta ^ k * x i ≤ ((A ^ k) *ᵥ x) i := by
  induction k generalizing i with
  | zero => simpa using le_refl (x i)
  | succ k ih =>
    have step1 : ((A ^ (k + 1)) *ᵥ x) i = (A *ᵥ ((A ^ k) *ᵥ x)) i := by
      rw [pow_succ', ← Matrix.mulVec_mulVec]
    rw [step1]
    have h2 : (A *ᵥ (fun j => beta ^ k * x j)) i ≤ (A *ᵥ ((A ^ k) *ᵥ x)) i :=
      mulVec_mono hA ih i
    have h3 : (A *ᵥ (fun j => beta ^ k * x j)) i
        = beta ^ k * (A *ᵥ x) i := by
      have hsmul : A *ᵥ (beta ^ k • x) = beta ^ k • (A *ᵥ x) :=
        Matrix.mulVec_smul A _ _
      have hfun : (beta ^ k • x) = (fun j => beta ^ k * x j) := by
        funext j; simp [Pi.smul_apply, smul_eq_mul]
      rw [hfun] at hsmul
      rw [hsmul]; simp [Pi.smul_apply, smul_eq_mul]
    have h4 : beta ^ (k + 1) * x i = beta ^ k * (beta * x i) := by
      rw [pow_succ']; ring
    rw [h4]
    exact le_trans (mul_le_mul_of_nonneg_left (hx i) (pow_nonneg hbeta k)) (h3 ▸ h2)

/-- A uniform gap: if `z` and `p` are strictly positive
vectors, some `delta > 0` has `delta * z i <= p i` for all
`i`. -/
theorem exists_delta {z p : n → ℝ} (hz : ∀ i, 0 < z i) (hp : ∀ i, 0 < p i) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ i, delta * z i ≤ p i := by
  obtain ⟨i0, -, hi0⟩ := Finset.exists_min_image Finset.univ (fun i => p i / z i)
    Finset.univ_nonempty
  refine ⟨p i0 / z i0, div_pos (hp i0) (hz i0), fun i => ?_⟩
  exact (le_div_iff₀ (hz i)).mp (hi0 i (Finset.mem_univ i))

/-! ## Complex transfer lemmas -/

/-- One step: complexified matrix action is the complexification
of the real action. -/
theorem complexify_mulVec (y : n → ℝ) :
    (complexify A) *ᵥ (fun i => (y i : ℂ)) = (fun i => ((A *ᵥ y) i : ℂ)) := by
  funext i
  simp [complexify, Matrix.mulVec, dotProduct, ← Complex.ofReal_sum,
    ← Complex.ofReal_mul]

/-- Powers: complexified powers act as the complexification
of the real powers. -/
theorem complexify_pow_mulVec (k : ℕ) (x : n → ℝ) :
    ((complexify A) ^ k) *ᵥ (fun i => (x i : ℂ))
      = (fun i => (((A ^ k) *ᵥ x) i : ℂ)) := by
  induction k generalizing x with
  | zero => simp [Matrix.one_mulVec]
  | succ k ih =>
    have h1 : ((complexify A) ^ (k + 1)) *ᵥ (fun i => (x i : ℂ))
        = (complexify A) *ᵥ (((complexify A) ^ k) *ᵥ (fun i => (x i : ℂ))) := by
      rw [pow_succ', ← Matrix.mulVec_mulVec]
    rw [h1, ih, complexify_mulVec]
    congr 1
    rw [pow_succ', ← Matrix.mulVec_mulVec]

/-! ## The growth bound -/

/-- Growth bound: if a strictly positive vector `x` satisfies
`A *ᵥ x >= beta * x` entrywise, then `beta^k <= ||Ac^k||`
(operator norm) for every `k`. -/
theorem pow_norm_ge (hA : ∀ i j, 0 < A i j) {x : n → ℝ} {beta : ℝ} (hx : ∀ i, 0 < x i)
    (hbeta : 0 ≤ beta) (hAx : ∀ i, beta * x i ≤ (A *ᵥ x) i) (k : ℕ) :
    beta ^ k ≤ ‖(complexify A) ^ k‖ := by
  obtain ⟨i0, -, hi0⟩ := Finset.exists_max_image Finset.univ x Finset.univ_nonempty
  set w : n → ℂ := fun i => (x i : ℂ) with hw
  have hnormw : ‖w‖ = x i0 := by
    apply le_antisymm
    · rw [pi_norm_le_iff_of_nonneg (hx i0).le]
      intro i
      simp only [hw, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hx i)]
      exact hi0 i (Finset.mem_univ i)
    · have h := norm_le_pi_norm w i0
      simpa [hw, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hx i0)] using h
  have hlow : beta ^ k * x i0 ≤ ((A ^ k) *ᵥ x) i0 := mulVec_pow_ge hA hbeta hAx k i0
  have hstep : ((A ^ k) *ᵥ x) i0 ≤ ‖(complexify A) ^ k‖ * x i0 := by
    have h2 : ‖((complexify A) ^ k) *ᵥ w‖ ≤ ‖(complexify A) ^ k‖ * ‖w‖ :=
      Matrix.linfty_opNorm_mulVec _ _
    rw [hnormw] at h2
    have h3 : ‖(((complexify A) ^ k) *ᵥ w) i0‖ ≤ ‖((complexify A) ^ k) *ᵥ w‖ :=
      norm_le_pi_norm _ i0
    have h4 : (((complexify A) ^ k) *ᵥ w) i0 = (((A ^ k) *ᵥ x) i0 : ℂ) := by
      rw [complexify_pow_mulVec]
    rw [h4, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (le_trans (mul_nonneg (pow_nonneg hbeta k) (hx i0).le) hlow)] at h3
    exact le_trans h3 h2
  exact le_of_mul_le_mul_right (le_trans hlow hstep) (hx i0)

/-! ## The headline -/

/-- **Perron-Frobenius, finite-dimensional positive case
(FULL form).** A square real matrix with all entries strictly
positive has a real eigenvalue `lam > 0` with a strictly
positive eigenvector, and `lam` is the spectral radius:
every complex eigenvalue `mu` satisfies `|mu| <= lam`. -/
theorem perronFrobenius (hA : ∀ i j, 0 < A i j) :
    ∃ (lam : ℝ) (x : n → ℝ), 0 < lam ∧ (∀ i, 0 < x i) ∧ A *ᵥ x = lam • x ∧
      ∀ (mu : ℂ) (v : n → ℂ), v ≠ 0 →
        (complexify A) *ᵥ v = mu • v → ‖mu‖ ≤ lam := by
  classical
  obtain ⟨mu0, hmu0spec, hmu0norm⟩ :=
    spectrum.exists_nnnorm_eq_spectralRadius (complexify A)
  set rho : ℝ := ‖mu0‖ with hrho
  have hrho_nonneg : 0 ≤ rho := by rw [hrho]; exact norm_nonneg _
  -- `mu0` is an eigenvalue of the complexification.
  have hroot : (complexify A).charpoly.IsRoot mu0 :=
    (Matrix.mem_spectrum_iff_isRoot_charpoly).mp hmu0spec
  have heig : Module.End.HasEigenvalue (Matrix.toLin' (complexify A)) mu0 := by
    rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, Matrix.charpoly_toLin']
    exact hroot
  obtain ⟨v, hv_mem, hv_ne⟩ :=
    (Submodule.ne_bot_iff _).mp (Module.End.hasEigenvalue_iff.mp heig)
  have hv_eq : (complexify A) *ᵥ v = mu0 • v := by
    have h := (Module.End.mem_eigenspace_iff).mp hv_mem
    rwa [Matrix.toLin'_apply] at h
  -- The modulus vector and the key triangle inequality.
  set u : n → ℝ := fun i => ‖v i‖ with hu
  have hu_nonneg : ∀ i, 0 ≤ u i := fun i => norm_nonneg _
  have hu_ne : u ≠ 0 := by
    intro h
    apply hv_ne
    funext i
    have hi : u i = 0 := by simp [h]
    rw [Pi.zero_apply]
    exact norm_eq_zero.mp hi
  have hkey : ∀ i, rho * u i ≤ (A *ᵥ u) i := by
    intro i
    have h1 : rho * u i = ‖((complexify A) *ᵥ v) i‖ := by
      rw [hv_eq]
      simp [hu, hrho, Pi.smul_apply, smul_eq_mul, norm_mul]
    rw [h1]
    have h2 : ((complexify A) *ᵥ v) i = ∑ j, (A i j : ℂ) * v j := by
      simp [complexify, Matrix.mulVec, dotProduct]
    rw [h2]
    refine le_trans (norm_sum_le _ _) ?_
    rw [Matrix.mulVec]
    refine Finset.sum_le_sum fun j _ => ?_
    simp [dotProduct, hu, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (hA i j), norm_mul]
  -- One more application: a strictly positive vector `y`.
  set y : n → ℝ := A *ᵥ u with hy
  have hy_pos : ∀ i, 0 < y i := fun i => mulVec_pos_of_nonneg hA hu_nonneg hu_ne i
  have hy_ne : y ≠ 0 := by
    intro h
    obtain ⟨i0⟩ : Nonempty n := inferInstance
    have hi := hy_pos i0
    rw [h] at hi
    simp at hi
  have hy_ineq : ∀ i, rho * y i ≤ (A *ᵥ y) i := by
    intro i
    have h := mulVec_mono hA hkey i
    have h2 : (A *ᵥ (fun j => rho * u j)) i = rho * y i := by
      have hsmul : A *ᵥ (rho • u) = rho • (A *ᵥ u) := Matrix.mulVec_smul A _ _
      have hfun : (rho • u) = (fun j => rho * u j) := by
        funext j; simp [Pi.smul_apply, smul_eq_mul]
      rw [hfun] at hsmul
      rw [hsmul]; simp [hy, Pi.smul_apply, smul_eq_mul]
    rw [← h2]; exact h
  -- The endgame: the inequality for `y` is an equality.
  have hy_eq : A *ᵥ y = rho • y := by
    by_contra hne
    -- The defect `w`, its image `z`, and a uniform gap `delta`.
    set w : n → ℝ := fun i => (A *ᵥ y) i - rho * y i with hw
    have hw_nonneg : ∀ i, 0 ≤ w i := fun i => sub_nonneg.mpr (hy_ineq i)
    have hw_ne : w ≠ 0 := by
      intro h
      apply hne
      funext i
      have hwi : (A *ᵥ y) i - rho * y i = 0 := by
        have h1 : w i = 0 := by simp [h]
        rwa [hw] at h1
      simp only [Pi.smul_apply, smul_eq_mul]
      linarith
    set z : n → ℝ := A *ᵥ y with hz
    have hz_pos : ∀ i, 0 < z i :=
      fun i => mulVec_pos_of_nonneg hA (fun j => (hy_pos j).le) hy_ne i
    have hAw_pos : ∀ i, 0 < (A *ᵥ w) i :=
      fun i => mulVec_pos_of_nonneg hA hw_nonneg hw_ne i
    have hz_eq : ∀ i, (A *ᵥ z) i = rho * z i + (A *ᵥ w) i := by
      intro i
      have hzw : z = rho • y + w := by
        funext j
        simp [hz, hw, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have h1 : A *ᵥ z = rho • z + A *ᵥ w := by
        have e : A *ᵥ z = A *ᵥ (rho • y + w) := by rw [hzw]
        rw [e, Matrix.mulVec_add, Matrix.mulVec_smul, ← hz]
      rw [h1]; simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    obtain ⟨delta, hdelta_pos, hdelta⟩ := exists_delta hz_pos hAw_pos
    have hbeta : ∀ i, (rho + delta) * z i ≤ (A *ᵥ z) i := by
      intro i
      rw [hz_eq i]
      have hring : (rho + delta) * z i = rho * z i + delta * z i := by ring
      rw [hring]
      exact add_le_add le_rfl (hdelta i)
    have hgrow : ∀ k : ℕ, (rho + delta) ^ k ≤ ‖(complexify A) ^ k‖ :=
      pow_norm_ge hA hz_pos (add_nonneg hrho_nonneg hdelta_pos.le) hbeta
    -- Gelfand's formula forbids the growth rate `rho + delta`.
    have hspec : spectralRadius ℂ (complexify A) = ENNReal.ofReal rho := by
      rw [← hmu0norm]
      have e : ENNReal.ofReal rho = (‖mu0‖₊ : ℝ≥0∞) := by
        rw [hrho, ← coe_nnnorm]
        exact ENNReal.ofReal_eq_coe_nnreal _
      rw [e]
    have htend := spectrum.pow_norm_pow_one_div_tendsto_nhds_spectralRadius
      (complexify A)
    rw [hspec] at htend
    set beta' : ℝ := rho + delta / 2 with hbeta'
    have hbeta'_lt : beta' < rho + delta := by
      rw [hbeta']; linarith [hdelta_pos]
    have hbeta'_gt : rho < beta' := by rw [hbeta']; linarith [hdelta_pos]
    have hbeta'pos : 0 < beta' := lt_of_le_of_lt hrho_nonneg hbeta'_gt
    have hlt : ENNReal.ofReal rho < ENNReal.ofReal beta' := by
      rw [ENNReal.ofReal_lt_ofReal_iff hbeta'pos]
      exact hbeta'_gt
    obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp (htend (Iio_mem_nhds hlt))
    obtain ⟨k, hkK, hk1⟩ : ∃ k, K ≤ k ∧ 1 ≤ k :=
      ⟨max K 1, le_max_left _ _, le_max_right _ _⟩
    have hk := hK k hkK
    simp only [Set.mem_Iio] at hk
    have hnorm_lt : ‖(complexify A) ^ k‖ ^ (1 / (k : ℝ)) < beta' :=
      (ENNReal.ofReal_lt_ofReal_iff hbeta'pos).mp hk
    have hpow_lt : ‖(complexify A) ^ k‖ < beta' ^ k := by
      by_contra hcon
      push_neg at hcon
      have hle : beta' ≤ ‖(complexify A) ^ k‖ ^ (1 / (k : ℝ)) := by
        have h1 : (beta' ^ k : ℝ) ^ (1 / (k : ℝ)) = beta' := by
          rw [one_div, ← Real.rpow_natCast, ← Real.rpow_mul hbeta'pos.le]
          simp [Nat.cast_ne_zero.mpr (by omega : k ≠ 0)]
        rw [← h1]
        exact Real.rpow_le_rpow (pow_nonneg hbeta'pos.le k) hcon (by positivity)
      linarith
    have hlt2 : beta' ^ k < (rho + delta) ^ k :=
      pow_lt_pow_left₀ hbeta'_lt (le_trans hrho_nonneg hbeta'_gt.le) (by omega)
    linarith [hgrow k, hpow_lt, hlt2]
  -- `rho > 0`, and part (ii).
  have hrho_pos : 0 < rho := by
    obtain ⟨i0⟩ : Nonempty n := inferInstance
    have h1 : (A *ᵥ y) i0 = rho * y i0 := by
      rw [hy_eq]; simp [Pi.smul_apply, smul_eq_mul]
    have h2 : 0 < (A *ᵥ y) i0 :=
      mulVec_pos_of_nonneg hA (fun j => (hy_pos j).le) hy_ne i0
    rw [h1] at h2
    by_contra h
    push_neg at h
    have h3 : rho * y i0 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h (hy_pos i0).le
    linarith
  refine ⟨rho, y, hrho_pos, hy_pos, hy_eq, ?_⟩
  intro mu v hv_ne hveq
  have heig2 : Module.End.HasEigenvalue (Matrix.toLin' (complexify A)) mu := by
    refine Module.End.hasEigenvalue_of_hasEigenvector ⟨?_, hv_ne⟩
    rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
    exact hveq
  have hroot2 : (complexify A).charpoly.IsRoot mu := by
    have h := (Module.End.hasEigenvalue_iff_isRoot_charpoly _ _).mp heig2
    rwa [Matrix.charpoly_toLin'] at h
  have hspec2 : mu ∈ spectrum ℂ (complexify A) :=
    (Matrix.mem_spectrum_iff_isRoot_charpoly).mpr hroot2
  have hle : (‖mu‖₊ : ℝ≥0∞) ≤ (‖mu0‖₊ : ℝ≥0∞) := by
    rw [hmu0norm, spectralRadius_eq_of_unital]
    exact le_iSup_of_le mu (le_iSup_of_le hspec2 le_rfl)
  have hle2 : ‖mu‖₊ ≤ ‖mu0‖₊ := ENNReal.coe_le_coe.mp hle
  have hle3 : (‖mu‖₊ : ℝ) ≤ (‖mu0‖₊ : ℝ) := by exact_mod_cast hle2
  simpa [hrho] using hle3

/-- A strictly positive matrix is primitive in the pin's
sense (`Matrix.IsPrimitive`), already at power `1`. -/
theorem isPrimitive_of_pos (hA : ∀ i j, 0 < A i j) : A.IsPrimitive := by
  refine ⟨fun i j => (hA i j).le, 1, one_pos, fun i j => ?_⟩
  simpa using hA i j

end ThetLogos
