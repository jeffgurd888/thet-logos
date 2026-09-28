import Mathlib.Basic.Complex.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic
import Mathlib.LinearAlgebra.Eigenspace.Matrix
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Matrix.ToLin
import ThetLogos.Axioms

/-!
# ThetLogos.TRO — ternary ring of operators (Tiers T2/T3)

After: Gurd, *The Ontological Thet–LOGOS Framework* (Revised Draft, Nexus
Research, Sept 2026), §2.1.2.

The ternary product is a Tier T2 definition; its associativity law is a
Tier T3 checked fact (scalar case proved below; matrix case stated).
-/

namespace ThetLogos

/-- Ternary product on scalars: ⟨a, b, c⟩ = a · star b · c. Tier T2. -/
def ternary (a b c : ℂ) : ℂ := a * star b * c

/-- Ternary product on square complex matrices: ⟨a,b,c⟩ = a bᴴ c. Tier T2. -/
def ternaryMat {n : ℕ} (a b c : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  a * b.conjTranspose * c

/-- TRO associativity law, scalar case. Tier T3 (proved).
    [[a b c] d e] = [a [d c b] e]. -/
theorem ternary_assoc_scalar (a b c d e : ℂ) :
    ternary (ternary a b c) d e = ternary a (ternary d c b) e := by
  simp only [ternary, star_mul, star_star]
  ring

/-- TRO associativity, second form: [[a b c] d e] = [a b [c d e]]. Tier T3. -/
theorem ternary_assoc_scalar' (a b c d e : ℂ) :
    ternary (ternary a b c) d e = ternary a b (ternary c d e) := by
  simp only [ternary, star_mul, star_star]
  ring

/-- TRO associativity for complex matrices. Tier T3 (proved). -/
theorem ternaryMat_assoc {n : ℕ} (a b c d e : Matrix (Fin n) (Fin n) ℂ) :
    ternaryMat (ternaryMat a b c) d e = ternaryMat a (ternaryMat d c b) e := by
  simp only [ternaryMat, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]

/-- TRO associativity, second form, for complex matrices. Tier T3 (proved).

Audit note (2026-09-28): an earlier review claimed this law FAILS for noncommutative
matrices, citing a=b=d=I, c=E₁₁, e=E₁₂ as a counterexample with "LHS = E₁₂, RHS = E₂₁".
The counterexample was miscalculated — both sides equal E₁₂ (checked numerically),
and the law holds in general by `Matrix.mul_assoc` alone:
LHS = a·bᴴ·c·dᴴ·e = RHS. No repair to the `IsTRO` class was needed. -/
theorem ternaryMat_assoc2 {n : ℕ} (a b c d e : Matrix (Fin n) (Fin n) ℂ) :
    ternaryMat (ternaryMat a b c) d e = ternaryMat a b (ternaryMat c d e) := by
  simp only [ternaryMat, Matrix.mul_assoc]

/-- Abstract TRO class: associativity law as fields. Tier T2/T3. -/
class IsTRO (T : Type*) [Mul T] [Star T] where
  ternary : T → T → T → T
  assoc1 : ∀ a b c d e : T, ternary (ternary a b c) d e = ternary a (ternary d c b) e
  assoc2 : ∀ a b c d e : T, ternary (ternary a b c) d e = ternary a b (ternary c d e)

/-- Square complex matrices form a TRO under `ternaryMat`. Tier T3 (instance). -/
instance Matrix.isTRO {n : ℕ} : IsTRO (Matrix (Fin n) (Fin n) ℂ) where
  ternary := ternaryMat
  assoc1 := ternaryMat_assoc
  assoc2 := ternaryMat_assoc2

/-- Spectrum of a self-adjoint tripotent matrix lies in `{-1, 0, 1}`. Tier T3 (proved).

From `Xᴴ = X` and `ternaryMat X X X = X` we get `X^3 = X`; the polynomial
`X^3 - X` therefore annihilates the endomorphism `X.toLin'`, so every eigenvalue
`μ` satisfies `μ^3 = μ`, i.e. `μ ∈ {-1, 0, 1}`.

The self-adjointness hypothesis is essential and cannot be dropped:
`Complex.I • 1` is a tripotent (`ternaryMat` gives `i·(-i)·i = i`) whose spectrum
is `{Complex.I}` — formalized as `tripotent_selfadjoint_sharp` below.
In particular this theorem cannot replace the individual
non-tripotent kill proofs — those concern matrices that fail the tripotent
equation itself. -/
theorem tripotent_selfadjoint_spectrum {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℂ) (hsa : X.conjTranspose = X)
    (htrip : ternaryMat X X X = X) :
    spectrum ℂ X ⊆ {-1, 0, 1} := by
  have h3 : X ^ 3 = X := by
    have h := htrip
    simp only [ternaryMat, hsa] at h
    calc X ^ 3 = X * X * X := by rw [pow_succ, pow_succ, pow_one]
      _ = X := h
  have hf3 : (Matrix.toLin' X) ^ 3 = Matrix.toLin' X := by
    rw [← Matrix.toLin'_pow, h3]
  have hann :
      Polynomial.aeval (Matrix.toLin' X)
        (Polynomial.X ^ 3 - Polynomial.X : Polynomial ℂ) = 0 := by
    simp only [map_sub, map_pow, Polynomial.aeval_X, hf3, sub_self]
  intro μ hμ
  have hμ' : μ ∈ spectrum ℂ (Matrix.toLin' X) := by
    rw [Matrix.spectrum_toLin']; exact hμ
  have heig : Module.End.HasEigenvalue (Matrix.toLin' X) μ :=
    Module.End.hasEigenvalue_iff_mem_spectrum.mpr hμ'
  obtain ⟨x, hxeig, hxne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot heig
  have hfx : Matrix.toLin' X x = μ • x := Module.End.mem_eigenspace_iff.mp hxeig
  have h0 : (Polynomial.X ^ 3 - Polynomial.X : Polynomial ℂ).eval μ • x = 0 := by
    have h2 :=
      Module.End.aeval_apply_of_mem_apply_eq_smul
        (p := (Polynomial.X ^ 3 - Polynomial.X : Polynomial ℂ)) hfx
    rw [hann, LinearMap.zero_apply] at h2
    exact h2.symm
  have hroot : (Polynomial.X ^ 3 - Polynomial.X : Polynomial ℂ).eval μ = 0 := by
    rcases smul_eq_zero.mp h0 with h | h
    · exact h
    · exact absurd h hxne
  have hfac : μ ^ 3 - μ = 0 := by
    have h := hroot
    simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X] at h
    exact h
  have hmul : μ * (μ - 1) * (μ + 1) = 0 := by
    have hfactor : μ ^ 3 - μ = μ * (μ - 1) * (μ + 1) := by ring
    rwa [hfactor] at hfac
  rw [Set.mem_insert_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
  rcases mul_eq_zero.mp hmul with h | h
  · rcases mul_eq_zero.mp h with h | h
    · subst h
      exact Or.inr (Or.inl rfl)
    · have h1 : μ = 1 := sub_eq_zero.mp h
      subst h1
      exact Or.inr (Or.inr rfl)
  · have hm1 : μ = -1 := eq_neg_of_add_eq_zero_left h
    subst hm1
    exact Or.inl rfl

/-- Sharpness: the self-adjointness hypothesis in `tripotent_selfadjoint_spectrum`
cannot be dropped. `Complex.I • 1` is a tripotent (`i·(-i)·i = i`) whose spectrum
is `{Complex.I}`, hence not contained in `{-1, 0, 1}`. Tier T3 (proved). -/
theorem tripotent_selfadjoint_sharp {n : ℕ} [Nonempty (Fin n)] :
    ternaryMat (Complex.I • 1) (Complex.I • 1) (Complex.I • 1)
      = (Complex.I • 1 : Matrix (Fin n) (Fin n) ℂ) ∧
    ¬ (spectrum ℂ (Complex.I • 1 : Matrix (Fin n) (Fin n) ℂ) ⊆ {-1, 0, 1}) := by
  have hdiag : (Complex.I • (1 : Matrix (Fin n) (Fin n) ℂ))
      = Matrix.diagonal (fun _ => Complex.I) := Matrix.smul_one_eq_diagonal Complex.I
  have hI : star (Complex.I : ℂ) = -Complex.I := by
    rw [Complex.star_def]; exact Complex.conj_I
  have htrip : ternaryMat (Complex.I • 1) (Complex.I • 1) (Complex.I • 1)
      = (Complex.I • 1 : Matrix (Fin n) (Fin n) ℂ) := by
    simp only [ternaryMat, Matrix.conjTranspose_smul, Matrix.conjTranspose_one, hI]
    simp only [Matrix.smul_one_eq_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    show Complex.I * -Complex.I * Complex.I = Complex.I
    rw [mul_neg, Complex.I_mul_I, neg_neg, one_mul]
  have hspec : spectrum ℂ (Complex.I • (1 : Matrix (Fin n) (Fin n) ℂ)) = {Complex.I} := by
    rw [hdiag, spectrum_diagonal, Set.range_const]
  refine ⟨htrip, ?_⟩
  intro hsub
  have hmem : Complex.I ∈ spectrum ℂ (Complex.I • (1 : Matrix (Fin n) (Fin n) ℂ)) := by
    rw [hspec]
    exact Set.mem_singleton_iff.mpr rfl
  have hcon := hsub hmem
  rw [Set.mem_insert_iff, Set.mem_insert_iff, Set.mem_singleton_iff] at hcon
  rcases hcon with h | h | h
  · have h2 : Complex.I * Complex.I = (-1 : ℂ) * (-1) := by rw [h]
    rw [Complex.I_mul_I] at h2
    norm_num at h2
  · exact Complex.I_ne_zero h
  · have h2 : Complex.I * Complex.I = (1 : ℂ) * 1 := by rw [h]
    rw [Complex.I_mul_I] at h2
    norm_num at h2

end ThetLogos
