import Mathlib.Basic.Complex.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic
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

/-- Abstract TRO class: associativity law as fields. Tier T2/T3. -/
class IsTRO (T : Type*) [Mul T] [Star T] where
  ternary : T → T → T → T
  assoc1 : ∀ a b c d e : T, ternary (ternary a b c) d e = ternary a (ternary d c b) e
  assoc2 : ∀ a b c d e : T, ternary (ternary a b c) d e = ternary a b (ternary c d e)

end ThetLogos
