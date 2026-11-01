/-
# ThetLogos.IcosidodecaBoundary — PHI-C1: ∂₁ ∘ ∂₂ = 0 over the explicit model (combinatorics only)

**NO CLAIM. Salvage label (per scoping memo
`routeb-general-scratch/scoping-phi-icosa-2026-10-30.md`, §4–§5):
T1-about-the-polyhedron, zero NCG content, not a promotion of the
mnemonic.** This module is PHI-C1 of the priced salvage line PHI-C
only: over the explicit icosidodecahedron chain model of PHI-C0
(`ThetLogos.IcosidodecaChain` — its names are cited here, never
forked), the chain identity ∂₁ ∘ ∂₂ = 0 holds, entry-wise, in matrix
form, and in the per-face column form. Combinatorics only. NO CLAIM
attaches to this line; it touches no dial and never mentions W₂₂.

## Proof route

The finite entry check over the explicit generated data is the
workhorse, done over ℤ: the integer product entries
`∑ e, d1MatZ v e * d2MatZ e f` vanish for every `(v, f)` by kernel
`decide` (`prodZ_entry_zero`), and the rational product entries are
the casts of the integer ones (`d1Mat_mul_d2Mat_entry`), so the
identity transfers to ℚ without ever asking kernel `decide` to
reduce rational arithmetic. No probe result is cited as a
hypothesis anywhere: the check is recomputed from PHI-C0's own
definitions (`edgeTail`, `edgeHead`, `faceSign`).
-/

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic.NormNum
import ThetLogos.IcosidodecaChain

namespace ThetLogos

/-! ## Integer shadows of the two boundary matrices -/

/-- The ∂₁ matrix over ℤ: `−1` at an edge's tail, `+1` at its head,
    `0` elsewhere — the integer shadow of PHI-C0's `d1Mat`. -/
def d1MatZ : Matrix (Fin 30) (Fin 60) ℤ :=
  fun v e => if v = edgeTail e then -1 else if v = edgeHead e then 1 else 0

/-- The ∂₂ matrix over ℤ: PHI-C0's signed face-boundary incidence
    `faceSign`, before casting to ℚ. -/
def d2MatZ : Matrix (Fin 60) (Fin 32) ℤ :=
  fun e f => faceSign f e

/-- Every `d1Mat` entry is the cast of the corresponding `d1MatZ`
    entry. -/
theorem d1Mat_eq_cast (v : Fin 30) (e : Fin 60) :
    d1Mat v e = (d1MatZ v e : ℚ) := by
  unfold d1Mat d1MatZ
  by_cases h1 : v = edgeTail e <;> by_cases h2 : v = edgeHead e <;>
    simp [h1, h2]

/-- Every `d2Mat` entry is the cast of the corresponding `d2MatZ`
    entry (this is PHI-C0's definition of `d2Mat`, read back). -/
theorem d2Mat_eq_cast (e : Fin 60) (f : Fin 32) :
    d2Mat e f = (d2MatZ e f : ℚ) := rfl

/-! ## The finite entry check over ℤ (kernel `decide`) -/

set_option maxRecDepth 16384 in
/-- The chain identity over ℤ, entry-wise: for every vertex `v` and
    face `f`, `∑ e, d1MatZ v e * d2MatZ e f = 0`. Proved by kernel
    `decide` over PHI-C0's explicit generated data — a finite
    identity (30 × 32 entries, each a 60-term integer sum), recomputed
    from the definitions, not cited from any probe. -/
theorem prodZ_entry_zero : ∀ (v : Fin 30) (f : Fin 32),
    ∑ e : Fin 60, d1MatZ v e * d2MatZ e f = 0 := by decide

/-! ## The chain identity over ℚ -/

/-- Every entry of the rational product `d1Mat * d2Mat` is the cast
    of the corresponding integer product entry. -/
theorem d1Mat_mul_d2Mat_entry (v : Fin 30) (f : Fin 32) :
    (d1Mat * d2Mat) v f
      = ((∑ e : Fin 60, d1MatZ v e * d2MatZ e f : ℤ) : ℚ) := by
  simp only [Matrix.mul_apply]
  rw [Int.cast_sum]
  apply Finset.sum_congr rfl
  intro e _
  rw [d1Mat_eq_cast, d2Mat_eq_cast, Int.cast_mul]

/-- **PHI-C1, entry form.** For every face `f` and vertex `v`, the
    `(v, f)` entry of `d1Mat * d2Mat` vanishes. -/
theorem d1Mat_mul_d2Mat_entry_zero (v : Fin 30) (f : Fin 32) :
    (d1Mat * d2Mat) v f = 0 := by
  rw [d1Mat_mul_d2Mat_entry, prodZ_entry_zero]
  exact Int.cast_zero

/-- **PHI-C1, matrix form.** `d1Mat * d2Mat = 0` over ℚ. -/
theorem d1Mat_mul_d2Mat : d1Mat * d2Mat = 0 := by
  ext v f
  exact d1Mat_mul_d2Mat_entry_zero v f

/-- **PHI-C1, linear-map form.** `d1 ∘ₗ d2 = 0`: the composite
    boundary map `C₂ → C₀` of PHI-C0's explicit model is zero. -/
theorem d1_comp_d2 : d1 ∘ₗ d2 = 0 := by
  have h : (d1 ∘ₗ d2) = Matrix.mulVecLin (d1Mat * d2Mat) := by
    unfold d1 d2
    rw [← Matrix.mulVecLin_mul]
  rw [h, d1Mat_mul_d2Mat]
  ext x v
  simp

/-- **PHI-C1, column form.** For every face `f`, the boundary of its
    boundary column vanishes: `d1 (d2 (Pi.single f 1)) = 0`. This is
    the form the PHI-C2 independence argument and the PHI-C3 census
    consume. -/
theorem d1_d2_single (f : Fin 32) : d1 (d2 (Pi.single f 1)) = 0 := by
  have h := LinearMap.ext_iff.mp d1_comp_d2 (Pi.single f 1)
  simpa [LinearMap.comp_apply] using h

/-- Column form, entry-wise: for every face `f` and vertex `v`,
    `(d1 (d2 (Pi.single f 1))) v = 0`, read off the named basis
    columns of PHI-C0 via `d1_apply_single` / `d2_apply_single`. -/
theorem d1_d2_single_apply (f : Fin 32) (v : Fin 30) :
    d1 (d2 (Pi.single f 1)) v = 0 := by
  rw [d1_d2_single]
  rfl

#print axioms prodZ_entry_zero
#print axioms d1Mat_mul_d2Mat_entry_zero
#print axioms d1Mat_mul_d2Mat
#print axioms d1_comp_d2
#print axioms d1_d2_single

end ThetLogos
