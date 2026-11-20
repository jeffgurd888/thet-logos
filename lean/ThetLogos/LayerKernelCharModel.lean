/-
# WP2 character route, Module B, brick B2a1 — chosen unitary
# models for the irreducible characters, and the entry
# expansion of a character along a four-letter word

Each member `χ` of the finite irreducible family `τ`
(B1b2's `irredCharSet`) is by definition the `charFn` of an
irreducible unitary model; this brick chooses one model per
character once and for all (`charModel`, of dimension
`charDim χ`), and proves the entry expansion of a character
along a word `a * b * c⁻¹ * d⁻¹` — the shape of a column
word (`colWordOf_eq_iff`'s unfolding) — as a sum over the
two index pairs that the separation (B2b) regroups by
sites: the outgoing pair `(a, l)` carried by the
`α`-letters' rows and the incoming pair `(j, k)` carried
by their columns.

**Fences.**  FACT-freeness (scope §3, F1–F3): nothing here
routes through `StratumColumnFactorization`.  This brick
proves no positivity and closes nothing: `DeltaGramGap` is
proved at no seat, no β, no `d`; `LayerKernelPos` at
general finite `(G, ρ)`, β > 0, remains OPEN.

NO CLAIM; dials 0/4.  Dial 2 = 0 under every outcome of
this line: M-U3 is a positivity joint, not a gravity
object.
-/

import ThetLogos.LayerKernelColumnExpansion
import ThetLogos.LayerKernelTensorChannel
import ThetLogos.LayerKernelContractionAPI

open Finset MeasureTheory
open scoped Matrix ENNReal NNReal InnerProductSpace

namespace ThetLogos

section CharModel

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]
  [MeasurableSpace G] [MeasurableSingletonClass G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] [DiscreteTopology G]
  {N : ℕ} [NeZero N] [DecidableEq (LayerLink N)]

/-- The finite irreducible family as a fintype (B1b2's
`irredCharSet`, via its finiteness). -/
abbrev charFamily (G : Type*) [Group G] [Fintype G] [DecidableEq G] :
    Type _ :=
  ↥(irredCharSet_finite (G := G)).toFinset

/-- The dimension of the chosen model of `χ`. -/
noncomputable def charDim (χ : charFamily G) : ℕ :=
  Classical.choose
    ((irredCharSet_finite.mem_toFinset).mp χ.2)

/-- The chosen irreducible unitary model of `χ`. -/
noncomputable def charModel (χ : charFamily G) :
    G →* ↥(Matrix.unitaryGroup (Fin (charDim χ)) ℂ) :=
  Classical.choose (Classical.choose_spec
    ((irredCharSet_finite.mem_toFinset).mp χ.2))

/-- The chosen model is irreducible. -/
theorem charModel_irreducible (χ : charFamily G) :
    RepIrreducible (charModel χ) :=
  (Classical.choose_spec (Classical.choose_spec
    ((irredCharSet_finite.mem_toFinset).mp χ.2))).1

/-- The chosen model's character is `χ` itself. -/
theorem charModel_charFn (χ : charFamily G) :
    charFn (charModel χ) = χ.1 :=
  (Classical.choose_spec (Classical.choose_spec
    ((irredCharSet_finite.mem_toFinset).mp χ.2))).2

/-- **Entry expansion of a character along a four-letter
word.**  For a unitary model `σ` and letters `a b c d`,
`charFn σ (a * b * c⁻¹ * d⁻¹)` is the sum over the
outgoing pair `X = (a, l)` and the incoming pair
`Y = (j, k)` of the product of the four letters' entries:
the `a`-entry at `(X.1, Y.1)`, the `b`-entry at
`(Y.1, Y.2)`, the conjugate `c`-entry at `(X.2, Y.2)`,
and the `d⁻¹`-entry at `(X.2, X.1)`. -/
theorem charFn_word_expand {e : ℕ}
    (σ : G →* ↥(Matrix.unitaryGroup (Fin e) ℂ)) (a b c d : G) :
    charFn σ (a * b * c⁻¹ * d⁻¹)
      = ∑ X : Fin e × Fin e, ∑ Y : Fin e × Fin e,
        repMatrix σ a X.1 Y.1 * repMatrix σ b Y.1 Y.2
          * star (repMatrix σ c X.2 Y.2)
          * repMatrix σ (d⁻¹) X.2 X.1 := by
  have hM3 : ∀ k l : Fin e, repMatrix σ (c⁻¹) k l
      = star (repMatrix σ c l k) := by
    intro k l
    rw [GramWordTensor.repMatrix_inv_entry,
      GramWordTensor.repMatrix_conjRep, GramWordTensor.conjMat_apply]
  show Matrix.trace (repMatrix σ (a * b * c⁻¹ * d⁻¹)) = _
  rw [repMatrix_mul, repMatrix_mul, repMatrix_mul]
  show (∑ i, (repMatrix σ a * repMatrix σ b * repMatrix σ (c⁻¹)
      * repMatrix σ (d⁻¹)) i i) = _
  simp only [Matrix.mul_apply, Finset.sum_mul, hM3,
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ =>
    Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_comm]

end CharModel

end ThetLogos
