/-
# WP2 character route, Module B, brick B1c — the word
# representation and its multiplicities

The word representation `σ_{a,b}` of the scope (§3, B1):
the tensor representation of Module A on the slot family
consisting of `a` copies of `ρ` and `b` copies of its
conjugate `conjRep ρ`.  Its character is `χ^a · χ̄^b`
(`wordRep_trace`).  B1a's decomposition of this
representation into minimal constituents, read through
B1b's unitary models, writes the word character over the
finite irreducible family τ with **multiplicities**
`mult χ (a, b)` bounded by the dimension of the word
space:

  `χ^a · χ̄^b = ∑_{χ ∈ τ} (mult χ) • χ`,
  `mult χ ≤ d ^ (a + b)`

(the bound: the number of constituents is at most the
trace at `g = 1`, i.e. the finrank `d ^ (a + b)` of the
word space, since every constituent has finrank `≥ 1`).
This is the regrouping input to B1d's column expansion.

**Fences.**  FACT-freeness (scope §3, F1–F3): nothing here
routes through `StratumColumnFactorization`.  This brick
proves no positivity and closes nothing: `DeltaGramGap` is
proved at no seat, no β, no `d`; `LayerKernelPos` at general
finite `(G, ρ)`, β > 0, remains OPEN.

NO CLAIM; dials 0/4.  Dial 2 = 0 under every outcome of
this line: M-U3 is a positivity joint, not a gravity object.
-/

import ThetLogos.LayerKernelIrredFamily

open Finset
open scoped Matrix InnerProductSpace

namespace ThetLogos

section WordDecomp

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]
  [TopologicalSpace G] [DiscreteTopology G]
variable {d : ℕ} (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ))

/-- The word slot family: `a` copies of `ρ` followed by
`b` copies of its conjugate, over the index type
`Fin a ⊕ Fin b` (all slots of dimension `d`). -/
def wordSlots (a b : ℕ) :
    ∀ j : Fin a ⊕ Fin b, G →* ↥(Matrix.unitaryGroup (Fin d) ℂ) :=
  fun j => Sum.elim (fun _ => ρ) (fun _ => GramWordTensor.conjRep ρ) j

/-- The character of the conjugate representation is the
conjugate character. -/
theorem charFn_conjRep (g : G) :
    charFn (GramWordTensor.conjRep ρ) g = star (charFn ρ g) := by
  show Matrix.trace (repMatrix (GramWordTensor.conjRep ρ) g)
    = star (Matrix.trace (repMatrix ρ g))
  rw [GramWordTensor.repMatrix_conjRep]
  show (∑ i, GramWordTensor.conjMat (repMatrix ρ g) i i)
    = star (∑ i, repMatrix ρ g i i)
  rw [star_sum]
  exact Finset.sum_congr rfl fun i _ => GramWordTensor.conjMat_apply _ _ _

/-- **The word representation** `σ_{a,b}`: Module A's
tensor CLM of the word slot family, bundled as a
homomorphism. -/
noncomputable def wordRep (a b : ℕ) :
    G →* ((EuclideanSpace ℂ (∀ j : Fin a ⊕ Fin b, Fin d)) →L[ℂ]
      (EuclideanSpace ℂ (∀ j : Fin a ⊕ Fin b, Fin d))) where
  toFun g := tensorRepCLM (wordSlots ρ a b) g
  map_one' := tensorRepCLM_one _
  map_mul' := fun g h => tensorRepCLM_mul _ _ _

/-- The trace of a tensor CLM is the tensor trace. -/
theorem tensorRepCLM_trace {κ : Type*} [Fintype κ] [DecidableEq κ]
    {n : κ → ℕ} (σ : ∀ j, G →* ↥(Matrix.unitaryGroup (Fin (n j)) ℂ))
    (g : G) :
    LinearMap.trace ℂ _
        (tensorRepCLM σ g).toLinearMap = tensorTrace σ g := by
  rw [LinearMap.trace_eq_sum_inner _
    (EuclideanSpace.basisFun (∀ j, Fin (n j)) ℂ)]
  show (∑ A, ⟪(EuclideanSpace.basisFun (∀ j, Fin (n j)) ℂ) A,
      (tensorRepCLM σ g).toLinearMap
        ((EuclideanSpace.basisFun (∀ j, Fin (n j)) ℂ) A)⟫_ℂ)
    = ∑ A, tensorEntry σ g A A
  refine Finset.sum_congr rfl fun A _ => ?_
  exact tensorRepCLM_inner_basis σ g A A

/-- **The word character**: the trace of the word
representation is `χ^a · χ̄^b`. -/
theorem wordRep_trace (a b : ℕ) (g : G) :
    LinearMap.trace ℂ _ ((wordRep ρ a b g).toLinearMap)
      = charFn ρ g ^ a * star (charFn ρ g) ^ b := by
  show LinearMap.trace ℂ _
    (tensorRepCLM (wordSlots ρ a b) g).toLinearMap = _
  rw [tensorRepCLM_trace, tensorTrace_eq_prod, Fintype.prod_sum_type]
  congr 1
  · calc (∏ j : Fin a, charFn (wordSlots ρ a b (Sum.inl j)) g)
        = ∏ _j : Fin a, charFn ρ g :=
          Finset.prod_congr rfl fun j _ => rfl
    _ = charFn ρ g ^ a := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  · calc (∏ j : Fin b, charFn (wordSlots ρ a b (Sum.inr j)) g)
        = ∏ _j : Fin b, star (charFn ρ g) :=
          Finset.prod_congr rfl fun j _ => charFn_conjRep ρ g
    _ = star (charFn ρ g) ^ b := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- **The word decomposition with multiplicities**: the
word character is a finite nonnegative-integral
combination of the irreducible characters, with
multiplicities bounded by the word space's dimension. -/
theorem word_decomp (a b : ℕ) :
    ∃ mult : (G → ℂ) → ℕ,
      (∀ g, charFn ρ g ^ a * star (charFn ρ g) ^ b
        = ∑ χ ∈ irredCharSet_finite.toFinset, (mult χ : ℂ) * χ g)
      ∧ ∀ χ, mult χ ≤ d ^ (a + b) := by
  classical
  -- the word representation and its unitarity, in B1a's form
  set T := wordRep ρ a b with hTdef
  have hT : ∀ g : G, ∀ v w :
      EuclideanSpace ℂ (∀ j : Fin a ⊕ Fin b, Fin d),
      ⟪T g v, T g w⟫_ℂ = ⟪v, w⟫_ℂ :=
    fun g v w => tensorRepCLM_unitary _ g v w
  obtain ⟨m, W, hinv, hne, hmin, htrace⟩ := unitary_decomp T hT
  -- the multiplicity of `χ`: the number of constituents
  -- whose model has character `χ`
  refine ⟨fun χ => (Finset.univ.filter
    (fun i => charFn (unitaryModel T hT (hinv i)) = χ)).card, ?_, ?_⟩
  · intro g
    have h1 : LinearMap.trace ℂ _ ((T g).toLinearMap)
        = ∑ i, charFn (unitaryModel T hT (hinv i)) g := by
      rw [htrace g]
      refine Finset.sum_congr rfl fun i _ => ?_
      exact (congrFun (charFn_unitaryModel T hT (hinv i)) g).symm
    have h2 : charFn ρ g ^ a * star (charFn ρ g) ^ b
        = LinearMap.trace ℂ _ ((T g).toLinearMap) :=
      (wordRep_trace ρ a b g).symm
    rw [h2, h1]
    -- regroup the constituent sum over the family τ
    have hmaps : ∀ i ∈ (Finset.univ : Finset (Fin m)),
        charFn (unitaryModel T hT (hinv i))
          ∈ irredCharSet_finite.toFinset := by
      intro i _
      rw [Set.Finite.mem_toFinset]
      exact ⟨Module.finrank ℂ ↥(W i), unitaryModel T hT (hinv i),
        unitaryModel_irreducible T hT (hinv i) (hmin i), rfl⟩
    rw [← Finset.sum_fiberwise_of_maps_to hmaps
      (fun i => charFn (unitaryModel T hT (hinv i)) g)]
    refine Finset.sum_congr rfl fun χ _ => ?_
    have hconst : ∀ i ∈ Finset.univ.filter
        (fun i => charFn (unitaryModel T hT (hinv i)) = χ),
        charFn (unitaryModel T hT (hinv i)) g = χ g :=
      fun i hi => congrFun (Finset.mem_filter.mp hi).2 g
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
  · intro χ
    have hle1 : (Finset.univ.filter
        (fun i => charFn (unitaryModel T hT (hinv i)) = χ)).card ≤ m :=
      (Finset.card_filter_le _ _).trans_eq (by
        rw [Finset.card_univ, Fintype.card_fin])
    refine hle1.trans ?_
    -- the number of constituents is at most the finrank of
    -- the word space: read the trace identity at `g = 1`
    have htr1 : (Module.finrank ℂ
          (EuclideanSpace ℂ (∀ j : Fin a ⊕ Fin b, Fin d)) : ℂ)
        = ∑ i, (Module.finrank ℂ ↥(W i) : ℂ) := by
      have h := htrace 1
      have h1eq : ((1 : (EuclideanSpace ℂ
            (∀ j : Fin a ⊕ Fin b, Fin d)) →L[ℂ]
            (EuclideanSpace ℂ (∀ j : Fin a ⊕ Fin b, Fin d)))).toLinearMap
          = (1 : Module.End ℂ
            (EuclideanSpace ℂ (∀ j : Fin a ⊕ Fin b, Fin d))) := by
        ext x
        rfl
      have hL : LinearMap.trace ℂ _ ((T 1).toLinearMap)
          = (Module.finrank ℂ
            (EuclideanSpace ℂ (∀ j : Fin a ⊕ Fin b, Fin d)) : ℂ) := by
        rw [map_one, h1eq]
        exact LinearMap.trace_one ℂ _
      refine (hL.symm.trans h).trans (Finset.sum_congr rfl fun i _ => ?_)
      have h2 := congrFun (charFn_unitaryModel T hT (hinv i)) 1
      rw [← h2]
      show Matrix.trace ((unitaryModel T hT (hinv i) 1).1) = _
      rw [map_one]
      show Matrix.trace (1 : Matrix _ _ ℂ) = _
      rw [Matrix.trace_one, Fintype.card_fin]
    have hfin : Module.finrank ℂ
          (EuclideanSpace ℂ (∀ j : Fin a ⊕ Fin b, Fin d))
        = ∑ i, Module.finrank ℂ ↥(W i) := by
      rw [← Nat.cast_sum] at htr1
      exact_mod_cast htr1
    have hm : m ≤ ∑ i, Module.finrank ℂ ↥(W i) := by
      have h1 : ∀ i : Fin m, 1 ≤ Module.finrank ℂ ↥(W i) := by
        intro i
        haveI : Nontrivial ↥(W i) := by
          obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).mp (hne i)
          exact ⟨⟨v, hv⟩, 0, fun hh => hv0 (Subtype.ext_iff.mp hh)⟩
        exact Module.finrank_pos
      calc m = ∑ _i : Fin m, 1 := by simp
      _ ≤ ∑ i, Module.finrank ℂ ↥(W i) :=
          Finset.sum_le_sum fun i _ => h1 i
    refine hm.trans (le_of_eq (hfin.symm.trans ?_))
    -- the word space has finrank `d ^ (a + b)`
    rw [finrank_euclideanSpace]
    simp only [Fintype.card_pi, Fintype.card_fin, Finset.prod_const,
      Finset.card_univ, Fintype.card_sum]

end WordDecomp

end ThetLogos
