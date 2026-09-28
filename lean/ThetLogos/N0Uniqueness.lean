import ThetLogos.CFKernelBase

/-!
# ThetLogos.N0Uniqueness — N₀-admissibility and the two-case elimination (T5 scaffold)

## What this file does

Formalizes Jeffrey Michael Gurd's N₀-admissibility predicate (2026-09-28):
an algebra is N₀-admissible if its representation on H_F = ℂ^32 decomposes
into four sectors and yields a 10-dimensional derivation nullspace
(ker 𝓛_{C_F} on the order-one Dirac space).

Two deviations from the original sketch, both deliberate:
1. The representation `rep` is an explicit parameter.  A bare `A : Type*` has
   no canonical representation, so "its representation" is meaningless without
   one.
2. The predicate itself is a genuine definition (no `sorry`): the unproved
   parts are isolated as labeled axioms below, per the repo's honesty tiers.

## What is PROVED here (zero sorrys in the inference layer)

- `n0_elim_of_dim_ne`: any algebra whose nullspace dimension differs from 10
  is not N₀-admissible.
- `cand1_not_admissible` / `cand2_not_admissible`: the elimination lemmas for
  ℂ ⊕ ℂ ⊕ M₄(ℂ) (18 ≠ 10) and ℂ ⊕ M₂(ℂ) ⊕ M₂(ℂ) (6 ≠ 10).
- `sm_admissible`: A_SM = ℂ ⊕ ℍ ⊕ M₃(ℂ) is admissible.
- `n0_uniqueness_three_candidates`: among the three candidates considered,
  A_SM is the UNIQUE admissible one.

## What is AXIOMATIC (labeled, not proved)

- `n0NullDim`: the nullspace-dimension functional itself (T5 scaffold).  Its
  *values* are census data, kept opaque so no proof can smuggle in an
  unverified count.
- `sm_nullDim_eq_10`, `sm_four_sectors`: T4 — the numerical census record.
- `cand1_nullDim_eq_18`, `cand2_nullDim_eq_6`: T5 — Gurd's claimed counts,
  NOT machine-checked.  The order-one census has been run only for the SM
  representation.

## What this file does NOT claim

General uniqueness over all finite algebras is NOT proved here.  See
`ThetLogos.CCMAlgebraClassification.filters_do_not_classify` (algebra-side
filters provably do not suffice) and the killed `AlgebraUniqueness` proposal
(2026-09-27, NO-GO).  The theorem below is uniqueness *among the three
candidates*, conditional on the labeled dimension axioms.
-/

namespace ThetLogos

/-! ## §1. The four-sector decomposition -/

/-- The representation decomposes H_F = ℂ^32 into four 8-dimensional sectors
    (H_L ⊕ H_R ⊕ H_L^c ⊕ H_R^c), pairwise disjoint, spanning, each stable
    under the algebra. -/
def FourSectorDecomp {A : Type*} [Ring A] (rep : A →+* Matrix I32 I32 ℂ) : Prop :=
  ∃ S₁ S₂ S₃ S₄ : Submodule ℂ (I32 → ℂ),
    Module.finrank ℂ ↥S₁ = 8 ∧ Module.finrank ℂ ↥S₂ = 8 ∧
    Module.finrank ℂ ↥S₃ = 8 ∧ Module.finrank ℂ ↥S₄ = 8 ∧
    Disjoint S₁ S₂ ∧ Disjoint S₁ S₃ ∧ Disjoint S₁ S₄ ∧
    Disjoint S₂ S₃ ∧ Disjoint S₂ S₄ ∧ Disjoint S₃ S₄ ∧
    S₁ ⊔ S₂ ⊔ S₃ ⊔ S₄ = ⊤ ∧
    ∀ a : A, (∀ x : I32 → ℂ, x ∈ S₁ → Matrix.mulVec (rep a) x ∈ S₁) ∧
             (∀ x : I32 → ℂ, x ∈ S₂ → Matrix.mulVec (rep a) x ∈ S₂) ∧
             (∀ x : I32 → ℂ, x ∈ S₃ → Matrix.mulVec (rep a) x ∈ S₃) ∧
             (∀ x : I32 → ℂ, x ∈ S₄ → Matrix.mulVec (rep a) x ∈ S₄)

/-! ## §2. The nullspace-dimension functional and the predicate -/

/-- T5 (scaffold): the dimension of ker 𝓛_{C_F} on the order-one Dirac space
    for the representation `rep`.  Kept opaque so that no proof can smuggle
    in an unverified count; values are census data (T4 for SM, T5-claimed
    for the candidates). -/
axiom n0NullDim (A : Type*) [Ring A] (rep : A →+* Matrix I32 I32 ℂ) : ℕ

/-- N₀-admissibility: the representation decomposes into four sectors and
    yields a 10-dimensional derivation nullspace. -/
def IsN0AdmissibleAlgebra (A : Type*) [Ring A]
    (rep : A →+* Matrix I32 I32 ℂ) : Prop :=
  FourSectorDecomp rep ∧ n0NullDim A rep = 10

/-! ## §3. The elimination step (PROVED) -/

/-- Elimination step, PROVED: any algebra whose nullspace dimension differs
    from 10 is not N₀-admissible.  The dimension *inputs* are axioms; the
    *inference* is machine-checked. -/
theorem n0_elim_of_dim_ne (A : Type*) [Ring A] (rep : A →+* Matrix I32 I32 ℂ)
    (hd : n0NullDim A rep ≠ 10) : ¬ IsN0AdmissibleAlgebra A rep := by
  intro h
  exact hd h.2

/-! ## §4. The candidate algebras and their dimension data -/

/-- Candidate 1: A₁ = ℂ ⊕ ℂ ⊕ M₄(ℂ). -/
abbrev CandAlg1 := ℂ × ℂ × Matrix (Fin 4) (Fin 4) ℂ

/-- Candidate 2: A₂ = ℂ ⊕ M₂(ℂ) ⊕ M₂(ℂ). -/
abbrev CandAlg2 := ℂ × Matrix (Fin 2) (Fin 2) ℂ × Matrix (Fin 2) (Fin 2) ℂ

/-- The SM finite algebra A_SM = ℂ ⊕ ℍ ⊕ M₃(ℂ), as an opaque type: the
    quaternion factor has no convenient concrete Mathlib model at this tier,
    so the type and its ring structure are T5 axioms. -/
axiom SMAlg : Type
axiom SMAlg_ring : Ring SMAlg
attribute [instance] SMAlg_ring

/-- T4 (numerical census): the SM representation yields nullspace dimension 10.
    This is the Lean-side record of the 46→10 census
    (`ThetLogos.CFKernelClassification`), not a machine computation. -/
axiom sm_nullDim_eq_10 (rep : SMAlg →+* Matrix I32 I32 ℂ) :
    n0NullDim SMAlg rep = 10

/-- T4 (numerical): the SM representation decomposes into the four 8-dim
    sectors (the 8×8 block structure of the finite Dirac space). -/
axiom sm_four_sectors (rep : SMAlg →+* Matrix I32 I32 ℂ) :
    FourSectorDecomp rep

/-- T5 (CLAIMED — Gurd's count, not machine-checked): candidate 1 yields
    nullspace dimension 18 ≠ 10. -/
axiom cand1_nullDim_eq_18 (rep : CandAlg1 →+* Matrix I32 I32 ℂ) :
    n0NullDim CandAlg1 rep = 18

/-- T5 (CLAIMED — Gurd's count, not machine-checked): candidate 2 yields
    nullspace dimension 6 ≠ 10. -/
axiom cand2_nullDim_eq_6 (rep : CandAlg2 →+* Matrix I32 I32 ℂ) :
    n0NullDim CandAlg2 rep = 6

/-! ## §5. Case elimination (PROVED modulo the labeled dimension axioms) -/

/-- Candidate 1 ruled out: 18 ≠ 10. -/
theorem cand1_not_admissible (rep : CandAlg1 →+* Matrix I32 I32 ℂ) :
    ¬ IsN0AdmissibleAlgebra CandAlg1 rep :=
  n0_elim_of_dim_ne CandAlg1 rep (by
    rw [cand1_nullDim_eq_18 rep]
    norm_num)

/-- Candidate 2 ruled out: 6 ≠ 10. -/
theorem cand2_not_admissible (rep : CandAlg2 →+* Matrix I32 I32 ℂ) :
    ¬ IsN0AdmissibleAlgebra CandAlg2 rep :=
  n0_elim_of_dim_ne CandAlg2 rep (by
    rw [cand2_nullDim_eq_6 rep]
    norm_num)

/-- The SM algebra IS N₀-admissible (modulo the T4 census axioms). -/
theorem sm_admissible (rep : SMAlg →+* Matrix I32 I32 ℂ) :
    IsN0AdmissibleAlgebra SMAlg rep :=
  ⟨sm_four_sectors rep, sm_nullDim_eq_10 rep⟩

/-! ## §6. Uniqueness among the three candidates -/

/-- Uniqueness AMONG THE THREE CANDIDATES CONSIDERED (proved modulo the
    labeled dimension axioms): A_SM is admissible; the two alternatives are
    not.  This is NOT general uniqueness over all finite algebras. -/
theorem n0_uniqueness_three_candidates
    (repSM : SMAlg →+* Matrix I32 I32 ℂ)
    (rep1 : CandAlg1 →+* Matrix I32 I32 ℂ)
    (rep2 : CandAlg2 →+* Matrix I32 I32 ℂ) :
    IsN0AdmissibleAlgebra SMAlg repSM ∧
    ¬ IsN0AdmissibleAlgebra CandAlg1 rep1 ∧
    ¬ IsN0AdmissibleAlgebra CandAlg2 rep2 :=
  ⟨sm_admissible repSM, cand1_not_admissible rep1, cand2_not_admissible rep2⟩

end ThetLogos
