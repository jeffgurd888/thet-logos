import ThetLogos.CFKernelRetarget

namespace ThetLogos

/-! # Exotic sector decomposition (ladder item 7.1, Tier 1)

The 12 exotic directions of W22 split canonically as **8 ⊕ 2 ⊕ 2**:

- Sector A (8 dirs): `NuLeR`, `ELNuR`, `NuREbarR`, `EREbarR` (Re/Im pairs).
  Mutually non-commuting connected component (Tier-4 probe).
- Sector B1 (2 dirs): the `ULDR` Re/Im pair. Commutes with everything outside itself.
- Sector B2 (2 dirs): the `DLUR` Re/Im pair. Commutes with everything outside itself.

The mechanism is elementary: every exotic matrix is a signed permutation
matrix, and the B-sector index sets are disjoint from the A-sector index
sets (and from each other). Disjoint support ⟹ both products vanish ⟹
the commutator vanishes.

Proof strategy (following `CFKernelRetarget.lean`): per-matrix support
lemmas (`M i k ≠ 0 → i ∈ S ∧ k ∈ S`), one general disjointness lemma,
then pairwise commutators by `decide`-checked disjointness. Zero `sorry`s.
-/

-- ============================================================================
-- Support index sets
-- ============================================================================

/-- Support indices of the ULDR pair (sector B1). -/
def suppULDR : Finset I32 := {2, 11, 4, 13, 6, 15, 18, 27, 20, 29, 22, 31}

/-- Support indices of the DLUR pair (sector B2). -/
def suppDLUR : Finset I32 := {3, 10, 5, 12, 7, 14, 19, 26, 21, 28, 23, 30}

/-- Support indices of the NuLeR pair (sector A). -/
def suppNuLeR : Finset I32 := {0, 9, 16, 25}

/-- Support indices of the ELNuR pair (sector A). -/
def suppELNuR : Finset I32 := {1, 8, 17, 24}

/-- Support indices of the NuREbarR pair (sector A). -/
def suppNuREbarR : Finset I32 := {8, 9, 24, 25}

/-- Support indices of the EREbarR pair (sector A). -/
def suppEREbarR : Finset I32 := {9, 25}

-- ============================================================================
-- General disjointness lemma
-- ============================================================================

/-- Two matrices with disjoint support index sets have vanishing product.
    Both factors of each entry-sum vanish: a nonzero `U i k` forces
    `k ∈ SU`, a nonzero `A k j` forces `k ∈ SA`, and these contradict. -/
theorem mul_eq_zero_of_disjoint_supp {U A : Matrix I32 I32 ℂ} {SU SA : Finset I32}
    (hU : ∀ i k, U i k ≠ 0 → i ∈ SU ∧ k ∈ SU)
    (hA : ∀ i k, A i k ≠ 0 → i ∈ SA ∧ k ∈ SA)
    (hdisj : Disjoint SU SA) : U * A = 0 := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.zero_apply]
  apply Finset.sum_eq_zero
  intro k _
  by_cases hUk : U i k = 0
  · simp [hUk]
  · by_cases hAk : A k j = 0
    · simp [hAk]
    · exfalso
      exact (Finset.disjoint_left.mp hdisj) (hU i k hUk).2 ((hA k j hAk).1)

-- ============================================================================
-- Finset-membership converters (reuse the disjunction-form support lemmas
-- already proved in CFKernelRetarget.lean)
-- ============================================================================

theorem exoticReULDR_mem_supp (i k : I32) (h : exoticReULDR i k ≠ 0) :
    i ∈ suppULDR ∧ k ∈ suppULDR := by
  rcases exoticReULDR_supp i k h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> decide

theorem exoticImULDR_mem_supp (i k : I32) (h : exoticImULDR i k ≠ 0) :
    i ∈ suppULDR ∧ k ∈ suppULDR := by
  rcases exoticImULDR_supp i k h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> decide

theorem exoticReDLUR_mem_supp (i k : I32) (h : exoticReDLUR i k ≠ 0) :
    i ∈ suppDLUR ∧ k ∈ suppDLUR := by
  rcases exoticReDLUR_supp i k h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> decide

theorem exoticImDLUR_mem_supp (i k : I32) (h : exoticImDLUR i k ≠ 0) :
    i ∈ suppDLUR ∧ k ∈ suppDLUR := by
  rcases exoticImDLUR_supp i k h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> decide

theorem exoticReNuLeR_mem_supp (i k : I32) (h : exoticReNuLeR i k ≠ 0) :
    i ∈ suppNuLeR ∧ k ∈ suppNuLeR := by
  rcases exoticReNuLeR_supp i k h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> decide

theorem exoticImNuLeR_mem_supp (i k : I32) (h : exoticImNuLeR i k ≠ 0) :
    i ∈ suppNuLeR ∧ k ∈ suppNuLeR := by
  rcases exoticImNuLeR_supp i k h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> decide

theorem exoticReELNuR_mem_supp (i k : I32) (h : exoticReELNuR i k ≠ 0) :
    i ∈ suppELNuR ∧ k ∈ suppELNuR := by
  rcases exoticReELNuR_supp i k h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> decide

theorem exoticImELNuR_mem_supp (i k : I32) (h : exoticImELNuR i k ≠ 0) :
    i ∈ suppELNuR ∧ k ∈ suppELNuR := by
  rcases exoticImELNuR_supp i k h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> decide

theorem exoticReNuREbarR_mem_supp (i k : I32) (h : exoticReNuREbarR i k ≠ 0) :
    i ∈ suppNuREbarR ∧ k ∈ suppNuREbarR := by
  rcases exoticReNuREbarR_supp i k h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> decide

theorem exoticImNuREbarR_mem_supp (i k : I32) (h : exoticImNuREbarR i k ≠ 0) :
    i ∈ suppNuREbarR ∧ k ∈ suppNuREbarR := by
  rcases exoticImNuREbarR_supp i k h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> decide

theorem exoticReEREbarR_mem_supp (i k : I32) (h : exoticReEREbarR i k ≠ 0) :
    i ∈ suppEREbarR ∧ k ∈ suppEREbarR := by
  rcases exoticReEREbarR_supp i k h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> decide

theorem exoticImEREbarR_mem_supp (i k : I32) (h : exoticImEREbarR i k ≠ 0) :
    i ∈ suppEREbarR ∧ k ∈ suppEREbarR := by
  rcases exoticImEREbarR_supp i k h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> decide

-- ============================================================================
-- Sector B1 (ULDR pair) commutes with sector A
-- ============================================================================

theorem comm_ReULDR_ReNuLeR :
    exoticReULDR * exoticReNuLeR - exoticReNuLeR * exoticReULDR = 0 := by
  have h1 : exoticReULDR * exoticReNuLeR = 0 :=
    mul_eq_zero_of_disjoint_supp exoticReULDR_mem_supp exoticReNuLeR_mem_supp (by decide)
  have h2 : exoticReNuLeR * exoticReULDR = 0 :=
    mul_eq_zero_of_disjoint_supp exoticReNuLeR_mem_supp exoticReULDR_mem_supp (by decide)
  rw [h1, h2, sub_self]

theorem comm_ReULDR_ImNuLeR :
    exoticReULDR * exoticImNuLeR - exoticImNuLeR * exoticReULDR = 0 := by
  have h1 : exoticReULDR * exoticImNuLeR = 0 :=
    mul_eq_zero_of_disjoint_supp exoticReULDR_mem_supp exoticImNuLeR_mem_supp (by decide)
  have h2 : exoticImNuLeR * exoticReULDR = 0 :=
    mul_eq_zero_of_disjoint_supp exoticImNuLeR_mem_supp exoticReULDR_mem_supp (by decide)
  rw [h1, h2, sub_self]

theorem comm_ReULDR_ReELNuR :
    exoticReULDR * exoticReELNuR - exoticReELNuR * exoticReULDR = 0 := by
  have h1 : exoticReULDR * exoticReELNuR = 0 :=
    mul_eq_zero_of_disjoint_supp exoticReULDR_mem_supp exoticReELNuR_mem_supp (by decide)
  have h2 : exoticReELNuR * exoticReULDR = 0 :=
    mul_eq_zero_of_disjoint_supp exoticReELNuR_mem_supp exoticReULDR_mem_supp (by decide)
  rw [h1, h2, sub_self]

theorem comm_ReULDR_ImELNuR :
    exoticReULDR * exoticImELNuR - exoticImELNuR * exoticReULDR = 0 := by
  have h1 : exoticReULDR * exoticImELNuR = 0 :=
    mul_eq_zero_of_disjoint_supp exoticReULDR_mem_supp exoticImELNuR_mem_supp (by decide)
  have h2 : exoticImELNuR * exoticReULDR = 0 :=
    mul_eq_zero_of_disjoint_supp exoticImELNuR_mem_supp exoticReULDR_mem_supp (by decide)
  rw [h1, h2, sub_self]

theorem comm_ReULDR_ReNuREbarR :
    exoticReULDR * exoticReNuREbarR - exoticReNuREbarR * exoticReULDR = 0 := by
  have h1 : exoticReULDR * exoticReNuREbarR = 0 :=
    mul_eq_zero_of_disjoint_supp exoticReULDR_mem_supp exoticReNuREbarR_mem_supp (by decide)
  have h2 : exoticReNuREbarR * exoticReULDR = 0 :=
    mul_eq_zero_of_disjoint_supp exoticReNuREbarR_mem_supp exoticReULDR_mem_supp (by decide)
  rw [h1, h2, sub_self]

theorem comm_ReULDR_ImNuREbarR :
    exoticReULDR * exoticImNuREbarR - exoticImNuREbarR * exoticReULDR = 0 := by
  have h1 : exoticReULDR * exoticImNuREbarR = 0 :=
    mul_eq_zero_of_disjoint_supp exoticReULDR_mem_supp exoticImNuREbarR_mem_supp (by decide)
  have h2 : exoticImNuREbarR * exoticReULDR = 0 :=
    mul_eq_zero_of_disjoint_supp exoticImNuREbarR_mem_supp exoticReULDR_mem_supp (by decide)
  rw [h1, h2, sub_self]

theorem comm_ReULDR_ReEREbarR :
    exoticReULDR * exoticReEREbarR - exoticReEREbarR * exoticReULDR = 0 := by
  have h1 : exoticReULDR * exoticReEREbarR = 0 :=
    mul_eq_zero_of_disjoint_supp exoticReULDR_mem_supp exoticReEREbarR_mem_supp (by decide)
  have h2 : exoticReEREbarR * exoticReULDR = 0 :=
    mul_eq_zero_of_disjoint_supp exoticReEREbarR_mem_supp exoticReULDR_mem_supp (by decide)
  rw [h1, h2, sub_self]

theorem comm_ReULDR_ImEREbarR :
    exoticReULDR * exoticImEREbarR - exoticImEREbarR * exoticReULDR = 0 := by
  have h1 : exoticReULDR * exoticImEREbarR = 0 :=
    mul_eq_zero_of_disjoint_supp exoticReULDR_mem_supp exoticImEREbarR_mem_supp (by decide)
  have h2 : exoticImEREbarR * exoticReULDR = 0 :=
    mul_eq_zero_of_disjoint_supp exoticImEREbarR_mem_supp exoticReULDR_mem_supp (by decide)
  rw [h1, h2, sub_self]

theorem comm_ImULDR_ReNuLeR :
    exoticImULDR * exoticReNuLeR - exoticReNuLeR * exoticImULDR = 0 := by
  have h1 : exoticImULDR * exoticReNuLeR = 0 :=
    mul_eq_zero_of_disjoint_supp exoticImULDR_mem_supp exoticReNuLeR_mem_supp (by decide)
  have h2 : exoticReNuLeR * exoticImULDR = 0 :=
    mul_eq_zero_of_disjoint_supp exoticReNuLeR_mem_supp exoticImULDR_mem_supp (by decide)
  rw [h1, h2, sub_self]

theorem comm_ImULDR_ImNuLeR :
    exoticImULDR * exoticImNuLeR - exoticImNuLeR * exoticImULDR = 0 := by
  have h1 : exoticImULDR * exoticImNuLeR = 0 :=
    mul_eq_zero_of_disjoint_supp exoticImULDR_mem_supp exoticImNuLeR_mem_supp (by decide)
  have h2 : exoticImNuLeR * exoticImULDR = 0 :=
    mul_eq_zero_of_disjoint_supp exoticImNuLeR_mem_supp exoticImULDR_mem_supp (by decide)
  rw [h1, h2, sub_self]

theorem comm_ImULDR_ReELNuR :
    exoticImULDR * exoticReELNuR - exoticReELNuR * exoticImULDR = 0 := by
  have h1 : exoticImULDR * exoticReELNuR = 0 :=
    mul_eq_zero_of_disjoint_supp exoticImULDR_mem_supp exoticReELNuR_mem_supp (by decide)
  have h2 : exoticReELNuR * exoticImULDR = 0 :=
    mul_eq_zero_of_disjoint_supp exoticReELNuR_mem_supp exoticImULDR_mem_supp (by decide)
  rw [h1, h2, sub_self]

theorem comm_ImULDR_ImELNuR :
    exoticImULDR * exoticImELNuR - exoticImELNuR * exoticImULDR = 0 := by
  have h1 : exoticImULDR * exoticImELNuR = 0 :=
    mul_eq_zero_of_disjoint_supp exoticImULDR_mem_supp exoticImELNuR_mem_supp (by decide)
  have h2 : exoticImELNuR * exoticImULDR = 0 :=
    mul_eq_zero_of_disjoint_supp exoticImELNuR_mem_supp exoticImULDR_mem_supp (by decide)
  rw [h1, h2, sub_self]

theorem comm_ImULDR_ReNuREbarR :
    exoticImULDR * exoticReNuREbarR - exoticReNuREbarR * exoticImULDR = 0 := by
  have h1 : exoticImULDR * exoticReNuREbarR = 0 :=
    mul_eq_zero_of_disjoint_supp exoticImULDR_mem_supp exoticReNuREbarR_mem_supp (by decide)
  have h2 : exoticReNuREbarR * exoticImULDR = 0 :=
    mul_eq_zero_of_disjoint_supp exoticReNuREbarR_mem_supp exoticImULDR_mem_supp (by decide)
  rw [h1, h2, sub_self]

theorem comm_ImULDR_ImNuREbarR :
    exoticImULDR * exoticImNuREbarR - exoticImNuREbarR * exoticImULDR = 0 := by
  have h1 : exoticImULDR * exoticImNuREbarR = 0 :=
    mul_eq_zero_of_disjoint_supp exoticImULDR_mem_supp exoticImNuREbarR_mem_supp (by decide)
  have h2 : exoticImNuREbarR * exoticImULDR = 0 :=
    mul_eq_zero_of_disjoint_supp exoticImNuREbarR_mem_supp exoticImULDR_mem_supp (by decide)
  rw [h1, h2, sub_self]

theorem comm_ImULDR_ReEREbarR :
    exoticImULDR * exoticReEREbarR - exoticReEREbarR * exoticImULDR = 0 := by
  have h1 : exoticImULDR * exoticReEREbarR = 0 :=
    mul_eq_zero_of_disjoint_supp exoticImULDR_mem_supp exoticReEREbarR_mem_supp (by decide)
  have h2 : exoticReEREbarR * exoticImULDR = 0 :=
    mul_eq_zero_of_disjoint_supp exoticReEREbarR_mem_supp exoticImULDR_mem_supp (by decide)
  rw [h1, h2, sub_self]

theorem comm_ImULDR_ImEREbarR :
    exoticImULDR * exoticImEREbarR - exoticImEREbarR * exoticImULDR = 0 := by
  have h1 : exoticImULDR * exoticImEREbarR = 0 :=
    mul_eq_zero_of_disjoint_supp exoticImULDR_mem_supp exoticImEREbarR_mem_supp (by decide)
  have h2 : exoticImEREbarR * exoticImULDR = 0 :=
    mul_eq_zero_of_disjoint_supp exoticImEREbarR_mem_supp exoticImULDR_mem_supp (by decide)
  rw [h1, h2, sub_self]

-- ============================================================================
-- Sector B2 (DLUR pair) commutes with sector A
-- ============================================================================

theorem comm_ReDLUR_ReNuLeR :
    exoticReDLUR * exoticReNuLeR - exoticReNuLeR * exoticReDLUR = 0 := by
  have h1 : exoticReDLUR * exoticReNuLeR = 0 :=
    mul_eq_zero_of_disjoint_supp exoticReDLUR_mem_supp exoticReNuLeR_mem_supp (by decide)
  have h2 : exoticReNuLeR * exoticReDLUR = 0 :=
    mul_eq_zero_of_disjoint_supp exoticReNuLeR_mem_supp exoticReDLUR_mem_supp (by decide)
  rw [h1, h2, sub_self]

theorem comm_ReDLUR_ImNuLeR :
    exoticReDLUR * exoticImNuLeR - exoticImNuLeR * exoticReDLUR = 0 := by
  have h1 : exoticReDLUR * exoticImNuLeR = 0 :=
    mul_eq_zero_of_disjoint_supp exoticReDLUR_mem_supp exoticImNuLeR_mem_supp (by decide)
  have h2 : exoticImNuLeR * exoticReDLUR = 0 :=
    mul_eq_zero_of_disjoint_supp exoticImNuLeR_mem_supp exoticReDLUR_mem_supp (by decide)
  rw [h1, h2, sub_self]

theorem comm_ReDLUR_ReELNuR :
    exoticReDLUR * exoticReELNuR - exoticReELNuR * exoticReDLUR = 0 := by
  have h1 : exoticReDLUR * exoticReELNuR = 0 :=
    mul_eq_zero_of_disjoint_supp exoticReDLUR_mem_supp exoticReELNuR_mem_supp (by decide)
  have h2 : exoticReELNuR * exoticReDLUR = 0 :=
    mul_eq_zero_of_disjoint_supp exoticReELNuR_mem_supp exoticReDLUR_mem_supp (by decide)
  rw [h1, h2, sub_self]

theorem comm_ReDLUR_ImELNuR :
    exoticReDLUR * exoticImELNuR - exoticImELNuR * exoticReDLUR = 0 := by
  have h1 : exoticReDLUR * exoticImELNuR = 0 :=
    mul_eq_zero_of_disjoint_supp exoticReDLUR_mem_supp exoticImELNuR_mem_supp (by decide)
  have h2 : exoticImELNuR * exoticReDLUR = 0 :=
    mul_eq_zero_of_disjoint_supp exoticImELNuR_mem_supp exoticReDLUR_mem_supp (by decide)
  rw [h1, h2, sub_self]

theorem comm_ReDLUR_ReNuREbarR :
    exoticReDLUR * exoticReNuREbarR - exoticReNuREbarR * exoticReDLUR = 0 := by
  have h1 : exoticReDLUR * exoticReNuREbarR = 0 :=
    mul_eq_zero_of_disjoint_supp exoticReDLUR_mem_supp exoticReNuREbarR_mem_supp (by decide)
  have h2 : exoticReNuREbarR * exoticReDLUR = 0 :=
    mul_eq_zero_of_disjoint_supp exoticReNuREbarR_mem_supp exoticReDLUR_mem_supp (by decide)
  rw [h1, h2, sub_self]

theorem comm_ReDLUR_ImNuREbarR :
    exoticReDLUR * exoticImNuREbarR - exoticImNuREbarR * exoticReDLUR = 0 := by
  have h1 : exoticReDLUR * exoticImNuREbarR = 0 :=
    mul_eq_zero_of_disjoint_supp exoticReDLUR_mem_supp exoticImNuREbarR_mem_supp (by decide)
  have h2 : exoticImNuREbarR * exoticReDLUR = 0 :=
    mul_eq_zero_of_disjoint_supp exoticImNuREbarR_mem_supp exoticReDLUR_mem_supp (by decide)
  rw [h1, h2, sub_self]

theorem comm_ReDLUR_ReEREbarR :
    exoticReDLUR * exoticReEREbarR - exoticReEREbarR * exoticReDLUR = 0 := by
  have h1 : exoticReDLUR * exoticReEREbarR = 0 :=
    mul_eq_zero_of_disjoint_supp exoticReDLUR_mem_supp exoticReEREbarR_mem_supp (by decide)
  have h2 : exoticReEREbarR * exoticReDLUR = 0 :=
    mul_eq_zero_of_disjoint_supp exoticReEREbarR_mem_supp exoticReDLUR_mem_supp (by decide)
  rw [h1, h2, sub_self]

theorem comm_ReDLUR_ImEREbarR :
    exoticReDLUR * exoticImEREbarR - exoticImEREbarR * exoticReDLUR = 0 := by
  have h1 : exoticReDLUR * exoticImEREbarR = 0 :=
    mul_eq_zero_of_disjoint_supp exoticReDLUR_mem_supp exoticImEREbarR_mem_supp (by decide)
  have h2 : exoticImEREbarR * exoticReDLUR = 0 :=
    mul_eq_zero_of_disjoint_supp exoticImEREbarR_mem_supp exoticReDLUR_mem_supp (by decide)
  rw [h1, h2, sub_self]

theorem comm_ImDLUR_ReNuLeR :
    exoticImDLUR * exoticReNuLeR - exoticReNuLeR * exoticImDLUR = 0 := by
  have h1 : exoticImDLUR * exoticReNuLeR = 0 :=
    mul_eq_zero_of_disjoint_supp exoticImDLUR_mem_supp exoticReNuLeR_mem_supp (by decide)
  have h2 : exoticReNuLeR * exoticImDLUR = 0 :=
    mul_eq_zero_of_disjoint_supp exoticReNuLeR_mem_supp exoticImDLUR_mem_supp (by decide)
  rw [h1, h2, sub_self]

theorem comm_ImDLUR_ImNuLeR :
    exoticImDLUR * exoticImNuLeR - exoticImNuLeR * exoticImDLUR = 0 := by
  have h1 : exoticImDLUR * exoticImNuLeR = 0 :=
    mul_eq_zero_of_disjoint_supp exoticImDLUR_mem_supp exoticImNuLeR_mem_supp (by decide)
  have h2 : exoticImNuLeR * exoticImDLUR = 0 :=
    mul_eq_zero_of_disjoint_supp exoticImNuLeR_mem_supp exoticImDLUR_mem_supp (by decide)
  rw [h1, h2, sub_self]

theorem comm_ImDLUR_ReELNuR :
    exoticImDLUR * exoticReELNuR - exoticReELNuR * exoticImDLUR = 0 := by
  have h1 : exoticImDLUR * exoticReELNuR = 0 :=
    mul_eq_zero_of_disjoint_supp exoticImDLUR_mem_supp exoticReELNuR_mem_supp (by decide)
  have h2 : exoticReELNuR * exoticImDLUR = 0 :=
    mul_eq_zero_of_disjoint_supp exoticReELNuR_mem_supp exoticImDLUR_mem_supp (by decide)
  rw [h1, h2, sub_self]

theorem comm_ImDLUR_ImELNuR :
    exoticImDLUR * exoticImELNuR - exoticImELNuR * exoticImDLUR = 0 := by
  have h1 : exoticImDLUR * exoticImELNuR = 0 :=
    mul_eq_zero_of_disjoint_supp exoticImDLUR_mem_supp exoticImELNuR_mem_supp (by decide)
  have h2 : exoticImELNuR * exoticImDLUR = 0 :=
    mul_eq_zero_of_disjoint_supp exoticImELNuR_mem_supp exoticImDLUR_mem_supp (by decide)
  rw [h1, h2, sub_self]

theorem comm_ImDLUR_ReNuREbarR :
    exoticImDLUR * exoticReNuREbarR - exoticReNuREbarR * exoticImDLUR = 0 := by
  have h1 : exoticImDLUR * exoticReNuREbarR = 0 :=
    mul_eq_zero_of_disjoint_supp exoticImDLUR_mem_supp exoticReNuREbarR_mem_supp (by decide)
  have h2 : exoticReNuREbarR * exoticImDLUR = 0 :=
    mul_eq_zero_of_disjoint_supp exoticReNuREbarR_mem_supp exoticImDLUR_mem_supp (by decide)
  rw [h1, h2, sub_self]

theorem comm_ImDLUR_ImNuREbarR :
    exoticImDLUR * exoticImNuREbarR - exoticImNuREbarR * exoticImDLUR = 0 := by
  have h1 : exoticImDLUR * exoticImNuREbarR = 0 :=
    mul_eq_zero_of_disjoint_supp exoticImDLUR_mem_supp exoticImNuREbarR_mem_supp (by decide)
  have h2 : exoticImNuREbarR * exoticImDLUR = 0 :=
    mul_eq_zero_of_disjoint_supp exoticImNuREbarR_mem_supp exoticImDLUR_mem_supp (by decide)
  rw [h1, h2, sub_self]

theorem comm_ImDLUR_ReEREbarR :
    exoticImDLUR * exoticReEREbarR - exoticReEREbarR * exoticImDLUR = 0 := by
  have h1 : exoticImDLUR * exoticReEREbarR = 0 :=
    mul_eq_zero_of_disjoint_supp exoticImDLUR_mem_supp exoticReEREbarR_mem_supp (by decide)
  have h2 : exoticReEREbarR * exoticImDLUR = 0 :=
    mul_eq_zero_of_disjoint_supp exoticReEREbarR_mem_supp exoticImDLUR_mem_supp (by decide)
  rw [h1, h2, sub_self]

theorem comm_ImDLUR_ImEREbarR :
    exoticImDLUR * exoticImEREbarR - exoticImEREbarR * exoticImDLUR = 0 := by
  have h1 : exoticImDLUR * exoticImEREbarR = 0 :=
    mul_eq_zero_of_disjoint_supp exoticImDLUR_mem_supp exoticImEREbarR_mem_supp (by decide)
  have h2 : exoticImEREbarR * exoticImDLUR = 0 :=
    mul_eq_zero_of_disjoint_supp exoticImEREbarR_mem_supp exoticImDLUR_mem_supp (by decide)
  rw [h1, h2, sub_self]

-- ============================================================================
-- Sector B1 commutes with sector B2
-- ============================================================================

theorem comm_ReULDR_ReDLUR :
    exoticReULDR * exoticReDLUR - exoticReDLUR * exoticReULDR = 0 := by
  have h1 : exoticReULDR * exoticReDLUR = 0 :=
    mul_eq_zero_of_disjoint_supp exoticReULDR_mem_supp exoticReDLUR_mem_supp (by decide)
  have h2 : exoticReDLUR * exoticReULDR = 0 :=
    mul_eq_zero_of_disjoint_supp exoticReDLUR_mem_supp exoticReULDR_mem_supp (by decide)
  rw [h1, h2, sub_self]

theorem comm_ReULDR_ImDLUR :
    exoticReULDR * exoticImDLUR - exoticImDLUR * exoticReULDR = 0 := by
  have h1 : exoticReULDR * exoticImDLUR = 0 :=
    mul_eq_zero_of_disjoint_supp exoticReULDR_mem_supp exoticImDLUR_mem_supp (by decide)
  have h2 : exoticImDLUR * exoticReULDR = 0 :=
    mul_eq_zero_of_disjoint_supp exoticImDLUR_mem_supp exoticReULDR_mem_supp (by decide)
  rw [h1, h2, sub_self]

theorem comm_ImULDR_ReDLUR :
    exoticImULDR * exoticReDLUR - exoticReDLUR * exoticImULDR = 0 := by
  have h1 : exoticImULDR * exoticReDLUR = 0 :=
    mul_eq_zero_of_disjoint_supp exoticImULDR_mem_supp exoticReDLUR_mem_supp (by decide)
  have h2 : exoticReDLUR * exoticImULDR = 0 :=
    mul_eq_zero_of_disjoint_supp exoticReDLUR_mem_supp exoticImULDR_mem_supp (by decide)
  rw [h1, h2, sub_self]

theorem comm_ImULDR_ImDLUR :
    exoticImULDR * exoticImDLUR - exoticImDLUR * exoticImULDR = 0 := by
  have h1 : exoticImULDR * exoticImDLUR = 0 :=
    mul_eq_zero_of_disjoint_supp exoticImULDR_mem_supp exoticImDLUR_mem_supp (by decide)
  have h2 : exoticImDLUR * exoticImULDR = 0 :=
    mul_eq_zero_of_disjoint_supp exoticImDLUR_mem_supp exoticImULDR_mem_supp (by decide)
  rw [h1, h2, sub_self]

-- ============================================================================
-- The B-sectors are non-abelian internally: [Re, Im] ≠ 0
-- ============================================================================

-- Single-entry facts for the ULDR pair at the (2,11)/(11,2) positions.
theorem exoticReULDR_2_11 : exoticReULDR 2 11 = (1 : ℂ) := by simp [exoticReULDR]
theorem exoticReULDR_11_2 : exoticReULDR 11 2 = (1 : ℂ) := by simp [exoticReULDR]
theorem exoticImULDR_2_11 : exoticImULDR 2 11 = Complex.I := by simp [exoticImULDR]
theorem exoticImULDR_11_2 : exoticImULDR 11 2 = -Complex.I := by simp [exoticImULDR]

-- Row 2 of each ULDR matrix is supported only at column 11.
theorem exoticReULDR_row2 (k : I32) (hk : k ≠ 11) : exoticReULDR 2 k = 0 := by
  by_contra hne
  rcases exoticReULDR_supp 2 k hne with ⟨_, rfl⟩|⟨h,_⟩|⟨h,_⟩|⟨h,_⟩|⟨h,_⟩|⟨h,_⟩|⟨h,_⟩|⟨h,_⟩|⟨h,_⟩|⟨h,_⟩|⟨h,_⟩|⟨h,_⟩
  · exact hk rfl
  · exact (by decide : (2:I32) ≠ 11) h
  · exact (by decide : (2:I32) ≠ 4) h
  · exact (by decide : (2:I32) ≠ 13) h
  · exact (by decide : (2:I32) ≠ 6) h
  · exact (by decide : (2:I32) ≠ 15) h
  · exact (by decide : (2:I32) ≠ 18) h
  · exact (by decide : (2:I32) ≠ 27) h
  · exact (by decide : (2:I32) ≠ 20) h
  · exact (by decide : (2:I32) ≠ 29) h
  · exact (by decide : (2:I32) ≠ 22) h
  · exact (by decide : (2:I32) ≠ 31) h

theorem exoticImULDR_row2 (k : I32) (hk : k ≠ 11) : exoticImULDR 2 k = 0 := by
  by_contra hne
  rcases exoticImULDR_supp 2 k hne with ⟨_, rfl⟩|⟨h,_⟩|⟨h,_⟩|⟨h,_⟩|⟨h,_⟩|⟨h,_⟩|⟨h,_⟩|⟨h,_⟩|⟨h,_⟩|⟨h,_⟩|⟨h,_⟩|⟨h,_⟩
  · exact hk rfl
  · exact (by decide : (2:I32) ≠ 4) h
  · exact (by decide : (2:I32) ≠ 6) h
  · exact (by decide : (2:I32) ≠ 27) h
  · exact (by decide : (2:I32) ≠ 29) h
  · exact (by decide : (2:I32) ≠ 31) h
  · exact (by decide : (2:I32) ≠ 11) h
  · exact (by decide : (2:I32) ≠ 13) h
  · exact (by decide : (2:I32) ≠ 15) h
  · exact (by decide : (2:I32) ≠ 18) h
  · exact (by decide : (2:I32) ≠ 20) h
  · exact (by decide : (2:I32) ≠ 22) h

theorem prod_B1_22a : (exoticReULDR * exoticImULDR) 2 2 = -Complex.I := by
  rw [Matrix.mul_apply,
    Finset.sum_eq_single 11
      (fun k _ hk => by rw [exoticReULDR_row2 k hk, zero_mul])
      (fun h => absurd (Finset.mem_univ 11) h),
    exoticReULDR_2_11, exoticImULDR_11_2, one_mul]

theorem prod_B1_22b : (exoticImULDR * exoticReULDR) 2 2 = Complex.I := by
  rw [Matrix.mul_apply,
    Finset.sum_eq_single 11
      (fun k _ hk => by rw [exoticImULDR_row2 k hk, zero_mul])
      (fun h => absurd (Finset.mem_univ 11) h),
    exoticImULDR_2_11, exoticReULDR_11_2, mul_one]

theorem comm_B1_22 :
    (exoticReULDR * exoticImULDR - exoticImULDR * exoticReULDR) 2 2
      = -2 * Complex.I := by
  rw [Matrix.sub_apply, prod_B1_22a, prod_B1_22b]
  ring

theorem exoticSector_B1_nonabelian :
    exoticReULDR * exoticImULDR - exoticImULDR * exoticReULDR ≠ 0 := by
  intro h
  have h2 := congr_fun (congr_fun h 2) 2
  simp only [Matrix.zero_apply] at h2
  rw [comm_B1_22] at h2
  exact (mul_ne_zero (by norm_num) Complex.I_ne_zero) h2

-- Single-entry facts for the DLUR pair at the (3,10)/(10,3) positions.
theorem exoticReDLUR_3_10 : exoticReDLUR 3 10 = (1 : ℂ) := by simp [exoticReDLUR]
theorem exoticReDLUR_10_3 : exoticReDLUR 10 3 = (1 : ℂ) := by simp [exoticReDLUR]
theorem exoticImDLUR_3_10 : exoticImDLUR 3 10 = Complex.I := by simp [exoticImDLUR]
theorem exoticImDLUR_10_3 : exoticImDLUR 10 3 = -Complex.I := by simp [exoticImDLUR]

-- Row 3 of each DLUR matrix is supported only at column 10.
theorem exoticReDLUR_row3 (k : I32) (hk : k ≠ 10) : exoticReDLUR 3 k = 0 := by
  by_contra hne
  rcases exoticReDLUR_supp 3 k hne with ⟨_, rfl⟩|⟨h,_⟩|⟨h,_⟩|⟨h,_⟩|⟨h,_⟩|⟨h,_⟩|⟨h,_⟩|⟨h,_⟩|⟨h,_⟩|⟨h,_⟩|⟨h,_⟩|⟨h,_⟩
  · exact hk rfl
  · exact (by decide : (3:I32) ≠ 10) h
  · exact (by decide : (3:I32) ≠ 5) h
  · exact (by decide : (3:I32) ≠ 12) h
  · exact (by decide : (3:I32) ≠ 7) h
  · exact (by decide : (3:I32) ≠ 14) h
  · exact (by decide : (3:I32) ≠ 19) h
  · exact (by decide : (3:I32) ≠ 26) h
  · exact (by decide : (3:I32) ≠ 21) h
  · exact (by decide : (3:I32) ≠ 28) h
  · exact (by decide : (3:I32) ≠ 23) h
  · exact (by decide : (3:I32) ≠ 30) h

theorem exoticImDLUR_row3 (k : I32) (hk : k ≠ 10) : exoticImDLUR 3 k = 0 := by
  by_contra hne
  rcases exoticImDLUR_supp 3 k hne with ⟨_, rfl⟩|⟨h,_⟩|⟨h,_⟩|⟨h,_⟩|⟨h,_⟩|⟨h,_⟩|⟨h,_⟩|⟨h,_⟩|⟨h,_⟩|⟨h,_⟩|⟨h,_⟩|⟨h,_⟩
  · exact hk rfl
  · exact (by decide : (3:I32) ≠ 5) h
  · exact (by decide : (3:I32) ≠ 7) h
  · exact (by decide : (3:I32) ≠ 26) h
  · exact (by decide : (3:I32) ≠ 28) h
  · exact (by decide : (3:I32) ≠ 30) h
  · exact (by decide : (3:I32) ≠ 10) h
  · exact (by decide : (3:I32) ≠ 12) h
  · exact (by decide : (3:I32) ≠ 14) h
  · exact (by decide : (3:I32) ≠ 19) h
  · exact (by decide : (3:I32) ≠ 21) h
  · exact (by decide : (3:I32) ≠ 23) h

theorem prod_B2_33a : (exoticReDLUR * exoticImDLUR) 3 3 = -Complex.I := by
  rw [Matrix.mul_apply,
    Finset.sum_eq_single 10
      (fun k _ hk => by rw [exoticReDLUR_row3 k hk, zero_mul])
      (fun h => absurd (Finset.mem_univ 10) h),
    exoticReDLUR_3_10, exoticImDLUR_10_3, one_mul]

theorem prod_B2_33b : (exoticImDLUR * exoticReDLUR) 3 3 = Complex.I := by
  rw [Matrix.mul_apply,
    Finset.sum_eq_single 10
      (fun k _ hk => by rw [exoticImDLUR_row3 k hk, zero_mul])
      (fun h => absurd (Finset.mem_univ 10) h),
    exoticImDLUR_3_10, exoticReDLUR_10_3, mul_one]

theorem comm_B2_33 :
    (exoticReDLUR * exoticImDLUR - exoticImDLUR * exoticReDLUR) 3 3
      = -2 * Complex.I := by
  rw [Matrix.sub_apply, prod_B2_33a, prod_B2_33b]
  ring

theorem exoticSector_B2_nonabelian :
    exoticReDLUR * exoticImDLUR - exoticImDLUR * exoticReDLUR ≠ 0 := by
  intro h
  have h3 := congr_fun (congr_fun h 3) 3
  simp only [Matrix.zero_apply] at h3
  rw [comm_B2_33] at h3
  exact (mul_ne_zero (by norm_num) Complex.I_ne_zero) h3

-- ============================================================================
-- The B1 pair plus its commutator spans a 3-dimensional space
-- (linear independence over ℂ)
-- ============================================================================

-- Diagonal entries vanish.
theorem exoticReULDR_2_2 : exoticReULDR 2 2 = (0 : ℂ) := by simp [exoticReULDR]
theorem exoticImULDR_2_2 : exoticImULDR 2 2 = (0 : ℂ) := by simp [exoticImULDR]
theorem exoticReULDR_11_11 : exoticReULDR 11 11 = (0 : ℂ) := by simp [exoticReULDR]
theorem exoticImULDR_11_11 : exoticImULDR 11 11 = (0 : ℂ) := by simp [exoticImULDR]

-- Row 11 of each ULDR matrix is supported only at column 2.
theorem exoticReULDR_row11 (k : I32) (hk : k ≠ 2) : exoticReULDR 11 k = 0 := by
  by_contra hne
  rcases exoticReULDR_supp 11 k hne with ⟨h,_⟩|⟨_, rfl⟩|⟨h,_⟩|⟨h,_⟩|⟨h,_⟩|⟨h,_⟩|⟨h,_⟩|⟨h,_⟩|⟨h,_⟩|⟨h,_⟩|⟨h,_⟩|⟨h,_⟩
  · exact (by decide : (11:I32) ≠ 2) h
  · exact hk rfl
  · exact (by decide : (11:I32) ≠ 4) h
  · exact (by decide : (11:I32) ≠ 13) h
  · exact (by decide : (11:I32) ≠ 6) h
  · exact (by decide : (11:I32) ≠ 15) h
  · exact (by decide : (11:I32) ≠ 18) h
  · exact (by decide : (11:I32) ≠ 27) h
  · exact (by decide : (11:I32) ≠ 20) h
  · exact (by decide : (11:I32) ≠ 29) h
  · exact (by decide : (11:I32) ≠ 22) h
  · exact (by decide : (11:I32) ≠ 31) h

theorem exoticImULDR_row11 (k : I32) (hk : k ≠ 2) : exoticImULDR 11 k = 0 := by
  by_contra hne
  rcases exoticImULDR_supp 11 k hne with ⟨h,_⟩|⟨h,_⟩|⟨h,_⟩|⟨h,_⟩|⟨h,_⟩|⟨h,_⟩|⟨_, rfl⟩|⟨h,_⟩|⟨h,_⟩|⟨h,_⟩|⟨h,_⟩|⟨h,_⟩
  · exact (by decide : (11:I32) ≠ 2) h
  · exact (by decide : (11:I32) ≠ 4) h
  · exact (by decide : (11:I32) ≠ 6) h
  · exact (by decide : (11:I32) ≠ 27) h
  · exact (by decide : (11:I32) ≠ 29) h
  · exact (by decide : (11:I32) ≠ 31) h
  · exact hk rfl
  · exact (by decide : (11:I32) ≠ 13) h
  · exact (by decide : (11:I32) ≠ 15) h
  · exact (by decide : (11:I32) ≠ 18) h
  · exact (by decide : (11:I32) ≠ 20) h
  · exact (by decide : (11:I32) ≠ 22) h

-- The commutator vanishes at the (2,11) and (11,2) entries.
theorem comm_B1_211 :
    (exoticReULDR * exoticImULDR - exoticImULDR * exoticReULDR) 2 11 = 0 := by
  have e1 : (exoticReULDR * exoticImULDR) 2 11 = 0 := by
    rw [Matrix.mul_apply,
      Finset.sum_eq_single 11
        (fun k _ hk => by rw [exoticReULDR_row2 k hk, zero_mul])
        (fun h => absurd (Finset.mem_univ 11) h),
      exoticReULDR_2_11, exoticImULDR_11_11, one_mul]
  have e2 : (exoticImULDR * exoticReULDR) 2 11 = 0 := by
    rw [Matrix.mul_apply,
      Finset.sum_eq_single 11
        (fun k _ hk => by rw [exoticImULDR_row2 k hk, zero_mul])
        (fun h => absurd (Finset.mem_univ 11) h),
      exoticImULDR_2_11, exoticReULDR_11_11, mul_zero]
  rw [Matrix.sub_apply, e1, e2, sub_self]

theorem comm_B1_112 :
    (exoticReULDR * exoticImULDR - exoticImULDR * exoticReULDR) 11 2 = 0 := by
  have e1 : (exoticReULDR * exoticImULDR) 11 2 = 0 := by
    rw [Matrix.mul_apply,
      Finset.sum_eq_single 2
        (fun k _ hk => by rw [exoticReULDR_row11 k hk, zero_mul])
        (fun h => absurd (Finset.mem_univ 2) h),
      exoticReULDR_11_2, exoticImULDR_2_2, one_mul]
  have e2 : (exoticImULDR * exoticReULDR) 11 2 = 0 := by
    rw [Matrix.mul_apply,
      Finset.sum_eq_single 2
        (fun k _ hk => by rw [exoticImULDR_row11 k hk, zero_mul])
        (fun h => absurd (Finset.mem_univ 2) h),
      exoticImULDR_11_2, exoticReULDR_2_2, mul_zero]
  rw [Matrix.sub_apply, e1, e2, sub_self]

-- Linear independence of {ReULDR, ImULDR, [ReULDR, ImULDR]} over ℂ.
-- The evaluation matrix at entries (2,2), (2,11), (11,2) is triangular
-- up to the (2,11)/(11,2) pair, which is then solved directly.
theorem exoticSector_B1_lie3 : LinearIndependent ℂ
    ![exoticReULDR, exoticImULDR,
      exoticReULDR * exoticImULDR - exoticImULDR * exoticReULDR] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  rw [Fin.sum_univ_three] at hg
  -- Reduce the `![...]` indexing definitionally.
  have hc0 : (![exoticReULDR, exoticImULDR,
      exoticReULDR * exoticImULDR - exoticImULDR * exoticReULDR] : Fin 3 → _) 0
      = exoticReULDR := rfl
  have hc1 : (![exoticReULDR, exoticImULDR,
      exoticReULDR * exoticImULDR - exoticImULDR * exoticReULDR] : Fin 3 → _) 1
      = exoticImULDR := rfl
  have hc2 : (![exoticReULDR, exoticImULDR,
      exoticReULDR * exoticImULDR - exoticImULDR * exoticReULDR] : Fin 3 → _) 2
      = exoticReULDR * exoticImULDR - exoticImULDR * exoticReULDR := rfl
  rw [hc0, hc1, hc2] at hg
  have e22 := congr_fun (congr_fun hg 2) 2
  have e211 := congr_fun (congr_fun hg 2) 11
  have e112 := congr_fun (congr_fun hg 11) 2
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.zero_apply, smul_eq_mul,
    exoticReULDR_2_2, exoticImULDR_2_2, comm_B1_22,
    exoticReULDR_2_11, exoticImULDR_2_11, comm_B1_211,
    exoticReULDR_11_2, exoticImULDR_11_2, comm_B1_112,
    mul_zero, add_zero, zero_add, mul_one] at e22 e211 e112
  -- e22 : g 2 * (-2 * I) = 0
  -- e211 : g 0 + g 1 * I = 0
  -- e112 : g 0 + g 1 * (-I) = 0
  have hg2 : g 2 = 0 :=
    (mul_eq_zero.mp e22).resolve_right
      (mul_ne_zero (by norm_num) Complex.I_ne_zero)
  have hg0 : g 0 = 0 := by
    have h2 : (2:ℂ) * g 0 = 0 := by linear_combination e211 + e112
    exact (mul_eq_zero.mp h2).resolve_left (by norm_num)
  have hg1 : g 1 = 0 := by
    rw [hg0] at e211
    simp only [zero_add] at e211
    exact (mul_eq_zero.mp e211).resolve_right Complex.I_ne_zero
  intro i
  fin_cases i <;> assumption

end ThetLogos
