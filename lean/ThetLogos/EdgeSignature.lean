/-
  EdgeSignature.lean — Gentle gauntlet: Morley / 3+1 emergence, steelmanned.

  Jeff's idea (2026-10-11): Morley's miracle takes an arbitrary triangle and
  finds a perfect equilateral triangle inside via trisectors — arbitrary input,
  perfect structure out. The naive 3D lift fails (no tetrahedron analogue).
  Question: can a 4D boundary carrying TWO 2D edge operators generate the
  3+1 (space+time) split?

  Concrete anchor: in 4D, 2-forms split self-dual/anti-self-dual, and that
  split IS signature-sensitive (⋆² = −1 Lorentzian). The Krein η (η² = 1)
  from Rung 3 is the abstract fundamental symmetry encoding signature.

  Jeff's refinement (built in): the projection from D_F may carry
  torsion/twist — carried here, never assumed away:
  - the Rung-2 flip twist is carried through §2 (equivariance);
  - torsion is modeled as an additive defect η ↦ η + T with the EXACT
    idempotence defect computed (§3);
  - the killed ℂ⁷-torsion claim is NOT resurrected (kill ledger stands).

  What this file proves (all T1, zero sorrys, zero new axioms):
  §1. Edge operators from a fundamental symmetry (Morley core):
      η² = 1 ⟹ perfect complementary orthogonal idempotent pair (E₊, E₋);
      and back — edge-pair ⟺ fundamental symmetry (bijection of data).
      The perfection is FORCED by η² = 1 alone: arbitrary η in,
      perfect pair out. That is the formal content of the Morley analogy.
  §2. Flip-twist equivariance: the doubled edge operators commute with the
      flip (Rung-2 twist preserves the edge decomposition).
  §3. Torsion defect: (η+T)² = 1 + (ηT + Tη + T²); the fluctuated edge
      operators miss idempotence by exactly (2⁻¹)² • (ηT + Tη + T²);
      torsion-flatness ⟺ ηT + Tη + T² = 0.
  §4. Signature non-emergence (honest NO-GO for the strong claim): two
      fundamental symmetries on M₂(ℂ), both squaring to 1, whose edge
      operators differ (signatures (2,0) vs (1,1)). η² = 1 does NOT
      determine the signature — the 3+1 numbers are extra data.

  Tier: T1 throughout. The Morley-analogy assessment and the D_F-specific
  torsion map are priced in whitepaper/gauntlet-morley-3plus1-2026-10-11.md.
-/

import Mathlib

namespace ThetLogos

variable {R : Type*} [Ring R] [Algebra ℂ R]

/-- Scalar helper: `(a • x) * (b • y) = (a*b) • (x*y)` in a ℂ-algebra. -/
private theorem smul_mul_smul' (a b : ℂ) (x y : R) :
    (a • x) * (b • y) = (a * b) • (x * y) := by
  rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, ← mul_smul]

/-- `(2:ℂ)⁻¹ + (2:ℂ)⁻¹ = 1`. -/
private theorem inv_two_add_self : (2 : ℂ)⁻¹ + (2 : ℂ)⁻¹ = 1 := by
  have hne : (2 : ℂ) ≠ 0 := by norm_num
  rw [← two_mul, mul_inv_cancel₀ hne]

/-- `((2:ℂ)⁻¹ * (2:ℂ)⁻¹) + ((2:ℂ)⁻¹ * (2:ℂ)⁻¹) = (2:ℂ)⁻¹`. -/
private theorem sq_inv_two_add :
    ((2 : ℂ)⁻¹ * (2 : ℂ)⁻¹) + ((2 : ℂ)⁻¹ * (2 : ℂ)⁻¹) = (2 : ℂ)⁻¹ := by
  rw [← mul_add, inv_two_add_self, mul_one]

/-- `(2:ℂ)⁻¹ * 2 = 1`. -/
private theorem inv_two_mul_two : (2 : ℂ)⁻¹ * 2 = 1 :=
  inv_mul_cancel₀ (by norm_num)

/-- Scalar engine for the torsion defect. -/
private theorem torsion_scalar (X D : R) :
    ((2:ℂ)⁻¹ * (2:ℂ)⁻¹) • (X + X + D)
      = (2:ℂ)⁻¹ • X + ((2:ℂ)⁻¹ * (2:ℂ)⁻¹) • D := by
  rw [smul_add, smul_add, ← add_smul, sq_inv_two_add]

-- ============================================================================
-- §1. Edge operators from a fundamental symmetry (the Morley core)
-- ============================================================================

/-- The two edge operators from a fundamental symmetry:
    `E₊ = (1+η)/2`, `E₋ = (1−η)/2` — the abstract self-dual/anti-self-dual pair. -/
noncomputable def edgePlus (η : R) : R := (2 : ℂ)⁻¹ • (1 + η)

/-- The two edge operators from a fundamental symmetry:
    `E₊ = (1+η)/2`, `E₋ = (1−η)/2` — the abstract self-dual/anti-self-dual pair. -/
noncomputable def edgeMinus (η : R) : R := (2 : ℂ)⁻¹ • (1 - η)

/-- A perfect edge pair: complementary orthogonal idempotents. -/
structure IsEdgePair (e₁ e₂ : R) : Prop where
  idem_left : e₁ * e₁ = e₁
  idem_right : e₂ * e₂ = e₂
  orth_lr : e₁ * e₂ = 0
  orth_rl : e₂ * e₁ = 0
  compl : e₁ + e₂ = 1

/-- Unnormalized engine: `(1+η)² = 2(1+η)` from `η² = 1`. -/
private theorem add_one_sq (η : R) (h : η * η = 1) :
    (1 + η) * (1 + η) = (1 + η) + (1 + η) := by
  have expand : (1 + η) * (1 + η) = 1 + (η + η) + η * η := by
    rw [add_mul, one_mul, mul_add, mul_one]; abel
  rw [expand, h]; abel

/-- Unnormalized engine: `(1−η)² = 2(1−η)` from `η² = 1`. -/
private theorem sub_one_sq (η : R) (h : η * η = 1) :
    (1 - η) * (1 - η) = (1 - η) + (1 - η) := by
  have expand : (1 - η) * (1 - η) = 1 - (η + η) + η * η := by
    rw [sub_mul, one_mul, mul_sub, mul_one]; abel
  rw [expand, h]; abel

/-- Unnormalized engine: `(1+η)(1−η) = 0` from `η² = 1`. -/
private theorem add_sub_orth (η : R) (h : η * η = 1) :
    (1 + η) * (1 - η) = 0 := by
  have expand : (1 + η) * (1 - η) = 1 + (η - η) - η * η := by
    rw [add_mul, one_mul, mul_sub, mul_one]; abel
  rw [expand, h]; simp

/-- Unnormalized engine: `(1−η)(1+η) = 0` from `η² = 1`. -/
private theorem sub_add_orth (η : R) (h : η * η = 1) :
    (1 - η) * (1 + η) = 0 := by
  have expand : (1 - η) * (1 + η) = 1 + (η - η) - η * η := by
    rw [sub_mul, one_mul, mul_add, mul_one]; abel
  rw [expand, h]; simp

/-- `E₊² = E₊` (T1): idempotence forced by `η² = 1` alone. -/
theorem edgePlus_idem (η : R) (h : η * η = 1) :
    edgePlus η * edgePlus η = edgePlus η := by
  unfold edgePlus
  rw [smul_mul_smul', add_one_sq _ h, smul_add, ← add_smul, sq_inv_two_add]

/-- `E₋² = E₋` (T1). -/
theorem edgeMinus_idem (η : R) (h : η * η = 1) :
    edgeMinus η * edgeMinus η = edgeMinus η := by
  unfold edgeMinus
  rw [smul_mul_smul', sub_one_sq _ h, smul_add, ← add_smul, sq_inv_two_add]

/-- `E₊E₋ = 0` (T1): orthogonality forced by `η² = 1` alone. -/
theorem edge_orth_lr (η : R) (h : η * η = 1) :
    edgePlus η * edgeMinus η = 0 := by
  unfold edgePlus edgeMinus
  rw [smul_mul_smul', add_sub_orth _ h, smul_zero]

/-- `E₋E₊ = 0` (T1). -/
theorem edge_orth_rl (η : R) (h : η * η = 1) :
    edgeMinus η * edgePlus η = 0 := by
  unfold edgePlus edgeMinus
  rw [smul_mul_smul', sub_add_orth _ h, smul_zero]

/-- `E₊ + E₋ = 1` (T1): complementarity. -/
theorem edge_compl (η : R) : edgePlus η + edgeMinus η = 1 := by
  unfold edgePlus edgeMinus
  have hadd : ((1 : R) + η) + (1 - η) = 1 + 1 := by abel
  rw [← smul_add, hadd, smul_add, ← add_smul, inv_two_add_self, one_smul]

/-- `η = E₊ − E₋` (T1): the fundamental symmetry recovered from its edges. -/
theorem edge_recover (η : R) : edgePlus η - edgeMinus η = η := by
  unfold edgePlus edgeMinus
  have hsub : ((1 : R) + η) - (1 - η) = η + η := by abel
  rw [← smul_sub, hsub, smul_add, ← add_smul, inv_two_add_self, one_smul]

/-- Morley core (T1): arbitrary `η` with `η² = 1` yields a PERFECT edge pair.
    The perfection (idempotence, orthogonality, complementarity) uses nothing
    beyond `η² = 1` — arbitrary input, perfect structure out. -/
theorem edgePair_of_symm (η : R) (h : η * η = 1) :
    IsEdgePair (edgePlus η) (edgeMinus η) :=
  { idem_left := edgePlus_idem η h
    idem_right := edgeMinus_idem η h
    orth_lr := edge_orth_lr η h
    orth_rl := edge_orth_rl η h
    compl := edge_compl η }

/-- Converse (T1): a perfect edge pair recovers a fundamental symmetry.
    Edge-pair data ⟺ fundamental-symmetry data: a bijection. -/
theorem symm_of_edgePair {e₁ e₂ : R} (h : IsEdgePair e₁ e₂) :
    (e₁ - e₂) * (e₁ - e₂) = 1 := by
  obtain ⟨h1, h2, h12, h21, hcompl⟩ := h
  have expand : (e₁ - e₂) * (e₁ - e₂)
      = e₁ * e₁ - e₁ * e₂ - e₂ * e₁ + e₂ * e₂ := by
    rw [sub_mul, mul_sub, mul_sub]; abel
  rw [expand, h1, h12, h21, h2]
  have hzero : e₁ - 0 - 0 + e₂ = e₁ + e₂ := by abel
  rw [hzero, hcompl]

-- ============================================================================
-- §2. Flip-twist equivariance (Rung-2 twist carried, not assumed away)
-- ============================================================================

/-- The flip on doubled edge data — cf. Rung 2's `flipProd`
    (`ProductTriple.lean`): the twist derived as the flip, carried here
    (definitionally identical). -/
def pairFlip {T : Type*} (p : T × T) : T × T := (p.2, p.1)

/-- Doubled edge operators: componentwise on pairs. -/
noncomputable def edgePlusPair (η₁ η₂ : R) : R × R := (edgePlus η₁, edgePlus η₂)

/-- Doubled edge operators: componentwise on pairs. -/
noncomputable def edgeMinusPair (η₁ η₂ : R) : R × R := (edgeMinus η₁, edgeMinus η₂)

/-- The flip swaps the two edge copies (T1). -/
theorem edgePlusPair_flip (η₁ η₂ : R) :
    pairFlip (edgePlusPair η₁ η₂) = edgePlusPair η₂ η₁ := rfl

/-- The flip swaps the two edge copies (T1). -/
theorem edgeMinusPair_flip (η₁ η₂ : R) :
    pairFlip (edgeMinusPair η₁ η₂) = edgeMinusPair η₂ η₁ := rfl

/-- For the doubled fundamental symmetry `(η,η)`, the edge pair is
    flip-INVARIANT (T1): the Rung-2 twist preserves the edge decomposition —
    Morley perfection survives the twist. -/
theorem edgePlusPair_diag_flip (η : R) :
    pairFlip (edgePlusPair η η) = edgePlusPair η η := rfl

/-- For the doubled fundamental symmetry `(η,η)`, the edge pair is
    flip-INVARIANT (T1). -/
theorem edgeMinusPair_diag_flip (η : R) :
    pairFlip (edgeMinusPair η η) = edgeMinusPair η η := rfl

-- ============================================================================
-- §3. Torsion defect (Jeff's refinement: torsion twist in the projection)
-- ============================================================================

/-- Torsion defect equation (T1): `(η+T)² = 1 + (ηT + Tη + T²)` given `η² = 1`.
    The defect from perfection is EXACT — no hand-waving. -/
theorem torsion_defect (η T : R) (h : η * η = 1) :
    (η + T) * (η + T) = 1 + (η * T + T * η + T * T) := by
  have expand : (η + T) * (η + T) = η * η + (η * T + T * η) + T * T := by
    rw [add_mul, mul_add, mul_add]; abel
  rw [expand, h]; abel

/-- Torsion-flatness (T1): `η+T` is a fundamental symmetry iff the
    Maurer–Cartan-type defect `ηT + Tη + T²` vanishes. -/
theorem torsion_flat_iff (η T : R) (h : η * η = 1) :
    (η + T) * (η + T) = 1 ↔ η * T + T * η + T * T = 0 := by
  rw [torsion_defect _ _ h]
  constructor
  · intro hh
    have h2 : (1 : R) + (η * T + T * η + T * T) = 1 + 0 := by rw [hh]; simp
    exact (add_left_cancel_iff.mp h2)
  · intro hh
    rw [hh, add_zero]

/-- Fluctuated edge operators miss idempotence by EXACTLY the torsion defect
    (T1): `(E₊^T)² = E₊^T + (2⁻¹)² • (ηT + Tη + T²)`.
    This is Jeff's "torsion twist in the projection from the D_F," accounted
    to the scalar: perfection survives torsion iff the defect vanishes. -/
theorem edgePlus_torsion_defect (η T : R) (h : η * η = 1) :
    edgePlus (η + T) * edgePlus (η + T)
      = edgePlus (η + T)
        + ((2 : ℂ)⁻¹ * (2 : ℂ)⁻¹) • (η * T + T * η + T * T) := by
  -- Unnormalized engine: (1+η+T)² = 2(1+η+T) + (ηT + Tη + T²).
  have engine : (1 + (η + T)) * (1 + (η + T))
      = ((1 + (η + T)) + (1 + (η + T))) + (η * T + T * η + T * T) := by
    have expand : (1 + (η + T)) * (1 + (η + T))
        = 1 + (η + T + (η + T)) + (η + T) * (η + T) := by
      rw [add_mul, one_mul, mul_add, mul_one]; abel
    rw [expand, torsion_defect _ _ h]; abel
  unfold edgePlus
  rw [smul_mul_smul', engine]
  exact torsion_scalar _ _

-- ============================================================================
-- ============================================================================
-- §4. Signature non-emergence (honest NO-GO for the strong claim)
--
-- Worked on `ℂ × ℂ` (commutative ℂ-algebra, clean Prod simp lemmas):
-- two fundamental symmetries, both squaring to 1, with different edge data.
-- ============================================================================

/-- First fundamental symmetry on `ℂ × ℂ`: `(1,1)` — signature `(2,0)`. -/
noncomputable def sigA : ℂ × ℂ := (1, 1)

/-- Second fundamental symmetry on `ℂ × ℂ`: `(1,−1)` — signature `(1,1)`. -/
noncomputable def sigB : ℂ × ℂ := (1, -1)

theorem sigA_sq : sigA * sigA = 1 := by
  ext <;> simp [sigA]

theorem sigB_sq : sigB * sigB = 1 := by
  ext <;> simp [sigB]

/-- On `(1,1)`, the minus-edge vanishes: signature `(2,0)`. -/
theorem edgeMinus_sigA : edgeMinus sigA = 0 := by
  have hsig : sigA = (1 : ℂ × ℂ) := rfl
  rw [hsig]
  unfold edgeMinus
  rw [sub_self, smul_zero]

/-- Second component of the minus-edge on `(1,−1)`:
    `(2⁻¹) • (1 − (−1)) = (2⁻¹)·2 = 1`. -/
theorem edgeMinus_sigB_snd : (edgeMinus sigB).2 = 1 := by
  have hsub : ((1 : ℂ × ℂ) - sigB).2 = 2 := by
    have h1 : ((1 : ℂ × ℂ) - sigB).2 = (1 : ℂ) - (-1 : ℂ) := rfl
    rw [h1]; norm_num
  have hsmul : (edgeMinus sigB).2 = (2 : ℂ)⁻¹ • (((1 : ℂ × ℂ) - sigB).2) := rfl
  rw [hsmul, hsub, smul_eq_mul, inv_two_mul_two]

/-- On `(1,−1)`, the minus-edge does NOT vanish: signature `(1,1)` ≠ `(2,0)`. -/
theorem edgeMinus_sigB_ne : edgeMinus sigB ≠ 0 := by
  intro hcon
  have h2 : (edgeMinus sigB).2 = ((0 : ℂ × ℂ)).2 := by rw [hcon]
  rw [edgeMinus_sigB_snd] at h2
  have h0 : ((0 : ℂ × ℂ)).2 = (0:ℂ) := rfl
  rw [h0] at h2
  norm_num at h2

/-- NO-GO, sharp (T1): `η² = 1` does NOT determine the signature.
    Both `sigA` and `sigB` square to 1, but one's minus-edge vanishes and the
    other's does not. The 3+1 numbers are EXTRA data — the strong emergence
    claim is dead; the edge-pair ⟺ symmetry mechanism (§1) stands. -/
theorem signature_not_determined :
    edgeMinus sigA = 0 ∧ edgeMinus sigB ≠ 0 :=
  ⟨edgeMinus_sigA, edgeMinus_sigB_ne⟩

#print axioms edgePlus_idem
#print axioms edgeMinus_idem
#print axioms edge_orth_lr
#print axioms edge_compl
#print axioms edge_recover
#print axioms edgePair_of_symm
#print axioms symm_of_edgePair
#print axioms edgePlusPair_diag_flip
#print axioms edgeMinusPair_diag_flip
#print axioms torsion_defect
#print axioms torsion_flat_iff
#print axioms edgePlus_torsion_defect
#print axioms signature_not_determined

end ThetLogos
