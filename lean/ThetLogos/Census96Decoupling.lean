import ThetLogos.Census96
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# ThetLogos.Census96Decoupling — C96-1: block decoupling + the 2352 discharge

Second half of the Census-96 interface (pack `pack-c96-1.md`; scoping
`scoping-census96-2026-10-30.md` §3 row C96-1). C96-0's names in
`ThetLogos.Census96` are FROZEN and untouched; every name defined here is
new and freezes at this landing.

## Content

1. `genBlock_doubleCommutator`: the `(g, g')` block of the 96-dimensional
   double commutator `[[D, smGen3 a], smGenOp3 b]` is the one-generation
   double commutator of the block `genBlock D g g'` alone.
2. `orderOneHolds₃_iff_blocks`: decoupling —
   `OrderOneHolds₃ D ↔ ∀ g g', OrderOneHolds (genBlock D g g')`.
3. Solution-space decomposition: `Census96Sol` is ℝ-linearly equivalent
   to `(Fin 3 → Sol32) × (GenPair → Census96PairSol)`, where
   `GenPair` is the type of unordered generation pairs `g < g'` (three of
   them) and `Census96PairSol` (the NAMED pair solution space) is the
   space of single off-diagonal blocks `M` such that the pair
   `(M, M†)` — `M†` is the self-adjoint partner block — has both members
   block-admissible (`IsAdmBlock`) and both satisfying the one-generation
   order-one condition. This is the pair condition extracted from
   `attack4_3gen.py` (commit `90a80e7`, Step 2): an off-diagonal block is
   a `γ_F`-odd block satisfying the entrywise-conj J-condition
   `UJ * conj(M) = M * UJ` (the Python's 512-real-dimensional pattern
   space `272 + 240`: a hermitian J-compatible part `H₊` and
   `Complex.I • H₋` with `H₋` hermitian J-ANTI-compatible); the partner
   block is forced to be its conjugate-transpose by self-adjointness of
   the whole, and the order-one condition is imposed on the block (the
   partner's condition is the `(g', g)` instance of the decoupling).
4. The `Adm96Dim` discharge: `adm96Dim_proved : Adm96Dim`, i.e.
   `finrank ℝ Adm96 = 2352 = 3 * 272 + 3 * 512`, from the
   parameterization: `finrank_adm32` (272, via the symmetric
   `16 × 16` complex cross-block: J-compatibility in the folded
   coordinates `a i = i.val % 16` is exactly symmetry, giving
   `136 = 16 * 17 / 2` complex coordinates) and `finrank_admBlock`
   (512, a free `16 × 16` complex cross-block), assembled over the
   three diagonal blocks and the three unordered pairs by
   `adm96Equiv`. The bases/coordinate equivalences ARE the argument;
   no machine rank computation is used.

## Fences

K-C96-2 guard: nothing here is the census. The 46/88 finranks are
C96-2/C96-3 targets, NOT proved here; `Census96PairSol` is raw material
for the 88, its finrank is not computed here. Generations imposed;
Q3 open; NO CLAIM; Dial 1 unmoved.
-/

open Matrix

namespace ThetLogos

/-! ## §1. Folded coordinates and grading signs

`acoord i = i.val % 16` folds the four 8-sectors onto `Fin 16`: the
partner map preserves it, and the grading sign flips under `partner`.
In folded coordinates the `(plus, minus)` cross-block of a matrix is a
plain `16 × 16` matrix. -/

/-- The grading sign of an index, as a complex number: `gammaF i i`. -/
def gSign (i : I32) : ℂ := gammaF i i

theorem gSign_apply (i : I32) :
    gSign i = if i.val < 8 then (1 : ℂ)
      else if i.val < 16 then -1
      else if i.val < 24 then -1 else 1 := by
  unfold gSign gammaF; simp

theorem gSign_eq_one_or_neg_one (i : I32) : gSign i = 1 ∨ gSign i = -1 := by
  rw [gSign_apply]
  split_ifs <;> simp

/-- Folded coordinate of a 32-index: `i.val % 16`. -/
def acoord (i : I32) : Fin 16 := ⟨i.val % 16, by have h := i.isLt; omega⟩

theorem acoord_val (i : I32) : (acoord i).val = i.val % 16 := rfl

/-- The half-swap on `Fin 16`: `a ↦ a + 8` if `a < 8`, else `a - 8`. -/
def flip8 (a : Fin 16) : Fin 16 :=
  if h : a.val < 8 then ⟨a.val + 8, by omega⟩ else ⟨a.val - 8, by omega⟩

theorem flip8_val (a : Fin 16) :
    (flip8 a).val = if a.val < 8 then a.val + 8 else a.val - 8 := by
  unfold flip8; split_ifs <;> simp_all

theorem flip8_flip8 (a : Fin 16) : flip8 (flip8 a) = a := by
  apply Fin.ext
  rw [flip8_val, flip8_val]
  split_ifs with h1 h2 h3 <;> omega

/-- The plus-sector embedding: `a ↦ a` for `a < 8`, `a ↦ a + 16` else.
    Its image is exactly the `+1` grading sector (indices `0–7, 24–31`). -/
def plusEmb (a : Fin 16) : I32 :=
  if h : a.val < 8 then ⟨a.val, by omega⟩ else ⟨a.val + 16, by omega⟩

/-- The minus-sector embedding: `a ↦ a + 8`. Its image is exactly the
    `-1` grading sector (indices `8–23`). -/
def minusEmb (a : Fin 16) : I32 := ⟨a.val + 8, by omega⟩

theorem plusEmb_val (a : Fin 16) :
    (plusEmb a).val = if a.val < 8 then a.val else a.val + 16 := by
  unfold plusEmb; split_ifs <;> simp_all

theorem minusEmb_val (a : Fin 16) : (minusEmb a).val = a.val + 8 := rfl

theorem gSign_plusEmb (a : Fin 16) : gSign (plusEmb a) = 1 := by
  rw [gSign_apply, plusEmb_val]
  split_ifs with h1 h2 h3 h4 <;> simp_all <;> omega

theorem gSign_minusEmb (a : Fin 16) : gSign (minusEmb a) = -1 := by
  rw [gSign_apply, minusEmb_val]
  have h := a.isLt
  split_ifs with h1 h2 h3 <;> simp_all <;> omega

theorem acoord_plusEmb (a : Fin 16) : acoord (plusEmb a) = a := by
  apply Fin.ext
  rw [acoord_val, plusEmb_val]
  split_ifs with h <;> simp [h] <;> omega

theorem acoord_minusEmb (a : Fin 16) : acoord (minusEmb a) = flip8 a := by
  apply Fin.ext
  rw [acoord_val, minusEmb_val, flip8_val]
  split_ifs with h <;> omega

theorem acoord_partner (i : I32) : acoord (partner i) = acoord i := by
  apply Fin.ext
  rw [acoord_val, acoord_val, partner_val_eq]
  split_ifs with h <;> omega

theorem gSign_partner (i : I32) : gSign (partner i) = - gSign i := by
  rw [gSign_apply, gSign_apply, partner_val_eq]
  have h := i.isLt
  split_ifs with h1 h2 h3 h4 h5 h6 h7 <;> simp_all <;> omega

theorem gSign_eq_one_ranges {i : I32} (hi : gSign i = 1) :
    i.val < 8 ∨ 24 ≤ i.val := by
  by_cases h1 : i.val < 8
  · exact Or.inl h1
  · by_cases h2 : i.val < 16
    · exfalso
      have hg : gSign i = -1 := by rw [gSign_apply, if_neg h1, if_pos h2]
      rw [hg] at hi; norm_num at hi
    · by_cases h3 : i.val < 24
      · exfalso
        have hg : gSign i = -1 := by rw [gSign_apply, if_neg h1, if_neg h2, if_pos h3]
        rw [hg] at hi; norm_num at hi
      · exact Or.inr (by omega)

theorem gSign_eq_neg_one_ranges {i : I32} (hi : gSign i = -1) :
    8 ≤ i.val ∧ i.val < 24 := by
  by_cases h1 : i.val < 8
  · exfalso
    have hg : gSign i = 1 := by rw [gSign_apply, if_pos h1]
    rw [hg] at hi; norm_num at hi
  · by_cases h2 : i.val < 16
    · exact ⟨by omega, by omega⟩
    · by_cases h3 : i.val < 24
      · exact ⟨by omega, by omega⟩
      · exfalso
        have hg : gSign i = 1 := by
          rw [gSign_apply, if_neg h1, if_neg h2, if_neg h3]
        rw [hg] at hi; norm_num at hi

/-- A plus-sector index is recovered from its folded coordinate. -/
theorem plusEmb_acoord_of_gSign_eq_one {i : I32} (hi : gSign i = 1) :
    plusEmb (acoord i) = i := by
  apply Fin.ext
  rw [plusEmb_val, acoord_val]
  rcases gSign_eq_one_ranges hi with h | h
  · have hm : i.val % 16 = i.val := Nat.mod_eq_of_lt (by omega)
    rw [hm, if_pos h]
  · have hm : i.val % 16 = i.val - 16 := by omega
    rw [hm, if_neg (by omega : ¬ i.val - 16 < 8)]
    omega

/-- A minus-sector index is recovered from its folded coordinate via
    `minusEmb ∘ flip8`. -/
theorem minusEmb_flip8_acoord_of_gSign_eq_neg_one {i : I32} (hi : gSign i = -1) :
    minusEmb (flip8 (acoord i)) = i := by
  apply Fin.ext
  show (minusEmb (flip8 (acoord i))).val = i.val
  rw [minusEmb_val, flip8_val, acoord_val]
  obtain ⟨hlo, hhi⟩ := gSign_eq_neg_one_ranges hi
  by_cases h16 : i.val < 16
  · have hm : i.val % 16 = i.val := Nat.mod_eq_of_lt (by omega)
    rw [hm, if_neg (by omega : ¬ i.val < 8)]
    omega
  · have hm : i.val % 16 = i.val - 16 := by omega
    rw [hm, if_pos (by omega : i.val - 16 < 8)]
    omega

/-! ## §2. `UJ` as a permutation, entrywise -/

theorem UJ_mul_apply (N : Matrix I32 I32 ℂ) (i j : I32) :
    (UJ * N) i j = N (partner i) j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (partner i)]
  · rw [show UJ i (partner i) = 1 from by
      rw [UJ_apply]; unfold UJ_matrix; exact ite_eq_left rfl, one_mul]
  · intro b _ hb
    have h0 : UJ i b = 0 := by
      rw [UJ_apply]; unfold UJ_matrix; exact ite_eq_right hb
    rw [h0, zero_mul]
  · intro hcon; exact absurd (Finset.mem_univ _) hcon

theorem mul_UJ_apply (N : Matrix I32 I32 ℂ) (i j : I32) :
    (N * UJ) i j = N i (partner j) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (partner j)]
  · rw [show UJ (partner j) j = 1 from by
      rw [UJ_apply]; unfold UJ_matrix
      exact ite_eq_left (partner_involutive j).symm, mul_one]
  · intro b _ hb
    have hb2 : j ≠ partner b := by
      intro hcon
      apply hb
      have hpb : partner j = b := by rw [hcon, partner_involutive]
      exact hpb.symm
    have h0 : UJ b j = 0 := by
      rw [UJ_apply]; unfold UJ_matrix; exact ite_eq_right hb2
    rw [h0, mul_zero]
  · intro hcon; exact absurd (Finset.mem_univ _) hcon

/-- `UJ3` conjugation permutes entries by `partner` inside each
    generation block. -/
theorem UJ3_conj_apply (N : Matrix I96 I96 ℂ) (i : I32) (g : Fin 3) (j : I32) (gp : Fin 3) :
    (UJ3 * N * UJ3) (i, g) (j, gp) = N (partner i, g) (partner j, gp) := by
  have hzero : ∀ (a : I32) (c : Fin 3) (b : I32) (d : Fin 3),
      ¬(b = partner a ∧ c = d) → UJ3 (a, c) (b, d) = 0 := by
    intro a c b d h
    unfold UJ3 UJ UJ_matrix
    by_cases hc : c = d
    · have hb : b ≠ partner a := fun hb => h ⟨hb, hc⟩
      simp [hc, hb]
    · simp [hc]
  have hone : ∀ (a : I32) (c : Fin 3), UJ3 (a, c) (partner a, c) = 1 := by
    intro a c
    unfold UJ3 UJ UJ_matrix
    simp
  have hone' : ∀ (a : I32) (c : Fin 3), UJ3 (partner a, c) (a, c) = 1 := by
    intro a c
    unfold UJ3 UJ UJ_matrix
    simp [partner_involutive]
  rw [Matrix.mul_apply, Finset.sum_eq_single (partner j, gp)]
  · rw [Matrix.mul_apply, Finset.sum_eq_single (partner i, g)]
    · rw [hone i g, hone' j gp, one_mul, mul_one]
    · intro b _ hb
      obtain ⟨k, c⟩ := b
      have hne : ¬(k = partner i ∧ g = c) := by
        rintro ⟨rfl, rfl⟩; exact hb rfl
      rw [hzero i g k c hne, zero_mul]
    · intro hcon; exact absurd (Finset.mem_univ _) hcon
  · intro b _ hb
    obtain ⟨k, c⟩ := b
    have hne : ¬(j = partner k ∧ c = gp) := by
      rintro ⟨hjk, rfl⟩
      apply hb
      have : partner k = j := hjk.symm
      have hk : k = partner j := by
        calc k = partner (partner k) := (partner_involutive k).symm
          _ = partner j := by rw [this]
      simp [hk]
    rw [hzero k c j gp hne, mul_zero]
  · intro hcon; exact absurd (Finset.mem_univ _) hcon

end ThetLogos

namespace ThetLogos

/-! ## §3. The block double-commutator formula and decoupling -/

theorem genBlock_apply (D : Matrix I96 I96 ℂ) (g gp : Fin 3) (i j : I32) :
    genBlock D g gp i j = D (i, g) (j, gp) := rfl

theorem genBlock_add (X Y : Matrix I96 I96 ℂ) (g gp : Fin 3) :
    genBlock (X + Y) g gp = genBlock X g gp + genBlock Y g gp := rfl

theorem genBlock_sub (X Y : Matrix I96 I96 ℂ) (g gp : Fin 3) :
    genBlock (X - Y) g gp = genBlock X g gp - genBlock Y g gp := rfl

/-- Right multiplication by a triplicated generator is blockwise. -/
theorem genBlock_mul_smGen3 (X : Matrix I96 I96 ℂ) (a : Fin 12) (g gp : Fin 3) :
    genBlock (X * smGen3 a) g gp = genBlock X g gp * smGen a := by
  ext i j
  show (X * smGen3 a) (i, g) (j, gp) = (genBlock X g gp * smGen a) i j
  rw [Matrix.mul_apply, Matrix.mul_apply, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_eq_single gp]
  · show X (i, g) (k, gp) * (smGen a k j * if gp = gp then (1 : ℂ) else 0)
      = genBlock X g gp i k * smGen a k j
    rw [if_pos rfl, mul_one, genBlock_apply]
  · intro c _ hc
    show X (i, g) (k, c) * (smGen a k j * if c = gp then (1 : ℂ) else 0) = 0
    rw [if_neg hc, mul_zero, mul_zero]
  · intro hcon; exact absurd (Finset.mem_univ _) hcon

theorem genBlock_mul_smGenOp3 (X : Matrix I96 I96 ℂ) (a : Fin 12) (g gp : Fin 3) :
    genBlock (X * smGenOp3 a) g gp = genBlock X g gp * smGenOp a := by
  ext i j
  show (X * smGenOp3 a) (i, g) (j, gp) = (genBlock X g gp * smGenOp a) i j
  rw [Matrix.mul_apply, Matrix.mul_apply, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_eq_single gp]
  · show X (i, g) (k, gp) * (smGenOp a k j * if gp = gp then (1 : ℂ) else 0)
      = genBlock X g gp i k * smGenOp a k j
    rw [if_pos rfl, mul_one, genBlock_apply]
  · intro c _ hc
    show X (i, g) (k, c) * (smGenOp a k j * if c = gp then (1 : ℂ) else 0) = 0
    rw [if_neg hc, mul_zero, mul_zero]
  · intro hcon; exact absurd (Finset.mem_univ _) hcon

/-- Left multiplication by a triplicated generator is blockwise. -/
theorem smGen3_mul_genBlock (X : Matrix I96 I96 ℂ) (a : Fin 12) (g gp : Fin 3) :
    genBlock (smGen3 a * X) g gp = smGen a * genBlock X g gp := by
  ext i j
  show (smGen3 a * X) (i, g) (j, gp) = (smGen a * genBlock X g gp) i j
  rw [Matrix.mul_apply, Matrix.mul_apply, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_eq_single g]
  · show (smGen a i k * if g = g then (1 : ℂ) else 0) * X (k, g) (j, gp)
      = smGen a i k * genBlock X g gp k j
    rw [if_pos rfl, mul_one, genBlock_apply]
  · intro c _ hc
    show (smGen a i k * if g = c then (1 : ℂ) else 0) * X (k, c) (j, gp) = 0
    rw [if_neg (fun h => hc h.symm), mul_zero, zero_mul]
  · intro hcon; exact absurd (Finset.mem_univ _) hcon

theorem smGenOp3_mul_genBlock (X : Matrix I96 I96 ℂ) (a : Fin 12) (g gp : Fin 3) :
    genBlock (smGenOp3 a * X) g gp = smGenOp a * genBlock X g gp := by
  ext i j
  show (smGenOp3 a * X) (i, g) (j, gp) = (smGenOp a * genBlock X g gp) i j
  rw [Matrix.mul_apply, Matrix.mul_apply, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_eq_single g]
  · show (smGenOp a i k * if g = g then (1 : ℂ) else 0) * X (k, g) (j, gp)
      = smGenOp a i k * genBlock X g gp k j
    rw [if_pos rfl, mul_one, genBlock_apply]
  · intro c _ hc
    show (smGenOp a i k * if g = c then (1 : ℂ) else 0) * X (k, c) (j, gp) = 0
    rw [if_neg (fun h => hc h.symm), mul_zero, zero_mul]
  · intro hcon; exact absurd (Finset.mem_univ _) hcon

/-- **The block double-commutator formula (C96-1, item 1).** The
    `(g, g')` block of `[[D, smGen3 a], smGenOp3 b]` is the
    one-generation double commutator of the block `genBlock D g g'`
    alone, against `smGen a` / `smGenOp b`. -/
theorem genBlock_doubleCommutator (D : Matrix I96 I96 ℂ) (a b : Fin 12) (g gp : Fin 3) :
    genBlock ((D * smGen3 a - smGen3 a * D) * smGenOp3 b
      - smGenOp3 b * (D * smGen3 a - smGen3 a * D)) g gp
    = (genBlock D g gp * smGen a - smGen a * genBlock D g gp) * smGenOp b
      - smGenOp b * (genBlock D g gp * smGen a - smGen a * genBlock D g gp) := by
  rw [genBlock_sub, genBlock_mul_smGenOp3, smGenOp3_mul_genBlock,
    genBlock_sub, genBlock_mul_smGen3, smGen3_mul_genBlock]

/-- **Decoupling (C96-1, item 2).** The 96-dimensional order-one
    condition splits over the nine generation blocks, with no
    cross-block coupling. -/
theorem orderOneHolds₃_iff_blocks (D : Matrix I96 I96 ℂ) :
    OrderOneHolds₃ D ↔ ∀ g gp : Fin 3, OrderOneHolds (genBlock D g gp) := by
  constructor
  · intro h g gp a b
    have h0 := h a b
    have hb := congrArg (fun M : Matrix I96 I96 ℂ => genBlock M g gp) h0
    rw [genBlock_doubleCommutator] at hb
    have hz : genBlock (0 : Matrix I96 I96 ℂ) g gp = 0 := rfl
    rw [hz] at hb
    exact hb
  · intro h a b
    ext ⟨i, g⟩ ⟨j, gp⟩
    have hb := h g gp a b
    have he : ((D * smGen3 a - smGen3 a * D) * smGenOp3 b
        - smGenOp3 b * (D * smGen3 a - smGen3 a * D)) (i, g) (j, gp)
      = ((genBlock D g gp * smGen a - smGen a * genBlock D g gp) * smGenOp b
        - smGenOp b * (genBlock D g gp * smGen a - smGen a * genBlock D g gp)) i j := by
      have h2 := congrFun (congrFun (genBlock_doubleCommutator D a b g gp) i) j
      rwa [genBlock_apply] at h2
    rw [he, hb]
    rfl

end ThetLogos

namespace ThetLogos

/-! ## §4. The one-generation and block admissible submodules -/

/-- The one-generation admissible space as a real submodule
    (carrier `IsAdm32`, C96-0's predicate). -/
def Adm32 : Submodule ℝ (Matrix I32 I32 ℂ) where
  carrier := {D | IsAdm32 D}
  add_mem' := by
    intro D1 D2 h1 h2
    obtain ⟨s1, g1, j1⟩ := h1
    obtain ⟨s2, g2, j2⟩ := h2
    refine ⟨?_, ?_, ?_⟩
    · show (D1 + D2).conjTranspose = D1 + D2
      rw [Matrix.conjTranspose_add, s1, s2]
    · show gammaF * (D1 + D2) + (D1 + D2) * gammaF = 0
      rw [Matrix.mul_add, Matrix.add_mul]
      have h3 : (gammaF * D1 + gammaF * D2) + (D1 * gammaF + D2 * gammaF)
          = (gammaF * D1 + D1 * gammaF) + (gammaF * D2 + D2 * gammaF) := by ac_rfl
      rw [h3, g1, g2, add_zero]
    · show UJ * (D1 + D2).transpose * UJ = D1 + D2
      rw [Matrix.transpose_add, Matrix.mul_add, Matrix.add_mul, j1, j2]
  zero_mem' := by
    refine ⟨?_, ?_, ?_⟩
    · show (0 : Matrix I32 I32 ℂ).conjTranspose = 0; simp
    · show gammaF * (0 : Matrix I32 I32 ℂ) + (0 : Matrix I32 I32 ℂ) * gammaF = 0; simp
    · show UJ * (0 : Matrix I32 I32 ℂ).transpose * UJ = 0; simp
  smul_mem' := by
    intro c D hD
    obtain ⟨s, g, j⟩ := hD
    refine ⟨?_, ?_, ?_⟩
    · have hS : (c • D).conjTranspose = c • D.conjTranspose := by
        ext i j
        have e1 : ((c • D) j i) = c • (D j i) := rfl
        have e2 : ((c • D.conjTranspose) i j) = c • (D.conjTranspose i j) := rfl
        rw [Matrix.conjTranspose_apply, e1, census96_star_real_smul, e2,
          Matrix.conjTranspose_apply]
      show (c • D).conjTranspose = c • D
      rw [hS, s]
    · have hG : gammaF * (c • D) + (c • D) * gammaF
          = c • (gammaF * D + D * gammaF) := by
        rw [Matrix.mul_smul, Matrix.smul_mul, ← smul_add]
      show gammaF * (c • D) + (c • D) * gammaF = 0
      rw [hG, g, smul_zero]
    · have hJ : UJ * (c • D).transpose * UJ = c • (UJ * D.transpose * UJ) := by
        rw [Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul]
      show UJ * (c • D).transpose * UJ = c • D
      rw [hJ, j]

theorem entrywiseConj_add (M N : Matrix I32 I32 ℂ) :
    entrywiseConj (M + N) = entrywiseConj M + entrywiseConj N := by
  ext i j
  show star ((M + N) i j) = star (M i j) + star (N i j)
  rw [Matrix.add_apply, star_add]

theorem entrywiseConj_smul_real (c : ℝ) (M : Matrix I32 I32 ℂ) :
    entrywiseConj (c • M) = c • entrywiseConj M := by
  ext i j
  show star ((c • M) i j) = c • star (M i j)
  have e1 : ((c • M) i j) = c • (M i j) := rfl
  rw [e1, census96_star_real_smul]

/-- The block admissible space as a real submodule (carrier
    `IsAdmBlock`, C96-0's Python-form predicate). -/
def AdmBlock : Submodule ℝ (Matrix I32 I32 ℂ) where
  carrier := {M | IsAdmBlock M}
  add_mem' := by
    intro M N hM hN
    obtain ⟨gM, jM⟩ := hM
    obtain ⟨gN, jN⟩ := hN
    refine ⟨?_, ?_⟩
    · show gammaF * (M + N) + (M + N) * gammaF = 0
      rw [Matrix.mul_add, Matrix.add_mul]
      have h3 : (gammaF * M + gammaF * N) + (M * gammaF + N * gammaF)
          = (gammaF * M + M * gammaF) + (gammaF * N + N * gammaF) := by ac_rfl
      rw [h3, gM, gN, add_zero]
    · show UJ * entrywiseConj (M + N) = (M + N) * UJ
      rw [entrywiseConj_add, Matrix.mul_add, Matrix.add_mul, jM, jN]
  zero_mem' := by
    refine ⟨?_, ?_⟩
    · show gammaF * (0 : Matrix I32 I32 ℂ) + (0 : Matrix I32 I32 ℂ) * gammaF = 0; simp
    · show UJ * entrywiseConj (0 : Matrix I32 I32 ℂ) = (0 : Matrix I32 I32 ℂ) * UJ
      ext i j
      rw [UJ_mul_apply]
      simp [entrywiseConj]
  smul_mem' := by
    intro c M hM
    obtain ⟨g, j⟩ := hM
    refine ⟨?_, ?_⟩
    · have hG : gammaF * (c • M) + (c • M) * gammaF
          = c • (gammaF * M + M * gammaF) := by
        rw [Matrix.mul_smul, Matrix.smul_mul, ← smul_add]
      show gammaF * (c • M) + (c • M) * gammaF = 0
      rw [hG, g, smul_zero]
    · show UJ * entrywiseConj (c • M) = (c • M) * UJ
      rw [entrywiseConj_smul_real, Matrix.mul_smul, Matrix.smul_mul, j]

/-! ## §5. Entry lemmas for the admissible conditions -/

theorem gammaOdd_entry (M : Matrix I32 I32 ℂ)
    (h : gammaF * M + M * gammaF = 0) (i j : I32) :
    gSign i * M i j + M i j * gSign j = 0 := by
  have he := congrFun (congrFun h i) j
  rw [Matrix.add_apply, Matrix.zero_apply, gammaF_mul_apply, mul_gammaF_apply] at he
  exact he

theorem gammaOdd_entry_eq_zero_of_gSign_eq (M : Matrix I32 I32 ℂ)
    (h : gammaF * M + M * gammaF = 0) {i j : I32} (hij : gSign i = gSign j) :
    M i j = 0 := by
  have he := gammaOdd_entry M h i j
  rw [← hij, mul_comm (M i j) (gSign i), ← two_mul (gSign i * M i j)] at he
  have hne : (gSign i) ≠ 0 := by
    rcases gSign_eq_one_or_neg_one i with h1 | h1 <;> rw [h1] <;> norm_num
  have h2 : gSign i * M i j = 0 := by
    have h20 : (2 : ℂ) ≠ 0 := by norm_num
    exact (mul_eq_zero.mp he).resolve_left h20
  exact (mul_eq_zero.mp h2).resolve_left hne

theorem selfAdjoint_entry (D : Matrix I32 I32 ℂ) (h : D.conjTranspose = D) (i j : I32) :
    D i j = star (D j i) := by
  have he := congrFun (congrFun h i) j
  rw [Matrix.conjTranspose_apply] at he
  exact he.symm

/-- Self-adjointness entrywise at 96. -/
theorem selfAdjoint_entry96 (D : Matrix I96 I96 ℂ) (h : D.conjTranspose = D)
    (x y : I96) : D x y = star (D y x) := by
  have he := congrFun (congrFun h x) y
  rw [Matrix.conjTranspose_apply] at he
  exact he.symm

/-- The one-generation J-condition in entrywise form (local copy of
    `CFKernelRetarget.j_compat_entry`, which is outside this module's
    import tree). -/
theorem jCompat_entry_local (D : Matrix I32 I32 ℂ) (hJ : IsJCompatible D)
    (i j : I32) : D i j = D (partner j) (partner i) := by
  have he := congrFun (congrFun hJ i) j
  rw [UJ_conj_apply, Matrix.transpose_apply] at he
  exact he.symm

/-- The block J-condition in entrywise form: for a block-admissible
    `M`, `star (M (partner i) (partner j)) = M i j`. This is the
    Python's `UJ * conj(M) = M * UJ` read at `(i, partner j)`. -/
theorem admBlock_entry_star (M : Matrix I32 I32 ℂ) (hM : IsAdmBlock M) (i j : I32) :
    star (M (partner i) (partner j)) = M i j := by
  have hJ := hM.2
  have he := congrFun (congrFun hJ i) (partner j)
  rw [UJ_mul_apply, mul_UJ_apply, partner_involutive] at he
  have h1 : entrywiseConj M (partner i) (partner j) = star (M (partner i) (partner j)) := rfl
  rw [h1] at he
  exact he

end ThetLogos

namespace ThetLogos

/-! ## §6. The 272 lemma: `Adm32` via symmetric folded cross-blocks

In folded coordinates the cross-block `X u v = D (plusEmb u)
(minusEmb (flip8 v))` of an admissible `D` satisfies `X u v = X v u`
(J-compatibility, via `j_compat_entry`), so `Adm32` is parameterized
by the `136` upper-triangular complex coordinates of a symmetric
`16 × 16` matrix: `272 = 2 * 136` real dimensions. -/

/-- Upper-triangular coordinate indices for a `16 × 16` matrix. -/
abbrev Upper16 := {p : Fin 16 × Fin 16 // p.1 ≤ p.2}

theorem card_upper16 : Fintype.card Upper16 = 136 := by
  rw [Fintype.card_subtype, Finset.card_filter,
    ← Finset.univ_product_univ, Finset.sum_product]
  have hinner : ∀ u : Fin 16, (∑ v : Fin 16, if u ≤ v then 1 else 0) = 16 - u.val := by
    intro u
    rw [← Finset.card_filter]
    have hset : Finset.univ.filter (fun v : Fin 16 => u ≤ v) = Finset.Ici u := by
      ext v
      simp [Finset.mem_Ici]
    rw [hset, Fin.card_Ici]
  rw [Finset.sum_congr rfl (fun u _ => hinner u)]
  rw [Fin.sum_univ_eq_sum_range (fun i => 16 - i) 16]
  norm_num [Finset.sum_range_succ]

/-- The symmetric matrix assembled from upper-triangular coordinates. -/
def symMatOf (f : Upper16 → ℂ) : Matrix (Fin 16) (Fin 16) ℂ :=
  fun u v => if h : u ≤ v then f ⟨(u, v), h⟩ else f ⟨(v, u), le_of_not_ge h⟩

theorem symMatOf_apply_le (f : Upper16 → ℂ) {u v : Fin 16} (h : u ≤ v) :
    symMatOf f u v = f ⟨(u, v), h⟩ := by
  unfold symMatOf; rw [dif_pos h]

theorem symMatOf_symm (f : Upper16 → ℂ) (u v : Fin 16) :
    symMatOf f u v = symMatOf f v u := by
  unfold symMatOf
  by_cases h : u ≤ v
  · rw [dif_pos h]
    by_cases h2 : v ≤ u
    · have huv : u = v := le_antisymm h h2
      subst huv; rw [dif_pos le_rfl]
    · rw [dif_neg h2]
  · rw [dif_neg h, dif_pos (le_of_not_ge h)]

theorem symMatOf_apply_of_not_le (f : Upper16 → ℂ) {u v : Fin 16} (h : ¬ u ≤ v) :
    symMatOf f u v = f ⟨(v, u), le_of_not_ge h⟩ := by
  unfold symMatOf; rw [dif_neg h]

theorem symMatOf_add (f g : Upper16 → ℂ) :
    symMatOf (f + g) = symMatOf f + symMatOf g := by
  ext u v
  rw [Matrix.add_apply]
  by_cases h : u ≤ v
  · rw [symMatOf_apply_le _ h, symMatOf_apply_le f h, symMatOf_apply_le g h, Pi.add_apply]
  · rw [symMatOf_apply_of_not_le _ h, symMatOf_apply_of_not_le f h,
      symMatOf_apply_of_not_le g h, Pi.add_apply]

theorem symMatOf_smul_real (c : ℝ) (f : Upper16 → ℂ) :
    symMatOf (c • f) = c • symMatOf f := by
  ext u v
  rw [Matrix.smul_apply]
  by_cases h : u ≤ v
  · rw [symMatOf_apply_le _ h, symMatOf_apply_le f h, Pi.smul_apply]
  · rw [symMatOf_apply_of_not_le _ h, symMatOf_apply_of_not_le f h, Pi.smul_apply]

theorem neg_one_ne_one_complex : ¬ (-1 : ℂ) = 1 := by norm_num

theorem gSign_ne_one_of_eq_neg_one {i : I32} (h : gSign i = -1) : gSign i ≠ 1 := by
  rw [h]; exact neg_one_ne_one_complex

theorem gSign_partner_eq_one_of_eq_neg_one {i : I32} (h : gSign i = -1) :
    gSign (partner i) = 1 := by
  rw [gSign_partner, h]; norm_num

theorem gSign_partner_eq_neg_one_of_eq_one {i : I32} (h : gSign i = 1) :
    gSign (partner i) = -1 := by
  rw [gSign_partner, h]

/-- Assembly of a one-generation admissible matrix from symmetric
    folded coordinates: cross-blocks from `symMatOf`, the
    `(minus, plus)` block forced by self-adjointness, zero elsewhere. -/
noncomputable def adm32MatOf (f : Upper16 → ℂ) : Matrix I32 I32 ℂ := fun i j =>
  if gSign i = 1 then (if gSign j = 1 then 0 else symMatOf f (acoord i) (acoord j))
  else (if gSign j = 1 then star (symMatOf f (acoord j) (acoord i)) else 0)

theorem adm32MatOf_apply (f : Upper16 → ℂ) (i j : I32) :
    adm32MatOf f i j =
      if gSign i = 1 then (if gSign j = 1 then 0 else symMatOf f (acoord i) (acoord j))
      else (if gSign j = 1 then star (symMatOf f (acoord j) (acoord i)) else 0) := rfl

theorem adm32MatOf_isAdm32 (f : Upper16 → ℂ) : IsAdm32 (adm32MatOf f) := by
  refine ⟨?_, ?_, ?_⟩
  · -- self-adjoint
    ext i j
    rw [Matrix.conjTranspose_apply]
    show star (adm32MatOf f j i) = adm32MatOf f i j
    rcases gSign_eq_one_or_neg_one i with hi | hi <;>
      rcases gSign_eq_one_or_neg_one j with hj | hj
    · have e1 : adm32MatOf f j i = 0 := by
        simp only [adm32MatOf_apply, hj, hi, eq_self_iff_true, ite_true]
      have e2 : adm32MatOf f i j = 0 := by
        simp only [adm32MatOf_apply, hi, hj, eq_self_iff_true, ite_true]
      rw [e1, e2, star_zero]
    · have e1 : adm32MatOf f j i = star (symMatOf f (acoord i) (acoord j)) := by
        simp only [adm32MatOf_apply, hj, hi, eq_self_iff_true, neg_one_ne_one_complex,
          ite_true, ite_false]
      have e2 : adm32MatOf f i j = symMatOf f (acoord i) (acoord j) := by
        simp only [adm32MatOf_apply, hi, hj, eq_self_iff_true, neg_one_ne_one_complex,
          ite_true, ite_false]
      rw [e1, e2, star_star]
    · have e1 : adm32MatOf f j i = symMatOf f (acoord j) (acoord i) := by
        simp only [adm32MatOf_apply, hj, hi, eq_self_iff_true, neg_one_ne_one_complex,
          ite_true, ite_false]
      have e2 : adm32MatOf f i j = star (symMatOf f (acoord j) (acoord i)) := by
        simp only [adm32MatOf_apply, hi, hj, eq_self_iff_true, neg_one_ne_one_complex,
          ite_true, ite_false]
      rw [e1, e2]
    · have e1 : adm32MatOf f j i = 0 := by
        simp only [adm32MatOf_apply, hj, hi, neg_one_ne_one_complex, ite_false]
      have e2 : adm32MatOf f i j = 0 := by
        simp only [adm32MatOf_apply, hi, hj, neg_one_ne_one_complex, ite_false]
      rw [e1, e2, star_zero]
  · -- grading-odd
    ext i j
    rw [Matrix.add_apply, Matrix.zero_apply, gammaF_mul_apply, mul_gammaF_apply]
    show gSign i * adm32MatOf f i j + adm32MatOf f i j * gSign j = 0
    rcases gSign_eq_one_or_neg_one i with hi | hi <;>
      rcases gSign_eq_one_or_neg_one j with hj | hj
    · have e : adm32MatOf f i j = 0 := by
        simp only [adm32MatOf_apply, hi, hj, eq_self_iff_true, ite_true]
      rw [e]; simp
    · have e : adm32MatOf f i j = symMatOf f (acoord i) (acoord j) := by
        simp only [adm32MatOf_apply, hi, hj, eq_self_iff_true, neg_one_ne_one_complex,
          ite_true, ite_false]
      rw [e, hi, hj, one_mul, mul_neg, mul_one, add_neg_cancel]
    · have e : adm32MatOf f i j = star (symMatOf f (acoord j) (acoord i)) := by
        simp only [adm32MatOf_apply, hi, hj, eq_self_iff_true, neg_one_ne_one_complex,
          ite_true, ite_false]
      rw [e, hi, hj, neg_mul, one_mul, mul_one, neg_add_cancel]
    · have e : adm32MatOf f i j = 0 := by
        simp only [adm32MatOf_apply, hi, hj, neg_one_ne_one_complex, ite_false]
      rw [e]; simp
  · -- J-compatible (transpose form)
    show UJ * (adm32MatOf f).transpose * UJ = adm32MatOf f
    ext i j
    rw [UJ_conj_apply, Matrix.transpose_apply]
    show adm32MatOf f (partner j) (partner i) = adm32MatOf f i j
    rcases gSign_eq_one_or_neg_one i with hi | hi <;>
      rcases gSign_eq_one_or_neg_one j with hj | hj
    · have hpj := gSign_partner_eq_neg_one_of_eq_one hj
      have hpi := gSign_partner_eq_neg_one_of_eq_one hi
      have e1 : adm32MatOf f (partner j) (partner i) = 0 := by
        simp only [adm32MatOf_apply, hpj, hpi, neg_one_ne_one_complex, ite_false]
      have e2 : adm32MatOf f i j = 0 := by
        simp only [adm32MatOf_apply, hi, hj, eq_self_iff_true, ite_true]
      rw [e1, e2]
    · have hpj := gSign_partner_eq_one_of_eq_neg_one hj
      have hpi := gSign_partner_eq_neg_one_of_eq_one hi
      have e1 : adm32MatOf f (partner j) (partner i)
          = symMatOf f (acoord j) (acoord i) := by
        simp only [adm32MatOf_apply, hpj, hpi, eq_self_iff_true, neg_one_ne_one_complex,
          ite_true, ite_false, acoord_partner]
      have e2 : adm32MatOf f i j = symMatOf f (acoord i) (acoord j) := by
        simp only [adm32MatOf_apply, hi, hj, eq_self_iff_true, neg_one_ne_one_complex,
          ite_true, ite_false]
      rw [e1, e2, symMatOf_symm]
    · have hpj := gSign_partner_eq_neg_one_of_eq_one hj
      have hpi := gSign_partner_eq_one_of_eq_neg_one hi
      have e1 : adm32MatOf f (partner j) (partner i)
          = star (symMatOf f (acoord i) (acoord j)) := by
        simp only [adm32MatOf_apply, hpj, hpi, eq_self_iff_true, neg_one_ne_one_complex,
          ite_true, ite_false, acoord_partner]
      have e2 : adm32MatOf f i j = star (symMatOf f (acoord j) (acoord i)) := by
        simp only [adm32MatOf_apply, hi, hj, eq_self_iff_true, neg_one_ne_one_complex,
          ite_true, ite_false]
      rw [e1, e2, symMatOf_symm]
    · have hpj := gSign_partner_eq_one_of_eq_neg_one hj
      have hpi := gSign_partner_eq_one_of_eq_neg_one hi
      have e1 : adm32MatOf f (partner j) (partner i) = 0 := by
        simp only [adm32MatOf_apply, hpj, hpi, eq_self_iff_true, ite_true]
      have e2 : adm32MatOf f i j = 0 := by
        simp only [adm32MatOf_apply, hi, hj, neg_one_ne_one_complex, ite_false]
      rw [e1, e2]

theorem adm32MatOf_add (f g : Upper16 → ℂ) :
    adm32MatOf (f + g) = adm32MatOf f + adm32MatOf g := by
  ext i j
  rw [Matrix.add_apply]
  rcases gSign_eq_one_or_neg_one i with hi | hi <;>
    rcases gSign_eq_one_or_neg_one j with hj | hj
  · have e : ∀ F : Upper16 → ℂ, adm32MatOf F i j = 0 := by
      intro F
      simp only [adm32MatOf_apply, hi, hj, eq_self_iff_true, ite_true]
    rw [e, e, e]; simp
  · have e : ∀ F : Upper16 → ℂ, adm32MatOf F i j = symMatOf F (acoord i) (acoord j) := by
      intro F
      simp only [adm32MatOf_apply, hi, hj, eq_self_iff_true, neg_one_ne_one_complex,
        ite_true, ite_false]
    rw [e, e, e, symMatOf_add, Matrix.add_apply]
  · have e : ∀ F : Upper16 → ℂ, adm32MatOf F i j
        = star (symMatOf F (acoord j) (acoord i)) := by
      intro F
      simp only [adm32MatOf_apply, hi, hj, eq_self_iff_true, neg_one_ne_one_complex,
        ite_true, ite_false]
    rw [e, e, e, symMatOf_add, Matrix.add_apply, star_add]
  · have e : ∀ F : Upper16 → ℂ, adm32MatOf F i j = 0 := by
      intro F
      simp only [adm32MatOf_apply, hi, hj, neg_one_ne_one_complex, ite_false]
    rw [e, e, e]; simp

theorem adm32MatOf_smul_real (c : ℝ) (f : Upper16 → ℂ) :
    adm32MatOf (c • f) = c • adm32MatOf f := by
  ext i j
  rw [Matrix.smul_apply]
  rcases gSign_eq_one_or_neg_one i with hi | hi <;>
    rcases gSign_eq_one_or_neg_one j with hj | hj
  · have e : ∀ F : Upper16 → ℂ, adm32MatOf F i j = 0 := by
      intro F
      simp only [adm32MatOf_apply, hi, hj, eq_self_iff_true, ite_true]
    rw [e, e]; simp
  · have e : ∀ F : Upper16 → ℂ, adm32MatOf F i j = symMatOf F (acoord i) (acoord j) := by
      intro F
      simp only [adm32MatOf_apply, hi, hj, eq_self_iff_true, neg_one_ne_one_complex,
        ite_true, ite_false]
    rw [e, e, symMatOf_smul_real, Matrix.smul_apply]
  · have e : ∀ F : Upper16 → ℂ, adm32MatOf F i j
        = star (symMatOf F (acoord j) (acoord i)) := by
      intro F
      simp only [adm32MatOf_apply, hi, hj, eq_self_iff_true, neg_one_ne_one_complex,
        ite_true, ite_false]
    rw [e, e, symMatOf_smul_real]
    show star ((c • symMatOf f) (acoord j) (acoord i))
      = c • star (symMatOf f (acoord j) (acoord i))
    have e1 : ((c • symMatOf f) (acoord j) (acoord i))
        = c • (symMatOf f (acoord j) (acoord i)) := rfl
    rw [e1, census96_star_real_smul]
  · have e : ∀ F : Upper16 → ℂ, adm32MatOf F i j = 0 := by
      intro F
      simp only [adm32MatOf_apply, hi, hj, neg_one_ne_one_complex, ite_false]
    rw [e, e]; simp

/-- A minus-sector index's partner is recovered from its folded
    coordinate by `plusEmb`. -/
theorem plusEmb_acoord_eq_partner_of_gSign_eq_neg_one {i : I32} (hi : gSign i = -1) :
    plusEmb (acoord i) = partner i := by
  have h := plusEmb_acoord_of_gSign_eq_one (gSign_partner_eq_one_of_eq_neg_one hi)
  rwa [acoord_partner] at h

/-- A plus-sector index's partner is recovered from its folded
    coordinate by `minusEmb ∘ flip8`. -/
theorem minusEmb_flip8_acoord_eq_partner_of_gSign_eq_one {i : I32} (hi : gSign i = 1) :
    minusEmb (flip8 (acoord i)) = partner i := by
  have h := minusEmb_flip8_acoord_of_gSign_eq_neg_one
    (gSign_partner_eq_neg_one_of_eq_one hi)
  rwa [acoord_partner] at h

/-- Folded cross-block coordinates of a `32 × 32` matrix. -/
def crossCoordOf (D : Matrix I32 I32 ℂ) (u v : Fin 16) : ℂ :=
  D (plusEmb u) (minusEmb (flip8 v))

theorem symMatOf_crossCoordOf (D : Matrix I32 I32 ℂ) (hJ : IsJCompatible D) (u v : Fin 16) :
    symMatOf (fun p : Upper16 => crossCoordOf D p.1.1 p.1.2) u v = crossCoordOf D u v := by
  unfold symMatOf
  by_cases h : u ≤ v
  · rw [dif_pos h]
  · rw [dif_neg h]
    show crossCoordOf D v u = crossCoordOf D u v
    unfold crossCoordOf
    have h1 : D (plusEmb u) (minusEmb (flip8 v))
        = D (partner (minusEmb (flip8 v))) (partner (plusEmb u)) :=
      jCompat_entry_local D hJ _ _
    have h2 : partner (minusEmb (flip8 v)) = plusEmb v := by
      have hs : gSign (minusEmb (flip8 v)) = -1 := gSign_minusEmb _
      have h3 := plusEmb_acoord_eq_partner_of_gSign_eq_neg_one hs
      rw [acoord_minusEmb, flip8_flip8] at h3
      exact h3.symm
    have h3 : partner (plusEmb u) = minusEmb (flip8 u) := by
      have hs : gSign (plusEmb u) = 1 := gSign_plusEmb _
      have h4 := minusEmb_flip8_acoord_eq_partner_of_gSign_eq_one hs
      rw [acoord_plusEmb] at h4
      exact h4.symm
    rw [h2, h3] at h1
    exact h1.symm

/-- The coordinate equivalence `Adm32 ≃ₗ[ℝ] (Upper16 → ℂ)`. -/
noncomputable def adm32Equiv : Adm32 ≃ₗ[ℝ] (Upper16 → ℂ) :=
  LinearEquiv.ofBijective
    { toFun := fun D p => crossCoordOf D.1 p.1.1 p.1.2
      map_add' := by
        intro D1 D2
        funext p
        show crossCoordOf (D1 + D2).1 p.1.1 p.1.2
          = crossCoordOf D1.1 p.1.1 p.1.2 + crossCoordOf D2.1 p.1.1 p.1.2
        unfold crossCoordOf
        rfl
      map_smul' := by
        intro c D
        funext p
        show crossCoordOf (c • D).1 p.1.1 p.1.2 = c • crossCoordOf D.1 p.1.1 p.1.2
        unfold crossCoordOf
        rfl }
    (Function.bijective_iff_has_inverse.mpr
      ⟨fun f => ⟨adm32MatOf f, adm32MatOf_isAdm32 f⟩,
       fun D => by
         apply Subtype.ext
         show adm32MatOf (fun p : Upper16 => crossCoordOf D.1 p.1.1 p.1.2) = D.1
         obtain ⟨hsa, hgr, hj⟩ := D.2
         ext i j
         rcases gSign_eq_one_or_neg_one i with hi | hi <;>
           rcases gSign_eq_one_or_neg_one j with hj2 | hj2
         · have h0 : D.1 i j = 0 :=
             gammaOdd_entry_eq_zero_of_gSign_eq D.1 hgr (by rw [hi, hj2])
           show adm32MatOf _ i j = D.1 i j
           rw [h0]
           simp only [adm32MatOf_apply, hi, hj2, eq_self_iff_true, ite_true]
         · show adm32MatOf _ i j = D.1 i j
           have e1 : adm32MatOf (fun p : Upper16 => crossCoordOf D.1 p.1.1 p.1.2) i j
               = symMatOf (fun p : Upper16 => crossCoordOf D.1 p.1.1 p.1.2)
                   (acoord i) (acoord j) := by
             simp only [adm32MatOf_apply, hi, hj2, eq_self_iff_true,
               neg_one_ne_one_complex, ite_true, ite_false]
           rw [e1, symMatOf_crossCoordOf D.1 hj]
           unfold crossCoordOf
           rw [plusEmb_acoord_of_gSign_eq_one hi,
             minusEmb_flip8_acoord_of_gSign_eq_neg_one hj2]
         · show adm32MatOf _ i j = D.1 i j
           have e1 : adm32MatOf (fun p : Upper16 => crossCoordOf D.1 p.1.1 p.1.2) i j
               = star (symMatOf (fun p : Upper16 => crossCoordOf D.1 p.1.1 p.1.2)
                   (acoord j) (acoord i)) := by
             simp only [adm32MatOf_apply, hi, hj2, eq_self_iff_true,
               neg_one_ne_one_complex, ite_true, ite_false]
           rw [e1, symMatOf_crossCoordOf D.1 hj]
           unfold crossCoordOf
           rw [plusEmb_acoord_of_gSign_eq_one hj2,
             minusEmb_flip8_acoord_of_gSign_eq_neg_one hi]
           exact (selfAdjoint_entry D.1 hsa i j).symm
         · have h0 : D.1 i j = 0 :=
             gammaOdd_entry_eq_zero_of_gSign_eq D.1 hgr (by rw [hi, hj2])
           show adm32MatOf _ i j = D.1 i j
           rw [h0]
           simp only [adm32MatOf_apply, hi, hj2, neg_one_ne_one_complex, ite_false],
       fun f => by
         funext p
         show crossCoordOf (adm32MatOf f) p.1.1 p.1.2 = f p
         unfold crossCoordOf
         have e1 : adm32MatOf f (plusEmb p.1.1) (minusEmb (flip8 p.1.2))
             = symMatOf f p.1.1 p.1.2 := by
           have e := adm32MatOf_apply f (plusEmb p.1.1) (minusEmb (flip8 p.1.2))
           rwa [ite_eq_left (gSign_plusEmb _),
             ite_eq_right (gSign_ne_one_of_eq_neg_one (gSign_minusEmb _)),
             acoord_plusEmb, acoord_minusEmb, flip8_flip8] at e
         rw [e1, symMatOf_apply_le f p.2]⟩)

/-- **The one-generation 272 lemma.** `finrank ℝ Adm32 = 272`, by the
    symmetric folded cross-block parameterization (`136` complex
    upper-triangular coordinates). -/
theorem finrank_adm32 : Module.finrank ℝ Adm32 = 272 := by
  rw [adm32Equiv.finrank_eq, Module.finrank_pi_fintype]
  simp [Complex.finrank_real_complex, card_upper16]

end ThetLogos

namespace ThetLogos

/-! ## §7. The 512 lemma: `AdmBlock` via a free folded cross-block

A block-admissible `M` is determined by its folded cross-block
`Z u v = M (plusEmb u) (minusEmb (flip8 v))`, which is a FREE
`16 × 16` complex matrix (the `(minus, plus)` block is forced by the
entrywise-conj J-condition to be `star (Z (acoord i) (acoord j))` at
`(i, j)`): `512 = 2 * 256` real dimensions. In the Python's split this
free block is `H₊ + Complex.I • H₋` (272 + 240). -/

/-- Assembly of a block-admissible matrix from a free folded
    cross-block. -/
noncomputable def admBlockMatOf (Z : Fin 16 × Fin 16 → ℂ) : Matrix I32 I32 ℂ := fun i j =>
  if gSign i = 1 then (if gSign j = 1 then 0 else Z (acoord i, acoord j))
  else (if gSign j = 1 then star (Z (acoord i, acoord j)) else 0)

theorem admBlockMatOf_apply (Z : Fin 16 × Fin 16 → ℂ) (i j : I32) :
    admBlockMatOf Z i j =
      if gSign i = 1 then (if gSign j = 1 then 0 else Z (acoord i, acoord j))
      else (if gSign j = 1 then star (Z (acoord i, acoord j)) else 0) := rfl

theorem admBlockMatOf_isAdmBlock (Z : Fin 16 × Fin 16 → ℂ) :
    IsAdmBlock (admBlockMatOf Z) := by
  refine ⟨?_, ?_⟩
  · ext i j
    rw [Matrix.add_apply, Matrix.zero_apply, gammaF_mul_apply, mul_gammaF_apply]
    show gSign i * admBlockMatOf Z i j + admBlockMatOf Z i j * gSign j = 0
    rcases gSign_eq_one_or_neg_one i with hi | hi <;>
      rcases gSign_eq_one_or_neg_one j with hj | hj
    · have e : admBlockMatOf Z i j = 0 := by
        simp only [admBlockMatOf_apply, hi, hj, eq_self_iff_true, ite_true]
      rw [e]; simp
    · have e : admBlockMatOf Z i j = Z (acoord i, acoord j) := by
        simp only [admBlockMatOf_apply, hi, hj, eq_self_iff_true, neg_one_ne_one_complex,
          ite_true, ite_false]
      rw [e, hi, hj, one_mul, mul_neg, mul_one, add_neg_cancel]
    · have e : admBlockMatOf Z i j = star (Z (acoord i, acoord j)) := by
        simp only [admBlockMatOf_apply, hi, hj, eq_self_iff_true, neg_one_ne_one_complex,
          ite_true, ite_false]
      rw [e, hi, hj, neg_mul, one_mul, mul_one, neg_add_cancel]
    · have e : admBlockMatOf Z i j = 0 := by
        simp only [admBlockMatOf_apply, hi, hj, neg_one_ne_one_complex, ite_false]
      rw [e]; simp
  · show UJ * entrywiseConj (admBlockMatOf Z) = admBlockMatOf Z * UJ
    ext i j
    rw [UJ_mul_apply, mul_UJ_apply]
    show entrywiseConj (admBlockMatOf Z) (partner i) j = admBlockMatOf Z i (partner j)
    have h1 : entrywiseConj (admBlockMatOf Z) (partner i) j
        = star (admBlockMatOf Z (partner i) j) := rfl
    rw [h1]
    rcases gSign_eq_one_or_neg_one i with hi | hi <;>
      rcases gSign_eq_one_or_neg_one j with hj | hj
    · have hpi := gSign_partner_eq_neg_one_of_eq_one hi
      have hpj := gSign_partner_eq_neg_one_of_eq_one hj
      have e1 : admBlockMatOf Z (partner i) j = star (Z (acoord i, acoord j)) := by
        simp only [admBlockMatOf_apply, hpi, hj, eq_self_iff_true, neg_one_ne_one_complex,
          ite_true, ite_false, acoord_partner]
      have e2 : admBlockMatOf Z i (partner j) = Z (acoord i, acoord j) := by
        simp only [admBlockMatOf_apply, hi, hpj, eq_self_iff_true, neg_one_ne_one_complex,
          ite_true, ite_false, acoord_partner]
      rw [e1, e2, star_star]
    · have hpi := gSign_partner_eq_neg_one_of_eq_one hi
      have hpj := gSign_partner_eq_one_of_eq_neg_one hj
      have e1 : admBlockMatOf Z (partner i) j = 0 := by
        simp only [admBlockMatOf_apply, hpi, hj, neg_one_ne_one_complex, ite_false]
      have e2 : admBlockMatOf Z i (partner j) = 0 := by
        simp only [admBlockMatOf_apply, hi, hpj, eq_self_iff_true, ite_true]
      rw [e1, e2, star_zero]
    · have hpi := gSign_partner_eq_one_of_eq_neg_one hi
      have hpj := gSign_partner_eq_neg_one_of_eq_one hj
      have e1 : admBlockMatOf Z (partner i) j = 0 := by
        simp only [admBlockMatOf_apply, hpi, hj, eq_self_iff_true, ite_true]
      have e2 : admBlockMatOf Z i (partner j) = 0 := by
        simp only [admBlockMatOf_apply, hi, hpj, neg_one_ne_one_complex, ite_false]
      rw [e1, e2, star_zero]
    · have hpi := gSign_partner_eq_one_of_eq_neg_one hi
      have hpj := gSign_partner_eq_one_of_eq_neg_one hj
      have e1 : admBlockMatOf Z (partner i) j = Z (acoord i, acoord j) := by
        simp only [admBlockMatOf_apply, hpi, hj, eq_self_iff_true, neg_one_ne_one_complex,
          ite_true, ite_false, acoord_partner]
      have e2 : admBlockMatOf Z i (partner j) = star (Z (acoord i, acoord j)) := by
        simp only [admBlockMatOf_apply, hi, hpj, eq_self_iff_true, neg_one_ne_one_complex,
          ite_true, ite_false, acoord_partner]
      rw [e1, e2]

theorem admBlockMatOf_add (Z W : Fin 16 × Fin 16 → ℂ) :
    admBlockMatOf (Z + W) = admBlockMatOf Z + admBlockMatOf W := by
  ext i j
  rw [Matrix.add_apply]
  rcases gSign_eq_one_or_neg_one i with hi | hi <;>
    rcases gSign_eq_one_or_neg_one j with hj | hj
  · have e : ∀ F : Fin 16 × Fin 16 → ℂ, admBlockMatOf F i j = 0 := by
      intro F
      simp only [admBlockMatOf_apply, hi, hj, eq_self_iff_true, ite_true]
    rw [e, e, e]; simp
  · have e : ∀ F : Fin 16 × Fin 16 → ℂ, admBlockMatOf F i j = F (acoord i, acoord j) := by
      intro F
      simp only [admBlockMatOf_apply, hi, hj, eq_self_iff_true, neg_one_ne_one_complex,
        ite_true, ite_false]
    rw [e, e, e, Pi.add_apply]
  · have e : ∀ F : Fin 16 × Fin 16 → ℂ, admBlockMatOf F i j
        = star (F (acoord i, acoord j)) := by
      intro F
      simp only [admBlockMatOf_apply, hi, hj, eq_self_iff_true, neg_one_ne_one_complex,
        ite_true, ite_false]
    rw [e, e, e, Pi.add_apply, star_add]
  · have e : ∀ F : Fin 16 × Fin 16 → ℂ, admBlockMatOf F i j = 0 := by
      intro F
      simp only [admBlockMatOf_apply, hi, hj, neg_one_ne_one_complex, ite_false]
    rw [e, e, e]; simp

theorem admBlockMatOf_smul_real (c : ℝ) (Z : Fin 16 × Fin 16 → ℂ) :
    admBlockMatOf (c • Z) = c • admBlockMatOf Z := by
  ext i j
  rw [Matrix.smul_apply]
  rcases gSign_eq_one_or_neg_one i with hi | hi <;>
    rcases gSign_eq_one_or_neg_one j with hj | hj
  · have e : ∀ F : Fin 16 × Fin 16 → ℂ, admBlockMatOf F i j = 0 := by
      intro F
      simp only [admBlockMatOf_apply, hi, hj, eq_self_iff_true, ite_true]
    rw [e, e]; simp
  · have e : ∀ F : Fin 16 × Fin 16 → ℂ, admBlockMatOf F i j = F (acoord i, acoord j) := by
      intro F
      simp only [admBlockMatOf_apply, hi, hj, eq_self_iff_true, neg_one_ne_one_complex,
        ite_true, ite_false]
    rw [e, e, Pi.smul_apply]
  · have e : ∀ F : Fin 16 × Fin 16 → ℂ, admBlockMatOf F i j
        = star (F (acoord i, acoord j)) := by
      intro F
      simp only [admBlockMatOf_apply, hi, hj, eq_self_iff_true, neg_one_ne_one_complex,
        ite_true, ite_false]
    rw [e, e, Pi.smul_apply, census96_star_real_smul]
  · have e : ∀ F : Fin 16 × Fin 16 → ℂ, admBlockMatOf F i j = 0 := by
      intro F
      simp only [admBlockMatOf_apply, hi, hj, neg_one_ne_one_complex, ite_false]
    rw [e, e]; simp

/-- The coordinate equivalence `AdmBlock ≃ₗ[ℝ] (Fin 16 × Fin 16 → ℂ)`. -/
noncomputable def admBlockEquiv : AdmBlock ≃ₗ[ℝ] (Fin 16 × Fin 16 → ℂ) :=
  LinearEquiv.ofBijective
    { toFun := fun M p => crossCoordOf M.1 p.1 p.2
      map_add' := by
        intro M N
        funext p
        show crossCoordOf (M + N).1 p.1 p.2
          = crossCoordOf M.1 p.1 p.2 + crossCoordOf N.1 p.1 p.2
        unfold crossCoordOf
        rfl
      map_smul' := by
        intro c M
        funext p
        show crossCoordOf (c • M).1 p.1 p.2 = c • crossCoordOf M.1 p.1 p.2
        unfold crossCoordOf
        rfl }
    (Function.bijective_iff_has_inverse.mpr
      ⟨fun Z => ⟨admBlockMatOf Z, admBlockMatOf_isAdmBlock Z⟩,
       fun M => by
         apply Subtype.ext
         show admBlockMatOf (fun p : Fin 16 × Fin 16 => crossCoordOf M.1 p.1 p.2) = M.1
         obtain ⟨hgr, hj⟩ := M.2
         ext i j
         rcases gSign_eq_one_or_neg_one i with hi | hi <;>
           rcases gSign_eq_one_or_neg_one j with hj2 | hj2
         · have h0 : M.1 i j = 0 :=
             gammaOdd_entry_eq_zero_of_gSign_eq M.1 hgr (by rw [hi, hj2])
           show admBlockMatOf _ i j = M.1 i j
           rw [h0]
           simp only [admBlockMatOf_apply, hi, hj2, eq_self_iff_true, ite_true]
         · show admBlockMatOf _ i j = M.1 i j
           have e1 : admBlockMatOf (fun p : Fin 16 × Fin 16 => crossCoordOf M.1 p.1 p.2) i j
               = crossCoordOf M.1 (acoord i) (acoord j) := by
             simp only [admBlockMatOf_apply, hi, hj2, eq_self_iff_true,
               neg_one_ne_one_complex, ite_true, ite_false]
           rw [e1]
           unfold crossCoordOf
           rw [plusEmb_acoord_of_gSign_eq_one hi,
             minusEmb_flip8_acoord_of_gSign_eq_neg_one hj2]
         · show admBlockMatOf _ i j = M.1 i j
           have e1 : admBlockMatOf (fun p : Fin 16 × Fin 16 => crossCoordOf M.1 p.1 p.2) i j
               = star (crossCoordOf M.1 (acoord i) (acoord j)) := by
             simp only [admBlockMatOf_apply, hi, hj2, eq_self_iff_true,
               neg_one_ne_one_complex, ite_true, ite_false]
           rw [e1]
           unfold crossCoordOf
           rw [plusEmb_acoord_eq_partner_of_gSign_eq_neg_one hi,
             minusEmb_flip8_acoord_eq_partner_of_gSign_eq_one hj2]
           exact admBlock_entry_star M.1 M.2 i j
         · have h0 : M.1 i j = 0 :=
             gammaOdd_entry_eq_zero_of_gSign_eq M.1 hgr (by rw [hi, hj2])
           show admBlockMatOf _ i j = M.1 i j
           rw [h0]
           simp only [admBlockMatOf_apply, hi, hj2, neg_one_ne_one_complex, ite_false],
       fun Z => by
         funext p
         show crossCoordOf (admBlockMatOf Z) p.1 p.2 = Z p
         unfold crossCoordOf
         have e1 : admBlockMatOf Z (plusEmb p.1) (minusEmb (flip8 p.2))
             = Z p := by
           have e := admBlockMatOf_apply Z (plusEmb p.1) (minusEmb (flip8 p.2))
           rw [ite_eq_left (gSign_plusEmb _),
             ite_eq_right (gSign_ne_one_of_eq_neg_one (gSign_minusEmb _)),
             acoord_plusEmb, acoord_minusEmb, flip8_flip8] at e
           exact e
         exact e1⟩)

/-- **The pair-block 512 lemma.** `finrank ℝ AdmBlock = 512`, by the
    free folded cross-block parameterization (`256` complex
    coordinates). -/
theorem finrank_admBlock : Module.finrank ℝ AdmBlock = 512 := by
  rw [admBlockEquiv.finrank_eq, Module.finrank_pi_fintype]
  simp [Complex.finrank_real_complex]

end ThetLogos

namespace ThetLogos

/-! ## §8. Blockwise splitting of `IsAdm96` -/

theorem conjTranspose_smul_real (c : ℝ) (M : Matrix I32 I32 ℂ) :
    (c • M).conjTranspose = c • M.conjTranspose := by
  ext i j
  have e1 : ((c • M) j i) = c • (M j i) := rfl
  have e2 : ((c • M.conjTranspose) i j) = c • (M.conjTranspose i j) := rfl
  rw [Matrix.conjTranspose_apply, e1, census96_star_real_smul, e2,
    Matrix.conjTranspose_apply]

theorem star_gSign (i : I32) : star (gSign i) = gSign i := by
  rcases gSign_eq_one_or_neg_one i with h | h <;> rw [h] <;> simp

theorem orderOneHolds_add {M N : Matrix I32 I32 ℂ}
    (hM : OrderOneHolds M) (hN : OrderOneHolds N) : OrderOneHolds (M + N) := by
  intro a b
  have e1 := hM a b
  have e2 := hN a b
  have hX : (M + N) * smGen a - smGen a * (M + N)
      = (M * smGen a - smGen a * M) + (N * smGen a - smGen a * N) := by
    simp only [Matrix.add_mul, Matrix.mul_add, sub_eq_add_neg, neg_add]
    ac_rfl
  rw [hX, Matrix.add_mul, Matrix.mul_add]
  have h3 : ((M * smGen a - smGen a * M) * smGenOp b
      + (N * smGen a - smGen a * N) * smGenOp b)
      - (smGenOp b * (M * smGen a - smGen a * M)
      + smGenOp b * (N * smGen a - smGen a * N))
      = ((M * smGen a - smGen a * M) * smGenOp b
      - smGenOp b * (M * smGen a - smGen a * M))
      + ((N * smGen a - smGen a * N) * smGenOp b
      - smGenOp b * (N * smGen a - smGen a * N)) := by
    simp only [sub_eq_add_neg, neg_add]
    ac_rfl
  rw [h3, e1, e2, add_zero]

theorem orderOneHolds_smul_real (c : ℝ) {M : Matrix I32 I32 ℂ}
    (hM : OrderOneHolds M) : OrderOneHolds (c • M) := by
  intro a b
  have e := hM a b
  have hX : (c • M) * smGen a - smGen a * (c • M)
      = c • (M * smGen a - smGen a * M) := by
    rw [Matrix.smul_mul, Matrix.mul_smul, ← smul_sub]
  show ((c • M) * smGen a - smGen a * (c • M)) * smGenOp b
    - smGenOp b * ((c • M) * smGen a - smGen a * (c • M)) = 0
  rw [hX, Matrix.smul_mul, Matrix.mul_smul, ← smul_sub, e, smul_zero]

theorem orderOneHolds_zero : OrderOneHolds (0 : Matrix I32 I32 ℂ) := by
  intro a b; simp

/-- The J₃-condition read blockwise. -/
theorem isAdm96_J_block (D : Matrix I96 I96 ℂ) (hD : IsAdm96 D)
    (i : I32) (g : Fin 3) (j : I32) (gp : Fin 3) :
    D (i, g) (j, gp) = genBlock D gp g (partner j) (partner i) := by
  have he := congrFun (congrFun hD.2.2 (i, g)) (j, gp)
  rw [UJ3_conj_apply, Matrix.transpose_apply] at he
  exact he.symm

/-- Every generation block of an admissible `D` is block-admissible. -/
theorem isAdmBlock_genBlock (D : Matrix I96 I96 ℂ) (hD : IsAdm96 D) (g gp : Fin 3) :
    IsAdmBlock (genBlock D g gp) := by
  refine ⟨?_, ?_⟩
  · ext i j
    rw [Matrix.add_apply, Matrix.zero_apply, gammaF_mul_apply, mul_gammaF_apply]
    have he := congrFun (congrFun hD.2.1 (i, g)) (j, gp)
    rw [Matrix.add_apply, Matrix.zero_apply, gamma3_mul_apply, mul_gamma3_apply] at he
    exact he
  · ext i j
    rw [UJ_mul_apply, mul_UJ_apply]
    show entrywiseConj (genBlock D g gp) (partner i) j = genBlock D g gp i (partner j)
    have h1 : entrywiseConj (genBlock D g gp) (partner i) j
        = star (D (partner i, g) (j, gp)) := rfl
    rw [h1, selfAdjoint_entry96 D hD.1 (partner i, g) (j, gp), star_star,
      isAdm96_J_block D hD j gp (partner i) g, partner_involutive]

/-- Every diagonal generation block of an admissible `D` is
    one-generation admissible. -/
theorem isAdm32_genBlock_diag (D : Matrix I96 I96 ℂ) (hD : IsAdm96 D) (g : Fin 3) :
    IsAdm32 (genBlock D g g) := by
  refine ⟨?_, (isAdmBlock_genBlock D hD g g).1, ?_⟩
  · ext i j
    rw [Matrix.conjTranspose_apply]
    show star (genBlock D g g j i) = genBlock D g g i j
    exact (selfAdjoint_entry96 D hD.1 (i, g) (j, g)).symm
  · show UJ * (genBlock D g g).transpose * UJ = genBlock D g g
    ext i j
    rw [UJ_conj_apply, Matrix.transpose_apply]
    show genBlock D g g (partner j) (partner i) = genBlock D g g i j
    exact (isAdm96_J_block D hD i g j g).symm

/-- Self-adjointness pairs the `(g', g)` block with the `(g, g')` block
    by conjugate-transpose. -/
theorem genBlock_conjTranspose_partner (D : Matrix I96 I96 ℂ) (hD : IsAdm96 D)
    (g gp : Fin 3) : genBlock D gp g = (genBlock D g gp).conjTranspose := by
  ext i j
  rw [Matrix.conjTranspose_apply]
  show D (i, gp) (j, g) = star (D (j, g) (i, gp))
  exact selfAdjoint_entry96 D hD.1 (i, gp) (j, g)

end ThetLogos

namespace ThetLogos

/-! ## §9. Assembly from diagonal and pair data -/

/-- Unordered generation pairs: `g < g'` in `Fin 3` (three of them). -/
abbrev GenPair := {p : Fin 3 × Fin 3 // p.1 < p.2}

theorem card_genPair : Fintype.card GenPair = 3 := by
  rw [Fintype.card_subtype, Finset.card_filter,
    ← Finset.univ_product_univ, Finset.sum_product]
  have hinner : ∀ u : Fin 3, (∑ v : Fin 3, if u < v then 1 else 0) = 2 - u.val := by
    intro u
    rw [← Finset.card_filter]
    have hset : Finset.univ.filter (fun v : Fin 3 => u < v) = Finset.Ioi u := by
      ext v
      simp [Finset.mem_Ioi]
    rw [hset, Fin.card_Ioi]
  rw [Finset.sum_congr rfl (fun u _ => hinner u)]
  rw [Fin.sum_univ_eq_sum_range (fun i => 2 - i) 3]
  norm_num [Finset.sum_range_succ]

/-- A `96 × 96` matrix from its nine generation blocks. -/
def blockMat96 (B : Fin 3 → Fin 3 → Matrix I32 I32 ℂ) : Matrix I96 I96 ℂ :=
  fun (i, g) (j, gp) => B g gp i j

theorem genBlock_blockMat96 (B : Fin 3 → Fin 3 → Matrix I32 I32 ℂ) (g gp : Fin 3) :
    genBlock (blockMat96 B) g gp = B g gp := rfl

/-- The block layout of an assembled matrix: diagonal data on the
    diagonal, pair data above it, conjugate-transposes below it. -/
def pairBlockOf (diag : Fin 3 → Matrix I32 I32 ℂ) (pair : GenPair → Matrix I32 I32 ℂ)
    (g gp : Fin 3) : Matrix I32 I32 ℂ :=
  if h : g = gp then diag g
  else if h2 : g < gp then pair ⟨(g, gp), h2⟩
  else (pair ⟨(gp, g), lt_of_le_of_ne (le_of_not_gt h2) (Ne.symm h)⟩).conjTranspose

/-- Assembly of a `96 × 96` matrix from three diagonal blocks and
    three unordered-pair blocks. -/
def assemble96 (diag : Fin 3 → Matrix I32 I32 ℂ) (pair : GenPair → Matrix I32 I32 ℂ) :
    Matrix I96 I96 ℂ :=
  blockMat96 (pairBlockOf diag pair)

theorem genBlock_assemble96 (diag : Fin 3 → Matrix I32 I32 ℂ)
    (pair : GenPair → Matrix I32 I32 ℂ) (g gp : Fin 3) :
    genBlock (assemble96 diag pair) g gp = pairBlockOf diag pair g gp := rfl

theorem pairBlockOf_diag (diag : Fin 3 → Matrix I32 I32 ℂ)
    (pair : GenPair → Matrix I32 I32 ℂ) (g : Fin 3) :
    pairBlockOf diag pair g g = diag g := dif_pos rfl

theorem pairBlockOf_of_lt (diag : Fin 3 → Matrix I32 I32 ℂ)
    (pair : GenPair → Matrix I32 I32 ℂ) {g gp : Fin 3} (h : g < gp) :
    pairBlockOf diag pair g gp = pair ⟨(g, gp), h⟩ := by
  unfold pairBlockOf
  rw [dif_neg (ne_of_lt h), dif_pos h]

theorem pairBlockOf_of_gt (diag : Fin 3 → Matrix I32 I32 ℂ)
    (pair : GenPair → Matrix I32 I32 ℂ) {g gp : Fin 3} (h : gp < g) :
    pairBlockOf diag pair g gp = (pair ⟨(gp, g), h⟩).conjTranspose := by
  unfold pairBlockOf
  rw [dif_neg (ne_of_gt h), dif_neg (not_lt_of_gt h)]

theorem assemble96_isAdm96 (diag : Fin 3 → Matrix I32 I32 ℂ)
    (pair : GenPair → Matrix I32 I32 ℂ)
    (hd : ∀ g, IsAdm32 (diag g)) (hp : ∀ p, IsAdmBlock (pair p)) :
    IsAdm96 (assemble96 diag pair) := by
  refine ⟨?_, ?_, ?_⟩
  · -- self-adjoint
    ext ⟨i, g⟩ ⟨j, gp⟩
    rw [Matrix.conjTranspose_apply]
    show star (assemble96 diag pair (j, gp) (i, g)) = assemble96 diag pair (i, g) (j, gp)
    have e1 : assemble96 diag pair (j, gp) (i, g) = pairBlockOf diag pair gp g j i := rfl
    have e2 : assemble96 diag pair (i, g) (j, gp) = pairBlockOf diag pair g gp i j := rfl
    rw [e1, e2]
    rcases lt_trichotomy g gp with h | h | h
    · rw [pairBlockOf_of_lt diag pair h, pairBlockOf_of_gt diag pair h,
        Matrix.conjTranspose_apply, star_star]
    · subst h
      rw [pairBlockOf_diag]
      exact (selfAdjoint_entry (diag g) (hd g).1 i j).symm
    · rw [pairBlockOf_of_gt diag pair h, pairBlockOf_of_lt diag pair h,
        Matrix.conjTranspose_apply]
  · -- grading-odd
    ext ⟨i, g⟩ ⟨j, gp⟩
    rw [Matrix.add_apply, Matrix.zero_apply, gamma3_mul_apply, mul_gamma3_apply]
    show gSign i * assemble96 diag pair (i, g) (j, gp)
      + assemble96 diag pair (i, g) (j, gp) * gSign j = 0
    have e2 : assemble96 diag pair (i, g) (j, gp) = pairBlockOf diag pair g gp i j := rfl
    rw [e2]
    rcases lt_trichotomy g gp with h | h | h
    · rw [pairBlockOf_of_lt diag pair h]
      exact gammaOdd_entry (pair ⟨(g, gp), h⟩) (hp _).1 i j
    · subst h
      rw [pairBlockOf_diag]
      exact gammaOdd_entry (diag g) (hd g).2.1 i j
    · rw [pairBlockOf_of_gt diag pair h, Matrix.conjTranspose_apply]
      have he := gammaOdd_entry (pair ⟨(gp, g), h⟩) (hp _).1 j i
      have hstar := congrArg star he
      simp only [star_add, star_zero] at hstar
      rw [star_mul, star_mul, star_gSign, star_gSign] at hstar
      -- hstar : star (P j i) * gSign j + gSign i * star (P j i) = 0
      rw [add_comm (gSign i * star (pair ⟨(gp, g), h⟩ j i))
        (star (pair ⟨(gp, g), h⟩ j i) * gSign j)]
      exact hstar
  · -- J-compatible (transpose form)
    show UJ3 * (assemble96 diag pair).transpose * UJ3 = assemble96 diag pair
    ext ⟨i, g⟩ ⟨j, gp⟩
    rw [UJ3_conj_apply, Matrix.transpose_apply]
    show assemble96 diag pair (partner j, gp) (partner i, g)
      = assemble96 diag pair (i, g) (j, gp)
    have e1 : assemble96 diag pair (partner j, gp) (partner i, g)
        = pairBlockOf diag pair gp g (partner j) (partner i) := rfl
    have e2 : assemble96 diag pair (i, g) (j, gp) = pairBlockOf diag pair g gp i j := rfl
    rw [e1, e2]
    rcases lt_trichotomy g gp with h | h | h
    · rw [pairBlockOf_of_lt diag pair h, pairBlockOf_of_gt diag pair h,
        Matrix.conjTranspose_apply]
      exact admBlock_entry_star (pair ⟨(g, gp), h⟩) (hp _) i j
    · subst h
      rw [pairBlockOf_diag]
      exact (jCompat_entry_local (diag g) (hd g).2.2 i j).symm
    · rw [pairBlockOf_of_gt diag pair h, pairBlockOf_of_lt diag pair h,
        Matrix.conjTranspose_apply]
      have he := admBlock_entry_star (pair ⟨(gp, g), h⟩) (hp _) j i
      have hstar := congrArg star he
      rwa [star_star] at hstar

theorem assemble96_orderOneHolds₃ (diag : Fin 3 → Matrix I32 I32 ℂ)
    (pair : GenPair → Matrix I32 I32 ℂ)
    (hd : ∀ g, OrderOneHolds (diag g))
    (hp : ∀ p, OrderOneHolds (pair p) ∧ OrderOneHolds (pair p).conjTranspose) :
    OrderOneHolds₃ (assemble96 diag pair) := by
  rw [orderOneHolds₃_iff_blocks]
  intro g gp
  rw [genBlock_assemble96]
  rcases lt_trichotomy g gp with h | h | h
  · rw [pairBlockOf_of_lt diag pair h]; exact (hp _).1
  · subst h; rw [pairBlockOf_diag]; exact hd g
  · rw [pairBlockOf_of_gt diag pair h]; exact (hp _).2

theorem assemble96_add (diag1 diag2 : Fin 3 → Matrix I32 I32 ℂ)
    (pair1 pair2 : GenPair → Matrix I32 I32 ℂ) :
    assemble96 (fun g => diag1 g + diag2 g) (fun p => pair1 p + pair2 p)
      = assemble96 diag1 pair1 + assemble96 diag2 pair2 := by
  ext ⟨i, g⟩ ⟨j, gp⟩
  show pairBlockOf (fun g => diag1 g + diag2 g) (fun p => pair1 p + pair2 p) g gp i j
    = pairBlockOf diag1 pair1 g gp i j + pairBlockOf diag2 pair2 g gp i j
  rcases lt_trichotomy g gp with h | h | h
  · rw [pairBlockOf_of_lt _ _ h, pairBlockOf_of_lt _ _ h, pairBlockOf_of_lt _ _ h]; rfl
  · subst h; rw [pairBlockOf_diag, pairBlockOf_diag, pairBlockOf_diag]; rfl
  · rw [pairBlockOf_of_gt _ _ h, pairBlockOf_of_gt _ _ h, pairBlockOf_of_gt _ _ h,
      Matrix.conjTranspose_add]
    rfl

theorem assemble96_smul_real (c : ℝ) (diag : Fin 3 → Matrix I32 I32 ℂ)
    (pair : GenPair → Matrix I32 I32 ℂ) :
    assemble96 (fun g => c • diag g) (fun p => c • pair p)
      = c • assemble96 diag pair := by
  ext ⟨i, g⟩ ⟨j, gp⟩
  show pairBlockOf (fun g => c • diag g) (fun p => c • pair p) g gp i j
    = c • pairBlockOf diag pair g gp i j
  rcases lt_trichotomy g gp with h | h | h
  · rw [pairBlockOf_of_lt _ _ h, pairBlockOf_of_lt _ _ h]; rfl
  · subst h; rw [pairBlockOf_diag, pairBlockOf_diag]; rfl
  · rw [pairBlockOf_of_gt _ _ h, pairBlockOf_of_gt _ _ h, conjTranspose_smul_real]
    rfl

/-- Assembly recovers a matrix from its own blocks iff it is
    self-adjoint (the off-diagonal blocks are then the
    conjugate-transposes of their partners). -/
theorem assemble96_of_isAdm96 (D : Matrix I96 I96 ℂ) (hD : IsAdm96 D) :
    assemble96 (fun g => genBlock D g g) (fun p => genBlock D p.1.1 p.1.2) = D := by
  ext ⟨i, g⟩ ⟨j, gp⟩
  show pairBlockOf (fun g => genBlock D g g) (fun p => genBlock D p.1.1 p.1.2) g gp i j
    = D (i, g) (j, gp)
  rcases lt_trichotomy g gp with h | h | h
  · rw [pairBlockOf_of_lt _ _ h]; rfl
  · subst h; rw [pairBlockOf_diag]; rfl
  · rw [pairBlockOf_of_gt _ _ h, Matrix.conjTranspose_apply]
    show star (genBlock D gp g j i) = D (i, g) (j, gp)
    exact (selfAdjoint_entry96 D hD.1 (i, g) (j, gp)).symm

end ThetLogos

namespace ThetLogos

/-! ## §10. The pair solution space (NAMED here)

The pair condition, extracted from `attack4_3gen.py` (commit `90a80e7`,
Step 2): an off-diagonal block ranges over the 512-real-dimensional
space of `γ_F`-odd blocks satisfying the entrywise-conj J-condition
`UJ * conj(M) = M * UJ` — in the Python's basis, `M = H₊` (hermitian
J-compatible, 272) or `M = Complex.I • H₋` (hermitian J-ANTI-compatible,
240). A generation pair `{g, g'}` in a self-adjoint `D` is the pair
`(M, M†)`; the pair solution space below is the space of first members
`M` whose pair `(M, M†)` has both members block-admissible and both
satisfying the one-generation order-one condition (the second is the
`(g', g)` instance of the decoupling). Its finrank is C96-3's raw
material — the 88 target — and is NOT computed here (K-C96-2 guard). -/

/-- **The pair solution space** `Census96PairSol`: single off-diagonal
    blocks `M` such that the self-adjoint pair `(M, M†)` is
    block-admissible in both members and order-one in both members. -/
def Census96PairSol : Submodule ℝ (Matrix I32 I32 ℂ) where
  carrier := {M | IsAdmBlock M ∧ IsAdmBlock M.conjTranspose ∧
    OrderOneHolds M ∧ OrderOneHolds M.conjTranspose}
  add_mem' := by
    intro M N hM hN
    refine ⟨AdmBlock.add_mem hM.1 hN.1, ?_, orderOneHolds_add hM.2.2.1 hN.2.2.1, ?_⟩
    · rw [Matrix.conjTranspose_add]
      exact AdmBlock.add_mem hM.2.1 hN.2.1
    · rw [Matrix.conjTranspose_add]
      exact orderOneHolds_add hM.2.2.2 hN.2.2.2
  zero_mem' := by
    have hAdm0 : IsAdmBlock (0 : Matrix I32 I32 ℂ) :=
      ⟨by simp, by ext i j; rw [UJ_mul_apply]; simp [entrywiseConj]⟩
    refine ⟨hAdm0, ?_, orderOneHolds_zero, ?_⟩
    · have h0 : (0 : Matrix I32 I32 ℂ).conjTranspose = 0 := by simp
      rw [h0]; exact hAdm0
    · have h0 : (0 : Matrix I32 I32 ℂ).conjTranspose = 0 := by simp
      rw [h0]; exact orderOneHolds_zero
  smul_mem' := by
    intro c M hM
    refine ⟨AdmBlock.smul_mem c hM.1, ?_, orderOneHolds_smul_real c hM.2.2.1, ?_⟩
    · rw [conjTranspose_smul_real]
      exact AdmBlock.smul_mem c hM.2.1
    · rw [conjTranspose_smul_real]
      exact orderOneHolds_smul_real c hM.2.2.2

/-! ## §11. The decomposition equivalences and the 2352 discharge -/

/-- The forward decomposition map on solution data: diagonal blocks
    to `Sol32`, unordered-pair blocks to `Census96PairSol`. -/
def census96Forward (D : Census96Sol) :
    (Fin 3 → Sol32) × (GenPair → Census96PairSol) :=
  (fun g => ⟨genBlock D.1 g g,
    ⟨isAdm32_genBlock_diag D.1 D.2.1 g,
      (orderOneHolds₃_iff_blocks D.1).mp D.2.2 g g⟩⟩,
   fun p => ⟨genBlock D.1 p.1.1 p.1.2,
    ⟨isAdmBlock_genBlock D.1 D.2.1 p.1.1 p.1.2,
      by rw [← genBlock_conjTranspose_partner D.1 D.2.1 p.1.1 p.1.2]
         exact isAdmBlock_genBlock D.1 D.2.1 p.1.2 p.1.1,
      (orderOneHolds₃_iff_blocks D.1).mp D.2.2 p.1.1 p.1.2,
      by rw [← genBlock_conjTranspose_partner D.1 D.2.1 p.1.1 p.1.2]
         exact (orderOneHolds₃_iff_blocks D.1).mp D.2.2 p.1.2 p.1.1⟩⟩)

/-- The backward assembly map on decomposed solution data. -/
def census96Backward (data : (Fin 3 → Sol32) × (GenPair → Census96PairSol)) :
    Census96Sol :=
  ⟨assemble96 (fun g => (data.1 g).1) (fun p => (data.2 p).1),
    ⟨assemble96_isAdm96 _ _
        (fun g => (data.1 g).2.1) (fun p => (data.2 p).2.1),
      assemble96_orderOneHolds₃ _ _
        (fun g => (data.1 g).2.2)
        (fun p => ⟨(data.2 p).2.2.2.1, (data.2 p).2.2.2.2⟩)⟩⟩

/-- **Solution-space decomposition (C96-1, item 3).** `Census96Sol` is
    ℝ-linearly equivalent to three diagonal `Sol32` pieces and three
    unordered-pair `Census96PairSol` pieces. -/
noncomputable def census96SolEquiv :
    Census96Sol ≃ₗ[ℝ] (Fin 3 → Sol32) × (GenPair → Census96PairSol) where
  toFun := census96Forward
  invFun := census96Backward
  left_inv D := by
    apply Subtype.ext
    show assemble96 (fun g => genBlock D.1 g g) (fun p => genBlock D.1 p.1.1 p.1.2)
      = D.1
    exact assemble96_of_isAdm96 D.1 D.2.1
  right_inv data := by
    apply Prod.ext
    · funext g
      apply Subtype.ext
      show genBlock (assemble96 (fun g => (data.1 g).1) (fun p => (data.2 p).1)) g g
        = (data.1 g).1
      rw [genBlock_assemble96, pairBlockOf_diag]
    · funext p
      apply Subtype.ext
      show genBlock (assemble96 (fun g => (data.1 g).1) (fun p => (data.2 p).1))
          p.1.1 p.1.2 = (data.2 p).1
      rw [genBlock_assemble96, pairBlockOf_of_lt _ _ p.2]
  map_add' D1 D2 := by
    apply Prod.ext <;> funext x <;> apply Subtype.ext <;> ext i j <;> rfl
  map_smul' c D := by
    apply Prod.ext <;> funext x <;> apply Subtype.ext <;> ext i j <;> rfl

/-- The forward decomposition map on admissible data. -/
def adm96Forward (D : Adm96) : (Fin 3 → Adm32) × (GenPair → AdmBlock) :=
  (fun g => ⟨genBlock D.1 g g, isAdm32_genBlock_diag D.1 D.2 g⟩,
   fun p => ⟨genBlock D.1 p.1.1 p.1.2, isAdmBlock_genBlock D.1 D.2 p.1.1 p.1.2⟩)

/-- The backward assembly map on decomposed admissible data. -/
def adm96Backward (data : (Fin 3 → Adm32) × (GenPair → AdmBlock)) : Adm96 :=
  ⟨assemble96 (fun g => (data.1 g).1) (fun p => (data.2 p).1),
    assemble96_isAdm96 _ _
      (fun g => (data.1 g).2) (fun p => (data.2 p).2)⟩

/-- **The admissible-space decomposition.** `Adm96` is ℝ-linearly
    equivalent to three diagonal `Adm32` pieces (272 each) and three
    unordered-pair `AdmBlock` pieces (512 each). -/
noncomputable def adm96Equiv :
    Adm96 ≃ₗ[ℝ] (Fin 3 → Adm32) × (GenPair → AdmBlock) where
  toFun := adm96Forward
  invFun := adm96Backward
  left_inv D := by
    apply Subtype.ext
    show assemble96 (fun g => genBlock D.1 g g) (fun p => genBlock D.1 p.1.1 p.1.2)
      = D.1
    exact assemble96_of_isAdm96 D.1 D.2
  right_inv data := by
    apply Prod.ext
    · funext g
      apply Subtype.ext
      show genBlock (assemble96 (fun g => (data.1 g).1) (fun p => (data.2 p).1)) g g
        = (data.1 g).1
      rw [genBlock_assemble96, pairBlockOf_diag]
    · funext p
      apply Subtype.ext
      show genBlock (assemble96 (fun g => (data.1 g).1) (fun p => (data.2 p).1))
          p.1.1 p.1.2 = (data.2 p).1
      rw [genBlock_assemble96, pairBlockOf_of_lt _ _ p.2]
  map_add' D1 D2 := by
    apply Prod.ext <;> funext x <;> apply Subtype.ext <;> ext i j <;> rfl
  map_smul' c D := by
    apply Prod.ext <;> funext x <;> apply Subtype.ext <;> ext i j <;> rfl

/-- **The `Adm96Dim` discharge (C96-1, item 4).** `finrank ℝ Adm96 =
    2352 = 3 * 272 + 3 * 512`, from the parameterization: the
    decomposition equivalence, the one-generation 272 lemma, and the
    pair-block 512 lemma. This is the interface's first proof
    obligation, discharged. NOT the census (K-C96-2 guard): the
    46/88 finranks remain C96-2/C96-3 targets. -/
theorem adm96Dim_proved : Adm96Dim := by
  unfold Adm96Dim
  rw [adm96Equiv.finrank_eq, Module.finrank_prod]
  have h1 : Module.finrank ℝ (Fin 3 → Adm32) = 3 * 272 := by
    rw [Module.finrank_pi_fintype]
    simp [finrank_adm32]
  have h2 : Module.finrank ℝ (GenPair → AdmBlock) = 3 * 512 := by
    rw [Module.finrank_pi_fintype]
    simp [finrank_admBlock, card_genPair]
  rw [h1, h2]

end ThetLogos
