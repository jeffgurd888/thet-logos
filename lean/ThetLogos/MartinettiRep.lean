import Mathlib.Data.Matrix.Mul
import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic
import ThetLogos.Scaffold32

/-!
# ThetLogos.MartinettiRep — the finite SM representation (T2/T3)

After: Martinetti, arXiv:2301.08346v2 §2.5 (recalling
Chamseddine–Connes–Marcolli); verified numerically 2026-09-26.

The 32-dim one-generation representation of A_F = ℂ ⊕ ℍ ⊕ M₃(ℂ)
in the repository's post-swap basis:

* 0–7   : left particles (H doublets, Γ=+1)
* 8–15  : right particles (C singlets, Γ=−1)
* 16–23 : left antiparticles (Γ=−1)
* 24–31 : right antiparticles (Γ=+1)

(C,I,α) index map:
  pL(I,a) = I*2+a         (0–7)
  pR(I,a) = 8+I*2+a       (8–15)
  aL(I,a) = 16+I*2+a      (16–23)
  aR(I,a) = 24+I*2+a      (24–31)

H acts on flavour α (Pauli on pL doublets).
M₃ acts on colour I (Gell-Mann on antiparticle triplets).
C acts on right particles and antileptons.

Tier T2: definitions. Tier T3: grading-evenness, order-zero (proved).
The 46-dim order-one nullspace is T4 (numerical, not formalized here).
-/

open Matrix

namespace ThetLogos

/-- Pauli matrices (as functions on Fin 2 × Fin 2). -/
def pauli : Fin 3 → Matrix (Fin 2) (Fin 2) ℂ
  | 0 => !![0, 1; 1, 0]
  | 1 => !![0, -Complex.I; Complex.I, 0]
  | 2 => !![1, 0; 0, -1]

/-- Gell-Mann matrices (as functions on Fin 3 × Fin 3). -/
noncomputable def gellMann : Fin 8 → Matrix (Fin 3) (Fin 3) ℂ
  | 0 => !![0, 1, 0; 1, 0, 0; 0, 0, 0]
  | 1 => !![0, -Complex.I, 0; Complex.I, 0, 0; 0, 0, 0]
  | 2 => !![1, 0, 0; 0, -1, 0; 0, 0, 0]
  | 3 => !![0, 0, 1; 0, 0, 0; 1, 0, 0]
  | 4 => !![0, 0, -Complex.I; 0, 0, 0; Complex.I, 0, 0]
  | 5 => !![0, 0, 0; 0, 0, 1; 0, 1, 0]
  | 6 => !![0, 0, 0; 0, 0, -Complex.I; 0, Complex.I, 0]
  | 7 => ((Real.sqrt 3 : ℂ))⁻¹ • !![1, 0, 0; 0, 1, 0; 0, 0, -2]

/-- C generator: i on 8–15 (right particles), 16–17 and 24–25 (antileptons). -/
def genC : Matrix I32 I32 ℂ := fun i j =>
  if i = j then
    let k := i.val
    if 8 ≤ k ∧ k < 16 then Complex.I
    else if k = 16 ∨ k = 17 ∨ k = 24 ∨ k = 25 then Complex.I
    else 0
  else 0

/-- H generator k: Pauli σ_k on each pL doublet (I*2, I*2+1) for I=0..3. -/
def genH (k : Fin 3) : Matrix I32 I32 ℂ := fun i j =>
  let iv := i.val; let jv := j.val
  if iv < 8 ∧ jv < 8 ∧ iv / 2 = jv / 2 then
    pauli k ⟨iv % 2, Nat.mod_lt _ (by norm_num)⟩ ⟨jv % 2, Nat.mod_lt _ (by norm_num)⟩
  else 0

/-- Map a flat index to (triplet, colour-position) if it lies in a colour triplet.
    T0=(18,20,22), T1=(19,21,23), T2=(26,28,30), T3=(27,29,31). -/
def tripletOf (n : Nat) : Option (Fin 4 × Fin 3) :=
  match n with
  | 18 => some (0, 0) | 20 => some (0, 1) | 22 => some (0, 2)
  | 19 => some (1, 0) | 21 => some (1, 1) | 23 => some (1, 2)
  | 26 => some (2, 0) | 28 => some (2, 1) | 30 => some (2, 2)
  | 27 => some (3, 0) | 29 => some (3, 1) | 31 => some (3, 2)
  | _ => none

/-- Triplet index determines the Γ-eigenspace: t<2 forces 18–23 (Γ=-1),
    t≥2 forces 26–31 (Γ=+1). Proved by finite case analysis on n<32. -/
theorem tripletOf_eig (n : Nat) (hn : n < 32) (t : Fin 4) (p : Fin 3)
    (h : tripletOf n = some (t, p)) :
    (t.val < 2 ∧ 18 ≤ n ∧ n < 24) ∨ (2 ≤ t.val ∧ 26 ≤ n ∧ n < 32) := by
  interval_cases n <;> simp only [tripletOf] at h <;> (
    -- h : some (c1,c2) = some (t,p) or h : none = some (t,p)
    simp at h <;> omega
  )

/-- M₃ generator a: Gell-Mann λ_a on colour triplets. -/
noncomputable def genM (a : Fin 8) : Matrix I32 I32 ℂ := fun i j =>
  match tripletOf i.val, tripletOf j.val with
  | some (t1, p1), some (t2, p2) => if t1 = t2 then gellMann a p1 p2 else 0
  | _, _ => 0

/-- All 12 generators as a single indexed family. -/
noncomputable def smGen : Fin 12 → Matrix I32 I32 ℂ
  | 0 => genC
  | 1 => genH 0
  | 2 => genH 1
  | 3 => genH 2
  | 4 => genM 0
  | 5 => genM 1
  | 6 => genM 2
  | 7 => genM 3
  | 8 => genM 4
  | 9 => genM 5
  | 10 => genM 6
  | 11 => genM 7


/-- Opposite representation: π°(M) = UJ * Mᵀ * UJ. -/
noncomputable def smGenOp (g : Fin 12) : Matrix I32 I32 ℂ :=
  UJ * (smGen g).transpose * UJ

/-! ## Grading-evenness: [Γ, π(a)] = 0 -/

/-- genC is diagonal: off-diagonal entries vanish. -/
theorem genC_apply_ne {i j : I32} (h : i ≠ j) : genC i j = 0 := by
  unfold genC
  simp [h]

/-- genC is diagonal, hence commutes with diagonal Γ. -/
theorem genC_grading_even : gammaF * genC = genC * gammaF := by
  ext i j
  simp only [Matrix.mul_apply]
  by_cases h : i = j
  · subst h
    rw [Finset.sum_eq_single i]
    · rw [Finset.sum_eq_single i]
      · ring
      · intro k _ hki
        rw [genC_apply_ne (Ne.symm hki), zero_mul]
      · intro hcon
        exact absurd (Finset.mem_univ i) hcon
    · intro k _ hki
      rw [gammaF_apply_ne (Ne.symm hki), zero_mul]
    · intro hcon
      exact absurd (Finset.mem_univ i) hcon
  · have h1 : ∑ k : I32, gammaF i k * genC k j = 0 := by
      apply Finset.sum_eq_zero
      intro k _
      by_cases hki : k = i
      · subst hki
        rw [genC_apply_ne h, mul_zero]
      · rw [gammaF_apply_ne (fun heq => hki heq.symm), zero_mul]
    have h2 : ∑ k : I32, genC i k * gammaF k j = 0 := by
      apply Finset.sum_eq_zero
      intro k _
      by_cases hki : k = i
      · subst hki
        rw [gammaF_apply_ne h, mul_zero]
      · rw [genC_apply_ne (fun heq => hki heq.symm), zero_mul]
    rw [h1, h2]

/-- genH preserves the Γ=+1 eigenspace (0–7). -/
theorem genH_grading_even (k : Fin 3) : gammaF * genH k = genH k * gammaF := by
  ext i j
  simp only [Matrix.mul_apply]
  -- Collapse sums: gammaF is diagonal
  have hsum1 : ∑ l : I32, gammaF i l * genH k l j = gammaF i i * genH k i j := by
    rw [Finset.sum_eq_single i]
    · intro l _ hli
      rw [gammaF_apply_ne (Ne.symm hli), zero_mul]
    · intro hcon
      exact absurd (Finset.mem_univ i) hcon
  have hsum2 : ∑ l : I32, genH k i l * gammaF l j = genH k i j * gammaF j j := by
    rw [Finset.sum_eq_single j]
    · intro l _ hlj
      rw [gammaF_apply_ne hlj, mul_zero]
    · intro hcon
      exact absurd (Finset.mem_univ j) hcon
  rw [hsum1, hsum2]
  -- If genH k i j ≠ 0 then i,j < 8, so both gammaF values are 1
  by_cases hnz : genH k i j = 0
  · rw [hnz, mul_zero, zero_mul]
  · -- Extract i.val < 8 and j.val < 8 from the definition
    have hi8 : i.val < 8 := by
      unfold genH at hnz
      simp only at hnz
      -- hnz says the if-then-else is ≠ 0, so the condition holds
      by_contra hcon
      push_neg at hcon
      have : (if i.val < 8 ∧ j.val < 8 ∧ i.val / 2 = j.val / 2 then
          pauli k ⟨i.val % 2, Nat.mod_lt _ (by norm_num)⟩ ⟨j.val % 2, Nat.mod_lt _ (by norm_num)⟩
          else 0) = 0 := by
        rw [if_neg]
        intro hcond
        exact absurd hcond.1 (Nat.not_lt_of_ge hcon)
      exact hnz this
    have hj8 : j.val < 8 := by
      unfold genH at hnz
      simp only at hnz
      by_contra hcon
      push_neg at hcon
      have : (if i.val < 8 ∧ j.val < 8 ∧ i.val / 2 = j.val / 2 then
          pauli k ⟨i.val % 2, Nat.mod_lt _ (by norm_num)⟩ ⟨j.val % 2, Nat.mod_lt _ (by norm_num)⟩
          else 0) = 0 := by
        rw [if_neg]
        intro hcond
        exact absurd hcond.2.1 (Nat.not_lt_of_ge hcon)
      exact hnz this
    -- gammaF is +1 on 0–7
    have gi : gammaF i i = 1 := by
      unfold gammaF
      simp [hi8]
    have gj : gammaF j j = 1 := by
      unfold gammaF
      simp [hj8]
    rw [gi, gj, one_mul, mul_one]

set_option maxHeartbeats 800000 in
/-- If genM is nonzero at (i,j), then i and j share the same Γ-eigenvalue.
    The match forces both indices into the same triplet group:
    {18-23} (Γ=-1) or {26-31} (Γ=+1). -/
theorem genM_gamma_eig (a : Fin 8) (i j : I32) (h : genM a i j ≠ 0) :
    gammaF i i = gammaF j j := by
  unfold genM at h
  -- h : (match tripletOf i.val, tripletOf j.val with ...) ≠ 0
  cases h1 : tripletOf i.val with
  | none =>
    simp [h1] at h
  | some tp1 =>
    cases h2 : tripletOf j.val with
    | none =>
      simp [h1, h2] at h
    | some tp2 =>
      obtain ⟨t1, p1⟩ := tp1
      obtain ⟨t2, p2⟩ := tp2
      simp only [h1, h2] at h
      -- h : (if t1 = t2 then gellMann a p1 p2 else 0) ≠ 0, so t1 = t2
      have heq : t1 = t2 := by
        by_contra hne
        simp [hne] at h
      -- Apply the eigenspace lemma to both (h1, h2 now have the unpacked form)
      have hi := tripletOf_eig i.val i.isLt t1 p1 h1
      have hj := tripletOf_eig j.val j.isLt t2 p2 h2
      have ht_eq : t1.val = t2.val := congrArg Fin.val heq
      rcases hi with ⟨hlt1, hi18, hi24⟩ | ⟨hle1, hi26, hi32⟩
      · rcases hj with ⟨hlt2, hj18, hj24⟩ | ⟨hle2, hj26, hj32⟩
        · -- Both in 18-23: Γ = -1
          unfold gammaF
          have g1 : ¬ i.val < 8 := by omega
          have g2 : ¬ i.val < 16 := by omega
          have g3 : ¬ j.val < 8 := by omega
          have g4 : ¬ j.val < 16 := by omega
          simp [g1, g2, hi24, g3, g4, hj24]
        · omega  -- t1<2 but t2≥2 contradicts t1=t2
      · rcases hj with ⟨hlt2, hj18, hj24⟩ | ⟨hle2, hj26, hj32⟩
        · omega  -- t1≥2 but t2<2 contradicts t1=t2
        · -- Both in 26-31: Γ = +1
          unfold gammaF
          have hg1 : ¬ i.val < 8 := by omega
          have hg2 : ¬ i.val < 16 := by omega
          have hg3 : ¬ i.val < 24 := by omega
          have hg4 : ¬ j.val < 8 := by omega
          have hg5 : ¬ j.val < 16 := by omega
          have hg6 : ¬ j.val < 24 := by omega
          simp [hg1, hg2, hg3, hg4, hg5, hg6]

/-- genM preserves Γ-eigenspaces (triplets within 16–23 and 24–31). -/
theorem genM_grading_even (a : Fin 8) : gammaF * genM a = genM a * gammaF := by
  ext i j
  simp only [Matrix.mul_apply]
  have hsum1 : ∑ l : I32, gammaF i l * genM a l j = gammaF i i * genM a i j := by
    rw [Finset.sum_eq_single i]
    · intro l _ hli
      rw [gammaF_apply_ne (Ne.symm hli), zero_mul]
    · intro hcon
      exact absurd (Finset.mem_univ i) hcon
  have hsum2 : ∑ l : I32, genM a i l * gammaF l j = genM a i j * gammaF j j := by
    rw [Finset.sum_eq_single j]
    · intro l _ hlj
      rw [gammaF_apply_ne hlj, mul_zero]
    · intro hcon
      exact absurd (Finset.mem_univ j) hcon
  rw [hsum1, hsum2]
  by_cases hnz : genM a i j = 0
  · rw [hnz, mul_zero, zero_mul]
  · have heig := genM_gamma_eig a i j hnz
    rw [heig, mul_comm]

/-- All 12 generators are grading-even. -/
theorem smGen_grading_even (g : Fin 12) :
    gammaF * smGen g = smGen g * gammaF := by
  fin_cases g
  · exact genC_grading_even
  · exact genH_grading_even 0
  · exact genH_grading_even 1
  · exact genH_grading_even 2
  · exact genM_grading_even 0
  · exact genM_grading_even 1
  · exact genM_grading_even 2
  · exact genM_grading_even 3
  · exact genM_grading_even 4
  · exact genM_grading_even 5
  · exact genM_grading_even 6
  · exact genM_grading_even 7

/-! ## Order-zero: [π(a), π°(b)] = 0 -/

/-- Opposite generator entries via the partner permutation. -/
theorem smGenOp_apply (g : Fin 12) (i j : I32) :
    smGenOp g i j = smGen g (partner j) (partner i) := by
  unfold smGenOp
  rw [UJ_conj_apply]
  rfl

/-- genH support: nonzero entries force both indices into 0–7. -/
theorem genH_supp (k : Fin 3) (i j : I32) (h : genH k i j ≠ 0) :
    i.val < 8 ∧ j.val < 8 := by
  unfold genH at h
  simp only at h
  -- h : (if c then X else 0) ≠ 0, so c must hold
  have hc : i.val < 8 ∧ j.val < 8 ∧ i.val / 2 = j.val / 2 := by
    by_contra hnc
    rw [if_neg hnc] at h
    exact h rfl
  exact ⟨hc.1, hc.2.1⟩

/-- genH support with block structure. -/
theorem genH_supp_block (k : Fin 3) (i j : I32) (h : genH k i j ≠ 0) :
    i.val < 8 ∧ j.val < 8 ∧ i.val / 2 = j.val / 2 := by
  unfold genH at h
  simp only at h
  by_contra hnc
  rw [if_neg hnc] at h
  exact h rfl

/-- partner maps 16–23 to 0–7. -/
theorem partner_mem_16_24 (i : I32) (h : (partner i).val < 8) :
    16 ≤ i.val ∧ i.val < 24 := by
  rw [partner_val_eq] at h
  split_ifs at h with h1
  · omega
  · omega

/-- Disjoint product: if A's column support and B's row support are disjoint, A*B = 0. -/
theorem disjoint_mul_zero {A B : Matrix I32 I32 ℂ} (P : I32 → Prop)
    (hA : ∀ i k, A i k ≠ 0 → P k) (hB : ∀ k j, B k j ≠ 0 → ¬ P k) :
    A * B = 0 := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.zero_apply]
  apply Finset.sum_eq_zero
  intro k _
  by_cases hak : A i k = 0
  · rw [hak, zero_mul]
  · have hPk := hA i k hak
    by_cases hbk : B k j = 0
    · rw [hbk, mul_zero]
    · exact absurd hPk (hB k j hbk)

/-- UJ-conjugated H generator is supported on 16–23. -/
theorem UJ_genH_transpose_UJ_supp (k : Fin 3) (i j : I32)
    (h : (UJ * (genH k).transpose * UJ) i j ≠ 0) :
    16 ≤ i.val ∧ i.val < 24 ∧ 16 ≤ j.val ∧ j.val < 24 := by
  rw [UJ_conj_apply] at h
  simp only [Matrix.transpose_apply] at h
  -- h : genH k (partner j) (partner i) ≠ 0
  have hsupp := genH_supp k (partner j) (partner i) h
  have hi := partner_mem_16_24 i hsupp.2
  have hj := partner_mem_16_24 j hsupp.1
  exact ⟨hi.1, hi.2, hj.1, hj.2⟩

/-- Order-zero for (H, H°): disjoint supports 0–7 vs 16–23. -/
theorem order_zero_H_H (k1 k2 : Fin 3) :
    genH k1 * (UJ * (genH k2).transpose * UJ)
      - (UJ * (genH k2).transpose * UJ) * genH k1 = 0 := by
  have hAB : genH k1 * (UJ * (genH k2).transpose * UJ) = 0 := by
    apply disjoint_mul_zero (fun i => i.val < 8)
    · intro i k hik
      exact (genH_supp k1 i k hik).2
    · intro k j hkj
      have hsupp := UJ_genH_transpose_UJ_supp k2 k j hkj
      omega
  have hBA : (UJ * (genH k2).transpose * UJ) * genH k1 = 0 := by
    apply disjoint_mul_zero (fun i => 16 ≤ i.val)
    · intro i k hik
      exact (UJ_genH_transpose_UJ_supp k2 i k hik).2.2.1
    · intro k j hkj
      have hsupp := genH_supp k1 k j hkj
      omega
  rw [hAB, hBA, sub_zero]

/-- genM support: nonzero entries force both indices into the triplet ranges. -/
theorem genM_supp (a : Fin 8) (i j : I32) (h : genM a i j ≠ 0) :
    ((18 ≤ i.val ∧ i.val < 24) ∨ (26 ≤ i.val ∧ i.val < 32)) ∧
    ((18 ≤ j.val ∧ j.val < 24) ∨ (26 ≤ j.val ∧ j.val < 32)) := by
  unfold genM at h
  cases h1 : tripletOf i.val with
  | none => simp [h1] at h
  | some tp1 =>
    cases h2 : tripletOf j.val with
    | none => simp [h1, h2] at h
    | some tp2 =>
      obtain ⟨t1, p1⟩ := tp1
      obtain ⟨t2, p2⟩ := tp2
      simp only [h1, h2] at h
      have heq : t1 = t2 := by
        by_contra hne
        simp [hne] at h
      have hi := tripletOf_eig i.val i.isLt t1 p1 h1
      have hj := tripletOf_eig j.val j.isLt t2 p2 h2
      constructor
      · rcases hi with ⟨_, h1a, h1b⟩ | ⟨_, h2a, h2b⟩
        · left; exact ⟨h1a, h1b⟩
        · right; exact ⟨h2a, h2b⟩
      · rcases hj with ⟨_, h1a, h1b⟩ | ⟨_, h2a, h2b⟩
        · left; exact ⟨h1a, h1b⟩
        · right; exact ⟨h2a, h2b⟩

/-- partner maps 18–23 back to 2–7, and 26–31 back to 10–15. -/
theorem partner_mem_particle_triplet (i : I32) :
    (18 ≤ (partner i).val ∧ (partner i).val < 24 → 2 ≤ i.val ∧ i.val < 8) ∧
    (26 ≤ (partner i).val ∧ (partner i).val < 32 → 10 ≤ i.val ∧ i.val < 16) := by
  rw [partner_val_eq]
  split_ifs with h1 <;> constructor <;> intro h <;> omega

/-- UJ-conjugated M generator is supported on particle triplets (2–7, 10–15). -/
theorem UJ_genM_transpose_UJ_supp (a : Fin 8) (i j : I32)
    (h : (UJ * (genM a).transpose * UJ) i j ≠ 0) :
    ((2 ≤ i.val ∧ i.val < 8) ∨ (10 ≤ i.val ∧ i.val < 16)) ∧
    ((2 ≤ j.val ∧ j.val < 8) ∨ (10 ≤ j.val ∧ j.val < 16)) := by
  rw [UJ_conj_apply] at h
  simp only [Matrix.transpose_apply] at h
  -- h : genM a (partner j) (partner i) ≠ 0
  have hsupp := genM_supp a (partner j) (partner i) h
  constructor
  · rcases hsupp.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left; exact (partner_mem_particle_triplet i).1 ⟨h1, h2⟩
    · right; exact (partner_mem_particle_triplet i).2 ⟨h1, h2⟩
  · rcases hsupp.1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left; exact (partner_mem_particle_triplet j).1 ⟨h1, h2⟩
    · right; exact (partner_mem_particle_triplet j).2 ⟨h1, h2⟩

/-- Order-zero for (M, M°): disjoint supports. -/
theorem order_zero_M_M (a1 a2 : Fin 8) :
    genM a1 * (UJ * (genM a2).transpose * UJ)
      - (UJ * (genM a2).transpose * UJ) * genM a1 = 0 := by
  -- M supported on 18–23, 26–31; M° on 2–7, 10–15; disjoint.
  have hAB : genM a1 * (UJ * (genM a2).transpose * UJ) = 0 := by
    apply disjoint_mul_zero (fun i => 18 ≤ i.val)
    · intro i k hik
      have hsupp := genM_supp a1 i k hik
      rcases hsupp.2 with ⟨h1, _⟩ | ⟨h1, _⟩ <;> omega
    · intro k j hkj
      have hsupp := UJ_genM_transpose_UJ_supp a2 k j hkj
      rcases hsupp.1 with ⟨_, h2⟩ | ⟨_, h2⟩ <;> omega
  have hBA : (UJ * (genM a2).transpose * UJ) * genM a1 = 0 := by
    apply disjoint_mul_zero (fun i => i.val < 18)
    · intro i k hik
      have hsupp := UJ_genM_transpose_UJ_supp a2 i k hik
      rcases hsupp.1 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
    · intro k j hkj
      have hsupp := genM_supp a1 k j hkj
      rcases hsupp.1 with ⟨h1, _⟩ | ⟨h1, _⟩ <;> omega
  rw [hAB, hBA, sub_zero]

/-- genC is diagonal. -/
theorem genC_diag (i j : I32) (h : genC i j ≠ 0) : i = j := by
  unfold genC at h
  simp only at h
  by_contra hne
  rw [if_neg hne] at h
  exact h rfl

/-- Diagonal matrices commute. -/
theorem diag_diag_zero {D1 D2 : Matrix I32 I32 ℂ}
    (h1 : ∀ i j, D1 i j ≠ 0 → i = j) (h2 : ∀ i j, D2 i j ≠ 0 → i = j) :
    D1 * D2 = D2 * D1 := by
  ext i j
  simp only [Matrix.mul_apply]
  -- Each sum has at most one nonzero term (k = i for the first, k = i for the second)
  have key1 : ∀ k ∈ (Finset.univ : Finset I32), k ≠ i → D1 i k * D2 k j = 0 := by
    intro k _ hki
    by_cases hD1 : D1 i k = 0
    · rw [hD1, zero_mul]
    · exact absurd (h1 i k hD1).symm hki
  have key2 : ∀ k ∈ (Finset.univ : Finset I32), k ≠ i → D2 i k * D1 k j = 0 := by
    intro k _ hki
    by_cases hD2 : D2 i k = 0
    · rw [hD2, zero_mul]
    · exact absurd (h2 i k hD2).symm hki
  have e1 : ∑ k : I32, D1 i k * D2 k j = D1 i i * D2 i j :=
    Finset.sum_eq_single i key1 (fun hcon => absurd (Finset.mem_univ i) hcon)
  have e2 : ∑ k : I32, D2 i k * D1 k j = D2 i i * D1 i j :=
    Finset.sum_eq_single i key2 (fun hcon => absurd (Finset.mem_univ i) hcon)
  rw [e1, e2]
  by_cases hij : i = j
  · subst hij; ring
  · -- i ≠ j: D2 i j = 0 and D1 i j = 0
    have hD2 : D2 i j = 0 := by
      by_contra hne; exact hij (h2 i j hne)
    have hD1 : D1 i j = 0 := by
      by_contra hne; exact hij (h1 i j hne)
    simp [hD1, hD2]

/-- partner is injective. -/
theorem partner_injective : Function.Injective partner := by
  intro a b hab
  have hval : (partner a).val = (partner b).val := congrArg Fin.val hab
  rw [partner_val_eq, partner_val_eq] at hval
  rw [Fin.ext_iff]
  split_ifs at hval with h1 h2 <;> omega

/-- smGenOp 0 (C opposite) is diagonal. -/
theorem smGenOp_C_diag (i j : I32) (h : (UJ * genC.transpose * UJ) i j ≠ 0) : i = j := by
  rw [UJ_conj_apply] at h
  simp only [Matrix.transpose_apply] at h
  -- h : genC (partner j) (partner i) ≠ 0, so partner j = partner i
  have hp : partner j = partner i := genC_diag (partner j) (partner i) h
  exact (partner_injective hp).symm

/-- Order-zero for (C, C°): both diagonal. -/
theorem order_zero_C_C :
    genC * (UJ * genC.transpose * UJ) - (UJ * genC.transpose * UJ) * genC = 0 := by
  rw [diag_diag_zero genC_diag smGenOp_C_diag, sub_self]

/-- A diagonal D commutes with B if D is constant on B's support. -/
theorem diag_mul_comm_of_const_on_supp {D B : Matrix I32 I32 ℂ}
    (hD : ∀ i j, D i j ≠ 0 → i = j)
    (hconst : ∀ i j, B i j ≠ 0 → D i i = D j j) :
    D * B - B * D = 0 := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.sub_apply, Matrix.zero_apply]
  have key : ∀ k ∈ (Finset.univ : Finset I32), k ≠ i → D i k * B k j = 0 := by
    intro k _ hki
    by_cases hDk : D i k = 0
    · rw [hDk, zero_mul]
    · exact absurd (hD i k hDk).symm hki
  have e1 : ∑ k : I32, D i k * B k j = D i i * B i j :=
    Finset.sum_eq_single i key (fun hcon => absurd (Finset.mem_univ i) hcon)
  -- (B*D) i j = B i j * D j j (D diagonal on the right)
  have key2 : ∀ k ∈ (Finset.univ : Finset I32), k ≠ j → B i k * D k j = 0 := by
    intro k _ hkj
    by_cases hDk : D k j = 0
    · rw [hDk, mul_zero]
    · exact absurd (hD k j hDk) hkj
  have e2 : ∑ k : I32, B i k * D k j = B i j * D j j :=
    Finset.sum_eq_single j key2 (fun hcon => absurd (Finset.mem_univ j) hcon)
  rw [e1, e2]
  by_cases hBij : B i j = 0
  · simp [hBij]
  · rw [hconst i j hBij]; ring

/-- genC diagonal value: I on 8–15, 16,17,24,25; 0 otherwise. -/
theorem genC_diag_val (i : I32) : genC i i =
    if 8 ≤ i.val ∧ i.val < 16 then Complex.I
    else if i.val = 16 ∨ i.val = 17 ∨ i.val = 24 ∨ i.val = 25 then Complex.I
    else 0 := by
  unfold genC
  simp

/-- For (C, H°): H° forces i,j into the same (16,17),(18,19),... pair, where genC is constant. -/
theorem order_zero_C_H (k : Fin 3) :
    genC * (UJ * (genH k).transpose * UJ) - (UJ * (genH k).transpose * UJ) * genC = 0 := by
  apply diag_mul_comm_of_const_on_supp genC_diag
  intro i j hij
  -- hij : (UJ * (genH k).transpose * UJ) i j ≠ 0
  rw [UJ_conj_apply] at hij
  simp only [Matrix.transpose_apply] at hij
  -- hij : genH k (partner j) (partner i) ≠ 0
  have hsupp := genH_supp_block k (partner j) (partner i) hij
  have hi16 := partner_mem_16_24 i hsupp.2.1
  have hj16 := partner_mem_16_24 j hsupp.1
  -- Same doublet in 0–7, so same pair in 16–23
  have hblock : i.val / 2 = j.val / 2 := by
    have hp_i := partner_val_eq i
    have hp_j := partner_val_eq j
    rw [if_neg (by omega : ¬ i.val < 16)] at hp_i
    rw [if_neg (by omega : ¬ j.val < 16)] at hp_j
    -- hp_i : (partner i).val = i.val - 16, hp_j : (partner j).val = j.val - 16
    -- hsupp.2.2 : (partner j).val / 2 = (partner i).val / 2
    omega
  -- genC i i = genC j j because they're in the same pair
  rw [genC_diag_val, genC_diag_val]
  -- Both are in 16–23, so the first if (8 ≤ · < 16) is false
  have hi8 : ¬ (8 ≤ i.val ∧ i.val < 16) := by omega
  have hj8 : ¬ (8 ≤ j.val ∧ j.val < 16) := by omega
  rw [if_neg hi8, if_neg hj8]
  -- Now show (i.val = 16 ∨ ...) ↔ (j.val = 16 ∨ ...) using hblock
  by_cases hi1617 : i.val = 16 ∨ i.val = 17 ∨ i.val = 24 ∨ i.val = 25
  · -- i.val ∈ {16,17} (can't be 24,25 since i.val < 24)
    have hi16 : i.val = 16 ∨ i.val = 17 := by omega
    have hj1617 : j.val = 16 ∨ j.val = 17 ∨ j.val = 24 ∨ j.val = 25 := by omega
    rw [if_pos hi1617, if_pos hj1617]
  · have hj1617 : ¬ (j.val = 16 ∨ j.val = 17 ∨ j.val = 24 ∨ j.val = 25) := by
      intro hcon
      apply hi1617
      rcases hcon with h|h|h|h <;> omega
    rw [if_neg hi1617, if_neg hj1617]

/-- C° diagonal value at i: genC (partner i) (partner i). -/
theorem smGenOp_C_diag_val (i : I32) : (UJ * genC.transpose * UJ) i i =
    genC (partner i) (partner i) := by
  rw [UJ_conj_apply]
  simp only [Matrix.transpose_apply]

/-- For (H, C°): H doublets map via partner to (16,17),(18,19),... where genC is constant. -/
theorem order_zero_H_C (k : Fin 3) :
    genH k * (UJ * genC.transpose * UJ) - (UJ * genC.transpose * UJ) * genH k = 0 := by
  -- H is not diagonal, C° is diagonal. Use the symmetric version.
  -- (A*B - B*A) = -(B*A - A*B), so prove B*A - A*B = 0 then negate.
  have h : (UJ * genC.transpose * UJ) * genH k - genH k * (UJ * genC.transpose * UJ) = 0 := by
    apply diag_mul_comm_of_const_on_supp smGenOp_C_diag
    intro i j hij
    -- hij : genH k i j ≠ 0, so i,j in same doublet in 0–7
    have hsupp := genH_supp_block k i j hij
    -- C° i i = genC (partner i) (partner i), C° j j = genC (partner j) (partner j)
    rw [smGenOp_C_diag_val, smGenOp_C_diag_val, genC_diag_val, genC_diag_val]
    -- partner i, partner j ∈ 16–23; (partner i).val = i.val + 16
    have hp_i := partner_val_eq i
    have hp_j := partner_val_eq j
    rw [if_pos (by omega : i.val < 16)] at hp_i
    rw [if_pos (by omega : j.val < 16)] at hp_j
    -- (partner i).val = i.val + 16 ∈ 16–23, so genC uses the 16,17 case
    have hi16 : (partner i).val = i.val + 16 := hp_i
    have hj16 : (partner j).val = j.val + 16 := hp_j
    -- i.val < 8, so (partner i).val < 24, and 8 ≤ (partner i).val is false for the first if
    -- Actually (partner i).val = i.val + 16, with i.val < 8, so 16 ≤ (partner i).val < 24
    -- genC_diag_val: if 8 ≤ · < 16 then I else if · = 16 ∨ · = 17 ∨ · = 24 ∨ · = 25 then I else 0
    -- Since 16 ≤ (partner i).val < 24, first if is false. Second if: (partner i).val = 16 ∨ = 17
    -- (partner i).val = 16 ↔ i.val = 0. (partner i).val = 17 ↔ i.val = 1.
    -- i.val/2 = j.val/2 and i.val,j.val < 8 → (i.val = 0 ∨ i.val = 1) ↔ (j.val = 0 ∨ j.val = 1)
    have h8i : ¬ (8 ≤ (partner i).val ∧ (partner i).val < 16) := by omega
    have h8j : ¬ (8 ≤ (partner j).val ∧ (partner j).val < 16) := by omega
    rw [if_neg h8i, if_neg h8j]
    by_cases hi01 : (partner i).val = 16 ∨ (partner i).val = 17 ∨ (partner i).val = 24 ∨ (partner i).val = 25
    · have hi01' : i.val = 0 ∨ i.val = 1 := by omega
      have hj01 : (partner j).val = 16 ∨ (partner j).val = 17 ∨ (partner j).val = 24 ∨ (partner j).val = 25 := by omega
      rw [if_pos hi01, if_pos hj01]
    · have hj01 : ¬ ((partner j).val = 16 ∨ (partner j).val = 17 ∨ (partner j).val = 24 ∨ (partner j).val = 25) := by
        intro hcon
        apply hi01
        omega
      rw [if_neg hi01, if_neg hj01]
  -- h : C°*H - H*C° = 0, so H*C° - C°*H = 0
  have hneg : genH k * (UJ * genC.transpose * UJ) - (UJ * genC.transpose * UJ) * genH k
      = -((UJ * genC.transpose * UJ) * genH k - genH k * (UJ * genC.transpose * UJ)) := by
    simp [sub_eq_add_neg, add_comm]
  rw [hneg, h, neg_zero]

/-- M° block structure: nonzero entries force i,j into the same
    particle-triplet range (both 2–7 or both 10–15). -/
theorem UJ_genM_block (a : Fin 8) (i j : I32)
    (h : (UJ * (genM a).transpose * UJ) i j ≠ 0) :
    (2 ≤ i.val ∧ i.val < 8 ∧ 2 ≤ j.val ∧ j.val < 8) ∨
    (10 ≤ i.val ∧ i.val < 16 ∧ 10 ≤ j.val ∧ j.val < 16) := by
  rw [UJ_conj_apply] at h
  simp only [Matrix.transpose_apply] at h
  -- h : genM a (partner j) (partner i) ≠ 0
  unfold genM at h
  cases h1 : tripletOf (partner j).val with
  | none => rw [h1] at h; simp at h
  | some tp1 =>
    cases h2 : tripletOf (partner i).val with
    | none => rw [h1, h2] at h; simp at h
    | some tp2 =>
      obtain ⟨t1, p1⟩ := tp1
      obtain ⟨t2, p2⟩ := tp2
      simp only [h1, h2] at h
      have heq : t1 = t2 := by
        by_contra hne
        simp [hne] at h
      subst heq
      -- Now both in triplet t1
      have hi := tripletOf_eig (partner i).val (partner i).isLt t1 p2 h2
      have hj := tripletOf_eig (partner j).val (partner j).isLt t1 p1 h1
      by_cases ht : t1.val < 2
      · -- t1 ∈ {0,1}: partner values in 18–23, so i,j ∈ 2–7
        left
        have hi1823 : 18 ≤ (partner i).val ∧ (partner i).val < 24 := by
          rcases hi with ⟨_, h1a, h1b⟩ | ⟨hcon, _, _⟩
          · exact ⟨h1a, h1b⟩
          · omega
        have hj1823 : 18 ≤ (partner j).val ∧ (partner j).val < 24 := by
          rcases hj with ⟨_, h1a, h1b⟩ | ⟨hcon, _, _⟩
          · exact ⟨h1a, h1b⟩
          · omega
        have pi := (partner_mem_particle_triplet i).1 hi1823
        have pj := (partner_mem_particle_triplet j).1 hj1823
        exact ⟨pi.1, pi.2, pj.1, pj.2⟩
      · -- t1 ∈ {2,3}: partner values in 26–31, so i,j ∈ 10–15
        right
        have hi2631 : 26 ≤ (partner i).val ∧ (partner i).val < 32 := by
          rcases hi with ⟨hcon, _, _⟩ | ⟨_, h2a, h2b⟩
          · omega
          · exact ⟨h2a, h2b⟩
        have hj2631 : 26 ≤ (partner j).val ∧ (partner j).val < 32 := by
          rcases hj with ⟨hcon, _, _⟩ | ⟨_, h2a, h2b⟩
          · omega
          · exact ⟨h2a, h2b⟩
        have pi := (partner_mem_particle_triplet i).2 hi2631
        have pj := (partner_mem_particle_triplet j).2 hj2631
        exact ⟨pi.1, pi.2, pj.1, pj.2⟩

/-- C/M° pairs: genC is diagonal; M° blocks from UJ_genM_block keep (i,j)
    in the same range (both 2–7 where genC=0, or both 10–15 where genC=I). -/
theorem order_zero_C_M (a : Fin 8) :
    genC * (UJ * (genM a).transpose * UJ) - (UJ * (genM a).transpose * UJ) * genC = 0 := by
  apply diag_mul_comm_of_const_on_supp genC_diag
  intro i j hij
  rcases UJ_genM_block a i j hij with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
  · -- both in 2–7: genC = 0
    rw [genC_diag_val, genC_diag_val]
    have hi8 : ¬ (8 ≤ i.val ∧ i.val < 16) := by omega
    have hj8 : ¬ (8 ≤ j.val ∧ j.val < 16) := by omega
    have hi16 : ¬ (i.val = 16 ∨ i.val = 17 ∨ i.val = 24 ∨ i.val = 25) := by omega
    have hj16 : ¬ (j.val = 16 ∨ j.val = 17 ∨ j.val = 24 ∨ j.val = 25) := by omega
    rw [if_neg hi8, if_neg hj8, if_neg hi16, if_neg hj16]
  · -- both in 10–15: genC = I
    rw [genC_diag_val, genC_diag_val]
    have hi8 : (8 ≤ i.val ∧ i.val < 16) := by omega
    have hj8 : (8 ≤ j.val ∧ j.val < 16) := by omega
    rw [if_pos hi8, if_pos hj8]

/-- M/C° pairs: genM support is 18–23 or 26–31; C° is diagonal with
    C°(i,i) = genC(partner i, partner i), which is 0 on 18–23 (partner in 2–7)
    and I on 26–31 (partner in 10–15). Constant on each triplet. -/
theorem order_zero_M_C (a : Fin 8) :
    genM a * (UJ * genC.transpose * UJ) - (UJ * genC.transpose * UJ) * genM a = 0 := by
  have hCdiag : ∀ i j : I32, (UJ * genC.transpose * UJ) i j ≠ 0 → i = j := smGenOp_C_diag
  -- It suffices to show C° * genM - genM * C° = 0, then negate
  suffices h : (UJ * genC.transpose * UJ) * genM a - genM a * (UJ * genC.transpose * UJ) = 0 by
    have heq : genM a * (UJ * genC.transpose * UJ) - (UJ * genC.transpose * UJ) * genM a
      = -((UJ * genC.transpose * UJ) * genM a - genM a * (UJ * genC.transpose * UJ)) := by
      simp [sub_eq_add_neg, add_comm]
    rw [heq, h, neg_zero]
  apply diag_mul_comm_of_const_on_supp hCdiag
  intro i j hij
  -- hij : genM a i j ≠ 0; show C° i i = C° j j
  have hCi : (UJ * genC.transpose * UJ) i i = genC (partner i) (partner i) := smGenOp_C_diag_val i
  have hCj : (UJ * genC.transpose * UJ) j j = genC (partner j) (partner j) := smGenOp_C_diag_val j
  rw [hCi, hCj]
  unfold genM at hij
  cases h1 : tripletOf i.val with
  | none => rw [h1] at hij; simp at hij
  | some tp1 =>
    cases h2 : tripletOf j.val with
    | none => rw [h1, h2] at hij; simp at hij
    | some tp2 =>
      obtain ⟨t1, p1⟩ := tp1
      obtain ⟨t2, p2⟩ := tp2
      simp only [h1, h2] at hij
      have heq : t1 = t2 := by
        by_contra hne
        simp [hne] at hij
      subst heq
      have hi := tripletOf_eig i.val i.isLt t1 p1 h1
      have hj := tripletOf_eig j.val j.isLt t1 p2 h2
      by_cases ht : t1.val < 2
      · -- i,j ∈ 18–23; partners in 2–7 where genC = 0
        have hi18 : 18 ≤ i.val ∧ i.val < 24 := by
          rcases hi with ⟨_, h1a, h1b⟩ | ⟨hcon, _, _⟩
          · exact ⟨h1a, h1b⟩
          · omega
        have hj18 : 18 ≤ j.val ∧ j.val < 24 := by
          rcases hj with ⟨_, h1a, h1b⟩ | ⟨hcon, _, _⟩
          · exact ⟨h1a, h1b⟩
          · omega
        have hni : ¬ i.val < 16 := by omega
        have hnj : ¬ j.val < 16 := by omega
        have hpi : (partner i).val = i.val - 16 := by rw [partner_val_eq]; simp [hni]
        have hpj : (partner j).val = j.val - 16 := by rw [partner_val_eq]; simp [hnj]
        rw [genC_diag_val, genC_diag_val]
        have h1 : ¬ (8 ≤ (partner i).val ∧ (partner i).val < 16) := by omega
        have h2 : ¬ (8 ≤ (partner j).val ∧ (partner j).val < 16) := by omega
        have h3 : ¬ ((partner i).val = 16 ∨ (partner i).val = 17 ∨ (partner i).val = 24 ∨ (partner i).val = 25) := by omega
        have h4 : ¬ ((partner j).val = 16 ∨ (partner j).val = 17 ∨ (partner j).val = 24 ∨ (partner j).val = 25) := by omega
        rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4]
      · -- i,j ∈ 26–31; partners in 10–15 where genC = I
        have hi26 : 26 ≤ i.val ∧ i.val < 32 := by
          rcases hi with ⟨hcon, _, _⟩ | ⟨_, h2a, h2b⟩
          · omega
          · exact ⟨h2a, h2b⟩
        have hj26 : 26 ≤ j.val ∧ j.val < 32 := by
          rcases hj with ⟨hcon, _, _⟩ | ⟨_, h2a, h2b⟩
          · omega
          · exact ⟨h2a, h2b⟩
        have hni : ¬ i.val < 16 := by omega
        have hnj : ¬ j.val < 16 := by omega
        have hpi : (partner i).val = i.val - 16 := by rw [partner_val_eq]; simp [hni]
        have hpj : (partner j).val = j.val - 16 := by rw [partner_val_eq]; simp [hnj]
        rw [genC_diag_val, genC_diag_val]
        have h1 : (8 ≤ (partner i).val ∧ (partner i).val < 16) := by omega
        have h2 : (8 ≤ (partner j).val ∧ (partner j).val < 16) := by omega
        rw [if_pos h1, if_pos h2]

/-- Colour index for i in 2-7: c = (i.val - 2) / 2 in {0,1,2}.
    H acts as Pauli on flavour; M-conj acts as Gell-Mann on colour. -/
def colour27 (i : I32) (_h : 2 ≤ i.val ∧ i.val < 8) : Fin 3 := ⟨(i.val - 2) / 2, by omega⟩

/-- Flavour index for i in 2-7: f = (i.val - 2) % 2 in {0,1}. -/
def flavour27 (i : I32) (_h : 2 ≤ i.val ∧ i.val < 8) : Fin 2 := ⟨(i.val - 2) % 2, by omega⟩

/-- In (H * M°) i j with i,j in 2-7, only t in 2-7 contributes.
    H_it != 0 forces t in 0-7; M°_tj != 0 forces t in (2-7) U (10-15).
    Intersection is 2-7. Moreover H on 0-1 pairs doesn't meet M° support. -/
theorem HM_sum_restrict (k : Fin 3) (a : Fin 8) (i j t : I32)
    (hi : 2 ≤ i.val ∧ i.val < 8) (hj : 2 ≤ j.val ∧ j.val < 8)
    (ht : ¬ (2 ≤ t.val ∧ t.val < 8)) :
    genH k i t * (UJ * (genM a).transpose * UJ) t j = 0 := by
  by_cases hHt : genH k i t = 0
  · rw [hHt, zero_mul]
  · -- genH k i t != 0, so t in 0-7 with i.val/2 = t.val/2
    have hsupp := genH_supp k i t hHt
    -- i in 2-7, t in 0-7, i.val/2 = t.val/2 forces t in 2-7. Contradiction.
    unfold genH at hHt
    simp only at hHt
    have hc : i.val < 8 ∧ t.val < 8 ∧ i.val / 2 = t.val / 2 := by
      by_contra hnc
      rw [if_neg hnc] at hHt
      exact hHt rfl
    -- i in 2-7 => i.val/2 in {1,2,3}; t.val/2 = i.val/2 and t.val < 8 => t in 2-7
    have : 2 ≤ t.val ∧ t.val < 8 := by omega
    exact absurd this ht

/-- H on 2-7 acts as Pauli on flavour, identity on colour.
    For i,j in 2-7: genH k i j = if colour matches then pauli_k(flavours) else 0. -/
theorem genH_eq_27 (k : Fin 3) (i j : I32) (hi : 2 ≤ i.val ∧ i.val < 8)
    (hj : 2 ≤ j.val ∧ j.val < 8) :
    genH k i j =
      if (i.val - 2) / 2 = (j.val - 2) / 2 then
        pauli k ⟨i.val % 2, by omega⟩ ⟨j.val % 2, by omega⟩
      else 0 := by
  unfold genH
  simp only
  have e1 : i.val / 2 = (i.val - 2) / 2 + 1 := by omega
  have e2 : j.val / 2 = (j.val - 2) / 2 + 1 := by omega
  rw [e1, e2]
  by_cases hc : (i.val - 2) / 2 = (j.val - 2) / 2
  · rw [if_pos hc]
    have hpos : i.val < 8 ∧ j.val < 8 ∧ (i.val - 2) / 2 + 1 = (j.val - 2) / 2 + 1 := by
      refine ⟨hi.2, hj.2, ?_⟩
      omega
    rw [if_pos hpos]
  · rw [if_neg hc]
    rw [if_neg]
    intro hcon
    apply hc
    omega

/-- tripletOf on 18-23: even -> (0, (n-18)/2), odd -> (1, (n-18)/2). -/
theorem tripletOf_18_23 (n : Nat) (h1 : 18 ≤ n) (h2 : n < 24) :
    tripletOf n = some (⟨n % 2, by omega⟩, ⟨(n - 18) / 2, by omega⟩) := by
  interval_cases n <;> rfl

/-- M-conj on 2-7 acts as Gell-Mann on colour, identity on flavour.
    For i,j in 2-7: (M°_a) i j = if flavours match then gellMann_a(colours) else 0.
    Note the transpose: gellMann_a(colour_j, colour_i). -/
theorem genMconj_eq_27 (a : Fin 8) (i j : I32) (hi : 2 ≤ i.val ∧ i.val < 8)
    (hj : 2 ≤ j.val ∧ j.val < 8) :
    (UJ * (genM a).transpose * UJ) i j =
      if (i.val - 2) % 2 = (j.val - 2) % 2 then
        gellMann a ⟨(j.val - 2) / 2, by omega⟩ ⟨(i.val - 2) / 2, by omega⟩
      else 0 := by
  rw [UJ_conj_apply, Matrix.transpose_apply]
  have hpj : (partner j).val = j.val + 16 := by
    rw [partner_val_eq, if_pos (by omega : j.val < 16)]
  have hpi : (partner i).val = i.val + 16 := by
    rw [partner_val_eq, if_pos (by omega : i.val < 16)]
  have htj : tripletOf (partner j).val =
      some (⟨(j.val + 16) % 2, by omega⟩, ⟨(j.val + 16 - 18) / 2, by omega⟩) := by
    rw [hpj]; exact tripletOf_18_23 _ (by omega) (by omega)
  have hti : tripletOf (partner i).val =
      some (⟨(i.val + 16) % 2, by omega⟩, ⟨(i.val + 16 - 18) / 2, by omega⟩) := by
    rw [hpi]; exact tripletOf_18_23 _ (by omega) (by omega)
  show genM a (partner j) (partner i) = _
  unfold genM
  rw [htj, hti]
  simp only [Fin.mk.injEq]
  -- Goal: if (j.val+16)%2 = (i.val+16)%2 then gellMann ... else 0 = if parity then ... else 0
  have e1 : (j.val + 16) % 2 = j.val % 2 := by omega
  have e2 : (j.val + 16 - 18) / 2 = (j.val - 2) / 2 := by omega
  have e4 : (i.val + 16 - 18) / 2 = (i.val - 2) / 2 := by omega
  rw [e1]
  have e3 : (i.val + 16) % 2 = i.val % 2 := by omega
  rw [e3]
  -- Now: if j.val%2 = i.val%2 then gellMann a ⟨(j.val+16-18)/2,_⟩ ⟨(i.val+16-18)/2,_⟩ else 0
  by_cases hc : j.val % 2 = i.val % 2
  · rw [if_pos hc]
    have hc27 : (i.val - 2) % 2 = (j.val - 2) % 2 := by omega
    rw [if_pos hc27]
    have g1 : (⟨(j.val + 16 - 18) / 2, by omega⟩ : Fin 3) = ⟨(j.val - 2) / 2, by omega⟩ := by
      apply Fin.ext; show (j.val + 16 - 18) / 2 = (j.val - 2) / 2; exact e2
    have g2 : (⟨(i.val + 16 - 18) / 2, by omega⟩ : Fin 3) = ⟨(i.val - 2) / 2, by omega⟩ := by
      apply Fin.ext; show (i.val + 16 - 18) / 2 = (i.val - 2) / 2; exact e4
    rw [g1, g2]
  · rw [if_neg hc]
    have hc27 : ¬ ((i.val - 2) % 2 = (j.val - 2) % 2) := by omega
    rw [if_neg hc27]

/-- Helper: for n in 2-7, n = 2 + 2*((n-2)/2) + ((n-2)%2). -/
theorem val_eq_27 (n : Nat) (h1 : 2 ≤ n) (h2 : n < 8) :
    n = 2 + 2 * ((n - 2) / 2) + ((n - 2) % 2) := by omega

/-- The index t0 with colour of i and flavour of j. -/
def t0_HM (i j : I32) : I32 := ⟨2 + 2 * ((i.val - 2) / 2) + ((j.val - 2) % 2), by
  have hi := i.isLt; have hj := j.isLt
  -- Need bounds on (i.val-2)/2 and (j.val-2)%2; omega with i.val<32, j.val<32
  omega⟩

/-- Order-zero H/M: [genH k, M°_a] = 0.
    Proof by support analysis and the tensor-product structure on 2-7. -/
theorem order_zero_H_M (k : Fin 3) (a : Fin 8) :
    genH k * (UJ * (genM a).transpose * UJ)
      - (UJ * (genM a).transpose * UJ) * genH k = 0 := by
  -- It suffices to show the two products are equal entrywise.
  suffices h : genH k * (UJ * (genM a).transpose * UJ)
      = (UJ * (genM a).transpose * UJ) * genH k by
    rw [h, sub_self]
  ext i j
  rw [Matrix.mul_apply, Matrix.mul_apply]
  -- Key: both sums reduce to the same value.
  -- We show Σ_t H_it M°_tj = Σ_t M°_it H_tj by considering cases.
  by_cases hi : 2 ≤ i.val ∧ i.val < 8 <;> by_cases hj : 2 ≤ j.val ∧ j.val < 8
  · -- Case 1: i,j ∈ 2-7. Use the tensor product structure.
    -- The sum collapses to a single term; both sides equal pauli * gellMann.
    -- Define t0 with colour of i, flavour of j.
    have hiLt := i.isLt; have hjLt := j.isLt
    have hfj : (j.val - 2) % 2 < 2 := Nat.mod_lt _ (by omega)
    set t0 : I32 := ⟨2 + 2 * ((i.val - 2) / 2) + ((j.val - 2) % 2), by omega⟩ with ht0
    have ht0eq : t0.val = 2 + 2 * ((i.val - 2) / 2) + ((j.val - 2) % 2) := rfl
    have ht027 : 2 ≤ t0.val ∧ t0.val < 8 := by rw [ht0eq]; constructor <;> omega
    have ht0c : (t0.val - 2) / 2 = (i.val - 2) / 2 := by rw [ht0eq]; omega
    have ht0f : (t0.val - 2) % 2 = (j.val - 2) % 2 := by rw [ht0eq]; omega
    -- Sum1 = H_{i,t0} * M°_{t0,j} by single-term collapse
    have hsum1 : ∑ t, genH k i t * (UJ * (genM a).transpose * UJ) t j
        = genH k i t0 * (UJ * (genM a).transpose * UJ) t0 j := by
      apply Finset.sum_eq_single t0
      · intro t _ htne
        by_cases ht27 : 2 ≤ t.val ∧ t.val < 8
        · -- t ∈ 2-7, t ≠ t0: must differ in colour or flavour
          by_cases hc : (t.val - 2) / 2 = (i.val - 2) / 2
          · by_cases hf : (t.val - 2) % 2 = (j.val - 2) % 2
            · -- t has colour of i and flavour of j → t = t0, contradiction
              exfalso; apply htne
              apply Fin.ext; show t.val = t0.val
              have hteq : t.val = 2 + 2 * ((t.val - 2) / 2) + ((t.val - 2) % 2) := by omega
              rw [hteq, hc, hf]
            · -- flavour differs → M°_tj = 0
              have hM0 : (UJ * (genM a).transpose * UJ) t j = 0 := by
                rw [genMconj_eq_27 a t j ht27 hj, if_neg hf]
              rw [hM0, mul_zero]
          · -- colour differs → H_it = 0
            have hH0 : genH k i t = 0 := by
              rw [genH_eq_27 k i t hi ht27, if_neg (Ne.symm hc)]
            rw [hH0, zero_mul]
        · exact HM_sum_restrict k a i j t hi hj ht27
      · intro hcon; exact absurd (Finset.mem_univ _) hcon
    -- Simplify H_{i,t0} and M°_{t0,j} using the factorizations
    have hHt0 : genH k i t0
        = pauli k ⟨i.val % 2, by omega⟩ ⟨j.val % 2, by omega⟩ := by
      rw [genH_eq_27 k i t0 hi ht027, if_pos ht0c.symm]
      -- Need: ⟨i.val%2,_⟩ = ⟨i.val%2,_⟩ and ⟨t0.val%2,_⟩ = ⟨j.val%2,_⟩
      congr 1
      · -- t0.val % 2 = j.val % 2
        apply Fin.ext
        show t0.val % 2 = j.val % 2
        rw [ht0eq]
        -- (2 + 2*((i.val-2)/2) + ((j.val-2)%2)) % 2 = (j.val-2)%2 = j.val%2
        have h1 : (2 + 2 * ((i.val - 2) / 2) + ((j.val - 2) % 2)) % 2
            = (j.val - 2) % 2 := by omega
        have h2 : (j.val - 2) % 2 = j.val % 2 := by omega
        omega
    have hMt0 : (UJ * (genM a).transpose * UJ) t0 j
        = gellMann a ⟨(j.val - 2) / 2, by omega⟩ ⟨(i.val - 2) / 2, by omega⟩ := by
      rw [genMconj_eq_27 a t0 j ht027 hj, if_pos ht0f]
      -- Need: ⟨(j.val-2)/2,_⟩ = ⟨(j.val-2)/2,_⟩ and ⟨(t0.val-2)/2,_⟩ = ⟨(i.val-2)/2,_⟩
      congr 1
      · apply Fin.ext; show (t0.val - 2) / 2 = (i.val - 2) / 2; exact ht0c
    -- Sum2: define s0 with colour of j, flavour of i
    have hfi : (i.val - 2) % 2 < 2 := Nat.mod_lt _ (by omega)
    set s0 : I32 := ⟨2 + 2 * ((j.val - 2) / 2) + ((i.val - 2) % 2), by omega⟩ with hs0
    have hs0eq : s0.val = 2 + 2 * ((j.val - 2) / 2) + ((i.val - 2) % 2) := rfl
    have hs027 : 2 ≤ s0.val ∧ s0.val < 8 := by rw [hs0eq]; constructor <;> omega
    have hs0c : (s0.val - 2) / 2 = (j.val - 2) / 2 := by rw [hs0eq]; omega
    have hs0f : (s0.val - 2) % 2 = (i.val - 2) % 2 := by rw [hs0eq]; omega
    have hsum2 : ∑ t, (UJ * (genM a).transpose * UJ) i t * genH k t j
        = (UJ * (genM a).transpose * UJ) i s0 * genH k s0 j := by
      apply Finset.sum_eq_single s0
      · intro t _ htne
        by_cases ht27 : 2 ≤ t.val ∧ t.val < 8
        · by_cases hc : (t.val - 2) / 2 = (j.val - 2) / 2
          · by_cases hf : (t.val - 2) % 2 = (i.val - 2) % 2
            · exfalso; apply htne
              apply Fin.ext; show t.val = s0.val
              have hteq : t.val = 2 + 2 * ((t.val - 2) / 2) + ((t.val - 2) % 2) := by omega
              rw [hteq, hc, hf, hs0eq]
            · have hM0 : (UJ * (genM a).transpose * UJ) i t = 0 := by
                rw [genMconj_eq_27 a i t hi ht27, if_neg (Ne.symm hf)]
              rw [hM0, zero_mul]
          · have hH0 : genH k t j = 0 := by
              rw [genH_eq_27 k t j ht27 hj, if_neg hc]
            rw [hH0, mul_zero]
        · -- t ∉ 2-7: show M°_it * H_tj = 0
          by_cases hM0 : (UJ * (genM a).transpose * UJ) i t = 0
          · rw [hM0, zero_mul]
          · have hsuppM := UJ_genM_block a i t hM0
            rcases hsuppM with ⟨_, _, ht1, ht2⟩ | ⟨_, _, ht1, ht2⟩
            · exact absurd ⟨ht1, ht2⟩ ht27
            · by_cases hH0 : genH k t j = 0
              · rw [hH0, mul_zero]
              · exfalso; have := (genH_supp_block k t j hH0).1; omega
      · intro hcon; exact absurd (Finset.mem_univ _) hcon
    -- Simplify M°_{i,s0} and H_{s0,j}
    have hMs0 : (UJ * (genM a).transpose * UJ) i s0
        = gellMann a ⟨(j.val - 2) / 2, by omega⟩ ⟨(i.val - 2) / 2, by omega⟩ := by
      rw [genMconj_eq_27 a i s0 hi hs027, if_pos hs0f.symm]
      congr 1
      · apply Fin.ext; show (s0.val - 2) / 2 = (j.val - 2) / 2; exact hs0c
    have hHs0 : genH k s0 j
        = pauli k ⟨i.val % 2, by omega⟩ ⟨j.val % 2, by omega⟩ := by
      rw [genH_eq_27 k s0 j hs027 hj, if_pos hs0c]
      congr 1
      · apply Fin.ext
        show s0.val % 2 = i.val % 2
        rw [hs0eq]
        have h1 : (2 + 2 * ((j.val - 2) / 2) + ((i.val - 2) % 2)) % 2
            = (i.val - 2) % 2 := by omega
        have h2 : (i.val - 2) % 2 = i.val % 2 := by omega
        omega
    -- Now both sums are explicit; they agree by mul_comm
    rw [hsum1, hHt0, hMt0, hsum2, hMs0, hHs0, mul_comm]
  · -- Case 2: i ∈ 2-7, j ∉ 2-7. Both sums are zero.
    have hsum1 : ∑ t, genH k i t * (UJ * (genM a).transpose * UJ) t j = 0 := by
      apply Finset.sum_eq_zero
      intro t _
      by_cases h1 : genH k i t = 0
      · rw [h1, zero_mul]
      · have ht27 : 2 ≤ t.val ∧ t.val < 8 := by
          have hsupp := genH_supp_block k i t h1
          constructor <;> omega
        have h2 : (UJ * (genM a).transpose * UJ) t j = 0 := by
          by_contra hnc
          have hsupp := UJ_genM_block a t j hnc
          rcases hsupp with ⟨_, _, hj1, hj2⟩ | ⟨ht1, ht2, _, _⟩
          · exact hj ⟨hj1, hj2⟩
          · omega
        rw [h2, mul_zero]
    have hsum2 : ∑ t, (UJ * (genM a).transpose * UJ) i t * genH k t j = 0 := by
      apply Finset.sum_eq_zero
      intro t _
      by_cases h1 : (UJ * (genM a).transpose * UJ) i t = 0
      · rw [h1, zero_mul]
      · -- M°_it ≠ 0, i ∈ 2-7 → t ∈ 2-7
        have ht27 : 2 ≤ t.val ∧ t.val < 8 := by
          have hsupp := UJ_genM_block a i t h1
          rcases hsupp with ⟨_, _, h1', h2'⟩ | ⟨hi1, hi2, _, _⟩
          · exact ⟨h1', h2'⟩
          · omega
        by_cases h2 : genH k t j = 0
        · rw [h2, mul_zero]
        · -- H_tj ≠ 0 → t.val/2 = j.val/2, j.val < 8. j ∉ 2-7 → j ∈ 0-1 → contradiction.
          have hsupp := genH_supp_block k t j h2
          exfalso
          have hj08 : j.val < 8 := by exact hsupp.2.1
          have hj01 : j.val < 2 := by
            by_contra hnc
            push_neg at hnc
            exact hj ⟨by omega, hj08⟩
          omega
    rw [hsum1, hsum2]
  · -- Case 3: i ∉ 2-7, j ∈ 2-7. Both sums are zero (symmetric).
    have hsum1 : ∑ t, genH k i t * (UJ * (genM a).transpose * UJ) t j = 0 := by
      apply Finset.sum_eq_zero
      intro t _
      by_cases h2 : (UJ * (genM a).transpose * UJ) t j = 0
      · rw [h2, mul_zero]
      · -- M°_tj ≠ 0, j ∈ 2-7 → t ∈ 2-7
        have ht27 : 2 ≤ t.val ∧ t.val < 8 := by
          have hsupp := UJ_genM_block a t j h2
          rcases hsupp with ⟨h1, h2', _, _⟩ | ⟨_, _, hj1, hj2⟩
          · exact ⟨h1, h2'⟩
          · omega
        by_cases h1 : genH k i t = 0
        · rw [h1, zero_mul]
        · -- H_it ≠ 0 → i.val/2 = t.val/2, i.val < 8. i ∉ 2-7 → i ∈ 0-1 → contradiction.
          have hsupp := genH_supp_block k i t h1
          exfalso
          have hi08 : i.val < 8 := hsupp.1
          have hi01 : i.val < 2 := by
            by_contra hnc
            push_neg at hnc
            exact hi ⟨by omega, hi08⟩
          omega
    have hsum2 : ∑ t, (UJ * (genM a).transpose * UJ) i t * genH k t j = 0 := by
      apply Finset.sum_eq_zero
      intro t _
      by_cases h2 : genH k t j = 0
      · rw [h2, mul_zero]
      · have ht08 : t.val < 8 := (genH_supp_block k t j h2).1
        by_cases h1 : (UJ * (genM a).transpose * UJ) i t = 0
        · rw [h1, zero_mul]
        · -- M°_it ≠ 0 → (i,t ∈ 2-7) ∨ (i,t ∈ 10-15). t.val<8 → i,t ∈ 2-7. But i ∉ 2-7.
          have hsupp := UJ_genM_block a i t h1
          rcases hsupp with ⟨hi1, hi2, _, _⟩ | ⟨hi1, hi2, _, _⟩
          · exact hi ⟨hi1, hi2⟩ |>.elim
          · omega
    rw [hsum1, hsum2]
  · -- Case 4: neither in 2-7. Both sums are zero.
    have hsum1 : ∑ t, genH k i t * (UJ * (genM a).transpose * UJ) t j = 0 := by
      apply Finset.sum_eq_zero
      intro t _
      by_cases h2 : (UJ * (genM a).transpose * UJ) t j = 0
      · rw [h2, mul_zero]
      · -- M°_tj ≠ 0 → j ∈ 2-7 or j ∈ 10-15. j ∉ 2-7 → j ∈ 10-15, t ∈ 10-15.
        -- H_it ≠ 0 → t.val < 8. Contradiction.
        have hsupp := UJ_genM_block a t j h2
        rcases hsupp with ⟨_, _, hj1, hj2⟩ | ⟨ht1, ht2, _, _⟩
        · exact hj ⟨hj1, hj2⟩ |>.elim
        · by_cases h1 : genH k i t = 0
          · rw [h1, zero_mul]
          · have ht08 := (genH_supp_block k i t h1).2.1
            omega
    have hsum2 : ∑ t, (UJ * (genM a).transpose * UJ) i t * genH k t j = 0 := by
      apply Finset.sum_eq_zero
      intro t _
      by_cases h1 : (UJ * (genM a).transpose * UJ) i t = 0
      · rw [h1, zero_mul]
      · -- M°_it ≠ 0 → i ∈ 2-7 or i ∈ 10-15. i ∉ 2-7 → i ∈ 10-15, t ∈ 10-15.
        -- H_tj ≠ 0 → t.val < 8. Contradiction.
        have hsupp := UJ_genM_block a i t h1
        rcases hsupp with ⟨hi1, hi2, _, _⟩ | ⟨hi1, hi2, _, _⟩
        · exact hi ⟨hi1, hi2⟩ |>.elim
        · by_cases h2 : genH k t j = 0
          · rw [h2, mul_zero]
          · have ht08 := (genH_supp_block k t j h2).1
            omega
    rw [hsum1, hsum2]

/-- UJ is symmetric: UJᵀ i j = UJ j i, and j = partner i ↔ i = partner j. -/
theorem UJ_transpose : UJᵀ = UJ := by
  ext i j
  simp only [Matrix.transpose_apply, UJ, UJ_matrix]
  -- Goal: (if i = partner j then 1 else 0) = (if j = partner i then 1 else 0)
  have hiff : (i = partner j) ↔ (j = partner i) := by
    constructor
    · intro h
      -- h : i = partner j. Then partner i = partner (partner j) = j.
      have h1 : partner i = j := by rw [h, partner_involutive]
      exact h1.symm
    · intro h
      -- h : j = partner i. Then partner j = partner (partner i) = i.
      have h1 : partner j = i := by rw [h, partner_involutive]
      exact h1.symm
  simp only [hiff]

/-- Order-zero M/H: [genM a, H°_k] = 0 by duality.
    From order_zero_H_M, transpose and conjugate by UJ. -/
theorem order_zero_M_H (a : Fin 8) (k : Fin 3) :
    genM a * (UJ * (genH k).transpose * UJ)
      - (UJ * (genH k).transpose * UJ) * genM a = 0 := by
  have hH := order_zero_H_M k a
  have heqH : genH k * (UJ * (genM a)ᵀ * UJ)
      = (UJ * (genM a)ᵀ * UJ) * genH k := sub_eq_zero.mp hH
  have hUU : UJ * UJ = (1 : Matrix I32 I32 ℂ) := UJ_mul_self
  -- Transpose heqH and simplify; keep simp normal form
  have hT := congrArg Matrix.transpose heqH
  simp only [Matrix.transpose_mul, UJ_transpose, Matrix.transpose_transpose,
    Matrix.mul_assoc] at hT
  -- hT : (genH k)ᵀ * (UJ * (genM a * UJ)) = UJ * (genM a * (UJ * (genH k)ᵀ))
  -- Conjugate by UJ
  have hC := congrArg (fun M => UJ * M * UJ) hT
  -- Simplify using UJ*UJ=1
  -- LHS: UJ * ((genH k)ᵀ * (UJ * (genM a * UJ))) * UJ
  --    = (UJ * (genH k)ᵀ * UJ) * genM a * (UJ*UJ)  [rearrange]
  --    = (UJ * (genH k)ᵀ * UJ) * genM a            [UJ*UJ=1]
  -- RHS: UJ * (UJ * (genM a * (UJ * (genH k)ᵀ))) * UJ
  --    = (UJ*UJ) * genM a * (UJ * (genH k)ᵀ * UJ)  [rearrange]
  --    = genM a * (UJ * (genH k)ᵀ * UJ)            [UJ*UJ=1]
  have lhs_eq : UJ * ((genH k)ᵀ * (UJ * (genM a * UJ))) * UJ
      = (UJ * (genH k)ᵀ * UJ) * genM a := by
    have h1 : UJ * ((genH k)ᵀ * (UJ * (genM a * UJ))) * UJ
        = (UJ * (genH k)ᵀ * UJ) * (genM a * (UJ * UJ)) := by
      simp only [Matrix.mul_assoc]
    rw [h1, hUU, Matrix.mul_one]
  have rhs_eq : UJ * (UJ * (genM a * (UJ * (genH k)ᵀ))) * UJ
      = genM a * (UJ * (genH k)ᵀ * UJ) := by
    have h1 : UJ * (UJ * (genM a * (UJ * (genH k)ᵀ))) * UJ
        = (UJ * UJ) * (genM a * (UJ * (genH k)ᵀ * UJ)) := by
      simp only [Matrix.mul_assoc]
    rw [h1, hUU, Matrix.one_mul]
  rw [lhs_eq, rhs_eq] at hC
  -- hC : (UJ * (genH k)ᵀ * UJ) * genM a = genM a * (UJ * (genH k)ᵀ * UJ)
  have hgoal : genM a * (UJ * (genH k)ᵀ * UJ)
      - (UJ * (genH k)ᵀ * UJ) * genM a = 0 := by
    rw [← hC, sub_self]
  simpa only [Matrix.transpose] using hgoal
/-- Order-zero for the Martinetti representation.
    Unlike the defective Option A (disjoint support), this uses the
    tensor-product structure: H acts on flavour, M₃ on colour.
    Numerically verified (residual = 0); the Lean proof needs the
    tensor-product commutator argument for the 48 cross pairs. -/
theorem smGen_order_zero (g1 g2 : Fin 12) :
    smGen g1 * smGenOp g2 - smGenOp g2 * smGen g1 = 0 := by
  fin_cases g1
  · fin_cases g2
    · exact order_zero_C_C
    · exact order_zero_C_H 0
    · exact order_zero_C_H 1
    · exact order_zero_C_H 2
    · exact order_zero_C_M 0
    · exact order_zero_C_M 1
    · exact order_zero_C_M 2
    · exact order_zero_C_M 3
    · exact order_zero_C_M 4
    · exact order_zero_C_M 5
    · exact order_zero_C_M 6
    · exact order_zero_C_M 7
  · fin_cases g2
    · exact order_zero_H_C 0
    · exact order_zero_H_H 0 0
    · exact order_zero_H_H 0 1
    · exact order_zero_H_H 0 2
    · exact order_zero_H_M 0 0
    · exact order_zero_H_M 0 1
    · exact order_zero_H_M 0 2
    · exact order_zero_H_M 0 3
    · exact order_zero_H_M 0 4
    · exact order_zero_H_M 0 5
    · exact order_zero_H_M 0 6
    · exact order_zero_H_M 0 7
  · fin_cases g2
    · exact order_zero_H_C 1
    · exact order_zero_H_H 1 0
    · exact order_zero_H_H 1 1
    · exact order_zero_H_H 1 2
    · exact order_zero_H_M 1 0
    · exact order_zero_H_M 1 1
    · exact order_zero_H_M 1 2
    · exact order_zero_H_M 1 3
    · exact order_zero_H_M 1 4
    · exact order_zero_H_M 1 5
    · exact order_zero_H_M 1 6
    · exact order_zero_H_M 1 7
  · fin_cases g2
    · exact order_zero_H_C 2
    · exact order_zero_H_H 2 0
    · exact order_zero_H_H 2 1
    · exact order_zero_H_H 2 2
    · exact order_zero_H_M 2 0
    · exact order_zero_H_M 2 1
    · exact order_zero_H_M 2 2
    · exact order_zero_H_M 2 3
    · exact order_zero_H_M 2 4
    · exact order_zero_H_M 2 5
    · exact order_zero_H_M 2 6
    · exact order_zero_H_M 2 7
  · fin_cases g2
    · exact order_zero_M_C 0
    · exact order_zero_M_H 0 0
    · exact order_zero_M_H 0 1
    · exact order_zero_M_H 0 2
    · exact order_zero_M_M 0 0
    · exact order_zero_M_M 0 1
    · exact order_zero_M_M 0 2
    · exact order_zero_M_M 0 3
    · exact order_zero_M_M 0 4
    · exact order_zero_M_M 0 5
    · exact order_zero_M_M 0 6
    · exact order_zero_M_M 0 7
  · fin_cases g2
    · exact order_zero_M_C 1
    · exact order_zero_M_H 1 0
    · exact order_zero_M_H 1 1
    · exact order_zero_M_H 1 2
    · exact order_zero_M_M 1 0
    · exact order_zero_M_M 1 1
    · exact order_zero_M_M 1 2
    · exact order_zero_M_M 1 3
    · exact order_zero_M_M 1 4
    · exact order_zero_M_M 1 5
    · exact order_zero_M_M 1 6
    · exact order_zero_M_M 1 7
  · fin_cases g2
    · exact order_zero_M_C 2
    · exact order_zero_M_H 2 0
    · exact order_zero_M_H 2 1
    · exact order_zero_M_H 2 2
    · exact order_zero_M_M 2 0
    · exact order_zero_M_M 2 1
    · exact order_zero_M_M 2 2
    · exact order_zero_M_M 2 3
    · exact order_zero_M_M 2 4
    · exact order_zero_M_M 2 5
    · exact order_zero_M_M 2 6
    · exact order_zero_M_M 2 7
  · fin_cases g2
    · exact order_zero_M_C 3
    · exact order_zero_M_H 3 0
    · exact order_zero_M_H 3 1
    · exact order_zero_M_H 3 2
    · exact order_zero_M_M 3 0
    · exact order_zero_M_M 3 1
    · exact order_zero_M_M 3 2
    · exact order_zero_M_M 3 3
    · exact order_zero_M_M 3 4
    · exact order_zero_M_M 3 5
    · exact order_zero_M_M 3 6
    · exact order_zero_M_M 3 7
  · fin_cases g2
    · exact order_zero_M_C 4
    · exact order_zero_M_H 4 0
    · exact order_zero_M_H 4 1
    · exact order_zero_M_H 4 2
    · exact order_zero_M_M 4 0
    · exact order_zero_M_M 4 1
    · exact order_zero_M_M 4 2
    · exact order_zero_M_M 4 3
    · exact order_zero_M_M 4 4
    · exact order_zero_M_M 4 5
    · exact order_zero_M_M 4 6
    · exact order_zero_M_M 4 7
  · fin_cases g2
    · exact order_zero_M_C 5
    · exact order_zero_M_H 5 0
    · exact order_zero_M_H 5 1
    · exact order_zero_M_H 5 2
    · exact order_zero_M_M 5 0
    · exact order_zero_M_M 5 1
    · exact order_zero_M_M 5 2
    · exact order_zero_M_M 5 3
    · exact order_zero_M_M 5 4
    · exact order_zero_M_M 5 5
    · exact order_zero_M_M 5 6
    · exact order_zero_M_M 5 7
  · fin_cases g2
    · exact order_zero_M_C 6
    · exact order_zero_M_H 6 0
    · exact order_zero_M_H 6 1
    · exact order_zero_M_H 6 2
    · exact order_zero_M_M 6 0
    · exact order_zero_M_M 6 1
    · exact order_zero_M_M 6 2
    · exact order_zero_M_M 6 3
    · exact order_zero_M_M 6 4
    · exact order_zero_M_M 6 5
    · exact order_zero_M_M 6 6
    · exact order_zero_M_M 6 7
  · fin_cases g2
    · exact order_zero_M_C 7
    · exact order_zero_M_H 7 0
    · exact order_zero_M_H 7 1
    · exact order_zero_M_H 7 2
    · exact order_zero_M_M 7 0
    · exact order_zero_M_M 7 1
    · exact order_zero_M_M 7 2
    · exact order_zero_M_M 7 3
    · exact order_zero_M_M 7 4
    · exact order_zero_M_M 7 5
    · exact order_zero_M_M 7 6
    · exact order_zero_M_M 7 7

end ThetLogos
