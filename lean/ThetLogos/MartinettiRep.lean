import Mathlib.Data.Matrix.Mul
import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic
import ThetLogos.Scaffold32
import ThetLogos.FiniteSpectralTriple

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

§ D_F ansatz (end of file): one-generation Yukawa+Majorana Dirac operator
`smDirac` (T2 definition; grading-odd, self-adjoint, J-compatible proved T3;
order-one stated as a predicate, proof pending — T5).
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

/-- The ℂ-support projection: -genC² is diagonal, 1 on C-support, 0 elsewhere.
    Tier T3. -/
theorem genC_sq_proj (i : I32) :
    (-(genC * genC)) i i =
      if (8 ≤ i.val ∧ i.val < 16) ∨ i.val = 16 ∨ i.val = 17 ∨ i.val = 24 ∨ i.val = 25
      then 1 else 0 := by
  have hdiag : (genC * genC) i i = (genC i i)^2 := by
    simp only [Matrix.mul_apply]
    rw [Finset.sum_eq_single i (fun k _ hk => by
      rw [genC_apply_ne (Ne.symm hk), zero_mul]) (by simp)]
    rw [sq]
  rw [Matrix.neg_apply, hdiag, genC_diag_val]
  have hI2 : (Complex.I)^2 = -1 := by rw [sq]; exact Complex.I_mul_I
  by_cases h : (8 ≤ i.val ∧ i.val < 16) ∨ i.val = 16 ∨ i.val = 17 ∨ i.val = 24 ∨ i.val = 25
  · rw [if_pos h]
    by_cases h1 : 8 ≤ i.val ∧ i.val < 16
    · rw [if_pos h1, hI2]; simp [Matrix.neg_apply]
    · rw [if_neg h1]
      have h2 : i.val = 16 ∨ i.val = 17 ∨ i.val = 24 ∨ i.val = 25 := by
        rcases h with h1' | h2 | h3 | h4 | h5
        · exact absurd h1' h1
        · exact Or.inl h2
        · exact Or.inr (Or.inl h3)
        · exact Or.inr (Or.inr (Or.inl h4))
        · exact Or.inr (Or.inr (Or.inr h5))
      rw [if_pos h2, hI2]; simp [Matrix.neg_apply]
  · rw [if_neg h]
    have h1 : ¬ (8 ≤ i.val ∧ i.val < 16) := by
      intro h1'; exact h (Or.inl h1')
    have h2 : ¬ (i.val = 16 ∨ i.val = 17 ∨ i.val = 24 ∨ i.val = 25) := by
      intro h2'; exact h (Or.inr h2')
    rw [if_neg h1, if_neg h2]
    simp [Matrix.neg_apply]

/-- -genC² vanishes off-diagonal. Tier T3. -/
theorem genC_sq_proj_offdiag {i j : I32} (hij : i ≠ j) :
    (-(genC * genC)) i j = 0 := by
  have h : (genC * genC) i j = 0 := by
    simp only [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro k _
    by_cases hik : i = k
    · subst hik; rw [genC_apply_ne hij, mul_zero]
    · rw [genC_apply_ne hik, zero_mul]
  rw [Matrix.neg_apply, h, neg_zero]

/-- Each Pauli matrix squares to the 2×2 identity. Tier T3. -/
theorem pauli_sq (k : Fin 3) : pauli k * pauli k = 1 := by
  fin_cases k <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [pauli, Matrix.mul_apply, Finset.sum_fin_eq_sum_range,
      Finset.sum_range_succ] <;> ring


/-- Sum of all 8 Gell-Mann matrix squares is (16/3) times the 3×3 identity.
    Tier T3. Standard identity: Σₐ λₐ² = (16/3)I₃. -/
theorem gellMann_sq_sum :
    ∑ a : Fin 8, gellMann a * gellMann a = ((16/3 : ℂ)) • (1 : Matrix (Fin 3) (Fin 3) ℂ) := by
  have hsq : (Real.sqrt 3 : ℂ)^2 = 3 := by
    have h : (Real.sqrt 3)^2 = (3:ℝ) := Real.sq_sqrt (by norm_num)
    calc (Real.sqrt 3 : ℂ)^2 = ((Real.sqrt 3 ^ 2 : ℝ) : ℂ) := by norm_cast
      _ = ((3:ℝ):ℂ) := by rw [h]
      _ = 3 := by norm_num
  have hinv : ((Real.sqrt 3 : ℂ))⁻¹ ^ 2 = 1/3 := by
    rw [inv_pow, hsq]; norm_num
  ext i j
  fin_cases i <;> fin_cases j <;> simp only []
  · simp only [Matrix.smul_apply, Matrix.one_apply, ite_true, smul_eq_mul, mul_one]
    conv_lhs =>
      rw [Fin.sum_univ_eight]
      simp only [Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_three, gellMann]
      simp
      ring_nf
      simp only [hinv]
    ring
  · simp only [Matrix.smul_apply, Matrix.one_apply]
    rw [ite_eq_right (by decide), smul_zero]
    rw [Fin.sum_univ_eight]
    simp only [Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_three, gellMann]
    simp
  · simp only [Matrix.smul_apply, Matrix.one_apply]
    rw [ite_eq_right (by decide), smul_zero]
    rw [Fin.sum_univ_eight]
    simp only [Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_three, gellMann]
    simp
  · simp only [Matrix.smul_apply, Matrix.one_apply]
    rw [ite_eq_right (by decide), smul_zero]
    rw [Fin.sum_univ_eight]
    simp only [Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_three, gellMann]
    simp
  · simp only [Matrix.smul_apply, Matrix.one_apply, ite_true, smul_eq_mul, mul_one]
    conv_lhs =>
      rw [Fin.sum_univ_eight]
      simp only [Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_three, gellMann]
      simp
      ring_nf
      simp only [hinv]
    ring
  · simp only [Matrix.smul_apply, Matrix.one_apply]
    rw [ite_eq_right (by decide), smul_zero]
    rw [Fin.sum_univ_eight]
    simp only [Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_three, gellMann]
    simp
  · simp only [Matrix.smul_apply, Matrix.one_apply]
    rw [ite_eq_right (by decide), smul_zero]
    rw [Fin.sum_univ_eight]
    simp only [Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_three, gellMann]
    simp
  · simp only [Matrix.smul_apply, Matrix.one_apply]
    rw [ite_eq_right (by decide), smul_zero]
    rw [Fin.sum_univ_eight]
    simp only [Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_three, gellMann]
    simp
  · simp only [Matrix.smul_apply, Matrix.one_apply, ite_true, smul_eq_mul, mul_one]
    conv_lhs =>
      rw [Fin.sum_univ_eight]
      simp only [Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_three, gellMann]
      simp
      ring_nf
      simp only [hinv]
    ring

/-! ## Unitality: the three block projectors sum to the identity

P_C = -(genC)² projects onto 8–15, 16, 17, 24, 25;
P_H = (genH k)² projects onto 0–7;
P_M = (3/16) • ∑ₐ (genM a)² projects onto the colour triplets 18–23, 26–31.
All three are proven by reduction to the Pauli / Gell-Mann square identities
on explicit finite supports — no 32×32 brute force. Tier T3. -/

/-- Sum over I32 reduces to sum over an explicit finite support set. -/
theorem sum_I32_support {f : I32 → ℂ} (s : Finset I32)
    (hvan : ∀ l : I32, l ∉ s → f l = 0) :
    (∑ l : I32, f l) = ∑ l ∈ s, f l := by
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro l _ hl
  exact hvan l hl

/-- genH entry on its block: reduces to the Pauli entry. -/
theorem genH_apply_eq (k : Fin 3) (i j : I32) (hi : i.val < 8) (hj : j.val < 8)
    (hblk : i.val / 2 = j.val / 2) :
    genH k i j = pauli k ⟨i.val % 2, Nat.mod_lt _ (by norm_num)⟩
                          ⟨j.val % 2, Nat.mod_lt _ (by norm_num)⟩ := by
  unfold genH
  simp only []
  rw [if_pos ⟨hi, hj, hblk⟩]

/-- Identify a Fin 2 index from its mod-2 value. -/
theorem fin2_of_mod_eq (n : Nat) (m : Fin 2) (h : n % 2 = m.val) :
    (⟨n % 2, Nat.mod_lt _ (by norm_num)⟩ : Fin 2) = m := by
  apply Fin.ext
  show n % 2 = m.val
  exact h

/-- (genH k)² on a doublet block equals the Pauli square. -/
theorem genH_sq_onblock (k : Fin 3) (i j : I32) (hi : i.val < 8) (hj : j.val < 8)
    (hblk : i.val / 2 = j.val / 2) :
    (genH k * genH k) i j =
      (pauli k * pauli k) ⟨i.val % 2, Nat.mod_lt _ (by norm_num)⟩
                            ⟨j.val % 2, Nat.mod_lt _ (by norm_num)⟩ := by
  obtain ⟨b, hb⟩ : ∃ b : I32, b.val = 2 * (i.val / 2) := ⟨⟨_, by omega⟩, rfl⟩
  obtain ⟨b1, hb1⟩ : ∃ b1 : I32, b1.val = 2 * (i.val / 2) + 1 := ⟨⟨_, by omega⟩, rfl⟩
  have hvan : ∀ l : I32, l ∉ ({b, b1} : Finset I32) →
      genH k i l * genH k l j = 0 := by
    intro l hl
    by_cases g1 : genH k i l = 0
    · rw [g1, zero_mul]
    · by_cases g2 : genH k l j = 0
      · rw [g2, mul_zero]
      · exfalso
        have hs1 := genH_supp_block k i l g1
        have hdiv : l.val / 2 = i.val / 2 := hs1.2.2.symm
        have hcon : l.val = 2 * (i.val / 2) ∨ l.val = 2 * (i.val / 2) + 1 := by omega
        apply hl
        simp only [Finset.mem_insert, Finset.mem_singleton]
        rcases hcon with hcon | hcon
        · exact Or.inl (Fin.ext (by rw [hb]; exact hcon))
        · exact Or.inr (Fin.ext (by rw [hb1]; exact hcon))
  rw [Matrix.mul_apply, sum_I32_support ({b, b1} : Finset I32) hvan]
  have d01 : b ≠ b1 := by
    intro hcon
    have h2 := congrArg Fin.val hcon
    rw [hb, hb1] at h2
    omega
  rw [Finset.sum_pair d01, Matrix.mul_apply, Fin.sum_univ_two]
  have hb8 : b.val < 8 := by rw [hb]; omega
  have hb18 : b1.val < 8 := by rw [hb1]; omega
  have hbb : i.val / 2 = b.val / 2 := by rw [hb]; omega
  have hbj : b.val / 2 = j.val / 2 := by rw [hb]; omega
  have hbb1 : i.val / 2 = b1.val / 2 := by rw [hb1]; omega
  have hb1j : b1.val / 2 = j.val / 2 := by rw [hb1]; omega
  have hm0 : (⟨b.val % 2, Nat.mod_lt _ (by norm_num)⟩ : Fin 2) = 0 :=
    fin2_of_mod_eq _ 0 (by rw [hb]; omega)
  have hm1 : (⟨b1.val % 2, Nat.mod_lt _ (by norm_num)⟩ : Fin 2) = 1 :=
    fin2_of_mod_eq _ 1 (by rw [hb1]; omega)
  have e1 : genH k i b = pauli k ⟨i.val % 2, Nat.mod_lt _ (by norm_num)⟩ 0 := by
    have h1 := genH_apply_eq k i b hi hb8 hbb
    rw [h1, hm0]
  have e2 : genH k b j = pauli k 0 ⟨j.val % 2, Nat.mod_lt _ (by norm_num)⟩ := by
    have h1 := genH_apply_eq k b j hb8 hj hbj
    rw [h1, hm0]
  have e3 : genH k i b1 = pauli k ⟨i.val % 2, Nat.mod_lt _ (by norm_num)⟩ 1 := by
    have h1 := genH_apply_eq k i b1 hi hb18 hbb1
    rw [h1, hm1]
  have e4 : genH k b1 j = pauli k 1 ⟨j.val % 2, Nat.mod_lt _ (by norm_num)⟩ := by
    have h1 := genH_apply_eq k b1 j hb18 hj hb1j
    rw [h1, hm1]
  rw [e1, e2, e3, e4]

/-- (genH k)² is the projector onto indices 0–7. Tier T3. -/
theorem genH_sq_proj (k : Fin 3) (i : I32) :
    ((genH k * genH k)) i i = if i.val < 8 then 1 else 0 := by
  by_cases hi : i.val < 8
  · rw [if_pos hi, genH_sq_onblock k i i hi hi rfl, pauli_sq,
      Matrix.one_apply, if_pos rfl]
  · rw [if_neg hi]
    simp only [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro l _
    by_cases g1 : genH k i l = 0
    · rw [g1, zero_mul]
    · exfalso; exact hi (genH_supp k i l g1).1

/-- (genH k)² vanishes off-diagonal. Tier T3. -/
theorem genH_sq_offdiag (k : Fin 3) {i j : I32} (hij : i ≠ j) :
    ((genH k * genH k)) i j = 0 := by
  by_cases hblk : i.val < 8 ∧ j.val < 8 ∧ i.val / 2 = j.val / 2
  · obtain ⟨hi, hj, hdiv⟩ := hblk
    rw [genH_sq_onblock k i j hi hj hdiv, pauli_sq]
    have hne : (⟨i.val % 2, Nat.mod_lt _ (by norm_num)⟩ : Fin 2) ≠
        ⟨j.val % 2, Nat.mod_lt _ (by norm_num)⟩ := by
      intro hcon
      apply hij
      have h1 : i.val % 2 = j.val % 2 := congrArg Fin.val hcon
      have h2 : i.val = j.val := by
        have e1 := Nat.div_add_mod i.val 2
        have e2 := Nat.div_add_mod j.val 2
        omega
      exact Fin.ext h2
    rw [Matrix.one_apply, if_neg hne]
  · simp only [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro l _
    by_cases g1 : genH k i l = 0
    · rw [g1, zero_mul]
    · by_cases g2 : genH k l j = 0
      · rw [g2, mul_zero]
      · exfalso
        have hs1 := genH_supp_block k i l g1
        have hs2 := genH_supp_block k l j g2
        apply hblk
        refine ⟨hs1.1, hs2.2.1, ?_⟩
        omega


/-! ## Gell-Mann / colour block -/

/-- Flat index of triplet `t`, colour position `p`. -/
def tripletIdx (t : Fin 4) (p : Fin 3) : I32 :=
  ⟨(if t.val < 2 then 18 else 26) + 2 * p.val + t.val % 2, by
    have h1 := t.isLt; have h2 := p.isLt
    by_cases h : t.val < 2
    · rw [if_pos h]; omega
    · rw [if_neg h]; omega⟩

/-- tripletIdx lands in the claimed triplet (12 concrete cases). -/
theorem tripletIdx_spec : ∀ t : Fin 4, ∀ p : Fin 3,
    tripletOf (tripletIdx t p).val = some (t, p) := by
  decide

/-- tripletIdx is injective in the colour position (36 concrete cases). -/
theorem tripletIdx_inj : ∀ t : Fin 4, ∀ p q : Fin 3,
    tripletIdx t p = tripletIdx t q → p = q := by
  decide

/-- Inversion: a triplet index is recovered from its (t, p) (384 concrete cases). -/
theorem tripletOf_inv_all : ∀ n : Nat, n < 32 → ∀ t : Fin 4, ∀ p : Fin 3,
    tripletOf n = some (t, p) → n = (tripletIdx t p).val := by
  decide

theorem tripletOf_inv (l : I32) (t : Fin 4) (p : Fin 3)
    (h : tripletOf l.val = some (t, p)) : l = tripletIdx t p :=
  Fin.ext (tripletOf_inv_all l.val l.isLt t p h)

/-- Nonzero genM entries stay inside a single triplet. -/
theorem genM_supp_triplet (a : Fin 8) (i j : I32) (h : genM a i j ≠ 0) :
    ∃ t : Fin 4, ∃ p q : Fin 3,
      tripletOf i.val = some (t, p) ∧ tripletOf j.val = some (t, q) := by
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
      -- note: `cases` rewrote `tripletOf i.val`/`tripletOf j.val` in the goal
      exact ⟨t1, p1, p2, rfl, by rw [heq]⟩

/-- genM entry on its triplet block reduces to the Gell-Mann entry. -/
theorem genM_apply_eq (a : Fin 8) (i j : I32) (t : Fin 4) (p q : Fin 3)
    (hi : tripletOf i.val = some (t, p)) (hj : tripletOf j.val = some (t, q)) :
    genM a i j = gellMann a p q := by
  simp only [genM, hi, hj]
  simp

/-- (genM a)² on a triplet block equals the Gell-Mann square. -/
theorem genM_sq_onblock (a : Fin 8) (i j : I32) (t : Fin 4) (p q : Fin 3)
    (hi : tripletOf i.val = some (t, p)) (hj : tripletOf j.val = some (t, q)) :
    (genM a * genM a) i j = (gellMann a * gellMann a) p q := by
  have hvan : ∀ l : I32, l ∉ Finset.image (tripletIdx t) Finset.univ →
      genM a i l * genM a l j = 0 := by
    intro l hl
    by_cases g1 : genM a i l = 0
    · rw [g1, zero_mul]
    · exfalso
      obtain ⟨t1, p1, q1, h1i, h1l⟩ := genM_supp_triplet a i l g1
      have htt : t1 = t := by
        have h := h1i.symm.trans hi
        have h2 := Option.some_inj.mp h
        exact congrArg Prod.fst h2
      apply hl
      rw [Finset.mem_image]
      exact ⟨q1, Finset.mem_univ q1,
        (tripletOf_inv l t q1 (by rw [← htt]; exact h1l)).symm⟩
  rw [Matrix.mul_apply, sum_I32_support _ hvan,
    Finset.sum_image (fun x _ y _ hxy => tripletIdx_inj t _ _ hxy),
    Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro p' _
  rw [genM_apply_eq a i (tripletIdx t p') t p p' hi (tripletIdx_spec t p'),
      genM_apply_eq a (tripletIdx t p') j t p' q (tripletIdx_spec t p') hj]

/-- Entry-wise corollary of gellMann_sq_sum. -/
theorem gellMann_sq_sum_apply (p q : Fin 3) :
    (∑ a : Fin 8, (gellMann a * gellMann a)) p q =
      if p = q then (16/3 : ℂ) else 0 := by
  have h : (∑ a : Fin 8, (gellMann a * gellMann a)) p q =
      (((16/3 : ℂ)) • (1 : Matrix (Fin 3) (Fin 3) ℂ)) p q := by
    rw [gellMann_sq_sum]
  rw [h]
  simp only [Matrix.smul_apply, Matrix.one_apply]
  by_cases hpq : p = q
  · simp only [if_pos hpq, smul_eq_mul, mul_one]
  · simp only [if_neg hpq, smul_zero]

/-- Term-level entry corollary (sum of applies). -/
theorem gellMann_sq_sum_entry (p q : Fin 3) :
    (∑ a : Fin 8, ((gellMann a * gellMann a) p q)) =
      if p = q then (16/3 : ℂ) else 0 := by
  have h := gellMann_sq_sum_apply p q
  rw [Matrix.sum_apply] at h
  exact h

/-- The summed square on a triplet block equals the Gell-Mann summed square. -/
theorem genM_sq_sum_onblock (i j : I32) (t : Fin 4) (p q : Fin 3)
    (hi : tripletOf i.val = some (t, p)) (hj : tripletOf j.val = some (t, q)) :
    (∑ a : Fin 8, ((genM a * genM a) i j)) =
      (∑ a : Fin 8, ((gellMann a * gellMann a) p q)) := by
  apply Finset.sum_congr rfl
  intro a _
  exact genM_sq_onblock a i j t p q hi hj

/-- ∑ₐ (genM a)² is (16/3) on triplet indices, 0 elsewhere. Tier T3. -/
theorem genM_sq_sum_proj (i : I32) :
    (∑ a : Fin 8, (genM a * genM a)) i i =
      if (tripletOf i.val).isSome then (16/3 : ℂ) else 0 := by
  by_cases hi : (tripletOf i.val).isSome
  · rw [if_pos hi]
    obtain ⟨⟨t, p⟩, htp⟩ := Option.isSome_iff_exists.mp hi
    simp only [Matrix.sum_apply]
    rw [genM_sq_sum_onblock i i t p p htp htp, gellMann_sq_sum_entry p p,
      if_pos rfl]
  · rw [if_neg hi]
    simp only [Matrix.sum_apply]
    apply Finset.sum_eq_zero
    intro a _
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro l _
    by_cases g1 : genM a i l = 0
    · rw [g1, zero_mul]
    · exfalso
      obtain ⟨t, p, q, h1, h2⟩ := genM_supp_triplet a i l g1
      exact hi (h1.symm ▸ (rfl : (some (t, p)).isSome = true))

/-- ∑ₐ (genM a)² vanishes off-diagonal. Tier T3. -/
theorem genM_sq_sum_offdiag {i j : I32} (hij : i ≠ j) :
    (∑ a : Fin 8, (genM a * genM a)) i j = 0 := by
  by_cases hcases : ∃ t : Fin 4, ∃ p q : Fin 3,
      tripletOf i.val = some (t, p) ∧ tripletOf j.val = some (t, q)
  · obtain ⟨t, p, q, hi, hj⟩ := hcases
    have hpq : p ≠ q := by
      intro hcon
      apply hij
      have hi' := tripletOf_inv i t p hi
      have hj' := tripletOf_inv j t q hj
      rw [hi', hj', hcon]
    simp only [Matrix.sum_apply]
    rw [genM_sq_sum_onblock i j t p q hi hj, gellMann_sq_sum_entry p q,
      if_neg hpq]
  · simp only [Matrix.sum_apply]
    apply Finset.sum_eq_zero
    intro a _
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro l _
    by_cases g1 : genM a i l = 0
    · rw [g1, zero_mul]
    · by_cases g2 : genM a l j = 0
      · rw [g2, mul_zero]
      · exfalso
        obtain ⟨t1, p1, q1, h1i, h1l⟩ := genM_supp_triplet a i l g1
        obtain ⟨t2, p2, q2, h2l, h2j⟩ := genM_supp_triplet a l j g2
        apply hcases
        have htt : t1 = t2 := by
          have h := h1l.symm.trans h2l
          have h2 := Option.some_inj.mp h
          exact congrArg Prod.fst h2
        exact ⟨t1, p1, q2, h1i, by rw [htt]; exact h2j⟩


/-! ## Full unitality -/

/-- Triplet support as a range disjunction (32 concrete cases). -/
theorem tripletOf_isSome_iff_all :
    ∀ n : Nat, n < 32 →
      ((tripletOf n).isSome ↔ (18 ≤ n ∧ n < 24) ∨ (26 ≤ n ∧ n < 32)) := by
  decide

/-- The three supports partition 0–31: each n gets exactly one unit of mass. -/
theorem unitality_arith (n : Nat) (hn : n < 32) :
    (if (8 ≤ n ∧ n < 16) ∨ n = 16 ∨ n = 17 ∨ n = 24 ∨ n = 25 then (1:ℂ) else 0) +
    (if n < 8 then (1:ℂ) else 0) +
    (if (18 ≤ n ∧ n < 24) ∨ (26 ≤ n ∧ n < 32) then (1:ℂ) else 0) = 1 := by
  interval_cases n <;> norm_num

/-- The (3/16)-scaled colour projector is the triplet indicator. -/
theorem smul_genM_sq_sum_proj (i : I32) :
    ((((3/16 : ℂ)) • (∑ a : Fin 8, (genM a * genM a))) : Matrix I32 I32 ℂ) i i =
      if (18 ≤ i.val ∧ i.val < 24) ∨ (26 ≤ i.val ∧ i.val < 32)
        then (1:ℂ) else 0 := by
  have hMiff := tripletOf_isSome_iff_all i.val i.isLt
  rw [Matrix.smul_apply, genM_sq_sum_proj i]
  by_cases hM : (tripletOf i.val).isSome
  · have hM' := hMiff.mp hM
    rw [if_pos hM, if_pos hM', smul_eq_mul]
    norm_num
  · have hM' : ¬((18 ≤ i.val ∧ i.val < 24) ∨ (26 ≤ i.val ∧ i.val < 32)) :=
      fun hcon => hM (hMiff.mpr hcon)
    rw [if_neg hM, if_neg hM', smul_zero]

/-- Full unitality: the three block projectors sum to the identity. Tier T3. -/
theorem unitality :
    (-(genC*genC)) + ((genH 0)*(genH 0)) +
      ((3/16 : ℂ)) • (∑ a : Fin 8, genM a * genM a) = 1 := by
  ext i j
  by_cases hij : i = j
  · subst hij
    rw [Matrix.add_apply, Matrix.add_apply, Matrix.one_apply, if_pos rfl,
      genC_sq_proj i, genH_sq_proj 0 i, smul_genM_sq_sum_proj i]
    exact unitality_arith i.val i.isLt
  · have h1 := genC_sq_proj_offdiag hij
    have h2 := genH_sq_offdiag (0 : Fin 3) hij
    have h3 := genM_sq_sum_offdiag hij
    simp only [Matrix.add_apply, Matrix.one_apply, Matrix.smul_apply,
      h1, h2, h3, smul_zero, add_zero]
    rw [if_neg hij]

/-! ## Faithfulness / kernel characterization

The representation is faithful: no nonzero algebra element acts as zero.
The three blocks (ℂ, ℍ, M₃) have disjoint supports covering all 32 dimensions,
and within each block the generators are linearly independent.
-/

/-- genC is nonzero: it has entry Complex.I at (8,8). Tier T3. -/
theorem genC_ne_zero : genC ≠ 0 := by
  intro h
  have h88 : genC ⟨8, by norm_num⟩ ⟨8, by norm_num⟩ = 0 := by rw [h]; rfl
  rw [genC_diag_val] at h88
  simp at h88

/-- The ℂ-block acts faithfully: c • genC = 0 forces c = 0. Tier T3. -/
theorem genC_faithful (c : ℂ) (h : c • genC = 0) : c = 0 := by
  have h88 : (c • genC) ⟨8, by norm_num⟩ ⟨8, by norm_num⟩ = 0 := by rw [h]; rfl
  rw [Matrix.smul_apply, genC_diag_val] at h88
  simpa using h88

/-- Pauli matrices are linearly independent (three-entry version).
    Vanishing at (0,0), (0,1), (1,0) suffices. Tier T3. -/
theorem pauli_linear_independent (c : Fin 3 → ℂ)
    (h00 : (∑ k : Fin 3, c k • pauli k) 0 0 = 0)
    (h01 : (∑ k : Fin 3, c k • pauli k) 0 1 = 0)
    (h10 : (∑ k : Fin 3, c k • pauli k) 1 0 = 0) : ∀ k, c k = 0 := by
  rw [Fin.sum_univ_three] at h00 h01 h10
  simp only [Matrix.add_apply, Matrix.smul_apply, pauli] at h00 h01 h10
  -- h00 : c 2 = 0; h01 : c 0 - c 1 * I = 0; h10 : c 0 + c 1 * I = 0
  -- Normalize the matrix-entry computations
  simp at h00 h01 h10
  intro k
  fin_cases k
  · -- c 0: from h01 + h10, 2 * c 0 = 0
    have hsum : (c 0 + -(c 1 * Complex.I)) + (c 0 + c 1 * Complex.I) = 0 := by
      rw [h01, h10]; ring
    have : 2 * c 0 = 0 := by linear_combination hsum
    simpa using this
  · -- c 1: from h01, c 1 * I = c 0 = 0
    have hc0 : c 0 = 0 := by
      have hsum : (c 0 + -(c 1 * Complex.I)) + (c 0 + c 1 * Complex.I) = 0 := by
        rw [h01, h10]; ring
      have : 2 * c 0 = 0 := by linear_combination hsum
      simpa using this
    have : c 1 * Complex.I = 0 := by
      have h := h01
      rw [hc0] at h
      simpa using h
    have hI : Complex.I ≠ 0 := Complex.I_ne_zero
    exact (mul_eq_zero.mp this).resolve_right hI
  · simpa using h00

/-- genH acts as pauli on the first doublet: entry (0,0). -/
theorem genH_entry_00 (k : Fin 3) :
    genH k ⟨0, by norm_num⟩ ⟨0, by norm_num⟩ = pauli k 0 0 := by
  simp [genH]

/-- genH acts as pauli on the first doublet: entry (0,1). -/
theorem genH_entry_01 (k : Fin 3) :
    genH k ⟨0, by norm_num⟩ ⟨1, by norm_num⟩ = pauli k 0 1 := by
  simp [genH]

/-- genH acts as pauli on the first doublet: entry (1,0). -/
theorem genH_entry_10 (k : Fin 3) :
    genH k ⟨1, by norm_num⟩ ⟨0, by norm_num⟩ = pauli k 1 0 := by
  simp [genH]

/-- The ℍ-block generators are linearly independent. Tier T3. -/
theorem genH_linear_independent (c : Fin 3 → ℂ)
    (h00 : (∑ k : Fin 3, c k • genH k) ⟨0, by norm_num⟩ ⟨0, by norm_num⟩ = 0)
    (h01 : (∑ k : Fin 3, c k • genH k) ⟨0, by norm_num⟩ ⟨1, by norm_num⟩ = 0)
    (h10 : (∑ k : Fin 3, c k • genH k) ⟨1, by norm_num⟩ ⟨0, by norm_num⟩ = 0) :
    ∀ k, c k = 0 := by
  -- Convert each to the corresponding Pauli-sum entry.
  have p00 : (∑ k : Fin 3, c k • pauli k) 0 0 = 0 := by
    rw [Fin.sum_univ_three] at h00 ⊢
    simp only [Matrix.add_apply, Matrix.smul_apply, genH_entry_00, pauli] at h00 ⊢
    -- h00 and goal are now the same explicit complex equation
    exact h00
  have p01 : (∑ k : Fin 3, c k • pauli k) 0 1 = 0 := by
    rw [Fin.sum_univ_three] at h01 ⊢
    simp only [Matrix.add_apply, Matrix.smul_apply, genH_entry_01, pauli] at h01 ⊢
    exact h01
  have p10 : (∑ k : Fin 3, c k • pauli k) 1 0 = 0 := by
    rw [Fin.sum_univ_three] at h10 ⊢
    simp only [Matrix.add_apply, Matrix.smul_apply, genH_entry_10, pauli] at h10 ⊢
    exact h10
  exact pauli_linear_independent c p00 p01 p10

/-- genM acts as gellMann on triplet T0=(18,20,22): entry (18,20). -/
theorem genM_entry_T0_01 (a : Fin 8) :
    genM a ⟨18, by norm_num⟩ ⟨20, by norm_num⟩ = gellMann a 0 1 := by
  simp [genM, tripletOf]

/-- genM acts as gellMann on triplet T0=(18,20,22): entry (20,18). -/
theorem genM_entry_T0_10 (a : Fin 8) :
    genM a ⟨20, by norm_num⟩ ⟨18, by norm_num⟩ = gellMann a 1 0 := by
  simp [genM, tripletOf]

/-- genM acts as gellMann on triplet T0=(18,20,22): entry (18,22). -/
theorem genM_entry_T0_02 (a : Fin 8) :
    genM a ⟨18, by norm_num⟩ ⟨22, by norm_num⟩ = gellMann a 0 2 := by
  simp [genM, tripletOf]

/-- genM acts as gellMann on triplet T0=(18,20,22): entry (22,18). -/
theorem genM_entry_T0_20 (a : Fin 8) :
    genM a ⟨22, by norm_num⟩ ⟨18, by norm_num⟩ = gellMann a 2 0 := by
  simp [genM, tripletOf]

/-- genM acts as gellMann on triplet T0=(18,20,22): entry (20,22). -/
theorem genM_entry_T0_12 (a : Fin 8) :
    genM a ⟨20, by norm_num⟩ ⟨22, by norm_num⟩ = gellMann a 1 2 := by
  simp [genM, tripletOf]

/-- genM acts as gellMann on triplet T0=(18,20,22): entry (22,20). -/
theorem genM_entry_T0_21 (a : Fin 8) :
    genM a ⟨22, by norm_num⟩ ⟨20, by norm_num⟩ = gellMann a 2 1 := by
  simp [genM, tripletOf]

/-- genM acts as gellMann on triplet T0=(18,20,22): entry (18,18). -/
theorem genM_entry_T0_00 (a : Fin 8) :
    genM a ⟨18, by norm_num⟩ ⟨18, by norm_num⟩ = gellMann a 0 0 := by
  simp [genM, tripletOf]

/-- genM acts as gellMann on triplet T0=(18,20,22): entry (20,20). -/
theorem genM_entry_T0_11 (a : Fin 8) :
    genM a ⟨20, by norm_num⟩ ⟨20, by norm_num⟩ = gellMann a 1 1 := by
  simp [genM, tripletOf]

/-- Gell-Mann matrices are linearly independent (8-entry version). Tier T3. -/
theorem gellMann_linear_independent (c : Fin 8 → ℂ)
    (e01 : (∑ a : Fin 8, c a • gellMann a) 0 1 = 0)
    (e10 : (∑ a : Fin 8, c a • gellMann a) 1 0 = 0)
    (e02 : (∑ a : Fin 8, c a • gellMann a) 0 2 = 0)
    (e20 : (∑ a : Fin 8, c a • gellMann a) 2 0 = 0)
    (e12 : (∑ a : Fin 8, c a • gellMann a) 1 2 = 0)
    (e21 : (∑ a : Fin 8, c a • gellMann a) 2 1 = 0)
    (e00 : (∑ a : Fin 8, c a • gellMann a) 0 0 = 0)
    (e11 : (∑ a : Fin 8, c a • gellMann a) 1 1 = 0) :
    ∀ a, c a = 0 := by
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  -- Helper: from x - y*I = 0 and x + y*I = 0, get x = 0 and y = 0.
  have pair_zero : ∀ x y : ℂ, x + -(y * Complex.I) = 0 → x + y * Complex.I = 0 →
      x = 0 ∧ y = 0 := by
    intro x y h1 h2
    have hsum : (x + -(y * Complex.I)) + (x + y * Complex.I) = 0 := by rw [h1, h2]; ring
    have hx : 2 * x = 0 := by linear_combination hsum
    have hx0 : x = 0 := by simpa using hx
    have hy : y * Complex.I = 0 := by
      have h := h1
      rw [hx0] at h
      simpa using h
    exact ⟨hx0, (mul_eq_zero.mp hy).resolve_right hI⟩
  -- Extract the off-diagonal pairs by direct computation.
  -- For (0,1): only gellMann 0 and 1 contribute.
  have g01 : ∀ a : Fin 8, gellMann a 0 1 =
      (if a = 0 then (1 : ℂ) else 0) + (if a = 1 then -Complex.I else 0) := by
    intro a
    fin_cases a <;> simp [gellMann]
  have g10 : ∀ a : Fin 8, gellMann a 1 0 =
      (if a = 0 then (1 : ℂ) else 0) + (if a = 1 then Complex.I else 0) := by
    intro a
    fin_cases a <;> simp [gellMann]
  -- Compute e01, e10 explicitly.
  have he01 : c 0 + -(c 1 * Complex.I) = 0 := by
    have h := e01
    rw [Fin.sum_univ_eight] at h
    simp only [Matrix.add_apply, Matrix.smul_apply, g01] at h
    simpa using h
  have he10 : c 0 + c 1 * Complex.I = 0 := by
    have h := e10
    rw [Fin.sum_univ_eight] at h
    simp only [Matrix.add_apply, Matrix.smul_apply, g10] at h
    simpa using h
  have h01 := pair_zero (c 0) (c 1) he01 he10
  -- For (0,2), (2,0): only gellMann 3 and 4 contribute.
  have g02 : ∀ a : Fin 8, gellMann a 0 2 =
      (if a = 3 then (1 : ℂ) else 0) + (if a = 4 then -Complex.I else 0) := by
    intro a
    fin_cases a <;> simp [gellMann]
  have g20 : ∀ a : Fin 8, gellMann a 2 0 =
      (if a = 3 then (1 : ℂ) else 0) + (if a = 4 then Complex.I else 0) := by
    intro a
    fin_cases a <;> simp [gellMann]
  have he02 : c 3 + -(c 4 * Complex.I) = 0 := by
    have h := e02
    rw [Fin.sum_univ_eight] at h
    simp only [Matrix.add_apply, Matrix.smul_apply, g02] at h
    simpa using h
  have he20 : c 3 + c 4 * Complex.I = 0 := by
    have h := e20
    rw [Fin.sum_univ_eight] at h
    simp only [Matrix.add_apply, Matrix.smul_apply, g20] at h
    simpa using h
  have h34 := pair_zero (c 3) (c 4) he02 he20
  -- For (1,2), (2,1): only gellMann 5 and 6 contribute.
  have g12 : ∀ a : Fin 8, gellMann a 1 2 =
      (if a = 5 then (1 : ℂ) else 0) + (if a = 6 then -Complex.I else 0) := by
    intro a
    fin_cases a <;> simp [gellMann]
  have g21 : ∀ a : Fin 8, gellMann a 2 1 =
      (if a = 5 then (1 : ℂ) else 0) + (if a = 6 then Complex.I else 0) := by
    intro a
    fin_cases a <;> simp [gellMann]
  have he12 : c 5 + -(c 6 * Complex.I) = 0 := by
    have h := e12
    rw [Fin.sum_univ_eight] at h
    simp only [Matrix.add_apply, Matrix.smul_apply, g12] at h
    simpa using h
  have he21 : c 5 + c 6 * Complex.I = 0 := by
    have h := e21
    rw [Fin.sum_univ_eight] at h
    simp only [Matrix.add_apply, Matrix.smul_apply, g21] at h
    simpa using h
  have h56 := pair_zero (c 5) (c 6) he12 he21
  -- Diagonal: (0,0) has gellMann 2 = 1, gellMann 7 = 1/√3.
  -- (1,1) has gellMann 2 = -1, gellMann 7 = 1/√3.
  have g00 : ∀ a : Fin 8, gellMann a 0 0 =
      (if a = 2 then (1 : ℂ) else 0) + (if a = 7 then (Real.sqrt 3 : ℂ)⁻¹ else 0) := by
    intro a
    fin_cases a <;> simp [gellMann]
  have g11 : ∀ a : Fin 8, gellMann a 1 1 =
      (if a = 2 then (-1 : ℂ) else 0) + (if a = 7 then (Real.sqrt 3 : ℂ)⁻¹ else 0) := by
    intro a
    fin_cases a <;> simp [gellMann]
  have he00 : c 2 + c 7 * (Real.sqrt 3 : ℂ)⁻¹ = 0 := by
    have h := e00
    rw [Fin.sum_univ_eight] at h
    simp only [Matrix.add_apply, Matrix.smul_apply, g00] at h
    simpa using h
  have he11 : -(c 2) + c 7 * (Real.sqrt 3 : ℂ)⁻¹ = 0 := by
    have h := e11
    rw [Fin.sum_univ_eight] at h
    simp only [Matrix.add_apply, Matrix.smul_apply, g11] at h
    simpa using h
  have h27 : c 2 = 0 ∧ c 7 = 0 := by
    have hsqrt : (Real.sqrt 3 : ℂ) ≠ 0 := by
      have h3 : (0 : ℝ) < 3 := by norm_num
      have h := Real.sqrt_ne_zero'.mpr h3
      exact_mod_cast h
    have hsum : (c 2 + c 7 * (Real.sqrt 3 : ℂ)⁻¹) + (-(c 2) + c 7 * (Real.sqrt 3 : ℂ)⁻¹) = 0 := by
      rw [he00, he11]; ring
    have h7 : 2 * (c 7 * (Real.sqrt 3 : ℂ)⁻¹) = 0 := by linear_combination hsum
    have h7' : c 7 * (Real.sqrt 3 : ℂ)⁻¹ = 0 := by simpa using h7
    have hc7 : c 7 = 0 := (mul_eq_zero.mp h7').resolve_right (inv_ne_zero hsqrt)
    have hc2 : c 2 = 0 := by
      rw [hc7] at he00
      simpa using he00
    exact ⟨hc2, hc7⟩
  intro a
  fin_cases a
  · exact h01.1
  · exact h01.2
  · exact h27.1
  · exact h34.1
  · exact h34.2
  · exact h56.1
  · exact h56.2
  · exact h27.2

/-- The M₃-block generators are linearly independent. Tier T3. -/
theorem genM_linear_independent (c : Fin 8 → ℂ)
    (e01 : (∑ a : Fin 8, c a • genM a) ⟨18, by norm_num⟩ ⟨20, by norm_num⟩ = 0)
    (e10 : (∑ a : Fin 8, c a • genM a) ⟨20, by norm_num⟩ ⟨18, by norm_num⟩ = 0)
    (e02 : (∑ a : Fin 8, c a • genM a) ⟨18, by norm_num⟩ ⟨22, by norm_num⟩ = 0)
    (e20 : (∑ a : Fin 8, c a • genM a) ⟨22, by norm_num⟩ ⟨18, by norm_num⟩ = 0)
    (e12 : (∑ a : Fin 8, c a • genM a) ⟨20, by norm_num⟩ ⟨22, by norm_num⟩ = 0)
    (e21 : (∑ a : Fin 8, c a • genM a) ⟨22, by norm_num⟩ ⟨20, by norm_num⟩ = 0)
    (e00 : (∑ a : Fin 8, c a • genM a) ⟨18, by norm_num⟩ ⟨18, by norm_num⟩ = 0)
    (e11 : (∑ a : Fin 8, c a • genM a) ⟨20, by norm_num⟩ ⟨20, by norm_num⟩ = 0) :
    ∀ a, c a = 0 := by
  -- Convert each to the corresponding gellMann-sum entry.
  have p01 : (∑ a : Fin 8, c a • gellMann a) 0 1 = 0 := by
    rw [Fin.sum_univ_eight] at e01 ⊢
    simp only [Matrix.add_apply, Matrix.smul_apply, genM_entry_T0_01] at e01 ⊢
    exact e01
  have p10 : (∑ a : Fin 8, c a • gellMann a) 1 0 = 0 := by
    rw [Fin.sum_univ_eight] at e10 ⊢
    simp only [Matrix.add_apply, Matrix.smul_apply, genM_entry_T0_10] at e10 ⊢
    exact e10
  have p02 : (∑ a : Fin 8, c a • gellMann a) 0 2 = 0 := by
    rw [Fin.sum_univ_eight] at e02 ⊢
    simp only [Matrix.add_apply, Matrix.smul_apply, genM_entry_T0_02] at e02 ⊢
    exact e02
  have p20 : (∑ a : Fin 8, c a • gellMann a) 2 0 = 0 := by
    rw [Fin.sum_univ_eight] at e20 ⊢
    simp only [Matrix.add_apply, Matrix.smul_apply, genM_entry_T0_20] at e20 ⊢
    exact e20
  have p12 : (∑ a : Fin 8, c a • gellMann a) 1 2 = 0 := by
    rw [Fin.sum_univ_eight] at e12 ⊢
    simp only [Matrix.add_apply, Matrix.smul_apply, genM_entry_T0_12] at e12 ⊢
    exact e12
  have p21 : (∑ a : Fin 8, c a • gellMann a) 2 1 = 0 := by
    rw [Fin.sum_univ_eight] at e21 ⊢
    simp only [Matrix.add_apply, Matrix.smul_apply, genM_entry_T0_21] at e21 ⊢
    exact e21
  have p00 : (∑ a : Fin 8, c a • gellMann a) 0 0 = 0 := by
    rw [Fin.sum_univ_eight] at e00 ⊢
    simp only [Matrix.add_apply, Matrix.smul_apply, genM_entry_T0_00] at e00 ⊢
    exact e00
  have p11 : (∑ a : Fin 8, c a • gellMann a) 1 1 = 0 := by
    rw [Fin.sum_univ_eight] at e11 ⊢
    simp only [Matrix.add_apply, Matrix.smul_apply, genM_entry_T0_11] at e11 ⊢
    exact e11
  exact gellMann_linear_independent c p01 p10 p02 p20 p12 p21 p00 p11

/-- genH vanishes at (8,8): outside the 0-7 support. -/
theorem genH_at_88_zero (k : Fin 3) :
    genH k ⟨8, by norm_num⟩ ⟨8, by norm_num⟩ = 0 := by
  by_contra h
  have := genH_supp k _ _ h
  simp at this

/-- genM vanishes at (8,8): 8 is not in any triplet. -/
theorem genM_at_88_zero (a : Fin 8) :
    genM a ⟨8, by norm_num⟩ ⟨8, by norm_num⟩ = 0 := by
  simp [genM, tripletOf]

/-- genC vanishes at (0,0): 0 not in ℂ-support. -/
theorem genC_at_00_zero :
    genC ⟨0, by norm_num⟩ ⟨0, by norm_num⟩ = 0 := by
  simp [genC]

/-- genC vanishes at (0,1): off-diagonal. -/
theorem genC_at_01_zero :
    genC ⟨0, by norm_num⟩ ⟨1, by norm_num⟩ = 0 := by
  simp [genC]

/-- genC vanishes at (1,0): off-diagonal. -/
theorem genC_at_10_zero :
    genC ⟨1, by norm_num⟩ ⟨0, by norm_num⟩ = 0 := by
  simp [genC]

/-- genM vanishes on the (0,1) doublet: not in any triplet. -/
theorem genM_at_doublet01_zero (a : Fin 8) :
    genM a ⟨0, by norm_num⟩ ⟨0, by norm_num⟩ = 0 ∧
    genM a ⟨0, by norm_num⟩ ⟨1, by norm_num⟩ = 0 ∧
    genM a ⟨1, by norm_num⟩ ⟨0, by norm_num⟩ = 0 := by
  simp [genM, tripletOf]

/-- genC vanishes on triplet T0 entries: diagonal + not in support. -/
theorem genC_at_T0_zero :
    genC ⟨18, by norm_num⟩ ⟨20, by norm_num⟩ = 0 ∧
    genC ⟨20, by norm_num⟩ ⟨18, by norm_num⟩ = 0 ∧
    genC ⟨18, by norm_num⟩ ⟨22, by norm_num⟩ = 0 ∧
    genC ⟨22, by norm_num⟩ ⟨18, by norm_num⟩ = 0 ∧
    genC ⟨20, by norm_num⟩ ⟨22, by norm_num⟩ = 0 ∧
    genC ⟨22, by norm_num⟩ ⟨20, by norm_num⟩ = 0 ∧
    genC ⟨18, by norm_num⟩ ⟨18, by norm_num⟩ = 0 ∧
    genC ⟨20, by norm_num⟩ ⟨20, by norm_num⟩ = 0 := by
  simp [genC]

/-- genH vanishes on triplet T0 entries: outside 0-7 support. -/
theorem genH_at_T0_zero (k : Fin 3) :
    genH k ⟨18, by norm_num⟩ ⟨20, by norm_num⟩ = 0 ∧
    genH k ⟨20, by norm_num⟩ ⟨18, by norm_num⟩ = 0 ∧
    genH k ⟨18, by norm_num⟩ ⟨22, by norm_num⟩ = 0 ∧
    genH k ⟨22, by norm_num⟩ ⟨18, by norm_num⟩ = 0 ∧
    genH k ⟨20, by norm_num⟩ ⟨22, by norm_num⟩ = 0 ∧
    genH k ⟨22, by norm_num⟩ ⟨20, by norm_num⟩ = 0 ∧
    genH k ⟨18, by norm_num⟩ ⟨18, by norm_num⟩ = 0 ∧
    genH k ⟨20, by norm_num⟩ ⟨20, by norm_num⟩ = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (by_contra h; have := genH_supp k _ _ h; simp at this)

/-- Faithfulness (block form): the three blocks act independently on disjoint
    supports. If a ℂ-multiple of genC plus an ℍ-combination plus an M₃-combination
    vanishes as a 32×32 matrix, then every coefficient vanishes.
    This is the kernel = {0} characterization: the representation is faithful.
    Tier T3. -/
theorem faithful_blocks (c : ℂ) (cH : Fin 3 → ℂ) (cM : Fin 8 → ℂ)
    (h : c • genC + (∑ k : Fin 3, cH k • genH k) + (∑ a : Fin 8, cM a • genM a) = 0) :
    c = 0 ∧ (∀ k, cH k = 0) ∧ (∀ a, cM a = 0) := by
  -- Helper: extract the (i,j) entry equation from h.
  have hentry : ∀ i j : I32,
      (c • genC) i j + (∑ k : Fin 3, cH k • genH k) i j
        + (∑ a : Fin 8, cM a • genM a) i j = 0 := by
    intro i j
    have h2 := congrFun (congrFun h i) j
    simpa [Matrix.add_apply] using h2
  -- Vanishing of the genH-sum at (8,8).
  have hH88 : (∑ k : Fin 3, cH k • genH k) ⟨8, by norm_num⟩ ⟨8, by norm_num⟩ = 0 := by
    rw [Fin.sum_univ_three]
    simp only [Matrix.add_apply, Matrix.smul_apply, genH_at_88_zero, smul_zero, add_zero]
  -- Vanishing of the genM-sum at (8,8).
  have hM88 : (∑ a : Fin 8, cM a • genM a) ⟨8, by norm_num⟩ ⟨8, by norm_num⟩ = 0 := by
    rw [Fin.sum_univ_eight]
    simp only [Matrix.add_apply, Matrix.smul_apply, genM_at_88_zero, smul_zero]
    simp
  -- Step 1: c = 0 from the (8,8) entry. Only genC is nonzero there.
  have hc : c = 0 := by
    have h88 := hentry ⟨8, by norm_num⟩ ⟨8, by norm_num⟩
    simp only [Matrix.smul_apply] at h88
    rw [hH88, hM88] at h88
    simp at h88
    rw [genC_diag_val] at h88
    simpa using h88
  -- Vanishing of the genM-sum on the (0,1) doublet entries.
  have hM_d00 : (∑ a : Fin 8, cM a • genM a) ⟨0, by norm_num⟩ ⟨0, by norm_num⟩ = 0 := by
    rw [Fin.sum_univ_eight]
    simp only [Matrix.add_apply, Matrix.smul_apply,
      fun a => (genM_at_doublet01_zero a).1, smul_zero]
    simp
  have hM_d01 : (∑ a : Fin 8, cM a • genM a) ⟨0, by norm_num⟩ ⟨1, by norm_num⟩ = 0 := by
    rw [Fin.sum_univ_eight]
    simp only [Matrix.add_apply, Matrix.smul_apply,
      fun a => (genM_at_doublet01_zero a).2.1, smul_zero]
    simp
  have hM_d10 : (∑ a : Fin 8, cM a • genM a) ⟨1, by norm_num⟩ ⟨0, by norm_num⟩ = 0 := by
    rw [Fin.sum_univ_eight]
    simp only [Matrix.add_apply, Matrix.smul_apply,
      fun a => (genM_at_doublet01_zero a).2.2, smul_zero]
    simp
  -- Step 2: cH = 0 from the doublet entries. genC and genM vanish there.
  have hH00 : (∑ k : Fin 3, cH k • genH k) ⟨0, by norm_num⟩ ⟨0, by norm_num⟩ = 0 := by
    have h0 := hentry ⟨0, by norm_num⟩ ⟨0, by norm_num⟩
    simp only [Matrix.smul_apply, genC_at_00_zero, mul_zero, zero_add] at h0
    rw [hM_d00] at h0
    simpa using h0
  have hH01 : (∑ k : Fin 3, cH k • genH k) ⟨0, by norm_num⟩ ⟨1, by norm_num⟩ = 0 := by
    have h0 := hentry ⟨0, by norm_num⟩ ⟨1, by norm_num⟩
    simp only [Matrix.smul_apply, genC_at_01_zero, mul_zero, zero_add] at h0
    rw [hM_d01] at h0
    simpa using h0
  have hH10 : (∑ k : Fin 3, cH k • genH k) ⟨1, by norm_num⟩ ⟨0, by norm_num⟩ = 0 := by
    have h0 := hentry ⟨1, by norm_num⟩ ⟨0, by norm_num⟩
    simp only [Matrix.smul_apply, genC_at_10_zero, mul_zero, zero_add] at h0
    rw [hM_d10] at h0
    simpa using h0
  have hcH := genH_linear_independent cH hH00 hH01 hH10
  -- Vanishing of the genH-sum on the eight T0 entries.
  have hH_T0_01 : (∑ k : Fin 3, cH k • genH k) ⟨18, by norm_num⟩ ⟨20, by norm_num⟩ = 0 := by
    rw [Fin.sum_univ_three]
    simp only [Matrix.add_apply, Matrix.smul_apply,
      fun k => (genH_at_T0_zero k).1, smul_zero]
    simp
  have hH_T0_10 : (∑ k : Fin 3, cH k • genH k) ⟨20, by norm_num⟩ ⟨18, by norm_num⟩ = 0 := by
    rw [Fin.sum_univ_three]
    simp only [Matrix.add_apply, Matrix.smul_apply,
      fun k => (genH_at_T0_zero k).2.1, smul_zero]
    simp
  have hH_T0_02 : (∑ k : Fin 3, cH k • genH k) ⟨18, by norm_num⟩ ⟨22, by norm_num⟩ = 0 := by
    rw [Fin.sum_univ_three]
    simp only [Matrix.add_apply, Matrix.smul_apply,
      fun k => (genH_at_T0_zero k).2.2.1, smul_zero]
    simp
  have hH_T0_20 : (∑ k : Fin 3, cH k • genH k) ⟨22, by norm_num⟩ ⟨18, by norm_num⟩ = 0 := by
    rw [Fin.sum_univ_three]
    simp only [Matrix.add_apply, Matrix.smul_apply,
      fun k => (genH_at_T0_zero k).2.2.2.1, smul_zero]
    simp
  have hH_T0_12 : (∑ k : Fin 3, cH k • genH k) ⟨20, by norm_num⟩ ⟨22, by norm_num⟩ = 0 := by
    rw [Fin.sum_univ_three]
    simp only [Matrix.add_apply, Matrix.smul_apply,
      fun k => (genH_at_T0_zero k).2.2.2.2.1, smul_zero]
    simp
  have hH_T0_21 : (∑ k : Fin 3, cH k • genH k) ⟨22, by norm_num⟩ ⟨20, by norm_num⟩ = 0 := by
    rw [Fin.sum_univ_three]
    simp only [Matrix.add_apply, Matrix.smul_apply,
      fun k => (genH_at_T0_zero k).2.2.2.2.2.1, smul_zero]
    simp
  have hH_T0_00 : (∑ k : Fin 3, cH k • genH k) ⟨18, by norm_num⟩ ⟨18, by norm_num⟩ = 0 := by
    rw [Fin.sum_univ_three]
    simp only [Matrix.add_apply, Matrix.smul_apply,
      fun k => (genH_at_T0_zero k).2.2.2.2.2.2.1, smul_zero]
    simp
  have hH_T0_11 : (∑ k : Fin 3, cH k • genH k) ⟨20, by norm_num⟩ ⟨20, by norm_num⟩ = 0 := by
    rw [Fin.sum_univ_three]
    simp only [Matrix.add_apply, Matrix.smul_apply,
      fun k => (genH_at_T0_zero k).2.2.2.2.2.2.2, smul_zero]
    simp
  -- Step 3: extract the eight genM-sum entries on T0.
  -- Each: hentry gives c•genC + genH-sum + genM-sum = 0;
  -- genC vanishes (genC_at_T0_zero), genH-sum vanishes (above).
  have hC_T0 := genC_at_T0_zero
  have e01 : (∑ a : Fin 8, cM a • genM a) ⟨18, by norm_num⟩ ⟨20, by norm_num⟩ = 0 := by
    have h0 := hentry ⟨18, by norm_num⟩ ⟨20, by norm_num⟩
    simp only [Matrix.smul_apply] at h0
    rw [hC_T0.1, hH_T0_01] at h0
    simp at h0
    simpa using h0
  have e10 : (∑ a : Fin 8, cM a • genM a) ⟨20, by norm_num⟩ ⟨18, by norm_num⟩ = 0 := by
    have h0 := hentry ⟨20, by norm_num⟩ ⟨18, by norm_num⟩
    simp only [Matrix.smul_apply] at h0
    rw [hC_T0.2.1, hH_T0_10] at h0
    simp at h0
    simpa using h0
  have e02 : (∑ a : Fin 8, cM a • genM a) ⟨18, by norm_num⟩ ⟨22, by norm_num⟩ = 0 := by
    have h0 := hentry ⟨18, by norm_num⟩ ⟨22, by norm_num⟩
    simp only [Matrix.smul_apply] at h0
    rw [hC_T0.2.2.1, hH_T0_02] at h0
    simp at h0
    simpa using h0
  have e20 : (∑ a : Fin 8, cM a • genM a) ⟨22, by norm_num⟩ ⟨18, by norm_num⟩ = 0 := by
    have h0 := hentry ⟨22, by norm_num⟩ ⟨18, by norm_num⟩
    simp only [Matrix.smul_apply] at h0
    rw [hC_T0.2.2.2.1, hH_T0_20] at h0
    simp at h0
    simpa using h0
  have e12 : (∑ a : Fin 8, cM a • genM a) ⟨20, by norm_num⟩ ⟨22, by norm_num⟩ = 0 := by
    have h0 := hentry ⟨20, by norm_num⟩ ⟨22, by norm_num⟩
    simp only [Matrix.smul_apply] at h0
    rw [hC_T0.2.2.2.2.1, hH_T0_12] at h0
    simp at h0
    simpa using h0
  have e21 : (∑ a : Fin 8, cM a • genM a) ⟨22, by norm_num⟩ ⟨20, by norm_num⟩ = 0 := by
    have h0 := hentry ⟨22, by norm_num⟩ ⟨20, by norm_num⟩
    simp only [Matrix.smul_apply] at h0
    rw [hC_T0.2.2.2.2.2.1, hH_T0_21] at h0
    simp at h0
    simpa using h0
  have e00 : (∑ a : Fin 8, cM a • genM a) ⟨18, by norm_num⟩ ⟨18, by norm_num⟩ = 0 := by
    have h0 := hentry ⟨18, by norm_num⟩ ⟨18, by norm_num⟩
    simp only [Matrix.smul_apply] at h0
    rw [hC_T0.2.2.2.2.2.2.1, hH_T0_00] at h0
    simp at h0
    simpa using h0
  have e11 : (∑ a : Fin 8, cM a • genM a) ⟨20, by norm_num⟩ ⟨20, by norm_num⟩ = 0 := by
    have h0 := hentry ⟨20, by norm_num⟩ ⟨20, by norm_num⟩
    simp only [Matrix.smul_apply] at h0
    rw [hC_T0.2.2.2.2.2.2.2, hH_T0_11] at h0
    simp at h0
    simpa using h0
  have hcM := genM_linear_independent cM e01 e10 e02 e20 e12 e21 e00 e11
  exact ⟨hc, hcH, hcM⟩

/-! ## The one-generation SM Dirac ansatz (D_F) -/

/-- The 8×8 Yukawa mass block A on (left particles 0–7) × (right particles 8–15).
    Conventional one-generation flavour assignment (the choice of placement inside
    degenerate irreps is an ANSATZ, not derived):
    A[0,0] = yν couples ν_L(0) ↔ ν_R(8);  A[1,1] = ye couples e_L(1) ↔ e_R(9);
    A[2,2] = A[4,4] = A[6,6] = yU couple u_L ↔ u_R over the three colours;
    A[3,3] = A[5,5] = A[7,7] = yD couple d_L ↔ d_R over the three colours.
    Matches the `sm_directions` flavour slots of `attack4_corrected.py` (T4).
    Tier T2. -/
def yukawaBlock (yNu yE yU yD : ℂ) : Block8 :=
  Matrix.diagonal (![yNu, yE, yU, yD, yU, yD, yU, yD] : Fin 8 → ℂ)

/-- The 8×8 Majorana block E on (right antiparticles 24–31) × (right particles 8–15).
    E[0,0] = yR couples ν_R(8) ↔ ν̄_R(24). Diagonal, hence symmetric — the symmetry
    E = Eᵀ is exactly what KO-dimension-6 J-compatibility requires of this block.
    Tier T2. -/
def majoranaBlock (yR : ℂ) : Block8 :=
  Matrix.diagonal fun k : Fin 8 => if k.val = 0 then yR else 0

/-- The Majorana block is symmetric. Tier T3. -/
theorem majoranaBlock_symmetric (yR : ℂ) :
    (majoranaBlock yR).transpose = majoranaBlock yR := by
  ext i j
  rw [Matrix.transpose_apply]
  unfold majoranaBlock
  rw [Matrix.diagonal_apply, Matrix.diagonal_apply]
  by_cases h : j = i
  · simp [h]
  · simp [h, Ne.symm h]

/-- The one-generation SM Dirac ansatz on ℂ³².
    D_F = buildDirac A Ā 0 E with A = yukawaBlock, E = majoranaBlock, i.e.
    D = [  0   A   0   0 ]   rows 0–7   (H_L)
        [  A†  0   0  E† ]   rows 8–15  (H_R)
        [  0   0   0   Ā ]   rows 16–23 (H_L^c)
        [  0   E  Aᵀ  0 ]   rows 24–31 (H_R^c)

    HONESTY (read before citing):
    * The five-block form (A, B, C, E) with B = Ā, C = 0 is an ANSATZ — imposed,
      not derived. Corrected Attack 4 (T4, 2026-09-27): order-one alone leaves a
      46-dimensional nullspace; the 10 real SM directions (Re/Im of yν, yE, yU, yD,
      yR) lie in it (residuals ≤ 2.2e−13) but 36 extra dimensions are
      uncharacterized. Order-one does NOT select this form alone.
    * One generation only (ℂ³²); flavour placement inside degenerate irreps is
      conventional (Martinetti §2.5 / Chamseddine–Connes–Marcolli).
    * Generalizes `ThetLogos.FiniteSpectralTriple.DF_oneGen` (real Yukawas, no
      Majorana) to complex Yukawas plus the Majorana block.
    Tier T2 (definition); grading-odd, self-adjoint, J-compatible are Tier T3 below. -/
def smDirac (yNu yE yU yD yR : ℂ) : Matrix I32 I32 ℂ :=
  buildDirac (yukawaBlock yNu yE yU yD)
    ((yukawaBlock yNu yE yU yD).map (starRingEnd ℂ))
    0 (majoranaBlock yR)

/-- Grading-oddness of the ansatz: {Γ, D_F} = 0. Tier T3 (proved). -/
theorem smDirac_grading_odd (yNu yE yU yD yR : ℂ) :
    gammaF * smDirac yNu yE yU yD yR + smDirac yNu yE yU yD yR * gammaF = 0 :=
  buildDirac_gamma_odd _ _ _ _

/-- Self-adjointness of the ansatz: D_F^* = D_F. Tier T3 (proved). -/
theorem smDirac_self_adjoint (yNu yE yU yD yR : ℂ) :
    (smDirac yNu yE yU yD yR).conjTranspose = smDirac yNu yE yU yD yR :=
  buildDirac_self_adjoint _ _ _ _

/-- J-compatibility, KO-dimension 6: JD = DJ, in linear form UJ·D̄ = D·UJ
    (for the antilinear J = UJ ∘ conjugation). Derived from the conjugation form
    `buildDirac_J_compat` via UJ² = 1. Tier T3 (proved). -/
theorem smDirac_J_compat (yNu yE yU yD yR : ℂ) :
    UJ * (smDirac yNu yE yU yD yR).map (star : ℂ → ℂ)
      = smDirac yNu yE yU yD yR * UJ := by
  have hJ := buildDirac_J_compat (yukawaBlock yNu yE yU yD)
    ((yukawaBlock yNu yE yU yD).map (starRingEnd ℂ))
    0 (majoranaBlock yR)
    rfl Matrix.transpose_zero.symm (majoranaBlock_symmetric yR).symm
  have h2 : UJ * (smDirac yNu yE yU yD yR).map (star : ℂ → ℂ) * UJ
      = smDirac yNu yE yU yD yR := hJ
  have hU : UJ * UJ = (1 : Matrix I32 I32 ℂ) := UJ_mul_self
  calc UJ * (smDirac yNu yE yU yD yR).map (star : ℂ → ℂ)
      = (UJ * (smDirac yNu yE yU yD yR).map (star : ℂ → ℂ) * UJ) * UJ := by
        rw [mul_assoc, hU, mul_one]
    _ = smDirac yNu yE yU yD yR * UJ := by rw [h2]

/-- Order-one for the ansatz Dirac: [[D_F, π(a)], π°(b)] = 0 over the 12 selected
    generators (144 pairs).
    PROVEN 2026-09-27 (`smDirac_order_one`): all 144 double commutators vanish
    for arbitrary complex yν, yE, yU, yD, yR. The five-block form of `smDirac`
    remains an imposed ansatz, not a consequence of order-one — T4 evidence
    (corrected Attack 4, 2026-09-27): the numerical order-one nullspace has
    dimension 46 real (≈36 extra directions beyond the 10 SM ones). -/
def smDiracOrderOne (yNu yE yU yD yR : ℂ) : Prop :=
  ∀ g1 g2 : Fin 12,
    (smDirac yNu yE yU yD yR * smGen g1 - smGen g1 * smDirac yNu yE yU yD yR)
      * smGenOp g2
      - smGenOp g2
        * (smDirac yNu yE yU yD yR * smGen g1 - smGen g1 * smDirac yNu yE yU yD yR)
      = 0

/-! ## Order-one for the ansatz: proof

Strategy (mirrors order-zero, but with D_F in the inner commutator):
* CB1 (color-blindness): [D, genM a] = 0 — D's antiparticle blocks are diagonal
  and constant on colour triplets. Proved entrywise.
* CB2 (opposite color-blindness): [D, (genM a)°] = 0 — from CB1 via the
  J-compatibility UJ·D̄ = D·UJ and Gell-Mann Hermiticity.
* Jacobi: [[D,G1],G2°] = [[D,G2°],G1] when [G1,G2°] = 0 (order-zero).
  This kills the (C,M°), (H,M°), (M,M°) cases via CB2/CB1.
* (C,H°), (H,H°): block-support disjointness (disjoint_mul_zero).
* (C,C°), (H,C°): (genC)° is diagonal and constant on the inner-commutator
  support (diag_mul_comm_of_const_on_supp).
* Assembly: fin_cases on the 12×12 pairs.
Tier T3. -/

/-- yukawaBlock is diagonal. -/
theorem yukawaBlock_supp (p q : Fin 8)
    (h : yukawaBlock yNu yE yU yD p q ≠ 0) : p = q := by
  unfold yukawaBlock at h
  rw [Matrix.diagonal_apply] at h
  by_contra hne
  rw [if_neg hne] at h
  exact h rfl

/-- yukawaBlock diagonal value. -/
theorem yukawaBlock_diag (p : Fin 8) :
    yukawaBlock yNu yE yU yD p p = ![yNu, yE, yU, yD, yU, yD, yU, yD] p := by
  unfold yukawaBlock
  rw [Matrix.diagonal_apply]
  simp

/-- majoranaBlock is supported only at (0,0). -/
theorem majoranaBlock_supp (p q : Fin 8)
    (h : majoranaBlock yR p q ≠ 0) : p = 0 ∧ q = 0 := by
  unfold majoranaBlock at h
  rw [Matrix.diagonal_apply] at h
  by_cases hpq : p = q
  · subst hpq
    rw [if_pos rfl] at h
    by_cases hp0 : p.val = 0
    · have hp0' : p = 0 := Fin.ext hp0
      exact ⟨hp0', hp0'⟩
    · rw [if_neg hp0] at h
      exact absurd rfl h
  · rw [if_neg hpq] at h
    exact absurd rfl h

/-- majoranaBlock value at (0,0). -/
theorem majoranaBlock_val : majoranaBlock yR 0 0 = yR := by
  unfold majoranaBlock
  rw [Matrix.diagonal_apply]
  simp

/-- Conjugate-transpose of majoranaBlock supported only at (0,0). -/
theorem majoranaBlock_conjT_supp (p q : Fin 8)
    (h : (majoranaBlock yR).conjTranspose p q ≠ 0) : p = 0 ∧ q = 0 := by
  rw [Matrix.conjTranspose_apply] at h
  have h2 : majoranaBlock yR q p ≠ 0 := by
    intro h0
    exact h (by rw [h0, star_zero])
  have h3 := majoranaBlock_supp q p h2
  exact ⟨h3.2, h3.1⟩

/-- Conjugate of yukawaBlock is diagonal (entrywise). -/
theorem yukawaBlock_conj_supp (p q : Fin 8)
    (h : ((yukawaBlock yNu yE yU yD).map (starRingEnd ℂ)) p q ≠ 0) : p = q := by
  rw [Matrix.map_apply] at h
  have h2 : yukawaBlock yNu yE yU yD p q ≠ 0 := by
    intro h0
    simp [h0] at h
  exact yukawaBlock_supp p q h2

/-- Conjugate-transpose of yukawaBlock: support implies q = p. -/
theorem yukawaBlock_conjT_supp (p q : Fin 8)
    (h : (yukawaBlock yNu yE yU yD).conjTranspose p q ≠ 0) : q = p := by
  rw [Matrix.conjTranspose_apply] at h
  have h2 : yukawaBlock yNu yE yU yD q p ≠ 0 := by
    intro h0
    rw [h0, star_zero] at h
    exact h rfl
  exact yukawaBlock_supp q p h2

/-- Conjugate-transpose of mapped yukawaBlock: support implies q = p. -/
theorem yukawaBlock_map_conjT_supp (p q : Fin 8)
    (h : ((yukawaBlock yNu yE yU yD).map (starRingEnd ℂ)).conjTranspose p q ≠ 0) :
    q = p := by
  rw [Matrix.conjTranspose_apply] at h
  have h2 : ((yukawaBlock yNu yE yU yD).map (starRingEnd ℂ)) q p ≠ 0 := by
    intro h0
    rw [h0, star_zero] at h
    exact h rfl
  exact yukawaBlock_conj_supp q p h2

/-- D_F entry support: six possible nonzero positions.
    Tier T3 helper. -/
theorem smDirac_Edag_entry_aux (yNu yE yU yD yR : ℂ) (i j : I32)
    (hi1 : ¬i.val < 8) (hi2 : i.val < 16)
    (hj1 : ¬j.val < 8) (hj2 : ¬j.val < 16) (hj3 : ¬j.val < 24) :
    smDirac yNu yE yU yD yR i j
      = (majoranaBlock yR).conjTranspose
        ⟨i.val - 8, by omega⟩ ⟨j.val - 24, by omega⟩ := by
  unfold smDirac
  exact buildDirac_Edag_entry _ _ _ _ i j hi1 hi2 hj1 hj2 hj3

theorem smDirac_B_entry_aux (yNu yE yU yD yR : ℂ) (i j : I32)
    (hi1 : ¬i.val < 8) (hi2 : ¬i.val < 16) (hi3 : i.val < 24)
    (hj1 : ¬j.val < 8) (hj2 : ¬j.val < 16) (hj3 : ¬j.val < 24) :
    smDirac yNu yE yU yD yR i j
      = ((yukawaBlock yNu yE yU yD).map (starRingEnd ℂ))
        ⟨i.val - 16, by omega⟩ ⟨j.val - 24, by omega⟩ := by
  unfold smDirac
  exact buildDirac_B_entry _ _ _ _ i j hi1 hi2 hi3 hj1 hj2 hj3

theorem smDirac_Bdag_entry_aux (yNu yE yU yD yR : ℂ) (i j : I32)
    (hi1 : ¬i.val < 8) (hi2 : ¬i.val < 16) (hi3 : ¬i.val < 24)
    (hj1 : ¬j.val < 8) (hj2 : ¬j.val < 16) (hj3 : j.val < 24) :
    smDirac yNu yE yU yD yR i j
      = (((yukawaBlock yNu yE yU yD).map (starRingEnd ℂ))).conjTranspose
        ⟨i.val - 24, by omega⟩ ⟨j.val - 16, by omega⟩ := by
  unfold smDirac
  exact buildDirac_Bdag_entry _ _ _ _ i j hi1 hi2 hi3 hj1 hj2 hj3

theorem smDirac_supp_aux (yNu yE yU yD yR : ℂ) (i j : I32)
    (h : smDirac yNu yE yU yD yR i j ≠ 0) :
    (i.val < 8 ∧ j.val = i.val + 8) ∨
    (8 ≤ i.val ∧ i.val < 16 ∧ j.val = i.val - 8) ∨
    (16 ≤ i.val ∧ i.val < 24 ∧ j.val = i.val + 8) ∨
    (24 ≤ i.val ∧ i.val < 32 ∧ j.val = i.val - 8) ∨
    (i.val = 8 ∧ j.val = 24) ∨
    (i.val = 24 ∧ j.val = 8) := by
  have h' : buildDirac (yukawaBlock yNu yE yU yD)
      ((yukawaBlock yNu yE yU yD).map (starRingEnd ℂ)) 0 (majoranaBlock yR) i j ≠ 0 := h
  by_cases hi8 : i.val < 8
  · by_cases hj8 : j.val < 8
    · have h0 : smDirac yNu yE yU yD yR i j = 0 := by
        unfold smDirac buildDirac; simp [hi8, hj8]
      exact absurd h0 h
    · by_cases hj16 : j.val < 16
      · have hval : smDirac yNu yE yU yD yR i j
            = yukawaBlock yNu yE yU yD ⟨i.val, hi8⟩ ⟨j.val - 8, by omega⟩ := by
          unfold smDirac buildDirac; simp [hi8, hj8, hj16]
        have hne := hval ▸ h
        have heq := yukawaBlock_supp _ _ hne
        have hveq : i.val = j.val - 8 := congrArg Fin.val heq
        left; exact ⟨hi8, by omega⟩
      · by_cases hj24 : j.val < 24
        · have h0 : smDirac yNu yE yU yD yR i j = 0 := by
            unfold smDirac buildDirac; simp [hi8, hj8, hj16, hj24]
          exact absurd h0 h
        · have h0 : smDirac yNu yE yU yD yR i j = 0 := by
            unfold smDirac buildDirac; simp [hi8, hj8, hj16, hj24]
          exact absurd h0 h
  · by_cases hi16 : i.val < 16
    · by_cases hj8 : j.val < 8
      · have hval : smDirac yNu yE yU yD yR i j
            = (yukawaBlock yNu yE yU yD).conjTranspose
              ⟨i.val - 8, by omega⟩ ⟨j.val, hj8⟩ := by
          unfold smDirac buildDirac; simp [hi8, hi16, hj8]
        have hne := hval ▸ h
        have heq := yukawaBlock_conjT_supp ⟨i.val - 8, by omega⟩ ⟨j.val, hj8⟩ hne
        have hveq : j.val = i.val - 8 := congrArg Fin.val heq
        right; left; exact ⟨by omega, hi16, by omega⟩
      · by_cases hj16 : j.val < 16
        · have h0 : smDirac yNu yE yU yD yR i j = 0 := by
            unfold smDirac buildDirac; simp [hi8, hi16, hj8, hj16]
          exact absurd h0 h
        · by_cases hj24 : j.val < 24
          · have h0 : smDirac yNu yE yU yD yR i j = 0 := by
              unfold smDirac buildDirac; simp [hi8, hi16, hj8, hj16, hj24]
            exact absurd h0 h
          · have hval := smDirac_Edag_entry_aux yNu yE yU yD yR i j hi8 hi16 hj8 hj16 hj24
            have hne := hval ▸ h
            have hpair := majoranaBlock_conjT_supp _ _ hne
            have h1 : i.val - 8 = 0 := congrArg Fin.val hpair.1
            have h2 : j.val - 24 = 0 := congrArg Fin.val hpair.2
            right; right; right; right; left
            exact ⟨by omega, by omega⟩
    · by_cases hi24 : i.val < 24
      · by_cases hj8 : j.val < 8
        · have h0 : smDirac yNu yE yU yD yR i j = 0 := by
            unfold smDirac buildDirac; simp [hi8, hi16, hi24, hj8]
          exact absurd h0 h
        · by_cases hj16 : j.val < 16
          · have h0 : smDirac yNu yE yU yD yR i j = 0 := by
              unfold smDirac buildDirac; simp [hi8, hi16, hi24, hj8, hj16]
            exact absurd h0 h
          · by_cases hj24 : j.val < 24
            · have h0 : smDirac yNu yE yU yD yR i j = 0 := by
                unfold smDirac buildDirac; simp [hi8, hi16, hi24, hj8, hj16, hj24]
              exact absurd h0 h
            · have hval := smDirac_B_entry_aux yNu yE yU yD yR i j hi8 hi16 hi24 hj8 hj16 hj24
              have hne := hval ▸ h
              have heq := yukawaBlock_conj_supp _ _ hne
              have hveq : i.val - 16 = j.val - 24 := congrArg Fin.val heq
              right; right; left; exact ⟨by omega, hi24, by omega⟩
      · by_cases hj8 : j.val < 8
        · have h0 : smDirac yNu yE yU yD yR i j = 0 := by
            unfold smDirac buildDirac; simp [hi8, hi16, hi24, hj8]
          exact absurd h0 h
        · by_cases hj16 : j.val < 16
          · have hval : smDirac yNu yE yU yD yR i j
                = majoranaBlock yR ⟨i.val - 24, by omega⟩ ⟨j.val - 8, by omega⟩ := by
              unfold smDirac buildDirac; simp [hi8, hi16, hi24, hj8, hj16]
            have hne := hval ▸ h
            have hpair := majoranaBlock_supp _ _ hne
            have h1 : i.val - 24 = 0 := congrArg Fin.val hpair.1
            have h2 : j.val - 8 = 0 := congrArg Fin.val hpair.2
            right; right; right; right; right
            exact ⟨by omega, by omega⟩
          · by_cases hj24 : j.val < 24
            · have hval := buildDirac_Bdag_entry (yukawaBlock yNu yE yU yD)
                ((yukawaBlock yNu yE yU yD).map (starRingEnd ℂ)) 0 (majoranaBlock yR)
                i j hi8 hi16 hi24 hj8 hj16 hj24
              have hne := hval ▸ h'
              have heq := yukawaBlock_map_conjT_supp ⟨i.val - 24, by omega⟩
                ⟨j.val - 16, by omega⟩ hne
              have hveq : j.val - 16 = i.val - 24 := congrArg Fin.val heq
              right; right; right; left; exact ⟨by omega, by omega, by omega⟩
            · have h0 : smDirac yNu yE yU yD yR i j = 0 := by
                unfold smDirac buildDirac; simp [hi8, hi16, hi24, hj8, hj16, hj24]
              exact absurd h0 h



def dPartnerT : Fin 4 → Fin 4 := ![2, 3, 0, 1]

noncomputable def dScalar (yU yD : ℂ) : Fin 4 → ℂ := ![star yU, star yD, yU, yD]

theorem triplet_val0 (p : Fin 3) : (tripletIdx 0 p).val = 18 + 2 * p.val := by
  show (if (0 : Fin 4).val < 2 then 18 else 26) + 2 * p.val + (0 : Fin 4).val % 2 = _
  norm_num
theorem triplet_val1 (p : Fin 3) : (tripletIdx 1 p).val = 19 + 2 * p.val := by
  show (if (1 : Fin 4).val < 2 then 18 else 26) + 2 * p.val + (1 : Fin 4).val % 2 = _
  norm_num; omega
theorem triplet_val2 (p : Fin 3) : (tripletIdx 2 p).val = 26 + 2 * p.val := by
  show (if (2 : Fin 4).val < 2 then 18 else 26) + 2 * p.val + (2 : Fin 4).val % 2 = _
  norm_num
theorem triplet_val3 (p : Fin 3) : (tripletIdx 3 p).val = 27 + 2 * p.val := by
  show (if (3 : Fin 4).val < 2 then 18 else 26) + 2 * p.val + (3 : Fin 4).val % 2 = _
  norm_num; omega

-- S: support of triplet rows.
theorem row0 (yNu yE yU yD yR : ℂ) (p : Fin 3) (k : I32)
    (h : smDirac yNu yE yU yD yR (tripletIdx 0 p) k ≠ 0) :
    k = tripletIdx 2 p := by
  have hsupp := smDirac_supp_aux yNu yE yU yD yR (tripletIdx 0 p) k h
  rw [triplet_val0 p] at hsupp
  have hkv : k.val = 26 + 2 * p.val := by
    rcases hsupp with h | h | h | h | h | h <;> omega
  apply Fin.ext; rw [triplet_val2 p]; exact hkv
theorem row1 (yNu yE yU yD yR : ℂ) (p : Fin 3) (k : I32)
    (h : smDirac yNu yE yU yD yR (tripletIdx 1 p) k ≠ 0) :
    k = tripletIdx 3 p := by
  have hsupp := smDirac_supp_aux yNu yE yU yD yR (tripletIdx 1 p) k h
  rw [triplet_val1 p] at hsupp
  have hkv : k.val = 27 + 2 * p.val := by
    rcases hsupp with h | h | h | h | h | h <;> omega
  apply Fin.ext; rw [triplet_val3 p]; exact hkv
theorem row2 (yNu yE yU yD yR : ℂ) (p : Fin 3) (k : I32)
    (h : smDirac yNu yE yU yD yR (tripletIdx 2 p) k ≠ 0) :
    k = tripletIdx 0 p := by
  have hsupp := smDirac_supp_aux yNu yE yU yD yR (tripletIdx 2 p) k h
  rw [triplet_val2 p] at hsupp
  have hkv : k.val = 18 + 2 * p.val := by
    rcases hsupp with h | h | h | h | h | h <;> omega
  apply Fin.ext; rw [triplet_val0 p]; exact hkv
theorem row3 (yNu yE yU yD yR : ℂ) (p : Fin 3) (k : I32)
    (h : smDirac yNu yE yU yD yR (tripletIdx 3 p) k ≠ 0) :
    k = tripletIdx 1 p := by
  have hsupp := smDirac_supp_aux yNu yE yU yD yR (tripletIdx 3 p) k h
  rw [triplet_val3 p] at hsupp
  have hkv : k.val = 19 + 2 * p.val := by
    rcases hsupp with h | h | h | h | h | h <;> omega
  apply Fin.ext; rw [triplet_val1 p]; exact hkv

theorem smDirac_triplet_row (yNu yE yU yD yR : ℂ) (t : Fin 4) (p : Fin 3) (k : I32)
    (h : smDirac yNu yE yU yD yR (tripletIdx t p) k ≠ 0) :
    k = tripletIdx (dPartnerT t) p := by
  fin_cases t
  · exact row0 yNu yE yU yD yR p k h
  · exact row1 yNu yE yU yD yR p k h
  · exact row2 yNu yE yU yD yR p k h
  · exact row3 yNu yE yU yD yR p k h

-- V: values on triplet rows.
theorem yukawaBlock_map_diag_up (yNu yE yU yD : ℂ) (q1 q2 : Fin 8) (p : Fin 3)
    (h1 : q1.val = 2 + 2 * p.val) (h2 : q2.val = 2 + 2 * p.val) :
    ((yukawaBlock yNu yE yU yD).map (starRingEnd ℂ)) q1 q2 = star yU := by
  have e1 : q1 = (⟨2 + 2 * p.val, by have h := p.isLt; omega⟩ : Fin 8) := Fin.ext h1
  have e2 : q2 = (⟨2 + 2 * p.val, by have h := p.isLt; omega⟩ : Fin 8) := Fin.ext h2
  rw [e1, e2, Matrix.map_apply, yukawaBlock_diag]
  change star _ = star yU
  congr 1
  fin_cases p <;> rfl
theorem yukawaBlock_map_diag_down (yNu yE yU yD : ℂ) (q1 q2 : Fin 8) (p : Fin 3)
    (h1 : q1.val = 3 + 2 * p.val) (h2 : q2.val = 3 + 2 * p.val) :
    ((yukawaBlock yNu yE yU yD).map (starRingEnd ℂ)) q1 q2 = star yD := by
  have e1 : q1 = (⟨3 + 2 * p.val, by have h := p.isLt; omega⟩ : Fin 8) := Fin.ext h1
  have e2 : q2 = (⟨3 + 2 * p.val, by have h := p.isLt; omega⟩ : Fin 8) := Fin.ext h2
  rw [e1, e2, Matrix.map_apply, yukawaBlock_diag]
  change star _ = star yD
  congr 1
  fin_cases p <;> rfl
theorem yukawaBlock_map_conjT_up (yNu yE yU yD : ℂ) (q1 q2 : Fin 8) (p : Fin 3)
    (h1 : q1.val = 2 + 2 * p.val) (h2 : q2.val = 2 + 2 * p.val) :
    (((yukawaBlock yNu yE yU yD).map (starRingEnd ℂ))).conjTranspose q1 q2 = yU := by
  rw [Matrix.conjTranspose_apply,
    yukawaBlock_map_diag_up yNu yE yU yD q2 q1 p h2 h1, star_star]
theorem yukawaBlock_map_conjT_down (yNu yE yU yD : ℂ) (q1 q2 : Fin 8) (p : Fin 3)
    (h1 : q1.val = 3 + 2 * p.val) (h2 : q2.val = 3 + 2 * p.val) :
    (((yukawaBlock yNu yE yU yD).map (starRingEnd ℂ))).conjTranspose q1 q2 = yD := by
  rw [Matrix.conjTranspose_apply,
    yukawaBlock_map_diag_down yNu yE yU yD q2 q1 p h2 h1, star_star]

theorem val0 (yNu yE yU yD yR : ℂ) (p : Fin 3) :
    smDirac yNu yE yU yD yR (tripletIdx 0 p) (tripletIdx 2 p) = star yU := by
  have hi1 : ¬(tripletIdx 0 p).val < 8 := by rw [triplet_val0 p]; omega
  have hi2 : ¬(tripletIdx 0 p).val < 16 := by rw [triplet_val0 p]; omega
  have hi3 : (tripletIdx 0 p).val < 24 := by rw [triplet_val0 p]; have h := p.isLt; omega
  have hj1 : ¬(tripletIdx 2 p).val < 8 := by rw [triplet_val2 p]; omega
  have hj2 : ¬(tripletIdx 2 p).val < 16 := by rw [triplet_val2 p]; omega
  have hj3 : ¬(tripletIdx 2 p).val < 24 := by rw [triplet_val2 p]; omega
  have hentry := smDirac_B_entry_aux yNu yE yU yD yR (tripletIdx 0 p) (tripletIdx 2 p)
    hi1 hi2 hi3 hj1 hj2 hj3
  rw [hentry]
  refine yukawaBlock_map_diag_up yNu yE yU yD _ _ p ?_ ?_
  · show (tripletIdx 0 p).val - 16 = 2 + 2 * p.val
    rw [triplet_val0 p]; omega
  · show (tripletIdx 2 p).val - 24 = 2 + 2 * p.val
    rw [triplet_val2 p]; omega
theorem val1 (yNu yE yU yD yR : ℂ) (p : Fin 3) :
    smDirac yNu yE yU yD yR (tripletIdx 1 p) (tripletIdx 3 p) = star yD := by
  have hi1 : ¬(tripletIdx 1 p).val < 8 := by rw [triplet_val1 p]; omega
  have hi2 : ¬(tripletIdx 1 p).val < 16 := by rw [triplet_val1 p]; omega
  have hi3 : (tripletIdx 1 p).val < 24 := by rw [triplet_val1 p]; have h := p.isLt; omega
  have hj1 : ¬(tripletIdx 3 p).val < 8 := by rw [triplet_val3 p]; omega
  have hj2 : ¬(tripletIdx 3 p).val < 16 := by rw [triplet_val3 p]; omega
  have hj3 : ¬(tripletIdx 3 p).val < 24 := by rw [triplet_val3 p]; omega
  have hentry := smDirac_B_entry_aux yNu yE yU yD yR (tripletIdx 1 p) (tripletIdx 3 p)
    hi1 hi2 hi3 hj1 hj2 hj3
  rw [hentry]
  refine yukawaBlock_map_diag_down yNu yE yU yD _ _ p ?_ ?_
  · show (tripletIdx 1 p).val - 16 = 3 + 2 * p.val
    rw [triplet_val1 p]; omega
  · show (tripletIdx 3 p).val - 24 = 3 + 2 * p.val
    rw [triplet_val3 p]; omega
theorem val2 (yNu yE yU yD yR : ℂ) (p : Fin 3) :
    smDirac yNu yE yU yD yR (tripletIdx 2 p) (tripletIdx 0 p) = yU := by
  have hi1 : ¬(tripletIdx 2 p).val < 8 := by rw [triplet_val2 p]; omega
  have hi2 : ¬(tripletIdx 2 p).val < 16 := by rw [triplet_val2 p]; omega
  have hi3 : ¬(tripletIdx 2 p).val < 24 := by rw [triplet_val2 p]; omega
  have hj1 : ¬(tripletIdx 0 p).val < 8 := by rw [triplet_val0 p]; omega
  have hj2 : ¬(tripletIdx 0 p).val < 16 := by rw [triplet_val0 p]; omega
  have hj3 : (tripletIdx 0 p).val < 24 := by rw [triplet_val0 p]; have h := p.isLt; omega
  have hentry := smDirac_Bdag_entry_aux yNu yE yU yD yR (tripletIdx 2 p) (tripletIdx 0 p)
    hi1 hi2 hi3 hj1 hj2 hj3
  rw [hentry]
  refine yukawaBlock_map_conjT_up yNu yE yU yD _ _ p ?_ ?_
  · show (tripletIdx 2 p).val - 24 = 2 + 2 * p.val
    rw [triplet_val2 p]; omega
  · show (tripletIdx 0 p).val - 16 = 2 + 2 * p.val
    rw [triplet_val0 p]; omega
theorem val3 (yNu yE yU yD yR : ℂ) (p : Fin 3) :
    smDirac yNu yE yU yD yR (tripletIdx 3 p) (tripletIdx 1 p) = yD := by
  have hi1 : ¬(tripletIdx 3 p).val < 8 := by rw [triplet_val3 p]; omega
  have hi2 : ¬(tripletIdx 3 p).val < 16 := by rw [triplet_val3 p]; omega
  have hi3 : ¬(tripletIdx 3 p).val < 24 := by rw [triplet_val3 p]; omega
  have hj1 : ¬(tripletIdx 1 p).val < 8 := by rw [triplet_val1 p]; omega
  have hj2 : ¬(tripletIdx 1 p).val < 16 := by rw [triplet_val1 p]; omega
  have hj3 : (tripletIdx 1 p).val < 24 := by rw [triplet_val1 p]; have h := p.isLt; omega
  have hentry := smDirac_Bdag_entry_aux yNu yE yU yD yR (tripletIdx 3 p) (tripletIdx 1 p)
    hi1 hi2 hi3 hj1 hj2 hj3
  rw [hentry]
  refine yukawaBlock_map_conjT_down yNu yE yU yD _ _ p ?_ ?_
  · show (tripletIdx 3 p).val - 24 = 3 + 2 * p.val
    rw [triplet_val3 p]; omega
  · show (tripletIdx 1 p).val - 16 = 3 + 2 * p.val
    rw [triplet_val1 p]; omega

theorem smDirac_triplet_val (yNu yE yU yD yR : ℂ) (t : Fin 4) (p : Fin 3) :
    smDirac yNu yE yU yD yR (tripletIdx t p) (tripletIdx (dPartnerT t) p)
      = dScalar yU yD t := by
  fin_cases t
  · show smDirac yNu yE yU yD yR (tripletIdx 0 p) (tripletIdx 2 p) = star yU
    exact val0 yNu yE yU yD yR p
  · show smDirac yNu yE yU yD yR (tripletIdx 1 p) (tripletIdx 3 p) = star yD
    exact val1 yNu yE yU yD yR p
  · show smDirac yNu yE yU yD yR (tripletIdx 2 p) (tripletIdx 0 p) = yU
    exact val2 yNu yE yU yD yR p
  · show smDirac yNu yE yU yD yR (tripletIdx 3 p) (tripletIdx 1 p) = yD
    exact val3 yNu yE yU yD yR p

-- Column lemma.
theorem tripletIdx_range (s : Fin 4) (p : Fin 3) :
    (18 ≤ (tripletIdx s p).val ∧ (tripletIdx s p).val < 24) ∨
    (26 ≤ (tripletIdx s p).val ∧ (tripletIdx s p).val < 32) := by
  have hs := s.isLt
  have hp := p.isLt
  have hval : (tripletIdx s p).val =
      (if s.val < 2 then 18 else 26) + 2 * p.val + s.val % 2 := rfl
  rw [hval]
  by_cases h2 : s.val < 2
  · simp [h2]; omega
  · simp [h2]; omega
theorem tripletOf_some_of_range (n : Nat)
    (h : (18 ≤ n ∧ n < 24) ∨ (26 ≤ n ∧ n < 32)) :
    tripletOf n ≠ none := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · interval_cases n <;> decide
  · interval_cases n <;> decide
theorem smDirac_col_triplet (yNu yE yU yD yR : ℂ) (i : I32) (s : Fin 4) (p : Fin 3)
    (hi : tripletOf i.val = none) :
    smDirac yNu yE yU yD yR i (tripletIdx s p) = 0 := by
  by_contra hne
  have hsupp := smDirac_supp_aux yNu yE yU yD yR i (tripletIdx s p) hne
  have hk := tripletIdx_range s p
  rcases hsupp with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · omega
  · omega
  · have hi18 : 18 ≤ i.val ∧ i.val < 24 := by omega
    exact tripletOf_some_of_range i.val (Or.inl hi18) hi
  · have hi26 : 26 ≤ i.val ∧ i.val < 32 := by omega
    exact tripletOf_some_of_range i.val (Or.inr hi26) hi
  · omega
  · omega

-- genM row sum.
theorem genM_row_sum (a : Fin 8) (s : Fin 4) (p' : Fin 3) (j : I32) :
    genM a (tripletIdx s p') j
      = ∑ q : Fin 3, if j = tripletIdx s q then gellMann a p' q else 0 := by
  by_cases hj : ∃ q : Fin 3, j = tripletIdx s q
  · obtain ⟨q0, hq0⟩ := hj
    have hLHS : genM a (tripletIdx s p') j = gellMann a p' q0 := by
      have h1 := tripletIdx_spec s p'
      have h2 : tripletOf j.val = some (s, q0) := by rw [hq0]; exact tripletIdx_spec s q0
      exact genM_apply_eq a (tripletIdx s p') j s p' q0 h1 h2
    have hRHS : (∑ q : Fin 3, (if j = tripletIdx s q then gellMann a p' q else 0))
              = gellMann a p' q0 := by
      rw [← Finset.sum_subset (Finset.subset_univ {q0})]
      · rw [Finset.sum_singleton]
        rw [if_pos hq0]
      · intro q _ hq0mem
        simp at hq0mem
        rw [if_neg]
        intro hcon
        have heq : tripletIdx s q = tripletIdx s q0 := hcon.symm.trans hq0
        exact hq0mem (tripletIdx_inj s q q0 heq)
    rw [hLHS, hRHS]
  · have hLHS : genM a (tripletIdx s p') j = 0 := by
      by_contra hne
      obtain ⟨t, p1, q1, h1, h2⟩ := genM_supp_triplet a (tripletIdx s p') j hne
      have ht : t = s := by
        have hspec := tripletIdx_spec s p'
        have h := h1.symm.trans hspec
        have h2' := Option.some_inj.mp h
        exact congrArg Prod.fst h2'
      have hj_eq : j = tripletIdx s q1 := by
        have h2' : tripletOf j.val = some (s, q1) := by rw [← ht]; exact h2
        exact tripletOf_inv j s q1 h2'
      exact hj ⟨q1, hj_eq⟩
    have hRHS : (∑ q : Fin 3, (if j = tripletIdx s q then gellMann a p' q else 0)) = 0 := by
      apply Finset.sum_eq_zero
      intro q _
      rw [if_neg]
      intro hcon
      exact hj ⟨q, hcon⟩
    rw [hLHS, hRHS]

-- ============ CB1: [D, genM a] = 0 ============
theorem CB1 (yNu yE yU yD yR : ℂ) (a : Fin 8) :
    smDirac yNu yE yU yD yR * genM a = genM a * smDirac yNu yE yU yD yR := by
  ext i j
  simp only [Matrix.mul_apply]
  by_cases hi : tripletOf i.val = none
  · -- i not in triplet: both sums vanish.
    have h1 : ∑ k : I32, smDirac yNu yE yU yD yR i k * genM a k j = 0 := by
      apply Finset.sum_eq_zero
      intro k _
      by_cases hG : genM a k j = 0
      · rw [hG, mul_zero]
      · obtain ⟨t, p1, q1, hkt, _⟩ := genM_supp_triplet a k j hG
        have hkk : k = tripletIdx t p1 := tripletOf_inv k t p1 hkt
        rw [hkk, smDirac_col_triplet yNu yE yU yD yR i t p1 hi, zero_mul]
    have h2 : ∑ k : I32, genM a i k * smDirac yNu yE yU yD yR k j = 0 := by
      apply Finset.sum_eq_zero
      intro k _
      by_cases hG : genM a i k = 0
      · rw [hG, zero_mul]
      · obtain ⟨t, p1, q1, hit, _⟩ := genM_supp_triplet a i k hG
        rw [hit] at hi
        simp at hi
    rw [h1, h2]
  · -- i = tripletIdx t' p'.
    have hex : ∃ tp : Fin 4 × Fin 3, tripletOf i.val = some tp := by
      cases h : tripletOf i.val with
      | none => exact absurd h hi
      | some tp => exact ⟨tp, rfl⟩
    obtain ⟨⟨t', p'⟩, htp⟩ := hex
    have hi_eq : i = tripletIdx t' p' := tripletOf_inv i t' p' htp
    -- (D*G) i j = dScalar t' * G (tripletIdx (dPartnerT t') p') j
    have hDG : ∑ k : I32, smDirac yNu yE yU yD yR i k * genM a k j
             = dScalar yU yD t' * genM a (tripletIdx (dPartnerT t') p') j := by
      have hsuppDG : ∀ k : I32,
          k ∉ ({tripletIdx (dPartnerT t') p'} : Finset I32) →
          smDirac yNu yE yU yD yR i k * genM a k j = 0 := by
        intro k hk
        by_cases hD : smDirac yNu yE yU yD yR i k = 0
        · rw [hD, zero_mul]
        · exfalso
          rw [hi_eq] at hD
          have hSk := smDirac_triplet_row yNu yE yU yD yR t' p' k hD
          apply hk
          exact Finset.mem_singleton.mpr hSk
      rw [sum_I32_support _ hsuppDG, Finset.sum_singleton, hi_eq,
        smDirac_triplet_val yNu yE yU yD yR t' p']
    -- (G*D) i j = dScalar t' * G (tripletIdx (dPartnerT t') p') j
    have hGD : ∑ k : I32, genM a i k * smDirac yNu yE yU yD yR k j
             = dScalar yU yD t' * genM a (tripletIdx (dPartnerT t') p') j := by
      have hsupp : ∀ k : I32, k ∉ Finset.image (tripletIdx t') Finset.univ →
          genM a i k * smDirac yNu yE yU yD yR k j = 0 := by
        intro k hk
        by_cases hG : genM a i k = 0
        · rw [hG, zero_mul]
        · exfalso
          obtain ⟨t1, p1, q1, hit, hkt⟩ := genM_supp_triplet a i k hG
          have heq : (t1, p1) = (t', p') := Option.some_inj.mp (hit.symm.trans htp)
          have hkk : k = tripletIdx t' q1 := by
            have h1 : k = tripletIdx t1 q1 := tripletOf_inv k t1 q1 hkt
            have ht1 : t1 = t' := congrArg Prod.fst heq
            rw [h1, ht1]
          apply hk
          rw [Finset.mem_image]
          exact ⟨q1, Finset.mem_univ q1, hkk.symm⟩
      rw [sum_I32_support _ hsupp,
        Finset.sum_image (fun x _ y _ hxy => tripletIdx_inj t' _ _ hxy)]
      have hGq : ∀ q : Fin 3, genM a i (tripletIdx t' q) = gellMann a p' q := by
        intro q
        exact genM_apply_eq a i (tripletIdx t' q) t' p' q htp (tripletIdx_spec t' q)
      simp_rw [hGq]
      rw [genM_row_sum a (dPartnerT t') p' j, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q _
      have hDq : smDirac yNu yE yU yD yR (tripletIdx t' q) j
               = if j = tripletIdx (dPartnerT t') q then dScalar yU yD t' else 0 := by
        by_cases hj : j = tripletIdx (dPartnerT t') q
        · rw [if_pos hj, hj]
          exact smDirac_triplet_val yNu yE yU yD yR t' q
        · rw [if_neg hj]
          by_cases hne : smDirac yNu yE yU yD yR (tripletIdx t' q) j = 0
          · exact hne
          · exfalso
            exact hj (smDirac_triplet_row yNu yE yU yD yR t' q j hne)
      rw [hDq]
      by_cases hc : j = tripletIdx (dPartnerT t') q
      · rw [if_pos hc, if_pos hc]; ring
      · rw [if_neg hc, if_neg hc]; ring
    rw [hDG, hGD]

-- Jacobi/reordering helper: [[D,G1],G2o] = [[D,G2o],G1] when [G1,G2o] = 0.
theorem jacobi_reorder (D G1 G2o : Matrix I32 I32 ℂ)
    (hcomm : G1 * G2o = G2o * G1) :
    (D * G1 - G1 * D) * G2o - G2o * (D * G1 - G1 * D)
      = (D * G2o - G2o * D) * G1 - G1 * (D * G2o - G2o * D) := by
  have hA1 : (D * G1) * G2o = (D * G2o) * G1 := by
    rw [Matrix.mul_assoc, hcomm, ← Matrix.mul_assoc]
  have hA2 : (G1 * D) * G2o = G1 * (D * G2o) := by
    rw [Matrix.mul_assoc]
  have hA3 : G2o * (D * G1) = (G2o * D) * G1 := by
    rw [Matrix.mul_assoc]
  have hA4 : G2o * (G1 * D) = G1 * (G2o * D) := by
    rw [← Matrix.mul_assoc, ← hcomm, Matrix.mul_assoc]
  simp only [Matrix.sub_mul, Matrix.mul_sub]
  rw [hA1, hA2, hA3, hA4]
  abel

-- Gell-Mann matrices are Hermitian (entrywise).
theorem gellMann_herm (a : Fin 8) : (gellMann a).conjTranspose = gellMann a := by
  fin_cases a <;> ext p q <;> fin_cases p <;> fin_cases q <;>
    simp [Matrix.conjTranspose_apply, gellMann]

-- genM is Hermitian (uses triplet structure + Gell-Mann Hermiticity).
theorem genM_herm (a : Fin 8) : (genM a).conjTranspose = genM a := by
  ext i j
  rw [Matrix.conjTranspose_apply]
  cases hi : tripletOf i.val with
  | none =>
    cases hj : tripletOf j.val with
    | none => simp [genM, hi, hj]
    | some tp2 => simp [genM, hi, hj]
  | some tp1 =>
    obtain ⟨t1, p1⟩ := tp1
    cases hj : tripletOf j.val with
    | none => simp [genM, hi, hj]
    | some tp2 =>
      obtain ⟨t2, p2⟩ := tp2
      simp only [genM, hi, hj]
      by_cases heq : t1 = t2
      · subst heq
        simp only [ite_true]
        have h2 := congrFun (congrFun (gellMann_herm a) p1) p2
        rwa [Matrix.conjTranspose_apply] at h2
      · rw [ite_eq_right heq, ite_eq_right (Ne.symm heq), star_zero]

-- ((genM a).map star).transpose = genM a (Hermitian in map/transpose form).
theorem genM_map_star_transpose (a : Fin 8) :
    ((genM a).map (starRingEnd ℂ)).transpose = genM a := by
  have h1 : ((genM a).map (starRingEnd ℂ)).transpose = (genM a).conjTranspose := rfl
  rw [h1]; exact genM_herm a

-- [D̄, Gᵀ] = 0, via Hermitian + CB1 + map star.
theorem Dbar_Gt_comm (yNu yE yU yD yR : ℂ) (a : Fin 8) :
    (smDirac yNu yE yU yD yR).map (starRingEnd ℂ) * (genM a).transpose
      = (genM a).transpose * (smDirac yNu yE yU yD yR).map (starRingEnd ℂ) := by
  have hCB1t : smDirac yNu yE yU yD yR * ((genM a).map (starRingEnd ℂ)).transpose
      = ((genM a).map (starRingEnd ℂ)).transpose * smDirac yNu yE yU yD yR := by
    rw [genM_map_star_transpose]; exact CB1 yNu yE yU yD yR a
  have h := congrArg (fun M : Matrix I32 I32 ℂ => M.map (starRingEnd ℂ)) hCB1t
  have htr : ∀ (M : Matrix I32 I32 ℂ),
      (M.transpose).map (starRingEnd ℂ) = (M.map (starRingEnd ℂ)).transpose := fun M => rfl
  have hss : ((genM a).map (starRingEnd ℂ)).map (starRingEnd ℂ) = genM a := by
    ext i j; simp [Matrix.map_apply]
  simp only [Matrix.map_mul, htr, hss] at h
  exact h

-- UJ * D = D̄ * UJ (with starRingEnd).
theorem UJ_D_eq' (yNu yE yU yD yR : ℂ) :
    UJ * smDirac yNu yE yU yD yR
      = (smDirac yNu yE yU yD yR).map (starRingEnd ℂ) * UJ := by
  have hJ := smDirac_J_compat yNu yE yU yD yR
  have hJ' : UJ * (smDirac yNu yE yU yD yR).map (starRingEnd ℂ)
      = smDirac yNu yE yU yD yR * UJ := hJ
  have h1 : (smDirac yNu yE yU yD yR).map (starRingEnd ℂ)
      = UJ * smDirac yNu yE yU yD yR * UJ := by
    have h := congrArg (fun X : Matrix I32 I32 ℂ => UJ * X) hJ'
    simp only [← Matrix.mul_assoc, UJ_mul_self, Matrix.one_mul] at h
    exact h
  calc UJ * smDirac yNu yE yU yD yR
      = UJ * smDirac yNu yE yU yD yR * 1 := by rw [Matrix.mul_one]
    _ = UJ * smDirac yNu yE yU yD yR * (UJ * UJ) := by rw [UJ_mul_self]
    _ = (UJ * smDirac yNu yE yU yD yR * UJ) * UJ := by rw [← Matrix.mul_assoc]
    _ = (smDirac yNu yE yU yD yR).map (starRingEnd ℂ) * UJ := by rw [← h1]

-- CB2: [D, UJ * (genM a)ᵀ * UJ] = 0 (colour-blind opposite).
theorem CB2 (yNu yE yU yD yR : ℂ) (a : Fin 8) :
    smDirac yNu yE yU yD yR * (UJ * (genM a).transpose * UJ)
      = (UJ * (genM a).transpose * UJ) * smDirac yNu yE yU yD yR := by
  have hDJ : UJ * smDirac yNu yE yU yD yR
      = (smDirac yNu yE yU yD yR).map (starRingEnd ℂ) * UJ :=
    UJ_D_eq' yNu yE yU yD yR
  have hDM : (smDirac yNu yE yU yD yR).map (starRingEnd ℂ) * (genM a).transpose
      = (genM a).transpose * (smDirac yNu yE yU yD yR).map (starRingEnd ℂ) :=
    Dbar_Gt_comm yNu yE yU yD yR a
  have hDUJ : smDirac yNu yE yU yD yR * UJ
      = UJ * (smDirac yNu yE yU yD yR).map (starRingEnd ℂ) := by
    have h1 : smDirac yNu yE yU yD yR
        = UJ * (smDirac yNu yE yU yD yR).map (starRingEnd ℂ) * UJ := by
      have h := congrArg (fun X : Matrix I32 I32 ℂ => UJ * X) hDJ
      simp only [← Matrix.mul_assoc, UJ_mul_self, Matrix.one_mul] at h
      exact h
    calc smDirac yNu yE yU yD yR * UJ
        = (UJ * (smDirac yNu yE yU yD yR).map (starRingEnd ℂ) * UJ) * UJ := by rw [← h1]
      _ = (UJ * (smDirac yNu yE yU yD yR).map (starRingEnd ℂ)) * (UJ * UJ) := by
          rw [Matrix.mul_assoc]
      _ = (UJ * (smDirac yNu yE yU yD yR).map (starRingEnd ℂ)) * 1 := by rw [UJ_mul_self]
      _ = UJ * (smDirac yNu yE yU yD yR).map (starRingEnd ℂ) := by rw [Matrix.mul_one]
  have lhs : smDirac yNu yE yU yD yR * (UJ * (genM a).transpose * UJ)
      = UJ * ((smDirac yNu yE yU yD yR).map (starRingEnd ℂ) * (genM a).transpose) * UJ := by
    calc smDirac yNu yE yU yD yR * (UJ * (genM a).transpose * UJ)
        = smDirac yNu yE yU yD yR * ((UJ * (genM a).transpose) * UJ) := rfl
      _ = (smDirac yNu yE yU yD yR * (UJ * (genM a).transpose)) * UJ := by
          rw [← Matrix.mul_assoc]
      _ = ((smDirac yNu yE yU yD yR * UJ) * (genM a).transpose) * UJ := by
          rw [← Matrix.mul_assoc]
      _ = ((UJ * (smDirac yNu yE yU yD yR).map (starRingEnd ℂ)) * (genM a).transpose) * UJ := by
          rw [hDUJ]
      _ = (UJ * ((smDirac yNu yE yU yD yR).map (starRingEnd ℂ) * (genM a).transpose)) * UJ := by
          rw [Matrix.mul_assoc UJ]
  have rhs : (UJ * (genM a).transpose * UJ) * smDirac yNu yE yU yD yR
      = UJ * ((genM a).transpose * (smDirac yNu yE yU yD yR).map (starRingEnd ℂ)) * UJ := by
    calc (UJ * (genM a).transpose * UJ) * smDirac yNu yE yU yD yR
        = ((UJ * (genM a).transpose) * UJ) * smDirac yNu yE yU yD yR := rfl
      _ = (UJ * (genM a).transpose) * (UJ * smDirac yNu yE yU yD yR) := by
          rw [Matrix.mul_assoc (UJ * (genM a).transpose) UJ]
      _ = (UJ * (genM a).transpose) *
          ((smDirac yNu yE yU yD yR).map (starRingEnd ℂ) * UJ) := by rw [hDJ]
      _ = ((UJ * (genM a).transpose) *
          (smDirac yNu yE yU yD yR).map (starRingEnd ℂ)) * UJ := by
          rw [← Matrix.mul_assoc]
      _ = (UJ * ((genM a).transpose *
          (smDirac yNu yE yU yD yR).map (starRingEnd ℂ))) * UJ := by
          rw [Matrix.mul_assoc UJ]
  rw [lhs, rhs, hDM]

/-! ## Order-one: the (C,H) × (C°,H°) block

The remaining 16 pairs. The inner commutators [D, genC] and [D, genH k] are
supported on indices < 16, while H° lives on 16–23 (disjointness) and C° is
diagonal and constant on their supports. The five-block ansatz remains
imposed, not derived (Attack 4 NO-GO preserved). -/

/-- A nonzero entry of a matrix difference forces a nonzero entry on one side. -/
theorem sub_entry_ne_zero {A B : Matrix I32 I32 ℂ} {i j : I32}
    (h : (A - B) i j ≠ 0) : A i j ≠ 0 ∨ B i j ≠ 0 := by
  by_contra hcon
  rw [not_or, not_not, not_not] at hcon
  exact h (by simp [Matrix.sub_apply, hcon.1, hcon.2])

/-- Congruence of `if` into `Complex.I` / `0`. -/
theorem if_Complex_I_congr {P Q : Prop} [Decidable P] [Decidable Q] (h : P ↔ Q) :
    (if P then Complex.I else (0 : ℂ)) = (if Q then Complex.I else (0 : ℂ)) := by
  by_cases hP : P
  · rw [ite_eq_left hP, ite_eq_left (h.mp hP)]
  · rw [ite_eq_right hP, ite_eq_right (fun hcon => hP (h.mpr hcon))]

set_option linter.unusedVariables false in
/-- genC diagonal on 16–23: I exactly at 16, 17. -/
theorem genC_diag_16_24 (i : I32) (h1 : 16 ≤ i.val) (h2 : i.val < 24) :
    genC i i = (if i.val = 16 ∨ i.val = 17 then Complex.I else 0) := by
  rw [genC_diag_val]
  have hc1 : ¬ (8 ≤ i.val ∧ i.val < 16) := by omega
  rw [ite_eq_right hc1]
  by_cases hP : i.val = 16 ∨ i.val = 17 ∨ i.val = 24 ∨ i.val = 25
  · have hP' : i.val = 16 ∨ i.val = 17 := by
      rcases hP with h|h|h|h <;> omega
    rw [ite_eq_left hP, ite_eq_left hP']
  · have hP' : ¬ (i.val = 16 ∨ i.val = 17) := by
      rintro (h|h) <;> exact hP (by omega)
    rw [ite_eq_right hP, ite_eq_right hP']

/-- genC diagonal on 24–31: I exactly at 24, 25. -/
theorem genC_diag_24_32 (i : I32) (h1 : 24 ≤ i.val) :
    genC i i = (if i.val = 24 ∨ i.val = 25 then Complex.I else 0) := by
  rw [genC_diag_val]
  have hc1 : ¬ (8 ≤ i.val ∧ i.val < 16) := by omega
  rw [ite_eq_right hc1]
  by_cases hP : i.val = 16 ∨ i.val = 17 ∨ i.val = 24 ∨ i.val = 25
  · have hP' : i.val = 24 ∨ i.val = 25 := by
      rcases hP with h|h|h|h <;> omega
    rw [ite_eq_left hP, ite_eq_left hP']
  · have hP' : ¬ (i.val = 24 ∨ i.val = 25) := by
      rintro (h|h) <;> exact hP (by omega)
    rw [ite_eq_right hP, ite_eq_right hP']

/-- [D, genC] entrywise: genC is diagonal, so only its diagonal values matter. -/
theorem DC_entry (yNu yE yU yD yR : ℂ) (i j : I32) :
    (smDirac yNu yE yU yD yR * genC - genC * smDirac yNu yE yU yD yR) i j
      = smDirac yNu yE yU yD yR i j * genC j j
        - genC i i * smDirac yNu yE yU yD yR i j := by
  have e1 : (smDirac yNu yE yU yD yR * genC) i j
      = smDirac yNu yE yU yD yR i j * genC j j := by
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_single j ?_ ?_
    · intro k _ hk
      have hkj : genC k j = 0 := by
        by_contra hcon
        exact hk (genC_diag k j hcon)
      rw [hkj, mul_zero]
    · intro hcon
      exact absurd (Finset.mem_univ j) hcon
  have e2 : (genC * smDirac yNu yE yU yD yR) i j
      = genC i i * smDirac yNu yE yU yD yR i j := by
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_single i ?_ ?_
    · intro k _ hk
      have hik : genC i k = 0 := by
        by_contra hcon
        exact hk (genC_diag i k hcon).symm
      rw [hik, zero_mul]
    · intro hcon
      exact absurd (Finset.mem_univ i) hcon
  simp only [Matrix.sub_apply]
  rw [e1, e2]

/-- Support of [D, genC]: only the particle Yukawa blocks survive, because genC
    takes equal values (I) on the antiparticle pairs (16,17)↔(24,25) and on the
    Majorana slots (8↔24). -/
theorem DC_cases (yNu yE yU yD yR : ℂ) (i j : I32)
    (h : (smDirac yNu yE yU yD yR * genC - genC * smDirac yNu yE yU yD yR) i j ≠ 0) :
    (i.val < 8 ∧ j.val = i.val + 8) ∨ (8 ≤ i.val ∧ i.val < 16 ∧ j.val = i.val - 8) := by
  have hD : smDirac yNu yE yU yD yR i j ≠ 0 := by
    by_contra hcon
    have h0 : (smDirac yNu yE yU yD yR * genC - genC * smDirac yNu yE yU yD yR) i j = 0 := by
      rw [DC_entry yNu yE yU yD yR i j, hcon, zero_mul, mul_zero, sub_self]
    exact h h0
  have hsupp := smDirac_supp_aux yNu yE yU yD yR i j hD
  rcases hsupp with ⟨hi8, hjm⟩ | ⟨hia, hib, hjm⟩ | ⟨hia, hib, hjm⟩
      | ⟨hia, hib, hjm⟩ | ⟨hiv, hjv⟩ | ⟨hiv, hjv⟩
  · exact Or.inl ⟨hi8, hjm⟩
  · exact Or.inr ⟨hia, hib, hjm⟩
  · -- 16 ≤ i < 24, j = i + 8: genC j j = genC i i, so the commutator vanishes
    exfalso
    have e : genC j j = genC i i := by
      have h1 := genC_diag_24_32 j (by omega)
      have h2 := genC_diag_16_24 i (by omega) (by omega)
      rw [h1, h2]
      apply if_Complex_I_congr
      constructor <;> intro hc <;> rcases hc with h|h <;> omega
    have h0 : (smDirac yNu yE yU yD yR * genC - genC * smDirac yNu yE yU yD yR) i j = 0 := by
      rw [DC_entry yNu yE yU yD yR i j, e]; ring
    exact h h0
  · -- 24 ≤ i < 32, j = i - 8: same
    exfalso
    have e : genC j j = genC i i := by
      have h1 := genC_diag_16_24 j (by omega) (by omega)
      have h2 := genC_diag_24_32 i (by omega)
      rw [h1, h2]
      apply if_Complex_I_congr
      constructor <;> intro hc <;> rcases hc with h|h <;> omega
    have h0 : (smDirac yNu yE yU yD yR * genC - genC * smDirac yNu yE yU yD yR) i j = 0 := by
      rw [DC_entry yNu yE yU yD yR i j, e]; ring
    exact h h0
  · -- Majorana (8, 24): genC takes value I at both slots
    exfalso
    have e : genC j j = genC i i := by
      have h1 : genC j j = Complex.I := by
        rw [genC_diag_val, ite_eq_right (by omega : ¬ (8 ≤ j.val ∧ j.val < 16)),
          ite_eq_left (by omega : j.val = 16 ∨ j.val = 17 ∨ j.val = 24 ∨ j.val = 25)]
      have h2 : genC i i = Complex.I := by
        rw [genC_diag_val, ite_eq_left (by omega : 8 ≤ i.val ∧ i.val < 16)]
      rw [h1, h2]
    have h0 : (smDirac yNu yE yU yD yR * genC - genC * smDirac yNu yE yU yD yR) i j = 0 := by
      rw [DC_entry yNu yE yU yD yR i j, e]; ring
    exact h h0
  · -- Majorana (24, 8): same
    exfalso
    have e : genC j j = genC i i := by
      have h1 : genC j j = Complex.I := by
        rw [genC_diag_val, ite_eq_left (by omega : 8 ≤ j.val ∧ j.val < 16)]
      have h2 : genC i i = Complex.I := by
        rw [genC_diag_val, ite_eq_right (by omega : ¬ (8 ≤ i.val ∧ i.val < 16)),
          ite_eq_left (by omega : i.val = 16 ∨ i.val = 17 ∨ i.val = 24 ∨ i.val = 25)]
      rw [h1, h2]
    have h0 : (smDirac yNu yE yU yD yR * genC - genC * smDirac yNu yE yU yD yR) i j = 0 := by
      rw [DC_entry yNu yE yU yD yR i j, e]; ring
    exact h h0

/-- C° diagonal value on indices < 16: I exactly at 0, 1, 8, 9 (partners 16, 17, 24, 25). -/
theorem Cop_diag_val (i : I32) (h : i.val < 16) :
    (UJ * genC.transpose * UJ) i i
      = if i.val = 0 ∨ i.val = 1 ∨ i.val = 8 ∨ i.val = 9 then Complex.I else 0 := by
  rw [smGenOp_C_diag_val, genC_diag_val]
  have hp : (partner i).val = i.val + 16 := by
    rw [partner_val_eq, ite_eq_left h]
  rw [hp]
  have hc1 : ¬ (8 ≤ i.val + 16 ∧ i.val + 16 < 16) := by omega
  rw [ite_eq_right hc1]
  have hPQ : (i.val + 16 = 16 ∨ i.val + 16 = 17 ∨ i.val + 16 = 24 ∨ i.val + 16 = 25)
      ↔ (i.val = 0 ∨ i.val = 1 ∨ i.val = 8 ∨ i.val = 9) := by
    constructor <;> intro hc <;> rcases hc with h|h|h|h <;> omega
  exact if_Complex_I_congr hPQ

/-- Support extraction for D * genH k: forces the (8–15, 0–7) Yukawa block. -/
theorem DG_supp (yNu yE yU yD yR : ℂ) (k : Fin 3) (i j : I32)
    (h : (smDirac yNu yE yU yD yR * genH k) i j ≠ 0) :
    8 ≤ i.val ∧ i.val < 16 ∧ j.val < 8 ∧
    ∃ m : I32, m.val < 8 ∧ m.val = i.val - 8 ∧ m.val / 2 = j.val / 2 := by
  rw [Matrix.mul_apply] at h
  have hex : ∃ m : I32, smDirac yNu yE yU yD yR i m * genH k m j ≠ 0 := by
    by_contra hcon
    rw [not_exists] at hcon
    exact h (Finset.sum_eq_zero (fun m _ => not_not.mp (hcon m)))
  obtain ⟨m, hm⟩ := hex
  have hDm : smDirac yNu yE yU yD yR i m ≠ 0 := (mul_ne_zero_iff.mp hm).1
  have hGm : genH k m j ≠ 0 := (mul_ne_zero_iff.mp hm).2
  have hGsupp := genH_supp k m j hGm
  have hDsupp := smDirac_supp_aux yNu yE yU yD yR i m hDm
  have hblock := (genH_supp_block k m j hGm).2.2
  rcases hDsupp with ⟨hi8, hjm⟩ | ⟨hia, hib, hjm⟩ | ⟨hia, hib, hjm⟩
      | ⟨hia, hib, hjm⟩ | ⟨hiv, hjv⟩ | ⟨hiv, hjv⟩
  · exfalso; omega
  · exact ⟨hia, hib, hGsupp.2, m, hGsupp.1, hjm, hblock⟩
  · exfalso; omega
  · exfalso; omega
  · exfalso; omega
  · exfalso; omega

/-- Support extraction for genH k * D: forces the (0–7, 8–15) Yukawa block. -/
theorem GD_supp (yNu yE yU yD yR : ℂ) (k : Fin 3) (i j : I32)
    (h : (genH k * smDirac yNu yE yU yD yR) i j ≠ 0) :
    i.val < 8 ∧ 8 ≤ j.val ∧ j.val < 16 ∧
    ∃ m : I32, m.val < 8 ∧ j.val = m.val + 8 ∧ i.val / 2 = m.val / 2 := by
  rw [Matrix.mul_apply] at h
  have hex : ∃ m : I32, genH k i m * smDirac yNu yE yU yD yR m j ≠ 0 := by
    by_contra hcon
    rw [not_exists] at hcon
    exact h (Finset.sum_eq_zero (fun m _ => not_not.mp (hcon m)))
  obtain ⟨m, hm⟩ := hex
  have hGm : genH k i m ≠ 0 := (mul_ne_zero_iff.mp hm).1
  have hDm : smDirac yNu yE yU yD yR m j ≠ 0 := (mul_ne_zero_iff.mp hm).2
  have hGsupp := genH_supp_block k i m hGm
  have hDsupp := smDirac_supp_aux yNu yE yU yD yR m j hDm
  rcases hDsupp with ⟨hm8, hjm⟩ | ⟨hia, hib, hjm⟩ | ⟨hia, hib, hjm⟩
      | ⟨hia, hib, hjm⟩ | ⟨hmv, hjv⟩ | ⟨hmv, hjv⟩
  · exact ⟨hGsupp.1, by omega, by omega, m, hGsupp.2.1, hjm, hGsupp.2.2⟩
  · exfalso; omega
  · exfalso; omega
  · exfalso; omega
  · exfalso; omega
  · exfalso; omega

/-- [D, genH k] lives on indices < 16. -/
theorem DH_supp16 (yNu yE yU yD yR : ℂ) (k : Fin 3) (i j : I32)
    (h : (smDirac yNu yE yU yD yR * genH k - genH k * smDirac yNu yE yU yD yR) i j ≠ 0) :
    i.val < 16 ∧ j.val < 16 := by
  rcases sub_entry_ne_zero h with hDG | hGD
  · have hs := DG_supp yNu yE yU yD yR k i j hDG
    omega
  · have hs := GD_supp yNu yE yU yD yR k i j hGD
    omega

/-- [D, genC] lives on indices < 16. -/
theorem DC_supp16 (yNu yE yU yD yR : ℂ) (i j : I32)
    (h : (smDirac yNu yE yU yD yR * genC - genC * smDirac yNu yE yU yD yR) i j ≠ 0) :
    i.val < 16 ∧ j.val < 16 := by
  have hs := DC_cases yNu yE yU yD yR i j h
  omega

/-- C° is constant across every nonzero entry of [D, genC]. -/
theorem DC_Cop_const (yNu yE yU yD yR : ℂ) (i j : I32)
    (h : (smDirac yNu yE yU yD yR * genC - genC * smDirac yNu yE yU yD yR) i j ≠ 0) :
    (UJ * genC.transpose * UJ) i i = (UJ * genC.transpose * UJ) j j := by
  have h16 : i.val < 16 ∧ j.val < 16 := DC_supp16 yNu yE yU yD yR i j h
  rw [Cop_diag_val i h16.1, Cop_diag_val j h16.2]
  have hs := DC_cases yNu yE yU yD yR i j h
  have hPQ : (i.val = 0 ∨ i.val = 1 ∨ i.val = 8 ∨ i.val = 9) ↔
      (j.val = 0 ∨ j.val = 1 ∨ j.val = 8 ∨ j.val = 9) := by
    constructor <;> intro hc <;> rcases hc with h|h|h|h <;> omega
  by_cases hP : i.val = 0 ∨ i.val = 1 ∨ i.val = 8 ∨ i.val = 9
  · rw [ite_eq_left hP, ite_eq_left (hPQ.mp hP)]
  · rw [ite_eq_right hP, ite_eq_right (fun hcon => hP (hPQ.mpr hcon))]

/-- C° is constant across every nonzero entry of [D, genH k]. -/
theorem DH_Cop_const (yNu yE yU yD yR : ℂ) (k : Fin 3) (i j : I32)
    (h : (smDirac yNu yE yU yD yR * genH k - genH k * smDirac yNu yE yU yD yR) i j ≠ 0) :
    (UJ * genC.transpose * UJ) i i = (UJ * genC.transpose * UJ) j j := by
  have h16 : i.val < 16 ∧ j.val < 16 := DH_supp16 yNu yE yU yD yR k i j h
  rw [Cop_diag_val i h16.1, Cop_diag_val j h16.2]
  have hPQ : (i.val = 0 ∨ i.val = 1 ∨ i.val = 8 ∨ i.val = 9) ↔
      (j.val = 0 ∨ j.val = 1 ∨ j.val = 8 ∨ j.val = 9) := by
    rcases sub_entry_ne_zero h with hDG | hGD
    · have hs := DG_supp yNu yE yU yD yR k i j hDG
      obtain ⟨hia, hib, hj8, m, hm8, hmi, hmj⟩ := hs
      constructor <;> intro hc <;> rcases hc with h|h|h|h <;> omega
    · have hs := GD_supp yNu yE yU yD yR k i j hGD
      obtain ⟨hi8, hja, hjb, m, hm8, hjm, hdiv⟩ := hs
      constructor <;> intro hc <;> rcases hc with h|h|h|h <;> omega
  by_cases hP : i.val = 0 ∨ i.val = 1 ∨ i.val = 8 ∨ i.val = 9
  · rw [ite_eq_left hP, ite_eq_left (hPQ.mp hP)]
  · rw [ite_eq_right hP, ite_eq_right (fun hcon => hP (hPQ.mpr hcon))]

/-- Order-one for the (C, C°) class: [D, genC] commutes with C° by diagonal constancy. -/
theorem orderOne_C_C (yNu yE yU yD yR : ℂ) :
    (smDirac yNu yE yU yD yR * genC - genC * smDirac yNu yE yU yD yR) * (UJ * genC.transpose * UJ)
      - (UJ * genC.transpose * UJ) * (smDirac yNu yE yU yD yR * genC - genC * smDirac yNu yE yU yD yR)
      = 0 := by
  have hconst : ∀ i j : I32,
      (smDirac yNu yE yU yD yR * genC - genC * smDirac yNu yE yU yD yR) i j ≠ 0 →
      (UJ * genC.transpose * UJ) i i = (UJ * genC.transpose * UJ) j j :=
    fun i j hij => DC_Cop_const yNu yE yU yD yR i j hij
  have h := diag_mul_comm_of_const_on_supp (D := UJ * genC.transpose * UJ)
    (B := smDirac yNu yE yU yD yR * genC - genC * smDirac yNu yE yU yD yR)
    smGenOp_C_diag hconst
  calc (smDirac yNu yE yU yD yR * genC - genC * smDirac yNu yE yU yD yR)
          * (UJ * genC.transpose * UJ)
        - (UJ * genC.transpose * UJ)
          * (smDirac yNu yE yU yD yR * genC - genC * smDirac yNu yE yU yD yR)
      = -((UJ * genC.transpose * UJ)
          * (smDirac yNu yE yU yD yR * genC - genC * smDirac yNu yE yU yD yR)
        - (smDirac yNu yE yU yD yR * genC - genC * smDirac yNu yE yU yD yR)
          * (UJ * genC.transpose * UJ)) := by rw [neg_sub]
    _ = 0 := by rw [h, neg_zero]

/-- Order-one for the (H, C°) class. -/
theorem orderOne_H_C (yNu yE yU yD yR : ℂ) (k : Fin 3) :
    (smDirac yNu yE yU yD yR * genH k - genH k * smDirac yNu yE yU yD yR) * (UJ * genC.transpose * UJ)
      - (UJ * genC.transpose * UJ) * (smDirac yNu yE yU yD yR * genH k - genH k * smDirac yNu yE yU yD yR)
      = 0 := by
  have hconst : ∀ i j : I32,
      (smDirac yNu yE yU yD yR * genH k - genH k * smDirac yNu yE yU yD yR) i j ≠ 0 →
      (UJ * genC.transpose * UJ) i i = (UJ * genC.transpose * UJ) j j :=
    fun i j hij => DH_Cop_const yNu yE yU yD yR k i j hij
  have h := diag_mul_comm_of_const_on_supp (D := UJ * genC.transpose * UJ)
    (B := smDirac yNu yE yU yD yR * genH k - genH k * smDirac yNu yE yU yD yR)
    smGenOp_C_diag hconst
  calc (smDirac yNu yE yU yD yR * genH k - genH k * smDirac yNu yE yU yD yR)
          * (UJ * genC.transpose * UJ)
        - (UJ * genC.transpose * UJ)
          * (smDirac yNu yE yU yD yR * genH k - genH k * smDirac yNu yE yU yD yR)
      = -((UJ * genC.transpose * UJ)
          * (smDirac yNu yE yU yD yR * genH k - genH k * smDirac yNu yE yU yD yR)
        - (smDirac yNu yE yU yD yR * genH k - genH k * smDirac yNu yE yU yD yR)
          * (UJ * genC.transpose * UJ)) := by rw [neg_sub]
    _ = 0 := by rw [h, neg_zero]

/-- Order-one for the (C, H°) class: disjoint supports (< 16 vs 16–23). -/
theorem orderOne_C_H (yNu yE yU yD yR : ℂ) (l : Fin 3) :
    (smDirac yNu yE yU yD yR * genC - genC * smDirac yNu yE yU yD yR) * (UJ * (genH l).transpose * UJ)
      - (UJ * (genH l).transpose * UJ) * (smDirac yNu yE yU yD yR * genC - genC * smDirac yNu yE yU yD yR)
      = 0 := by
  have hAB : (smDirac yNu yE yU yD yR * genC - genC * smDirac yNu yE yU yD yR)
      * (UJ * (genH l).transpose * UJ) = 0 := by
    apply disjoint_mul_zero (fun m => m.val < 16)
    · intro i m him
      exact (DC_supp16 yNu yE yU yD yR i m him).2
    · intro m j hmj
      have hsupp := UJ_genH_transpose_UJ_supp l m j hmj
      omega
  have hBA : (UJ * (genH l).transpose * UJ)
      * (smDirac yNu yE yU yD yR * genC - genC * smDirac yNu yE yU yD yR) = 0 := by
    apply disjoint_mul_zero (fun m => 16 ≤ m.val)
    · intro i m him
      exact (UJ_genH_transpose_UJ_supp l i m him).2.2.1
    · intro m j hmj
      have hsupp := DC_supp16 yNu yE yU yD yR m j hmj
      omega
  rw [hAB, hBA, sub_self]

/-- Order-one for the (H, H°) class: disjoint supports. -/
theorem orderOne_H_H (yNu yE yU yD yR : ℂ) (k l : Fin 3) :
    (smDirac yNu yE yU yD yR * genH k - genH k * smDirac yNu yE yU yD yR) * (UJ * (genH l).transpose * UJ)
      - (UJ * (genH l).transpose * UJ) * (smDirac yNu yE yU yD yR * genH k - genH k * smDirac yNu yE yU yD yR)
      = 0 := by
  have hAB : (smDirac yNu yE yU yD yR * genH k - genH k * smDirac yNu yE yU yD yR)
      * (UJ * (genH l).transpose * UJ) = 0 := by
    apply disjoint_mul_zero (fun m => m.val < 16)
    · intro i m him
      exact (DH_supp16 yNu yE yU yD yR k i m him).2
    · intro m j hmj
      have hsupp := UJ_genH_transpose_UJ_supp l m j hmj
      omega
  have hBA : (UJ * (genH l).transpose * UJ)
      * (smDirac yNu yE yU yD yR * genH k - genH k * smDirac yNu yE yU yD yR) = 0 := by
    apply disjoint_mul_zero (fun m => 16 ≤ m.val)
    · intro i m him
      exact (UJ_genH_transpose_UJ_supp l i m him).2.2.1
    · intro m j hmj
      have hsupp := DH_supp16 yNu yE yU yD yR k m j hmj
      omega
  rw [hAB, hBA, sub_self]

/-- Order-one with first generator an M generator: CB1 makes the inner commutator vanish. -/
theorem orderOne_M_row (yNu yE yU yD yR : ℂ) (a : Fin 8) (g2 : Fin 12) :
    (smDirac yNu yE yU yD yR * genM a - genM a * smDirac yNu yE yU yD yR) * smGenOp g2
      - smGenOp g2 * (smDirac yNu yE yU yD yR * genM a - genM a * smDirac yNu yE yU yD yR)
      = 0 := by
  have hCB1 : smDirac yNu yE yU yD yR * genM a - genM a * smDirac yNu yE yU yD yR = 0 :=
    sub_eq_zero.mpr (CB1 yNu yE yU yD yR a)
  rw [hCB1]
  simp

/-- Every selected generator commutes with every opposite M° generator (order-zero). -/
theorem orderZero_genM_op (g1 : Fin 12) (a : Fin 8) :
    smGen g1 * (UJ * (genM a).transpose * UJ)
      = (UJ * (genM a).transpose * UJ) * smGen g1 := by
  fin_cases g1
  · exact sub_eq_zero.mp (order_zero_C_M a)
  · exact sub_eq_zero.mp (order_zero_H_M 0 a)
  · exact sub_eq_zero.mp (order_zero_H_M 1 a)
  · exact sub_eq_zero.mp (order_zero_H_M 2 a)
  · exact sub_eq_zero.mp (order_zero_M_M 0 a)
  · exact sub_eq_zero.mp (order_zero_M_M 1 a)
  · exact sub_eq_zero.mp (order_zero_M_M 2 a)
  · exact sub_eq_zero.mp (order_zero_M_M 3 a)
  · exact sub_eq_zero.mp (order_zero_M_M 4 a)
  · exact sub_eq_zero.mp (order_zero_M_M 5 a)
  · exact sub_eq_zero.mp (order_zero_M_M 6 a)
  · exact sub_eq_zero.mp (order_zero_M_M 7 a)

/-- Order-one with opposite generator an M° generator: Jacobi reorder + CB2. -/
theorem orderOne_M_col (yNu yE yU yD yR : ℂ) (g1 : Fin 12) (a : Fin 8) :
    (smDirac yNu yE yU yD yR * smGen g1 - smGen g1 * smDirac yNu yE yU yD yR)
        * (UJ * (genM a).transpose * UJ)
      - (UJ * (genM a).transpose * UJ)
        * (smDirac yNu yE yU yD yR * smGen g1 - smGen g1 * smDirac yNu yE yU yD yR)
      = 0 := by
  have hOZ : smGen g1 * (UJ * (genM a).transpose * UJ)
      = (UJ * (genM a).transpose * UJ) * smGen g1 :=
    orderZero_genM_op g1 a
  have hJ := jacobi_reorder (smDirac yNu yE yU yD yR) (smGen g1) (UJ * (genM a).transpose * UJ) hOZ
  rw [hJ]
  have hCB2 : smDirac yNu yE yU yD yR * (UJ * (genM a).transpose * UJ)
      - (UJ * (genM a).transpose * UJ) * smDirac yNu yE yU yD yR = 0 :=
    sub_eq_zero.mpr (CB2 yNu yE yU yD yR a)
  rw [hCB2]
  simp

/-- **Order-one for the imposed one-generation SM ansatz over the selected
    12-generator family**: all 144 double commutators
    `[[D, smGen g1], smGenOp g2]` vanish. The five-block form of `smDirac`
    remains an imposed ansatz (Attack 4 NO-GO: the numerical order-one
    nullspace has dimension 46, not 10). -/
theorem smDirac_order_one (yNu yE yU yD yR : ℂ) :
    smDiracOrderOne yNu yE yU yD yR := by
  intro g1 g2
  fin_cases g1
  · -- g1 = 0 : genC
    fin_cases g2
    · exact orderOne_C_C yNu yE yU yD yR
    · exact orderOne_C_H yNu yE yU yD yR 0
    · exact orderOne_C_H yNu yE yU yD yR 1
    · exact orderOne_C_H yNu yE yU yD yR 2
    · exact orderOne_M_col yNu yE yU yD yR 0 0
    · exact orderOne_M_col yNu yE yU yD yR 0 1
    · exact orderOne_M_col yNu yE yU yD yR 0 2
    · exact orderOne_M_col yNu yE yU yD yR 0 3
    · exact orderOne_M_col yNu yE yU yD yR 0 4
    · exact orderOne_M_col yNu yE yU yD yR 0 5
    · exact orderOne_M_col yNu yE yU yD yR 0 6
    · exact orderOne_M_col yNu yE yU yD yR 0 7
  · -- g1 = 1 : genH 0
    fin_cases g2
    · exact orderOne_H_C yNu yE yU yD yR 0
    · exact orderOne_H_H yNu yE yU yD yR 0 0
    · exact orderOne_H_H yNu yE yU yD yR 0 1
    · exact orderOne_H_H yNu yE yU yD yR 0 2
    · exact orderOne_M_col yNu yE yU yD yR 1 0
    · exact orderOne_M_col yNu yE yU yD yR 1 1
    · exact orderOne_M_col yNu yE yU yD yR 1 2
    · exact orderOne_M_col yNu yE yU yD yR 1 3
    · exact orderOne_M_col yNu yE yU yD yR 1 4
    · exact orderOne_M_col yNu yE yU yD yR 1 5
    · exact orderOne_M_col yNu yE yU yD yR 1 6
    · exact orderOne_M_col yNu yE yU yD yR 1 7
  · -- g1 = 2 : genH 1
    fin_cases g2
    · exact orderOne_H_C yNu yE yU yD yR 1
    · exact orderOne_H_H yNu yE yU yD yR 1 0
    · exact orderOne_H_H yNu yE yU yD yR 1 1
    · exact orderOne_H_H yNu yE yU yD yR 1 2
    · exact orderOne_M_col yNu yE yU yD yR 2 0
    · exact orderOne_M_col yNu yE yU yD yR 2 1
    · exact orderOne_M_col yNu yE yU yD yR 2 2
    · exact orderOne_M_col yNu yE yU yD yR 2 3
    · exact orderOne_M_col yNu yE yU yD yR 2 4
    · exact orderOne_M_col yNu yE yU yD yR 2 5
    · exact orderOne_M_col yNu yE yU yD yR 2 6
    · exact orderOne_M_col yNu yE yU yD yR 2 7
  · -- g1 = 3 : genH 2
    fin_cases g2
    · exact orderOne_H_C yNu yE yU yD yR 2
    · exact orderOne_H_H yNu yE yU yD yR 2 0
    · exact orderOne_H_H yNu yE yU yD yR 2 1
    · exact orderOne_H_H yNu yE yU yD yR 2 2
    · exact orderOne_M_col yNu yE yU yD yR 3 0
    · exact orderOne_M_col yNu yE yU yD yR 3 1
    · exact orderOne_M_col yNu yE yU yD yR 3 2
    · exact orderOne_M_col yNu yE yU yD yR 3 3
    · exact orderOne_M_col yNu yE yU yD yR 3 4
    · exact orderOne_M_col yNu yE yU yD yR 3 5
    · exact orderOne_M_col yNu yE yU yD yR 3 6
    · exact orderOne_M_col yNu yE yU yD yR 3 7
  · -- g1 = 4..11 : genM a
    exact orderOne_M_row yNu yE yU yD yR 0 g2
  · exact orderOne_M_row yNu yE yU yD yR 1 g2
  · exact orderOne_M_row yNu yE yU yD yR 2 g2
  · exact orderOne_M_row yNu yE yU yD yR 3 g2
  · exact orderOne_M_row yNu yE yU yD yR 4 g2
  · exact orderOne_M_row yNu yE yU yD yR 5 g2
  · exact orderOne_M_row yNu yE yU yD yR 6 g2
  · exact orderOne_M_row yNu yE yU yD yR 7 g2

end ThetLogos
