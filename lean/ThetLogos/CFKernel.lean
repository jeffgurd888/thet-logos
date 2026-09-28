import ThetLogos.MartinettiRep
import ThetLogos.OrderOne
import ThetLogos.Scaffold32

/-!
# ThetLogos.CFKernel — the C_F commutation kernel

CCM hep-th/0610241, Definition 2.20: a Dirac operator is a selfadjoint D on
H_F commuting with J_F and C_F = {(λ,λ,0)}, anticommuting with γ_F, and
satisfying order-one. Remark 2.19: C_F "ensure[s] that the photon will remain
massless." Their Theorem 2.21 ("all Dirac operators are D(Y)") is proved under
this definition.

Representation (grounded in the census, `attack4_corrected.py`):
π(λ,λ,0) = λ·(P_C + P_H), with
  C_SUPPORT = {8,…,15,16,17,24,25}, H_SUPPORT = {0,…,7}.
Hence the λ = 1 representative is the diagonal projector
  cfMat = diag(1 on {0,…,17,24,25}, 0 elsewhere),
spectrally diag(0×12, 1×20).

NOTE on the requested form diag(0, I_3⊗I_2, …): that does not match the working
basis of the repo's representation; we formalize the grounded matrix (P_C+P_H),
which is what the census actually measured ([D,C_F] = 0: all 10 SM directions
exact, all 36 extras fail with min norm 0.48 — T4 numerical, order-one census).

PROVED here (T3):
- `smDirac_comm_cfMat`: [smDirac(yν,yE,yU,yD,yR), cfMat] = 0 for arbitrary
  complex Yukawas — the 5 SM Yukawa/Majorana matrices lie in the C_F kernel.
- `cfMat_comm_forces_block`: [D, cfMat] = 0 forces D to respect the C_F
  support split (no S ↔ complement entries) — the proved mechanism of Q3.1.
- `cf_support_card`: the C_F support has 20 dimensions (complement 12).

TARGET (OPEN, labeled T3 sorrys — Q3.1/Q3.2, the two CCM C_F proof stages):
- `cf_kernel_classification`: order-one + [D,C_F] = 0 (+ J, γ, self-adjoint)
  ⟹ D = smDirac(…) — i.e. the kernel is EXACTLY the 5 matrices.

The "46 → 10 real = 5 complex" count is T4 numerical (order-one-census-paper);
the 46-dimensional nullspace is not a Lean object, so the Lean statement is
the qualitative classification.
-/

namespace ThetLogos

/-! ## §1. The C_F representative -/

/-- Indicator of the C_F support S = C_SUPPORT ∪ H_SUPPORT = {0,…,17,24,25}. -/
def cfIndicator : I32 → ℂ := fun i =>
  if i.val < 18 ∨ i.val = 24 ∨ i.val = 25 then 1 else 0

/-- The 32×32 representative of C_F = {(λ,λ,0)} at λ = 1: π(1,1,0) = P_C + P_H,
    the diagonal projector onto the C/H support. [D, π(λ,λ,0)] = 0 for all
    λ ∈ ℂ iff [D, cfMat] = 0. Tier T2. -/
def cfMat : Matrix I32 I32 ℂ := Matrix.diagonal cfIndicator

theorem cfMat_apply (i j : I32) :
    cfMat i j = if i = j then cfIndicator i else 0 := by
  unfold cfMat; rw [Matrix.diagonal_apply]

theorem cfMat_apply_ne {i j : I32} (h : i ≠ j) : cfMat i j = 0 := by
  rw [cfMat_apply, if_neg h]

theorem mul_cfMat_apply (M : Matrix I32 I32 ℂ) (i j : I32) :
    (M * cfMat) i j = M i j * cfIndicator j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single_of_mem j (Finset.mem_univ j)]
  · rw [cfMat_apply, if_pos rfl]
  · intro k _ hkj
    rw [cfMat_apply_ne hkj, mul_zero]

theorem cfMat_mul_apply (M : Matrix I32 I32 ℂ) (i j : I32) :
    (cfMat * M) i j = cfIndicator i * M i j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single_of_mem i (Finset.mem_univ i)]
  · rw [cfMat_apply, if_pos rfl]
  · intro k _ hki
    rw [cfMat_apply_ne (Ne.symm hki), zero_mul]

/-! ## §2. Block support lemmas -/

/-- The star-mapped Yukawa block is diagonal (uses `majoranaBlock_supp`-style
    diagonality via the existing `yukawaBlock_supp`). -/
theorem starYukawa_supp (yNu yE yU yD : ℂ) (p q : Fin 8)
    (h : ((yukawaBlock yNu yE yU yD).map (starRingEnd ℂ)) p q ≠ 0) :
    p = q := by
  rw [Matrix.map_apply] at h
  have hA : yukawaBlock yNu yE yU yD p q ≠ 0 := by
    intro h0
    rw [h0] at h
    simp at h
  exact yukawaBlock_supp p q hA

/-! ## §3. Nonzero SM-Dirac entries respect the C_F support -/

/-- Nonzero SM-Dirac entries never connect the C_F support S = {0,…,17,24,25}
    to its complement. Proof: 16-case block analysis (mirroring
    `buildDirac_nonzero_opp_grading`); the only blocks straddling the S/Sᶜ
    boundary are the diagonal B = Ā and B† = Aᵀ blocks, where diagonality plus
    index arithmetic (a < 2 ↔ both in S) closes the goal. Tier T3. -/
theorem smDirac_cf_supp (yNu yE yU yD yR : ℂ) (i j : I32)
    (h : smDirac yNu yE yU yD yR i j ≠ 0) :
    cfIndicator i = cfIndicator j := by
  have hD : buildDirac (yukawaBlock yNu yE yU yD)
      ((yukawaBlock yNu yE yU yD).map (starRingEnd ℂ))
      0 (majoranaBlock yR) i j ≠ 0 := h
  by_cases H1 : i.val < 8
  · -- R1: rows 0–7, all in S.
    have cfi : cfIndicator i = 1 := by
      have hi18 : i.val < 18 := by omega
      unfold cfIndicator; rw [if_pos (Or.inl hi18)]
    by_cases H2 : j.val < 8
    · have h0 : buildDirac (yukawaBlock yNu yE yU yD)
          ((yukawaBlock yNu yE yU yD).map (starRingEnd ℂ))
          0 (majoranaBlock yR) i j = 0 := by
        unfold buildDirac; simp [H1, H2]
      exact absurd h0 hD
    · by_cases H3 : j.val < 16
      · -- A-block: cols 8–15, all in S.
        have cfj : cfIndicator j = 1 := by
          have hj18 : j.val < 18 := by omega
          unfold cfIndicator; rw [if_pos (Or.inl hj18)]
        rw [cfi, cfj]
      · by_cases H4 : j.val < 24
        · -- C-block = 0.
          have h0 : buildDirac (yukawaBlock yNu yE yU yD)
              ((yukawaBlock yNu yE yU yD).map (starRingEnd ℂ))
              0 (majoranaBlock yR) i j = 0 := by
            unfold buildDirac; simp [H1, H2, H3, H4]
          exact absurd h0 hD
        · have h0 : buildDirac (yukawaBlock yNu yE yU yD)
              ((yukawaBlock yNu yE yU yD).map (starRingEnd ℂ))
              0 (majoranaBlock yR) i j = 0 := by
            unfold buildDirac; simp [H1, H2, H3, H4]
          exact absurd h0 hD
  · by_cases H5 : i.val < 16
    · -- R2: rows 8–15, all in S.
      have cfi : cfIndicator i = 1 := by
        have hi18 : i.val < 18 := by omega
        unfold cfIndicator; rw [if_pos (Or.inl hi18)]
      by_cases H2 : j.val < 8
      · -- A†-block: cols 0–7, all in S.
        have cfj : cfIndicator j = 1 := by
          have hj18 : j.val < 18 := by omega
          unfold cfIndicator; rw [if_pos (Or.inl hj18)]
        rw [cfi, cfj]
      · by_cases H3 : j.val < 16
        · have h0 : buildDirac (yukawaBlock yNu yE yU yD)
              ((yukawaBlock yNu yE yU yD).map (starRingEnd ℂ))
              0 (majoranaBlock yR) i j = 0 := by
            unfold buildDirac; simp [H1, H5, H2, H3]
          exact absurd h0 hD
        · by_cases H4 : j.val < 24
          · have h0 : buildDirac (yukawaBlock yNu yE yU yD)
                ((yukawaBlock yNu yE yU yD).map (starRingEnd ℂ))
                0 (majoranaBlock yR) i j = 0 := by
              unfold buildDirac; simp [H1, H5, H2, H3, H4]
            exact absurd h0 hD
          · -- E†-block: diagonal, only (8,24) nonzero; both in S.
            have he := buildDirac_Edag_entry (yukawaBlock yNu yE yU yD)
              ((yukawaBlock yNu yE yU yD).map (starRingEnd ℂ))
              0 (majoranaBlock yR) i j H1 H5 H2 H3 H4
            rw [he, Matrix.conjTranspose_apply] at hD
            have hE : majoranaBlock yR ⟨j.val - 24, by omega⟩
                ⟨i.val - 8, by omega⟩ ≠ 0 := by
              intro h0; apply hD; rw [h0]; simp
            obtain ⟨hj0, hi0⟩ := majoranaBlock_supp _ _ hE
            have hjv : j.val - 24 = 0 := congrArg Fin.val hj0
            have hjv24 : j.val = 24 := by omega
            have cfj : cfIndicator j = 1 := by
              unfold cfIndicator; rw [if_pos (Or.inr (Or.inl hjv24))]
            rw [cfi, cfj]
    · by_cases H6 : i.val < 24
      · -- R3: rows 16–23, straddle S/Sᶜ at 18.
        by_cases H2 : j.val < 8
        · -- C† = 0.
          have h0 : buildDirac (yukawaBlock yNu yE yU yD)
              ((yukawaBlock yNu yE yU yD).map (starRingEnd ℂ))
              0 (majoranaBlock yR) i j = 0 := by
            unfold buildDirac; simp [H1, H5, H6, H2]
          exact absurd h0 hD
        · by_cases H3 : j.val < 16
          · have h0 : buildDirac (yukawaBlock yNu yE yU yD)
                ((yukawaBlock yNu yE yU yD).map (starRingEnd ℂ))
                0 (majoranaBlock yR) i j = 0 := by
              unfold buildDirac; simp [H1, H5, H6, H2, H3]
            exact absurd h0 hD
          · by_cases H4 : j.val < 24
            · have h0 : buildDirac (yukawaBlock yNu yE yU yD)
                  ((yukawaBlock yNu yE yU yD).map (starRingEnd ℂ))
                  0 (majoranaBlock yR) i j = 0 := by
                unfold buildDirac; simp [H1, H5, H6, H2, H3, H4]
              exact absurd h0 hD
            · -- B = Ā block: diagonal, (16+a, 24+a); a<2 ↔ both in S.
              have he := buildDirac_B_entry (yukawaBlock yNu yE yU yD)
                ((yukawaBlock yNu yE yU yD).map (starRingEnd ℂ))
                0 (majoranaBlock yR) i j H1 H5 H6 H2 H3 H4
              rw [he] at hD
              have hBeq := starYukawa_supp yNu yE yU yD _ _ hD
              have hnat : i.val - 16 = j.val - 24 := congrArg Fin.val hBeq
              unfold cfIndicator
              by_cases hiv : i.val < 18
              · have hjv : j.val = 24 ∨ j.val = 25 := by omega
                rw [if_pos (Or.inl hiv), if_pos (Or.inr hjv)]
              · have hni : ¬(i.val < 18 ∨ i.val = 24 ∨ i.val = 25) := by omega
                have hnj : ¬(j.val < 18 ∨ j.val = 24 ∨ j.val = 25) := by omega
                rw [if_neg hni, if_neg hnj]
      · -- R4: rows 24–31, straddle S/Sᶜ at 26.
        by_cases H2 : j.val < 8
        · have h0 : buildDirac (yukawaBlock yNu yE yU yD)
              ((yukawaBlock yNu yE yU yD).map (starRingEnd ℂ))
              0 (majoranaBlock yR) i j = 0 := by
            unfold buildDirac; simp [H1, H5, H6, H2]
          exact absurd h0 hD
        · by_cases H3 : j.val < 16
          · -- E-block: diagonal, only (24,8) nonzero; both in S.
            have he : buildDirac (yukawaBlock yNu yE yU yD)
                ((yukawaBlock yNu yE yU yD).map (starRingEnd ℂ))
                0 (majoranaBlock yR) i j
                = majoranaBlock yR ⟨i.val - 24, by omega⟩
                  ⟨j.val - 8, by omega⟩ := by
              unfold buildDirac; simp [H1, H5, H6, H2, H3]
            rw [he] at hD
            obtain ⟨hi0, hj0⟩ := majoranaBlock_supp _ _ hD
            have h0nat : i.val - 24 = 0 := congrArg Fin.val hi0
            have hiv : i.val = 24 := by omega
            have h8nat : j.val - 8 = 0 := congrArg Fin.val hj0
            have hjv : j.val = 8 := by omega
            have cfi : cfIndicator i = 1 := by
              unfold cfIndicator; rw [if_pos (Or.inr (Or.inl hiv))]
            have cfj : cfIndicator j = 1 := by
              have hj18 : j.val < 18 := by omega
              unfold cfIndicator; rw [if_pos (Or.inl hj18)]
            rw [cfi, cfj]
          · by_cases H4 : j.val < 24
            · -- B† = Aᵀ block: diagonal, (24+a, 16+a); a<2 ↔ both in S.
              have he := buildDirac_Bdag_entry (yukawaBlock yNu yE yU yD)
                ((yukawaBlock yNu yE yU yD).map (starRingEnd ℂ))
                0 (majoranaBlock yR) i j H1 H5 H6 H2 H3 H4
              rw [he, Matrix.conjTranspose_apply] at hD
              have hB : ((yukawaBlock yNu yE yU yD).map (starRingEnd ℂ))
                  ⟨j.val - 16, by omega⟩ ⟨i.val - 24, by omega⟩ ≠ 0 := by
                intro h0; apply hD; rw [h0]; simp
              have hBeq := starYukawa_supp yNu yE yU yD _ _ hB
              have hnat : j.val - 16 = i.val - 24 := congrArg Fin.val hBeq
              unfold cfIndicator
              by_cases hiv : i.val = 24 ∨ i.val = 25
              · have hjv : j.val = 16 ∨ j.val = 17 := by omega
                have hj18 : j.val < 18 := by omega
                rw [if_pos (Or.inr hiv), if_pos (Or.inl hj18)]
              · have hni : ¬(i.val < 18 ∨ i.val = 24 ∨ i.val = 25) := by omega
                have hnj : ¬(j.val < 18 ∨ j.val = 24 ∨ j.val = 25) := by omega
                rw [if_neg hni, if_neg hnj]
            · have h0 : buildDirac (yukawaBlock yNu yE yU yD)
                  ((yukawaBlock yNu yE yU yD).map (starRingEnd ℂ))
                  0 (majoranaBlock yR) i j = 0 := by
                unfold buildDirac; simp [H1, H5, H6, H2, H3, H4]
              exact absurd h0 hD

/-! ## §4. The SM Dirac commutes with C_F -/

/-- The 5 SM Yukawa/Majorana matrices commute with C_F: [D_F, C_F] = 0 for
    arbitrary complex yν, yE, yU, yD, yR. Entrywise: (DP − PD)_ij =
    D_ij·(cf_j − cf_i) = 0 by §3. Tier T3. -/
theorem smDirac_comm_cfMat (yNu yE yU yD yR : ℂ) :
    smDirac yNu yE yU yD yR * cfMat - cfMat * smDirac yNu yE yU yD yR = 0 := by
  ext i j
  rw [Matrix.sub_apply, Matrix.zero_apply, mul_cfMat_apply, cfMat_mul_apply]
  by_cases hD : smDirac yNu yE yU yD yR i j = 0
  · rw [hD]; simp
  · have hcf := smDirac_cf_supp yNu yE yU yD yR i j hD
    rw [hcf]; ring

/-! ## §4. The C_F mechanism (PROVED)

For a diagonal 0/1 projector P, [D, P] = 0 forces D to respect the
support split: D_ij = 0 whenever P_ii ≠ P_jj. This is the proved
formal core of CCM's Q3.1 stage — the mechanism by which C_F cuts the
order-one nullspace. (It does not by itself classify the kernel; the
order-one + J + γ analysis of Q3.1/Q3.2 is §5.)
-/

/-- The indicator takes only the values 0 and 1. -/
theorem cfIndicator_mem (i : I32) : cfIndicator i = 0 ∨ cfIndicator i = 1 := by
  unfold cfIndicator
  by_cases h : (i.val < 18 ∨ i.val = 24 ∨ i.val = 25)
  · rw [if_pos h]; exact Or.inr rfl
  · rw [if_neg h]; exact Or.inl rfl

/-- Commutation with C_F forces block structure: if [D, cfMat] = 0 then D
    cannot connect the C_F support S = {0,…,17,24,25} to its complement.
    Proof: (DP − PD)_ij = D_ij·(cf_j − cf_i); with cf values in {0,1} and
    cf_i ≠ cf_j, the factor (cf_j − cf_i) = ±1 is a unit, so D_ij = 0. -/
theorem cfMat_comm_forces_block (D : Matrix I32 I32 ℂ)
    (h : D * cfMat - cfMat * D = 0) (i j : I32)
    (hij : cfIndicator i ≠ cfIndicator j) : D i j = 0 := by
  have hcomm : D * cfMat = cfMat * D := by
    have := h; rw [sub_eq_zero] at this; exact this
  have hij' : (D * cfMat) i j = (cfMat * D) i j :=
    congrArg (fun M : Matrix I32 I32 ℂ => M i j) hcomm
  rw [mul_cfMat_apply, cfMat_mul_apply] at hij'
  -- hij' : D i j * cfIndicator j = cfIndicator i * D i j
  have hdiff : cfIndicator j - cfIndicator i ≠ 0 := by
    rcases cfIndicator_mem i with hi | hi <;> rcases cfIndicator_mem j with hj | hj
    · rw [hi, hj] at hij; exact absurd rfl hij
    · rw [hi, hj]; norm_num
    · rw [hi, hj]; norm_num
    · rw [hi, hj] at hij; exact absurd rfl hij
  have hprod : D i j * (cfIndicator j - cfIndicator i) = 0 := by
    rw [mul_sub, hij']; ring
  rcases mul_eq_zero.mp hprod with hD | hcon
  · exact hD
  · exact absurd hcon hdiff

/-- The C_F support has 20 dimensions (complement: 12). -/
theorem cf_support_card :
    (Finset.univ.filter (fun i : I32 => decide (i.val < 18 ∨ i.val = 24 ∨ i.val = 25))).card = 20 := by
  decide

/-! ## §5. Classification target (OPEN) -/

/-- Classification target: order-one + [D, C_F] = 0 (+ J-compatibility,
    grading-oddness, self-adjointness) forces D to be SM-type — exactly the
    5 Yukawa/Majorana matrices. This is the two CCM C_F proof stages:
    Q3.1 (C_F cuts the S-sector to the 8 SM Yukawas) and Q3.2 (C_F forces the
    Majorana T-block to SM form). Status: OPEN — the analytic classification
    is not yet formalized.

    NOTE (2026-09-28): `OrderOneHolds` is now the REPAIRED predicate via the
    Martinetti `smGen`/`smGenOp` (OrderOne.lean). It is NON-VACUOUS:
    `OrderOneHolds_smDirac` proves it holds for the SM ansatz. (The old
    Option-A version was unsatisfiable; see `not_OrderOneHolds_optionA_smDirac`
    in OrderOneFull.lean.) -/
theorem cf_kernel_classification (D : Matrix I32 I32 ℂ)
    (h_oo : OrderOneHolds D)
    (h_cf : D * cfMat - cfMat * D = 0)
    (h_sa : D.conjTranspose = D)
    (h_J : UJ * D.map (star : ℂ → ℂ) = D * UJ)
    (h_g : gammaF * D + D * gammaF = 0) :
    ∃ yNu yE yU yD yR : ℂ, D = smDirac yNu yE yU yD yR := by
  -- T3-sorry (Q3.1): CCM proof stage 1 — [D, C_F] = 0 cuts the order-one
  -- S-sector to the 8 SM Yukawa directions.
  -- T3-sorry (Q3.2): CCM proof stage 2 — [D, C_F] = 0 forces the Majorana
  -- T-block to the single SM direction yR.
  sorry

end ThetLogos
