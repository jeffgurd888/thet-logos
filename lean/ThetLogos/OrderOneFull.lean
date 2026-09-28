import ThetLogos.MartinettiRep
import ThetLogos.OrderOne

/-!
# ThetLogos.OrderOneFull — order-one over the full 24-generator family

`smDirac_order_one` (MartinettiRep.lean) proves order-one over the selected
12-generator family `smGen`. But `OrderOneHolds` (OrderOne.lean) — the
hypothesis used by `cf_kernel_classification` — is over the full `Fin 24`
real basis `AFGenerators` of `ℂ ⊕ ℍ ⊕ M₃(ℂ)`, via the Option-A `pi`.

## Results in this module

1. **Collapse (T3, proved):** In the Option-A representation, pure-color algebra
   elements act trivially (`pi_pure_color_zero`), so 540 of the 576 order-one
   pairs vanish trivially.

2. **REFUTATION (T3, proved):** `¬ OrderOneHolds_optionA (smDirac 0 0 0 0 1)`.
   The OLD `OrderOneHolds_optionA` predicate — as defined via the Option-A `pi`
   — is NOT satisfied by the SM Dirac ansatz. The `(⟨1,0,0⟩, ⟨1,0,0⟩)` pair has
   a nonzero `(8,24)` entry equal to `-conj(yR)` (the Majorana block leaking
   through). Moreover the `(⟨1,0,0⟩, quat)` pairs fail independently of `yR`
   (numerical: entry `(16,8) = -conj(yNu)`), so the old predicate is
   unsatisfiable for generic Yukawas.

   This refutation motivated the 2026-09-28 repair: `OrderOneHolds` is now
   defined via the repaired Martinetti `smGen`/`smGenOp`, and IS satisfied
   by the SM Dirac (`OrderOneHolds_smDirac`, proved). The
   `cf_kernel_classification` hypothesis is no longer vacuous.

3. **Diagnosis:** `OrderOne.lean` previously used the Option-A `pi`, which
   MartinettiRep.lean itself calls "defective" (disjoint support). The
   repaired Martinetti representation (`smGen`/`smGenOp`) DOES satisfy
   order-one (`smDirac_order_one`, 144 pairs, proved). As of 2026-09-28,
   `OrderOneHolds` is redefined via the repaired representation, and
   `OrderOneHolds_smDirac` closes it for the SM ansatz.
-/

namespace ThetLogos

/-! ## Trivial pairs -/

/-- If `pi a = 0` the order-one double commutator vanishes. -/
theorem orderOneComm_of_pi_left_zero (D : Matrix I32 I32 ℂ) (a b : AF)
    (ha : pi a = 0) : orderOneComm D a b = 0 := by
  simp only [orderOneComm]
  rw [ha]
  simp

/-- If `pi b = 0` the order-one double commutator vanishes. -/
theorem orderOneComm_of_pi_right_zero (D : Matrix I32 I32 ℂ) (a b : AF)
    (hb : pi b = 0) : orderOneComm D a b = 0 := by
  simp only [orderOneComm, piOp]
  rw [hb]
  simp

/-! ## The color generators -/

/-- Every `AFGenerators m` with `m ≥ 6` is a pure-color element. -/
theorem AFGenerators_color (m : Fin 24) (h6 : 6 ≤ m.val) :
    ∃ mc : Matrix I3 I3 ℂ, AFGenerators m = ⟨0, 0, mc⟩ := by
  unfold AFGenerators
  dsimp only
  split_ifs <;> first | omega | exact ⟨_, rfl⟩

/-- 540 of the 576 order-one pairs vanish because a color generator is involved.
    (The remaining 36 are over the 6 non-color generators — but see the
    refutation below: the full `OrderOneHolds` is in fact FALSE.) -/
theorem orderOneComm_color_left (D : Matrix I32 I32 ℂ) (m n : Fin 24)
    (hm : 6 ≤ m.val) :
    orderOneComm D (AFGenerators m) (AFGenerators n) = 0 := by
  obtain ⟨mc, hmc⟩ := AFGenerators_color m hm
  rw [hmc]
  exact orderOneComm_of_pi_left_zero _ _ _ (pi_pure_color_zero mc)

theorem orderOneComm_color_right (D : Matrix I32 I32 ℂ) (m n : Fin 24)
    (hn : 6 ≤ n.val) :
    orderOneComm D (AFGenerators m) (AFGenerators n) = 0 := by
  obtain ⟨mc, hmc⟩ := AFGenerators_color n hn
  rw [hmc]
  exact orderOneComm_of_pi_right_zero _ _ _ (pi_pure_color_zero mc)

/-! ## Refutation of `OrderOneHolds` for the SM ansatz

The `(⟨1,0,0⟩, ⟨1,0,0⟩)` pair: `pi ⟨1,0,0⟩` is diagonal with `1` at `(8,8)`
and `(9,9)`; `piOp` of it is diagonal with `1` at `(24,24)` and `(25,25)`;
the Majorana block gives `smDirac_{8,24} = conj(yR)`. The double commutator
at `(8,24)` is `-conj(yR)`, nonzero for `yR ≠ 0`.
-/

/-- The Majorana block entry: `smDirac_{8,24} = conj(yR)`. For `yR = 1`: `1`. -/
theorem smDirac_8_24 :
    smDirac (0:ℂ) 0 0 0 1 ⟨8, by norm_num⟩ ⟨24, by norm_num⟩ = 1 := by
  unfold smDirac
  rw [buildDirac_Edag_entry _ _ _ _ _ _
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  unfold majoranaBlock
  simp [Matrix.conjTranspose_apply, Matrix.diagonal_apply]

/-- `pi ⟨1,0,0⟩` at `(8,8)` is `1`. -/
theorem pi_u1_88 :
    pi (⟨1,0,0⟩ : AF) ⟨8, by norm_num⟩ ⟨8, by norm_num⟩ = 1 := by
  unfold pi embedSM
  dsimp only
  simp

/-- `pi ⟨1,0,0⟩` vanishes when the column index is `≥ 16`. -/
theorem pi_u1_col_ge16 (k j : I32) (hj : 16 ≤ j.val) :
    pi (⟨1,0,0⟩ : AF) k j = 0 := by
  unfold pi
  split_ifs with h
  · omega
  · rfl

/-- `pi ⟨1,0,0⟩` at `(8,k)` vanishes for `k ≠ 8`. -/
theorem pi_u1_row8_ne (k : I32) (hk : k ≠ ⟨8, by norm_num⟩) :
    pi (⟨1,0,0⟩ : AF) ⟨8, by norm_num⟩ k = 0 := by
  have hk8 : k.val ≠ 8 := by
    intro h
    apply hk
    ext
    simpa using h
  unfold pi embedSM
  dsimp only
  split_ifs <;> first | omega | simp | rfl

/-- `piOp (pi ⟨1,0,0⟩)` at `(k,24)`: supported only at `k = 24`. -/
theorem piOp_u1_entry (k : I32) :
    piOp (pi (⟨1,0,0⟩ : AF)) k ⟨24, by norm_num⟩
      = if k = ⟨24, by norm_num⟩ then 1 else 0 := by
  unfold piOp
  rw [UJ_conj_apply, Matrix.transpose_apply]
  have hp24 : partner (⟨24, by norm_num⟩ : I32) = ⟨8, by norm_num⟩ := by decide
  rw [hp24]
  by_cases hk : k = ⟨24, by norm_num⟩
  · rw [if_pos hk, hk, hp24]
    exact pi_u1_88
  · rw [if_neg hk]
    have hpk : partner k ≠ ⟨8, by norm_num⟩ := by
      intro h
      apply hk
      have hinv := partner_involutive k
      rw [h] at hinv
      have hp8 : partner (⟨8, by norm_num⟩ : I32) = ⟨24, by norm_num⟩ := by decide
      rw [hp8] at hinv
      exact hinv.symm
    exact pi_u1_row8_ne _ hpk

/-- The `(8,24)` entry of the order-one double commutator for
    `(⟨1,0,0⟩, ⟨1,0,0⟩)` with `yR = 1` is `-1`. -/
theorem orderOneComm_u1_u1_entry :
    orderOneComm (smDirac (0:ℂ) 0 0 0 1) (⟨1,0,0⟩ : AF) (⟨1,0,0⟩ : AF)
      ⟨8, by norm_num⟩ ⟨24, by norm_num⟩ = -1 := by
  have hXQ : (((smDirac (0:ℂ) 0 0 0 1) * pi (⟨1,0,0⟩ : AF)
      - pi (⟨1,0,0⟩ : AF) * (smDirac (0:ℂ) 0 0 0 1))
      * piOp (pi (⟨1,0,0⟩ : AF))) ⟨8, by norm_num⟩ ⟨24, by norm_num⟩
      = ((smDirac (0:ℂ) 0 0 0 1) * pi (⟨1,0,0⟩ : AF)
        - pi (⟨1,0,0⟩ : AF) * (smDirac (0:ℂ) 0 0 0 1))
        ⟨8, by norm_num⟩ ⟨24, by norm_num⟩ := by
    rw [Matrix.mul_apply, Finset.sum_eq_single ⟨24, by norm_num⟩]
    · rw [piOp_u1_entry, if_pos rfl, mul_one]
    · intro k _ hk
      rw [piOp_u1_entry, if_neg hk, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hQX : (piOp (pi (⟨1,0,0⟩ : AF))
      * ((smDirac (0:ℂ) 0 0 0 1) * pi (⟨1,0,0⟩ : AF)
        - pi (⟨1,0,0⟩ : AF) * (smDirac (0:ℂ) 0 0 0 1)))
      ⟨8, by norm_num⟩ ⟨24, by norm_num⟩ = 0 := by
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro k _
    have hQ8k : piOp (pi (⟨1,0,0⟩ : AF)) ⟨8, by norm_num⟩ k = 0 := by
      show (UJ * (pi (⟨1,0,0⟩ : AF)).transpose * UJ) ⟨8, by norm_num⟩ k = 0
      rw [UJ_conj_apply, Matrix.transpose_apply]
      have hp8 : partner (⟨8, by norm_num⟩ : I32) = ⟨24, by norm_num⟩ := by decide
      rw [hp8]
      exact pi_u1_col_ge16 _ _ (by norm_num)
    rw [hQ8k, zero_mul]
  have hX : ((smDirac (0:ℂ) 0 0 0 1) * pi (⟨1,0,0⟩ : AF)
      - pi (⟨1,0,0⟩ : AF) * (smDirac (0:ℂ) 0 0 0 1))
      ⟨8, by norm_num⟩ ⟨24, by norm_num⟩ = -1 := by
    rw [Matrix.sub_apply]
    have hDd1 : ((smDirac (0:ℂ) 0 0 0 1) * pi (⟨1,0,0⟩ : AF))
        ⟨8, by norm_num⟩ ⟨24, by norm_num⟩ = 0 := by
      rw [Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro k _
      rw [pi_u1_col_ge16 k _ (by norm_num), mul_zero]
    have hd1D : (pi (⟨1,0,0⟩ : AF) * (smDirac (0:ℂ) 0 0 0 1))
        ⟨8, by norm_num⟩ ⟨24, by norm_num⟩ = 1 := by
      rw [Matrix.mul_apply, Finset.sum_eq_single ⟨8, by norm_num⟩]
      · rw [pi_u1_88, smDirac_8_24, one_mul]
      · intro k _ hk
        rw [pi_u1_row8_ne k hk, zero_mul]
      · intro h
        exact absurd (Finset.mem_univ _) h
    rw [hDd1, hd1D, zero_sub]
  unfold orderOneComm
  rw [Matrix.sub_apply, hXQ, hQX, hX, sub_zero]

/-- The `(⟨1,0,0⟩, ⟨1,0,0⟩)` order-one commutator is nonzero. -/
theorem orderOneComm_u1_u1_ne_zero :
    orderOneComm (smDirac (0:ℂ) 0 0 0 1) (⟨1,0,0⟩ : AF) (⟨1,0,0⟩ : AF) ≠ 0 := by
  intro h
  have hentry := orderOneComm_u1_u1_entry
  rw [h] at hentry
  simp at hentry

/-- `AFGenerators 0 = ⟨1,0,0⟩`. -/
theorem AFGenerators_zero :
    AFGenerators (0 : Fin 24) = (⟨1,0,0⟩ : AF) := by
  unfold AFGenerators
  simp

/-- MAIN REFUTATION (T3, proved): the OLD `OrderOneHolds_optionA` — as defined
    via the Option-A `pi` — is NOT satisfied by the SM Dirac ansatz. This
    motivated the 2026-09-28 repair redefining `OrderOneHolds` via `smGen`. -/
theorem not_OrderOneHolds_optionA_smDirac :
    ¬ OrderOneHolds_optionA (smDirac (0:ℂ) 0 0 0 1) := by
  intro h
  unfold OrderOneHolds_optionA at h
  have h00 := h (0 : Fin 24) (0 : Fin 24)
  rw [AFGenerators_zero] at h00
  exact orderOneComm_u1_u1_ne_zero h00

end ThetLogos
