import Mathlib.Tactic
import ThetLogos.DialOneExtraction
import ThetLogos.DialOneCrossSign
import ThetLogos.DialOneShapeBIdentification

open Matrix Complex
open ThetLogos.Track1RouteB
open ThetLogos.PreOptionARepresentation
open ThetLogos.HyperchargeForcing
open ThetLogos.DialOneSeatTiePin
open ThetLogos.DialOneExtraction
open ThetLogos.DialOneCrossSign
open ThetLogos.DialOneShapeBIdentification
open ThetLogos.DialOneClassificationPin

/-!
# ThetLogos.DialOneConjugationCounterexample — CLS-1a-FIRE: K-CLS-1a by construction

Governing texts: CLS-1a/1b scoping §1.5 (the registered
conjugation route) and the BR1-029 probe memo
(`routeb-general-scratch/scoping-br1-029-conjugation-probe-2026-11-02.md`),
whose exact-arithmetic verdict was ROUTE LIVE at generic
Yukawa values. This module is the T1 firing: **K-CLS-1a
FIRES, in BASE form.**

## The witness

`conjU` is the probe's explicit rational orthogonal matrix:
identity outside its 12-seat support (the u-channel seats
`{2, 4, 6, 26, 28, 30}` in `V₊` and `{10, 12, 14, 18, 20, 22}`
in `V₋`, in the probe's D-correspondence orders), acting on
each sign block as `[[P, Q], [Q, P]]` with
`P = diag(3/5, 3/5, 1)` and `Q` the `(4/5)`-rotation block
(entries in `{0, ±1, ±3/5, ±4/5}`, seated here through the
seat-mate involution `mateSeat`: `2 ↔ 28`, `4 ↔ 26`,
`10 ↔ 20`, `12 ↔ 18`, diagonal coefficient `diagC`,
off-diagonal coefficient `offC`). `piU a := conjU * pi1 a *
conjUᵀ` is the conjugate representation.

## Transport checklist (§1.5 conditions (a)/(b)/(c), per clause group)

The §1.5 transport hypotheses are proved, not assumed:

* **(a) grading**: `conjU_gamma_comm` — `[conjU, gammaF] = 0`
  (seat-mates share their γ-sign, `gammaF_mateSeat`).
* **(b) J-intertwining**: `piOp_conjU` — `piOp conjU =
  conjUᵀ` (i.e. `piOp (U) = U⁻¹` in the transport form, since
  `conjU * conjUᵀ = 1`), and its consequence `piOp_conj`:
  `piOp (conjU * M * conjUᵀ) = conjU * (piOp M) * conjUᵀ`
  for all `M`, via `piOp_mul_rev` and
  `piOp_conjU_transpose`.
* **(c) Dirac channels at GENERIC Yukawa values**:
  `conjU_df_comm` — `[conjU, DF_oneGen Ynu Ye Yu Yd] = 0`
  for all real `Ynu Ye Yu Yd`. The proof goes through the
  channel coefficient matrices: `df_entry` writes
  `DF_oneGen` entrywise through the per-seat channel
  coefficient `dcoef` (the slot's channel `ν/e/u/d`, i.e.
  `DF = Σ_ch Y_ch • D_ch` entrywise), and the commutation
  is checked against those coefficients — no seated Yukawa
  value is used anywhere.

Clause-group transport for `dialOneBase_piU` (every one of
the ten clauses of `DialOneBase`, from
`dialOneBase_pi1`):

* clauses 1–2 (mul/add): `conj_mul` / `conj_add` — pure
  sandwich algebra from `conjUᵀ * conjU = 1`.
* clause 3 (star): `conjU_conjTranspose` (`conjUᴴ =
  conjUᵀ`, entries real) and
  `conjU_transpose_conjTranspose`.
* clauses 4–5 (one/zero): `conjU_mul_transpose` and
  `Matrix.mul_zero`/`zero_mul` sandwich collapse.
* clause 6 (injectivity): left/right cancellation by
  `conjUᵀ`/`conjU` against `pi1_injective`.
* clause 7 (grading): (a) on the left, and
  `gammaF_conjU_transpose_comm` on the right (via
  `gammaFᵀ = gammaF`).
* clause 8 (order-zero): (b) (`piOp_conj`) + `conj_mul`
  + π₁'s clause 8.
* clause 9 (first-order): (c) on the left
  (`left_conj_comm`), (c) for the transpose on the right
  (`df_conjU_transpose_comm`, via `DF_oneGenᵀ =
  DF_oneGen`), (b) for the `piOp` factor, `conj_mul` /
  `conj_sub` — reducing entrywise to π₁'s clause 9.
* clause 10 (unimodular direction): `piU_det` —
  `det (piU a) = det (pi1 a)` (determinant is
  conjugation-invariant), so π₁'s primitive direction
  `(3, -1)` serves verbatim.

**No clause resisted transport.** (Had one resisted, the
pack's instruction was STOP-and-report; none did.)

## The firing computation

`liftedProd_piU_entry_form`: along `(3, -1)`,
`liftedProd piU 3 (-1) t` at the seat pair `(2, 28)` is
`(12/25) • (exp (4 • (t • I)) - exp (1 • (t • I)))` — the
`(12/25)(x⁴ - x¹)` Laurent entry of the probe, with
`x = e^{it}`. Seats `2` and `28` are both `γ = +1`
(`gamma_two_twenty_eight`) with π₁ lifted weights `1` and
`4` (`weights_two_twenty_eight`, from
`commonWeightVector`). At `t = π/2`:
`liftedProd_piU_entry_pi_div_two` — the entry is
`(12/25)(1 - i)`, and `liftedProd_piU_entry_ne_zero` — it
is `≠ 0`. The second primitive det-1 direction `(-3, 1)`
is the same computation at `-t`
(`liftedProd_piU_entry_neg_dir`, via `u1ParamGen_neg`), and
`det_one_pi1` + `dir_of_det_shape_4312` (landed,
`DialOneShapeBIdentification`) say `(3, -1)` and `(-3, 1)`
are the ONLY primitive det-1 directions.

## The headline

* `k_cls_1a_fired` — the registered kill form: there is a
  `π` (`piU`) with `DialOneBase π` such that for EVERY
  primitive direction with `det = 1` along the family
  there exist `t` and seats `s ≠ s'` of the SAME γ-sign
  with `liftedProd π α β t s s' ≠ 0`.
* `not_forall_base_diagLift` — **K-CLS-1a FIRED, base
  form**: `¬ ∀ π, DialOneBase π → DiagLift π`, witnessed
  by `piU` at `(2, 28)`. `DiagLift` has NO in-tree
  definition; the one below is frozen verbatim from the
  CLS-1a scoping §1.1 (the first three conjuncts of
  `ExtractionLemma`, at one joint direction), and this
  module says so on its face.

## Fences (on the face)

* **Base form only.** The STRENGTHENED form is NOT
  addressed: `colProj c` does not commute with `conjU`
  (it mixes colours across the half-split), so
  C3col-type clauses are not inherited; `piU`'s
  strengthened-family status is claimed NEITHER way.
* **`(8, 9)` is NOT the firing pair and cannot be**
  (channel separation, probe §3): seats `8` and `9` lie
  in different channel groups and no element of the
  (a)∧(c) commutant mixes them. The firing pair is
  `(2, 28)` (with `(4, 26)` and the `V₋` mirrors in the
  support). CLS-1a-X's cross-sign theorem is untouched;
  `(8, 9)` remains a γ-blind pair whose diagonality
  clause 7 does not force — it is simply not reachable
  by THIS construction.
* `DiagLift` + regularity remain the extraction's
  hypothesis material (CLS-1 PARTIAL stands); this
  module proves only that the diagonality half is not
  base-implied. Grade W untouched.

**NO CLAIM. Dial 1 = 0; all dials 0/4.**
-/

namespace ThetLogos.DialOneConjugationCounterexample

/-- mate involution on seats -/
def mateSeat (i : Fin 32) : Fin 32 :=
  if i.val = 2 then ⟨28, by norm_num⟩
  else if i.val = 28 then ⟨2, by norm_num⟩
  else if i.val = 4 then ⟨26, by norm_num⟩
  else if i.val = 26 then ⟨4, by norm_num⟩
  else if i.val = 10 then ⟨20, by norm_num⟩
  else if i.val = 20 then ⟨10, by norm_num⟩
  else if i.val = 12 then ⟨18, by norm_num⟩
  else if i.val = 18 then ⟨12, by norm_num⟩
  else i

noncomputable def diagC (i : Fin 32) : ℂ :=
  if i.val = 2 ∨ i.val = 4 ∨ i.val = 10 ∨ i.val = 12
      ∨ i.val = 18 ∨ i.val = 20 ∨ i.val = 26 ∨ i.val = 28
    then ((3 / 5 : ℝ) : ℂ) else 1

noncomputable def offC (i : Fin 32) : ℂ :=
  if i.val = 2 ∨ i.val = 10 ∨ i.val = 18 ∨ i.val = 26
    then ((4 / 5 : ℝ) : ℂ)
  else if i.val = 4 ∨ i.val = 12 ∨ i.val = 20 ∨ i.val = 28
    then (-(4 / 5 : ℝ) : ℂ) else 0

noncomputable def conjU : Matrix (Fin 32) (Fin 32) ℂ := fun i j =>
  if j = i then diagC i
  else if j = mateSeat i then offC i
  else 0

theorem mateSeat_involutive (i : Fin 32) : mateSeat (mateSeat i) = i := by
  fin_cases i <;> rfl

theorem mateSeat_diagC (i : Fin 32) : diagC (mateSeat i) = diagC i := by
  fin_cases i <;> rfl

theorem mateSeat_offC (i : Fin 32) : offC (mateSeat i) = -offC i := by
  fin_cases i <;> simp [mateSeat, offC] <;> norm_num

theorem mateSeat_mate_ne (i : Fin 32) (h : mateSeat i ≠ i) :
    mateSeat (mateSeat i) ≠ mateSeat i := by
  rw [mateSeat_involutive]; exact Ne.symm h

theorem mateSeat_injective : Function.Injective mateSeat :=
  Function.Involutive.injective mateSeat_involutive

theorem partner_diagC (i : Fin 32) : diagC (partner i) = diagC i := by
  fin_cases i <;> rfl

theorem partner_offC (i : Fin 32) : offC (partner i) = offC i := by
  fin_cases i <;> rfl

theorem mateSeat_partner (i : Fin 32) :
    mateSeat (partner i) = partner (mateSeat i) := by
  fin_cases i <;> rfl

theorem mateSeat_eq_self_diagC (i : Fin 32) (h : mateSeat i = i) :
    diagC i = 1 ∧ offC i = 0 := by
  fin_cases i <;> simp_all [mateSeat, diagC, offC]

theorem diagC_sq_add_offC_sq (i : Fin 32) :
    diagC i * diagC i + offC i * offC i = 1 := by
  fin_cases i <;> simp [diagC, offC] <;> norm_num


theorem conjU_apply_diag (i : Fin 32) : conjU i i = diagC i := by
  simp [conjU]

theorem conjU_apply_mate (i : Fin 32) (h : mateSeat i ≠ i) :
    conjU i (mateSeat i) = offC i := by
  simp [conjU, h, Ne.symm h]

theorem conjU_apply_of_ne (i k : Fin 32) (h1 : k ≠ i) (h2 : k ≠ mateSeat i) :
    conjU i k = 0 := by
  simp [conjU, h1, h2]

theorem conjU_mul_apply (M : Matrix (Fin 32) (Fin 32) ℂ) (i j : Fin 32) :
    (conjU * M) i j = diagC i * M i j + offC i * M (mateSeat i) j := by
  rw [Matrix.mul_apply]
  by_cases hm : mateSeat i = i
  · have hdc : diagC i = 1 ∧ offC i = 0 := mateSeat_eq_self_diagC i hm
    rw [Finset.sum_eq_single i]
    · simp [conjU_apply_diag, hdc.1, hdc.2, hm]
    · intro k _ hk
      have hk2 : k ≠ mateSeat i := by rw [hm]; exact hk
      rw [conjU_apply_of_ne i k hk hk2, zero_mul]
    · intro hcon; exact absurd (Finset.mem_univ i) hcon
  · have hsum : (∑ k : Fin 32, conjU i k * M k j)
        = ∑ k ∈ ({i, mateSeat i} : Finset (Fin 32)), conjU i k * M k j :=
      (Finset.sum_subset (Finset.subset_univ _) (fun k _ hk => by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hk
        push_neg at hk
        rw [conjU_apply_of_ne i k hk.1 hk.2, zero_mul])).symm
    rw [hsum, Finset.sum_insert (by rw [Finset.mem_singleton]; exact Ne.symm hm),
      Finset.sum_singleton, conjU_apply_diag, conjU_apply_mate i hm]

theorem mul_conjU_apply (M : Matrix (Fin 32) (Fin 32) ℂ) (i j : Fin 32) :
    (M * conjU) i j = M i j * diagC j + M i (mateSeat j) * offC (mateSeat j) := by
  rw [Matrix.mul_apply]
  by_cases hm : mateSeat j = j
  · have hdc : diagC j = 1 ∧ offC j = 0 := mateSeat_eq_self_diagC j hm
    rw [Finset.sum_eq_single j]
    · rw [hm, conjU_apply_diag, hdc.1, hdc.2]
      simp
    · intro k _ hk
      have hkj : conjU k j = 0 := by
        apply conjU_apply_of_ne k j (Ne.symm hk)
        intro hcon
        have h2 : mateSeat j = k := by
          have h3 : mateSeat j = mateSeat (mateSeat k) := congrArg mateSeat hcon
          rwa [mateSeat_involutive] at h3
        rw [hm] at h2
        exact hk h2.symm
      rw [hkj, mul_zero]
    · intro hcon; exact absurd (Finset.mem_univ j) hcon
  · have hsum : (∑ k : Fin 32, M i k * conjU k j)
        = ∑ k ∈ ({j, mateSeat j} : Finset (Fin 32)), M i k * conjU k j :=
      (Finset.sum_subset (Finset.subset_univ _) (fun k _ hk => by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hk
        push_neg at hk
        have hkj : conjU k j = 0 := by
          apply conjU_apply_of_ne k j (Ne.symm hk.1)
          intro hcon
          have h2 : mateSeat j = k := by
            have h3 : mateSeat j = mateSeat (mateSeat k) :=
              congrArg mateSeat hcon
            rwa [mateSeat_involutive] at h3
          exact hk.2 h2.symm
        rw [hkj, mul_zero])).symm
    rw [hsum, Finset.sum_insert (by rw [Finset.mem_singleton]; exact Ne.symm hm),
      Finset.sum_singleton, conjU_apply_diag]
    have hmj : conjU (mateSeat j) j = offC (mateSeat j) := by
      unfold conjU
      rw [if_neg (Ne.symm hm), if_pos (mateSeat_involutive j).symm]
    rw [hmj]

theorem conjU_transpose_mate (i : Fin 32) (h : mateSeat i ≠ i) :
    conjUᵀ i (mateSeat i) = offC (mateSeat i) := by
  rw [Matrix.transpose_apply]
  unfold conjU
  rw [if_neg (Ne.symm h), if_pos (mateSeat_involutive i).symm]

theorem conjU_transpose_of_ne (i j : Fin 32) (h1 : j ≠ i) (h2 : j ≠ mateSeat i) :
    conjUᵀ i j = 0 := by
  rw [Matrix.transpose_apply]
  apply conjU_apply_of_ne j i (Ne.symm h1)
  intro hcon
  have h3 : mateSeat i = mateSeat (mateSeat j) := congrArg mateSeat hcon
  rw [mateSeat_involutive] at h3
  exact h2 h3.symm

theorem conjU_mul_transpose : conjU * conjUᵀ = 1 := by
  ext i j
  rw [conjU_mul_apply]
  by_cases hij : j = i
  · rw [← hij, Matrix.transpose_apply, conjU_apply_diag, Matrix.one_apply_eq]
    by_cases hm : mateSeat j = j
    · have hdc := mateSeat_eq_self_diagC j hm
      rw [Matrix.transpose_apply, hm, conjU_apply_diag, hdc.1, hdc.2]
      norm_num
    · rw [Matrix.transpose_apply, conjU_apply_mate j hm]
      exact diagC_sq_add_offC_sq j
  · by_cases hjm : j = mateSeat i
    · subst hjm
      have hm : mateSeat i ≠ i := hij
      rw [Matrix.one_apply_ne (Ne.symm hm), conjU_transpose_mate i hm,
        Matrix.transpose_apply, conjU_apply_diag, mateSeat_diagC,
        mateSeat_offC]
      ring
    · rw [Matrix.one_apply_ne (Ne.symm hij), conjU_transpose_of_ne i j hij hjm]
      have h3 : conjUᵀ (mateSeat i) j = 0 := by
        apply conjU_transpose_of_ne (mateSeat i) j hjm
        intro hcon
        have h4 : mateSeat j = mateSeat i := by
          have h5 : mateSeat j = mateSeat (mateSeat (mateSeat i)) :=
            congrArg mateSeat hcon
          rwa [mateSeat_involutive] at h5
        exact hij (mateSeat_injective h4)
      rw [h3]
      ring

theorem conjU_transpose_mul : conjUᵀ * conjU = 1 := by
  have h := conjU_mul_transpose
  rwa [mul_eq_one_comm] at h

/-- piOp of conjU is its transpose -/
theorem piOp_conjU : piOp conjU = conjUᵀ := by
  ext i j
  rw [piOp_apply, Matrix.transpose_apply]
  by_cases hij : j = i
  · subst hij
    rw [conjU_apply_diag, conjU_apply_diag, partner_diagC]
  · by_cases hjm : j = mateSeat i
    · subst hjm
      have hpi : partner i ≠ partner (mateSeat i) := by
        intro hcon
        have h3 := congrArg partner hcon
        rw [partner_involutive, partner_involutive] at h3
        exact hij h3.symm
      have hmate : partner i = mateSeat (partner (mateSeat i)) := by
        rw [mateSeat_partner, mateSeat_involutive]
      have hL : conjU (partner (mateSeat i)) (partner i)
          = offC (partner (mateSeat i)) := by
        conv_lhs => rw [hmate]
        exact conjU_apply_mate _ (by rw [← hmate]; exact hpi)
      have hR : conjU (mateSeat i) i = offC (mateSeat i) := by
        have h := conjU_transpose_mate i hij
        rwa [Matrix.transpose_apply] at h
      rw [hL, hR, partner_offC]
    · have h1 : conjU (partner j) (partner i) = 0 := by
        apply conjU_apply_of_ne
        · intro hcon
          exact hij (Function.Involutive.injective partner_involutive hcon.symm)
        · intro hcon
          apply hjm
          have h3 : i = mateSeat j := by
            have h4 : partner i = partner (mateSeat j) := by
              rw [hcon, mateSeat_partner]
            exact Function.Involutive.injective partner_involutive h4
          have h5 : mateSeat i = j := by
            have h6 : mateSeat i = mateSeat (mateSeat j) :=
              congrArg mateSeat h3
            rwa [mateSeat_involutive] at h6
          exact h5.symm
      have hne2 : i ≠ mateSeat j := by
        intro hh
        have h3 : mateSeat i = mateSeat (mateSeat j) := congrArg mateSeat hh
        rw [mateSeat_involutive] at h3
        exact hjm h3.symm
      rw [h1, conjU_apply_of_ne j i (Ne.symm hij) hne2]

theorem star_diagC (i : Fin 32) : star (diagC i) = diagC i := by
  unfold diagC
  split_ifs <;> simp

theorem star_offC (i : Fin 32) : star (offC i) = offC i := by
  unfold offC
  split_ifs <;> simp

theorem conjU_conjTranspose : conjUᴴ = conjUᵀ := by
  ext i j
  rw [Matrix.conjTranspose_apply, Matrix.transpose_apply]
  by_cases h1 : i = j
  · rw [h1, conjU_apply_diag, star_diagC]
  · by_cases h2 : i = mateSeat j
    · have hval : conjU j i = offC j := by
        unfold conjU
        rw [if_neg h1, if_pos h2]
      rw [hval, star_offC]
    · rw [conjU_apply_of_ne j i h1 h2]
      simp

theorem conjU_transpose_conjTranspose : conjUᵀᴴ = conjU := by
  have h1 : conjUᴴ = conjUᵀ := conjU_conjTranspose
  have h2 : conjUᴴᴴ = conjU := Matrix.conjTranspose_conjTranspose conjU
  rw [h1] at h2
  exact h2


/-- Dirac partner seat -/
def dparSeat (i : Fin 32) : Fin 32 :=
  if h1 : i.val < 8 then ⟨i.val + 8, by have h := i.isLt; omega⟩
  else if h2 : i.val < 16 then ⟨i.val - 8, by have h := i.isLt; omega⟩
  else if h3 : i.val < 24 then ⟨i.val + 8, by have h := i.isLt; omega⟩
  else ⟨i.val - 8, by have h := i.isLt; omega⟩

noncomputable def dcoef (Ynu Ye Yu Yd : ℝ) (i : Fin 32) : ℂ :=
  let s := i.val % 8
  if s = 0 then (Ynu : ℂ)
  else if s = 1 then (Ye : ℂ)
  else if s % 2 = 0 then (Yu : ℂ)
  else (Yd : ℂ)

theorem dparSeat_involutive (i : Fin 32) : dparSeat (dparSeat i) = i := by
  fin_cases i <;> rfl

theorem mateSeat_dparSeat (i : Fin 32) :
    mateSeat (dparSeat i) = dparSeat (mateSeat i) := by
  fin_cases i <;> rfl

theorem diagC_dparSeat (i : Fin 32) : diagC (dparSeat i) = diagC i := by
  fin_cases i <;> rfl

theorem offC_dparSeat (i : Fin 32) : offC (dparSeat i) = offC i := by
  fin_cases i <;> rfl

theorem dcoef_mateSeat (Ynu Ye Yu Yd : ℝ) (i : Fin 32) :
    dcoef Ynu Ye Yu Yd (mateSeat i) = dcoef Ynu Ye Yu Yd i := by
  fin_cases i <;> rfl

theorem dcoef_dparSeat (Ynu Ye Yu Yd : ℝ) (i : Fin 32) :
    dcoef Ynu Ye Yu Yd (dparSeat i) = dcoef Ynu Ye Yu Yd i := by
  have hmod : (dparSeat i).val % 8 = i.val % 8 := by
    unfold dparSeat
    split_ifs <;> simp only [] <;> omega
  unfold dcoef
  rw [hmod]

set_option maxHeartbeats 6400000 in
theorem df_entry (Ynu Ye Yu Yd : ℝ) (i j : Fin 32) :
    DF_oneGen Ynu Ye Yu Yd i j
      = if j = dparSeat i then dcoef Ynu Ye Yu Yd i else 0 := by
  fin_cases i <;> fin_cases j <;> simp [DF_oneGen, buildDirac, dparSeat, dcoef]


theorem gammaF_mateSeat (i : Fin 32) :
    gammaF (mateSeat i) (mateSeat i) = gammaF i i := by
  fin_cases i <;> rfl

theorem conjU_gamma_comm : gammaF * conjU = conjU * gammaF := by
  ext i j
  rw [gammaF_mul_apply, mul_gammaF_apply]
  by_cases h1 : j = i
  · rw [h1]; ring
  · by_cases h2 : j = mateSeat i
    · rw [h2, gammaF_mateSeat]; ring
    · rw [conjU_apply_of_ne i j h1 h2]; simp

theorem gammaF_transpose_eq : gammaFᵀ = gammaF := by
  ext i j
  rw [Matrix.transpose_apply]
  by_cases h : i = j
  · rw [h]
  · rw [gammaF_apply_ne h, gammaF_apply_ne (Ne.symm h)]

theorem transpose_conjU_comm_of_comm {M : Matrix (Fin 32) (Fin 32) ℂ}
    (hM : Mᵀ = M) (h : M * conjU = conjU * M) : M * conjUᵀ = conjUᵀ * M := by
  calc M * conjUᵀ = Mᵀ * conjUᵀ := by rw [hM]
    _ = (conjU * M)ᵀ := by rw [Matrix.transpose_mul]
    _ = (M * conjU)ᵀ := by rw [h]
    _ = conjUᵀ * Mᵀ := by rw [Matrix.transpose_mul]
    _ = conjUᵀ * M := by rw [hM]

theorem gammaF_conjU_transpose_comm : gammaF * conjUᵀ = conjUᵀ * gammaF :=
  transpose_conjU_comm_of_comm gammaF_transpose_eq conjU_gamma_comm

theorem df_transpose_eq (Ynu Ye Yu Yd : ℝ) :
    (DF_oneGen Ynu Ye Yu Yd)ᵀ = DF_oneGen Ynu Ye Yu Yd := by
  ext i j
  rw [Matrix.transpose_apply, df_entry, df_entry]
  by_cases h : j = dparSeat i
  · rw [if_pos h]
    have h2 : i = dparSeat j := by
      rw [h]; exact (dparSeat_involutive i).symm
    rw [if_pos h2, h, dcoef_dparSeat]
  · rw [if_neg h]
    apply if_neg
    intro h2
    apply h
    have h3 : dparSeat i = dparSeat (dparSeat j) := congrArg dparSeat h2
    rw [dparSeat_involutive] at h3
    exact h3.symm

theorem conjU_df_comm (Ynu Ye Yu Yd : ℝ) :
    DF_oneGen Ynu Ye Yu Yd * conjU = conjU * DF_oneGen Ynu Ye Yu Yd := by
  ext i j
  rw [mul_conjU_apply, conjU_mul_apply]
  have hC : (j = dparSeat (mateSeat i)) ↔ (mateSeat j = dparSeat i) := by
    constructor
    · intro hh
      have h2 : mateSeat j = mateSeat (dparSeat (mateSeat i)) :=
        congrArg mateSeat hh
      rwa [mateSeat_dparSeat, mateSeat_involutive] at h2
    · intro hh
      have h2 : mateSeat (mateSeat j) = mateSeat (dparSeat i) :=
        congrArg mateSeat hh
      rwa [mateSeat_involutive, mateSeat_dparSeat] at h2
  by_cases hA : j = dparSeat i
  · by_cases hB : mateSeat j = dparSeat i
    · have hdj : diagC j = diagC i := by rw [hA]; exact diagC_dparSeat i
      have hmj : mateSeat j = j := by rw [hB, ← hA]
      have hoc : offC (mateSeat j) = offC i := by
        rw [hmj, hA]; exact offC_dparSeat i
      have hdc : dcoef Ynu Ye Yu Yd (mateSeat i) = dcoef Ynu Ye Yu Yd i :=
        dcoef_mateSeat _ _ _ _ i
      rw [df_entry, if_pos hA, df_entry, if_pos hB, df_entry,
        if_pos (hC.mpr hB), hdj, hoc, hdc]
      ring
    · have hdj : diagC j = diagC i := by rw [hA]; exact diagC_dparSeat i
      rw [df_entry, if_pos hA, df_entry, if_neg hB, df_entry,
        if_neg (fun hh => hB (hC.mp hh)), hdj]
      ring
  · by_cases hB : mateSeat j = dparSeat i
    · have hoc : offC (mateSeat j) = offC i := by
        rw [hB]; exact offC_dparSeat i
      have hdc : dcoef Ynu Ye Yu Yd (mateSeat i) = dcoef Ynu Ye Yu Yd i :=
        dcoef_mateSeat _ _ _ _ i
      rw [df_entry, if_neg hA, df_entry, if_pos hB, df_entry,
        if_pos (hC.mpr hB), hoc, hdc]
      ring
    · rw [df_entry, if_neg hA, df_entry, if_neg hB, df_entry,
        if_neg (fun hh => hB (hC.mp hh))]
      ring

theorem df_conjU_transpose_comm (Ynu Ye Yu Yd : ℝ) :
    DF_oneGen Ynu Ye Yu Yd * conjUᵀ = conjUᵀ * DF_oneGen Ynu Ye Yu Yd :=
  transpose_conjU_comm_of_comm (df_transpose_eq _ _ _ _) (conjU_df_comm _ _ _ _)


/-- The conjugated representation -/
noncomputable def piU (a : AF) : Matrix (Fin 32) (Fin 32) ℂ :=
  conjU * pi1 a * conjUᵀ

theorem conj_mul (X Y : Matrix (Fin 32) (Fin 32) ℂ) :
    (conjU * X * conjUᵀ) * (conjU * Y * conjUᵀ)
      = conjU * (X * Y) * conjUᵀ := by
  have h : (conjU * X * conjUᵀ) * (conjU * Y * conjUᵀ)
      = conjU * X * (conjUᵀ * conjU) * Y * conjUᵀ := by
    simp only [Matrix.mul_assoc]
  rw [h, conjU_transpose_mul]
  simp [Matrix.mul_assoc]

theorem conj_add (X Y : Matrix (Fin 32) (Fin 32) ℂ) :
    conjU * (X + Y) * conjUᵀ = conjU * X * conjUᵀ + conjU * Y * conjUᵀ := by
  rw [Matrix.mul_add, Matrix.add_mul]

theorem conj_sub (X Y : Matrix (Fin 32) (Fin 32) ℂ) :
    conjU * (X - Y) * conjUᵀ = conjU * X * conjUᵀ - conjU * Y * conjUᵀ := by
  rw [Matrix.mul_sub, Matrix.sub_mul]

theorem left_conj_comm {M : Matrix (Fin 32) (Fin 32) ℂ}
    (h : M * conjU = conjU * M) (X : Matrix (Fin 32) (Fin 32) ℂ) :
    M * (conjU * X * conjUᵀ) = conjU * (M * X) * conjUᵀ := by
  calc M * (conjU * X * conjUᵀ) = (M * conjU) * X * conjUᵀ := by
        simp only [Matrix.mul_assoc]
    _ = (conjU * M) * X * conjUᵀ := by rw [h]
    _ = conjU * (M * X) * conjUᵀ := by simp only [Matrix.mul_assoc]

theorem right_conj_comm {M : Matrix (Fin 32) (Fin 32) ℂ}
    (h : conjUᵀ * M = M * conjUᵀ) (X : Matrix (Fin 32) (Fin 32) ℂ) :
    (conjU * X * conjUᵀ) * M = conjU * (X * M) * conjUᵀ := by
  calc (conjU * X * conjUᵀ) * M = conjU * X * (conjUᵀ * M) := by
        simp only [Matrix.mul_assoc]
    _ = conjU * X * (M * conjUᵀ) := by rw [h]
    _ = conjU * (X * M) * conjUᵀ := by simp only [Matrix.mul_assoc]

theorem piOp_piOp (M : Matrix (Fin 32) (Fin 32) ℂ) : piOp (piOp M) = M := by
  ext i j
  rw [piOp_apply, piOp_apply, partner_involutive, partner_involutive]

theorem piOp_conjU_transpose : piOp conjUᵀ = conjU := by
  have h := piOp_conjU
  rw [← h]
  exact piOp_piOp conjU

theorem piOp_conj (M : Matrix (Fin 32) (Fin 32) ℂ) :
    piOp (conjU * M * conjUᵀ) = conjU * piOp M * conjUᵀ := by
  rw [piOp_mul_rev, piOp_mul_rev, piOp_conjU_transpose, piOp_conjU]
  simp only [Matrix.mul_assoc]

theorem piU_det (a : AF) : (piU a).det = (pi1 a).det := by
  unfold piU
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  have h2 : conjU.det * conjU.det = 1 := by
    have h : (conjU * conjUᵀ).det = 1 := by
      rw [conjU_mul_transpose]; exact Matrix.det_one
    rwa [Matrix.det_mul, Matrix.det_transpose] at h
  calc conjU.det * (pi1 a).det * conjU.det
      = (conjU.det * conjU.det) * (pi1 a).det := by ring
    _ = (pi1 a).det := by rw [h2, one_mul]

theorem dialOneBase_piU : DialOneBase piU := by
  obtain ⟨hmul, hadd, hstar, hone, hzero, hinj, hgamma, hord, hfirst, hdet⟩ :=
    ThetLogos.DialOneGammaTraceChecks.dialOneBase_pi1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a b
    show piU (afMul a b) = piU a * piU b
    unfold piU
    rw [hmul a b]
    exact (conj_mul _ _).symm
  · intro a b
    show piU (afAdd a b) = piU a + piU b
    unfold piU
    rw [hadd a b]
    exact conj_add _ _
  · intro a
    show piU (afStar a) = (piU a)ᴴ
    unfold piU
    rw [hstar a, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      conjU_conjTranspose, conjU_transpose_conjTranspose]
    simp only [Matrix.mul_assoc]
  · show piU afOne = 1
    unfold piU
    rw [hone]
    simp [conjU_mul_transpose]
  · show piU afZero = 0
    unfold piU
    rw [hzero]
    simp
  · intro a b hab
    apply hinj
    have h : conjUᵀ * piU a * conjU = conjUᵀ * piU b * conjU := by rw [hab]
    unfold piU at h
    have e1 : conjUᵀ * (conjU * pi1 a * conjUᵀ) * conjU = pi1 a := by
      calc conjUᵀ * (conjU * pi1 a * conjUᵀ) * conjU
          = (conjUᵀ * conjU) * pi1 a * (conjUᵀ * conjU) := by
            simp only [Matrix.mul_assoc]
        _ = pi1 a := by rw [conjU_transpose_mul]; simp
    have e2 : conjUᵀ * (conjU * pi1 b * conjUᵀ) * conjU = pi1 b := by
      calc conjUᵀ * (conjU * pi1 b * conjUᵀ) * conjU
          = (conjUᵀ * conjU) * pi1 b * (conjUᵀ * conjU) := by
            simp only [Matrix.mul_assoc]
        _ = pi1 b := by rw [conjU_transpose_mul]; simp
    rw [e1, e2] at h
    exact h
  · intro a
    show gammaF * piU a = piU a * gammaF
    unfold piU
    calc gammaF * (conjU * pi1 a * conjUᵀ)
        = conjU * (gammaF * pi1 a) * conjUᵀ :=
          left_conj_comm conjU_gamma_comm _
      _ = conjU * (pi1 a * gammaF) * conjUᵀ := by rw [hgamma a]
      _ = (conjU * pi1 a * conjUᵀ) * gammaF :=
          (right_conj_comm gammaF_conjU_transpose_comm.symm _).symm
  · intro a b
    show piU a * piOp (piU b) = piOp (piU b) * piU a
    unfold piU
    rw [piOp_conj]
    rw [conj_mul, conj_mul, hord a b]
  · intro Ynu Ye Yu Yd a b i j
    have hC : DF_oneGen Ynu Ye Yu Yd * piU a - piU a * DF_oneGen Ynu Ye Yu Yd
        = conjU * (DF_oneGen Ynu Ye Yu Yd * pi1 a
            - pi1 a * DF_oneGen Ynu Ye Yu Yd) * conjUᵀ := by
      have e1 : DF_oneGen Ynu Ye Yu Yd * piU a
          = conjU * (DF_oneGen Ynu Ye Yu Yd * pi1 a) * conjUᵀ := by
        unfold piU
        exact left_conj_comm (conjU_df_comm _ _ _ _) _
      have e2 : piU a * DF_oneGen Ynu Ye Yu Yd
          = conjU * (pi1 a * DF_oneGen Ynu Ye Yu Yd) * conjUᵀ := by
        unfold piU
        exact right_conj_comm (df_conjU_transpose_comm _ _ _ _).symm _
      rw [e1, e2]
      exact (conj_sub _ _).symm
    have hmain : ((DF_oneGen Ynu Ye Yu Yd * piU a
          - piU a * DF_oneGen Ynu Ye Yu Yd) * piOp (piU b)
        - piOp (piU b) * (DF_oneGen Ynu Ye Yu Yd * piU a
          - piU a * DF_oneGen Ynu Ye Yu Yd)) = 0 := by
      rw [hC]
      unfold piU
      rw [piOp_conj, conj_mul, conj_mul]
      have h0 : ((DF_oneGen Ynu Ye Yu Yd * pi1 a
            - pi1 a * DF_oneGen Ynu Ye Yu Yd) * piOp (pi1 b)
          - piOp (pi1 b) * (DF_oneGen Ynu Ye Yu Yd * pi1 a
            - pi1 a * DF_oneGen Ynu Ye Yu Yd)) = 0 := by
        ext x y
        rw [Matrix.zero_apply]
        exact hfirst Ynu Ye Yu Yd a b x y
      rw [← conj_sub, h0]
      simp
    have h := congrArg (fun M : Matrix (Fin 32) (Fin 32) ℂ => M i j) hmain
    rwa [Matrix.zero_apply] at h
  · obtain ⟨α, β, hgcd, hdet1⟩ := hdet
    refine ⟨α, β, hgcd, fun t => ?_⟩
    rw [piU_det]
    exact hdet1 t


theorem diag_mul_apply {L V : Matrix (Fin 32) (Fin 32) ℂ}
    (hL : ∀ x y : Fin 32, x ≠ y → L x y = 0) (x y : Fin 32) :
    (L * V) x y = L x x * V x y := by
  rw [Matrix.mul_apply, Finset.sum_eq_single x]
  · intro k _ hk
    rw [hL x k (Ne.symm hk), zero_mul]
  · intro hcon; exact absurd (Finset.mem_univ x) hcon

theorem liftedProd_piU (α β : ℤ) (t : ℝ) :
    liftedProd piU α β t = conjU * liftedProd pi1 α β t * conjUᵀ := by
  unfold liftedProd piU
  rw [piOp_conj, conj_mul]

theorem mateSeat_two : mateSeat ⟨2, by norm_num⟩ = ⟨28, by norm_num⟩ := rfl

theorem mateSeat_twenty_eight : mateSeat ⟨28, by norm_num⟩ = ⟨2, by norm_num⟩ := rfl

theorem pi1_lifted_two (t : ℝ) :
    liftedProd pi1 3 (-1) t ⟨2, by norm_num⟩ ⟨2, by norm_num⟩
      = Complex.exp (((1 : ℤ) : ℂ) * ((t : ℂ) * Complex.I)) := by
  have hK : (pi1AVal (⟨2, by norm_num⟩ : Fin 32).val * 3
      + pi1BVal (⟨2, by norm_num⟩ : Fin 32).val * (-1))
      + (pi1AVal (partner ⟨2, by norm_num⟩).val * 3
        + pi1BVal (partner ⟨2, by norm_num⟩).val * (-1)) = 1 := by decide
  rw [pi1_liftedProd_entry, hK]

theorem pi1_lifted_twenty_eight (t : ℝ) :
    liftedProd pi1 3 (-1) t ⟨28, by norm_num⟩ ⟨28, by norm_num⟩
      = Complex.exp (((4 : ℤ) : ℂ) * ((t : ℂ) * Complex.I)) := by
  have hK : (pi1AVal (⟨28, by norm_num⟩ : Fin 32).val * 3
      + pi1BVal (⟨28, by norm_num⟩ : Fin 32).val * (-1))
      + (pi1AVal (partner ⟨28, by norm_num⟩).val * 3
        + pi1BVal (partner ⟨28, by norm_num⟩).val * (-1)) = 4 := by decide
  rw [pi1_liftedProd_entry, hK]

theorem liftedProd_piU_entry_form (t : ℝ) :
    liftedProd piU 3 (-1) t ⟨2, by norm_num⟩ ⟨28, by norm_num⟩
      = ((12 / 25 : ℝ) : ℂ)
        * (Complex.exp (((4 : ℤ) : ℂ) * ((t : ℂ) * Complex.I))
          - Complex.exp (((1 : ℤ) : ℂ) * ((t : ℂ) * Complex.I))) := by
  rw [liftedProd_piU, Matrix.mul_assoc, conjU_mul_apply, mateSeat_two]
  have hdiag : ∀ x y : Fin 32, x ≠ y →
      liftedProd pi1 3 (-1) t x y = 0 :=
    fun x y h => pi1_liftedProd_diag t x y h
  rw [diag_mul_apply hdiag, diag_mul_apply hdiag, pi1_lifted_two,
    pi1_lifted_twenty_eight]
  have e1 : conjUᵀ ⟨2, by norm_num⟩ ⟨28, by norm_num⟩ = (-(4 / 5 : ℝ) : ℂ) := by
    rw [Matrix.transpose_apply]
    show conjU ⟨28, by norm_num⟩ ⟨2, by norm_num⟩ = _
    rw [← mateSeat_twenty_eight]
    exact conjU_apply_mate _ (by decide)
  have e2 : conjUᵀ ⟨28, by norm_num⟩ ⟨28, by norm_num⟩ = ((3 / 5 : ℝ) : ℂ) :=
    Matrix.transpose_apply _ _ _ ▸ conjU_apply_diag _
  have e3 : diagC ⟨2, by norm_num⟩ = ((3 / 5 : ℝ) : ℂ) := rfl
  have e4 : offC ⟨2, by norm_num⟩ = ((4 / 5 : ℝ) : ℂ) := rfl
  rw [e1, e2, e3, e4]
  push_cast
  ring

theorem exp_one_pi_div_two :
    Complex.exp (((1 : ℤ) : ℂ) * (((Real.pi / 2 : ℝ) : ℂ) * Complex.I))
      = Complex.I := by
  have h : ((1 : ℤ) : ℂ) * (((Real.pi / 2 : ℝ) : ℂ) * Complex.I)
      = ((Real.pi / 2 : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [h, Complex.exp_mul_I]
  simp [Complex.ofReal_cos, Complex.ofReal_sin, Real.cos_pi_div_two,
    Real.sin_pi_div_two]

theorem exp_four_pi_div_two :
    Complex.exp (((4 : ℤ) : ℂ) * (((Real.pi / 2 : ℝ) : ℂ) * Complex.I)) = 1 := by
  have h : ((4 : ℤ) : ℂ) * (((Real.pi / 2 : ℝ) : ℂ) * Complex.I)
      = 2 * (Real.pi : ℂ) * Complex.I := by push_cast; ring
  rw [h, Complex.exp_two_pi_mul_I]

theorem liftedProd_piU_entry_pi_div_two :
    liftedProd piU 3 (-1) (Real.pi / 2) ⟨2, by norm_num⟩ ⟨28, by norm_num⟩
      = ((12 / 25 : ℝ) : ℂ) * (1 - Complex.I) := by
  rw [liftedProd_piU_entry_form, exp_one_pi_div_two, exp_four_pi_div_two]

theorem liftedProd_piU_entry_ne_zero :
    liftedProd piU 3 (-1) (Real.pi / 2) ⟨2, by norm_num⟩ ⟨28, by norm_num⟩
      ≠ 0 := by
  rw [liftedProd_piU_entry_pi_div_two]
  apply mul_ne_zero
  · norm_num
  · intro h
    have him := congrArg Complex.im h
    simp at him

theorem u1ParamGen_neg (α β : ℤ) (t : ℝ) :
    u1ParamGen (-α) (-β) t = u1ParamGen α β (-t) := by
  simp only [u1ParamGen, SMAlgebra.mk.injEq]
  refine ⟨?_, trivial, ?_⟩
  · congr 1
    push_cast
    ring
  · congr 1
    congr 1
    push_cast
    ring

theorem liftedProd_piU_entry_neg_dir :
    liftedProd piU (-3) 1 (-(Real.pi / 2)) ⟨2, by norm_num⟩ ⟨28, by norm_num⟩
      = ((12 / 25 : ℝ) : ℂ) * (1 - Complex.I) := by
  have hgen : u1ParamGen (-3) 1 (-(Real.pi / 2))
      = u1ParamGen 3 (-1) (Real.pi / 2) := by
    have h := u1ParamGen_neg 3 (-1) (-(Real.pi / 2))
    simpa using h
  unfold liftedProd
  rw [hgen]
  exact liftedProd_piU_entry_pi_div_two

/-- DiagLift: the scoping's §1.1 statement (no in-tree def existed) -/
def DiagLift (π : AF → Matrix (Fin 32) (Fin 32) ℂ) : Prop :=
  ∃ α β : ℤ, Nat.gcd α.natAbs β.natAbs = 1
    ∧ (∀ t, (π (u1ParamGen α β t)).det = 1)
    ∧ (∀ t (s s' : Fin 32), s ≠ s'
        → liftedProd π α β t s s' = 0)

theorem gamma_two_twenty_eight :
    gammaF ⟨2, by norm_num⟩ ⟨2, by norm_num⟩ = 1
      ∧ gammaF ⟨28, by norm_num⟩ ⟨28, by norm_num⟩ = 1 :=
  ⟨by norm_num [gammaF], by norm_num [gammaF]⟩

theorem weights_two_twenty_eight :
    commonWeightVector ⟨2, by norm_num⟩ = 1
      ∧ commonWeightVector ⟨28, by norm_num⟩ = 4 := by
  decide

theorem k_cls_1a_fired : ∃ π, DialOneBase π
    ∧ ∀ α β : ℤ, Nat.gcd α.natAbs β.natAbs = 1
      → (∀ t, (π (u1ParamGen α β t)).det = 1)
      → ∃ (t : ℝ) (s s' : Fin 32), s ≠ s'
        ∧ gammaF s s = gammaF s' s'
        ∧ liftedProd π α β t s s' ≠ 0 := by
  refine ⟨piU, dialOneBase_piU, fun α β hgcd hdet => ?_⟩
  have hdet1 : ∀ t, (pi1 (u1ParamGen α β t)).det = 1 := by
    intro t
    rw [← piU_det]
    exact hdet t
  have hlin := det_one_pi1 hdet1
  have hne : (⟨2, by norm_num⟩ : Fin 32) ≠ ⟨28, by norm_num⟩ := by decide
  have hgamma : gammaF ⟨2, by norm_num⟩ ⟨2, by norm_num⟩
      = gammaF ⟨28, by norm_num⟩ ⟨28, by norm_num⟩ := by
    rw [gamma_two_twenty_eight.1, gamma_two_twenty_eight.2]
  rcases dir_of_det_shape_4312 hgcd hlin with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨Real.pi / 2, ⟨2, by norm_num⟩, ⟨28, by norm_num⟩, hne, hgamma,
      liftedProd_piU_entry_ne_zero⟩
  · refine ⟨-(Real.pi / 2), ⟨2, by norm_num⟩, ⟨28, by norm_num⟩, hne, hgamma,
      ?_⟩
    rw [liftedProd_piU_entry_neg_dir]
    exact mul_ne_zero (by norm_num) (by
      intro h
      have him := congrArg Complex.im h
      simp at him)

theorem not_forall_base_diagLift : ¬ ∀ π, DialOneBase π → DiagLift π := by
  intro h
  obtain ⟨α, β, hgcd, hdet, hdiag⟩ := h piU dialOneBase_piU
  have hdet1 : ∀ t, (pi1 (u1ParamGen α β t)).det = 1 := by
    intro t
    rw [← piU_det]
    exact hdet t
  have hlin := det_one_pi1 hdet1
  have hne : (⟨2, by norm_num⟩ : Fin 32) ≠ ⟨28, by norm_num⟩ := by decide
  rcases dir_of_det_shape_4312 hgcd hlin with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have h0 := hdiag (Real.pi / 2) ⟨2, by norm_num⟩ ⟨28, by norm_num⟩ hne
    rw [liftedProd_piU_entry_pi_div_two] at h0
    have hcontra : ((12 / 25 : ℝ) : ℂ) * (1 - Complex.I) ≠ 0 :=
      mul_ne_zero (by norm_num) (by
        intro hh
        have him := congrArg Complex.im hh
        simp at him)
    exact hcontra h0
  · have h0 := hdiag (-(Real.pi / 2)) ⟨2, by norm_num⟩ ⟨28, by norm_num⟩ hne
    rw [liftedProd_piU_entry_neg_dir] at h0
    have hcontra : ((12 / 25 : ℝ) : ℂ) * (1 - Complex.I) ≠ 0 :=
      mul_ne_zero (by norm_num) (by
        intro hh
        have him := congrArg Complex.im hh
        simp at him)
    exact hcontra h0

end ThetLogos.DialOneConjugationCounterexample
