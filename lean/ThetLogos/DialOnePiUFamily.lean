import Mathlib.Tactic
import ThetLogos.DialOneConjugationCounterexample
import ThetLogos.DialOneGammaFamilyChecks

open Matrix Complex
open ThetLogos.Track1RouteB
open ThetLogos.PreOptionARepresentation
open ThetLogos.HyperchargeForcing
open ThetLogos.DialOneSeatTiePin
open ThetLogos.DialOneGammaTracePin
open ThetLogos.DialOneGammaFamilyPin
open ThetLogos.DialOneGammaTraceChecks
open ThetLogos.DialOneGammaFamilyChecks
open ThetLogos.DialOneConjugationCounterexample

/-!
# ThetLogos.DialOnePiUFamily — D1-PIU-STR, CORRECTED: `piU` IS a member of the strengthened family

Governing text: the Q1 menu scoping
(`~/workspace/your_files/q1-sep-audit-reg-scope-2026-11-06.md`,
menu item D1-PIU-STR), fired by Jeff 2026-11-06, resumed
2026-11-07, and the correction record appended to that paper
2026-11-07 ~19:40 EST, which is the operative verdict for
this rebuild (Jeff's rebuild word: "Build the corrected
brick", 2026-11-07 20:04 EST).
**NO CLAIM. Dial 1 = 0 on every outcome; all dials 0/4.**

## The question, as priced

K-CLS-1a fired in BASE form (`DialOneConjugationCounterexample.
not_forall_base_diagLift`): the conjugate representation
`piU a = conjU * pi1 a * conjUᵀ` satisfies `DialOneBase` while
its lifted product is non-diagonal at the seat pair `(2, 28)`.
This brick decides `piU` against every clause of
`DialOneStrengthenedFam` (base ∧ C3 ∧ GammaFamily) — the
family definition and every clause predicate EXACTLY as
pinned in `DialOneGammaFamilyPin` / `DialOneGammaTracePin`,
untouched — by direct trace computation, no inheritance.

## The draft's verdict was FALSE — correction at full rank

The never-landed draft of this module claimed
`piU ∉ DialOneStrengthenedFam`, decided by a colour-0 trace
of `(336/25) • i`. The resume lane (2026-11-07) disproved
that computation by two independent mechanical routes (the
kernel's `decide` on the ℤ shadows, and an exact recomputation
from the landed tables): the draft's pulled colour table is
wrong at 8 of the 32 seats, its "enlarged" e_R indicator
`{9, 25, 13, 21}` is a fiction (seats 9 and 25 are mate-fixed
inside `conjU`'s support: the conjugated e_R projection is
`eRProj` itself), and with the true tables every clause of
the family HOLDS at `piU`. This module is the corrected
brick: it proves the membership.

## The method

`conjU` is an involution up to transpose (`conjU * conjUᵀ = 1`),
so every family functional of `piU` is the same functional of
`π₁` conjugated on the projection side
(`trace_gammaF_proj_piU`). The conjugated projections:

* `γ_F` commutes with `conjU` (landed: `conjU_gamma_comm`):
  **C3 transports** (`c3_piU`).
* `lepProj`'s indicator is `mateSeat`-invariant, so `lepProj`
  commutes with `conjU`: **C3lep transports** (`c3lep_piU`).
* The e_R support `{9, 25}` is a mate pair on which `conjU`
  is the identity (`diagC = 1`, `offC = 0` at both seats), so
  the conjugated γ-weighted e_R projection is `γ_F * eRProj`
  itself, seat by seat (`eR_pull_diag`, `eR_pull_off`):
  **FeR transports** (`feR_piU`).
* The colour projections do NOT transport as matrices: the
  conjugated colour projections carry mate-pair entries
  `±12/25` (colours 0 and 1; colour 2 has none). But the
  trace never sees them: `π₁ (u1Gen α β)` is diagonal
  (landed: `pi1_u1Gen_diagonal`), so only the conjugated
  projections' DIAGONALS enter, and the diagonal is the
  pulled weight `9/25` at each colour's own mixed seats,
  `16/25` at the mate-pulled seats, computed here over the
  ℤ shadow `colWZ` at ×25 (`pulled_col_diag`). With the true
  pulled weights, the γ-weighted A- and B-shadow sums vanish
  for all three colours (`colWZ_sum_A`, `colWZ_sum_B`, by
  `decide`): **every C3col clause holds at `piU`**
  (`c3col_piU`).

## The verdict

**`piU ∈ DialOneStrengthenedFam`** (`strengthened_piU`):
base holds (landed `dialOneBase_piU`), C3 holds, C3lep
holds, every colour clause holds, FeR holds.

## Kill register, decided on this face

* **K-CLS-1a-STR — FIRES, by this proof.** Its firing
  condition was `piU ∈ DialOneStrengthenedFam`: the
  strengthened family does NOT exclude the K-CLS-1a witness.
  Strengthened-set extraction (`DialOneStrengthenedFam π →
  DiagLift π` for arbitrary `π`) therefore dies by this
  witness, on top of the base-form kill.
* **K-PIU-SEP — DOES NOT FIRE.** Its firing condition was
  that an excluding clause exists and fails the scoping's
  §2 honesty gate. There is no excluding clause at all; the
  separation premise collapses.

**Fences.** This brick proves a pointwise membership, not a
forcing theorem. It moves no dial: Dial 1 = 0, all dials
0/4. NO CLAIM.
-/

namespace ThetLogos.DialOnePiUFamily

/-- Conjugation by `conjU` moves past a product under the
trace: `trace (M * piU-generator form) = trace ((conjUᵀ * M *
conjU) * X)` whenever the middle factor is `conjU * X *
conjUᵀ`. Pure trace cyclicity + `conjUᵀ * conjU = 1`. -/
theorem trace_conjU_sandwich (M X : Matrix (Fin 32) (Fin 32) ℂ) :
    Matrix.trace (M * (conjU * X * conjUᵀ))
      = Matrix.trace ((conjUᵀ * M * conjU) * X) := by
  have e1 : M * (conjU * X * conjUᵀ) = (M * conjU * X) * conjUᵀ := by
    simp only [Matrix.mul_assoc]
  have e2 : (conjUᵀ * M * conjU) * X = conjUᵀ * (M * conjU * X) := by
    simp only [Matrix.mul_assoc]
  rw [e1, Matrix.trace_mul_comm (M * conjU * X) conjUᵀ, e2]

/-- The trace identity in the exact shape the family clauses
need: a γ_F-weighted projection trace of `piU` at the
generator is the conjugated-projection trace of `π₁`. -/
theorem trace_gammaF_proj_piU (P : Matrix (Fin 32) (Fin 32) ℂ)
    (α β : ℤ) :
    Matrix.trace (gammaF * P * piU (u1Gen α β))
      = Matrix.trace ((conjUᵀ * (gammaF * P) * conjU)
          * pi1 (u1Gen α β)) := by
  have h : gammaF * P * piU (u1Gen α β)
      = (gammaF * P) * (conjU * pi1 (u1Gen α β) * conjUᵀ) := by
    simp only [piU, Matrix.mul_assoc]
  rw [h, trace_conjU_sandwich]

/-! ## The transpose expansion (the draft's missing helper) -/

/-- **The transpose expansion**: entrywise product rule for
`conjUᵀ * M`. The draft misapplied `conjU_mul_apply` (a rule
about `conjU * M`) to `conjUᵀ` products throughout; the
transpose rule is proved here, once, from `mul_conjU_apply`
by transposing. Note the off-diagonal coefficient is
`offC (mateSeat i)`, the transpose's own table. -/
theorem conjUT_mul_apply (M : Matrix (Fin 32) (Fin 32) ℂ)
    (i j : Fin 32) :
    (conjUᵀ * M) i j
      = diagC i * M i j + offC (mateSeat i) * M (mateSeat i) j := by
  have h : (conjUᵀ * M) i j = (Mᵀ * conjU) j i := by
    have e : (Mᵀ * conjU)ᵀ = conjUᵀ * M := by
      rw [Matrix.transpose_mul, Matrix.transpose_transpose]
    rw [← e]
    rfl
  rw [h, mul_conjU_apply]
  simp only [Matrix.transpose_apply]
  ring

/-! ## The conjugated projections, entrywise -/

/-- `conjU` is diagonal-or-mate entrywise, so any conjugate
`conjUᵀ * D * conjU` of a DIAGONAL matrix `D` has diagonal
entry the `diagC²`/`offC²` mixture of `D`'s diagonal at the
seat and its mate. -/
theorem conjT_diag_conjU_diag (d : Fin 32 → ℂ) (i : Fin 32) :
    (conjUᵀ * Matrix.diagonal d * conjU) i i
      = diagC i * diagC i * d i
        + offC (mateSeat i) * offC (mateSeat i) * d (mateSeat i) := by
  rw [Matrix.mul_assoc, conjUT_mul_apply, mul_conjU_apply,
    mul_conjU_apply]
  by_cases hm : mateSeat i = i
  · have hdc := mateSeat_eq_self_diagC i hm
    rw [hm, hdc.1, hdc.2]
    simp only [Matrix.diagonal_apply_eq]
    ring
  · rw [Matrix.diagonal_apply_ne _
      (fun hh : i = mateSeat i => hm hh.symm),
      Matrix.diagonal_apply_ne _ hm]
    simp only [Matrix.diagonal_apply_eq]
    ring

/-- The off-diagonal entries of a conjugated diagonal matrix
at a NON-FIXED mate pair `(i, mateSeat i)`: the cross
mixture. (At a mate-fixed seat the pair entry is the
diagonal entry, so the non-fixed hypothesis is part of the
true statement; the draft stated it without, which is false
at fixed seats.) -/
theorem conjT_diag_conjU_off (d : Fin 32 → ℂ) (i : Fin 32)
    (hm : mateSeat i ≠ i) :
    (conjUᵀ * Matrix.diagonal d * conjU) i (mateSeat i)
      = diagC i * offC i * d i
        + offC (mateSeat i) * diagC (mateSeat i)
          * d (mateSeat i) := by
  rw [Matrix.mul_assoc, conjUT_mul_apply, mul_conjU_apply,
    mul_conjU_apply, mateSeat_involutive,
    Matrix.diagonal_apply_ne _
      (fun hh : i = mateSeat i => hm hh.symm),
    Matrix.diagonal_apply_ne _ hm]
  simp only [Matrix.diagonal_apply_eq]
  ring

/-- Every other entry of a conjugated diagonal matrix
vanishes: the conjugate of a diagonal matrix by `conjU` is
supported on the diagonal and the mate pairs. -/
theorem conjT_diag_conjU_ne (d : Fin 32 → ℂ) (i j : Fin 32)
    (h1 : j ≠ i) (h2 : j ≠ mateSeat i) :
    (conjUᵀ * Matrix.diagonal d * conjU) i j = 0 := by
  have e1 : (Matrix.diagonal d) i (mateSeat j) = 0 := by
    refine Matrix.diagonal_apply_ne _ (fun hh => h2 ?_)
    have h3 : mateSeat i = mateSeat (mateSeat j) :=
      congrArg mateSeat hh
    rw [mateSeat_involutive] at h3
    exact h3.symm
  have e2 : (Matrix.diagonal d) (mateSeat i) (mateSeat j) = 0 := by
    refine Matrix.diagonal_apply_ne _ (fun hh => h1 ?_)
    exact (mateSeat_injective hh).symm
  rw [Matrix.mul_assoc, conjUT_mul_apply, mul_conjU_apply,
    mul_conjU_apply,
    Matrix.diagonal_apply_ne _ (fun hh : i = j => h1 hh.symm),
    e1, e2,
    Matrix.diagonal_apply_ne _
      (fun hh : mateSeat i = j => h2 hh.symm)]
  ring

/-! ## Transport: γ_F and the lepton projection -/

/-- Any diagonal matrix whose diagonal function is
`mateSeat`-invariant commutes with `conjU`: entrywise, both
products are the same diagonal-or-mate matrix. -/
theorem diag_comm_conjU {d : Fin 32 → ℂ}
    (hd : ∀ i, d (mateSeat i) = d i) :
    Matrix.diagonal d * conjU = conjU * Matrix.diagonal d := by
  ext i j
  rw [mul_conjU_apply, conjU_mul_apply]
  by_cases h1 : j = i
  · rw [h1]
    by_cases hm : mateSeat i = i
    · have hdc := mateSeat_eq_self_diagC i hm
      rw [hm, hdc.1, hdc.2]
      ring
    · rw [Matrix.diagonal_apply_ne _
        (fun hh : i = mateSeat i => hm hh.symm),
        Matrix.diagonal_apply_ne _ hm]
      ring
  · by_cases h2 : j = mateSeat i
    · subst h2
      by_cases hm : mateSeat i = i
      · exact absurd hm h1
      · rw [mateSeat_involutive,
          Matrix.diagonal_apply_ne _
            (fun hh : i = mateSeat i => hm hh.symm)]
        simp only [Matrix.diagonal_apply_eq]
        rw [hd i]
        ring
    · have e1 : (Matrix.diagonal d) i (mateSeat j) = 0 := by
        refine Matrix.diagonal_apply_ne _ (fun hh => h2 ?_)
        have h3 : mateSeat i = mateSeat (mateSeat j) :=
          congrArg mateSeat hh
        rw [mateSeat_involutive] at h3
        exact h3.symm
      have e2 : (Matrix.diagonal d) (mateSeat i) j = 0 :=
        Matrix.diagonal_apply_ne _
          (fun hh : mateSeat i = j => h2 hh.symm)
      rw [Matrix.diagonal_apply_ne _
        (fun hh : i = j => h1 hh.symm), e1, e2]
      ring

/-- The projections and `gammaF` are diagonal matrices with
the landed indicator diagonals. -/
theorem lepProj_eq_diag : lepProj
    = Matrix.diagonal (fun i => (lepInd i.val : ℂ)) := by
  unfold lepProj seatProj
  congr 1
  funext i
  obtain ⟨v, hv⟩ := i
  interval_cases v <;> simp [lepInd, partner]

theorem eRProj_eq_diag : eRProj
    = Matrix.diagonal (fun i => (eRInd i.val : ℂ)) := by
  unfold eRProj seatProj
  congr 1
  funext i
  obtain ⟨v, hv⟩ := i
  interval_cases v <;> simp [eRInd, partner]

theorem colProj_eq_diag (c : Fin 3) : colProj c
    = Matrix.diagonal (fun i => (colInd c i.val : ℂ)) := by
  unfold colProj seatProj
  congr 1
  funext i
  fin_cases c <;>
    (obtain ⟨v, hv⟩ := i <;> interval_cases v <;>
      simp [colInd, partner])

theorem gammaF_eq_diag : gammaF
    = Matrix.diagonal (fun i => (gammaVal i.val : ℂ)) := by
  ext a b
  by_cases hab : a = b
  · rw [hab, gammaF_diag_eq]; simp [Matrix.diagonal]
  · rw [gammaF_apply_ne hab, Matrix.diagonal_apply_ne _ hab]

/-- `γ_F` times an indicator-diagonal projection, in
diagonal form. -/
theorem gammaF_mul_proj (P : Matrix (Fin 32) (Fin 32) ℂ)
    (ind : ℕ → ℤ)
    (hP : P = Matrix.diagonal (fun i => (ind i.val : ℂ))) :
    gammaF * P
      = Matrix.diagonal
          (fun i => (gammaVal i.val : ℂ) * (ind i.val : ℂ)) := by
  rw [hP, gammaF_eq_diag, Matrix.diagonal_mul_diagonal]

/-- `lepInd` is mate-invariant (checked seat by seat). -/
theorem lepInd_mate (i : Fin 32) :
    lepInd (mateSeat i).val = lepInd i.val := by
  fin_cases i <;> rfl

/-- `gammaVal` is mate-invariant (checked seat by seat). -/
theorem gammaVal_mate (i : Fin 32) :
    gammaVal (mateSeat i).val = gammaVal i.val := by
  fin_cases i <;> rfl

/-- The conjugated γ_F-weighted lepton projection is the
projection itself: both factors commute with `conjU`, so the
conjugation collapses by `conjUᵀ * conjU = 1`. -/
theorem conjT_gammaF_lepProj : conjUᵀ * (gammaF * lepProj) * conjU
    = gammaF * lepProj := by
  have hL : lepProj * conjU = conjU * lepProj := by
    rw [lepProj_eq_diag]
    exact diag_comm_conjU (d := fun i => (lepInd i.val : ℂ))
      (fun i => by rw [lepInd_mate])
  have step1 : conjUᵀ * (gammaF * lepProj) * conjU
      = conjUᵀ * (gammaF * (lepProj * conjU)) := by
    simp only [Matrix.mul_assoc]
  have step2 : gammaF * (lepProj * conjU) = gammaF * (conjU * lepProj) := by
    rw [hL]
  have step3 : gammaF * (conjU * lepProj) = (gammaF * conjU) * lepProj := by
    simp only [Matrix.mul_assoc]
  have step4 : (gammaF * conjU) * lepProj = (conjU * gammaF) * lepProj := by
    rw [conjU_gamma_comm]
  have step5 : (conjU * gammaF) * lepProj = conjU * (gammaF * lepProj) := by
    simp only [Matrix.mul_assoc]
  rw [step1, step2, step3, step4, step5,
    ← Matrix.mul_assoc conjUᵀ conjU (gammaF * lepProj),
    conjU_transpose_mul, Matrix.one_mul]

/-- The conjugated bare γ_F is γ_F itself. -/
theorem conjT_gammaF : conjUᵀ * gammaF * conjU = gammaF := by
  have step1 : conjUᵀ * gammaF * conjU
      = conjUᵀ * (gammaF * conjU) := by simp only [Matrix.mul_assoc]
  have step2 : gammaF * conjU = conjU * gammaF := conjU_gamma_comm
  rw [step1, step2, ← Matrix.mul_assoc conjUᵀ conjU gammaF,
    conjU_transpose_mul, Matrix.one_mul]

/-- **C3 `piU` HOLDS** — the plain γ-trace clause transports
through the conjugation because γ_F commutes with `conjU`. -/
theorem c3_piU : C3 piU := by
  intro α β
  have h := trace_gammaF_proj_piU 1 α β
  simp only [Matrix.mul_one] at h
  rw [h, conjT_gammaF]
  exact DialOneGammaTraceChecks.trace_gammaF_pi1_u1Gen α β

/-- **C3lep `piU` HOLDS** — the lepton clause transports:
its conjugated projection is itself. -/
theorem c3lep_piU : C3lep piU := by
  intro α β
  rw [trace_gammaF_proj_piU lepProj α β, conjT_gammaF_lepProj]
  exact (c3lep_pi1) α β

/-! ## The ℤ shadows of `conjU`'s tables, at ×5 -/

/-- The integer shadow of `diagC`: `diagC i = diagCZ i / 5`
in `ℂ` (3 at the eight mixed seats, 5 elsewhere). -/
def diagCZ (i : Fin 32) : ℤ :=
  if i.val = 2 ∨ i.val = 4 ∨ i.val = 10 ∨ i.val = 12
      ∨ i.val = 18 ∨ i.val = 20 ∨ i.val = 26 ∨ i.val = 28
    then 3 else 5

/-- The integer shadow of `offC`: `offC i = offCZ i / 5` in
`ℂ` (+4 at `{2, 10, 18, 26}`, −4 at `{4, 12, 20, 28}`). -/
def offCZ (i : Fin 32) : ℤ :=
  if i.val = 2 ∨ i.val = 10 ∨ i.val = 18 ∨ i.val = 26
    then 4
  else if i.val = 4 ∨ i.val = 12 ∨ i.val = 20 ∨ i.val = 28
    then -4 else 0

theorem diagC_shadow (i : Fin 32) :
    diagC i = ((diagCZ i : ℤ) : ℂ) / 5 := by
  fin_cases i <;> simp [diagC, diagCZ]

theorem offC_shadow (i : Fin 32) :
    offC i = ((offCZ i : ℤ) : ℂ) / 5 := by
  fin_cases i <;> simp [offC, offCZ] <;> norm_num

/-! ## The e_R clause: the conjugated projection is itself -/

/-- The pulled γ-weighted e_R diagonal, seat by seat: the
`diagC²`/`offC²` mixture of `γ • eRInd` at a seat and its
mate is `γ • eRInd` itself — the support `{9, 25}` is a mate
pair at which `offC` vanishes and `diagC = 1`, and every
other seat has `eRInd = 0` at both itself and its mate. -/
theorem eR_pull_diag (i : Fin 32) :
    diagC i * diagC i
        * ((gammaVal i.val : ℂ) * (eRInd i.val : ℂ))
      + offC (mateSeat i) * offC (mateSeat i)
        * ((gammaVal (mateSeat i).val : ℂ)
          * (eRInd (mateSeat i).val : ℂ))
      = (gammaVal i.val : ℂ) * (eRInd i.val : ℂ) := by
  fin_cases i <;> simp [diagC, offC, mateSeat, gammaVal, eRInd]

/-- The γ-weighted e_R mate-pair entries vanish, seat by
seat: at the support seats `offC` is `0`, and elsewhere
`eRInd` vanishes at both members of the pair. -/
theorem eR_pull_off (i : Fin 32) :
    diagC i * offC i
        * ((gammaVal i.val : ℂ) * (eRInd i.val : ℂ))
      + offC (mateSeat i) * diagC (mateSeat i)
        * ((gammaVal (mateSeat i).val : ℂ)
          * (eRInd (mateSeat i).val : ℂ))
      = 0 := by
  fin_cases i <;> simp [diagC, offC, mateSeat, gammaVal, eRInd]

/-- The conjugated γ_F-weighted e_R projection, as a matrix:
it is `γ_F * eRProj` ITSELF. (The draft's "enlarged
indicator" `{9, 25, 13, 21}` never existed: the pull is the
identity, seat by seat.) -/
theorem conjT_gammaF_eRProj : conjUᵀ * (gammaF * eRProj) * conjU
    = gammaF * eRProj := by
  have hge : gammaF * eRProj
      = Matrix.diagonal
          (fun i => (gammaVal i.val : ℂ) * (eRInd i.val : ℂ)) :=
    gammaF_mul_proj _ _ eRProj_eq_diag
  rw [hge]
  ext a b
  by_cases h1 : b = a
  · rw [h1]
    rw [conjT_diag_conjU_diag, Matrix.diagonal_apply_eq]
    exact eR_pull_diag a
  · by_cases h2 : b = mateSeat a
    · subst h2
      rw [conjT_diag_conjU_off _ _ h1,
        Matrix.diagonal_apply_ne _
          (fun hh : a = mateSeat a => h1 hh.symm)]
      exact eR_pull_off a
    · rw [conjT_diag_conjU_ne _ a b h1 h2,
        Matrix.diagonal_apply_ne _
          (fun hh : a = b => h1 hh.symm)]

/-- **FeR `piU` HOLDS** — its conjugated projection is
itself, so the clause transports by identity. -/
theorem feR_piU : FeR piU := by
  intro α β
  rw [trace_gammaF_proj_piU eRProj α β, conjT_gammaF_eRProj]
  exact (feR_pi1) α β

/-! ## The colour clauses: the pulled weights, at ×25 -/

/-- The pulled colour weight, as an integer shadow at ×25:
`colWZ c i = 25 • (the conjugated colour-`c` projection's
diagonal at seat `i`)` — `diagCZ² • colInd` at the seat plus
`offCZ² • colInd` at its mate. With this definition the
diagonal identity below is the cast of the definition, and
the vanishing of the γ-weighted shadow sums is a `decide`. -/
def colWZ (c : Fin 3) (i : Fin 32) : ℤ :=
  diagCZ i * diagCZ i * colInd c i.val
    + offCZ (mateSeat i) * offCZ (mateSeat i)
      * colInd c (mateSeat i).val

/-- The conjugated colour projection's diagonal is the
pulled weight: the `diagC`/`offC` mixture of `colInd c` at a
seat and its mate is `colWZ c / 25` in `ℂ`. (For colour 0
this reads: `9/25` at the own mixed seats `{2, 10, 18, 26}`,
`16/25` at the mate-pulled seats `{4, 12, 20, 28}`, `1` at
the unmixed own seats, `0` elsewhere — the true table the
draft's `colW0` got wrong at exactly the eight mixed/mate
seats.) -/
theorem pulled_col_diag (c : Fin 3) (i : Fin 32) :
    diagC i * diagC i * (colInd c i.val : ℂ)
      + offC (mateSeat i) * offC (mateSeat i)
        * (colInd c (mateSeat i).val : ℂ)
      = ((colWZ c i : ℤ) : ℂ) / 25 := by
  rw [diagC_shadow i, offC_shadow (mateSeat i)]
  unfold colWZ
  push_cast
  ring

/-- The γ-weighted A-shadow sum of the pulled colour weights
vanishes, for every colour (ℤ shadow at ×25, `decide`). -/
theorem colWZ_sum_A (c : Fin 3) :
    ∑ i : Fin 32, gammaVal i.val * colWZ c i * pi1AVal i.val
      = 0 := by
  fin_cases c <;> decide

/-- The γ-weighted B-shadow sum of the pulled colour weights
vanishes, for every colour (ℤ shadow at ×25, `decide`).
This is the sum the draft computed as `336/25 ≠ 0` from its
false table; with the true pulled weights it is `0`. -/
theorem colWZ_sum_B (c : Fin 3) :
    ∑ i : Fin 32, gammaVal i.val * colWZ c i * pi1BVal i.val
      = 0 := by
  fin_cases c <;> decide

/-- The trace of a matrix against a diagonal matrix reads
only the diagonal. -/
theorem trace_mul_diagonal (M : Matrix (Fin 32) (Fin 32) ℂ)
    (d : Fin 32 → ℂ) :
    Matrix.trace (M * Matrix.diagonal d)
      = ∑ i : Fin 32, M i i * d i := by
  unfold Matrix.trace Matrix.diag
  apply Finset.sum_congr rfl
  intro i _
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · rw [Matrix.diagonal_apply_eq]
  · intro k _ hk
    rw [Matrix.diagonal_apply_ne _ hk, mul_zero]
  · intro hcon; exact absurd (Finset.mem_univ i) hcon

/-- The diagonal of the conjugated γ_F-weighted colour
projection: `γ` times the pulled weight. (The full matrix
is NOT diagonal — its mate-pair entries are `±12/25` for
colours 0 and 1 — but `π₁` at the generator is diagonal, so
the trace below needs only this diagonal.) -/
theorem conjT_gammaF_colProj_diag (c : Fin 3) (i : Fin 32) :
    (conjUᵀ * (gammaF * colProj c) * conjU) i i
      = (gammaVal i.val : ℂ) * (((colWZ c i : ℤ) : ℂ) / 25) := by
  have hge : gammaF * colProj c
      = Matrix.diagonal
          (fun i => (gammaVal i.val : ℂ) * (colInd c i.val : ℂ)) :=
    gammaF_mul_proj _ _ (colProj_eq_diag c)
  rw [hge, conjT_diag_conjU_diag]
  have hg : (gammaVal (mateSeat i).val : ℂ)
      = (gammaVal i.val : ℂ) := by
    rw [gammaVal_mate]
  have e : diagC i * diagC i
        * ((gammaVal i.val : ℂ) * (colInd c i.val : ℂ))
      + offC (mateSeat i) * offC (mateSeat i)
        * ((gammaVal (mateSeat i).val : ℂ)
          * (colInd c (mateSeat i).val : ℂ))
      = (gammaVal i.val : ℂ)
        * (diagC i * diagC i * (colInd c i.val : ℂ)
          + offC (mateSeat i) * offC (mateSeat i)
            * (colInd c (mateSeat i).val : ℂ)) := by
    rw [hg]; ring
  rw [e, pulled_col_diag]

/-- **C3col `c` `piU` HOLDS**, for every colour — decided by
direct computation: the colour trace of `piU` is the pulled
γ-trace of `π₁`, and both pulled shadow sums vanish. -/
theorem c3col_piU (c : Fin 3) : C3col c piU := by
  intro α β
  rw [trace_gammaF_proj_piU (colProj c) α β,
    ThetLogos.DialOneShapeBIdentification.pi1_u1Gen_diagonal,
    trace_mul_diagonal]
  have hterm : ∀ i : Fin 32,
      (conjUᵀ * (gammaF * colProj c) * conjU) i i
          * (Complex.I
            * ((pi1AVal i.val * α + pi1BVal i.val * β : ℤ) : ℂ))
        = Complex.I / 25
          * ((gammaVal i.val * colWZ c i
              * (pi1AVal i.val * α + pi1BVal i.val * β) : ℤ) : ℂ) := by
    intro i
    rw [conjT_gammaF_colProj_diag]
    push_cast
    ring
  rw [Finset.sum_congr rfl (fun i _ => hterm i), ← Finset.mul_sum,
    ← Int.cast_sum]
  have hsum : ∑ i : Fin 32, gammaVal i.val * colWZ c i
        * (pi1AVal i.val * α + pi1BVal i.val * β) = 0 := by
    have h1 : ∀ i : Fin 32, gammaVal i.val * colWZ c i
          * (pi1AVal i.val * α + pi1BVal i.val * β)
        = (gammaVal i.val * colWZ c i * pi1AVal i.val) * α
          + (gammaVal i.val * colWZ c i * pi1BVal i.val) * β :=
      fun i => by ring
    rw [Finset.sum_congr rfl (fun i _ => h1 i),
      Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul,
      colWZ_sum_A c, colWZ_sum_B c]
    simp
  rw [hsum]
  simp

/-- **THE VERDICT — `piU ∈ DialOneStrengthenedFam`.** The
K-CLS-1a witness is a MEMBER of the strengthened family:
base holds (landed), C3 holds, C3lep holds, every colour
clause holds, FeR holds — each proved in this module or
cited from the landed checks. **K-CLS-1a-STR FIRES by this
proof** (the strengthened family does not exclude its
witness); **K-PIU-SEP does not fire** (there is no excluding
clause). Dial 1 = 0: a membership proof derives no measured
number. NO CLAIM. -/
theorem strengthened_piU : DialOneStrengthenedFam piU :=
  ⟨dialOneBase_piU, c3_piU, c3lep_piU, c3col_piU, feR_piU⟩

end ThetLogos.DialOnePiUFamily

#print axioms ThetLogos.DialOnePiUFamily.strengthened_piU
