import Mathlib.Tactic
import ThetLogos.DialOneGammaFamilyPin
import ThetLogos.DialOneGammaTraceChecks
import ThetLogos.DialOneDoubleFlipChecks

open Matrix Complex
open ThetLogos.Track1RouteB
open ThetLogos.PreOptionARepresentation
open ThetLogos.HyperchargeForcing
open ThetLogos.DialOneSeatTiePin
open ThetLogos.DialOneGammaTracePin
open ThetLogos.DialOneDoubleFlipPin
open ThetLogos.DialOneGammaTraceChecks
open ThetLogos.DialOneGammaFamilyPin

/-!
# D1-CMP-FAM — the clean-family gauntlet and the quark-swap tests

Builder checks for `ThetLogos.DialOneGammaFamilyPin` (D1-CMP-FAM,
stage 2 of the Dial-1 compensator lane). **NO CLAIM; Dial 1 = 0 on
every outcome.** Nothing in this module is a forcing theorem.

## Verdicts (all T1, machine-checked below)

* **Part 1(i) — `gammaFamily_pi1 : GammaFamilyPi1Check`.** π₁
  satisfies the whole clean family: the γ-weighted A/B sub-sums
  over each pinned seat set are **(0, 0)** per clause — `C3lep`
  over `{0,1,8,9,16,17,24,25}`, `C3col c` over
  `{2+2c,3+2c,10+2c,11+2c,18+2c,19+2c,26+2c,27+2c}`, `FeR` over
  `{9,25}` — discharged by ℤ-shadow `decide` over `Fin 32`.
  **K-CMP-F2 does not fire** (no clause is mis-posed).
* **Part 1(ii) — `piDouble_family : PiDoubleFamilyCheck`.**
  piDouble satisfies `C3lep` (the seat-8/seat-9 single
  contributions `+2α·i` and `−2α·i` cancel inside the lepton
  sector) and every `C3col c` (both singles vanish against the
  colour projections), but fails the family by `FeR` alone:
  `trace_feR_piDouble : Tr (γ_F · eRProj · piDouble (u1Gen α β))
  = −2·α·i`, witness `(α, β) = (1, 0)` giving `−2i ≠ 0`.
  **K-CMP-F3 does not fire** (the F_eR arithmetic stands).
* **Part 2 — the per-colour quark swaps.** `piSwap c` is π₁ with
  the conjugation toggles at colour `c`'s particle-side quark
  pair `(uSeat c, dSeat c) = (10 + 2c, 11 + 2c)` — the dossier
  pair table `{(10,11)}, {(12,13)}, {(14,15)}` — two
  `Matrix.single` terms on piDouble's pattern: at `u_R^c` π₁'s
  `a.u1` is toggled to `star a.u1`, at `d_R^c` π₁'s
  `star a.u1` is toggled to `a.u1`. For every colour `c`:
  - `GammaFamily (piSwap c)` **HOLDS** (`gammaFamily_piSwap`):
    a swap is invisible to every clean functional — against
    `colProj c` the two singles contribute `+2α·i` and `−2α·i`
    and cancel; against every other projection they vanish.
  - `DialOneBase (piSwap c)` **FAILS at the order-zero clause**
    (`not_base_piSwap`), for every colour. The toggle single at
    a quark-R seat does not commute with `ρ₁`, whose quark-R
    block is a colour matrix, not a scalar: with `a₀ = ⟨i, 0, 0⟩`
    and `b` carrying the colour single `single c' c 1`
    (`c' = c + 1 mod 3`), the `(u_R^c, u_R^{c'})` entry of
    `piSwap c a₀ * piOp (piSwap c b)` is `star i = −i` while the
    reversed product gives `+i`. This failure is the exclusion
    mechanism.
  - Non-proportionality, as pinned (the colour-0 slice
    `fermionIndex f 0`): **HOLDS for `c = 0`**
    (`nonprop_piSwap_zero`: lifted `u_R` weight swaps `4 ↦ −2`,
    `d_R` swaps `−2 ↦ 4`; at `t = π/2` resp. `t = π` the two
    seats force `exp (κπi) = −1` and `(exp (κπi))² = −1`,
    contradiction) and is **FALSE as pinned for `c = 1, 2`**
    (`exists_kappa_piSwap_of_ne`: the colour-0 slice is
    untouched by a colour-1/2 swap, so `κ = 1` satisfies the
    pinned equation exactly). The intended per-colour statement
    does hold at every colour: `swap_slice_nonprop` — read on
    colour `c`'s own `u_R^c`/`u_L^c` seats, no single `κ`
    fits. The pinned refutation for `c = 1, 2` is an artefact
    of the pin's colour-0-sliced conclusion shape, recorded
    here at full rank, not a failure of the swap's own sectors.
* **K-CMP-F1 does NOT fire** (`kCMP_F1_does_not_fire :
  ¬ QuarkSwapCheck piSwap`): no colour gives
  base ∧ family ∧ non-proportional.
* **Conclusion, at exactly its registered rank**
  (`toggle_exclusion`): π₁ lies in
  `DialOneStrengthenedFam` (base ∧ C3 ∧ clean family) while
  piFlip, piDouble, and every `piSwap c` lie outside it —
  **base + clean family excludes every named toggle
  compensator. This is a toggle-level exclusion, NOT a
  forcing theorem.** Non-toggle representations remain the
  unscoped base-set realizability classification question.
-/

namespace ThetLogos.DialOneGammaFamilyChecks

def lepInd (v : ℕ) : ℤ := if v ∈ [0, 1, 8, 9, 16, 17, 24, 25] then 1 else 0
def eRInd (v : ℕ) : ℤ := if v ∈ [9, 25] then 1 else 0
def colInd (c : Fin 3) (v : ℕ) : ℤ :=
  if v ∈ [2 + 2 * c.val, 3 + 2 * c.val, 10 + 2 * c.val, 11 + 2 * c.val,
    18 + 2 * c.val, 19 + 2 * c.val, 26 + 2 * c.val, 27 + 2 * c.val] then 1 else 0

theorem lepProj_diag (i : Fin 32) : lepProj i i = (lepInd i.val : ℂ) := by
  obtain ⟨v, hv⟩ := i
  interval_cases v <;> simp [lepProj, seatProj, lepInd, partner]

theorem eRProj_diag (i : Fin 32) : eRProj i i = (eRInd i.val : ℂ) := by
  obtain ⟨v, hv⟩ := i
  interval_cases v <;> simp [eRProj, seatProj, eRInd, partner]

theorem colProj_diag (c : Fin 3) (i : Fin 32) :
    colProj c i i = (colInd c i.val : ℂ) := by
  fin_cases c <;> obtain ⟨v, hv⟩ := i <;> interval_cases v <;>
    simp [colProj, seatProj, colInd, partner]

theorem lepProj_diag_mul (M : Matrix (Fin 32) (Fin 32) ℂ) (i : Fin 32) :
    (lepProj * M) i i = lepProj i i * M i i := by
  simp only [lepProj, seatProj, Matrix.diagonal_mul, Matrix.diagonal_apply_eq]

theorem eRProj_diag_mul (M : Matrix (Fin 32) (Fin 32) ℂ) (i : Fin 32) :
    (eRProj * M) i i = eRProj i i * M i i := by
  simp only [eRProj, seatProj, Matrix.diagonal_mul, Matrix.diagonal_apply_eq]

theorem colProj_diag_mul (c : Fin 3) (M : Matrix (Fin 32) (Fin 32) ℂ) (i : Fin 32) :
    (colProj c * M) i i = colProj c i i * M i i := by
  simp only [colProj, seatProj, Matrix.diagonal_mul, Matrix.diagonal_apply_eq]

theorem trace_gammaF_proj_pi1 (P : Matrix (Fin 32) (Fin 32) ℂ) (ind : ℕ → ℤ)
    (hdiag : ∀ (M : Matrix (Fin 32) (Fin 32) ℂ) (i : Fin 32),
      (P * M) i i = P i i * M i i)
    (hP : ∀ i, P i i = (ind i.val : ℂ)) (α β : ℤ) :
    Matrix.trace (gammaF * P * pi1 (u1Gen α β))
      = ((∑ i : Fin 32, gammaVal i.val * ind i.val * pi1AVal i.val : ℤ) : ℂ)
          * ((α : ℂ) * Complex.I)
        + ((∑ i : Fin 32, gammaVal i.val * ind i.val * pi1BVal i.val : ℤ) : ℂ)
          * ((β : ℂ) * Complex.I) := by
  rw [Matrix.mul_assoc, trace_gammaF_mul]
  trans ∑ i : Fin 32,
    (((gammaVal i.val * ind i.val * pi1AVal i.val : ℤ) : ℂ) * ((α : ℂ) * Complex.I)
      + ((gammaVal i.val * ind i.val * pi1BVal i.val : ℤ) : ℂ)
        * ((β : ℂ) * Complex.I))
  · apply Finset.sum_congr rfl
    intro i _
    rw [hdiag, gammaF_diag_eq, hP, pi1_diag_u1Gen]
    push_cast
    ring
  · rw [Finset.sum_add_distrib, Int.cast_sum, Int.cast_sum,
      Finset.sum_mul, Finset.sum_mul]

theorem trace_gammaF_proj_single (P : Matrix (Fin 32) (Fin 32) ℂ)
    (s : Fin 32) (x : ℂ) :
    Matrix.trace (gammaF * P * Matrix.single s s x)
      = gammaF s s * P s s * x := by
  have hPs : (P * Matrix.single s s x) s s = P s s * x := by
    rw [Matrix.mul_apply, Finset.sum_eq_single s]
    · rw [Matrix.single_apply_same]
    · intro k _ hk
      rw [Matrix.single_apply, if_neg (fun h => hk h.1.symm), mul_zero]
    · intro h; exact absurd (Finset.mem_univ s) h
  rw [Matrix.mul_assoc, trace_gammaF_mul, Finset.sum_eq_single s]
  · rw [hPs]
    ring
  · intro i _ hi
    have hz : (P * Matrix.single s s x) i i = 0 := by
      rw [Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro k _
      rw [Matrix.single_apply, if_neg (fun h => hi h.2.symm), mul_zero]
    rw [hz, mul_zero]
  · intro h; exact absurd (Finset.mem_univ s) h

theorem hstar (α : ℤ) :
    star ((α : ℂ) * Complex.I) = -((α : ℂ) * Complex.I) := by
  rw [star_mul]
  have h1 : star ((α : ℂ)) = (α : ℂ) := by simp
  have h2 : star (Complex.I) = -Complex.I := by simp
  rw [h1, h2]
  ring

theorem gammaF_s8 : gammaF s8 s8 = -1 := by
  rw [gammaF_diag_eq]; norm_num [gammaVal]

theorem gammaF_s9 : gammaF s9 s9 = -1 := by
  rw [gammaF_diag_eq]; norm_num [gammaVal]

theorem trace_gammaF_proj_piDouble (P : Matrix (Fin 32) (Fin 32) ℂ)
    (ind : ℕ → ℤ)
    (hdiag : ∀ (M : Matrix (Fin 32) (Fin 32) ℂ) (i : Fin 32),
      (P * M) i i = P i i * M i i)
    (hP : ∀ i, P i i = (ind i.val : ℂ)) (α β : ℤ) :
    Matrix.trace (gammaF * P * piDouble (u1Gen α β))
      = ((∑ i : Fin 32, gammaVal i.val * ind i.val * pi1AVal i.val : ℤ) : ℂ)
          * ((α : ℂ) * Complex.I)
        + ((∑ i : Fin 32, gammaVal i.val * ind i.val * pi1BVal i.val : ℤ) : ℂ)
          * ((β : ℂ) * Complex.I)
        + gammaF s8 s8 * P s8 s8
          * (star ((α : ℂ) * Complex.I) - (α : ℂ) * Complex.I)
        + gammaF s9 s9 * P s9 s9
          * ((α : ℂ) * Complex.I - star ((α : ℂ) * Complex.I)) := by
  have hdec : piDouble (u1Gen α β)
      = pi1 (u1Gen α β)
        + Matrix.single s8 s8 (star ((α : ℂ) * Complex.I) - (α : ℂ) * Complex.I)
        + Matrix.single s9 s9 ((α : ℂ) * Complex.I
            - star ((α : ℂ) * Complex.I)) := rfl
  rw [hdec, Matrix.mul_add, Matrix.mul_add, Matrix.trace_add, Matrix.trace_add,
    trace_gammaF_proj_pi1 P ind hdiag hP, trace_gammaF_proj_single,
    trace_gammaF_proj_single]

theorem c3lep_pi1 : C3lep pi1 := by
  intro α β
  rw [trace_gammaF_proj_pi1 lepProj lepInd lepProj_diag_mul lepProj_diag]
  have hA : (∑ i : Fin 32, gammaVal i.val * lepInd i.val * pi1AVal i.val) = 0 := by
    decide
  have hB : (∑ i : Fin 32, gammaVal i.val * lepInd i.val * pi1BVal i.val) = 0 := by
    decide
  rw [hA, hB]
  simp

theorem c3col_pi1 : ∀ c, C3col c pi1 := by
  intro c α β
  rw [trace_gammaF_proj_pi1 (colProj c) (colInd c) (colProj_diag_mul c)
    (colProj_diag c)]
  have hA : (∑ i : Fin 32, gammaVal i.val * colInd c i.val * pi1AVal i.val)
      = 0 := by
    fin_cases c <;> decide
  have hB : (∑ i : Fin 32, gammaVal i.val * colInd c i.val * pi1BVal i.val)
      = 0 := by
    fin_cases c <;> decide
  rw [hA, hB]
  simp

theorem feR_pi1 : FeR pi1 := by
  intro α β
  rw [trace_gammaF_proj_pi1 eRProj eRInd eRProj_diag_mul eRProj_diag]
  have hA : (∑ i : Fin 32, gammaVal i.val * eRInd i.val * pi1AVal i.val) = 0 := by
    decide
  have hB : (∑ i : Fin 32, gammaVal i.val * eRInd i.val * pi1BVal i.val) = 0 := by
    decide
  rw [hA, hB]
  simp

theorem gammaFamily_pi1 : GammaFamilyPi1Check :=
  ⟨c3lep_pi1, c3col_pi1, feR_pi1⟩

theorem c3lep_piDouble : C3lep piDouble := by
  intro α β
  rw [trace_gammaF_proj_piDouble lepProj lepInd lepProj_diag_mul lepProj_diag]
  have hA : (∑ i : Fin 32, gammaVal i.val * lepInd i.val * pi1AVal i.val) = 0 := by
    decide
  have hB : (∑ i : Fin 32, gammaVal i.val * lepInd i.val * pi1BVal i.val) = 0 := by
    decide
  have p8 : lepProj s8 s8 = 1 := by
    have h := lepProj_diag s8
    simpa [lepInd] using h
  have p9 : lepProj s9 s9 = 1 := by
    have h := lepProj_diag s9
    simpa [lepInd] using h
  rw [hA, hB]
  simp only [Int.cast_zero, zero_mul, add_zero]
  rw [gammaF_s8, gammaF_s9, p8, p9, hstar α]
  ring

theorem colProj_s8 (c : Fin 3) : colProj c s8 s8 = 0 := by
  have h := colProj_diag c s8
  fin_cases c <;> simpa [colInd] using h

theorem colProj_s9 (c : Fin 3) : colProj c s9 s9 = 0 := by
  have h := colProj_diag c s9
  fin_cases c <;> simpa [colInd] using h

theorem c3col_piDouble : ∀ c, C3col c piDouble := by
  intro c α β
  rw [trace_gammaF_proj_piDouble (colProj c) (colInd c) (colProj_diag_mul c)
    (colProj_diag c)]
  have hA : (∑ i : Fin 32, gammaVal i.val * colInd c i.val * pi1AVal i.val)
      = 0 := by
    fin_cases c <;> decide
  have hB : (∑ i : Fin 32, gammaVal i.val * colInd c i.val * pi1BVal i.val)
      = 0 := by
    fin_cases c <;> decide
  rw [hA, hB]
  simp only [Int.cast_zero, zero_mul, add_zero]
  rw [gammaF_s8, gammaF_s9, colProj_s8 c, colProj_s9 c]
  simp

theorem trace_feR_piDouble (α β : ℤ) :
    Matrix.trace (gammaF * eRProj * piDouble (u1Gen α β))
      = -2 * (α : ℂ) * Complex.I := by
  rw [trace_gammaF_proj_piDouble eRProj eRInd eRProj_diag_mul eRProj_diag]
  have hA : (∑ i : Fin 32, gammaVal i.val * eRInd i.val * pi1AVal i.val) = 0 := by
    decide
  have hB : (∑ i : Fin 32, gammaVal i.val * eRInd i.val * pi1BVal i.val) = 0 := by
    decide
  have p8 : eRProj s8 s8 = 0 := by
    have h := eRProj_diag s8
    simpa [eRInd] using h
  have p9 : eRProj s9 s9 = 1 := by
    have h := eRProj_diag s9
    simpa [eRInd] using h
  rw [hA, hB]
  simp only [Int.cast_zero, zero_mul, add_zero]
  rw [gammaF_s8, gammaF_s9, p8, p9, hstar α]
  ring

theorem not_feR_piDouble : ¬ FeR piDouble := by
  intro h
  have h10 := h 1 0
  rw [trace_feR_piDouble] at h10
  norm_num [Complex.ext_iff] at h10

theorem piDouble_family : PiDoubleFamilyCheck :=
  ⟨c3lep_piDouble, c3col_piDouble, not_feR_piDouble⟩



-- ===== Part 2 chunk A: piSwap, diagonal form, family =====

def uSeat (c : Fin 3) : Fin 32 := ⟨10 + 2 * c.val, by have hc := c.isLt; omega⟩
def dSeat (c : Fin 3) : Fin 32 := ⟨11 + 2 * c.val, by have hc := c.isLt; omega⟩

def piSwap (c : Fin 3) (a : AF) : Matrix (Fin 32) (Fin 32) ℂ :=
  pi1 a + Matrix.single (uSeat c) (uSeat c) (star a.u1 - a.u1)
    + Matrix.single (dSeat c) (dSeat c) (a.u1 - star a.u1)

def updDiag (c : Fin 3) (lam μ : ℂ) : Fin 32 → ℂ :=
  Function.update (Function.update (pi1Diag lam μ) (uSeat c) (star lam))
    (dSeat c) lam

theorem piSwap_eq_diagonal (c : Fin 3) (α β : ℤ) (t : ℝ) :
    piSwap c (u1ParamGen α β t)
      = Matrix.diagonal (updDiag c
          (Complex.exp ((α : ℂ) * ((t : ℂ) * Complex.I)))
          (Complex.exp ((β : ℂ) * ((t : ℂ) * Complex.I)))) := by
  have hU : u1ParamGen α β t
      = ⟨Complex.exp ((α : ℂ) * ((t : ℂ) * Complex.I)), 1,
        Complex.exp ((β : ℂ) * ((t : ℂ) * Complex.I))
          • (1 : Matrix I3 I3 ℂ)⟩ := rfl
  have hdU : pi1Diag (Complex.exp ((α : ℂ) * ((t : ℂ) * Complex.I)))
        (Complex.exp ((β : ℂ) * ((t : ℂ) * Complex.I))) (uSeat c)
      = Complex.exp ((α : ℂ) * ((t : ℂ) * Complex.I)) := by
    have h := pi1DiagVal_quarkR (Complex.exp ((α : ℂ) * ((t : ℂ) * Complex.I)))
      (Complex.exp ((β : ℂ) * ((t : ℂ) * Complex.I))) c 0
    have hval : (uSeat c).val = 10 + 2 * c.val + (0 : Fin 2).val := by
      show 10 + 2 * c.val = 10 + 2 * c.val + (0 : Fin 2).val
      omega
    show pi1DiagVal _ _ (uSeat c).val = _
    rw [hval]
    simpa using h
  have hdD : pi1Diag (Complex.exp ((α : ℂ) * ((t : ℂ) * Complex.I)))
        (Complex.exp ((β : ℂ) * ((t : ℂ) * Complex.I))) (dSeat c)
      = star (Complex.exp ((α : ℂ) * ((t : ℂ) * Complex.I))) := by
    have h := pi1DiagVal_quarkR (Complex.exp ((α : ℂ) * ((t : ℂ) * Complex.I)))
      (Complex.exp ((β : ℂ) * ((t : ℂ) * Complex.I))) c 1
    have hval : (dSeat c).val = 10 + 2 * c.val + (1 : Fin 2).val := by
      show 11 + 2 * c.val = 10 + 2 * c.val + (1 : Fin 2).val
      omega
    show pi1DiagVal _ _ (dSeat c).val = _
    rw [hval]
    simpa using h
  have hne : dSeat c ≠ uSeat c := by
    intro h
    have hv := congrArg Fin.val h
    simp [dSeat, uSeat] at hv
  rw [hU]
  show pi1 _ + Matrix.single (uSeat c) (uSeat c) _
      + Matrix.single (dSeat c) (dSeat c) _ = _
  rw [pi1_eq_diagonal, diagonal_add_single_diag, diagonal_add_single_diag]
  congr 1
  funext i
  by_cases hiD : i = dSeat c
  · subst hiD
    simp only [updDiag, Function.update_self, Function.update_of_ne hne, hdD]
    ring
  · by_cases hiU : i = uSeat c
    · subst hiU
      simp only [updDiag, Function.update_of_ne hiD, Function.update_self, hdU]
      ring
    · simp only [updDiag, Function.update_of_ne hiD, Function.update_of_ne hiU]

theorem piSwap_lifted_entry (c : Fin 3) (α β : ℤ) (t : ℝ) (s : Fin 32) :
    (piSwap c (u1ParamGen α β t) * piOp (piSwap c (u1ParamGen α β t))) s s
      = updDiag c (Complex.exp ((α : ℂ) * ((t : ℂ) * Complex.I)))
          (Complex.exp ((β : ℂ) * ((t : ℂ) * Complex.I))) s
        * updDiag c (Complex.exp ((α : ℂ) * ((t : ℂ) * Complex.I)))
          (Complex.exp ((β : ℂ) * ((t : ℂ) * Complex.I))) (partner s) := by
  rw [piSwap_eq_diagonal, Track1RouteB.piOp_diagonal,
    Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply_eq]

theorem pi1_lifted_entry (α β : ℤ) (t : ℝ) (s : Fin 32) :
    (pi1 (u1ParamGen α β t) * piOp (pi1 (u1ParamGen α β t))) s s
      = pi1Diag (Complex.exp ((α : ℂ) * ((t : ℂ) * Complex.I)))
          (Complex.exp ((β : ℂ) * ((t : ℂ) * Complex.I))) s
        * pi1Diag (Complex.exp ((α : ℂ) * ((t : ℂ) * Complex.I)))
          (Complex.exp ((β : ℂ) * ((t : ℂ) * Complex.I))) (partner s) := by
  have hU : u1ParamGen α β t
      = ⟨Complex.exp ((α : ℂ) * ((t : ℂ) * Complex.I)), 1,
        Complex.exp ((β : ℂ) * ((t : ℂ) * Complex.I))
          • (1 : Matrix I3 I3 ℂ)⟩ := rfl
  rw [hU, pi1_eq_diagonal, Track1RouteB.piOp_diagonal,
    Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply_eq]

theorem uSeat_ne_dSeat (c : Fin 3) : uSeat c ≠ dSeat c := by
  intro h
  have hv := congrArg Fin.val h
  simp [uSeat, dSeat] at hv

theorem dSeat_ne_uSeat (c : Fin 3) : dSeat c ≠ uSeat c := by
  intro h
  have hv := congrArg Fin.val h
  simp [dSeat, uSeat] at hv

theorem updDiag_uSeat (c : Fin 3) (lam μ : ℂ) :
    updDiag c lam μ (uSeat c) = star lam := by
  simp only [updDiag, Function.update_of_ne (uSeat_ne_dSeat c),
    Function.update_self]

theorem updDiag_dSeat (c : Fin 3) (lam μ : ℂ) :
    updDiag c lam μ (dSeat c) = lam := by
  simp only [updDiag, Function.update_self]

theorem updDiag_eq_pi1Diag_of_ne (c : Fin 3) (lam μ : ℂ) (s : Fin 32)
    (h1 : s ≠ uSeat c) (h2 : s ≠ dSeat c) :
    updDiag c lam μ s = pi1Diag lam μ s := by
  simp only [updDiag, Function.update_of_ne h2, Function.update_of_ne h1]

theorem partner_uSeat (c : Fin 3) :
    partner (uSeat c) = ⟨26 + 2 * c.val, by have h := c.isLt; omega⟩ := by
  apply Fin.ext
  show (partner (uSeat c)).val = 26 + 2 * c.val
  rw [partner_val_eq]
  have hv : (uSeat c).val = 10 + 2 * c.val := rfl
  rw [hv]
  have hc3 := c.isLt
  rw [if_pos (by omega : 10 + 2 * c.val < 16)]
  omega

theorem updDiag_partner_uSeat (c : Fin 3) (lam μ : ℂ) :
    updDiag c lam μ (partner (uSeat c)) = star μ := by
  rw [partner_uSeat]
  have h1 : (⟨26 + 2 * c.val, by have h := c.isLt; omega⟩ : Fin 32) ≠ uSeat c := by
    intro h
    have hv := congrArg Fin.val h
    simp [uSeat] at hv
  have h2 : (⟨26 + 2 * c.val, by have h := c.isLt; omega⟩ : Fin 32) ≠ dSeat c := by
    intro h
    have hv := congrArg Fin.val h
    simp [dSeat] at hv
  rw [updDiag_eq_pi1Diag_of_ne c lam μ _ h1 h2]
  have h := pi1DiagVal_quarkRc lam μ c 0
  simpa [pi1Diag] using h

theorem gammaF_uSeat (c : Fin 3) : gammaF (uSeat c) (uSeat c) = -1 := by
  have hv : gammaVal (uSeat c).val = -1 := by
    fin_cases c <;> decide
  rw [gammaF_diag_eq, hv]
  norm_num

theorem gammaF_dSeat (c : Fin 3) : gammaF (dSeat c) (dSeat c) = -1 := by
  have hv : gammaVal (dSeat c).val = -1 := by
    fin_cases c <;> decide
  rw [gammaF_diag_eq, hv]
  norm_num

theorem lepProj_uSeat (c : Fin 3) : lepProj (uSeat c) (uSeat c) = 0 := by
  have h := lepProj_diag (uSeat c)
  fin_cases c <;> simpa [lepInd, uSeat] using h

theorem lepProj_dSeat (c : Fin 3) : lepProj (dSeat c) (dSeat c) = 0 := by
  have h := lepProj_diag (dSeat c)
  fin_cases c <;> simpa [lepInd, dSeat] using h

theorem eRProj_uSeat (c : Fin 3) : eRProj (uSeat c) (uSeat c) = 0 := by
  have h := eRProj_diag (uSeat c)
  fin_cases c <;> simpa [eRInd, uSeat] using h

theorem eRProj_dSeat (c : Fin 3) : eRProj (dSeat c) (dSeat c) = 0 := by
  have h := eRProj_diag (dSeat c)
  fin_cases c <;> simpa [eRInd, dSeat] using h

theorem colProj_uSeat (c c' : Fin 3) :
    colProj c' (uSeat c) (uSeat c) = if c' = c then 1 else 0 := by
  have h := colProj_diag c' (uSeat c)
  fin_cases c <;> fin_cases c' <;> simpa [colInd, uSeat] using h

theorem colProj_dSeat (c c' : Fin 3) :
    colProj c' (dSeat c) (dSeat c) = if c' = c then 1 else 0 := by
  have h := colProj_diag c' (dSeat c)
  fin_cases c <;> fin_cases c' <;> simpa [colInd, dSeat] using h

theorem trace_gammaF_proj_piSwap (c : Fin 3) (P : Matrix (Fin 32) (Fin 32) ℂ)
    (ind : ℕ → ℤ)
    (hdiag : ∀ (M : Matrix (Fin 32) (Fin 32) ℂ) (i : Fin 32),
      (P * M) i i = P i i * M i i)
    (hP : ∀ i, P i i = (ind i.val : ℂ)) (α β : ℤ) :
    Matrix.trace (gammaF * P * piSwap c (u1Gen α β))
      = ((∑ i : Fin 32, gammaVal i.val * ind i.val * pi1AVal i.val : ℤ) : ℂ)
          * ((α : ℂ) * Complex.I)
        + ((∑ i : Fin 32, gammaVal i.val * ind i.val * pi1BVal i.val : ℤ) : ℂ)
          * ((β : ℂ) * Complex.I)
        + gammaF (uSeat c) (uSeat c) * P (uSeat c) (uSeat c)
          * (star ((α : ℂ) * Complex.I) - (α : ℂ) * Complex.I)
        + gammaF (dSeat c) (dSeat c) * P (dSeat c) (dSeat c)
          * ((α : ℂ) * Complex.I - star ((α : ℂ) * Complex.I)) := by
  have hdec : piSwap c (u1Gen α β)
      = pi1 (u1Gen α β)
        + Matrix.single (uSeat c) (uSeat c)
          (star ((α : ℂ) * Complex.I) - (α : ℂ) * Complex.I)
        + Matrix.single (dSeat c) (dSeat c)
          ((α : ℂ) * Complex.I - star ((α : ℂ) * Complex.I)) := rfl
  rw [hdec, Matrix.mul_add, Matrix.mul_add, Matrix.trace_add, Matrix.trace_add,
    trace_gammaF_proj_pi1 P ind hdiag hP, trace_gammaF_proj_single,
    trace_gammaF_proj_single]

theorem c3lep_piSwap (c : Fin 3) : C3lep (piSwap c) := by
  intro α β
  rw [trace_gammaF_proj_piSwap c lepProj lepInd lepProj_diag_mul lepProj_diag]
  have hA : (∑ i : Fin 32, gammaVal i.val * lepInd i.val * pi1AVal i.val) = 0 := by
    decide
  have hB : (∑ i : Fin 32, gammaVal i.val * lepInd i.val * pi1BVal i.val) = 0 := by
    decide
  rw [hA, hB]
  simp only [Int.cast_zero, zero_mul, add_zero]
  rw [gammaF_uSeat, gammaF_dSeat, lepProj_uSeat, lepProj_dSeat]
  simp

theorem c3col_piSwap (c : Fin 3) : ∀ c', C3col c' (piSwap c) := by
  intro c' α β
  rw [trace_gammaF_proj_piSwap c (colProj c') (colInd c') (colProj_diag_mul c')
    (colProj_diag c')]
  have hA : (∑ i : Fin 32, gammaVal i.val * colInd c' i.val * pi1AVal i.val)
      = 0 := by
    fin_cases c' <;> decide
  have hB : (∑ i : Fin 32, gammaVal i.val * colInd c' i.val * pi1BVal i.val)
      = 0 := by
    fin_cases c' <;> decide
  rw [hA, hB]
  simp only [Int.cast_zero, zero_mul, add_zero]
  rw [gammaF_uSeat, gammaF_dSeat, colProj_uSeat, colProj_dSeat]
  split_ifs with hc'
  · rw [hstar α]
    ring
  · simp

theorem feR_piSwap (c : Fin 3) : FeR (piSwap c) := by
  intro α β
  rw [trace_gammaF_proj_piSwap c eRProj eRInd eRProj_diag_mul eRProj_diag]
  have hA : (∑ i : Fin 32, gammaVal i.val * eRInd i.val * pi1AVal i.val) = 0 := by
    decide
  have hB : (∑ i : Fin 32, gammaVal i.val * eRInd i.val * pi1BVal i.val) = 0 := by
    decide
  rw [hA, hB]
  simp only [Int.cast_zero, zero_mul, add_zero]
  rw [gammaF_uSeat, gammaF_dSeat, eRProj_uSeat, eRProj_dSeat]
  simp

theorem gammaFamily_piSwap (c : Fin 3) : GammaFamily (piSwap c) :=
  ⟨c3lep_piSwap c, c3col_piSwap c, feR_piSwap c⟩



-- ===== Part 2 chunk B: order-zero refutation =====

theorem hstarI : star (Complex.I : ℂ) = -Complex.I := by simp

theorem hneI : star (Complex.I : ℂ) ≠ Complex.I := by
  rw [hstarI, ne_eq, Complex.ext_iff]
  simp only [Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im]
  norm_num

theorem piSwap_row_uSeat (c : Fin 3) (a : AF) (j : Fin 32) :
    piSwap c a (uSeat c) j = if j = uSeat c then star a.u1 else 0 := by
  fin_cases c <;> obtain ⟨v, hv⟩ := j <;> interval_cases v <;>
    simp [piSwap, pi1, uSeat, dSeat]

theorem piSwap_col_uSeat_other (c c' : Fin 3) (hc' : c' ≠ c) (a : AF)
    (k : Fin 32) :
    piSwap c a k (uSeat c') = if k = uSeat c' then a.u1 else 0 := by
  fin_cases c <;> fin_cases c' <;>
    first
    | exact (hc' rfl).elim
    | (obtain ⟨v, hv⟩ := k <;> interval_cases v <;>
        simp [piSwap, pi1, uSeat, dSeat])

theorem rho0 (b : AF)
    (hb : b.color = Matrix.single (⟨1, by omega⟩ : Fin 3)
      (⟨0, by omega⟩ : Fin 3) 1) :
    piOp (piSwap 0 b) (uSeat 0) (uSeat 1) = 1 := by
  rw [piOp_apply, partner_uSeat, partner_uSeat]
  show piSwap 0 b (⟨28, by omega⟩ : Fin 32) (⟨26, by omega⟩ : Fin 32) = 1
  have h1 : piSwap 0 b (⟨28, by omega⟩ : Fin 32) (⟨26, by omega⟩ : Fin 32)
      = pi1 b (⟨28, by omega⟩ : Fin 32) (⟨26, by omega⟩ : Fin 32) := by
    show (pi1 b + Matrix.single (uSeat 0) (uSeat 0) (star b.u1 - b.u1)
      + Matrix.single (dSeat 0) (dSeat 0) (b.u1 - star b.u1))
        (⟨28, by omega⟩ : Fin 32) (⟨26, by omega⟩ : Fin 32)
      = pi1 b (⟨28, by omega⟩ : Fin 32) (⟨26, by omega⟩ : Fin 32)
    rw [Matrix.add_apply, Matrix.add_apply, Matrix.single_apply,
      Matrix.single_apply,
      if_neg (by decide : ¬ (uSeat 0 = (⟨28, by omega⟩ : Fin 32)
        ∧ uSeat 0 = (⟨26, by omega⟩ : Fin 32))),
      if_neg (by decide : ¬ (dSeat 0 = (⟨28, by omega⟩ : Fin 32)
        ∧ dSeat 0 = (⟨26, by omega⟩ : Fin 32))),
      add_zero, add_zero]
  rw [h1]
  have h2 := pi1_entry_quarkRc b (⟨1, by omega⟩ : Fin 3)
    (⟨0, by omega⟩ : Fin 3) (⟨0, by omega⟩ : Fin 2) (⟨0, by omega⟩ : Fin 2)
  rw [hb] at h2
  simpa using h2

theorem rho1 (b : AF)
    (hb : b.color = Matrix.single (⟨2, by omega⟩ : Fin 3)
      (⟨1, by omega⟩ : Fin 3) 1) :
    piOp (piSwap 1 b) (uSeat 1) (uSeat 2) = 1 := by
  rw [piOp_apply, partner_uSeat, partner_uSeat]
  show piSwap 1 b (⟨30, by omega⟩ : Fin 32) (⟨28, by omega⟩ : Fin 32) = 1
  have h1 : piSwap 1 b (⟨30, by omega⟩ : Fin 32) (⟨28, by omega⟩ : Fin 32)
      = pi1 b (⟨30, by omega⟩ : Fin 32) (⟨28, by omega⟩ : Fin 32) := by
    show (pi1 b + Matrix.single (uSeat 1) (uSeat 1) (star b.u1 - b.u1)
      + Matrix.single (dSeat 1) (dSeat 1) (b.u1 - star b.u1))
        (⟨30, by omega⟩ : Fin 32) (⟨28, by omega⟩ : Fin 32)
      = pi1 b (⟨30, by omega⟩ : Fin 32) (⟨28, by omega⟩ : Fin 32)
    rw [Matrix.add_apply, Matrix.add_apply, Matrix.single_apply,
      Matrix.single_apply,
      if_neg (by decide : ¬ (uSeat 1 = (⟨30, by omega⟩ : Fin 32)
        ∧ uSeat 1 = (⟨28, by omega⟩ : Fin 32))),
      if_neg (by decide : ¬ (dSeat 1 = (⟨30, by omega⟩ : Fin 32)
        ∧ dSeat 1 = (⟨28, by omega⟩ : Fin 32))),
      add_zero, add_zero]
  rw [h1]
  have h2 := pi1_entry_quarkRc b (⟨2, by omega⟩ : Fin 3)
    (⟨1, by omega⟩ : Fin 3) (⟨0, by omega⟩ : Fin 2) (⟨0, by omega⟩ : Fin 2)
  rw [hb] at h2
  simpa using h2

theorem rho2 (b : AF)
    (hb : b.color = Matrix.single (⟨0, by omega⟩ : Fin 3)
      (⟨2, by omega⟩ : Fin 3) 1) :
    piOp (piSwap 2 b) (uSeat 2) (uSeat 0) = 1 := by
  rw [piOp_apply, partner_uSeat, partner_uSeat]
  show piSwap 2 b (⟨26, by omega⟩ : Fin 32) (⟨30, by omega⟩ : Fin 32) = 1
  have h1 : piSwap 2 b (⟨26, by omega⟩ : Fin 32) (⟨30, by omega⟩ : Fin 32)
      = pi1 b (⟨26, by omega⟩ : Fin 32) (⟨30, by omega⟩ : Fin 32) := by
    show (pi1 b + Matrix.single (uSeat 2) (uSeat 2) (star b.u1 - b.u1)
      + Matrix.single (dSeat 2) (dSeat 2) (b.u1 - star b.u1))
        (⟨26, by omega⟩ : Fin 32) (⟨30, by omega⟩ : Fin 32)
      = pi1 b (⟨26, by omega⟩ : Fin 32) (⟨30, by omega⟩ : Fin 32)
    rw [Matrix.add_apply, Matrix.add_apply, Matrix.single_apply,
      Matrix.single_apply,
      if_neg (by decide : ¬ (uSeat 2 = (⟨26, by omega⟩ : Fin 32)
        ∧ uSeat 2 = (⟨30, by omega⟩ : Fin 32))),
      if_neg (by decide : ¬ (dSeat 2 = (⟨26, by omega⟩ : Fin 32)
        ∧ dSeat 2 = (⟨30, by omega⟩ : Fin 32))),
      add_zero, add_zero]
  rw [h1]
  have h2 := pi1_entry_quarkRc b (⟨0, by omega⟩ : Fin 3)
    (⟨2, by omega⟩ : Fin 3) (⟨0, by omega⟩ : Fin 2) (⟨0, by omega⟩ : Fin 2)
  rw [hb] at h2
  simpa using h2

theorem not_base_piSwap0 : ¬ DialOneBase (piSwap 0) := by
  intro hbase
  have hoz := hbase.2.2.2.2.2.2.2.1 (⟨Complex.I, 0, 0⟩ : AF)
    (⟨0, 0, Matrix.single (⟨1, by omega⟩ : Fin 3) (⟨0, by omega⟩ : Fin 3) 1⟩
      : AF)
  have hentry := congrArg (fun M : Matrix (Fin 32) (Fin 32) ℂ =>
    M (uSeat 0) (uSeat 1)) hoz
  have hL : (piSwap 0 (⟨Complex.I, 0, 0⟩ : AF)
      * piOp (piSwap 0 (⟨0, 0, Matrix.single (⟨1, by omega⟩ : Fin 3)
          (⟨0, by omega⟩ : Fin 3) 1⟩ : AF))) (uSeat 0) (uSeat 1)
      = star Complex.I := by
    rw [Matrix.mul_apply, Finset.sum_eq_single (uSeat 0)]
    · rw [piSwap_row_uSeat, if_pos rfl, rho0 _ rfl]
      show star (Complex.I) * 1 = star Complex.I
      exact mul_one _
    · intro k _ hk
      rw [piSwap_row_uSeat, if_neg hk, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hR : (piOp (piSwap 0 (⟨0, 0, Matrix.single (⟨1, by omega⟩ : Fin 3)
        (⟨0, by omega⟩ : Fin 3) 1⟩ : AF))
      * piSwap 0 (⟨Complex.I, 0, 0⟩ : AF)) (uSeat 0) (uSeat 1)
      = Complex.I := by
    rw [Matrix.mul_apply, Finset.sum_eq_single (uSeat 1)]
    · rw [rho0 _ rfl,
        piSwap_col_uSeat_other 0 1 (by decide) _ (uSeat 1), if_pos rfl]
      show (1 : ℂ) * Complex.I = Complex.I
      exact one_mul _
    · intro k _ hk
      rw [piSwap_col_uSeat_other 0 1 (by decide) _ k, if_neg hk, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [hL, hR] at hentry
  exact hneI hentry

theorem not_base_piSwap1 : ¬ DialOneBase (piSwap 1) := by
  intro hbase
  have hoz := hbase.2.2.2.2.2.2.2.1 (⟨Complex.I, 0, 0⟩ : AF)
    (⟨0, 0, Matrix.single (⟨2, by omega⟩ : Fin 3) (⟨1, by omega⟩ : Fin 3) 1⟩
      : AF)
  have hentry := congrArg (fun M : Matrix (Fin 32) (Fin 32) ℂ =>
    M (uSeat 1) (uSeat 2)) hoz
  have hL : (piSwap 1 (⟨Complex.I, 0, 0⟩ : AF)
      * piOp (piSwap 1 (⟨0, 0, Matrix.single (⟨2, by omega⟩ : Fin 3)
          (⟨1, by omega⟩ : Fin 3) 1⟩ : AF))) (uSeat 1) (uSeat 2)
      = star Complex.I := by
    rw [Matrix.mul_apply, Finset.sum_eq_single (uSeat 1)]
    · rw [piSwap_row_uSeat, if_pos rfl, rho1 _ rfl]
      show star (Complex.I) * 1 = star Complex.I
      exact mul_one _
    · intro k _ hk
      rw [piSwap_row_uSeat, if_neg hk, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hR : (piOp (piSwap 1 (⟨0, 0, Matrix.single (⟨2, by omega⟩ : Fin 3)
        (⟨1, by omega⟩ : Fin 3) 1⟩ : AF))
      * piSwap 1 (⟨Complex.I, 0, 0⟩ : AF)) (uSeat 1) (uSeat 2)
      = Complex.I := by
    rw [Matrix.mul_apply, Finset.sum_eq_single (uSeat 2)]
    · rw [rho1 _ rfl,
        piSwap_col_uSeat_other 1 2 (by decide) _ (uSeat 2), if_pos rfl]
      show (1 : ℂ) * Complex.I = Complex.I
      exact one_mul _
    · intro k _ hk
      rw [piSwap_col_uSeat_other 1 2 (by decide) _ k, if_neg hk, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [hL, hR] at hentry
  exact hneI hentry

theorem not_base_piSwap2 : ¬ DialOneBase (piSwap 2) := by
  intro hbase
  have hoz := hbase.2.2.2.2.2.2.2.1 (⟨Complex.I, 0, 0⟩ : AF)
    (⟨0, 0, Matrix.single (⟨0, by omega⟩ : Fin 3) (⟨2, by omega⟩ : Fin 3) 1⟩
      : AF)
  have hentry := congrArg (fun M : Matrix (Fin 32) (Fin 32) ℂ =>
    M (uSeat 2) (uSeat 0)) hoz
  have hL : (piSwap 2 (⟨Complex.I, 0, 0⟩ : AF)
      * piOp (piSwap 2 (⟨0, 0, Matrix.single (⟨0, by omega⟩ : Fin 3)
          (⟨2, by omega⟩ : Fin 3) 1⟩ : AF))) (uSeat 2) (uSeat 0)
      = star Complex.I := by
    rw [Matrix.mul_apply, Finset.sum_eq_single (uSeat 2)]
    · rw [piSwap_row_uSeat, if_pos rfl, rho2 _ rfl]
      show star (Complex.I) * 1 = star Complex.I
      exact mul_one _
    · intro k _ hk
      rw [piSwap_row_uSeat, if_neg hk, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hR : (piOp (piSwap 2 (⟨0, 0, Matrix.single (⟨0, by omega⟩ : Fin 3)
        (⟨2, by omega⟩ : Fin 3) 1⟩ : AF))
      * piSwap 2 (⟨Complex.I, 0, 0⟩ : AF)) (uSeat 2) (uSeat 0)
      = Complex.I := by
    rw [Matrix.mul_apply, Finset.sum_eq_single (uSeat 0)]
    · rw [rho2 _ rfl,
        piSwap_col_uSeat_other 2 0 (by decide) _ (uSeat 0), if_pos rfl]
      show (1 : ℂ) * Complex.I = Complex.I
      exact one_mul _
    · intro k _ hk
      rw [piSwap_col_uSeat_other 2 0 (by decide) _ k, if_neg hk, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [hL, hR] at hentry
  exact hneI hentry

theorem not_base_piSwap (c : Fin 3) : ¬ DialOneBase (piSwap c) := by
  fin_cases c
  · exact not_base_piSwap0
  · exact not_base_piSwap1
  · exact not_base_piSwap2



-- ===== Part 2 chunk C: non-proportionality =====

theorem partner_uL (c : Fin 3) :
    partner (fermionIndex .uL c)
      = ⟨18 + 2 * c.val, by have h := c.isLt; omega⟩ := by
  apply Fin.ext
  show (partner (fermionIndex .uL c)).val = 18 + 2 * c.val
  rw [partner_val_eq]
  have hv : (fermionIndex .uL c).val = 2 + 2 * c.val := fermionIndex_val _ _
  rw [hv]
  have hc3 := c.isLt
  rw [if_pos (by omega : 2 + 2 * c.val < 16)]
  omega

theorem uL_ne_uSeat (c : Fin 3) : fermionIndex .uL c ≠ uSeat c := by
  intro h
  have hv := congrArg Fin.val h
  have hv2 : (fermionIndex .uL c).val = 2 + 2 * c.val := fermionIndex_val _ _
  have hv3 : (uSeat c).val = 10 + 2 * c.val := rfl
  rw [hv2, hv3] at hv
  omega

theorem uL_ne_dSeat (c : Fin 3) : fermionIndex .uL c ≠ dSeat c := by
  intro h
  have hv := congrArg Fin.val h
  have hv2 : (fermionIndex .uL c).val = 2 + 2 * c.val := fermionIndex_val _ _
  have hv3 : (dSeat c).val = 11 + 2 * c.val := rfl
  rw [hv2, hv3] at hv
  omega

theorem partner_uL_ne_uSeat (c : Fin 3) :
    partner (fermionIndex .uL c) ≠ uSeat c := by
  intro h
  have hv := congrArg Fin.val h
  have hv2 : (partner (fermionIndex .uL c)).val = 18 + 2 * c.val := by
    rw [partner_uL]
  have hv3 : (uSeat c).val = 10 + 2 * c.val := rfl
  rw [hv2, hv3] at hv
  omega

theorem partner_uL_ne_dSeat (c : Fin 3) :
    partner (fermionIndex .uL c) ≠ dSeat c := by
  intro h
  have hv := congrArg Fin.val h
  have hv2 : (partner (fermionIndex .uL c)).val = 18 + 2 * c.val := by
    rw [partner_uL]
  have hv3 : (dSeat c).val = 11 + 2 * c.val := rfl
  rw [hv2, hv3] at hv
  omega

theorem updDiag_uL (c : Fin 3) (lam μ : ℂ) :
    updDiag c lam μ (fermionIndex .uL c) = 1 := by
  rw [updDiag_eq_pi1Diag_of_ne c lam μ _ (uL_ne_uSeat c) (uL_ne_dSeat c)]
  have hv : (fermionIndex .uL c).val = 2 + 2 * c.val := fermionIndex_val _ _
  have h := pi1DiagVal_quarkL lam μ c 0
  show pi1DiagVal lam μ (fermionIndex .uL c).val = 1
  rw [hv]
  simpa using h

theorem updDiag_partner_uL (c : Fin 3) (lam μ : ℂ) :
    updDiag c lam μ (partner (fermionIndex .uL c)) = star μ := by
  rw [updDiag_eq_pi1Diag_of_ne c lam μ _ (partner_uL_ne_uSeat c)
    (partner_uL_ne_dSeat c)]
  have hv : (partner (fermionIndex .uL c)).val = 18 + 2 * c.val := by
    rw [partner_uL]
  have h := pi1DiagVal_quarkLc lam μ c 0
  show pi1DiagVal lam μ (partner (fermionIndex .uL c)).val = star μ
  rw [hv]
  simpa using h

theorem entry_uR (c : Fin 3) (t : ℝ) :
    (piSwap c (u1ParamGen 3 (-1) t) * piOp (piSwap c (u1ParamGen 3 (-1) t)))
        (fermionIndex .uR c) (fermionIndex .uR c)
      = star (Complex.exp (((3 : ℤ) : ℂ) * ((t : ℂ) * Complex.I)))
        * star (Complex.exp (((-1 : ℤ) : ℂ) * ((t : ℂ) * Complex.I))) := by
  have hseat : fermionIndex .uR c = uSeat c := rfl
  rw [hseat, piSwap_lifted_entry, updDiag_uSeat, updDiag_partner_uSeat]

theorem entry_uL (c : Fin 3) (t : ℝ) :
    (piSwap c (u1ParamGen 3 (-1) t) * piOp (piSwap c (u1ParamGen 3 (-1) t)))
        (fermionIndex .uL c) (fermionIndex .uL c)
      = star (Complex.exp (((-1 : ℤ) : ℂ) * ((t : ℂ) * Complex.I))) := by
  rw [piSwap_lifted_entry, updDiag_uL, updDiag_partner_uL, one_mul]

theorem entry_uR_pi_div_two (c : Fin 3) :
    (piSwap c (u1ParamGen 3 (-1) (Real.pi / 2))
      * piOp (piSwap c (u1ParamGen 3 (-1) (Real.pi / 2))))
        (fermionIndex .uR c) (fermionIndex .uR c) = -1 := by
  rw [entry_uR, ← star_mul, ← Complex.exp_add]
  have hexp : (((-1 : ℤ) : ℂ) * (((Real.pi / 2 : ℝ) : ℂ) * Complex.I)
      + ((3 : ℤ) : ℂ) * (((Real.pi / 2 : ℝ) : ℂ) * Complex.I))
      = ((Real.pi : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [hexp, Complex.exp_pi_mul_I]
  simp

theorem entry_uL_pi (c : Fin 3) :
    (piSwap c (u1ParamGen 3 (-1) Real.pi)
      * piOp (piSwap c (u1ParamGen 3 (-1) Real.pi)))
        (fermionIndex .uL c) (fermionIndex .uL c) = -1 := by
  rw [entry_uL]
  have hμ : (Complex.exp (((-1 : ℤ) : ℂ)
      * (((Real.pi : ℝ) : ℂ) * Complex.I)))
      = Complex.exp (-(((Real.pi : ℝ) : ℂ) * Complex.I)) := by
    congr 1
    push_cast
    ring
  rw [hμ, star_exp_neg_one, Complex.exp_pi_mul_I]

theorem kappa_contra (κ : ℝ)
    (hR : Complex.exp (↑(κ * (Real.pi / 2)) * (4 : ℂ) * Complex.I) = -1)
    (hL : Complex.exp (↑(κ * Real.pi) * (1 : ℂ) * Complex.I) = -1) :
    False := by
  have e1 : (↑(κ * Real.pi) * (1 : ℂ) * Complex.I)
      = (κ : ℂ) * ((Real.pi : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  have e2 : (↑(κ * (Real.pi / 2)) * (4 : ℂ) * Complex.I)
      = (κ : ℂ) * ((Real.pi : ℝ) : ℂ) * Complex.I
        + (κ : ℂ) * ((Real.pi : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [e1] at hL
  rw [e2, Complex.exp_add] at hR
  rw [hL] at hR
  norm_num at hR

theorem nonprop_piSwap_zero :
    ¬ ∃ κ : ℝ, ∀ (f : SMFermion) (t : ℝ),
      (piSwap 0 (u1ParamGen 3 (-1) t) * piOp (piSwap 0 (u1ParamGen 3 (-1) t)))
          (fermionIndex f 0) (fermionIndex f 0)
        = Complex.exp (↑(κ * t)
          * commonHyperchargeMatrix (fermionIndex f 0) (fermionIndex f 0)
          * Complex.I) := by
  rintro ⟨κ, h⟩
  have hR := h .uR (Real.pi / 2)
  have hL := h .uL Real.pi
  rw [entry_uR_pi_div_two 0] at hR
  rw [entry_uL_pi 0] at hL
  rw [commonHyperchargeMatrix_diag] at hR hL
  have huR : (3 : ℂ) * ((hypercharge .uR : ℚ) : ℂ) = 4 := by
    have hh : hypercharge .uR = 4 / 3 := rfl
    rw [hh]
    norm_num
  have huL : (3 : ℂ) * ((hypercharge .uL : ℚ) : ℂ) = 1 := by
    have hh : hypercharge .uL = 1 / 3 := rfl
    rw [hh]
    norm_num
  rw [huR] at hR
  rw [huL] at hL
  exact kappa_contra κ hR.symm hL.symm

theorem swap_slice_nonprop (c : Fin 3) (κ : ℝ) :
    ¬ ((∀ t : ℝ, (piSwap c (u1ParamGen 3 (-1) t)
          * piOp (piSwap c (u1ParamGen 3 (-1) t)))
          (fermionIndex .uR c) (fermionIndex .uR c)
          = Complex.exp (↑(κ * t) * (4 : ℂ) * Complex.I))
      ∧ (∀ t : ℝ, (piSwap c (u1ParamGen 3 (-1) t)
          * piOp (piSwap c (u1ParamGen 3 (-1) t)))
          (fermionIndex .uL c) (fermionIndex .uL c)
          = Complex.exp (↑(κ * t) * (1 : ℂ) * Complex.I))) := by
  rintro ⟨huR, huL⟩
  have hR := huR (Real.pi / 2)
  have hL := huL Real.pi
  rw [entry_uR_pi_div_two c] at hR
  rw [entry_uL_pi c] at hL
  exact kappa_contra κ hR.symm hL.symm

theorem updDiag_gen_eq_pi1Diag_of_ne (c : Fin 3) (α β : ℤ) (t : ℝ)
    (s : Fin 32) (h1 : s ≠ uSeat c) (h2 : s ≠ dSeat c) :
    updDiag c (Complex.exp ((α : ℂ) * ((t : ℂ) * Complex.I)))
        (Complex.exp ((β : ℂ) * ((t : ℂ) * Complex.I))) s
      = pi1Diag (Complex.exp ((α : ℂ) * ((t : ℂ) * Complex.I)))
        (Complex.exp ((β : ℂ) * ((t : ℂ) * Complex.I))) s :=
  updDiag_eq_pi1Diag_of_ne c _ _ s h1 h2

theorem exists_kappa_piSwap_one :
    ∃ κ : ℝ, ∀ (f : SMFermion) (t : ℝ),
      (piSwap 1 (u1ParamGen 3 (-1) t) * piOp (piSwap 1 (u1ParamGen 3 (-1) t)))
          (fermionIndex f 0) (fermionIndex f 0)
        = Complex.exp (↑(κ * t)
          * commonHyperchargeMatrix (fermionIndex f 0) (fermionIndex f 0)
          * Complex.I) := by
  refine ⟨1, fun f t => ?_⟩
  cases f <;>
    (rw [piSwap_lifted_entry,
      updDiag_gen_eq_pi1Diag_of_ne _ _ _ _ _ (by decide) (by decide),
      updDiag_gen_eq_pi1Diag_of_ne _ _ _ _ _ (by decide) (by decide),
      ← pi1_lifted_entry, ← u1ParamB_eq_gen, pi1_hypercharge_pattern,
      commonHyperchargeMatrix_diag]
     congr 1
     push_cast
     ring)

theorem exists_kappa_piSwap_two :
    ∃ κ : ℝ, ∀ (f : SMFermion) (t : ℝ),
      (piSwap 2 (u1ParamGen 3 (-1) t) * piOp (piSwap 2 (u1ParamGen 3 (-1) t)))
          (fermionIndex f 0) (fermionIndex f 0)
        = Complex.exp (↑(κ * t)
          * commonHyperchargeMatrix (fermionIndex f 0) (fermionIndex f 0)
          * Complex.I) := by
  refine ⟨1, fun f t => ?_⟩
  cases f <;>
    (rw [piSwap_lifted_entry,
      updDiag_gen_eq_pi1Diag_of_ne _ _ _ _ _ (by decide) (by decide),
      updDiag_gen_eq_pi1Diag_of_ne _ _ _ _ _ (by decide) (by decide),
      ← pi1_lifted_entry, ← u1ParamB_eq_gen, pi1_hypercharge_pattern,
      commonHyperchargeMatrix_diag]
     congr 1
     push_cast
     ring)

theorem exists_kappa_piSwap_of_ne (c : Fin 3) (hc : c ≠ 0) :
    ∃ κ : ℝ, ∀ (f : SMFermion) (t : ℝ),
      (piSwap c (u1ParamGen 3 (-1) t) * piOp (piSwap c (u1ParamGen 3 (-1) t)))
          (fermionIndex f 0) (fermionIndex f 0)
        = Complex.exp (↑(κ * t)
          * commonHyperchargeMatrix (fermionIndex f 0) (fermionIndex f 0)
          * Complex.I) := by
  fin_cases c
  · exact (hc rfl).elim
  · exact exists_kappa_piSwap_one
  · exact exists_kappa_piSwap_two

-- ===== Assemblies =====

theorem kCMP_F1_does_not_fire : ¬ QuarkSwapCheck piSwap := by
  intro h
  exact not_base_piSwap 0 (h 0).1

theorem strengthened_pi1 : DialOneStrengthenedFam pi1 :=
  ⟨dialOneBase_pi1, c3_pi1_holds, gammaFamily_pi1⟩

theorem not_strengthened_piDouble : ¬ DialOneStrengthenedFam piDouble :=
  fun h => not_feR_piDouble h.2.2.2.2

theorem not_strengthened_piFlip :
    ¬ DialOneStrengthenedFam ThetLogos.HyperchargeForcing.piFlip :=
  fun h => c3_piFlip_fails h.2.1

theorem not_strengthened_piSwap (c : Fin 3) :
    ¬ DialOneStrengthenedFam (piSwap c) :=
  fun h => not_base_piSwap c h.1

theorem toggle_exclusion :
    DialOneStrengthenedFam pi1
    ∧ ¬ DialOneStrengthenedFam ThetLogos.HyperchargeForcing.piFlip
    ∧ ¬ DialOneStrengthenedFam piDouble
    ∧ ∀ c, ¬ DialOneStrengthenedFam (piSwap c) :=
  ⟨strengthened_pi1, not_strengthened_piFlip, not_strengthened_piDouble,
    not_strengthened_piSwap⟩

theorem quarkSwap_zero_verdicts :
    GammaFamily (piSwap 0)
    ∧ ¬ DialOneBase (piSwap 0)
    ∧ (¬ ∃ κ : ℝ, ∀ (f : SMFermion) (t : ℝ),
      (piSwap 0 (u1ParamGen 3 (-1) t) * piOp (piSwap 0 (u1ParamGen 3 (-1) t)))
          (fermionIndex f 0) (fermionIndex f 0)
        = Complex.exp (↑(κ * t)
          * commonHyperchargeMatrix (fermionIndex f 0) (fermionIndex f 0)
          * Complex.I)) :=
  ⟨gammaFamily_piSwap 0, not_base_piSwap 0, nonprop_piSwap_zero⟩

theorem quarkSwap_verdicts_of_ne (c : Fin 3) (hc : c ≠ 0) :
    GammaFamily (piSwap c)
    ∧ ¬ DialOneBase (piSwap c)
    ∧ (∃ κ : ℝ, ∀ (f : SMFermion) (t : ℝ),
      (piSwap c (u1ParamGen 3 (-1) t) * piOp (piSwap c (u1ParamGen 3 (-1) t)))
          (fermionIndex f 0) (fermionIndex f 0)
        = Complex.exp (↑(κ * t)
          * commonHyperchargeMatrix (fermionIndex f 0) (fermionIndex f 0)
          * Complex.I)) :=
  ⟨gammaFamily_piSwap c, not_base_piSwap c, exists_kappa_piSwap_of_ne c hc⟩

-- Axiom audit for the headline verdicts (expected:
-- [propext, Classical.choice, Quot.sound] throughout).
#print axioms gammaFamily_pi1
#print axioms piDouble_family
#print axioms trace_feR_piDouble
#print axioms gammaFamily_piSwap
#print axioms not_base_piSwap
#print axioms nonprop_piSwap_zero
#print axioms exists_kappa_piSwap_of_ne
#print axioms swap_slice_nonprop
#print axioms kCMP_F1_does_not_fire
#print axioms toggle_exclusion

end ThetLogos.DialOneGammaFamilyChecks
