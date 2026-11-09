import Mathlib.Tactic
import ThetLogos.DialOneGradeRConjAmend
import ThetLogos.DialOneGradeRConj
import ThetLogos.DialOneGradeRConjReadback
import ThetLogos.DialOnePiUFamily
import ThetLogos.DialOnePiAntiPackage
import ThetLogos.DialOneSwapOrbitBase
import ThetLogos.DialOneShapeBIdentification

open Matrix Complex
open ThetLogos.Track1RouteB
open ThetLogos.PreOptionARepresentation
open ThetLogos.HyperchargeForcing
open ThetLogos.DialOneSeatTiePin
open ThetLogos.DialOneGammaTracePin
open ThetLogos.DialOneGammaFamilyPin
open ThetLogos.DialOneGradeRConjPin
open ThetLogos.DialOneConjugationCounterexample
open ThetLogos.DialOneGammaTraceChecks
open ThetLogos.DialOneGammaFamilyChecks
open ThetLogos.DialOneSwapOrbit
open ThetLogos.DialOneSwapOrbitBase
open ThetLogos.DialOneAntiparticleChapter

namespace ThetLogos.DialOnePresSweep

/-!
# ThetLogos.DialOnePresSweep — P-C: the exhibited-pair preservation decision sweep (Q1)

Governing text: `q1-class-level-scope-2026-11-08.md` §1 (Route P-C,
§1.3–§1.5), fired as brick P-C with kill **K-Q1-PRES-EXH** armed.
**NO CLAIM. Dials 0/4; Dial 1 = 0 on every outcome.**

## The frozen target

At the one nontrivial landed member `U = conjU` of the amended
class (`RealCentralizingClass`, `DialOneGradeRConjAmend`), decide
preservation at the three remaining exhibited strengthened points
`π ∈ {orbitRep allSwapBits, piU, conjRep conjU piAnti}`: for each,
the three pulled clauses of the amended capstone
(`strengthened_preserved_of_real_pulled`) — equivalently, by the
landed iffs of `DialOneGradeRConj`, the three family clauses at
the conjugate. Each pair's pulled clauses are finite trace
computations over the landed tables.

## The verdict

**All three pulled clauses vanish at all three pairs**
(`pulled_lep_piU` / `pulled_col_piU` / `pulled_eR_piU`,
`pulled_lep_conjRepPiAnti` / …, `pulled_lep_allSwap` / …), so the
amended capstone fires at each pair:

* `DialOneStrengthenedFam (conjRep conjU (orbitRep allSwapBits))`
* `DialOneStrengthenedFam (conjRep conjU piU)`
* `DialOneStrengthenedFam (conjRep conjU (conjRep conjU piAnti))`

**K-Q1-PRES-EXH does NOT fire** — no pulled trace is nonzero at
any exhibited pair. Together with the two previously landed pairs
(`preservationAtPi1ConjU`, `strengthened_conjRep_piAnti`), the
exhibited sublattice
`{pi1, piAnti, allSwap, piU, conjRep conjU piAnti} × {conjU}` is
preservation-closed (`presSweep_package`).

**Scope fence, stated at full rank:** this is evidence at exactly
the three pairs computed. The class-level statement
`PreservationQReal` remains **OPEN**: a clean sweep is not
class-level evidence — the `U0` precedent (spec §1.4) is precisely
the warning that the (original) class is strictly larger than its
exhibited members, and no unlanded member of the amended class is
excluded or decided here. Nothing in this module asserts
`PreservationQReal`.

## Method, per pair

* **`piU`** — the pulled trace at `piU`, pulled back once more by
  the landed `trace_gammaF_proj_piU`, is the trace against the
  diagonal `pi1 (u1Gen α β)` of the *double-pulled* γ-weighted
  projection `Qᵀ * (gammaF * P) * Q`, where `Q = conjU * conjU` is
  again diagonal-or-mate (its tables `diagQ`/`offQ`, ℤ shadows
  `diagQZ`/`offQZ` at ×25: `−7`/`±24` on the mixed seats). Only
  the double-pulled diagonal enters; it is the ℤ shadow `dpWZ`
  at ×625, and its γ-weighted A- and B-shadow sums vanish for
  every projection indicator (`dpWZ_sum_*`, by kernel `decide`
  on ℤ sums — the `DialOnePiUFamily.colWZ` idiom).
* **`conjRep conjU piAnti`** — at the generator this point *is*
  `piU` at the flipped direction (`conjRep_piAnti_gen`, via the
  landed colour-twist flip `piAnti_flip_u1Gen`), so its pulled
  clauses are `piU`'s at `(α, −β)`.
* **`orbitRep allSwapBits`** — at the generator the point is
  `pi1 + swapCorr` (`allSwap_eq`). The `pi1` pulled part is the
  landed preservation at `pi1`, read through the pulled iffs.
  The `swapCorr` part is a sum over its six diagonal seats
  `{uSeat c, dSeat c}` with coefficients `∓2α·I`; the pulled
  diagonals there are the `9/25 / 16/25 / 1` seat values, and the
  seat sum cancels colour by colour.

## Fences

NO CLAIM. Dial 1 = 0: a family-membership decision derives no
measured number. No `axiom` declarations; no sorrys; no
`native_decide`. The Layer-2 span obstruction of spec §1.3
(why no form argument substitutes for this sweep) is certified
at paper grade in the lane's STATUS.md, not in this module.
-/

/-! ## §0. The double conjugation `Q = conjU * conjU`: entry tables -/

/-- The diagonal table of `Q = conjU * conjU`:
`diagC² + offC · offC ∘ mateSeat` (at a mixed seat:
`(3/5)² + (4/5)(−4/5) = −7/25`; at a fixed seat: `1`). -/
noncomputable def diagQ (i : Fin 32) : ℂ :=
  diagC i * diagC i + offC i * offC (mateSeat i)

/-- The mate table of `Q = conjU * conjU`:
`diagC · offC + offC · diagC ∘ mateSeat` (at a mixed seat:
`±24/25`; at a fixed seat: `0`). -/
noncomputable def offQ (i : Fin 32) : ℂ :=
  diagC i * offC i + offC i * diagC (mateSeat i)

/-- `Q` times a matrix, entrywise — `conjU_mul_apply` twice. -/
theorem conjU_mul_conjU_mul_apply (M : Matrix (Fin 32) (Fin 32) ℂ)
    (i j : Fin 32) :
    ((conjU * conjU) * M) i j
      = diagQ i * M i j + offQ i * M (mateSeat i) j := by
  rw [Matrix.mul_assoc, conjU_mul_apply, conjU_mul_apply,
    conjU_mul_apply, mateSeat_diagC, mateSeat_involutive]
  simp only [diagQ, offQ, mateSeat_diagC]
  ring

/-- A matrix times `Q`, entrywise — `mul_conjU_apply` twice. -/
theorem mul_conjU_mul_conjU_apply (M : Matrix (Fin 32) (Fin 32) ℂ)
    (i j : Fin 32) :
    (M * (conjU * conjU)) i j
      = M i j * diagQ j + M i (mateSeat j) * offQ (mateSeat j) := by
  rw [← Matrix.mul_assoc, mul_conjU_apply, mul_conjU_apply,
    mul_conjU_apply, mateSeat_diagC, mateSeat_involutive]
  simp only [diagQ, offQ, mateSeat_diagC, mateSeat_involutive]
  ring

/-- `Qᵀ` times a matrix, entrywise — by transposing
`mul_conjU_mul_conjU_apply` (the `conjUT_mul_apply` route). -/
theorem conjQT_mul_apply (M : Matrix (Fin 32) (Fin 32) ℂ)
    (i j : Fin 32) :
    ((conjU * conjU)ᵀ * M) i j
      = diagQ i * M i j + offQ (mateSeat i) * M (mateSeat i) j := by
  have h : ((conjU * conjU)ᵀ * M) i j
      = (Mᵀ * (conjU * conjU)) j i := by
    have e : (Mᵀ * (conjU * conjU))ᵀ = (conjU * conjU)ᵀ * M := by
      rw [Matrix.transpose_mul, Matrix.transpose_transpose]
    rw [← e]
    rfl
  rw [h, mul_conjU_mul_conjU_apply]
  simp only [Matrix.transpose_apply]
  ring

/-- At a mate-fixed seat, `Q` is the identity row:
`diagQ = 1`, `offQ = 0`. -/
theorem mateSeat_eq_self_diagQ (i : Fin 32) (h : mateSeat i = i) :
    diagQ i = 1 ∧ offQ i = 0 := by
  have hdc := mateSeat_eq_self_diagC i h
  rw [h] at *
  simp [diagQ, offQ, hdc.1, hdc.2]

/-- The diagonal of a `Q`-conjugated diagonal matrix: the
`diagQ²`/`offQ²` mixture of the diagonal at the seat and its
mate (the `conjT_diag_conjU_diag` formula, one conjugation
deeper). -/
theorem conjQT_diag_conjQ_diag (d : Fin 32 → ℂ) (i : Fin 32) :
    ((conjU * conjU)ᵀ * Matrix.diagonal d * (conjU * conjU)) i i
      = diagQ i * diagQ i * d i
        + offQ (mateSeat i) * offQ (mateSeat i) * d (mateSeat i) := by
  rw [Matrix.mul_assoc, conjQT_mul_apply, mul_conjU_mul_conjU_apply,
    mul_conjU_mul_conjU_apply]
  by_cases hm : mateSeat i = i
  · have hdc := mateSeat_eq_self_diagQ i hm
    rw [hm, hdc.1, hdc.2]
    simp only [Matrix.diagonal_apply_eq]
    ring
  · rw [Matrix.diagonal_apply_ne _
      (fun hh : i = mateSeat i => hm hh.symm),
      Matrix.diagonal_apply_ne _ hm]
    simp only [Matrix.diagonal_apply_eq]
    ring

/-! ## §1. The ℤ shadows of `Q`'s tables, at ×25 -/

/-- The integer shadow of `diagQ`: `diagQ i = diagQZ i / 25`
in `ℂ` (`−7` at the eight mixed seats, `25` elsewhere). -/
def diagQZ (i : Fin 32) : ℤ :=
  if i.val = 2 ∨ i.val = 4 ∨ i.val = 10 ∨ i.val = 12
      ∨ i.val = 18 ∨ i.val = 20 ∨ i.val = 26 ∨ i.val = 28
    then -7 else 25

/-- The integer shadow of `offQ`: `offQ i = offQZ i / 25` in
`ℂ` (`+24` at `{2, 10, 18, 26}`, `−24` at `{4, 12, 20, 28}`). -/
def offQZ (i : Fin 32) : ℤ :=
  if i.val = 2 ∨ i.val = 10 ∨ i.val = 18 ∨ i.val = 26
    then 24
  else if i.val = 4 ∨ i.val = 12 ∨ i.val = 20 ∨ i.val = 28
    then -24 else 0

theorem diagQ_shadow (i : Fin 32) :
    diagQ i = ((diagQZ i : ℤ) : ℂ) / 25 := by
  fin_cases i <;> simp [diagQ, diagQZ, diagC, offC, mateSeat] <;> norm_num

theorem offQ_shadow (i : Fin 32) :
    offQ i = ((offQZ i : ℤ) : ℂ) / 25 := by
  fin_cases i <;> simp [offQ, offQZ, diagC, offC, mateSeat] <;> norm_num

/-! ## §2. The double-pulled weights, as ℤ shadows at ×625 -/

/-- The double-pulled γ-weighted weight, as an integer shadow
at ×625: `dpWZ ind i = 625 • (the double-pulled projection's
diagonal at seat `i`)` — `diagQZ² • (γ • ind)` at the seat plus
`offQZ² • (γ • ind)` at its mate, for a projection with
indicator `ind`. -/
def dpWZ (ind : ℕ → ℤ) (i : Fin 32) : ℤ :=
  diagQZ i * diagQZ i * (gammaVal i.val * ind i.val)
    + offQZ (mateSeat i) * offQZ (mateSeat i)
      * (gammaVal (mateSeat i).val * ind (mateSeat i).val)

/-- The diagonal of the double-pulled γ-weighted projection
is the shadow weight: `dpWZ ind / 625` in `ℂ`. -/
theorem doublePulled_diag (P : Matrix (Fin 32) (Fin 32) ℂ)
    (ind : ℕ → ℤ)
    (hP : P = Matrix.diagonal (fun i => (ind i.val : ℂ))) (i : Fin 32) :
    ((conjU * conjU)ᵀ * (gammaF * P) * (conjU * conjU)) i i
      = ((dpWZ ind i : ℤ) : ℂ) / 625 := by
  have hge : gammaF * P
      = Matrix.diagonal
          (fun i => (gammaVal i.val : ℂ) * (ind i.val : ℂ)) :=
    ThetLogos.DialOnePiUFamily.gammaF_mul_proj _ _ hP
  rw [hge, conjQT_diag_conjQ_diag, diagQ_shadow i,
    offQ_shadow (mateSeat i)]
  unfold dpWZ
  push_cast
  ring

/-- The γ-weighted A-shadow sum of the double-pulled lepton
weights vanishes (ℤ shadow at ×625, `decide`). -/
theorem dpWZ_sum_A_lep :
    ∑ i : Fin 32, dpWZ lepInd i * pi1AVal i.val = 0 := by decide

/-- The γ-weighted B-shadow sum of the double-pulled lepton
weights vanishes. -/
theorem dpWZ_sum_B_lep :
    ∑ i : Fin 32, dpWZ lepInd i * pi1BVal i.val = 0 := by decide

/-- The γ-weighted A-shadow sum of the double-pulled e_R
weights vanishes. -/
theorem dpWZ_sum_A_eR :
    ∑ i : Fin 32, dpWZ eRInd i * pi1AVal i.val = 0 := by decide

/-- The γ-weighted B-shadow sum of the double-pulled e_R
weights vanishes. -/
theorem dpWZ_sum_B_eR :
    ∑ i : Fin 32, dpWZ eRInd i * pi1BVal i.val = 0 := by decide

/-- The γ-weighted A-shadow sum of the double-pulled colour
weights vanishes, for every colour. -/
theorem dpWZ_sum_A_col (c : Fin 3) :
    ∑ i : Fin 32, dpWZ (colInd c) i * pi1AVal i.val = 0 := by
  fin_cases c <;> decide

/-- The γ-weighted B-shadow sum of the double-pulled colour
weights vanishes, for every colour. -/
theorem dpWZ_sum_B_col (c : Fin 3) :
    ∑ i : Fin 32, dpWZ (colInd c) i * pi1BVal i.val = 0 := by
  fin_cases c <;> decide

/-! ## §3. The pulled clauses at `piU`: the double pull -/

/-- **The pulled trace at `piU`, for a diagonal projection.**
Pulling `piU` back once more (the landed
`trace_gammaF_proj_piU`) turns the pulled clause at `piU` into
the trace of the double-pulled γ-weighted projection
`Qᵀ * (gammaF * P) * Q` against the diagonal `pi1` generator;
only its diagonal (the `dpWZ` shadow) enters, and both shadow
sums vanish. -/
theorem pulled_trace_piU (P : Matrix (Fin 32) (Fin 32) ℂ)
    (ind : ℕ → ℤ)
    (hP : P = Matrix.diagonal (fun i => (ind i.val : ℂ)))
    (hA : ∑ i : Fin 32, dpWZ ind i * pi1AVal i.val = 0)
    (hB : ∑ i : Fin 32, dpWZ ind i * pi1BVal i.val = 0)
    (α β : ℤ) :
    Matrix.trace (gammaF * (conjUᵀ * P * conjU) * piU (u1Gen α β))
      = 0 := by
  have hg : gammaF * conjUᵀ = conjUᵀ * gammaF :=
    ThetLogos.DialOneGradeRConj.gammaF_transpose_comm_of_class
      ThetLogos.DialOneGradeRConjPin.conjU_centralizing
  have hQ : (conjU * conjU)ᵀ = conjUᵀ * conjUᵀ :=
    Matrix.transpose_mul conjU conjU
  have hid : conjUᵀ * (gammaF * (conjUᵀ * P * conjU)) * conjU
      = (conjU * conjU)ᵀ * (gammaF * P) * (conjU * conjU) := by
    calc conjUᵀ * (gammaF * (conjUᵀ * P * conjU)) * conjU
        = conjUᵀ * ((gammaF * conjUᵀ) * P * conjU) * conjU := by
          simp only [Matrix.mul_assoc]
      _ = conjUᵀ * ((conjUᵀ * gammaF) * P * conjU) * conjU := by
          rw [hg]
      _ = (conjUᵀ * conjUᵀ) * (gammaF * P) * (conjU * conjU) := by
          simp only [Matrix.mul_assoc]
      _ = (conjU * conjU)ᵀ * (gammaF * P) * (conjU * conjU) := by
          rw [hQ]
  rw [ThetLogos.DialOnePiUFamily.trace_gammaF_proj_piU
      (conjUᵀ * P * conjU) α β, hid,
    ThetLogos.DialOneShapeBIdentification.pi1_u1Gen_diagonal,
    ThetLogos.DialOnePiUFamily.trace_mul_diagonal]
  have hterm : ∀ i : Fin 32,
      ((conjU * conjU)ᵀ * (gammaF * P) * (conjU * conjU)) i i
          * (Complex.I
            * ((pi1AVal i.val * α + pi1BVal i.val * β : ℤ) : ℂ))
        = Complex.I / 625
          * ((dpWZ ind i
              * (pi1AVal i.val * α + pi1BVal i.val * β) : ℤ) : ℂ) := by
    intro i
    rw [doublePulled_diag P ind hP]
    push_cast
    ring
  rw [Finset.sum_congr rfl (fun i _ => hterm i), ← Finset.mul_sum,
    ← Int.cast_sum]
  have hsum : ∑ i : Fin 32, dpWZ ind i
        * (pi1AVal i.val * α + pi1BVal i.val * β) = 0 := by
    have h1 : ∀ i : Fin 32, dpWZ ind i
          * (pi1AVal i.val * α + pi1BVal i.val * β)
        = (dpWZ ind i * pi1AVal i.val) * α
          + (dpWZ ind i * pi1BVal i.val) * β :=
      fun i => by ring
    rw [Finset.sum_congr rfl (fun i _ => h1 i),
      Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul,
      hA, hB]
    simp
  rw [hsum]
  simp

/-- **The pulled lepton clause of `piU` under `conjU` —
PROVED** (hypothesis `hlep` of the amended capstone at this
pair). -/
theorem pulled_lep_piU :
    ∀ α β : ℤ,
      Matrix.trace (gammaF * (conjUᵀ * lepProj * conjU)
        * piU (u1Gen α β)) = 0 :=
  fun α β => pulled_trace_piU lepProj lepInd
    ThetLogos.DialOnePiUFamily.lepProj_eq_diag
    dpWZ_sum_A_lep dpWZ_sum_B_lep α β

/-- **The pulled colour clause of `piU` under `conjU` —
PROVED** (the capstone's `hcol` at this pair). -/
theorem pulled_col_piU :
    ∀ (c : Fin 3) (α β : ℤ),
      Matrix.trace (gammaF * (conjUᵀ * colProj c * conjU)
        * piU (u1Gen α β)) = 0 :=
  fun c α β => pulled_trace_piU (colProj c) (colInd c)
    (ThetLogos.DialOnePiUFamily.colProj_eq_diag c)
    (dpWZ_sum_A_col c) (dpWZ_sum_B_col c) α β

/-- **The pulled e_R clause of `piU` under `conjU` — PROVED**
(the capstone's `heR` at this pair). -/
theorem pulled_eR_piU :
    ∀ α β : ℤ,
      Matrix.trace (gammaF * (conjUᵀ * eRProj * conjU)
        * piU (u1Gen α β)) = 0 :=
  fun α β => pulled_trace_piU eRProj eRInd
    ThetLogos.DialOnePiUFamily.eRProj_eq_diag
    dpWZ_sum_A_eR dpWZ_sum_B_eR α β

/-- **Preservation at the pair (`conjU`, `piU`)** — the
amended capstone fires with `conjU`'s amended membership,
`piU`'s landed strengthened membership, and the three pulled
clauses above. This is the `PreservationQReal` instance at
this pair; the class-level statement remains open. -/
theorem strengthened_conjRep_piU :
    DialOneStrengthenedFam (conjRep conjU piU) :=
  ThetLogos.DialOneGradeRConjAmend.strengthened_preserved_of_real_pulled
    ThetLogos.DialOneGradeRConjAmend.conjU_realCentralizing
    piU
    ThetLogos.DialOnePiUFamily.strengthened_piU
    pulled_lep_piU pulled_col_piU pulled_eR_piU

/-! ## §4. The pair (`conjU`, `conjRep conjU piAnti`): the flip -/

/-- **The third exhibited point at the generator is `piU` at
the flipped direction**: `conjRep conjU piAnti` at
`u1Gen α β` is `conjU * piAnti (u1Gen α β) * conjUᵀ`, and the
landed colour-twist flip (`piAnti_flip_u1Gen`) turns
`piAnti (u1Gen α β)` into `pi1 (u1Gen α (−β))` — the sandwich
is then `piU` at the flipped direction, by definition. -/
theorem conjRep_piAnti_gen (α β : ℤ) :
    (conjRep conjU piAnti) (u1Gen α β) = piU (u1Gen α (-β)) := by
  show conjU * piAnti (u1Gen α β) * conjUᵀ
    = piU (u1Gen α (-β))
  rw [ThetLogos.DialOnePiAntiPackage.piAnti_flip_u1Gen]
  rfl

/-- **The pulled lepton clause of `conjRep conjU piAnti`
under `conjU` — PROVED**: by `conjRep_piAnti_gen` it is
`piU`'s pulled lepton clause at the flipped direction. -/
theorem pulled_lep_conjRepPiAnti :
    ∀ α β : ℤ,
      Matrix.trace (gammaF * (conjUᵀ * lepProj * conjU)
        * (conjRep conjU piAnti) (u1Gen α β)) = 0 := by
  intro α β
  rw [conjRep_piAnti_gen]
  exact pulled_lep_piU α (-β)

/-- **The pulled colour clause of `conjRep conjU piAnti`
under `conjU` — PROVED**, same route. -/
theorem pulled_col_conjRepPiAnti :
    ∀ (c : Fin 3) (α β : ℤ),
      Matrix.trace (gammaF * (conjUᵀ * colProj c * conjU)
        * (conjRep conjU piAnti) (u1Gen α β)) = 0 := by
  intro c α β
  rw [conjRep_piAnti_gen]
  exact pulled_col_piU c α (-β)

/-- **The pulled e_R clause of `conjRep conjU piAnti` under
`conjU` — PROVED**, same route. -/
theorem pulled_eR_conjRepPiAnti :
    ∀ α β : ℤ,
      Matrix.trace (gammaF * (conjUᵀ * eRProj * conjU)
        * (conjRep conjU piAnti) (u1Gen α β)) = 0 := by
  intro α β
  rw [conjRep_piAnti_gen]
  exact pulled_eR_piU α (-β)

/-- **Preservation at the pair (`conjU`,
`conjRep conjU piAnti`)** — the amended capstone fires with
the point's landed strengthened membership
(`DialOnePiAntiPackage.strengthened_conjRep_piAnti`) and the
three pulled clauses above. The `PreservationQReal` instance
at this pair; the class-level statement remains open. -/
theorem strengthened_conjRep_conjRep_piAnti :
    DialOneStrengthenedFam (conjRep conjU (conjRep conjU piAnti)) :=
  ThetLogos.DialOneGradeRConjAmend.strengthened_preserved_of_real_pulled
    ThetLogos.DialOneGradeRConjAmend.conjU_realCentralizing
    (conjRep conjU piAnti)
    ThetLogos.DialOnePiAntiPackage.strengthened_conjRep_piAnti
    pulled_lep_conjRepPiAnti pulled_col_conjRepPiAnti
    pulled_eR_conjRepPiAnti

/-! ## §5. The pair (`conjU`, `orbitRep allSwapBits`) -/

/-! ### §5.1 The pulled clauses at `pi1` (landed, read through the iffs) -/

/-- **The pulled lepton clause at `pi1` under `conjU`** —
the landed preservation at `pi1` (`preservationAtPi1ConjU`,
i.e. `piU`'s family clauses) read back through the content
module's pulled iff. Cited, not recomputed. -/
theorem pulled_lep_pi1 :
    ∀ α β : ℤ,
      Matrix.trace (gammaF * (conjUᵀ * lepProj * conjU)
        * pi1 (u1Gen α β)) = 0 :=
  (ThetLogos.DialOneGradeRConj.c3lep_conjRep_iff
    ThetLogos.DialOneGradeRConjPin.conjU_centralizing pi1).mp
    (by
      rw [← ThetLogos.DialOneGradeRConjPin.piU_eq_conjRep]
      exact ThetLogos.DialOnePiUFamily.c3lep_piU)

/-- **The pulled colour clause at `pi1` under `conjU`**,
same read-back. -/
theorem pulled_col_pi1 :
    ∀ (c : Fin 3) (α β : ℤ),
      Matrix.trace (gammaF * (conjUᵀ * colProj c * conjU)
        * pi1 (u1Gen α β)) = 0 :=
  fun c =>
    (ThetLogos.DialOneGradeRConj.c3col_conjRep_iff
      ThetLogos.DialOneGradeRConjPin.conjU_centralizing c pi1).mp
      (by
        rw [← ThetLogos.DialOneGradeRConjPin.piU_eq_conjRep]
        exact ThetLogos.DialOnePiUFamily.c3col_piU c)

/-- **The pulled e_R clause at `pi1` under `conjU`**, same
read-back. -/
theorem pulled_eR_pi1 :
    ∀ α β : ℤ,
      Matrix.trace (gammaF * (conjUᵀ * eRProj * conjU)
        * pi1 (u1Gen α β)) = 0 :=
  (ThetLogos.DialOneGradeRConj.feR_conjRep_iff
    ThetLogos.DialOneGradeRConjPin.conjU_centralizing pi1).mp
    (by
      rw [← ThetLogos.DialOneGradeRConjPin.piU_eq_conjRep]
      exact ThetLogos.DialOnePiUFamily.feR_piU)

/-! ### §5.2 Seat lemmas for the swap correction -/

/-- The trace of a matrix against a diagonal single reads
the diagonal entry: `trace (X * single s s v) = X s s * v`. -/
theorem trace_mul_single_diag (X : Matrix (Fin 32) (Fin 32) ℂ)
    (s : Fin 32) (v : ℂ) :
    Matrix.trace (X * Matrix.single s s v) = X s s * v := by
  unfold Matrix.trace Matrix.diag
  rw [Finset.sum_eq_single s]
  · rw [Matrix.mul_apply, Finset.sum_eq_single s]
    · rw [Matrix.single_apply, if_pos ⟨rfl, rfl⟩]
    · intro k _ hk
      rw [Matrix.single_apply,
        if_neg (fun h : s = k ∧ s = s => hk h.1.symm), mul_zero]
    · intro hcon
      exact absurd (Finset.mem_univ s) hcon
  · intro i _ hi
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro k _
    rw [Matrix.single_apply,
      if_neg (fun h : s = k ∧ s = i => hi h.2.symm), mul_zero]
  · intro hcon
    exact absurd (Finset.mem_univ s) hcon

/-- The diagonal entry of `gammaF * M`: `γ` times the
diagonal entry of `M` (`gammaF` is diagonal). -/
theorem gammaF_mul_entry_diag (M : Matrix (Fin 32) (Fin 32) ℂ)
    (s : Fin 32) :
    (gammaF * M) s s = (gammaVal s.val : ℂ) * M s s := by
  rw [Matrix.mul_apply, Finset.sum_eq_single s]
  · rw [gammaF_diag_eq]
  · intro k _ hk
    rw [gammaF_apply_ne (Ne.symm hk), zero_mul]
  · intro hcon
    exact absurd (Finset.mem_univ s) hcon

/-- The γ-weighted pulled diagonal entry at a seat, for a
diagonal projection with indicator `ind`: `γ` times the
`diagC²`/`offC²` mixture of `ind` at the seat and its mate
(the pulled table of spec §1.2). -/
theorem gammaPulled_entry (P : Matrix (Fin 32) (Fin 32) ℂ)
    (ind : ℕ → ℤ)
    (hP : P = Matrix.diagonal (fun i => (ind i.val : ℂ)))
    (s : Fin 32) :
    (gammaF * (conjUᵀ * P * conjU)) s s
      = (gammaVal s.val : ℂ)
        * (diagC s * diagC s * (ind s.val : ℂ)
          + offC (mateSeat s) * offC (mateSeat s)
            * (ind (mateSeat s).val : ℂ)) := by
  rw [gammaF_mul_entry_diag, hP,
    ThetLogos.DialOnePiUFamily.conjT_diag_conjU_diag]

/-- **The pulled trace against the swap correction, as a
seat sum.** `swapCorr (u1Gen α β)` is the sum of the six
diagonal singles at `{uSeat c, dSeat c}` with coefficients
`star (α·I) − α·I = −2α·I` (uSeats) and `α·I − star (α·I)
= +2α·I` (dSeats); the trace reads the six γ-weighted pulled
diagonal entries. -/
theorem pulled_trace_swapCorr_formula
    (P : Matrix (Fin 32) (Fin 32) ℂ) (α β : ℤ) :
    Matrix.trace (gammaF * (conjUᵀ * P * conjU)
        * swapCorr (u1Gen α β))
      = ((α : ℂ) * Complex.I)
        * (2 * (((gammaF * (conjUᵀ * P * conjU)) (dSeat 0) (dSeat 0)
              - (gammaF * (conjUᵀ * P * conjU)) (uSeat 0) (uSeat 0))
            + ((gammaF * (conjUᵀ * P * conjU)) (dSeat 1) (dSeat 1)
              - (gammaF * (conjUᵀ * P * conjU)) (uSeat 1) (uSeat 1))
            + ((gammaF * (conjUᵀ * P * conjU)) (dSeat 2) (dSeat 2)
              - (gammaF * (conjUᵀ * P * conjU)) (uSeat 2) (uSeat 2)))) := by
  have hu1 : (u1Gen α β).u1 = (α : ℂ) * Complex.I := rfl
  rw [swapCorr]
  simp only [orbitCorrS, Matrix.mul_add, Matrix.trace_add,
    trace_mul_single_diag, hu1]
  rw [show star ((α : ℂ) * Complex.I) = -((α : ℂ) * Complex.I) by simp]
  ring

/-! ### §5.3 The swap-correction pulled traces vanish -/

/-- **The pulled lepton trace against `swapCorr` vanishes**:
every γ-weighted pulled lepton diagonal at the six seats
(and their mates) is `0` — the lepton indicator vanishes at
seats `10–15`, `18`, `20`. -/
theorem pulled_swapCorr_lep (α β : ℤ) :
    Matrix.trace (gammaF * (conjUᵀ * lepProj * conjU)
        * swapCorr (u1Gen α β)) = 0 := by
  rw [pulled_trace_swapCorr_formula]
  have e : ∀ c : Fin 3,
      (gammaF * (conjUᵀ * lepProj * conjU)) (dSeat c) (dSeat c)
        - (gammaF * (conjUᵀ * lepProj * conjU)) (uSeat c) (uSeat c)
        = 0 := by
    intro c
    fin_cases c <;>
      rw [gammaPulled_entry lepProj lepInd
        ThetLogos.DialOnePiUFamily.lepProj_eq_diag,
        gammaPulled_entry lepProj lepInd
          ThetLogos.DialOnePiUFamily.lepProj_eq_diag] <;>
      simp [uSeat, dSeat, mateSeat, diagC, offC, lepInd, gammaVal]
  rw [e 0, e 1, e 2]
  simp

/-- **The pulled e_R trace against `swapCorr` vanishes**:
the e_R indicator `{9, 25}` meets none of the six seats or
their mates. -/
theorem pulled_swapCorr_eR (α β : ℤ) :
    Matrix.trace (gammaF * (conjUᵀ * eRProj * conjU)
        * swapCorr (u1Gen α β)) = 0 := by
  rw [pulled_trace_swapCorr_formula]
  have e : ∀ c : Fin 3,
      (gammaF * (conjUᵀ * eRProj * conjU)) (dSeat c) (dSeat c)
        - (gammaF * (conjUᵀ * eRProj * conjU)) (uSeat c) (uSeat c)
        = 0 := by
    intro c
    fin_cases c <;>
      rw [gammaPulled_entry eRProj eRInd
        ThetLogos.DialOnePiUFamily.eRProj_eq_diag,
        gammaPulled_entry eRProj eRInd
          ThetLogos.DialOnePiUFamily.eRProj_eq_diag] <;>
      simp [uSeat, dSeat, mateSeat, diagC, offC, eRInd, gammaVal]
  rw [e 0, e 1, e 2]
  simp

/-- **The pulled colour trace against `swapCorr` vanishes**,
for every colour: the six-seat sum cancels — e.g. colour `0`:
`(−1 + 9/25) + 16/25 = 0` over the `(dSeat 0, uSeat 0, uSeat 1)`
seats and `0` elsewhere (the `16/25` is the mate-pulled entry
at seat `12` from colour-0's seat `18`). Seat values are the
pulled table `9/25 / 16/25 / 1` of spec §1.2. -/
theorem pulled_swapCorr_col (c : Fin 3) (α β : ℤ) :
    Matrix.trace (gammaF * (conjUᵀ * colProj c * conjU)
        * swapCorr (u1Gen α β)) = 0 := by
  rw [pulled_trace_swapCorr_formula]
  rw [gammaPulled_entry (colProj c) (colInd c)
      (ThetLogos.DialOnePiUFamily.colProj_eq_diag c),
    gammaPulled_entry (colProj c) (colInd c)
      (ThetLogos.DialOnePiUFamily.colProj_eq_diag c),
    gammaPulled_entry (colProj c) (colInd c)
      (ThetLogos.DialOnePiUFamily.colProj_eq_diag c),
    gammaPulled_entry (colProj c) (colInd c)
      (ThetLogos.DialOnePiUFamily.colProj_eq_diag c),
    gammaPulled_entry (colProj c) (colInd c)
      (ThetLogos.DialOnePiUFamily.colProj_eq_diag c),
    gammaPulled_entry (colProj c) (colInd c)
      (ThetLogos.DialOnePiUFamily.colProj_eq_diag c)]
  fin_cases c <;>
    simp [uSeat, dSeat, mateSeat, diagC, offC, colInd, gammaVal] <;>
    norm_num

/-! ### §5.4 The allSwap pulled clauses and assembly -/

/-- **The pulled lepton clause of `orbitRep allSwapBits`
under `conjU` — PROVED**: the point is `pi1 + swapCorr` at
the generator (`allSwap_eq`); both pulled parts vanish. -/
theorem pulled_lep_allSwap :
    ∀ α β : ℤ,
      Matrix.trace (gammaF * (conjUᵀ * lepProj * conjU)
        * orbitRep allSwapBits (u1Gen α β)) = 0 := by
  intro α β
  rw [allSwap_eq, Matrix.mul_add, Matrix.trace_add,
    pulled_lep_pi1 α β, pulled_swapCorr_lep α β, add_zero]

/-- **The pulled colour clause of `orbitRep allSwapBits`
under `conjU` — PROVED**, same split. -/
theorem pulled_col_allSwap :
    ∀ (c : Fin 3) (α β : ℤ),
      Matrix.trace (gammaF * (conjUᵀ * colProj c * conjU)
        * orbitRep allSwapBits (u1Gen α β)) = 0 := by
  intro c α β
  rw [allSwap_eq, Matrix.mul_add, Matrix.trace_add,
    pulled_col_pi1 c α β, pulled_swapCorr_col c α β, add_zero]

/-- **The pulled e_R clause of `orbitRep allSwapBits` under
`conjU` — PROVED**, same split. -/
theorem pulled_eR_allSwap :
    ∀ α β : ℤ,
      Matrix.trace (gammaF * (conjUᵀ * eRProj * conjU)
        * orbitRep allSwapBits (u1Gen α β)) = 0 := by
  intro α β
  rw [allSwap_eq, Matrix.mul_add, Matrix.trace_add,
    pulled_eR_pi1 α β, pulled_swapCorr_eR α β, add_zero]

/-- **Preservation at the pair (`conjU`,
`orbitRep allSwapBits`)** — the amended capstone fires with
the point's landed strengthened membership
(`allSwap_mem_strengthened`) and the three pulled clauses
above. The `PreservationQReal` instance at this pair; the
class-level statement remains open. -/
theorem strengthened_conjRep_allSwap :
    DialOneStrengthenedFam (conjRep conjU (orbitRep allSwapBits)) :=
  ThetLogos.DialOneGradeRConjAmend.strengthened_preserved_of_real_pulled
    ThetLogos.DialOneGradeRConjAmend.conjU_realCentralizing
    (orbitRep allSwapBits)
    allSwap_mem_strengthened
    pulled_lep_allSwap pulled_col_allSwap pulled_eR_allSwap

/-! ## §6. The sweep, assembled -/

/-- **THE P-C SWEEP — HEADLINE.** At the exhibited amended-class
member `conjU`, the strengthened family is closed under
`conjRep conjU` at every exhibited point: the two previously
landed pairs (`pi1`, via the read-back brick; `piAnti`, via the
piAnti package) and the three pairs decided here (`allSwap`,
`piU`, and `conjRep conjU piAnti` itself). **K-Q1-PRES-EXH
does not fire**: no pulled trace at any exhibited pair is
nonzero.

**Scope, verbatim:** this decides the exhibited sublattice
`{pi1, piAnti, allSwap, piU, conjRep conjU piAnti} × {conjU}`
and nothing more. The class-level `PreservationQReal`
**remains open** — the sweep is evidence at exactly the pairs
it computes, and a clean sweep must never be reported as
class-level evidence (the `U0` fence, spec §1.4). Dial 1 = 0. -/
theorem presSweep_package :
    ThetLogos.DialOneGradeRConjAmend.RealCentralizingClass conjU
      ∧ ThetLogos.DialOneGradeRConjPin.PreservationAtPi1ConjU
      ∧ DialOneStrengthenedFam (conjRep conjU piAnti)
      ∧ DialOneStrengthenedFam (conjRep conjU (orbitRep allSwapBits))
      ∧ DialOneStrengthenedFam (conjRep conjU piU)
      ∧ DialOneStrengthenedFam (conjRep conjU (conjRep conjU piAnti)) :=
  ⟨ThetLogos.DialOneGradeRConjAmend.conjU_realCentralizing,
   ThetLogos.DialOneGradeRConjReadback.preservationAtPi1ConjU,
   ThetLogos.DialOnePiAntiPackage.strengthened_conjRep_piAnti,
   strengthened_conjRep_allSwap,
   strengthened_conjRep_piU,
   strengthened_conjRep_conjRep_piAnti⟩

end ThetLogos.DialOnePresSweep

-- Axiom audit for the headlines (expected:
-- [propext, Classical.choice, Quot.sound] throughout).
#print axioms ThetLogos.DialOnePresSweep.strengthened_conjRep_allSwap
#print axioms ThetLogos.DialOnePresSweep.strengthened_conjRep_piU
#print axioms ThetLogos.DialOnePresSweep.strengthened_conjRep_conjRep_piAnti
#print axioms ThetLogos.DialOnePresSweep.presSweep_package
