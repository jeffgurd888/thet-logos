import Mathlib.Tactic
import ThetLogos.DialOneGradeRConjAmend
import ThetLogos.DialOnePiUFamily
import ThetLogos.DialOneAntiparticleBase

open Matrix Complex
open ThetLogos.Track1RouteB
open ThetLogos.PreOptionARepresentation
open ThetLogos.HyperchargeForcing
open ThetLogos.DialOneSeatTiePin
open ThetLogos.DialOneGammaTracePin
open ThetLogos.DialOneGammaFamilyPin
open ThetLogos.DialOneGradeRConjPin
open ThetLogos.DialOneConjugationCounterexample
open ThetLogos.DialOneAntiparticleChapter

namespace ThetLogos.DialOnePiAntiPackage

/-!
# ThetLogos.DialOnePiAntiPackage — the piAnti closure at the exhibited member, on the AMENDED class

The Dial-1 chapter's remaining `piAnti` questions, decided
at T1 for the amended class's exhibited member `conjU`
(`RealCentralizingClass conjU`, landed as
`DialOneGradeRConjAmend.conjU_realCentralizing`).
Enrolled under Jeff's "build all you can"
(2026-11-07 20:26 EST) as the piAnti package; priced S–M.

## The three questions, and their verdicts

1. **The orbit question at the exhibited witness**
   (`PiAntiOrbitQReal`, stated in
   `DialOneGradeRConjAmend`, asks for SOME real class
   member conjugating `pi1` to `piAnti`): at the
   exhibited witness the answer is **FALSE** —
   `piAnti ≠ conjRep conjU pi1`
   (`piAnti_ne_conjRep_conjU_pi1` below). The deciding
   computation is one diagonal entry at `u1Gen 0 1`,
   seat `⟨2⟩`: `piAnti` gives `0` (its β-table vanishes
   at seat 2), while `conjRep conjU pi1 = piU` gives
   `-(16/25) * I` (the `diagC`/`offC` mixture over the
   mate pair `{2, 28}`: `(3/5)² • 0 + (4/5)² • (-I)`).
   **The class-level `PiAntiOrbitQReal` remains OPEN**:
   this decides its exhibited-witness instance only; no
   other real class member is landed, and none is
   excluded here. The companion positive also lands:
   `piU` IS in the amended orbit of `pi1`, at the same
   witness (`gaugeConjReal_pi1_piU`).

2. **Gap (β) for `piAnti` under `conjU`** — the three
   pulled clauses of the amended capstone: **all three
   PROVED** (`pulled_lep_piAnti_conjU`,
   `pulled_col_piAnti_conjU`, `pulled_eR_piAnti_conjU`).
   The deciding computation is exact, not numerical:
   the pulled trace at direction `(α, β)` is, by
   γ_F-transpose commutation (`gammaF * Uᵀ = Uᵀ * γ_F`
   on the class) and trace cyclicity
   (`trace_conjU_sandwich`), equal to `piU`'s own
   clause at the flipped direction `(α, -β)` — the
   flip being the landed colour-twist identity
   `piAnti (u1Gen α β) = pi1 (u1Gen α (-β))` — and
   `piU`'s three clauses are landed
   (`c3lep_piU` / `c3col_piU` / `feR_piU`).

3. **Assembly**: with all three pulled clauses in hand,
   the amended capstone
   (`DialOneGradeRConjAmend.strengthened_preserved_of_real_pulled`)
   fires: **`DialOneStrengthenedFam (conjRep conjU
   piAnti)`** (`strengthened_conjRep_piAnti`) —
   `piAnti`'s strengthened membership, transported to
   the conjugate representation.

## What the package does and does not give, stated plainly

The transport (3) and the orbit verdict (1) are about
DIFFERENT points: (3) says the conjugate OF `piAnti`
stays in the strengthened family; (1) says `piAnti` is
not the conjugate OF `pi1` at the exhibited witness.
Together: under the exhibited amended-class action,
`pi1 ↦ piU` (in family, by the read-back brick) and
`piAnti ↦ conjRep conjU piAnti` (in family, here), and
`piAnti` does not lie on `pi1`'s orbit at this witness.
Class-level `PreservationQReal` and class-level
`PiAntiOrbitQReal` both remain OPEN, exactly as the
amendment module left them.

## Fences

NO CLAIM. Dial 1 = 0: orbit and transport facts about
the classification derive no measured number. No
`axiom` declarations; no sorrys.
-/

/-- **The colour-twist flip at the generator** (landed
route, restated for this package): `piAnti` at
direction `(α, β)` is `pi1` at the flipped direction
`(α, -β)`. -/
theorem piAnti_flip_u1Gen (α β : ℤ) :
    piAnti (u1Gen α β) = pi1 (u1Gen α (-β)) := by
  rw [ThetLogos.DialOneAntiparticleBase.piAnti_eq_pi1_colourTwist,
    ThetLogos.DialOneAntiparticleBase.colourTwist_u1Gen]

/-! ## The transported traces at the conjugate of `piAnti` -/

/-- **The lepton trace at `conjRep conjU piAnti`**:
by trace cyclicity (`trace_conjU_sandwich`) this is
the pulled trace at `piAnti`, which the γ_F-transpose
identity rewrites as `piU`'s lepton trace at the
flipped direction — landed, hence `0`. -/
theorem trace_gammaF_lep_conjRep_piAnti (α β : ℤ) :
    Matrix.trace (gammaF * lepProj
      * (conjRep conjU piAnti) (u1Gen α β)) = 0 := by
  rw [show (conjRep conjU piAnti) (u1Gen α β)
      = conjU * piAnti (u1Gen α β) * conjUᵀ from rfl,
    ThetLogos.DialOnePiUFamily.trace_conjU_sandwich, piAnti_flip_u1Gen,
    ← ThetLogos.DialOnePiUFamily.trace_gammaF_proj_piU]
  exact ThetLogos.DialOnePiUFamily.c3lep_piU α (-β)

/-- **The colour trace at `conjRep conjU piAnti`**,
same route as the lepton trace. -/
theorem trace_gammaF_col_conjRep_piAnti (c : Fin 3) (α β : ℤ) :
    Matrix.trace (gammaF * colProj c
      * (conjRep conjU piAnti) (u1Gen α β)) = 0 := by
  rw [show (conjRep conjU piAnti) (u1Gen α β)
      = conjU * piAnti (u1Gen α β) * conjUᵀ from rfl,
    ThetLogos.DialOnePiUFamily.trace_conjU_sandwich, piAnti_flip_u1Gen,
    ← ThetLogos.DialOnePiUFamily.trace_gammaF_proj_piU]
  exact ThetLogos.DialOnePiUFamily.c3col_piU c α (-β)

/-- **The e_R trace at `conjRep conjU piAnti`**, same
route as the lepton trace. -/
theorem trace_gammaF_eR_conjRep_piAnti (α β : ℤ) :
    Matrix.trace (gammaF * eRProj
      * (conjRep conjU piAnti) (u1Gen α β)) = 0 := by
  rw [show (conjRep conjU piAnti) (u1Gen α β)
      = conjU * piAnti (u1Gen α β) * conjUᵀ from rfl,
    ThetLogos.DialOnePiUFamily.trace_conjU_sandwich, piAnti_flip_u1Gen,
    ← ThetLogos.DialOnePiUFamily.trace_gammaF_proj_piU]
  exact ThetLogos.DialOnePiUFamily.feR_piU α (-β)

/-- **C3lep transports to the conjugate of `piAnti`**
(the named clause form of the lepton trace above). -/
theorem c3lep_conjRep_piAnti :
    C3lep (conjRep conjU piAnti) :=
  fun α β => trace_gammaF_lep_conjRep_piAnti α β

/-- **C3col transports to the conjugate of `piAnti`**. -/
theorem c3col_conjRep_piAnti (c : Fin 3) :
    C3col c (conjRep conjU piAnti) :=
  fun α β => trace_gammaF_col_conjRep_piAnti c α β

/-- **FeR transports to the conjugate of `piAnti`**. -/
theorem feR_conjRep_piAnti :
    FeR (conjRep conjU piAnti) :=
  fun α β => trace_gammaF_eR_conjRep_piAnti α β

/-! ## Gap (β) at the pair (`conjU`, `piAnti`): the pulled clauses -/

/-- **The pulled lepton clause of `piAnti` under
`conjU` — PROVED.** This is hypothesis `hlep` of the
amended capstone at this pair, obtained from the
transported trace by the content module's pulled
reduction (`pulled_clause_transport`). -/
theorem pulled_lep_piAnti_conjU :
    ∀ α β : ℤ,
      Matrix.trace (gammaF * (conjUᵀ * lepProj * conjU)
        * piAnti (u1Gen α β)) = 0 :=
  (ThetLogos.DialOneGradeRConj.pulled_clause_transport
    ThetLogos.DialOneGradeRConjPin.conjU_centralizing
    lepProj piAnti).mp
    (fun α β => trace_gammaF_lep_conjRep_piAnti α β)

/-- **The pulled colour clause of `piAnti` under
`conjU` — PROVED** (the capstone's `hcol` at this
pair). -/
theorem pulled_col_piAnti_conjU :
    ∀ (c : Fin 3) (α β : ℤ),
      Matrix.trace (gammaF * (conjUᵀ * colProj c * conjU)
        * piAnti (u1Gen α β)) = 0 :=
  fun c =>
    (ThetLogos.DialOneGradeRConj.pulled_clause_transport
      ThetLogos.DialOneGradeRConjPin.conjU_centralizing
      (colProj c) piAnti).mp
      (fun α β => trace_gammaF_col_conjRep_piAnti c α β)

/-- **The pulled e_R clause of `piAnti` under `conjU`
— PROVED** (the capstone's `heR` at this pair). -/
theorem pulled_eR_piAnti_conjU :
    ∀ α β : ℤ,
      Matrix.trace (gammaF * (conjUᵀ * eRProj * conjU)
        * piAnti (u1Gen α β)) = 0 :=
  (ThetLogos.DialOneGradeRConj.pulled_clause_transport
    ThetLogos.DialOneGradeRConjPin.conjU_centralizing
    eRProj piAnti).mp
    (fun α β => trace_gammaF_eR_conjRep_piAnti α β)

/-! ## The assembly: preservation at the pair (`conjU`, `piAnti`) -/

/-- **HEADLINE — preservation at the pair (`conjU`,
`piAnti`) on the amended class.** The amended
capstone fires with `conjU`'s amended membership,
`piAnti`'s landed strengthened membership, and the
three pulled clauses above: the conjugate of
`piAnti` by `conjU` is in the strengthened family.
This is the `PreservationQReal` instance at this
pair; the class-level statement remains open. -/
theorem strengthened_conjRep_piAnti :
    DialOneStrengthenedFam (conjRep conjU piAnti) :=
  ThetLogos.DialOneGradeRConjAmend.strengthened_preserved_of_real_pulled
    ThetLogos.DialOneGradeRConjAmend.conjU_realCentralizing
    piAnti
    ThetLogos.DialOneAntiparticleBase.strengthenedFam_piAnti
    pulled_lep_piAnti_conjU pulled_col_piAnti_conjU
    pulled_eR_piAnti_conjU

/-! ## The orbit question at the exhibited witness -/

/-- **`piAnti`'s diagonal entry at seat `⟨2⟩`,
`u1Gen 0 1`: `0`** — its β-table vanishes at seat 2
(`piAntiBVal 2 = 0`), by the landed diagonal formula. -/
theorem piAnti_entry_two :
    piAnti (u1Gen 0 1) ⟨2, by norm_num⟩ ⟨2, by norm_num⟩ = 0 := by
  rw [ThetLogos.DialOneAntiparticleChapter.piAnti_diag_u1Gen]
  simp [ThetLogos.DialOneAntiparticleChapter.piAntiBVal]

/-- **`piU`'s diagonal entry at seat `⟨2⟩`, `u1Gen 0
1`: `-(16/25) * I`** — the conjugate of `pi1`'s
diagonal mixes seat 2 (β-weight `0`) with its mate
28 (β-weight `-1`) through `diagC 2 = 3/5`,
`offC 2 = 4/5`: `(3/5)² • 0 + (4/5)² • (-I)`. -/
theorem piU_entry_two :
    piU (u1Gen 0 1) ⟨2, by norm_num⟩ ⟨2, by norm_num⟩
      = -((16 / 25 : ℂ)) * Complex.I := by
  have hD : pi1 (u1Gen 0 1)
      = Matrix.diagonal
        (fun i => Complex.I * ((pi1BVal i.val : ℤ) : ℂ)) := by
    rw [ThetLogos.DialOneShapeBIdentification.pi1_u1Gen_diagonal]
    congr 1
    funext i
    simp
  have e : piU (u1Gen 0 1)
      = conjU * (pi1 (u1Gen 0 1) * conjUᵀ) := Matrix.mul_assoc _ _ _
  have hmate : conjU ⟨2, by norm_num⟩ ⟨28, by norm_num⟩
      = offC ⟨2, by norm_num⟩ := by
    rw [← ThetLogos.DialOneConjugationCounterexample.mateSeat_two]
    exact conjU_apply_mate _ (by decide)
  rw [e, hD, conjU_mul_apply,
    ThetLogos.DialOneConjugationCounterexample.mateSeat_two,
    Matrix.diagonal_mul, Matrix.diagonal_mul,
    Matrix.transpose_apply, Matrix.transpose_apply,
    conjU_apply_diag, hmate]
  simp only [pi1BVal]
  norm_num [diagC, offC]
  ring

/-- **`piAnti ≠ piU`** — the seat-`⟨2⟩` entry at
`u1Gen 0 1` decides it: `0` against `-(16/25) * I`. -/
theorem piAnti_ne_piU : piAnti ≠ piU := by
  intro h
  have hentry := congrArg
    (fun M : Matrix (Fin 32) (Fin 32) ℂ =>
      M ⟨2, by norm_num⟩ ⟨2, by norm_num⟩)
    (congrFun h (u1Gen 0 1))
  rw [piAnti_entry_two, piU_entry_two] at hentry
  norm_num [Complex.ext_iff] at hentry

/-- **THE ORBIT VERDICT AT THE EXHIBITED WITNESS —
FALSE.** `piAnti` is not the conjugate of `pi1` by
`conjU`: by the pin's read-back that conjugate is
`piU`, and `piAnti ≠ piU`. This decides the
`PiAntiOrbitQReal` question at the one exhibited
amended-class member; the class-level statement
(quantifying over all real class members) remains
OPEN — no other member is landed or excluded. -/
theorem piAnti_ne_conjRep_conjU_pi1 :
    piAnti ≠ conjRep conjU pi1 := by
  rw [← ThetLogos.DialOneGradeRConjPin.piU_eq_conjRep]
  exact piAnti_ne_piU

/-- **The companion positive**: `piU` IS in the
amended gauge orbit of `pi1`, witnessed by `conjU`
itself (its amended membership plus the pin's
read-back). -/
theorem gaugeConjReal_pi1_piU :
    ThetLogos.DialOneGradeRConjAmend.GaugeConjReal pi1 piU :=
  ⟨conjU, ThetLogos.DialOneGradeRConjAmend.conjU_realCentralizing,
   ThetLogos.DialOneGradeRConjPin.piU_eq_conjRep⟩

/-- **THE PACKAGE, assembled**: at the exhibited
amended-class member `conjU` — its membership holds;
`piAnti`'s strengthened membership transports to its
conjugate; `piAnti` is NOT `pi1`'s conjugate at this
witness; and `pi1`'s amended orbit does contain
`piU`. -/
theorem piAnti_package :
    ThetLogos.DialOneGradeRConjAmend.RealCentralizingClass conjU
      ∧ DialOneStrengthenedFam (conjRep conjU piAnti)
      ∧ piAnti ≠ conjRep conjU pi1
      ∧ ThetLogos.DialOneGradeRConjAmend.GaugeConjReal pi1 piU :=
  ⟨ThetLogos.DialOneGradeRConjAmend.conjU_realCentralizing,
   strengthened_conjRep_piAnti,
   piAnti_ne_conjRep_conjU_pi1,
   gaugeConjReal_pi1_piU⟩

end ThetLogos.DialOnePiAntiPackage

-- Axiom audit for the headlines (expected:
-- [propext, Classical.choice, Quot.sound] throughout).
#print axioms ThetLogos.DialOnePiAntiPackage.strengthened_conjRep_piAnti
#print axioms ThetLogos.DialOnePiAntiPackage.pulled_lep_piAnti_conjU
#print axioms ThetLogos.DialOnePiAntiPackage.pulled_col_piAnti_conjU
#print axioms ThetLogos.DialOnePiAntiPackage.pulled_eR_piAnti_conjU
#print axioms ThetLogos.DialOnePiAntiPackage.piAnti_ne_conjRep_conjU_pi1
#print axioms ThetLogos.DialOnePiAntiPackage.piAnti_package
