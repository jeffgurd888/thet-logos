import Mathlib.Tactic
import ThetLogos.DialOneGradeRConjPin
import ThetLogos.DialOneGradeRConjAmend
import ThetLogos.DialOneAntiparticleBase

open Matrix Complex
open ThetLogos.Track1RouteB
open ThetLogos.DialOneGradeRConjPin
open ThetLogos.DialOneGradeRConjAmend
open ThetLogos.DialOneAntiparticleBase
open ThetLogos.DialOneAntiparticleChapter

namespace ThetLogos.DialOneOrbitKill

/-!
# ThetLogos.DialOneOrbitKill — Q1 brick O-A: the orbit kill (K-Q1-ORBIT-TRACE)

Scoping of record: `q1-class-level-scope-2026-11-08.md` §2 (Route O-A,
the trace separation). **NO CLAIM. Dials 0/4; Dial 1 = 0** — a
classification kill derives no measured number (§4 of the scoping).

The plain trace of a representation's values is invariant under
sandwich conjugation by ANY matrix `U` with `Uᵀ * U = 1` — a field
both classes carry by definition (`CentralizingClass`, pin) — while
`trace (piAnti a) − trace (pi1 a) = 4·(tr(a.color) − star(tr(a.color)))`,
which is `8i ≠ 0` at the exhibited witness below (`tr(a.color) = i`).
Hence `piAnti` is not in `pi1`'s orbit under the amended class, nor
under the original class, in either direction. **Kill
K-Q1-ORBIT-TRACE fires at T1 with the headline theorem below.**
-/

/-- **Trace invariance under the sandwich** (spec §2.2): only
transpose-unitarity `Uᵀ * U = 1` is spent — no class condition
(a)/(b)/(c), no reality. Re-derived here; the Form B lane's version
is not on master. -/
theorem trace_conjRep (U : Matrix (Fin 32) (Fin 32) ℂ)
    (hU : Uᵀ * U = 1) (π : AF → Matrix (Fin 32) (Fin 32) ℂ) (a : AF) :
    Matrix.trace (conjRep U π a) = Matrix.trace (π a) := by
  show Matrix.trace (U * π a * Uᵀ) = Matrix.trace (π a)
  rw [Matrix.trace_mul_comm (U * π a) Uᵀ, ← Matrix.mul_assoc, hU,
    Matrix.one_mul]

/-- **The witness** (spec §2.2): `a = ⟨0, 0, M⟩` with `M` the colour
matrix unit carrying `i` at `(0,0)`; `tr(a.color) = i`. A legitimate
element of `AF = ℂ ⊕ M₂(ℂ) ⊕ M₃(ℂ)`. -/
def witnessAF : AF :=
  ⟨0, 0, fun i j => if i = 0 ∧ j = 0 then Complex.I else 0⟩

/-- Colour-only elements of the witness's shape, seat by seat: at a
colour seat over colour `0` (seats 18, 19, 26, 27) `pi1`'s diagonal
is `star c`; every other seat vanishes (`u1 = 0`, `q = 0`, and the
colour diagonal entries at colours `1, 2` are `0`). By 32-case
exhaustion over the landed entry definition — the genus of the
landed `pi1_diag_u1Gen`. -/
theorem pi1_diag_colourOnly (c : ℂ) (i : Fin 32) :
    pi1 ⟨0, 0, fun k l => if k = 0 ∧ l = 0 then c else 0⟩ i i
      = if i.val = 18 ∨ i.val = 19 ∨ i.val = 26 ∨ i.val = 27
          then star c else 0 := by
  obtain ⟨v, hv⟩ := i
  interval_cases v <;> simp [pi1]

/-- The witness's own diagonal under `pi1`: `star i = -i` at the
four colour-`0` seats. -/
theorem pi1_diag_witness (i : Fin 32) :
    pi1 witnessAF i i
      = if i.val = 18 ∨ i.val = 19 ∨ i.val = 26 ∨ i.val = 27
          then -Complex.I else 0 := by
  show pi1 ⟨0, 0, fun k l => if k = 0 ∧ l = 0 then Complex.I else 0⟩ i i
      = if i.val = 18 ∨ i.val = 19 ∨ i.val = 26 ∨ i.val = 27
          then -Complex.I else 0
  rw [pi1_diag_colourOnly]
  split_ifs with hp
  · simp
  · rfl

/-- The twist of the witness, as an `AF` element: the colour
`(0,0)` entry is `star i = -i`, all other colour entries `0`. -/
theorem colourTwist_witness : colourTwist witnessAF
    = ⟨0, 0, fun k l => if k = 0 ∧ l = 0 then -Complex.I else 0⟩ := by
  have h3 : (colourTwist witnessAF).color
      = (fun k l => if k = 0 ∧ l = 0 then -Complex.I else 0) := by
    funext k l
    rw [ThetLogos.DialOneAntiparticleBase.colourTwist_color_apply]
    by_cases hp : k = 0 ∧ l = 0 <;> simp [witnessAF, hp]
  have h1 : (colourTwist witnessAF).u1 = 0 := rfl
  have h2 : (colourTwist witnessAF).q = 0 := rfl
  calc colourTwist witnessAF
      = ⟨(colourTwist witnessAF).u1, (colourTwist witnessAF).q,
          (colourTwist witnessAF).color⟩ := rfl
    _ = ⟨0, 0, fun k l => if k = 0 ∧ l = 0 then -Complex.I else 0⟩ := by
          rw [h1, h2, h3]

/-- The witness's diagonal under `piAnti`: through
`piAnti = pi1 ∘ colourTwist` the colour `(0,0)` entry becomes
`star i = -i` first, so `pi1`'s colour seats read `star (-i) = i`. -/
theorem piAnti_diag_witness (i : Fin 32) :
    piAnti witnessAF i i
      = if i.val = 18 ∨ i.val = 19 ∨ i.val = 26 ∨ i.val = 27
          then Complex.I else 0 := by
  have h : piAnti witnessAF
      = pi1 ⟨0, 0, fun k l => if k = 0 ∧ l = 0 then -Complex.I else 0⟩ := by
    rw [piAnti_eq_pi1_colourTwist, colourTwist_witness]
  rw [h, pi1_diag_colourOnly]
  split_ifs with hp
  · simp
  · rfl

/-- `trace (pi1 witness) = -4i`: four seats of `star i`. -/
theorem trace_pi1_witness :
    Matrix.trace (pi1 witnessAF) = -4 * Complex.I := by
  show (∑ i : Fin 32, pi1 witnessAF i i) = -4 * Complex.I
  rw [Finset.sum_congr rfl (fun i _ => pi1_diag_witness i)]
  rw [Fin.sum_univ_eq_sum_range
    (fun n => if n = 18 ∨ n = 19 ∨ n = 26 ∨ n = 27
      then -Complex.I else 0) 32]
  norm_num [Finset.sum_range_succ]
  ring

/-- `trace (piAnti witness) = 4i`: four seats of `star (star i)`. -/
theorem trace_piAnti_witness :
    Matrix.trace (piAnti witnessAF) = 4 * Complex.I := by
  show (∑ i : Fin 32, piAnti witnessAF i i) = 4 * Complex.I
  rw [Finset.sum_congr rfl (fun i _ => piAnti_diag_witness i)]
  rw [Fin.sum_univ_eq_sum_range
    (fun n => if n = 18 ∨ n = 19 ∨ n = 26 ∨ n = 27
      then Complex.I else 0) 32]
  norm_num [Finset.sum_range_succ]
  ring

/-- The two trace functionals differ at the witness — the
separation the whole brick rests on:
`trace (piAnti a) − trace (pi1 a) = 8i ≠ 0` there. -/
theorem trace_piAnti_ne_pi1_witness :
    Matrix.trace (piAnti witnessAF) ≠ Matrix.trace (pi1 witnessAF) := by
  rw [trace_piAnti_witness, trace_pi1_witness]
  intro h
  have h8 : (8 : ℂ) * Complex.I = 0 := by linear_combination h
  exact mul_ne_zero (by norm_num) Complex.I_ne_zero h8

/-- **THE KILL — K-Q1-ORBIT-TRACE fires (amended class).**
`piAnti` is NOT in `pi1`'s orbit under `RealCentralizingClass`:
the frozen statement of the scoping (§2.1), verbatim. -/
theorem piAnti_not_in_real_orbit :
    ¬ ∃ U, RealCentralizingClass U ∧ piAnti = conjRep U pi1 := by
  rintro ⟨U, hU, hEq⟩
  apply trace_piAnti_ne_pi1_witness
  have htr := trace_conjRep U hU.1.2.1 pi1 witnessAF
  rw [← htr]
  exact congrArg Matrix.trace (congrFun hEq witnessAF)

/-- The kill in the pin's own packaging: `¬ PiAntiOrbitQReal`
(Amend:168) — definitionally the headline above. -/
theorem not_piAntiOrbitQReal : ¬ PiAntiOrbitQReal :=
  piAnti_not_in_real_orbit

/-- **The kill on the original class, free** (spec §2.2): the
invariance spends only `Uᵀ * U = 1`, which `CentralizingClass`
also carries by definition. `¬ PiAntiOrbitQ` (Pin:168). -/
theorem not_piAntiOrbitQ : ¬ PiAntiOrbitQ := by
  rintro ⟨U, hU, hEq⟩
  apply trace_piAnti_ne_pi1_witness
  have htr := trace_conjRep U hU.2.1 pi1 witnessAF
  rw [← htr]
  exact congrArg Matrix.trace (congrFun hEq witnessAF)

/-- **The reverse direction dies identically** (spec §2.1/§2.2):
`pi1` is not a conjugate of `piAnti` by any amended-class member
either — the invariant is direction-blind. -/
theorem pi1_not_in_real_orbit_of_piAnti :
    ¬ ∃ U, RealCentralizingClass U ∧ pi1 = conjRep U piAnti := by
  rintro ⟨U, hU, hEq⟩
  apply trace_piAnti_ne_pi1_witness
  have htr := trace_conjRep U hU.1.2.1 piAnti witnessAF
  rw [← htr]
  exact (congrArg Matrix.trace (congrFun hEq witnessAF)).symm

end ThetLogos.DialOneOrbitKill
