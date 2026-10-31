import Mathlib.Tactic
import ThetLogos.Q7C4R4Trifecta
import ThetLogos.ThermalZ4KMS
import ThetLogos.ThermalZ4ClockDefect
import ThetLogos.Q7C4R4Spectrum
import ThetLogos.ModularTime

namespace ThetLogos

/-!
# ThetLogos.Q7C4R4SecondLeg — T-C4-1: the W1 (section-form) test at the C⁴ seat

**Status: TEST EXECUTED — K-T-C4-1 FIRES at full rank. NO CLAIM.
Dials 0/4. No measured number.** Governing pack:
`routeb-general-scratch/pack-t-c4-1.md`; governing scoping:
`scoping-q7c4r4-trifecta-2026-10-30.md` (§2.2's W1 registration,
§3's analysis, §4's T-C4-1 line and K-T-C4-1); registration:
`ThetLogos.Q7C4R4Trifecta` (Q7CR-T0), which stays untouched as
the record.

## W1's registered statement, quoted verbatim

From `ThetLogos.Q7C4R4Trifecta` (definition and its docstring):

```
def SecondW1Section
    (quarterSample shift : (Fin 4 → ℂ) → (Fin 4 → ℂ)) : Prop :=
  quarterSample = shift ∧
    ∀ x : Fin 4 → ℂ, (shift ∘ shift ∘ shift ∘ shift) x = x
```

> **W1, the C⁴ leg's section form, as a schema** over two
> variables on the C⁴ factor: a quarter-period sample
> `quarterSample` of a modular flow, and a shift `shift`. The
> section claim is that the sample IS the shift, and that the
> shift has the Z₄ order (fourfold iterate = identity). The flow
> itself, its seat, and the spectral lattice condition under which
> sampling could close are NOT owned objects on the composite
> today; the instantiated form awaits Q7CR-0's seats and Q7CR-2's
> spectrum. Seat-scoped: a failure at a seat kills W1 at that seat
> only.

The memo's test design (§2.2), quoted: "At a *named* seat whose
modular spectrum satisfies stated lattice conditions, the modular
flow sampled at quarter-period steps restricts to the Z₄ shift
action on the C⁴ factor. Statable, falsifiable, and expected to
fail at generic seats." Pre-registered kill **K-T-C4-1**: "the
section identity fails at the seat ⇒ W1 dead at that seat."

## The seats and the objects, in owned vocabulary only

- **The shift** is the corpus's owned clock turn `z4Shift`
  (`ThetLogos.ThermalZ4ClockDefect`, T2), in its action on the
  factor: `z4ShiftOp x k = x (z4Shift k)` — the same action that
  module lands on weights as `z4ShiftedWeight`.
- **The modular sample** is the vector-level implementation of
  the corpus's eigenbasis modular flow: `diagFlow w s`
  (`ThetLogos.ModularTime`, T1) is conjugation by the diagonal
  unitary of the phases `cpowI (w j) s`; that unitary acts on
  vectors `x : Fin 4 → ℂ` by pointwise phase multiplication,
  `modSample w s x k = cpowI (w k) s * x k`. This is the only
  vector-level sample the owned flow has.
- **Seat 1 — the Z4 ladder Gibbs seat** (Q7CR-0's C⁴ raw
  material, seated by `ThetLogos.ThermalZ4KMS`): weights
  `w = z4Weight β`, the Gibbs weights of `z4Generator`.
- **Seat 2 — the composite's C⁴ factor seat** (Q7CR-2,
  `ThetLogos.Q7C4R4Spectrum`): `factorC4`, whose square is the
  diagonal of `(d₄ k)^2` (`factorC4_D_sq_apply`); its Gibbs
  weights are `c4FactorWeight β` below.

## The deciding facts

- **(a) The shift DOES have Z4 order** (`z4ShiftOp_order_four`):
  the second conjunct of the registered Prop holds for the owned
  shift. The kill below is therefore exactly the first conjunct —
  the section identity — and nothing else.
- **(b) Diagonal-vs-permutation obstruction** (`w1_section_fails`):
  for EVERY weight function `w` and EVERY sample time `s`, the
  modular sample is NOT the shift. The sample multiplies the
  basis line at site `0` by the phase `cpowI (w 0) s`, which is
  never zero (`Complex.exp_ne_zero`), so it keeps the basis
  vector at site `0` supported at site `0`; the shift moves that
  support to site `1`, where its value at site `0` is `0`. No
  spectral tuning can repair this: tuning changes the phases,
  and the obstruction is not in the phases — it is that the flow
  at any diagonal seat fixes every site line, while the shift
  permutes them. The spectral lattice condition the memo prices
  is therefore moot at these seats: even a perfectly tuned sample
  is a diagonal phase action, never the cyclic permutation.
- **(c) The tuning is in fact perfect at the ladder seat, and it
  does not help** (`ladder_quarter_phase_step`): at the quarter
  period `s = 2π/β` (`β ≠ 0`), each within-ladder step multiplies
  the phase by exactly `-I` — the primitive 4th root the quarter
  lattice asks for. The sample's relative phases cycle with
  period exactly 4 in the rung index — and the sample is still
  diagonal, hence still not the shift, by (b).
- **(d) Stationarity corroboration, observable form**
  (§5): the landed `gibbsWeight_stationary`
  (`ThetLogos.KMSBridge`, T1) fixes the ladder seat's Gibbs state
  under the flow at every time `s`
  (`gibbsState_z4_stationary`), while the shift reindexing moves
  that same state (`obsShift_gibbsState_ne`, from the landed
  `z4_gibbsState_eq` and `z4Weight_step_ratio` at `β > 0` — the
  same fact `ThetLogos.ThermalZ4ClockDefect` packages as
  `z4_clock_not_invariant`). So the observable-level reading of
  the section identity fails at the ladder seat too
  (`w1_observable_form_fails`).

## Verdict

**K-T-C4-1 FIRES at full rank: W1, in its registered form
`SecondW1Section`, is FALSE at the C⁴ seat — at the Z4 ladder
Gibbs seat and at the composite's C⁴ factor seat, at every
sample time, including the exactly tuned quarter period.** The
registered Prop is not narrowed here and no re-registration is
attempted: a statement that must be changed to survive is a kill,
recorded as such. (The general lemma (b) is stated for arbitrary
weights and times because that is what the mathematics gives;
the verdict is registered at the two named owned seats only, per
the seat-scope discipline.)

**The leg's resulting status, stated exactly:** the C⁴ / Second
leg's strong form stands REFUTED-AS-STATED (T0, unchanged); W1
(section form) is DEAD at the C⁴ seat in its registered form
(this brick); W2 (grading form, `LegSecondArrow`) is UNTOUCHED
by this brick in either direction and untested until T-C4-2; the
W3 floor (pure definition) is not engaged while W2 stands
untested. The trifecta assignment itself is Jeff's registered
DATA; this brick tests one leg's stated consequence only, and no
outcome here promotes the assignment.
-/

/-! ## §1. The owned Z4 shift action on the factor -/

/-- The Z4 shift action on the C⁴ factor: the owned clock turn
    `z4Shift` acting on vectors by precomposition — the same
    action `ThetLogos.ThermalZ4ClockDefect` lands on weights as
    `z4ShiftedWeight`. Tier T2 (definition). -/
def z4ShiftOp : (Fin 4 → ℂ) → (Fin 4 → ℂ) :=
  fun x k => x (z4Shift k)

/-- Pointwise formula for the shift action. Tier T1. -/
theorem z4ShiftOp_apply (x : Fin 4 → ℂ) (k : Fin 4) :
    z4ShiftOp x k = x (z4Shift k) :=
  rfl

/-- The clock turn at site `0` lands at site `1`. Tier T1. -/
theorem z4Shift_zero : z4Shift (0 : Fin 4) = 1 := rfl

/-- Four clock turns are the identity on `Fin 4`. Tier T1. -/
theorem z4Shift_iter4 (k : Fin 4) :
    z4Shift (z4Shift (z4Shift (z4Shift k))) = k := by
  fin_cases k <;> rfl

/-- **Deciding fact (a):** the owned shift has exact Z4 order as
    an operator — the second conjunct of the registered W1 Prop
    HOLDS for `z4ShiftOp`. Tier T1. -/
theorem z4ShiftOp_order_four (x : Fin 4 → ℂ) :
    (z4ShiftOp ∘ z4ShiftOp ∘ z4ShiftOp ∘ z4ShiftOp) x = x := by
  funext k
  show x (z4Shift (z4Shift (z4Shift (z4Shift k)))) = x k
  rw [z4Shift_iter4]

/-! ## §2. The modular sample and the obstruction -/

/-- The modular sample at time `s` of the eigenbasis flow with
    weights `w`: the diagonal unitary implementing `diagFlow w s`
    acting on vectors by pointwise phase multiplication,
    `(modSample w s x) k = cpowI (w k) s * x k`. Tier T2
    (definition). -/
noncomputable def modSample (w : Fin 4 → ℝ) (s : ℝ) :
    (Fin 4 → ℂ) → (Fin 4 → ℂ) :=
  fun x k => cpowI (w k) s * x k

/-- Pointwise formula for the modular sample. Tier T1. -/
theorem modSample_apply (w : Fin 4 → ℝ) (s : ℝ) (x : Fin 4 → ℂ)
    (k : Fin 4) :
    modSample w s x k = cpowI (w k) s * x k :=
  rfl

/-- The modular phases never vanish: `cpowI` is a complex
    exponential. Tier T1. -/
theorem cpowI_ne_zero' (w s : ℝ) : cpowI w s ≠ 0 :=
  Complex.exp_ne_zero _

/-- The site-`0` basis vector: `1` at site `0`, `0` elsewhere.
    Tier T2 (definition). -/
def siteZeroVec : Fin 4 → ℂ :=
  fun k => if k = 0 then 1 else 0

/-- **Deciding fact (b) — the obstruction, at full generality:**
    for every weight function `w : Fin 4 → ℝ` and every sample
    time `s : ℝ`, the registered W1 section identity FAILS for
    the modular sample against the owned shift: the sample keeps
    `siteZeroVec` supported at site `0` with the nonzero value
    `cpowI (w 0) s`, while the shift's value there is `0`. The
    section's registered first conjunct is what dies; the
    shift's order (fact (a)) is untouched. Tier T1. -/
theorem w1_section_fails (w : Fin 4 → ℝ) (s : ℝ) :
    ¬ SecondW1Section (modSample w s) z4ShiftOp := by
  intro h
  have hEq := congrFun (congrFun h.1 siteZeroVec) 0
  rw [modSample_apply, z4ShiftOp_apply, z4Shift_zero] at hEq
  have hL : cpowI (w 0) s * siteZeroVec 0 ≠ 0 := by
    have hv : siteZeroVec 0 = 1 := rfl
    rw [hv, mul_one]
    exact cpowI_ne_zero' _ _
  have hR : siteZeroVec (1 : Fin 4) = 0 := rfl
  rw [hR] at hEq
  exact hL hEq

/-! ## §3. Seat 1 — the Z4 ladder Gibbs seat -/

/-- **K-T-C4-1 at the ladder seat:** W1's registered section
    identity fails at the Z4 ladder Gibbs seat, at every inverse
    temperature and every sample time. Tier T1. -/
theorem w1_fails_ladder_seat (β s : ℝ) :
    ¬ SecondW1Section (modSample (z4Weight β) s) z4ShiftOp :=
  w1_section_fails _ _

/-- **Deciding fact (c) — the quarter tuning is exact at the
    ladder seat:** at sample time `s = 2π/β` (`β ≠ 0`) — the
    quarter of the flow's period `8π/β`, read off the ladder's
    log-weight differences `-β/4` per rung — each within-ladder
    step multiplies the modular phase by exactly `-I`, the
    primitive 4th root of unity. The spectral lattice condition
    the registration prices is SATISFIED here, in its strongest
    form; the section still fails, by fact (b), because the
    tuned sample is diagonal. Tier T1. -/
theorem ladder_quarter_phase_step {β : ℝ} (hβ : β ≠ 0) (k : Fin 3) :
    cpowI (z4Weight β k.succ) (2 * Real.pi / β)
      = (-Complex.I)
        * cpowI (z4Weight β (Fin.castSucc k)) (2 * Real.pi / β) := by
  have hlog : Real.log (z4Weight β k.succ)
      = Real.log (z4Weight β (Fin.castSucc k)) + (-β / 4) := by
    rw [z4Weight_step_ratio, Real.log_mul (z4Weight_pos β _).ne'
      (Real.exp_pos _).ne', Real.log_exp]
  have hexp : Complex.exp (Complex.I * ((2 * Real.pi / β : ℝ) : ℂ)
        * ((-β / 4 : ℝ) : ℂ)) = -Complex.I := by
    have hβc : (β : ℂ) ≠ 0 := by exact_mod_cast hβ
    have harg : Complex.I * ((2 * Real.pi / β : ℝ) : ℂ)
          * ((-β / 4 : ℝ) : ℂ)
        = -(↑Real.pi / 2 * Complex.I) := by
      push_cast
      field_simp
      ring
    rw [harg, Complex.exp_neg, Complex.exp_pi_div_two_mul_I,
      Complex.inv_I]
  have hsplit : Complex.I * ((2 * Real.pi / β : ℝ) : ℂ)
        * ((Real.log (z4Weight β k.succ) : ℝ) : ℂ)
      = Complex.I * ((2 * Real.pi / β : ℝ) : ℂ)
          * ((Real.log (z4Weight β (Fin.castSucc k)) : ℝ) : ℂ)
        + Complex.I * ((2 * Real.pi / β : ℝ) : ℂ)
          * ((-β / 4 : ℝ) : ℂ) := by
    rw [hlog]
    push_cast
    ring
  unfold cpowI
  rw [hsplit, Complex.exp_add, hexp]
  ring

/-- **K-T-C4-1 at the ladder seat, at the quarter period
    itself:** even the exactly tuned quarter-period sample is
    not the shift. Tier T1. -/
theorem w1_fails_ladder_quarter {β : ℝ} (_hβ : β ≠ 0) :
    ¬ SecondW1Section (modSample (z4Weight β) (2 * Real.pi / β))
      z4ShiftOp :=
  w1_section_fails _ _

/-! ## §4. Seat 2 — the composite's C⁴ factor seat -/

/-- The Gibbs weights of the composite's C⁴ factor at inverse
    temperature `β`: the normalized exponentials of
    `-β * (d₄ k)^2`, where `(d₄ k)^2` is the eigenvalue of
    `factorC4.D ^ 2` at site `k` (landed as
    `factorC4_D_sq_apply`, Q7CR-2). Tier T2 (definition). -/
noncomputable def c4FactorWeight (β : ℝ) (k : Fin 4) : ℝ :=
  Real.exp (-β * (d₄ k) ^ 2)
    / ∑ j : Fin 4, Real.exp (-β * (d₄ j) ^ 2)

/-- The factor seat's Gibbs weights are strictly positive.
    Tier T1. -/
theorem c4FactorWeight_pos (β : ℝ) (k : Fin 4) :
    0 < c4FactorWeight β k :=
  div_pos (Real.exp_pos _) (Finset.sum_pos
    (fun _j _ => Real.exp_pos _) ⟨0, Finset.mem_univ 0⟩)

/-- **K-T-C4-1 at the factor seat:** W1's registered section
    identity fails at the composite's C⁴ factor seat
    (`factorC4`, Q7CR-2), at every inverse temperature and every
    sample time. Tier T1. -/
theorem w1_fails_factorC4_seat (β s : ℝ) :
    ¬ SecondW1Section (modSample (c4FactorWeight β) s) z4ShiftOp :=
  w1_section_fails _ _

/-! ## §5. Stationarity corroboration — the observable form -/

/-- The observable-level modular flow at the ladder seat, in the
    exact form of the landed stationarity theorem: conjugation
    of an observable by `exp (i s • z4Generator)`. Tier T2
    (definition). -/
noncomputable def obsFlow (s : ℝ) (A : Matrix (Fin 4) (Fin 4) ℂ) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  NormedSpace.exp ((Complex.I * (s : ℂ)) • z4Generator) * A
    * NormedSpace.exp ((-(Complex.I * (s : ℂ))) • z4Generator)

/-- The observable-level shift at the ladder seat: reindexing of
    an observable by the clock turn on both indices — the
    conjugation-by-permutation action of `z4Shift`, read
    entrywise. Tier T2 (definition). -/
def obsShift (A : Matrix (Fin 4) (Fin 4) ℂ) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.of fun i j => A (z4Shift i) (z4Shift j)

/-- **Deciding fact (d), first half:** the ladder seat's Gibbs
    state is stationary under the observable flow at every time —
    the landed `gibbsWeight_stationary` (`ThetLogos.KMSBridge`,
    T1), with the normalization scalar factored out. Tier T1
    (transport of a landed theorem). -/
theorem gibbsState_z4_stationary (β s : ℝ) :
    obsFlow s (gibbsState z4Generator β) = gibbsState z4Generator β := by
  unfold obsFlow gibbsState
  rw [mul_smul_comm, smul_mul_assoc, gibbsWeight_stationary]

/-- **Deciding fact (d), second half:** the shift reindexing
    MOVES the ladder seat's Gibbs state, for `β > 0`: its
    `(0, 0)` entry would force `z4Weight β 1 = z4Weight β 0`,
    against the landed step ratio `z4Weight_step_ratio` and the
    weights' positivity. Tier T1. -/
theorem obsShift_gibbsState_ne {β : ℝ} (hβ : 0 < β) :
    obsShift (gibbsState z4Generator β) ≠ gibbsState z4Generator β := by
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ => M 0 0) h
  simp only [obsShift, Matrix.of_apply, z4Shift_zero, z4_gibbsState_eq,
    Matrix.diagonal_apply_eq] at h00
  have hreal : z4Weight β 1 = z4Weight β 0 := by exact_mod_cast h00
  have hstep := z4Weight_step_ratio β (0 : Fin 3)
  have h1 : (0 : Fin 3).succ = (1 : Fin 4) := rfl
  have h0 : Fin.castSucc (0 : Fin 3) = (0 : Fin 4) := rfl
  rw [h1, h0] at hstep
  rw [hstep] at hreal
  have hw : z4Weight β 0 ≠ 0 := (z4Weight_pos β 0).ne'
  have hexp : Real.exp (-β / 4) = 1 :=
    mul_left_cancel₀ hw (by rw [mul_one]; exact hreal)
  rw [Real.exp_eq_one_iff] at hexp
  linarith

/-- **The observable-level section identity also fails at the
    ladder seat:** the flow (any time `s`) is not the shift
    reindexing, since the flow fixes the Gibbs state and the
    shift moves it. Tier T1. -/
theorem w1_observable_form_fails {β : ℝ} (hβ : 0 < β) (s : ℝ) :
    obsFlow s ≠ obsShift := by
  intro h
  have hG := congrFun h (gibbsState z4Generator β)
  rw [gibbsState_z4_stationary] at hG
  exact obsShift_gibbsState_ne hβ hG.symm

end ThetLogos
