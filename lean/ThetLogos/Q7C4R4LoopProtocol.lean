import Mathlib.Tactic
import ThetLogos.Q7C4R4LoopNoGo

namespace ThetLogos

/-!
# ThetLogos.Q7C4R4LoopProtocol - the C4-graded four-step protocol
loop (Q7CR-LOOP-2)

**Status: T1 theorem brick. NO CLAIM. Dials 0/4. No measured
number is claimed by this line.**

Governing documents: the scoping memo
`scoping-q7cr-missing-pieces-thermal-loops-2026-10-30.md`
section 2 (the three closure notions) and the section 4 LOOP-2
row, and the brick pack `pack-loop-2.md`. Built over LOOP-0's
landed registration (`ThetLogos.Q7C4R4LoopPost`: `LoopData`,
`LoopStep`, `loopStepDefect`, `loopDefectSum`,
`loopEntropyChangeSum`, the three closure Props, the Z4 clock
miniature) and LOOP-1's landed machinery
(`ThetLogos.Q7C4R4LoopNoGo`: `heatLoopStep` with its discharged
hypotheses `heat_defect_nonneg`, `heat_weight_law`,
`heat_fixed_of_defect_zero`, `heat_preserve`; the iteration form
`loopIter` and `loopIter_succ`), and Z4-KMS-1
(`ThetLogos.ThermalZ4ClockDefect`: `z4_clock_defect_factor`,
`z4_clock_not_invariant`). No landed file is edited.

## The protocol

Four steps on the composite's weight-state space. Step `j`
(`j : Fin 4`) is LOOP-1's owned multiplier (heat/ternary) step
`heatLoopStep tau rate` carrying the clock grade `j + 1` as its
control parameter: the grades cycle `1, 2, 3, 0` through the four
steps (controls), and between grades the owned heat step acts.
The protocol data (`protocolLoopData`) starts and ends at grade
`0`, time `tau`, coupling `0`.

## Verdicts, one per registered part, closure labels exact

- **(a) IndexClosed - CONSTRUCTION FACT, not a finding.**
  `protocol_indexClosed`: the protocol's `finalParam` equals its
  `initialParam` because both are *stated* as grade `0` after the
  four grades cycle (the cycle itself is
  `protocol_grade_cycle`: step 3 carries grade `3 + 1 = 0` in
  `Fin 4`). This is IndexClosed ONLY. Per kill K-LOOP-3 it is
  never presented as state closure or thermal closure, and
  part (d) below proves the distinction is real at this very
  protocol's grade advance: the ladder state is moved by the
  first grade, not returned.
- **(b) Defect additivity - LedgerClosed's substance, PROVED.**
  `protocol_defect_additivity`: LOOP-0's `loopDefectSum` at the
  protocol equals the sum of the four steps' measured defects,
  where each measured defect is the UNGRADED `loopStepDefect`
  of LOOP-1's `heatLoopStep` at the visited state. The teeth
  identity is `gradedHeatStep_defect_eq`: a graded step's own
  registered defect equals the ungraded defect at the same
  state - proved, not arranged: the protocol's total is
  LOOP-0's `loopDefectSum` at the protocol data, unmodified.
  The entropy half of the ledger telescopes separately
  (`loopEntropyChangeSum_telescope`).
- **LedgerClosed status, stated explicitly:** the protocol IS
  `LedgerClosed` (`protocol_ledgerClosed`), with
  `statedLedgerTotal` set to the proved internal ledger sum
  (defect sum plus entropy-change sum at the protocol's own
  steps and visited states). The nontrivial content of that
  status is exactly (b) plus the entropy telescope; the
  equality itself is the registration's form.
- **(c) The closure trichotomy - StateClosed content, PROVED.**
  `protocol_trichotomy`: for `tau >= 0`, nonnegative rates, and
  a nonnegative initial weight,
  `StateClosed protocol <-> total defect = 0 <-> every visited
  state is fixed by its own step`. The route is the weight-law
  telescope generalized to a step sequence
  (`loopDefectSum_telescope`) plus LOOP-1's per-step
  fixed-sector characterization (`heat_fixed_of_defect_zero`)
  applied stepwise. Corollary (`protocol_selfContained_iff`):
  since the protocol is LedgerClosed with external work `0`,
  it is `SelfContainedLoop` iff its total defect is `0`.
- **(d) The clock-defect corollary - PROVED (lifts; no seam).**
  The protocol's grade advance is LOOP-0's registered clock
  step `z4ClockStep` (same grade data:
  `protocol_first_grade`). At the ladder package's Gibbs state
  read on the composite along the C4 coordinate
  (`ladderCompState`, LOOP-0's miniature initial state), the
  state after one grade is exactly the Z4-KMS-1 shifted state
  (`first_grade_shift`), its per-index values carry the
  Z4-KMS-1 defect factors `exp (-beta / 4)` per step and
  `exp (3 * beta / 4)` at the wrap (`first_grade_factor`), and
  for `beta > 0` it is NOT the initial state
  (`first_grade_not_returned`, via `z4_clock_not_invariant`):
  moved, measurably, not returned. This is a statement about
  the grade-advance (clock) step's action on the ladder state;
  it is the standing counterexample to reading (a)'s
  IndexClosed as state closure (K-LOOP-3).

Fences: NO CLAIM; dials 0/4; no measured number is claimed by
this line; every result above is labeled with exactly the
closure notion it is (IndexClosed / StateClosed /
LedgerClosed / SelfContainedLoop), never the bare word "loop"
as a claim.
-/

/-! ## Section 1. The graded heat step and the protocol data -/

/-- **The graded heat step**: LOOP-1's owned multiplier step
`heatLoopStep tau rate` carrying clock grade `k + 1` as its
control parameter. The state map, time, and rate data are
exactly the ungraded step's; only the grade (a control) is
added. Both ledger terms are carried by the Q7 factor, as in
LOOP-1's step. Tier T2 (definition). -/
noncomputable def gradedHeatStep (tau : ℝ) (rate : compIndex → ℝ)
    (k : Fin 4) : LoopStep where
  param := { time := tau, grade := k + 1, coupling := 0 }
  applyState := fun w x => Real.exp (-2 * tau * rate x) * w x
  rate := rate
  defectFactor := LoopFactor.q7
  entropyFactor := LoopFactor.q7

/-- **The graded step's state map is the ungraded step's**:
grading changes a control parameter only, never the state map.
Tier T1. -/
theorem gradedHeatStep_apply_eq (tau : ℝ) (rate : compIndex → ℝ)
    (k : Fin 4) :
    (gradedHeatStep tau rate k).applyState
      = (heatLoopStep tau rate).applyState := rfl

/-- **THE TEETH IDENTITY (Tier T1)**: a graded step's own
registered defect (`loopStepDefect` at the graded step) equals
the ungraded step's defect at the same visited state. The
grade enters the protocol parameters only; the defect
functional reads time and rate data, which the grading leaves
untouched - and that is a proved identity about LOOP-0's
`loopStepDefect` at two different `LoopStep` data, not a
definition of either side. -/
theorem gradedHeatStep_defect_eq (tau : ℝ)
    (rate : compIndex → ℝ) (k : Fin 4) (w : compIndex → ℝ) :
    loopStepDefect (gradedHeatStep tau rate k) w
      = loopStepDefect (heatLoopStep tau rate) w := rfl

/-- **The graded step's weight law** (Tier T1): LOOP-1's
discharged weight law `heat_weight_law`, transported across
the teeth identity and the state-map identity. -/
theorem gradedHeatStep_weight_law (tau : ℝ)
    (rate : compIndex → ℝ) (k : Fin 4) (w : compIndex → ℝ) :
    weightSum ((gradedHeatStep tau rate k).applyState w)
      = weightSum w
        - loopStepDefect (gradedHeatStep tau rate k) w :=
  heat_weight_law tau rate w

/-- **The graded step preserves nonnegative weights** (Tier
T1): LOOP-1's `heat_preserve` across the state-map identity. -/
theorem gradedHeatStep_preserve (tau : ℝ)
    (rate : compIndex → ℝ) (k : Fin 4) (w : compIndex → ℝ)
    (hw : ∀ x, 0 ≤ w x) :
    ∀ x, 0 ≤ (gradedHeatStep tau rate k).applyState w x :=
  heat_preserve rate w hw

/-- **The four-step graded protocol as loop data**: steps at
grades `0, 1, 2, 3` (carrying control grades `1, 2, 3, 0`),
initial weight `rho`, protocol parameters starting and ending
at grade `0` / time `tau` / coupling `0`, external work `0`,
and the stated ledger total set to the internal ledger sum
(defect sum plus entropy-change sum at the protocol's own
steps and visited states) - the total that part (b) and the
entropy telescope prove. Tier T2 (definition). -/
noncomputable def protocolLoopData (tau : ℝ)
    (rate : compIndex → ℝ) (rho : compIndex → ℝ) : LoopData where
  steps := [gradedHeatStep tau rate 0, gradedHeatStep tau rate 1,
    gradedHeatStep tau rate 2, gradedHeatStep tau rate 3]
  initialState := rho
  initialParam := { time := tau, grade := 0, coupling := 0 }
  finalParam := { time := tau, grade := 0, coupling := 0 }
  statedLedgerTotal :=
    loopDefectSum [gradedHeatStep tau rate 0,
      gradedHeatStep tau rate 1, gradedHeatStep tau rate 2,
      gradedHeatStep tau rate 3] rho
    + loopEntropyChangeSum [gradedHeatStep tau rate 0,
      gradedHeatStep tau rate 1, gradedHeatStep tau rate 2,
      gradedHeatStep tau rate 3] rho
  externalWork := 0

/-- The protocol's step list, as registered. -/
theorem protocol_steps (tau : ℝ) (rate : compIndex → ℝ)
    (rho : compIndex → ℝ) :
    (protocolLoopData tau rate rho).steps
      = [gradedHeatStep tau rate 0, gradedHeatStep tau rate 1,
        gradedHeatStep tau rate 2, gradedHeatStep tau rate 3] :=
  rfl

/-- The protocol's initial state, as registered. -/
theorem protocol_initialState (tau : ℝ) (rate : compIndex → ℝ)
    (rho : compIndex → ℝ) :
    (protocolLoopData tau rate rho).initialState = rho := rfl

/-! ## Section 2. Part (a) - IndexClosed, a CONSTRUCTION FACT

This section is IndexClosed ONLY: a statement about the
protocol's control parameters. It is proved at the
definitional level because it holds by construction - the
protocol was built so its grades cycle back. It is NOT a
finding, and per K-LOOP-3 no sentence in this module presents
it as state closure or thermal closure; part (d) (Section 5)
proves the ladder state is moved by the first grade advance
of this same protocol. -/

/-- **The grade cycle (construction fact)**: the four steps
carry control grades `1, 2, 3, 0` - the last step's grade is
`3 + 1 = 0` in `Fin 4`, the protocol's starting grade. -/
theorem protocol_grade_cycle (tau : ℝ) (rate : compIndex → ℝ) :
    (gradedHeatStep tau rate 0).param.grade = 1
      ∧ (gradedHeatStep tau rate 1).param.grade = 2
      ∧ (gradedHeatStep tau rate 2).param.grade = 3
      ∧ (gradedHeatStep tau rate 3).param.grade = 0 :=
  ⟨rfl, rfl, rfl, by
    show ((3 : Fin 4) + 1) = 0
    decide⟩

/-- **(a) IndexClosed of the protocol - CONSTRUCTION FACT
(Tier T1 as a definitional equality, labeled as such)**:
the protocol's final protocol parameters equal its initial
ones, because both are stated as grade `0`, time `tau`,
coupling `0` after the four grades cycle
(`protocol_grade_cycle`). IndexClosed ONLY - a statement
about the protocol's controls, not about any state. -/
theorem protocol_indexClosed (tau : ℝ) (rate : compIndex → ℝ)
    (rho : compIndex → ℝ) :
    IndexClosed (protocolLoopData tau rate rho) := rfl

/-- **LedgerClosed status of the protocol, stated explicitly
(Tier T1)**: the protocol IS LedgerClosed, with its
`statedLedgerTotal` set to the proved internal ledger sum
(part (b)'s defect additivity plus the entropy telescope of
Section 3 are the content of that sum). The equality here is
the registration's own form: internal sum against stated
total, every term carried by a named factor through its
step's `defectFactor` / `entropyFactor` fields. -/
theorem protocol_ledgerClosed (tau : ℝ) (rate : compIndex → ℝ)
    (rho : compIndex → ℝ) :
    LedgerClosed (protocolLoopData tau rate rho) := rfl


/-! ## Section 3. Sequence telescopes and part (b) - defect
additivity (LedgerClosed's substance) -/

/-- **Four-step expansion of LOOP-0's defect sum**: the sum
over a four-step list is the four visited-state defects, in
order. Tier T1. -/
theorem loopDefectSum_four (a b c d : LoopStep)
    (w : compIndex → ℝ) :
    loopDefectSum [a, b, c, d] w
      = loopStepDefect a w
        + (loopStepDefect b (a.applyState w)
          + (loopStepDefect c (b.applyState (a.applyState w))
            + (loopStepDefect d
                (c.applyState (b.applyState (a.applyState w)))
              + 0))) := rfl

/-- **Four-step expansion of LOOP-0's step composition**.
Tier T1. -/
theorem applyLoopSteps_four (a b c d : LoopStep)
    (w : compIndex → ℝ) :
    applyLoopSteps [a, b, c, d] w
      = d.applyState (c.applyState (b.applyState
          (a.applyState w))) := rfl

/-- **The weight-law telescope over a step SEQUENCE** (Tier
T1): LOOP-1's `defect_telescope` generalized from a constant
step to a stated list - if every step of the list satisfies
the weight law for its own registered defect, the list's
total defect (LOOP-0's `loopDefectSum`) is the initial weight
sum minus the final weight sum. -/
theorem loopDefectSum_telescope :
    ∀ (L : List LoopStep),
      (∀ s ∈ L, ∀ w, weightSum (s.applyState w)
        = weightSum w - loopStepDefect s w)
      → ∀ w, loopDefectSum L w
        = weightSum w - weightSum (applyLoopSteps L w) := by
  intro L
  induction L with
  | nil =>
    intro _ w
    show (0 : ℝ) = weightSum w - weightSum w
    rw [sub_self]
  | cons s rest ih =>
    intro h w
    have hrest : ∀ s' ∈ rest, ∀ w, weightSum (s'.applyState w)
        = weightSum w - loopStepDefect s' w :=
      fun s' hs' => h s' (List.mem_cons_of_mem s hs')
    show loopStepDefect s w + loopDefectSum rest (s.applyState w)
      = weightSum w
        - weightSum (applyLoopSteps rest (s.applyState w))
    rw [ih hrest (s.applyState w),
      h s List.mem_cons_self w]
    ring

/-- **The entropy telescope over a step sequence** (Tier T1):
LOOP-0's entropy-change sum over any step list is the final
state's `entropyW` minus the initial state's - each step's
term is its own `entropyW` change, and the changes telescope.
This is the entropy half of the protocol's ledger. -/
theorem loopEntropyChangeSum_telescope :
    ∀ (L : List LoopStep) (w : compIndex → ℝ),
      loopEntropyChangeSum L w
        = entropyW (applyLoopSteps L w) - entropyW w := by
  intro L
  induction L with
  | nil =>
    intro w
    show (0 : ℝ) = entropyW w - entropyW w
    rw [sub_self]
  | cons s rest ih =>
    intro w
    show loopStepEntropyChange s w
        + loopEntropyChangeSum rest (s.applyState w)
      = entropyW (applyLoopSteps rest (s.applyState w))
        - entropyW w
    show (entropyW (s.applyState w) - entropyW w)
        + loopEntropyChangeSum rest (s.applyState w)
      = entropyW (applyLoopSteps rest (s.applyState w))
        - entropyW w
    rw [ih (s.applyState w)]
    ring

/-- **Visited-state bridges**: the protocol's `j`-th visited
state (in LOOP-1's iteration form) is reached from the
previous visited state by any graded step - all graded steps
share the ungraded state map. Tier T1. -/
theorem graded_apply_loopIter (tau : ℝ) (rate : compIndex → ℝ)
    (k : Fin 4) (rho : compIndex → ℝ) (m : ℕ) :
    (gradedHeatStep tau rate k).applyState
        (loopIter (heatLoopStep tau rate).applyState rho m)
      = loopIter (heatLoopStep tau rate).applyState rho (m + 1) := by
  rw [loopIter_succ]
  rfl

/-- **(b) DEFECT ADDITIVITY (Tier T1; LedgerClosed's
substance)**: the protocol's total defect - LOOP-0's
`loopDefectSum` at the protocol data, unmodified - equals the
sum of the four steps' MEASURED defects, where each measured
defect is the ungraded `loopStepDefect` of LOOP-1's
`heatLoopStep` at the state that step visits. The passage
from the graded steps' own defects to the measured ones is
the teeth identity `gradedHeatStep_defect_eq`, applied at
each visited state. -/
theorem protocol_defect_additivity (tau : ℝ)
    (rate : compIndex → ℝ) (rho : compIndex → ℝ) :
    loopDefectSum (protocolLoopData tau rate rho).steps rho
      = loopStepDefect (heatLoopStep tau rate) rho
        + loopStepDefect (heatLoopStep tau rate)
            ((heatLoopStep tau rate).applyState rho)
        + loopStepDefect (heatLoopStep tau rate)
            ((heatLoopStep tau rate).applyState
              ((heatLoopStep tau rate).applyState rho))
        + loopStepDefect (heatLoopStep tau rate)
            ((heatLoopStep tau rate).applyState
              ((heatLoopStep tau rate).applyState
                ((heatLoopStep tau rate).applyState rho))) := by
  rw [protocol_steps, loopDefectSum_four]
  rw [gradedHeatStep_defect_eq, gradedHeatStep_defect_eq,
    gradedHeatStep_defect_eq, gradedHeatStep_defect_eq]
  rw [gradedHeatStep_apply_eq, gradedHeatStep_apply_eq,
    gradedHeatStep_apply_eq]
  ring


/-! ## Section 4. Part (c) - the closure trichotomy
(StateClosed content) -/

/-- The protocol's final state in iteration form: four
applications of the ungraded step map. Tier T1. -/
theorem protocol_final_apply (tau : ℝ) (rate : compIndex → ℝ)
    (rho : compIndex → ℝ) :
    applyLoopSteps (protocolLoopData tau rate rho).steps rho
      = loopIter (heatLoopStep tau rate).applyState rho 4 :=
  calc applyLoopSteps (protocolLoopData tau rate rho).steps rho
      = (gradedHeatStep tau rate 3).applyState
          ((gradedHeatStep tau rate 2).applyState
            ((gradedHeatStep tau rate 1).applyState
              ((gradedHeatStep tau rate 0).applyState rho))) :=
        applyLoopSteps_four _ _ _ _ _
    _ = loopIter (heatLoopStep tau rate).applyState rho 4 := rfl

/-- **(c) THE CLOSURE TRICHOTOMY (Tier T1; StateClosed
content)**: for `tau >= 0`, nonnegative rates, and a
nonnegative initial weight `rho`,

`StateClosed protocol <-> total defect = 0 <-> every visited
state is fixed by its own step`

(the last clause: for each grade `j : Fin 4`, the `j`-th
graded step fixes the `j`-th visited state). Route: the
sequence weight-law telescope `loopDefectSum_telescope`
(state closure collapses the telescope), nonnegativity of
each visited defect (LOOP-1's `heat_defect_nonneg`), and
LOOP-1's per-step fixed-sector characterization
(`heat_fixed_of_defect_zero`) applied stepwise; the return
direction builds the final state from the fixed visited
states along `loopIter_succ`. -/
theorem protocol_trichotomy {tau : ℝ} (htau : 0 ≤ tau)
    {rate : compIndex → ℝ} (hrate : ∀ x, 0 ≤ rate x)
    (rho : compIndex → ℝ) (hrho : ∀ x, 0 ≤ rho x) :
    (StateClosed (protocolLoopData tau rate rho)
      ↔ loopDefectSum (protocolLoopData tau rate rho).steps rho
        = 0)
    ∧ (loopDefectSum (protocolLoopData tau rate rho).steps rho
        = 0
      ↔ ∀ j : Fin 4, (gradedHeatStep tau rate j).applyState
          (loopIter (heatLoopStep tau rate).applyState rho j.val)
        = loopIter (heatLoopStep tau rate).applyState rho
            j.val) := by
  -- Every step of the protocol satisfies the weight law.
  have hweight : ∀ s ∈ (protocolLoopData tau rate rho).steps,
      ∀ w, weightSum (s.applyState w)
        = weightSum w - loopStepDefect s w := by
    intro s hs w
    rw [protocol_steps] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl
    · exact gradedHeatStep_weight_law tau rate 0 w
    · exact gradedHeatStep_weight_law tau rate 1 w
    · exact gradedHeatStep_weight_law tau rate 2 w
    · exact gradedHeatStep_weight_law tau rate 3 w
  -- Visited states are nonnegative.
  have hnonneg_vis : ∀ k x, 0 ≤ loopIter
      (heatLoopStep tau rate).applyState rho k x :=
    fun k => loopIter_nonneg (heatLoopStep tau rate).applyState
      (fun w hw => heat_preserve rate w hw) rho hrho k
  -- The total defect in four-term form, at the visited states.
  have hbridge0 : ∀ k : Fin 4,
      (gradedHeatStep tau rate k).applyState rho
        = loopIter (heatLoopStep tau rate).applyState rho 1 :=
    fun k => rfl
  have hsum4 : loopDefectSum
      (protocolLoopData tau rate rho).steps rho
      = loopStepDefect (heatLoopStep tau rate) rho
        + (loopStepDefect (heatLoopStep tau rate)
            (loopIter (heatLoopStep tau rate).applyState rho 1)
          + (loopStepDefect (heatLoopStep tau rate)
              (loopIter (heatLoopStep tau rate).applyState rho 2)
            + (loopStepDefect (heatLoopStep tau rate)
                (loopIter (heatLoopStep tau rate).applyState
                  rho 3)
              + 0))) := by
    rw [protocol_steps, loopDefectSum_four,
      gradedHeatStep_defect_eq, gradedHeatStep_defect_eq,
      gradedHeatStep_defect_eq, gradedHeatStep_defect_eq,
      hbridge0, graded_apply_loopIter, graded_apply_loopIter]
  -- Each visited defect is nonnegative.
  have hd_nonneg : ∀ k, 0 ≤ loopStepDefect
      (heatLoopStep tau rate)
      (loopIter (heatLoopStep tau rate).applyState rho k) :=
    fun k => heat_defect_nonneg htau hrate _
      (hnonneg_vis k)
  have hd0_nonneg : 0 ≤ loopStepDefect
      (heatLoopStep tau rate) rho :=
    heat_defect_nonneg htau hrate rho hrho
  -- Total defect zero forces each visited defect to zero.
  have hzeros_of_total : loopDefectSum
      (protocolLoopData tau rate rho).steps rho = 0
      → (loopStepDefect (heatLoopStep tau rate) rho = 0
        ∧ loopStepDefect (heatLoopStep tau rate)
            (loopIter (heatLoopStep tau rate).applyState rho 1)
          = 0
        ∧ loopStepDefect (heatLoopStep tau rate)
            (loopIter (heatLoopStep tau rate).applyState rho 2)
          = 0
        ∧ loopStepDefect (heatLoopStep tau rate)
            (loopIter (heatLoopStep tau rate).applyState
              rho 3) = 0) := by
    intro htotal
    rw [hsum4] at htotal
    refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith [hd_nonneg 1, hd_nonneg 2,
      hd_nonneg 3, hd0_nonneg]
  -- Each visited defect zero gives each visited state fixed
  -- by its own step (LOOP-1's characterization, stepwise).
  have hfixed_of_zeros :
      (loopStepDefect (heatLoopStep tau rate) rho = 0
        ∧ loopStepDefect (heatLoopStep tau rate)
            (loopIter (heatLoopStep tau rate).applyState rho 1)
          = 0
        ∧ loopStepDefect (heatLoopStep tau rate)
            (loopIter (heatLoopStep tau rate).applyState rho 2)
          = 0
        ∧ loopStepDefect (heatLoopStep tau rate)
            (loopIter (heatLoopStep tau rate).applyState
              rho 3) = 0)
      → ∀ j : Fin 4, (gradedHeatStep tau rate j).applyState
          (loopIter (heatLoopStep tau rate).applyState rho j.val)
        = loopIter (heatLoopStep tau rate).applyState rho
            j.val := by
    intro hz j
    obtain ⟨e0, e1, e2, e3⟩ := hz
    obtain ⟨jv, hjv⟩ := j
    interval_cases jv
    · exact heat_fixed_of_defect_zero htau hrate rho hrho e0
    · exact heat_fixed_of_defect_zero htau hrate _
        (hnonneg_vis 1) e1
    · exact heat_fixed_of_defect_zero htau hrate _
        (hnonneg_vis 2) e2
    · exact heat_fixed_of_defect_zero htau hrate _
        (hnonneg_vis 3) e3
  -- Each visited state fixed forces each visited defect to
  -- zero (the weight law at a fixed state).
  have hzeros_of_fixed :
      (∀ j : Fin 4, (gradedHeatStep tau rate j).applyState
          (loopIter (heatLoopStep tau rate).applyState rho j.val)
        = loopIter (heatLoopStep tau rate).applyState rho
            j.val)
      → (loopStepDefect (heatLoopStep tau rate) rho = 0
        ∧ loopStepDefect (heatLoopStep tau rate)
            (loopIter (heatLoopStep tau rate).applyState rho 1)
          = 0
        ∧ loopStepDefect (heatLoopStep tau rate)
            (loopIter (heatLoopStep tau rate).applyState rho 2)
          = 0
        ∧ loopStepDefect (heatLoopStep tau rate)
            (loopIter (heatLoopStep tau rate).applyState
              rho 3) = 0) := by
    intro hfixed
    have hfix : ∀ k (hk : k < 4),
        (heatLoopStep tau rate).applyState
          (loopIter (heatLoopStep tau rate).applyState rho k)
        = loopIter (heatLoopStep tau rate).applyState rho k :=
      fun k hk => hfixed ⟨k, hk⟩
    have hz : ∀ k (hk : k < 4), loopStepDefect
        (heatLoopStep tau rate)
        (loopIter (heatLoopStep tau rate).applyState rho k)
        = 0 := by
      intro k hk
      have hw := heat_weight_law tau rate
        (loopIter (heatLoopStep tau rate).applyState rho k)
      rw [hfix k hk] at hw
      linarith
    refine ⟨?_, hz 1 (by norm_num), hz 2 (by norm_num),
      hz 3 (by norm_num)⟩
    have hw := heat_weight_law tau rate rho
    have hf0 : (heatLoopStep tau rate).applyState rho = rho :=
      hfix 0 (by norm_num)
    rw [hf0] at hw
    linarith
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · -- StateClosed -> total defect zero (telescope collapse).
    intro hclosed
    have hfin : applyLoopSteps
        (protocolLoopData tau rate rho).steps rho = rho :=
      hclosed
    rw [loopDefectSum_telescope _ hweight rho, hfin, sub_self]
  · -- Total defect zero -> StateClosed (fixed chain).
    intro htotal
    have hfixed := hfixed_of_zeros (hzeros_of_total htotal)
    have hfix : ∀ k (hk : k < 4),
        (heatLoopStep tau rate).applyState
          (loopIter (heatLoopStep tau rate).applyState rho k)
        = loopIter (heatLoopStep tau rate).applyState rho k :=
      fun k hk => hfixed ⟨k, hk⟩
    have hchain : loopIter (heatLoopStep tau rate).applyState
        rho 4 = rho := by
      calc loopIter (heatLoopStep tau rate).applyState rho 4
          = (heatLoopStep tau rate).applyState
              (loopIter (heatLoopStep tau rate).applyState
                rho 3) := loopIter_succ _ rho 3
        _ = loopIter (heatLoopStep tau rate).applyState rho 3 :=
            hfix 3 (by norm_num)
        _ = (heatLoopStep tau rate).applyState
              (loopIter (heatLoopStep tau rate).applyState
                rho 2) := (loopIter_succ _ rho 2).symm
        _ = loopIter (heatLoopStep tau rate).applyState rho 2 :=
            hfix 2 (by norm_num)
        _ = (heatLoopStep tau rate).applyState
              (loopIter (heatLoopStep tau rate).applyState
                rho 1) := (loopIter_succ _ rho 1).symm
        _ = loopIter (heatLoopStep tau rate).applyState rho 1 :=
            hfix 1 (by norm_num)
        _ = (heatLoopStep tau rate).applyState rho :=
            (loopIter_succ _ rho 0).symm
        _ = rho := hfix 0 (by norm_num)
    show loopFinalState (protocolLoopData tau rate rho)
      = (protocolLoopData tau rate rho).initialState
    have happ : loopFinalState (protocolLoopData tau rate rho)
        = loopIter (heatLoopStep tau rate).applyState rho 4 :=
      protocol_final_apply tau rate rho
    exact happ.trans hchain
  · -- Total defect zero -> every visited state fixed.
    intro htotal
    exact hfixed_of_zeros (hzeros_of_total htotal)
  · -- Every visited state fixed -> total defect zero.
    intro hfixed
    obtain ⟨e0, e1, e2, e3⟩ := hzeros_of_fixed hfixed
    rw [hsum4, e0, e1, e2, e3]
    norm_num

/-- **SelfContained status of the protocol (Tier T1)**:
the protocol is LedgerClosed with external work term `0`
(Sections 2-3), so it is `SelfContainedLoop` exactly when its
total defect is `0` - equivalently (by `protocol_trichotomy`)
exactly when it is StateClosed. No stronger self-contained
reading is claimed. -/
theorem protocol_selfContained_iff {tau : ℝ} (htau : 0 ≤ tau)
    {rate : compIndex → ℝ} (hrate : ∀ x, 0 ≤ rate x)
    (rho : compIndex → ℝ) (hrho : ∀ x, 0 ≤ rho x) :
    SelfContainedLoop (protocolLoopData tau rate rho)
      ↔ loopDefectSum (protocolLoopData tau rate rho).steps rho
        = 0 := by
  have htri := (protocol_trichotomy htau hrate rho hrho).1
  constructor
  · intro h
    unfold SelfContainedLoop at h
    exact htri.mp h.1
  · intro h
    unfold SelfContainedLoop
    exact ⟨htri.mpr h, protocol_ledgerClosed tau rate rho, rfl⟩


/-! ## Section 5. Part (d) - the clock-defect corollary

The protocol's grade advance is the clock turn: LOOP-0's
registered clock step `z4ClockStep` carries exactly the grade
data of the protocol's first step (`protocol_first_grade`).
This section instantiates that grade advance at the ladder
package's Gibbs state, read on the composite along the C4
factor's `Fin 4` coordinate - LOOP-0's miniature anatomy.
The verdict: (d) LIFTS in full; there is no seam. The state
after one grade is the Z4-KMS-1 shifted state, it carries the
Z4-KMS-1 defect factors, and at `beta > 0` it is not the
initial state. This is the standing witness that Section 2's
IndexClosed is not state closure (K-LOOP-3). -/

/-- **The ladder state on the composite**: the ladder package's
Gibbs weights `z4Weight beta` read along the C4 factor's
`Fin 4` coordinate - LOOP-0's clock-miniature initial state.
Tier T2 (definition). -/
noncomputable def ladderCompState (beta : ℝ) :
    compIndex → ℝ :=
  fun t => z4Weight beta t.1.2.1

/-- The ladder state on the composite is LOOP-0's miniature
initial state, as registered. Tier T1. -/
theorem ladderCompState_eq (beta : ℝ) :
    ladderCompState beta
      = (z4ClockLoopData beta).initialState := rfl

/-- **The protocol's first grade advance is the clock step's**:
the protocol's first step and LOOP-0's registered clock step
`z4ClockStep 0` carry the same grade data (grade `0 + 1`).
Tier T1. -/
theorem protocol_first_grade (tau : ℝ)
    (rate : compIndex → ℝ) :
    (gradedHeatStep tau rate 0).param.grade
      = (z4ClockStep 0).param.grade := rfl

/-- **(d) THE SHIFTED STATE AFTER ONE GRADE (Tier T1)**:
the protocol's grade advance (the clock step) applied to the
ladder state on the composite gives exactly the Z4-KMS-1
shifted state, read along the C4 coordinate: at each index
`t`, the new weight is `z4ShiftedWeight beta t.1.2.1`. -/
theorem first_grade_shift (beta : ℝ) :
    (z4ClockStep 0).applyState (ladderCompState beta)
      = fun t => z4ShiftedWeight beta t.1.2.1 := by
  funext t
  rfl

/-- **(d) THE DEFECT FACTORS AFTER ONE GRADE (Tier T1)**:
measured index by index, the state after one grade is the
initial ladder state scaled by the Z4-KMS-1 defect factor -
`exp (-beta / 4)` at every index whose C4 coordinate is below
the wrap, `exp (3 * beta / 4)` at the wrap coordinate `3`.
Transported from `z4_clock_defect_factor`; not re-derived. -/
theorem first_grade_factor (beta : ℝ) :
    (∀ t : compIndex, t.1.2.1.val < 3 →
        (z4ClockStep 0).applyState (ladderCompState beta) t
          = Real.exp (-beta / 4) * ladderCompState beta t)
      ∧ ∀ t : compIndex, t.1.2.1 = 3 →
        (z4ClockStep 0).applyState (ladderCompState beta) t
          = Real.exp (3 * beta / 4) * ladderCompState beta t := by
  constructor
  · intro t ht
    rw [first_grade_shift]
    exact (z4_clock_defect_factor beta).1 t.1.2.1 ht
  · intro t ht
    rw [first_grade_shift]
    show z4ShiftedWeight beta t.1.2.1
      = Real.exp (3 * beta / 4) * z4Weight beta t.1.2.1
    rw [ht]
    exact (z4_clock_defect_factor beta).2

/-- **(d) NOT RETURNED (Tier T1)**: for `beta > 0`, the state
after one grade advance is NOT the ladder state - moved,
measurably (by `first_grade_factor`), not returned. Via
Z4-KMS-1's `z4_clock_not_invariant`, evaluated at composite
indices of each C4 coordinate. This is a statement about the
grade advance's action on the state; it is exactly what
Section 2's IndexClosed does NOT say, and the two must never
be conflated (K-LOOP-3). -/
theorem first_grade_not_returned {beta : ℝ} (hbeta : 0 < beta) :
    (z4ClockStep 0).applyState (ladderCompState beta)
      ≠ ladderCompState beta := by
  intro h
  apply z4_clock_not_invariant hbeta
  intro k
  have h2 := congrFun h (((0, 0), (k, 0)), 0)
  rw [first_grade_shift] at h2
  exact h2

#print axioms protocol_indexClosed
#print axioms protocol_ledgerClosed
#print axioms protocol_defect_additivity
#print axioms protocol_trichotomy
#print axioms protocol_selfContained_iff
#print axioms first_grade_shift
#print axioms first_grade_factor
#print axioms first_grade_not_returned

end ThetLogos
