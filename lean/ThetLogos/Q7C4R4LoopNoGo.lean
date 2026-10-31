import Mathlib.Tactic
import ThetLogos.Q7C4R4LoopPost

namespace ThetLogos

/-!
# ThetLogos.Q7C4R4LoopNoGo - the autonomous no-go (Q7CR-LOOP-1)

**Status: T1 theorem brick. NO CLAIM. Dials 0/4. No measured
number is claimed by this line.**

Governing documents: the scoping memo
`scoping-q7cr-missing-pieces-thermal-loops-2026-10-30.md`
section 3 (obstruction O1) and the section 4 LOOP-1 row, and the
brick pack `pack-loop-1.md`. Built over LOOP-0's landed
registration (`ThetLogos.Q7C4R4LoopPost`: `LoopData`, `LoopStep`,
`StateClosed`, `loopStepDefect`, `applyLoopSteps`,
`loopDefectSum`), which is not edited here.

## Obstruction O1, stated

An autonomous defect-carrying step admits no nontrivial exact
cycle: around an exact cycle the total defect is a sum of
nonnegative per-step terms and exact return forces the total to
be zero, hence every term is zero, hence - under the fixed-sector
characterization - every visited state is fixed by the step. A
self-contained autonomous thermal loop is therefore either
trivial (a chain of fixed states) or nonexistent. This module
proves that statement in two layers.

## Layer 1 - the general no-go, hypotheses IN the statement

`autonomous_no_go`: for a `LoopData` whose step list is one
stated step `s` repeated `n >= 1` times, over nonnegative weight
states, with a defect function `D` satisfying three hypotheses
stated in the theorem itself -

- (nonneg) `D w >= 0` at every nonnegative weight `w`;
- (weight law) the step's weight-sum accounting identity
  `weightSum (s.applyState w) = weightSum w - D w` for every `w`
  (the trace-defect accounting form);
- (fixed-sector, LOAD-BEARING) `D w = 0` implies
  `s.applyState w = w` at every nonnegative weight `w`;

plus the standing state-space condition that the step carries
nonnegative weights to nonnegative weights (without it "visited
state" has no meaning on this state space) - exact state return
(`StateClosed`) forces the total defect over the cycle to be
zero AND every visited state to be fixed by the step.

The fixed-sector hypothesis is load-bearing and is the whole
teeth of the statement: it is what separates heat/ternary-type
steps from permutation steps. A permutation step (the Z4 clock
shift is the standing miniature) admits the identically-zero
defect, satisfies the nonneg and weight-law hypotheses for that
defect, and moves states - so any version of this theorem whose
hypotheses the clock shift satisfied would be false, and the
separation is enforced by the statement itself, not by prose.
Section 4 below proves the failure at the clock step as a
theorem (`clock_fixed_sector_fails`): at the registered clock
step's own defect (`loopStepDefect`, identically zero because
its time and rate data are zero) there is a nonnegative weight
with defect zero that the clock step moves.

## Layer 2 - the owned instantiation

Section 3 exhibits the composite's autonomous step in the owned
multiplier (heat/ternary) form on weight states over
`compIndex`: `heatLoopStep tau rate`, with
`applyState w = fun x => Real.exp (-2 * tau * rate x) * w x` -
exactly LOOP-0's `loopStepDefect` form, with `D` taken to be
`loopStepDefect (heatLoopStep tau rate)` itself. The rate data
used is a general stated `rate : compIndex -> R` with
`0 <= rate x` and a step time `tau >= 0` (the no-go is about the
step FORM); the Q7CR-5 eigenvalue function `eigComp` is then
plugged in as a named specialization. All three Layer-1
hypotheses are DISCHARGED for this step:

- nonneg and the weight law from the closed defect form
  `sum x, w x * (1 - exp (-2 * tau * rate x))` - the
  `compIndex`-seat form of `ViscousLine.traceDefect_eq_sum` /
  `traceDefect_nonneg`;
- the fixed-sector hypothesis PROVED from the eq-zero
  characterization at this seat (`heat_defect_eq_zero_occupied`,
  the seat form of `ViscousLine.traceDefect_eq_zero_of_support`):
  defect zero iff every occupied mode has `tau * rate x = 0`,
  iff the multiplier at that mode is `exp 0 = 1`, iff the step
  fixes the state. Consequently NO state with `D = 0` exists
  outside the fixed sector at this instantiation - the
  characterization is the proof, and a single exhibited such
  state would have killed the registered claim; none exists.

At the `eigComp` specialization with `tau > 0` the conclusion
sharpens (`heat_eig_no_return`): since `eigComp x >= 1 / 64`
everywhere (Q7CR-2, landed), the fixed sector at positive time
contains no weight state at all, so no exact autonomous cycle
of a weight state (sum 1) exists for that step - not merely
that any such cycle is a chain of fixed states.

## Why the theorem does not apply to the Z4 clock shift

The clock step registered in LOOP-0 (`z4ClockStep`) has time
and rate data zero, so its `loopStepDefect` is identically zero:
the nonneg and weight-law hypotheses are available to it, but
the load-bearing fixed-sector hypothesis FAILS - the clock
pullback moves every single-mode weight (its index shift has no
fixed index at all, `z4ClockShiftIndex_ne`), while its defect
stays zero. This is the loop-form of the clock's registered
reading (LOOP-0 section 5, citing Z4-KMS-1's
`z4_clock_not_invariant`: at `beta > 0` one turn moves the
ladder weights): the clock is IndexClosed only, a relabeling
with zero thermal content, and this theorem cannot be spent on
it. Selling index closure as state closure is kill K-LOOP-3;
this module does not.

## On the verb in Jeff's sentence

Jeff's verb appears in this line in the memo's labeled
exclusion sense only: this theorem is a forcing result in the
exclusion sense - the owned defect structure forces any exact
autonomous thermal cycle to be defect-free and
fixed-sector-bound. It forces nothing to organize into loops;
the compulsion reading is refuted by this very theorem for
autonomous dynamics.

## Verdict

LOOP-1 lands in both layers: the general no-go with the
load-bearing hypothesis stated (`autonomous_no_go`, with its
`loopDefectSum` form `autonomous_no_go_defectSum`), and the
owned multiplier instantiation with all hypotheses discharged
(`heat_autonomous_no_go`, sharpened at `eigComp` by
`heat_eig_no_return`). The strong reading of a self-contained
autonomous thermal loop is refuted as a theorem - that
refutation IS the deliverable of this brick.

Fences: NO CLAIM; dials 0/4; no measured number is claimed by
this line; the closure type of every result here is
`StateClosed` (never index closure); K-LOOP-1/2/3/4 stand as
registered in the memo.
-/

/-! ## Section 1. Iteration machinery for a constant step list -/

/-- **The weight sum of a weight function** on `compIndex`:
`sum x, w x`. The quantity the weight law accounts. -/
noncomputable def weightSum (w : compIndex → ℝ) : ℝ :=
  ∑ x, w x

/-- **Iteration of one step map from an initial weight**, in the
tail form matching `applyLoopSteps` on a constant list:
`loopIter Phi w 0 = w` and
`loopIter Phi w (k+1) = loopIter Phi (Phi w) k`. -/
def loopIter (Phi : (compIndex → ℝ) → (compIndex → ℝ))
    (w : compIndex → ℝ) : ℕ → (compIndex → ℝ)
  | 0 => w
  | (k + 1) => loopIter Phi (Phi w) k

/-- **The successor form of iteration**: the `(k+1)`-st visited
state is the step applied to the `k`-th visited state. -/
theorem loopIter_succ (Phi : (compIndex → ℝ) → (compIndex → ℝ))
    (w : compIndex → ℝ) (k : ℕ) :
    loopIter Phi w (k + 1) = Phi (loopIter Phi w k) := by
  induction k generalizing w with
  | zero => rfl
  | succ k ih =>
    calc loopIter Phi w (k + 1 + 1)
        = loopIter Phi (Phi w) (k + 1) := rfl
      _ = Phi (loopIter Phi (Phi w) k) := ih _
      _ = Phi (loopIter Phi w (k + 1)) := rfl

/-- **Constant-list application is iteration**: LOOP-0's
`applyLoopSteps` on the constant list `List.replicate n s` is
`loopIter` of the step's state map. -/
theorem applyLoopSteps_replicate (s : LoopStep)
    (w : compIndex → ℝ) (n : ℕ) :
    applyLoopSteps (List.replicate n s) w
      = loopIter s.applyState w n := by
  induction n generalizing w with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ]
    exact ih (s.applyState w)

/-- **The defect sum of a constant list is the sum over visited
states**: LOOP-0's `loopDefectSum` on `List.replicate n s`
equals the sum of `loopStepDefect s` over the visited states
`loopIter s.applyState w k`, `k = 0, ..., n - 1`. -/
theorem loopDefectSum_replicate (s : LoopStep)
    (w : compIndex → ℝ) (n : ℕ) :
    loopDefectSum (List.replicate n s) w
      = ∑ k ∈ Finset.range n,
          loopStepDefect s (loopIter s.applyState w k) := by
  induction n generalizing w with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ, Finset.sum_range_succ']
    show loopStepDefect s w
        + loopDefectSum (List.replicate k s) (s.applyState w)
      = (∑ i ∈ Finset.range k,
          loopStepDefect s (loopIter s.applyState w (i + 1)))
        + loopStepDefect s (loopIter s.applyState w 0)
    rw [ih (s.applyState w)]
    have hshift : (∑ i ∈ Finset.range k,
          loopStepDefect s (loopIter s.applyState w (i + 1)))
        = ∑ i ∈ Finset.range k,
          loopStepDefect s
            (loopIter s.applyState (s.applyState w) i) :=
      Finset.sum_congr rfl (fun i _ => rfl)
    rw [hshift]
    exact add_comm _ _

/-- **Iteration preserves nonnegative weights** under a step
that carries nonnegative weights to nonnegative weights. -/
theorem loopIter_nonneg
    (Phi : (compIndex → ℝ) → (compIndex → ℝ))
    (hpreserve : ∀ w, (∀ x, 0 ≤ w x) → ∀ x, 0 ≤ Phi w x)
    (w : compIndex → ℝ) (hw : ∀ x, 0 ≤ w x) (k : ℕ) (x : compIndex) :
    0 ≤ loopIter Phi w k x := by
  induction k generalizing w with
  | zero => exact hw x
  | succ k ih => exact ih (Phi w) (hpreserve w hw)

/-- **Telescoping of the weight law**: under the weight-sum
accounting identity, the total defect over `n` visited states
is the initial weight sum minus the final weight sum. -/
theorem defect_telescope
    (Phi : (compIndex → ℝ) → (compIndex → ℝ))
    (D : (compIndex → ℝ) → ℝ)
    (hweight : ∀ w, weightSum (Phi w) = weightSum w - D w)
    (rho : compIndex → ℝ) (n : ℕ) :
    (∑ k ∈ Finset.range n, D (loopIter Phi rho k))
      = weightSum rho - weightSum (loopIter Phi rho n) := by
  induction n with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty]
    change (0 : ℝ) = weightSum rho - weightSum rho
    rw [sub_self]
  | succ k ih =>
    rw [Finset.sum_range_succ, ih, loopIter_succ]
    have h := hweight (loopIter Phi rho k)
    linarith

/-! ## Section 2. Layer 1 - the general autonomous no-go -/

/-- **THE AUTONOMOUS NO-GO (Layer 1, general form; Tier T1).**
For a loop `L` whose step list is one stated step `s` repeated
`n >= 1` times, with defect function `D` satisfying the three
hypotheses stated here -

- `hpreserve`: the step carries nonnegative weights to
  nonnegative weights (the state-space condition);
- `hnonneg`: `D w >= 0` at every nonnegative weight `w`;
- `hweight`: the weight-sum law
  `weightSum (s.applyState w) = weightSum w - D w` for all `w`;
- `hfixed` (LOAD-BEARING): `D w = 0` implies
  `s.applyState w = w` at every nonnegative weight `w`;

- exact state return (`StateClosed L`) forces the total defect
over the cycle to be zero AND every visited state
`loopIter s.applyState L.initialState k` (`k < n`) to be fixed
by the step. The proof is the telescoping of `hweight` around
the cycle (`defect_telescope`): return makes the telescope
collapse to zero, nonnegativity makes every summand zero, and
`hfixed` converts each zero into a fixed state. -/
theorem autonomous_no_go (s : LoopStep)
    (D : (compIndex → ℝ) → ℝ) (L : LoopData) (n : ℕ)
    (hn : 0 < n)
    (hsteps : L.steps = List.replicate n s)
    (hpreserve : ∀ w, (∀ x, 0 ≤ w x)
      → ∀ x, 0 ≤ s.applyState w x)
    (hnonneg : ∀ w, (∀ x, 0 ≤ w x) → 0 ≤ D w)
    (hweight : ∀ w, weightSum (s.applyState w)
      = weightSum w - D w)
    (hfixed : ∀ w, (∀ x, 0 ≤ w x) → D w = 0
      → s.applyState w = w)
    (hrho : ∀ x, 0 ≤ L.initialState x)
    (hclosed : StateClosed L) :
    (∑ k ∈ Finset.range n,
        D (loopIter s.applyState L.initialState k)) = 0
      ∧ ∀ k, k < n
        → s.applyState (loopIter s.applyState L.initialState k)
          = loopIter s.applyState L.initialState k := by
  have hiter : loopIter s.applyState L.initialState n
      = L.initialState := by
    have h1 : loopFinalState L = L.initialState := hclosed
    unfold loopFinalState at h1
    rw [hsteps, applyLoopSteps_replicate] at h1
    exact h1
  have hnonneg_iter : ∀ k, ∀ x,
      0 ≤ loopIter s.applyState L.initialState k x :=
    fun k => loopIter_nonneg s.applyState hpreserve
      L.initialState hrho k
  have htotal : (∑ k ∈ Finset.range n,
      D (loopIter s.applyState L.initialState k)) = 0 := by
    rw [defect_telescope s.applyState D hweight L.initialState n,
      hiter]
    simp
  refine ⟨htotal, fun k hk => ?_⟩
  have hterm : ∀ i ∈ Finset.range n,
      0 ≤ D (loopIter s.applyState L.initialState i) :=
    fun i _ => hnonneg _ (hnonneg_iter i)
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg hterm).mp
    htotal k (Finset.mem_range.mpr hk)
  exact hfixed _ (hnonneg_iter k) hzero

/-- **The no-go in LOOP-0's own ledger form (Tier T1)**: the
same statement with `D` taken to be the step's registered
defect `loopStepDefect s` and the total defect read as LOOP-0's
`loopDefectSum` of the loop's own step list. The three
hypotheses are the same, specialized to `loopStepDefect s`. -/
theorem autonomous_no_go_defectSum (s : LoopStep)
    (L : LoopData) (n : ℕ)
    (hn : 0 < n)
    (hsteps : L.steps = List.replicate n s)
    (hpreserve : ∀ w, (∀ x, 0 ≤ w x)
      → ∀ x, 0 ≤ s.applyState w x)
    (hnonneg : ∀ w, (∀ x, 0 ≤ w x) → 0 ≤ loopStepDefect s w)
    (hweight : ∀ w, weightSum (s.applyState w)
      = weightSum w - loopStepDefect s w)
    (hfixed : ∀ w, (∀ x, 0 ≤ w x) → loopStepDefect s w = 0
      → s.applyState w = w)
    (hrho : ∀ x, 0 ≤ L.initialState x)
    (hclosed : StateClosed L) :
    loopDefectSum L.steps L.initialState = 0
      ∧ ∀ k, k < n
        → s.applyState (loopIter s.applyState L.initialState k)
          = loopIter s.applyState L.initialState k := by
  obtain ⟨htotal, hfixedstates⟩ := autonomous_no_go s
    (loopStepDefect s) L n hn hsteps hpreserve hnonneg hweight
    hfixed hrho hclosed
  refine ⟨?_, hfixedstates⟩
  rw [hsteps, loopDefectSum_replicate]
  exact htotal

/-! ## Section 3. Layer 2 - the owned multiplier instantiation -/

/-- **The owned autonomous step in multiplier (heat/ternary)
form** on weight states over `compIndex`: at step time `tau`
and per-mode rate data `rate`, the state map multiplies each
weight by `Real.exp (-2 * tau * rate x)` - exactly the form
whose trace defect LOOP-0 registered as `loopStepDefect`. Both
ledger terms are carried by the Q7 factor (a named factor, as
LOOP-0 requires; the choice of carrier is bookkeeping, not
content). -/
noncomputable def heatLoopStep (tau : ℝ)
    (rate : compIndex → ℝ) : LoopStep where
  param := { time := tau, grade := 0, coupling := 0 }
  applyState := fun w x => Real.exp (-2 * tau * rate x) * w x
  rate := rate
  defectFactor := LoopFactor.q7
  entropyFactor := LoopFactor.q7

/-- **The defect of the multiplier step in closed form**: LOOP-0's
`loopStepDefect` at `heatLoopStep tau rate` is
`sum x, w x * (1 - exp (-2 * tau * rate x))` - the
`compIndex`-seat form of `ViscousLine.traceDefect_eq_sum`. -/
theorem heatLoopStep_defect (tau : ℝ) (rate : compIndex → ℝ)
    (w : compIndex → ℝ) :
    loopStepDefect (heatLoopStep tau rate) w
      = ∑ x, w x * (1 - Real.exp (-2 * tau * rate x)) := rfl

/-- **The multiplier bound at the step's modes**: for
`tau >= 0` and nonnegative rates, every multiplier
`exp (-2 * tau * rate x)` lies in `(0, 1]`. -/
theorem heat_multiplier_mem_Ioc {tau : ℝ} (htau : 0 ≤ tau)
    {rate : compIndex → ℝ} (hrate : ∀ x, 0 ≤ rate x)
    (x : compIndex) :
    Real.exp (-2 * tau * rate x) ∈ Set.Ioc 0 1 := by
  constructor
  · exact Real.exp_pos _
  · have hnn : (0 : ℝ) ≤ 2 * tau * rate x :=
      mul_nonneg (mul_nonneg (by norm_num) htau) (hrate x)
    calc Real.exp (-2 * tau * rate x)
        ≤ Real.exp 0 := Real.exp_le_exp.mpr (by linarith)
      _ = 1 := Real.exp_zero

/-- **Discharge 0 (state-space condition)**: the multiplier step
carries nonnegative weights to nonnegative weights. -/
theorem heat_preserve {tau : ℝ} (rate : compIndex → ℝ)
    (w : compIndex → ℝ) (hw : ∀ x, 0 ≤ w x) :
    ∀ x, 0 ≤ (heatLoopStep tau rate).applyState w x :=
  fun x => mul_nonneg (Real.exp_pos _).le (hw x)

/-- **Discharge 1 (defect nonneg)**: for `tau >= 0` and
nonnegative rates, the multiplier step's defect is nonnegative
at every nonnegative weight - the seat form of
`ViscousLine.traceDefect_nonneg`. -/
theorem heat_defect_nonneg {tau : ℝ} (htau : 0 ≤ tau)
    {rate : compIndex → ℝ} (hrate : ∀ x, 0 ≤ rate x)
    (w : compIndex → ℝ) (hw : ∀ x, 0 ≤ w x) :
    0 ≤ loopStepDefect (heatLoopStep tau rate) w := by
  rw [heatLoopStep_defect]
  apply Finset.sum_nonneg
  intro x _
  exact mul_nonneg (hw x)
    (sub_nonneg.mpr (heat_multiplier_mem_Ioc htau hrate x).2)

/-- **Discharge 2 (the weight law)**: for every weight `w`
(no sign condition needed - it is an algebra identity), the
multiplier step's weight sum is the initial weight sum minus
the defect, in `loopStepDefect` form. -/
theorem heat_weight_law (tau : ℝ) (rate : compIndex → ℝ)
    (w : compIndex → ℝ) :
    weightSum ((heatLoopStep tau rate).applyState w)
      = weightSum w - loopStepDefect (heatLoopStep tau rate) w := by
  rw [heatLoopStep_defect]
  unfold weightSum
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x _
  show Real.exp (-2 * tau * rate x) * w x
    = w x - w x * (1 - Real.exp (-2 * tau * rate x))
  ring

set_option maxRecDepth 8192 in
/-- **Discharge 3, the eq-zero characterization (the proof of
the fixed-sector hypothesis)**: for `tau >= 0`, nonnegative
rates, and a nonnegative weight, defect zero implies every
occupied mode has `tau * rate x = 0` - the seat form of
`ViscousLine.traceDefect_eq_zero_of_support`. Hence no state
with defect zero exists outside the fixed sector at this
instantiation: an occupied mode with `tau * rate x` nonzero
contributes a strictly positive defect summand. (The raised
recursion limit is for the nested-product `Finset.univ`
unification at this seat only.) -/
theorem heat_defect_eq_zero_occupied {tau : ℝ} (htau : 0 ≤ tau)
    {rate : compIndex → ℝ} (hrate : ∀ x, 0 ≤ rate x)
    (w : compIndex → ℝ) (hw : ∀ x, 0 ≤ w x)
    (hD : loopStepDefect (heatLoopStep tau rate) w = 0) :
    ∀ x, w x ≠ 0 → tau * rate x = 0 := by
  rw [heatLoopStep_defect] at hD
  have hnonneg : ∀ i ∈ Finset.univ,
      0 ≤ w i * (1 - Real.exp (-2 * tau * rate i)) :=
    fun i _ => mul_nonneg (hw i)
      (sub_nonneg.mpr (heat_multiplier_mem_Ioc htau hrate i).2)
  intro x hx
  have hiff := Finset.sum_eq_zero_iff_of_nonneg
    (s := Finset.univ)
    (f := fun i => w i * (1 - Real.exp (-2 * tau * rate i)))
    hnonneg
  have hterm : w x * (1 - Real.exp (-2 * tau * rate x)) = 0 :=
    hiff.mp hD x (Finset.mem_univ x)
  rcases mul_eq_zero.mp hterm with hw0 | h10
  · exact absurd hw0 hx
  · have hexp : Real.exp (-2 * tau * rate x) = 1 := by
      have h1 : (1 : ℝ) = Real.exp (-2 * tau * rate x) :=
        sub_eq_zero.mp h10
      exact h1.symm
    have harg : -2 * tau * rate x = 0 :=
      Real.exp_injective (show
        Real.exp (-2 * tau * rate x) = Real.exp 0 by
        rw [hexp, Real.exp_zero])
    have h2 : -2 * tau * rate x = -2 * (tau * rate x) := by ring
    rw [h2] at harg
    linarith

/-- **Discharge 3 (the fixed-sector hypothesis itself)**:
defect zero at a nonnegative weight implies the multiplier step
fixes the weight - at each mode, either the weight is zero or
the characterization gives `tau * rate x = 0`, so the
multiplier is `exp 0 = 1` there. -/
theorem heat_fixed_of_defect_zero {tau : ℝ} (htau : 0 ≤ tau)
    {rate : compIndex → ℝ} (hrate : ∀ x, 0 ≤ rate x)
    (w : compIndex → ℝ) (hw : ∀ x, 0 ≤ w x)
    (hD : loopStepDefect (heatLoopStep tau rate) w = 0) :
    (heatLoopStep tau rate).applyState w = w := by
  funext x
  by_cases hx : w x = 0
  · simp [heatLoopStep, hx]
  · have htr := heat_defect_eq_zero_occupied htau hrate w hw hD
      x hx
    have harg : -2 * tau * rate x = 0 := by
      have h2 : -2 * tau * rate x = -2 * (tau * rate x) := by ring
      rw [h2, htr]
      norm_num
    show Real.exp (-2 * tau * rate x) * w x = w x
    rw [harg, Real.exp_zero, one_mul]

/-- **THE OWNED NO-GO (Layer 2; Tier T1)**: at the composite's
autonomous multiplier step `heatLoopStep tau rate`
(`tau >= 0`, nonnegative rates), any exact autonomous cycle
(`StateClosed`, constant step list of length `n >= 1`, from a
nonnegative initial weight) has total defect zero in LOOP-0's
ledger form and every visited state fixed by the step - a chain
of fixed states. All three Layer-1 hypotheses are discharged
above; none is assumed here. -/
theorem heat_autonomous_no_go {tau : ℝ} (htau : 0 ≤ tau)
    {rate : compIndex → ℝ} (hrate : ∀ x, 0 ≤ rate x)
    (L : LoopData) (n : ℕ) (hn : 0 < n)
    (hsteps : L.steps
      = List.replicate n (heatLoopStep tau rate))
    (hrho : ∀ x, 0 ≤ L.initialState x)
    (hclosed : StateClosed L) :
    loopDefectSum L.steps L.initialState = 0
      ∧ ∀ k, k < n
        → (heatLoopStep tau rate).applyState
            (loopIter (heatLoopStep tau rate).applyState
              L.initialState k)
          = loopIter (heatLoopStep tau rate).applyState
              L.initialState k :=
  autonomous_no_go_defectSum (heatLoopStep tau rate) L n hn
    hsteps (fun w hw => heat_preserve rate w hw)
    (fun w hw => heat_defect_nonneg htau hrate w hw)
    (fun w => heat_weight_law tau rate w)
    (fun w hw hD => heat_fixed_of_defect_zero htau hrate w hw hD)
    hrho hclosed

/-- **The sharpened `eigComp` form (Tier T1)**: at the Q7CR-5
eigenvalue rate data `rate = eigComp` and positive step time
`tau > 0`, NO exact autonomous cycle of a weight state exists:
a nonnegative initial weight with total weight `1` cannot
return exactly. Reason: the no-go makes the initial state
(visited at `k = 0`) fixed, but `eigComp x >= 1 / 64 > 0`
(Q7CR-2) makes every multiplier `exp (-2 * tau * eigComp x)`
strictly below `1`, so a fixed weight vanishes at every mode,
contradicting total weight `1`. The fixed sector of this step
at positive time contains no weight state at all. -/
theorem heat_eig_no_return {tau : ℝ} (htau : 0 < tau)
    (L : LoopData) (n : ℕ) (hn : 0 < n)
    (hsteps : L.steps
      = List.replicate n (heatLoopStep tau eigComp))
    (hrho : ∀ x, 0 ≤ L.initialState x)
    (hsum : ∑ x, L.initialState x = 1)
    (hclosed : StateClosed L) : False := by
  have heig : ∀ x, 0 ≤ eigComp x :=
    fun x => by have h := eigComp_ge x; linarith
  have hzero : ∀ x, L.initialState x = 0 := by
    intro x
    show L.initialState x = 0
    by_contra hx
    have htr : tau * eigComp x = 0 :=
      heat_defect_eq_zero_occupied htau.le heig L.initialState
        hrho (by
          have hDsum : (∑ k ∈ Finset.range n,
              loopStepDefect (heatLoopStep tau eigComp)
                (loopIter (heatLoopStep tau eigComp).applyState
                  L.initialState k)) = 0 := by
            have h1 := (heat_autonomous_no_go htau.le heig L n hn
              hsteps hrho hclosed).1
            rwa [hsteps, loopDefectSum_replicate] at h1
          have hterm : ∀ i ∈ Finset.range n,
              0 ≤ loopStepDefect (heatLoopStep tau eigComp)
                (loopIter (heatLoopStep tau eigComp).applyState
                  L.initialState i) :=
            fun i _ => heat_defect_nonneg htau.le heig _
              (loopIter_nonneg _ (fun w hw =>
                heat_preserve eigComp w hw) _ hrho i)
          exact (Finset.sum_eq_zero_iff_of_nonneg hterm).mp
            hDsum 0 (Finset.mem_range.mpr hn)) x hx
    have hpos : 0 < tau * eigComp x :=
      mul_pos htau (by have h := eigComp_ge x; linarith)
    linarith
  have : (∑ x, L.initialState x) = 0 := by
    simp [hzero]
  linarith

/-! ## Section 4. The clock separation, as a theorem -/

/-- **The clock index shift has no fixed index**: advancing the
C4 factor's `Fin 4` coordinate by one always moves the index,
since `a + 1` is never `a` in `Fin 4`. -/
theorem z4ClockShiftIndex_ne (t : compIndex) :
    z4ClockShiftIndex t ≠ t := by
  intro h
  have h2 := congrArg (fun u : compIndex => u.1.2.1) h
  change t.1.2.1 + 1 = t.1.2.1 at h2
  exact (by decide : ∀ a : Fin 4, a + 1 ≠ a) _ h2

/-- **The clock step's defect is identically zero**: the
registered clock step `z4ClockStep k` has time `0` and rate
data `0`, so its `loopStepDefect` vanishes at every weight.
(This is why the nonneg and weight-law hypotheses are available
to permutation steps - and why the fixed-sector hypothesis,
not they, carries the separation.) -/
theorem z4ClockStep_defect_eq_zero (k : Fin 4)
    (w : compIndex → ℝ) :
    loopStepDefect (z4ClockStep k) w = 0 := by
  simp [loopStepDefect, z4ClockStep]

/-- **THE CLOCK SEPARATION (Tier T1)**: the load-bearing
fixed-sector hypothesis of `autonomous_no_go` FAILS at LOOP-0's
registered clock step, for its own registered defect. The
single-mode weight at the zero index is nonnegative, has clock
defect zero, and is moved by the clock step. Hence the no-go
cannot be applied to the Z4 clock shift: the hypothesis that
would be needed is false there, which is exactly the
statement-level separation of heat/ternary steps from
permutation steps that O1/O2 require. The clock remains what
LOOP-0 registered it as - IndexClosed only, a relabeling whose
Gibbs state is moved at `beta > 0` (Z4-KMS-1, cited there). -/
theorem clock_fixed_sector_fails :
    ∃ w : compIndex → ℝ, (∀ x, 0 ≤ w x)
      ∧ loopStepDefect (z4ClockStep 0) w = 0
      ∧ (z4ClockStep 0).applyState w ≠ w := by
  classical
  refine ⟨fun t => if t = (((0, 0), (0, 0)), 0) then 1 else 0,
    ?_, ?_, ?_⟩
  · intro x
    by_cases hx : x = (((0, 0), (0, 0)), 0) <;> simp [hx]
  · exact z4ClockStep_defect_eq_zero 0 _
  · intro hcon
    have hne := z4ClockShiftIndex_ne (((0, 0), (0, 0)), 0)
    have hval := congrFun hcon (((0, 0), (0, 0)), 0)
    simp only [z4ClockStep, hne, ite_false, ite_true] at hval
    norm_num at hval

#print axioms autonomous_no_go
#print axioms autonomous_no_go_defectSum
#print axioms heat_autonomous_no_go
#print axioms heat_eig_no_return
#print axioms clock_fixed_sector_fails

end ThetLogos
