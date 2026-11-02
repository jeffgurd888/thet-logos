import ThetLogos.DualCurrentRing
import ThetLogos.DualCurrentLeedskalnin
import Mathlib.Tactic

/-!
# ThetLogos.DualCurrentMixing — DUAL-CURRENT F3: helicity bookkeeping under channel mixing

**Status: NO CLAIM. Definitions and finite theorems only. This line
moves no dial (dials stay 0/4).**

Registration source: `dual-current-theory-charter-2026-11-01.md`
(§3 F3, §4 kills K-DC-1..4, §5b naming).

Named for Edward Leedskalnin (1887–1951), builder of Coral Castle, whose
*Magnetic Current* (1945) posed the counter-streaming picture this theory
makes checkable. Named for the question he asked, not for his answers —
his answers keep their audited grades (see §6).

## What this module is

Charter F3: if a stated dynamics mixes the channels, which of the
helicity, the channel helicities, and the churn are conserved, and which
provably are not? The mixing here is a STATED DEFINITION, not a physical
dynamics: `dcMix t jp jm` replaces the channel pair `(jp, jm)` by
`((1 - t) • jp + t • jm, t • jp + (1 - t) • jm)` pointwise.

## F3 verdict table (on the face)

Under the stated mixing `dcMix`:

- CONSERVED (proved): the net field itself (`dcMix_net`:
  `(dcMix t jp jm).1 + (dcMix t jp jm).2 = jp + jm`), hence `dcEnergy`
  and `dcHelicity` of the net (`dcMix_dcEnergy_net`,
  `dcMix_dcHelicity_net`). The helicity of a sum splits exactly as
  channel helicities plus the cross-helicity `dcCrossHelicity`
  (`dcHelicity_add`), and helicity is quadratic under scaling
  (`dcHelicity_smul`).
- NOT CONSERVED (killed by counterexample at `n = 2`, `t = 1/2`,
  witnesses `dcExA`/`dcExB`): channel energies, singly
  (`dcMix_channelEnergy_counterexample`: `1/4 ≠ 1`) and in total
  (`dcMix_totalChannelEnergy_counterexample`: `1/2 ≠ 1`); channel
  helicities (`dcMix_channelHelicity_counterexample`: `-1/4 ≠ -1`);
  total churn (`dcMix_churn_counterexample`: `-1/2 ≠ 0`); and
  cross-helicity (`dcMix_crossHelicity_counterexample`: `0 ≠ 2`).
  Each counterexample theorem states BOTH the `t = 1/2` value and the
  unmixed value — the pair of values IS the kill. The charter's naive
  F3 hope of channel-wise conservation under mixing is KILLED.

## Fences (charter §4, armed before the build)

- K-DC-1 (relabeling kill): no monopole reading. The channels are
  bookkeeping channels; nothing in this module is a claim that
  Leedskalnin's monopole particles exist or were vindicated.
- K-DC-2 (coupling kill): no coupling term appears in this module.
- K-DC-3 (energy kill): no energy claim — mixing here is a stated
  definition, not a physical dynamics; the counterexample values are
  bookkeeping values of the stated functionals, not extracted or
  destroyed physical energy.
- K-DC-4 (anchor-theft kill): the T4 anchors are the literature's
  results, never this line's results.

NO CLAIM; no dial moves.
-/

namespace ThetLogos

variable {n : ℕ} [NeZero n]

def dcMix (t : ℚ) (jp jm : ZMod n → ℚ) : (ZMod n → ℚ) × (ZMod n → ℚ) :=
  (fun i => (1 - t) * jp i + t * jm i, fun i => t * jp i + (1 - t) * jm i)

theorem dcMix_net (t : ℚ) (jp jm : ZMod n → ℚ) :
    (dcMix t jp jm).1 + (dcMix t jp jm).2 = jp + jm := by
  funext i
  simp only [dcMix, Pi.add_apply]
  ring

theorem dcMix_dcEnergy_net (t : ℚ) (jp jm : ZMod n → ℚ) :
    dcEnergy ((dcMix t jp jm).1 + (dcMix t jp jm).2) = dcEnergy (jp + jm) := by
  rw [dcMix_net]

theorem dcMix_dcHelicity_net (t : ℚ) (jp jm : ZMod n → ℚ) :
    dcHelicity ((dcMix t jp jm).1 + (dcMix t jp jm).2) = dcHelicity (jp + jm) := by
  rw [dcMix_net]

def dcCrossHelicity (jp jm : ZMod n → ℚ) : ℚ :=
  ∑ i, (jp i * (jm (i + 1) - jm i) + jm i * (jp (i + 1) - jp i))

theorem dcHelicity_add (jp jm : ZMod n → ℚ) :
    dcHelicity (jp + jm) = dcHelicity jp + dcHelicity jm +
      dcCrossHelicity jp jm := by
  unfold dcHelicity dcCrossHelicity
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.add_apply]
  ring

theorem dcHelicity_smul (c : ℚ) (j : ZMod n → ℚ) :
    dcHelicity (c • j) = c ^ 2 * dcHelicity j := by
  unfold dcHelicity
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-! ## Counterexample package at `n = 2`

Kills of the channel-wise conservation claims. Each theorem states BOTH
values — the pair of values IS the kill. -/

/-- The two-point sum over `ZMod 2`, by finite enumeration (`decide` on
the Finset identity over the 2-element type — a finite shadow, not a
Rat-arithmetic goal). -/
private theorem sum_zmod_two (f : ZMod 2 → ℚ) : ∑ i, f i = f 0 + f 1 := by
  have huniv : (Finset.univ : Finset (ZMod 2)) = {0, 1} := by decide
  rw [huniv, Finset.sum_pair (by decide)]

def dcExA : ZMod 2 → ℚ := fun i => if i = 0 then 1 else 0

def dcExB : ZMod 2 → ℚ := fun i => if i = 0 then 0 else 1

theorem dcMix_channelEnergy_counterexample :
    dcEnergy (dcMix (1/2) dcExA 0).1 = 1/4 ∧ dcEnergy dcExA = 1 := by
  constructor
  · simp only [dcEnergy, dcMix, dcExA, Pi.zero_apply]
    rw [sum_zmod_two]
    norm_num
  · simp only [dcEnergy, dcExA]
    rw [sum_zmod_two]
    norm_num

theorem dcMix_channelHelicity_counterexample :
    dcHelicity (dcMix (1/2) dcExA 0).1 = -1/4 ∧ dcHelicity dcExA = -1 := by
  have h01 : (0 : ZMod 2) + 1 = 1 := by decide
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  constructor
  · simp only [dcHelicity, dcMix, Pi.zero_apply]
    rw [sum_zmod_two, h01, h11]
    simp only [dcExA]
    norm_num
  · simp only [dcHelicity]
    rw [sum_zmod_two, h01, h11]
    simp only [dcExA]
    norm_num

theorem dcMix_totalChannelEnergy_counterexample :
    dcEnergy (dcMix (1/2) dcExA 0).1 + dcEnergy (dcMix (1/2) dcExA 0).2 = 1/2 ∧
      dcEnergy dcExA + dcEnergy (0 : ZMod 2 → ℚ) = 1 := by
  constructor
  · simp only [dcEnergy, dcMix, dcExA, Pi.zero_apply]
    rw [sum_zmod_two, sum_zmod_two]
    norm_num
  · simp only [dcEnergy, dcExA, Pi.zero_apply]
    rw [sum_zmod_two, sum_zmod_two]
    norm_num

theorem dcMix_churn_counterexample :
    dcChurn (dcMix (1/2) dcExA dcExB).1 (dcMix (1/2) dcExA dcExB).2 = -1/2 ∧
      dcChurn dcExA dcExB = 0 := by
  constructor
  · simp only [dcChurn, dcMix, dcExA, dcExB]
    rw [sum_zmod_two]
    norm_num
  · simp only [dcChurn, dcExA, dcExB]
    rw [sum_zmod_two]
    norm_num

theorem dcMix_crossHelicity_counterexample :
    dcCrossHelicity (dcMix (1/2) dcExA dcExB).1 (dcMix (1/2) dcExA dcExB).2 = 0 ∧
      dcCrossHelicity dcExA dcExB = 2 := by
  have h01 : (0 : ZMod 2) + 1 = 1 := by decide
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  constructor
  · simp only [dcCrossHelicity, dcMix]
    rw [sum_zmod_two, h01, h11]
    simp only [dcExA, dcExB]
    norm_num
  · simp only [dcCrossHelicity]
    rw [sum_zmod_two, h01, h11]
    simp only [dcExA, dcExB]
    norm_num

end ThetLogos

#print axioms ThetLogos.dcMix_net
#print axioms ThetLogos.dcMix_dcEnergy_net
#print axioms ThetLogos.dcMix_dcHelicity_net
#print axioms ThetLogos.dcHelicity_add
#print axioms ThetLogos.dcHelicity_smul
#print axioms ThetLogos.dcMix_channelEnergy_counterexample
#print axioms ThetLogos.dcMix_channelHelicity_counterexample
#print axioms ThetLogos.dcMix_totalChannelEnergy_counterexample
#print axioms ThetLogos.dcMix_churn_counterexample
#print axioms ThetLogos.dcMix_crossHelicity_counterexample
