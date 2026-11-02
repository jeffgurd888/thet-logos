import ThetLogos.DualCurrentRing
import Mathlib.Tactic

/-!
# ThetLogos.DualCurrentLeedskalnin — DUAL-CURRENT F2: the Leedskalnin configuration

**Status: NO CLAIM. Definitions and finite theorems only. This line
moves no dial (dials stay 0/4).**

Registration source: `dual-current-theory-charter-2026-11-01.md`
(§2 D2, §3 F2, §4 kills K-DC-1..4, §5b naming).

Named for Edward Leedskalnin (1887–1951), builder of Coral Castle, whose
*Magnetic Current* (1945) posed the counter-streaming picture this theory
makes checkable. Named for the question he asked, not for his answers —
his answers keep their audited grades (see §6).

## What this module is

The Leedskalnin configuration is the pure counter-streaming state
`j+ = -j-` (all churn, no net current). `leedskalninConfig` parametrizes
ALL of them by a single channel field `a : ZMod n → ℚ`, and on such a
configuration the churn is exactly the energy of the single channel
(`leedskalnin_churn_eq_energy`): `dcChurn a (-a) = dcEnergy a`.

`dcProject` is a STATED update rule (a definition, this line's choice —
charter F2 asks for stability under stated update rules); its fixed
points are EXACTLY the Leedskalnin configurations
(`dcProject_eq_self_iff`) — that fixed-point statement is the finite,
exact sense in which a closed loop "holds" a circulating state.

## Fences (charter §4, armed before the build)

- K-DC-1: the configuration is a state of two bookkeeping channels,
  not evidence for monopole particles.
- K-DC-3: a fixed point is not an energy source; no energy claim
  attaches; the PMH stays remanence. In particular
  `dcProject_eq_self_iff` is a fixed-point statement about a
  DEFINITION (`dcProject`); no energy statement about the projection
  appears in this module.

NO CLAIM; no dial moves.
-/

namespace ThetLogos

variable {n : ℕ} [NeZero n]

def IsLeedskalninConfig (jp jm : ZMod n → ℚ) : Prop := ∀ i, jm i = - jp i

def leedskalninConfig (a : ZMod n → ℚ) : (ZMod n → ℚ) × (ZMod n → ℚ) := (a, -a)

theorem leedskalninConfig_isLeedskalnin (a : ZMod n → ℚ) :
    IsLeedskalninConfig (leedskalninConfig a).1 (leedskalninConfig a).2 := by
  intro i
  simp [leedskalninConfig, Pi.neg_apply]

theorem leedskalninConfig_injective :
    Function.Injective (leedskalninConfig (n := n)) := by
  intro a b hab
  exact congrArg Prod.fst hab

theorem isLeedskalninConfig_iff (jp jm : ZMod n → ℚ) :
    IsLeedskalninConfig jp jm ↔ ∃ a, leedskalninConfig a = (jp, jm) := by
  constructor
  · intro h
    refine ⟨jp, Prod.ext rfl ?_⟩
    funext i
    simp only [leedskalninConfig, Pi.neg_apply]
    exact (h i).symm
  · rintro ⟨a, ha⟩
    intro i
    have h1 : a = jp := congrArg Prod.fst ha
    have h2 : -a = jm := congrArg Prod.snd ha
    rw [← h2, ← h1]
    simp [Pi.neg_apply]

theorem leedskalnin_net_eq_zero (jp jm : ZMod n → ℚ)
    (h : IsLeedskalninConfig jp jm) : jp + jm = 0 := by
  funext i
  simp only [Pi.add_apply, Pi.zero_apply, h i]
  exact add_neg_cancel _

theorem leedskalnin_churn_eq_energy (jp jm : ZMod n → ℚ)
    (h : IsLeedskalninConfig jp jm) : dcChurn jp jm = dcEnergy jp := by
  unfold dcChurn dcEnergy
  apply Finset.sum_congr rfl
  intro i _
  rw [h i]
  ring

def dcProject (jp jm : ZMod n → ℚ) : (ZMod n → ℚ) × (ZMod n → ℚ) :=
  (fun i => (jp i - jm i) / 2, fun i => (jm i - jp i) / 2)

theorem dcProject_isLeedskalnin (jp jm : ZMod n → ℚ) :
    IsLeedskalninConfig (dcProject jp jm).1 (dcProject jp jm).2 := by
  intro i
  simp only [dcProject]
  ring

theorem dcProject_idempotent (jp jm : ZMod n → ℚ) :
    dcProject (dcProject jp jm).1 (dcProject jp jm).2 = dcProject jp jm := by
  apply Prod.ext
  · funext i
    simp only [dcProject]
    ring
  · funext i
    simp only [dcProject]
    ring

/-- K-DC-3 fence: this is a fixed-point statement about a DEFINITION
(`dcProject`) — a fixed point is not an energy source; no energy claim
attaches to the projection; the PMH stays remanence. -/
theorem dcProject_eq_self_iff (jp jm : ZMod n → ℚ) :
    dcProject jp jm = (jp, jm) ↔ IsLeedskalninConfig jp jm := by
  constructor
  · intro h i
    have h1 : (dcProject jp jm).1 = jp := congrArg Prod.fst h
    have hi : (jp i - jm i) / 2 = jp i := congrFun h1 i
    linarith
  · intro h
    apply Prod.ext
    · funext i
      show (jp i - jm i) / 2 = jp i
      rw [h i]
      ring
    · funext i
      show (jm i - jp i) / 2 = jm i
      rw [h i]
      ring

theorem dcProject_net_eq_zero (jp jm : ZMod n → ℚ) :
    (dcProject jp jm).1 + (dcProject jp jm).2 = 0 := by
  funext i
  simp only [dcProject, Pi.add_apply, Pi.zero_apply]
  ring

end ThetLogos

#print axioms ThetLogos.leedskalninConfig_isLeedskalnin
#print axioms ThetLogos.leedskalninConfig_injective
#print axioms ThetLogos.isLeedskalninConfig_iff
#print axioms ThetLogos.leedskalnin_net_eq_zero
#print axioms ThetLogos.leedskalnin_churn_eq_energy
#print axioms ThetLogos.dcProject_isLeedskalnin
#print axioms ThetLogos.dcProject_idempotent
#print axioms ThetLogos.dcProject_eq_self_iff
#print axioms ThetLogos.dcProject_net_eq_zero
