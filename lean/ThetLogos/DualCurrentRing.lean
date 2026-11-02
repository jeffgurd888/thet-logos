import Mathlib.Tactic

/-!
# ThetLogos.DualCurrentRing — DUAL-CURRENT F1: the ring model

**Status: NO CLAIM. Definitions and finite theorems only. This line
moves no dial (dials stay 0/4).**

Registration source: `dual-current-theory-charter-2026-11-01.md`
(§2 D1–D4, §3 F1, §4 kills K-DC-1..4, §5b naming). Jeff's fire order
2026-11-01 22:33 EST ("3 fire").

Named for Edward Leedskalnin (1887–1951), builder of Coral Castle, whose
*Magnetic Current* (1945) posed the counter-streaming picture this theory
makes checkable. Named for the question he asked, not for his answers —
his answers keep their audited grades (see §6).

## What this module is

The F1 ring model: sites `ZMod n`, a current `j : ZMod n → ℚ`, and three
bookkeeping functionals — energy `dcEnergy j = ∑ i, (j i)^2`, the
forward-difference helicity analogue
`dcHelicity j = ∑ i, j i * (j (i + 1) - j i)`, and the churn of a channel
pair `dcChurn jp jm = ∑ i, -(jp i * jm i)`.

Charter D1, on the face: a channel split is a bookkeeping choice, not a
discovery. These definitions are bookkeeping; nothing here asserts what
any physical channel *is*.

Charter D4, net-vs-churn reading of the three defs: `dcEnergy` measures
the size of a current (the net-transport side); `dcChurn jp jm` is
positive exactly where the two channels counter-stream — opposed flow
that transports nothing net; `dcHelicity` reads the current against its
own forward difference. The headline identity `dcEnergy_add` is the
bookkeeping split of the net energy of a two-channel current into the
channel energies minus twice the churn.

## Fences (charter §4, armed before the build)

- K-DC-1 (relabeling kill): no monopole reading. The channels are
  bookkeeping channels `+`/`-`; nothing in this module is a claim that
  Leedskalnin's monopole particles exist or were vindicated.
- K-DC-2 (coupling kill): no coupling term appears in this module; no
  term of the dropped document's type is asserted here.
- K-DC-3 (energy kill): no energy-surplus statement appears here;
  `dcEnergy_add` is an exact identity, not an extraction claim.
- K-DC-4 (anchor-theft kill): the T4 anchors — spin currents, Berry
  connections, the paramagnetic/diamagnetic split, ring persistent
  currents — are the literature's results, never this line's results.
  Nothing in this module presents them otherwise.

NO CLAIM. This line moves no dial.
-/

namespace ThetLogos

variable {n : ℕ} [NeZero n]

def dcEnergy (j : ZMod n → ℚ) : ℚ := ∑ i, (j i) ^ 2

def dcHelicity (j : ZMod n → ℚ) : ℚ := ∑ i, j i * (j (i + 1) - j i)

def dcChurn (jp jm : ZMod n → ℚ) : ℚ := ∑ i, -(jp i * jm i)

/-- The single reindex the F1 identities need: shifting the summation
index by `1` permutes `ZMod n`, so the sum of the shifted squares is the
sum of the squares. -/
private theorem sum_sq_shift (j : ZMod n → ℚ) :
    ∑ i, (j (i + 1)) ^ 2 = ∑ i, (j i) ^ 2 := by
  apply Fintype.sum_equiv (Equiv.addRight (1 : ZMod n))
  intro i
  simp [Equiv.addRight]

theorem dcEnergy_nonneg (j : ZMod n → ℚ) : 0 ≤ dcEnergy j := by
  unfold dcEnergy
  exact Finset.sum_nonneg fun i _ => by positivity

theorem dcHelicity_eq_neg_half (j : ZMod n → ℚ) :
    dcHelicity j = -(1/2) * ∑ i, (j (i + 1) - j i) ^ 2 := by
  have hshift : ∑ i, (j (i + 1)) ^ 2 = ∑ i, (j i) ^ 2 := sum_sq_shift j
  have hD : ∑ i, (j (i + 1) - j i) ^ 2
      = ∑ i, (j (i + 1)) ^ 2 + ∑ i, (j i) ^ 2
        - 2 * (∑ i, j i * j (i + 1)) := by
    have h1 : ∑ i, (j (i + 1) - j i) ^ 2
        = ∑ i, ((j (i + 1)) ^ 2 + (j i) ^ 2 - 2 * (j i * j (i + 1))) :=
      Finset.sum_congr rfl fun i _ => by ring
    rw [h1, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hH : dcHelicity j = (∑ i, j i * j (i + 1)) - ∑ i, (j i) ^ 2 := by
    have h1 : dcHelicity j = ∑ i, (j i * j (i + 1) - (j i) ^ 2) := by
      unfold dcHelicity
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [h1, Finset.sum_sub_distrib]
  rw [hH, hD, hshift]
  ring

theorem dcHelicity_nonpos (j : ZMod n → ℚ) : dcHelicity j ≤ 0 := by
  rw [dcHelicity_eq_neg_half]
  have h : 0 ≤ ∑ i, (j (i + 1) - j i) ^ 2 :=
    Finset.sum_nonneg fun i _ => by positivity
  linarith

theorem dcHelicity_eq_zero_iff (j : ZMod n → ℚ) :
    dcHelicity j = 0 ↔ ∀ i k, j i = j k := by
  constructor
  · intro h
    rw [dcHelicity_eq_neg_half] at h
    have hD : ∑ i, (j (i + 1) - j i) ^ 2 = 0 := by linarith
    have hnonneg : ∀ i ∈ (Finset.univ : Finset (ZMod n)),
        0 ≤ (j (i + 1) - j i) ^ 2 := fun i _ => by positivity
    rw [Finset.sum_eq_zero_iff_of_nonneg hnonneg] at hD
    have hstep : ∀ i, j (i + 1) = j i := by
      intro i
      have h2 := hD i (Finset.mem_univ i)
      have hi : j (i + 1) - j i = 0 := by simpa using h2
      exact sub_eq_zero.mp hi
    have hwalk : ∀ (a : ZMod n) (m : ℕ), j (a + (m : ZMod n)) = j a := by
      intro a m
      induction m with
      | zero => simp
      | succ m ih =>
        have hcast : ((m + 1 : ℕ) : ZMod n) = (m : ZMod n) + 1 := by
          push_cast
          ring
        rw [hcast, ← add_assoc, hstep (a + (m : ZMod n)), ih]
    intro i k
    have hk : i + ((k - i).val : ZMod n) = k := by
      rw [ZMod.natCast_zmod_val, add_comm]
      exact sub_add_cancel k i
    calc j i = j (i + ((k - i).val : ZMod n)) := (hwalk i _).symm
      _ = j k := by rw [hk]
  · intro h
    unfold dcHelicity
    apply Finset.sum_eq_zero
    intro i _
    rw [h (i + 1) i, sub_self, mul_zero]

theorem dcHelicity_abs_le (j : ZMod n → ℚ) : |dcHelicity j| ≤ 2 * dcEnergy j := by
  have hshift : ∑ i, (j (i + 1)) ^ 2 = ∑ i, (j i) ^ 2 := sum_sq_shift j
  have hDle : ∑ i, (j (i + 1) - j i) ^ 2 ≤ 4 * dcEnergy j := by
    have hpt : ∀ i, (j (i + 1) - j i) ^ 2
        ≤ 2 * (j (i + 1)) ^ 2 + 2 * (j i) ^ 2 :=
      fun i => by nlinarith [sq_nonneg (j (i + 1) + j i)]
    calc ∑ i, (j (i + 1) - j i) ^ 2
        ≤ ∑ i, (2 * (j (i + 1)) ^ 2 + 2 * (j i) ^ 2) :=
          Finset.sum_le_sum fun i _ => hpt i
      _ = 2 * (∑ i, (j (i + 1)) ^ 2) + 2 * (∑ i, (j i) ^ 2) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      _ = 4 * dcEnergy j := by
          rw [hshift]
          unfold dcEnergy
          ring
  have hH := dcHelicity_eq_neg_half j
  have hnonpos := dcHelicity_nonpos j
  rw [abs_of_nonpos hnonpos, hH]
  linarith

theorem dcEnergy_add (jp jm : ZMod n → ℚ) :
    dcEnergy (jp + jm) = dcEnergy jp + dcEnergy jm - 2 * dcChurn jp jm := by
  unfold dcEnergy dcChurn
  have hC : (∑ i, -(jp i * jm i)) = -∑ i, jp i * jm i := by
    rw [Finset.sum_neg_distrib]
  have h1 : (∑ i, ((jp + jm) i) ^ 2)
      = ∑ i, ((jp i) ^ 2 + (jm i) ^ 2 + 2 * (jp i * jm i)) :=
    Finset.sum_congr rfl fun i _ => by simp only [Pi.add_apply]; ring
  rw [h1, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hC]
  ring

end ThetLogos

#print axioms ThetLogos.dcEnergy_nonneg
#print axioms ThetLogos.dcHelicity_eq_neg_half
#print axioms ThetLogos.dcHelicity_nonpos
#print axioms ThetLogos.dcHelicity_eq_zero_iff
#print axioms ThetLogos.dcHelicity_abs_le
#print axioms ThetLogos.dcEnergy_add
