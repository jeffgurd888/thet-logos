import Mathlib.Tactic
import ThetLogos.ContinuumCyclePin

/-!
# ThetLogos.ContinuumCycleBrick1 — the cycle closes on Fin 2; a snap, exhibited (T5 charter; NO CLAIM)

Working label only — naming is Zero's hand. Brick 1 of
the Continuum Cycle line: the smallest-seat content of
`cycleCloses`, and a concrete snap in the pinned order
E → M → C.

## Verdicts

- **`cycleCloses` PROVED on the Fin 2 seat**
  (`cycleCloses_finTwo`). On `cycleSeatFinTwo` (charge
  `![1, -1]`, distant `{0}`, exchange swapping the two
  points), the configuration `![1/2, 1/2]` is balanced
  and standing: normalised (weights sum to `1`), zero
  net charge, and maximal-entropy over the normalised
  zero-charge class — on Fin 2 with this charge that
  class is the single point `![1/2, 1/2]` itself (the
  two constraints `r 0 + r 1 = 1` and `r 0 - r 1 = 0`
  fix it), so maximality is by uniqueness. It stands
  under the exchange because it is constant. Since
  Brick 0 registered decay as bare return, this
  balanced standing configuration is the return
  `cycleCloses` asks for, for every snap. **K-CYCLE-OPEN
  does not fire on this seat.** (Registered honestly:
  the bare-return registration is what makes this
  provable without a decay operator; tying the return
  to the snap's own endpoint is the strengthening a
  decay operator would make, still owed.)
- **A snap, exhibited in the pinned order**
  (`snapExhibit`). On the Fin 3 seat (charge
  `![1, -1, 2]`, distant `{2}`, exchange swapping 0
  and 2): stage E `![0, 2, 1]` splits the charge
  (distant charge `2`, complement charge `-2`); stage
  M `![1, 2, 0]` is stage E carried by the exchange;
  stage C `![0, 1, 0]` condenses stage M (it stands,
  and carries charge `-1` undiminished). The three
  stage properties are checked by computation in
  `snap_split`, `snap_motion`, `snap_condenses`.
  **K-SNAP-ORDER is not tested by an exhibit** — one
  snap in the order does not show every snap is forced
  through it; the kill stays armed, and this brick
  says so.

## Walls named on the face

- **K-SHADOW-IDENTITY** (standing tension, unsoftened):
  shadows hold for every weighting and pick out no
  gravity object. This line does not dissolve it and
  claims no gravity object.
- Per Zero's register (2026-11-24): a completed finite
  theorem is not a continuum theorem. T5 charter,
  NO CLAIM; dials 0/4.
-/

namespace ThetLogos

/-- **The Fin 2 cycle seat.** Charge `![1, -1]`,
distant component `{0}`, exchange swapping the two
points of the seat. -/
def cycleSeatFinTwo : CycleSeat (Fin 2) :=
  { charge := ![1, -1], distant := {0}, exch := ![1, 0] }

/-- **`cycleCloses` on the Fin 2 seat.** For every
snap, the balanced standing configuration
`![1/2, 1/2]` is the return: normalised, zero-charge,
and the unique — hence maximal-entropy — point of the
normalised zero-charge class; standing because
constant. K-CYCLE-OPEN does not fire here. -/
theorem cycleCloses_finTwo : cycleCloses cycleSeatFinTwo := by
  intro _snap
  refine ⟨![1/2, 1/2], ⟨?_, ?_, ?_⟩, ?_⟩
  · norm_num [Fin.sum_univ_two]
  · norm_num [nedZeroCharge, nedCharge, cycleSeatFinTwo,
      Fin.sum_univ_two]
  · intro r hsum hzc
    have hsum' : r 0 + r 1 = 1 := by
      simpa [Fin.sum_univ_two] using hsum
    have hzc' : r 0 - r 1 = 0 := by
      have h := hzc
      simp [nedZeroCharge, nedCharge, cycleSeatFinTwo,
        Fin.sum_univ_two] at h
      linarith
    have hr0 : r 0 = 1 / 2 := by linarith
    have hr1 : r 1 = 1 / 2 := by linarith
    have hent : nedEntropy r
        = -(r 0 * Real.log (r 0) + r 1 * Real.log (r 1)) := by
      simp [nedEntropy, gibbsEntropy, Fin.sum_univ_two]
    have hentp : nedEntropy ![1 / 2, 1 / 2]
        = -(1 / 2 * Real.log (1 / 2)
          + 1 / 2 * Real.log (1 / 2)) := by
      simp [nedEntropy, gibbsEntropy, Fin.sum_univ_two]
    rw [hent, hentp, hr0, hr1]
  · funext i
    fin_cases i <;> simp [cycleSeatFinTwo]

/-- **The Fin 3 cycle seat of the snap exhibit.**
Charge `![1, -1, 2]`, distant component `{2}`,
exchange swapping 0 and 2 and fixing 1. -/
def cycleSeatFinThree : CycleSeat (Fin 3) :=
  { charge := ![1, -1, 2], distant := {2}, exch := ![2, 1, 0] }

/-- **Stage E, checked.** `![0, 2, 1]` splits the
charge across the pair on `cycleSeatFinThree`: the
distant component carries `1 * 2 = 2 ≠ 0`, the
complement carries `0 * 1 + 2 * (-1) = -2`, and the
two cancel. -/
theorem snap_split :
    cycleChargeSplit cycleSeatFinThree ![0, 2, 1] := by
  constructor
  · norm_num [cycleChargeOn, cycleSeatFinThree]
  · have hcompl : ({2} : Finset (Fin 3))ᶜ = {0, 1} := by decide
    norm_num [cycleChargeOn, cycleSeatFinThree, hcompl]

/-- **Stage M, checked.** `![1, 2, 0]` is
`![0, 2, 1]` carried by the exchange `![2, 1, 0]`:
position 0 receives stage E's position-2 weight,
position 2 receives its position-0 weight, position 1
is fixed. -/
theorem snap_motion :
    cycleRingMotion cycleSeatFinThree ![0, 2, 1] ![1, 2, 0] := by
  funext i
  fin_cases i <;> simp [cycleSeatFinThree]

/-- **Stage C, checked.** `![0, 1, 0]` condenses
`![1, 2, 0]`: it stands under the exchange (its
position-0 and position-2 weights agree) and carries
the motion stage's charge `-1` undiminished. -/
theorem snap_condenses :
    cycleCondensed cycleSeatFinThree ![1, 2, 0] ![0, 1, 0] := by
  constructor
  · funext i
    fin_cases i <;> simp [cycleSeatFinThree]
  · norm_num [nedCharge, cycleSeatFinThree, Fin.sum_univ_three]

/-- **The snap exhibit.** One concrete `CycleSnap` on
`cycleSeatFinThree`, its three stages in the pinned
order E → M → C, each stage property checked by the
three theorems above. An exhibit in the order — not a
proof that the order is forced; K-SNAP-ORDER stays
armed. -/
def snapExhibit : CycleSnap cycleSeatFinThree :=
  ⟨![0, 2, 1], ![1, 2, 0], ![0, 1, 0],
    snap_split, snap_motion, snap_condenses⟩

end ThetLogos
