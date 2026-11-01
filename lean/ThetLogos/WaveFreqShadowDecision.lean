import Mathlib.Tactic
import ThetLogos.WaveModeIdentification

namespace ThetLogos

open scoped InnerProductSpace
open Finset

/-!
# ThetLogos.WaveFreqShadowDecision - GR-PROP-3: the frequency-shadow decision

**Working label only.** The module name
`WaveFreqShadowDecision` and the line name GR-PROP are
working labels; Jeff names.

**Status: GR-PROP-3 landing brick. NO CLAIM. Dial 2 = 0
under every outcome of this line, including total
success. No gravity object is defined, constructed, or
asserted to exist.**

## The candidate seat, named in advance (first write)

- Seat size: `N = 2`.
- Named plaquette: `seatPlaq : PlaqDatum 2`, base the zero
  layer site, directions `mu = 1`, `nu = 2`.
- Named mode: `seatMode = gaugeAngle seatPhi`, the
  longitudinal (pure-gauge) mode of GR-PROP-2's stationary
  gauge sector, for the named site potential
  `seatPhi c = ((c.1 1).val : R)` (the site's
  coordinate-`1` value, read in `R`) - exactly the witness
  potential of MAX-3's `hasEigenvalue_zero`.
- Named frequencies: `omega = 0` (unperturbed),
  `omega' = 0` (perturbed).
- Named stated shift: `statedShift = 0`.

## Verdict (proved below)

**HOLDS at the named seat above.** All three clauses of
the registered predicate hold at that seat:

1. `seatMode` is a `ModeFreq` mode of `maxwellOp 2` at
   frequency `0` (MAX-2's `maxwellOp_gaugeAngle`: gauge
   modes are in the kernel).
2. `seatMode` is a `ModeFreq` mode of the named defect
   operator `onePlaqDefectOp 2 seatPlaq` at frequency
   `0`: the defect's rank-one term at `seatPlaq` is
   `plaqSign seatPlaq l * plaqAngle seatPlaq seatMode`,
   and the plaquette angle of a pure-gauge mode vanishes
   at EVERY plaquette by additive telescoping (MAX-2's
   `maxwellM3_proved`), so the defect term is exactly
   zero on this mode.
3. The stated shift `0` equals the computed
   `FreqShift ... 0 0 = 0 - 0 = 0`.

This is the longitudinal sector's stationarity read
through the defect: honest finite eigenvalue arithmetic
only, named as such (the pin's K-PROP-STATIC fence) -
the perturbation is invisible to this mode because its
plaquette angle at the defect plaquette is zero, not
because any propagation fact holds. No statement about
any transverse mode's defect shift is made or implied
here; GR-PROP-2's completeness seam is NOT consumed and
NOT needed: this is a seat fact about one named mode.

## Inputs consumed, and not consumed

- GR-PROP-0 (`WaveFamilyPost.lean`): the registered
  predicate `PoseObjBFreqShadow`, its read-back
  `poseObjBFreqShadow_unfold`, `ModeFreq`, `FreqShift`
  and `freqShift_unfold`, and the frozen perturbation
  `onePlaqDefectOp`. The predicate is NOT repaired,
  weakened, or re-registered.
- GR-PROP-1 (`WaveFamilyWeld.lean`): consumed through
  GR-PROP-2's stationary-sector headline, which is built
  on `linkWaveFamily`.
- GR-PROP-2 (`WaveModeIdentification.lean`, PARTIAL):
  its `ModeFreq` instance for the gauge sector at
  frequency `0` (`gaugeModeC_modeFreq_zero`) and its
  stationarity headline (`gaugeModeC_stationary`) are
  consumed as seat corollaries below. Its completeness
  seam is NOT an input and is not needed.
- MAX-3 clause 4 is NOT an input, not consumed, not
  implied anywhere in this brick.

## Fences (binding)

- A statement about a registered finite predicate at a
  named seat - not gravity, not propagation-as-physics.
  The chair receives candidates; it does not seat them.
- Frequencies and the stated shift are named/supplied,
  never existentially quantified (K-GR-VAC).
- Ceiling on the face: Dial 2 unmoved by anything in
  this brick; NO CLAIM.
-/

section Seat

/-- **The named seat potential.** The site potential of
MAX-3's zero-eigenvalue witness: the value of the site's
coordinate `Fin.succ 0` (= direction `1`), read in `R`. -/
def seatPhi : LayerSite 2 → ℝ :=
  fun c => ((c.1 (Fin.succ (0 : Fin 3))).val : ℝ)

/-- **The named seat plaquette**: base the zero layer
site, directions `mu = 1`, `nu = 2` in `Fin 4`. -/
def seatPlaq : PlaqDatum 2 where
  base := zeroLayerSite
  mu := 1
  nu := 2
  hmu := by decide
  hnu := by decide
  hne := by decide

/-- **The named seat mode**: the pure-gauge (longitudinal)
link angle of `seatPhi` - GR-PROP-2's stationary gauge
sector, at the real seat of the registered predicate. -/
def seatMode : linkAngle 2 :=
  gaugeAngle seatPhi

/-- **The seat mode is nonzero**: its value at the link
from the zero layer site in direction `Fin.succ 0` is
exactly `1` (the head site's coordinate value is `1`, the
tail's is `0`) - the same computation as MAX-3's
`hasEigenvalue_zero` witness. -/
theorem seatMode_ne_zero : seatMode ≠ 0 := by
  intro hzero
  have hval : seatMode (layerLinkOf (zeroLayerSite (N := 2))
        (Fin.succ (0 : Fin 3)) (Fin.succ_ne_zero 0)) = 1 := by
    have hshift : ((layerShift (Fin.succ (0 : Fin 3))
        (Fin.succ_ne_zero 0) (zeroLayerSite (N := 2))).1
          (Fin.succ (0 : Fin 3))).val = 1 := by
      rw [layerShift_coord_self]
      have hz : (zeroLayerSite (N := 2)).1
          (Fin.succ (0 : Fin 3)) = 0 := rfl
      rw [hz, zero_add, ZMod.val_one_eq_one_mod,
        Nat.mod_eq_of_lt (by norm_num : 1 < 2)]
    have htail : ((zeroLayerSite (N := 2)).1
        (Fin.succ (0 : Fin 3))).val = 0 := by
      have hz : (zeroLayerSite (N := 2)).1
          (Fin.succ (0 : Fin 3)) = 0 := rfl
      rw [hz, ZMod.val_zero]
    show (((layerShift (Fin.succ (0 : Fin 3))
        (Fin.succ_ne_zero 0) (zeroLayerSite (N := 2))).1
          (Fin.succ (0 : Fin 3))).val : ℝ)
      - (((zeroLayerSite (N := 2)).1
          (Fin.succ (0 : Fin 3))).val : ℝ) = 1
    rw [hshift, htail, Nat.cast_one, Nat.cast_zero, sub_zero]
  have hcon := congrFun hzero (layerLinkOf
    (zeroLayerSite (N := 2)) (Fin.succ (0 : Fin 3))
    (Fin.succ_ne_zero 0))
  simp only [Pi.zero_apply] at hcon
  rw [hval] at hcon
  exact one_ne_zero hcon

end Seat

section Decision

/-- **Read-back at the seat.** The registered predicate
at the named seat is exactly its registered statement,
unfolded, by the pin's own `poseObjBFreqShadow_unfold`.
The decision below is visibly about the registered
object. -/
theorem freqShadow_seat_readback :
    PoseObjBFreqShadow 2 seatPlaq seatMode 0 0 0
      ↔ ModeFreq (maxwellOp 2) seatMode 0
          ∧ ModeFreq (onePlaqDefectOp 2 seatPlaq) seatMode 0
          ∧ (0 : ℝ)
              = FreqShift (maxwellOp 2)
                  (onePlaqDefectOp 2 seatPlaq) seatMode 0 0 :=
  poseObjBFreqShadow_unfold _ _ _ _ _

/-- **Clause 1 at the seat (unperturbed mode).**
`seatMode` is a mode of `maxwellOp 2` at frequency `0`:
gauge modes are in the kernel (MAX-2's
`maxwellOp_gaugeAngle`). -/
theorem seatMode_modeFreq_unperturbed :
    ModeFreq (maxwellOp 2) seatMode 0 :=
  ⟨seatMode_ne_zero, by
    show maxwellOp 2 (gaugeAngle seatPhi) = (0 : ℝ) • seatMode
    rw [maxwellOp_gaugeAngle, zero_smul]⟩

/-- **The seat mode's plaquette angle at the defect
plaquette is zero** - in fact at every plaquette, by
additive telescoping (MAX-2's `maxwellM3_proved`, the
(M3) discharge). This is the finite computation the
defect clause turns on. -/
theorem seat_plaqAngle_zero :
    plaqAngle seatPlaq seatMode = 0 :=
  maxwellM3_proved seatPhi seatPlaq

/-- **The defect operator at the seat, applied to the
seat mode, is zero**: componentwise, the unperturbed
component vanishes (kernel) and the rank-one defect
component is `plaqSign seatPlaq l * plaqAngle seatPlaq
seatMode = plaqSign seatPlaq l * 0 = 0`. -/
theorem seatMode_defect_eq_zero :
    onePlaqDefectOp 2 seatPlaq seatMode = 0 := by
  funext ℓ
  have h1 : (maxwellOp 2 seatMode) ℓ = 0 := by
    have h : maxwellOp 2 seatMode = 0 := by
      show maxwellOp 2 (gaugeAngle seatPhi) = 0
      exact maxwellOp_gaugeAngle seatPhi
    rw [h]
    rfl
  simp only [onePlaqDefectOp_apply, h1, seat_plaqAngle_zero,
    mul_zero, add_zero, Pi.zero_apply]

/-- **Clause 2 at the seat (perturbed mode).**
`seatMode` is a mode of the named defect operator
`onePlaqDefectOp 2 seatPlaq` at frequency `0`. -/
theorem seatMode_modeFreq_defect :
    ModeFreq (onePlaqDefectOp 2 seatPlaq) seatMode 0 :=
  ⟨seatMode_ne_zero, by
    rw [seatMode_defect_eq_zero, zero_smul]⟩

/-- **Clause 3 at the seat (the stated shift).** The
named stated shift `0` equals the computed frequency
shift `FreqShift ... 0 0 = 0 - 0`, by the pin's
`freqShift_unfold`. -/
theorem seat_shift_eq :
    (0 : ℝ) = FreqShift (maxwellOp 2)
        (onePlaqDefectOp 2 seatPlaq) seatMode 0 0 := by
  rw [freqShift_unfold]
  exact (sub_self (0 : ℝ)).symm

/-- **HEADLINE - THE DECISION: HOLDS at the named seat.**
The registered frequency-shadow predicate
`PoseObjBFreqShadow` holds at the seat named on this
module's face: seat size `N = 2`, plaquette `seatPlaq`
(base zero site, directions `1, 2`), mode
`seatMode = gaugeAngle seatPhi` (the longitudinal /
pure-gauge mode), frequencies `omega = omega' = 0`, and
stated shift `0`. A seat fact, stated as a seat fact:
the one-plaquette rank-one defect at `seatPlaq` is
invisible to this mode because the mode's plaquette
angle at `seatPlaq` telescopes to `0`. FINITE
eigenvalue arithmetic only; NO CLAIM; Dial 2 = 0. -/
theorem freqShadow_holds_at_seat :
    PoseObjBFreqShadow 2 seatPlaq seatMode 0 0 0 :=
  ⟨seatMode_modeFreq_unperturbed, seatMode_modeFreq_defect,
    seat_shift_eq⟩

end Decision

section Prop2SeatCorollaries

/-- **GR-PROP-2 input, at the seat (complexified form).**
The complexification of the seat mode is a `ModeFreq`
mode of the complexified operator `maxwellOpCE 2` at
frequency `0`, by GR-PROP-2's `gaugeModeC_modeFreq_zero`.
Consumed as an input; its completeness seam is not used. -/
theorem seatModeC_modeFreq :
    ModeFreq (maxwellOpCE 2) (gaugeModeC seatPhi) (0 : ℂ) :=
  gaugeModeC_modeFreq_zero seatPhi seatMode_ne_zero

/-- **GR-PROP-2 / GR-PROP-1 input, at the seat
(stationarity).** The link wave family (GR-PROP-1's weld
of the pin's `waveFamily`) fixes the complexified seat
mode exactly, for every time `t`, by GR-PROP-2's
`gaugeModeC_stationary` - the phase at frequency `0` is
`1`. Finite eigenvalue arithmetic only. -/
theorem seatModeC_stationary (t : ℝ) :
    linkWaveFamily 2 t (gaugeModeC seatPhi)
      = gaugeModeC seatPhi :=
  gaugeModeC_stationary t seatPhi

end Prop2SeatCorollaries

/-! ## Axiom audit

Headlines checked on exactly
`[propext, Classical.choice, Quot.sound]`. -/

#print axioms freqShadow_seat_readback
#print axioms seatMode_modeFreq_unperturbed
#print axioms seatMode_modeFreq_defect
#print axioms seat_shift_eq
#print axioms freqShadow_holds_at_seat
#print axioms seatModeC_modeFreq
#print axioms seatModeC_stationary

end ThetLogos
