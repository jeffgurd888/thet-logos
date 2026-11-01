import ThetLogos.CpecBridgePost

namespace ThetLogos

/-!
# ThetLogos.CpecEcDecision - CPEC-EC-1: the Einstein-Cartan finite shadow decision

**Working label only.** The module name `CpecEcDecision` and the
brick name CPEC-EC-1 are working labels; Jeff names.

**Status: DECISION of the registered predicate `CpecW6Shadow`
(CPEC-0, `CpecBridgePost`), assembled from landed arithmetic
only. NO CLAIM. No gravity object is defined, constructed, or
asserted to exist. Dial 2 = 0, dials 0/4.**

The registered predicate, stated in `CpecBridgePost` with
supplied parameters `(y, s)`, never existentially quantified:
along the Majorana line `s -> smDirac (y:ℂ) (y:ℂ) (y:ℂ) (y:ℂ) s`,
under the seat fence `y != 0`, the finite a2 matter slot (the
trace of the square of the line's operator) is an explicit
function of `(y, s)` whose s-dependent part is
`2 * Complex.normSq s`, and the torsion defect at its witness
entry `(<0>, <24>)` is `(y:ℂ)^{-1} * star s`.

This module ASSEMBLES that slot from the landed forms
`sa_finite_a2_yukawa` and `sa_finite_a2_fluctuated`
(`SpectralActionBridge`) and the landed `defect_entry`
(`DiracTorsionMap`), and DECIDES the registered predicate:
the degrees are exactly as registered.

- (a) In the slot, `s` enters in degree exactly 2: the slot is
  the s-free part plus `((2 * Complex.normSq s : ℝ) : ℂ)`, and
  the s-dependent part scales by `Complex.normSq t` under
  `s -> t * s` (`cpecEcSDep_homogeneous`), with value `2` at
  `s = 1`, so it is not a degree-1 or degree-0 s-term.
- (b) In the defect, `s` enters in degree exactly 1: the
  witness entry is `(y:ℂ)^{-1} * star s`, linear in `star s`,
  scaling by `star t` under `s -> t * s`
  (`cpecEcDefectEntry_linear_star`), with value `(y:ℂ)^{-1}`
  at `s = 1`, so it is not a degree-2 or degree-0 s-term.

Boundaries, as registered: `s = 0` is the survival point -
both s-parts vanish there and the slot reduces to its s-free
part (`cpecEc_survival_point_consistent`), consistent with
the degree statements (`0 = 0`); `y = 0` is outside the seat
by the landed fence `hy : y != 0` and no statement here
extends the seat to it.

Fence, repeated from the defect's home module: the defect
here is the algebraic defect of a deformed fundamental
symmetry; no connection is involved. This module's prose and
statements are the arithmetic and the fences only.
-/

/-! ## The assembled slot -/

/-- The finite a2 matter slot along the Majorana line, as a
named function of the supplied parameters `(y, s)`: the trace
of the square of `smDirac (y:ℂ) (y:ℂ) (y:ℂ) (y:ℂ) s`. -/
noncomputable def cpecEcSlot (y : ℝ) (s : ℂ) : ℂ :=
  Matrix.trace ((smDirac (y : ℂ) (y : ℂ) (y : ℂ) (y : ℂ) s) ^ 2)

/-- The s-free part of the assembled slot, in the exact shape
the landed `sa_finite_a2_yukawa` form carries it. -/
def cpecEcSlotSFree (y : ℝ) : ℝ :=
  4 * (Complex.normSq (y : ℂ) + Complex.normSq (y : ℂ)
    + 3 * Complex.normSq (y : ℂ) + 3 * Complex.normSq (y : ℂ))

/-- The s-dependent part of the assembled slot: exactly
`2 * Complex.normSq s`. -/
def cpecEcSlotSDep (s : ℂ) : ℝ :=
  2 * Complex.normSq s

/-- The torsion defect at its witness entry `(<0>, <24>)`,
as a named function of the supplied parameters `(y, s)`. -/
noncomputable def cpecEcDefectEntry (y : ℝ) (s : ℂ) : ℂ :=
  defect (etaSign y) (torsionMajorana y s)
    ⟨0, by norm_num⟩ ⟨24, by norm_num⟩

/-- **The assembled slot, in the registered form.** The slot
along the line is exactly the displayed function of `(y, s)`,
by the landed `sa_finite_a2_yukawa` at
`yNu = yE = yU = yD = (y:ℂ)` and `yR = s`. -/
theorem cpecEcSlot_eq_registered (y : ℝ) (s : ℂ) :
    cpecEcSlot y s
      = (((4 * (Complex.normSq (y : ℂ) + Complex.normSq (y : ℂ)
              + 3 * Complex.normSq (y : ℂ)
              + 3 * Complex.normSq (y : ℂ))
            + 2 * Complex.normSq s) : ℝ) : ℂ) :=
  sa_finite_a2_yukawa (y : ℂ) (y : ℂ) (y : ℂ) (y : ℂ) s

/-- **The assembled slot, decomposed.** The slot is the cast
of the s-free part plus the s-dependent part; the whole
s-dependence of the slot is the single term
`2 * Complex.normSq s`. -/
theorem cpecEcSlot_eq (y : ℝ) (s : ℂ) :
    cpecEcSlot y s
      = (((cpecEcSlotSFree y + cpecEcSlotSDep s) : ℝ) : ℂ) := by
  unfold cpecEcSlotSFree cpecEcSlotSDep
  exact cpecEcSlot_eq_registered y s

/-- **Decomposition, split at the cast.** The slot is the
s-free cast plus the s-dependent cast, as a sum in `ℂ`. -/
theorem cpecEcSlot_decomp (y : ℝ) (s : ℂ) :
    cpecEcSlot y s
      = ((cpecEcSlotSFree y : ℝ) : ℂ)
        + ((cpecEcSlotSDep s : ℝ) : ℂ) := by
  rw [cpecEcSlot_eq, Complex.ofReal_add]

/-- **Read-back of the fluctuated a2 form.** The landed
`sa_finite_a2_fluctuated`, restated under this brick's name:
with inner fluctuation the a2 trace splits as the unfluctuated
trace plus the two A-dependent terms. Citation only. -/
theorem cpecEcA2Fluctuated_readback (D_F A : Matrix I32 I32 ℂ) :
    Matrix.trace ((fluctuatedDirac D_F A) ^ 2)
      = Matrix.trace (D_F ^ 2)
        + 2 * Matrix.trace (D_F * (A + oppositeOneForm A))
        + Matrix.trace ((A + oppositeOneForm A) ^ 2) :=
  sa_finite_a2_fluctuated D_F A

/-! ## Degree (a): the slot's s-part is degree exactly 2 -/

/-- The s-dependent part at `s = 0` is `0`. -/
theorem cpecEcSDep_zero : cpecEcSlotSDep 0 = 0 := by
  simp [cpecEcSlotSDep]

/-- The s-dependent part at `s = 1` is `2`: the s-part is not
identically zero and not a degree-0 term. -/
theorem cpecEcSDep_one : cpecEcSlotSDep 1 = 2 := by
  simp [cpecEcSlotSDep]

/-- **Degree 2, homogeneous form.** Under `s -> t * s` the
slot's s-dependent part scales by `Complex.normSq t`: it is
homogeneous of degree 2 in `(s, star s)`. -/
theorem cpecEcSDep_homogeneous (t s : ℂ) :
    cpecEcSlotSDep (t * s) = Complex.normSq t * cpecEcSlotSDep s := by
  unfold cpecEcSlotSDep
  rw [Complex.normSq_mul]
  ring

/-- **Degree 2, real-scale form.** Under a real scaling
`s -> (r:ℂ) * s` the slot's s-dependent part scales by
`r ^ 2`. -/
theorem cpecEcSDep_real_scale (r : ℝ) (s : ℂ) :
    cpecEcSlotSDep ((r : ℂ) * s) = r ^ 2 * cpecEcSlotSDep s := by
  rw [cpecEcSDep_homogeneous, Complex.normSq_ofReal]
  ring

/-- The slot at the survival point `s = 0` is exactly its
s-free part. -/
theorem cpecEcSlot_at_zero (y : ℝ) :
    cpecEcSlot y 0 = ((cpecEcSlotSFree y : ℝ) : ℂ) := by
  rw [cpecEcSlot_decomp, cpecEcSDep_zero]
  simp

/-- The slot's whole deviation from its survival-point value
is the s-dependent part `((2 * Complex.normSq s : ℝ) : ℂ)`:
no degree-1 or degree-0 s-term is present. -/
theorem cpecEcSlot_sub_zero (y : ℝ) (s : ℂ) :
    cpecEcSlot y s - cpecEcSlot y 0
      = ((cpecEcSlotSDep s : ℝ) : ℂ) := by
  rw [cpecEcSlot_decomp, cpecEcSlot_at_zero, add_sub_cancel_left]

/-! ## Degree (b): the defect entry is degree exactly 1 -/

/-- **The defect entry, in the registered form.** Under the
seat fence `y != 0` the witness entry is exactly
`(y:ℂ)^{-1} * star s`, by the landed `defect_entry`. -/
theorem cpecEcDefectEntry_eq (y : ℝ) (hy : y ≠ 0) (s : ℂ) :
    cpecEcDefectEntry y s = (y : ℂ)⁻¹ * star s :=
  defect_entry y hy s

/-- **Degree 1, linear form.** Under `s -> t * s` the defect
entry scales by `star t`: it is linear in `star s`. -/
theorem cpecEcDefectEntry_linear_star (y : ℝ) (hy : y ≠ 0)
    (t s : ℂ) :
    cpecEcDefectEntry y (t * s)
      = star t * cpecEcDefectEntry y s := by
  rw [cpecEcDefectEntry_eq y hy, cpecEcDefectEntry_eq y hy, star_mul]
  ring

/-- The defect entry at `s = 0` is `0`: the survival point,
consistent with degree 1. -/
theorem cpecEcDefectEntry_zero (y : ℝ) (hy : y ≠ 0) :
    cpecEcDefectEntry y 0 = 0 := by
  rw [cpecEcDefectEntry_eq y hy]
  simp

/-- The defect entry at `s = 1` is `(y:ℂ)^{-1}`, nonzero
wherever the seat scalar is a unit multiple of it: the entry
is not identically zero and not a degree-0 or degree-2 term
(read with `cpecEcDefectEntry_linear_star`). -/
theorem cpecEcDefectEntry_one (y : ℝ) (hy : y ≠ 0) :
    cpecEcDefectEntry y 1 = (y : ℂ)⁻¹ := by
  rw [cpecEcDefectEntry_eq y hy]
  simp

/-! ## The boundary and the decision -/

/-- **The survival point is consistent.** At `s = 0` the slot
is its s-free part and the defect entry vanishes: the degree
statements specialize to `0 = 0` there, as registered. -/
theorem cpecEc_survival_point_consistent (y : ℝ) (hy : y ≠ 0) :
    cpecEcSlot y 0 = ((cpecEcSlotSFree y : ℝ) : ℂ)
      ∧ cpecEcDefectEntry y 0 = 0 :=
  ⟨cpecEcSlot_at_zero y, cpecEcDefectEntry_zero y hy⟩

/-- **The degree pattern, jointly.** The slot's s-part is
homogeneous of degree 2 and the defect entry is linear of
degree 1 in `star s`, at every seat point `y != 0`. -/
theorem cpecEc_degree_pattern (y : ℝ) (hy : y ≠ 0) :
    (∀ t s : ℂ, cpecEcSlotSDep (t * s)
        = Complex.normSq t * cpecEcSlotSDep s)
      ∧ (∀ t s : ℂ, cpecEcDefectEntry y (t * s)
          = star t * cpecEcDefectEntry y s) :=
  ⟨fun t s => cpecEcSDep_homogeneous t s,
   fun t s => cpecEcDefectEntry_linear_star y hy t s⟩

/-- **DECISION: the registered shadow holds, exactly as
registered.** For every supplied `(y, s)`, the predicate
`CpecW6Shadow y s` of the CPEC-0 pin holds: under `y != 0`
the slot is the displayed explicit function with its
`2 * Complex.normSq s` term (degree 2) and the defect entry
is `(y:ℂ)^{-1} * star s` (degree 1). No degree flips at any
seat point; `s = 0` is the consistent survival point and
`y = 0` remains outside the seat. -/
theorem cpecW6Shadow_decided (y : ℝ) (s : ℂ) : CpecW6Shadow y s := by
  intro hy
  exact ⟨cpecEcSlot_eq_registered y s, defect_entry y hy s⟩

end ThetLogos
