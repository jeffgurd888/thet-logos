import ThetLogos.GravityPosePost

namespace ThetLogos

/-!
# ThetLogos.GravityPoseResponse - GR-POSE-2: the fluctuation-response brick

**Working label only.** The module name `GravityPoseResponse`
and the line name GR-POSE are working labels; Jeff names.

**Status: RESPONSE LAW - the pin's registered pose `PoseVarA`
is discharged here constructively, against the frozen path of
`ThetLogos.GravityPosePost` (`PoseVarAPathData`, `poseVarAPath`,
`PoseVarA`), with no frozen definition renamed or extended.
NO CLAIM beyond the response law itself. No gravity object is
defined, constructed, or asserted to exist. Dials 0/4.**

Governing pack: `routeb-general-scratch/pack-gr-pose-2.md`,
governing memo: `routeb-general-scratch/scoping-gravity-pose-2026-10-31.md`
(section 2 pose P-var-A, section 5 GR-POSE-2 spec, section 6
kills).

## Ceiling (on the face)

The finite shadow of the variational pose: a proved response
law of the finite action's numbers under finite fluctuation
along the named path. No manifold factor exists in-corpus
whose response this could be promoted to. This module seats
NO object; Dial 2 = 0 under every outcome, including this one.

Ceiling fence for fenced vocabulary: the words metric,
geodesic, curvature, Einstein, stress-energy, propagation,
spacetime, and the expression 1/r are FRONTIER vocabulary in
this line, owned by nothing in the corpus. In this module
each of them appears only inside this fence. Any other use
is a fence breach.

## The degeneracy boundary, named on the face (K-GR-STAB)

The response law below is a statement about TRACE FUNCTIONS
of the defined matrix family `poseVarAPath P t`, for all real
`t`. It asserts membership in the order-one / self-adjoint
class ONLY where landed results reach: at `t = 1`, by the
pin's `poseVarAPath_one_orderOne` and
`poseVarAPath_one_selfAdjoint` (restated below as boundary
read-backs), and at `t = 0`, where the pin's
`poseVarAPath_zero` identifies the path with the unfluctuated
seat operator itself. For general `t` NO class membership is
asserted here: closure of the algebraic one-form class under
scaling is not a landed result, and it is not claimed. The
named degenerate case is the zero-one-form constant path:
if `P.oneForm = 0`, the path is constant, and both response
coefficients vanish identically (proved below as
`poseVarA_zeroForm_degenerate`).

## What is proved here

1. `poseVarAPath_eq` - the frozen path is affine in `t`:
   `poseVarAPath P t = D0 + (t : C) * B` in scalar-multiple
   form, where `D0` is the unfluctuated seat operator and
   `B = poseVarACoeffOp P` is the one-form fluctuation's
   coefficient operator read off the landed
   `fluctuatedDirac` construction.
2. `poseVarA_trace_sq` - the M2 response identity, with the
   coefficients exhibited as the named trace expressions
   `poseVarAC0`, `poseVarAC1`, `poseVarAC2`.
3. `poseVarA_discharged` - the pin's `PoseVarA`, discharged
   with exactly those named coefficients.
4. `poseVarA_M0`, `poseVarA_M1` - the zeroth moment (the
   dimension 32, constant in `t`) and the first moment as an
   explicit affine function with named coefficients; the
   first moment's slope is `2 * trace P.oneForm`
   (`poseVarA_M1_slope`).
5. `poseVarA_firstVariation_M2`, `poseVarA_firstVariation_M1`
   - the first variations at `t = 0`, stated as the response
   law: the derivative of each trace function at `0` is its
   named linear coefficient.
6. `poseVarA_zeroForm_degenerate` - the named degenerate
   case, on the face.
-/

/-! ## The path's own data: D0 and the coefficient operator -/

/-- **The unfluctuated seat operator of the path.** `D0` in
the pack's notation: the `smDirac` of the path data's Yukawa
parameters, before any fluctuation. -/
def poseVarAD0 (P : PoseVarAPathData) : Matrix I32 I32 ℂ :=
  smDirac P.yNu P.yE P.yU P.yD P.yR

/-- **The one-form fluctuation's coefficient operator.** The
landed construction is `fluctuatedDirac D_F A = D_F + A +
oppositeOneForm A` (`InnerFluctuations`), so fluctuating by
the scaled one-form `(t : C) * A` contributes `A +
oppositeOneForm A` at coefficient `t`. This operator is that
contribution at the path's own one-form: the fluctuation at
the unscaled one-form minus `D0`, read off the construction.
No new operator is invented; this is a name for the landed
construction's `t`-coefficient. -/
def poseVarACoeffOp (P : PoseVarAPathData) : Matrix I32 I32 ℂ :=
  P.oneForm + oppositeOneForm P.oneForm

/-- The opposite-one-form construction is homogeneous in its
argument at a complex scalar: the transpose and the two
fixed `UJ` factors pass the scalar through. Helper for the
affine form of the frozen path. -/
theorem oppositeOneForm_smul (c : ℂ) (A : Matrix I32 I32 ℂ) :
    oppositeOneForm (c • A) = c • oppositeOneForm A := by
  simp [oppositeOneForm, Matrix.transpose_smul]

/-- **The frozen path is affine in `t`.** At parameter `t`,
the path is the unfluctuated operator plus `t` times the
coefficient operator. This is the landed `fluctuatedDirac`
construction unfolded once, with the homogeneity of
`oppositeOneForm` used at the scaled one-form. -/
theorem poseVarAPath_eq (P : PoseVarAPathData) (t : ℝ) :
    poseVarAPath P t
      = poseVarAD0 P + (t : ℂ) • poseVarACoeffOp P := by
  unfold poseVarAPath poseVarAD0 poseVarACoeffOp fluctuatedDirac
  rw [oppositeOneForm_smul, add_assoc, ← smul_add]

/-! ## The M2 coefficients, as named trace expressions -/

/-- **Coefficient `c0` of the M2 response:** the trace of the
square of the unfluctuated operator. -/
def poseVarAC0 (P : PoseVarAPathData) : ℂ :=
  Matrix.trace ((poseVarAD0 P) ^ 2)

/-- **Coefficient `c1` of the M2 response - the first
variation:** the trace of the two cross products of the
unfluctuated operator with the coefficient operator. -/
def poseVarAC1 (P : PoseVarAPathData) : ℂ :=
  Matrix.trace (poseVarAD0 P * poseVarACoeffOp P
    + poseVarACoeffOp P * poseVarAD0 P)

/-- **Coefficient `c2` of the M2 response:** the trace of the
square of the coefficient operator. -/
def poseVarAC2 (P : PoseVarAPathData) : ℂ :=
  Matrix.trace ((poseVarACoeffOp P) ^ 2)

/-- Matrix-level expansion of the square of the affine path.
Helper for `poseVarA_trace_sq`: the square of `D0 + s * B`
is `D0^2` plus `s` times the cross products plus `s^2` times
`B^2`, with the scalars carried as scalar multiples. -/
theorem poseVarA_sq_expand (P : PoseVarAPathData) (t : ℝ) :
    (poseVarAD0 P + (t : ℂ) • poseVarACoeffOp P) ^ 2
      = (poseVarAD0 P) ^ 2
        + (t : ℂ) • (poseVarAD0 P * poseVarACoeffOp P
            + poseVarACoeffOp P * poseVarAD0 P)
        + ((t : ℂ) ^ 2) • ((poseVarACoeffOp P) ^ 2) := by
  simp only [pow_two, Matrix.add_mul, Matrix.mul_add,
    Matrix.smul_mul, Matrix.mul_smul]
  module

/-- **The M2 response identity.** For every path datum `P`
and every real `t`, the trace of the square of the frozen
path is the quadratic polynomial in `t` whose coefficients
are the named trace expressions `poseVarAC0`, `poseVarAC1`,
`poseVarAC2` of the path's own data. -/
theorem poseVarA_trace_sq (P : PoseVarAPathData) (t : ℝ) :
    Matrix.trace ((poseVarAPath P t) ^ 2)
      = poseVarAC0 P + poseVarAC1 P * (t : ℂ)
        + poseVarAC2 P * (t : ℂ) ^ 2 := by
  rw [poseVarAPath_eq, poseVarA_sq_expand]
  simp [poseVarAC0, poseVarAC1, poseVarAC2, Matrix.trace_add,
    Matrix.trace_smul]
  ring

/-- **HEADLINE - GR-POSE-2: `PoseVarA` discharged.** The
pin's registered pose, discharged constructively in exactly
its registered shape: the existential coefficients are
exhibited, not merely asserted - they are `poseVarAC0`,
`poseVarAC1`, `poseVarAC2` above, and the identity for all
real `t` is `poseVarA_trace_sq`. Ceiling and boundary as
named in this module's header: a response law for trace
functions of the finite matrix family; it seats no object
and Dial 2 = 0. -/
theorem poseVarA_discharged (P : PoseVarAPathData) :
    PoseVarA P :=
  ⟨poseVarAC0 P, poseVarAC1 P, poseVarAC2 P,
    fun t => poseVarA_trace_sq P t⟩

/-! ## The other moments on the same path -/

/-- **M0 on the path: the dimension, constant in `t`.** The
trace of the zeroth power of the path operator - the trace
of the identity matrix at this seat - is `32` for every
`t`. -/
theorem poseVarA_M0 (P : PoseVarAPathData) (t : ℝ) :
    Matrix.trace ((poseVarAPath P t) ^ 0) = 32 := by
  simp [Matrix.trace_one]

/-- **Constant coefficient of M1:** the trace of the
unfluctuated operator. -/
def poseVarAM1C0 (P : PoseVarAPathData) : ℂ :=
  Matrix.trace (poseVarAD0 P)

/-- **Slope coefficient of M1:** the trace of the
coefficient operator. -/
def poseVarAM1C1 (P : PoseVarAPathData) : ℂ :=
  Matrix.trace (poseVarACoeffOp P)

/-- **The M1 response identity.** The trace of the path
operator is affine in `t`, with the named coefficients
`poseVarAM1C0` (constant) and `poseVarAM1C1` (slope). -/
theorem poseVarA_M1 (P : PoseVarAPathData) (t : ℝ) :
    Matrix.trace (poseVarAPath P t)
      = poseVarAM1C0 P + poseVarAM1C1 P * (t : ℂ) := by
  rw [poseVarAPath_eq]
  simp [poseVarAM1C0, poseVarAM1C1, Matrix.trace_add,
    Matrix.trace_smul]
  ring

/-- **Trace of the opposite one-form.** Conjugating the
transpose by the fixed `UJ` factors does not change the
trace: by cyclicity of trace the two `UJ` factors meet and
cancel (`UJ_mul_self`), and the trace of a transpose is the
trace itself. Helper for the exact form of the M1 slope. -/
theorem trace_oppositeOneForm (A : Matrix I32 I32 ℂ) :
    Matrix.trace (oppositeOneForm A) = Matrix.trace A := by
  rw [oppositeOneForm,
    Matrix.trace_mul_comm (UJ * A.transpose) UJ,
    ← Matrix.mul_assoc, UJ_mul_self, Matrix.one_mul,
    Matrix.trace_transpose]

/-- **The M1 slope, exactly.** The slope of the first moment
is twice the trace of the path's one-form: the coefficient
operator is the one-form plus its opposite, and the two
summands have the same trace. In particular the slope
vanishes exactly when the one-form is traceless - a named
locus, stated here, not narrowed away (K-GR-STAB). -/
theorem poseVarA_M1_slope (P : PoseVarAPathData) :
    poseVarAM1C1 P = 2 * Matrix.trace P.oneForm := by
  rw [poseVarAM1C1, poseVarACoeffOp, Matrix.trace_add,
    trace_oppositeOneForm]
  ring

/-! ## First variation: the response law -/

/-- **First variation of M2 at `t = 0` - the response law.**
The derivative at `0` of the M2 trace function along the
frozen path is the named linear coefficient `poseVarAC1 P`:
the trace of the cross products of the unfluctuated operator
with the coefficient operator. The polynomial identity
`poseVarA_trace_sq` is the proof; the derivative is read off
it and agrees with the coefficient. -/
theorem poseVarA_firstVariation_M2 (P : PoseVarAPathData) :
    deriv (fun t : ℝ => Matrix.trace ((poseVarAPath P t) ^ 2)) 0
      = poseVarAC1 P := by
  have hfun : (fun t : ℝ => Matrix.trace ((poseVarAPath P t) ^ 2))
      = fun t : ℝ => poseVarAC0 P + poseVarAC1 P * (t : ℂ)
          + poseVarAC2 P * (t : ℂ) ^ 2 :=
    funext fun t => poseVarA_trace_sq P t
  rw [hfun]
  have hid : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 0 := by
    simpa using (hasDerivAt_id ((0 : ℝ) : ℂ)).comp_ofReal
  have ha : HasDerivAt
      (fun t : ℝ => poseVarAC0 P + poseVarAC1 P * (t : ℂ))
      (poseVarAC1 P) 0 := by
    simpa using (hid.const_mul (poseVarAC1 P)).const_add
      (poseVarAC0 P)
  have h2 : HasDerivAt
      (fun t : ℝ => poseVarAC2 P * (t : ℂ) ^ 2) 0 0 := by
    simpa using (hid.pow 2).const_mul (poseVarAC2 P)
  have hb := ha.add h2
  simp only [add_zero] at hb
  exact hb.deriv

/-- **First variation of M1 at `t = 0`.** The derivative at
`0` of the M1 trace function along the frozen path is its
named slope `poseVarAM1C1 P`, which by `poseVarA_M1_slope`
is `2 * trace P.oneForm`. The affine identity
`poseVarA_M1` is the proof. -/
theorem poseVarA_firstVariation_M1 (P : PoseVarAPathData) :
    deriv (fun t : ℝ => Matrix.trace (poseVarAPath P t)) 0
      = poseVarAM1C1 P := by
  have hfun : (fun t : ℝ => Matrix.trace (poseVarAPath P t))
      = fun t : ℝ => poseVarAM1C0 P + poseVarAM1C1 P * (t : ℂ) :=
    funext fun t => poseVarA_M1 P t
  rw [hfun]
  have hid : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 0 := by
    simpa using (hasDerivAt_id ((0 : ℝ) : ℂ)).comp_ofReal
  have ha : HasDerivAt
      (fun t : ℝ => poseVarAM1C0 P + poseVarAM1C1 P * (t : ℂ))
      (poseVarAM1C1 P) 0 := by
    simpa using (hid.const_mul (poseVarAM1C1 P)).const_add
      (poseVarAM1C0 P)
  exact ha.deriv

/-! ## The named degenerate case and the class boundary -/

/-- **The named degenerate case: the zero-one-form constant
path.** If the path's one-form is `0`, the coefficient
operator is `0`, both response coefficients of M2 vanish,
the M1 slope vanishes, and the path itself is constant at
the unfluctuated operator. The response is identically zero
on this locus - stated as the finding, on the face. -/
theorem poseVarA_zeroForm_degenerate (P : PoseVarAPathData)
    (hA : P.oneForm = 0) :
    poseVarACoeffOp P = 0 ∧ poseVarAC1 P = 0 ∧ poseVarAC2 P = 0
      ∧ poseVarAM1C1 P = 0
      ∧ ∀ t : ℝ, poseVarAPath P t = poseVarAD0 P := by
  have hB : poseVarACoeffOp P = 0 := by
    simp [poseVarACoeffOp, hA, oppositeOneForm]
  refine ⟨hB, ?_, ?_, ?_, ?_⟩
  · simp [poseVarAC1, hB]
  · simp [poseVarAC2, hB]
  · simp [poseVarAM1C1, hB]
  · intro t
    rw [poseVarAPath_eq, hB]
    simp

/-- **Class boundary read-back at `t = 1` (order-one).**
Restated from the pin so the boundary named in this
module's header is code-checked here: order-one membership
for the path is asserted at `t = 1`, where the landed
theorem reaches, and nowhere else in this module. -/
theorem poseVarA_boundary_one_orderOne (P : PoseVarAPathData) :
    OrderOneHolds (poseVarAPath P 1) :=
  poseVarAPath_one_orderOne P

/-- **Class boundary read-back at `t = 1`
(self-adjointness).** Restated from the pin, same fence as
the order-one read-back. -/
theorem poseVarA_boundary_one_selfAdjoint
    (P : PoseVarAPathData) :
    IsSelfAdjoint (poseVarAPath P 1) :=
  poseVarAPath_one_selfAdjoint P

/-- **Class boundary read-back at `t = 0`.** At `t = 0` the
path is the unfluctuated seat operator itself (the pin's
read-back), which is the seat at which the landed
`smDirac` results apply directly. No statement about the
path at any other parameter is a class statement. -/
theorem poseVarA_boundary_zero (P : PoseVarAPathData) :
    poseVarAPath P 0 = poseVarAD0 P :=
  poseVarAPath_zero P

end ThetLogos
