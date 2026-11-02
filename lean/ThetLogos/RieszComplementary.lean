/-
# SHELF-8b, brick 1 (8B-1) - complementary Riesz projection + CLM seat

Brick 8B-1 of SHELF-8b (scoping dossier
`whitepaper/shelf-8b-scoping-2026-11-02.md` SS4, pack
`routeb-general-scratch/pack-8b-1.md`): the complementary
projection `1 - rieszProj a lam r` of the GATE-A1/GATE-A2
Riesz projection (`ThetLogos.RieszGate`,
`ThetLogos.RieszGateIdem`), its projection algebra, radius
transfer under isolation, and the instantiations at the CLM
seat `A := E ->L[C] E`. NO CLAIM beyond the theorems below;
no dial is touched. Fences on the face (scoping SS4/SS5):
no `rieszComplProj != 0` headline (K-8B-COMPL-NONZERO - it
is false for a singleton spectrum); no two-point
orthogonality (that is 8B-2); no local calculus (8B-3); no
spectrum statement (8B-4). K-8B-KILLED-FORM binds: nothing
here consumes the killed `circleIntegrable_resolvent`; the
only integrability form in the gate is the corrected
`circleIntegrable_resolvent_of_nonneg`, and this brick in
fact needs no integrability at all - it is ring algebra over
two landed theorems (`rieszProj_mul_self`,
`commute_a_rieszProj`) plus one-step CLM instantiation
(K-8B-CLM-REPROOF: the gate is not re-proved at CLM
generality).

Hypothesis adjustment, flagged at full rank (the pack's SS B,
in the GATE-A1-headline-4 pattern - recorded, not silent):
the scoping's frozen list states the complement's
idempotence and the two orthogonality products WITHOUT
hypotheses, but all three route through `P^2 = P`, i.e.
through `rieszProj_mul_self`, which requires isolation.
They are therefore stated WITH
`(hR : specIsolatedWithin a lam R) (hr : 0 < r) (hrR : r <= R)`;
without them the statements are unprovable (a Riesz integral
at a non-isolating radius is not a projection). The remaining
algebra headlines need no isolation.

Same-pattern adjustments, also flagged: the CLM seat's range
invariance headline likewise routes through `P^2 = P`
(pointwise it is `P (T (P x)) = T (P x)`, which by the
apply-commutation is `T (P (P x)) = T (P x)`), so it too is
stated with the isolation hypotheses; the scoping's seat
list omits them for this headline as well. And the seat
context carries `[NontrivialTopology E]`, which the
scoping's seat context omits: without it the pin has no
`NormOneClass (E ->L[C] E)` instance (its `normOneClass`
instance in `Mathlib/Analysis/Normed/Operator/Basic.lean`
requires exactly this hypothesis), so `rieszProj` at the
CLM seat does not typecheck at all.
-/

import ThetLogos.RieszGate
import ThetLogos.RieszGateIdem

namespace ThetLogos

noncomputable section

variable {A : Type*} [NormedRing A] [NormOneClass A] [NormedAlgebra ℂ A]
  [CompleteSpace A]

variable (a : A)

/-! ## Frozen definition (verbatim from the scoping) -/

/-- The complementary Riesz projection: `1 - rieszProj a lam r`. -/
def rieszComplProj (a : A) (lam : ℂ) (r : ℝ) : A :=
  1 - rieszProj a lam r

/-! ## Complementary-projection algebra -/

theorem rieszProj_add_rieszComplProj (lam : ℂ) (r : ℝ) :
    rieszProj a lam r + rieszComplProj a lam r = 1 :=
  add_sub_cancel _ _

theorem rieszComplProj_mul_self {lam : ℂ} {R : ℝ}
    (hR : specIsolatedWithin a lam R) {r : ℝ}
    (hr : 0 < r) (hrR : r ≤ R) :
    rieszComplProj a lam r * rieszComplProj a lam r
      = rieszComplProj a lam r := by
  have hP : rieszProj a lam r * rieszProj a lam r = rieszProj a lam r :=
    rieszProj_mul_self a hR hr hrR
  show (1 - rieszProj a lam r) * (1 - rieszProj a lam r)
    = 1 - rieszProj a lam r
  calc (1 - rieszProj a lam r) * (1 - rieszProj a lam r)
      = (1 - rieszProj a lam r)
        - (1 - rieszProj a lam r) * rieszProj a lam r := by
          rw [mul_sub, mul_one]
    _ = (1 - rieszProj a lam r)
        - (rieszProj a lam r
          - rieszProj a lam r * rieszProj a lam r) := by
          rw [sub_mul, one_mul]
    _ = (1 - rieszProj a lam r)
        - (rieszProj a lam r - rieszProj a lam r) := by rw [hP]
    _ = 1 - rieszProj a lam r := by rw [sub_self, sub_zero]

theorem rieszProj_mul_rieszComplProj {lam : ℂ} {R : ℝ}
    (hR : specIsolatedWithin a lam R) {r : ℝ}
    (hr : 0 < r) (hrR : r ≤ R) :
    rieszProj a lam r * rieszComplProj a lam r = 0 := by
  have hP : rieszProj a lam r * rieszProj a lam r = rieszProj a lam r :=
    rieszProj_mul_self a hR hr hrR
  show rieszProj a lam r * (1 - rieszProj a lam r) = 0
  rw [mul_sub, mul_one, hP, sub_self]

theorem rieszComplProj_mul_rieszProj {lam : ℂ} {R : ℝ}
    (hR : specIsolatedWithin a lam R) {r : ℝ}
    (hr : 0 < r) (hrR : r ≤ R) :
    rieszComplProj a lam r * rieszProj a lam r = 0 := by
  have hP : rieszProj a lam r * rieszProj a lam r = rieszProj a lam r :=
    rieszProj_mul_self a hR hr hrR
  show (1 - rieszProj a lam r) * rieszProj a lam r = 0
  rw [sub_mul, one_mul, hP, sub_self]

theorem commute_a_rieszComplProj (lam : ℂ) (r : ℝ) :
    Commute a (rieszComplProj a lam r) :=
  (Commute.one_right a).sub_right (commute_a_rieszProj a lam r)

theorem commute_rieszProj_rieszComplProj (lam : ℂ) (r : ℝ) :
    Commute (rieszProj a lam r) (rieszComplProj a lam r) :=
  (Commute.one_right _).sub_right (Commute.refl _)

theorem a_eq_mul_rieszProj_add (lam : ℂ) (r : ℝ) :
    a = a * rieszProj a lam r + a * rieszComplProj a lam r := by
  show a = a * rieszProj a lam r + a * (1 - rieszProj a lam r)
  rw [mul_sub, mul_one]
  exact (add_sub_cancel _ _).symm

/-! ## Radius transfer of the complement under isolation -/

theorem rieszComplProj_eq_of_le {lam : ℂ} {R : ℝ}
    (hR : specIsolatedWithin a lam R) {r₁ r₂ : ℝ}
    (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (h₁ : r₁ ≤ R) (h₂ : r₂ ≤ R) :
    rieszComplProj a lam r₁ = rieszComplProj a lam r₂ :=
  congrArg (1 - ·) (rieszProj_eq_of_le a hR hr₁ hr₂ h₁ h₂)

/-! ## CLM seat: instantiations at `A := E ->L[C] E` -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [CompleteSpace E] [NontrivialTopology E] (T : E →L[ℂ] E)

theorem rieszProj_clm_mul_self {lam : ℂ} {R : ℝ}
    (hR : specIsolatedWithin T lam R) {r : ℝ}
    (hr : 0 < r) (hrR : r ≤ R) :
    (rieszProj T lam r) * (rieszProj T lam r) = rieszProj T lam r :=
  rieszProj_mul_self T hR hr hrR

theorem rieszProj_clm_apply_commute (lam : ℂ) (r : ℝ) (x : E) :
    (rieszProj T lam r) (T x) = T ((rieszProj T lam r) x) := by
  have h : ((T * rieszProj T lam r) : E →L[ℂ] E) x
      = ((rieszProj T lam r * T) : E →L[ℂ] E) x := by
    rw [(commute_a_rieszProj T lam r).eq]
  rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply] at h
  exact h.symm

theorem rieszProj_clm_range_invariant {lam : ℂ} {R : ℝ}
    (hR : specIsolatedWithin T lam R) {r : ℝ}
    (hr : 0 < r) (hrR : r ≤ R) (x : E) :
    T ((rieszProj T lam r) x)
      = (rieszProj T lam r) (T ((rieszProj T lam r) x)) := by
  have hPx : (rieszProj T lam r) ((rieszProj T lam r) x)
      = (rieszProj T lam r) x := by
    have h : ((rieszProj T lam r * rieszProj T lam r) : E →L[ℂ] E) x
        = (rieszProj T lam r) x := by
      rw [rieszProj_mul_self T hR hr hrR]
    rwa [ContinuousLinearMap.mul_apply] at h
  calc T ((rieszProj T lam r) x)
      = T ((rieszProj T lam r) ((rieszProj T lam r) x)) :=
        congrArg T hPx.symm
    _ = (rieszProj T lam r) (T ((rieszProj T lam r) x)) :=
        (rieszProj_clm_apply_commute T lam r ((rieszProj T lam r) x)).symm

end

end ThetLogos
