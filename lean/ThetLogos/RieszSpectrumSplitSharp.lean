/-
# SHELF-8b, extension 8B-4(ii) - algebra-level spectral splitting,
sharp half: INCLUSIONS / EXCLUSION only

Brick 8B-4(ii) of the SHELF-8b extensions (registration
`whitepaper/shelf-8b345-registration-2026-11-02.md`, scoping
`whitepaper/shelf-8b-scoping-2026-11-02.md` SS2, 8B-4 paragraph,
part (ii)), on top of 8B-4(i) (`ThetLogos.RieszSpectrumSplit`) and
the landed 8B-3 local calculus (`ThetLogos.RieszLocalCalc`,
including multiplicativity). For the Riesz projection
`P = rieszProj a lam r` of GATE-A1/GATE-A2 and its complement
`Q = rieszComplProj a lam r = 1 - P` of 8B-1, the headlines are:

  `spectrum C (a * P) subset {0, lam}`                 (target 1),
  `lam notin spectrum C (a * Q)`                       (target 2,
                                                        CORRECTED -
                                                        see below),
  `spectrum C ((a - lam . 1) * P) subset {0}`          (target 3,
                                                        corollary).

NO CLAIM beyond the theorems below; no dial is touched.

## Deviation on target 2, at full rank (NOT silent)

Target 2 as registered (`lam notin spectrum C (a * (1 - P))`,
no side condition on `lam`) is FALSE as stated, at `lam = 0`.
Counterexample: `A = C`, `a = 0`, `lam = 0`, any admissible
`r > 0`. Then `spectrum C a = {0}`, so `lam` is isolated;
the Riesz integral of the resolvent of `0` over any circle
around `0` is `1`, i.e. `P = 1`, `Q = 0`, `a * Q = 0`, and
`spectrum C (0 : C) = {0}` contains `lam = 0`. The mechanism
is visible in the corner decomposition used below:
`algebraMap C A lam - a * Q = (algebraMap C A lam - a) * Q
+ lam . (1 - Q)`, and the `P`-corner component is `lam . P`,
which is a corner unit only when `lam != 0` (or `P = 0`).
What is landed is the corrected form, with the hypothesis
`(hlam : lam != 0)` on its face, under the frozen name
`lam_not_mem_spectrum_mul_rieszComplProj`. The `lam = 0`
case of the registered statement is therefore a KILL of the
stated form (counterexample above), not an open remainder:
no proof of it exists. Targets 1 and 3 are landed exactly
as registered, with no extra hypothesis.

## Route actually taken

One corner machine serves all three headlines. A generic
lemma (`isUnit_corner_add_smul_compl`) promotes a corner
inverse pair `B * Y = P`, `Y * B = P` for a corner element
`B` (with the four corner absorptions) to a genuine unit
`B + mu . (1 - P)` when `mu != 0`. The corner inverses for
`B = (algebraMap C A nu - a) * P` are supplied by
`exists_corner_inv_algebraMap_sub_mul_rieszProj`
(requiring `nu != lam`), in two cases:

* `nu notin spectrum C a`: the global unit of
  `algebraMap C A nu - a`, compressed to the corner by
  right multiplication with `P` (the 8B-4(i) pattern);
* `nu in spectrum C a`: then isolation forces
  `r < |nu - lam|`, and 8B-3 applied to
  `f = fun z => (z - nu)^{-1}` and `g = fun z => z - nu`
  gives the corner inverse `-FC f`. The registered
  subtlety is handled honestly: `f * g` is NOT `1` as a
  global function (at `z = nu` both factors vanish in
  Lean's field-inverse convention), but `f * g` agrees
  with `1` on the circle `C(lam, r)` (every `z` there has
  `z != nu`), and `rieszLocalFC` is defined by that circle
  integral - the congruence is proved from the definition
  (`rieszLocalFC_eq_of_forall_sphere_eq`), not by
  pretending `f * g = 1` globally.

Target 1 is the machine at `nu = mu`; target 3 is the same
machine at `nu = mu + lam` (then `nu != lam` is exactly
`mu != 0`), via the decomposition
`(algebraMap C A (mu + lam) - a) * P + mu . (1 - P)
  = algebraMap C A mu - (a - lam . 1) * P`
(`algebraMap_sub_sub_smul_mul_rieszProj_eq`). Target 2 uses
the corner `Q` in place of `P`: the corner inverse of
`(algebraMap C A lam - a) * Q` is the compression
`Q * W * Q` of the auxiliary integral
`W = rieszLocalFC a lam r (fun z => (z - lam)^{-1})`
(the `(z - lam)^{-1}`-weighted resolvent integral of
`rieszProj_ne_zero`, `RieszGate.lean:232`), which satisfies
`(algebraMap C A lam - a) * W = Q = W * (algebraMap C A lam
- a)` (`algebraMap_sub_mul_rieszLocalFC_inv_sub_eq`,
`rieszLocalFC_inv_sub_mul_algebraMap_sub_eq`); the scalar
corner is then `lam . P`, inverted by `lam^{-1} . P` -
which is exactly where `lam != 0` is consumed.

Fences on the face (registration / scoping SS3):
* Seam S-8B-4: full splitting EQUALITIES and any
  CLM-restriction spectrum statement are the named
  remainder - they are NOT stated here.
* K-8B-KILLED-FORM untouched: the only integrability
  consumed is via the landed corrected forms (through
  8B-3 and the gate's auxiliary-integral pattern, all
  carrying `0 < r` on their face).
-/

import ThetLogos.RieszLocalCalc
import ThetLogos.RieszSpectrumSplit

open Real

namespace ThetLogos

noncomputable section

variable {A : Type*} [NormedRing A] [NormOneClass A] [NormedAlgebra ℂ A]
  [CompleteSpace A]

variable (a : A)

/-! ## Support: isolation is monotone in the radius, and the
local calculus only sees the circle -/

/-- Isolation at a large radius implies isolation at any
smaller radius. -/
theorem specIsolatedWithin_of_le {lam : ℂ} {R₁ R₂ : ℝ}
    (hR : specIsolatedWithin a lam R₁) (h : R₂ ≤ R₁) :
    specIsolatedWithin a lam R₂ := by
  obtain ⟨h1, h2⟩ := hR
  exact ⟨h1, fun z hz hzlam => lt_of_le_of_lt h (h2 z hz hzlam)⟩

/-- `rieszLocalFC` is defined by the circle integral, so it
only depends on the values of `f` on the circle itself. This
is the honest form of "`f * g = 1` on the circle" used for
the corner inverse at a spectral point: no global identity
`f * g = 1` is asserted. -/
theorem rieszLocalFC_eq_of_forall_sphere_eq {f g : ℂ → ℂ} {lam : ℂ}
    {r : ℝ} (hr : 0 < r)
    (h : ∀ z ∈ Metric.sphere lam r, f z = g z) :
    rieszLocalFC a lam r f = rieszLocalFC a lam r g := by
  show (2 * π * Complex.I : ℂ)⁻¹
      • (∮ z in C(lam, r), f z • resolvent a z)
    = (2 * π * Complex.I : ℂ)⁻¹
      • (∮ z in C(lam, r), g z • resolvent a z)
  congr 1
  exact circleIntegral.integral_congr hr.le (fun z hz => by rw [h z hz])

/-! ## The generic corner machine -/

/-- If `B` is an element of the `P`-corner (idempotent `P`)
with a two-sided corner inverse `Y` (itself in the corner),
then `B + μ • (1 - P)` is a unit for every `μ ≠ 0`, with
two-sided inverse `Y + μ⁻¹ • (1 - P)`. -/
theorem isUnit_corner_add_smul_compl {P B Y : A} {μ : ℂ}
    (hPP : P * P = P) (hμ : μ ≠ 0)
    (hBY : B * Y = P) (hYB : Y * B = P)
    (hBP : B * P = B) (hPB : P * B = B)
    (hYP : Y * P = Y) (hPY : P * Y = Y) :
    IsUnit (B + μ • (1 - P)) := by
  have hPQ : P * (1 - P) = 0 := by rw [mul_sub, mul_one, hPP, sub_self]
  have hQP : (1 - P) * P = 0 := by rw [sub_mul, one_mul, hPP, sub_self]
  have hQQ : (1 - P) * (1 - P) = 1 - P := by
    rw [mul_sub, mul_one, hQP, sub_zero]
  have hBQ : B * (1 - P) = 0 := by rw [mul_sub, mul_one, hBP, sub_self]
  have hQB : (1 - P) * B = 0 := by rw [sub_mul, one_mul, hPB, sub_self]
  have hQY : (1 - P) * Y = 0 := by rw [sub_mul, one_mul, hPY, sub_self]
  have hYQ : Y * (1 - P) = 0 := by rw [mul_sub, mul_one, hYP, sub_self]
  have t2 : B * (μ⁻¹ • (1 - P)) = 0 := by
    rw [mul_smul_comm, hBQ, smul_zero]
  have t3 : (μ • (1 - P)) * Y = 0 := by
    rw [smul_mul_assoc, hQY, smul_zero]
  have t4 : (μ • (1 - P)) * (μ⁻¹ • (1 - P)) = 1 - P := by
    calc (μ • (1 - P)) * (μ⁻¹ • (1 - P))
        = μ • ((1 - P) * (μ⁻¹ • (1 - P))) := smul_mul_assoc _ _ _
      _ = μ • (μ⁻¹ • ((1 - P) * (1 - P))) :=
          congrArg _ (mul_smul_comm _ _ _)
      _ = (μ * μ⁻¹) • ((1 - P) * (1 - P)) := smul_smul _ _ _
      _ = 1 - P := by rw [mul_inv_cancel₀ hμ, one_smul, hQQ]
  have s2 : Y * (μ • (1 - P)) = 0 := by
    rw [mul_smul_comm, hYQ, smul_zero]
  have s3 : (μ⁻¹ • (1 - P)) * B = 0 := by
    rw [smul_mul_assoc, hQB, smul_zero]
  have s4 : (μ⁻¹ • (1 - P)) * (μ • (1 - P)) = 1 - P := by
    calc (μ⁻¹ • (1 - P)) * (μ • (1 - P))
        = μ⁻¹ • ((1 - P) * (μ • (1 - P))) := smul_mul_assoc _ _ _
      _ = μ⁻¹ • (μ • ((1 - P) * (1 - P))) :=
          congrArg _ (mul_smul_comm _ _ _)
      _ = (μ⁻¹ * μ) • ((1 - P) * (1 - P)) := smul_smul _ _ _
      _ = 1 - P := by rw [inv_mul_cancel₀ hμ, one_smul, hQQ]
  have hXY : (B + μ • (1 - P)) * (Y + μ⁻¹ • (1 - P)) = 1 := by
    calc (B + μ • (1 - P)) * (Y + μ⁻¹ • (1 - P))
        = (B * Y + B * (μ⁻¹ • (1 - P)))
          + ((μ • (1 - P)) * Y + (μ • (1 - P)) * (μ⁻¹ • (1 - P))) := by
            rw [add_mul, mul_add, mul_add]
      _ = (P + 0) + (0 + (1 - P)) := by rw [hBY, t2, t3, t4]
      _ = 1 := by rw [add_zero, zero_add, add_sub_cancel]
  have hYX : (Y + μ⁻¹ • (1 - P)) * (B + μ • (1 - P)) = 1 := by
    calc (Y + μ⁻¹ • (1 - P)) * (B + μ • (1 - P))
        = (Y * B + Y * (μ • (1 - P)))
          + ((μ⁻¹ • (1 - P)) * B + (μ⁻¹ • (1 - P)) * (μ • (1 - P))) := by
            rw [add_mul, mul_add, mul_add]
      _ = (P + 0) + (0 + (1 - P)) := by rw [hYB, s2, s3, s4]
      _ = 1 := by rw [add_zero, zero_add, add_sub_cancel]
  exact ⟨⟨B + μ • (1 - P), Y + μ⁻¹ • (1 - P), hXY, hYX⟩, rfl⟩

/-! ## Corner inverses for `(algebraMap ℂ A ν - a) * P` -/

/-- Corner inverse, global case: if `algebraMap ℂ A ν - a`
is a unit `u`, then `↑u⁻¹ * P` is a two-sided corner inverse
of `(algebraMap ℂ A ν - a) * P` in the `P`-corner. -/
theorem exists_corner_inv_of_isUnit {lam : ℂ} {R : ℝ}
    (hR : specIsolatedWithin a lam R) {r : ℝ}
    (hr : 0 < r) (hrR : r ≤ R) {ν : ℂ}
    (hB : IsUnit (algebraMap ℂ A ν - a)) :
    ∃ Y : A, (algebraMap ℂ A ν - a) * rieszProj a lam r * Y
        = rieszProj a lam r
      ∧ Y * ((algebraMap ℂ A ν - a) * rieszProj a lam r)
        = rieszProj a lam r
      ∧ Y * rieszProj a lam r = Y
      ∧ rieszProj a lam r * Y = Y := by
  obtain ⟨u, hu⟩ := hB
  have hPP : rieszProj a lam r * rieszProj a lam r = rieszProj a lam r :=
    rieszProj_mul_self a hR hr hrR
  have hPu : Commute (rieszProj a lam r) (u : A) := by
    rw [hu]
    exact commute_corner_algebraMap_sub a (rieszProj a lam r)
      (commute_a_rieszProj a lam r) ν
  have hPui : Commute (rieszProj a lam r) (↑u⁻¹ : A) := hPu.units_inv_right
  have tPP : ((u : A) * rieszProj a lam r) * ((↑u⁻¹ : A) * rieszProj a lam r)
      = rieszProj a lam r := by
    calc ((u : A) * rieszProj a lam r) * ((↑u⁻¹ : A) * rieszProj a lam r)
        = (u : A) * (rieszProj a lam r * ((↑u⁻¹ : A) * rieszProj a lam r)) :=
          mul_assoc _ _ _
      _ = (u : A) * ((rieszProj a lam r * (↑u⁻¹ : A)) * rieszProj a lam r) :=
          congrArg _ (mul_assoc _ _ _).symm
      _ = (u : A) * (((↑u⁻¹ : A) * rieszProj a lam r) * rieszProj a lam r) :=
          congrArg _ (congrArg (· * rieszProj a lam r) hPui.eq)
      _ = ((u : A) * ((↑u⁻¹ : A) * rieszProj a lam r)) * rieszProj a lam r :=
          (mul_assoc _ _ _).symm
      _ = (((u : A) * (↑u⁻¹ : A)) * rieszProj a lam r) * rieszProj a lam r :=
          congrArg (· * rieszProj a lam r) (mul_assoc _ _ _).symm
      _ = rieszProj a lam r := by rw [Units.mul_inv, one_mul, hPP]
  have sPP : ((↑u⁻¹ : A) * rieszProj a lam r) * ((u : A) * rieszProj a lam r)
      = rieszProj a lam r := by
    calc ((↑u⁻¹ : A) * rieszProj a lam r) * ((u : A) * rieszProj a lam r)
        = (↑u⁻¹ : A) * (rieszProj a lam r * ((u : A) * rieszProj a lam r)) :=
          mul_assoc _ _ _
      _ = (↑u⁻¹ : A) * ((rieszProj a lam r * (u : A)) * rieszProj a lam r) :=
          congrArg _ (mul_assoc _ _ _).symm
      _ = (↑u⁻¹ : A) * (((u : A) * rieszProj a lam r) * rieszProj a lam r) :=
          congrArg _ (congrArg (· * rieszProj a lam r) hPu.eq)
      _ = ((↑u⁻¹ : A) * ((u : A) * rieszProj a lam r)) * rieszProj a lam r :=
          (mul_assoc _ _ _).symm
      _ = (((↑u⁻¹ : A) * (u : A)) * rieszProj a lam r) * rieszProj a lam r :=
          congrArg (· * rieszProj a lam r) (mul_assoc _ _ _).symm
      _ = rieszProj a lam r := by rw [Units.inv_mul, one_mul, hPP]
  have hYP : (↑u⁻¹ : A) * rieszProj a lam r * rieszProj a lam r
      = (↑u⁻¹ : A) * rieszProj a lam r := by
    calc (↑u⁻¹ : A) * rieszProj a lam r * rieszProj a lam r
        = (↑u⁻¹ : A) * (rieszProj a lam r * rieszProj a lam r) :=
          mul_assoc _ _ _
      _ = (↑u⁻¹ : A) * rieszProj a lam r := by rw [hPP]
  have hPY : rieszProj a lam r * ((↑u⁻¹ : A) * rieszProj a lam r)
      = (↑u⁻¹ : A) * rieszProj a lam r := by
    calc rieszProj a lam r * ((↑u⁻¹ : A) * rieszProj a lam r)
        = (rieszProj a lam r * (↑u⁻¹ : A)) * rieszProj a lam r :=
          (mul_assoc _ _ _).symm
      _ = ((↑u⁻¹ : A) * rieszProj a lam r) * rieszProj a lam r :=
          congrArg (· * rieszProj a lam r) hPui.eq
      _ = (↑u⁻¹ : A) * rieszProj a lam r := hYP
  refine ⟨(↑u⁻¹ : A) * rieszProj a lam r, ?_, ?_, hYP, hPY⟩
  · show (algebraMap ℂ A ν - a) * rieszProj a lam r
        * ((↑u⁻¹ : A) * rieszProj a lam r) = rieszProj a lam r
    rw [← hu]
    exact tPP
  · show (↑u⁻¹ : A) * rieszProj a lam r
        * ((algebraMap ℂ A ν - a) * rieszProj a lam r) = rieszProj a lam r
    rw [← hu]
    exact sPP

/-- The value of the local calculus at `g = fun z => z - ν`:
`FC g = a * P - ν • P`. -/
theorem rieszLocalFC_sub_const_eq {lam : ℂ} {R : ℝ}
    (hR : specIsolatedWithin a lam R) {r : ℝ}
    (hr : 0 < r) (hrR : r ≤ R) (ν : ℂ) :
    rieszLocalFC a lam r (fun z => z - ν)
      = a * rieszProj a lam r - ν • rieszProj a lam r := by
  have hRr : specIsolatedWithin a lam r := specIsolatedWithin_of_le a hR hrR
  have hg : DifferentiableOn ℂ (fun z => z - ν) (Metric.closedBall lam r) :=
    differentiableOn_id.sub (differentiableOn_const ν)
  have hc : DifferentiableOn ℂ (fun _ => ν) (Metric.closedBall lam r) :=
    differentiableOn_const ν
  have hsum : (fun z => z - ν) + (fun _ => ν) = id := by
    funext z
    show (z - ν) + ν = z
    exact sub_add_cancel z ν
  have hFCadd := rieszLocalFC_add a hRr hg hc hr le_rfl
  rw [hsum] at hFCadd
  have hFCid : rieszLocalFC a lam r id = a * rieszProj a lam r :=
    rieszLocalFC_id a hRr hr le_rfl
  have hFCc : rieszLocalFC a lam r (fun _ => ν) = ν • rieszProj a lam r := by
    have heq : (fun _ : ℂ => ν) = ν • (fun _ : ℂ => (1 : ℂ)) := by
      funext z
      show ν = ν * 1
      exact (mul_one ν).symm
    calc rieszLocalFC a lam r (fun _ => ν)
        = rieszLocalFC a lam r (ν • (fun _ => (1 : ℂ))) := by rw [heq]
      _ = ν • rieszLocalFC a lam r (fun _ => (1 : ℂ)) :=
          rieszLocalFC_smul a ν r
      _ = ν • rieszProj a lam r := by rw [rieszLocalFC_one a r]
  have hE : rieszLocalFC a lam r (fun z => z - ν) + ν • rieszProj a lam r
      = a * rieszProj a lam r := by
    rw [← hFCc, ← hFCid]
    exact hFCadd.symm
  calc rieszLocalFC a lam r (fun z => z - ν)
      = (rieszLocalFC a lam r (fun z => z - ν) + ν • rieszProj a lam r)
        - ν • rieszProj a lam r := (add_sub_cancel_right _ _).symm
    _ = a * rieszProj a lam r - ν • rieszProj a lam r := by rw [hE]

/-- Corner inverse, spectral case: if `r < ‖ν - lam‖` (as
isolation forces for `ν ∈ spectrum ℂ a`, `ν ≠ lam`), then
`-FC (fun z => (z - ν)⁻¹)` is a two-sided corner inverse of
`(algebraMap ℂ A ν - a) * P` in the `P`-corner, by 8B-3
multiplicativity and the circle congruence
`FC (f * g) = FC 1 = P`. -/
theorem exists_corner_inv_of_dist_gt {lam : ℂ} {R : ℝ}
    (hR : specIsolatedWithin a lam R) {r : ℝ}
    (hr : 0 < r) (hrR : r ≤ R) {ν : ℂ}
    (hdist : r < ‖ν - lam‖) :
    ∃ Y : A, (algebraMap ℂ A ν - a) * rieszProj a lam r * Y
        = rieszProj a lam r
      ∧ Y * ((algebraMap ℂ A ν - a) * rieszProj a lam r)
        = rieszProj a lam r
      ∧ Y * rieszProj a lam r = Y
      ∧ rieszProj a lam r * Y = Y := by
  have hRr : specIsolatedWithin a lam r := specIsolatedWithin_of_le a hR hrR
  have hf : DifferentiableOn ℂ (fun z => (z - ν)⁻¹) (Metric.closedBall lam r) := by
    intro z hz
    rw [Metric.mem_closedBall, dist_eq_norm] at hz
    have hzν : z ≠ ν := by
      intro hzz
      rw [hzz] at hz
      exact absurd hz (not_le_of_gt hdist)
    exact (((differentiableAt_id.sub (differentiableAt_const ν)).inv
      (sub_ne_zero.mpr hzν)).differentiableWithinAt)
  have hg : DifferentiableOn ℂ (fun z => z - ν) (Metric.closedBall lam r) :=
    differentiableOn_id.sub (differentiableOn_const ν)
  have hmul_fg : rieszLocalFC a lam r
        ((fun z => (z - ν)⁻¹) * (fun z => z - ν))
      = rieszLocalFC a lam r (fun z => (z - ν)⁻¹)
        * rieszLocalFC a lam r (fun z => z - ν) :=
    rieszLocalFC_mul a hRr hf hg hr le_rfl
  have hmul_gf : rieszLocalFC a lam r
        ((fun z => z - ν) * (fun z => (z - ν)⁻¹))
      = rieszLocalFC a lam r (fun z => z - ν)
        * rieszLocalFC a lam r (fun z => (z - ν)⁻¹) :=
    rieszLocalFC_mul a hRr hg hf hr le_rfl
  have hcongr : rieszLocalFC a lam r
        ((fun z => (z - ν)⁻¹) * (fun z => z - ν)) = rieszProj a lam r := by
    calc rieszLocalFC a lam r ((fun z => (z - ν)⁻¹) * (fun z => z - ν))
        = rieszLocalFC a lam r (fun _ => (1 : ℂ)) := by
          refine rieszLocalFC_eq_of_forall_sphere_eq a hr (fun z hz => ?_)
          rw [Metric.mem_sphere, dist_eq_norm] at hz
          have hzν : z ≠ ν := by
            intro hzz
            rw [hzz] at hz
            rw [hz] at hdist
            exact lt_irrefl _ hdist
          show ((fun z => (z - ν)⁻¹) * (fun z => z - ν)) z = 1
          rw [Pi.mul_apply]
          exact inv_mul_cancel₀ (sub_ne_zero.mpr hzν)
      _ = rieszProj a lam r := rieszLocalFC_one a r
  have hFCg : rieszLocalFC a lam r (fun z => z - ν)
      = a * rieszProj a lam r - ν • rieszProj a lam r :=
    rieszLocalFC_sub_const_eq a hR hr hrR ν
  have hB : (algebraMap ℂ A ν - a) * rieszProj a lam r
      = - rieszLocalFC a lam r (fun z => z - ν) := by
    calc (algebraMap ℂ A ν - a) * rieszProj a lam r
        = ν • rieszProj a lam r - a * rieszProj a lam r := by
          rw [sub_mul, Algebra.algebraMap_eq_smul_one, smul_mul_assoc,
            one_mul]
      _ = - (a * rieszProj a lam r - ν • rieszProj a lam r) :=
          (neg_sub _ _).symm
      _ = - rieszLocalFC a lam r (fun z => z - ν) := by rw [hFCg]
  have hfg_eq : (fun z => z - ν) * (fun z => (z - ν)⁻¹)
      = (fun z => (z - ν)⁻¹) * (fun z => z - ν) := by
    funext z
    show (z - ν) * (z - ν)⁻¹ = (z - ν)⁻¹ * (z - ν)
    exact mul_comm _ _
  refine ⟨- rieszLocalFC a lam r (fun z => (z - ν)⁻¹), ?_, ?_, ?_, ?_⟩
  · show (algebraMap ℂ A ν - a) * rieszProj a lam r
        * (- rieszLocalFC a lam r (fun z => (z - ν)⁻¹)) = rieszProj a lam r
    rw [hB, neg_mul_neg]
    calc rieszLocalFC a lam r (fun z => z - ν)
          * rieszLocalFC a lam r (fun z => (z - ν)⁻¹)
        = rieszLocalFC a lam r ((fun z => z - ν) * (fun z => (z - ν)⁻¹)) :=
          hmul_gf.symm
      _ = rieszLocalFC a lam r ((fun z => (z - ν)⁻¹) * (fun z => z - ν)) := by
          rw [hfg_eq]
      _ = rieszProj a lam r := hcongr
  · show (- rieszLocalFC a lam r (fun z => (z - ν)⁻¹))
        * ((algebraMap ℂ A ν - a) * rieszProj a lam r) = rieszProj a lam r
    rw [hB, neg_mul_neg]
    calc rieszLocalFC a lam r (fun z => (z - ν)⁻¹)
          * rieszLocalFC a lam r (fun z => z - ν)
        = rieszLocalFC a lam r ((fun z => (z - ν)⁻¹) * (fun z => z - ν)) :=
          hmul_fg.symm
      _ = rieszProj a lam r := hcongr
  · show (- rieszLocalFC a lam r (fun z => (z - ν)⁻¹)) * rieszProj a lam r
      = - rieszLocalFC a lam r (fun z => (z - ν)⁻¹)
    rw [neg_mul, rieszLocalFC_mul_rieszProj a hRr hf hr le_rfl]
  · show rieszProj a lam r * (- rieszLocalFC a lam r (fun z => (z - ν)⁻¹))
      = - rieszLocalFC a lam r (fun z => (z - ν)⁻¹)
    rw [mul_neg, rieszProj_mul_rieszLocalFC a hRr hf hr le_rfl]

/-- Corner inverse for `(algebraMap ℂ A ν - a) * P`, for
every `ν ≠ lam`: the global case and the spectral case
together. -/
theorem exists_corner_inv_algebraMap_sub_mul_rieszProj {lam : ℂ} {R : ℝ}
    (hR : specIsolatedWithin a lam R) {r : ℝ}
    (hr : 0 < r) (hrR : r ≤ R) {ν : ℂ} (hνlam : ν ≠ lam) :
    ∃ Y : A, (algebraMap ℂ A ν - a) * rieszProj a lam r * Y
        = rieszProj a lam r
      ∧ Y * ((algebraMap ℂ A ν - a) * rieszProj a lam r)
        = rieszProj a lam r
      ∧ Y * rieszProj a lam r = Y
      ∧ rieszProj a lam r * Y = Y := by
  by_cases hν : ν ∈ spectrum ℂ a
  · have hRcopy := hR
    obtain ⟨-, hiso⟩ := hRcopy
    exact exists_corner_inv_of_dist_gt a hR hr hrR
      (lt_of_le_of_lt hrR (hiso ν hν hνlam))
  · exact exists_corner_inv_of_isUnit a hR hr hrR (spectrum.notMem_iff.mp hν)

/-- The corner machine assembled: for `ν ≠ lam` and any
`μ ≠ 0`, `(algebraMap ℂ A ν - a) * P + μ • (1 - P)` is a
unit. -/
theorem isUnit_corner_add_of_ne {lam : ℂ} {R : ℝ}
    (hR : specIsolatedWithin a lam R) {r : ℝ}
    (hr : 0 < r) (hrR : r ≤ R) {ν : ℂ} (hνlam : ν ≠ lam)
    {μ : ℂ} (hμ : μ ≠ 0) :
    IsUnit ((algebraMap ℂ A ν - a) * rieszProj a lam r
      + μ • (1 - rieszProj a lam r)) := by
  obtain ⟨Y, hBY, hYB, hYP, hPY⟩ :=
    exists_corner_inv_algebraMap_sub_mul_rieszProj a hR hr hrR hνlam
  have hPP : rieszProj a lam r * rieszProj a lam r = rieszProj a lam r :=
    rieszProj_mul_self a hR hr hrR
  have hBP : (algebraMap ℂ A ν - a) * rieszProj a lam r * rieszProj a lam r
      = (algebraMap ℂ A ν - a) * rieszProj a lam r := by
    calc (algebraMap ℂ A ν - a) * rieszProj a lam r * rieszProj a lam r
        = (algebraMap ℂ A ν - a) * (rieszProj a lam r * rieszProj a lam r) :=
          mul_assoc _ _ _
      _ = (algebraMap ℂ A ν - a) * rieszProj a lam r := by rw [hPP]
  have hPB : rieszProj a lam r
        * ((algebraMap ℂ A ν - a) * rieszProj a lam r)
      = (algebraMap ℂ A ν - a) * rieszProj a lam r := by
    calc rieszProj a lam r * ((algebraMap ℂ A ν - a) * rieszProj a lam r)
        = (rieszProj a lam r * (algebraMap ℂ A ν - a)) * rieszProj a lam r :=
          (mul_assoc _ _ _).symm
      _ = ((algebraMap ℂ A ν - a) * rieszProj a lam r) * rieszProj a lam r :=
          congrArg (· * rieszProj a lam r)
            (commute_corner_algebraMap_sub a (rieszProj a lam r)
              (commute_a_rieszProj a lam r) ν).eq
      _ = (algebraMap ℂ A ν - a) * rieszProj a lam r := hBP
  exact isUnit_corner_add_smul_compl hPP hμ hBY hYB hBP hPB hYP hPY

/-- Sharp resolvent form at the `P`-corner: for `μ ≠ 0`
with `μ ≠ lam`, `algebraMap ℂ A μ - a * P` is a unit. -/
theorem isUnit_algebraMap_sub_mul_rieszProj_sharp {lam : ℂ} {R : ℝ}
    (hR : specIsolatedWithin a lam R) {r : ℝ}
    (hr : 0 < r) (hrR : r ≤ R) {μ : ℂ} (hμ : μ ≠ 0) (hμlam : μ ≠ lam) :
    IsUnit (algebraMap ℂ A μ - a * rieszProj a lam r) := by
  have hU := isUnit_corner_add_of_ne a hR hr hrR hμlam hμ
  rwa [sub_mul_add_smul_compl_eq a (rieszProj a lam r) μ] at hU

/-! ## Headline (target 1): the sharp inclusion for `a * P` -/

/-- **Headline (8B-4(ii), target 1):**
`spectrum ℂ (a * rieszProj a lam r) ⊆ {0, lam}`, under the
isolation hypotheses exactly as landed for the projection
algebra. Inclusion only - no equality is stated. -/
theorem spectrum_mul_rieszProj_subset_pair {lam : ℂ} {R : ℝ}
    (hR : specIsolatedWithin a lam R) {r : ℝ}
    (hr : 0 < r) (hrR : r ≤ R) :
    spectrum ℂ (a * rieszProj a lam r) ⊆ {0, lam} := by
  intro μ hμspec
  by_cases h0 : μ = 0
  · simp [h0]
  · by_cases hlam : μ = lam
    · simp [hlam]
    · exfalso
      have hU : IsUnit (algebraMap ℂ A μ - a * rieszProj a lam r) :=
        isUnit_algebraMap_sub_mul_rieszProj_sharp a hR hr hrR h0 hlam
      exact spectrum.mem_iff.mp hμspec hU

/-! ## The auxiliary integral at the complementary corner -/

/-- Pointwise auxiliary identity (the identity inside
`rieszProj_ne_zero`, `RieszGate.lean:232`): at a resolvent
point `z`, `(algebraMap ℂ A lam - a) * resolvent a z
= 1 - (z - lam) • resolvent a z`. -/
theorem algebraMap_sub_mul_resolvent_eq {lam z : ℂ}
    (hz : z ∈ resolventSet ℂ a) :
    (algebraMap ℂ A lam - a) * resolvent a z
      = 1 - (z - lam) • resolvent a z := by
  have h1 : (algebraMap ℂ A z - a) * resolvent a z = 1 := by
    have e : (algebraMap ℂ A z - a) * resolvent a z
        = ↑hz.unit * ↑hz.unit⁻¹ := by
      rw [spectrum.resolvent_eq hz, hz.unit_spec]
    rw [e]
    exact Units.mul_inv _
  have h2 : (algebraMap ℂ A lam - algebraMap ℂ A z) * resolvent a z
      = -((z - lam) • resolvent a z) := by
    have e1 : algebraMap ℂ A lam - algebraMap ℂ A z
        = -algebraMap ℂ A (z - lam) := by
      rw [← map_sub, ← neg_sub z lam, map_neg]
    rw [e1, Algebra.smul_def, neg_mul]
  calc (algebraMap ℂ A lam - a) * resolvent a z
      = (algebraMap ℂ A lam - algebraMap ℂ A z) * resolvent a z
        + (algebraMap ℂ A z - a) * resolvent a z := by
        rw [← add_mul]
        congr 1
        abel
    _ = -((z - lam) • resolvent a z) + 1 := by rw [h2, h1]
    _ = 1 - (z - lam) • resolvent a z := by abel

/-- The mirrored pointwise auxiliary identity. -/
theorem resolvent_mul_algebraMap_sub_eq {lam z : ℂ}
    (hz : z ∈ resolventSet ℂ a) :
    resolvent a z * (algebraMap ℂ A lam - a)
      = 1 - (z - lam) • resolvent a z := by
  have hcomm : Commute (algebraMap ℂ A lam - a) (resolvent a z) :=
    Commute.sub_left (Algebra.commutes lam (resolvent a z))
      (commute_a_resolvent_all a)
  calc resolvent a z * (algebraMap ℂ A lam - a)
      = (algebraMap ℂ A lam - a) * resolvent a z := hcomm.eq.symm
    _ = 1 - (z - lam) • resolvent a z :=
        algebraMap_sub_mul_resolvent_eq a hz

/-- The auxiliary integral identity, left form: with
`W = rieszLocalFC a lam r (fun z => (z - lam)⁻¹)` (the
`(z - lam)⁻¹`-weighted resolvent integral - a bare circle
integral here, NOT an application of the holomorphic local
calculus, since `z ↦ (z - lam)⁻¹` is not holomorphic at
`lam`), `(algebraMap ℂ A lam - a) * W = 1 - P`. -/
theorem algebraMap_sub_mul_rieszLocalFC_inv_sub_eq {lam : ℂ} {R : ℝ}
    (hR : specIsolatedWithin a lam R) {r : ℝ}
    (hr : 0 < r) (hrR : r ≤ R) :
    (algebraMap ℂ A lam - a)
        * rieszLocalFC a lam r (fun z => (z - lam)⁻¹)
      = rieszComplProj a lam r := by
  have h2pi : (2 * π * Complex.I : ℂ) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (by norm_num) ?_) Complex.I_ne_zero
    exact Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hfR : CircleIntegrable (resolvent a) lam r :=
    circleIntegrable_resolvent_of_isolated a hR hr hrR
  have hnotmem : lam ∉ Metric.sphere lam |r| := by
    rw [Metric.mem_sphere, dist_self, abs_of_pos hr]
    exact ne_of_lt hr
  have hfAux : CircleIntegrable
      (fun z => (z - lam)⁻¹ • resolvent a z) lam r := by
    have h := hfR.sub_zpow_smul (-1 : ℤ) hnotmem
    simpa only [zpow_neg_one] using h
  have hfConst : CircleIntegrable
      (fun z => (z - lam)⁻¹ • (1 : A)) lam r := by
    have h := (circleIntegrable_const (1 : A) lam r).sub_zpow_smul (-1 : ℤ)
      hnotmem
    simpa only [zpow_neg_one] using h
  have hJeq : (∮ z in C(lam, r), resolvent a z)
      = (2 * π * Complex.I : ℂ) • rieszProj a lam r := by
    show (∮ z in C(lam, r), resolvent a z)
      = (2 * π * Complex.I : ℂ)
        • ((2 * π * Complex.I : ℂ)⁻¹ • ∮ z in C(lam, r), resolvent a z)
    rw [smul_inv_smul₀ h2pi]
  have hJ : (algebraMap ℂ A lam - a)
        * (∮ z in C(lam, r), (z - lam)⁻¹ • resolvent a z)
      = (2 * π * Complex.I : ℂ) • (1 - rieszProj a lam r) := by
    calc (algebraMap ℂ A lam - a)
          * (∮ z in C(lam, r), (z - lam)⁻¹ • resolvent a z)
        = ∮ z in C(lam, r),
            (algebraMap ℂ A lam - a) * ((z - lam)⁻¹ • resolvent a z) :=
          const_mul_circleIntegral (algebraMap ℂ A lam - a) hfAux
      _ = ∮ z in C(lam, r), ((z - lam)⁻¹ • (1 : A) - resolvent a z) := by
          refine circleIntegral.integral_congr hr.le (fun z hz => ?_)
          have hzres : z ∈ resolventSet ℂ a :=
            mem_resolventSet_of_sphere_of_isolated a hR hr hrR hz
          have hzne : z ≠ lam := by
            intro hzz
            rw [Metric.mem_sphere, dist_eq_norm, hzz, sub_self, norm_zero]
              at hz
            exact hr.ne' hz.symm
          show (algebraMap ℂ A lam - a) * ((z - lam)⁻¹ • resolvent a z)
            = (z - lam)⁻¹ • (1 : A) - resolvent a z
          rw [mul_smul_comm, algebraMap_sub_mul_resolvent_eq a hzres,
            smul_sub, smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr hzne),
            one_smul]
      _ = (∮ z in C(lam, r), (z - lam)⁻¹ • (1 : A))
          - ∮ z in C(lam, r), resolvent a z :=
          circleIntegral.integral_sub hfConst hfR
      _ = (2 * π * Complex.I : ℂ) • (1 : A)
          - (2 * π * Complex.I : ℂ) • rieszProj a lam r := by
          rw [circleIntegral.integral_smul_const,
            circleIntegral.integral_sub_inv_of_mem_ball
              (Metric.mem_ball_self hr), hJeq]
      _ = (2 * π * Complex.I : ℂ) • (1 - rieszProj a lam r) := by
          rw [smul_sub]
  show (algebraMap ℂ A lam - a)
      * ((2 * π * Complex.I : ℂ)⁻¹
        • ∮ z in C(lam, r), (z - lam)⁻¹ • resolvent a z)
    = rieszComplProj a lam r
  rw [mul_smul_comm, hJ, inv_smul_smul₀ h2pi]
  rfl

/-- The auxiliary integral identity, right form:
`W * (algebraMap ℂ A lam - a) = 1 - P`. -/
theorem rieszLocalFC_inv_sub_mul_algebraMap_sub_eq {lam : ℂ} {R : ℝ}
    (hR : specIsolatedWithin a lam R) {r : ℝ}
    (hr : 0 < r) (hrR : r ≤ R) :
    rieszLocalFC a lam r (fun z => (z - lam)⁻¹)
        * (algebraMap ℂ A lam - a)
      = rieszComplProj a lam r := by
  have h2pi : (2 * π * Complex.I : ℂ) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (by norm_num) ?_) Complex.I_ne_zero
    exact Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hfR : CircleIntegrable (resolvent a) lam r :=
    circleIntegrable_resolvent_of_isolated a hR hr hrR
  have hnotmem : lam ∉ Metric.sphere lam |r| := by
    rw [Metric.mem_sphere, dist_self, abs_of_pos hr]
    exact ne_of_lt hr
  have hfAux : CircleIntegrable
      (fun z => (z - lam)⁻¹ • resolvent a z) lam r := by
    have h := hfR.sub_zpow_smul (-1 : ℤ) hnotmem
    simpa only [zpow_neg_one] using h
  have hfConst : CircleIntegrable
      (fun z => (z - lam)⁻¹ • (1 : A)) lam r := by
    have h := (circleIntegrable_const (1 : A) lam r).sub_zpow_smul (-1 : ℤ)
      hnotmem
    simpa only [zpow_neg_one] using h
  have hJeq : (∮ z in C(lam, r), resolvent a z)
      = (2 * π * Complex.I : ℂ) • rieszProj a lam r := by
    show (∮ z in C(lam, r), resolvent a z)
      = (2 * π * Complex.I : ℂ)
        • ((2 * π * Complex.I : ℂ)⁻¹ • ∮ z in C(lam, r), resolvent a z)
    rw [smul_inv_smul₀ h2pi]
  have hJ : (∮ z in C(lam, r), (z - lam)⁻¹ • resolvent a z)
        * (algebraMap ℂ A lam - a)
      = (2 * π * Complex.I : ℂ) • (1 - rieszProj a lam r) := by
    calc (∮ z in C(lam, r), (z - lam)⁻¹ • resolvent a z)
          * (algebraMap ℂ A lam - a)
        = ∮ z in C(lam, r),
            ((z - lam)⁻¹ • resolvent a z) * (algebraMap ℂ A lam - a) :=
          circleIntegral_mul_const (algebraMap ℂ A lam - a) hfAux
      _ = ∮ z in C(lam, r), ((z - lam)⁻¹ • (1 : A) - resolvent a z) := by
          refine circleIntegral.integral_congr hr.le (fun z hz => ?_)
          have hzres : z ∈ resolventSet ℂ a :=
            mem_resolventSet_of_sphere_of_isolated a hR hr hrR hz
          have hzne : z ≠ lam := by
            intro hzz
            rw [Metric.mem_sphere, dist_eq_norm, hzz, sub_self, norm_zero]
              at hz
            exact hr.ne' hz.symm
          show ((z - lam)⁻¹ • resolvent a z) * (algebraMap ℂ A lam - a)
            = (z - lam)⁻¹ • (1 : A) - resolvent a z
          rw [smul_mul_assoc, resolvent_mul_algebraMap_sub_eq a hzres,
            smul_sub, smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr hzne),
            one_smul]
      _ = (∮ z in C(lam, r), (z - lam)⁻¹ • (1 : A))
          - ∮ z in C(lam, r), resolvent a z :=
          circleIntegral.integral_sub hfConst hfR
      _ = (2 * π * Complex.I : ℂ) • (1 : A)
          - (2 * π * Complex.I : ℂ) • rieszProj a lam r := by
          rw [circleIntegral.integral_smul_const,
            circleIntegral.integral_sub_inv_of_mem_ball
              (Metric.mem_ball_self hr), hJeq]
      _ = (2 * π * Complex.I : ℂ) • (1 - rieszProj a lam r) := by
          rw [smul_sub]
  show ((2 * π * Complex.I : ℂ)⁻¹
      • ∮ z in C(lam, r), (z - lam)⁻¹ • resolvent a z)
      * (algebraMap ℂ A lam - a)
    = rieszComplProj a lam r
  rw [smul_mul_assoc, hJ, inv_smul_smul₀ h2pi]
  rfl

/-! ## Headline (target 2, corrected): `lam` is not in the
spectrum of `a * Q`, for `lam ≠ 0` -/

/-- **Headline (8B-4(ii), target 2, CORRECTED form - see the
module header for the `lam = 0` counterexample to the
registered statement):** for `lam ≠ 0`,
`lam ∉ spectrum ℂ (a * rieszComplProj a lam r)`, under the
isolation hypotheses exactly as landed for the projection
algebra. The corner inverse of
`(algebraMap ℂ A lam - a) * Q` is `Q * W * Q` with `W` the
auxiliary integral; the scalar corner is `lam • P`, which
is where `lam ≠ 0` is consumed. -/
theorem lam_not_mem_spectrum_mul_rieszComplProj {lam : ℂ} {R : ℝ}
    (hR : specIsolatedWithin a lam R) {r : ℝ}
    (hr : 0 < r) (hrR : r ≤ R) (hlam : lam ≠ 0) :
    lam ∉ spectrum ℂ (a * rieszComplProj a lam r) := by
  have hQQ : rieszComplProj a lam r * rieszComplProj a lam r
      = rieszComplProj a lam r :=
    rieszComplProj_mul_self a hR hr hrR
  have hcommQ : Commute (algebraMap ℂ A lam - a) (rieszComplProj a lam r) :=
    Commute.sub_left (Algebra.commutes lam (rieszComplProj a lam r))
      (commute_a_rieszComplProj a lam r)
  have hBW : (algebraMap ℂ A lam - a)
        * rieszLocalFC a lam r (fun z => (z - lam)⁻¹)
      = rieszComplProj a lam r :=
    algebraMap_sub_mul_rieszLocalFC_inv_sub_eq a hR hr hrR
  have hWB : rieszLocalFC a lam r (fun z => (z - lam)⁻¹)
        * (algebraMap ℂ A lam - a)
      = rieszComplProj a lam r :=
    rieszLocalFC_inv_sub_mul_algebraMap_sub_eq a hR hr hrR
  -- The four corner facts for `B = (algebraMap ℂ A lam - a) * Q`
  -- and its corner inverse `Y = Q * W * Q`, at the corner `Q`.
  have hBqQ : (algebraMap ℂ A lam - a) * rieszComplProj a lam r
        * rieszComplProj a lam r
      = (algebraMap ℂ A lam - a) * rieszComplProj a lam r := by
    calc (algebraMap ℂ A lam - a) * rieszComplProj a lam r
          * rieszComplProj a lam r
        = (algebraMap ℂ A lam - a)
          * (rieszComplProj a lam r * rieszComplProj a lam r) :=
          mul_assoc _ _ _
      _ = (algebraMap ℂ A lam - a) * rieszComplProj a lam r := by rw [hQQ]
  have hQBq : rieszComplProj a lam r
        * ((algebraMap ℂ A lam - a) * rieszComplProj a lam r)
      = (algebraMap ℂ A lam - a) * rieszComplProj a lam r := by
    calc rieszComplProj a lam r
          * ((algebraMap ℂ A lam - a) * rieszComplProj a lam r)
        = (rieszComplProj a lam r * (algebraMap ℂ A lam - a))
          * rieszComplProj a lam r := by simp only [mul_assoc]
      _ = ((algebraMap ℂ A lam - a) * rieszComplProj a lam r)
          * rieszComplProj a lam r := by rw [← hcommQ.eq]
      _ = (algebraMap ℂ A lam - a) * rieszComplProj a lam r := hBqQ
  have hYQ : rieszComplProj a lam r
        * rieszLocalFC a lam r (fun z => (z - lam)⁻¹)
        * rieszComplProj a lam r * rieszComplProj a lam r
      = rieszComplProj a lam r
        * rieszLocalFC a lam r (fun z => (z - lam)⁻¹)
        * rieszComplProj a lam r := by
    calc rieszComplProj a lam r
          * rieszLocalFC a lam r (fun z => (z - lam)⁻¹)
          * rieszComplProj a lam r * rieszComplProj a lam r
        = (rieszComplProj a lam r
          * rieszLocalFC a lam r (fun z => (z - lam)⁻¹))
          * (rieszComplProj a lam r * rieszComplProj a lam r) := by
          simp only [mul_assoc]
      _ = rieszComplProj a lam r
          * rieszLocalFC a lam r (fun z => (z - lam)⁻¹)
          * rieszComplProj a lam r := by rw [hQQ]
  have hQY : rieszComplProj a lam r
        * (rieszComplProj a lam r
          * rieszLocalFC a lam r (fun z => (z - lam)⁻¹)
          * rieszComplProj a lam r)
      = rieszComplProj a lam r
        * rieszLocalFC a lam r (fun z => (z - lam)⁻¹)
        * rieszComplProj a lam r := by
    calc rieszComplProj a lam r
          * (rieszComplProj a lam r
            * rieszLocalFC a lam r (fun z => (z - lam)⁻¹)
            * rieszComplProj a lam r)
        = ((rieszComplProj a lam r * rieszComplProj a lam r)
          * rieszLocalFC a lam r (fun z => (z - lam)⁻¹))
          * rieszComplProj a lam r := by simp only [mul_assoc]
      _ = rieszComplProj a lam r
          * rieszLocalFC a lam r (fun z => (z - lam)⁻¹)
          * rieszComplProj a lam r := by rw [hQQ]
  have hBYq : (algebraMap ℂ A lam - a) * rieszComplProj a lam r
        * (rieszComplProj a lam r
          * rieszLocalFC a lam r (fun z => (z - lam)⁻¹)
          * rieszComplProj a lam r)
      = rieszComplProj a lam r := by
    calc (algebraMap ℂ A lam - a) * rieszComplProj a lam r
          * (rieszComplProj a lam r
            * rieszLocalFC a lam r (fun z => (z - lam)⁻¹)
            * rieszComplProj a lam r)
        = ((algebraMap ℂ A lam - a)
          * ((rieszComplProj a lam r * rieszComplProj a lam r)
            * rieszLocalFC a lam r (fun z => (z - lam)⁻¹)))
          * rieszComplProj a lam r := by simp only [mul_assoc]
      _ = ((algebraMap ℂ A lam - a)
          * (rieszComplProj a lam r
            * rieszLocalFC a lam r (fun z => (z - lam)⁻¹)))
          * rieszComplProj a lam r := by rw [hQQ]
      _ = (((algebraMap ℂ A lam - a) * rieszComplProj a lam r)
          * rieszLocalFC a lam r (fun z => (z - lam)⁻¹))
          * rieszComplProj a lam r := by simp only [mul_assoc]
      _ = ((rieszComplProj a lam r * (algebraMap ℂ A lam - a))
          * rieszLocalFC a lam r (fun z => (z - lam)⁻¹))
          * rieszComplProj a lam r := by rw [hcommQ.eq]
      _ = (rieszComplProj a lam r
          * ((algebraMap ℂ A lam - a)
            * rieszLocalFC a lam r (fun z => (z - lam)⁻¹)))
          * rieszComplProj a lam r := by simp only [mul_assoc]
      _ = (rieszComplProj a lam r * rieszComplProj a lam r)
          * rieszComplProj a lam r := by rw [hBW]
      _ = rieszComplProj a lam r := by rw [hQQ, hQQ]
  have hYBq : rieszComplProj a lam r
        * rieszLocalFC a lam r (fun z => (z - lam)⁻¹)
        * rieszComplProj a lam r
        * ((algebraMap ℂ A lam - a) * rieszComplProj a lam r)
      = rieszComplProj a lam r := by
    calc rieszComplProj a lam r
          * rieszLocalFC a lam r (fun z => (z - lam)⁻¹)
          * rieszComplProj a lam r
          * ((algebraMap ℂ A lam - a) * rieszComplProj a lam r)
        = (rieszComplProj a lam r
          * rieszLocalFC a lam r (fun z => (z - lam)⁻¹))
          * ((rieszComplProj a lam r * (algebraMap ℂ A lam - a))
            * rieszComplProj a lam r) := by simp only [mul_assoc]
      _ = (rieszComplProj a lam r
          * rieszLocalFC a lam r (fun z => (z - lam)⁻¹))
          * (((algebraMap ℂ A lam - a) * rieszComplProj a lam r)
            * rieszComplProj a lam r) := by rw [← hcommQ.eq]
      _ = (rieszComplProj a lam r
          * rieszLocalFC a lam r (fun z => (z - lam)⁻¹))
          * ((algebraMap ℂ A lam - a)
            * (rieszComplProj a lam r * rieszComplProj a lam r)) := by
          simp only [mul_assoc]
      _ = (rieszComplProj a lam r
          * rieszLocalFC a lam r (fun z => (z - lam)⁻¹))
          * ((algebraMap ℂ A lam - a) * rieszComplProj a lam r) := by
          rw [hQQ]
      _ = ((rieszComplProj a lam r
          * rieszLocalFC a lam r (fun z => (z - lam)⁻¹))
          * (algebraMap ℂ A lam - a)) * rieszComplProj a lam r := by
          simp only [mul_assoc]
      _ = (rieszComplProj a lam r
          * (rieszLocalFC a lam r (fun z => (z - lam)⁻¹)
            * (algebraMap ℂ A lam - a))) * rieszComplProj a lam r := by
          simp only [mul_assoc]
      _ = (rieszComplProj a lam r * rieszComplProj a lam r)
          * rieszComplProj a lam r := by rw [hWB]
      _ = rieszComplProj a lam r := by rw [hQQ, hQQ]
  have hU : IsUnit (algebraMap ℂ A lam - a * rieszComplProj a lam r) := by
    have hU' := isUnit_corner_add_smul_compl (P := rieszComplProj a lam r)
      (B := (algebraMap ℂ A lam - a) * rieszComplProj a lam r)
      (Y := rieszComplProj a lam r
        * rieszLocalFC a lam r (fun z => (z - lam)⁻¹)
        * rieszComplProj a lam r)
      hQQ hlam hBYq hYBq hBqQ hQBq hYQ hQY
    rwa [sub_mul_add_smul_compl_eq a (rieszComplProj a lam r) lam] at hU'
  intro hmem
  exact spectrum.mem_iff.mp hmem hU

/-! ## Headline (target 3): the quasinilpotent corollary -/

/-- The decomposition behind target 3:
`(algebraMap ℂ A (μ + lam) - a) * P + μ • (1 - P)
= algebraMap ℂ A μ - (a - lam • 1) * P`. -/
theorem algebraMap_sub_sub_smul_mul_rieszProj_eq {lam : ℂ} (μ : ℂ) (r : ℝ) :
    (algebraMap ℂ A (μ + lam) - a) * rieszProj a lam r
        + μ • (1 - rieszProj a lam r)
      = algebraMap ℂ A μ - (a - lam • (1 : A)) * rieszProj a lam r := by
  calc (algebraMap ℂ A (μ + lam) - a) * rieszProj a lam r
        + μ • (1 - rieszProj a lam r)
      = (((μ + lam) • (1 : A) - a) * rieszProj a lam r)
        + μ • (1 - rieszProj a lam r) := by
          rw [Algebra.algebraMap_eq_smul_one (μ + lam)]
    _ = (((μ + lam) • rieszProj a lam r - a * rieszProj a lam r))
        + (μ • (1 : A) - μ • rieszProj a lam r) := by
          rw [sub_mul, smul_mul_assoc, one_mul, smul_sub]
    _ = ((μ • rieszProj a lam r + lam • rieszProj a lam r)
        - a * rieszProj a lam r)
        + (μ • (1 : A) - μ • rieszProj a lam r) := by
          rw [add_smul]
    _ = μ • (1 : A) - (a * rieszProj a lam r - lam • rieszProj a lam r) := by
          abel
    _ = algebraMap ℂ A μ - (a - lam • (1 : A)) * rieszProj a lam r := by
          rw [Algebra.algebraMap_eq_smul_one μ, sub_mul, smul_mul_assoc,
            one_mul]

/-- **Headline (8B-4(ii), target 3, corollary):**
`spectrum ℂ ((a - lam • 1) * rieszProj a lam r) ⊆ {0}`,
under the same isolation hypotheses. Via the corner
machine at `ν = μ + lam`: for `μ ≠ 0` one has `ν ≠ lam`,
and the decomposition
`algebraMap_sub_sub_smul_mul_rieszProj_eq` identifies the
resolvent element with the corner sum at `ν`. -/
theorem spectrum_sub_smul_mul_rieszProj_subset {lam : ℂ} {R : ℝ}
    (hR : specIsolatedWithin a lam R) {r : ℝ}
    (hr : 0 < r) (hrR : r ≤ R) :
    spectrum ℂ ((a - lam • (1 : A)) * rieszProj a lam r) ⊆ {0} := by
  intro μ hμspec
  by_cases h0 : μ = 0
  · exact Set.mem_singleton_iff.mpr h0
  · exfalso
    have hνlam : μ + lam ≠ lam := by
      intro h
      apply h0
      have h' : μ + lam = 0 + lam := by rw [h, zero_add]
      exact add_right_cancel h'
    have hU : IsUnit (algebraMap ℂ A μ
        - (a - lam • (1 : A)) * rieszProj a lam r) := by
      have hU' := isUnit_corner_add_of_ne a hR hr hrR hνlam h0
      rwa [algebraMap_sub_sub_smul_mul_rieszProj_eq a μ r] at hU'
    exact spectrum.mem_iff.mp hμspec hU

/-! ## The `lam = 0` counterexample to target 2 as
registered (machine-checked kill) -/

/-- **Counterexample (KILL of target 2 as registered):**
at `A = ℂ`, `a = 0`, `lam = 0`, `r = 1`, one has
`0 ∈ spectrum ℂ ((0 : ℂ) * rieszComplProj (0 : ℂ) 0 1)`,
i.e. `lam ∈ spectrum ℂ (a * (1 - P))`. Here
`spectrum ℂ (0 : ℂ) = {0}` makes `lam = 0` isolated, the
Riesz projection is `P = 1`, the complement is `Q = 0`, and
`a * Q = 0`. Hence the registered target 2, stated without
a side condition on `lam`, is false; the corrected form
above carries `lam ≠ 0` on its face. -/
theorem zero_mem_spectrum_mul_rieszComplProj_at_zero :
    (0 : ℂ) ∈ spectrum ℂ ((0 : ℂ) * rieszComplProj (0 : ℂ) 0 1) := by
  have h2pi : (2 * π * Complex.I : ℂ) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (by norm_num) ?_) Complex.I_ne_zero
    exact Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hsphere : ∀ z ∈ Metric.sphere (0 : ℂ) 1,
      z ∈ resolventSet ℂ (0 : ℂ) := by
    intro z hz
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero] at hz
    have hz0 : z ≠ 0 := by
      intro hzz
      rw [hzz, norm_zero] at hz
      exact one_ne_zero hz.symm
    show IsUnit (algebraMap ℂ ℂ z - (0 : ℂ))
    rw [Algebra.algebraMap_eq_smul_one, smul_eq_mul, mul_one, sub_zero]
    exact isUnit_iff_ne_zero.mpr hz0
  have hfR : CircleIntegrable (resolvent (0 : ℂ)) 0 1 :=
    circleIntegrable_resolvent_of_nonneg (0 : ℂ) zero_le_one hsphere
  have hJ : (∮ z in C((0 : ℂ), 1), resolvent (0 : ℂ) z)
      = (2 * π * Complex.I : ℂ) • (1 : ℂ) := by
    calc (∮ z in C((0 : ℂ), 1), resolvent (0 : ℂ) z)
        = ∮ z in C((0 : ℂ), 1), (z - 0)⁻¹ • (1 : ℂ) := by
          refine circleIntegral.integral_congr zero_le_one (fun z hz => ?_)
          have hzres : z ∈ resolventSet ℂ (0 : ℂ) := hsphere z hz
          have hunit : (↑hzres.unit : ℂ) = z := by
            rw [hzres.unit_spec, Algebra.algebraMap_eq_smul_one, smul_eq_mul,
              mul_one, sub_zero]
          show resolvent (0 : ℂ) z = (z - 0)⁻¹ • (1 : ℂ)
          rw [spectrum.resolvent_eq hzres, Units.val_inv_eq_inv_val, hunit,
            sub_zero, smul_eq_mul, mul_one]
      _ = (2 * π * Complex.I : ℂ) • (1 : ℂ) := by
          rw [circleIntegral.integral_smul_const,
            circleIntegral.integral_sub_inv_of_mem_ball
              (Metric.mem_ball_self one_pos)]
  have hP : rieszProj (0 : ℂ) 0 1 = 1 := by
    show (2 * π * Complex.I : ℂ)⁻¹
        • (∮ z in C((0 : ℂ), 1), resolvent (0 : ℂ) z) = 1
    rw [hJ, inv_smul_smul₀ h2pi]
  have hQ : rieszComplProj (0 : ℂ) 0 1 = 0 := by
    show (1 : ℂ) - rieszProj (0 : ℂ) 0 1 = 0
    rw [hP, sub_self]
  rw [hQ, mul_zero]
  refine spectrum.mem_iff.mpr ?_
  rw [map_zero, sub_zero]
  simp [isUnit_iff_ne_zero]

end

end ThetLogos
