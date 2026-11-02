/-
# SHELF-8b, extension 8B-4(i) - algebra-level spectral splitting,
cheap half: INCLUSIONS only

Brick 8B-4(i) of the SHELF-8b extensions (registration
`whitepaper/shelf-8b345-registration-2026-11-02.md`, scoping
`whitepaper/shelf-8b-scoping-2026-11-02.md` SS2, 8B-4 paragraph,
part (i)): for the Riesz projection `P = rieszProj a lam r` of
GATE-A1/GATE-A2 and its complement `1 - P` of 8B-1
(`ThetLogos.RieszComplementary`), the ambient-spectrum inclusions

  `spectrum C (a * P) ⊆ {0} ∪ spectrum C a`,
  `spectrum C (a * (1 - P)) ⊆ {0} ∪ spectrum C a`.

NO CLAIM beyond the theorems below; no dial is touched.

Route (the scoping's candidate inverse, with the sign as in the
task pack - the scoping text's minus sign in front of the
`mu⁻¹ • (1 - P)` term is a typo: with a minus the corner products
below give `P - (1 - P)`, not `1`): for `mu ≠ 0` with
`mu ∉ spectrum C a`, write, with `B = algebraMap C A mu - a`,

  `algebraMap C A mu - a * P = B * P + mu • (1 - P)`

(the decomposition lemma below), and exhibit the two-sided
inverse `↑hB.unit⁻¹ * P + mu⁻¹ • (1 - P)` of it, where
`hB : IsUnit B`. The corner products close by the landed
algebra of `P`: idempotence, both orthogonality products
against `1 - P`, and commutation of `P` with `a`, hence with
`B` and with its inverse. The complement headline is the same
proof at the corner `1 - P`.

Hypothesis adjustment, flagged at full rank (the 8B-1 pattern,
recorded, not silent): the registration pin states part (i)
with no isolation hypothesis, but the only landed route to
`P * P = P` and to the orthogonality products is
`rieszProj_mul_self` / the 8B-1 algebra, which carry
`specIsolatedWithin a lam R`, `0 < r`, `r ≤ R`. The headlines
below therefore carry those hypotheses exactly as landed; a
Riesz integral at a non-isolating radius is not a projection
and the inclusions are not asserted there. Commutation of `a`
with `P` needs no isolation and is consumed as landed.

Fences on the face (registration / scoping SS3):
* Part (ii) is NOT in this brick - it is gated on 8B-3:
  no `{0, lam}` sharp inclusion, no `lam`-exclusion from
  `spectrum C (a * (1 - P))`, no quasinilpotent corollary
  (`spectrum C ((a - lam • 1) * P) ⊆ {0}`) is stated or
  attempted here.
* Seam S-8B-4: full splitting EQUALITIES and any
  CLM-restriction spectrum statement are the named remainder,
  unpriceable - they are NOT stated here.
* K-8B-KILLED-FORM untouched: no integrability is consumed
  in this brick at all; the proof is pure algebra over the
  landed projection algebra plus `spectrum.mem_iff` /
  `spectrum.notMem_iff` from the pin.
-/

import ThetLogos.RieszGate
import ThetLogos.RieszGateIdem
import ThetLogos.RieszComplementary

namespace ThetLogos

noncomputable section

variable {A : Type*} [NormedRing A] [NormOneClass A] [NormedAlgebra ℂ A]
  [CompleteSpace A]

variable (a : A)

/-! ## The corner decomposition and commutation -/

/-- The decomposition behind the candidate inverse: splitting
`algebraMap ℂ A μ - a * P` along the corner `P` and its
complement `1 - P`. No hypotheses on `P` are needed. -/
theorem sub_mul_add_smul_compl_eq (P : A) (μ : ℂ) :
    (algebraMap ℂ A μ - a) * P + μ • (1 - P)
      = algebraMap ℂ A μ - a * P := by
  have hmap : algebraMap ℂ A μ = μ • (1 : A) :=
    Algebra.algebraMap_eq_smul_one μ
  calc (algebraMap ℂ A μ - a) * P + μ • (1 - P)
      = ((μ • (1 : A)) - a) * P + μ • (1 - P) := by rw [hmap]
    _ = (μ • P - a * P) + (μ • (1 : A) - μ • P) := by
          rw [sub_mul, smul_mul_assoc, one_mul, smul_sub]
    _ = μ • (1 : A) - a * P := by abel
    _ = algebraMap ℂ A μ - a * P := by rw [hmap]

/-- A corner element commuting with `a` also commutes with
`algebraMap ℂ A μ - a`. -/
theorem commute_corner_algebraMap_sub (P : A) (hPa : Commute a P)
    (μ : ℂ) : Commute P (algebraMap ℂ A μ - a) :=
  Commute.sub_right (Commute.symm (Algebra.commutes μ P))
    (Commute.symm hPa)

/-! ## The corner products with the candidate inverse -/

/-- First corner product: with `u` a unit of the corner's
`B`-part, `B * P + μ • (1 - P)` times the candidate inverse
`↑u⁻¹ * P + μ⁻¹ • (1 - P)` is `1`. The four corner terms are
`P`, `0`, `0`, `1 - P`, closing by idempotence, both
orthogonality products, and commutation of the corners with
`u` and `↑u⁻¹`. -/
theorem corner_mul_candidate_eq_one (P : A) (u : Aˣ)
    (hPP : P * P = P)
    (hPQ : P * (1 - P) = 0)
    (hQP : (1 - P) * P = 0)
    (hPu : Commute P (u : A))
    {μ : ℂ} (hμ : μ ≠ 0) :
    ((u : A) * P + μ • (1 - P)) * ((↑u⁻¹ : A) * P + μ⁻¹ • (1 - P))
      = 1 := by
  have hQu : Commute (1 - P) (u : A) := (Commute.one_left _).sub_left hPu
  have hPui : Commute P (↑u⁻¹ : A) := hPu.units_inv_right
  have hQui : Commute (1 - P) (↑u⁻¹ : A) := hQu.units_inv_right
  have hQQ : (1 - P) * (1 - P) = 1 - P := by
    rw [mul_sub, mul_one, hQP, sub_zero]
  have tPP : ((u : A) * P) * ((↑u⁻¹ : A) * P) = P := by
    calc ((u : A) * P) * ((↑u⁻¹ : A) * P)
        = (u : A) * (P * ((↑u⁻¹ : A) * P)) := mul_assoc _ _ _
      _ = (u : A) * ((P * (↑u⁻¹ : A)) * P) :=
          congrArg _ (mul_assoc _ _ _).symm
      _ = (u : A) * (((↑u⁻¹ : A) * P) * P) :=
          congrArg _ (congrArg (· * P) hPui.eq)
      _ = ((u : A) * ((↑u⁻¹ : A) * P)) * P := (mul_assoc _ _ _).symm
      _ = (((u : A) * (↑u⁻¹ : A)) * P) * P :=
          congrArg (· * P) (mul_assoc _ _ _).symm
      _ = P := by rw [Units.mul_inv, one_mul, hPP]
  have tPQ : ((u : A) * P) * (μ⁻¹ • (1 - P)) = 0 := by
    calc ((u : A) * P) * (μ⁻¹ • (1 - P))
        = μ⁻¹ • (((u : A) * P) * (1 - P)) := mul_smul_comm _ _ _
      _ = μ⁻¹ • ((u : A) * (P * (1 - P))) := congrArg _ (mul_assoc _ _ _)
      _ = 0 := by rw [hPQ, mul_zero, smul_zero]
  have tQP : (μ • (1 - P)) * ((↑u⁻¹ : A) * P) = 0 := by
    calc (μ • (1 - P)) * ((↑u⁻¹ : A) * P)
        = μ • ((1 - P) * ((↑u⁻¹ : A) * P)) := smul_mul_assoc _ _ _
      _ = μ • (((1 - P) * (↑u⁻¹ : A)) * P) :=
          congrArg _ (mul_assoc _ _ _).symm
      _ = μ • (((↑u⁻¹ : A) * (1 - P)) * P) :=
          congrArg _ (congrArg (· * P) hQui.eq)
      _ = μ • ((↑u⁻¹ : A) * ((1 - P) * P)) :=
          congrArg _ (mul_assoc _ _ _)
      _ = 0 := by rw [hQP, mul_zero, smul_zero]
  have tQQ : (μ • (1 - P)) * (μ⁻¹ • (1 - P)) = 1 - P := by
    calc (μ • (1 - P)) * (μ⁻¹ • (1 - P))
        = μ • ((1 - P) * (μ⁻¹ • (1 - P))) := smul_mul_assoc _ _ _
      _ = μ • (μ⁻¹ • ((1 - P) * (1 - P))) :=
          congrArg _ (mul_smul_comm _ _ _)
      _ = (μ * μ⁻¹) • ((1 - P) * (1 - P)) := smul_smul _ _ _
      _ = 1 - P := by rw [mul_inv_cancel₀ hμ, one_smul, hQQ]
  calc ((u : A) * P + μ • (1 - P)) * ((↑u⁻¹ : A) * P + μ⁻¹ • (1 - P))
      = (((u : A) * P) * ((↑u⁻¹ : A) * P)
          + ((u : A) * P) * (μ⁻¹ • (1 - P)))
        + ((μ • (1 - P)) * ((↑u⁻¹ : A) * P)
          + (μ • (1 - P)) * (μ⁻¹ • (1 - P))) := by
          rw [add_mul, mul_add, mul_add]
    _ = (P + 0) + (0 + (1 - P)) := by rw [tPP, tPQ, tQP, tQQ]
    _ = 1 := by rw [add_zero, zero_add, add_sub_cancel]

/-- Second corner product: the candidate inverse times
`B * P + μ • (1 - P)` is `1`, by the mirrored corner
computation. -/
theorem candidate_mul_corner_eq_one (P : A) (u : Aˣ)
    (hPP : P * P = P)
    (hPQ : P * (1 - P) = 0)
    (hQP : (1 - P) * P = 0)
    (hPu : Commute P (u : A))
    {μ : ℂ} (hμ : μ ≠ 0) :
    ((↑u⁻¹ : A) * P + μ⁻¹ • (1 - P)) * ((u : A) * P + μ • (1 - P))
      = 1 := by
  have hQu : Commute (1 - P) (u : A) := (Commute.one_left _).sub_left hPu
  have hPui : Commute P (↑u⁻¹ : A) := hPu.units_inv_right
  have hQui : Commute (1 - P) (↑u⁻¹ : A) := hQu.units_inv_right
  have hQQ : (1 - P) * (1 - P) = 1 - P := by
    rw [mul_sub, mul_one, hQP, sub_zero]
  have sPP : ((↑u⁻¹ : A) * P) * ((u : A) * P) = P := by
    calc ((↑u⁻¹ : A) * P) * ((u : A) * P)
        = (↑u⁻¹ : A) * (P * ((u : A) * P)) := mul_assoc _ _ _
      _ = (↑u⁻¹ : A) * ((P * (u : A)) * P) :=
          congrArg _ (mul_assoc _ _ _).symm
      _ = (↑u⁻¹ : A) * (((u : A) * P) * P) :=
          congrArg _ (congrArg (· * P) hPu.eq)
      _ = ((↑u⁻¹ : A) * ((u : A) * P)) * P := (mul_assoc _ _ _).symm
      _ = (((↑u⁻¹ : A) * (u : A)) * P) * P :=
          congrArg (· * P) (mul_assoc _ _ _).symm
      _ = P := by rw [Units.inv_mul, one_mul, hPP]
  have sPQ : ((↑u⁻¹ : A) * P) * (μ • (1 - P)) = 0 := by
    calc ((↑u⁻¹ : A) * P) * (μ • (1 - P))
        = μ • (((↑u⁻¹ : A) * P) * (1 - P)) := mul_smul_comm _ _ _
      _ = μ • ((↑u⁻¹ : A) * (P * (1 - P))) :=
          congrArg _ (mul_assoc _ _ _)
      _ = 0 := by rw [hPQ, mul_zero, smul_zero]
  have sQP : (μ⁻¹ • (1 - P)) * ((u : A) * P) = 0 := by
    calc (μ⁻¹ • (1 - P)) * ((u : A) * P)
        = μ⁻¹ • ((1 - P) * ((u : A) * P)) := smul_mul_assoc _ _ _
      _ = μ⁻¹ • (((1 - P) * (u : A)) * P) :=
          congrArg _ (mul_assoc _ _ _).symm
      _ = μ⁻¹ • (((u : A) * (1 - P)) * P) :=
          congrArg _ (congrArg (· * P) hQu.eq)
      _ = μ⁻¹ • ((u : A) * ((1 - P) * P)) :=
          congrArg _ (mul_assoc _ _ _)
      _ = 0 := by rw [hQP, mul_zero, smul_zero]
  have sQQ : (μ⁻¹ • (1 - P)) * (μ • (1 - P)) = 1 - P := by
    calc (μ⁻¹ • (1 - P)) * (μ • (1 - P))
        = μ⁻¹ • ((1 - P) * (μ • (1 - P))) := smul_mul_assoc _ _ _
      _ = μ⁻¹ • (μ • ((1 - P) * (1 - P))) :=
          congrArg _ (mul_smul_comm _ _ _)
      _ = (μ⁻¹ * μ) • ((1 - P) * (1 - P)) := smul_smul _ _ _
      _ = 1 - P := by rw [inv_mul_cancel₀ hμ, one_smul, hQQ]
  calc ((↑u⁻¹ : A) * P + μ⁻¹ • (1 - P)) * ((u : A) * P + μ • (1 - P))
      = (((↑u⁻¹ : A) * P) * ((u : A) * P)
          + ((↑u⁻¹ : A) * P) * (μ • (1 - P)))
        + ((μ⁻¹ • (1 - P)) * ((u : A) * P)
          + (μ⁻¹ • (1 - P)) * (μ • (1 - P))) := by
          rw [add_mul, mul_add, mul_add]
    _ = (P + 0) + (0 + (1 - P)) := by rw [sPP, sPQ, sQP, sQQ]
    _ = 1 := by rw [add_zero, zero_add, add_sub_cancel]

/-! ## The IsUnit deliverable at a general corner -/

/-- If `μ ≠ 0` lies in the resolvent set of `a`, then
`algebraMap ℂ A μ - a * P` is a unit for every corner element
`P` with the projection algebra (idempotence, both
orthogonality products, commutation with `a`). -/
theorem isUnit_algebraMap_sub_mul_corner (P : A)
    (hPP : P * P = P)
    (hPQ : P * (1 - P) = 0)
    (hQP : (1 - P) * P = 0)
    (hPa : Commute a P)
    {μ : ℂ} (hμ : μ ≠ 0)
    (hB : IsUnit (algebraMap ℂ A μ - a)) :
    IsUnit (algebraMap ℂ A μ - a * P) := by
  obtain ⟨u, hu⟩ := hB
  have hPu : Commute P (u : A) := by
    rw [hu]
    exact commute_corner_algebraMap_sub a P hPa μ
  have hXY : (algebraMap ℂ A μ - a * P)
      * ((↑u⁻¹ : A) * P + μ⁻¹ • (1 - P)) = 1 := by
    rw [← sub_mul_add_smul_compl_eq a P μ, ← hu]
    exact corner_mul_candidate_eq_one P u hPP hPQ hQP hPu hμ
  have hYX : ((↑u⁻¹ : A) * P + μ⁻¹ • (1 - P))
      * (algebraMap ℂ A μ - a * P) = 1 := by
    rw [← sub_mul_add_smul_compl_eq a P μ, ← hu]
    exact candidate_mul_corner_eq_one P u hPP hPQ hQP hPu hμ
  exact ⟨⟨algebraMap ℂ A μ - a * P,
    (↑u⁻¹ : A) * P + μ⁻¹ • (1 - P), hXY, hYX⟩, rfl⟩

/-! ## The IsUnit deliverable at the two Riesz corners -/

/-- At the Riesz corner `P = rieszProj a lam r`, under the
isolation hypotheses exactly as landed for
`rieszProj_mul_self`. -/
theorem isUnit_algebraMap_sub_mul_rieszProj {lam : ℂ} {R : ℝ}
    (hR : specIsolatedWithin a lam R) {r : ℝ}
    (hr : 0 < r) (hrR : r ≤ R)
    {μ : ℂ} (hμ : μ ≠ 0)
    (hB : IsUnit (algebraMap ℂ A μ - a)) :
    IsUnit (algebraMap ℂ A μ - a * rieszProj a lam r) :=
  isUnit_algebraMap_sub_mul_corner a (rieszProj a lam r)
    (rieszProj_mul_self a hR hr hrR)
    (rieszProj_mul_rieszComplProj a hR hr hrR)
    (rieszComplProj_mul_rieszProj a hR hr hrR)
    (commute_a_rieszProj a lam r) hμ hB

/-- At the complementary corner `1 - P = rieszComplProj a lam r`,
under the same isolation hypotheses. Here `1 - (1 - P) = P` is
proved by `abel`, not by definitional unfolding. -/
theorem isUnit_algebraMap_sub_mul_rieszComplProj {lam : ℂ} {R : ℝ}
    (hR : specIsolatedWithin a lam R) {r : ℝ}
    (hr : 0 < r) (hrR : r ≤ R)
    {μ : ℂ} (hμ : μ ≠ 0)
    (hB : IsUnit (algebraMap ℂ A μ - a)) :
    IsUnit (algebraMap ℂ A μ - a * rieszComplProj a lam r) := by
  have h1Q : (1 : A) - rieszComplProj a lam r = rieszProj a lam r := by
    show (1 : A) - (1 - rieszProj a lam r) = rieszProj a lam r
    abel
  have hPQ : rieszComplProj a lam r
      * (1 - rieszComplProj a lam r) = 0 := by
    rw [h1Q]
    exact rieszComplProj_mul_rieszProj a hR hr hrR
  have hQP : (1 - rieszComplProj a lam r)
      * rieszComplProj a lam r = 0 := by
    rw [h1Q]
    exact rieszProj_mul_rieszComplProj a hR hr hrR
  exact isUnit_algebraMap_sub_mul_corner a (rieszComplProj a lam r)
    (rieszComplProj_mul_self a hR hr hrR) hPQ hQP
    (commute_a_rieszComplProj a lam r) hμ hB

/-! ## Headlines: the two inclusions of 8B-4(i) -/

/-- **Headline (8B-4(i), first inclusion):**
`spectrum ℂ (a * rieszProj a lam r) ⊆ {0} ∪ spectrum ℂ a`,
under the isolation hypotheses exactly as landed for the
projection algebra. Inclusions only - no equality, no sharp
`{0, lam}` form (that is part (ii), gated on 8B-3). -/
theorem spectrum_mul_rieszProj_subset {lam : ℂ} {R : ℝ}
    (hR : specIsolatedWithin a lam R) {r : ℝ}
    (hr : 0 < r) (hrR : r ≤ R) :
    spectrum ℂ (a * rieszProj a lam r) ⊆ {0} ∪ spectrum ℂ a := by
  intro μ hμspec
  by_cases ha : μ ∈ spectrum ℂ a
  · exact Set.mem_union_right _ ha
  · by_cases h0 : μ = 0
    · exact Set.mem_union_left _ (Set.mem_singleton_iff.mpr h0)
    · exfalso
      have hB : IsUnit (algebraMap ℂ A μ - a) :=
        spectrum.notMem_iff.mp ha
      have hU : IsUnit (algebraMap ℂ A μ - a * rieszProj a lam r) :=
        isUnit_algebraMap_sub_mul_rieszProj a hR hr hrR h0 hB
      exact spectrum.mem_iff.mp hμspec hU

/-- **Headline (8B-4(i), second inclusion):**
`spectrum ℂ (a * rieszComplProj a lam r) ⊆ {0} ∪ spectrum ℂ a`,
under the same isolation hypotheses. Inclusions only. -/
theorem spectrum_mul_rieszComplProj_subset {lam : ℂ} {R : ℝ}
    (hR : specIsolatedWithin a lam R) {r : ℝ}
    (hr : 0 < r) (hrR : r ≤ R) :
    spectrum ℂ (a * rieszComplProj a lam r) ⊆ {0} ∪ spectrum ℂ a := by
  intro μ hμspec
  by_cases ha : μ ∈ spectrum ℂ a
  · exact Set.mem_union_right _ ha
  · by_cases h0 : μ = 0
    · exact Set.mem_union_left _ (Set.mem_singleton_iff.mpr h0)
    · exfalso
      have hB : IsUnit (algebraMap ℂ A μ - a) :=
        spectrum.notMem_iff.mp ha
      have hU : IsUnit
          (algebraMap ℂ A μ - a * rieszComplProj a lam r) :=
        isUnit_algebraMap_sub_mul_rieszComplProj a hR hr hrR h0 hB
      exact spectrum.mem_iff.mp hμspec hU

end

end ThetLogos
