/-
# THE HONEST BATTERY — the zero-point kill, instantiated at the
# slice seat

Commissioned 2026-10-25 (Jeff: "Build the honest battery
package"). This module welds the zero-point extraction KILL
(`whitepaper/zero-point-extraction-kill-2026-10-25.md`) to the
FG-2 Hamiltonian (`LatticeSliceFriedrichs`, `LatticeSliceCfc`,
`LatticeSliceResolvent`): a battery whose datasheet is
machine-checked, including the line that its empty state is
provably empty.

## The datasheet, on its face

* The battery stores only what is put in. Its charge is the
  FG-2b form energy `E(x) = ⟪Ĥx, x⟫.re` of a domain state —
  nonnegative by the form's positivity (T1), and zero at the
  vacuum (T1).
* The vacuum stores nothing extractable. Every generator the
  corpus owns fixes the vacuum line (T2: `T̂_c Ω = Ω`,
  `R_λ Ω = λ⁻¹ • Ω`, `cfc f T̂_c Ω = f(1) • Ω`), and for ANY
  domain-preserving continuous linear equivalence `U` of the
  carrier, the work extracted from the vacuum in one cycle
  satisfies `W(U) = E(Ω) − E(UΩ) ≤ 0` (T3). This is the kill
  of the whitepaper, instantiated: the floor cannot be mined,
  now with the floor exhibited as a machine-checked ground
  state of a machine-checked Hamiltonian.
* The smallest stored quantum is priced only CONDITIONALLY
  (T4): under the spectral correspondence at `Ω⊥` — the
  pairing-level content that FG-2c-4's identification
  `exp(−Ĥ) = T̂_c` would supply through a spectral theorem
  for `Ĥ` that the pinned Mathlib does not carry — a unit
  state orthogonal to the vacuum stores at least
  `−log (1 − δ)`, where `δ` is the Q12 gap
  (`GapBoundU1`). The correspondence is a NAMED HYPOTHESIS
  of T4, not a fact; the step from it to the bound is proved
  in full. `exp(−Ĥ) = T̂_c` is NOT asserted anywhere here.

## Fences

No device is claimed. No energy source is claimed: the
extraction bound T3 is a non-positivity statement, the exact
opposite of a power source. No positivity beyond landed
labels; no semigroup identification; Stage 1b-B untouched;
Items 3/4 untouched. NO CLAIM; Clay parts closed: 0.
-/

import ThetLogos.LatticeSliceResolvent
import ThetLogos.LatticeSliceCfc
import ThetLogos.LatticeSliceCircle
import ThetLogos.LatticeVacuumSimple

namespace ThetLogos

open MeasureTheory Finset
open scoped Matrix ENNReal NNReal InnerProduct Polynomial

section SliceBattery

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ))
  {N : ℕ} [NeZero N]

/-! ## D0. The vacuum as a carrier element, a domain element,
and the battery's energy -/

/-- **The battery's empty state**: the completed vacuum as an
element of the FG-2b carrier `H' = sliceFormClosure`. -/
noncomputable def sliceBatteryVacuum (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (hd : 0 < d) :
    ↥(sliceFormClosure μG ρ hN2 hρcont hN β hpos) :=
  ⟨sliceOmegaCompleted μG ρ hN2 hρcont hN β hpos hd,
    sliceFormDomain_le_closure μG ρ hN2 hρcont hN β hpos
      (sliceHamC_vacuum_mem_domain μG ρ hN2 hρcont hN β hpos
        hd)⟩

/-- The vacuum's ambient vector is the completed vacuum. -/
theorem sliceBatteryVacuum_val (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (hd : 0 < d) :
    (sliceBatteryVacuum μG ρ hN2 hρcont hN β hpos hd).1
      = sliceOmegaCompleted μG ρ hN2 hρcont hN β hpos hd :=
  rfl

/-- **The vacuum lies in the operator domain** `D(Ĥ)`: it is
the resolvent's value at itself (FG-2b's
`sliceFriedrichsResolvent_vacuum`). -/
theorem sliceBatteryVacuum_mem_domain (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (hd : 0 < d) :
    sliceBatteryVacuum μG ρ hN2 hρcont hN β hpos hd
      ∈ sliceHamOperatorDomain μG ρ hN2 hρcont hN β hpos :=
  ⟨sliceBatteryVacuum μG ρ hN2 hρcont hN β hpos hd,
    sliceFriedrichsResolvent_vacuum μG ρ hN2 hρcont hN β
      hpos hd⟩

/-- **The empty state as a domain element.** -/
noncomputable def sliceBatteryVacuumDom (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (hd : 0 < d) :
    ↥(sliceHamOperatorDomain μG ρ hN2 hρcont hN β hpos) :=
  ⟨sliceBatteryVacuum μG ρ hN2 hρcont hN β hpos hd,
    sliceBatteryVacuum_mem_domain μG ρ hN2 hρcont hN β hpos
      hd⟩

/-- The domain vacuum's carrier value is the vacuum. -/
theorem sliceBatteryVacuumDom_val (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (hd : 0 < d) :
    (sliceBatteryVacuumDom μG ρ hN2 hρcont hN β hpos hd).1
      = sliceBatteryVacuum μG ρ hN2 hρcont hN β hpos hd :=
  rfl

/-- **`Ĥ` kills the vacuum, pointed form**: the Friedrichs
Hamiltonian at the battery's empty state is zero — the
vacuum is a ground state of energy exactly `0`. -/
theorem sliceBattery_ham_vacuum (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (hd : 0 < d) :
    sliceHamOperator μG ρ hN2 hρcont hN β hpos
        (sliceBatteryVacuumDom μG ρ hN2 hρcont hN β hpos hd)
      = 0 := by
  have h := sliceHamOperator_eq μG ρ hN2 hρcont hN β hpos
    (sliceBatteryVacuumDom μG ρ hN2 hρcont hN β hpos hd)
    (sliceBatteryVacuum μG ρ hN2 hρcont hN β hpos hd)
    (by
      rw [sliceBatteryVacuumDom_val μG ρ hN2 hρcont hN β
        hpos hd]
      exact sliceFriedrichsResolvent_vacuum μG ρ hN2 hρcont
        hN β hpos hd)
  rw [h, sliceBatteryVacuumDom_val μG ρ hN2 hρcont hN β hpos
    hd]
  exact sub_self _

/-- **D0 — the battery energy** of a domain state: the real
part of the Hamiltonian pairing, `E(x) = ⟪Ĥx, x⟫.re`. The
stored charge of a (unit) state is this number; the vacuum
floor sits at `0` (T1). -/
noncomputable def sliceBatteryEnergy (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (x : ↥(sliceHamOperatorDomain μG ρ hN2 hρcont hN β
      hpos)) : ℝ :=
  (inner ℂ (sliceHamOperator μG ρ hN2 hρcont hN β hpos x)
    x.1).re

/-- The battery energy is the FG-2 Hamiltonian form value of
the state's ambient vector (FG-2b's diagonal identity). -/
theorem sliceBatteryEnergy_eq_formVal (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (x : ↥(sliceHamOperatorDomain μG ρ hN2 hρcont hN β
      hpos)) :
    sliceBatteryEnergy μG ρ hN2 hρcont hN β hpos x
      = sliceFormVal μG ρ hN2 hρcont hN β hpos (x.1).1 := by
  unfold sliceBatteryEnergy
  rw [sliceHamOperator_inner_self μG ρ hN2 hρcont hN β hpos
    x, Complex.ofReal_re]

/-! ## T1. The floor -/

/-- **T1 (floor)**: every domain state has nonnegative
battery energy — the charge is the form value, and the form
is nonnegative. -/
theorem sliceBatteryEnergy_nonneg (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (x : ↥(sliceHamOperatorDomain μG ρ hN2 hρcont hN β
      hpos)) :
    0 ≤ sliceBatteryEnergy μG ρ hN2 hρcont hN β hpos x := by
  rw [sliceBatteryEnergy_eq_formVal μG ρ hN2 hρcont hN β
    hpos x]
  exact sliceFormVal_nonneg μG ρ hN2 hρcont hN β hpos _

/-- **T1 (the empty state is empty)**: the vacuum's stored
charge is exactly zero. -/
theorem sliceBatteryEnergy_vacuum (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (hd : 0 < d) :
    sliceBatteryEnergy μG ρ hN2 hρcont hN β hpos
        (sliceBatteryVacuumDom μG ρ hN2 hρcont hN β hpos hd)
      = 0 := by
  unfold sliceBatteryEnergy
  rw [sliceBattery_ham_vacuum μG ρ hN2 hρcont hN β hpos hd]
  simp

/-! ## T2 (first two clauses). The vacuum is a fixed point
of the operating algebra -/

/-- **T2 (transfer)**: the completed transfer operator
fixes the vacuum, `T̂_c Ω = Ω` — the vacuum is an eigenvector
of eigenvalue `1` (Rung 1's package, pointed form, on the
ambient space where `T̂_c` and the `cfc` live). -/
theorem sliceBattery_tc_vacuum (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (hd : 0 < d) :
    sliceTc μG ρ hN2 hρcont hN β hpos
        (sliceOmegaCompleted μG ρ hN2 hρcont hN β hpos hd)
      = sliceOmegaCompleted μG ρ hN2 hρcont hN β hpos hd := by
  rw [sliceTc_apply μG ρ hN2 hρcont hN β hpos]
  exact sliceHatCompletedFun_omega μG ρ hN2 hρcont hN β hpos
    hd

/-- **T2 (resolvent)**: at every weight `λ > 0` the
resolvent scales the vacuum by `λ⁻¹` and nothing else,
`R_λ Ω = λ⁻¹ • Ω` — on the carrier, where `Ĥ` and `R_λ`
live (FG-2c-1's vacuum law, at the battery's empty state). -/
theorem sliceBattery_resolvent_vacuum (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (lam : ℝ)
    (hlam : 0 < lam) (hd : 0 < d) :
    sliceResolventLin μG ρ hN2 hρcont hN β hpos lam hlam
        (sliceBatteryVacuum μG ρ hN2 hρcont hN β hpos hd)
      = ((lam : ℂ))⁻¹
          • sliceBatteryVacuum μG ρ hN2 hρcont hN β hpos
            hd :=
  sliceResolvent_vacuum μG ρ hN2 hρcont hN β hpos lam hlam
    hd

/-! ## T2 (third clause). The `cfc` evaluation at the vacuum

The eigenvector evaluation lemma for the continuous
functional calculus at the eigenvalue `1`: for polynomials
it is the corpus's polynomial agreement plus `T̂_c Ω = Ω`;
for general continuous `f` it follows by Weierstrass
approximation on the spectrum, which lies in `[0, 1]`
(FG-2c-0), with `norm_cfc_le` pricing the operator error by
the uniform error on the spectrum. -/

/-- The real algebra map into the continuous linear maps,
applied to a vector, is the complex scalar multiple. -/
theorem sliceBattery_algebraMap_apply (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (c : ℝ)
    (v : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos) :
    (algebraMap ℝ
        (sliceHilbertSpace μG ρ hN2 hρcont hN β hpos →L[ℂ]
          sliceHilbertSpace μG ρ hN2 hρcont hN β hpos) c) v
      = ((c : ℂ)) • v := by
  have h1 : algebraMap ℝ
        (sliceHilbertSpace μG ρ hN2 hρcont hN β hpos →L[ℂ]
          sliceHilbertSpace μG ρ hN2 hρcont hN β hpos) c
      = algebraMap ℂ
          (sliceHilbertSpace μG ρ hN2 hρcont hN β hpos
            →L[ℂ] sliceHilbertSpace μG ρ hN2 hρcont hN β
              hpos) (c : ℂ) := by
    rw [IsScalarTower.algebraMap_eq ℝ ℂ _]
    simp [RingHom.comp_apply, Complex.coe_algebraMap]
  rw [h1, Algebra.algebraMap_eq_smul_one,
    ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.one_apply]

/-- Every power of the transfer operator fixes the vacuum. -/
theorem sliceBattery_tc_pow_vacuum (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (hd : 0 < d)
    (n : ℕ) :
    ((sliceTc μG ρ hN2 hρcont hN β hpos) ^ n)
        (sliceOmegaCompleted μG ρ hN2 hρcont hN β hpos hd)
      = sliceOmegaCompleted μG ρ hN2 hρcont hN β hpos hd := by
  induction n with
  | zero =>
      rw [pow_zero, ContinuousLinearMap.one_apply]
  | succ n ih =>
      rw [pow_succ, ContinuousLinearMap.mul_apply,
        sliceBattery_tc_vacuum μG ρ hN2 hρcont hN β hpos hd,
        ih]

/-- **Polynomial evaluation at the vacuum**: for a real
polynomial `p`, `cfc` of the polynomial function, applied
to the vacuum, evaluates the polynomial at the eigenvalue
`1`. -/
theorem sliceBattery_cfc_polynomial_vacuum (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (hd : 0 < d)
    (p : ℝ[X]) :
    (cfc (fun μ : ℝ => p.eval μ)
        (sliceTc μG ρ hN2 hρcont hN β hpos))
        (sliceOmegaCompleted μG ρ hN2 hρcont hN β hpos hd)
      = (((p.eval 1 : ℝ) : ℂ))
          • sliceOmegaCompleted μG ρ hN2 hρcont hN β hpos
            hd := by
  induction p using Polynomial.induction_on with
  | C c =>
      have hfun : (fun μ : ℝ => (Polynomial.C c).eval μ)
          = (fun _ : ℝ => c) := by
        funext μ
        simp
      rw [hfun, sliceCfc_const μG ρ hN2 hρcont hN β hpos c,
        Polynomial.eval_C]
      exact sliceBattery_algebraMap_apply μG ρ hN2 hρcont
        hN β hpos c _
  | add p q hp hq =>
      have hfun : (fun μ : ℝ => (p + q).eval μ)
          = (fun μ => p.eval μ + q.eval μ) := by
        funext μ
        simp only [Polynomial.eval_add]
      rw [hfun,
        cfc_add _ _ _ (Polynomial.continuous p).continuousOn
          (Polynomial.continuous q).continuousOn,
        ContinuousLinearMap.add_apply, hp, hq,
        Polynomial.eval_add]
      push_cast
      rw [add_smul]
  | monomial n c _ih =>
      have hfun : (fun μ : ℝ => (Polynomial.C c
              * Polynomial.X ^ (n + 1)).eval μ)
          = (fun μ => c * μ ^ (n + 1)) := by
        funext μ
        simp [Polynomial.eval_mul, Polynomial.eval_C,
          Polynomial.eval_pow, Polynomial.eval_X]
      have hsmul : (c • ((sliceTc μG ρ hN2 hρcont hN β
              hpos) ^ (n + 1)))
            (sliceOmegaCompleted μG ρ hN2 hρcont hN β hpos
              hd)
          = ((c : ℂ))
              • sliceOmegaCompleted μG ρ hN2 hρcont hN β
                hpos hd := by
        rw [Algebra.smul_def, ContinuousLinearMap.mul_apply,
          sliceBattery_tc_pow_vacuum μG ρ hN2 hρcont hN β
            hpos hd (n + 1),
          sliceBattery_algebraMap_apply μG ρ hN2 hρcont hN
            β hpos c _]
      rw [hfun,
        cfc_const_mul c (fun μ : ℝ => μ ^ (n + 1)) _
          (continuous_pow _).continuousOn,
        sliceCfc_pow μG ρ hN2 hρcont hN β hpos (n + 1),
        hsmul]
      simp [Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_pow, Polynomial.eval_X]

/-- **T2 (functional calculus) — the eigenvector evaluation
lemma.** For every continuous real function `f`, the
functional calculus of the transfer operator at the vacuum
evaluates `f` at the eigenvalue `1`:
`cfc f T̂_c Ω = f(1) • Ω`. The vacuum line is therefore
invariant under the whole continuous functional calculus
of `T̂_c`. -/
theorem sliceBattery_cfc_vacuum (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (hd : 0 < d)
    (f : ℝ → ℝ) (hf : Continuous f) :
    (cfc f (sliceTc μG ρ hN2 hρcont hN β hpos))
        (sliceOmegaCompleted μG ρ hN2 hρcont hN β hpos hd)
      = ((f 1 : ℂ))
          • sliceOmegaCompleted μG ρ hN2 hρcont hN β hpos
            hd := by
  apply eq_of_forall_dist_le
  intro ε hε
  obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn
    0 1 f hf.continuousOn (ε / 2) (half_pos hε)
  have hspec : spectrum ℝ (sliceTc μG ρ hN2 hρcont hN β
        hpos) ⊆ Set.Icc 0 1 :=
    sliceTc_spectrum_subset μG ρ hN2 hρcont hN β hpos
  have hsub : cfc f (sliceTc μG ρ hN2 hρcont hN β hpos)
        - cfc (fun μ => p.eval μ)
          (sliceTc μG ρ hN2 hρcont hN β hpos)
      = cfc (fun μ => f μ - p.eval μ)
          (sliceTc μG ρ hN2 hρcont hN β hpos) := by
    have h := cfc_sub f (fun μ => p.eval μ)
      (sliceTc μG ρ hN2 hρcont hN β hpos) hf.continuousOn
      (Polynomial.continuous p).continuousOn
    rw [← h]
  have hdiff : dist ((cfc f (sliceTc μG ρ hN2 hρcont hN β
          hpos)) (sliceOmegaCompleted μG ρ hN2 hρcont hN β
            hpos hd))
        ((((p.eval 1 : ℝ) : ℂ))
          • sliceOmegaCompleted μG ρ hN2 hρcont hN β hpos
            hd) ≤ ε / 2 := by
    calc dist ((cfc f (sliceTc μG ρ hN2 hρcont hN β hpos))
            (sliceOmegaCompleted μG ρ hN2 hρcont hN β hpos
              hd))
          ((((p.eval 1 : ℝ) : ℂ))
            • sliceOmegaCompleted μG ρ hN2 hρcont hN β hpos
              hd)
        = ‖(cfc f (sliceTc μG ρ hN2 hρcont hN β hpos))
              (sliceOmegaCompleted μG ρ hN2 hρcont hN β
                hpos hd)
            - (cfc (fun μ => p.eval μ)
                (sliceTc μG ρ hN2 hρcont hN β hpos))
              (sliceOmegaCompleted μG ρ hN2 hρcont hN β
                hpos hd)‖ := by
          rw [dist_eq_norm,
            sliceBattery_cfc_polynomial_vacuum μG ρ hN2
              hρcont hN β hpos hd p]
      _ = ‖(cfc f (sliceTc μG ρ hN2 hρcont hN β hpos)
              - cfc (fun μ => p.eval μ)
                (sliceTc μG ρ hN2 hρcont hN β hpos))
            (sliceOmegaCompleted μG ρ hN2 hρcont hN β hpos
              hd)‖ := by
          rw [ContinuousLinearMap.sub_apply]
      _ = ‖(cfc (fun μ => f μ - p.eval μ)
              (sliceTc μG ρ hN2 hρcont hN β hpos))
            (sliceOmegaCompleted μG ρ hN2 hρcont hN β hpos
              hd)‖ := by
          rw [hsub]
      _ ≤ ‖cfc (fun μ => f μ - p.eval μ)
              (sliceTc μG ρ hN2 hρcont hN β hpos)‖
            * ‖sliceOmegaCompleted μG ρ hN2 hρcont hN β
                hpos hd‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ = ‖cfc (fun μ => f μ - p.eval μ)
              (sliceTc μG ρ hN2 hρcont hN β hpos)‖ := by
          rw [sliceOmegaCompleted_norm μG ρ hN2 hρcont hN β
            hpos hd, mul_one]
      _ ≤ ε / 2 := by
          apply norm_cfc_le (le_of_lt (half_pos hε))
          intro μ hμ
          rw [Real.norm_eq_abs, abs_sub_comm]
          exact le_of_lt (hp μ (hspec hμ))
  have hscal : dist ((((p.eval 1 : ℝ) : ℂ))
          • sliceOmegaCompleted μG ρ hN2 hρcont hN β hpos
            hd)
        (((f 1 : ℂ))
          • sliceOmegaCompleted μG ρ hN2 hρcont hN β hpos
            hd) ≤ ε / 2 := by
    rw [dist_eq_norm, ← sub_smul,
      show (((p.eval 1 : ℝ) : ℂ) - (f 1 : ℂ))
          = ((p.eval 1 - f 1 : ℝ) : ℂ) by push_cast; ring,
      norm_smul, sliceOmegaCompleted_norm μG ρ hN2 hρcont
        hN β hpos hd, mul_one, Complex.norm_real,
      Real.norm_eq_abs]
    exact le_of_lt (hp 1 (by norm_num))
  calc dist ((cfc f (sliceTc μG ρ hN2 hρcont hN β hpos))
          (sliceOmegaCompleted μG ρ hN2 hρcont hN β hpos
            hd))
        (((f 1 : ℂ))
          • sliceOmegaCompleted μG ρ hN2 hρcont hN β hpos
            hd)
      ≤ dist ((cfc f (sliceTc μG ρ hN2 hρcont hN β hpos))
            (sliceOmegaCompleted μG ρ hN2 hρcont hN β hpos
              hd))
          ((((p.eval 1 : ℝ) : ℂ))
            • sliceOmegaCompleted μG ρ hN2 hρcont hN β hpos
              hd)
        + dist ((((p.eval 1 : ℝ) : ℂ))
            • sliceOmegaCompleted μG ρ hN2 hρcont hN β hpos
              hd)
          (((f 1 : ℂ))
            • sliceOmegaCompleted μG ρ hN2 hρcont hN β hpos
              hd) :=
        dist_triangle _ _ _
    _ ≤ ε / 2 + ε / 2 := add_le_add hdiff hscal
    _ = ε := add_halves ε

/-- **T2 — THE VACUUM IS A FIXED POINT OF THE OPERATING
ALGEBRA** (the package): the transfer operator fixes the
vacuum; every resolvent `R_λ` (`λ > 0`) scales it by
`λ⁻¹`; and the whole continuous functional calculus of
`T̂_c` evaluates at the eigenvalue `1` on it. No operation
in the operating algebra moves the empty state off its own
line — in particular, none of them charges the battery
from its empty state. -/
def sliceBatteryVacuumFixed (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (hd : 0 < d) :
    Prop :=
  (sliceTc μG ρ hN2 hρcont hN β hpos
      (sliceOmegaCompleted μG ρ hN2 hρcont hN β hpos hd)
    = sliceOmegaCompleted μG ρ hN2 hρcont hN β hpos hd)
  ∧ (∀ lam : ℝ, ∀ hlam : 0 < lam,
      sliceResolventLin μG ρ hN2 hρcont hN β hpos lam hlam
          (sliceBatteryVacuum μG ρ hN2 hρcont hN β hpos hd)
        = ((lam : ℂ))⁻¹
            • sliceBatteryVacuum μG ρ hN2 hρcont hN β hpos
              hd)
  ∧ (∀ f : ℝ → ℝ, Continuous f →
      (cfc f (sliceTc μG ρ hN2 hρcont hN β hpos))
          (sliceOmegaCompleted μG ρ hN2 hρcont hN β hpos
            hd)
        = ((f 1 : ℂ))
            • sliceOmegaCompleted μG ρ hN2 hρcont hN β hpos
              hd)

/-- **T2 stands**: the fixed-point package holds at every
seat where the engine stands. -/
theorem sliceBattery_vacuum_fixed (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (hd : 0 < d) :
    sliceBatteryVacuumFixed μG ρ hN2 hρcont hN β hpos hd :=
  ⟨sliceBattery_tc_vacuum μG ρ hN2 hρcont hN β hpos hd,
    fun lam hlam => sliceBattery_resolvent_vacuum μG ρ hN2
      hρcont hN β hpos lam hlam hd,
    fun f hf => sliceBattery_cfc_vacuum μG ρ hN2 hρcont hN
      β hpos hd f hf⟩

/-! ## T3. Passivity: the kill, instantiated -/

/-- **The extracted work of one cycle**: a continuous linear
equivalence `U` of the carrier that preserves the operator
domain acts on the empty state; the extracted work is the
energy drop `E(Ω) − E(UΩ)`. (The domain element for `UΩ` is
built from the preservation hypothesis.) -/
noncomputable def sliceBatteryExtracted (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (hd : 0 < d)
    (U : ↥(sliceFormClosure μG ρ hN2 hρcont hN β hpos)
      ≃L[ℂ] ↥(sliceFormClosure μG ρ hN2 hρcont hN β hpos))
    (hU : ∀ y : ↥(sliceFormClosure μG ρ hN2 hρcont hN β
        hpos),
      y ∈ sliceHamOperatorDomain μG ρ hN2 hρcont hN β hpos
        → U y ∈ sliceHamOperatorDomain μG ρ hN2 hρcont hN β
          hpos) : ℝ :=
  (sliceBatteryEnergy μG ρ hN2 hρcont hN β hpos
      (sliceBatteryVacuumDom μG ρ hN2 hρcont hN β hpos
        hd))
    - sliceBatteryEnergy μG ρ hN2 hρcont hN β hpos
        ⟨U (sliceBatteryVacuum μG ρ hN2 hρcont hN β hpos
            hd),
          hU _ (sliceBatteryVacuum_mem_domain μG ρ hN2
            hρcont hN β hpos hd)⟩

/-- **T3 — PASSIVITY AT THE SEAT (the kill, instantiated).**
For every domain-preserving continuous linear equivalence
`U` of the carrier, the work extracted from the vacuum in
one cycle is non-positive: `W(U) ≤ 0`. The vacuum is a
ground state (T1: `E ≥ 0`, `E(Ω) = 0`), so a cycle can only
charge the battery or break even — never discharge the
empty state. This is the variational line of
`whitepaper/zero-point-extraction-kill-2026-10-25.md` with
the floor exhibited inside the corpus. -/
theorem sliceBattery_extracted_nonpos (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (hd : 0 < d)
    (U : ↥(sliceFormClosure μG ρ hN2 hρcont hN β hpos)
      ≃L[ℂ] ↥(sliceFormClosure μG ρ hN2 hρcont hN β hpos))
    (hU : ∀ y : ↥(sliceFormClosure μG ρ hN2 hρcont hN β
        hpos),
      y ∈ sliceHamOperatorDomain μG ρ hN2 hρcont hN β hpos
        → U y ∈ sliceHamOperatorDomain μG ρ hN2 hρcont hN β
          hpos) :
    sliceBatteryExtracted μG ρ hN2 hρcont hN β hpos hd U
        hU ≤ 0 := by
  unfold sliceBatteryExtracted
  rw [sliceBatteryEnergy_vacuum μG ρ hN2 hρcont hN β hpos
    hd]
  have h := sliceBatteryEnergy_nonneg μG ρ hN2 hρcont hN β
    hpos ⟨U (sliceBatteryVacuum μG ρ hN2 hρcont hN β hpos
        hd),
      hU _ (sliceBatteryVacuum_mem_domain μG ρ hN2 hρcont
        hN β hpos hd)⟩
  linarith

/-! ## The package -/

/-- **THE HONEST BATTERY PACKAGE** (a `Prop`): the
datasheet of §D0–T3 at a general seat — (i) the floor:
every domain state's charge is nonnegative; (ii) the
empty state is empty: the vacuum's charge is `0`; (iii)
the vacuum is a fixed point of the operating algebra
(T2); (iv) passivity: no domain-preserving cycle extracts
work from the vacuum (T3). -/
def sliceBatteryPackage (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (hd : 0 < d) :
    Prop :=
  (∀ x : ↥(sliceHamOperatorDomain μG ρ hN2 hρcont hN β
      hpos),
    0 ≤ sliceBatteryEnergy μG ρ hN2 hρcont hN β hpos x)
  ∧ sliceBatteryEnergy μG ρ hN2 hρcont hN β hpos
      (sliceBatteryVacuumDom μG ρ hN2 hρcont hN β hpos hd)
    = 0
  ∧ sliceBatteryVacuumFixed μG ρ hN2 hρcont hN β hpos hd
  ∧ (∀ (U : ↥(sliceFormClosure μG ρ hN2 hρcont hN β hpos)
        ≃L[ℂ] ↥(sliceFormClosure μG ρ hN2 hρcont hN β
          hpos))
      (hU : ∀ y : ↥(sliceFormClosure μG ρ hN2 hρcont hN β
          hpos),
        y ∈ sliceHamOperatorDomain μG ρ hN2 hρcont hN β
            hpos
          → U y ∈ sliceHamOperatorDomain μG ρ hN2 hρcont
              hN β hpos),
    sliceBatteryExtracted μG ρ hN2 hρcont hN β hpos hd U
        hU ≤ 0)

/-- **The package stands** at every seat where the engine
stands. -/
theorem sliceBattery_package (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (hd : 0 < d) :
    sliceBatteryPackage μG ρ hN2 hρcont hN β hpos hd :=
  ⟨fun x => sliceBatteryEnergy_nonneg μG ρ hN2 hρcont hN β
      hpos x,
    sliceBatteryEnergy_vacuum μG ρ hN2 hρcont hN β hpos hd,
    sliceBattery_vacuum_fixed μG ρ hN2 hρcont hN β hpos hd,
    fun U hU => sliceBattery_extracted_nonpos μG ρ hN2
      hρcont hN β hpos hd U hU⟩

end SliceBattery

/-! ## T4. The smallest stored quantum — conditional, at
the U(1) seat

The price of the smallest stored quantum is the one clause
whose proof would run through a spectral theorem for the
UNBOUNDED `Ĥ` — an object the pinned Mathlib does not
carry (no unbounded functional calculus, no spectral
measure for `Ĥ`; this absence is exactly FG-2c's gate).
FG-2c-4's identification `exp(−Ĥ) = T̂_c` (hypothesis
`hID`, NOT asserted anywhere in this module) classically
implies, via that spectral theorem and the seat
identifications, the pairing-level correspondence stated
below: Jensen for the spectral measure of a domain state
gives `exp(−E x) ≤ ⟪x, T̂_c x⟫.re`, and the Q12 gap —
transferred from `transferOp`'s spectrum to `T̂_c`'s
pairings on `Ω⊥` through vacuum simplicity — gives
`⟪x, T̂_c x⟫.re ≤ 1 − δ`. Per the commission, T4 is
delivered with that correspondence as its ONE named
hypothesis; the step from the correspondence to the bound
is elementary and is proved in full. The gap `δ` itself is
Q12's, carried by `GapBoundU1` (landed at `β > 0` modulo
the weld's carried data, `gapBoundU1_of_weld`). -/

/-- **The spectral correspondence at `Ω⊥`** — the named
hypothesis of T4: for every unit domain state `x` of the
circle seat's Hamiltonian with `x ⊥ Ω`, the transfer
pairing of `x` is trapped between the Jensen bound
`exp(−E x)` below and the gap bound `1 − δ` above. -/
def SliceSpectralCorrespondence (β : ℝ) {N : ℕ} [NeZero N]
    (hN2 : 2 ≤ N) (hN : Even N) (δ : ℝ)
    (hpos : SliceHPosOne (haarProb Circle) circleRep hN2
      circleRep_continuous β) : Prop :=
  ∀ x : ↥(sliceHamOperatorDomain (haarProb Circle)
        circleRep hN2 circleRep_continuous hN β hpos),
    ‖x.1‖ = 1
    → inner ℂ x.1 (sliceBatteryVacuum (haarProb Circle)
          circleRep hN2 circleRep_continuous hN β hpos
            zero_lt_one) = 0
    → Real.exp (- sliceBatteryEnergy (haarProb Circle)
          circleRep hN2 circleRep_continuous hN β hpos x)
        ≤ (inner ℂ (x.1).1 (sliceTc (haarProb Circle)
            circleRep hN2 circleRep_continuous hN β hpos
              (x.1).1)).re
      ∧ (inner ℂ (x.1).1 (sliceTc (haarProb Circle)
            circleRep hN2 circleRep_continuous hN β hpos
              (x.1).1)).re
        ≤ 1 - δ

/-- **T4 — THE SMALLEST STORED QUANTUM (conditional).**
Under the spectral correspondence at `Ω⊥`, every unit
domain state of the circle seat orthogonal to the vacuum
stores at least `−log (1 − δ)`, where `δ ∈ (0, 1)` is a
Q12 gap bound (`GapBoundU1`). Charged states orthogonal
to the vacuum cannot be arbitrarily cheap: the gap of the
transfer operator is the floor price of one stored
quantum. -/
theorem sliceBattery_smallest_quantum (β : ℝ) {N : ℕ}
    [NeZero N] (hN2 : 2 ≤ N) (hN : Even N)
    (hpos : SliceHPosOne (haarProb Circle) circleRep hN2
      circleRep_continuous β)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hgap : GapBoundU1 β hN2 δ)
    (hcorr : SliceSpectralCorrespondence β hN2 hN δ hpos)
    (x : ↥(sliceHamOperatorDomain (haarProb Circle)
        circleRep hN2 circleRep_continuous hN β hpos))
    (hx : ‖x.1‖ = 1)
    (horth : inner ℂ x.1 (sliceBatteryVacuum
        (haarProb Circle) circleRep hN2 circleRep_continuous
          hN β hpos zero_lt_one) = 0) :
    -Real.log (1 - δ)
      ≤ sliceBatteryEnergy (haarProb Circle) circleRep hN2
          circleRep_continuous hN β hpos x := by
  obtain ⟨hJ, hP⟩ := hcorr x hx horth
  have hexp : 0 < Real.exp (- sliceBatteryEnergy
      (haarProb Circle) circleRep hN2 circleRep_continuous
        hN β hpos x) := Real.exp_pos _
  have hle : Real.exp (- sliceBatteryEnergy (haarProb Circle)
        circleRep hN2 circleRep_continuous hN β hpos x)
      ≤ 1 - δ := le_trans hJ hP
  have hlog := Real.log_le_log hexp hle
  rw [Real.log_exp] at hlog
  linarith

/-- The price in T4 is a positive price: for `δ ∈ (0, 1)`,
`−log (1 − δ) > 0`. -/
theorem sliceBattery_smallest_quantum_pos (δ : ℝ)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    0 < -Real.log (1 - δ) := by
  have h1 : 0 < 1 - δ := by linarith
  have h2 : 1 - δ < 1 := by linarith
  have h := Real.log_neg h1 h2
  linarith

/-- **The gap data exists at the seat** (provenance of
T4's `δ`): at every `β > 0` and even `N ≥ 2`, under
exactly the weld's carried data (the two-slice density
hypothesis `HDen` and a Hilbert basis), some `δ ∈ (0, 1)`
is a Q12 gap bound. -/
theorem sliceBattery_gap_exists (β : ℝ) (hβ : 0 < β)
    {N : ℕ} [NeZero N] (hN2 : 2 ≤ N) (hN : Even N)
    (hHDen : HDen (haarProb Circle) circleRep β hN2
      circleRep_continuous zero_lt_one)
    {ι : Type*} [Countable ι]
    (b : HilbertBasis ι ℂ (osSpace (N := N)
      (haarProb Circle) circleRep β)) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ GapBoundU1 β hN2 δ := by
  obtain ⟨δ, hδ, hgap⟩ := gapBoundU1_of_weld hβ hN2 hN
    hHDen b
  refine ⟨min δ (1 / 2), lt_min hδ (by norm_num),
    lt_of_le_of_lt (min_le_right _ _) (by norm_num), ?_⟩
  exact gapBoundU1_of_le β hN2 (min_le_left _ _) hgap

/-- **T4 at the seat, with `SliceHPosOne` discharged**:
at every `β ≥ 0` the circle seat's positivity hypothesis
is free (S2-3, `sliceHPosOne_circle`), so T4's only
remaining inputs are the gap bound and the named
correspondence. -/
theorem sliceBattery_smallest_quantum_seat (β : ℝ)
    (hβ : 0 ≤ β) {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    (hN : Even N) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hgap : GapBoundU1 β hN2 δ)
    (hcorr : SliceSpectralCorrespondence β hN2 hN δ
      (sliceHPosOne_circle hN2 hN β hβ))
    (x : ↥(sliceHamOperatorDomain (haarProb Circle)
        circleRep hN2 circleRep_continuous hN β
          (sliceHPosOne_circle hN2 hN β hβ)))
    (hx : ‖x.1‖ = 1)
    (horth : inner ℂ x.1 (sliceBatteryVacuum
        (haarProb Circle) circleRep hN2 circleRep_continuous
          hN β (sliceHPosOne_circle hN2 hN β hβ)
            zero_lt_one) = 0) :
    -Real.log (1 - δ)
      ≤ sliceBatteryEnergy (haarProb Circle) circleRep hN2
          circleRep_continuous hN β
            (sliceHPosOne_circle hN2 hN β hβ) x :=
  sliceBattery_smallest_quantum β hN2 hN
    (sliceHPosOne_circle hN2 hN β hβ) δ hδ0 hδ1 hgap hcorr
    x hx horth

end ThetLogos
