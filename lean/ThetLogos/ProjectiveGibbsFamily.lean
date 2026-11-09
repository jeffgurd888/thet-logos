/-
# MQ3-2: the corpus family as a projective family, with its limit measure

Rung MQ3-2 of the M-Q3 continuum ladder
(`m-q3-scope-2026-11-08.md` §4; route context §2(b)). Lane STATUS:
`STATUS.md` at the worktree root — the design (§2 there) was frozen
before this content, and the obstruction computation (§3 there) is
part of this rung's record.

## What is built

The corpus's finite-volume Gibbs seats (`LatticeGauge` Stage 0 /
`LatticeCorrelations` §1: configurations `Config Λ G = (Λ × Fin 4) → G`,
Wilson action from `plaquetteDensity`, Gibbs measure
`gibbsMeasure σ μG ρ β = Z⁻¹ • (configMeasure μG).withDensity
(exp (−S_β))`, a probability measure at every real `β`) are assembled
into a projective system over the infinite lattice:

* sites `SiteZ := Fin 4 → ℤ` (ℤ⁴), links `LinkZ := SiteZ × Fin 4`
  (countable), constant factor `G` — the corpus's standing seat data
  `(G, μG, ρ, d)` under exactly the hypotheses `LatticeCorrelations`
  §1 consumes, plus `PolishSpace G` (MQ3-1's requirement);
* for a finite window `J : Finset LinkZ`, the **window action**
  `windowAction ρ β J U = β · Σ_{p ∈ windowPlaquettes J}
  plaquetteDensity`-formula evaluated at the plaquette `p` of the
  configuration `U` extended by `1` off `J`, summed over the
  plaquettes *fully contained* in `J` — the corpus Wilson action
  restricted to the plaquettes a finite volume fully contains;
* the **window Gibbs family** `windowGibbs μG ρ β J`, the exact
  analogue of `gibbsMeasure` with `configMeasure` in its finite-window
  form `Measure.pi (fun _ : J ↦ μG)`. Each seat is a probability
  measure at every real `β` (`isProbabilityMeasure_windowGibbs`).

## Verdict shape — PARTIAL, pre-registered in STATUS §3

Projectivity under restriction (`Finset.restrict₂`, the pin's bonding
map) is **false at general `β ≠ 0`** for this naive window family:
tracing out a link shared by two plaquettes leaves a nonconstant
boundary weight (`2·cosh(β(u+v))` on the traced seat pair of STATUS
§3, a T2 hand computation) that no window Gibbs measure at the same
`(β, ρ)` reproduces. Marginal consistency at `β ≠ 0` is the
DLR/specification property, which is not in the tree. Accordingly:

* **(2b/2c) at `β = 0` — FULL, unconditional.** The action carries the
  prefactor `β`, so at `β = 0` every window seat is the product Haar
  measure — the corpus's own Gibbs measure at the free point
  (`windowGibbs_zero`), an infinite non-Dirac family over all finite
  windows of ℤ⁴ links. Product families are projective
  (`isProjectiveMeasureFamily_windowGibbs_zero`, via the pin's
  `MeasureTheory.isProjectiveMeasureFamily_pi`), and MQ3-1 gives the
  limit: `exists_isProjectiveLimit_windowGibbs_zero`, a probability
  measure on the full configuration space `LinkZ → G` whose every
  finite-window marginal is the window Gibbs seat at `β = 0`.
* **(2c) at general `β` — conditional.** `WindowGibbsProjective
  μG ρ β` is the projectivity of the window family *named as a Prop*;
  `exists_isProjectiveLimit_windowGibbs` proves the limit exists
  under exactly that hypothesis, never silently assumed.
  **K-MQ3-BOND is recorded as fired for the interacting naive family**
  (STATUS §3); it does not fire at `β = 0`.

NO CLAIM. This is scaffolding (scope §2(b)): the limit constructed
here is a thermodynamic-style limit over window seats, with no proved
tie to `ScalingLimitOfLattice`'s seats; it is not the M-Q3 event
(MQ3-6) and moves no dial. Dials 0/4; Dial 3 = 0.
-/

import ThetLogos.LatticeCorrelations
import ThetLogos.KolmogorovExtension
import Mathlib.Probability.ProductMeasure

namespace ThetLogos

open MeasureTheory Finset
open scoped Matrix ENNReal NNReal

/-! ## §1. The infinite lattice and its windows -/

/-- Sites of the infinite lattice: `ℤ⁴`. -/
abbrev SiteZ : Type := Fin 4 → ℤ

/-- Links of the infinite lattice: a site and a direction — the
corpus's `Config Λ G = (Λ × Fin 4) → G` link set at `Λ = SiteZ`. -/
abbrev LinkZ : Type := SiteZ × Fin 4

/-- Translation by `+1` in coordinate `μ` on `ℤ⁴` — the infinite-volume
form of the corpus's shifts `σ : Fin 4 → Equiv.Perm Λ`. -/
def shiftSite (μ : Fin 4) (x : SiteZ) : SiteZ :=
  Function.update x μ (x μ + 1)

section Seats

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  [PolishSpace G]
variable (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
variable {d : ℕ} (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ))

/-- The four links of the plaquette at `x` in directions `μ ν`, in the
corpus's `plaquette` order. -/
def windowPlaquetteLinks (x : SiteZ) (μ ν : Fin 4) : Finset LinkZ :=
  {(x, μ), (shiftSite μ x, ν), (shiftSite ν x, μ), (x, ν)}

/-- The plaquette positions `(x, μ, ν)`, `ν > μ`, fully contained in
the window `J`: all four links lie in `J`. Finiteness: a contained
plaquette has its first link in `J`, so `x ∈ J.image Prod.fst`. -/
def windowPlaquettes (J : Finset LinkZ) : Finset (SiteZ × Fin 4 × Fin 4) :=
  ((J.image Prod.fst) ×ˢ (Finset.univ ×ˢ Finset.univ)).filter
    (fun p => p.2.2 ∈ Finset.Ioi p.2.1 ∧ windowPlaquetteLinks p.1 p.2.1 p.2.2 ⊆ J)

/-- A window configuration extended by the identity off the window:
the finite-volume configuration read as a full configuration. -/
def extConfig (J : Finset LinkZ) (U : ∀ j : J, G) : Config SiteZ G :=
  fun ℓ => if h : ℓ ∈ J then U ⟨ℓ, h⟩ else 1

theorem measurable_extConfig (J : Finset LinkZ) :
    Measurable (extConfig J : (∀ j : J, G) → Config SiteZ G) := by
  refine measurable_pi_iff.mpr fun ℓ => ?_
  by_cases hℓ : ℓ ∈ J
  · have hfun : (fun U : ∀ j : J, G => extConfig J U ℓ)
        = fun U => U ⟨ℓ, hℓ⟩ := by
      funext U
      exact dif_pos hℓ
    rw [hfun]
    exact measurable_pi_apply _
  · have hfun : (fun U : ∀ j : J, G => extConfig J U ℓ)
        = fun _ => (1 : G) := by
      funext U
      exact dif_neg hℓ
    rw [hfun]
    exact measurable_const

/-- The plaquette product, in the corpus's `plaquette` formula with
the infinite shifts `shiftSite`: `U(x,μ) * U(σ μ x, ν) * (U(σ ν x,
μ))⁻¹ * (U(x,ν))⁻¹`. -/
def windowPlaquette (U : Config SiteZ G) (x : SiteZ) (μ ν : Fin 4) : G :=
  U (x, μ) * U (shiftSite μ x, ν) * (U (shiftSite ν x, μ))⁻¹ * (U (x, ν))⁻¹

/-- The Wilson density of one plaquette, in the corpus's
`plaquetteDensity` formula: `1 − (1/d) Re tr ρ(U_p)`. -/
noncomputable def windowPlaquetteDensity (U : Config SiteZ G)
    (x : SiteZ) (μ ν : Fin 4) : ℝ :=
  1 - (Matrix.trace (repMatrix ρ (windowPlaquette U x μ ν))).re / (d : ℝ)

/-- Each window plaquette density lies in `[0, 2]` (for `0 < d`) —
the corpus's `plaquetteDensity_mem_Icc` argument, re-proved here
because that lemma's section carries `[Fintype Λ]`, which `SiteZ`
cannot. -/
theorem windowPlaquetteDensity_mem_Icc (hd : 0 < d) (U : Config SiteZ G)
    (x : SiteZ) (μ ν : Fin 4) :
    windowPlaquetteDensity ρ U x μ ν ∈ Set.Icc (0 : ℝ) 2 := by
  have hmem : repMatrix ρ (windowPlaquette U x μ ν)
      ∈ Matrix.unitaryGroup (Fin d) ℂ := repMatrix_mem ρ _
  have h1 := re_trace_le_of_mem_unitaryGroup hmem
  have h2 := neg_re_trace_le_of_mem_unitaryGroup hmem
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  constructor
  · unfold windowPlaquetteDensity
    rw [sub_nonneg, div_le_one hdR]
    exact h1
  · unfold windowPlaquetteDensity
    rw [sub_le_iff_le_add]
    have hge : (Matrix.trace (repMatrix ρ (windowPlaquette U x μ ν))).re
        / (d : ℝ) ≥ -1 := by
      rw [ge_iff_le, le_div_iff₀ hdR]
      calc (-1 : ℝ) * d = -(d : ℝ) := by ring
        _ ≤ (Matrix.trace (repMatrix ρ (windowPlaquette U x μ ν))).re := h2
    linarith

/-- The window plaquette map is measurable in the window
configuration — the corpus's `measurable_plaquette` pattern
(its section carries `[Fintype Λ]`; re-proved here). -/
theorem measurable_windowPlaquette (J : Finset LinkZ) (x : SiteZ)
    (μ ν : Fin 4) :
    Measurable fun U : ∀ j : J, G =>
      windowPlaquette (extConfig J U) x μ ν := by
  have hE := measurable_extConfig (G := G) J
  unfold windowPlaquette
  exact ((((measurable_pi_apply (x, μ)).comp hE).mul
    ((measurable_pi_apply (shiftSite μ x, ν)).comp hE)).mul
    ((measurable_pi_apply (shiftSite ν x, μ)).comp hE).inv).mul
    ((measurable_pi_apply (x, ν)).comp hE).inv

/-! ## §2. The window Gibbs family -/

/-- The window Wilson action at coupling `β`: `β` times the sum of
the corpus plaquette densities over the plaquettes fully contained
in `J`, evaluated at the configuration extended by `1` off `J`. -/
noncomputable def windowAction (β : ℝ) (J : Finset LinkZ)
    (U : ∀ j : J, G) : ℝ :=
  β * ∑ p ∈ windowPlaquettes J,
    windowPlaquetteDensity ρ (extConfig J U) p.1 p.2.1 p.2.2

theorem measurable_windowAction
    (hρcont : Continuous fun g : G => repMatrix ρ g) (β : ℝ)
    (J : Finset LinkZ) :
    Measurable (windowAction ρ β J) := by
  have htr : ∀ p : SiteZ × Fin 4 × Fin 4,
      Measurable fun U : ∀ j : J, G =>
        (Matrix.trace (repMatrix ρ
          (windowPlaquette (extConfig J U) p.1 p.2.1 p.2.2))).re := by
    intro p
    refine Complex.measurable_re.comp ?_
    refine Finset.measurable_sum _ fun i _ => ?_
    exact (measurable_pi_apply i).comp ((measurable_pi_apply i).comp
      (hρcont.measurable.comp (measurable_windowPlaquette J p.1 p.2.1 p.2.2)))
  unfold windowAction
  refine Measurable.const_mul ?_ β
  refine Finset.measurable_sum _ fun p _ => ?_
  unfold windowPlaquetteDensity
  exact Measurable.sub measurable_const ((htr p).div_const _)

theorem abs_windowAction_le (hd : 0 < d) (β : ℝ) (J : Finset LinkZ)
    (U : ∀ j : J, G) :
    |windowAction ρ β J U| ≤ |β| * (2 * (windowPlaquettes J).card) := by
  unfold windowAction
  rw [abs_mul]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg β)
  calc |∑ p ∈ windowPlaquettes J,
        windowPlaquetteDensity ρ (extConfig J U) p.1 p.2.1 p.2.2|
      ≤ ∑ p ∈ windowPlaquettes J,
        |windowPlaquetteDensity ρ (extConfig J U) p.1 p.2.1 p.2.2| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _p ∈ windowPlaquettes J, (2 : ℝ) := by
      refine Finset.sum_le_sum fun p _ => ?_
      have hIcc := windowPlaquetteDensity_mem_Icc ρ hd (extConfig J U)
        p.1 p.2.1 p.2.2
      exact abs_le.mpr ⟨by linarith [hIcc.1], hIcc.2⟩
    _ = 2 * (windowPlaquettes J).card := by
      rw [Finset.sum_const, nsmul_eq_mul]
      ring

/-- The Gibbs density of the window seat, as an `ℝ≥0`-valued
function: `U ↦ exp (−S_β U)`. -/
noncomputable def windowDensity (β : ℝ) (J : Finset LinkZ)
    (U : ∀ j : J, G) : ℝ≥0 :=
  ⟨Real.exp (- windowAction ρ β J U), Real.exp_nonneg _⟩

theorem windowDensity_coe (β : ℝ) (J : Finset LinkZ) (U : ∀ j : J, G) :
    (windowDensity ρ β J U : ℝ≥0∞)
      = ENNReal.ofReal (Real.exp (- windowAction ρ β J U)) :=
  (ENNReal.ofReal_eq_coe_nnreal (Real.exp_nonneg _)).symm

/-- The window partition function: `Z = ∫ U, exp (−S_β U)` against
the product Haar measure of the window. -/
noncomputable def windowPartition (β : ℝ) (J : Finset LinkZ) : ℝ :=
  ∫ U, Real.exp (- windowAction ρ β J U) ∂(Measure.pi fun _ : J => μG)

theorem integrable_exp_neg_windowAction
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hd : 0 < d)
    (β : ℝ) (J : Finset LinkZ) :
    Integrable (fun U => Real.exp (- windowAction ρ β J U))
      (Measure.pi fun _ : J => μG) := by
  refine Integrable.of_bound
    ((Real.measurable_exp.comp
      (measurable_windowAction ρ hρcont β J).neg).aestronglyMeasurable)
    (Real.exp (|β| * (2 * (windowPlaquettes J).card)))
    (ae_of_all _ fun U => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.mpr
    (le_trans (neg_le_abs _) (abs_windowAction_le ρ hd β J U))

theorem windowPartition_pos
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hd : 0 < d)
    (β : ℝ) (J : Finset LinkZ) :
    0 < windowPartition μG ρ β J := by
  have hbound : ∀ U : ∀ j : J, G,
      Real.exp (- (|β| * (2 * (windowPlaquettes J).card)))
        ≤ Real.exp (- windowAction ρ β J U) :=
    fun U => Real.exp_le_exp.mpr (by
      have h := abs_windowAction_le ρ hd β J U
      have h3 := le_abs_self (windowAction ρ β J U)
      linarith)
  unfold windowPartition
  calc (0 : ℝ) < Real.exp (- (|β| * (2 * (windowPlaquettes J).card))) :=
      Real.exp_pos _
    _ = ∫ _, Real.exp (- (|β| * (2 * (windowPlaquettes J).card)))
        ∂(Measure.pi fun _ : J => μG) := by
      simp
    _ ≤ ∫ U, Real.exp (- windowAction ρ β J U)
        ∂(Measure.pi fun _ : J => μG) :=
      integral_mono_ae (integrable_const _)
        (integrable_exp_neg_windowAction μG ρ hρcont hd β J)
        (ae_of_all _ hbound)

/-- **The window Gibbs measure** at coupling `β`: the normalized
density `exp (−S_β) / Z` against the product Haar measure of the
window — the corpus's `gibbsMeasure` construction at the window
seat. The family `J ↦ windowGibbs μG ρ β J` is the corpus family of
this rung. -/
noncomputable def windowGibbs (β : ℝ) (J : Finset LinkZ) :
    Measure (∀ j : J, G) :=
  (ENNReal.ofReal (windowPartition μG ρ β J))⁻¹ •
    (Measure.pi fun _ : J => μG).withDensity
      (fun U => (windowDensity ρ β J U : ℝ≥0∞))

theorem withDensity_windowGibbs_univ
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hd : 0 < d)
    (β : ℝ) (J : Finset LinkZ) :
    (Measure.pi fun _ : J => μG).withDensity
        (fun U => (windowDensity ρ β J U : ℝ≥0∞)) Set.univ
      = ENNReal.ofReal (windowPartition μG ρ β J) := by
  rw [MeasureTheory.withDensity_apply _ MeasurableSet.univ,
    setLIntegral_univ]
  have hcongr : (fun U => (windowDensity ρ β J U : ℝ≥0∞))
      = fun U => ENNReal.ofReal (Real.exp (- windowAction ρ β J U)) :=
    funext fun U => windowDensity_coe ρ β J U
  rw [hcongr, ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal
    (integrable_exp_neg_windowAction μG ρ hρcont hd β J)
    (ae_of_all _ fun U => Real.exp_nonneg _)]
  rfl

/-- **Each window Gibbs seat is a probability measure**, for every
real `β` — the window form of the corpus's
`isProbabilityMeasure_gibbsMeasure`. -/
theorem isProbabilityMeasure_windowGibbs
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hd : 0 < d)
    (β : ℝ) (J : Finset LinkZ) :
    IsProbabilityMeasure (windowGibbs μG ρ β J) := by
  have hZ := windowPartition_pos μG ρ hρcont hd β J
  refine ⟨?_⟩
  show ((ENNReal.ofReal (windowPartition μG ρ β J))⁻¹
      • (Measure.pi fun _ : J => μG).withDensity
          (fun U => (windowDensity ρ β J U : ℝ≥0∞))) Set.univ = 1
  rw [Measure.smul_apply, withDensity_windowGibbs_univ μG ρ hρcont hd β J,
    smul_eq_mul, ENNReal.inv_mul_cancel]
  · exact (ENNReal.ofReal_pos.mpr hZ).ne'
  · exact ENNReal.ofReal_ne_top

/-! ## §3. Projectivity at `β = 0` (FULL) -/

theorem windowAction_zero (J : Finset LinkZ) (U : ∀ j : J, G) :
    windowAction ρ 0 J U = 0 := by
  unfold windowAction
  exact zero_mul _

theorem windowPartition_zero (J : Finset LinkZ) :
    windowPartition μG ρ 0 J = 1 := by
  unfold windowPartition
  have hfun : (fun U : ∀ j : J, G =>
        Real.exp (- windowAction ρ 0 J U)) = fun _ => (1 : ℝ) := by
    funext U
    rw [windowAction_zero ρ J U]
    simp
  rw [hfun]
  simp

/-- **At `β = 0` the window Gibbs seat is the product Haar measure** —
the corpus's Gibbs measure at the free point, in window form. -/
theorem windowGibbs_zero (J : Finset LinkZ) :
    windowGibbs μG ρ 0 J = Measure.pi (fun _ : J => μG) := by
  unfold windowGibbs
  rw [windowPartition_zero μG ρ J, ENNReal.ofReal_one, inv_one]
  have hdens : (fun U : ∀ j : J, G => (windowDensity ρ 0 J U : ℝ≥0∞))
      = 1 := by
    funext U
    show (windowDensity ρ 0 J U : ℝ≥0∞) = 1
    rw [windowDensity_coe ρ 0 J U, windowAction_zero ρ J U]
    simp
  rw [hdens]
  ext s hs
  rw [Measure.smul_apply, smul_eq_mul, one_mul,
    MeasureTheory.withDensity_apply _ hs]
  simp only [Pi.one_apply]
  rw [setLIntegral_one]

/-- **(2b) FULL at `β = 0`:** the corpus window Gibbs family at the
free point is a projective measure family in the pin's sense. -/
theorem isProjectiveMeasureFamily_windowGibbs_zero :
    IsProjectiveMeasureFamily (α := fun _ : LinkZ => G)
      (windowGibbs μG ρ 0) := by
  have h : windowGibbs μG ρ 0
      = fun J : Finset LinkZ => Measure.pi (fun _ : J => μG) :=
    funext fun J => windowGibbs_zero μG ρ J
  rw [h]
  exact MeasureTheory.isProjectiveMeasureFamily_pi (fun _ : LinkZ => μG)

/-! ## §4. The headline: limit measures -/

/-- **The named hypothesis at general `β`** (STATUS §3): the window
Gibbs family at coupling `β` is projective. This is the
DLR/marginal-consistency content the tree does not carry at
`β ≠ 0` — stated as a Prop, never silently assumed. -/
def WindowGibbsProjective (β : ℝ) : Prop :=
  IsProjectiveMeasureFamily (α := fun _ : LinkZ => G)
    (windowGibbs μG ρ β)

/-- **(2c) at general `β`, conditional:** under the named hypothesis
`WindowGibbsProjective`, the corpus window Gibbs family has a
projective limit measure on the full configuration space. -/
theorem exists_isProjectiveLimit_windowGibbs
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hd : 0 < d)
    (β : ℝ) (h : WindowGibbsProjective μG ρ β) :
    ∃ μ : Measure (∀ i : LinkZ, G),
      IsProjectiveLimit μ (windowGibbs μG ρ β) := by
  haveI : ∀ J : Finset LinkZ,
      IsProbabilityMeasure (windowGibbs μG ρ β J) :=
    fun J => isProbabilityMeasure_windowGibbs μG ρ hρcont hd β J
  exact ThetLogos.exists_isProjectiveLimit
    (show IsProjectiveMeasureFamily (α := fun _ : LinkZ => G)
      (windowGibbs μG ρ β) from h)

/-- **(2c) HEADLINE at `β = 0`, unconditional:** a limit probability
measure on the inverse-limit (full) configuration space exists and
is the projective limit of the corpus window Gibbs family at the
free point. -/
theorem exists_isProjectiveLimit_windowGibbs_zero
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hd : 0 < d) :
    ∃ μ : Measure (∀ i : LinkZ, G),
      IsProjectiveLimit μ (windowGibbs μG ρ 0) :=
  exists_isProjectiveLimit_windowGibbs μG ρ hρcont hd 0
    (isProjectiveMeasureFamily_windowGibbs_zero μG ρ)

/-- The `β = 0` limit measure is a probability measure. -/
theorem isProbabilityMeasure_limit_windowGibbs_zero
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hd : 0 < d) :
    ∃ μ : Measure (∀ i : LinkZ, G),
      IsProjectiveLimit μ (windowGibbs μG ρ 0) ∧
        IsProbabilityMeasure μ := by
  obtain ⟨μ, hμ⟩ := exists_isProjectiveLimit_windowGibbs_zero μG ρ hρcont hd
  haveI := isProbabilityMeasure_windowGibbs μG ρ hρcont hd 0 ∅
  refine ⟨μ, hμ, ⟨?_⟩⟩
  rw [hμ.measure_univ_eq (∅ : Finset LinkZ)]
  exact measure_univ

end Seats

end ThetLogos
