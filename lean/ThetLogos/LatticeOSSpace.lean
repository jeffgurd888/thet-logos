import ThetLogos.LatticePositivity
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# ThetLogos.LatticeOSSpace — Pitch 4, Stage 1b-C: the
Osterwalder–Schrader Hilbert space, by the time-slice L² route
(T1, with the OS-positivity identification fenced to 1b-B's open
clause)

HONESTY LEDGER (read before citing):

- Everything proved in this file is **T1 finite-lattice
  mathematics** on Stage 0's concrete torus (`Fin 4 → ZMod N`,
  shifts `torusShift N`), at general `(G, ρ)`, general even `N`,
  consuming Stage 1a's Gibbs measure, Stage 1b-A's reflection
  pack, and Stage 1b-B's OS form.

- *(the route, of record)* The parked-fleet gauntlet
  (`whitepaper/gauntlet-parked-fleet-2026-10-17.md` §1) chose the
  **time-slice L² route** for the OS space and **declined** the
  quotient/completion-of-the-OS-form route. This module follows
  the chosen route: states are L² functions of one time slice's
  spatial links, against the **slice marginal of the Gibbs
  measure**, an honest Mathlib `Lp` space. No null-space
  quotient, no abstract completion machinery.

- *(what stands, unconditionally)* The slice marginal is a
  probability measure at every real `β`; the space
  `osSpace β = Lp ℂ 2 (sliceMeasure β)` is a Hilbert space
  (Mathlib's `Lp` instances); the constant vacuum vector has
  norm `1`; slice observables embed as vectors with the L²
  inner product equal to the slice integral; vacuum expectation
  of a slice observable is its Gibbs expectation. At `β = 0`
  the slice marginal is the product Haar measure on the slice
  links — the gauntlet's "slice Haar measure" is exactly the
  `β = 0` case of the Gibbs marginal. The marginal on the
  reflected slice is the transport of the slice marginal along
  the reflection (no positivity input: 1b-A's Gibbs invariance).

- *(the fence — 1b-B's open clause is NOT spent here)* Stage
  1b-B landed PARTIAL: the OS form stands in full and its
  positivity is proved at `β = 0`, but positivity at general
  `β` is reduced to one open clause — the Gram /
  character-expansion factorization of the Wilson weight
  (Peter–Weyl orthogonality, absent from the pinned Mathlib
  v4.35.0-rc3, priced XL / Mathlib-blocked). Accordingly:
  **no statement in this module identifies the slice L² inner
  product with the OS form, and none needs to** — the L² inner
  product is positive because it is the inner product of an
  `Lp` space over an actual measure. The one place where the
  OS form's positivity would be *spent* (positivity of the OS
  form restricted to slice-supported observables) is stated
  **conditionally**, with the Gram clause as an explicit
  hypothesis (`GramClause`, §5), proved by applying 1b-B's
  criterion verbatim. At `β = 0` the same statement is proved
  unconditionally (§5), by 1b-B's `β = 0` theorem.

- *(finite-lattice discipline)* "Results in this module are
  about a finite lattice at fixed spacing and volume. Nothing
  here is a continuum result; the words 'continuum', 'ℝ⁴', and
  'Poincaré' do not describe anything proved in this module."

- *(gap discipline)* "Any gap statement in this module is a
  lattice statement at the stated $(a, L, \beta)$. No continuum
  mass gap is claimed; a lattice gap transfers to the continuum
  only with uniformity in the spacing along the tuning curve,
  which is not proved here or anywhere in this corpus." (This
  module proves no gap statement of any kind; the transfer
  matrix itself is Stage 1b-D.)

- *(gauge discipline)* "Gauge invariance here is exact
  invariance of a finite lattice action and measure under
  finite gauge transformations. It is not a continuum gauge
  theory, and this module contains no quantized continuum
  gauge field."

- *(standing charter)* "Parts of the official Clay Yang–Mills
  statement closed by this module: 0."

WHAT THIS MODULE IS, AND IS NOT (Stage 1b decomposition of
record — `whitepaper/gauntlet-parked-fleet-2026-10-17.md` §1):
this is campaign **1b-C only**. Stage 1b-A stands whole; Stage
1b-B stands as form + `β = 0` positivity + the Gram criterion,
with general positivity the single open clause (fenced above,
not consumed). This module builds the finite-volume Hilbert
space. No transfer matrix appears (1b-D), and no
reconstruction theorem is stated; **PARTIAL-δ is not
claimed**: δ is A + B with B's positivity proved.

DESIGN CHOICES (disclosed):

- **The slice** is the time-`0` slice's spatial links
  (`sliceLinks`: direction `≠ 0`, base time value `0`). Its
  reflection is the time-`N−1` slice (§2), matching 1b-A's
  between-sites reflection (time coordinate `k ↦ −1−k`).
  `sliceLinks ⊆ posLinks` at even `N`: slice observables are
  strict-positive-half observables (§5 uses this).
- **The measure on the slice is the Gibbs marginal**, not the
  bare slice Haar measure: the marginal remembers the coupling
  to the rest of the lattice, which is what a transfer matrix
  in Stage 1b-D will propagate. At `β = 0` the two coincide
  (proved, §2).
- **`hρcont` and `0 < d`** are carried as explicit hypotheses
  wherever the Gibbs measure's probability property is consumed
  (the corpus pattern of Stages 1a/1b-A/1b-B); the marginal, the
  space, and its inner product need neither.

This module is NOT in the root import list of the library (the
corpus pattern for recent exhibits); it is verified by a
targeted build.
-/

namespace ThetLogos

open MeasureTheory Finset
open scoped Matrix ENNReal NNReal InnerProduct

/-! ## §1. Marginals of configuration measures (general)

For a finset `s` of coordinates, the marginal of a measure on
the full configuration space is its pushforward under the
restriction map. For the product measure, the marginal is the
product over `s` (via Stage 1a's splitting equiv). -/

section Marginal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {G : Type*} [Group G] [MeasurableSpace G]
variable (μG : Measure G) [IsProbabilityMeasure μG]

/-- The restriction of a configuration to the coordinates in
`s`. -/
def restrictConfig (s : Finset ι) : (ι → G) → (↥s → G) :=
  fun U ℓ => U ℓ.1

theorem restrictConfig_apply (s : Finset ι) (U : ι → G)
    (ℓ : ↥s) : restrictConfig s U ℓ = U ℓ.1 :=
  rfl

/-- The restriction map is measurable. -/
theorem measurable_restrictConfig (s : Finset ι) :
    Measurable (restrictConfig (G := G) s) := by
  unfold restrictConfig
  exact Measurable.of_eval fun ℓ => measurable_pi_apply ℓ.1

/-- The restriction map is continuous (Pi topology). -/
theorem continuous_restrictConfig [TopologicalSpace G]
    (s : Finset ι) : Continuous (restrictConfig (G := G) s) := by
  unfold restrictConfig
  exact continuous_pi fun ℓ => continuous_apply ℓ.1

/-- The **marginal** of a configuration measure on the
coordinates in `s`: the pushforward under restriction. -/
noncomputable def marginalMeasure (μ : Measure (ι → G))
    (s : Finset ι) : Measure (↥s → G) :=
  μ.map (restrictConfig s)

/-- A marginal of a probability measure is a probability
measure. -/
instance isProbabilityMeasure_marginalMeasure
    (μ : Measure (ι → G)) [IsProbabilityMeasure μ]
    (s : Finset ι) :
    IsProbabilityMeasure (marginalMeasure μ s) := by
  unfold marginalMeasure
  infer_instance

/-- Integrals against a marginal are integrals of the pulled
back observable against the original measure. -/
theorem integral_marginalMeasure (μ : Measure (ι → G))
    (s : Finset ι) (f : (↥s → G) → ℂ)
    (hf : AEStronglyMeasurable f (marginalMeasure μ s)) :
    ∫ z, f z ∂(marginalMeasure μ s)
      = ∫ U, f (restrictConfig s U) ∂μ :=
  integral_map (measurable_restrictConfig s).aemeasurable hf

/-- **The marginal of the product measure is the product over
`s`** (Stage 1a's splitting equiv, plus the first-factor
marginal of a product measure). -/
theorem marginalMeasure_pi (s : Finset ι) :
    marginalMeasure (Measure.pi fun _ : ι => μG) s
      = Measure.pi fun _ : ↥s => μG := by
  have hrestr : restrictConfig (G := G) s
      = Prod.fst ∘ (splitEquiv (G := G) s) := by
    funext U
    exact (splitEquiv_fst s U).symm
  have hunfold : marginalMeasure (Measure.pi fun _ : ι => μG) s
      = (Measure.pi fun _ : ι => μG).map (restrictConfig s) :=
    rfl
  rw [hunfold, hrestr, ← Measure.map_map
    measurable_fst (splitEquiv s).measurable,
    (measurePreserving_splitEquiv μG s).map_eq,
    Measure.map_fst_prod, measure_univ, one_smul]

end Marginal

/-! ## §2. The Gibbs measure at `β = 0` is the product measure

A pure algebra-of-the-definition fact (the density is `1` and
the partition integral is `1`), stated at Stage 1a's general
`(Λ, σ)`. It is what makes the slice marginal at `β = 0` the
slice product Haar measure. -/

section GibbsZero

variable {Λ : Type*} [Fintype Λ]
variable {G : Type*} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology G]
variable (σ : Fin 4 → Equiv.Perm Λ)
variable (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
variable {d : ℕ} (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ))

/-- At `β = 0` the Gibbs density is identically `1`. -/
theorem gibbsDensity_zero (U : Config Λ G) :
    (gibbsDensity σ ρ 0 U : ℝ≥0∞) = 1 := by
  have hS : wilsonAction σ ρ 0 U = 0 := by simp [wilsonAction]
  rw [gibbsDensity_coe, hS]
  simp

/-- At `β = 0` the partition integral is `1`. -/
theorem gibbsPartition_zero : gibbsPartition σ μG ρ 0 = 1 := by
  have hS : ∀ U : Config Λ G, wilsonAction σ ρ 0 U = 0 :=
    fun U => by simp [wilsonAction]
  have hexp : ∀ U : Config Λ G,
      Real.exp (- wilsonAction σ ρ 0 U) = 1 :=
    fun U => by rw [hS U]; simp
  have h1 : ∫ U, Real.exp (- wilsonAction σ ρ 0 U)
        ∂(configMeasure μG)
      = ∫ _U : Config Λ G, (1 : ℝ) ∂(configMeasure μG) :=
    integral_congr_ae (ae_of_all _ hexp)
  unfold gibbsPartition
  rw [h1, integral_const, Measure.real, measure_univ,
    ENNReal.toReal_one, one_smul]

/-- **The Gibbs measure at `β = 0` is the configuration
(product Haar) measure itself.** -/
theorem gibbsMeasure_zero :
    gibbsMeasure σ μG ρ 0 = configMeasure μG := by
  have hD : (fun U : Config Λ G =>
        (gibbsDensity σ ρ 0 U : ℝ≥0∞)) = 1 :=
    funext fun U => gibbsDensity_zero σ ρ U
  unfold gibbsMeasure
  rw [gibbsPartition_zero σ μG ρ, hD,
    MeasureTheory.withDensity_one, ENNReal.ofReal_one, inv_one,
    one_smul]

end GibbsZero

/-! ## §3. The time slices and their links

The time-`0` slice's spatial links, and the reflected slice at
time `N − 1`. Membership is by base time value and direction. -/

section SliceLinks

variable {N : ℕ} [NeZero N]

/-- The **time slice**: spatial links based at time `0`. -/
def sliceLinks : Finset (Link (Fin 4 → ZMod N)) :=
  Finset.univ.filter (fun ℓ => ℓ.2 ≠ 0 ∧ (ℓ.1 0).val = 0)

theorem mem_sliceLinks {ℓ : Link (Fin 4 → ZMod N)} :
    ℓ ∈ sliceLinks ↔ ℓ.2 ≠ 0 ∧ (ℓ.1 0).val = 0 := by
  simp [sliceLinks]

/-- The **reflected slice**: spatial links based at time
`N − 1` — the image of the slice under 1b-A's between-sites
reflection (time coordinate `k ↦ −1 −k` sends `0 ↦ N − 1`). -/
def reflSliceLinks : Finset (Link (Fin 4 → ZMod N)) :=
  Finset.univ.filter (fun ℓ => ℓ.2 ≠ 0 ∧ (ℓ.1 0).val = N - 1)

theorem mem_reflSliceLinks {ℓ : Link (Fin 4 → ZMod N)} :
    ℓ ∈ reflSliceLinks ↔ ℓ.2 ≠ 0 ∧ (ℓ.1 0).val = N - 1 := by
  simp [reflSliceLinks]

/-- **The slice lies in the strict positive half** (at even
`N`): a based-at-time-`0` spatial link has base time `< N/2`,
and it is not reflection-fixed — its reflection is based at
time `N − 1 ≠ 0`. So slice observables are `posLinks`
observables (consumed in §6). -/
theorem sliceLinks_subset_posLinks (hN : Even N) :
    sliceLinks (N := N) ⊆ posLinks (N := N) := by
  have hNpos : 0 < N := NeZero.pos N
  intro ℓ hℓ
  obtain ⟨x, μ⟩ := ℓ
  rw [mem_sliceLinks] at hℓ
  have hμ : μ ≠ 0 := hℓ.1
  have ht : (x 0).val = 0 := hℓ.2
  rw [mem_posLinks]
  refine ⟨?_, ?_⟩
  · show (x 0).val < N / 2
    obtain ⟨r, hr⟩ := hN
    omega
  · show reflLink (x, μ) ≠ (x, μ)
    intro hfix
    have htime : ((reflLink (x, μ)).1 0).val = (x 0).val := by
      rw [hfix]
    rw [reflLink_fst_zero_val_of_ne hμ, ht] at htime
    obtain ⟨r, hr⟩ := hN
    omega

/-- The link reflection restricts to an equivalence between
the slice and the reflected slice. -/
def sliceReflEquiv :
    ↥(sliceLinks (N := N)) ≃ ↥(reflSliceLinks (N := N)) where
  toFun ℓ := ⟨reflLink ℓ.1, by
    obtain ⟨⟨x, μ⟩, hℓ⟩ := ℓ
    rw [mem_sliceLinks] at hℓ
    have hμ : μ ≠ 0 := hℓ.1
    have ht : (x 0).val = 0 := hℓ.2
    rw [mem_reflSliceLinks]
    refine ⟨?_, ?_⟩
    · show (reflLink (x, μ)).2 ≠ 0
      rw [reflLink_of_ne hμ]
      exact hμ
    · show ((reflLink (x, μ)).1 0).val = N - 1
      rw [reflLink_fst_zero_val_of_ne hμ, ht]
      exact Nat.sub_zero _⟩
  invFun ℓ := ⟨reflLink ℓ.1, by
    obtain ⟨⟨x, μ⟩, hℓ⟩ := ℓ
    rw [mem_reflSliceLinks] at hℓ
    have hμ : μ ≠ 0 := hℓ.1
    have ht : (x 0).val = N - 1 := hℓ.2
    rw [mem_sliceLinks]
    refine ⟨?_, ?_⟩
    · show (reflLink (x, μ)).2 ≠ 0
      rw [reflLink_of_ne hμ]
      exact hμ
    · show ((reflLink (x, μ)).1 0).val = 0
      rw [reflLink_fst_zero_val_of_ne hμ, ht]
      exact Nat.sub_self _⟩
  left_inv ℓ := Subtype.ext (reflLink_involutive ℓ.1)
  right_inv ℓ := Subtype.ext (reflLink_involutive ℓ.1)

theorem sliceReflEquiv_apply (ℓ : ↥(sliceLinks (N := N))) :
    (sliceReflEquiv ℓ).1 = reflLink ℓ.1 :=
  rfl

theorem sliceReflEquiv_symm_apply
    (ℓ : ↥(reflSliceLinks (N := N))) :
    (sliceReflEquiv.symm ℓ).1 = reflLink ℓ.1 :=
  rfl

end SliceLinks

/-! ## §4. The slice marginal of the Gibbs measure

The state space's measure: the Gibbs measure pushed forward
to the slice. Probability at every real `β`; at `β = 0` it is
the product Haar measure on the slice links; the reflected
slice's marginal is its transport along the reflection. -/

section SliceMeasure

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ))
  {N : ℕ} [NeZero N]

/-- Configurations of the time slice: one group element per
slice link. -/
abbrev SliceConfig := ↥(sliceLinks (N := N)) → G

/-- **The slice measure**: the marginal of the Gibbs measure
on the time slice's spatial links. -/
noncomputable def sliceMeasure (β : ℝ) :
    Measure (↥(sliceLinks (N := N)) → G) :=
  marginalMeasure (gibbsMeasure (torusShift N) μG ρ β) sliceLinks

/-- The slice measure is a probability measure, at every real
`β`. -/
theorem isProbabilityMeasure_sliceMeasure
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hd : 0 < d)
    (β : ℝ) :
    IsProbabilityMeasure (sliceMeasure (N := N) μG ρ β) := by
  haveI := isProbabilityMeasure_gibbsMeasure (torusShift N) μG ρ
    hρcont hd β
  unfold sliceMeasure
  infer_instance

/-- Integrals against the slice measure are Gibbs integrals of
the pulled-back observable. -/
theorem integral_sliceMeasure (β : ℝ)
    (f : (↥(sliceLinks (N := N)) → G) → ℂ)
    (hf : AEStronglyMeasurable f (sliceMeasure μG ρ β)) :
    ∫ z, f z ∂(sliceMeasure μG ρ β)
      = ∫ U, f (restrictConfig sliceLinks U)
          ∂(gibbsMeasure (torusShift N) μG ρ β) :=
  integral_marginalMeasure _ _ f hf

/-- The Gibbs expectation of a slice observable (pulled back
to the full configuration space) is its slice integral. -/
theorem gibbsExpect_slice
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hd : 0 < d)
    (β : ℝ) (f : (↥(sliceLinks (N := N)) → G) → ℂ)
    (hf : AEStronglyMeasurable f (sliceMeasure μG ρ β)) :
    gibbsExpect (torusShift N) μG ρ β
        (fun U => f (restrictConfig sliceLinks U))
      = ∫ z, f z ∂(sliceMeasure μG ρ β) :=
  (gibbsExpect_eq_integral (torusShift N) μG ρ hρcont hd β _).trans
    (integral_sliceMeasure μG ρ β f hf).symm

/-- **At `β = 0` the slice measure is the product Haar measure
on the slice links** — the gauntlet's "slice Haar measure" is
the free point of the Gibbs marginal. -/
theorem sliceMeasure_zero :
    sliceMeasure μG ρ 0
      = Measure.pi fun _ : ↥(sliceLinks (N := N)) => μG := by
  unfold sliceMeasure
  rw [gibbsMeasure_zero (torusShift N) μG ρ]
  exact marginalMeasure_pi μG sliceLinks

/-- The transport of slice configurations along the reflection:
read a slice configuration on the reflected slice via the
link equivalence. -/
def sliceTransport (z : ↥(sliceLinks (N := N)) → G) :
    ↥(reflSliceLinks (N := N)) → G :=
  fun ℓ' => z (sliceReflEquiv.symm ℓ')

theorem measurable_sliceTransport :
    Measurable (sliceTransport (G := G) (N := N)) := by
  unfold sliceTransport
  exact Measurable.of_eval fun ℓ' =>
    measurable_pi_apply (sliceReflEquiv.symm ℓ')

/-- Restriction to the reflected slice of a reflected
configuration is the transport of the slice restriction. (For
spatial links the configuration reflection carries no
inversion — 1b-A's `reflConfig_apply_of_ne`.) -/
theorem restrict_reflConfig_eq (U : Config (Fin 4 → ZMod N) G) :
    restrictConfig reflSliceLinks (reflConfig U)
      = sliceTransport (restrictConfig sliceLinks U) := by
  funext ℓ'
  obtain ⟨⟨x, μ⟩, hℓ'⟩ := ℓ'
  have hμ : μ ≠ 0 := (mem_reflSliceLinks.mp hℓ').1
  show reflConfig U (x, μ)
    = sliceTransport (restrictConfig sliceLinks U) ⟨⟨x, μ⟩, hℓ'⟩
  rw [reflConfig_apply_of_ne U hμ]
  show U (reflSite x, μ) = U (reflLink (x, μ))
  rw [reflLink_of_ne hμ]

/-- **The reflected slice's marginal is the transport of the
slice marginal.** No positivity input: this is 1b-A's Gibbs
reflection invariance, marginalized. -/
theorem sliceMeasure_map_transport
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ) :
    (sliceMeasure μG ρ β).map (sliceTransport (G := G) (N := N))
      = marginalMeasure (gibbsMeasure (torusShift N) μG ρ β)
          reflSliceLinks := by
  calc (sliceMeasure μG ρ β).map (sliceTransport (G := G) (N := N))
      = ((gibbsMeasure (torusShift N) μG ρ β).map
          (restrictConfig sliceLinks)).map
          (sliceTransport (G := G) (N := N)) := rfl
    _ = (gibbsMeasure (torusShift N) μG ρ β).map
          (sliceTransport ∘ restrictConfig sliceLinks) :=
        Measure.map_map measurable_sliceTransport
          (measurable_restrictConfig sliceLinks)
    _ = (gibbsMeasure (torusShift N) μG ρ β).map
          (restrictConfig reflSliceLinks ∘ reflConfig) := by
        congr 1
        funext U
        exact (restrict_reflConfig_eq U).symm
    _ = ((gibbsMeasure (torusShift N) μG ρ β).map reflConfig).map
          (restrictConfig reflSliceLinks) :=
        (Measure.map_map (measurable_restrictConfig reflSliceLinks)
          measurable_reflConfig).symm
    _ = (gibbsMeasure (torusShift N) μG ρ β).map
          (restrictConfig reflSliceLinks) := by
        rw [gibbsMeasure_map_reflConfig ρ μG hρcont hN β]
    _ = marginalMeasure (gibbsMeasure (torusShift N) μG ρ β)
          reflSliceLinks := rfl

end SliceMeasure

/-! ## §5. The OS Hilbert space (time-slice `L²` route)

The space is `L²` of the time-slice configuration space with
respect to the slice marginal of the Gibbs measure. It is a
Hilbert space **by construction** (Mathlib's `Lp` instance
package): no quotient by null vectors of a form, no completion
of a pre-Hilbert space, and — critically — no appeal to the OS
form's positivity at general `β`. It therefore stands
UNCONDITIONALLY (given the standing hypotheses `hρcont`, `hd`
where the probability property of the Gibbs measure is
consumed). -/

section OSSpace

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ))
  {N : ℕ} [NeZero N]

/-- **The Osterwalder–Schrader Hilbert space (time-slice `L²`
route):** `L²` of the time-slice configuration space with
respect to the slice marginal of the Gibbs measure at coupling
`β`. -/
noncomputable abbrev osSpace (β : ℝ) :=
  Lp ℂ 2 (sliceMeasure (N := N) μG ρ β)

/-- The OS space is complete (Mathlib's `Lp` instance). -/
theorem osSpace_completeSpace (β : ℝ) :
    CompleteSpace (osSpace (N := N) μG ρ β) := inferInstance

/-- The OS space's inner-product-space structure (Mathlib's
`Lp` instance), as a term. -/
noncomputable def osSpace_innerProductSpace (β : ℝ) :
    InnerProductSpace ℂ (osSpace (N := N) μG ρ β) := inferInstance

/-- The inner product on the OS space is the slice integral of
the pointwise inner product. -/
theorem inner_osSpace (β : ℝ)
    (ψ φ : osSpace (N := N) μG ρ β) :
    inner ℂ ψ φ
      = ∫ z, inner ℂ (ψ z) (φ z)
        ∂(sliceMeasure (N := N) μG ρ β) :=
  MeasureTheory.L2.inner_def ψ φ

/-- **The vacuum:** the constant function `1`, as an element
of the OS space (the slice measure is a probability measure,
so the constant is square-integrable). -/
noncomputable def osVacuum
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hd : 0 < d) (β : ℝ) : osSpace (N := N) μG ρ β := by
  haveI := isProbabilityMeasure_sliceMeasure (N := N) μG ρ hρcont hd β
  exact MeasureTheory.Lp.const 2 _ (1 : ℂ)

/-- The vacuum has norm `1`. -/
theorem norm_osVacuum
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hd : 0 < d) (β : ℝ) :
    ‖osVacuum (N := N) μG ρ hρcont hd β‖ = 1 := by
  haveI := isProbabilityMeasure_sliceMeasure (N := N) μG ρ hρcont hd β
  show ‖MeasureTheory.Lp.const 2 (sliceMeasure (N := N) μG ρ β)
      (1 : ℂ)‖ = 1
  refine (MeasureTheory.Lp.norm_const' (p := 2)
    (μ := sliceMeasure (N := N) μG ρ β) (c := (1 : ℂ))
    (by norm_num) (by norm_num)).trans ?_
  simp [measure_univ]

/-- A slice observable, as a vector of the OS space, from an
`L²` representative. -/
noncomputable def sliceState (β : ℝ)
    (f : SliceConfig → ℂ)
    (hf : MemLp f 2 (sliceMeasure (N := N) μG ρ β)) :
    osSpace (N := N) μG ρ β :=
  hf.toLp f

/-- Bounded measurable slice observables are in `L²`. -/
theorem memLp_of_bounded
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hd : 0 < d) (β : ℝ)
    (f : SliceConfig → ℂ)
    (hfsm : AEStronglyMeasurable f
      (sliceMeasure (N := N) μG ρ β)) (C : ℝ)
    (hC : ∀ z, ‖f z‖ ≤ C) :
    MemLp f 2 (sliceMeasure (N := N) μG ρ β) := by
  haveI := isProbabilityMeasure_sliceMeasure (N := N) μG ρ hρcont hd β
  exact MemLp.of_bound hfsm C (ae_of_all _ hC)

/-- The inner product of two slice states is the slice
integral of the pointwise inner product. -/
theorem inner_sliceState (β : ℝ)
    (f g : SliceConfig → ℂ)
    (hf : MemLp f 2 (sliceMeasure (N := N) μG ρ β))
    (hg : MemLp g 2 (sliceMeasure (N := N) μG ρ β)) :
    inner ℂ (sliceState μG ρ β f hf) (sliceState μG ρ β g hg)
      = ∫ z, inner ℂ (f z) (g z)
        ∂(sliceMeasure (N := N) μG ρ β) := by
  rw [inner_osSpace]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with z hz1 hz2
  unfold sliceState
  rw [hz1, hz2]

/-- **Vacuum expectation:** the inner product of the vacuum
with a slice state is the slice integral of the observable —
the Gibbs expectation of the pulled-back full observable, by
`gibbsExpect_slice`. -/
theorem vacuum_expectation
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hd : 0 < d) (β : ℝ)
    (f : SliceConfig → ℂ)
    (hf : MemLp f 2 (sliceMeasure (N := N) μG ρ β)) :
    inner ℂ (osVacuum (N := N) μG ρ hρcont hd β)
        (sliceState μG ρ β f hf)
      = ∫ z, f z ∂(sliceMeasure (N := N) μG ρ β) := by
  haveI := isProbabilityMeasure_sliceMeasure (N := N) μG ρ hρcont hd β
  have h1 : ⇑(osVacuum (N := N) μG ρ hρcont hd β)
      =ᵐ[sliceMeasure (N := N) μG ρ β] fun _ => (1 : ℂ) := by
    show ⇑(MeasureTheory.Lp.const 2
        (sliceMeasure (N := N) μG ρ β) (1 : ℂ))
      =ᵐ[sliceMeasure (N := N) μG ρ β] fun _ => (1 : ℂ)
    exact MeasureTheory.Lp.coeFn_const 2
      (sliceMeasure (N := N) μG ρ β) (1 : ℂ)
  rw [inner_osSpace]
  apply integral_congr_ae
  filter_upwards [h1, hf.coeFn_toLp] with z hz1 hz2
  unfold sliceState
  rw [hz1, hz2]
  simp [RCLike.inner_apply]

/-- Norm bound for a slice state built from a bounded
observable. -/
theorem norm_sliceState_le
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hd : 0 < d) (β : ℝ)
    (f : SliceConfig → ℂ)
    (hf : MemLp f 2 (sliceMeasure (N := N) μG ρ β))
    (C : ℝ) (hC : ∀ z, ‖f z‖ ≤ C) :
    ‖sliceState μG ρ β f hf‖ ≤ C := by
  haveI := isProbabilityMeasure_sliceMeasure (N := N) μG ρ hρcont hd β
  have hC0 : 0 ≤ C :=
    le_trans (norm_nonneg _) (hC (fun _ => (1 : G)))
  rw [sliceState, Lp.norm_def, eLpNorm_congr_ae hf.coeFn_toLp]
  refine ENNReal.toReal_le_of_le_ofReal hC0 ?_
  refine le_trans (eLpNorm_le_of_ae_bound hf.aestronglyMeasurable
    (ae_of_all _ hC)) ?_
  simp [measure_univ]

end OSSpace

/-! ## §6. Multiplication operators on the OS space

A bounded measurable function `F` on the time slice acts on
the OS space by pointwise multiplication. Boundedness puts `F`
in `L^∞`, and Hölder (`∞ · 2 → 2`) puts the product back in
`L²`. The resulting bounded operators form a commutative
algebra mirroring the pointwise algebra of slice observables,
with adjoints given by pointwise conjugation; a real-valued
observable gives a self-adjoint operator. All of this is
proved from the `L²` construction alone — the OS form plays
no role.

Design note: the `L^∞` membership of `F` is taken as a
hypothesis (`hFinf`), because `MemLp.of_bound` needs a
finite-measure instance that the slice measure only has
conditionally (via `hρcont`, `hd`); the helper
`memLp_top_of_bounded` discharges it under those hypotheses. -/

section Operators

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ))
  {N : ℕ} [NeZero N]

/-- Bounded measurable slice observables are in `L^∞`. -/
theorem memLp_top_of_bounded
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hd : 0 < d) (β : ℝ)
    (F : SliceConfig → ℂ)
    (hFaesm : AEStronglyMeasurable F
      (sliceMeasure (N := N) μG ρ β)) (C : ℝ)
    (hC : ∀ z, ‖F z‖ ≤ C) :
    MemLp F ∞ (sliceMeasure (N := N) μG ρ β) := by
  haveI := isProbabilityMeasure_sliceMeasure (N := N) μG ρ hρcont hd β
  exact MemLp.of_bound hFaesm C (ae_of_all _ hC)

/-- The product of an `L^∞` slice observable with an `L²`
vector is in `L²` (Hölder, `∞ · 2 → 2`). Stated as a lemma so
the Hölder triple's exponents are pinned by the ascribed
type. -/
theorem memLp_mul_slice (β : ℝ)
    (F : SliceConfig → ℂ)
    (hFinf : MemLp F ∞ (sliceMeasure (N := N) μG ρ β))
    (ψ : osSpace (N := N) μG ρ β) :
    MemLp (F * ⇑ψ) 2 (sliceMeasure (N := N) μG ρ β) :=
  hFinf.mul (Lp.memLp ψ)

/-- Norm bound for pointwise multiplication by an `L^∞`
observable, at the level of `L²` representatives: the
`L∞`–`L²` Hölder estimate. -/
theorem norm_mul_toLp_le (β : ℝ)
    (F : SliceConfig → ℂ)
    (hFinf : MemLp F ∞ (sliceMeasure (N := N) μG ρ β))
    (C : ℝ) (hFC : ∀ z, ‖F z‖ ≤ C)
    (ψ : osSpace (N := N) μG ρ β) :
    ‖(memLp_mul_slice μG ρ β F hFinf ψ).toLp (F * ⇑ψ)‖ ≤ C * ‖ψ‖ := by
  have hC0 : 0 ≤ C :=
    le_trans (norm_nonneg _) (hFC (fun _ => (1 : G)))
  have hFinfle : eLpNorm F ∞ (sliceMeasure (N := N) μG ρ β)
      ≤ ENNReal.ofReal C := by
    refine le_trans (eLpNorm_le_of_ae_bound
      hFinf.aestronglyMeasurable (ae_of_all _ hFC)) ?_
    rw [ENNReal.toReal_top, inv_zero, ENNReal.rpow_zero, one_mul]
  have hmul : (F * ⇑ψ) = F • ⇑ψ :=
    funext fun z => (smul_eq_mul (F z) (ψ z)).symm
  have hfin : eLpNorm (⇑ψ) 2 (sliceMeasure (N := N) μG ρ β)
      ≠ ⊤ := ne_of_lt (Lp.memLp ψ).eLpNorm_lt_top
  have hle : eLpNorm (F • ⇑ψ) 2 (sliceMeasure (N := N) μG ρ β)
      ≤ ENNReal.ofReal C
        * eLpNorm (⇑ψ) 2 (sliceMeasure (N := N) μG ρ β) :=
    le_trans (eLpNorm_smul_le_mul_eLpNorm
      hFinf.aestronglyMeasurable (Lp.aestronglyMeasurable ψ))
      (mul_le_mul' hFinfle le_rfl)
  rw [Lp.norm_def, Lp.norm_def,
    eLpNorm_congr_ae (memLp_mul_slice μG ρ β F hFinf ψ).coeFn_toLp, hmul]
  calc (eLpNorm (F • ⇑ψ) 2 (sliceMeasure (N := N) μG ρ β)).toReal
      ≤ (ENNReal.ofReal C
          * eLpNorm (⇑ψ) 2 (sliceMeasure (N := N) μG ρ β)).toReal :=
        ENNReal.toReal_mono
          (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin) hle
    _ = C * (eLpNorm (⇑ψ) 2 (sliceMeasure (N := N) μG ρ β)).toReal := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC0]

/-- Pointwise multiplication by an `L^∞` slice observable, as
a linear map on the OS space. -/
noncomputable def sliceMulLinear (β : ℝ)
    (F : SliceConfig → ℂ)
    (hFinf : MemLp F ∞ (sliceMeasure (N := N) μG ρ β))
    (C : ℝ) (hFC : ∀ z, ‖F z‖ ≤ C) :
    osSpace (N := N) μG ρ β →ₗ[ℂ] osSpace (N := N) μG ρ β where
  toFun ψ := (memLp_mul_slice μG ρ β F hFinf ψ).toLp (F * ⇑ψ)
  map_add' := by
    intro ψ φ
    have e1 := (memLp_mul_slice μG ρ β F hFinf (ψ + φ)).coeFn_toLp
    have e2 := (memLp_mul_slice μG ρ β F hFinf ψ).coeFn_toLp
    have e3 := (memLp_mul_slice μG ρ β F hFinf φ).coeFn_toLp
    apply Lp.ext
    filter_upwards [e1, e2, e3, Lp.coeFn_add ψ φ,
      Lp.coeFn_add
        ((memLp_mul_slice μG ρ β F hFinf ψ).toLp (F * ⇑ψ))
        ((memLp_mul_slice μG ρ β F hFinf φ).toLp (F * ⇑φ))]
      with z h1 h2 h3 h4 h5
    rw [h1, h5]
    simp only [Pi.add_apply]
    rw [h2, h3]
    simp only [Pi.mul_apply]
    rw [h4]
    simp only [Pi.add_apply, mul_add]
  map_smul' := by
    intro c ψ
    have e1 := (memLp_mul_slice μG ρ β F hFinf (c • ψ)).coeFn_toLp
    have e2 := (memLp_mul_slice μG ρ β F hFinf ψ).coeFn_toLp
    apply Lp.ext
    filter_upwards [e1, e2, Lp.coeFn_smul c ψ,
      Lp.coeFn_smul c
        ((memLp_mul_slice μG ρ β F hFinf ψ).toLp (F * ⇑ψ))]
      with z h1 h2 h3 h4
    simp only [RingHom.id_apply]
    rw [h1, h4]
    simp only [Pi.smul_apply]
    rw [h2]
    simp only [Pi.mul_apply]
    rw [h3]
    simp only [Pi.mul_apply, Pi.smul_apply, RingHom.id_apply,
      smul_eq_mul]
    ring

/-- **Multiplication operator:** an `L^∞` slice observable
`F`, bounded by `C`, acts on the OS space by pointwise
multiplication, as a continuous linear map. -/
noncomputable def sliceMul (β : ℝ)
    (F : SliceConfig → ℂ)
    (hFinf : MemLp F ∞ (sliceMeasure (N := N) μG ρ β))
    (C : ℝ) (hFC : ∀ z, ‖F z‖ ≤ C) :
    osSpace (N := N) μG ρ β →L[ℂ] osSpace (N := N) μG ρ β :=
  LinearMap.mkContinuous (sliceMulLinear μG ρ β F hFinf C hFC) C
    (fun ψ => norm_mul_toLp_le μG ρ β F hFinf C hFC ψ)

/-- The multiplication operator acts as pointwise
multiplication almost everywhere. -/
theorem sliceMul_coeFn (β : ℝ)
    (F : SliceConfig → ℂ)
    (hFinf : MemLp F ∞ (sliceMeasure (N := N) μG ρ β))
    (C : ℝ) (hFC : ∀ z, ‖F z‖ ≤ C)
    (ψ : osSpace (N := N) μG ρ β) :
    ⇑(sliceMul μG ρ β F hFinf C hFC ψ)
      =ᵐ[sliceMeasure (N := N) μG ρ β] (F * ⇑ψ) :=
  (memLp_mul_slice μG ρ β F hFinf ψ).coeFn_toLp

/-- The multiplication operator's norm is at most the
observable's bound. -/
theorem norm_sliceMul_le (β : ℝ)
    (F : SliceConfig → ℂ)
    (hFinf : MemLp F ∞ (sliceMeasure (N := N) μG ρ β))
    (C : ℝ) (hFC : ∀ z, ‖F z‖ ≤ C) :
    ‖sliceMul μG ρ β F hFinf C hFC‖ ≤ C := by
  have hC0 : 0 ≤ C :=
    le_trans (norm_nonneg _) (hFC (fun _ => (1 : G)))
  exact (sliceMul μG ρ β F hFinf C hFC).opNorm_le_bound hC0
    (fun ψ => norm_mul_toLp_le μG ρ β F hFinf C hFC ψ)

/-- The multiplication operator depends only on the
observable, not on the chosen boundedness data. -/
theorem sliceMul_congr (β : ℝ)
    (F H : SliceConfig → ℂ) (hFH : F = H)
    (hFinf : MemLp F ∞ (sliceMeasure (N := N) μG ρ β))
    (hHinf : MemLp H ∞ (sliceMeasure (N := N) μG ρ β))
    (C : ℝ) (hFC : ∀ z, ‖F z‖ ≤ C) (hHC : ∀ z, ‖H z‖ ≤ C) :
    sliceMul μG ρ β F hFinf C hFC
      = sliceMul μG ρ β H hHinf C hHC := by
  subst hFH
  rfl

/-- Multiplication by the constant observable `1` is the
identity operator. -/
theorem sliceMul_one (β : ℝ)
    (hFinf : MemLp (fun _ => (1 : ℂ)) ∞
      (sliceMeasure (N := N) μG ρ β)) :
    sliceMul μG ρ β (fun _ => (1 : ℂ)) hFinf 1
        (fun _ => le_of_eq norm_one)
      = ContinuousLinearMap.id ℂ (osSpace (N := N) μG ρ β) := by
  apply ContinuousLinearMap.ext
  intro ψ
  apply Lp.ext
  filter_upwards [sliceMul_coeFn μG ρ β (fun _ => (1 : ℂ)) hFinf 1
    (fun _ => le_of_eq norm_one) ψ] with z hz
  rw [hz]
  simp

/-- Multiplication operators compose as the pointwise
product of observables. -/
theorem sliceMul_mul (β : ℝ)
    (F : SliceConfig → ℂ)
    (hFinf : MemLp F ∞ (sliceMeasure (N := N) μG ρ β))
    (C : ℝ) (hFC : ∀ z, ‖F z‖ ≤ C)
    (H : SliceConfig → ℂ)
    (hHinf : MemLp H ∞ (sliceMeasure (N := N) μG ρ β))
    (D : ℝ) (hHD : ∀ z, ‖H z‖ ≤ D)
    (hFH : ∀ z, ‖(F * H) z‖ ≤ C * D) :
    sliceMul μG ρ β (F * H) (hFinf.mul hHinf) (C * D) hFH
      = (sliceMul μG ρ β F hFinf C hFC)
        ∘L (sliceMul μG ρ β H hHinf D hHD) := by
  apply ContinuousLinearMap.ext
  intro ψ
  apply Lp.ext
  filter_upwards [sliceMul_coeFn μG ρ β (F * H) (hFinf.mul hHinf)
      (C * D) hFH ψ,
    sliceMul_coeFn μG ρ β F hFinf C hFC
      (sliceMul μG ρ β H hHinf D hHD ψ),
    sliceMul_coeFn μG ρ β H hHinf D hHD ψ] with z h1 h2 h3
  simp only [ContinuousLinearMap.comp_apply]
  rw [h1, h2]
  simp only [Pi.mul_apply]
  rw [h3]
  simp only [Pi.mul_apply, mul_assoc]

/-- **Adjoint of a multiplication operator:** pointwise
conjugation of the observable. -/
theorem sliceMul_adjoint (β : ℝ)
    (F : SliceConfig → ℂ)
    (hFinf : MemLp F ∞ (sliceMeasure (N := N) μG ρ β))
    (C : ℝ) (hFC : ∀ z, ‖F z‖ ≤ C)
    (hFinf' : MemLp (starRingEnd ℂ ∘ F) ∞
      (sliceMeasure (N := N) μG ρ β))
    (hFC' : ∀ z, ‖(starRingEnd ℂ ∘ F) z‖ ≤ C) :
    (sliceMul μG ρ β F hFinf C hFC)†
      = sliceMul μG ρ β (starRingEnd ℂ ∘ F) hFinf' C hFC' := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro ψ φ
  rw [inner_osSpace, inner_osSpace]
  apply integral_congr_ae
  filter_upwards [sliceMul_coeFn μG ρ β (starRingEnd ℂ ∘ F) hFinf'
      C hFC' ψ,
    sliceMul_coeFn μG ρ β F hFinf C hFC φ] with z hz1 hz2
  rw [hz1, hz2]
  simp only [Pi.mul_apply, Function.comp_apply, starRingEnd_apply,
    RCLike.inner_apply, star_mul, star_star]
  ring

/-- A real-valued observable gives a **self-adjoint**
multiplication operator. -/
theorem sliceMul_selfAdjoint (β : ℝ)
    (F : SliceConfig → ℂ)
    (hFinf : MemLp F ∞ (sliceMeasure (N := N) μG ρ β))
    (C : ℝ) (hFC : ∀ z, ‖F z‖ ≤ C)
    (hFinf' : MemLp (starRingEnd ℂ ∘ F) ∞
      (sliceMeasure (N := N) μG ρ β))
    (hFC' : ∀ z, ‖(starRingEnd ℂ ∘ F) z‖ ≤ C)
    (hFreal : ∀ z, (starRingEnd ℂ) (F z) = F z) :
    (sliceMul μG ρ β F hFinf C hFC)†
      = sliceMul μG ρ β F hFinf C hFC := by
  have hF : (starRingEnd ℂ ∘ F) = F :=
    funext fun z => hFreal z
  rw [sliceMul_adjoint μG ρ β F hFinf C hFC hFinf' hFC']
  exact sliceMul_congr μG ρ β (starRingEnd ℂ ∘ F) F hF hFinf'
    hFinf C hFC' hFC

end Operators

/-! ## §7. The fence: the OS form, and the named Gram clause

Stage 1b-B left exactly one clause open: the
Gram/character-expansion factorization of the Wilson weight,
whose standard proof needs Peter–Weyl orthogonality for a
general compact group — absent from the pinned Mathlib. This
section does NOT spend that clause. It

* names it once, as `GramClause` (shape copied verbatim from
  Stage 1b-B's `osForm_nonneg_of_gram` hypothesis);
* proves the bridge: **if** the clause holds, **then** the OS
  form is positive on observables factoring through the time
  slice (`osForm_nonneg_of_gramClause`) — a conditional
  restatement of 1b-B's criterion, nothing more;
* observes that time-slice observables ARE `posLinks`
  observables (§3), so the bridge reaches exactly the present
  module's states (`osForm_slice_nonneg_of_gramClause`);
* and records the unconditional `β = 0` comparison
  (`osForm_slice_zero`): at zero coupling the OS form of a
  slice observable is the squared modulus of its slice
  integral — the vacuum-expectation inner product of §5.

An identification of the OS form with the slice `L²` inner
product at general `β` would route through the same clause
and is therefore NOT asserted here; it is fenced to Stage
1b-D / future work, together with the transfer matrix. -/

section OSComparison

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ))
  {N : ℕ} [NeZero N]

/-- **The named Gram clause** (Stage 1b-B's open clause): the
Wilson weight at coupling `β`, in split coordinates, factors
as a finite sum of products of a function of the mirrored
negative configuration times a function of the positive
configuration. This is the character-expansion factorization
whose standard proof needs Peter–Weyl orthogonality; it is
**named here, not proved**. -/
def GramClause (hN : Even N) (β : ℝ) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι)
    (Ξ : ι → (↥(posLinks (N := N)) → G) → ℂ),
    (∀ i, AEStronglyMeasurable (Ξ i)
      (Measure.pi fun _ : ↥(posLinks (N := N)) => μG))
    ∧ (∃ CΞ : ℝ, ∀ i z, ‖Ξ i z‖ ≤ CΞ)
    ∧ ∀ (y : ↥(halfLinks (N := N)) → G)
        (u : ↥(negLinks (N := N)) → G),
        (Real.exp (- wilsonAction (torusShift N) ρ β
          ((splitEquiv (halfLinks (N := N))).symm (y, u))) : ℂ)
        = ∑ i, (starRingEnd ℂ) (Ξ i (mirrorP hN u))
            * Ξ i (restrictPos y)

/-- **The conditional bridge.** IF the Gram clause holds at
coupling `β`, THEN Stage 1b-B's OS form is positive on every
observable factoring through the strict positive half. This
is a restatement of 1b-B's proved Gram criterion fed with
the named clause — the clause itself remains open. -/
theorem osForm_nonneg_of_gramClause
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (hd : 0 < d) (β : ℝ)
    (hgram : GramClause μG ρ hN β)
    (F : Config (Fin 4 → ZMod N) G → ℂ)
    (f : (↥(posLinks (N := N)) → G) → ℂ)
    (hF : ∀ U, F U = f (fun ℓ : ↥(posLinks (N := N)) => U ℓ.1))
    (hfA : AEStronglyMeasurable f
      (Measure.pi fun _ : ↥(posLinks (N := N)) => μG))
    (Cf : ℝ) (hfB : ∀ z, ‖f z‖ ≤ Cf) :
    0 ≤ (osForm μG ρ β F F).re ∧ (osForm μG ρ β F F).im = 0 := by
  obtain ⟨ι, hι, Ξ, hΞA, ⟨CΞ, hΞB⟩, hfact⟩ := hgram
  letI := hι
  exact osForm_nonneg_of_gram μG ρ hρcont hN hd β F f hF hfA Cf hfB
    Ξ hΞA CΞ hΞB hfact

/-- A function on the time slice, pulled back to the strict
positive half along the inclusion of §3. -/
noncomputable def posToSlice (hN : Even N) :
    (↥(posLinks (N := N)) → G) → (↥(sliceLinks (N := N)) → G) :=
  fun y ℓ => y ⟨ℓ.1, sliceLinks_subset_posLinks hN ℓ.2⟩

/-- `posToSlice` is continuous (it is a coordinate
restriction). -/
theorem continuous_posToSlice (hN : Even N) :
    Continuous (posToSlice (G := G) hN) := by
  unfold posToSlice
  exact continuous_pi fun ℓ =>
    continuous_apply (⟨ℓ.1, sliceLinks_subset_posLinks hN ℓ.2⟩ :
      ↥(posLinks (N := N)))

/-- A slice observable, as a full configuration observable,
factors through the strict positive half via the slice
inclusion: its `posLinks` representative is precomposition
with `posToSlice`. -/
theorem sliceFactor (hN : Even N)
    (f : SliceConfig → ℂ) :
    ∀ U : Config (Fin 4 → ZMod N) G,
      f (fun ℓ : ↥(sliceLinks (N := N)) => U ℓ.1)
        = (f ∘ posToSlice hN)
            (fun ℓ : ↥(posLinks (N := N)) => U ℓ.1) :=
  fun U => rfl

/-- **Conditional OS positivity for slice observables.** IF
the Gram clause holds at `β`, THEN the OS form is positive
on every observable factoring through the time slice whose
`posLinks` representative is measurable with respect to the
product measure and bounded. The Gram hypothesis is the
named clause of 1b-B — spent only as a hypothesis. (The
transfer of measurability from the slice measure to the
product measure is the `posToSlice` marginal identity —
`Measure.map (posToSlice hN) π = π` over the slice — named
here as an unproved identity, priced S; it is NOT used.) -/
theorem osForm_slice_nonneg_of_gramClause
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (hd : 0 < d) (β : ℝ)
    (hgram : GramClause μG ρ hN β)
    (f : SliceConfig → ℂ)
    (hfA : AEStronglyMeasurable (f ∘ posToSlice hN)
      (Measure.pi fun _ : ↥(posLinks (N := N)) => μG))
    (Cf : ℝ) (hfB : ∀ z, ‖f z‖ ≤ Cf) :
    0 ≤ (osForm μG ρ β
      (fun U => f (fun ℓ : ↥(sliceLinks (N := N)) => U ℓ.1))
      (fun U => f (fun ℓ : ↥(sliceLinks (N := N)) => U ℓ.1))).re
      ∧ (osForm μG ρ β
      (fun U => f (fun ℓ : ↥(sliceLinks (N := N)) => U ℓ.1))
      (fun U => f (fun ℓ : ↥(sliceLinks (N := N)) => U ℓ.1))).im
      = 0 := by
  apply osForm_nonneg_of_gramClause μG ρ hρcont hN hd β hgram
    _ (f ∘ posToSlice hN) _ hfA Cf
  · intro z
    exact hfB (posToSlice hN z)
  · intro U
    rfl

/-- **Unconditional positivity at `β = 0` for slice
observables.** At zero coupling, the OS form of a slice
observable is nonnegative — proved from 1b-B's `β = 0`
theorem, with NO appeal to the Gram clause; the factor
identity is definitional. (By 1b-B's `osForm_zero_eq`, the
value there is the squared modulus of the representative's
product-measure integral; identifying that integral with
the slice integral of §5 is the `posToSlice` marginal
identity named in `osForm_slice_nonneg_of_gramClause` —
unproved here, priced S, and NOT used.) -/
theorem osForm_slice_zero (hN : Even N)
    (f : SliceConfig → ℂ)
    (hfA : AEStronglyMeasurable f
      (sliceMeasure (N := N) μG ρ 0)) :
    0 ≤ (osForm μG ρ 0
      (fun U => f (fun ℓ : ↥(sliceLinks (N := N)) => U ℓ.1))
      (fun U => f (fun ℓ : ↥(sliceLinks (N := N)) => U ℓ.1))).re
      ∧ (osForm μG ρ 0
      (fun U => f (fun ℓ : ↥(sliceLinks (N := N)) => U ℓ.1))
      (fun U => f (fun ℓ : ↥(sliceLinks (N := N)) => U ℓ.1))).im
      = 0 := by
  apply osForm_zero_nonneg μG ρ hN _ (f ∘ posToSlice hN)
  intro U
  rfl

end OSComparison

end ThetLogos
