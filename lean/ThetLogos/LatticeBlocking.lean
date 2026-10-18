import ThetLogos.LatticeTransfer
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.Tactic

/-!
# ThetLogos.LatticeBlocking — Pitch 4, Stage 2: one exact blocking step (T1)

HONESTY LEDGER (read before citing):

- Everything in this file is **T1 finite lattice algebra, finite
  combinatorics, and finite integration**: on Stage 0/1a's abstract
  finite lattices (sites `Λ`, `Λ'`, shift families `σ`, `σ'`), this
  module fixes **one blocking scheme** — a factor-2 decimation whose
  blocked link variables are the ordered products of the two fine
  links along each blocked edge — and proves the exact properties of
  the induced coarse-graining step: gauge covariance of the blocked
  variables, gauge invariance of the blocked (pushforward) measure in
  the strong `Measure.map` form at every `β`, consistency of
  expectations for the observables that factor through the blocking
  (coarse Wilson loops are fine perimeter loops, proved), the exact
  `β = 0` image (the pushforward of product Haar is product Haar, so
  the blocked theory at `β = 0` *is* the coarse Stage-0 theory at
  `β = 0`, and its plaquette package transports verbatim), the
  Elitzur constraint transported to the blocked measure at **every**
  `β`, composition of two blockings (a `4 : 1` step, as a function
  identity and a measure identity), the existence of the blocked
  effective action at every `β` as a measurable log-density, and a
  concrete torus instance. Zero sorrys, no new axioms (headline
  theorems are checked against the standard three — `propext`,
  `Classical.choice`, `Quot.sound` — and the audit is recorded in the
  dossier `whitepaper/pitch-4-stage-2-2026-10-18.md`).

- *(finite-lattice discipline)* "Results in this module are about a
  finite lattice at fixed spacing and volume. Nothing here is a
  continuum result; the words 'continuum', 'ℝ⁴', and 'Poincaré' do
  not describe anything proved in this module."

- *(gap discipline)* "Any gap statement in this module is a lattice
  statement at the stated $(a, L, \beta)$. No continuum mass gap is
  claimed; a lattice gap transfers to the continuum only with
  uniformity in the spacing along the tuning curve, which is not
  proved here or anywhere in this corpus." (This module proves no
  gap statement of any kind; the clause travels with the pitch.)

- *(gauge discipline)* "Gauge invariance here is exact invariance of
  a finite lattice action and measure under finite gauge
  transformations. It is not a continuum gauge theory, and this module
  contains no quantized continuum gauge field."

- *(RG discipline, Stage 2)* "A blocking step is a map, not the
  flow; no β-function, fixed-point criticality, or continuum limit
  is stated or implied by anything in this module." One blocking
  step is formalized here; iterating it *with estimates* is the
  priced wall behind Stage 3, not a result of this module.

- *(standing charter)* "Parts of the official Clay Yang–Mills
  statement closed by this module: 0."

DESIGN CHOICES (the choices §6.3 of the Pitch 4 scoping delegated,
disclosed):

- **The scheme.** One scheme, chosen: **decimation by path-ordered
  products**. A blocking scheme is a structure (`BlockingScheme`)
  packaging a coarse-site embedding `ι : Λ' → Λ` with three proved
  properties: injectivity; the two-step law `σ μ (σ μ (ι y)) =
  ι (σ' μ y)` (two fine steps from a coarse site are one coarse
  step); and the parity law `σ μ (ι y) ∉ range ι` (one fine step
  from a coarse site leaves the coarse sublattice). The blocked
  link at `(y, μ)` is `U(ι y, μ) * U(σ μ (ι y), μ)`. The concrete
  torus instance (extent `2M` blocking to extent `M`) is discharged
  in §8. The scoping's partial-integration definition of the blocked
  measure is, for this deterministic (delta-kernel) scheme, exactly
  the pushforward under the blocking map; the dossier names this
  realization choice.
- **The blocked measure is the primary object.** `blockedMeasure`
  is the pushforward of a fine measure under the blocking map;
  `blockedGibbsMeasure` is the pushforward of Stage 1a's Gibbs
  measure. At general `β` the blocked Gibbs measure is **not** a
  coarse Wilson–Gibbs measure (blocking generates multi-plaquette
  couplings); §7 makes the precise statement that survives: the
  blocked measure has a measurable log-density — the effective
  action — against the coarse configuration measure, at every `β`.
  The assertion that no coarse Wilson action reproduces the blocked
  measure at `β > 0` is **fenced**, as a named `Prop`
  (`BlockedGibbsIsCoarseGibbs`), proved at `β = 0` (with image
  coupling `β' = 0`) and not claimed at `β > 0`: it is the
  Stage 3-facing question, priced in the dossier.
- **What "fixed point" means here.** At finite volume the blocking
  map goes between *different* configuration spaces, so a fixed
  point is a statement about a family across scales, not about one
  measure. Two exact fixed families are proved: the product-Haar
  family (equivalently the `β = 0` Gibbs family — the free fixed
  point), and the trivial-configuration Dirac family. No other
  fixed point is claimed or expected at finite volume.

This module is NOT in the root import list of the library (the corpus
pattern for recent exhibits); it is verified by a targeted build.
-/

namespace ThetLogos

open MeasureTheory Finset
open scoped Matrix ENNReal NNReal

/-! ## §1. The blocking scheme and the blocking map

Pure group algebra: `G` is an abstract group here. -/

section Algebra

variable {Λ Λ' : Type*} [Fintype Λ] [Fintype Λ'] {G : Type*} [Group G]
variable (σ : Fin 4 → Equiv.Perm Λ) (σ' : Fin 4 → Equiv.Perm Λ')

/-- A **blocking scheme** from the fine lattice `(Λ, σ)` to the
coarse lattice `(Λ', σ')`: a coarse-site embedding `ι` satisfying
the two-step law (two fine steps from a coarse site are one coarse
step) and the parity law (one fine step from a coarse site leaves
the coarse sublattice). This is the one coarse-graining scheme of
Stage 2, chosen and disclosed (Pitch 4 scoping §6.3). -/
structure BlockingScheme (σ : Fin 4 → Equiv.Perm Λ)
    (σ' : Fin 4 → Equiv.Perm Λ') where
  /-- The coarse sites, embedded in the fine lattice. -/
  ι : Λ' → Λ
  /-- The embedding is injective. -/
  ι_injective : Function.Injective ι
  /-- Two fine steps from a coarse site are one coarse step. -/
  twoStep : ∀ (μ : Fin 4) (y : Λ'), σ μ (σ μ (ι y)) = ι (σ' μ y)
  /-- One fine step from a coarse site is not a coarse site. -/
  oddStep : ∀ (μ : Fin 4) (y : Λ'), σ μ (ι y) ∉ Set.range ι

/-- The first fine link of the blocked edge over the coarse link
`ℓ'`: the link based at the coarse site itself. -/
def fineLinkA (B : BlockingScheme σ σ') (ℓ' : Link Λ') : Link Λ :=
  (B.ι ℓ'.1, ℓ'.2)

/-- The second fine link of the blocked edge over the coarse link
`ℓ'`: the link based one fine step along the edge. -/
def fineLinkB (B : BlockingScheme σ σ') (ℓ' : Link Λ') : Link Λ :=
  (σ ℓ'.2 (B.ι ℓ'.1), ℓ'.2)

/-- The **blocking map**: the coarse configuration whose link
variables are the ordered products of the two fine links along each
blocked edge, `(blockMap σ σ' B U)(y, μ) = U(ι y, μ) * U(σ μ (ι y), μ)`. -/
def blockMap (B : BlockingScheme σ σ') (U : Config Λ G) : Config Λ' G :=
  fun ℓ' => U (fineLinkA σ σ' B ℓ') * U (fineLinkB σ σ' B ℓ')

theorem blockMap_apply (B : BlockingScheme σ σ') (U : Config Λ G)
    (y : Λ') (μ : Fin 4) :
    blockMap σ σ' B U (y, μ) = U (B.ι y, μ) * U (σ μ (B.ι y), μ) := rfl

/-- The first-factor fine links are pairwise distinct: distinct
coarse links have distinct first factors. -/
theorem fineLinkA_injective (B : BlockingScheme σ σ') :
    Function.Injective (fineLinkA σ σ' B) := by
  intro ℓ₁ ℓ₂ h
  obtain ⟨x₁, μ₁⟩ := ℓ₁
  obtain ⟨x₂, μ₂⟩ := ℓ₂
  have h1 : B.ι x₁ = B.ι x₂ := congrArg Prod.fst h
  have h2 : μ₁ = μ₂ := congrArg Prod.snd h
  exact Prod.ext_iff.mpr ⟨B.ι_injective h1, h2⟩

/-- The second-factor fine links are pairwise distinct. -/
theorem fineLinkB_injective (B : BlockingScheme σ σ') :
    Function.Injective (fineLinkB σ σ' B) := by
  intro ℓ₁ ℓ₂ h
  obtain ⟨x₁, μ₁⟩ := ℓ₁
  obtain ⟨x₂, μ₂⟩ := ℓ₂
  have h2 : μ₁ = μ₂ := congrArg Prod.snd h
  have h1 : σ μ₁ (B.ι x₁) = σ μ₂ (B.ι x₂) := congrArg Prod.fst h
  rw [h2] at h1
  have h3 : B.ι x₁ = B.ι x₂ := (σ μ₂).injective h1
  exact Prod.ext_iff.mpr ⟨B.ι_injective h3, h2⟩

/-- A first-factor link is never a second-factor link: their base
sites have opposite parity (coarse vs one-step-off). This is the
disjointness the `β = 0` pushforward computation consumes. -/
theorem fineLinkA_ne_fineLinkB (B : BlockingScheme σ σ')
    (ℓ' ℓ'' : Link Λ') : fineLinkA σ σ' B ℓ' ≠ fineLinkB σ σ' B ℓ'' := by
  intro h
  have hsite : B.ι ℓ'.1 = σ ℓ''.2 (B.ι ℓ''.1) := congrArg Prod.fst h
  have hmem : σ ℓ''.2 (B.ι ℓ''.1) ∈ Set.range B.ι := ⟨ℓ'.1, hsite⟩
  exact B.oddStep ℓ''.2 ℓ''.1 hmem

/-- A second-factor link is never a first-factor link. -/
theorem fineLinkB_ne_fineLinkA (B : BlockingScheme σ σ')
    (ℓ' ℓ'' : Link Λ') : fineLinkB σ σ' B ℓ' ≠ fineLinkA σ σ' B ℓ'' :=
  fun h => fineLinkA_ne_fineLinkB σ σ' B ℓ'' ℓ' h.symm

/-- The blocking map fixes the trivial configuration. -/
theorem blockMap_one (B : BlockingScheme σ σ') :
    blockMap σ σ' B (fun _ => (1 : G)) = (fun _ => (1 : G)) := by
  funext ℓ'
  simp [blockMap]

end Algebra

/-! ## §2. Gauge covariance of the blocked variables

The blocked link based at `(y, μ)` is the product of two fine links
along a path from the coarse site `ι y` to the coarse site
`ι (σ' μ y)`. Under a fine gauge transformation that agrees with a
coarse gauge transformation `g'` at coarse sites and is trivial at
the intermediate (odd) sites, the blocked link therefore transforms
exactly as a coarse link variable. -/

section Covariance

variable {Λ Λ' : Type*} [Fintype Λ] [Fintype Λ'] {G : Type*} [Group G]
variable (σ : Fin 4 → Equiv.Perm Λ) (σ' : Fin 4 → Equiv.Perm Λ')

open Classical in
/-- The extension of a coarse gauge transformation `g'` to the fine
lattice: `g'` at coarse sites, `1` at all other sites. -/
noncomputable def gaugeExtend (B : BlockingScheme σ σ') (g' : Λ' → G) :
    Λ → G :=
  fun x => if h : x ∈ Set.range B.ι then g' (Classical.choose h)
    else 1

open Classical in
theorem gaugeExtend_apply (B : BlockingScheme σ σ') (g' : Λ' → G)
    (x : Λ) : gaugeExtend σ σ' B g' x
      = if h : x ∈ Set.range B.ι then g' (Classical.choose h)
        else 1 := rfl

/-- The extension agrees with `g'` at coarse sites. -/
theorem gaugeExtend_coarse (B : BlockingScheme σ σ') (g' : Λ' → G)
    (y : Λ') : gaugeExtend σ σ' B g' (B.ι y) = g' y := by
  have hmem : B.ι y ∈ Set.range B.ι := ⟨y, rfl⟩
  have hchoose : Classical.choose hmem = y :=
    B.ι_injective (Classical.choose_spec hmem)
  rw [gaugeExtend_apply, dif_pos hmem, hchoose]

/-- The extension is trivial off the coarse sublattice. -/
theorem gaugeExtend_of_not_mem (B : BlockingScheme σ σ') (g' : Λ' → G)
    {x : Λ} (hx : x ∉ Set.range B.ι) : gaugeExtend σ σ' B g' x = 1 := by
  rw [gaugeExtend_apply, dif_neg hx]

/-- **Gauge covariance of the blocked variables.** Blocking the
gauge-transform of a fine configuration by the extension of a coarse
gauge transformation is the coarse gauge transform of the blocked
configuration. The blocked links are therefore genuine coarse link
variables. -/
theorem blockMap_gaugeExtend (B : BlockingScheme σ σ') (g' : Λ' → G)
    (U : Config Λ G) :
    blockMap σ σ' B (gaugeAction σ (gaugeExtend σ σ' B g') U)
      = gaugeAction σ' g' (blockMap σ σ' B U) := by
  funext ⟨y, μ⟩
  have h1 : gaugeExtend σ σ' B g' (σ μ (B.ι y)) = 1 :=
    gaugeExtend_of_not_mem σ σ' B g' (B.oddStep μ y)
  have h2 : gaugeExtend σ σ' B g' (B.ι (σ' μ y)) = g' (σ' μ y) :=
    gaugeExtend_coarse σ σ' B g' (σ' μ y)
  have h3 : σ μ (σ μ (B.ι y)) = B.ι (σ' μ y) := B.twoStep μ y
  have h0 : gaugeExtend σ σ' B g' (B.ι y) = g' y :=
    gaugeExtend_coarse σ σ' B g' y
  simp only [blockMap_apply, gaugeAction_apply, h0, h1, h2, h3]
  group

end Covariance

/-! ## §3. The blocked measure and its gauge invariance

The blocked measure is the pushforward under the blocking map —
for the deterministic (delta-kernel) scheme chosen here this *is*
the scoping's partial-integration definition: the blocked Boltzmann
weight of a coarse configuration is the fine weight integrated over
the fiber of configurations blocking to it. -/

section MeasureTransport

variable {Λ Λ' : Type*} [Fintype Λ] [Fintype Λ']
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
variable (σ : Fin 4 → Equiv.Perm Λ) (σ' : Fin 4 → Equiv.Perm Λ')

/-- The blocking map is measurable (each blocked link is a product
of two evaluations). -/
theorem measurable_blockMap (B : BlockingScheme σ σ') :
    Measurable (blockMap σ σ' B : Config Λ G → Config Λ' G) :=
  measurable_pi_iff.mpr fun ℓ' => by
    show Measurable (fun U : Config Λ G =>
      U (fineLinkA σ σ' B ℓ') * U (fineLinkB σ σ' B ℓ'))
    have hA : Measurable (fun U : Config Λ G =>
        U (fineLinkA σ σ' B ℓ')) := measurable_pi_apply _
    have hB : Measurable (fun U : Config Λ G =>
        U (fineLinkB σ σ' B ℓ')) := measurable_pi_apply _
    exact continuous_mul.measurable.comp (hA.prodMk hB)

/-- The **blocked measure**: the pushforward of a fine measure
under the blocking map. This is the coarse-grained measure of one
blocking step. -/
noncomputable def blockedMeasure (B : BlockingScheme σ σ')
    (μ : Measure (Config Λ G)) : Measure (Config Λ' G) :=
  Measure.map (blockMap σ σ' B) μ

/-- **Gauge invariance of the blocked measure (strong form).** The
pushforward of any gauge-invariant fine measure under the blocking
map is gauge invariant under coarse gauge transformations. The
proof is the covariance of §2 composed with the assumed invariance:
the coarse gauge action on the blocked measure is the blocked fine
gauge action by the *extended* transformation. -/
theorem blockedMeasure_map_gaugeAction (B : BlockingScheme σ σ')
    {μ : Measure (Config Λ G)}
    (hμ : ∀ g : Λ → G, Measure.map (gaugeAction σ g) μ = μ)
    (g' : Λ' → G) :
    Measure.map (gaugeAction σ' g') (blockedMeasure σ σ' B μ)
      = blockedMeasure σ σ' B μ := by
  have hfun : gaugeAction σ' g' ∘ blockMap σ σ' B
      = blockMap σ σ' B ∘ gaugeAction σ (gaugeExtend σ σ' B g') := by
    funext U
    simp only [Function.comp_apply]
    exact (blockMap_gaugeExtend σ σ' B g' U).symm
  unfold blockedMeasure
  rw [Measure.map_map (measurable_gaugeAction σ' g')
      (measurable_blockMap σ σ' B), hfun,
    ← Measure.map_map (measurable_blockMap σ σ' B)
      (measurable_gaugeAction σ _), hμ]

end MeasureTransport

section GibbsTransport

variable {Λ Λ' : Type*} [Fintype Λ] [Fintype Λ']
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
variable (σ : Fin 4 → Equiv.Perm Λ) (σ' : Fin 4 → Equiv.Perm Λ')
variable (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
variable {d : ℕ} (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ))

/-- The Gibbs density is invariant under the gauge action, because
the Wilson action is (Stage 0). Needs the shifts to commute. -/
theorem gibbsDensity_gaugeAction
    (hσ : ∀ μ ν x, σ μ (σ ν x) = σ ν (σ μ x)) (g : Λ → G) (β : ℝ)
    (U : Config Λ G) :
    gibbsDensity σ ρ β (gaugeAction σ g U) = gibbsDensity σ ρ β U := by
  apply Subtype.ext
  show Real.exp (- wilsonAction σ ρ β (gaugeAction σ g U))
    = Real.exp (- wilsonAction σ ρ β U)
  rw [wilsonAction_gauge_invariant σ ρ hσ g β U]

/-- The Gibbs density, coerced to `ℝ≥0∞`, is measurable. -/
theorem measurable_coe_gibbsDensity
    (hρcont : Continuous fun g : G => repMatrix ρ g) (β : ℝ) :
    Measurable (fun U : Config Λ G => (gibbsDensity σ ρ β U : ℝ≥0∞)) :=
  measurable_coe_nnreal_ennreal.comp
    (measurable_gibbsDensity σ ρ hρcont β)

/-- **The Gibbs measure is gauge invariant** (strong `Measure.map`
form), at every real `β`, for every gauge transformation `g`. The
Stage 1 corpus proved this invariance for the torus reflection and
for torus shifts; here it is the gauge action itself, at Stage
0/1a's abstract `(Λ, G, σ, μG, ρ)`. The proof is the same transport:
the density is invariant and the base configuration measure is
invariant (Stage 0). -/
theorem gibbsMeasure_map_gaugeAction
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hσ : ∀ μ ν x, σ μ (σ ν x) = σ ν (σ μ x)) (g : Λ → G) (β : ℝ) :
    Measure.map (gaugeAction σ g) (gibbsMeasure σ μG ρ β)
      = gibbsMeasure σ μG ρ β := by
  ext s hs
  rw [Measure.map_apply (measurable_gaugeAction σ g) hs]
  unfold gibbsMeasure
  rw [Measure.smul_apply, Measure.smul_apply]
  have h1 : ((configMeasure μG : Measure (Config Λ G)).restrict s)
      = Measure.map (gaugeAction σ g)
          ((configMeasure μG : Measure (Config Λ G)).restrict
            (gaugeAction σ g ⁻¹' s)) := by
    rw [← Measure.restrict_map (measurable_gaugeAction σ g) hs,
      configMeasure_map_gaugeAction μG σ g]
  have key : (∫⁻ U, (gibbsDensity σ ρ β U : ℝ≥0∞)
        ∂((configMeasure μG : Measure (Config Λ G)).restrict
          (gaugeAction σ g ⁻¹' s)))
      = ∫⁻ U, (gibbsDensity σ ρ β U : ℝ≥0∞)
        ∂((configMeasure μG : Measure (Config Λ G)).restrict s) := by
    rw [h1, lintegral_map
      (measurable_coe_gibbsDensity σ ρ hρcont β)
      (measurable_gaugeAction σ g)]
    refine lintegral_congr fun U => ?_
    simp only [gibbsDensity_gaugeAction σ ρ hσ g β]
  have hwd : ((configMeasure μG : Measure (Config Λ G)).withDensity
        (fun U => (gibbsDensity σ ρ β U : ℝ≥0∞)))
        (gaugeAction σ g ⁻¹' s)
      = ((configMeasure μG : Measure (Config Λ G)).withDensity
        (fun U => (gibbsDensity σ ρ β U : ℝ≥0∞))) s := by
    rw [withDensity_apply _ (measurable_gaugeAction σ g hs),
      withDensity_apply _ hs]
    exact key
  rw [hwd]

/-- The **blocked Gibbs measure**: the pushforward of Stage 1a's
Gibbs measure at parameter `β` under the blocking map. At `β = 0`
it is the coarse Gibbs measure at `β = 0` (§5); at general `β` it
is a gauge-invariant probability measure on coarse configurations
which is *not* a coarse Wilson–Gibbs measure — see §7. -/
noncomputable def blockedGibbsMeasure (B : BlockingScheme σ σ')
    (β : ℝ) : Measure (Config Λ' G) :=
  blockedMeasure σ σ' B (gibbsMeasure σ μG ρ β)

/-- **Gauge invariance of the blocked Gibbs measure (strong form)**,
at every real `β` and every coarse gauge transformation. -/
theorem blockedGibbsMeasure_map_gaugeAction (B : BlockingScheme σ σ')
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hσ : ∀ μ ν x, σ μ (σ ν x) = σ ν (σ μ x)) (β : ℝ) (g' : Λ' → G) :
    Measure.map (gaugeAction σ' g') (blockedGibbsMeasure σ σ' μG ρ B β)
      = blockedGibbsMeasure σ σ' μG ρ B β :=
  blockedMeasure_map_gaugeAction σ σ' B
    (fun g => gibbsMeasure_map_gaugeAction σ μG ρ hρcont hσ g β) g'

/-- The blocked Gibbs measure is a probability measure. -/
theorem isProbabilityMeasure_blockedGibbsMeasure
    (B : BlockingScheme σ σ')
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hd : 0 < d)
    (β : ℝ) :
    IsProbabilityMeasure (blockedGibbsMeasure σ σ' μG ρ B β) := by
  haveI := isProbabilityMeasure_gibbsMeasure σ μG ρ hρcont hd β
  refine ⟨?_⟩
  show blockedGibbsMeasure σ σ' μG ρ B β Set.univ = 1
  unfold blockedGibbsMeasure blockedMeasure
  rw [Measure.map_apply (measurable_blockMap σ σ' B)
    MeasurableSet.univ, Set.preimage_univ, measure_univ]

end GibbsTransport

/-! ## §4. The β = 0 pushforward: blocked product Haar is product Haar

The computation has two factors. First the pair map, which reads
off the two fine links of each blocked edge: its pushforward of the
fine product measure is the product, over coarse links, of the
two-fold product measure (the pairs of fine links used by distinct
coarse links are pairwise disjoint — the parity law). Then the
pairwise product map `(u, v) ↦ u * v`, which preserves the Haar
probability measure by translation invariance. -/

section BetaZeroPushforward

variable {Λ Λ' : Type*} [Fintype Λ] [Fintype Λ']
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
variable (σ : Fin 4 → Equiv.Perm Λ) (σ' : Fin 4 → Equiv.Perm Λ')
variable (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]

/-- Pairwise multiplication preserves the product of the Haar
probability measure with itself: a product of two independent
Haar variables is Haar. -/
theorem measurePreserving_mul_pair :
    MeasurePreserving (fun p : G × G => p.1 * p.2) (μG.prod μG) μG := by
  have hmul : Measurable (fun p : G × G => p.1 * p.2) :=
    (continuous_fst.mul continuous_snd).measurable
  refine ⟨hmul, ?_⟩
  ext s hs
  rw [Measure.map_apply hmul hs, Measure.prod_apply (hmul hs)]
  have hsec : ∀ x : G,
      μG (Prod.mk x ⁻¹' ((fun p : G × G => p.1 * p.2) ⁻¹' s))
        = μG s := by
    intro x
    have heq : Prod.mk x ⁻¹' ((fun p : G × G => p.1 * p.2) ⁻¹' s)
        = (x * ·) ⁻¹' s := rfl
    rw [heq, ← Measure.map_apply (measurable_const_mul x) hs,
      map_mul_left_eq_self]
  trans ∫⁻ _x : G, μG s ∂μG
  · exact lintegral_congr hsec
  · simp [lintegral_const]

/-- The pair map: the two fine links of each blocked edge, read off
a fine configuration. -/
def pairMap (B : BlockingScheme σ σ') (U : Config Λ G) :
    Link Λ' → G × G :=
  fun ℓ' => (U (fineLinkA σ σ' B ℓ'), U (fineLinkB σ σ' B ℓ'))

/-- The pair map is measurable. -/
theorem measurable_pairMap (B : BlockingScheme σ σ') :
    Measurable (pairMap σ σ' B : Config Λ G → (Link Λ' → G × G)) :=
  measurable_pi_iff.mpr fun ℓ' =>
    (measurable_pi_apply (fineLinkA σ σ' B ℓ')).prodMk
      (measurable_pi_apply (fineLinkB σ σ' B ℓ'))

/-- **The pair map's pushforward is the pair-product measure.**
Distinct coarse links consume pairwise disjoint pairs of fine
links (injectivity on each factor, parity across factors), so the
fine product measure pushes forward to the product over coarse
links of `μG × μG`. Proved by the π-system characterization of
product measures, testing on rectangles. -/
theorem pi_eq_map_pairMap (B : BlockingScheme σ σ') :
    Measure.pi (fun _ : Link Λ' => μG.prod μG)
      = Measure.map (pairMap σ σ' B) (configMeasure μG) := by
  classical
  refine MeasureTheory.Measure.pi_eq_generateFrom
    (C := fun _ : Link Λ' => Set.image2 (· ×ˢ ·)
      {s : Set G | MeasurableSet s} {t : Set G | MeasurableSet t})
    (fun _ => generateFrom_prod) (fun _ => isPiSystem_prod)
    (fun _ => Measure.FiniteSpanningSetsIn.prod
      μG.toFiniteSpanningSetsIn μG.toFiniteSpanningSetsIn) ?_
  intro t ht
  have hex : ∀ ℓ', ∃ A B : Set G, MeasurableSet A ∧ MeasurableSet B
      ∧ A ×ˢ B = t ℓ' := by
    intro ℓ'
    have h := ht ℓ'
    rw [Set.mem_image2] at h
    obtain ⟨A, hA, B, hB, hAB⟩ := h
    exact ⟨A, B, hA, hB, hAB⟩
  choose A Bset hA hB hAB using hex
  -- The fine rectangle: `A` on first-factor links, `B` on
  -- second-factor links, everything elsewhere.
  set s : Link Λ → Set G := fun ℓ =>
    if h : ∃ ℓ', fineLinkA σ σ' B ℓ' = ℓ then A (Classical.choose h)
    else if h' : ∃ ℓ', fineLinkB σ σ' B ℓ' = ℓ then Bset (Classical.choose h')
    else Set.univ with hs
  have hsA : ∀ ℓ', s (fineLinkA σ σ' B ℓ') = A ℓ' := by
    intro ℓ'
    have hex' : ∃ ℓ'', fineLinkA σ σ' B ℓ'' = fineLinkA σ σ' B ℓ' := ⟨ℓ', rfl⟩
    have hchoose : Classical.choose hex' = ℓ' :=
      fineLinkA_injective σ σ' B (Classical.choose_spec hex')
    calc s (fineLinkA σ σ' B ℓ') = A (Classical.choose hex') := dif_pos hex'
      _ = A ℓ' := by rw [hchoose]
  have hsB : ∀ ℓ', s (fineLinkB σ σ' B ℓ') = Bset ℓ' := by
    intro ℓ'
    have hnex : ¬ ∃ ℓ'', fineLinkA σ σ' B ℓ'' = fineLinkB σ σ' B ℓ' := by
      push_neg
      exact fun ℓ'' => fineLinkA_ne_fineLinkB σ σ' B ℓ'' ℓ'
    have hex' : ∃ ℓ'', fineLinkB σ σ' B ℓ'' = fineLinkB σ σ' B ℓ' := ⟨ℓ', rfl⟩
    have hchoose : Classical.choose hex' = ℓ' :=
      fineLinkB_injective σ σ' B (Classical.choose_spec hex')
    calc s (fineLinkB σ σ' B ℓ')
        = (if h' : ∃ ℓ'', fineLinkB σ σ' B ℓ'' = fineLinkB σ σ' B ℓ'
            then Bset (Classical.choose h') else Set.univ) := dif_neg hnex
      _ = Bset (Classical.choose hex') := dif_pos hex'
      _ = Bset ℓ' := by rw [hchoose]
  have hsO : ∀ ℓ : Link Λ, (∀ ℓ', fineLinkA σ σ' B ℓ' ≠ ℓ)
      → (∀ ℓ', fineLinkB σ σ' B ℓ' ≠ ℓ) → s ℓ = Set.univ := by
    intro ℓ hA' hB'
    have hnex1 : ¬ ∃ ℓ', fineLinkA σ σ' B ℓ' = ℓ := by
      push_neg
      exact hA'
    have hnex2 : ¬ ∃ ℓ', fineLinkB σ σ' B ℓ' = ℓ := by
      push_neg
      exact hB'
    calc s ℓ = (if h' : ∃ ℓ'', fineLinkB σ σ' B ℓ'' = ℓ
          then Bset (Classical.choose h') else Set.univ) := dif_neg hnex1
      _ = Set.univ := dif_neg hnex2
  have hpre : pairMap σ σ' B ⁻¹' (Set.pi Set.univ t) = Set.pi Set.univ s := by
    ext U
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ,
      forall_const]
    constructor
    · intro h ℓ
      by_cases hAℓ : ∃ ℓ', fineLinkA σ σ' B ℓ' = ℓ
      · obtain ⟨ℓ', hℓ'⟩ := hAℓ
        have hmem := h ℓ'
        rw [← hAB ℓ'] at hmem
        rw [← hℓ', hsA]
        exact (Set.mem_prod.mp hmem).1
      · by_cases hBℓ : ∃ ℓ', fineLinkB σ σ' B ℓ' = ℓ
        · obtain ⟨ℓ', hℓ'⟩ := hBℓ
          have hmem := h ℓ'
          rw [← hAB ℓ'] at hmem
          rw [← hℓ', hsB]
          exact (Set.mem_prod.mp hmem).2
        · have hAn : ∀ ℓ', fineLinkA σ σ' B ℓ' ≠ ℓ := by
            push_neg at hAℓ
            exact hAℓ
          have hBn : ∀ ℓ', fineLinkB σ σ' B ℓ' ≠ ℓ := by
            push_neg at hBℓ
            exact hBℓ
          rw [hsO ℓ hAn hBn]
          exact Set.mem_univ _
    · intro h ℓ'
      have h1 := h (fineLinkA σ σ' B ℓ')
      rw [hsA] at h1
      have h2 := h (fineLinkB σ σ' B ℓ')
      rw [hsB] at h2
      rw [← hAB ℓ']
      exact Set.mk_mem_prod h1 h2
  have htmeas : ∀ ℓ', MeasurableSet (t ℓ') := fun ℓ' => by
    rw [← hAB ℓ']
    exact MeasurableSet.prod (hA ℓ') (hB ℓ')
  rw [Measure.map_apply (measurable_pairMap σ σ' B)
    ((measurableSet_pi Set.countable_univ).mpr
      (Or.inl fun ℓ' _ => htmeas ℓ')), hpre,
    show configMeasure μG = Measure.pi (fun _ : Link Λ => μG) from rfl,
    MeasureTheory.Measure.pi_pi]
  -- Split the fine product over the two disjoint used-link images.
  classical
  set usedA : Finset (Link Λ) := Finset.univ.image (fineLinkA σ σ' B)
    with husedA
  set usedB : Finset (Link Λ) := Finset.univ.image (fineLinkB σ σ' B)
    with husedB
  have hdisj : Disjoint usedA usedB := by
    rw [Finset.disjoint_left]
    intro ℓ hℓA hℓB
    rw [husedA, Finset.mem_image] at hℓA
    rw [husedB, Finset.mem_image] at hℓB
    obtain ⟨ℓ₁, _, hℓ₁⟩ := hℓA
    obtain ⟨ℓ₂, _, hℓ₂⟩ := hℓB
    exact fineLinkA_ne_fineLinkB σ σ' B ℓ₁ ℓ₂ (hℓ₁.trans hℓ₂.symm)
  calc ∏ ℓ, μG (s ℓ)
      = ∏ ℓ ∈ usedA ∪ usedB, μG (s ℓ) := by
        refine (Finset.prod_subset (Finset.subset_univ _) ?_).symm
        intro ℓ _ hℓ
        have hnotA : ∀ ℓ', fineLinkA σ σ' B ℓ' ≠ ℓ := by
          intro ℓ' hcon
          apply hℓ
          rw [Finset.mem_union]
          left
          rw [husedA, Finset.mem_image]
          exact ⟨ℓ', Finset.mem_univ ℓ', hcon⟩
        have hnotB : ∀ ℓ', fineLinkB σ σ' B ℓ' ≠ ℓ := by
          intro ℓ' hcon
          apply hℓ
          rw [Finset.mem_union]
          right
          rw [husedB, Finset.mem_image]
          exact ⟨ℓ', Finset.mem_univ ℓ', hcon⟩
        rw [hsO ℓ hnotA hnotB, measure_univ]
    _ = (∏ ℓ ∈ usedA, μG (s ℓ)) * (∏ ℓ ∈ usedB, μG (s ℓ)) :=
        Finset.prod_union hdisj
    _ = (∏ ℓ', μG (A ℓ')) * (∏ ℓ', μG (Bset ℓ')) := by
        congr 1
        · rw [husedA, Finset.prod_image
            (fun x _ y _ h => fineLinkA_injective σ σ' B h)]
          exact Finset.prod_congr rfl fun ℓ' _ => by rw [hsA]
        · rw [husedB, Finset.prod_image
            (fun x _ y _ h => fineLinkB_injective σ σ' B h)]
          exact Finset.prod_congr rfl fun ℓ' _ => by rw [hsB]
    _ = ∏ ℓ', (μG (A ℓ') * μG (Bset ℓ')) := Finset.prod_mul_distrib.symm
    _ = ∏ ℓ', (μG.prod μG) (t ℓ') := by
        exact Finset.prod_congr rfl fun ℓ' _ => by
          rw [← hAB ℓ', Measure.prod_prod]

/-- **The β = 0 pushforward (headline of the stage's free point).**
The pushforward of the fine product Haar measure under the blocking
map is the coarse product Haar measure: a blocked link is a product
of two independent Haar variables (hence Haar), and blocked links
over distinct coarse links are independent (disjoint fine pairs). -/
theorem blockedMeasure_configMeasure (B : BlockingScheme σ σ') :
    blockedMeasure σ σ' B (configMeasure μG) = configMeasure μG := by
  have hmul : Measurable
      (fun V : Link Λ' → G × G => fun ℓ' => (V ℓ').1 * (V ℓ').2) :=
    measurable_pi_iff.mpr fun ℓ' =>
      (continuous_fst.mul continuous_snd).measurable.comp
        (measurable_pi_apply ℓ')
  have hcomp : (fun V : Link Λ' → G × G =>
        fun ℓ' => (V ℓ').1 * (V ℓ').2) ∘ pairMap σ σ' B
      = blockMap σ σ' B := by
    funext U ℓ'
    rfl
  unfold blockedMeasure
  rw [← hcomp, ← Measure.map_map hmul (measurable_pairMap σ σ' B),
    ← pi_eq_map_pairMap σ σ' μG B]
  exact (measurePreserving_pi (fun _ : Link Λ' => μG.prod μG)
    (fun _ : Link Λ' => μG)
    (fun _ => measurePreserving_mul_pair μG)).map_eq

end BetaZeroPushforward

/-! ## §5. β = 0 transports and the fixed families

At `β = 0` the blocked theory *is* the coarse theory: the blocked
Gibbs measure at `β = 0` is the coarse Gibbs measure at `β = 0`, and
every `β = 0` expectation computed with blocked observables equals
the coarse expectation — in particular the Stage-0 plaquette package
(the Haar intertwiner value, and its vanishing form) transports
verbatim. -/

section BetaZeroTransports

variable {Λ Λ' : Type*} [Fintype Λ] [Fintype Λ']
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
variable (σ : Fin 4 → Equiv.Perm Λ) (σ' : Fin 4 → Equiv.Perm Λ')
variable (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
variable {d : ℕ} (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ))

/-- **The β = 0 Gibbs fixed family.** The blocked Gibbs measure at
`β = 0` is the coarse Gibbs measure at `β = 0`: the `β = 0` theory
is a fixed point of the blocking, at every volume, for every
representation. -/
theorem blockedGibbsMeasure_zero (B : BlockingScheme σ σ') :
    blockedGibbsMeasure σ σ' μG ρ B 0 = gibbsMeasure σ' μG ρ 0 := by
  unfold blockedGibbsMeasure
  rw [gibbsMeasure_zero σ μG ρ, gibbsMeasure_zero σ' μG ρ,
    blockedMeasure_configMeasure σ σ' μG B]

/-- **Expectation transport at β = 0** (for strongly measurable
observables): the coarse Gibbs expectation of `F` is the fine Gibbs
expectation of `F` pulled back along the blocking map. -/
theorem gibbsExpect_zero_blocked
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hd : 0 < d)
    (B : BlockingScheme σ σ') (F : Config Λ' G → ℂ)
    (hF : AEStronglyMeasurable F (blockedGibbsMeasure σ σ' μG ρ B 0)) :
    gibbsExpect σ' μG ρ 0 F
      = gibbsExpect σ μG ρ 0 (F ∘ blockMap σ σ' B) := by
  rw [gibbsExpect_eq_integral σ' μG ρ hρcont hd 0 F,
    gibbsExpect_eq_integral σ μG ρ hρcont hd 0 (F ∘ blockMap σ σ' B),
    ← blockedGibbsMeasure_zero σ σ' μG ρ B]
  exact integral_map (measurable_blockMap σ σ' B).aemeasurable hF

/-- The measurability input for the plaquette observable's
transport: its trace is a finite sum of matrix entries. -/
theorem aestronglyMeasurable_trace_plaquette
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (B : BlockingScheme σ σ') (y : Λ') (μ ν : Fin 4) :
    AEStronglyMeasurable
      (fun V : Config Λ' G => Matrix.trace
        (repMatrix ρ (plaquette σ' V y μ ν)))
      (blockedGibbsMeasure σ σ' μG ρ B 0) :=
  (Finset.measurable_sum _ fun i _ =>
    measurable_repMatrix_plaquette_entry σ' ρ hρcont y μ ν i i
    ).aestronglyMeasurable

/-- **Transport of the β = 0 plaquette package.** The fine Gibbs
expectation at `β = 0` of the blocked plaquette observable is the
trace of the Haar intertwiner — the Stage-0 value, verbatim, read
through the block map. -/
theorem gibbsExpect_zero_blocked_plaquette
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hd : 0 < d)
    (B : BlockingScheme σ σ') (y : Λ') {μ ν : Fin 4} (hμν : μ ≠ ν)
    (hμy : σ' μ y ≠ y) (hνy : σ' ν y ≠ y) :
    gibbsExpect σ μG ρ 0
        (fun U => Matrix.trace
          (repMatrix ρ (plaquette σ' (blockMap σ σ' B U) y μ ν)))
      = Matrix.trace (haarIntertwiner μG ρ) := by
  calc gibbsExpect σ μG ρ 0
        (fun U => Matrix.trace
          (repMatrix ρ (plaquette σ' (blockMap σ σ' B U) y μ ν)))
      = gibbsExpect σ' μG ρ 0
          (fun V => Matrix.trace
            (repMatrix ρ (plaquette σ' V y μ ν))) :=
        (gibbsExpect_zero_blocked σ σ' μG ρ hρcont hd B _
          (aestronglyMeasurable_trace_plaquette σ σ' μG ρ hρcont B y μ ν)
          ).symm
    _ = Matrix.trace (haarIntertwiner μG ρ) :=
        gibbsExpect_zero_plaquette σ' μG ρ hρcont y hμν hμy hνy

/-- **Transport of the vanishing form.** When `ρ` has no nonzero
fixed vectors, the blocked plaquette expectation at `β = 0` is `0`. -/
theorem gibbsExpect_zero_blocked_plaquette_eq_zero
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hd : 0 < d)
    (B : BlockingScheme σ σ') (y : Λ') {μ ν : Fin 4} (hμν : μ ≠ ν)
    (hμy : σ' μ y ≠ y) (hνy : σ' ν y ≠ y)
    (h : ∀ v : Fin d → ℂ, (∀ g : G, repMatrix ρ g *ᵥ v = v)
      → v = 0) :
    gibbsExpect σ μG ρ 0
        (fun U => Matrix.trace
          (repMatrix ρ (plaquette σ' (blockMap σ σ' B U) y μ ν)))
      = 0 := by
  calc gibbsExpect σ μG ρ 0
        (fun U => Matrix.trace
          (repMatrix ρ (plaquette σ' (blockMap σ σ' B U) y μ ν)))
      = gibbsExpect σ' μG ρ 0
          (fun V => Matrix.trace
            (repMatrix ρ (plaquette σ' V y μ ν))) :=
        (gibbsExpect_zero_blocked σ σ' μG ρ hρcont hd B _
          (aestronglyMeasurable_trace_plaquette σ σ' μG ρ hρcont B y μ ν)
          ).symm
    _ = 0 := gibbsExpect_zero_plaquette_eq_zero σ' μG ρ hρcont y hμν
        hμy hνy h

end BetaZeroTransports

section DiracFixedPoint

variable {Λ Λ' : Type*} [Fintype Λ] [Fintype Λ']
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  [MeasurableSingletonClass G]
variable (σ : Fin 4 → Equiv.Perm Λ) (σ' : Fin 4 → Equiv.Perm Λ')

/-- **The trivial-configuration fixed family.** The Dirac measure
at the constant-`1` configuration is fixed by blocking: blocking
the trivial configuration gives the trivial configuration
(`blockMap_one`). -/
theorem blockedMeasure_dirac_one (B : BlockingScheme σ σ') :
    blockedMeasure σ σ' B
        (Measure.dirac (fun _ : Link Λ => (1 : G)))
      = Measure.dirac (fun _ : Link Λ' => (1 : G)) := by
  unfold blockedMeasure
  rw [Measure.map_dirac, blockMap_one]

end DiracFixedPoint

/-! ## §6. Consistency: integrals, loops, Elitzur, non-factoring

Integrals against a blocked measure are integrals of the pulled-back
observable against the fine measure — at *every* `β`, by definition
of the pushforward. Closed coarse loops are fine loops with every
step doubled. Elitzur's theorem transports to the blocked theory:
the blocked measure's gauge invariance (§3) drives the same
fixed-vector argument Stage 1a runs on the Gibbs measure. And the
blocking is genuinely many-to-one: a single fine-link observable
does not factor through the blocked configuration. -/

section Consistency

variable {Λ Λ' : Type*} [Fintype Λ] [Fintype Λ'] [DecidableEq Λ]
  [DecidableEq Λ']
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
variable (σ : Fin 4 → Equiv.Perm Λ) (σ' : Fin 4 → Equiv.Perm Λ')
variable (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
variable {d : ℕ} (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ))

/-- Integrals against a blocked measure are integrals of the
pullback (Bochner form). -/
theorem integral_blockedMeasure {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (μ : Measure (Config Λ G))
    (B : BlockingScheme σ σ') (F : Config Λ' G → E)
    (hF : AEStronglyMeasurable F (blockedMeasure σ σ' B μ)) :
    ∫ V, F V ∂(blockedMeasure σ σ' B μ)
      = ∫ U, F (blockMap σ σ' B U) ∂μ :=
  integral_map (measurable_blockMap σ σ' B).aemeasurable hF

/-- Integrals against the blocked Gibbs measure are integrals of
the pullback against the fine Gibbs measure — at every `β`. -/
theorem integral_blockedGibbsMeasure {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (B : BlockingScheme σ σ') (β : ℝ)
    (F : Config Λ' G → E)
    (hF : AEStronglyMeasurable F
      (blockedGibbsMeasure σ σ' μG ρ B β)) :
    ∫ V, F V ∂(blockedGibbsMeasure σ σ' μG ρ B β)
      = ∫ U, F (blockMap σ σ' B U) ∂(gibbsMeasure σ μG ρ β) :=
  integral_blockedMeasure σ σ' (gibbsMeasure σ μG ρ β) B F hF

/-- Integrability of a blocked-side matrix entry against the
blocked Gibbs measure (unitary entries are bounded by `1`). -/
theorem integrable_blocked_entry
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hd : 0 < d)
    (B : BlockingScheme σ σ') (β : ℝ) (ℓ₀ : Link Λ') (i j : Fin d) :
    Integrable (fun V => repMatrix ρ (V ℓ₀) i j)
      (blockedGibbsMeasure σ σ' μG ρ B β) := by
  haveI := isProbabilityMeasure_blockedGibbsMeasure σ σ' μG ρ B
    hρcont hd β
  refine Integrable.of_bound
    (Measurable.aestronglyMeasurable
      (measurable_repMatrix_entry_of_measurable ρ hρcont _
        (measurable_pi_apply ℓ₀) i j)) 1 ?_
  exact ae_of_all _ fun V =>
    abs_entry_of_mem_unitaryGroup (repMatrix_mem ρ (V ℓ₀)) i j

/-- The blocked-side Elitzur identity: the blocked single-link
expectation matrix `E` satisfies `E = ρ(h) * E` for every `h` —
Stage 1a's intertwiner identity, driven by the blocked measure's
gauge invariance (§3) instead of the Gibbs measure's. -/
theorem blocked_expect_entry_eq
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hd : 0 < d)
    (hσ : ∀ μ ν x, σ μ (σ ν x) = σ ν (σ μ x))
    (B : BlockingScheme σ σ') (β : ℝ) (y₀ : Λ') (μ₀ : Fin 4)
    (hne2 : σ' μ₀ y₀ ≠ y₀) (h : G) (i j : Fin d) :
    ∫ V, repMatrix ρ (V (y₀, μ₀)) i j
        ∂(blockedGibbsMeasure σ σ' μG ρ B β)
      = ∑ k, repMatrix ρ h i k *
          ∫ V, repMatrix ρ (V (y₀, μ₀)) k j
            ∂(blockedGibbsMeasure σ σ' μG ρ B β) := by
  classical
  haveI := isProbabilityMeasure_blockedGibbsMeasure σ σ' μG ρ B
    hρcont hd β
  set ν := blockedGibbsMeasure σ σ' μG ρ B β with hν
  set g' := Function.update (1 : Λ' → G) y₀ h with hg'
  have hfactor : ∀ V : Config Λ' G,
      (gaugeAction σ' g' V) (y₀, μ₀) = h * V (y₀, μ₀) := by
    intro V
    have h1 : g' y₀ = h := by
      rw [hg', Function.update_apply, if_pos rfl]
    have h2 : g' (σ' μ₀ y₀) = 1 := by
      rw [hg', Function.update_apply, if_neg hne2, Pi.one_apply]
    rw [gaugeAction_apply, h1, h2, inv_one, mul_one]
  have hmeas : ∀ a b, Measurable fun V : Config Λ' G =>
      repMatrix ρ (V (y₀, μ₀)) a b := fun a b =>
    measurable_repMatrix_entry_of_measurable ρ hρcont _
      (measurable_pi_apply (y₀, μ₀)) a b
  have hInt : ∀ a b, Integrable (fun V => repMatrix ρ (V (y₀, μ₀)) a b)
      ν := fun a b => integrable_blocked_entry σ σ' μG ρ hρcont hd B β
        (y₀, μ₀) a b
  calc ∫ V, repMatrix ρ (V (y₀, μ₀)) i j ∂ν
      = ∫ V, repMatrix ρ (V (y₀, μ₀)) i j
          ∂(ν.map (gaugeAction σ' g')) := by
        have hinv := blockedGibbsMeasure_map_gaugeAction σ σ' μG ρ B
          hρcont hσ β g'
        rw [← hν] at hinv
        rw [hinv]
    _ = ∫ V, repMatrix ρ ((gaugeAction σ' g' V) (y₀, μ₀)) i j ∂ν := by
        refine integral_map (measurable_gaugeAction σ' g').aemeasurable ?_
        have hinv := blockedGibbsMeasure_map_gaugeAction σ σ' μG ρ B
          hρcont hσ β g'
        rw [← hν] at hinv
        rw [hinv]
        exact (hInt i j).aestronglyMeasurable
    _ = ∫ V, ∑ k, repMatrix ρ h i k * repMatrix ρ (V (y₀, μ₀)) k j
          ∂ν := by
        refine integral_congr_ae (ae_of_all _ fun V => ?_)
        show repMatrix ρ ((gaugeAction σ' g' V) (y₀, μ₀)) i j
          = ∑ k, repMatrix ρ h i k * repMatrix ρ (V (y₀, μ₀)) k j
        rw [hfactor V, repMatrix_mul]
        exact Matrix.mul_apply
    _ = ∑ k, repMatrix ρ h i k *
          ∫ V, repMatrix ρ (V (y₀, μ₀)) k j ∂ν := by
        rw [integral_finset_sum _ fun k _ =>
          (hInt k j).const_mul (repMatrix ρ h i k)]
        exact Finset.sum_congr rfl fun k _ =>
          integral_const_mul (repMatrix ρ h i k) _

/-- **Elitzur transported to the blocked theory.** The blocked
single-link expectation matrix vanishes at every `β`, for every
blocking scheme, when `ρ` has no nonzero fixed vectors: no local
gauge-variant observable acquires an expectation in the blocked
theory either. -/
theorem blocked_singleLink_expect_eq_zero
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hd : 0 < d)
    (hσ : ∀ μ ν x, σ μ (σ ν x) = σ ν (σ μ x))
    (hfixed : ∀ v : Fin d → ℂ, (∀ g : G, repMatrix ρ g *ᵥ v = v)
      → v = 0)
    (B : BlockingScheme σ σ') (β : ℝ) (y₀ : Λ') (μ₀ : Fin 4)
    (hne2 : σ' μ₀ y₀ ≠ y₀) :
    Matrix.of (fun i j => ∫ V, repMatrix ρ (V (y₀, μ₀)) i j
        ∂(blockedGibbsMeasure σ σ' μG ρ B β)) = 0 := by
  apply Matrix.ext
  intro i j
  have hcol := hfixed (fun i => ∫ V, repMatrix ρ (V (y₀, μ₀)) i j
    ∂(blockedGibbsMeasure σ σ' μG ρ B β)) (fun h => by
    funext a
    have hE := blocked_expect_entry_eq σ σ' μG ρ hρcont hd hσ B β y₀
      μ₀ hne2 h a j
    show (∑ k, repMatrix ρ h a k *
        ∫ V, repMatrix ρ (V (y₀, μ₀)) k j
          ∂(blockedGibbsMeasure σ σ' μG ρ B β))
      = ∫ V, repMatrix ρ (V (y₀, μ₀)) a j
          ∂(blockedGibbsMeasure σ σ' μG ρ B β)
    exact hE.symm)
  have hzero_entry := congrFun hcol i
  simpa [Matrix.of_apply] using hzero_entry

/-- **Elitzur for blocked observables, fine side.** The Stage-1a
expectation matrix of a blocked single-link observable vanishes at
every `β`: the fine avatar of the blocked Elitzur theorem. -/
theorem expectMatrix_blocked_singleLink_eq_zero
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hd : 0 < d)
    (hσ : ∀ μ ν x, σ μ (σ ν x) = σ ν (σ μ x))
    (hfixed : ∀ v : Fin d → ℂ, (∀ g : G, repMatrix ρ g *ᵥ v = v)
      → v = 0)
    (B : BlockingScheme σ σ') (β : ℝ) (y₀ : Λ') (μ₀ : Fin 4)
    (hne2 : σ' μ₀ y₀ ≠ y₀) :
    expectMatrix σ μG ρ β (fun U => blockMap σ σ' B U (y₀, μ₀)) = 0 := by
  apply Matrix.ext
  intro i j
  rw [expectMatrix_apply,
    gibbsExpect_eq_integral σ μG ρ hρcont hd β, Matrix.zero_apply]
  have hzero := blocked_singleLink_expect_eq_zero σ σ' μG ρ hρcont
    hd hσ hfixed B β y₀ μ₀ hne2
  have hentry : ∫ V, repMatrix ρ (V (y₀, μ₀)) i j
      ∂(blockedGibbsMeasure σ σ' μG ρ B β) = 0 := by
    have h := congrFun (congrFun hzero i) j
    simpa [Matrix.of_apply] using h
  rw [← hentry]
  exact (integral_blockedGibbsMeasure σ σ' μG ρ B β _
    (Measurable.aestronglyMeasurable
      (measurable_repMatrix_entry_of_measurable ρ hρcont _
        (measurable_pi_apply (y₀, μ₀)) i j))).symm

end Consistency

section NonFactoring

variable {Λ Λ' : Type*} [Fintype Λ] [Fintype Λ'] {G : Type*} [Group G]
variable (σ : Fin 4 → Equiv.Perm Λ) (σ' : Fin 4 → Equiv.Perm Λ')

/-- **Non-factoring (the blocking is many-to-one).** A single
fine-link observable does *not* factor through the blocking map:
two fine configurations with the same blocked image — the constant
`1` configuration, and one carrying `c ≠ 1` on the first link of a
blocked pair and `c⁻¹` on the second — take different values on it.
Single-link physics is exactly what blocking integrates out. -/
theorem singleLink_not_factor_blockMap [Nontrivial G]
    (B : BlockingScheme σ σ') (ℓ₀ : Link Λ') :
    ¬ ∃ F : Config Λ' G → G, ∀ U : Config Λ G,
      U (fineLinkA σ σ' B ℓ₀) = F (blockMap σ σ' B U) := by
  classical
  intro ⟨F, hF⟩
  obtain ⟨c, hc⟩ : ∃ c : G, c ≠ 1 := exists_ne 1
  have hab : fineLinkA σ σ' B ℓ₀ ≠ fineLinkB σ σ' B ℓ₀ :=
    fineLinkA_ne_fineLinkB σ σ' B ℓ₀ ℓ₀
  have hU₂a : Function.update
        (Function.update (fun _ => (1 : G)) (fineLinkA σ σ' B ℓ₀) c)
        (fineLinkB σ σ' B ℓ₀) c⁻¹ (fineLinkA σ σ' B ℓ₀) = c := by
    rw [Function.update_apply, Function.update_apply, if_neg hab,
      if_pos rfl]
  have hU₂b : Function.update
        (Function.update (fun _ => (1 : G)) (fineLinkA σ σ' B ℓ₀) c)
        (fineLinkB σ σ' B ℓ₀) c⁻¹ (fineLinkB σ σ' B ℓ₀) = c⁻¹ := by
    rw [Function.update_apply, if_pos rfl]
  have hblock : blockMap σ σ' B
        (Function.update
          (Function.update (fun _ => (1 : G)) (fineLinkA σ σ' B ℓ₀) c)
          (fineLinkB σ σ' B ℓ₀) c⁻¹)
      = blockMap σ σ' B (fun _ => (1 : G)) := by
    funext ⟨y, μ⟩
    rw [blockMap_apply, blockMap_apply]
    by_cases hℓ₀ : (y, μ) = ℓ₀
    · subst hℓ₀
      have hU₂a' : Function.update
            (Function.update (fun _ => (1 : G))
              (fineLinkA σ σ' B (y, μ)) c)
            (fineLinkB σ σ' B (y, μ)) c⁻¹ (B.ι y, μ) = c := hU₂a
      have hU₂b' : Function.update
            (Function.update (fun _ => (1 : G))
              (fineLinkA σ σ' B (y, μ)) c)
            (fineLinkB σ σ' B (y, μ)) c⁻¹ ((σ μ) (B.ι y), μ)
          = c⁻¹ := hU₂b
      rw [hU₂a', hU₂b', mul_inv_cancel]
      show (1 : G) = 1 * 1
      exact (mul_one 1).symm
    · have hA : Function.update
          (Function.update (fun _ => (1 : G)) (fineLinkA σ σ' B ℓ₀) c)
          (fineLinkB σ σ' B ℓ₀) c⁻¹ (fineLinkA σ σ' B (y, μ)) = 1 := by
        rw [Function.update_apply, Function.update_apply,
          if_neg (fineLinkA_ne_fineLinkB σ σ' B (y, μ) ℓ₀),
          if_neg (fun hh => hℓ₀ (fineLinkA_injective σ σ' B hh))]
      have hB : Function.update
          (Function.update (fun _ => (1 : G)) (fineLinkA σ σ' B ℓ₀) c)
          (fineLinkB σ σ' B ℓ₀) c⁻¹ (fineLinkB σ σ' B (y, μ)) = 1 := by
        rw [Function.update_apply, Function.update_apply,
          if_neg (fun hh => hℓ₀ (fineLinkB_injective σ σ' B hh)),
          if_neg (fineLinkB_ne_fineLinkA σ σ' B (y, μ) ℓ₀)]
      have hA' : Function.update
            (Function.update (fun _ => (1 : G)) (fineLinkA σ σ' B ℓ₀) c)
            (fineLinkB σ σ' B ℓ₀) c⁻¹ (B.ι y, μ) = 1 := hA
      have hB' : Function.update
            (Function.update (fun _ => (1 : G)) (fineLinkA σ σ' B ℓ₀) c)
            (fineLinkB σ σ' B ℓ₀) c⁻¹ ((σ μ) (B.ι y), μ) = 1 := hB
      rw [hA', hB']
  have h1 : (1 : G) = F (blockMap σ σ' B (fun _ => (1 : G))) :=
    hF (fun _ => (1 : G))
  have h2 := hF (Function.update
    (Function.update (fun _ => (1 : G)) (fineLinkA σ σ' B ℓ₀) c)
    (fineLinkB σ σ' B ℓ₀) c⁻¹)
  rw [hblock, hU₂a] at h2
  exact hc (h2.trans h1.symm)

end NonFactoring

section LoopDoubling

variable {Λ Λ' : Type*} [Fintype Λ] [Fintype Λ'] {G : Type*} [Group G]
variable (σ : Fin 4 → Equiv.Perm Λ) (σ' : Fin 4 → Equiv.Perm Λ')
variable {d : ℕ} (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ))

/-- The doubled step list: every coarse step replaced by the two
consecutive fine steps that traverse its blocked link. -/
def doubleStep (B : BlockingScheme σ σ') : List Step → List Step
  | [] => []
  | Step.fwd μ :: rest => Step.fwd μ :: Step.fwd μ :: doubleStep B rest
  | Step.bwd μ :: rest => Step.bwd μ :: Step.bwd μ :: doubleStep B rest

/-- **Loop doubling.** The doubled fine loop based at the coarse
site `B.ι x` ends at the coarse image of the coarse loop's end, and
its ordered product is the blocked configuration's coarse loop
product: coarse Wilson loops are fine Wilson loops of doubled
paths, exactly. -/
theorem loopEnd_loopProd_doubleStep (B : BlockingScheme σ σ')
    (U : Config Λ G) (x : Λ') (steps : List Step) :
    loopEnd σ (B.ι x) (doubleStep σ σ' B steps)
        = B.ι (loopEnd σ' x steps)
      ∧ loopProd σ U (B.ι x) (doubleStep σ σ' B steps)
        = loopProd σ' (blockMap σ σ' B U) x steps := by
  induction steps generalizing x with
  | nil => exact ⟨rfl, rfl⟩
  | cons s steps ih =>
    cases s with
    | fwd μ =>
      constructor
      · simp only [doubleStep, loopEnd_cons]
        show loopEnd σ (σ μ (σ μ (B.ι x))) (doubleStep σ σ' B steps)
            = B.ι (loopEnd σ' (σ' μ x) steps)
        rw [B.twoStep μ x]
        exact (ih (σ' μ x)).1
      · simp only [doubleStep, loopProd_cons]
        show U (B.ι x, μ) * (U (σ μ (B.ι x), μ)
            * loopProd σ U (σ μ (σ μ (B.ι x)))
              (doubleStep σ σ' B steps))
          = (blockMap σ σ' B U) (x, μ)
            * loopProd σ' (blockMap σ σ' B U) (σ' μ x) steps
        rw [blockMap_apply, B.twoStep μ x, (ih (σ' μ x)).2, mul_assoc]
    | bwd μ =>
      have h2 := B.twoStep μ ((σ' μ).symm x)
      rw [Equiv.apply_symm_apply] at h2
      have e1 : (σ μ).symm (B.ι x) = σ μ (B.ι ((σ' μ).symm x)) := by
        have h3 := congrArg (σ μ).symm h2
        rw [Equiv.symm_apply_apply] at h3
        exact h3.symm
      have e2 : (σ μ).symm ((σ μ).symm (B.ι x))
          = B.ι ((σ' μ).symm x) := by
        calc (σ μ).symm ((σ μ).symm (B.ι x))
            = (σ μ).symm ((σ μ).symm
                (σ μ (σ μ (B.ι ((σ' μ).symm x))))) := by rw [h2]
          _ = B.ι ((σ' μ).symm x) := by
              simp [Equiv.symm_apply_apply]
      constructor
      · simp only [doubleStep, loopEnd_cons]
        show loopEnd σ ((σ μ).symm ((σ μ).symm (B.ι x)))
            (doubleStep σ σ' B steps)
          = B.ι (loopEnd σ' ((σ' μ).symm x) steps)
        rw [e2]
        exact (ih ((σ' μ).symm x)).1
      · simp only [doubleStep, loopProd_cons]
        show (U ((σ μ).symm (B.ι x), μ))⁻¹
            * ((U ((σ μ).symm ((σ μ).symm (B.ι x)), μ))⁻¹
              * loopProd σ U ((σ μ).symm ((σ μ).symm (B.ι x)))
                (doubleStep σ σ' B steps))
          = ((blockMap σ σ' B U) ((σ' μ).symm x, μ))⁻¹
            * loopProd σ' (blockMap σ σ' B U) ((σ' μ).symm x) steps
        rw [blockMap_apply, e2, e1, (ih ((σ' μ).symm x)).2,
          ← mul_assoc, ← mul_inv_rev]

/-- **Wilson-loop doubling.** The coarse Wilson loop of the blocked
configuration along `steps` is the fine Wilson loop along the
doubled path. -/
theorem wilsonLoop_doubleStep (B : BlockingScheme σ σ')
    (U : Config Λ G) (x : Λ') (steps : List Step) :
    wilsonLoop σ ρ U (B.ι x) (doubleStep σ σ' B steps)
      = wilsonLoop σ' ρ (blockMap σ σ' B U) x steps := by
  unfold wilsonLoop
  rw [(loopEnd_loopProd_doubleStep σ σ' B U x steps).2]

/-- The doubled plaquette path is the eight-link perimeter of the
blocked plaquette. -/
theorem doubleStep_plaquetteSteps (B : BlockingScheme σ σ')
    (μ ν : Fin 4) :
    doubleStep σ σ' B (plaquetteSteps μ ν)
      = [Step.fwd μ, Step.fwd μ, Step.fwd ν, Step.fwd ν,
        Step.bwd μ, Step.bwd μ, Step.bwd ν, Step.bwd ν] := rfl

/-- **The blocked plaquette is the fine perimeter loop.** The
coarse plaquette Wilson loop of a blocked configuration equals the
fine Wilson loop around the blocked plaquette's eight-link
perimeter. -/
theorem wilsonLoop_blocked_plaquette (B : BlockingScheme σ σ')
    (U : Config Λ G) (y : Λ') (μ ν : Fin 4) :
    wilsonLoop σ ρ U (B.ι y) (doubleStep σ σ' B (plaquetteSteps μ ν))
      = wilsonLoop σ' ρ (blockMap σ σ' B U) y (plaquetteSteps μ ν) :=
  wilsonLoop_doubleStep σ σ' ρ B U y (plaquetteSteps μ ν)

end LoopDoubling

/-! ## §7. Composition: two blockings are one 4-link blocking

Since a blocking scheme's two-step law is first-order in the coarse
shifts, two consecutive factor-2 blockings compose at the level of
*maps* (the composite blocked link is the ordered product of four
consecutive fine links) and hence at the level of measures. That
the composite is again "one exact blocking step" of a composed
scheme is the associativity the RG trajectory of Stage 3 needs;
the map-level composition proved here is its exact finite content. -/

section Composition

variable {Λ Λ' Λ'' : Type*} [Fintype Λ] [Fintype Λ'] [Fintype Λ'']
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
variable (σ : Fin 4 → Equiv.Perm Λ) (σ' : Fin 4 → Equiv.Perm Λ')
  (σ'' : Fin 4 → Equiv.Perm Λ'')

/-- The four-link blocked variables of two consecutive blockings:
the ordered product of the four consecutive fine links along a
twice-blocked edge. -/
def block4Map (B₁ : BlockingScheme σ σ') (B₂ : BlockingScheme σ' σ'')
    (U : Config Λ G) : Config Λ'' G :=
  fun ℓ'' => (U (fineLinkA σ σ' B₁ (fineLinkA σ' σ'' B₂ ℓ''))
      * U (fineLinkB σ σ' B₁ (fineLinkA σ' σ'' B₂ ℓ'')))
    * (U (fineLinkA σ σ' B₁ (fineLinkB σ' σ'' B₂ ℓ''))
      * U (fineLinkB σ σ' B₁ (fineLinkB σ' σ'' B₂ ℓ'')))

/-- **Composition of blocked variables.** Blocking twice is the
four-link product: the composite blocked link is the ordered
product of the four consecutive fine links along the twice-blocked
edge. Proved from the definitions alone — the two-step law is not
even consumed. -/
theorem blockMap_blockMap (B₁ : BlockingScheme σ σ')
    (B₂ : BlockingScheme σ' σ'') (U : Config Λ G) :
    blockMap σ' σ'' B₂ (blockMap σ σ' B₁ U) = block4Map σ σ' σ'' B₁ B₂ U := by
  funext ⟨y, μ⟩
  simp only [blockMap_apply, fineLinkA, fineLinkB, block4Map]

/-- Measurability of the four-link blocking map. -/
theorem measurable_block4Map (B₁ : BlockingScheme σ σ')
    (B₂ : BlockingScheme σ' σ'') :
    Measurable (block4Map σ σ' σ'' B₁ B₂ : Config Λ G → Config Λ'' G) := by
  have hfun : block4Map σ σ' σ'' B₁ B₂
      = (blockMap σ' σ'' B₂ : Config Λ' G → Config Λ'' G)
        ∘ (blockMap σ σ' B₁ : Config Λ G → Config Λ' G) := by
    funext U
    exact (blockMap_blockMap σ σ' σ'' B₁ B₂ U).symm
  rw [hfun]
  exact (measurable_blockMap (G := G) σ' σ'' B₂).comp
    (measurable_blockMap (G := G) σ σ' B₁)

/-- **Composition of blocked measures.** The pushforward of the
pushforward is the pushforward under the four-link product map. -/
theorem blockedMeasure_blockedMeasure (B₁ : BlockingScheme σ σ')
    (B₂ : BlockingScheme σ' σ'') (μ : Measure (Config Λ G)) :
    blockedMeasure σ' σ'' B₂ (blockedMeasure σ σ' B₁ μ)
      = Measure.map (block4Map σ σ' σ'' B₁ B₂) μ := by
  have hfun : (blockMap σ' σ'' B₂ : Config Λ' G → Config Λ'' G)
        ∘ (blockMap σ σ' B₁ : Config Λ G → Config Λ' G)
      = block4Map σ σ' σ'' B₁ B₂ :=
    funext fun U => blockMap_blockMap σ σ' σ'' B₁ B₂ U
  unfold blockedMeasure
  rw [Measure.map_map (measurable_blockMap (G := G) σ' σ'' B₂)
    (measurable_blockMap (G := G) σ σ' B₁), hfun]

end Composition

/-! ## §8. The effective action

The blocked Gibbs measure and the coarse product Haar measure are
mutually absolutely continuous — both densities (the Gibbs density
on the fine side, its pushforward on the coarse side) are strictly
positive. The blocked measure therefore *has* an exact effective
action: minus the log of its Radon–Nikodym density against the
coarse product Haar measure, and the blocked measure is exactly
the Gibbs-shaped measure of that action. What is *not* claimed —
and is fenced as the named Stage-3 question in the dossier — is
that this action is of single-plaquette Wilson form at `β > 0`. -/

section EffectiveAction

variable {Λ Λ' : Type*} [Fintype Λ] [Fintype Λ']
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
variable (σ : Fin 4 → Equiv.Perm Λ) (σ' : Fin 4 → Equiv.Perm Λ')
variable (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
variable {d : ℕ} (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ))

/-- The Gibbs density is strictly positive (it is an exponential),
coerced to `ℝ≥0∞`. -/
theorem gibbsDensity_coe_ne_zero (β : ℝ) (U : Config Λ G) :
    (gibbsDensity σ ρ β U : ℝ≥0∞) ≠ 0 := by
  have hval : (gibbsDensity σ ρ β U : ℝ)
      = Real.exp (- wilsonAction σ ρ β U) := rfl
  have hpos : (gibbsDensity σ ρ β U : ℝ≥0) ≠ 0 := by
    intro hcon
    have h3 : (gibbsDensity σ ρ β U : ℝ) = 0 := by rw [hcon]; rfl
    rw [hval] at h3
    exact (Real.exp_pos _).ne' h3
  rw [Ne, ENNReal.coe_eq_zero]
  exact hpos

/-- Helper: a Gibbs-null set is null for the unnormalized density
measure (the normalizing constant is finite and nonzero). -/
theorem withDensity_eq_zero_of_gibbsMeasure_eq_zero
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hd : 0 < d)
    (β : ℝ) {s : Set (Config Λ G)}
    (hs : gibbsMeasure σ μG ρ β s = 0) :
    (configMeasure μG).withDensity
      (fun U => (gibbsDensity σ ρ β U : ℝ≥0∞)) s = 0 := by
  have hZ : (0 : ℝ) < gibbsPartition σ μG ρ β :=
    gibbsPartition_pos σ μG ρ hρcont hd β
  have hc : (ENNReal.ofReal (gibbsPartition σ μG ρ β))⁻¹ ≠ 0 :=
    ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top
  unfold gibbsMeasure at hs
  rw [Measure.smul_apply, smul_eq_mul] at hs
  rcases mul_eq_zero.mp hs with h | h
  · exact absurd h hc
  · exact h

/-- The configuration measure is absolutely continuous with respect
to the Gibbs measure: the Gibbs density is everywhere positive, so
Gibbs-null sets are configuration-null. -/
theorem configMeasure_ac_gibbsMeasure
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hd : 0 < d)
    (β : ℝ) :
    configMeasure μG ≪ gibbsMeasure σ μG ρ β := by
  have h1 : configMeasure μG ≪ (configMeasure μG).withDensity
      (fun U => (gibbsDensity σ ρ β U : ℝ≥0∞)) :=
    withDensity_absolutelyContinuous'
      (measurable_coe_gibbsDensity σ ρ hρcont β).aemeasurable
      (ae_of_all _ fun U => gibbsDensity_coe_ne_zero σ ρ β U)
  intro s hs
  exact h1 (withDensity_eq_zero_of_gibbsMeasure_eq_zero σ μG ρ
    hρcont hd β hs)

/-- The Gibbs measure is absolutely continuous with respect to the
configuration measure (its density exists by definition). -/
theorem gibbsMeasure_ac_configMeasure
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hd : 0 < d)
    (β : ℝ) :
    gibbsMeasure σ μG ρ β ≪ configMeasure μG := by
  have hwd : (configMeasure μG).withDensity
      (fun U => (gibbsDensity σ ρ β U : ℝ≥0∞)) ≪ configMeasure μG :=
    withDensity_absolutelyContinuous _ _
  intro s hs
  have h2 : (configMeasure μG).withDensity
      (fun U => (gibbsDensity σ ρ β U : ℝ≥0∞)) s = 0 := hwd hs
  unfold gibbsMeasure
  rw [Measure.smul_apply, smul_eq_mul, h2, mul_zero]

/-- **Mutual absolute continuity, blocked side (one direction).**
The blocked Gibbs measure is absolutely continuous with respect to
the coarse configuration measure. -/
theorem blockedGibbsMeasure_ac_configMeasure
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hd : 0 < d)
    (B : BlockingScheme σ σ') (β : ℝ) :
    blockedGibbsMeasure σ σ' μG ρ B β ≪ configMeasure μG := by
  have h : blockedGibbsMeasure σ σ' μG ρ B β
      ≪ blockedMeasure σ σ' B (configMeasure μG) :=
    (gibbsMeasure_ac_configMeasure σ μG ρ hρcont hd β).map
      (measurable_blockMap σ σ' B)
  rwa [blockedMeasure_configMeasure σ σ' μG B] at h

/-- **Mutual absolute continuity, blocked side (other direction).**
The coarse configuration measure is absolutely continuous with
respect to the blocked Gibbs measure: the blocked theory charges
exactly the same null sets as the free coarse theory. -/
theorem configMeasure_ac_blockedGibbsMeasure
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hd : 0 < d)
    (B : BlockingScheme σ σ') (β : ℝ) :
    configMeasure μG ≪ blockedGibbsMeasure σ σ' μG ρ B β := by
  have h : blockedMeasure σ σ' B (configMeasure μG)
      ≪ blockedGibbsMeasure σ σ' μG ρ B β :=
    (configMeasure_ac_gibbsMeasure σ μG ρ hρcont hd β).map
      (measurable_blockMap σ σ' B)
  rwa [blockedMeasure_configMeasure σ σ' μG B] at h

/-- The **blocked density**: the Radon–Nikodym derivative of the
blocked Gibbs measure against the coarse configuration measure. -/
noncomputable def blockedDensity (B : BlockingScheme σ σ') (β : ℝ) :
    Config Λ' G → ℝ≥0∞ :=
  MeasureTheory.Measure.rnDeriv (blockedGibbsMeasure σ σ' μG ρ B β)
    (configMeasure μG)

/-- The **effective (blocked) action**: minus the logarithm of the
blocked density. This is an exact definition at every `β` — the
log-density of the pushforward — not an ansatz. -/
noncomputable def blockedAction (B : BlockingScheme σ σ') (β : ℝ) :
    Config Λ' G → ℝ :=
  fun V => -Real.log ((blockedDensity σ σ' μG ρ B β V).toReal)

/-- The blocked density is nonzero almost everywhere (mutual
absolute continuity kills its zero set). -/
theorem blockedDensity_ne_zero_ae
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hd : 0 < d)
    (B : BlockingScheme σ σ') (β : ℝ) :
    ∀ᵐ V ∂(configMeasure μG), blockedDensity σ σ' μG ρ B β V ≠ 0 := by
  haveI : IsProbabilityMeasure (blockedGibbsMeasure σ σ' μG ρ B β) :=
    isProbabilityMeasure_blockedGibbsMeasure σ σ' μG ρ B hρcont hd β
  have hνμ : blockedGibbsMeasure σ σ' μG ρ B β ≪ configMeasure μG :=
    blockedGibbsMeasure_ac_configMeasure σ σ' μG ρ hρcont hd B β
  have hμν : configMeasure μG ≪ blockedGibbsMeasure σ σ' μG ρ B β :=
    configMeasure_ac_blockedGibbsMeasure σ σ' μG ρ hρcont hd B β
  have hmeas : MeasurableSet
      {V | blockedDensity σ σ' μG ρ B β V = 0} :=
    MeasureTheory.Measure.measurable_rnDeriv _ _
      (measurableSet_singleton 0)
  have hZ : blockedGibbsMeasure σ σ' μG ρ B β
      {V | blockedDensity σ σ' μG ρ B β V = 0} = 0 := by
    calc blockedGibbsMeasure σ σ' μG ρ B β
          {V | blockedDensity σ σ' μG ρ B β V = 0}
        = ∫⁻ V in {V | blockedDensity σ σ' μG ρ B β V = 0},
            blockedDensity σ σ' μG ρ B β V ∂(configMeasure μG) := by
          rw [← Measure.withDensity_rnDeriv_eq _ _ hνμ,
            MeasureTheory.withDensity_apply _ hmeas]
          rfl
      _ = 0 := by
          have hcongr : (∫⁻ V in {V | blockedDensity σ σ' μG ρ B β V = 0},
              blockedDensity σ σ' μG ρ B β V ∂(configMeasure μG))
              = ∫⁻ _ in {V | blockedDensity σ σ' μG ρ B β V = 0},
                (0 : ℝ≥0∞) ∂(configMeasure μG) :=
            lintegral_congr_ae (by
              filter_upwards [ae_restrict_mem hmeas] with V hV
              exact hV)
          rw [hcongr]
          simp
  rw [ae_iff]
  have hset : {V | ¬ blockedDensity σ σ' μG ρ B β V ≠ 0}
      = {V | blockedDensity σ σ' μG ρ B β V = 0} := by
    ext V
    simp [ne_eq]
  rw [hset]
  exact hμν hZ

/-- **The effective-action representation.** The blocked Gibbs
measure is exactly the Gibbs-shaped measure of its effective
action: the coarse configuration measure weighted by
`exp (- S_eff)`. Proved at every `β`. (That `S_eff` is *not* of
single-plaquette Wilson form at `β > 0` is the fenced Stage-3
question — see the dossier; at `β = 0` it is `0`, next theorem.) -/
theorem blockedGibbsMeasure_eq_withDensity_exp
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hd : 0 < d)
    (B : BlockingScheme σ σ') (β : ℝ) :
    blockedGibbsMeasure σ σ' μG ρ B β
      = (configMeasure μG).withDensity
          (fun V => ENNReal.ofReal
            (Real.exp (- blockedAction σ σ' μG ρ B β V))) := by
  haveI : IsProbabilityMeasure (blockedGibbsMeasure σ σ' μG ρ B β) :=
    isProbabilityMeasure_blockedGibbsMeasure σ σ' μG ρ B hρcont hd β
  have hνμ : blockedGibbsMeasure σ σ' μG ρ B β ≪ configMeasure μG :=
    blockedGibbsMeasure_ac_configMeasure σ σ' μG ρ hρcont hd B β
  rw [← Measure.withDensity_rnDeriv_eq _ _ hνμ]
  refine MeasureTheory.withDensity_congr_ae ?_
  filter_upwards [blockedDensity_ne_zero_ae σ σ' μG ρ hρcont hd B β,
    MeasureTheory.Measure.rnDeriv_lt_top
      (blockedGibbsMeasure σ σ' μG ρ B β)
      (configMeasure μG)] with V hV0 hVtop
  show blockedDensity σ σ' μG ρ B β V
    = ENNReal.ofReal (Real.exp (- blockedAction σ σ' μG ρ B β V))
  have hact : - blockedAction σ σ' μG ρ B β V
      = Real.log ((blockedDensity σ σ' μG ρ B β V).toReal) := by
    unfold blockedAction
    exact neg_neg _
  have htop' : blockedDensity σ σ' μG ρ B β V ≠ ∞ := ne_of_lt hVtop
  rw [hact, Real.exp_log
    (ENNReal.toReal_pos hV0 (ne_of_lt hVtop)),
    ENNReal.ofReal_toReal htop']

/-- The fenced statement, named: the blocked Gibbs measure *is*
the coarse Gibbs measure at some coarse coupling. At `β = 0` it is
proved (with `β' = 0`); at `β > 0` it is the Stage-3 question — the
blocked action of §8 exists exactly, but its identification with a
single-plaquette Wilson action is not claimed anywhere in this
module. -/
def BlockedGibbsIsCoarseGibbs (B : BlockingScheme σ σ') (β β' : ℝ) :
    Prop :=
  blockedGibbsMeasure σ σ' μG ρ B β = gibbsMeasure σ' μG ρ β'

/-- **The fenced statement at β = 0: proved.** The blocked Gibbs
measure at `β = 0` is the coarse Gibbs measure at `β' = 0`. -/
theorem blockedGibbsIsCoarseGibbs_zero (B : BlockingScheme σ σ') :
    BlockedGibbsIsCoarseGibbs σ σ' μG ρ B 0 0 :=
  blockedGibbsMeasure_zero σ σ' μG ρ B

end EffectiveAction

/-! ## §9. The concrete torus instance

The abstract scheme of §1, instantiated on Stage 0's torus: fine
extent `2M`, coarse extent `M`, the embedding doubling each
coordinate. The parity argument is arithmetic: doubled coordinates
have even `ZMod.val`, one fine step makes the value odd, so one
fine step never lands on the coarse sublattice — and two fine steps
are exactly the coarse step, wrap-around included. -/

section TorusInstance

variable {M : ℕ} [NeZero M]

/-- The coordinate doubling map `ZMod M → ZMod (2M)`. -/
def torusDouble (z : ZMod M) : ZMod (2 * M) :=
  ((2 * z.val : ℕ) : ZMod (2 * M))

theorem torusDouble_val (z : ZMod M) :
    (torusDouble z).val = 2 * z.val := by
  show (((2 * z.val : ℕ) : ZMod (2 * M))).val = 2 * z.val
  rw [ZMod.val_natCast]
  exact Nat.mod_eq_of_lt (by have := ZMod.val_lt z; omega)

theorem torusDouble_add_one_val (z : ZMod M) :
    (torusDouble z + 1).val = 2 * z.val + 1 := by
  have hMpos : 0 < M := Nat.pos_of_neZero M
  haveI : NeZero (2 * M) :=
    ⟨Nat.mul_ne_zero (by norm_num) (Nat.pos_iff_ne_zero.mp hMpos)⟩
  have h1 : torusDouble z + 1
      = torusDouble z + ((1 : ℕ) : ZMod (2 * M)) := by
    rw [Nat.cast_one]
  rw [h1, ZMod.val_add, torusDouble_val, ZMod.val_natCast,
    Nat.mod_eq_of_lt (show 1 < 2 * M by omega)]
  exact Nat.mod_eq_of_lt (by have := ZMod.val_lt z; omega)

theorem torusDouble_injective : Function.Injective (torusDouble (M := M)) := by
  intro z w h
  have h2 : (torusDouble z).val = (torusDouble w).val :=
    congrArg ZMod.val h
  rw [torusDouble_val, torusDouble_val] at h2
  have hv : z.val = w.val := by omega
  exact ZMod.val_injective M hv

/-- The coarse-site embedding: double every coordinate. -/
def torusEmbed : (Fin 4 → ZMod M) → (Fin 4 → ZMod (2 * M)) :=
  fun y μ => torusDouble (y μ)

theorem torusBlocking_injective : Function.Injective (torusEmbed (M := M)) := by
  intro y₁ y₂ h
  funext μ
  exact torusDouble_injective (congrFun h μ)

theorem torusBlocking_twoStep (μ : Fin 4) (y : Fin 4 → ZMod M) :
    torusShift (2 * M) μ (torusShift (2 * M) μ (torusEmbed y))
      = torusEmbed (torusShift M μ y) := by
  funext ν
  show ((Pi.single μ 1 : Fin 4 → ZMod (2 * M))
      + ((Pi.single μ 1 : Fin 4 → ZMod (2 * M)) + torusEmbed y)) ν
      = torusDouble (((Pi.single μ 1 : Fin 4 → ZMod M) + y) ν)
  by_cases hνμ : ν = μ
  · rw [hνμ]
    simp only [Pi.add_apply, Pi.single_eq_same]
    show (1 : ZMod (2 * M)) + (1 + torusDouble (y μ))
        = torusDouble (1 + y μ)
    rw [add_comm (1 : ZMod M) (y μ)]
    have hL : (1 : ZMod (2 * M)) + (1 + torusDouble (y μ))
        = ((2 * (y μ).val + 2 : ℕ) : ZMod (2 * M)) := by
      show (1 : ZMod (2 * M))
          + (1 + ((2 * (y μ).val : ℕ) : ZMod (2 * M)))
        = ((2 * (y μ).val + 2 : ℕ) : ZMod (2 * M))
      rw [← Nat.cast_one, ← Nat.cast_add, ← Nat.cast_add]
      congr 1
      omega
    by_cases hwrap : (y μ).val + 1 < M
    · have e1 : (y μ + 1).val = (y μ).val + 1 := by
        have h1 : (y μ + 1) = y μ + ((1 : ℕ) : ZMod M) := by
          rw [Nat.cast_one]
        rw [h1, ZMod.val_add, ZMod.val_natCast,
          Nat.mod_eq_of_lt (show 1 < M by omega),
          Nat.mod_eq_of_lt hwrap]
      have hR : torusDouble (y μ + 1)
          = ((2 * (y μ).val + 2 : ℕ) : ZMod (2 * M)) := by
        show ((2 * (y μ + 1).val : ℕ) : ZMod (2 * M))
          = ((2 * (y μ).val + 2 : ℕ) : ZMod (2 * M))
        rw [e1]
        congr 1
      exact hL.trans hR.symm
    · have hv : (y μ).val + 1 = M := by
        have := ZMod.val_lt (y μ); omega
      have hval0 : (y μ + 1).val = 0 := by
        have h1 : (y μ + 1) = y μ + ((1 : ℕ) : ZMod M) := by
          rw [Nat.cast_one]
        rw [h1, ZMod.val_add, ZMod.val_natCast]
        by_cases hM1 : M = 1
        · subst hM1
          have hv0 : (y μ).val = 0 := by
            have := ZMod.val_lt (y μ); omega
          rw [hv0]
        · rw [Nat.mod_eq_of_lt (show 1 < M by omega), hv]
          exact Nat.mod_self M
      have e0 : y μ + 1 = 0 :=
        ZMod.val_injective M (by rw [hval0, ZMod.val_zero])
      have hR : torusDouble (y μ + 1)
          = ((2 * (y μ).val + 2 : ℕ) : ZMod (2 * M)) := by
        rw [e0]
        show ((2 * (0 : ZMod M).val : ℕ) : ZMod (2 * M))
          = ((2 * (y μ).val + 2 : ℕ) : ZMod (2 * M))
        rw [ZMod.val_zero]
        have e2 : 2 * (y μ).val + 2 = 2 * M := by omega
        show (((2 * 0 : ℕ)) : ZMod (2 * M))
          = ((2 * (y μ).val + 2 : ℕ) : ZMod (2 * M))
        rw [e2, Nat.cast_zero, ZMod.natCast_self]
      exact hL.trans hR.symm
  · simp only [Pi.add_apply, Pi.single_eq_of_ne hνμ, zero_add]
    rfl

theorem torusBlocking_oddStep (μ : Fin 4) (y : Fin 4 → ZMod M) :
    torusShift (2 * M) μ (torusEmbed y) ∉ Set.range (torusEmbed (M := M)) := by
  rintro ⟨z, hz⟩
  have hμ : torusDouble (z μ)
      = ((Pi.single μ 1 : Fin 4 → ZMod (2 * M)) + torusEmbed y) μ :=
    congrFun hz μ
  rw [Pi.add_apply, Pi.single_eq_same] at hμ
  have hv := congrArg ZMod.val hμ
  have e1 : (1 + torusEmbed y μ).val = 2 * (y μ).val + 1 := by
    show (1 + torusDouble (y μ)).val = 2 * (y μ).val + 1
    rw [add_comm]
    exact torusDouble_add_one_val (y μ)
  rw [e1, torusDouble_val] at hv
  omega

/-- **The torus blocking scheme.** Factor-2 blocking of the
concrete torus: extent `2M` (fine) to extent `M` (coarse). -/
def torusBlocking :
    BlockingScheme (torusShift (2 * M)) (torusShift M) where
  ι := torusEmbed
  ι_injective := torusBlocking_injective
  twoStep := torusBlocking_twoStep
  oddStep := torusBlocking_oddStep

section TorusCorollaries

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
variable (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
variable {d : ℕ} (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ))

/-- **Torus, β = 0.** The blocked Gibbs measure on the torus at
`β = 0` is the coarse torus Gibbs measure at `β = 0`. -/
theorem torus_blockedGibbsMeasure_zero :
    blockedGibbsMeasure (torusShift (2 * M)) (torusShift M) μG ρ
        torusBlocking 0
      = gibbsMeasure (torusShift M) μG ρ 0 :=
  blockedGibbsMeasure_zero (torusShift (2 * M)) (torusShift M) μG ρ
    torusBlocking

/-- **Torus, β = 0 plaquette.** The blocked plaquette expectation
on the torus at `β = 0` is the Stage-0 Haar intertwiner trace. -/
theorem torus_blocked_plaquette_expectation
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hd : 0 < d)
    (hM : 2 ≤ M) (y : Fin 4 → ZMod M) {μ ν : Fin 4} (hμν : μ ≠ ν) :
    gibbsExpect (torusShift (2 * M)) μG ρ 0
        (fun U => Matrix.trace
          (repMatrix ρ (plaquette (torusShift M)
            (blockMap (torusShift (2 * M)) (torusShift M) torusBlocking
              U) y μ ν)))
      = Matrix.trace (haarIntertwiner μG ρ) :=
  gibbsExpect_zero_blocked_plaquette (torusShift (2 * M))
    (torusShift M) μG ρ hρcont hd torusBlocking y hμν
    (torusShift_ne_self M hM μ y) (torusShift_ne_self M hM ν y)

/-- **Torus Elitzur at every β.** The blocked single-link
expectation matrix on the torus vanishes at every coupling,
provided the representation has no nonzero fixed vectors (the
Stage-1a fixed-vector hypothesis). -/
theorem torus_blocked_elitzur
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hd : 0 < d)
    (hfixed : ∀ v : Fin d → ℂ, (∀ g : G, repMatrix ρ g *ᵥ v = v)
      → v = 0)
    (hM : 2 ≤ M) (β : ℝ) (y₀ : Fin 4 → ZMod M) (μ₀ : Fin 4) :
    expectMatrix (torusShift (2 * M)) μG ρ β
        (fun U => blockMap (torusShift (2 * M)) (torusShift M)
          torusBlocking U (y₀, μ₀))
      = 0 :=
  expectMatrix_blocked_singleLink_eq_zero (torusShift (2 * M))
    (torusShift M) μG ρ hρcont hd
    (fun μ ν x => torusShift_comm (2 * M) μ ν x) hfixed torusBlocking
    β y₀ μ₀ (torusShift_ne_self M hM μ₀ y₀)

end TorusCorollaries

/-- **Torus composition.** Two torus blockings compose: extent
`2(2K) → 2K → K` equals the single four-link pushforward. -/
theorem torus_blockedMeasure_blockedMeasure (K : ℕ) [NeZero K]
    [NeZero (2 * K)] {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
    (μ : Measure (Config (Fin 4 → ZMod (2 * (2 * K))) G)) :
    blockedMeasure (torusShift (2 * K)) (torusShift K)
        (torusBlocking (M := K))
        (blockedMeasure (torusShift (2 * (2 * K))) (torusShift (2 * K))
          (torusBlocking (M := 2 * K)) μ)
      = Measure.map
          (block4Map (torusShift (2 * (2 * K))) (torusShift (2 * K))
            (torusShift K) (torusBlocking (M := 2 * K))
            (torusBlocking (M := K))) μ :=
  blockedMeasure_blockedMeasure (torusShift (2 * (2 * K)))
    (torusShift (2 * K)) (torusShift K) (torusBlocking (M := 2 * K))
    (torusBlocking (M := K)) μ

end TorusInstance

end ThetLogos
