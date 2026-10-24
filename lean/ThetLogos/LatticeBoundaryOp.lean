import ThetLogos.LatticeLayerFactor

/-!
# ThetLogos.LatticeBoundaryOp — dynamic-boundary charter, brick
DB1: the boundary operator as a named object

The dynamic-boundary scoping charter
(`whitepaper/dynamic-boundary-scoping-2026-10-24.md`, §2.1)
audited Jeff's fragment against the ledger and found the
fragment's central object already landed, unnamed: the
reflection plane is a boundary (Stage 1b-A's split), and the
boundary's dynamics is the **seam kernel** — R1's layer
Boltzmann factor `layerWeightZero = exp (−S₀)`, the
exponential of the crossing-stratum action `wilsonActionZero`
(the temporal plaquettes over the two fixed link layers
`N/2 − 1` and `N − 1`, the only plaquettes coupling the two
halves), and the object to whose positive-definiteness R2's
obstruction reduced all-vector positivity of the transfer
operator. What did not exist is the boundary as a **named,
citable object with its own basic theory**. This module
supplies exactly that, and no more (charter §2.1):

- **Definition (§1).** `Bdry`, the boundary operator of the
  finite theory at `(G, ρ, β, N)`: the seam kernel
  `layerWeightZero`, packaged as one named object on the
  split configuration space — the form R2's reduction uses
  (charter U1's fixed choice: no mid-layer space, no
  disintegration; kill K-DB1(a) does not trigger).
- **Reality (§2).** `Bdry` is a positive real function:
  every value is a strictly positive real number, hence
  real when read in `ℂ`.
- **β = 0 form (§3), computed.** At `β = 0`,
  `wilsonActionZero = 0`, so `Bdry ≡ 1`: the boundary
  operator at zero coupling is the trivial kernel, the two
  half weights trivialize with it, and R1's factorization
  decouples into the plain product of the two halves'
  product Haar measures.
- **Mirror symmetry (§4).** The reflection pairing,
  transported to split coordinates as `bdrySwap`, leaves
  `Bdry` invariant — the landed term-by-term reflection
  invariance of `S₀` (`wilsonActionZero_reflConfig`: on the
  crossing class the reflected index is the index itself),
  restated about the named object. Together with §2 this is
  the self-adjointness of the kernel's quadratic form at
  the level R2 states it. Kill K-DB1(b) (mirror symmetry
  fails) does not trigger.
- **Place in R1's factorization (§5).** The layer / Markov
  factorization, restated with `Bdry` as its density: the
  Gibbs measure in split coordinates is `Z⁻¹` times the
  product of the two half Gibbs-type measures, reweighted
  by the boundary operator.
- **Pairing through the boundary (§6).** The charter's
  §2.3 corollary, stated about the named object: every
  cross-half pairing factors through `Bdry` — in
  expectation form, and iterated over the two halves by
  Fubini. The only channel between the halves is `Bdry`.

**Charter fence (kill K-DB1(c)), on the face:**
positive-definiteness of `Bdry` is **not** asserted
anywhere in this module, on any vector class. That property
is exactly Road Map Item 1's open question at general
`(G, ρ)` — it was F3's output, F3 is dead with the third
family (charter U3), and no brick manufactures it here.
What §2 asserts is positivity of the kernel's *values* (a
positive real density), a different and weaker statement,
which the charter itself makes (§2.1: "the seam factor is
a positive real function").

NO CLAIM. Parts of the official Clay Yang–Mills statement
closed by this module: 0. Stage 1b-B label unchanged
(positivity T1 for U(1) at all `β ≥ 0`; general `(G, ρ)`
OPEN).

- Status: brick DB1 — built 2026-10-24 under the
  dynamic-boundary charter; parent verification pending.
-/

namespace ThetLogos

open MeasureTheory Finset
open scoped Matrix ENNReal NNReal

section BoundaryOp

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ))
  {N : ℕ} [NeZero N]

/-! ## §1. The boundary operator

The seam kernel of R1's factorization, named. `Bdry` is
`layerWeightZero` itself — the exponential of the
crossing-stratum action, read on a split configuration
through the unsplit one — packaged as the boundary
operator of the finite theory. The packaging is a
definition, not a construction: no disintegration, no
mid-layer marginal, nothing beyond R1's finite density
algebra is involved (charter kill K-DB1(a) does not
trigger). -/

/-- **The boundary operator** of the finite theory at
`(G, ρ, β, N)`: the seam kernel — the exponential of the
crossing-stratum action `S₀` — as a named `ℝ≥0`-valued
kernel on the split configuration space. This is the form
in which R2's reduction speaks of the object (its
positive-definiteness is Item 1's open question, *not*
asserted here). -/
noncomputable def Bdry (β : ℝ)
    (p : (↥(halfLinks (N := N)) → G)
      × (↥(negLinks (N := N)) → G)) : ℝ≥0 :=
  layerWeightZero ρ β p

/-- The boundary operator *is* R1's layer Boltzmann factor,
by definition. -/
theorem bdry_eq_layerWeightZero (β : ℝ)
    (p : (↥(halfLinks (N := N)) → G)
      × (↥(negLinks (N := N)) → G)) :
    Bdry ρ β p = layerWeightZero ρ β p := rfl

/-- The boundary operator, evaluated: the exponential of
minus the crossing-stratum action of the unsplit
configuration. -/
theorem bdry_apply (β : ℝ)
    (p : (↥(halfLinks (N := N)) → G)
      × (↥(negLinks (N := N)) → G)) :
    (Bdry ρ β p : ℝ) = Real.exp (- wilsonActionZero ρ β
      ((splitEquiv (halfLinks (N := N))).symm p)) := rfl

/-! ## §2. Reality

The seam factor is a positive real function (charter
§2.1): its values are strictly positive real numbers, so
read in `ℂ` the kernel is real. This is positivity of the
kernel's *values* — the statement that a Boltzmann density
is a positive function — not positive-definiteness of the
operator on any vector class (charter kill K-DB1(c): that
statement is not made in this module). -/

/-- Every value of the boundary operator is a strictly
positive real number. -/
theorem bdry_pos (β : ℝ)
    (p : (↥(halfLinks (N := N)) → G)
      × (↥(negLinks (N := N)) → G)) :
    0 < (Bdry ρ β p : ℝ) := by
  rw [bdry_apply]
  exact Real.exp_pos _

/-- Read in `ℂ`, the boundary operator is real: its
imaginary part vanishes identically. -/
theorem bdry_im_zero (β : ℝ)
    (p : (↥(halfLinks (N := N)) → G)
      × (↥(negLinks (N := N)) → G)) :
    ((Bdry ρ β p : ℝ) : ℂ).im = 0 :=
  Complex.ofReal_im _

/-- The boundary operator, as an `ℝ≥0`-valued function on
the split space, is measurable. -/
theorem measurable_bdry
    (hρcont : Continuous fun g : G => repMatrix ρ g) (β : ℝ) :
    Measurable fun p : (↥(halfLinks (N := N)) → G)
        × (↥(negLinks (N := N)) → G) => Bdry ρ β p :=
  measurable_layerWeightZero_nn ρ hρcont β

/-! ## §3. The β = 0 form

At zero coupling the crossing-stratum action vanishes
(it is `β` times a finite plaquette sum), so the boundary
operator is the trivial kernel `≡ 1`. The two half
actions vanish with it, the half Gibbs-type measures are
the plain product Haar measures, and the Gibbs measure in
split coordinates decouples into the scalar `Z⁻¹` times
the product of the two halves — the halves decouple
(charter §2.1). -/

/-- The crossing-stratum action at `β = 0` is zero. -/
theorem wilsonActionZero_beta_zero
    (U : Config (Fin 4 → ZMod N) G) :
    wilsonActionZero ρ 0 U = 0 := by
  unfold wilsonActionZero
  exact zero_mul _

/-- The half action at `β = 0` is zero. -/
theorem halfActionP_beta_zero
    (z : ↥(posLinks (N := N)) → G) :
    halfActionP ρ 0 z = 0 := by
  unfold halfActionP wilsonActionPlus
  exact zero_mul _

/-- **The boundary operator at `β = 0` is the trivial
kernel:** identically `1`. -/
theorem bdry_zero
    (p : (↥(halfLinks (N := N)) → G)
      × (↥(negLinks (N := N)) → G)) :
    Bdry ρ 0 p = 1 := by
  apply Subtype.ext
  show (Bdry ρ 0 p : ℝ) = ((1 : ℝ≥0) : ℝ)
  rw [bdry_apply, wilsonActionZero_beta_zero]
  simp

/-- At `β = 0` the positive half Gibbs-type measure is
the plain product Haar measure on the closed half. -/
theorem halfGibbsPlus_zero :
    halfGibbsPlus μG ρ 0
      = Measure.pi (fun _ : ↥(halfLinks (N := N)) => μG) := by
  have hval : ∀ y : ↥(halfLinks (N := N)) → G,
      layerWeightPlus ρ 0 y = 1 := by
    intro y
    apply Subtype.ext
    show (layerWeightPlus ρ 0 y : ℝ) = ((1 : ℝ≥0) : ℝ)
    show Real.exp (- halfActionP ρ 0 (restrictPos y)) = 1
    have hz := halfActionP_beta_zero (ρ := ρ) (N := N) (restrictPos y)
    rw [hz]
    simp
  have h1 : (fun y => (layerWeightPlus ρ 0 y : ℝ≥0∞))
      = (1 : (↥(halfLinks (N := N)) → G) → ℝ≥0∞) := by
    funext y
    show (layerWeightPlus ρ 0 y : ℝ≥0∞)
      = (1 : (↥(halfLinks (N := N)) → G) → ℝ≥0∞) y
    rw [hval]
    simp
  unfold halfGibbsPlus
  rw [h1]
  exact MeasureTheory.withDensity_one

/-- At `β = 0` the negative half Gibbs-type measure is
the plain product Haar measure on the negative half. -/
theorem halfGibbsMinus_zero (hN : Even N) :
    halfGibbsMinus μG ρ hN 0
      = Measure.pi (fun _ : ↥(negLinks (N := N)) => μG) := by
  have hval : ∀ u : ↥(negLinks (N := N)) → G,
      layerWeightMinus ρ hN 0 u = 1 := by
    intro u
    apply Subtype.ext
    show (layerWeightMinus ρ hN 0 u : ℝ) = ((1 : ℝ≥0) : ℝ)
    show Real.exp (- halfActionP ρ 0 (mirrorP hN u)) = 1
    have hz := halfActionP_beta_zero (ρ := ρ) (N := N) (mirrorP hN u)
    rw [hz]
    simp
  have h1 : (fun u => (layerWeightMinus ρ hN 0 u : ℝ≥0∞))
      = (1 : (↥(negLinks (N := N)) → G) → ℝ≥0∞) := by
    funext u
    show (layerWeightMinus ρ hN 0 u : ℝ≥0∞)
      = (1 : (↥(negLinks (N := N)) → G) → ℝ≥0∞) u
    rw [hval]
    simp
  unfold halfGibbsMinus
  rw [h1]
  exact MeasureTheory.withDensity_one

/-- **Decoupling at `β = 0`.** With the boundary operator
trivial, the Gibbs measure in split coordinates is the
normalizing scalar times the plain product of the two
halves' product Haar measures: at zero coupling the two
halves are independent — there is no channel between
them, because the only channel is `Bdry` and it is `1`. -/
theorem gibbsMeasure_map_splitEquiv_zero
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) :
    (gibbsMeasure (torusShift N) μG ρ 0).map
        (splitEquiv (halfLinks (N := N)))
      = (ENNReal.ofReal (gibbsPartition (torusShift N) μG ρ 0))⁻¹ •
        ((Measure.pi fun _ : ↥(halfLinks (N := N)) => μG).prod
          (Measure.pi fun _ : ↥(negLinks (N := N)) => μG)) := by
  have h1 : (fun p => (layerWeightZero ρ 0 p : ℝ≥0∞))
      = (1 : (↥(halfLinks (N := N)) → G)
          × (↥(negLinks (N := N)) → G) → ℝ≥0∞) := by
    funext p
    show (Bdry ρ 0 p : ℝ≥0∞) = (1 : (↥(halfLinks (N := N)) → G)
      × (↥(negLinks (N := N)) → G) → ℝ≥0∞) p
    rw [bdry_zero]
    simp
  rw [gibbsMeasure_map_splitEquiv μG ρ hρcont hN 0,
    halfGibbsPlus_zero, halfGibbsMinus_zero, h1,
    MeasureTheory.withDensity_one]

/-! ## §4. Mirror symmetry

The reflection pairing of the two halves, transported to
split coordinates: reflect the unsplit configuration.
`Bdry` is invariant under it — this is the landed
term-by-term reflection invariance of the crossing-stratum
action (`wilsonActionZero_reflConfig`: on the crossing
class the reflected plaquette index is the index itself,
so `S₀` is invariant *stratum by stratum*), restated about
the named operator. Charter kill K-DB1(b) — the symmetry
fails at the stated level — does not trigger; the kill
doubled as a consistency check on the charter's audit,
and the audit stands. -/

/-- **The reflection pairing on split configurations:**
the time reflection, transported along the split
coordinatization. It exchanges the two halves (it is the
split-coordinate form of `reflConfig`). -/
noncomputable def bdrySwap
    (p : (↥(halfLinks (N := N)) → G)
      × (↥(negLinks (N := N)) → G)) :
    (↥(halfLinks (N := N)) → G)
      × (↥(negLinks (N := N)) → G) :=
  splitEquiv (halfLinks (N := N))
    (reflConfig ((splitEquiv (halfLinks (N := N))).symm p))

/-- The unsplit reading of a reflected split configuration
is the reflection of the unsplit reading. -/
theorem bdrySwap_symm_apply
    (p : (↥(halfLinks (N := N)) → G)
      × (↥(negLinks (N := N)) → G)) :
    (splitEquiv (halfLinks (N := N))).symm (bdrySwap p)
      = reflConfig ((splitEquiv (halfLinks (N := N))).symm p) :=
  MeasurableEquiv.symm_apply_apply _ _

/-- The reflection pairing is an involution on split
configurations. -/
theorem bdrySwap_involutive :
    Function.Involutive (bdrySwap (G := G) (N := N)) := by
  intro p
  show splitEquiv (halfLinks (N := N))
      (reflConfig ((splitEquiv (halfLinks (N := N))).symm
        (splitEquiv (halfLinks (N := N))
          (reflConfig ((splitEquiv (halfLinks (N := N))).symm p)))))
      = p
  rw [MeasurableEquiv.symm_apply_apply, reflConfig_involutive,
    MeasurableEquiv.apply_symm_apply]

/-- **Mirror symmetry of the boundary operator.** `Bdry`
is invariant under the exchange of the two halves by the
reflection pairing, at every real `β`, general `(G, ρ)`,
even `N`. With §2 (reality) this is the self-adjointness
of the kernel's quadratic form at the level R2's
reduction states it — reality plus symmetry under the
pairing, *not* positive-definiteness. -/
theorem bdry_mirror (hN : Even N) (β : ℝ)
    (p : (↥(halfLinks (N := N)) → G)
      × (↥(negLinks (N := N)) → G)) :
    Bdry ρ β (bdrySwap p) = Bdry ρ β p := by
  apply Subtype.ext
  show (Bdry ρ β (bdrySwap p) : ℝ) = (Bdry ρ β p : ℝ)
  rw [bdry_apply, bdry_apply, bdrySwap_symm_apply,
    wilsonActionZero_reflConfig ρ hN]

/-! ## §5. The boundary operator in R1's factorization

R1's layer / Markov factorization, restated with the
boundary operator as the density: the Gibbs measure in
split coordinates is the normalizing scalar times the
product of the two half Gibbs-type measures, reweighted
by `Bdry`. This is the identification of the named object
with its place in the landed factorization (charter
§2.1): `Bdry` is not an analogue of the seam factor in
R1's identity; it *is* that factor, named. -/

/-- **R1, factored form, with the boundary operator as
its density.** At every real `β`, general `(G, ρ)`, even
`N`. -/
theorem gibbsMeasure_map_splitEquiv_bdry
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ) :
    (gibbsMeasure (torusShift N) μG ρ β).map
        (splitEquiv (halfLinks (N := N)))
      = (ENNReal.ofReal (gibbsPartition (torusShift N) μG ρ β))⁻¹ •
        ((halfGibbsPlus μG ρ β).prod
          (halfGibbsMinus μG ρ hN β)).withDensity
          (fun p => (Bdry ρ β p : ℝ≥0∞)) :=
  gibbsMeasure_map_splitEquiv μG ρ hρcont hN β

/-! ## §6. Pairing through the boundary

The charter's §2.3 corollary — finite confinement in the
split seat — stated about the named operator. In split
coordinates every Gibbs pairing of a two-half observable
runs through `Bdry` (§5's expectation form), and the
pairing iterates over the halves by Fubini: integrate one
half against the kernel, then the other. Conditionally on
the seam, the halves do not speak to each other at all;
the only channel between them is the boundary operator.
Both statements are R1's shipped forms, restated with
`Bdry` for `layerWeightZero` — no new integration is
performed, and none is needed. -/

/-- **Expectation form.** The Gibbs expectation of a
split-coordinate observable is the boundary-operator
pairing of the observable under the product of the two
half Gibbs-type measures (with the normalizing scalar). -/
theorem integral_splitEquiv_factor_bdry
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (Φ : ((↥(halfLinks (N := N)) → G)
      × (↥(negLinks (N := N)) → G)) → ℂ)
    (hΦ : StronglyMeasurable Φ) :
    ∫ U, Φ ((splitEquiv (halfLinks (N := N))) U)
        ∂(gibbsMeasure (torusShift N) μG ρ β)
      = ∫ p, (Bdry ρ β p) • Φ p
          ∂((ENNReal.ofReal
              (gibbsPartition (torusShift N) μG ρ β))⁻¹ •
            ((halfGibbsPlus μG ρ β).prod
              (halfGibbsMinus μG ρ hN β))) :=
  integral_splitEquiv_factor μG ρ hρcont hN β Φ hΦ

/-- **Iterated form (pairing through the boundary).** The
boundary-operator pairing iterates over the two halves:
first the negative half against the kernel, then the
closed half. -/
theorem pairing_through_bdry (hN : Even N) (β : ℝ)
    (Φ : ((↥(halfLinks (N := N)) → G)
      × (↥(negLinks (N := N)) → G)) → ℂ)
    (hΦ : Integrable (fun p => (Bdry ρ β p) • Φ p)
      ((halfGibbsPlus μG ρ β).prod (halfGibbsMinus μG ρ hN β))) :
    ∫ p, (Bdry ρ β p) • Φ p
        ∂((halfGibbsPlus μG ρ β).prod (halfGibbsMinus μG ρ hN β))
      = ∫ y, ∫ u, (Bdry ρ β
            ((y, u) : (↥(halfLinks (N := N)) → G)
              × (↥(negLinks (N := N)) → G))) • Φ
            ((y, u) : (↥(halfLinks (N := N)) → G)
              × (↥(negLinks (N := N)) → G))
          ∂(halfGibbsMinus μG ρ hN β) ∂(halfGibbsPlus μG ρ β) :=
  integral_layerFactor_iterated μG ρ hN β Φ hΦ

end BoundaryOp

end ThetLogos
