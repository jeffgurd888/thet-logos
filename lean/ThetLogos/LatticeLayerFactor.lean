import ThetLogos.LatticePositivity

/-!
# ThetLogos.LatticeLayerFactor — transfer-matrix route, rung R1:
the layer / Markov factorization of the Gibbs measure

The transfer-matrix charter
(`whitepaper/gram-clause-transfer-matrix-scoping-2026-10-24.md`,
§4, rung R1; gap-queue item Q3) named the missing input for
both remaining gaps of Stage 1b-D's transfer package — the
half-step square (R2) and the depth-`N/2` identification
(R3): a **time-direction Markov/layer factorization of the
Gibbs measure**. The 1b-D dossier fenced it verbatim ("It
would need a time-direction Markov/layer factorization of the
Gibbs measure (factoring the weight across slices), not
formalized in this corpus (priced M–L)").

This module formalizes it at its one-step core, as a finite
measure identity on the corpus's own product configuration
spaces. The coordinatization is Stage 0's `splitEquiv` at the
closed half `halfLinks` — configurations split into the two
half-spaces (base times `< N/2` and `≥ N/2`) — and the
factorization is the one Stage 1b-A's action split
(`wilsonAction_split_half`) dictates:

```
gibbsMeasure.map (splitEquiv halfLinks)
  = Z⁻¹ • ( (half-Gibbs on the closed half)
            × (half-Gibbs on the negative half) )
          withDensity (layer Boltzmann factor)
```

where the two half factors are Gibbs-type measures — the
product Haar measure on the half's links, reweighted by the
exponential of the half action — **with the same half-action
function `halfActionP` on both sides** (the positive half
read by restriction, the negative half read through the
mirror `mirrorP`, by the landed
`wilsonActionMinus_eq_halfActionP`), and the layer Boltzmann
factor is `exp (−S₀)`, the exponential of the
crossing-stratum action `wilsonActionZero`: the temporal
plaquettes over the two fixed link layers `N/2 − 1` and
`N − 1`, the only plaquettes coupling the two halves. No
conditional measure and no disintegration is involved: the
split is a permutation of the factors of a finite product,
and the proof is the landed action split, the algebra of
`exp` of a sum, and Fubini/density transport — in particular
**no expansion of the Boltzmann weight in any basis**
(charter constraint D5).

The consumption form (§5) is the iterated expectation: a
Gibbs expectation of a split-space observable is the
`Z⁻¹`-multiple of the half-marginal integral of the
layer-kernel pairing — the shape `transferOp_inner`'s
right-hand side (a Gibbs integral of a two-reading
observable) consumes, and the shape R3 iterates over the
positive half's layers.

Scope fences (charter §3, kept): general `(G, ρ)` (D2);
every real `β` — the factorization consumes only that the
Boltzmann weight is a positive function, no sign condition
on `β` (D3); the `d = 1` case flows through the same proof
(D4); fixed even `N`, finite lattice (D6). This module does
**not** prove positivity of the transfer operator on
arbitrary vectors (that is R2's half-step square, which
consumes this factorization), does not identify `osForm`
with a transfer power beyond depth one (R3), and does not
discharge Stage 1b-B.

NO CLAIM. Parts of the official Clay Yang–Mills statement
closed by this module: 0. Stage 1b-B label unchanged
(positivity T1 for U(1); general `(G, ρ)` OPEN).

- Status: rung R1 — LANDED 2026-10-24 (gap-queue Q3).
  PARENT-VERIFIED: fresh `lake build
  ThetLogos.LatticeLayerFactor` green (3,394 jobs, exit 0);
  19 strict theorems / 5 defs in this file, zero
  `sorry`/`admit`; `#print axioms` on
  `gibbsMeasure_map_splitEquiv`,
  `gibbsMeasure_map_splitEquiv_half`,
  `integral_splitEquiv_factor`,
  `integral_layerFactor_iterated` — standard axioms only
  (propext, Classical.choice, Quot.sound), no `sorryAx`.
-/

namespace ThetLogos

open MeasureTheory Finset
open scoped Matrix ENNReal NNReal

section LayerFactor

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ))
  {N : ℕ} [NeZero N]

/-! ## §1. The three weights and the two half measures

The split Gibbs density in the coordinatization
`splitEquiv halfLinks`: by Stage 1b-B's
`wilsonAction_split_half`, the Wilson action of the unsplit
configuration `(splitEquiv halfLinks).symm (y, u)` is
`halfActionP (restrictPos y) + halfActionP (mirrorP hN u)
+ wilsonActionZero ((splitEquiv halfLinks).symm (y, u))` —
a positive-half term, the *same* half-action function of the
mirrored negative half, and the crossing (layer) term. The
three weights below are the exponentials of the three terms,
as `ℝ≥0`-valued functions in the style of `gibbsDensity`. -/

/-- The **positive half weight**: the exponential of the
positive half action, read on a closed-half configuration
through its strict-half restriction. -/
noncomputable def layerWeightPlus (β : ℝ)
    (y : ↥(halfLinks (N := N)) → G) : ℝ≥0 :=
  ⟨Real.exp (- halfActionP ρ β (restrictPos y)), Real.exp_nonneg _⟩

/-- The **negative half weight**: the exponential of the
negative half action, read on a negative-half configuration
through the mirror — the same `halfActionP` as the positive
weight (Stage 1b-A's `S₋ = S₊ ∘ θ`, in the factored form of
`wilsonActionMinus_eq_halfActionP`). The two half-step
factors are therefore one function read on the two sides:
the symmetric split the charter's R1 kill criterion asks
for. -/
noncomputable def layerWeightMinus (hN : Even N) (β : ℝ)
    (u : ↥(negLinks (N := N)) → G) : ℝ≥0 :=
  ⟨Real.exp (- halfActionP ρ β (mirrorP hN u)), Real.exp_nonneg _⟩

/-- The **layer Boltzmann factor**: the exponential of the
crossing-stratum action `S₀` — the temporal plaquettes over
the two fixed link layers `N/2 − 1` and `N − 1` — read on a
split configuration through the unsplit one. This is the
only factor coupling the two halves. -/
noncomputable def layerWeightZero (β : ℝ)
    (p : (↥(halfLinks (N := N)) → G) × (↥(negLinks (N := N)) → G)) :
    ℝ≥0 :=
  ⟨Real.exp (- wilsonActionZero ρ β
      ((splitEquiv (halfLinks (N := N))).symm p)), Real.exp_nonneg _⟩

/-- The **positive half Gibbs-type measure**: product Haar
measure on the closed half's links, reweighted by the
positive half weight. (A "Gibbs-type" measure: it is the
half's own Boltzmann reweighting, *not* a marginal of the
full Gibbs measure — the halves are coupled by the layer
factor, which is carried separately.) -/
noncomputable def halfGibbsPlus (β : ℝ) :
    Measure (↥(halfLinks (N := N)) → G) :=
  (Measure.pi fun _ : ↥(halfLinks (N := N)) => μG).withDensity
    (fun y => (layerWeightPlus ρ β y : ℝ≥0∞))

/-- The **negative half Gibbs-type measure**: product Haar
measure on the negative half's links, reweighted by the
negative half weight. -/
noncomputable def halfGibbsMinus (hN : Even N) (β : ℝ) :
    Measure (↥(negLinks (N := N)) → G) :=
  (Measure.pi fun _ : ↥(negLinks (N := N)) => μG).withDensity
    (fun u => (layerWeightMinus ρ hN β u : ℝ≥0∞))

/-! ## §2. Measurability of the weights

The analytic side conditions, discharged by the corpus's
continuity/boundedness API (charter D5): a plaquette density
is measurable in the configuration (Stage 0's pattern), the
three action pieces are finite sums of plaquette densities,
the half action is measurable in the strict-half
configuration (through the extension by `1`), and the two
transports `restrictPos` / `mirrorP` are coordinate maps,
hence measurable. -/

/-- A single plaquette density is measurable in the ambient
configuration (Stage 0's `measurable_wilsonAction` pattern,
for one density). -/
theorem measurable_plaquetteDensity_lf
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (x : Fin 4 → ZMod N) (μ ν : Fin 4) :
    Measurable fun U : Config (Fin 4 → ZMod N) G =>
      plaquetteDensity (torusShift N) ρ U x μ ν := by
  have htr : Measurable fun U : Config (Fin 4 → ZMod N) G =>
      (Matrix.trace (repMatrix ρ (plaquette (torusShift N) U x μ ν))).re := by
    refine Complex.measurable_re.comp ?_
    refine Finset.measurable_sum _ fun i _ => ?_
    exact (measurable_pi_apply i).comp ((measurable_pi_apply i).comp
      (hρcont.measurable.comp (measurable_plaquette (torusShift N) x μ ν)))
  unfold plaquetteDensity
  exact measurable_const.sub (htr.div_const _)

/-- The positive Wilson action is measurable in the ambient
configuration. -/
theorem measurable_wilsonActionPlus_lf
    (hρcont : Continuous fun g : G => repMatrix ρ g) (β : ℝ) :
    Measurable fun U : Config (Fin 4 → ZMod N) G =>
      wilsonActionPlus ρ β U := by
  unfold wilsonActionPlus
  exact (Finset.measurable_sum _ fun p _ =>
    measurable_plaquetteDensity_lf ρ hρcont p.1 p.2.1 p.2.2).const_mul β

/-- The negative Wilson action is measurable in the ambient
configuration. -/
theorem measurable_wilsonActionMinus_lf
    (hρcont : Continuous fun g : G => repMatrix ρ g) (β : ℝ) :
    Measurable fun U : Config (Fin 4 → ZMod N) G =>
      wilsonActionMinus ρ β U := by
  unfold wilsonActionMinus
  exact (Finset.measurable_sum _ fun p _ =>
    measurable_plaquetteDensity_lf ρ hρcont p.1 p.2.1 p.2.2).const_mul β

/-- The crossing-stratum Wilson action is measurable in the
ambient configuration. -/
theorem measurable_wilsonActionZero_lf
    (hρcont : Continuous fun g : G => repMatrix ρ g) (β : ℝ) :
    Measurable fun U : Config (Fin 4 → ZMod N) G =>
      wilsonActionZero ρ β U := by
  unfold wilsonActionZero
  exact (Finset.measurable_sum _ fun p _ =>
    measurable_plaquetteDensity_lf ρ hρcont p.1 p.2.1 p.2.2).const_mul β

/-- The extension of a strict-half configuration by `1` off
the half is measurable in the configuration. -/
theorem measurable_extendP_lf :
    Measurable fun z : ↥(posLinks (N := N)) → G => extendP z := by
  refine Measurable.of_eval fun ℓ => ?_
  by_cases hℓ : ℓ ∈ posLinks (N := N)
  · have hfun : (fun z : ↥(posLinks (N := N)) → G => extendP z ℓ)
        = fun z => z ⟨ℓ, hℓ⟩ :=
      funext fun z => extendP_apply hℓ
    rw [hfun]
    exact measurable_pi_apply _
  · have hfun : (fun z : ↥(posLinks (N := N)) → G => extendP z ℓ)
        = fun _ => (1 : G) := by
      funext z
      show (if h : ℓ ∈ posLinks (N := N) then z ⟨ℓ, h⟩ else 1) = 1
      exact dif_neg hℓ
    rw [hfun]
    exact measurable_const

/-- The half action is measurable in the strict-half
configuration. -/
theorem measurable_halfActionP_lf
    (hρcont : Continuous fun g : G => repMatrix ρ g) (β : ℝ) :
    Measurable fun z : ↥(posLinks (N := N)) → G => halfActionP ρ β z :=
  (measurable_wilsonActionPlus_lf ρ hρcont β).comp measurable_extendP_lf

/-- The restriction from the closed half to the strict half
is a coordinate map, hence measurable. -/
theorem measurable_restrictPos_lf :
    Measurable fun y : ↥(halfLinks (N := N)) → G => restrictPos y :=
  Measurable.of_eval fun ℓ =>
    measurable_pi_apply
      (⟨ℓ.1, posLinks_subset_halfLinks ℓ.2⟩ : ↥(halfLinks (N := N)))

/-- The mirror transport from the negative half to the
strict half is a coordinate map (with inversion on time
links), hence measurable. -/
theorem measurable_mirrorP_lf (hN : Even N) :
    Measurable fun w : ↥(negLinks (N := N)) → G => mirrorP hN w := by
  refine Measurable.of_eval fun ℓ => ?_
  by_cases hc : ℓ.1.2 = 0
  · have hfun : (fun w : ↥(negLinks (N := N)) → G => mirrorP hN w ℓ)
        = fun w => (w ⟨reflLink ℓ.1,
            reflLink_mem_negLinks hN ℓ.2⟩)⁻¹ := by
      funext w
      show (if ℓ.1.2 = 0
          then (w ⟨reflLink ℓ.1, reflLink_mem_negLinks hN ℓ.2⟩)⁻¹
          else w ⟨reflLink ℓ.1, reflLink_mem_negLinks hN ℓ.2⟩)
        = (w ⟨reflLink ℓ.1, reflLink_mem_negLinks hN ℓ.2⟩)⁻¹
      exact if_pos hc
    rw [hfun]
    exact (measurable_pi_apply _).inv
  · have hfun : (fun w : ↥(negLinks (N := N)) → G => mirrorP hN w ℓ)
        = fun w => w ⟨reflLink ℓ.1,
            reflLink_mem_negLinks hN ℓ.2⟩ := by
      funext w
      show (if ℓ.1.2 = 0
          then (w ⟨reflLink ℓ.1, reflLink_mem_negLinks hN ℓ.2⟩)⁻¹
          else w ⟨reflLink ℓ.1, reflLink_mem_negLinks hN ℓ.2⟩)
        = w ⟨reflLink ℓ.1, reflLink_mem_negLinks hN ℓ.2⟩
      exact if_neg hc
    rw [hfun]
    exact measurable_pi_apply _

/-- The positive half weight, as an `ℝ≥0∞`-valued density,
is measurable. -/
theorem measurable_layerWeightPlus
    (hρcont : Continuous fun g : G => repMatrix ρ g) (β : ℝ) :
    Measurable fun y : ↥(halfLinks (N := N)) → G =>
      (layerWeightPlus ρ β y : ℝ≥0∞) := by
  have hreal : Measurable fun y : ↥(halfLinks (N := N)) → G =>
      Real.exp (- halfActionP ρ β (restrictPos y)) :=
    Real.measurable_exp.comp
      ((measurable_halfActionP_lf ρ hρcont β).comp
        measurable_restrictPos_lf).neg
  have hcoe : (fun y : ↥(halfLinks (N := N)) → G =>
        (layerWeightPlus ρ β y : ℝ≥0∞))
      = fun y => ENNReal.ofReal
          (Real.exp (- halfActionP ρ β (restrictPos y))) :=
    funext fun y =>
      (ENNReal.ofReal_eq_coe_nnreal (Real.exp_nonneg _)).symm
  rw [hcoe]
  exact ENNReal.measurable_ofReal.comp hreal

/-- The negative half weight, as an `ℝ≥0∞`-valued density,
is measurable. -/
theorem measurable_layerWeightMinus
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hN : Even N)
    (β : ℝ) :
    Measurable fun u : ↥(negLinks (N := N)) → G =>
      (layerWeightMinus ρ hN β u : ℝ≥0∞) := by
  have hreal : Measurable fun u : ↥(negLinks (N := N)) → G =>
      Real.exp (- halfActionP ρ β (mirrorP hN u)) :=
    Real.measurable_exp.comp
      ((measurable_halfActionP_lf ρ hρcont β).comp
        (measurable_mirrorP_lf (N := N) hN)).neg
  have hcoe : (fun u : ↥(negLinks (N := N)) → G =>
        (layerWeightMinus ρ hN β u : ℝ≥0∞))
      = fun u => ENNReal.ofReal
          (Real.exp (- halfActionP ρ β (mirrorP hN u))) :=
    funext fun u =>
      (ENNReal.ofReal_eq_coe_nnreal (Real.exp_nonneg _)).symm
  rw [hcoe]
  exact ENNReal.measurable_ofReal.comp hreal

/-- The layer Boltzmann factor, as an `ℝ≥0∞`-valued
density, is measurable. -/
theorem measurable_layerWeightZero
    (hρcont : Continuous fun g : G => repMatrix ρ g) (β : ℝ) :
    Measurable fun p : (↥(halfLinks (N := N)) → G)
        × (↥(negLinks (N := N)) → G) =>
      (layerWeightZero ρ β p : ℝ≥0∞) := by
  have hreal : Measurable fun p : (↥(halfLinks (N := N)) → G)
        × (↥(negLinks (N := N)) → G) =>
      Real.exp (- wilsonActionZero ρ β
        ((splitEquiv (halfLinks (N := N))).symm p)) :=
    Real.measurable_exp.comp
      ((measurable_wilsonActionZero_lf ρ hρcont β).comp
        (splitEquiv (halfLinks (N := N))).symm.measurable).neg
  have hcoe : (fun p : (↥(halfLinks (N := N)) → G)
        × (↥(negLinks (N := N)) → G) =>
        (layerWeightZero ρ β p : ℝ≥0∞))
      = fun p => ENNReal.ofReal
          (Real.exp (- wilsonActionZero ρ β
            ((splitEquiv (halfLinks (N := N))).symm p))) :=
    funext fun p =>
      (ENNReal.ofReal_eq_coe_nnreal (Real.exp_nonneg _)).symm
  rw [hcoe]
  exact ENNReal.measurable_ofReal.comp hreal

/-! ## §3. The split density factors

The pointwise content of the factorization: in split
variables, the Gibbs density is the product of the three
weights. This is Stage 1b-B's `wilsonAction_split_half`
(the action of the unsplit configuration is the positive
half action of the restriction, plus the *same* half action
of the mirror, plus the crossing action) fed through
`exp` of a sum. No basis expansion of the weight occurs
anywhere (charter D5): the density is manipulated as a
whole. -/

/-- The three weights multiply to the Gibbs density's
exponential, as `ℝ≥0` values: the symmetric split of the
density across the two halves and the layer. -/
theorem layerWeight_product (hN : Even N) (β : ℝ)
    (p : (↥(halfLinks (N := N)) → G) × (↥(negLinks (N := N)) → G)) :
    layerWeightPlus ρ β p.1
        * (layerWeightMinus ρ hN β p.2 * layerWeightZero ρ β p)
      = (⟨Real.exp (- wilsonAction (torusShift N) ρ β
          ((splitEquiv (halfLinks (N := N))).symm p)),
        Real.exp_nonneg _⟩ : ℝ≥0) := by
  apply Subtype.ext
  show Real.exp (- halfActionP ρ β (restrictPos p.1))
      * (Real.exp (- halfActionP ρ β (mirrorP hN p.2))
        * Real.exp (- wilsonActionZero ρ β
            ((splitEquiv (halfLinks (N := N))).symm p)))
      = Real.exp (- wilsonAction (torusShift N) ρ β
          ((splitEquiv (halfLinks (N := N))).symm p))
  rw [wilsonAction_split_half ρ hN β p, ← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

/-- The Gibbs density in split variables is the product of
the two half weights and the layer Boltzmann factor, as an
`ℝ≥0∞` density. -/
theorem gibbsDensity_split (hN : Even N) (β : ℝ)
    (p : (↥(halfLinks (N := N)) → G) × (↥(negLinks (N := N)) → G)) :
    (gibbsDensity (torusShift N) ρ β
        ((splitEquiv (halfLinks (N := N))).symm p) : ℝ≥0∞)
      = (layerWeightPlus ρ β p.1 : ℝ≥0∞)
        * ((layerWeightMinus ρ hN β p.2 : ℝ≥0∞)
          * (layerWeightZero ρ β p : ℝ≥0∞)) := by
  have h := congrArg (fun x : ℝ≥0 => (x : ℝ≥0∞))
    (layerWeight_product ρ hN β p)
  rw [ENNReal.coe_mul, ENNReal.coe_mul] at h
  exact h.symm

/-! ## §4. The layer factorization — the measure identity

The Gibbs measure, pushed forward along the split
coordinatization, is the scalar `Z⁻¹` times the product of
the two half product-Haar measures reweighted by the
product density of §3. The proof is definition unfolding
plus the transport of a set-lintegral along the
measure-preserving split equivalence — finite product
machinery only; no disintegration (the split is a
permutation of finitely many product factors). -/

/-- **R1, density form.** The Gibbs measure in split
coordinates: the product of the two half product measures,
weighted by the product of the two half weights and the
layer Boltzmann factor, normalized by the partition
function. At every real `β`, general `(G, ρ)`, even `N`. -/
theorem gibbsMeasure_map_splitEquiv_half
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ) :
    (gibbsMeasure (torusShift N) μG ρ β).map
        (splitEquiv (halfLinks (N := N)))
      = (ENNReal.ofReal (gibbsPartition (torusShift N) μG ρ β))⁻¹ •
        ((Measure.pi fun _ : ↥(halfLinks (N := N)) => μG).prod
            (Measure.pi fun _ : ↥(negLinks (N := N)) => μG)).withDensity
          (fun p => (layerWeightPlus ρ β p.1 : ℝ≥0∞)
            * ((layerWeightMinus ρ hN β p.2 : ℝ≥0∞)
              * (layerWeightZero ρ β p : ℝ≥0∞))) := by
  classical
  ext t ht
  have hmp := measurePreserving_splitEquiv μG (halfLinks (N := N))
  have hE : MeasurableEmbedding
      (⇑(splitEquiv (halfLinks (N := N)) :
        Config (Fin 4 → ZMod N) G ≃ᵐ
          ((↥(halfLinks (N := N)) → G) × (↥(negLinks (N := N)) → G)))) :=
    (splitEquiv (halfLinks (N := N))).measurableEmbedding
  -- Transport of the set-lintegral along the split: the
  -- preimage form of the layer factorization, via the
  -- measure-preserving split equivalence (no measurability
  -- side condition: the embedding form of the transport).
  have htrans : ∫⁻ U in (splitEquiv (halfLinks (N := N))) ⁻¹' t,
        (gibbsDensity (torusShift N) ρ β U : ℝ≥0∞)
          ∂(configMeasure μG)
      = ∫⁻ p in t, (gibbsDensity (torusShift N) ρ β
          ((splitEquiv (halfLinks (N := N))).symm p) : ℝ≥0∞)
        ∂((Measure.pi fun _ : ↥(halfLinks (N := N)) => μG).prod
          (Measure.pi fun _ : ↥(negLinks (N := N)) => μG)) := by
    calc ∫⁻ U in (splitEquiv (halfLinks (N := N))) ⁻¹' t,
          (gibbsDensity (torusShift N) ρ β U : ℝ≥0∞)
            ∂(configMeasure μG)
        = ∫⁻ U in (splitEquiv (halfLinks (N := N))) ⁻¹' t,
            (gibbsDensity (torusShift N) ρ β
              ((splitEquiv (halfLinks (N := N))).symm
                ((splitEquiv (halfLinks (N := N))) U)) : ℝ≥0∞)
            ∂(configMeasure μG) :=
          setLIntegral_congr_fun
            ((splitEquiv (halfLinks (N := N))).measurable ht)
            (fun U _ => by rw [MeasurableEquiv.symm_apply_apply])
      _ = ∫⁻ p in t, (gibbsDensity (torusShift N) ρ β
            ((splitEquiv (halfLinks (N := N))).symm p) : ℝ≥0∞)
          ∂((Measure.pi fun _ : ↥(halfLinks (N := N)) => μG).prod
            (Measure.pi fun _ : ↥(negLinks (N := N)) => μG)) :=
          hmp.setLIntegral_comp_preimage_emb hE
            (fun p : (↥(halfLinks (N := N)) → G)
              × (↥(negLinks (N := N)) → G) =>
              (gibbsDensity (torusShift N) ρ β
                ((splitEquiv (halfLinks (N := N))).symm p) : ℝ≥0∞)) t
  -- The left side, evaluated on `t`: unfold the Gibbs
  -- measure and transport.
  have hLHS : (gibbsMeasure (torusShift N) μG ρ β).map
        (splitEquiv (halfLinks (N := N))) t
      = (ENNReal.ofReal (gibbsPartition (torusShift N) μG ρ β))⁻¹
        * ∫⁻ p in t, (gibbsDensity (torusShift N) ρ β
            ((splitEquiv (halfLinks (N := N))).symm p) : ℝ≥0∞)
          ∂((Measure.pi fun _ : ↥(halfLinks (N := N)) => μG).prod
            (Measure.pi fun _ : ↥(negLinks (N := N)) => μG)) := by
    rw [Measure.map_apply (splitEquiv (halfLinks (N := N))).measurable ht]
    show gibbsMeasure (torusShift N) μG ρ β
        ((splitEquiv (halfLinks (N := N))) ⁻¹' t) = _
    unfold gibbsMeasure
    rw [Measure.smul_apply, smul_eq_mul,
      withDensity_apply _
        ((splitEquiv (halfLinks (N := N))).measurable ht), htrans]
  -- The right side, evaluated on `t`: the density is the
  -- product of the three weights, by §3.
  have hRHS : ((ENNReal.ofReal
        (gibbsPartition (torusShift N) μG ρ β))⁻¹ •
        ((Measure.pi fun _ : ↥(halfLinks (N := N)) => μG).prod
            (Measure.pi fun _ : ↥(negLinks (N := N)) => μG)).withDensity
          (fun p => (layerWeightPlus ρ β p.1 : ℝ≥0∞)
            * ((layerWeightMinus ρ hN β p.2 : ℝ≥0∞)
              * (layerWeightZero ρ β p : ℝ≥0∞)))) t
      = (ENNReal.ofReal (gibbsPartition (torusShift N) μG ρ β))⁻¹
        * ∫⁻ p in t, (gibbsDensity (torusShift N) ρ β
            ((splitEquiv (halfLinks (N := N))).symm p) : ℝ≥0∞)
          ∂((Measure.pi fun _ : ↥(halfLinks (N := N)) => μG).prod
            (Measure.pi fun _ : ↥(negLinks (N := N)) => μG)) := by
    rw [Measure.smul_apply, smul_eq_mul, withDensity_apply _ ht]
    congr 1
    exact setLIntegral_congr_fun ht
      (fun p _ => (gibbsDensity_split ρ hN β p).symm)
  rw [hLHS, hRHS]

/-! ## §5. The factored form

The product of the two half Gibbs-type measures is the
product product measure weighted by the product of the two
half weights (`prod_withDensity`); absorbing the layer
factor as a second density (`withDensity_mul₀`) then gives
the headline in its factored form: the Gibbs measure in
split coordinates is the scalar `Z⁻¹` times the product of
the two half Gibbs-type measures, reweighted by the layer
Boltzmann factor — the layer / Markov factorization. -/

/-- The product of the two half Gibbs-type measures is the
product product measure weighted by the product of the two
half Boltzmann weights. -/
theorem halfGibbs_prod
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ) :
    (halfGibbsPlus μG ρ β).prod (halfGibbsMinus μG ρ hN β)
      = ((Measure.pi fun _ : ↥(halfLinks (N := N)) => μG).prod
          (Measure.pi fun _ : ↥(negLinks (N := N)) => μG)).withDensity
        (fun p => (layerWeightPlus ρ β p.1 : ℝ≥0∞)
          * (layerWeightMinus ρ hN β p.2 : ℝ≥0∞)) := by
  unfold halfGibbsPlus halfGibbsMinus
  exact prod_withDensity
    (measurable_layerWeightPlus ρ hρcont β)
    (measurable_layerWeightMinus ρ hρcont hN β)

/-- **R1, factored form (the layer / Markov
factorization).** The Gibbs measure, pushed forward along
the split coordinatization at the middle layer, is the
normalizing scalar times the product of the two half
Gibbs-type measures, reweighted by the layer Boltzmann
factor `exp (−S₀)`. At every real `β`, general `(G, ρ)`,
even `N`. -/
theorem gibbsMeasure_map_splitEquiv
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ) :
    (gibbsMeasure (torusShift N) μG ρ β).map
        (splitEquiv (halfLinks (N := N)))
      = (ENNReal.ofReal (gibbsPartition (torusShift N) μG ρ β))⁻¹ •
        ((halfGibbsPlus μG ρ β).prod
          (halfGibbsMinus μG ρ hN β)).withDensity
          (fun p => (layerWeightZero ρ β p : ℝ≥0∞)) := by
  rw [gibbsMeasure_map_splitEquiv_half μG ρ hρcont hN β]
  congr 1
  have hsplit : ((Measure.pi fun _ : ↥(halfLinks (N := N)) => μG).prod
        (Measure.pi fun _ : ↥(negLinks (N := N)) => μG)).withDensity
        (fun p => (layerWeightPlus ρ β p.1 : ℝ≥0∞)
          * ((layerWeightMinus ρ hN β p.2 : ℝ≥0∞)
            * (layerWeightZero ρ β p : ℝ≥0∞)))
      = (((Measure.pi fun _ : ↥(halfLinks (N := N)) => μG).prod
          (Measure.pi fun _ : ↥(negLinks (N := N)) => μG)).withDensity
          (fun p => (layerWeightPlus ρ β p.1 : ℝ≥0∞)
            * (layerWeightMinus ρ hN β p.2 : ℝ≥0∞))).withDensity
        (fun p => (layerWeightZero ρ β p : ℝ≥0∞)) := by
    rw [← withDensity_mul₀]
    · congr 1
      funext p
      simp only [Pi.mul_apply]
      exact (mul_assoc _ _ _).symm
    · exact (((measurable_layerWeightPlus ρ hρcont β).comp
          measurable_fst).mul
        ((measurable_layerWeightMinus ρ hρcont hN β).comp
          measurable_snd)).aemeasurable
    · exact (measurable_layerWeightZero ρ hρcont β).aemeasurable
  rw [hsplit, ← halfGibbs_prod μG ρ hρcont hN β]

/-! ## §6. The iterated-expectation form

The form the transfer-matrix iteration (R3) consumes: the
Gibbs expectation of a two-slice observable, read in split
coordinates, is the pairing of the observable against the
layer Boltzmann factor under the product of the two half
Gibbs-type measures (with the normalizing scalar), and
that pairing iterates over the two halves by Fubini. -/

/-- The layer Boltzmann factor, as an `ℝ≥0`-valued
function, is measurable (the form
`integral_withDensity_eq_integral_smul` consumes). -/
theorem measurable_layerWeightZero_nn
    (hρcont : Continuous fun g : G => repMatrix ρ g) (β : ℝ) :
    Measurable fun p : (↥(halfLinks (N := N)) → G)
        × (↥(negLinks (N := N)) → G) => layerWeightZero ρ β p := by
  have hreal : Measurable fun p : (↥(halfLinks (N := N)) → G)
        × (↥(negLinks (N := N)) → G) =>
      Real.exp (- wilsonActionZero ρ β
        ((splitEquiv (halfLinks (N := N))).symm p)) :=
    Real.measurable_exp.comp
      ((measurable_wilsonActionZero_lf ρ hρcont β).comp
        (splitEquiv (halfLinks (N := N))).symm.measurable).neg
  exact hreal.subtype_mk

/-- **R1, expectation form.** The Gibbs expectation of a
split-coordinate observable is the layer-factor pairing
under the product of the two half Gibbs-type measures. -/
theorem integral_splitEquiv_factor
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (Φ : ((↥(halfLinks (N := N)) → G)
      × (↥(negLinks (N := N)) → G)) → ℂ)
    (hΦ : StronglyMeasurable Φ) :
    ∫ U, Φ ((splitEquiv (halfLinks (N := N))) U)
        ∂(gibbsMeasure (torusShift N) μG ρ β)
      = ∫ p, (layerWeightZero ρ β p) • Φ p
          ∂((ENNReal.ofReal (gibbsPartition (torusShift N) μG ρ β))⁻¹ •
            ((halfGibbsPlus μG ρ β).prod
              (halfGibbsMinus μG ρ hN β))) := by
  rw [← integral_map (splitEquiv (halfLinks (N := N))).measurable.aemeasurable
      hΦ.aestronglyMeasurable,
    gibbsMeasure_map_splitEquiv μG ρ hρcont hN β,
    ← withDensity_smul_measure,
    integral_withDensity_eq_integral_smul
      (measurable_layerWeightZero_nn ρ hρcont β) Φ]

/-- **R1, iterated form.** The layer-factor pairing
iterates over the two halves (Fubini): integrate the
negative-half variable first, then the closed-half
variable. -/
theorem integral_layerFactor_iterated (hN : Even N) (β : ℝ)
    (Φ : ((↥(halfLinks (N := N)) → G)
      × (↥(negLinks (N := N)) → G)) → ℂ)
    (hΦ : Integrable (fun p => (layerWeightZero ρ β p) • Φ p)
      ((halfGibbsPlus μG ρ β).prod (halfGibbsMinus μG ρ hN β))) :
    ∫ p, (layerWeightZero ρ β p) • Φ p
        ∂((halfGibbsPlus μG ρ β).prod (halfGibbsMinus μG ρ hN β))
      = ∫ y, ∫ u, (layerWeightZero ρ β
            ((y, u) : (↥(halfLinks (N := N)) → G)
              × (↥(negLinks (N := N)) → G))) • Φ
            ((y, u) : (↥(halfLinks (N := N)) → G)
              × (↥(negLinks (N := N)) → G))
          ∂(halfGibbsMinus μG ρ hN β) ∂(halfGibbsPlus μG ρ β) := by
  have hS1 : SFinite (halfGibbsPlus μG ρ β) :=
    Measure.withDensity.instSFinite
      (μ := Measure.pi fun _ : ↥(halfLinks (N := N)) => μG)
      (f := fun y => (layerWeightPlus ρ β y : ℝ≥0∞))
  have hS2 : SFinite (halfGibbsMinus μG ρ hN β) :=
    Measure.withDensity.instSFinite
      (μ := Measure.pi fun _ : ↥(negLinks (N := N)) => μG)
      (f := fun u => (layerWeightMinus ρ hN β u : ℝ≥0∞))
  exact integral_prod _ hΦ
