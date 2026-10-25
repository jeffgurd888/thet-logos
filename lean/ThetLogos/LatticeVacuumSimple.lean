/-
# ThetLogos.LatticeVacuumSimple — the D-1 weld: vacuum simplicity
at the U(1) seat

Brick: the D-1 weld, named by the frontier gate
(`whitepaper/frontier-gate-scoping-2026-10-25.md` §2.1) and by
FG-1's addendum (`whitepaper/frontier-fg1-formulation-2026-10-25.md`
§5) as the next brick after FG-1: discharge clause **(b)** of
`TransferFormPos` — vacuum simplicity for `transferOp` on
`osSpace` — at the circle seat `(haarProb Circle, circleRep)`,
for `β > 0` (the proof below is in fact `β`-sign-independent:
it works at every real `β`, and the all-`β` statement is the
one proved; the `β > 0` headline is recorded separately).

## Route

Classical Perron–Frobenius / Jentzsch, in form language.
Everything is routed through the landed form identity
`transferOp_inner` (every real `β`, no `Even N`):

  `⟪g, T f⟫ = ∫ U, conj (g (restr₀ U)) * f (next U) ∂Gibbs`.

* **(FI) form improvement** (§2): the Gibbs density
  `exp (−S_β)` is pointwise strictly positive with two-sided
  exponential bounds (`wilsonAction_abs_le`), so the Gibbs
  measure is equivalent to the configuration (product Haar)
  measure; the two readings `restr₀`, `next` depend on
  disjoint link coordinates (`sliceLinks` vs `slice1Links`),
  and the landed Fubini factorization `integral_pi_split_mul`
  makes their joint law charge every product of
  positive-measure slice sets. Hence for `g, f` a.e.
  real-nonnegative and nonzero, `0 < ⟪g, T f⟫.re`.
* **Modulus** (§3): `T v = v` implies `T |v| = |v|`, from
  (FI)-free integral comparison plus the landed contraction
  `transferOp_norm_le` — pure norm algebra, no
  Cauchy–Schwarz equality case, no self-adjointness.
* **Real endgame** (§4): a real fixed `r` splits as
  `r = r⁺ − r⁻` with `r± = (|r| ± r)/2` both fixed;
  `⟪r⁻, T r⁺⟫ = ⟪r⁻, r⁺⟫ = 0`, so (FI) kills one of them:
  `r` is one-signed; subtracting its vacuum component and
  applying (FI) once more against `Ω` gives `r ∈ ℂ ∙ Ω`.
* **Complex assembly** (§5): `T` commutes with `star`
  (form identity again), so `Re v`, `Im v` are real fixed
  vectors, and §4 closes `v ∈ ℂ ∙ Ω`.

## Assembly

With FG-1's clause (a) (`transferDiagU1_circle`, landed),
`TransferFormPosU1 β hN2` follows at every `β > 0` (even `N`),
and with Q12's `transferOp_compact_of_HDen` the full
per-instance package `GapPackageU1` — hence a per-instance
gap bound `∃ δ > 0, GapBoundU1 β hN2 δ` at the seat, `β > 0` —
is assembled **modulo the named hypothesis `HDen` alone**.
`HDen` is NOT discharged here: its formalization is the
disintegration project named in Q12's fence, a separate
brick. Compactness at general `β` remains exactly as
conditional as Q12 left it.

**NO CLAIM** — parts of any Clay statement closed by this
module: 0. Dials: 0/4. Stage 1b-B at general `(G, ρ)` remains
OPEN and untouched: clause (b) here is the circle seat only,
proved from the seat's Gibbs kernel, not from any
general-`(G, ρ)` positivity.
-/

import ThetLogos.LatticeUniformGap

namespace ThetLogos

open MeasureTheory Finset
open scoped Matrix ENNReal NNReal InnerProduct

section VacuumSimple

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ))
  {N : ℕ} [NeZero N]

/-! ## §1. The Gibbs density: two-sided bounds, and positivity
of joint slice events -/

/-- The Wilson-action bound constant on the torus:
`|S_β U| ≤ actionBound (N := N) β` is `wilsonAction_abs_le`. -/
noncomputable def actionBound (β : ℝ) : ℝ :=
  |β| * (2 * (16 * (Fintype.card (Fin 4 → ZMod N) : ℝ)))

/-- The Gibbs density is bounded above by a positive
exponential constant, pointwise. -/
theorem gibbsDensity_le (hd : 0 < d) (β : ℝ)
    (U : Config (Fin 4 → ZMod N) G) :
    (gibbsDensity (torusShift N) ρ β U : ℝ≥0∞)
      ≤ ENNReal.ofReal (Real.exp (actionBound (N := N) β)) := by
  rw [gibbsDensity_coe]
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_monotone
  have h := wilsonAction_abs_le (torusShift N) ρ hd β U
  unfold actionBound
  linarith [neg_le_abs (wilsonAction (torusShift N) ρ β U)]

/-- The Gibbs density is bounded below by a positive
exponential constant, pointwise. This is the strict
positivity the whole weld rests on: the Gibbs measure is
equivalent to the configuration measure. -/
theorem gibbsDensity_ge (hd : 0 < d) (β : ℝ)
    (U : Config (Fin 4 → ZMod N) G) :
    ENNReal.ofReal (Real.exp (- actionBound (N := N) β))
      ≤ (gibbsDensity (torusShift N) ρ β U : ℝ≥0∞) := by
  rw [gibbsDensity_coe]
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_monotone
  have h := wilsonAction_abs_le (torusShift N) ρ hd β U
  unfold actionBound
  have h2 := le_of_abs_le h
  linarith

/-- Upper bound of a Gibbs set-mass by the configuration
mass, up to explicit positive constants. -/
theorem gibbsMeasure_le (hd : 0 < d)
    (hρcont : Continuous fun g : G => repMatrix ρ g) (β : ℝ)
    {E : Set (Config (Fin 4 → ZMod N) G)} (hE : MeasurableSet E) :
    gibbsMeasure (torusShift N) μG ρ β E
      ≤ (ENNReal.ofReal (gibbsPartition (torusShift N) μG ρ β))⁻¹
        * (ENNReal.ofReal (Real.exp (actionBound (N := N) β))
          * configMeasure μG E) := by
  unfold gibbsMeasure
  rw [Measure.smul_apply, smul_eq_mul, withDensity_apply _ hE]
  refine mul_le_mul le_rfl ?_ zero_le zero_le
  calc ∫⁻ a in E, (gibbsDensity (torusShift N) ρ β a : ℝ≥0∞)
        ∂(configMeasure μG)
      ≤ ∫⁻ _a in E, ENNReal.ofReal (Real.exp (actionBound (N := N) β))
          ∂(configMeasure μG) :=
        lintegral_mono_ae (Filter.Eventually.of_forall
          fun a => gibbsDensity_le ρ hd β a)
    _ = ENNReal.ofReal (Real.exp (actionBound (N := N) β))
          * configMeasure μG E :=
        setLIntegral_const E _

/-- Lower bound of a Gibbs set-mass by the configuration
mass, up to explicit positive constants. -/
theorem gibbsMeasure_ge (hd : 0 < d)
    (hρcont : Continuous fun g : G => repMatrix ρ g) (β : ℝ)
    {E : Set (Config (Fin 4 → ZMod N) G)} (hE : MeasurableSet E) :
    (ENNReal.ofReal (gibbsPartition (torusShift N) μG ρ β))⁻¹
        * (ENNReal.ofReal (Real.exp (- actionBound (N := N) β))
          * configMeasure μG E)
      ≤ gibbsMeasure (torusShift N) μG ρ β E := by
  unfold gibbsMeasure
  rw [Measure.smul_apply, smul_eq_mul, withDensity_apply _ hE]
  refine mul_le_mul le_rfl ?_ zero_le zero_le
  calc ENNReal.ofReal (Real.exp (- actionBound (N := N) β))
          * configMeasure μG E
      = ∫⁻ _a in E, ENNReal.ofReal (Real.exp (- actionBound (N := N) β))
          ∂(configMeasure μG) :=
        (setLIntegral_const E _).symm
    _ ≤ ∫⁻ a in E, (gibbsDensity (torusShift N) ρ β a : ℝ≥0∞)
          ∂(configMeasure μG) :=
        lintegral_mono_ae (Filter.Eventually.of_forall
          fun a => gibbsDensity_ge ρ hd β a)

/-- A slice set of positive Gibbs-marginal mass has positive
product-Haar mass: the upper density bound transfers
positivity from `sliceMeasure` to the pi marginal. -/
theorem pi_pos_of_sliceMeasure_pos (hd : 0 < d)
    (hρcont : Continuous fun g : G => repMatrix ρ g) (β : ℝ)
    {A : Set (↥(sliceLinks (N := N)) → G)} (hA : MeasurableSet A)
    (hApos : 0 < sliceMeasure (N := N) μG ρ β A) :
    0 < (Measure.pi fun _ : ↥(sliceLinks (N := N)) => μG) A := by
  have hmap : (configMeasure μG).map
        (restrictConfig (G := G) sliceLinks)
      = Measure.pi fun _ : ↥(sliceLinks (N := N)) => μG := by
    have h := marginalMeasure_pi (μG := μG)
      (s := sliceLinks (N := N)) (ι := Link (Fin 4 → ZMod N))
      (G := G)
    rwa [show marginalMeasure
          (Measure.pi fun _ : Link (Fin 4 → ZMod N) => μG)
          (sliceLinks (N := N))
        = (configMeasure μG).map
          (restrictConfig (G := G) sliceLinks) from rfl] at h
  have hcfg : configMeasure μG
        (restrictConfig (G := G) sliceLinks ⁻¹' A)
      = (Measure.pi fun _ : ↥(sliceLinks (N := N)) => μG) A := by
    rw [← hmap, Measure.map_apply
      (measurable_restrictConfig sliceLinks) hA]
  have hgib : gibbsMeasure (torusShift N) μG ρ β
        (restrictConfig (G := G) sliceLinks ⁻¹' A)
      = sliceMeasure (N := N) μG ρ β A :=
    (Measure.map_apply (measurable_restrictConfig sliceLinks)
      hA).symm
  have hle := gibbsMeasure_le μG ρ hd hρcont β
    ((measurable_restrictConfig sliceLinks) hA)
  rw [hgib, hcfg] at hle
  by_contra hcon
  have h0 : (Measure.pi fun _ : ↥(sliceLinks (N := N)) => μG) A
      = 0 := le_antisymm (not_lt.mp hcon) zero_le
  rw [h0, mul_zero, mul_zero] at hle
  exact not_lt.mpr hle hApos

end VacuumSimple

section JointPositivity

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ))
  {N : ℕ} [NeZero N]

/-- A time-`1` link lies outside the time-`0` slice: the two
strata are disjoint. -/
theorem slice1Link_not_mem_sliceLinks
    {ℓ : Link (Fin 4 → ZMod N)} (hℓ : ℓ ∈ slice1Links (N := N)) :
    ℓ ∉ sliceLinks (N := N) :=
  fun h => (Finset.disjoint_left.mp
    (sliceLinks_disjoint_slice1Links (N := N))) h hℓ

/-- The next-slice reading, factored through the complement
coordinates: `nextConfig U` depends on `U` only through its
restriction to `sliceLinksᶜ`. -/
noncomputable def nextOfRest (hN2 : 2 ≤ N)
    (w : ↥(sliceLinks (N := N))ᶜ → G) : ↥(sliceLinks (N := N)) → G :=
  sliceStep hN2 (fun ℓ => w ⟨ℓ.1, Finset.mem_compl.mpr
    (slice1Link_not_mem_sliceLinks ℓ.2)⟩)

theorem nextOfRest_apply (hN2 : 2 ≤ N)
    (w : ↥(sliceLinks (N := N))ᶜ → G) (ℓ : ↥(sliceLinks (N := N))) :
    nextOfRest (N := N) hN2 w ℓ
      = w ⟨(slice01Equiv hN2 ℓ).1, Finset.mem_compl.mpr
          (slice1Link_not_mem_sliceLinks (slice01Equiv hN2 ℓ).2)⟩ :=
  rfl

theorem measurable_nextOfRest (hN2 : 2 ≤ N) :
    Measurable (nextOfRest (G := G) (N := N) hN2) := by
  unfold nextOfRest
  apply Measurable.comp (measurable_sliceStep hN2)
  exact Measurable.of_eval fun ℓ =>
    measurable_pi_apply (⟨ℓ.1, Finset.mem_compl.mpr
      (slice1Link_not_mem_sliceLinks ℓ.2)⟩ :
        ↥(sliceLinks (N := N))ᶜ)

/-- The factorization is exact, pointwise. -/
theorem nextConfig_eq_nextOfRest (hN2 : 2 ≤ N)
    (U : Config (Fin 4 → ZMod N) G) :
    nextConfig hN2 U
      = nextOfRest (N := N) hN2 (restrictConfig (sliceLinks (N := N))ᶜ U) :=
  rfl

/-- The slice-`1` links, viewed as a finset of the complement
index type. -/
def slice1InCompl : Finset ↥(sliceLinks (N := N))ᶜ :=
  Finset.univ.filter (fun x => x.1 ∈ slice1Links (N := N))

/-- The reindexing between time-`0` links and the slice-`1`
links inside the complement, via `slice01Equiv`. -/
def sliceToCompl (hN2 : 2 ≤ N) :
    ↥(sliceLinks (N := N)) ≃ ↥(slice1InCompl (N := N)) where
  toFun ℓ := ⟨⟨(slice01Equiv hN2 ℓ).1, Finset.mem_compl.mpr
      (slice1Link_not_mem_sliceLinks (slice01Equiv hN2 ℓ).2)⟩,
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (slice01Equiv hN2 ℓ).2⟩⟩
  invFun y := (slice01Equiv hN2).symm ⟨y.1.1,
    Finset.mem_filter.mp y.2 |>.2⟩
  left_inv ℓ := by
    show (slice01Equiv hN2).symm ⟨(slice01Equiv hN2 ℓ).1,
      (slice01Equiv hN2 ℓ).2⟩ = ℓ
    exact Equiv.symm_apply_apply _ ℓ
  right_inv y := by
    apply Subtype.ext
    apply Subtype.ext
    show (slice01Equiv hN2 ((slice01Equiv hN2).symm ⟨y.1.1, _⟩)).1
        = y.1.1
    rw [Equiv.apply_symm_apply]

/-- Precomposition with `sliceToCompl` is measure-preserving
between the pi measures: it is `piCongrLeft` of the inverse
equivalence. -/
theorem measurePreserving_sliceToCompl_precomp (hN2 : 2 ≤ N) :
    MeasurePreserving
      (fun w : ↥(slice1InCompl (N := N)) → G =>
        fun ℓ => w (sliceToCompl (N := N) hN2 ℓ))
      (Measure.pi fun _ : ↥(slice1InCompl (N := N)) => μG)
      (Measure.pi fun _ : ↥(sliceLinks (N := N)) => μG) := by
  have hfun : (fun w : ↥(slice1InCompl (N := N)) → G =>
        fun ℓ => w (sliceToCompl (N := N) hN2 ℓ))
      = ⇑(MeasurableEquiv.piCongrLeft (fun _ => G)
          (sliceToCompl (N := N) hN2).symm) := by
    funext w ℓ
    conv_rhs => rw [← Equiv.symm_apply_apply
      (sliceToCompl (N := N) hN2) ℓ]
    exact (MeasurableEquiv.piCongrLeft_apply_apply
      (β := fun _ : ↥(sliceLinks (N := N)) => G) _ _ _).symm
  rw [hfun]
  exact measurePreserving_piCongrLeft (fun _ => μG)
    (sliceToCompl (N := N) hN2).symm

/-- `nextOfRest` is the complement restriction followed by the
`sliceToCompl` reindexing and `sliceStep`. -/
theorem nextOfRest_eq (hN2 : 2 ≤ N)
    (w : ↥(sliceLinks (N := N))ᶜ → G) :
    nextOfRest (N := N) hN2 w
      = (fun ℓ => (restrictConfig (slice1InCompl (N := N)) w)
          (sliceToCompl (N := N) hN2 ℓ)) := by
  funext ℓ
  rw [nextOfRest_apply]
  rfl

/-- The complement pi-mass of a `nextOfRest` preimage is the
slice pi-mass: the next-slice reading is measure-preserving
onto the slice law, through the split. -/
theorem pi_compl_nextOfRest_preimage (hN2 : 2 ≤ N)
    {B : Set (↥(sliceLinks (N := N)) → G)} (hB : MeasurableSet B) :
    (Measure.pi fun _ : ↥(sliceLinks (N := N))ᶜ => μG)
        (nextOfRest (N := N) hN2 ⁻¹' B)
      = (Measure.pi fun _ : ↥(sliceLinks (N := N)) => μG) B := by
  have hpre : nextOfRest (N := N) hN2 ⁻¹' B
      = restrictConfig (slice1InCompl (N := N)) ⁻¹'
        ((fun w : ↥(slice1InCompl (N := N)) → G =>
          fun ℓ => w (sliceToCompl (N := N) hN2 ℓ)) ⁻¹' B) := by
    ext w
    simp only [Set.mem_preimage]
    rw [nextOfRest_eq]
  rw [hpre, ← Measure.map_apply (measurable_restrictConfig _)
    ((measurePreserving_sliceToCompl_precomp (μG := μG) hN2).measurable hB)]
  have hmarg : marginalMeasure
        (Measure.pi fun _ : ↥(sliceLinks (N := N))ᶜ => μG)
        (slice1InCompl (N := N))
      = Measure.pi fun _ : ↥(slice1InCompl (N := N)) => μG :=
    marginalMeasure_pi (μG := μG) (s := slice1InCompl (N := N))
      (ι := ↥(sliceLinks (N := N))ᶜ) (G := G)
  have hmap : (Measure.pi fun _ : ↥(sliceLinks (N := N))ᶜ => μG).map
        (restrictConfig (slice1InCompl (N := N)))
      = Measure.pi fun _ : ↥(slice1InCompl (N := N)) => μG := hmarg
  rw [hmap, ← (measurePreserving_sliceToCompl_precomp
    (μG := μG) hN2).map_eq]
  exact (Measure.map_apply
    (measurePreserving_sliceToCompl_precomp (μG := μG) hN2).measurable
    hB).symm

/-- The configuration mass of a joint slice event factors
and is positive: the two readings are independent under the
product Haar measure, and each charges its positive-mass
slice sets. -/
theorem config_joint_pos (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hd : 0 < d)
    (β : ℝ)
    {A B : Set (↥(sliceLinks (N := N)) → G)}
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hApos : 0 < sliceMeasure (N := N) μG ρ β A)
    (hBpos : 0 < sliceMeasure (N := N) μG ρ β B) :
    0 < configMeasure μG
      (restrictConfig (G := G) sliceLinks ⁻¹' A
        ∩ nextConfig hN2 ⁻¹' B) := by
  have hpiA : 0 < (Measure.pi fun _ : ↥(sliceLinks (N := N)) => μG) A :=
    pi_pos_of_sliceMeasure_pos μG ρ hd hρcont β hA hApos
  have hpiB : 0 < (Measure.pi fun _ : ↥(sliceLinks (N := N)) => μG) B :=
    pi_pos_of_sliceMeasure_pos μG ρ hd hρcont β hB hBpos
  have htoA : 0 < ((Measure.pi fun _ : ↥(sliceLinks (N := N)) => μG).real A) :=
    ENNReal.toReal_pos hpiA.ne' (measure_ne_top _ _)
  have htoB : 0 < ((Measure.pi fun _ : ↥(sliceLinks (N := N)) => μG).real B) :=
    ENNReal.toReal_pos hpiB.ne' (measure_ne_top _ _)
  have hsmul : ∀ r : ℝ, r • (1 : ℂ) = (r : ℂ) := fun r => by
    simp [Algebra.smul_def]
  -- The two factor integrals.
  have hfst : (∫ v, A.indicator (fun _ => (1 : ℂ)) v
        ∂(Measure.pi fun _ : ↥(sliceLinks (N := N)) => μG))
      = ((Measure.pi fun _ : ↥(sliceLinks (N := N)) => μG).real A : ℂ) := by
    rw [integral_indicator_const _ hA, hsmul]
  have hsnd : (∫ w, (B.indicator (fun _ => (1 : ℂ)) ∘ nextOfRest (N := N) hN2) w
        ∂(Measure.pi fun _ : ↥(sliceLinks (N := N))ᶜ => μG))
      = ((Measure.pi fun _ : ↥(sliceLinks (N := N)) => μG).real B : ℂ) := by
    have hmapEq : (Measure.pi fun _ : ↥(sliceLinks (N := N))ᶜ => μG).map
          (nextOfRest (N := N) hN2)
        = Measure.pi fun _ : ↥(sliceLinks (N := N)) => μG :=
      Measure.ext fun s hs => by
        rw [Measure.map_apply (measurable_nextOfRest (N := N) hN2) hs]
        exact pi_compl_nextOfRest_preimage (μG := μG) hN2 hs
    have h2 : (∫ y, B.indicator (fun _ => (1 : ℂ)) y
          ∂((Measure.pi fun _ : ↥(sliceLinks (N := N))ᶜ => μG).map
            (nextOfRest (N := N) hN2)))
        = ((Measure.pi fun _ : ↥(sliceLinks (N := N)) => μG).real B : ℂ) := by
      rw [integral_indicator_const _ hB, hmapEq, hsmul]
    rwa [integral_map (measurable_nextOfRest (N := N) hN2).aemeasurable
      (stronglyMeasurable_const.indicator hB).aestronglyMeasurable]
      at h2
  -- The Bochner integral of the joint indicator factors.
  have hInt : (∫ U, (restrictConfig (G := G) sliceLinks ⁻¹' A
        ∩ nextConfig hN2 ⁻¹' B).indicator (fun _ => (1 : ℂ)) U
        ∂(configMeasure μG))
      = ((Measure.pi fun _ : ↥(sliceLinks (N := N)) => μG).real A : ℂ)
        * ((Measure.pi fun _ : ↥(sliceLinks (N := N)) => μG).real B : ℂ) := by
    have hpt : ∀ U : Config (Fin 4 → ZMod N) G,
        (restrictConfig (G := G) sliceLinks ⁻¹' A
          ∩ nextConfig hN2 ⁻¹' B).indicator (fun _ => (1 : ℂ)) U
        = A.indicator (fun _ => (1 : ℂ)) (restrictConfig (G := G) sliceLinks U)
          * (B.indicator (fun _ => (1 : ℂ)) ∘ nextOfRest (N := N) hN2)
            (restrictConfig (G := G) (sliceLinks (N := N))ᶜ U) := by
      intro U
      have hnx : nextConfig hN2 U = nextOfRest (N := N) hN2
          (restrictConfig (G := G) (sliceLinks (N := N))ᶜ U) :=
        nextConfig_eq_nextOfRest (N := N) hN2 U
      by_cases h0 : restrictConfig (G := G) sliceLinks U ∈ A <;>
        by_cases h1 : nextOfRest (N := N) hN2
          (restrictConfig (G := G) (sliceLinks (N := N))ᶜ U) ∈ B <;>
        simp [Set.indicator_of_mem, Set.indicator_of_notMem,
          Function.comp_apply, h0, h1, hnx]
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
    show (∫ U, A.indicator (fun _ => (1 : ℂ)) (fun ℓ : ↥(sliceLinks (N := N)) => U ℓ.1)
        * (B.indicator (fun _ => (1 : ℂ)) ∘ nextOfRest (N := N) hN2)
          (fun ℓ : ↥(sliceLinks (N := N))ᶜ => U ℓ.1)
        ∂(Measure.pi fun _ : Link (Fin 4 → ZMod N) => μG)) = _
    rw [integral_pi_split_mul μG (sliceLinks (N := N))
      (A.indicator (fun _ => (1 : ℂ))) (B.indicator (fun _ => (1 : ℂ)) ∘ nextOfRest (N := N) hN2),
      hfst, hsnd]
  -- Hence the mass's `toReal` is positive.
  have hE : MeasurableSet (restrictConfig (G := G) sliceLinks ⁻¹' A
      ∩ nextConfig hN2 ⁻¹' B) :=
    ((measurable_restrictConfig sliceLinks) hA).inter
      ((measurable_nextConfig hN2) hB)
  have hmass : ((configMeasure μG).real (restrictConfig (G := G) sliceLinks ⁻¹' A ∩ nextConfig hN2 ⁻¹' B))
      = ((Measure.pi fun _ : ↥(sliceLinks (N := N)) => μG).real A)
        * ((Measure.pi fun _ : ↥(sliceLinks (N := N)) => μG).real B) := by
    have h := integral_indicator_const (μ := configMeasure μG)
      (1 : ℂ) hE
    rw [hInt, hsmul] at h
    rw [← Complex.ofReal_mul] at h
    exact (Complex.ofReal_inj.mp h).symm
  have hpos : 0 < ((configMeasure μG).real (restrictConfig (G := G) sliceLinks ⁻¹' A ∩ nextConfig hN2 ⁻¹' B)) := by
    rw [hmass]
    exact mul_pos htoA htoB
  have hpos' : 0 < ((configMeasure μG) (restrictConfig (G := G)
      sliceLinks ⁻¹' A ∩ nextConfig hN2 ⁻¹' B)).toReal := hpos
  exact (ENNReal.toReal_pos_iff.mp hpos').1

/-- **Joint Gibbs positivity:** the two-slice Gibbs law
charges every product of positive-slice-mass sets. This is
the strict positivity the weld rests on: the Gibbs density
is bounded below, and the configuration law makes the two
readings independent. -/
theorem gibbs_joint_pos (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hd : 0 < d)
    (β : ℝ)
    {A B : Set (↥(sliceLinks (N := N)) → G)}
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hApos : 0 < sliceMeasure (N := N) μG ρ β A)
    (hBpos : 0 < sliceMeasure (N := N) μG ρ β B) :
    0 < gibbsMeasure (torusShift N) μG ρ β
      (restrictConfig (G := G) sliceLinks ⁻¹' A
        ∩ nextConfig hN2 ⁻¹' B) := by
  have hE : MeasurableSet (restrictConfig (G := G) sliceLinks ⁻¹' A
      ∩ nextConfig hN2 ⁻¹' B) :=
    ((measurable_restrictConfig sliceLinks) hA).inter
      ((measurable_nextConfig hN2) hB)
  have hcfg : 0 < configMeasure μG
      (restrictConfig (G := G) sliceLinks ⁻¹' A
        ∩ nextConfig hN2 ⁻¹' B) :=
    config_joint_pos μG ρ hN2 hρcont hd β hA hB hApos hBpos
  have hge := gibbsMeasure_ge μG ρ hd hρcont β hE
  have hZ : 0 < gibbsPartition (torusShift N) μG ρ β :=
    gibbsPartition_pos (torusShift N) μG ρ hρcont hd β
  have hprod : 0 < (ENNReal.ofReal
        (gibbsPartition (torusShift N) μG ρ β))⁻¹
      * (ENNReal.ofReal (Real.exp (- actionBound (N := N) β))
        * configMeasure μG (restrictConfig (G := G) sliceLinks ⁻¹' A
          ∩ nextConfig hN2 ⁻¹' B)) :=
    ENNReal.mul_pos (by
      rw [ne_eq, ENNReal.inv_eq_zero]
      exact ENNReal.ofReal_ne_top)
      (ENNReal.mul_pos (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
        hcfg.ne').ne'
  exact hprod.trans_le hge

end JointPositivity

section Weld

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ))
  {N : ℕ} [NeZero N]

/-- The pointwise modulus of an OS vector, as an OS vector:
the `L²` class of `z ↦ ‖v z‖` (real-valued, cast to `ℂ`). -/
noncomputable def absVec (β : ℝ) (v : osSpace (N := N) μG ρ β) :
    osSpace (N := N) μG ρ β :=
  ((MeasureTheory.Lp.memLp v).norm.ofReal).toLp (fun z => (‖v z‖ : ℂ))

theorem coeFn_absVec (β : ℝ) (v : osSpace (N := N) μG ρ β) :
    ⇑(absVec μG ρ β v) =ᵐ[sliceMeasure (N := N) μG ρ β]
      fun z => (‖v z‖ : ℂ) :=
  MeasureTheory.MemLp.coeFn_toLp _

/-- The squared `L²` norm is the integral of the squared
pointwise norm. -/
theorem norm_sq_osSpace (β : ℝ) (x : osSpace (N := N) μG ρ β) :
    ‖x‖ ^ 2 = ∫ z, ‖x z‖ ^ 2 ∂(sliceMeasure (N := N) μG ρ β) := by
  have hInt : Integrable (fun z => inner ℂ (x z) (x z))
      (sliceMeasure (N := N) μG ρ β) := by
    have h : MeasureTheory.MemLp (fun z => (starRingEnd ℂ) (x z) * x z)
        1 (sliceMeasure (N := N) μG ρ β) :=
      (MeasureTheory.Lp.memLp x).star.mul (MeasureTheory.Lp.memLp x)
    refine MeasureTheory.memLp_one_iff_integrable.mp
      (MeasureTheory.memLp_congr_ae (p := 1) ?_ |>.mp h)
    filter_upwards with z
    show (starRingEnd ℂ) (x z) * x z = inner ℂ (x z) (x z)
    rw [RCLike.inner_apply, mul_comm]
  have h1 : ‖x‖ ^ 2 = RCLike.re (inner ℂ x x) :=
    (inner_self_eq_norm_sq x).symm
  rw [h1, inner_osSpace μG ρ β, ← integral_re hInt]
  apply integral_congr_ae
  filter_upwards with z
  rw [RCLike.inner_apply]
  simp only [Complex.mul_conj, RCLike.ofReal_re]
  exact Complex.normSq_eq_norm_sq _

theorem norm_absVec (β : ℝ) (v : osSpace (N := N) μG ρ β) :
    ‖absVec μG ρ β v‖ = ‖v‖ := by
  have hpt : ∀ z : ↥(sliceLinks (N := N)) → G,
      ‖((‖v z‖ : ℝ) : ℂ)‖ ^ 2 = ‖v z‖ ^ 2 := by
    intro z
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal,
      ← Complex.normSq_eq_norm_sq, ← pow_two]
    exact (Complex.normSq_eq_norm_sq _).symm
  have hsq : ‖absVec μG ρ β v‖ ^ 2 = ‖v‖ ^ 2 := by
    rw [norm_sq_osSpace μG ρ β, norm_sq_osSpace μG ρ β]
    apply integral_congr_ae
    filter_upwards [coeFn_absVec μG ρ β v] with z hz
    rw [hz]
    exact hpt z
  have hsq' : ‖absVec μG ρ β v‖ * ‖absVec μG ρ β v‖
      = ‖v‖ * ‖v‖ := by
    rw [← pow_two, ← pow_two]
    exact hsq
  rcases mul_self_eq_mul_self_iff.mp hsq' with h | h
  · exact h
  · have hsum : ‖absVec μG ρ β v‖ + ‖v‖ = 0 := by
      linarith [norm_nonneg (absVec μG ρ β v), norm_nonneg v]
    have h3 := (add_eq_zero_iff_of_nonneg (norm_nonneg
      (absVec μG ρ β v)) (norm_nonneg v)).mp hsum
    rw [h3.1, h3.2]

/-- The transfer form's integrand is integrable against the
Gibbs measure: it is the product of the two `L²` pullbacks. -/
theorem integrable_transfer_integrand (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g) (β : ℝ)
    (g f : osSpace (N := N) μG ρ β) :
    Integrable (fun U => (starRingEnd ℂ)
        (g (restrictConfig (G := G) sliceLinks U))
        * f (nextConfig hN2 U))
      (gibbsMeasure (torusShift N) μG ρ β) := by
  have h1 : MeasureTheory.MemLp (fun U => (starRingEnd ℂ)
        (g (restrictConfig (G := G) sliceLinks U)))
      2 (gibbsMeasure (torusShift N) μG ρ β) := by
    refine (MeasureTheory.memLp_congr_ae (p := 2) ?_).mp
      (MeasureTheory.Lp.memLp (slicePull μG ρ β g)).star
    filter_upwards [coeFn_slicePull μG ρ β g] with U hU
    show (star ⇑(slicePull μG ρ β g)) U
      = (starRingEnd ℂ) (g (restrictConfig (G := G) sliceLinks U))
    rw [Function.comp_apply] at hU
    rw [Pi.star_apply, hU]
    exact Eq.refl _
  have h2 : MeasureTheory.MemLp (fun U => f (nextConfig hN2 U))
      2 (gibbsMeasure (torusShift N) μG ρ β) := by
    exact (MeasureTheory.memLp_congr_ae (p := 2)
      (coeFn_nextPull μG ρ hN2 hρcont β f)).mp
        (MeasureTheory.Lp.memLp (nextPull μG ρ hN2 hρcont β f))
  exact MeasureTheory.memLp_one_iff_integrable.mp (h1.mul h2)

/-- **(FI) Form improvement.** For a.e.-real-nonnegative
nonzero `g, f`, the transfer form is strictly positive. The
Gibbs density is strictly positive (chunk §1), the two
readings are independent under the configuration law
(`gibbs_joint_pos`), and the form is the Gibbs integral of
the product of the readings (`transferOp_inner`). -/
theorem form_improving (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hd : 0 < d)
    (β : ℝ)
    (g f : osSpace (N := N) μG ρ β)
    (hg : ∀ᵐ z ∂(sliceMeasure (N := N) μG ρ β),
      (g z).im = 0 ∧ 0 ≤ (g z).re)
    (hf : ∀ᵐ z ∂(sliceMeasure (N := N) μG ρ β),
      (f z).im = 0 ∧ 0 ≤ (f z).re)
    (hg0 : g ≠ 0) (hf0 : f ≠ 0) :
    0 < (inner ℂ g (transferOp μG ρ hN2 hρcont β f)).re := by
  obtain ⟨ĝ, hĝsm, hĝeq⟩ := MeasureTheory.Lp.aestronglyMeasurable g
  obtain ⟨fh, fhsm, fheq⟩ := MeasureTheory.Lp.aestronglyMeasurable f
  have hĝmeas : Measurable ĝ := hĝsm.measurable
  have fhmeas : Measurable fh := fhsm.measurable
  have hAmeas : MeasurableSet {z : ↥(sliceLinks (N := N)) → G |
      (ĝ z).im = 0 ∧ 0 < (ĝ z).re} := by
    have him : Measurable fun z : ↥(sliceLinks (N := N)) → G =>
        (ĝ z).im :=
      Complex.continuous_im.measurable.comp hĝmeas
    have hre : Measurable fun z : ↥(sliceLinks (N := N)) → G =>
        (ĝ z).re :=
      Complex.continuous_re.measurable.comp hĝmeas
    exact (measurableSet_eq_fun him measurable_const).inter
      (measurableSet_lt measurable_const hre)
  have hBmeas : MeasurableSet {z : ↥(sliceLinks (N := N)) → G |
      (fh z).im = 0 ∧ 0 < (fh z).re} := by
    have him : Measurable fun z : ↥(sliceLinks (N := N)) → G =>
        (fh z).im :=
      Complex.continuous_im.measurable.comp fhmeas
    have hre : Measurable fun z : ↥(sliceLinks (N := N)) → G =>
        (fh z).re :=
      Complex.continuous_re.measurable.comp fhmeas
    exact (measurableSet_eq_fun him measurable_const).inter
      (measurableSet_lt measurable_const hre)
  have hApos : 0 < sliceMeasure (N := N) μG ρ β
      {z : ↥(sliceLinks (N := N)) → G |
        (ĝ z).im = 0 ∧ 0 < (ĝ z).re} := by
    by_contra hcon
    have hA0 : sliceMeasure (N := N) μG ρ β
        {z : ↥(sliceLinks (N := N)) → G |
          (ĝ z).im = 0 ∧ 0 < (ĝ z).re} = 0 :=
      le_antisymm (not_lt.mp hcon) zero_le
    have hnotmem : ∀ᵐ z ∂(sliceMeasure (N := N) μG ρ β),
        z ∉ {z : ↥(sliceLinks (N := N)) → G |
          (ĝ z).im = 0 ∧ 0 < (ĝ z).re} := by
      rw [MeasureTheory.ae_iff]
      have hset : {z : ↥(sliceLinks (N := N)) → G |
          ¬ z ∉ {z : ↥(sliceLinks (N := N)) → G |
            (ĝ z).im = 0 ∧ 0 < (ĝ z).re}}
        = {z : ↥(sliceLinks (N := N)) → G |
            (ĝ z).im = 0 ∧ 0 < (ĝ z).re} := by
        ext z
        simp only [Set.mem_setOf_eq, not_not]
      rw [hset]
      exact hA0
    have hae0 : ∀ᵐ z ∂(sliceMeasure (N := N) μG ρ β), g z = 0 := by
      filter_upwards [hnotmem, hg, hĝeq] with z hzA hz hg2
      have hgg : (ĝ z).im = 0 ∧ (ĝ z).re = (g z).re :=
        ⟨by rw [← hg2]; exact hz.1, by rw [hg2]⟩
      have hre : (g z).re = 0 := by
        by_contra hne
        apply hzA
        exact ⟨hgg.1, by
          rw [hgg.2]
          exact lt_of_le_of_ne hz.2 (Ne.symm hne)⟩
      exact Complex.ext hre hz.1
    exact hg0 (MeasureTheory.Lp.eq_zero_iff_ae_eq_zero.mpr hae0)
  have hBpos : 0 < sliceMeasure (N := N) μG ρ β
      {z : ↥(sliceLinks (N := N)) → G |
        (fh z).im = 0 ∧ 0 < (fh z).re} := by
    by_contra hcon
    have hB0 : sliceMeasure (N := N) μG ρ β
        {z : ↥(sliceLinks (N := N)) → G |
          (fh z).im = 0 ∧ 0 < (fh z).re} = 0 :=
      le_antisymm (not_lt.mp hcon) zero_le
    have hnotmem : ∀ᵐ z ∂(sliceMeasure (N := N) μG ρ β),
        z ∉ {z : ↥(sliceLinks (N := N)) → G |
          (fh z).im = 0 ∧ 0 < (fh z).re} := by
      rw [MeasureTheory.ae_iff]
      have hset : {z : ↥(sliceLinks (N := N)) → G |
          ¬ z ∉ {z : ↥(sliceLinks (N := N)) → G |
            (fh z).im = 0 ∧ 0 < (fh z).re}}
        = {z : ↥(sliceLinks (N := N)) → G |
            (fh z).im = 0 ∧ 0 < (fh z).re} := by
        ext z
        simp only [Set.mem_setOf_eq, not_not]
      rw [hset]
      exact hB0
    have hae0 : ∀ᵐ z ∂(sliceMeasure (N := N) μG ρ β), f z = 0 := by
      filter_upwards [hnotmem, hf, fheq] with z hzB hz hf2
      have hff : (fh z).im = 0 ∧ (fh z).re = (f z).re :=
        ⟨by rw [← hf2]; exact hz.1, by rw [hf2]⟩
      have hre : (f z).re = 0 := by
        by_contra hne
        apply hzB
        exact ⟨hff.1, by
          rw [hff.2]
          exact lt_of_le_of_ne hz.2 (Ne.symm hne)⟩
      exact Complex.ext hre hz.1
    exact hf0 (MeasureTheory.Lp.eq_zero_iff_ae_eq_zero.mpr hae0)
  -- Transfers of the sign hypotheses and the representative
  -- equalities to configuration space.  The slice measure is
  -- *definitionally* the Gibbs marginal (`map_eq` there is
  -- `rfl`), so `ae_of_ae_map` accepts the slice-side statements
  -- directly (the `LatticeTransferID` pattern).
  have hgU : ∀ᵐ U ∂(gibbsMeasure (torusShift N) μG ρ β),
      (g (restrictConfig (G := G) sliceLinks U)).im = 0
        ∧ 0 ≤ (g (restrictConfig (G := G) sliceLinks U)).re :=
    ae_of_ae_map (measurable_restrictConfig sliceLinks).aemeasurable
      (p := fun z => (g z).im = 0 ∧ 0 ≤ (g z).re) hg
  have hfU : ∀ᵐ U ∂(gibbsMeasure (torusShift N) μG ρ β),
      (f (nextConfig hN2 U)).im = 0
        ∧ 0 ≤ (f (nextConfig hN2 U)).re := by
    have hmap : (gibbsMeasure (torusShift N) μG ρ β).map
        (nextConfig hN2) = sliceMeasure (N := N) μG ρ β :=
      (measurePreserving_nextConfig (N := N) μG ρ hN2 hρcont
        β).map_eq
    have hcoe : ∀ᵐ z ∂((gibbsMeasure (torusShift N) μG ρ β).map
        (nextConfig hN2)), (f z).im = 0 ∧ 0 ≤ (f z).re := by
      rw [hmap]
      exact hf
    exact ae_of_ae_map (measurable_nextConfig hN2).aemeasurable
      hcoe
  have hge : ∀ᵐ U ∂(gibbsMeasure (torusShift N) μG ρ β),
      g (restrictConfig (G := G) sliceLinks U)
        = ĝ (restrictConfig (G := G) sliceLinks U) :=
    ae_of_ae_map (measurable_restrictConfig sliceLinks).aemeasurable
      (p := fun z => g z = ĝ z) hĝeq
  have hfe : ∀ᵐ U ∂(gibbsMeasure (torusShift N) μG ρ β),
      f (nextConfig hN2 U) = fh (nextConfig hN2 U) := by
    have hmap : (gibbsMeasure (torusShift N) μG ρ β).map
        (nextConfig hN2) = sliceMeasure (N := N) μG ρ β :=
      (measurePreserving_nextConfig (N := N) μG ρ hN2 hρcont
        β).map_eq
    have hcoe : f =ᵐ[(gibbsMeasure (torusShift N) μG ρ β).map
        (nextConfig hN2)] fh := by
      rw [hmap]
      exact fheq
    exact ae_of_ae_map (measurable_nextConfig hN2).aemeasurable
      (p := fun z => f z = fh z) hcoe

  have hInt : Integrable (fun U => (starRingEnd ℂ)
        (g (restrictConfig (G := G) sliceLinks U))
        * f (nextConfig hN2 U))
      (gibbsMeasure (torusShift N) μG ρ β) :=
    integrable_transfer_integrand μG ρ hN2 hρcont β g f
  have hform : (inner ℂ g (transferOp μG ρ hN2 hρcont β f)).re
      = ∫ U, ((starRingEnd ℂ) (g (restrictConfig (G := G) sliceLinks U))
          * f (nextConfig hN2 U)).re
        ∂(gibbsMeasure (torusShift N) μG ρ β) := by
    rw [transferOp_inner μG ρ hN2 hρcont β g f]
    exact (integral_re hInt).symm
  have hRnn : (0 : Config (Fin 4 → ZMod N) G → ℝ)
      ≤ᵐ[gibbsMeasure (torusShift N) μG ρ β]
      fun U => ((starRingEnd ℂ) (g (restrictConfig (G := G) sliceLinks U))
        * f (nextConfig hN2 U)).re := by
    filter_upwards [hgU, hfU] with U hUg hUf
    have hcalc : ((starRingEnd ℂ) (g (restrictConfig (G := G) sliceLinks U))
        * f (nextConfig hN2 U)).re
        = (g (restrictConfig (G := G) sliceLinks U)).re
          * (f (nextConfig hN2 U)).re := by
      rw [Complex.mul_re, Complex.conj_re, Complex.conj_im, hUg.1, hUf.1]
      ring
    rw [hcalc]
    exact mul_nonneg hUg.2 hUf.2
  have hsupp : ∀ᵐ U ∂(gibbsMeasure (torusShift N) μG ρ β),
      U ∈ restrictConfig (G := G) sliceLinks ⁻¹'
          {z : ↥(sliceLinks (N := N)) → G |
            (ĝ z).im = 0 ∧ 0 < (ĝ z).re}
        ∩ nextConfig hN2 ⁻¹'
          {z : ↥(sliceLinks (N := N)) → G |
            (fh z).im = 0 ∧ 0 < (fh z).re}
      → U ∈ Function.support fun U =>
          ((starRingEnd ℂ) (g (restrictConfig (G := G) sliceLinks U))
            * f (nextConfig hN2 U)).re := by
    filter_upwards [hge, hfe, hgU, hfU] with U hUg1 hUf1 hUg2 hUf2 hUmem
    obtain ⟨hA, hB⟩ := hUmem
    have hcalc : ((starRingEnd ℂ) (g (restrictConfig (G := G) sliceLinks U))
        * f (nextConfig hN2 U)).re
        = (g (restrictConfig (G := G) sliceLinks U)).re
          * (f (nextConfig hN2 U)).re := by
      rw [Complex.mul_re, Complex.conj_re, Complex.conj_im, hUg2.1, hUf2.1]
      ring
    show ((starRingEnd ℂ) (g (restrictConfig (G := G) sliceLinks U))
      * f (nextConfig hN2 U)).re ≠ 0
    rw [hcalc]
    apply ne_of_gt
    apply mul_pos
    · rw [hUg1]
      exact hA.2
    · rw [hUf1]
      exact hB.2
  have hEpos : 0 < gibbsMeasure (torusShift N) μG ρ β
      (restrictConfig (G := G) sliceLinks ⁻¹'
          {z : ↥(sliceLinks (N := N)) → G |
            (ĝ z).im = 0 ∧ 0 < (ĝ z).re}
        ∩ nextConfig hN2 ⁻¹'
          {z : ↥(sliceLinks (N := N)) → G |
            (fh z).im = 0 ∧ 0 < (fh z).re}) :=
    gibbs_joint_pos μG ρ hN2 hρcont hd β hAmeas hBmeas hApos hBpos
  have hInt' : Integrable (fun U => ((starRingEnd ℂ)
        (g (restrictConfig (G := G) sliceLinks U))
        * f (nextConfig hN2 U)).re)
      (gibbsMeasure (torusShift N) μG ρ β) := hInt.re
  rw [hform, integral_pos_iff_support_of_nonneg_ae hRnn hInt']
  exact lt_of_lt_of_le hEpos (MeasureTheory.measure_mono_ae hsupp)

/-- The transfer form of the modulus, as a real integral of
pointwise norms. -/
theorem transferOp_absVec_form (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g) (β : ℝ)
    (v : osSpace (N := N) μG ρ β) :
    (inner ℂ (absVec μG ρ β v)
        (transferOp μG ρ hN2 hρcont β (absVec μG ρ β v))).re
      = ∫ U, ‖v (restrictConfig (G := G) sliceLinks U)‖
          * ‖v (nextConfig hN2 U)‖
        ∂(gibbsMeasure (torusShift N) μG ρ β) := by
  have ht1 : ∀ᵐ U ∂(gibbsMeasure (torusShift N) μG ρ β),
      absVec μG ρ β v (restrictConfig (G := G) sliceLinks U)
        = ((‖v (restrictConfig (G := G) sliceLinks U)‖ : ℝ) : ℂ) :=
    ae_of_ae_map (measurable_restrictConfig sliceLinks).aemeasurable
      (p := fun z => absVec μG ρ β v z = ((‖v z‖ : ℝ) : ℂ))
      (coeFn_absVec μG ρ β v)
  have ht2 : ∀ᵐ U ∂(gibbsMeasure (torusShift N) μG ρ β),
      absVec μG ρ β v (nextConfig hN2 U)
        = ((‖v (nextConfig hN2 U)‖ : ℝ) : ℂ) := by
    have hmap : (gibbsMeasure (torusShift N) μG ρ β).map
        (nextConfig hN2) = sliceMeasure (N := N) μG ρ β :=
      (measurePreserving_nextConfig (N := N) μG ρ hN2 hρcont
        β).map_eq
    have hcoe : absVec μG ρ β v
        =ᵐ[(gibbsMeasure (torusShift N) μG ρ β).map (nextConfig hN2)]
        (fun z => ((‖v z‖ : ℝ) : ℂ)) := by
      rw [hmap]
      exact coeFn_absVec μG ρ β v
    exact ae_of_ae_map (measurable_nextConfig hN2).aemeasurable
      (p := fun z => absVec μG ρ β v z = ((‖v z‖ : ℝ) : ℂ)) hcoe
  have hcongr : (fun U => (starRingEnd ℂ)
        (absVec μG ρ β v (restrictConfig (G := G) sliceLinks U))
        * absVec μG ρ β v (nextConfig hN2 U))
      =ᵐ[gibbsMeasure (torusShift N) μG ρ β]
      (fun U => ((‖v (restrictConfig (G := G) sliceLinks U)‖
        * ‖v (nextConfig hN2 U)‖ : ℝ) : ℂ)) := by
    filter_upwards [ht1, ht2] with U h1 h2
    rw [h1, h2]
    simp [Complex.conj_ofReal, Complex.ofReal_mul]
  rw [transferOp_inner μG ρ hN2 hρcont β]
  rw [MeasureTheory.integral_congr_ae hcongr]
  have hcast : (∫ a, ((‖v (restrictConfig (G := G) sliceLinks a)‖
          * ‖v (nextConfig hN2 a)‖ : ℝ) : ℂ)
        ∂(gibbsMeasure (torusShift N) μG ρ β))
      = ((∫ a, ‖v (restrictConfig (G := G) sliceLinks a)‖
          * ‖v (nextConfig hN2 a)‖
        ∂(gibbsMeasure (torusShift N) μG ρ β) : ℝ) : ℂ) :=
    integral_ofReal
  rw [hcast, Complex.ofReal_re]

/-- **Modulus step.** A fixed vector's modulus is fixed:
if `transferOp v = v` then `transferOp |v| = |v|`. The form
of `|v|` dominates `‖v‖²` (the pointwise triangle inequality
inside `transferOp_inner`), and the contraction squeezes
`‖transferOp |v| − |v|‖² ≤ 0`. -/
theorem transferOp_absVec (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hd : 0 < d)
    (β : ℝ) (v : osSpace (N := N) μG ρ β)
    (hfix : transferOp μG ρ hN2 hρcont β v = v) :
    transferOp μG ρ hN2 hρcont β (absVec μG ρ β v)
      = absVec μG ρ β v := by
  set w := absVec μG ρ β v with hw
  have hnormw : ‖w‖ = ‖v‖ := norm_absVec μG ρ β v
  have hstep1 : ‖w‖ ^ 2
      ≤ (inner ℂ w (transferOp μG ρ hN2 hρcont β w)).re := by
    have e2 : ‖v‖ ^ 2 = (inner ℂ v v).re :=
      (inner_self_eq_norm_sq (𝕜 := ℂ) v).symm
    have e3 : (inner ℂ v v).re
        = (inner ℂ v (transferOp μG ρ hN2 hρcont β v)).re := by
      rw [hfix]
    have e4 : (inner ℂ v (transferOp μG ρ hN2 hρcont β v)).re
        ≤ ‖inner ℂ v (transferOp μG ρ hN2 hρcont β v)‖ :=
      le_trans (le_abs_self _) (Complex.abs_re_le_norm _)
    have e5 : ‖inner ℂ v (transferOp μG ρ hN2 hρcont β v)‖
        ≤ ∫ U, ‖v (restrictConfig (G := G) sliceLinks U)‖
            * ‖v (nextConfig hN2 U)‖
          ∂(gibbsMeasure (torusShift N) μG ρ β) := by
      rw [transferOp_inner μG ρ hN2 hρcont β v v]
      refine le_trans (norm_integral_le_integral_norm _) ?_
      apply le_of_eq
      apply MeasureTheory.integral_congr_ae
      apply MeasureTheory.ae_of_all
      intro U
      show ‖(starRingEnd ℂ) (v (restrictConfig (G := G) sliceLinks U))
          * v (nextConfig hN2 U)‖
        = ‖v (restrictConfig (G := G) sliceLinks U)‖
          * ‖v (nextConfig hN2 U)‖
      rw [norm_mul, RCLike.norm_conj]
    have hTw : (inner ℂ w (transferOp μG ρ hN2 hρcont β w)).re
        = ∫ U, ‖v (restrictConfig (G := G) sliceLinks U)‖
            * ‖v (nextConfig hN2 U)‖
          ∂(gibbsMeasure (torusShift N) μG ρ β) :=
      transferOp_absVec_form μG ρ hN2 hρcont β v
    rw [hnormw, e2, e3]
    exact le_trans (le_trans e4 e5) (le_of_eq hTw.symm)
  have hnormT : ‖transferOp μG ρ hN2 hρcont β w‖ ≤ ‖w‖ :=
    calc ‖transferOp μG ρ hN2 hρcont β w‖
        ≤ ‖transferOp μG ρ hN2 hρcont β‖ * ‖w‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * ‖w‖ :=
          mul_le_mul_of_nonneg_right
            (transferOp_norm_le μG ρ hN2 hρcont β) (norm_nonneg _)
      _ = ‖w‖ := one_mul _
  have hnormT2 : ‖transferOp μG ρ hN2 hρcont β w‖ ^ 2 ≤ ‖w‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hnormT 2
  have hsq : ‖transferOp μG ρ hN2 hρcont β w - w‖ ^ 2 ≤ 0 := by
    have h1 : ‖transferOp μG ρ hN2 hρcont β w - w‖ ^ 2
        = ‖transferOp μG ρ hN2 hρcont β w‖ ^ 2
          - 2 * (inner ℂ w (transferOp μG ρ hN2 hρcont β w)).re
          + ‖w‖ ^ 2 := by
      have h := norm_sub_sq (𝕜 := ℂ) (transferOp μG ρ hN2 hρcont β w) w
      rwa [inner_re_symm] at h
    rw [h1]
    linarith [hnormT2, hstep1]
  have hnorm0 : ‖transferOp μG ρ hN2 hρcont β w - w‖ = 0 := by
    have h2 : ‖transferOp μG ρ hN2 hρcont β w - w‖ ^ 2 = 0 :=
      le_antisymm hsq (sq_nonneg _)
    exact (pow_eq_zero_iff (two_ne_zero)).mp h2
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm0)

/-- Sign facts for the positive half `(1/2)(|r| + r)` of a
real vector: its values are a.e. real and nonnegative. -/
theorem half_absVec_add_sign (β : ℝ) (r : osSpace (N := N) μG ρ β)
    (hr : ∀ᵐ z ∂(sliceMeasure (N := N) μG ρ β), (r z).im = 0) :
    ∀ᵐ z ∂(sliceMeasure (N := N) μG ρ β),
      (((1/2 : ℂ) • (absVec μG ρ β r + r)) z).im = 0
        ∧ 0 ≤ (((1/2 : ℂ) • (absVec μG ρ β r + r)) z).re := by
  filter_upwards [coeFn_absVec μG ρ β r,
    MeasureTheory.Lp.coeFn_add (absVec μG ρ β r) r,
    MeasureTheory.Lp.coeFn_smul (1/2 : ℂ) (absVec μG ρ β r + r), hr]
    with z hw hadd hsm him
  have hval : ((1/2 : ℂ) • (absVec μG ρ β r + r)) z
      = (((‖r z‖ + (r z).re)/2 : ℝ) : ℂ) := by
    rw [hsm]
    simp only [Pi.smul_apply]
    rw [hadd]
    simp only [Pi.add_apply]
    rw [hw, smul_eq_mul]
    refine Complex.ext ?_ ?_ <;>
      simp [Complex.mul_re, Complex.mul_im, Complex.add_re,
        Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
        him] <;> ring
  rw [hval]
  refine ⟨by simp, ?_⟩
  rw [Complex.ofReal_re]
  apply div_nonneg _ (by norm_num)
  have h := Complex.abs_re_le_norm (r z)
  have h2 := (abs_le.mp h).1
  linarith

/-- Sign facts for the negative half `(1/2)(|r| − r)` of a
real vector. -/
theorem half_absVec_sub_sign (β : ℝ) (r : osSpace (N := N) μG ρ β)
    (hr : ∀ᵐ z ∂(sliceMeasure (N := N) μG ρ β), (r z).im = 0) :
    ∀ᵐ z ∂(sliceMeasure (N := N) μG ρ β),
      (((1/2 : ℂ) • (absVec μG ρ β r - r)) z).im = 0
        ∧ 0 ≤ (((1/2 : ℂ) • (absVec μG ρ β r - r)) z).re := by
  filter_upwards [coeFn_absVec μG ρ β r,
    MeasureTheory.Lp.coeFn_sub (absVec μG ρ β r) r,
    MeasureTheory.Lp.coeFn_smul (1/2 : ℂ) (absVec μG ρ β r - r), hr]
    with z hw hsub hsm him
  have hval : ((1/2 : ℂ) • (absVec μG ρ β r - r)) z
      = (((‖r z‖ - (r z).re)/2 : ℝ) : ℂ) := by
    rw [hsm]
    simp only [Pi.smul_apply]
    rw [hsub]
    simp only [Pi.sub_apply]
    rw [hw, smul_eq_mul]
    refine Complex.ext ?_ ?_ <;>
      simp [Complex.mul_re, Complex.mul_im, Complex.sub_re,
        Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
        him] <;> ring
  rw [hval]
  refine ⟨by simp, ?_⟩
  rw [Complex.ofReal_re]
  apply div_nonneg _ (by norm_num)
  have h := Complex.abs_re_le_norm (r z)
  have h2 := (abs_le.mp h).2
  linarith

/-- The two halves of a real vector are orthogonal:
`⟪(1/2)(|r| − r), (1/2)(|r| + r)⟫ = 0`. Pure algebra from
`⟪|r|, r⟫ = ⟪r, |r|⟫` (the pairing is real) and
`‖|r|‖ = ‖r‖`. -/
theorem inner_half_sub_add (β : ℝ) (r : osSpace (N := N) μG ρ β)
    (hr : ∀ᵐ z ∂(sliceMeasure (N := N) μG ρ β), (r z).im = 0) :
    inner ℂ ((1/2 : ℂ) • (absVec μG ρ β r - r))
      ((1/2 : ℂ) • (absVec μG ρ β r + r)) = 0 := by
  have hpt : (fun z => (inner ℂ (absVec μG ρ β r z) (r z)).im)
      =ᵐ[sliceMeasure (N := N) μG ρ β] 0 := by
    filter_upwards [coeFn_absVec μG ρ β r, hr] with z hw him
    rw [hw]
    simp [RCLike.inner_apply, him]
  have him_wr : (inner ℂ (absVec μG ρ β r) r).im = 0 := by
    have h1 : (inner ℂ (absVec μG ρ β r) r).im
        = ∫ z, (inner ℂ (absVec μG ρ β r z) (r z)).im
          ∂(sliceMeasure (N := N) μG ρ β) := by
      rw [inner_osSpace μG ρ β]
      exact (integral_im (MeasureTheory.L2.integrable_inner (𝕜 := ℂ)
        (absVec μG ρ β r) r)).symm
    rw [h1]
    exact integral_eq_zero_of_ae hpt
  have hconj : inner ℂ r (absVec μG ρ β r)
      = inner ℂ (absVec μG ρ β r) r := by
    have h2 := inner_conj_symm (𝕜 := ℂ) r (absVec μG ρ β r)
    rw [← h2]
    exact RCLike.conj_eq_iff_im.mpr him_wr
  have hexp : inner ℂ (absVec μG ρ β r - r)
      (absVec μG ρ β r + r) = 0 := by
    simp only [inner_sub_left, inner_add_right, inner_add_left,
      inner_sub_right, inner_self_eq_norm_sq_to_K]
    rw [hconj, norm_absVec μG ρ β r]
    ring
  rw [inner_smul_left, inner_smul_right, hexp]
  simp

/-- **Real endgame.** A real fixed vector is a scalar
multiple of the vacuum: the dichotomy (form improvement
against the orthogonal halves) forces it one-signed, and a
real fixed vector orthogonal to the vacuum is then zero by
form improvement against the vacuum itself. -/
theorem real_fixed_mem_span (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hd : 0 < d)
    (β : ℝ) (r : osSpace (N := N) μG ρ β)
    (hr : ∀ᵐ z ∂(sliceMeasure (N := N) μG ρ β), (r z).im = 0)
    (hfix : transferOp μG ρ hN2 hρcont β r = r) :
    r ∈ Submodule.span ℂ {osVacuum (N := N) μG ρ hρcont hd β} := by
  haveI := isProbabilityMeasure_sliceMeasure (N := N) μG ρ
    hρcont hd β
  have hvac : ⇑(osVacuum (N := N) μG ρ hρcont hd β)
      =ᵐ[sliceMeasure (N := N) μG ρ β] fun _ => (1 : ℂ) := by
    show ⇑(MeasureTheory.Lp.const 2 (sliceMeasure (N := N) μG ρ β)
        (1 : ℂ))
      =ᵐ[sliceMeasure (N := N) μG ρ β] fun _ => (1 : ℂ)
    exact MeasureTheory.Lp.coeFn_const 2 _ (1 : ℂ)
  have hΩsign : ∀ᵐ z ∂(sliceMeasure (N := N) μG ρ β),
      ((osVacuum (N := N) μG ρ hρcont hd β) z).im = 0
        ∧ 0 ≤ ((osVacuum (N := N) μG ρ hρcont hd β) z).re := by
    filter_upwards [hvac] with z hz
    rw [hz]
    simp
  have hΩ0 : osVacuum (N := N) μG ρ hρcont hd β ≠ 0 := by
    have h1 : ‖osVacuum (N := N) μG ρ hρcont hd β‖ = 1 :=
      norm_osVacuum μG ρ hρcont hd β
    intro h
    rw [h, norm_zero] at h1
    exact zero_ne_one h1
  have key0 : ∀ x : osSpace (N := N) μG ρ β,
      (∀ᵐ z ∂(sliceMeasure (N := N) μG ρ β), (x z).im = 0) →
      transferOp μG ρ hN2 hρcont β x = x →
      inner ℂ (osVacuum (N := N) μG ρ hρcont hd β) x = 0 →
      x = 0 := by
    intro x hxreal hxfix hxorth
    by_contra hx0
    have hwfix : transferOp μG ρ hN2 hρcont β (absVec μG ρ β x)
        = absVec μG ρ β x :=
      transferOp_absVec μG ρ hN2 hρcont hd β x hxfix
    have hw0 : absVec μG ρ β x ≠ 0 := by
      intro h
      apply hx0
      have h2 : ‖absVec μG ρ β x‖ = 0 := by
        rw [h]
        exact norm_zero
      rw [norm_absVec μG ρ β x] at h2
      exact norm_eq_zero.mp h2
    have hwsign : ∀ᵐ z ∂(sliceMeasure (N := N) μG ρ β),
        ((absVec μG ρ β x) z).im = 0
          ∧ 0 ≤ ((absVec μG ρ β x) z).re := by
      filter_upwards [coeFn_absVec μG ρ β x] with z hz
      rw [hz]
      refine ⟨by simp, by simp [Complex.ofReal_re, norm_nonneg]⟩
    have hfixminus : transferOp μG ρ hN2 hρcont β
        ((1/2 : ℂ) • (absVec μG ρ β x - x))
        = (1/2 : ℂ) • (absVec μG ρ β x - x) := by
      rw [map_smul, map_sub, hwfix, hxfix]
    have hfixplus : transferOp μG ρ hN2 hρcont β
        ((1/2 : ℂ) • (absVec μG ρ β x + x))
        = (1/2 : ℂ) • (absVec μG ρ β x + x) := by
      rw [map_smul, map_add, hwfix, hxfix]
    have hdich : (1/2 : ℂ) • (absVec μG ρ β x - x) = 0
        ∨ (1/2 : ℂ) • (absVec μG ρ β x + x) = 0 := by
      by_contra hcon
      push_neg at hcon
      have hpos := form_improving μG ρ hN2 hρcont hd β _ _
        (half_absVec_sub_sign μG ρ β x hxreal)
        (half_absVec_add_sign μG ρ β x hxreal) hcon.1 hcon.2
      rw [hfixplus, inner_half_sub_add μG ρ β x hxreal] at hpos
      simp at hpos
    have hΩw : inner ℂ (osVacuum (N := N) μG ρ hρcont hd β)
        (absVec μG ρ β x) = 0 := by
      rcases hdich with h | h
      · have h2 : absVec μG ρ β x - x = 0 := by
          rcases smul_eq_zero.mp h with h3 | h3
          · norm_num at h3
          · exact h3
        have hwx : absVec μG ρ β x = x := sub_eq_zero.mp h2
        rw [hwx]
        exact hxorth
      · have h2 : absVec μG ρ β x + x = 0 := by
          rcases smul_eq_zero.mp h with h3 | h3
          · norm_num at h3
          · exact h3
        have hxw : x = -absVec μG ρ β x := by
          rw [eq_neg_iff_add_eq_zero, add_comm]
          exact h2
        have hwx2 : absVec μG ρ β x = -x := by
          rw [eq_neg_iff_add_eq_zero]
          exact h2
        rw [hwx2, inner_neg_right, hxorth, neg_zero]
    have hpos := form_improving μG ρ hN2 hρcont hd β _ _
      hΩsign hwsign hΩ0 hw0
    rw [hwfix, hΩw] at hpos
    simp at hpos
  set c := inner ℂ (osVacuum (N := N) μG ρ hρcont hd β) r with hc
  have hr'fix : transferOp μG ρ hN2 hρcont β
      (r - c • osVacuum (N := N) μG ρ hρcont hd β)
      = r - c • osVacuum (N := N) μG ρ hρcont hd β := by
    rw [map_sub, map_smul, hfix,
      transferOp_vacuum μG ρ hN2 hρcont hd β]
  have hcim : c.im = 0 := by
    rw [hc, inner_osVacuum_left μG ρ hρcont hd β r]
    have hInt : Integrable (⇑r) (sliceMeasure (N := N) μG ρ β) := by
      haveI := isProbabilityMeasure_sliceMeasure (N := N) μG ρ
        hρcont hd β
      exact MeasureTheory.MemLp.integrable (q := 2) (by norm_num)
        (MeasureTheory.Lp.memLp r)
    have e1 : (∫ z, r z ∂(sliceMeasure (N := N) μG ρ β)).im
        = ∫ z, (r z).im ∂(sliceMeasure (N := N) μG ρ β) :=
      (integral_im hInt).symm
    rw [e1]
    have hr0 : (fun z => (r z).im)
        =ᵐ[sliceMeasure (N := N) μG ρ β] 0 := hr
    exact integral_eq_zero_of_ae hr0
  have hr'real : ∀ᵐ z ∂(sliceMeasure (N := N) μG ρ β),
      ((r - c • osVacuum (N := N) μG ρ hρcont hd β) z).im = 0 := by
    filter_upwards [MeasureTheory.Lp.coeFn_sub r
      (c • osVacuum (N := N) μG ρ hρcont hd β),
      MeasureTheory.Lp.coeFn_smul c
        (osVacuum (N := N) μG ρ hρcont hd β), hvac, hr]
      with z hsub hsm hv him
    have hz : (r - c • osVacuum (N := N) μG ρ hρcont hd β) z
        = r z - c := by
      rw [hsub]
      simp only [Pi.sub_apply]
      rw [hsm]
      simp only [Pi.smul_apply]
      rw [hv]
      simp [smul_eq_mul]
    rw [hz]
    simp [Complex.sub_im, him, hcim]
  have hr'orth : inner ℂ (osVacuum (N := N) μG ρ hρcont hd β)
      (r - c • osVacuum (N := N) μG ρ hρcont hd β) = 0 := by
    rw [inner_sub_right, inner_smul_right,
      inner_self_eq_norm_sq_to_K, norm_osVacuum μG ρ hρcont hd β]
    simp [hc]
  have hr'0 : r - c • osVacuum (N := N) μG ρ hρcont hd β = 0 :=
    key0 _ hr'real hr'fix hr'orth
  have hrr : r = c • osVacuum (N := N) μG ρ hρcont hd β :=
    sub_eq_zero.mp hr'0
  rw [hrr]
  exact Submodule.smul_mem _ _
    (Submodule.subset_span (Set.mem_singleton _))

/-- The star-pairing identity on the OS space:
`⟪a, star b⟫ = conj ⟪star a, b⟫`, pointwise from the
definition of the `L²` inner product. -/
theorem inner_star (β : ℝ) (a b : osSpace (N := N) μG ρ β) :
    inner ℂ a (star b)
      = starRingEnd ℂ (inner ℂ (star a) b) := by
  rw [inner_osSpace μG ρ β a (star b),
    inner_osSpace μG ρ β (star a) b, ← integral_conj]
  apply integral_congr_ae
  filter_upwards [MeasureTheory.Lp.coeFn_star a,
    MeasureTheory.Lp.coeFn_star b] with z ha hb
  rw [ha, hb]
  simp only [Pi.star_apply]
  rw [RCLike.inner_apply, RCLike.inner_apply]
  simp only [starRingEnd_apply, map_mul, star_star]

/-- The transfer-form star identity:
`⟪g, transferOp (star v)⟫ = conj ⟪star g, transferOp v⟫`,
from `transferOp_inner` and `integral_conj`. -/
theorem transferOp_inner_star (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g) (β : ℝ)
    (g v : osSpace (N := N) μG ρ β) :
    inner ℂ g (transferOp μG ρ hN2 hρcont β (star v))
      = starRingEnd ℂ
        (inner ℂ (star g) (transferOp μG ρ hN2 hρcont β v)) := by
  have htg : ∀ᵐ U ∂(gibbsMeasure (torusShift N) μG ρ β),
      (star g) (restrictConfig (G := G) sliceLinks U)
        = star (g (restrictConfig (G := G) sliceLinks U)) :=
    ae_of_ae_map (measurable_restrictConfig sliceLinks).aemeasurable
      (p := fun z => (star g) z = star (g z))
      (by filter_upwards [MeasureTheory.Lp.coeFn_star g] with z hz
          rw [hz]
          rfl)
  have htv : ∀ᵐ U ∂(gibbsMeasure (torusShift N) μG ρ β),
      (star v) (nextConfig hN2 U)
        = star (v (nextConfig hN2 U)) := by
    have hmap : (gibbsMeasure (torusShift N) μG ρ β).map
        (nextConfig hN2) = sliceMeasure (N := N) μG ρ β :=
      (measurePreserving_nextConfig (N := N) μG ρ hN2 hρcont
        β).map_eq
    have hcoe : (star v) =ᵐ[(gibbsMeasure (torusShift N) μG ρ β).map
        (nextConfig hN2)] (fun z => star (v z)) := by
      rw [hmap]
      filter_upwards [MeasureTheory.Lp.coeFn_star v] with z hz
      rw [hz]
      rfl
    exact ae_of_ae_map (measurable_nextConfig hN2).aemeasurable
      (p := fun z => (star v) z = star (v z)) hcoe
  rw [transferOp_inner μG ρ hN2 hρcont β g (star v),
    transferOp_inner μG ρ hN2 hρcont β (star g) v, ← integral_conj]
  apply integral_congr_ae
  filter_upwards [htg, htv] with U hg hv
  rw [hg, hv]
  simp only [starRingEnd_apply, map_mul, star_star]

/-- **Star commutation.** The transfer operator commutes
with the pointwise star, at every real `β` and every
`N ≥ 2` — from the form identity alone (no self-adjointness,
no evenness). -/
theorem transferOp_star (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g) (β : ℝ)
    (v : osSpace (N := N) μG ρ β) :
    transferOp μG ρ hN2 hρcont β (star v)
      = star (transferOp μG ρ hN2 hρcont β v) := by
  apply eq_of_forall_inner_left μG ρ β
  intro g
  rw [transferOp_inner_star μG ρ hN2 hρcont β g v,
    inner_star μG ρ β g (transferOp μG ρ hN2 hρcont β v)]

/-- **Complex assembly.** Every fixed vector lies in the
vacuum line: its real and imaginary parts are real fixed
vectors, hence in the line by the real endgame, and the
vector is their combination `Re v + I • Im v`. -/
theorem fixed_mem_span (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hd : 0 < d)
    (β : ℝ) (v : osSpace (N := N) μG ρ β)
    (hfix : transferOp μG ρ hN2 hρcont β v = v) :
    v ∈ Submodule.span ℂ {osVacuum (N := N) μG ρ hρcont hd β} := by
  have hstarfix : transferOp μG ρ hN2 hρcont β (star v)
      = star v := by
    rw [transferOp_star μG ρ hN2 hρcont β v, hfix]
  have ha_val : ⇑((1/2 : ℂ) • (v + star v))
      =ᵐ[sliceMeasure (N := N) μG ρ β]
      fun z => ((v z).re : ℂ) := by
    filter_upwards [MeasureTheory.Lp.coeFn_smul (1/2 : ℂ)
      (v + star v), MeasureTheory.Lp.coeFn_add v (star v),
      MeasureTheory.Lp.coeFn_star v] with z hsm hadd hstar
    rw [hsm]
    simp only [Pi.smul_apply]
    rw [hadd]
    simp only [Pi.add_apply]
    rw [hstar]
    simp only [Pi.star_apply]
    rw [smul_eq_mul, ← starRingEnd_apply, RCLike.add_conj]
    simp
  have hb_val : ⇑((-Complex.I / 2 : ℂ) • (v - star v))
      =ᵐ[sliceMeasure (N := N) μG ρ β]
      fun z => ((v z).im : ℂ) := by
    filter_upwards [MeasureTheory.Lp.coeFn_smul
      (-Complex.I / 2 : ℂ) (v - star v),
      MeasureTheory.Lp.coeFn_sub v (star v),
      MeasureTheory.Lp.coeFn_star v] with z hsm hsub hstar
    rw [hsm]
    simp only [Pi.smul_apply]
    rw [hsub]
    simp only [Pi.sub_apply]
    rw [hstar]
    simp only [Pi.star_apply]
    rw [smul_eq_mul, ← starRingEnd_apply, RCLike.sub_conj,
      RCLike.im_to_complex, RCLike.I_to_complex]
    rw [Complex.ext_iff]
    constructor <;> simp <;> ring
  have hareal : ∀ᵐ z ∂(sliceMeasure (N := N) μG ρ β),
      (((1/2 : ℂ) • (v + star v)) z).im = 0 := by
    filter_upwards [ha_val] with z hz
    rw [hz]
    simp
  have hbreal : ∀ᵐ z ∂(sliceMeasure (N := N) μG ρ β),
      (((-Complex.I / 2 : ℂ) • (v - star v)) z).im = 0 := by
    filter_upwards [hb_val] with z hz
    rw [hz]
    simp
  have hafix : transferOp μG ρ hN2 hρcont β
      ((1/2 : ℂ) • (v + star v)) = (1/2 : ℂ) • (v + star v) := by
    rw [map_smul, map_add, hfix, hstarfix]
  have hbfix : transferOp μG ρ hN2 hρcont β
      ((-Complex.I / 2 : ℂ) • (v - star v))
      = (-Complex.I / 2 : ℂ) • (v - star v) := by
    rw [map_smul, map_sub, hfix, hstarfix]
  have ha_mem := real_fixed_mem_span μG ρ hN2 hρcont hd β _
    hareal hafix
  have hb_mem := real_fixed_mem_span μG ρ hN2 hρcont hd β _
    hbreal hbfix
  have hdecomp : v = (1/2 : ℂ) • (v + star v)
      + Complex.I • ((-Complex.I / 2 : ℂ) • (v - star v)) := by
    apply MeasureTheory.Lp.ext
    filter_upwards [ha_val, hb_val,
      MeasureTheory.Lp.coeFn_add ((1/2 : ℂ) • (v + star v))
        (Complex.I • ((-Complex.I / 2 : ℂ) • (v - star v))),
      MeasureTheory.Lp.coeFn_smul Complex.I
        ((-Complex.I / 2 : ℂ) • (v - star v))] with z hz1 hz2 hadd hsm
    rw [hadd]
    simp only [Pi.add_apply]
    rw [hz1, hsm]
    simp only [Pi.smul_apply]
    rw [hz2, smul_eq_mul]
    rw [Complex.ext_iff]
    constructor <;> simp
  rw [hdecomp]
  exact add_mem ha_mem (Submodule.smul_mem _ _ hb_mem)

end Weld

section Seat

/-- **Vacuum simplicity at the U(1) seat — clause (b) of
`TransferFormPos` discharged at `β > 0`.** The eigenvalue-`1`
eigenspace of the circle transfer operator is exactly the
vacuum line, at every even `N ≥ 2` and every `β > 0`. The
evenness is consumed only by the neighbouring clauses of the
conjunction; the weld itself is all-`β`, all-`N`. [T1] -/
theorem vacuumSimpleU1_of_weld (hβ : 0 < β) {N : ℕ} [NeZero N]
    (hN2 : 2 ≤ N) (hN : Even N) : VacuumSimpleU1 β hN2 := by
  intro f hf
  exact fixed_mem_span (haarProb Circle) circleRep hN2
    circleRep_continuous zero_lt_one β f hf

/-- **`TransferFormPos` at the U(1) seat, `β > 0`: the full
conjunction.** Clause (a) is S2-3's landed circle discharge
(`transferDiagU1_circle`); clause (b) is the weld. [T1] -/
theorem transferFormPosU1_of_weld (hβ : 0 < β) {N : ℕ} [NeZero N]
    (hN2 : 2 ≤ N) (hN : Even N) : TransferFormPosU1 β hN2 :=
  (transferFormPosU1_iff β hN2).mpr
    ⟨transferDiagU1_circle β hβ.le hN2 hN,
      vacuumSimpleU1_of_weld hβ hN2 hN⟩

/-- **`GapPackageU1` at `β > 0`, modulo exactly the two
carried data of Q12's route:** the two-slice density
hypothesis `HDen` and a Hilbert basis (separability carried
as data, FG-1's convention). Nothing else is assumed. [T1] -/
theorem gapPackageU1_of_weld (hβ : 0 < β) {N : ℕ} [NeZero N]
    (hN2 : 2 ≤ N) (hN : Even N)
    (hHDen : HDen (haarProb Circle) circleRep β hN2
      circleRep_continuous zero_lt_one)
    {ι : Type*} [Countable ι]
    (b : HilbertBasis ι ℂ (osSpace (N := N)
      (haarProb Circle) circleRep β)) :
    GapPackageU1 β hN2 :=
  ⟨transferOp_compact_of_HDen (haarProb Circle) circleRep β
      hN2 circleRep_continuous zero_lt_one hHDen b,
    transferFormPosU1_of_weld hβ hN2 hN⟩

/-- **The per-instance gap at the U(1) seat, `β > 0`:** under
the same two carried data, some `δ > 0` bounds every
non-vacuum spectral point of the transfer operator by
`1 − δ` in norm. This is the (U-vol) instance statement of
the frontier gate at fixed `(β, N)` — not a uniform bound.
[T1] -/
theorem gapBoundU1_of_weld (hβ : 0 < β) {N : ℕ} [NeZero N]
    (hN2 : 2 ≤ N) (hN : Even N)
    (hHDen : HDen (haarProb Circle) circleRep β hN2
      circleRep_continuous zero_lt_one)
    {ι : Type*} [Countable ι]
    (b : HilbertBasis ι ℂ (osSpace (N := N)
      (haarProb Circle) circleRep β)) :
    ∃ δ > 0, GapBoundU1 β hN2 δ :=
  gapBoundU1_of_package β hN2 hN
    (gapPackageU1_of_weld hβ hN2 hN hHDen b)

end Seat

end ThetLogos
