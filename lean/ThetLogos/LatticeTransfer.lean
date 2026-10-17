import ThetLogos.LatticeOSSpace

/-!
# Pitch 4, Stage 1b-D: the transfer matrix on the OS space

THE CONCRETE LEDGER (tiers per Jeff's standing law, 2026-10-16):
every claim in this file is T1 (machine-checked Lean in this
file, zero `sorry`/`admit`) unless explicitly marked otherwise
in this header. Computations conducted 2026-10-17.

## What this file is

Stage 1b-C built the Osterwalder–Schrader Hilbert space of the
finite lattice gauge theory by the time-slice `L²` route:
`osSpace β = L²` of the time-`0` slice's configuration space
under the Gibbs slice marginal `sliceMeasure β`. This module
puts the dynamics on that space: the **one-step transfer
operator**

```
T_β = A*† ∘ B* : osSpace β →L[ℂ] osSpace β,
```

where `A*` pulls a slice observable back to the full
configuration space along the time-`0` restriction, `B*`
pulls it back along the time-`1` restriction transported
back to the time-`0` slice, and `A*†` is the Hilbert-space
adjoint. The transfer matrix of the classical OS / Glimm–Jaffe
construction is exactly this compression of the Gibbs
measure's two-slice kernel; here it is an operator identity,
not an analogy: the quadratic form of `T` is the two-slice
Gibbs kernel pairing (`transferOp_inner`, §5).

## The contents, section by section

* **§1 — the next slice.** The time-`1` link stratum
  `slice1Links`, the link transport `slice01Equiv` between
  the time-`0` and time-`1` strata (needs `2 ≤ N`: a one-step
  transfer needs at least two time slices), the induced
  transports `sliceStep`/`sliceStepBack` of slice content,
  and the reading `nextConfig` of the next slice's content
  on the time-`0` slice.
* **§2 — translation invariance.** For any site permutation
  commuting with the torus shifts, the induced configuration
  map (`shiftConfig`) preserves the Wilson action, hence the
  Gibbs density, hence the Gibbs measure (`Measure.map`
  form). This is Stage 1b-A's reflection argument run for
  translations; it is what identifies the time-`1` marginal,
  transported to slice `0`, with the slice measure itself.
* **§3 — stationarity identifications.** The time-`1`
  marginal `slice1Measure`, its identification with the
  pushforward of the slice measure along `sliceStepBack`,
  and the conclusion that both readings are measure
  preserving: `B*` is a genuine isometry into the same
  `L²(ν)` as `A*` — `ν.map nextConfig = sliceMeasure β` at
  **every** real `β` (translation invariance of the Gibbs
  measure).
* **§4 — the operator.** `slicePull` (`A*`) and `nextPull`
  (`B*`) as linear isometries, and `transferOp` as the
  adjoint-compression. A general extensionality lemma for the
  OS space (inner products against all vectors determine a
  vector) is recorded once and spent repeatedly.
* **§5 — the operator package, first half (every real
  `β`).** The form identity `transferOp_inner`; the
  contraction bound `‖T_β‖ ≤ 1` (`transferOp_norm_le`,
  Cauchy–Schwarz against the two isometries); the vacuum is
  fixed, `T_β Ω = Ω` (`transferOp_vacuum`, stationarity).
* **§6 — the reflection step.** `Ψ = ` time-shift-by-`(−2)`
  after Stage 1b-A's reflection: `Ψ` preserves the Gibbs
  measure (at even `N`, like reflection invariance itself)
  and exchanges the two slices
  (`restrict_reflStepConfig_zero/one`,
  `nextConfig_reflStepConfig`).
* **§7 — the operator package, second half.** Positivity in
  form: for slice observables whose representatives are
  pointwise real and nonnegative, `⟪g, T_β f⟫` is real and
  nonnegative, at **every** real `β`
  (`transferOp_form_nonneg`); and at even `N`, `T_β` is
  **self-adjoint**, `T_β† = T_β` (`transferOp_adjoint`,
  `transferOp_isSelfAdjoint`, from 1b-A's *proved*
  reflection invariance via §6 — no clause is spent).
* **§8 — the exact gap at `β = 0`.** At zero coupling the
  Gibbs measure is the product measure, the two slices are
  independent, and the kernel pairing **factorizes exactly**
  (Stage 1a's disjoint-support factorization):
  `T₀ f = ⟪Ω, f⟫ • Ω` — the transfer operator is *exactly*
  the vacuum projection (`transferOp_zero_apply`).
  Corollaries: `T₀` annihilates the vacuum-orthogonal
  complement; `T₀` is idempotent (`T₀ ∘L T₀ = T₀`).
  **The lattice gap at `β = 0` is therefore exactly `1`:**
  the spectrum of `T₀` is `{1}` on the vacuum line and `{0}`
  on its complement.

## The fences (read before citing)

* **NO CLAIM on any part of any official Clay statement.**
  Parts of the official Yang–Mills statement closed by this
  stage: **0**. This is finite-volume lattice scaffolding on a
  fixed finite torus.
* **The general-`β` gap is NOT claimed and NOT proved here.**
  What is missing, named: (i) spectral input on `T_β` at fixed
  `β > 0` — classically one shows `T_β` is a compact
  (indeed positive) operator and reads the gap off its
  spectrum; neither compactness nor a spectral theorem for
  this operator is formalized in this corpus (priced M–L);
  (ii) a gap at fixed `β` uniform in the volume/coupling
  along a continuum trajectory is Stage 3c's uniform
  estimates — research-scale, open in print. The exact
  `β = 0` gap of §8 does not extend by any argument in this
  file.
* **The quadratic form of `T` is NOT identified with Stage
  1b-B's `osForm`.** That identification would route through
  a time-direction Markov/layer factorization of the Gibbs
  measure (factoring the weight across slices), which is not
  formalized in this corpus (priced M–L). It is fenced, not
  spent — and in particular **nothing in this file routes
  through Stage 1b-B's Gram clause**: the positivity proved
  here (`transferOp_form_nonneg`) is positivity of the
  two-slice kernel pairing, proved from the definition of the
  Gibbs measure as a positive measure, not from OS-form
  positivity. The Gram clause (character-expansion
  factorization of the Wilson weight; priced XL,
  Mathlib-blocked on Peter–Weyl orthogonality for general
  compact groups) remains OPEN, and **PARTIAL-δ for Stage 1b
  as a whole is still NOT claimed**: δ needs B's positivity,
  which still waits on that clause.
* **Pointwise positivity of `T_β f`** (that `T_β` sends
  positive functions to positive functions) is NOT stated:
  the form positivity of §7 is what the kernel argument gives
  directly in `L²`. The pointwise statement follows from the
  form by the standard indicator-function argument; it is
  routine but not formalized here (priced S).
* `2 ≤ N` is assumed wherever the time-`1` slice is
  identified with the time-`0` slice (a one-step transfer on
  a one-slice torus is degenerate); even `N` is assumed only
  where reflection symmetry is consumed (self-adjointness),
  matching Stage 1b-A's hypotheses.

This module is NOT in the root import list of the library
(the corpus pattern for recent exhibits); it is verified by a
targeted build.
-/

namespace ThetLogos

open MeasureTheory Finset
open scoped Matrix ENNReal NNReal InnerProduct

/-! ## §1. The time-`1` slice and its transport to slice `0`

The time-`1` stratum mirrors Stage 1b-C's `sliceLinks` with
base time value `1`. The transport between the strata is the
site update `x ↦ update x 0 1` on base sites, which is a
bijection because it only rewrites the time coordinate. -/

section SliceOne

variable {G : Type*} [Group G] [MeasurableSpace G]
variable {N : ℕ} [NeZero N]

/-- The links of the time-`1` slice: spatial direction
(`≠ 0`), base site at time value `1`. -/
def slice1Links : Finset (Link (Fin 4 → ZMod N)) :=
  Finset.univ.filter (fun ℓ => ℓ.2 ≠ 0 ∧ (ℓ.1 0).val = 1)

theorem mem_slice1Links {ℓ : Link (Fin 4 → ZMod N)} :
    ℓ ∈ slice1Links ↔ ℓ.2 ≠ 0 ∧ (ℓ.1 0).val = 1 := by
  simp [slice1Links]

/-- The time-`0` and time-`1` strata are disjoint (a base
site has only one time value). -/
theorem sliceLinks_disjoint_slice1Links :
    Disjoint (sliceLinks (N := N)) (slice1Links (N := N)) := by
  rw [Finset.disjoint_left]
  intro ℓ h0 h1
  rw [mem_sliceLinks] at h0
  rw [mem_slice1Links] at h1
  omega

/-- The value `(1 : ZMod N)` has `ZMod.val` equal to `1`
(needs `N ≥ 2`). -/
theorem val_one_of_two_le (hN2 : 2 ≤ N) : (1 : ZMod N).val = 1 := by
  have h1N : 1 < N := by omega
  have h1 : (1 : ZMod N) = ((1 : ℕ) : ZMod N) := by
    rw [Nat.cast_one]
  rw [h1]
  exact ZMod.val_natCast_of_lt h1N

/-- The link equivalence between the time-`0` and time-`1`
strata: rewrite the base site's time coordinate `0 ↦ 1`.
Needs `2 ≤ N` so that time value `1` is a genuine second
slice. -/
def slice01Equiv (hN2 : 2 ≤ N) :
    ↥(sliceLinks (N := N)) ≃ ↥(slice1Links (N := N)) where
  toFun ℓ := ⟨(Function.update ℓ.1.1 0 1, ℓ.1.2), by
    have h := (mem_sliceLinks).mp ℓ.2
    rw [mem_slice1Links]
    refine ⟨h.1, ?_⟩
    show ((Function.update ℓ.1.1 0 1) 0).val = 1
    rw [Function.update_self, val_one_of_two_le hN2]⟩
  invFun ℓ' := ⟨(Function.update ℓ'.1.1 0 0, ℓ'.1.2), by
    have h := (mem_slice1Links).mp ℓ'.2
    rw [mem_sliceLinks]
    refine ⟨h.1, ?_⟩
    show ((Function.update ℓ'.1.1 0 0) 0).val = 0
    rw [Function.update_self]
    exact ZMod.val_zero⟩
  left_inv ℓ := by
    have h := (mem_sliceLinks).mp ℓ.2
    have hx0 : ℓ.1.1 0 = 0 := (ZMod.val_eq_zero _).mp h.2
    apply Subtype.ext
    apply Prod.ext
    · show Function.update (Function.update ℓ.1.1 0 1) 0 0 = ℓ.1.1
      rw [Function.update_idem]
      have h2 : Function.update ℓ.1.1 0 (0 : ZMod N)
          = Function.update ℓ.1.1 0 (ℓ.1.1 0) := by
        rw [hx0]
      rw [h2, Function.update_eq_self]
    · rfl
  right_inv ℓ' := by
    have h := (mem_slice1Links).mp ℓ'.2
    have hy1 : ℓ'.1.1 0 = 1 := by
      have hcast := ZMod.natCast_zmod_val (ℓ'.1.1 0)
      rw [h.2, Nat.cast_one] at hcast
      exact hcast.symm
    apply Subtype.ext
    apply Prod.ext
    · show Function.update (Function.update ℓ'.1.1 0 0) 0 1 = ℓ'.1.1
      rw [Function.update_idem, ← hy1, Function.update_eq_self]
    · rfl

/-- Reading a time-`1` slice configuration on the time-`0`
slice, along `slice01Equiv`. -/
def sliceStep (hN2 : 2 ≤ N) (w : ↥(slice1Links (N := N)) → G) :
    ↥(sliceLinks (N := N)) → G :=
  fun ℓ => w (slice01Equiv hN2 ℓ)

/-- Reading a time-`0` slice configuration on the time-`1`
slice, along the inverse transport. -/
def sliceStepBack (hN2 : 2 ≤ N) (z : ↥(sliceLinks (N := N)) → G) :
    ↥(slice1Links (N := N)) → G :=
  fun ℓ' => z (slice01Equiv hN2 |>.symm ℓ')

theorem measurable_sliceStep (hN2 : 2 ≤ N) :
    Measurable (sliceStep (G := G) (N := N) hN2) := by
  unfold sliceStep
  exact Measurable.of_eval fun ℓ =>
    measurable_pi_apply (slice01Equiv hN2 ℓ)

theorem measurable_sliceStepBack (hN2 : 2 ≤ N) :
    Measurable (sliceStepBack (G := G) (N := N) hN2) := by
  unfold sliceStepBack
  exact Measurable.of_eval fun ℓ' =>
    measurable_pi_apply (slice01Equiv hN2 |>.symm ℓ')

theorem sliceStep_sliceStepBack (hN2 : 2 ≤ N)
    (z : ↥(sliceLinks (N := N)) → G) :
    sliceStep hN2 (sliceStepBack hN2 z) = z := by
  funext ℓ
  show z (slice01Equiv hN2 |>.symm (slice01Equiv hN2 ℓ)) = z ℓ
  rw [Equiv.symm_apply_apply]

theorem sliceStepBack_sliceStep (hN2 : 2 ≤ N)
    (w : ↥(slice1Links (N := N)) → G) :
    sliceStepBack hN2 (sliceStep hN2 w) = w := by
  funext ℓ'
  show w (slice01Equiv hN2 (slice01Equiv hN2 |>.symm ℓ')) = w ℓ'
  rw [Equiv.apply_symm_apply]

/-- The next slice's content, read on the time-`0` slice: the
input of the transfer operator's second leg. -/
def nextConfig (hN2 : 2 ≤ N) (U : Config (Fin 4 → ZMod N) G) :
    ↥(sliceLinks (N := N)) → G :=
  sliceStep hN2 (restrictConfig slice1Links U)

theorem measurable_nextConfig (hN2 : 2 ≤ N) :
    Measurable (nextConfig (G := G) (N := N) hN2) :=
  measurable_sliceStep hN2 |>.comp (measurable_restrictConfig slice1Links)

end SliceOne

/-! ## §2. Translation invariance of the Gibbs measure

Stage 1b-A proved the Gibbs measure is invariant under the
configuration reflection; the same argument, with the Wilson
action's invariance under a commuting site permutation in
place of reflection invariance, gives invariance under
`shiftConfig e`. The proof of `gibbsMeasure_map_shiftConfig`
mirrors `gibbsMeasure_map_reflConfig` step for step. -/

section Shift

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ))
  {N : ℕ} [NeZero N]

/-- The link permutation induced by a site permutation:
permute the base sites, keep the directions. Oriented so
that the induced configuration map (precomposition along the
inverse) reads `U (e x, μ)` at `(x, μ)`. -/
def shiftLinkEquiv (e : Equiv.Perm (Fin 4 → ZMod N)) :
    Equiv.Perm (Link (Fin 4 → ZMod N)) where
  toFun ℓ := (e.symm ℓ.1, ℓ.2)
  invFun ℓ := (e ℓ.1, ℓ.2)
  left_inv ℓ := Prod.ext (Equiv.apply_symm_apply e ℓ.1) rfl
  right_inv ℓ := Prod.ext (Equiv.symm_apply_apply e ℓ.1) rfl

/-- The configuration map induced by a site permutation:
the shifted configuration reads `U (e x, μ)` at `(x, μ)`. -/
def shiftConfig (e : Equiv.Perm (Fin 4 → ZMod N))
    (U : Config (Fin 4 → ZMod N) G) : Config (Fin 4 → ZMod N) G :=
  fun ℓ => U (e ℓ.1, ℓ.2)

/-- `shiftConfig` as a measurable equivalence (precomposition
along the link permutation). -/
def shiftConfigEquiv (e : Equiv.Perm (Fin 4 → ZMod N)) :
    Config (Fin 4 → ZMod N) G ≃ᵐ Config (Fin 4 → ZMod N) G :=
  MeasurableEquiv.piCongrLeft (fun _ : Link (Fin 4 → ZMod N) => G)
    (shiftLinkEquiv e)

theorem shiftConfigEquiv_apply (e : Equiv.Perm (Fin 4 → ZMod N))
    (U : Config (Fin 4 → ZMod N) G) (ℓ : Link (Fin 4 → ZMod N)) :
    shiftConfigEquiv e U ℓ = U (e ℓ.1, ℓ.2) := by
  have h := MeasurableEquiv.piCongrLeft_apply_apply
    (β := fun _ : Link (Fin 4 → ZMod N) => G) (shiftLinkEquiv e)
    U ((shiftLinkEquiv e).symm ℓ)
  rw [Equiv.apply_symm_apply] at h
  exact h

/-- `shiftConfig` agrees pointwise with its measurable-
equivalence presentation. -/
theorem shiftConfig_eq_shiftConfigEquiv (e : Equiv.Perm (Fin 4 → ZMod N))
    (U : Config (Fin 4 → ZMod N) G) :
    shiftConfig e U = shiftConfigEquiv e U := by
  funext ℓ
  show U (e ℓ.1, ℓ.2) = shiftConfigEquiv e U ℓ
  rw [shiftConfigEquiv_apply]

theorem measurable_shiftConfig (e : Equiv.Perm (Fin 4 → ZMod N)) :
    Measurable (shiftConfig (G := G) (N := N) e) :=
  Measurable.of_eval fun ℓ => measurable_pi_apply (e ℓ.1, ℓ.2)

/-- The product-Haar measure is invariant under any
`shiftConfig` (a coordinate permutation of the product). -/
theorem measurePreserving_shiftConfig (e : Equiv.Perm (Fin 4 → ZMod N)) :
    MeasurePreserving (shiftConfig e) (configMeasure μG)
      (configMeasure μG) := by
  refine ⟨measurable_shiftConfig e, ?_⟩
  have hpre : ∀ s : Set (Config (Fin 4 → ZMod N) G),
      shiftConfig e ⁻¹' s = (shiftConfigEquiv e) ⁻¹' s := by
    intro s
    ext U
    simp only [Set.mem_preimage, shiftConfig_eq_shiftConfigEquiv e U]
  ext s hs
  rw [Measure.map_apply (measurable_shiftConfig e) hs, hpre s,
    ← Measure.map_apply (shiftConfigEquiv e).measurable hs]
  exact congrArg (fun ν : Measure (Config (Fin 4 → ZMod N) G) => ν s)
    (measurePreserving_piCongrLeft
      (fun _ : Link (Fin 4 → ZMod N) => μG) (shiftLinkEquiv e)).map_eq

theorem configMeasure_map_shiftConfig (e : Equiv.Perm (Fin 4 → ZMod N)) :
    (configMeasure μG).map (shiftConfig e) = configMeasure μG :=
  (measurePreserving_shiftConfig μG e).map_eq

/-- Plaquettes of a shifted configuration are plaquettes of
the original at the shifted site, provided `e` commutes with
every torus shift. -/
theorem plaquette_shiftConfig (e : Equiv.Perm (Fin 4 → ZMod N))
    (hcomm : ∀ μ x, e (torusShift N μ x) = torusShift N μ (e x))
    (U : Config (Fin 4 → ZMod N) G) (x : Fin 4 → ZMod N) (μ ν : Fin 4) :
    plaquette (torusShift N) (shiftConfig e U) x μ ν
      = plaquette (torusShift N) U (e x) μ ν := by
  show U (e x, μ) * U (e (torusShift N μ x), ν)
      * (U (e (torusShift N ν x), μ))⁻¹ * (U (e x, ν))⁻¹
    = plaquette (torusShift N) U (e x) μ ν
  rw [hcomm μ x, hcomm ν x]
  rfl

/-- The Wilson action is invariant under `shiftConfig e`
(the plaquette at `x` is the plaquette at `e x`, and `e`
permutes the sites). -/
theorem wilsonAction_shiftConfig (e : Equiv.Perm (Fin 4 → ZMod N))
    (hcomm : ∀ μ x, e (torusShift N μ x) = torusShift N μ (e x))
    (β : ℝ) (U : Config (Fin 4 → ZMod N) G) :
    wilsonAction (torusShift N) ρ β (shiftConfig e U)
      = wilsonAction (torusShift N) ρ β U := by
  unfold wilsonAction
  congr 1
  rw [← Equiv.sum_comp e (fun x => ∑ μ, ∑ ν ∈ Finset.Ioi μ,
    plaquetteDensity (torusShift N) ρ U x μ ν)]
  refine Finset.sum_congr rfl fun x _ => ?_
  refine Finset.sum_congr rfl fun μ _ => ?_
  refine Finset.sum_congr rfl fun ν _ => ?_
  show plaquetteDensity (torusShift N) ρ (shiftConfig e U) x μ ν
    = plaquetteDensity (torusShift N) ρ U (e x) μ ν
  unfold plaquetteDensity
  rw [plaquette_shiftConfig e hcomm U x μ ν]

/-- The Gibbs density is invariant under `shiftConfig e`,
because the Wilson action is. -/
theorem gibbsDensity_shiftConfig (e : Equiv.Perm (Fin 4 → ZMod N))
    (hcomm : ∀ μ x, e (torusShift N μ x) = torusShift N μ (e x))
    (β : ℝ) (U : Config (Fin 4 → ZMod N) G) :
    gibbsDensity (torusShift N) ρ β (shiftConfig e U)
      = gibbsDensity (torusShift N) ρ β U := by
  apply Subtype.ext
  show Real.exp (- wilsonAction (torusShift N) ρ β (shiftConfig e U))
    = Real.exp (- wilsonAction (torusShift N) ρ β U)
  rw [wilsonAction_shiftConfig ρ e hcomm β U]

/-- **The Gibbs measure is invariant under `shiftConfig e`**
(strong `Measure.map` form), for every real `β`, whenever
`e` commutes with the torus shifts. Mirror of Stage 1b-A's
`gibbsMeasure_map_reflConfig`. -/
theorem gibbsMeasure_map_shiftConfig (e : Equiv.Perm (Fin 4 → ZMod N))
    (hcomm : ∀ μ x, e (torusShift N μ x) = torusShift N μ (e x))
    (hρcont : Continuous fun g => repMatrix ρ g) (β : ℝ) :
    Measure.map (shiftConfig e) (gibbsMeasure (torusShift N) μG ρ β)
      = gibbsMeasure (torusShift N) μG ρ β := by
  ext s hs
  rw [Measure.map_apply (measurable_shiftConfig e) hs]
  unfold gibbsMeasure
  rw [Measure.smul_apply, Measure.smul_apply]
  have h1 : ((configMeasure μG :
        Measure (Config (Fin 4 → ZMod N) G)).restrict s)
      = Measure.map (shiftConfig e)
          ((configMeasure μG :
            Measure (Config (Fin 4 → ZMod N) G)).restrict
            (shiftConfig e ⁻¹' s)) := by
    rw [← Measure.restrict_map (measurable_shiftConfig e) hs,
      configMeasure_map_shiftConfig μG e]
  have key : (∫⁻ U, (gibbsDensity (torusShift N) ρ β U : ℝ≥0∞)
        ∂((configMeasure μG :
          Measure (Config (Fin 4 → ZMod N) G)).restrict
          (shiftConfig e ⁻¹' s)))
      = ∫⁻ U, (gibbsDensity (torusShift N) ρ β U : ℝ≥0∞)
        ∂((configMeasure μG :
          Measure (Config (Fin 4 → ZMod N) G)).restrict s) := by
    rw [h1, lintegral_map (measurable_gibbsDensity_coe ρ hρcont β)
      (measurable_shiftConfig e)]
    refine lintegral_congr fun U => ?_
    exact congrArg (fun r : ℝ≥0 => (r : ℝ≥0∞))
      (gibbsDensity_shiftConfig ρ e hcomm β U).symm
  have hwd : ((configMeasure μG :
        Measure (Config (Fin 4 → ZMod N) G)).withDensity
        (fun U => (gibbsDensity (torusShift N) ρ β U : ℝ≥0∞)))
        (shiftConfig e ⁻¹' s)
      = ((configMeasure μG :
          Measure (Config (Fin 4 → ZMod N) G)).withDensity
          (fun U => (gibbsDensity (torusShift N) ρ β U : ℝ≥0∞))) s := by
    rw [withDensity_apply _ ((measurable_shiftConfig e) hs),
      withDensity_apply _ hs]
    exact key
  rw [hwd]

/-- The one-step time translation commutes with every torus
shift. -/
theorem torusShift_one_hcomm (μ : Fin 4) (x : Fin 4 → ZMod N) :
    torusShift N 0 (torusShift N μ x)
      = torusShift N μ (torusShift N 0 x) :=
  (torusShift_comm N μ 0 x).symm

/-- The inverse one-step time translation commutes with
every torus shift (coordinate arithmetic: both sides shift
`x μ` by `+1` and `x 0` by `0`, resp. `x 0` by `-1` and the
others by `0`). -/
theorem torusShift_one_symm_hcomm (μ : Fin 4) (x : Fin 4 → ZMod N) :
    (torusShift N 0).symm (torusShift N μ x)
      = torusShift N μ ((torusShift N 0).symm x) := by
  funext j
  rw [torusShift_symm_apply_coord, torusShift_apply_coord,
    torusShift_apply_coord, torusShift_symm_apply_coord]
  by_cases hj0 : j = 0
  · subst hj0
    by_cases hμ : μ = 0
    · subst hμ
      simp [Pi.single_eq_same]
    · simp [Pi.single_eq_of_ne' (Ne.symm hμ), Pi.single_eq_of_ne' hμ]
      -- goal shape: (if ...) arithmetic in ZMod N; closed by the simp set
  · by_cases hμj : j = μ
    · subst hμj
      simp [Pi.single_eq_same, Pi.single_eq_of_ne hj0,
        Pi.single_eq_of_ne (Ne.symm hj0)]
    · simp [Pi.single_eq_of_ne hμj, Pi.single_eq_of_ne' hμj,
        Pi.single_eq_of_ne hj0, Pi.single_eq_of_ne (Ne.symm hj0)]

/-- Products of commuting site permutations: if `e₁` and
`e₂` each commute with every torus shift, so does `e₁ * e₂`
(application order: `e₂` first). -/
theorem perm_mul_hcomm {e₁ e₂ : Equiv.Perm (Fin 4 → ZMod N)}
    (h₁ : ∀ μ x, e₁ (torusShift N μ x) = torusShift N μ (e₁ x))
    (h₂ : ∀ μ x, e₂ (torusShift N μ x) = torusShift N μ (e₂ x))
    (μ : Fin 4) (x : Fin 4 → ZMod N) :
    (e₁ * e₂) (torusShift N μ x) = torusShift N μ ((e₁ * e₂) x) := by
  have step1 : (e₁ * e₂) (torusShift N μ x)
      = e₁ (torusShift N μ (e₂ x)) := by
    rw [Equiv.Perm.mul_apply, h₂]
  rw [step1, h₁, Equiv.Perm.mul_apply]

end Shift

/-! ## §3. Stationarity: the two slices have the same law

The one-step shift identifies the time-`1` marginal, read on
slice `0` along `sliceStepBack`, with the slice measure
itself — at **every** real `β`. This is translation
invariance of the Gibbs measure (§2) read on the slice, and
it is what makes the second leg of the transfer operator an
isometry into the same `L²(ν)` as the first. -/

section Stationarity

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ))
  {N : ℕ} [NeZero N]

/-- A time-`0` site, shifted one step in time, is the
time-update of the site. -/
theorem torusShift_zero_eq_update (x : Fin 4 → ZMod N) (hx : x 0 = 0) :
    torusShift N 0 x = Function.update x 0 1 := by
  funext j
  rw [torusShift_apply_coord]
  by_cases hj : j = 0
  · subst hj
    rw [Pi.single_eq_same, hx, add_zero, Function.update_self]
  · rw [Pi.single_eq_of_ne hj, zero_add, Function.update_of_ne hj]

/-- A time-`1` site, shifted back one step in time, is the
site updated to time `0`. -/
theorem torusShift_symm_zero_eq_update (y : Fin 4 → ZMod N)
    (hy : y 0 = 1) :
    (torusShift N 0).symm y = Function.update y 0 0 := by
  funext j
  rw [torusShift_symm_apply_coord]
  by_cases hj : j = 0
  · subst hj
    rw [Pi.single_eq_same, hy, Function.update_self, sub_self]
  · rw [Pi.single_eq_of_ne hj, sub_zero, Function.update_of_ne hj]

/-- Restricting the one-step-shifted configuration to slice
`0` reads the configuration's time-`1` slice, transported to
slice `0`. -/
theorem restrict_shiftConfig_step (hN2 : 2 ≤ N)
    (U : Config (Fin 4 → ZMod N) G) :
    restrictConfig sliceLinks (shiftConfig (torusShift N 0) U)
      = sliceStep hN2 (restrictConfig slice1Links U) := by
  funext ℓ
  show U (torusShift N 0 ℓ.1.1, ℓ.1.2) = U ((slice01Equiv hN2 ℓ).1)
  have hx0 : ℓ.1.1 0 = 0 :=
    (ZMod.val_eq_zero _).mp (mem_sliceLinks.mp ℓ.2).2
  have hpair : (slice01Equiv hN2 ℓ).1
      = (Function.update ℓ.1.1 0 1, ℓ.1.2) := rfl
  rw [torusShift_zero_eq_update ℓ.1.1 hx0, hpair]

/-- **The slice measure of the time-`1` slice**: the
marginal of the Gibbs measure on `slice1Links`. -/
noncomputable def slice1Measure (β : ℝ) :
    Measure (↥(slice1Links (N := N)) → G) :=
  marginalMeasure (gibbsMeasure (torusShift N) μG ρ β) slice1Links

/-- The time-`1` slice measure is a probability measure, at
every real `β`. -/
theorem isProbabilityMeasure_slice1Measure
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hd : 0 < d)
    (β : ℝ) :
    IsProbabilityMeasure (slice1Measure (N := N) μG ρ β) := by
  haveI := isProbabilityMeasure_gibbsMeasure (torusShift N) μG ρ
    hρcont hd β
  unfold slice1Measure
  infer_instance

/-- **Stationarity of the slice law:** the time-`1` slice
measure, transported back to slice `0`, is the slice
measure — at every real `β`. Proof: the transport is the
restriction after the inverse one-step shift, and the Gibbs
measure is shift-invariant (§2). -/
theorem slice1Measure_eq_sliceMeasure (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g) (β : ℝ) :
    slice1Measure μG ρ β
      = (sliceMeasure μG ρ β).map (sliceStepBack hN2) := by
  have hcomp : sliceStepBack hN2 ∘ restrictConfig (G := G) sliceLinks
      = restrictConfig (G := G) slice1Links
        ∘ shiftConfig (torusShift N 0).symm := by
    funext U ℓ'
    have hy1 : ℓ'.1.1 0 = 1 := by
      have hcast := ZMod.natCast_zmod_val (ℓ'.1.1 0)
      rw [(mem_slice1Links.mp ℓ'.2).2, Nat.cast_one] at hcast
      exact hcast.symm
    have hpair : (slice01Equiv hN2 |>.symm ℓ').1
        = (Function.update ℓ'.1.1 0 0, ℓ'.1.2) := rfl
    show U ((slice01Equiv hN2 |>.symm ℓ').1)
      = U ((torusShift N 0).symm ℓ'.1.1, ℓ'.1.2)
    rw [hpair, torusShift_symm_zero_eq_update ℓ'.1.1 hy1]
  calc slice1Measure μG ρ β
      = (gibbsMeasure (torusShift N) μG ρ β).map
          (restrictConfig slice1Links) := rfl
    _ = ((gibbsMeasure (torusShift N) μG ρ β).map
          (shiftConfig (torusShift N 0).symm)).map
          (restrictConfig slice1Links) := by
        rw [gibbsMeasure_map_shiftConfig μG ρ (torusShift N 0).symm
          torusShift_one_symm_hcomm hρcont β]
    _ = (gibbsMeasure (torusShift N) μG ρ β).map
          (restrictConfig slice1Links
            ∘ shiftConfig (torusShift N 0).symm) := by
        rw [Measure.map_map (measurable_restrictConfig slice1Links)
          (measurable_shiftConfig (torusShift N 0).symm)]
    _ = (gibbsMeasure (torusShift N) μG ρ β).map
          (sliceStepBack hN2 ∘ restrictConfig sliceLinks) := by
        rw [← hcomp]
    _ = ((gibbsMeasure (torusShift N) μG ρ β).map
          (restrictConfig sliceLinks)).map (sliceStepBack hN2) := by
        rw [Measure.map_map (measurable_sliceStepBack hN2)
          (measurable_restrictConfig sliceLinks)]
    _ = (sliceMeasure μG ρ β).map (sliceStepBack hN2) := rfl

/-- The time-`0` restriction is measure-preserving from the
Gibbs measure to the slice measure (the definition of the
slice measure, packaged). -/
theorem measurePreserving_slicePull (β : ℝ) :
    MeasurePreserving (restrictConfig (G := G) sliceLinks)
      (gibbsMeasure (torusShift N) μG ρ β) (sliceMeasure μG ρ β) :=
  ⟨measurable_restrictConfig sliceLinks, rfl⟩

/-- The next-slice reading is measure-preserving from the
Gibbs measure to the slice measure, at every real `β`:
the two legs of the transfer operator land in the same
space. Proof: `nextConfig = sliceStep ∘ restr₁`, the
time-`1` marginal is the transported slice measure
(`slice1Measure_eq_sliceMeasure`), and `sliceStep` undoes
`sliceStepBack`. -/
theorem measurePreserving_nextConfig (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g) (β : ℝ) :
    MeasurePreserving (nextConfig hN2)
      (gibbsMeasure (torusShift N) μG ρ β) (sliceMeasure μG ρ β) := by
  refine ⟨measurable_nextConfig hN2, ?_⟩
  have h1 : (gibbsMeasure (torusShift N) μG ρ β).map (nextConfig hN2)
      = (slice1Measure μG ρ β).map (sliceStep hN2) := by
    show (gibbsMeasure (torusShift N) μG ρ β).map (nextConfig hN2)
      = ((gibbsMeasure (torusShift N) μG ρ β).map
          (restrictConfig slice1Links)).map (sliceStep hN2)
    have hcomp : nextConfig hN2
        = sliceStep hN2 ∘ restrictConfig (G := G) slice1Links := rfl
    rw [hcomp, ← Measure.map_map (measurable_sliceStep hN2)
      (measurable_restrictConfig slice1Links)]
  have hid : sliceStep (G := G) (N := N) hN2
      ∘ sliceStepBack (G := G) (N := N) hN2 = id := by
    funext z
    exact sliceStep_sliceStepBack (G := G) (N := N) hN2 z
  rw [h1, slice1Measure_eq_sliceMeasure μG ρ hN2 hρcont β,
    Measure.map_map (measurable_sliceStep hN2)
      (measurable_sliceStepBack hN2), hid, Measure.map_id]

end Stationarity

/-! ## §4. The transfer operator

`A*` (`slicePull`) and `B*` (`nextPull`) are the two
pullbacks of slice observables to the full configuration
space, as linear isometries into `L²(ν)` — Mathlib's
`Lp.compMeasurePreserving` for the two measure-preserving
readings of §3. The transfer operator is the compression
`T = A*† ∘L B*`. -/

section Operator

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ))
  {N : ℕ} [NeZero N]

/-- Vectors of the OS space are determined by their inner
products against all vectors (the `w`-trick, recorded once
and spent on the vacuum and self-adjointness arguments). -/
theorem eq_of_forall_inner_left (β : ℝ)
    {x y : osSpace (N := N) μG ρ β}
    (h : ∀ g : osSpace (N := N) μG ρ β, inner ℂ g x = inner ℂ g y) :
    x = y := by
  have h0 : inner ℂ (x - y) (x - y) = 0 := by
    have hg := h (x - y)
    rw [inner_sub_right]
    exact sub_eq_zero.mpr hg
  exact sub_eq_zero.mp (inner_self_eq_zero.mp h0)

/-- **The first leg `A*`:** pullback of a slice observable
along the time-`0` restriction, as a linear isometry
`osSpace β → L²(ν)`. -/
noncomputable def slicePull (β : ℝ) :
    osSpace (N := N) μG ρ β →ₗᵢ[ℂ]
      Lp ℂ 2 (gibbsMeasure (torusShift N) μG ρ β) where
  toFun := Lp.compMeasurePreserving (restrictConfig (G := G) sliceLinks)
    (measurePreserving_slicePull (N := N) μG ρ β)
  map_add' := fun f g => map_add _ f g
  map_smul' := fun c f => by
    have hMP := measurePreserving_slicePull (N := N) μG ρ β
    have hsm : ⇑(c • f) ∘ restrictConfig (G := G) sliceLinks
        =ᵐ[gibbsMeasure (torusShift N) μG ρ β]
        (c • ⇑f) ∘ restrictConfig (G := G) sliceLinks :=
      ae_of_ae_map (measurable_restrictConfig sliceLinks).aemeasurable
        (Lp.coeFn_smul c f)
    apply Lp.ext
    filter_upwards [Lp.coeFn_compMeasurePreserving (c • f) hMP,
      Lp.coeFn_compMeasurePreserving f hMP,
      Lp.coeFn_smul c (Lp.compMeasurePreserving
        (restrictConfig (G := G) sliceLinks) hMP f), hsm] with U h1 h2 h3 h4
    simp only [Function.comp_apply, Pi.smul_apply, RingHom.id_apply]
      at h1 h2 h3 h4 ⊢
    rw [h1, h4, h3, h2]
  norm_map' := fun f => Lp.norm_compMeasurePreserving f
    (measurePreserving_slicePull (N := N) μG ρ β)

/-- The first leg acts as composition with the restriction,
almost everywhere. -/
theorem coeFn_slicePull (β : ℝ) (f : osSpace (N := N) μG ρ β) :
    ⇑(slicePull μG ρ β f)
      =ᵐ[gibbsMeasure (torusShift N) μG ρ β]
      ⇑f ∘ restrictConfig (G := G) sliceLinks :=
  Lp.coeFn_compMeasurePreserving f
    (measurePreserving_slicePull (N := N) μG ρ β)

/-- **The second leg `B*`:** pullback of a slice observable
along the next-slice reading, as a linear isometry
`osSpace β → L²(ν)`. Measure-preservation of the reading is
stationarity (§3), so this leg needs `hρcont`. -/
noncomputable def nextPull (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g) (β : ℝ) :
    osSpace (N := N) μG ρ β →ₗᵢ[ℂ]
      Lp ℂ 2 (gibbsMeasure (torusShift N) μG ρ β) where
  toFun := Lp.compMeasurePreserving (nextConfig hN2)
    (measurePreserving_nextConfig (N := N) μG ρ hN2 hρcont β)
  map_add' := fun f g => map_add _ f g
  map_smul' := fun c f => by
    have hMP := measurePreserving_nextConfig (N := N) μG ρ hN2 hρcont β
    have hsm : ⇑(c • f) ∘ nextConfig hN2
        =ᵐ[gibbsMeasure (torusShift N) μG ρ β]
        (c • ⇑f) ∘ nextConfig hN2 := by
      have h : ∀ᵐ y ∂((gibbsMeasure (torusShift N) μG ρ β).map
            (nextConfig hN2)), ⇑(c • f) y = (c • ⇑f) y := by
        rw [hMP.map_eq]
        exact Lp.coeFn_smul c f
      exact ae_of_ae_map (measurable_nextConfig hN2).aemeasurable h
    apply Lp.ext
    filter_upwards [Lp.coeFn_compMeasurePreserving (c • f) hMP,
      Lp.coeFn_compMeasurePreserving f hMP,
      Lp.coeFn_smul c (Lp.compMeasurePreserving (nextConfig hN2) hMP f),
      hsm] with U h1 h2 h3 h4
    simp only [Function.comp_apply, Pi.smul_apply, RingHom.id_apply]
      at h1 h2 h3 h4 ⊢
    rw [h1, h4, h3, h2]
  norm_map' := fun f => Lp.norm_compMeasurePreserving f
    (measurePreserving_nextConfig (N := N) μG ρ hN2 hρcont β)

/-- The second leg acts as composition with the next-slice
reading, almost everywhere. -/
theorem coeFn_nextPull (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g) (β : ℝ)
    (f : osSpace (N := N) μG ρ β) :
    ⇑(nextPull μG ρ hN2 hρcont β f)
      =ᵐ[gibbsMeasure (torusShift N) μG ρ β]
      ⇑f ∘ nextConfig hN2 :=
  Lp.coeFn_compMeasurePreserving f
    (measurePreserving_nextConfig (N := N) μG ρ hN2 hρcont β)

/-- **The transfer operator** `T_β = A*† ∘L B*` on the OS
space: the one-step time evolution of the finite lattice
gauge theory, compressed to the time slice. -/
noncomputable def transferOp (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g) (β : ℝ) :
    osSpace (N := N) μG ρ β →L[ℂ] osSpace (N := N) μG ρ β :=
  ((slicePull μG ρ β).toContinuousLinearMap)†
    ∘L (nextPull μG ρ hN2 hρcont β).toContinuousLinearMap

/-- The transfer operator applied: `T f = A*† (B* f)`. -/
theorem transferOp_apply (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g) (β : ℝ)
    (f : osSpace (N := N) μG ρ β) :
    transferOp μG ρ hN2 hρcont β f
      = ContinuousLinearMap.adjoint (slicePull μG ρ β).toContinuousLinearMap
        (nextPull μG ρ hN2 hρcont β f) :=
  rfl

end Operator

/-! ## §5. The operator package

Everything in this section is at a general real `β` and
routes only through §3's stationarity and Stage 1b-A's
proved reflection invariance — **no Gram clause is spent**.
The form identity is the two-slice Gibbs kernel pairing;
contraction is Cauchy–Schwarz against the two isometries;
the vacuum is fixed because both pullbacks of the constant
observable agree; positivity is the pointwise positivity of
the kernel integrand; self-adjointness is §3's reflection
exchange of the two slices. -/

section Properties

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ))
  {N : ℕ} [NeZero N]

/-- The adjoint leg's continuous-linear-map presentation
acts as the isometry itself. -/
theorem slicePull_toCLM_apply (β : ℝ) (x : osSpace (N := N) μG ρ β) :
    (slicePull μG ρ β).toContinuousLinearMap x = slicePull μG ρ β x :=
  rfl

/-- The second leg's continuous-linear-map presentation
acts as the isometry itself. -/
theorem nextPull_toCLM_apply (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g) (β : ℝ)
    (x : osSpace (N := N) μG ρ β) :
    (nextPull μG ρ hN2 hρcont β).toContinuousLinearMap x
      = nextPull μG ρ hN2 hρcont β x :=
  rfl

/-- **The form identity:** the quadratic form of the
transfer operator is the two-slice Gibbs kernel pairing —
the conjugate of the first observable read on slice `0`
against the second read on slice `1`, integrated against
the Gibbs measure. At every real `β`. -/
theorem transferOp_inner (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g) (β : ℝ)
    (g f : osSpace (N := N) μG ρ β) :
    inner ℂ g (transferOp μG ρ hN2 hρcont β f)
      = ∫ U, (starRingEnd ℂ) (⇑g (restrictConfig (G := G) sliceLinks U))
          * ⇑f (nextConfig hN2 U)
        ∂(gibbsMeasure (torusShift N) μG ρ β) := by
  rw [transferOp_apply, ContinuousLinearMap.adjoint_inner_right,
    slicePull_toCLM_apply, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [coeFn_slicePull μG ρ β g,
    coeFn_nextPull μG ρ hN2 hρcont β f] with U h1 h2
  rw [h1, h2]
  simp only [Function.comp_apply, RCLike.inner_apply, starRingEnd_apply]
  exact mul_comm _ _

/-- **Contraction:** `‖T_β‖ ≤ 1` at every real `β`.
Cauchy–Schwarz against the two isometries:
`‖T f‖² = re ⟪B* f, A* (T f)⟫ ≤ ‖f‖ · ‖T f‖`. -/
theorem transferOp_norm_le (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g) (β : ℝ) :
    ‖transferOp μG ρ hN2 hρcont β‖ ≤ 1 := by
  have hTf : ∀ f : osSpace (N := N) μG ρ β,
      ‖transferOp μG ρ hN2 hρcont β f‖ ≤ ‖f‖ := by
    intro f
    by_cases hf : transferOp μG ρ hN2 hρcont β f = 0
    · rw [hf, norm_zero]
      exact norm_nonneg f
    · have hstep : RCLike.re (inner ℂ (transferOp μG ρ hN2 hρcont β f)
            (transferOp μG ρ hN2 hρcont β f))
          = RCLike.re (inner ℂ (nextPull μG ρ hN2 hρcont β f)
            (slicePull μG ρ β (transferOp μG ρ hN2 hρcont β f))) := by
        rw [transferOp_apply, ContinuousLinearMap.adjoint_inner_left,
          slicePull_toCLM_apply]
      have hnorm : ‖transferOp μG ρ hN2 hρcont β f‖ ^ 2
          = RCLike.re (inner ℂ (transferOp μG ρ hN2 hρcont β f)
            (transferOp μG ρ hN2 hρcont β f)) :=
        (inner_self_eq_norm_sq _).symm
      have h2 : ‖transferOp μG ρ hN2 hρcont β f‖ ^ 2
          ≤ ‖f‖ * ‖transferOp μG ρ hN2 hρcont β f‖ := by
        rw [hnorm, hstep]
        calc RCLike.re (inner ℂ (nextPull μG ρ hN2 hρcont β f)
              (slicePull μG ρ β (transferOp μG ρ hN2 hρcont β f)))
            ≤ ‖nextPull μG ρ hN2 hρcont β f‖
              * ‖slicePull μG ρ β (transferOp μG ρ hN2 hρcont β f)‖ :=
            re_inner_le_norm _ _
          _ = ‖f‖ * ‖transferOp μG ρ hN2 hρcont β f‖ := by
              have e1 : ‖nextPull μG ρ hN2 hρcont β f‖ = ‖f‖ :=
                (nextPull μG ρ hN2 hρcont β).norm_map' f
              have e2 : ‖slicePull μG ρ β
                    (transferOp μG ρ hN2 hρcont β f)‖
                  = ‖transferOp μG ρ hN2 hρcont β f‖ :=
                (slicePull μG ρ β).norm_map' _
              rw [e1, e2]
      have ha : 0 < ‖transferOp μG ρ hN2 hρcont β f‖ :=
        norm_pos_iff.mpr hf
      rw [pow_two] at h2
      exact le_of_mul_le_mul_right h2 ha
  exact ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun f => by
    rw [one_mul]
    exact hTf f

/-- The second leg sends the vacuum to the constant
function `1` on configuration space, almost everywhere
(the pulled-back constant observable). -/
theorem coeFn_nextPull_osVacuum (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hd : 0 < d)
    (β : ℝ) :
    ⇑(nextPull μG ρ hN2 hρcont β (osVacuum (N := N) μG ρ hρcont hd β))
      =ᵐ[gibbsMeasure (torusShift N) μG ρ β] fun _ => (1 : ℂ) := by
  haveI := isProbabilityMeasure_sliceMeasure (N := N) μG ρ hρcont hd β
  have hvac : ⇑(osVacuum (N := N) μG ρ hρcont hd β)
      =ᵐ[sliceMeasure (N := N) μG ρ β] fun _ => (1 : ℂ) := by
    show ⇑(MeasureTheory.Lp.const 2 (sliceMeasure (N := N) μG ρ β)
        (1 : ℂ))
      =ᵐ[sliceMeasure (N := N) μG ρ β] fun _ => (1 : ℂ)
    exact MeasureTheory.Lp.coeFn_const 2 _ (1 : ℂ)
  have h2 : ∀ᵐ U ∂(gibbsMeasure (torusShift N) μG ρ β),
      ⇑(osVacuum (N := N) μG ρ hρcont hd β) (nextConfig hN2 U) = 1 := by
    have h : ∀ᵐ y ∂((gibbsMeasure (torusShift N) μG ρ β).map
          (nextConfig hN2)),
        ⇑(osVacuum (N := N) μG ρ hρcont hd β) y = 1 := by
      rw [(measurePreserving_nextConfig (N := N) μG ρ hN2 hρcont β).map_eq]
      exact hvac
    exact ae_of_ae_map (measurable_nextConfig hN2).aemeasurable h
  filter_upwards [coeFn_nextPull μG ρ hN2 hρcont β
      (osVacuum (N := N) μG ρ hρcont hd β), h2] with U h1 h3
  simp only [Function.comp_apply, h1, h3]

/-- The adjoint of the first leg sends any vector of
`L²(ν)` that is almost everywhere `1` to the vacuum: the
slice integral of the conjugate observable, read through
the marginal. -/
theorem slicePull_adjoint_of_coeFn_one
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hd : 0 < d)
    (β : ℝ) (x : Lp ℂ 2 (gibbsMeasure (torusShift N) μG ρ β))
    (hx : ⇑x =ᵐ[gibbsMeasure (torusShift N) μG ρ β]
      fun _ => (1 : ℂ)) :
    ContinuousLinearMap.adjoint (slicePull μG ρ β).toContinuousLinearMap x
      = osVacuum (N := N) μG ρ hρcont hd β := by
  haveI := isProbabilityMeasure_sliceMeasure (N := N) μG ρ hρcont hd β
  apply eq_of_forall_inner_left μG ρ β
  intro g
  have hφ : AEStronglyMeasurable
      (fun z => (starRingEnd ℂ) (⇑g z))
      (sliceMeasure (N := N) μG ρ β) :=
    Complex.continuous_conj.comp_aestronglyMeasurable
      (Lp.aestronglyMeasurable g)
  have hvac : ⇑(osVacuum (N := N) μG ρ hρcont hd β)
      =ᵐ[sliceMeasure (N := N) μG ρ β] fun _ => (1 : ℂ) := by
    show ⇑(MeasureTheory.Lp.const 2 (sliceMeasure (N := N) μG ρ β)
        (1 : ℂ))
      =ᵐ[sliceMeasure (N := N) μG ρ β] fun _ => (1 : ℂ)
    exact MeasureTheory.Lp.coeFn_const 2 _ (1 : ℂ)
  have hL : (∫ U, inner ℂ (⇑(slicePull μG ρ β g) U) (⇑x U)
        ∂(gibbsMeasure (torusShift N) μG ρ β))
      = ∫ U, (starRingEnd ℂ) (⇑g (restrictConfig (G := G) sliceLinks U))
        ∂(gibbsMeasure (torusShift N) μG ρ β) := by
    apply integral_congr_ae
    filter_upwards [coeFn_slicePull μG ρ β g, hx] with U h1 h2
    rw [h1, h2]
    simp [RCLike.inner_apply]
  have hR : (∫ z, inner ℂ (⇑g z)
        (⇑(osVacuum (N := N) μG ρ hρcont hd β) z)
        ∂(sliceMeasure (N := N) μG ρ β))
      = ∫ z, (starRingEnd ℂ) (⇑g z)
        ∂(sliceMeasure (N := N) μG ρ β) := by
    apply integral_congr_ae
    filter_upwards [hvac] with z hz
    rw [hz]
    simp [RCLike.inner_apply]
  rw [ContinuousLinearMap.adjoint_inner_right, slicePull_toCLM_apply,
    MeasureTheory.L2.inner_def, inner_osSpace]
  exact hL.trans ((integral_sliceMeasure μG ρ β
    (fun z => (starRingEnd ℂ) (⇑g z)) hφ).symm.trans hR.symm)

/-- **The vacuum is fixed:** `T_β Ω = Ω` at every real `β`
(stationarity of the Gibbs measure, as an operator
identity). -/
theorem transferOp_vacuum (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hd : 0 < d)
    (β : ℝ) :
    transferOp μG ρ hN2 hρcont β (osVacuum (N := N) μG ρ hρcont hd β)
      = osVacuum (N := N) μG ρ hρcont hd β := by
  rw [transferOp_apply]
  exact slicePull_adjoint_of_coeFn_one μG ρ hρcont hd β _
    (coeFn_nextPull_osVacuum μG ρ hN2 hρcont hd β)

end Properties

/-! ## §6. The reflection step

Self-adjointness of `T_β` is the reflection symmetry of
the two-slice kernel. The symmetry is implemented on
configurations by `Ψ` = (shift by `−2` in time) ∘
(reflection): Stage 1b-A's reflection sends slice `0` to
slice `−1`; shifting the reflected configuration back by
two lattice units exchanges slices `0` and `1`. `Ψ`
preserves the Gibbs measure (both factors do), and its
action on the two slices is exactly the
`slice01Equiv` exchange — the two restriction identities
below. `Ψ` needs the length-two time direction, like
everything here: `2 ≤ N`; the Gibbs invariance needs the
evenness `Even N` that Stage 1b-A's reflection invariance
already asks for. -/

section ReflectionStep

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ))
  {N : ℕ} [NeZero N]

/-- The reflection step: reflect, then shift by `−2` in
the time direction (two inverse unit shifts). -/
def reflStepConfig : Config (Fin 4 → ZMod N) G
    → Config (Fin 4 → ZMod N) G :=
  fun U => shiftConfig ((torusShift N 0).symm * (torusShift N 0).symm)
    (reflConfig U)

theorem measurable_reflStepConfig :
    Measurable (reflStepConfig (G := G) (N := N)) :=
  (measurable_shiftConfig
    ((torusShift N 0).symm * (torusShift N 0).symm)).comp
    (measurable_reflConfig (G := G) (N := N))

/-- The reflection step preserves the Gibbs measure at
every real `β` (needs `Even N`, as reflection invariance
does): `Measure.map` form. -/
theorem gibbsMeasure_map_reflStepConfig
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hN : Even N)
    (β : ℝ) :
    Measure.map reflStepConfig (gibbsMeasure (torusShift N) μG ρ β)
      = gibbsMeasure (torusShift N) μG ρ β := by
  have h1 : reflStepConfig (N := N)
      = shiftConfig ((torusShift N 0).symm * (torusShift N 0).symm)
        ∘ (reflConfig (G := G) (N := N)) := rfl
  rw [h1, ← Measure.map_map
      (measurable_shiftConfig
        ((torusShift N 0).symm * (torusShift N 0).symm))
      measurable_reflConfig,
    gibbsMeasure_map_reflConfig ρ μG hρcont hN β,
    gibbsMeasure_map_shiftConfig μG ρ
      ((torusShift N 0).symm * (torusShift N 0).symm)
      (perm_mul_hcomm torusShift_one_symm_hcomm
        torusShift_one_symm_hcomm) hρcont β]

theorem measurePreserving_reflStepConfig
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hN : Even N)
    (β : ℝ) :
    MeasurePreserving reflStepConfig
      (gibbsMeasure (torusShift N) μG ρ β)
      (gibbsMeasure (torusShift N) μG ρ β) :=
  ⟨measurable_reflStepConfig,
    gibbsMeasure_map_reflStepConfig μG ρ hρcont hN β⟩

/-- The double inverse unit shift subtracts `2` from the
time coordinate and fixes the others. -/
theorem torusShift_symm_two_eq (x : Fin 4 → ZMod N) :
    ((torusShift N 0).symm * (torusShift N 0).symm) x
      = Function.update x 0 (x 0 - 2) := by
  funext j
  rw [Equiv.Perm.mul_apply, torusShift_symm_apply_coord,
    torusShift_symm_apply_coord]
  by_cases hj : j = 0
  · subst hj
    simp only [Pi.single_eq_same, Function.update_self]
    ring
  · simp only [Pi.single_eq_of_ne hj, Function.update_of_ne hj,
      sub_zero]

/-- On a site of time `0`, reflection after the `−2` shift
lands at time `1`: `reflSite (e₋₂ x) = update x 0 1`. -/
theorem reflSite_torusShift_symm_two (x : Fin 4 → ZMod N)
    (hx : x 0 = 0) :
    reflSite (((torusShift N 0).symm * (torusShift N 0).symm) x)
      = Function.update x 0 1 := by
  funext j
  rw [torusShift_symm_two_eq]
  by_cases hj : j = 0
  · subst hj
    rw [reflSite_apply_self, Function.update_self,
      Function.update_self, hx]
    ring
  · rw [reflSite_apply_of_ne _ hj, Function.update_of_ne hj,
      Function.update_of_ne hj]

/-- On a site of time `1`, reflection after the `−2` shift
lands back at time `0`: `reflSite (e₋₂ y) = update y 0 0`. -/
theorem reflSite_torusShift_symm_two_of_one (y : Fin 4 → ZMod N)
    (hy : y 0 = 1) :
    reflSite (((torusShift N 0).symm * (torusShift N 0).symm) y)
      = Function.update y 0 0 := by
  funext j
  rw [torusShift_symm_two_eq]
  by_cases hj : j = 0
  · subst hj
    rw [reflSite_apply_self, Function.update_self,
      Function.update_self, hy]
    ring
  · rw [reflSite_apply_of_ne _ hj, Function.update_of_ne hj,
      Function.update_of_ne hj]

/-- **Slice exchange, forward:** the slice-`0` restriction
of the reflected configuration is the slice-`1`
restriction stepped forward — `restr₀ (Ψ U) = nextConfig U`
in disguise. -/
theorem restrict_reflStepConfig_zero (hN2 : 2 ≤ N)
    (U : Config (Fin 4 → ZMod N) G) :
    restrictConfig sliceLinks (reflStepConfig U)
      = sliceStep hN2 (restrictConfig slice1Links U) := by
  funext ℓ
  have hμ : ℓ.1.2 ≠ 0 := (mem_sliceLinks.mp ℓ.2).1
  have hx0 : ℓ.1.1 0 = 0 :=
    (ZMod.val_eq_zero _).mp (mem_sliceLinks.mp ℓ.2).2
  have hpair : (slice01Equiv hN2 ℓ).1
      = (Function.update ℓ.1.1 0 1, ℓ.1.2) := rfl
  have step1 : reflStepConfig U ℓ.1
      = reflConfig U (((torusShift N 0).symm * (torusShift N 0).symm)
        ℓ.1.1, ℓ.1.2) := rfl
  have step2 : reflConfig U (((torusShift N 0).symm
        * (torusShift N 0).symm) ℓ.1.1, ℓ.1.2)
      = U (reflSite (((torusShift N 0).symm * (torusShift N 0).symm)
        ℓ.1.1), ℓ.1.2) :=
    reflConfig_apply_of_ne U hμ
  show reflStepConfig U ℓ.1 = U ((slice01Equiv hN2 ℓ).1)
  rw [step1, step2, reflSite_torusShift_symm_two ℓ.1.1 hx0, hpair]

/-- **Slice exchange, backward:** the slice-`1` restriction
of the reflected configuration is the slice-`0`
restriction stepped back — the input of the
`nextConfig (Ψ U) = restr₀ U` computation. -/
theorem restrict_reflStepConfig_one (hN2 : 2 ≤ N)
    (U : Config (Fin 4 → ZMod N) G) :
    restrictConfig slice1Links (reflStepConfig U)
      = sliceStepBack hN2 (restrictConfig sliceLinks U) := by
  funext ℓ'
  have hμ : ℓ'.1.2 ≠ 0 := (mem_slice1Links.mp ℓ'.2).1
  have hy1 : ℓ'.1.1 0 = 1 := by
    have hval : (ℓ'.1.1 0).val = (1 : ZMod N).val := by
      rw [val_one_of_two_le hN2]
      exact (mem_slice1Links.mp ℓ'.2).2
    have h1 : ((ℓ'.1.1 0).val : ZMod N) = ((1 : ZMod N).val : ZMod N) := by
      rw [hval]
    rwa [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val] at h1
  have hpair : ((slice01Equiv hN2).symm ℓ').1
      = (Function.update ℓ'.1.1 0 0, ℓ'.1.2) := rfl
  have step1 : reflStepConfig U ℓ'.1
      = reflConfig U (((torusShift N 0).symm * (torusShift N 0).symm)
        ℓ'.1.1, ℓ'.1.2) := rfl
  have step2 : reflConfig U (((torusShift N 0).symm
        * (torusShift N 0).symm) ℓ'.1.1, ℓ'.1.2)
      = U (reflSite (((torusShift N 0).symm * (torusShift N 0).symm)
        ℓ'.1.1), ℓ'.1.2) :=
    reflConfig_apply_of_ne U hμ
  show reflStepConfig U ℓ'.1 = U (((slice01Equiv hN2).symm ℓ').1)
  rw [step1, step2, reflSite_torusShift_symm_two_of_one ℓ'.1.1 hy1,
    hpair]

/-- The second leg at the reflected configuration is the
slice-`0` restriction itself: `nextConfig (Ψ U) = restr₀ U`. -/
theorem nextConfig_reflStepConfig (hN2 : 2 ≤ N)
    (U : Config (Fin 4 → ZMod N) G) :
    nextConfig hN2 (reflStepConfig U)
      = restrictConfig sliceLinks U := by
  show sliceStep hN2 (restrictConfig slice1Links (reflStepConfig U))
    = restrictConfig sliceLinks U
  rw [restrict_reflStepConfig_one hN2 U, sliceStep_sliceStepBack]

end ReflectionStep

/-! ## §7. Self-adjointness and positivity of the form

Self-adjointness: the pairing `⟪T f, g⟫` is the reflected
kernel pairing — composing the integrand with the
reflection step `Ψ` of §6 exchanges the two slices and
returns the pairing `⟪f, T g⟫`. Positivity: for
slice observables that are real and nonnegative, the
kernel integrand of the form identity is pointwise a
product of two real nonnegative numbers, so the form is
real and nonnegative. Both at every real `β`; neither
spends the Gram clause (the form here is the operator's
own form, not 1b-B's `osForm` — the identification of the
two is fenced, see the header). -/

section SelfAdjointPositivity

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ))
  {N : ℕ} [NeZero N]

/-- **Kernel symmetry:** `⟪T_β f, g⟫ = ⟪f, T_β g⟫` at
every real `β` (with `Even N`, for the reflection).
The two kernel pairings agree after composing the
integrand with the measure-preserving reflection step. -/
theorem transferOp_inner_symm (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ) (f g : osSpace (N := N) μG ρ β) :
    inner ℂ (transferOp μG ρ hN2 hρcont β f) g
      = inner ℂ f (transferOp μG ρ hN2 hρcont β g) := by
  have hφ₂ : AEStronglyMeasurable
      (fun U => (starRingEnd ℂ) (⇑f (nextConfig hN2 U))
        * ⇑g (restrictConfig (G := G) sliceLinks U))
      (gibbsMeasure (torusShift N) μG ρ β) :=
    AEStronglyMeasurable.mul
      (Complex.continuous_conj.comp_aestronglyMeasurable
        ((Lp.aestronglyMeasurable f).comp_measurePreserving
          (measurePreserving_nextConfig (N := N) μG ρ hN2 hρcont β)))
      ((Lp.aestronglyMeasurable g).comp_measurePreserving
        (measurePreserving_slicePull μG ρ β))
  have hφ : (fun U => (starRingEnd ℂ) (⇑f (nextConfig hN2 U))
        * ⇑g (restrictConfig (G := G) sliceLinks U))
        ∘ reflStepConfig
      = fun U => (starRingEnd ℂ) (⇑f (restrictConfig (G := G)
          sliceLinks U)) * ⇑g (nextConfig hN2 U) := by
    funext U
    show (starRingEnd ℂ) (⇑f (nextConfig hN2 (reflStepConfig U)))
        * ⇑g (restrictConfig (G := G) sliceLinks (reflStepConfig U))
      = (starRingEnd ℂ) (⇑f (restrictConfig (G := G) sliceLinks U))
        * ⇑g (sliceStep hN2 (restrictConfig slice1Links U))
    rw [nextConfig_reflStepConfig hN2 U,
      restrict_reflStepConfig_zero hN2 U]
  have hInt2 : (∫ U, (starRingEnd ℂ) (⇑f (nextConfig hN2 U))
        * ⇑g (restrictConfig (G := G) sliceLinks U)
        ∂(gibbsMeasure (torusShift N) μG ρ β))
      = ∫ U, (starRingEnd ℂ) (⇑f (restrictConfig (G := G)
          sliceLinks U)) * ⇑g (nextConfig hN2 U)
        ∂(gibbsMeasure (torusShift N) μG ρ β) := by
    have hmp := measurePreserving_reflStepConfig μG ρ hρcont hN β
    calc (∫ U, (starRingEnd ℂ) (⇑f (nextConfig hN2 U))
          * ⇑g (restrictConfig (G := G) sliceLinks U)
          ∂(gibbsMeasure (torusShift N) μG ρ β))
        = ∫ U, (starRingEnd ℂ) (⇑f (nextConfig hN2 U))
          * ⇑g (restrictConfig (G := G) sliceLinks U)
          ∂((gibbsMeasure (torusShift N) μG ρ β).map
            reflStepConfig) := by
          rw [hmp.map_eq]
      _ = ∫ U, ((fun U => (starRingEnd ℂ) (⇑f (nextConfig hN2 U))
            * ⇑g (restrictConfig (G := G) sliceLinks U))
            ∘ reflStepConfig) U
          ∂(gibbsMeasure (torusShift N) μG ρ β) :=
          integral_map
            (measurable_reflStepConfig (G := G) (N := N)).aemeasurable
            (by rw [hmp.map_eq]; exact hφ₂)
      _ = ∫ U, (starRingEnd ℂ) (⇑f (restrictConfig (G := G)
            sliceLinks U)) * ⇑g (nextConfig hN2 U)
          ∂(gibbsMeasure (torusShift N) μG ρ β) := by
          rw [hφ]
  have hL : (∫ U, inner ℂ (⇑(nextPull μG ρ hN2 hρcont β f) U)
        (⇑(slicePull μG ρ β g) U)
        ∂(gibbsMeasure (torusShift N) μG ρ β))
      = ∫ U, (starRingEnd ℂ) (⇑f (nextConfig hN2 U))
          * ⇑g (restrictConfig (G := G) sliceLinks U)
        ∂(gibbsMeasure (torusShift N) μG ρ β) := by
    apply integral_congr_ae
    filter_upwards [coeFn_nextPull μG ρ hN2 hρcont β f,
      coeFn_slicePull μG ρ β g] with U h1 h2
    rw [h1, h2]
    simp only [Function.comp_apply, RCLike.inner_apply,
      starRingEnd_apply]
    exact mul_comm _ _
  rw [transferOp_apply, ContinuousLinearMap.adjoint_inner_left,
    slicePull_toCLM_apply, MeasureTheory.L2.inner_def, hL,
    transferOp_inner μG ρ hN2 hρcont β f g]
  exact hInt2

/-- **Self-adjointness:** `T_β† = T_β` at every real `β`
(with `Even N`). -/
theorem transferOp_adjoint (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ) :
    ContinuousLinearMap.adjoint (transferOp μG ρ hN2 hρcont β)
      = transferOp μG ρ hN2 hρcont β := by
  apply ContinuousLinearMap.ext
  intro g
  apply eq_of_forall_inner_left μG ρ β
  intro f
  rw [ContinuousLinearMap.adjoint_inner_right]
  exact transferOp_inner_symm μG ρ hN2 hρcont hN β f g

/-- **Self-adjointness, star form:** `IsSelfAdjoint T_β`. -/
theorem transferOp_isSelfAdjoint (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ) :
    IsSelfAdjoint (transferOp μG ρ hN2 hρcont β) :=
  ContinuousLinearMap.isSelfAdjoint_iff'.mpr
    (transferOp_adjoint μG ρ hN2 hρcont hN β)

/-- **Positivity of the form on positive observables:**
for real nonnegative slice observables `f, g`, the form
`⟪g, T_β f⟫` is real and nonnegative — the kernel
integrand is pointwise a product of two real nonnegative
numbers. At every real `β`; no Gram clause spent. -/
theorem transferOp_form_nonneg (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hd : 0 < d)
    (β : ℝ) (f g : (↥(sliceLinks (N := N)) → G) → ℂ)
    (hf : MemLp f 2 (sliceMeasure (N := N) μG ρ β))
    (hg : MemLp g 2 (sliceMeasure (N := N) μG ρ β))
    (hfpos : ∀ z, 0 ≤ (f z).re ∧ (f z).im = 0)
    (hgpos : ∀ z, 0 ≤ (g z).re ∧ (g z).im = 0) :
    0 ≤ (inner ℂ (sliceState μG ρ β g hg)
        (transferOp μG ρ hN2 hρcont β (sliceState μG ρ β f hf))).re
      ∧ (inner ℂ (sliceState μG ρ β g hg)
        (transferOp μG ρ hN2 hρcont β
          (sliceState μG ρ β f hf))).im = 0 := by
  haveI := isProbabilityMeasure_gibbsMeasure (torusShift N) μG ρ
    hρcont hd β
  have hform : inner ℂ (sliceState μG ρ β g hg)
        (transferOp μG ρ hN2 hρcont β (sliceState μG ρ β f hf))
      = ∫ U, (starRingEnd ℂ) (g (restrictConfig (G := G)
            sliceLinks U)) * f (nextConfig hN2 U)
        ∂(gibbsMeasure (torusShift N) μG ρ β) := by
    rw [transferOp_inner μG ρ hN2 hρcont β (sliceState μG ρ β g hg)
      (sliceState μG ρ β f hf)]
    apply integral_congr_ae
    have hgt : ∀ᵐ y ∂((gibbsMeasure (torusShift N) μG ρ β).map
          (restrictConfig (G := G) sliceLinks)),
        ⇑(sliceState μG ρ β g hg) y = g y := by
      have h2 : (gibbsMeasure (torusShift N) μG ρ β).map
            (restrictConfig (G := G) sliceLinks)
          = sliceMeasure (N := N) μG ρ β := rfl
      rw [h2]
      exact hg.coeFn_toLp
    have hft : ∀ᵐ y ∂((gibbsMeasure (torusShift N) μG ρ β).map
          (nextConfig hN2)),
        ⇑(sliceState μG ρ β f hf) y = f y := by
      rw [(measurePreserving_nextConfig (N := N) μG ρ hN2
        hρcont β).map_eq]
      exact hf.coeFn_toLp
    filter_upwards [ae_of_ae_map
        (measurable_restrictConfig sliceLinks).aemeasurable hgt,
      ae_of_ae_map (measurable_nextConfig hN2).aemeasurable hft]
      with U h1U h2U
    rw [h1U, h2U]
  have hInt : Integrable
      (fun U => (starRingEnd ℂ) (g (restrictConfig (G := G)
          sliceLinks U)) * f (nextConfig hN2 U))
      (gibbsMeasure (torusShift N) μG ρ β) :=
    MemLp.integrable_mul
      ((hg.comp_measurePreserving
        (measurePreserving_slicePull μG ρ β)).star)
      (hf.comp_measurePreserving
        (measurePreserving_nextConfig (N := N) μG ρ hN2 hρcont β))
  have hpt : ∀ U, 0 ≤ ((starRingEnd ℂ)
        (g (restrictConfig (G := G) sliceLinks U))
        * f (nextConfig hN2 U)).re
      ∧ ((starRingEnd ℂ) (g (restrictConfig (G := G) sliceLinks U))
        * f (nextConfig hN2 U)).im = 0 := by
    intro U
    have ha := hgpos (restrictConfig (G := G) sliceLinks U)
    have hb := hfpos (nextConfig hN2 U)
    constructor
    · have h1 : ((starRingEnd ℂ)
            (g (restrictConfig (G := G) sliceLinks U))
            * f (nextConfig hN2 U)).re
          = (g (restrictConfig (G := G) sliceLinks U)).re
            * (f (nextConfig hN2 U)).re := by
        simp [Complex.mul_re, Complex.conj_re, Complex.conj_im,
          ha.2, hb.2]
      rw [h1]
      exact mul_nonneg ha.1 hb.1
    · simp [Complex.mul_im, Complex.conj_re, Complex.conj_im,
        ha.2, hb.2]
  rw [hform]
  constructor
  · have hre : (∫ U, (starRingEnd ℂ)
          (g (restrictConfig (G := G) sliceLinks U))
          * f (nextConfig hN2 U)
          ∂(gibbsMeasure (torusShift N) μG ρ β)).re
        = ∫ U, ((starRingEnd ℂ)
            (g (restrictConfig (G := G) sliceLinks U))
            * f (nextConfig hN2 U)).re
          ∂(gibbsMeasure (torusShift N) μG ρ β) :=
      (integral_re hInt).symm
    rw [hre]
    exact integral_nonneg_of_ae (ae_of_all _ fun U => (hpt U).1)
  · have him : (∫ U, (starRingEnd ℂ)
          (g (restrictConfig (G := G) sliceLinks U))
          * f (nextConfig hN2 U)
          ∂(gibbsMeasure (torusShift N) μG ρ β)).im
        = ∫ U, ((starRingEnd ℂ)
            (g (restrictConfig (G := G) sliceLinks U))
            * f (nextConfig hN2 U)).im
          ∂(gibbsMeasure (torusShift N) μG ρ β) :=
      (integral_im hInt).symm
    rw [him, integral_congr_ae (ae_of_all _ fun U => (hpt U).2)]
    simp

end SelfAdjointPositivity

/-! ## §8. The gap at `β = 0`: `T₀` is the vacuum projection

At `β = 0` the Gibbs measure is the product measure
(Stage 0/1a), and Stage 1a's disjoint-support
factorization splits the two-slice kernel pairing into a
product of two one-slice expectations. The transfer
operator collapses to rank one: `T₀ f = ⟪Ω, f⟫ • Ω`,
the orthogonal projection onto the vacuum line. In
particular `T₀` is idempotent, kills the vacuum's
orthogonal complement, and its spectrum is `{1, 0}` —
**the lattice gap at `β = 0` is exactly `1`**. This is
the free (infinite-temperature) point; no interacting
gap is claimed anywhere in this module (see the header
for the general-`β` fence). -/

section ZeroGap

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ))
  {N : ℕ} [NeZero N]

/-- Pairing with the vacuum on the left is the slice
expectation. -/
theorem inner_osVacuum_left
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hd : 0 < d)
    (β : ℝ) (f : osSpace (N := N) μG ρ β) :
    inner ℂ (osVacuum (N := N) μG ρ hρcont hd β) f
      = ∫ z, ⇑f z ∂(sliceMeasure (N := N) μG ρ β) := by
  haveI := isProbabilityMeasure_sliceMeasure (N := N) μG ρ hρcont
    hd β
  have hvac : ⇑(osVacuum (N := N) μG ρ hρcont hd β)
      =ᵐ[sliceMeasure (N := N) μG ρ β] fun _ => (1 : ℂ) := by
    show ⇑(MeasureTheory.Lp.const 2 (sliceMeasure (N := N) μG ρ β)
        (1 : ℂ))
      =ᵐ[sliceMeasure (N := N) μG ρ β] fun _ => (1 : ℂ)
    exact MeasureTheory.Lp.coeFn_const 2 _ (1 : ℂ)
  rw [inner_osSpace]
  apply integral_congr_ae
  filter_upwards [hvac] with z hz
  rw [hz]
  simp [RCLike.inner_apply]

/-- Pairing with the vacuum on the right is the slice
expectation of the conjugate. -/
theorem inner_osVacuum_right
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hd : 0 < d)
    (β : ℝ) (g : osSpace (N := N) μG ρ β) :
    inner ℂ g (osVacuum (N := N) μG ρ hρcont hd β)
      = ∫ z, (starRingEnd ℂ) (⇑g z)
        ∂(sliceMeasure (N := N) μG ρ β) := by
  haveI := isProbabilityMeasure_sliceMeasure (N := N) μG ρ hρcont
    hd β
  have hvac : ⇑(osVacuum (N := N) μG ρ hρcont hd β)
      =ᵐ[sliceMeasure (N := N) μG ρ β] fun _ => (1 : ℂ) := by
    show ⇑(MeasureTheory.Lp.const 2 (sliceMeasure (N := N) μG ρ β)
        (1 : ℂ))
      =ᵐ[sliceMeasure (N := N) μG ρ β] fun _ => (1 : ℂ)
    exact MeasureTheory.Lp.coeFn_const 2 _ (1 : ℂ)
  rw [inner_osSpace]
  apply integral_congr_ae
  filter_upwards [hvac] with z hz
  rw [hz]
  simp [RCLike.inner_apply]

/-- The conjugate vacuum expectation is `1`. -/
theorem integral_conj_osVacuum
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hd : 0 < d)
    (β : ℝ) :
    ∫ z, (starRingEnd ℂ)
        (⇑(osVacuum (N := N) μG ρ hρcont hd β) z)
        ∂(sliceMeasure (N := N) μG ρ β) = 1 := by
  haveI := isProbabilityMeasure_sliceMeasure (N := N) μG ρ hρcont
    hd β
  have hvac : ⇑(osVacuum (N := N) μG ρ hρcont hd β)
      =ᵐ[sliceMeasure (N := N) μG ρ β] fun _ => (1 : ℂ) := by
    show ⇑(MeasureTheory.Lp.const 2 (sliceMeasure (N := N) μG ρ β)
        (1 : ℂ))
      =ᵐ[sliceMeasure (N := N) μG ρ β] fun _ => (1 : ℂ)
    exact MeasureTheory.Lp.coeFn_const 2 _ (1 : ℂ)
  have hce : (fun z => (starRingEnd ℂ)
        (⇑(osVacuum (N := N) μG ρ hρcont hd β) z))
      =ᵐ[sliceMeasure (N := N) μG ρ β] fun _ => (1 : ℂ) :=
    hvac.mono fun z hz => by
      show (starRingEnd ℂ)
          (⇑(osVacuum (N := N) μG ρ hρcont hd β) z) = 1
      rw [hz]; simp
  rw [integral_congr_ae hce]
  simp

/-- **The factorized form at `β = 0`:** the kernel pairing
splits as a product of the two one-slice expectations —
Stage 1a's disjoint-support factorization applied to the
two slices. -/
theorem transferOp_zero_inner (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hd : 0 < d)
    (f g : osSpace (N := N) μG ρ 0) :
    inner ℂ g (transferOp μG ρ hN2 hρcont 0 f)
      = (∫ z, (starRingEnd ℂ) (⇑g z)
          ∂(sliceMeasure (N := N) μG ρ 0))
        * (∫ z, ⇑f z ∂(sliceMeasure (N := N) μG ρ 0)) := by
  have hμ₀ : (configMeasure μG).map
        (restrictConfig (G := G) sliceLinks)
      = sliceMeasure (N := N) μG ρ 0 := by
    show (configMeasure μG).map (restrictConfig (G := G) sliceLinks)
      = marginalMeasure (gibbsMeasure (torusShift N) μG ρ 0)
        sliceLinks
    rw [gibbsMeasure_zero]
    rfl
  have hμ₁ : (configMeasure μG).map (nextConfig hN2)
      = sliceMeasure (N := N) μG ρ 0 := by
    have h := (measurePreserving_nextConfig (N := N) μG ρ hN2
      hρcont 0).map_eq
    rwa [gibbsMeasure_zero] at h
  have hφ : AEStronglyMeasurable (fun z => (starRingEnd ℂ) (⇑g z))
      (sliceMeasure (N := N) μG ρ 0) :=
    Complex.continuous_conj.comp_aestronglyMeasurable
      (Lp.aestronglyMeasurable g)
  have hfac1 : ∫ z, (starRingEnd ℂ) (⇑g z)
        ∂(sliceMeasure (N := N) μG ρ 0)
      = ∫ U, (starRingEnd ℂ) (⇑g (restrictConfig (G := G)
          sliceLinks U)) ∂(configMeasure μG) := by
    have h := integral_map
      (measurable_restrictConfig sliceLinks).aemeasurable
      (show AEStronglyMeasurable (fun z => (starRingEnd ℂ) (⇑g z))
          ((configMeasure μG).map (restrictConfig (G := G) sliceLinks))
        from by rw [hμ₀]; exact hφ)
    rwa [hμ₀] at h
  have hfac2 : ∫ z, ⇑f z ∂(sliceMeasure (N := N) μG ρ 0)
      = ∫ U, ⇑f (nextConfig hN2 U) ∂(configMeasure μG) := by
    have h := integral_map (measurable_nextConfig hN2).aemeasurable
      (show AEStronglyMeasurable (fun z => ⇑f z)
          ((configMeasure μG).map (nextConfig hN2))
        from by rw [hμ₁]; exact Lp.aestronglyMeasurable f)
    rwa [hμ₁] at h
  have key : gibbsExpect (torusShift N) μG ρ 0
        (fun U => (starRingEnd ℂ) (⇑g (restrictConfig (G := G)
            sliceLinks U)) * ⇑f (nextConfig hN2 U))
      = (∫ z, (starRingEnd ℂ) (⇑g z)
          ∂(sliceMeasure (N := N) μG ρ 0))
        * (∫ z, ⇑f z ∂(sliceMeasure (N := N) μG ρ 0)) := by
    rw [gibbsExpect_zero_mul_of_disjoint_dependsOnlyOn
        (torusShift N) μG ρ
        (fun U => (starRingEnd ℂ) (⇑g (restrictConfig (G := G)
          sliceLinks U)))
        (fun U => ⇑f (nextConfig hN2 U))
        sliceLinks slice1Links sliceLinks_disjoint_slice1Links
        (fun w => (starRingEnd ℂ) (⇑g w))
        (fun w => ⇑f (sliceStep hN2 w))
        (fun U => rfl) (fun U => rfl),
      gibbsExpect_zero, gibbsExpect_zero, ← hfac1, ← hfac2]
  rw [transferOp_inner μG ρ hN2 hρcont 0 g f,
    ← gibbsExpect_eq_integral (torusShift N) μG ρ hρcont hd 0
      (fun U => (starRingEnd ℂ) (⇑g (restrictConfig (G := G)
        sliceLinks U)) * ⇑f (nextConfig hN2 U))]
  exact key

/-- **`T₀` is the vacuum projection:** `T₀ f = ⟪Ω, f⟫ • Ω`
at `β = 0` — rank one, range the vacuum line. -/
theorem transferOp_zero_apply (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hd : 0 < d)
    (f : osSpace (N := N) μG ρ 0) :
    transferOp μG ρ hN2 hρcont 0 f
      = (inner ℂ (osVacuum (N := N) μG ρ hρcont hd 0) f)
        • osVacuum (N := N) μG ρ hρcont hd 0 := by
  apply eq_of_forall_inner_left μG ρ 0
  intro g
  rw [transferOp_zero_inner μG ρ hN2 hρcont hd f g, inner_smul_right,
    inner_osVacuum_left μG ρ hρcont hd 0 f,
    inner_osVacuum_right μG ρ hρcont hd 0 g]
  exact mul_comm _ _

/-- `T₀` kills the vacuum's orthogonal complement. -/
theorem transferOp_zero_of_inner_vacuum_eq_zero (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hd : 0 < d)
    (f : osSpace (N := N) μG ρ 0)
    (hf : inner ℂ (osVacuum (N := N) μG ρ hρcont hd 0) f = 0) :
    transferOp μG ρ hN2 hρcont 0 f = 0 := by
  rw [transferOp_zero_apply μG ρ hN2 hρcont hd f, hf, zero_smul]

/-- `T₀` is idempotent: `T₀ ∘L T₀ = T₀` — a projection. -/
theorem transferOp_zero_comp_self (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hd : 0 < d) :
    transferOp μG ρ hN2 hρcont 0 ∘L transferOp μG ρ hN2 hρcont 0
      = transferOp μG ρ hN2 hρcont 0 := by
  apply ContinuousLinearMap.ext
  intro f
  show transferOp μG ρ hN2 hρcont 0
      (transferOp μG ρ hN2 hρcont 0 f)
    = transferOp μG ρ hN2 hρcont 0 f
  calc transferOp μG ρ hN2 hρcont 0
        (transferOp μG ρ hN2 hρcont 0 f)
      = ((∫ z, (starRingEnd ℂ)
            (⇑(osVacuum (N := N) μG ρ hρcont hd 0) z)
            ∂(sliceMeasure (N := N) μG ρ 0))
          * (∫ z, ⇑f z ∂(sliceMeasure (N := N) μG ρ 0)))
        • osVacuum (N := N) μG ρ hρcont hd 0 := by
        rw [transferOp_zero_apply μG ρ hN2 hρcont hd,
          transferOp_zero_inner μG ρ hN2 hρcont hd f
            (osVacuum (N := N) μG ρ hρcont hd 0)]
    _ = (∫ z, ⇑f z ∂(sliceMeasure (N := N) μG ρ 0))
        • osVacuum (N := N) μG ρ hρcont hd 0 := by
        rw [integral_conj_osVacuum μG ρ hρcont hd 0, one_mul]
    _ = transferOp μG ρ hN2 hρcont 0 f := by
        rw [← inner_osVacuum_left μG ρ hρcont hd 0 f,
          ← transferOp_zero_apply μG ρ hN2 hρcont hd f]

end ZeroGap
