import ThetLogos.LatticeBlocking
import Mathlib.Tactic

/-!
# ThetLogos.LatticeBlockingFlow — Pitch 4, Stage 3-facing: RG-1, the
non-closure theorem at a finite seat (T1)

HONESTY LEDGER (read before citing):

- **What this module proves.** `LatticeBlocking` (Stage 2) fenced
  the statement `BlockedGibbsIsCoarseGibbs B β β'` — the blocked
  Gibbs measure *is* a coarse Wilson–Gibbs measure at a single
  coarse coupling `β'` — proving it at `β = 0` (image `β' = 0`)
  and naming it as the Stage-3-facing question at `β > 0`. This
  module settles it **in the negative** at one named finite seat,
  for **every** `β > 0`:

  > `rg1_blocked_not_coarse_gibbs`: at the seat below, there is
  > no `β'` with `BlockedGibbsIsCoarseGibbs flowσ flowσ' μG₀
  > flowSignRep flowBlocking β β'`.

  This is the first flow-shaped theorem of the corpus: the
  blocking trajectory **leaves the Wilson line** at this seat.
  One coupling does not suffice; any β-running here is
  intrinsically multi-coupling, and a `β'(β)` can only ever be a
  *projection* (plaquette matching — RG-2, a separate brick, not
  attempted here).

- **The seat, disclosed in full.** Group
  `G₀ = Multiplicative (ZMod 2)` with the sign character into
  `unitaryGroup (Fin 1) ℂ` (`d = 1`); fine lattice `Fin 2` with
  all four shifts equal to `Equiv.swap 0 1`; coarse lattice
  `Fin 1` with identity shifts; the Stage-2 decimation scheme
  with `ι = fun _ => 0` (blocking factor 2); `μG₀` the uniform
  probability measure on the two-element group. Two disclosures
  ride with the seat and are part of the result's statement, not
  fine print: (a) the group is **abelian**, and the phenomenon
  survives anyway — the blocked measure is genuinely not a
  coarse Wilson–Gibbs measure; (b) at this one-site coarse
  lattice every coarse plaquette is a commutator, hence trivial
  in the abelian group, so the coarse Wilson action is
  *identically zero* and the coarse Gibbs family degenerates to
  the single product measure (every coarse configuration has
  mass `1/16` at every `β'`). The separation is proved against
  that point. What varies — and what no coarse coupling can
  reproduce — is the blocked measure: its effective action,
  computed exactly below, is the multi-link Ising-type form
  `2β Σ_{μ<ν} (1 − sgn w_μ sgn w_ν)` in the blocked links, which
  assigns different masses to different coarse configurations.

- **The mechanism, in one paragraph.** With
  `a_μ = U(0,μ)`, `b_μ = U(1,μ)` and blocked links
  `w_μ = a_μ b_μ`, every fine plaquette at this seat is, as a
  group element, exactly `w_μ w_ν` (`flow_plaquette`): the fine
  Wilson action factors through the blocking map. The two test
  configurations are the trivial coarse configuration `V₁`
  (fiber action `0`) and `V₂`, differing from `V₁` only at the
  direction-3 link (fiber action `12β`). Both fibers have 16
  fine configurations. Hence the blocked masses of `{V₁}` and
  `{V₂}` differ by the factor `exp(−12β) < 1`, while every
  coarse Gibbs measure gives them equal mass `1/16`.

- *(finite-lattice discipline)* Everything is a finite lattice
  at fixed spacing and volume. Nothing here is a continuum
  statement; no β-function, fixed point, criticality, or
  continuum limit is stated or implied. A blocking step remains
  a map; this module proves one fact about the map's image.

- *(standing charter)* "Parts of the official Clay Yang–Mills
  statement closed by this module: 0." Dials: 0/4.

This module is NOT in the root import list of the library (the
corpus pattern for recent exhibits); it is verified by a targeted
build.
-/

namespace ThetLogos

open MeasureTheory Finset
open scoped Matrix ENNReal NNReal

/-! ## §0. The seat group's measure-theoretic instances

`Multiplicative (ZMod 2)` carries no canonical topology or
measurable-space structure in Mathlib, so the seat installs the
discrete ones. There is no competing instance, so nothing here
can diamond against the corpus. -/

instance : TopologicalSpace (Multiplicative (ZMod 2)) := ⊥

instance : MeasurableSpace (Multiplicative (ZMod 2)) := ⊤

instance : DiscreteTopology (Multiplicative (ZMod 2)) := ⟨rfl⟩

instance : BorelSpace (Multiplicative (ZMod 2)) :=
  ⟨borel_eq_top_of_discrete.symm⟩

/-- The uniform probability measure on the two-element seat
group: half the counting measure. -/
noncomputable abbrev μG₀ : Measure (Multiplicative (ZMod 2)) :=
  (2 : ℝ≥0∞)⁻¹ • Measure.count

instance : IsProbabilityMeasure μG₀ := ⟨by
  rw [Measure.smul_apply, smul_eq_mul, Measure.count_univ]
  simp only [ENat.card_eq_coe_natCard, Nat.card_eq_fintype_card]
  norm_num
  exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)⟩

instance : Measure.IsInvInvariant μG₀ where
  inv_eq_self := by
    show Measure.map Inv.inv ((2 : ℝ≥0∞)⁻¹ • Measure.count)
      = (2 : ℝ≥0∞)⁻¹ • Measure.count
    rw [Measure.map_smul _ measurable_inv.aemeasurable,
      Measure.map_inv_eq_self]

theorem μG₀_singleton (g : Multiplicative (ZMod 2)) :
    μG₀ {g} = (2 : ℝ≥0∞)⁻¹ := by
  simp [Measure.smul_apply]

/-! ## §1. The seat group and the sign representation

`G₀ = Multiplicative (ZMod 2)`, its sign character into
`unitaryGroup (Fin 1) ℂ`. The construction follows β2-0's seat
(`PlaneCrossingColumn`), renamed to keep the namespace clean. -/

section SeatGroup

/-- The nonidentity element of the seat group. -/
def flowSeatS : Multiplicative (ZMod 2) := Multiplicative.ofAdd 1

theorem flowSeatS_ne_one : flowSeatS ≠ 1 := by decide

theorem flowSeatS_mul_self : flowSeatS * flowSeatS = 1 := by decide

/-- Every element of the seat group is `1` or `flowSeatS`. -/
theorem flow_eq_one_or_seatS (x : Multiplicative (ZMod 2)) :
    x = 1 ∨ x = flowSeatS := by
  have hall : ∀ y : ZMod 2, y = 0 ∨ y = 1 := by decide
  rcases hall (Multiplicative.toAdd x) with h | h
  · left
    have h' := congrArg Multiplicative.ofAdd h
    simpa using h'
  · right
    have h' := congrArg Multiplicative.ofAdd h
    simpa [flowSeatS] using h'

/-- Every element of the seat group is self-inverse. -/
theorem flow_inv_self (x : Multiplicative (ZMod 2)) : x⁻¹ = x := by
  revert x
  decide

/-- The sign of a seat-group element, as a real number:
`1` at the identity, `−1` at `flowSeatS`. -/
def sgnR (x : Multiplicative (ZMod 2)) : ℝ := if x = 1 then 1 else -1

theorem sgnR_one : sgnR 1 = 1 := by simp [sgnR]

theorem sgnR_seatS : sgnR flowSeatS = -1 := by simp [sgnR, flowSeatS_ne_one]

theorem sgnR_mul (x y : Multiplicative (ZMod 2)) :
    sgnR (x * y) = sgnR x * sgnR y := by
  rcases flow_eq_one_or_seatS x with rfl | rfl <;>
    rcases flow_eq_one_or_seatS y with rfl | rfl <;>
    simp [sgnR, flowSeatS_mul_self, flowSeatS_ne_one]

theorem sgnR_sq (x : Multiplicative (ZMod 2)) : sgnR x ^ 2 = 1 := by
  rcases flow_eq_one_or_seatS x with rfl | rfl
  · simp [sgnR_one]
  · simp [sgnR_seatS]

/-- The sign coefficient as a complex number. -/
def flowSignVal (x : Multiplicative (ZMod 2)) : ℂ := if x = 1 then 1 else -1

theorem flowSignVal_eq (x : Multiplicative (ZMod 2)) :
    flowSignVal x = (sgnR x : ℂ) := by
  by_cases hx : x = 1 <;> simp [flowSignVal, sgnR, hx]

/-- The constant `Fin 1` matrix with entry `flowSignVal x`. -/
def flowSignMat (x : Multiplicative (ZMod 2)) :
    Matrix (Fin 1) (Fin 1) ℂ :=
  Matrix.of (fun _ _ => flowSignVal x)

theorem flowSignMat_apply (x : Multiplicative (ZMod 2)) (i j : Fin 1) :
    flowSignMat x i j = flowSignVal x := rfl

theorem flowSignMat_mul (x y : Multiplicative (ZMod 2)) :
    flowSignMat (x * y) = flowSignMat x * flowSignMat y := by
  ext i j
  fin_cases i <;> fin_cases j
  rw [Matrix.mul_apply, Fin.sum_univ_one]
  simp only [flowSignMat_apply, flowSignVal_eq, sgnR_mul, Complex.ofReal_mul]

theorem flowSignMat_one : flowSignMat 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [flowSignMat, flowSignVal_eq, sgnR_one]

theorem flowSignMat_mem (x : Multiplicative (ZMod 2)) :
    flowSignMat x ∈ Matrix.unitaryGroup (Fin 1) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext i j
  fin_cases i <;> fin_cases j
  rw [Matrix.mul_apply, Fin.sum_univ_one]
  simp only [flowSignMat_apply, Matrix.star_apply, Matrix.one_apply, ite_true]
  by_cases hx : x = 1 <;> simp [flowSignVal, hx]

/-- **The seat representation** `ρ₀`: the sign character of
`Multiplicative (ZMod 2)` into `unitaryGroup (Fin 1) ℂ`. -/
def flowSignRep : Multiplicative (ZMod 2) →*
    ↥(Matrix.unitaryGroup (Fin 1) ℂ) where
  toFun x := ⟨flowSignMat x, flowSignMat_mem x⟩
  map_one' := Subtype.ext flowSignMat_one
  map_mul' x y := Subtype.ext (flowSignMat_mul x y)

theorem repMatrix_flowSignRep (x : Multiplicative (ZMod 2)) :
    repMatrix flowSignRep x = flowSignMat x := rfl

/-- The trace of the seat representation at `x` is the sign. -/
theorem trace_flowSignRep (x : Multiplicative (ZMod 2)) :
    Matrix.trace (repMatrix flowSignRep x) = (sgnR x : ℂ) := by
  rw [repMatrix_flowSignRep]
  simp [Matrix.trace, Matrix.diag, Fin.sum_univ_one, flowSignMat_apply,
    flowSignVal_eq]

theorem trace_flowSignRep_re (x : Multiplicative (ZMod 2)) :
    (Matrix.trace (repMatrix flowSignRep x)).re = sgnR x := by
  rw [trace_flowSignRep]
  simp

/-- The seat representation is continuous (the seat group is
discrete, so every function out of it is). -/
theorem flowSignRep_continuous :
    Continuous fun g : Multiplicative (ZMod 2) => repMatrix flowSignRep g :=
  continuous_of_discreteTopology

end SeatGroup

/-! ## §2. The seat lattices and the blocking scheme

Fine: `Fin 2`, every shift the swap. Coarse: `Fin 1`, identity
shifts. The scheme embeds the coarse site at fine site `0`. -/

section SeatScheme

/-- The fine shifts: every direction swaps the two fine sites. -/
def flowσ : Fin 4 → Equiv.Perm (Fin 2) := fun _ => Equiv.swap 0 1

/-- The coarse shifts: the identity on the one-site lattice. -/
def flowσ' : Fin 4 → Equiv.Perm (Fin 1) := fun _ => Equiv.refl _

theorem flowσ_apply_zero (μ : Fin 4) : flowσ μ 0 = 1 := by
  simp [flowσ, Equiv.swap_apply_left]

theorem flowσ_apply_one (μ : Fin 4) : flowσ μ 1 = 0 := by
  simp [flowσ, Equiv.swap_apply_right]

theorem flowσ'_apply (μ : Fin 4) (y : Fin 1) : flowσ' μ y = y := rfl

/-- **The seat blocking scheme**: coarse site ↦ fine site `0`. -/
def flowBlocking : BlockingScheme flowσ flowσ' where
  ι := fun _ => 0
  ι_injective := fun a b _ => Subsingleton.elim a b
  twoStep := by
    intro μ y
    show flowσ μ (flowσ μ 0) = 0
    rw [flowσ_apply_zero, flowσ_apply_one]
  oddStep := by
    intro μ y h
    have h1 : flowσ μ 0 = 1 := flowσ_apply_zero μ
    rw [h1] at h
    obtain ⟨z, hz⟩ := h
    exact (by decide : (0 : Fin 2) ≠ 1) hz

/-- The blocked link at the seat: the product of the two fine
links over the blocked edge, based at fine sites `0` and `1`. -/
theorem flowBlockMap_apply (U : Config (Fin 2) (Multiplicative (ZMod 2)))
    (y : Fin 1) (μ : Fin 4) :
    blockMap flowσ flowσ' flowBlocking U (y, μ) = U (0, μ) * U (1, μ) := by
  show U (flowBlocking.ι y, μ) * U (flowσ μ (flowBlocking.ι y), μ) = _
  have hι : flowBlocking.ι y = 0 := rfl
  rw [hι, flowσ_apply_zero]

end SeatScheme

/-! ## §3. Fine plaquettes factor through the blocking

The heart of the computation: at this seat every fine plaquette
is, as a group element, the product of two blocked links. The
inverses in the plaquette word disappear (every seat-group
element is self-inverse) and the remaining four factors are
rearranged by commutativity. -/

section PlaquetteFactor

variable (U : Config (Fin 2) (Multiplicative (ZMod 2)))

/-- **Plaquette factorization.** For every fine site `x` and
directions `μ ν`, the fine plaquette at `(x, μ, ν)` equals
`w_μ * w_ν`, the product of the two blocked links over the
coarse site. -/
theorem flow_plaquette (x : Fin 2) (μ ν : Fin 4) :
    plaquette flowσ U x μ ν
      = blockMap flowσ flowσ' flowBlocking U (0, μ)
        * blockMap flowσ flowσ' flowBlocking U (0, ν) := by
  rw [flowBlockMap_apply, flowBlockMap_apply]
  fin_cases x
  · show U (0, μ) * U (flowσ μ 0, ν) * (U (flowσ ν 0, μ))⁻¹ * (U (0, ν))⁻¹
      = U (0, μ) * U (1, μ) * (U (0, ν) * U (1, ν))
    rw [flowσ_apply_zero, flowσ_apply_zero, flow_inv_self, flow_inv_self]
    ac_rfl
  · show U (1, μ) * U (flowσ μ 1, ν) * (U (flowσ ν 1, μ))⁻¹ * (U (1, ν))⁻¹
      = U (0, μ) * U (1, μ) * (U (0, ν) * U (1, ν))
    rw [flowσ_apply_one, flowσ_apply_one, flow_inv_self, flow_inv_self]
    ac_rfl

/-- The fine plaquette density reads the blocked configuration:
it is `1 − sgn(w_μ) · sgn(w_ν)`, independent of the fine site. -/
theorem flow_plaquetteDensity (x : Fin 2) (μ ν : Fin 4) :
    plaquetteDensity flowσ flowSignRep U x μ ν
      = 1 - sgnR (blockMap flowσ flowσ' flowBlocking U (0, μ))
          * sgnR (blockMap flowσ flowσ' flowBlocking U (0, ν)) := by
  unfold plaquetteDensity
  rw [flow_plaquette, trace_flowSignRep_re, sgnR_mul]
  norm_num

end PlaquetteFactor

/-! ## §4. The blocked effective action at the seat

Summing the factorized densities over the two fine sites, the
fine Wilson action is `β` times twice an Ising-type multi-link
form in the blocked links — the generated non-Wilson coupling,
in closed form. -/

section EffectiveAction

/-- The seat's blocked effective action (the multi-link form):
`Σ_{μ<ν} (1 − sgn(w_μ) sgn(w_ν))` in the blocked links `w`. -/
def effAction (V : Config (Fin 1) (Multiplicative (ZMod 2))) : ℝ :=
  ∑ μ : Fin 4, ∑ ν ∈ Finset.Ioi μ,
    (1 - sgnR (V (0, μ)) * sgnR (V (0, ν)))

/-- **The fine Wilson action factors through the blocking**:
`S_β(U) = 2β · effAction(blockMap U)`. -/
theorem flow_wilsonAction (β : ℝ)
    (U : Config (Fin 2) (Multiplicative (ZMod 2))) :
    wilsonAction flowσ flowSignRep β U
      = β * (2 * effAction (blockMap flowσ flowσ' flowBlocking U)) := by
  have h : ∀ x : Fin 2, (∑ μ : Fin 4, ∑ ν ∈ Finset.Ioi μ,
        plaquetteDensity flowσ flowSignRep U x μ ν)
      = ∑ μ : Fin 4, ∑ ν ∈ Finset.Ioi μ,
        (1 - sgnR (blockMap flowσ flowσ' flowBlocking U (0, μ))
          * sgnR (blockMap flowσ flowσ' flowBlocking U (0, ν))) := by
    intro x
    refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => ?_
    exact flow_plaquetteDensity U x μ ν
  show β * (∑ x : Fin 2, ∑ μ : Fin 4, ∑ ν ∈ Finset.Ioi μ,
      plaquetteDensity flowσ flowSignRep U x μ ν) = _
  rw [Fin.sum_univ_two, h 0, h 1]
  unfold effAction
  ring

/-- The trivial coarse configuration. -/
def flowV₁ : Config (Fin 1) (Multiplicative (ZMod 2)) := fun _ => 1

/-- The second test configuration: the nonidentity element at
the direction-`3` link, trivial at the other three links. -/
def flowV₂ : Config (Fin 1) (Multiplicative (ZMod 2)) :=
  fun ℓ => if ℓ.2 = 3 then flowSeatS else 1

theorem sgnR_flowV₁ (μ : Fin 4) : sgnR (flowV₁ (0, μ)) = 1 := sgnR_one

theorem sgnR_flowV₂ (μ : Fin 4) :
    sgnR (flowV₂ (0, μ)) = if μ = 3 then -1 else 1 := by
  by_cases hμ : μ = 3
  · subst hμ
    show sgnR (if (3 : Fin 4) = 3 then flowSeatS else 1) = -1
    rw [if_pos rfl]
    exact sgnR_seatS
  · have h2 : flowV₂ (0, μ) = 1 := by
      show (if μ = 3 then flowSeatS else 1) = 1
      rw [if_neg hμ]
    rw [h2, if_neg hμ]
    exact sgnR_one

/-- The effective action vanishes at the trivial configuration. -/
theorem effAction_flowV₁ : effAction flowV₁ = 0 := by
  refine Finset.sum_eq_zero fun μ _ => Finset.sum_eq_zero fun ν _ => ?_
  rw [sgnR_flowV₁, sgnR_flowV₁]
  norm_num

/-- The effective action at the second test configuration is
exactly `6`: of the six direction pairs, the three meeting
direction `3` contribute `2` each. -/
theorem effAction_flowV₂ : effAction flowV₂ = 6 := by
  have hIoi0 : Finset.Ioi (0 : Fin 4) = {1, 2, 3} := by decide
  have hIoi1 : Finset.Ioi (1 : Fin 4) = {2, 3} := by decide
  have hIoi2 : Finset.Ioi (2 : Fin 4) = {3} := by decide
  have hIoi3 : Finset.Ioi (3 : Fin 4) = ∅ := by decide
  have ht : ∀ μ ν : Fin 4,
      (1 - sgnR (flowV₂ (0, μ)) * sgnR (flowV₂ (0, ν)))
        = if ν = 3 then (if μ = 3 then 0 else 2)
          else (if μ = 3 then 2 else 0) := by
    intro μ ν
    rw [sgnR_flowV₂, sgnR_flowV₂]
    by_cases hν : ν = 3 <;> by_cases hμ : μ = 3 <;>
      simp [hν, hμ] <;> norm_num
  unfold effAction
  rw [Fin.sum_univ_four]
  simp only [ht, hIoi0, hIoi1, hIoi2, hIoi3]
  norm_num [Finset.sum_insert, Finset.sum_singleton]

/-- On the fiber over `V₁` the fine action vanishes. -/
theorem flow_action_fiber_one (β : ℝ)
    {U : Config (Fin 2) (Multiplicative (ZMod 2))}
    (hU : blockMap flowσ flowσ' flowBlocking U = flowV₁) :
    wilsonAction flowσ flowSignRep β U = 0 := by
  rw [flow_wilsonAction, hU, effAction_flowV₁]
  simp

/-- On the fiber over `V₂` the fine action is exactly `12β`. -/
theorem flow_action_fiber_two (β : ℝ)
    {U : Config (Fin 2) (Multiplicative (ZMod 2))}
    (hU : blockMap flowσ flowσ' flowBlocking U = flowV₂) :
    wilsonAction flowσ flowSignRep β U = 12 * β := by
  rw [flow_wilsonAction, hU, effAction_flowV₂]
  ring

end EffectiveAction

/-! ## §5. Singleton masses of the seat configuration measures

Every configuration at either level has the same `configMeasure`
mass — `(1/2)` per link — but the two levels have different
numbers of links: `4` coarse, `8` fine. -/

section SeatMeasure

/-- Singleton masses under a product measure are the product of
the link masses. -/
theorem configMeasure_singleton_eq {Λ' : Type*} [Fintype Λ']
    (V : Config Λ' (Multiplicative (ZMod 2))) :
    (configMeasure μG₀) {V}
      = ∏ ℓ : Link Λ', μG₀ {V ℓ} := by
  have h : ({V} : Set (Config Λ' (Multiplicative (ZMod 2))))
      = Set.univ.pi (fun ℓ : Link Λ' => {V ℓ}) := by
    ext W
    simp [Set.mem_pi, funext_iff]
  rw [configMeasure, h, Measure.pi_pi]

/-- Every coarse configuration has `configMeasure` mass `1/16`. -/
theorem configMeasure_coarse_singleton
    (V : Config (Fin 1) (Multiplicative (ZMod 2))) :
    (configMeasure μG₀) {V} = (16 : ℝ≥0∞)⁻¹ := by
  rw [configMeasure_singleton_eq]
  simp only [μG₀_singleton, Finset.prod_const, Finset.card_univ]
  show ((2 : ℝ≥0∞)⁻¹) ^ (Fintype.card (Fin 1 × Fin 4)) = (16 : ℝ≥0∞)⁻¹
  simp only [Fintype.card_prod, Fintype.card_fin]
  rw [← ENNReal.inv_pow]
  norm_num

/-- Every fine configuration has `configMeasure` mass `1/256`. -/
theorem configMeasure_fine_singleton
    (U : Config (Fin 2) (Multiplicative (ZMod 2))) :
    (configMeasure μG₀) {U} = (256 : ℝ≥0∞)⁻¹ := by
  rw [configMeasure_singleton_eq]
  simp only [μG₀_singleton, Finset.prod_const, Finset.card_univ]
  show ((2 : ℝ≥0∞)⁻¹) ^ (Fintype.card (Fin 2 × Fin 4)) = (256 : ℝ≥0∞)⁻¹
  simp only [Fintype.card_prod, Fintype.card_fin]
  rw [← ENNReal.inv_pow]
  norm_num

/-- The real coarse singleton mass. -/
theorem configMeasure_coarse_singleton_real
    (V : Config (Fin 1) (Multiplicative (ZMod 2))) :
    (configMeasure μG₀).real {V} = 1 / 16 := by
  show ((configMeasure μG₀) {V}).toReal = 1 / 16
  rw [configMeasure_coarse_singleton, ENNReal.toReal_inv]
  norm_num

/-- The real fine singleton mass. -/
theorem configMeasure_fine_singleton_real
    (U : Config (Fin 2) (Multiplicative (ZMod 2))) :
    (configMeasure μG₀).real {U} = 1 / 256 := by
  show ((configMeasure μG₀) {U}).toReal = 1 / 256
  rw [configMeasure_fine_singleton, ENNReal.toReal_inv]
  norm_num

end SeatMeasure

/-! ## §6. The coarse side is trivial at this seat

Every coarse plaquette is a commutator `a b a⁻¹ b⁻¹` (the coarse
shifts are identities), and the seat group is abelian — so every
coarse plaquette is `1`, the coarse Wilson action vanishes
identically, and the whole coarse Gibbs family is the single
product measure. **This degeneracy is disclosed on the module's
face**: the separation below is proved against this point of the
coarse family, and what it shows is that the *blocked* measure
moves while no coarse coupling can follow it. -/

section CoarseTrivial

/-- Every coarse plaquette is trivial: it is a commutator in an
abelian group. -/
theorem flow_coarse_plaquette (V : Config (Fin 1) (Multiplicative (ZMod 2)))
    (y : Fin 1) (μ ν : Fin 4) :
    plaquette flowσ' V y μ ν = 1 := by
  show V (y, μ) * V (y, ν) * (V (y, μ))⁻¹ * (V (y, ν))⁻¹ = 1
  rw [mul_assoc (V (y, μ)) (V (y, ν)) ((V (y, μ))⁻¹),
    mul_comm (V (y, ν)) ((V (y, μ))⁻¹),
    ← mul_assoc (V (y, μ)) ((V (y, μ))⁻¹) (V (y, ν)),
    mul_inv_cancel, one_mul, mul_inv_cancel]

/-- Every coarse plaquette density vanishes. -/
theorem flow_coarse_density (V : Config (Fin 1) (Multiplicative (ZMod 2)))
    (x : Fin 1) (μ ν : Fin 4) :
    plaquetteDensity flowσ' flowSignRep V x μ ν = 0 := by
  unfold plaquetteDensity
  rw [flow_coarse_plaquette, trace_flowSignRep_re, sgnR_one]
  norm_num

/-- The coarse Wilson action is identically zero, at every
coupling. -/
theorem flow_coarse_wilsonAction (β' : ℝ)
    (V : Config (Fin 1) (Multiplicative (ZMod 2))) :
    wilsonAction flowσ' flowSignRep β' V = 0 := by
  simp [wilsonAction, flow_coarse_density]

/-- The coarse partition function is `1` at every coupling. -/
theorem flow_coarse_partition (β' : ℝ) :
    gibbsPartition flowσ' μG₀ flowSignRep β' = 1 := by
  show ∫ _U : Config (Fin 1) (Multiplicative (ZMod 2)),
      Real.exp (- wilsonAction flowσ' flowSignRep β' _U)
      ∂(configMeasure μG₀) = 1
  have h1 : ∀ U : Config (Fin 1) (Multiplicative (ZMod 2)),
      Real.exp (- wilsonAction flowσ' flowSignRep β' U) = 1 := by
    intro U
    rw [flow_coarse_wilsonAction]
    simp
  simp only [h1]
  rw [integral_const, Measure.real, measure_univ, ENNReal.toReal_one,
    one_smul]

/-- **The coarse Gibbs family degenerates to a point**: at every
`β'`, the coarse Gibbs measure is the product measure itself. -/
theorem flow_coarse_gibbsMeasure (β' : ℝ) :
    gibbsMeasure flowσ' μG₀ flowSignRep β' = configMeasure μG₀ := by
  have hdens : (fun U : Config (Fin 1) (Multiplicative (ZMod 2)) =>
      ((gibbsDensity flowσ' flowSignRep β' U : ℝ≥0) : ℝ≥0∞)) = 1 := by
    funext U
    rw [Pi.one_apply, gibbsDensity_coe, flow_coarse_wilsonAction]
    simp
  unfold gibbsMeasure
  rw [flow_coarse_partition, hdens]
  simp [withDensity_one]

end CoarseTrivial

/-! ## §7. The fibers of the blocking map

A fine configuration is exactly its blocked configuration plus
its four links over the coarse sites (`a_μ = U(0,μ)`): the second
layer is then forced, `U(1,μ) = a_μ⁻¹ w_μ`. Hence every fiber
has exactly `2⁴ = 16` elements. -/

section Fibers

/-- The fiber representative: given coarse links `w` and first
layer `a`, the unique fine configuration with those data. -/
def flowFiberRep (V : Config (Fin 1) (Multiplicative (ZMod 2)))
    (a : Fin 4 → Multiplicative (ZMod 2)) :
    Config (Fin 2) (Multiplicative (ZMod 2)) :=
  fun ℓ => if ℓ.1 = 0 then a ℓ.2 else (a ℓ.2)⁻¹ * V (0, ℓ.2)

/-- The representative really lies over `V`. -/
theorem flowFiberRep_blockMap (V : Config (Fin 1) (Multiplicative (ZMod 2)))
    (a : Fin 4 → Multiplicative (ZMod 2)) (μ : Fin 4) :
    blockMap flowσ flowσ' flowBlocking (flowFiberRep V a) (0, μ) = V (0, μ) := by
  rw [flowBlockMap_apply]
  show (if (0 : Fin 2) = 0 then a μ else (a μ)⁻¹ * V (0, μ))
      * (if (1 : Fin 2) = 0 then a μ else (a μ)⁻¹ * V (0, μ)) = V (0, μ)
  rw [if_pos rfl, if_neg (by decide)]
  exact mul_inv_cancel_left _ _

/-- The first layer of the representative is `a`. -/
theorem flowFiberRep_fst (V : Config (Fin 1) (Multiplicative (ZMod 2)))
    (a : Fin 4 → Multiplicative (ZMod 2)) (μ : Fin 4) :
    flowFiberRep V a (0, μ) = a μ := by
  show (if (0 : Fin 2) = 0 then a μ else (a μ)⁻¹ * V (0, μ)) = a μ
  rw [if_pos rfl]

/-- **Fiber parametrization**: the fiber of the blocking map
over `V` is in bijection with the four free first-layer links. -/
def flowFiberEquivAt (V : Config (Fin 1) (Multiplicative (ZMod 2))) :
    {U : Config (Fin 2) (Multiplicative (ZMod 2)) //
      blockMap flowσ flowσ' flowBlocking U = V}
      ≃ (Fin 4 → Multiplicative (ZMod 2)) where
  toFun U := fun μ => U.1 (0, μ)
  invFun a := ⟨flowFiberRep V a, by
    funext ⟨y, μ⟩
    have hy : y = 0 := Subsingleton.elim y 0
    subst hy
    exact flowFiberRep_blockMap V a μ⟩
  left_inv := by
    rintro ⟨U, hU⟩
    apply Subtype.ext
    funext ℓ
    obtain ⟨x, μ⟩ := ℓ
    fin_cases x
    · show (if (0 : Fin 2) = 0 then U (0, μ)
        else (U (0, μ))⁻¹ * V (0, μ)) = U (0, μ)
      rw [if_pos rfl]
    · show (if (1 : Fin 2) = 0 then U (0, μ)
        else (U (0, μ))⁻¹ * V (0, μ)) = U (1, μ)
      rw [if_neg (by decide), ← hU, flowBlockMap_apply]
      exact inv_mul_cancel_left _ _
  right_inv := by
    intro a
    funext μ
    exact flowFiberRep_fst V a μ

/-- Every fiber of the blocking map has exactly `16` elements. -/
theorem flow_fiber_card (V : Config (Fin 1) (Multiplicative (ZMod 2))) :
    (Finset.univ.filter (fun U : Config (Fin 2) (Multiplicative (ZMod 2)) =>
      blockMap flowσ flowσ' flowBlocking U = V)).card = 16 := by
  have h2 : Fintype.card (Multiplicative (ZMod 2)) = 2 := by
    rw [Fintype.card_congr Multiplicative.toAdd]
    exact ZMod.card 2
  rw [← Fintype.card_subtype, Fintype.card_congr (flowFiberEquivAt V),
    Fintype.card_fun, Fintype.card_fin, h2]
  norm_num

end Fibers

/-! ## §8. The two observables and their exact expectations

The observables are the indicators of the two test
configurations. On the coarse side both have expectation `1/16`
at **every** coupling (§6: the coarse family is one point). On
the blocked side the expectations are computed exactly from the
fiber data of §§4–7. -/

section Expectations

/-- The indicator observable of a single coarse configuration. -/
def flowObs (V : Config (Fin 1) (Multiplicative (ZMod 2))) :
    Config (Fin 1) (Multiplicative (ZMod 2)) → ℝ :=
  fun W => if W = V then 1 else 0

/-- Every observable on a seat configuration space is
measurable: the configuration spaces are discrete. -/
theorem measurable_flowObs (V : Config (Fin 1) (Multiplicative (ZMod 2))) :
    Measurable (flowObs V) :=
  Measurable.of_discrete

/-- On these finite discrete configuration spaces every real
observable is integrable against the product measure: bound it
by the sum of its absolute values. -/
theorem flow_integrand_integrable {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : Config ι (Multiplicative (ZMod 2)) → ℝ) :
    Integrable f (configMeasure μG₀) :=
  Integrable.of_bound Measurable.of_discrete.aestronglyMeasurable
    (∑ U, ‖f U‖)
    (ae_of_all _ fun U =>
      Finset.single_le_sum (fun U' _ => norm_nonneg _) (Finset.mem_univ U))

/-- The indicator's integral is the mass of the singleton. -/
theorem flowObs_integral
    (μ : Measure (Config (Fin 1) (Multiplicative (ZMod 2))))
    (V : Config (Fin 1) (Multiplicative (ZMod 2))) :
    ∫ W, flowObs V W ∂μ = μ.real {V} := by
  have hfun : flowObs V
      = Set.indicator ({V} : Set (Config (Fin 1) (Multiplicative (ZMod 2))))
        (fun _ => (1 : ℝ)) := by
    funext W
    by_cases hW : W = V
    · simp [flowObs, hW]
    · simp [flowObs, hW, Set.mem_singleton_iff]
  rw [hfun, integral_indicator_const _ (measurableSet_singleton V),
    smul_eq_mul, mul_one]

/-- **Coarse expectations.** Both test observables have
expectation exactly `1/16` under **every** coarse Gibbs measure
— the coarse curve, at this seat, is a single point. -/
theorem flow_coarse_expect (β' : ℝ)
    (V : Config (Fin 1) (Multiplicative (ZMod 2))) :
    gibbsExpectR flowσ' μG₀ flowSignRep β' (flowObs V) = 1 / 16 := by
  show ∫ W, flowObs V W ∂(gibbsMeasure flowσ' μG₀ flowSignRep β') = 1 / 16
  rw [flow_coarse_gibbsMeasure, flowObs_integral,
    configMeasure_coarse_singleton_real]

/-- The fine numerator integral over one fiber: the Boltzmann
weight is constant on the fiber (§4), the fiber has `16`
configurations (§7), each of `configMeasure` mass `1/256` (§5). -/
theorem flow_num_integral (β : ℝ)
    (V : Config (Fin 1) (Multiplicative (ZMod 2))) (Ŝ : ℝ)
    (hŜ : ∀ U : Config (Fin 2) (Multiplicative (ZMod 2)),
      blockMap flowσ flowσ' flowBlocking U = V →
      wilsonAction flowσ flowSignRep β U = Ŝ) :
    ∫ U : Config (Fin 2) (Multiplicative (ZMod 2)),
        Real.exp (- wilsonAction flowσ flowSignRep β U)
          * flowObs V (blockMap flowσ flowσ' flowBlocking U)
        ∂(configMeasure μG₀)
      = (16 / 256) * Real.exp (-Ŝ) := by
  rw [integral_fintype (flow_integrand_integrable _)]
  simp only [configMeasure_fine_singleton_real, smul_eq_mul]
  calc (∑ U : Config (Fin 2) (Multiplicative (ZMod 2)), (1 / 256 : ℝ)
          * (Real.exp (- wilsonAction flowσ flowSignRep β U)
            * flowObs V (blockMap flowσ flowσ' flowBlocking U)))
      = (1 / 256) * ∑ U : Config (Fin 2) (Multiplicative (ZMod 2)),
          (if blockMap flowσ flowσ' flowBlocking U = V
            then Real.exp (- wilsonAction flowσ flowSignRep β U)
            else 0) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun U _ => ?_
        by_cases hU : blockMap flowσ flowσ' flowBlocking U = V
        · rw [if_pos hU]; simp [flowObs, hU]
        · rw [if_neg hU]; simp [flowObs, hU]
    _ = (1 / 256) * ∑ U ∈ Finset.univ.filter
          (fun U : Config (Fin 2) (Multiplicative (ZMod 2)) =>
            blockMap flowσ flowσ' flowBlocking U = V),
          Real.exp (- wilsonAction flowσ flowSignRep β U) := by
        rw [Finset.sum_filter]
    _ = (1 / 256) * ∑ _U ∈ Finset.univ.filter
          (fun U : Config (Fin 2) (Multiplicative (ZMod 2)) =>
            blockMap flowσ flowσ' flowBlocking U = V),
          Real.exp (-Ŝ) := by
        congr 1
        refine Finset.sum_congr rfl fun U hU => ?_
        rw [hŜ U (Finset.mem_filter.mp hU).2]
    _ = (16 / 256) * Real.exp (-Ŝ) := by
        rw [Finset.sum_const, flow_fiber_card, nsmul_eq_mul]
        ring

/-- **Blocked expectations, exactly.** The blocked expectation
of a fiber-constant observable is the fiber Boltzmann weight
over `16 · Z_β`. -/
theorem flow_blocked_expect (β : ℝ)
    (V : Config (Fin 1) (Multiplicative (ZMod 2))) (Ŝ : ℝ)
    (hŜ : ∀ U : Config (Fin 2) (Multiplicative (ZMod 2)),
      blockMap flowσ flowσ' flowBlocking U = V →
      wilsonAction flowσ flowSignRep β U = Ŝ) :
    gibbsExpectR flowσ μG₀ flowSignRep β
        (flowObs V ∘ blockMap flowσ flowσ' flowBlocking)
      = Real.exp (-Ŝ) / (16 * gibbsPartition flowσ μG₀ flowSignRep β) := by
  rw [gibbsExpectR_eq_ratio flowσ μG₀ flowSignRep flowSignRep_continuous
    (by norm_num) β _]
  simp only [Function.comp_apply]
  rw [flow_num_integral β V Ŝ hŜ]
  have hZ : (0 : ℝ) < gibbsPartition flowσ μG₀ flowSignRep β :=
    gibbsPartition_pos flowσ μG₀ flowSignRep flowSignRep_continuous
      (by norm_num) β
  rw [div_eq_div_iff hZ.ne' (mul_ne_zero (by norm_num) hZ.ne')]
  ring

/-- The blocked expectation of the `V₁` indicator. -/
theorem rg1_blocked_expect_one (β : ℝ) :
    ∫ W, flowObs flowV₁ W
        ∂(blockedGibbsMeasure flowσ flowσ' μG₀ flowSignRep flowBlocking β)
      = 1 / (16 * gibbsPartition flowσ μG₀ flowSignRep β) := by
  rw [integral_blockedGibbsMeasure flowσ flowσ' μG₀ flowSignRep flowBlocking
    β _ (measurable_flowObs flowV₁).aestronglyMeasurable]
  show gibbsExpectR flowσ μG₀ flowSignRep β
      (flowObs flowV₁ ∘ blockMap flowσ flowσ' flowBlocking) = _
  rw [flow_blocked_expect β flowV₁ 0 (fun U hU => flow_action_fiber_one β hU)]
  simp

/-- The blocked expectation of the `V₂` indicator: the `V₁`
value suppressed by exactly `exp (−12β)`. -/
theorem rg1_blocked_expect_two (β : ℝ) :
    ∫ W, flowObs flowV₂ W
        ∂(blockedGibbsMeasure flowσ flowσ' μG₀ flowSignRep flowBlocking β)
      = Real.exp (-(12 * β))
        / (16 * gibbsPartition flowσ μG₀ flowSignRep β) := by
  rw [integral_blockedGibbsMeasure flowσ flowσ' μG₀ flowSignRep flowBlocking
    β _ (measurable_flowObs flowV₂).aestronglyMeasurable]
  show gibbsExpectR flowσ μG₀ flowSignRep β
      (flowObs flowV₂ ∘ blockMap flowσ flowσ' flowBlocking) = _
  exact flow_blocked_expect β flowV₂ (12 * β)
    (fun U hU => flow_action_fiber_two β hU)

end Expectations

/-! ## §9. The verdict

The two blocked expectations differ (for `β > 0`) by the factor
`exp (−12β) < 1`; the two coarse expectations agree at every
`β'`. No single coarse coupling reproduces the blocked measure. -/

section Verdict

/-- **RG-1, the non-closure theorem at the seat.** For every
`β > 0`, the blocked Gibbs measure at the seat of §2 is **not**
a coarse Wilson–Gibbs measure at any single coupling `β'`: the
statement `BlockedGibbsIsCoarseGibbs`, fenced in
`LatticeBlocking` §7, is **false** at this seat for `β > 0`.

The coarse side is computed in §6 (every coarse Gibbs measure
is the product measure; both indicators have expectation
`1/16`); the blocked side in §8 (the indicators have
expectations `1/(16 Z_β)` and `exp(−12β)/(16 Z_β)`). A single
`β'` would force both pairs to agree, hence `exp(−12β) = 1`,
contradicting `β > 0`. -/
theorem rg1_blocked_not_coarse_gibbs {β : ℝ} (hβ : 0 < β) :
    ¬ ∃ β' : ℝ, BlockedGibbsIsCoarseGibbs flowσ flowσ' μG₀ flowSignRep
      flowBlocking β β' := by
  rintro ⟨β', hβ'⟩
  have hEq : blockedGibbsMeasure flowσ flowσ' μG₀ flowSignRep flowBlocking β
      = gibbsMeasure flowσ' μG₀ flowSignRep β' := hβ'
  have hZpos : (0 : ℝ) < gibbsPartition flowσ μG₀ flowSignRep β :=
    gibbsPartition_pos flowσ μG₀ flowSignRep flowSignRep_continuous
      (by norm_num) β
  have key : ∀ V : Config (Fin 1) (Multiplicative (ZMod 2)),
      (∫ W, flowObs V W
          ∂(blockedGibbsMeasure flowσ flowσ' μG₀ flowSignRep flowBlocking β))
        = gibbsExpectR flowσ' μG₀ flowSignRep β' (flowObs V) := by
    intro V
    show (∫ W, flowObs V W
        ∂(blockedGibbsMeasure flowσ flowσ' μG₀ flowSignRep flowBlocking β))
      = ∫ W, flowObs V W ∂(gibbsMeasure flowσ' μG₀ flowSignRep β')
    rw [hEq]
  have e1 := key flowV₁
  have e2 := key flowV₂
  rw [rg1_blocked_expect_one, flow_coarse_expect] at e1
  rw [rg1_blocked_expect_two, flow_coarse_expect] at e2
  have hZ : gibbsPartition flowσ μG₀ flowSignRep β = 1 := by
    rw [div_eq_div_iff (mul_ne_zero (by norm_num) hZpos.ne')
      (by norm_num : (16 : ℝ) ≠ 0)] at e1
    linarith
  rw [hZ] at e2
  have hexp : Real.exp (-(12 * β)) = 1 := by
    rw [div_eq_div_iff (by norm_num : (16 : ℝ) * 1 ≠ 0)
      (by norm_num : (16 : ℝ) ≠ 0)] at e2
    linarith
  have hlt : Real.exp (-(12 * β)) < 1 := by
    have h := Real.exp_strictMono (show (-(12 * β)) < (0 : ℝ) by linarith)
    rwa [Real.exp_zero] at h
  exact (ne_of_lt hlt) hexp

/-- **Corollary (the blocked measure is non-uniform, exactly).**
The blocked masses of the two test configurations stand in the
exact ratio `exp (−12β)`, while every coarse Gibbs measure at
this seat gives the two configurations equal mass. Any
`β'(β)` "flow" here is therefore a projection of a genuinely
multi-coupling trajectory, not a trajectory in the Wilson line
(plaquette matching is RG-2, a separate brick). -/
theorem rg1_blocked_mass_ratio {β : ℝ} (hβ : 0 < β) :
    (blockedGibbsMeasure flowσ flowσ' μG₀ flowSignRep flowBlocking β).real
        {flowV₂}
      = Real.exp (-(12 * β))
        * (blockedGibbsMeasure flowσ flowσ' μG₀ flowSignRep flowBlocking
            β).real {flowV₁} := by
  rw [← flowObs_integral, ← flowObs_integral, rg1_blocked_expect_one,
    rg1_blocked_expect_two, mul_one_div]

/-- **Corollary (non-uniformity).** For `β > 0` the blocked
measure assigns different masses to `{V₁}` and `{V₂}`. -/
theorem rg1_blocked_not_uniform {β : ℝ} (hβ : 0 < β) :
    blockedGibbsMeasure flowσ flowσ' μG₀ flowSignRep flowBlocking β
        {flowV₁}
      ≠ blockedGibbsMeasure flowσ flowσ' μG₀ flowSignRep flowBlocking β
        {flowV₂} := by
  intro hcon
  have hratio := rg1_blocked_mass_ratio hβ
  have hconR : (blockedGibbsMeasure flowσ flowσ' μG₀ flowSignRep
      flowBlocking β).real {flowV₁}
      = (blockedGibbsMeasure flowσ flowσ' μG₀ flowSignRep flowBlocking
          β).real {flowV₂} :=
    congrArg ENNReal.toReal hcon
  rw [hconR] at hratio
  have hZpos : (0 : ℝ) < gibbsPartition flowσ μG₀ flowSignRep β :=
    gibbsPartition_pos flowσ μG₀ flowSignRep flowSignRep_continuous
      (by norm_num) β
  have hX : (0 : ℝ) < (blockedGibbsMeasure flowσ flowσ' μG₀ flowSignRep
      flowBlocking β).real {flowV₂} := by
    rw [← hconR, ← flowObs_integral, rg1_blocked_expect_one]
    exact div_pos (by norm_num) (mul_pos (by norm_num) hZpos)
  have hexp : Real.exp (-(12 * β)) = 1 :=
    (mul_eq_right₀ hX.ne').mp hratio.symm
  have hlt : Real.exp (-(12 * β)) < 1 := by
    have h := Real.exp_strictMono (show (-(12 * β)) < (0 : ℝ) by linarith)
    rwa [Real.exp_zero] at h
  exact (ne_of_lt hlt) hexp

end Verdict

end ThetLogos
