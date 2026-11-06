/-
# SU(3)-center bridge — C-3 (the filter, re-read) + C-4 (the center seat)
(working label `TernarySeatSU3CenterTransport`; naming is Jeff's)

Commission: parent-side completion of the SU(3)-center menu
(scoping dossier
`~/workspace/your_files/ternary-seat-su3-center-scoping-2026-11-05.md`,
§§3.1/4.1/5/6), downstream of C-0..C-2 in
`TernarySeatSU3Center.lean` (landed in-lane: `centerScalarSU3`,
`charFn_centerScalarSU3` with the factor `3` = dimension,
`center_eq_range_centerScalarSU3`,
`su3CenterEquiv : Multiplicative (ZMod 3) ≃* ↥(Subgroup.center ↥SU3)`;
**K-SU3-CENTER decided there: it did NOT fire**).

## What this module is

* **C-3 — the filter, re-read** (scoping §3.1, shape (b1)).  The
  ternary seat's pattern monomial, transported to the center group
  along `su3CenterEquiv`: the center element at a site acts through
  its **scalar character** `centerChar` (= `seatChar₃` read through
  the iso), and the site exponent is TM-2's `patternExp₃ ε c` — the
  ℕ-shadow of the ZMod 3 **site charge** `patternDiv₃ ε c` (the two
  are tied by the landed `patternDiv₃_eq_zero_iff`:
  `patternDiv₃ ε c = 0 ↔ 3 ∣ patternExp₃ ε c`).  The headline
  (`patternSurvives₃_iff_centerMono_invariant`,
  `patternSurvives₃_iff_centerActionFactor₃`): a pattern survives
  the mod-3 divergence filter **iff** its transported monomial is
  invariant under the diagonal action of
  `↥(Subgroup.center ↥SU3)` — the center acting site-wise on
  stratum configurations by left multiplication, the monomial
  transforming by the explicit factor `centerActionFactor₃`.  The
  two stratum averages are identified termwise
  (`center_stratum_average₃`): the average over the center group
  *is* the average over the seat group.  Landing verdict, in the
  scoping's exact words: **the mod-3 divergence filter is, as a
  theorem, the center-neutrality projector of the seat** — the
  strongest form of the triality *analogy* that the corpus's
  objects can honestly carry.  **K-SU3-FILTER is decided in this
  section: it does NOT fire** (no surviving pattern's transported
  monomial transforms nontrivially, and vice versa — the iff is
  proved, both directions).
* **C-4 — the center seat** (scoping §4.1, shape (c1)).  The
  ternary seat rebuilt at `G := ↥(Subgroup.center ↥SU3)`: the
  discrete instance package in TM-1's shape, the uniform measure
  `centerμ`, and the rep `centerRep` — the fundamental
  representation of the bare group `SU3` restricted to the center
  (a `Fin 3` rep whose scalar is `seatChar₃`, by C-1's weld), and
  TM-3's headline re-registered there:
  `layerKernelPos_center_seat`.  **HONEST LABEL: this is a
  re-dressing, not a new seat.**  Its entire mathematical content
  is C-1 + C-2; the transport itself is registration work.  What
  moves is exactly one identification: the layer kernel at the
  center seat *is* the ternary seat kernel read through
  `su3CenterEquiv` (`layerKernel_center`), because the Wilson
  density at either seat reads the word only through the
  normalized character `charFn ρ / d`, and the weld pins
  `charFn centerRep = 3 * centerChar` against
  `charFn seatρ₃ = seatChar₃` — the `3` is the dimension, and it
  cancels in the normalization.  **K-SU3-TRANSPORT is decided in
  this section: it does NOT fire** (every hypothesis of the TM
  chain's headline is iso-stable; the transport is proved).

## Fences (binding on every summary of this module)

* **(b2) remains NOT STATEABLE** (scoping §3.2).  This module
  grades **seat patterns by center charge**; it does NOT grade
  SU(3) representations by triality.  No SU(3) representation
  objects exist in-tree to have triality (`ColorRep` in
  `SMFermions` is a label inductive carrying no group action, no
  tensor product, no character), nothing SU(3)-shaped acts on the
  pattern space, and the represented route to color is closed by
  T1 (`pi_pure_color_zero`, `pi_ker_iff`).  The analogy's one
  structural rhyme — the filter's signed divergence (base branches
  *minus* head branches, values `1` vs `2` in `ZMod 3`) against
  triality `+1` (fundamental) vs `−1 ≡ 2` (antifundamental) — is a
  rhyme: it is mathematics only through C-3's restricted statement,
  never by renaming the filter.
* **K-SU3-PI — PRE-FIRED, inherited.**  The weld and both of its
  transports live on the BARE group `SU3` and nowhere else; this
  module must never be cited as closing `SMGaugeAlgebra` §4's
  priced gap (no independent represented SU(3) gauge action on
  quarks), which stands exactly as priced.
* The SM assembly's measured numbers remain **T2/T4 inputs**; the
  weld derives none of them — **no Dial-1 content**.  Nothing
  about continuum QCD, confinement, glueballs, or the Yang–Mills
  mass gap follows; **NO CLAIM on every Millennium Problem
  stands.**  Triality as a property of SU(3) representations
  remains unformalized and unclaimed.
* **Dial 2 = 0**: no test body, no response law, no gravity
  object of any species is in view.
* **NO CLAIM; dials 0/4 under every outcome.**  Finite algebra:
  two previously separate formalizations shown to be about one
  object — the A0-weld species of result.
-/

import ThetLogos.TernarySeatSU3Center
import ThetLogos.LayerKernelPosTernaryFilter
import ThetLogos.LayerKernelPosTernaryGram
import ThetLogos.LayerKernelPos

open MeasureTheory Finset
open scoped ENNReal

namespace ThetLogos

/-! ## Seat data for the center group (shared by both bricks)

The center group `↥(Subgroup.center ↥SU3)` is a three-element
group: C-2's iso exhibits it as such.  Its `Fintype` instance —
transported along `su3CenterEquiv` — is what both bricks' finite
sums and (in C-4) the uniform measure stand on. -/

/-- The center group is finite, with the finiteness transported
along C-2's iso. -/
noncomputable instance su3CenterSeatFintype :
    Fintype ↥(Subgroup.center ↥SU3) :=
  Fintype.ofEquiv (Multiplicative (ZMod 3)) su3CenterEquiv.toEquiv

/-- The center group has three elements. -/
theorem centerSU3_card :
    Fintype.card ↥(Subgroup.center ↥SU3) = 3 := by
  rw [← Fintype.card_congr su3CenterEquiv.toEquiv]
  exact ternarySeat_card

/-! ## C-3 — the filter, re-read (scoping §3.1)

The transported monomial: a stratum configuration at the center
seat is `γ : LayerSite 2 → ↥(Subgroup.center ↥SU3)`; the center
element `γ c` acts on the monomial through its scalar character
`centerChar (γ c)` raised to the site exponent
`patternExp₃ ε c`.  The diagonal action of a center-valued site
field `η` (left multiplication of configurations) multiplies the
monomial by `centerActionFactor₃ ε η` — proved, not stipulated
(`centerMono₃_act`). -/

/-- The **scalar character of the center**: a central element of
`SU3` acts on `ℂ³` as the scalar `seatChar₃` of its preimage under
the C-2 iso.  By C-1's weld this is `charFn centerRep / 3` — the
center's defining character, read on the center group itself. -/
noncomputable def centerChar (z : ↥(Subgroup.center ↥SU3)) : ℂ :=
  seatChar₃ (su3CenterEquiv.symm z)

/-- The transported character agrees with the seat character along
the iso — the definition of `centerChar`, read forward. -/
theorem centerChar_su3CenterEquiv (g : Multiplicative (ZMod 3)) :
    centerChar (su3CenterEquiv g) = seatChar₃ g := by
  rw [centerChar, MulEquiv.symm_apply_apply]

/-- The scalar character at the identity is `1`. -/
theorem centerChar_one : centerChar 1 = 1 := by
  show seatChar₃ (su3CenterEquiv.symm (1 : ↥(Subgroup.center ↥SU3)))
    = 1
  rw [map_one, seatChar₃_one]

/-- The scalar character is multiplicative: the center action's
scalar of a product is the product of the scalars. -/
theorem centerChar_mul (z w : ↥(Subgroup.center ↥SU3)) :
    centerChar (z * w) = centerChar z * centerChar w := by
  show seatChar₃ (su3CenterEquiv.symm (z * w))
    = seatChar₃ (su3CenterEquiv.symm z)
      * seatChar₃ (su3CenterEquiv.symm w)
  rw [map_mul, seatChar₃_mul]

/-- The scalar character takes cube-root-of-unity values: its cube
is `1` at every central element (the transported form of the seat
character's values `{1, ω, ω²}`). -/
theorem centerChar_cube (z : ↥(Subgroup.center ↥SU3)) :
    (centerChar z) ^ 3 = 1 := by
  show (seatChar₃ (su3CenterEquiv.symm z)) ^ 3 = 1
  rcases seatChar₃_cases (su3CenterEquiv.symm z) with h | h | h <;>
    rw [h]
  · norm_num
  · exact zetaC3_cube
  · have h6 : (zetaC3 ^ 2) ^ 3 = (zetaC3 ^ 3) ^ 2 := by ring
    rw [h6, zetaC3_cube]
    norm_num

/-- The pattern's monomial at the center seat: the product over
sites of the acting center element's scalar character raised to
the site exponent — TM-2's `stratumMono₃` with every seat element
read through `su3CenterEquiv` and every character value the
center's own scalar character. -/
noncomputable def centerMono₃ (ε : LayerColumn 2 → ZMod 3)
    (γ : LayerSite 2 → ↥(Subgroup.center ↥SU3)) : ℂ :=
  ∏ c : LayerSite 2, (centerChar (γ c)) ^ patternExp₃ ε c

/-- The **diagonal action factor**: the scalar by which the
diagonal center action of a site field `η` multiplies the pattern
monomial.  Site by site it is the center's scalar character at
`η c` raised to the site exponent `patternExp₃ ε c` — the
ℕ-shadow of the site charge `patternDiv₃ ε c`
(`patternDiv₃_eq_zero_iff`). -/
noncomputable def centerActionFactor₃ (ε : LayerColumn 2 → ZMod 3)
    (η : LayerSite 2 → ↥(Subgroup.center ↥SU3)) : ℂ :=
  ∏ c : LayerSite 2, (centerChar (η c)) ^ patternExp₃ ε c

/-- The monomial transforms under the diagonal center action by
exactly the action factor: shifting every stratum value by the
site field `η` multiplies the monomial by
`centerActionFactor₃ ε η`, independently of the configuration. -/
theorem centerMono₃_act (ε : LayerColumn 2 → ZMod 3)
    (η γ : LayerSite 2 → ↥(Subgroup.center ↥SU3)) :
    centerMono₃ ε (η * γ)
      = centerActionFactor₃ ε η * centerMono₃ ε γ := by
  unfold centerMono₃ centerActionFactor₃
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun c _ => ?_
  rw [Pi.mul_apply, centerChar_mul, mul_pow]

/-- The transported monomial *is* TM-2's stratum monomial read
through the iso — the pointwise identification behind the two
averages. -/
theorem centerMono₃_su3CenterEquiv (ε : LayerColumn 2 → ZMod 3)
    (α : LayerSite 2 → Multiplicative (ZMod 3)) :
    centerMono₃ ε (fun c => su3CenterEquiv (α c))
      = stratumMono₃ ε α := by
  unfold centerMono₃ stratumMono₃
  refine Finset.prod_congr rfl fun c _ => ?_
  rw [centerChar_su3CenterEquiv]

/-- **The two averages identified.**  The stratum average of the
pattern monomial over the center group equals the stratum average
over the seat group — the same `6561 = 3^8` configurations, the
same values, by reindexing along `su3CenterEquiv` — and hence
equals the filter's verdict directly: `1` if the pattern survives,
`0` otherwise (TM-2's `stratum_average₃`, transported).  This is
C-3's proof obligation as priced: the identification of the two
averages, not new analysis. -/
theorem center_stratum_average₃ (ε : LayerColumn 2 → ZMod 3) :
    (6561 : ℂ)⁻¹
        * ∑ γ : LayerSite 2 → ↥(Subgroup.center ↥SU3),
          centerMono₃ ε γ
      = if patternSurvives₃ ε then 1 else 0 := by
  have hsum :
      (∑ γ : LayerSite 2 → ↥(Subgroup.center ↥SU3),
          centerMono₃ ε γ)
        = ∑ α : LayerSite 2 → Multiplicative (ZMod 3),
            stratumMono₃ ε α := by
    rw [← Equiv.sum_comp
      (Equiv.piCongrRight fun _ : LayerSite 2 =>
        su3CenterEquiv.toEquiv)
      (fun γ => centerMono₃ ε γ)]
    refine Finset.sum_congr rfl fun α _ => ?_
    exact centerMono₃_su3CenterEquiv ε α
  rw [hsum, stratum_average₃]

/-- If the pattern survives, the diagonal action factor is `1` at
every site field: at each site `3 ∣ patternExp₃ ε c`
(`patternDiv₃_eq_zero_iff` on the survival hypothesis), and the
scalar character's cube is `1` (`centerChar_cube`). -/
theorem centerActionFactor₃_eq_one_of_survives
    {ε : LayerColumn 2 → ZMod 3} (hε : patternSurvives₃ ε)
    (η : LayerSite 2 → ↥(Subgroup.center ↥SU3)) :
    centerActionFactor₃ ε η = 1 := by
  unfold centerActionFactor₃
  refine Finset.prod_eq_one fun c _ => ?_
  obtain ⟨k, hk⟩ := (patternDiv₃_eq_zero_iff ε c).mp (hε c)
  rw [hk, pow_mul, centerChar_cube, one_pow]

/-- The monomial at the trivial configuration is `1` (every scalar
character is `1` there). -/
theorem centerMono₃_one (ε : LayerColumn 2 → ZMod 3) :
    centerMono₃ ε (1 : LayerSite 2 → ↥(Subgroup.center ↥SU3))
      = 1 := by
  unfold centerMono₃
  refine Finset.prod_eq_one fun c _ => ?_
  rw [Pi.one_apply, centerChar_one, one_pow]

/-- If the diagonal action factor is `1` at every site field, the
pattern survives: test against the field supported at a single
site `c₀` with the generator's value — the factor there is
`ω^(patternExp₃ ε c₀)`, which is `1` only when
`3 ∣ patternExp₃ ε c₀` (`zetaC3_ne_one`, `zetaC3_sq_ne_one`), i.e.
`patternDiv₃ ε c₀ = 0`.  This is the direction **K-SU3-FILTER**
was armed against: a charge mislabeling under the iso would
surface here as a surviving-but-noninvariant pattern or the
converse, and none does. -/
theorem patternSurvives₃_of_centerActionFactor₃
    {ε : LayerColumn 2 → ZMod 3}
    (h : ∀ η : LayerSite 2 → ↥(Subgroup.center ↥SU3),
      centerActionFactor₃ ε η = 1) :
    patternSurvives₃ ε := by
  intro c₀
  rw [patternDiv₃_eq_zero_iff]
  set η : LayerSite 2 → ↥(Subgroup.center ↥SU3) :=
    Function.update (1 : LayerSite 2 → ↥(Subgroup.center ↥SU3))
      c₀ (su3CenterEquiv (Multiplicative.ofAdd 1)) with hη
  have hfac := h η
  have hsingle :
      (∏ c : LayerSite 2, (centerChar (η c)) ^ patternExp₃ ε c)
        = (zetaC3 : ℂ) ^ patternExp₃ ε c₀ := by
    rw [Finset.prod_eq_single c₀]
    · rw [hη, Function.update_self, centerChar_su3CenterEquiv,
        seatChar₃_ofAdd_one]
    · intro b _ hb
      rw [hη, Function.update_of_ne hb, Pi.one_apply,
        centerChar_one, one_pow]
    · simp
  unfold centerActionFactor₃ at hfac
  rw [hsingle] at hfac
  have hE : (zetaC3 : ℂ) ^ (patternExp₃ ε c₀ % 3) = 1 := by
    have h2 := hfac
    rw [← Nat.div_add_mod (patternExp₃ ε c₀) 3, pow_add, pow_mul']
      at h2
    have h3 : (zetaC3 ^ (patternExp₃ ε c₀ / 3)) ^ 3 = 1 := by
      rw [← pow_mul', pow_mul, zetaC3_cube, one_pow]
    rw [h3, one_mul] at h2
    exact h2
  have hmod : patternExp₃ ε c₀ % 3 = 0 ∨ patternExp₃ ε c₀ % 3 = 1
      ∨ patternExp₃ ε c₀ % 3 = 2 := by
    have := Nat.mod_lt (patternExp₃ ε c₀) (show 0 < 3 by norm_num)
    omega
  rcases hmod with hm | hm | hm
  · exact Nat.dvd_of_mod_eq_zero hm
  · rw [hm, pow_one] at hE
    exact absurd hE zetaC3_ne_one
  · rw [hm] at hE
    exact absurd hE zetaC3_sq_ne_one

/-- **C-3, the filter re-read — the center-neutrality form.**
A pattern survives the mod-3 divergence filter iff the diagonal
center action's factor is trivial at every site field: survival
*is* center-neutrality of the pattern monomial, site charge
`patternDiv₃ ε c`. -/
theorem patternSurvives₃_iff_centerActionFactor₃
    (ε : LayerColumn 2 → ZMod 3) :
    patternSurvives₃ ε ↔
      ∀ η : LayerSite 2 → ↥(Subgroup.center ↥SU3),
        centerActionFactor₃ ε η = 1 :=
  ⟨fun hε η => centerActionFactor₃_eq_one_of_survives hε η,
    fun h => patternSurvives₃_of_centerActionFactor₃ h⟩

/-- **C-3, the filter re-read — the invariance form (the scoping
§3.1 statement).**  For every pattern `ε`, `patternSurvives₃ ε`
iff the pattern monomial is invariant under the diagonal action
of `↥(Subgroup.center ↥SU3)` transported along `su3CenterEquiv`,
with site charge `patternDiv₃ ε c`.  Together with
`center_stratum_average₃` this earns the word **identity** at
exactly this level: **the mod-3 divergence filter is the
center-neutrality projector of the seat.**  The stronger word —
triality as a selection rule for SU(3) *representations* — remains
NOT STATEABLE (§3.2 fences, on this module's face).
**K-SU3-FILTER is decided by this theorem: it does NOT fire.** -/
theorem patternSurvives₃_iff_centerMono_invariant
    (ε : LayerColumn 2 → ZMod 3) :
    patternSurvives₃ ε ↔
      ∀ η γ : LayerSite 2 → ↥(Subgroup.center ↥SU3),
        centerMono₃ ε (η * γ) = centerMono₃ ε γ := by
  rw [patternSurvives₃_iff_centerActionFactor₃]
  constructor
  · intro h η γ
    rw [centerMono₃_act, h η, one_mul]
  · intro h η
    have h1 := h η (1 : LayerSite 2 → ↥(Subgroup.center ↥SU3))
    rw [mul_one] at h1
    have h2 := centerMono₃_act ε η
      (1 : LayerSite 2 → ↥(Subgroup.center ↥SU3))
    rw [mul_one, centerMono₃_one, mul_one] at h2
    rw [h2] at h1
    rw [h1, centerMono₃_one]

/-! ## C-4 — the center seat (scoping §4.1)

The ternary seat rebuilt at `G := ↥(Subgroup.center ↥SU3)`.
**Honest label: a re-dressing, not a new seat** — its entire
mathematical content is C-1 + C-2, and the transport below is
registration work: the instance package is TM-1's, the measure is
TM-1's uniform measure, the rep is the fundamental rep restricted
to the center, and the headline is TM-3's, re-registered.  Zero
new mathematics is claimed.  **K-SU3-TRANSPORT is decided by
`layerKernelPos_center_seat`: it does NOT fire.** -/

/-- The center seat topology: discrete (`⊥`). -/
instance su3CenterSeatTopologicalSpace :
    TopologicalSpace ↥(Subgroup.center ↥SU3) := ⊥

/-- The center seat σ-algebra: everything measurable (`⊤`). -/
instance su3CenterSeatMeasurableSpace :
    MeasurableSpace ↥(Subgroup.center ↥SU3) := ⊤

/-- The center seat topology is discrete. -/
instance su3CenterSeatDiscreteTopology :
    DiscreteTopology ↥(Subgroup.center ↥SU3) := ⟨rfl⟩

/-- The center seat Borel σ-algebra agrees with `⊤`. -/
instance su3CenterSeatBorelSpace :
    BorelSpace ↥(Subgroup.center ↥SU3) :=
  ⟨borel_eq_top_of_discrete.symm⟩

/-- The center seat measure: the uniform probability measure on
the three-element center group, `(3)⁻¹ • Measure.count` — TM-1's
`seatμ₃`, transported. -/
noncomputable def centerμ :
    Measure ↥(Subgroup.center ↥SU3) :=
  (3 : ℝ≥0∞)⁻¹ • Measure.count

/-- The center seat measure is a probability measure. -/
instance : IsProbabilityMeasure centerμ := by
  constructor
  have hc : Nat.card ↥(Subgroup.center ↥SU3) = 3 := by
    rw [Nat.card_eq_fintype_card]
    exact centerSU3_card
  rw [centerμ, Measure.smul_apply, smul_eq_mul, Measure.count_univ,
    ENat.card_eq_coe_natCard, hc, Nat.cast_ofNat]
  exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)

/-- The center seat measure is inversion-invariant. -/
instance : Measure.IsInvInvariant centerμ := by
  constructor
  show Measure.map Inv.inv ((3 : ℝ≥0∞)⁻¹ • Measure.count)
    = (3 : ℝ≥0∞)⁻¹ • Measure.count
  rw [Measure.map_smul _ measurable_inv.aemeasurable,
    Measure.map_inv_eq_self]

/-- The center seat measure is left-invariant. -/
instance : Measure.IsMulLeftInvariant centerμ := by
  constructor
  intro g
  show Measure.map (g * ·) ((3 : ℝ≥0∞)⁻¹ • Measure.count)
    = (3 : ℝ≥0∞)⁻¹ • Measure.count
  rw [Measure.map_smul _ (measurable_const_mul g).aemeasurable]
  congr 1
  exact MeasureTheory.Measure.IsMulLeftInvariant.map_mul_left_eq_self
    (μ := (Measure.count : Measure ↥(Subgroup.center ↥SU3))) g

/-- The center seat measure is right-invariant. -/
instance : Measure.IsMulRightInvariant centerμ := by
  constructor
  intro g
  show Measure.map (· * g) ((3 : ℝ≥0∞)⁻¹ • Measure.count)
    = (3 : ℝ≥0∞)⁻¹ • Measure.count
  rw [Measure.map_smul _ (measurable_mul_const g).aemeasurable]
  congr 1
  exact MeasureTheory.Measure.IsMulRightInvariant.map_mul_right_eq_self
    (μ := (Measure.count : Measure ↥(Subgroup.center ↥SU3))) g

/-- A singleton under the center seat measure has mass `(3)⁻¹`. -/
theorem centerμ_singleton (z : ↥(Subgroup.center ↥SU3)) :
    centerμ {z} = (3 : ℝ≥0∞)⁻¹ := by
  rw [centerμ, Measure.smul_apply, smul_eq_mul, Measure.count_singleton,
    mul_one]

/-- **The finite-seat integral at the center seat** (TM-1's
`seatIntegralPi₃`, transported): for a finite index type `ι`, the
integral over the product center measure is the sum over all
configurations scaled by the inverse configuration count. -/
theorem centerIntegralPi {ι : Type*} [Fintype ι] [DecidableEq ι]
    {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : (ι → ↥(Subgroup.center ↥SU3)) → E) :
    (∫ a, f a ∂(Measure.pi fun _ : ι => centerμ))
      = (Fintype.card (ι → ↥(Subgroup.center ↥SU3)) : ℝ)⁻¹
        • ∑ a, f a := by
  have hInt : Integrable f (Measure.pi fun _ : ι => centerμ) := by
    rw [← Measure.sum_smul_dirac (Measure.pi fun _ : ι => centerμ)]
    refine integrable_sum_dirac (fun a => measure_ne_top _ _) ?_
    exact Summable.of_finite
  rw [integral_fintype hInt, Finset.smul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  have hsing : ∀ z : ↥(Subgroup.center ↥SU3),
      centerμ {z} = (3 : ℝ≥0∞)⁻¹ := centerμ_singleton
  have hc3 : Fintype.card ↥(Subgroup.center ↥SU3) = 3 :=
    centerSU3_card
  rw [measureReal_def, Measure.pi_singleton]
  simp only [hsing]
  rw [Finset.prod_const, ← ENNReal.inv_pow, ENNReal.toReal_inv,
    Fintype.card_fun, hc3]
  simp [Finset.card_univ, ENNReal.toReal_pow]

/-- **The center seat rep**: the fundamental representation of
the bare group `SU3` restricted to its center — `centerRep z` is
the unitary matrix of the central element `z` itself.  By C-1's
weld its scalar is `seatChar₃` read through the iso: it is the
scalar action `seatChar₃ ⊗ id₃`. -/
noncomputable def centerRep :
    ↥(Subgroup.center ↥SU3) →* ↥(Matrix.unitaryGroup (Fin 3) ℂ) :=
  su3Inclusion.comp (Subgroup.subtype (Subgroup.center ↥SU3))

/-- **The character of the center seat rep** (C-1's weld, read on
the center group): `charFn centerRep z = 3 * centerChar z`.  The
`3` is dimension — the fundamental restricts to the center as
three copies of the scalar character, and the trace sees all
three.  Against `charFn_seat₃` (`charFn seatρ₃ = seatChar₃`), the
**normalized** characters of the two seats agree along the iso —
the single fact the whole transport stands on. -/
theorem charFn_centerRep (z : ↥(Subgroup.center ↥SU3)) :
    charFn centerRep z = 3 * centerChar z := by
  have hz : (z : ↥SU3)
      = centerScalarSU3 (su3CenterEquiv.symm z) :=
    (congrArg Subtype.val
      (MulEquiv.apply_symm_apply su3CenterEquiv z)).symm
  show Matrix.trace (repMatrix centerRep z) = 3 * centerChar z
  rw [show repMatrix centerRep z
      = repMatrix su3Inclusion (z : ↥SU3) from rfl, hz]
  exact charFn_centerScalarSU3 _

/-- The column word commutes with the iso: the word of the
transported data is the transport of the word (the word is built
from group operations only). -/
theorem colWord_center (u u' : LayerLink 2 → Multiplicative (ZMod 3))
    (c : LayerSite 2) (ν : Fin 4) (hν : ν ≠ 0)
    (α : LayerSite 2 → Multiplicative (ZMod 3)) :
    colWord (fun ℓ => su3CenterEquiv (u ℓ))
        (fun ℓ => su3CenterEquiv (u' ℓ)) c ν hν
        (fun s => su3CenterEquiv (α s))
      = su3CenterEquiv (colWord u u' c ν hν α) := by
  unfold colWord
  simp only [map_mul, map_inv]

/-- The column density is unchanged by transport: at either seat
the density reads the column word only through the normalized
character `charFn ρ / d` (`colDens_eq`), the iso carries the word
to the word (`colWord_center`), and the normalized characters
agree (`charFn_centerRep` against `charFn_seat₃` — the dimension
`3` cancels). -/
theorem colDensC_center (u u' : LayerLink 2 → Multiplicative (ZMod 3))
    (P : LayerColumn 2) (α : LayerSite 2 → Multiplicative (ZMod 3)) :
    colDensC centerRep (fun ℓ => su3CenterEquiv (u ℓ))
        (fun ℓ => su3CenterEquiv (u' ℓ)) P
        (fun s => su3CenterEquiv (α s))
      = colDensC seatρ₃ u u' P α := by
  unfold colDensC
  rw [colDens_eq, colDens_eq, colWord_center, charFn_centerRep,
    centerChar_su3CenterEquiv, charFn_seat₃]
  have hre : (3 * seatChar₃ (colWord u u' P.1 P.2.1 P.2.2 α)).re
      = 3 * (seatChar₃ (colWord u u' P.1 P.2.1 P.2.2 α)).re := by
    simp [Complex.mul_re]
  rw [hre, Nat.cast_ofNat, Nat.cast_one, div_one,
    mul_div_cancel_left₀ _
      (show (3 : ℝ) ≠ 0 by norm_num)]

/-- The layer action is unchanged by transport (column by
column). -/
theorem layerAction_center (β : ℝ)
    (α : LayerSite 2 → Multiplicative (ZMod 3))
    (u u' : LayerLink 2 → Multiplicative (ZMod 3)) :
    layerAction centerRep β (fun s => su3CenterEquiv (α s))
        (fun ℓ => su3CenterEquiv (u ℓ))
        (fun ℓ => su3CenterEquiv (u' ℓ))
      = layerAction seatρ₃ β α u u' := by
  rw [layerAction_eq, layerAction_eq,
    layerDensSum_eq_sum_columns centerRep (by decide),
    layerDensSum_eq_sum_columns seatρ₃ (by decide)]
  refine congrArg _ (Finset.sum_congr rfl fun P _ => ?_)
  exact colDensC_center u u' P α

/-- **The layer kernel is unchanged by transport**: at transported
configurations, the center seat's kernel *is* the ternary seat's
kernel (the stratum sums reindex along the iso;
`centerIntegralPi` against `seatIntegralPi₃`). -/
theorem layerKernel_center (β : ℝ)
    (u u' : LayerLink 2 → Multiplicative (ZMod 3)) :
    layerKernel centerμ centerRep β (fun ℓ => su3CenterEquiv (u ℓ))
        (fun ℓ => su3CenterEquiv (u' ℓ))
      = layerKernel seatμ₃ seatρ₃ β u u' := by
  have hcard :
      (Fintype.card (LayerSite 2 → ↥(Subgroup.center ↥SU3)) : ℝ)
        = (Fintype.card (LayerSite 2 → Multiplicative (ZMod 3))
            : ℝ) := by
    rw [Fintype.card_fun, Fintype.card_fun, centerSU3_card,
      ternarySeat_card]
  unfold layerKernel
  rw [centerIntegralPi, seatIntegralPi₃, hcard]
  congr 1
  rw [← Equiv.sum_comp
    (Equiv.piCongrRight fun _ : LayerSite 2 => su3CenterEquiv.toEquiv)
    (fun α' => (Real.exp
      (-(layerAction centerRep β α'
        (fun ℓ => su3CenterEquiv (u ℓ))
        (fun ℓ => su3CenterEquiv (u' ℓ)))) : ℂ))]
  refine Finset.sum_congr rfl fun α _ => ?_
  exact congrArg (fun t : ℝ => (Real.exp (-t) : ℂ))
    (layerAction_center β α u u')

/-- The layer gauge action commutes with the iso, pointwise (the
gauge value is a product of group elements and one inverse). -/
theorem layerGaugeAction_center
    (g : (Fin 4 → ZMod 2) → Multiplicative (ZMod 3))
    (u : LayerLink 2 → Multiplicative (ZMod 3)) :
    layerGaugeAction (fun x => su3CenterEquiv (g x))
        (fun ℓ => su3CenterEquiv (u ℓ))
      = fun ℓ => su3CenterEquiv (layerGaugeAction g u ℓ) := by
  funext ℓ
  show gaugeLinkVal (fun x => su3CenterEquiv (g x)) ℓ.1
      (su3CenterEquiv (u ℓ))
    = su3CenterEquiv (gaugeLinkVal g ℓ.1 (u ℓ))
  unfold gaugeLinkVal
  simp only [map_mul, map_inv]

/-- Gauge invariance transports: a gauge-invariant observable at
the center seat pulls back to a gauge-invariant observable at
the ternary seat. -/
theorem gaugeInvariant_center_comp
    {F' : (LayerLink 2 → ↥(Subgroup.center ↥SU3)) → ℂ}
    (hF' : GaugeInvariantLayerObs F') :
    GaugeInvariantLayerObs
      (fun u => F' (fun ℓ => su3CenterEquiv (u ℓ))) := by
  intro g u
  have h := hF' (fun x => su3CenterEquiv (g x))
    (fun ℓ => su3CenterEquiv (u ℓ))
  rwa [layerGaugeAction_center] at h

/-- **The positivity pairing is unchanged by transport**: the
`LayerKernelPos` pairing at the center seat, against an arbitrary
observable `F'`, equals the pairing at the ternary seat against
the pulled-back observable.  Both pairings are finite sums in
disguise (`centerIntegralPi` / `seatIntegralPi₃`); the sums
reindex along the iso and the kernels agree
(`layerKernel_center`). -/
theorem pairing_center_eq (β : ℝ)
    (F' : (LayerLink 2 → ↥(Subgroup.center ↥SU3)) → ℂ) :
    (∫ u, ∫ u', (starRingEnd ℂ) (F' u)
        * layerKernel centerμ centerRep β u u' * F' u'
        ∂(Measure.pi fun _ : LayerLink 2 => centerμ)
      ∂(Measure.pi fun _ : LayerLink 2 => centerμ))
    = ∫ u, ∫ u',
        (starRingEnd ℂ) (F' (fun ℓ => su3CenterEquiv (u ℓ)))
        * layerKernel seatμ₃ seatρ₃ β u u'
          * F' (fun ℓ => su3CenterEquiv (u' ℓ))
        ∂(Measure.pi fun _ : LayerLink 2 => seatμ₃)
      ∂(Measure.pi fun _ : LayerLink 2 => seatμ₃) := by
  have hcard :
      (Fintype.card (LayerLink 2 → ↥(Subgroup.center ↥SU3)) : ℝ)
        = (Fintype.card (LayerLink 2 → Multiplicative (ZMod 3))
            : ℝ) := by
    rw [Fintype.card_fun, Fintype.card_fun, centerSU3_card,
      ternarySeat_card]
  have hinner : ∀ u : LayerLink 2 → Multiplicative (ZMod 3),
      (∑ U' : LayerLink 2 → ↥(Subgroup.center ↥SU3),
        (starRingEnd ℂ) (F' (fun ℓ => su3CenterEquiv (u ℓ)))
          * layerKernel centerμ centerRep β
              (fun ℓ => su3CenterEquiv (u ℓ)) U' * F' U')
      = ∑ u' : LayerLink 2 → Multiplicative (ZMod 3),
        (starRingEnd ℂ) (F' (fun ℓ => su3CenterEquiv (u ℓ)))
          * layerKernel seatμ₃ seatρ₃ β u u'
            * F' (fun ℓ => su3CenterEquiv (u' ℓ)) := by
    intro u
    rw [← Equiv.sum_comp
      (Equiv.piCongrRight fun _ : LayerLink 2 =>
        su3CenterEquiv.toEquiv)
      (fun U' => (starRingEnd ℂ)
          (F' (fun ℓ => su3CenterEquiv (u ℓ)))
        * layerKernel centerμ centerRep β
            (fun ℓ => su3CenterEquiv (u ℓ)) U' * F' U')]
    refine Finset.sum_congr rfl fun u' _ => ?_
    exact congrArg
      (fun k : ℂ =>
        (starRingEnd ℂ) (F' (fun ℓ => su3CenterEquiv (u ℓ)))
          * k * F' (fun ℓ => su3CenterEquiv (u' ℓ)))
      (layerKernel_center β u u')
  have hsum :
      (∑ U : LayerLink 2 → ↥(Subgroup.center ↥SU3),
        (Fintype.card (LayerLink 2 → ↥(Subgroup.center ↥SU3))
            : ℝ)⁻¹
          • ∑ U', (starRingEnd ℂ) (F' U)
              * layerKernel centerμ centerRep β U U' * F' U')
      = ∑ u : LayerLink 2 → Multiplicative (ZMod 3),
        (Fintype.card (LayerLink 2 → ↥(Subgroup.center ↥SU3))
            : ℝ)⁻¹
          • ∑ u',
            (starRingEnd ℂ) (F' (fun ℓ => su3CenterEquiv (u ℓ)))
              * layerKernel seatμ₃ seatρ₃ β u u'
                * F' (fun ℓ => su3CenterEquiv (u' ℓ)) := by
    rw [← Equiv.sum_comp
      (Equiv.piCongrRight fun _ : LayerLink 2 =>
        su3CenterEquiv.toEquiv)
      (fun U =>
        (Fintype.card (LayerLink 2 → ↥(Subgroup.center ↥SU3))
            : ℝ)⁻¹
          • ∑ U', (starRingEnd ℂ) (F' U)
              * layerKernel centerμ centerRep β U U' * F' U')]
    refine Finset.sum_congr rfl fun u _ => ?_
    exact congrArg
      (fun t : ℂ =>
        (Fintype.card (LayerLink 2 → ↥(Subgroup.center ↥SU3))
            : ℝ)⁻¹ • t)
      (hinner u)
  calc (∫ u, ∫ u', (starRingEnd ℂ) (F' u)
          * layerKernel centerμ centerRep β u u' * F' u'
          ∂(Measure.pi fun _ : LayerLink 2 => centerμ)
        ∂(Measure.pi fun _ : LayerLink 2 => centerμ))
      = (Fintype.card (LayerLink 2 → ↥(Subgroup.center ↥SU3))
            : ℝ)⁻¹
          • ∑ U,
            (Fintype.card (LayerLink 2 → ↥(Subgroup.center ↥SU3))
                : ℝ)⁻¹
              • ∑ U', (starRingEnd ℂ) (F' U)
                  * layerKernel centerμ centerRep β U U'
                    * F' U' := by
        rw [centerIntegralPi]
        refine congrArg _ (Finset.sum_congr rfl fun U _ => ?_)
        exact centerIntegralPi _
    _ = (Fintype.card (LayerLink 2 → ↥(Subgroup.center ↥SU3))
            : ℝ)⁻¹
          • ∑ u,
            (Fintype.card (LayerLink 2 → ↥(Subgroup.center ↥SU3))
                : ℝ)⁻¹
              • ∑ u',
                (starRingEnd ℂ)
                    (F' (fun ℓ => su3CenterEquiv (u ℓ)))
                  * layerKernel seatμ₃ seatρ₃ β u u'
                    * F' (fun ℓ => su3CenterEquiv (u' ℓ)) :=
        congrArg _ hsum
    _ = ∫ u, ∫ u',
          (starRingEnd ℂ) (F' (fun ℓ => su3CenterEquiv (u ℓ)))
          * layerKernel seatμ₃ seatρ₃ β u u'
            * F' (fun ℓ => su3CenterEquiv (u' ℓ))
          ∂(Measure.pi fun _ : LayerLink 2 => seatμ₃)
        ∂(Measure.pi fun _ : LayerLink 2 => seatμ₃) := by
        rw [hcard]
        symm
        rw [seatIntegralPi₃]
        refine congrArg _ (Finset.sum_congr rfl fun u _ => ?_)
        exact seatIntegralPi₃ _

/-- **C-4 headline — TM-3 re-registered at the center of SU(3).**
`LayerKernelPos` at the center seat
`(↥(Subgroup.center ↥SU3), centerμ, centerRep)` for all `β ≥ 0`:
`layerKernelPos_ternary_seat` transported along `su3CenterEquiv`.
The corpus owns, as a theorem, the statement
"`layerKernelPos_ternary_seat` is `LayerKernelPos` at the center
of SU(3) with the restricted fundamental rep" — the two wings
joined by name instead of by resemblance (scoping §4.1).  A
re-dressing: the mathematical content is C-1 + C-2 + TM-3, and no
new mathematics is claimed.  **K-SU3-TRANSPORT does NOT fire:**
every hypothesis of the TM chain's headline is iso-stable, and
the transport is proved above (`layerKernel_center`,
`pairing_center_eq`). -/
theorem layerKernelPos_center_seat {β : ℝ} (hβ : 0 ≤ β) :
    LayerKernelPos (N := 2) centerμ centerRep β := by
  intro F' hF'
  rw [pairing_center_eq]
  exact layerKernelPos_ternary_seat hβ _
    (gaugeInvariant_center_comp hF')

end ThetLogos
