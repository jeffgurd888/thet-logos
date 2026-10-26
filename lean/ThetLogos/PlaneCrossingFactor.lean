import ThetLogos.PlaneAvgKernel
import ThetLogos.PlaneCrossingSymm

/-!
# ThetLogos.PlaneCrossingFactor — Brick β1: the crossing marginal factors by base layer

The crossing class `IsZeroPlaq` has exactly **two** base layers at
every even `N` (the arithmetic inside
`refPlaq_eq_of_isZeroPlaq`): temporal plaquettes based at time
`N / 2 - 1` (the **top** class, touching the positive half's plane
stratum `a`) and at time `N - 1` (the **bottom** class, touching
the negative half's plane stratum `a'`). This module proves the
factorization the β-scoping registered:

- `S₀ = S₀^top + S₀^bot` on **every** configuration
  (`wilsonActionZero_split`);
- the top action of an assembly `planeAssemble hN z z' a a'` does
  not depend on `a'`, and the bottom action does not depend on
  `a` (the four link-value formulas per class: a top plaquette
  reads `a · z' · a⁻¹ · z⁻¹` over its four links — the mirrored
  edge is the link `(x, ν)` itself, read in `z'`, because
  `reflSite (σ₀ x) = x` at the top layer; a bottom plaquette
  reads `a' · z · a'⁻¹ · z'⁻¹` over the layer-`0` links);
- hence the crossing marginal is a plain product of two
  one-stratum kernels,
  `planeCrossingMarginal = planeCrossingTop * planeCrossingBot`
  (`planeCrossingMarginal_factor_top_bot`), the corpus form of
  the seat's `M = A₁ · A₂`;
- each factor depends on its half-configurations only through
  one boundary layer: `planeCrossingTop` through the spatial
  links at time `N / 2 - 1` (the memo's `τ⁺`),
  `planeCrossingBot` through the spatial links at time `0`
  (`τ₀`) — the extractions, as factoring statements.

**Not in this module:** the identification of the two factors
as *one* kernel `𝒜` on abstract layer data — the scoping's
`A₂(z,z′) = 𝒜(τ₀z′, τ₀z)` against `A₁(z,z′) = 𝒜(τ⁺z, τ⁺z′)` —
and with it the per-stratum symmetry `𝒜(u,u′) = 𝒜(u′,u)`. The
plaquette words that force the swapped orientation are proved
here (the link formulas: the bottom word is the top word with
the two layer readings exchanged); what remains is a cube
parametrization of the layers with Haar/pi transport, a
separate brick (β1-remainder).

**No positivity is asserted anywhere in this module.** The
single-layer kernel's positivity (`𝒜 ⪰ 0`) is Brick β2,
L+ / open, untouched here. NO CLAIM: this module closes **0**
parts of the Clay Yang–Mills statement.
-/

namespace ThetLogos

open MeasureTheory Finset
open scoped Matrix ENNReal NNReal

section Split

variable {G : Type*} [Group G] {d : ℕ}
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ)) {N : ℕ} [NeZero N]

/-- The **top crossing class**: plaquette indices based at time
`N / 2 - 1`. -/
abbrev IsTopPlaq (p : (Fin 4 → ZMod N) × Fin 4 × Fin 4) : Prop :=
  (p.1 0).val = N / 2 - 1

/-- The **bottom crossing class**: plaquette indices based at
time `N - 1`. -/
abbrev IsBotPlaq (p : (Fin 4 → ZMod N) × Fin 4 × Fin 4) : Prop :=
  (p.1 0).val = N - 1

/-- **The crossing class, characterized** (the arithmetic inside
`refPlaq_eq_of_isZeroPlaq`, extracted): a crossing index is
temporal, based at `N / 2 - 1` or at `N - 1`. -/
theorem isZeroPlaq_dir_base (hN : Even N)
    (p : (Fin 4 → ZMod N) × Fin 4 × Fin 4) (hp : IsZeroPlaq p) :
    p.2.1 = 0 ∧ ((p.1 0).val = N / 2 - 1 ∨ (p.1 0).val = N - 1) := by
  obtain ⟨x, μ, ν⟩ := p
  have h2M : 2 * (N / 2) = N := by
    rw [mul_comm]
    exact Nat.div_mul_cancel (even_iff_two_dvd.mp hN)
  have hN2 : 2 ≤ N := by
    have hne : N ≠ 0 := NeZero.ne N
    omega
  have hμ : μ = 0 := by
    by_contra hμ
    by_cases hv : (x 0).val < N / 2
    · apply hp.1
      show plaqTimeHi x μ < N / 2
      rw [plaqTimeHi_of_ne (N := N) _ hμ]
      exact hv
    · apply hp.2
      refine ⟨not_lt.mp hv, ?_⟩
      show plaqTimeHi x μ < N
      rw [plaqTimeHi_of_ne (N := N) _ hμ]
      exact (x 0).val_lt
  subst hμ
  refine ⟨rfl, ?_⟩
  show (x 0).val = N / 2 - 1 ∨ (x 0).val = N - 1
  have hnp : ¬ ((x 0).val + 1 < N / 2) := hp.1
  have hnn : ¬ (N / 2 ≤ (x 0).val ∧ (x 0).val + 1 < N) := hp.2
  have hlt := (x 0).val_lt
  omega

/-- The top crossing action `S₀^top`: the crossing action
restricted to the base layer `N / 2 - 1`. -/
noncomputable def wilsonActionZeroTop (β : ℝ)
    (U : Config (Fin 4 → ZMod N) G) : ℝ :=
  β * ∑ p ∈ plaqIndex.filter (fun p => IsZeroPlaq p ∧ IsTopPlaq p),
    plaquetteDensity (torusShift N) ρ U p.1 p.2.1 p.2.2

/-- The bottom crossing action `S₀^bot`: the crossing action
restricted to the base layer `N - 1`. -/
noncomputable def wilsonActionZeroBot (β : ℝ)
    (U : Config (Fin 4 → ZMod N) G) : ℝ :=
  β * ∑ p ∈ plaqIndex.filter (fun p => IsZeroPlaq p ∧ IsBotPlaq p),
    plaquetteDensity (torusShift N) ρ U p.1 p.2.1 p.2.2

/-- **The base-layer split of the crossing action**: on every
configuration, `S₀ = S₀^top + S₀^bot`. The crossing class has
exactly the two base layers, at every even `N`. -/
theorem wilsonActionZero_split (hN : Even N) (β : ℝ)
    (U : Config (Fin 4 → ZMod N) G) :
    wilsonActionZero ρ β U
      = wilsonActionZeroTop ρ β U + wilsonActionZeroBot ρ β U := by
  have h2M : 2 * (N / 2) = N := by
    rw [mul_comm]
    exact Nat.div_mul_cancel (even_iff_two_dvd.mp hN)
  have hN2 : 2 ≤ N := by
    have hne : N ≠ 0 := NeZero.ne N
    omega
  have hpart : (plaqIndex (N := N)).filter IsZeroPlaq
      = ((plaqIndex (N := N)).filter (fun p => IsZeroPlaq p ∧ IsTopPlaq p))
        ∪ ((plaqIndex (N := N)).filter (fun p => IsZeroPlaq p ∧ IsBotPlaq p)) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨hpI, hpZ⟩
      rcases (isZeroPlaq_dir_base hN p hpZ).2 with h | h
      · exact Or.inl ⟨hpI, hpZ, h⟩
      · exact Or.inr ⟨hpI, hpZ, h⟩
    · rintro (⟨hpI, hpZ, -⟩ | ⟨hpI, hpZ, -⟩)
      exacts [⟨hpI, hpZ⟩, ⟨hpI, hpZ⟩]
  have hdisj : Disjoint
      ((plaqIndex (N := N)).filter (fun p => IsZeroPlaq p ∧ IsTopPlaq p))
      ((plaqIndex (N := N)).filter (fun p => IsZeroPlaq p ∧ IsBotPlaq p)) := by
    rw [Finset.disjoint_filter]
    intro p _ hp1 hp2
    have h1 : (p.1 0).val = N / 2 - 1 := hp1.2
    have h2 : (p.1 0).val = N - 1 := hp2.2
    omega
  unfold wilsonActionZero wilsonActionZeroTop wilsonActionZeroBot
  rw [hpart, Finset.sum_union hdisj]
  ring

end Split

section Factor

variable {G : Type*} [Group G] {d : ℕ}
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ)) {N : ℕ} [NeZero N]

/-- At the **top layer** (base time `N / 2 - 1`), mirroring the
time-shifted site returns the site itself: the mirrored edge of
a top plaquette is its own spatial link, read in the other
half-configuration. -/
theorem reflSite_torusShift_zero_eq (hN : Even N) {x : Fin 4 → ZMod N}
    (hx : (x 0).val = N / 2 - 1) : reflSite (torusShift N 0 x) = x := by
  have h2x : 2 * x 0 = -2 := two_mul_timeCoord_eq hN x (Or.inl hx)
  funext j
  by_cases hj : j = 0
  · subst hj
    rw [reflSite_apply_self, torusShift_apply_coord, Pi.single_eq_same]
    linear_combination -h2x
  · rw [reflSite_apply_of_ne _ hj, torusShift_apply_coord,
      Pi.single_eq_of_ne hj, zero_add]

/-- At the **bottom layer** (base time `N - 1`), the mirrored
site is the time-shifted site: the two layer-`0` readings of a
bottom plaquette sit on one and the same link. -/
theorem reflSite_eq_torusShift_zero (hN : Even N) {x : Fin 4 → ZMod N}
    (hx : (x 0).val = N - 1) : reflSite x = torusShift N 0 x := by
  have h2x : 2 * x 0 = -2 := two_mul_timeCoord_eq hN x (Or.inr hx)
  funext j
  by_cases hj : j = 0
  · subst hj
    rw [reflSite_apply_self, torusShift_apply_coord, Pi.single_eq_same]
    linear_combination -h2x
  · rw [reflSite_apply_of_ne _ hj, torusShift_apply_coord,
      Pi.single_eq_of_ne hj, zero_add]

/-- The time coordinate one step above the top layer is `N / 2`. -/
theorem torusShift_zero_val_top (hN : Even N) {x : Fin 4 → ZMod N}
    (hx : (x 0).val = N / 2 - 1) : (torusShift N 0 x 0).val = N / 2 := by
  have h2M : 2 * (N / 2) = N := by
    rw [mul_comm]
    exact Nat.div_mul_cancel (even_iff_two_dvd.mp hN)
  have hN2 : 2 ≤ N := two_le_of_even hN
  have hx0 : x 0 = ((N / 2 - 1 : ℕ) : ZMod N) := by
    rw [← ZMod.natCast_zmod_val (x 0), hx]
  rw [torusShift_apply_coord, Pi.single_eq_same, hx0,
    ← Nat.cast_one, ← Nat.cast_add]
  have hsum : (1 : ℕ) + (N / 2 - 1) = N / 2 := by omega
  rw [hsum]
  exact ZMod.val_natCast_of_lt (by omega)

/-- The time coordinate one step above the bottom layer wraps
to `0`. -/
theorem torusShift_zero_val_bot {x : Fin 4 → ZMod N}
    (hx : (x 0).val = N - 1) : (torusShift N 0 x 0).val = 0 := by
  have hx0 : x 0 = ((N - 1 : ℕ) : ZMod N) := by
    rw [← ZMod.natCast_zmod_val (x 0), hx]
  rw [torusShift_apply_coord, Pi.single_eq_same, hx0, natCast_pred_eq_neg_one]
  simp

/-- A spatial link at the top layer is a positive link. -/
theorem mem_posLinks_top (hN : Even N) {x : Fin 4 → ZMod N}
    (hx : (x 0).val = N / 2 - 1) {ν : Fin 4} (hν : ν ≠ 0) :
    (x, ν) ∈ posLinks := by
  have hN2 : 2 ≤ N := two_le_of_even hN
  rw [mem_posLinks]
  refine ⟨by show (x 0).val < N / 2; omega, ?_⟩
  rw [reflLink_of_ne hν]
  intro h
  exact (reflSite_ne_self hN x) (congrArg Prod.fst h)

/-- A time link at the top layer is a positive-half plane link. -/
theorem mem_planeHalfLinks_top (hN : Even N) {x : Fin 4 → ZMod N}
    (hx : (x 0).val = N / 2 - 1) : (x, 0) ∈ planeHalfLinks := by
  have hN2 : 2 ≤ N := two_le_of_even hN
  rw [mem_planeHalfLinks]
  refine ⟨(reflLink_eq_self_iff hN x 0).mpr ⟨rfl, Or.inl hx⟩,
    by show (x 0).val < N / 2; omega⟩

/-- A spatially shifted time link at the top layer is a
positive-half plane link. -/
theorem mem_planeHalfLinks_top_shift (hN : Even N) {x : Fin 4 → ZMod N}
    (hx : (x 0).val = N / 2 - 1) {ν : Fin 4} (hν : ν ≠ 0) :
    (torusShift N ν x, 0) ∈ planeHalfLinks := by
  have hN2 : 2 ≤ N := two_le_of_even hN
  have hval : ((torusShift N ν x) 0).val = N / 2 - 1 := by
    rw [torusShift_apply_zero_of_ne hν]; exact hx
  rw [mem_planeHalfLinks]
  refine ⟨(reflLink_eq_self_iff hN (torusShift N ν x) 0).mpr ⟨rfl, Or.inl hval⟩,
    by show ((torusShift N ν x) 0).val < N / 2; omega⟩

/-- The time-shifted spatial link of a top plaquette lies in the
negative half. -/
theorem mem_negLinks_top_shift (hN : Even N) {x : Fin 4 → ZMod N}
    (hx : (x 0).val = N / 2 - 1) {ν : Fin 4} :
    (torusShift N 0 x, ν) ∈ negLinks := by
  rw [mem_negLinks]
  exact le_of_eq (torusShift_zero_val_top hN hx).symm

/-- The time-shifted spatial link of a top plaquette is not a
plane link (the reflection has no fixed sites). -/
theorem not_mem_planeLinks_top_shift (hN : Even N) {x : Fin 4 → ZMod N}
    {ν : Fin 4} (hν : ν ≠ 0) : (torusShift N 0 x, ν) ∉ planeLinks := by
  rw [mem_planeLinks, reflLink_of_ne hν]
  intro h
  exact (reflSite_ne_self hN (torusShift N 0 x)) (congrArg Prod.fst h)

/-- A time link at the bottom layer is a negative-half plane
link. -/
theorem mem_planeNegLinks_bot (hN : Even N) {x : Fin 4 → ZMod N}
    (hx : (x 0).val = N - 1) : (x, 0) ∈ planeNegLinks := by
  have hN2 : 2 ≤ N := two_le_of_even hN
  rw [mem_planeNegLinks]
  refine ⟨(reflLink_eq_self_iff hN x 0).mpr ⟨rfl, Or.inr hx⟩,
    by show N / 2 ≤ (x 0).val; omega⟩

/-- A spatially shifted time link at the bottom layer is a
negative-half plane link. -/
theorem mem_planeNegLinks_bot_shift (hN : Even N) {x : Fin 4 → ZMod N}
    (hx : (x 0).val = N - 1) {ν : Fin 4} (hν : ν ≠ 0) :
    (torusShift N ν x, 0) ∈ planeNegLinks := by
  have hN2 : 2 ≤ N := two_le_of_even hN
  have hval : ((torusShift N ν x) 0).val = N - 1 := by
    rw [torusShift_apply_zero_of_ne hν]; exact hx
  rw [mem_planeNegLinks]
  refine ⟨(reflLink_eq_self_iff hN (torusShift N ν x) 0).mpr ⟨rfl, Or.inr hval⟩,
    by show N / 2 ≤ ((torusShift N ν x) 0).val; omega⟩

/-- The time-shifted spatial link of a bottom plaquette (based
at time `0` after the wrap) is a positive link. -/
theorem mem_posLinks_bot_shift (hN : Even N) {x : Fin 4 → ZMod N}
    (hx : (x 0).val = N - 1) {ν : Fin 4} (hν : ν ≠ 0) :
    (torusShift N 0 x, ν) ∈ posLinks := by
  have hN2 : 2 ≤ N := two_le_of_even hN
  rw [mem_posLinks]
  refine ⟨by
    show (torusShift N 0 x 0).val < N / 2
    rw [torusShift_zero_val_bot hx]; omega, ?_⟩
  rw [reflLink_of_ne hν]
  intro h
  exact (reflSite_ne_self hN (torusShift N 0 x)) (congrArg Prod.fst h)

/-- A spatial link at the bottom layer lies in the negative
half. -/
theorem mem_negLinks_bot (hN : Even N) {x : Fin 4 → ZMod N}
    (hx : (x 0).val = N - 1) {ν : Fin 4} : (x, ν) ∈ negLinks := by
  have hN2 : 2 ≤ N := two_le_of_even hN
  rw [mem_negLinks]; show N / 2 ≤ (x 0).val; omega

/-- A spatial link is never a plane link (the reflection has no
fixed sites). -/
theorem not_mem_planeLinks_spatial (hN : Even N) {x : Fin 4 → ZMod N}
    {ν : Fin 4} (hν : ν ≠ 0) : (x, ν) ∉ planeLinks := by
  rw [mem_planeLinks, reflLink_of_ne hν]
  intro h
  exact (reflSite_ne_self hN x) (congrArg Prod.fst h)

/-- `joinHalf` on a positive link reads the strict configuration. -/
theorem joinHalf_apply_pos {ℓ : ↥(halfLinks (N := N))}
    (h : ℓ.1 ∈ posLinks) (z : ↥(posLinks (N := N)) → G)
    (a : ↥(planeHalfLinks (N := N)) → G) :
    joinHalf z a ℓ = z ⟨ℓ.1, h⟩ := dite_eq_left h

/-- `joinHalf` on a non-positive half link reads the plane
stratum. -/
theorem joinHalf_apply_not_pos {ℓ : ↥(halfLinks (N := N))}
    (h : ℓ.1 ∉ posLinks) (z : ↥(posLinks (N := N)) → G)
    (a : ↥(planeHalfLinks (N := N)) → G) :
    joinHalf z a ℓ
      = a ⟨ℓ.1, halfLinks_mem_planeHalf_of_not_pos ℓ.2 h⟩ :=
  dite_eq_right h

end Factor

section Values

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ)) {N : ℕ} [NeZero N]

/-- **Top plaquette, base time edge**: the assembly at `(x, 0)`
reads the positive plane stratum `a` — no `a'`, no `z`, no `z'`. -/
theorem planeAssemble_top_time (hN : Even N) {x : Fin 4 → ZMod N}
    (hx : (x 0).val = N / 2 - 1)
    (z z' : ↥(posLinks (N := N)) → G)
    (a : ↥(planeHalfLinks (N := N)) → G)
    (a' : ↥(planeNegLinks (N := N)) → G) :
    planeAssemble hN z z' a a' (x, 0)
      = a ⟨(x, 0), mem_planeHalfLinks_top hN hx⟩ := by
  have hmem := mem_planeHalfLinks_top hN hx
  have hhalf : (x, 0) ∈ halfLinks := planeHalfLinks_subset_halfLinks hmem
  have hnot : (x, 0) ∉ posLinks := fun h =>
    (mem_posLinks.mp h).2 (mem_planeHalfLinks.mp hmem).1
  rw [planeAssemble, splitSymm_apply_mem _ _ hhalf, joinHalf_apply_not_pos hnot]

/-- **Top plaquette, spatial edge**: the assembly at `(x, ν)`
reads the strict configuration `z` at the same link. -/
theorem planeAssemble_top_spatial (hN : Even N) {x : Fin 4 → ZMod N}
    (hx : (x 0).val = N / 2 - 1) {ν : Fin 4} (hν : ν ≠ 0)
    (z z' : ↥(posLinks (N := N)) → G)
    (a : ↥(planeHalfLinks (N := N)) → G)
    (a' : ↥(planeNegLinks (N := N)) → G) :
    planeAssemble hN z z' a a' (x, ν)
      = z ⟨(x, ν), mem_posLinks_top hN hx hν⟩ := by
  have hpos := mem_posLinks_top hN hx hν
  have hhalf : (x, ν) ∈ halfLinks := posLinks_subset_halfLinks hpos
  rw [planeAssemble, splitSymm_apply_mem _ _ hhalf, joinHalf_apply_pos hpos]

/-- **Top plaquette, mirrored edge**: the assembly at
`(σ₀x, ν)` reads the mirrored strict configuration `z'` at the
link `(x, ν)` itself — the mirror of the shifted site is the
base site (`reflSite_torusShift_zero_eq`). -/
theorem planeAssemble_top_shift (hN : Even N) {x : Fin 4 → ZMod N}
    (hx : (x 0).val = N / 2 - 1) {ν : Fin 4} (hν : ν ≠ 0)
    (z z' : ↥(posLinks (N := N)) → G)
    (a : ↥(planeHalfLinks (N := N)) → G)
    (a' : ↥(planeNegLinks (N := N)) → G) :
    planeAssemble hN z z' a a' (torusShift N 0 x, ν)
      = z' ⟨(x, ν), mem_posLinks_top hN hx hν⟩ := by
  have hneg := mem_negLinks_top_shift hN hx (ν := ν)
  have hnotp := not_mem_planeLinks_top_shift hN hν (x := x)
  have hcomp : (torusShift N 0 x, ν) ∈ (halfLinks (N := N))ᶜ := hneg
  have hdir : (reflLink (torusShift N 0 x, ν)).2 ≠ 0 := by
    rw [reflLink_snd]; exact hν
  have hlink : reflLink (torusShift N 0 x, ν) = (x, ν) := by
    rw [reflLink_of_ne hν, reflSite_torusShift_zero_eq hN hx]
  rw [planeAssemble, splitSymm_apply_not_mem _ _ hcomp,
    joinNeg_apply_not_plane hN z' a' hnotp, if_neg hdir]
  congr 1
  exact Subtype.ext hlink

/-- **Top plaquette, shifted time edge**: the assembly at
`(σ_ν x, 0)` reads the positive plane stratum `a`. -/
theorem planeAssemble_top_time_shift (hN : Even N) {x : Fin 4 → ZMod N}
    (hx : (x 0).val = N / 2 - 1) {ν : Fin 4} (hν : ν ≠ 0)
    (z z' : ↥(posLinks (N := N)) → G)
    (a : ↥(planeHalfLinks (N := N)) → G)
    (a' : ↥(planeNegLinks (N := N)) → G) :
    planeAssemble hN z z' a a' (torusShift N ν x, 0)
      = a ⟨(torusShift N ν x, 0), mem_planeHalfLinks_top_shift hN hx hν⟩ := by
  have hmem := mem_planeHalfLinks_top_shift hN hx hν
  have hhalf : (torusShift N ν x, 0) ∈ halfLinks :=
    planeHalfLinks_subset_halfLinks hmem
  have hnot : (torusShift N ν x, 0) ∉ posLinks := fun h =>
    (mem_posLinks.mp h).2 (mem_planeHalfLinks.mp hmem).1
  rw [planeAssemble, splitSymm_apply_mem _ _ hhalf, joinHalf_apply_not_pos hnot]

/-- **Bottom plaquette, base time edge**: the assembly at
`(x, 0)` reads the negative plane stratum `a'`. -/
theorem planeAssemble_bot_time (hN : Even N) {x : Fin 4 → ZMod N}
    (hx : (x 0).val = N - 1)
    (z z' : ↥(posLinks (N := N)) → G)
    (a : ↥(planeHalfLinks (N := N)) → G)
    (a' : ↥(planeNegLinks (N := N)) → G) :
    planeAssemble hN z z' a a' (x, 0)
      = a' ⟨(x, 0), mem_planeNegLinks_bot hN hx⟩ := by
  have hmem := mem_planeNegLinks_bot hN hx
  have hneg : (x, 0) ∈ negLinks := planeNegLinks_subset_negLinks hmem
  have hcomp : (x, 0) ∈ (halfLinks (N := N))ᶜ := hneg
  have hplane : (x, 0) ∈ planeLinks :=
    mem_planeLinks.mpr (mem_planeNegLinks.mp hmem).1
  rw [planeAssemble, splitSymm_apply_not_mem _ _ hcomp,
    joinNeg_apply_plane hN z' a' hplane]

/-- **Bottom plaquette, mirrored edge**: the assembly at
`(σ₀x, ν)` (time `0` after the wrap) reads the strict
configuration `z` at that same link. -/
theorem planeAssemble_bot_shift (hN : Even N) {x : Fin 4 → ZMod N}
    (hx : (x 0).val = N - 1) {ν : Fin 4} (hν : ν ≠ 0)
    (z z' : ↥(posLinks (N := N)) → G)
    (a : ↥(planeHalfLinks (N := N)) → G)
    (a' : ↥(planeNegLinks (N := N)) → G) :
    planeAssemble hN z z' a a' (torusShift N 0 x, ν)
      = z ⟨(torusShift N 0 x, ν), mem_posLinks_bot_shift hN hx hν⟩ := by
  have hpos := mem_posLinks_bot_shift hN hx hν
  have hhalf : (torusShift N 0 x, ν) ∈ halfLinks :=
    posLinks_subset_halfLinks hpos
  rw [planeAssemble, splitSymm_apply_mem _ _ hhalf, joinHalf_apply_pos hpos]

/-- **Bottom plaquette, shifted time edge**: the assembly at
`(σ_ν x, 0)` reads the negative plane stratum `a'`. -/
theorem planeAssemble_bot_time_shift (hN : Even N) {x : Fin 4 → ZMod N}
    (hx : (x 0).val = N - 1) {ν : Fin 4} (hν : ν ≠ 0)
    (z z' : ↥(posLinks (N := N)) → G)
    (a : ↥(planeHalfLinks (N := N)) → G)
    (a' : ↥(planeNegLinks (N := N)) → G) :
    planeAssemble hN z z' a a' (torusShift N ν x, 0)
      = a' ⟨(torusShift N ν x, 0), mem_planeNegLinks_bot_shift hN hx hν⟩ := by
  have hmem := mem_planeNegLinks_bot_shift hN hx hν
  have hneg : (torusShift N ν x, 0) ∈ negLinks :=
    planeNegLinks_subset_negLinks hmem
  have hcomp : (torusShift N ν x, 0) ∈ (halfLinks (N := N))ᶜ := hneg
  have hplane : (torusShift N ν x, 0) ∈ planeLinks :=
    mem_planeLinks.mpr (mem_planeNegLinks.mp hmem).1
  rw [planeAssemble, splitSymm_apply_not_mem _ _ hcomp,
    joinNeg_apply_plane hN z' a' hplane]

/-- **Bottom plaquette, spatial edge**: the assembly at `(x, ν)`
reads the mirrored strict configuration `z'` at the layer-`0`
link `(σ₀x, ν)` — the plaquette word's swapped orientation,
through `reflSite_eq_torusShift_zero`. -/
theorem planeAssemble_bot_spatial (hN : Even N) {x : Fin 4 → ZMod N}
    (hx : (x 0).val = N - 1) {ν : Fin 4} (hν : ν ≠ 0)
    (z z' : ↥(posLinks (N := N)) → G)
    (a : ↥(planeHalfLinks (N := N)) → G)
    (a' : ↥(planeNegLinks (N := N)) → G) :
    planeAssemble hN z z' a a' (x, ν)
      = z' ⟨(torusShift N 0 x, ν), mem_posLinks_bot_shift hN hx hν⟩ := by
  have hneg := mem_negLinks_bot hN hx (ν := ν)
  have hnotp := not_mem_planeLinks_spatial hN hν (x := x)
  have hcomp : (x, ν) ∈ (halfLinks (N := N))ᶜ := hneg
  have hdir : (reflLink (x, ν)).2 ≠ 0 := by
    rw [reflLink_snd]; exact hν
  have hlink : reflLink (x, ν) = (torusShift N 0 x, ν) := by
    rw [reflLink_of_ne hν, reflSite_eq_torusShift_zero hN hx]
  rw [planeAssemble, splitSymm_apply_not_mem _ _ hcomp,
    joinNeg_apply_not_plane hN z' a' hnotp, if_neg hdir]
  congr 1
  exact Subtype.ext hlink

/-- **Top density**: at a top plaquette the density of an
assembly does not see the negative plane stratum `a'` at all —
it reads `a(x,0) · z'(x,ν) · (a(σ_ν x, 0))⁻¹ · (z(x,ν))⁻¹`. -/
theorem plaquetteDensity_top (hN : Even N) {x : Fin 4 → ZMod N}
    {ν : Fin 4} (hx : (x 0).val = N / 2 - 1) (hν : ν ≠ 0)
    (z z' : ↥(posLinks (N := N)) → G)
    (a : ↥(planeHalfLinks (N := N)) → G)
    (a₁' a₂' : ↥(planeNegLinks (N := N)) → G) :
    plaquetteDensity (torusShift N) ρ (planeAssemble hN z z' a a₁') x 0 ν
      = plaquetteDensity (torusShift N) ρ (planeAssemble hN z z' a a₂')
        x 0 ν := by
  have hplaq : plaquette (torusShift N) (planeAssemble hN z z' a a₁') x 0 ν
      = plaquette (torusShift N) (planeAssemble hN z z' a a₂') x 0 ν := by
    unfold plaquette
    rw [planeAssemble_top_time hN hx z z' a a₁',
      planeAssemble_top_time hN hx z z' a a₂',
      planeAssemble_top_shift hN hx hν z z' a a₁',
      planeAssemble_top_shift hN hx hν z z' a a₂',
      planeAssemble_top_time_shift hN hx hν z z' a a₁',
      planeAssemble_top_time_shift hN hx hν z z' a a₂',
      planeAssemble_top_spatial hN hx hν z z' a a₁',
      planeAssemble_top_spatial hN hx hν z z' a a₂']
  unfold plaquetteDensity
  rw [hplaq]

/-- **Bottom density**: at a bottom plaquette the density of an
assembly does not see the positive plane stratum `a` at all —
it reads `a'(x,0) · z(σ₀x,ν) · (a'(σ_ν x, 0))⁻¹ · (z'(σ₀x,ν))⁻¹`
over the layer-`0` links. -/
theorem plaquetteDensity_bot (hN : Even N) {x : Fin 4 → ZMod N}
    {ν : Fin 4} (hx : (x 0).val = N - 1) (hν : ν ≠ 0)
    (z z' : ↥(posLinks (N := N)) → G)
    (a₁ a₂ : ↥(planeHalfLinks (N := N)) → G)
    (a' : ↥(planeNegLinks (N := N)) → G) :
    plaquetteDensity (torusShift N) ρ (planeAssemble hN z z' a₁ a') x 0 ν
      = plaquetteDensity (torusShift N) ρ (planeAssemble hN z z' a₂ a')
        x 0 ν := by
  have hplaq : plaquette (torusShift N) (planeAssemble hN z z' a₁ a') x 0 ν
      = plaquette (torusShift N) (planeAssemble hN z z' a₂ a') x 0 ν := by
    unfold plaquette
    rw [planeAssemble_bot_time hN hx z z' a₁ a',
      planeAssemble_bot_time hN hx z z' a₂ a',
      planeAssemble_bot_shift hN hx hν z z' a₁ a',
      planeAssemble_bot_shift hN hx hν z z' a₂ a',
      planeAssemble_bot_time_shift hN hx hν z z' a₁ a',
      planeAssemble_bot_time_shift hN hx hν z z' a₂ a',
      planeAssemble_bot_spatial hN hx hν z z' a₁ a',
      planeAssemble_bot_spatial hN hx hν z z' a₂ a']
  unfold plaquetteDensity
  rw [hplaq]

/-- The top action of an assembly is independent of the
negative plane stratum. -/
theorem wilsonActionZeroTop_assemble_indep (hN : Even N) (β : ℝ)
    (z z' : ↥(posLinks (N := N)) → G)
    (a : ↥(planeHalfLinks (N := N)) → G)
    (a₁' a₂' : ↥(planeNegLinks (N := N)) → G) :
    wilsonActionZeroTop ρ β (planeAssemble hN z z' a a₁')
      = wilsonActionZeroTop ρ β (planeAssemble hN z z' a a₂') := by
  unfold wilsonActionZeroTop
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.mem_filter] at hp
  obtain ⟨hpI, hpZ, hpT⟩ := hp
  obtain ⟨x, μ, ν⟩ := p
  have hμ : μ = 0 := (isZeroPlaq_dir_base hN _ hpZ).1
  subst hμ
  have hν : ν ≠ 0 := ne_of_gt (mem_plaqIndex hpI)
  exact plaquetteDensity_top ρ hN hpT hν z z' a a₁' a₂'

/-- The bottom action of an assembly is independent of the
positive plane stratum. -/
theorem wilsonActionZeroBot_assemble_indep (hN : Even N) (β : ℝ)
    (z z' : ↥(posLinks (N := N)) → G)
    (a₁ a₂ : ↥(planeHalfLinks (N := N)) → G)
    (a' : ↥(planeNegLinks (N := N)) → G) :
    wilsonActionZeroBot ρ β (planeAssemble hN z z' a₁ a')
      = wilsonActionZeroBot ρ β (planeAssemble hN z z' a₂ a') := by
  unfold wilsonActionZeroBot
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.mem_filter] at hp
  obtain ⟨hpI, hpZ, hpB⟩ := hp
  obtain ⟨x, μ, ν⟩ := p
  have hμ : μ = 0 := (isZeroPlaq_dir_base hN _ hpZ).1
  subst hμ
  have hν : ν ≠ 0 := ne_of_gt (mem_plaqIndex hpI)
  exact plaquetteDensity_bot ρ hN hpB hν z z' a₁ a₂ a'

/-- **Top density, layer form**: a top density reads `z, z'`
only at the single spatial link `(x, ν)` of the top layer. -/
theorem plaquetteDensity_top_layer (hN : Even N) {x : Fin 4 → ZMod N}
    {ν : Fin 4} (hx : (x 0).val = N / 2 - 1) (hν : ν ≠ 0)
    (z₁ z₂ z₁' z₂' : ↥(posLinks (N := N)) → G)
    (a : ↥(planeHalfLinks (N := N)) → G)
    (a' : ↥(planeNegLinks (N := N)) → G)
    (hz : z₁ ⟨(x, ν), mem_posLinks_top hN hx hν⟩
        = z₂ ⟨(x, ν), mem_posLinks_top hN hx hν⟩)
    (hz' : z₁' ⟨(x, ν), mem_posLinks_top hN hx hν⟩
        = z₂' ⟨(x, ν), mem_posLinks_top hN hx hν⟩) :
    plaquetteDensity (torusShift N) ρ (planeAssemble hN z₁ z₁' a a') x 0 ν
      = plaquetteDensity (torusShift N) ρ (planeAssemble hN z₂ z₂' a a')
        x 0 ν := by
  have hplaq : plaquette (torusShift N) (planeAssemble hN z₁ z₁' a a') x 0 ν
      = plaquette (torusShift N) (planeAssemble hN z₂ z₂' a a') x 0 ν := by
    unfold plaquette
    rw [planeAssemble_top_time hN hx z₁ z₁' a a',
      planeAssemble_top_time hN hx z₂ z₂' a a',
      planeAssemble_top_shift hN hx hν z₁ z₁' a a',
      planeAssemble_top_shift hN hx hν z₂ z₂' a a', hz',
      planeAssemble_top_time_shift hN hx hν z₁ z₁' a a',
      planeAssemble_top_time_shift hN hx hν z₂ z₂' a a',
      planeAssemble_top_spatial hN hx hν z₁ z₁' a a',
      planeAssemble_top_spatial hN hx hν z₂ z₂' a a', hz]
  unfold plaquetteDensity
  rw [hplaq]

/-- **Bottom density, layer form**: a bottom density reads
`z, z'` only at the single spatial link `(σ₀x, ν)` of the
bottom layer (time `0`). -/
theorem plaquetteDensity_bot_layer (hN : Even N) {x : Fin 4 → ZMod N}
    {ν : Fin 4} (hx : (x 0).val = N - 1) (hν : ν ≠ 0)
    (z₁ z₂ z₁' z₂' : ↥(posLinks (N := N)) → G)
    (a : ↥(planeHalfLinks (N := N)) → G)
    (a' : ↥(planeNegLinks (N := N)) → G)
    (hz : z₁ ⟨(torusShift N 0 x, ν), mem_posLinks_bot_shift hN hx hν⟩
        = z₂ ⟨(torusShift N 0 x, ν), mem_posLinks_bot_shift hN hx hν⟩)
    (hz' : z₁' ⟨(torusShift N 0 x, ν), mem_posLinks_bot_shift hN hx hν⟩
        = z₂' ⟨(torusShift N 0 x, ν), mem_posLinks_bot_shift hN hx hν⟩) :
    plaquetteDensity (torusShift N) ρ (planeAssemble hN z₁ z₁' a a') x 0 ν
      = plaquetteDensity (torusShift N) ρ (planeAssemble hN z₂ z₂' a a')
        x 0 ν := by
  have hplaq : plaquette (torusShift N) (planeAssemble hN z₁ z₁' a a') x 0 ν
      = plaquette (torusShift N) (planeAssemble hN z₂ z₂' a a') x 0 ν := by
    unfold plaquette
    rw [planeAssemble_bot_time hN hx z₁ z₁' a a',
      planeAssemble_bot_time hN hx z₂ z₂' a a',
      planeAssemble_bot_shift hN hx hν z₁ z₁' a a',
      planeAssemble_bot_shift hN hx hν z₂ z₂' a a', hz,
      planeAssemble_bot_time_shift hN hx hν z₁ z₁' a a',
      planeAssemble_bot_time_shift hN hx hν z₂ z₂' a a',
      planeAssemble_bot_spatial hN hx hν z₁ z₁' a a',
      planeAssemble_bot_spatial hN hx hν z₂ z₂' a a', hz']
  unfold plaquetteDensity
  rw [hplaq]

/-- The top action of an assembly depends on `z, z'` only
through their spatial links at time `N / 2 - 1` (the memo's
extraction `τ⁺`, as a factoring statement). -/
theorem wilsonActionZeroTop_layer (hN : Even N) (β : ℝ)
    (z₁ z₂ z₁' z₂' : ↥(posLinks (N := N)) → G)
    (a : ↥(planeHalfLinks (N := N)) → G)
    (a' : ↥(planeNegLinks (N := N)) → G)
    (hz : ∀ ℓ : ↥(posLinks (N := N)), (ℓ.1.1 0).val = N / 2 - 1 →
      ℓ.1.2 ≠ 0 → z₁ ℓ = z₂ ℓ)
    (hz' : ∀ ℓ : ↥(posLinks (N := N)), (ℓ.1.1 0).val = N / 2 - 1 →
      ℓ.1.2 ≠ 0 → z₁' ℓ = z₂' ℓ) :
    wilsonActionZeroTop ρ β (planeAssemble hN z₁ z₁' a a')
      = wilsonActionZeroTop ρ β (planeAssemble hN z₂ z₂' a a') := by
  unfold wilsonActionZeroTop
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.mem_filter] at hp
  obtain ⟨hpI, hpZ, hpT⟩ := hp
  obtain ⟨x, μ, ν⟩ := p
  have hμ : μ = 0 := (isZeroPlaq_dir_base hN _ hpZ).1
  subst hμ
  have hν : ν ≠ 0 := ne_of_gt (mem_plaqIndex hpI)
  exact plaquetteDensity_top_layer ρ hN hpT hν z₁ z₂ z₁' z₂' a a'
    (hz ⟨(x, ν), mem_posLinks_top hN hpT hν⟩ hpT hν)
    (hz' ⟨(x, ν), mem_posLinks_top hN hpT hν⟩ hpT hν)

/-- The bottom action of an assembly depends on `z, z'` only
through their spatial links at time `0` (the memo's extraction
`τ₀`, as a factoring statement). -/
theorem wilsonActionZeroBot_layer (hN : Even N) (β : ℝ)
    (z₁ z₂ z₁' z₂' : ↥(posLinks (N := N)) → G)
    (a : ↥(planeHalfLinks (N := N)) → G)
    (a' : ↥(planeNegLinks (N := N)) → G)
    (hz : ∀ ℓ : ↥(posLinks (N := N)), (ℓ.1.1 0).val = 0 →
      ℓ.1.2 ≠ 0 → z₁ ℓ = z₂ ℓ)
    (hz' : ∀ ℓ : ↥(posLinks (N := N)), (ℓ.1.1 0).val = 0 →
      ℓ.1.2 ≠ 0 → z₁' ℓ = z₂' ℓ) :
    wilsonActionZeroBot ρ β (planeAssemble hN z₁ z₁' a a')
      = wilsonActionZeroBot ρ β (planeAssemble hN z₂ z₂' a a') := by
  unfold wilsonActionZeroBot
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.mem_filter] at hp
  obtain ⟨hpI, hpZ, hpB⟩ := hp
  obtain ⟨x, μ, ν⟩ := p
  have hμ : μ = 0 := (isZeroPlaq_dir_base hN _ hpZ).1
  subst hμ
  have hν : ν ≠ 0 := ne_of_gt (mem_plaqIndex hpI)
  exact plaquetteDensity_bot_layer ρ hN hpB hν z₁ z₂ z₁' z₂' a a'
    (hz ⟨(torusShift N 0 x, ν), mem_posLinks_bot_shift hN hpB hν⟩
      (torusShift_zero_val_bot hpB) hν)
    (hz' ⟨(torusShift N 0 x, ν), mem_posLinks_bot_shift hN hpB hν⟩
      (torusShift_zero_val_bot hpB) hν)

end Values

section Kernels

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ))
  {N : ℕ} [NeZero N]

/-- The **top stratum kernel** `𝒯` (the memo's `A₁`): one Haar
integral over the positive plane stratum of the top action,
the other stratum frozen at the identity. By
`wilsonActionZeroTop_assemble_indep` the frozen value is
immaterial. -/
noncomputable def planeCrossingTop (hN : Even N) (β : ℝ)
    (z z' : ↥(posLinks (N := N)) → G) : ℂ :=
  ∫ a, (Real.exp (-(wilsonActionZeroTop ρ β
      (planeAssemble hN z z' a (fun _ => 1)))) : ℂ)
    ∂(Measure.pi fun _ : ↥(planeHalfLinks (N := N)) => μG)

/-- The **bottom stratum kernel** `ℬ` (the memo's `A₂`): one
Haar integral over the negative plane stratum of the bottom
action, the other stratum frozen at the identity. -/
noncomputable def planeCrossingBot (hN : Even N) (β : ℝ)
    (z z' : ↥(posLinks (N := N)) → G) : ℂ :=
  ∫ a', (Real.exp (-(wilsonActionZeroBot ρ β
      (planeAssemble hN z z' (fun _ => 1) a'))) : ℂ)
    ∂(Measure.pi fun _ : ↥(planeNegLinks (N := N)) => μG)

/-- **Brick β1 headline — the crossing marginal factors by base
layer**: at general `(G, ρ)`, every even `N` and every real `β`,
`planeCrossingMarginal = 𝒯 · ℬ`, the corpus form of the
scoping's `M(z,z′) = A₁(z,z′) · A₂(z,z′)`. The pointwise step is
the base-layer split of the crossing action together with the
two stratum-independence lemmas; the integral step is
`integral_const_mul`/`integral_mul_const` — no Fubini, no
product-measure identification. **No positivity** is asserted:
`𝒯, ℬ ⪰ 0` is Brick β2, open. -/
theorem planeCrossingMarginal_factor_top_bot (hN : Even N) (β : ℝ)
    (z z' : ↥(posLinks (N := N)) → G) :
    planeCrossingMarginal μG ρ hN β z z'
      = planeCrossingTop μG ρ hN β z z'
        * planeCrossingBot μG ρ hN β z z' := by
  have hpt : ∀ (a : ↥(planeHalfLinks (N := N)) → G)
      (a' : ↥(planeNegLinks (N := N)) → G),
      (Real.exp (-(wilsonActionZero ρ β (planeAssemble hN z z' a a'))) : ℂ)
        = (Real.exp (-(wilsonActionZeroTop ρ β
              (planeAssemble hN z z' a (fun _ => 1)))) : ℂ)
          * (Real.exp (-(wilsonActionZeroBot ρ β
              (planeAssemble hN z z' (fun _ => 1) a'))) : ℂ) := by
    intro a a'
    rw [wilsonActionZero_split ρ hN β (planeAssemble hN z z' a a'),
      wilsonActionZeroTop_assemble_indep ρ hN β z z' a a' (fun _ => 1),
      wilsonActionZeroBot_assemble_indep ρ hN β z z' a (fun _ => 1) a',
      ← Complex.ofReal_mul, ← Real.exp_add]
    congr 1
    ring
  have hinner : ∀ a : ↥(planeHalfLinks (N := N)) → G,
      (∫ a', (Real.exp (-(wilsonActionZero ρ β
          (planeAssemble hN z z' a a'))) : ℂ)
        ∂(Measure.pi fun _ : ↥(planeNegLinks (N := N)) => μG))
      = (Real.exp (-(wilsonActionZeroTop ρ β
            (planeAssemble hN z z' a (fun _ => 1)))) : ℂ)
        * ∫ a', (Real.exp (-(wilsonActionZeroBot ρ β
            (planeAssemble hN z z' (fun _ => 1) a'))) : ℂ)
          ∂(Measure.pi fun _ : ↥(planeNegLinks (N := N)) => μG) := by
    intro a
    rw [integral_congr_ae (ae_of_all _ (fun a' => hpt a a')),
      integral_const_mul]
  unfold planeCrossingMarginal planeCrossingTop planeCrossingBot
  rw [integral_congr_ae (ae_of_all _ hinner), integral_mul_const]

/-- At `β = 0` the top kernel is `1` (the top action vanishes). -/
theorem planeCrossingTop_zero (hN : Even N)
    (z z' : ↥(posLinks (N := N)) → G) :
    planeCrossingTop μG ρ hN 0 z z' = 1 := by
  unfold planeCrossingTop wilsonActionZeroTop
  simp

/-- At `β = 0` the bottom kernel is `1`. -/
theorem planeCrossingBot_zero (hN : Even N)
    (z z' : ↥(posLinks (N := N)) → G) :
    planeCrossingBot μG ρ hN 0 z z' = 1 := by
  unfold planeCrossingBot wilsonActionZeroBot
  simp

/-- At `β = 0` the crossing marginal is `1`, so the headline
factorization reads `1 = 1 * 1`. -/
theorem planeCrossingMarginal_zero (hN : Even N)
    (z z' : ↥(posLinks (N := N)) → G) :
    planeCrossingMarginal μG ρ hN 0 z z' = 1 := by
  unfold planeCrossingMarginal wilsonActionZero
  simp

/-- **Symmetry consistency**: the product form reproduces Brick
α's `planeCrossingMarginal_symm` — the two factors exchange
roles under `z ↔ z'`, as the seat computation required. (The
per-factor symmetry of a single stratum kernel is the memo's
expected `𝒜(u,u′) = 𝒜(u′,u)`; it is the layer-exchange
identification, not asserted here.) -/
theorem planeCrossing_factor_symm (hN : Even N) (β : ℝ)
    (z z' : ↥(posLinks (N := N)) → G) :
    planeCrossingTop μG ρ hN β z z' * planeCrossingBot μG ρ hN β z z'
      = planeCrossingTop μG ρ hN β z' z
        * planeCrossingBot μG ρ hN β z' z := by
  rw [← planeCrossingMarginal_factor_top_bot μG ρ hN β z z',
    ← planeCrossingMarginal_factor_top_bot μG ρ hN β z' z,
    planeCrossingMarginal_symm]

/-- **`τ⁺`-factoring**: the top kernel depends on `z, z'` only
through their spatial links at time `N / 2 - 1`. -/
theorem planeCrossingTop_layer (hN : Even N) (β : ℝ)
    (z₁ z₂ z₁' z₂' : ↥(posLinks (N := N)) → G)
    (hz : ∀ ℓ : ↥(posLinks (N := N)), (ℓ.1.1 0).val = N / 2 - 1 →
      ℓ.1.2 ≠ 0 → z₁ ℓ = z₂ ℓ)
    (hz' : ∀ ℓ : ↥(posLinks (N := N)), (ℓ.1.1 0).val = N / 2 - 1 →
      ℓ.1.2 ≠ 0 → z₁' ℓ = z₂' ℓ) :
    planeCrossingTop μG ρ hN β z₁ z₁'
      = planeCrossingTop μG ρ hN β z₂ z₂' := by
  unfold planeCrossingTop
  apply integral_congr_ae
  apply ae_of_all
  intro a
  show (Real.exp (-(wilsonActionZeroTop ρ β
        (planeAssemble hN z₁ z₁' a (fun _ => 1)))) : ℂ)
      = (Real.exp (-(wilsonActionZeroTop ρ β
        (planeAssemble hN z₂ z₂' a (fun _ => 1)))) : ℂ)
  rw [wilsonActionZeroTop_layer ρ hN β z₁ z₂ z₁' z₂' a (fun _ => 1) hz hz']

/-- **`τ₀`-factoring**: the bottom kernel depends on `z, z'`
only through their spatial links at time `0`. -/
theorem planeCrossingBot_layer (hN : Even N) (β : ℝ)
    (z₁ z₂ z₁' z₂' : ↥(posLinks (N := N)) → G)
    (hz : ∀ ℓ : ↥(posLinks (N := N)), (ℓ.1.1 0).val = 0 →
      ℓ.1.2 ≠ 0 → z₁ ℓ = z₂ ℓ)
    (hz' : ∀ ℓ : ↥(posLinks (N := N)), (ℓ.1.1 0).val = 0 →
      ℓ.1.2 ≠ 0 → z₁' ℓ = z₂' ℓ) :
    planeCrossingBot μG ρ hN β z₁ z₁'
      = planeCrossingBot μG ρ hN β z₂ z₂' := by
  unfold planeCrossingBot
  apply integral_congr_ae
  apply ae_of_all
  intro a'
  show (Real.exp (-(wilsonActionZeroBot ρ β
        (planeAssemble hN z₁ z₁' (fun _ => 1) a'))) : ℂ)
      = (Real.exp (-(wilsonActionZeroBot ρ β
        (planeAssemble hN z₂ z₂' (fun _ => 1) a'))) : ℂ)
  rw [wilsonActionZeroBot_layer ρ hN β z₁ z₂ z₁' z₂' (fun _ => 1) a' hz hz']

end Kernels
