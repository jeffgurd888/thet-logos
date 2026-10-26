import ThetLogos.PlaneCrossingFactor

/-!
# ThetLogos.PlaneCrossingCube — Brick β1-remainder: one kernel `𝒜` on layer data

Brick β1 (`PlaneCrossingFactor`) proved the crossing marginal
factors by base layer, `planeCrossingMarginal = 𝒯 · ℬ`, with the
top/bottom density words differing exactly by the layer exchange
(the swap in the words: top `a·z'·a⁻¹·z⁻¹`, bottom
`a'·z·a'⁻¹·z'⁻¹`). What β1 named as its remainder — and what
this module lands — is the identification of the two factors as
evaluations of **one** functional on abstract layer data:

- `LayerSite N`: the sites of one layer (time coordinate `0`);
  `LayerLink N`: its spatial links. A layer datum is a pair
  `(u, u')` of functions on `LayerLink N`.
- `layerConfig α u u'`: the honest configuration realizing the
  one-layer word (time links at time `0` read `α`, spatial links
  at time `0` read `u`, spatial links at time `1` read `u'`).
- **`𝒜`**: `layerKernel μG ρ β u u'`, the Haar average over the
  layer's stratum `α` of the one-layer Boltzmann factor
  `exp (−layerAction ρ β α u u')`.
- The two extractions `τ⁺` (spatial links at time `N/2 − 1`,
  stratum links at time `N/2 − 1`) and `τ₀` (spatial links at
  time `0`, stratum links at time `N − 1` read back to the layer
  through `(torusShift N 0).symm`), with the evaluation theorems
  `planeCrossingTop_eq_layerKernel` (𝒯 = 𝒜∘(τ⁺, τ⁺)) and
  `planeCrossingBot_eq_layerKernel` (ℬ = 𝒜∘(τ₀-swap)) — the
  swap is β1's bottom word read through 𝒜's word.
- **Per-stratum symmetry** `layerKernel_symm`: `𝒜(u,u') =
  𝒜(u',u)`. No spatial reflection is used: `plaquetteDensity`
  sees the word only through `(tr ρ ·).re`, invariant under
  inversion (`trace_repMatrix_inv`) and conjugation
  (`trace_repMatrix_conj`); substituting `α ↦ α⁻¹` in the
  stratum integral and inverting/conjugating each word is the
  in-cube reflection, one stratum down from
  `wilsonActionZero_reflConfig`'s mechanism.

**No positivity is asserted anywhere in this module.** The
single-layer kernel's positivity (`𝒜 ⪰ 0`) is Brick β2,
L+ / open, untouched here. NO CLAIM: this module closes **0**
parts of the Clay Yang–Mills statement.
-/

namespace ThetLogos

open MeasureTheory Finset
open scoped Matrix ENNReal NNReal

section LayerData

variable {N : ℕ} [NeZero N]

/-- The sites of one layer: sites whose time coordinate is `0`.
The spatial cube `(ZMod N)³` in the corpus's site vocabulary. -/
def LayerSite (N : ℕ) : Type :=
  {x : Fin 4 → ZMod N // (x 0).val = 0}

instance : Fintype (LayerSite N) := Subtype.fintype _

/-- The spatial links based in one layer: links based at time
`0` in a spatial direction. -/
def LayerLink (N : ℕ) : Type :=
  {ℓ : Link (Fin 4 → ZMod N) // (ℓ.1 0).val = 0 ∧ ℓ.2 ≠ 0}

instance : Fintype (LayerLink N) := Subtype.fintype _

/-- The layer link over a layer site in a spatial direction. -/
def layerLinkOf (c : LayerSite N) (ν : Fin 4) (hν : ν ≠ 0) :
    LayerLink N :=
  ⟨(c.1, ν), c.2, hν⟩

/-- A spatial shift inside the layer (a spatial shift does not
move the time coordinate). -/
def layerShift (ν : Fin 4) (hν : ν ≠ 0) (c : LayerSite N) :
    LayerSite N :=
  ⟨torusShift N ν c.1, by
    rw [torusShift_apply_zero_of_ne hν]; exact c.2⟩

/-- The top extraction site: a layer site read at time
`N / 2 - 1` (its time coordinate replaced). -/
def topSite (c : LayerSite N) : Fin 4 → ZMod N :=
  Function.update c.1 0 ((N / 2 - 1 : ℕ) : ZMod N)

/-- The time coordinate of a top site is `N / 2 - 1`. -/
theorem topSite_val (c : LayerSite N) :
    (topSite c 0).val = N / 2 - 1 := by
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  show ((N / 2 - 1 : ℕ) : ZMod N).val = N / 2 - 1
  exact ZMod.val_natCast_of_lt (by omega)

/-- Away from the time coordinate, a top site is the layer site. -/
theorem topSite_of_ne (c : LayerSite N) {j : Fin 4} (hj : j ≠ 0) :
    topSite c j = c.1 j :=
  Function.update_of_ne hj _ _

/-- The top extraction commutes with spatial shifts. -/
theorem topSite_shift (ν : Fin 4) (hν : ν ≠ 0) (c : LayerSite N) :
    topSite (layerShift ν hν c) = torusShift N ν (topSite c) := by
  funext j
  by_cases hj : j = 0
  · subst hj
    rw [show topSite (layerShift ν hν c) 0
          = ((N / 2 - 1 : ℕ) : ZMod N) from Function.update_self ..,
      torusShift_apply_coord, Pi.single_eq_of_ne (Ne.symm hν),
      zero_add]
    rfl
  · rw [topSite_of_ne _ hj, torusShift_apply_coord, topSite_of_ne c hj]
    rfl

/-- The bottom extraction site: a layer site read one time step
below the layer (time coordinate `N - 1`). -/
def botSite (c : LayerSite N) : Fin 4 → ZMod N :=
  (torusShift N 0).symm c.1

/-- A layer site's value is `0` at the time coordinate. -/
theorem layerSite_zero (c : LayerSite N) : c.1 0 = 0 := by
  rw [← ZMod.natCast_zmod_val (c.1 0), c.2, Nat.cast_zero]

/-- The time coordinate of a bottom site is `N - 1`. -/
theorem botSite_val (c : LayerSite N) : (botSite c 0).val = N - 1 := by
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have h1 : botSite c 0 = -1 := by
    show (torusShift N 0).symm c.1 0 = -1
    rw [torusShift_symm_apply_coord, Pi.single_eq_same,
      layerSite_zero c, zero_sub]
  rw [h1, ← natCast_pred_eq_neg_one]
  exact ZMod.val_natCast_of_lt (by omega)

/-- One time step up from a bottom site is the layer site. -/
theorem torusShift_zero_botSite (c : LayerSite N) :
    torusShift N 0 (botSite c) = c.1 :=
  Equiv.apply_symm_apply _ _

/-- The bottom extraction commutes with spatial shifts (inverse
shifts commute with shifts). -/
theorem botSite_shift (ν : Fin 4) (hν : ν ≠ 0) (c : LayerSite N) :
    botSite (layerShift ν hν c) = torusShift N ν (botSite c) :=
  torusShift_symm_apply_comm 0 ν c.1

/-- The layer site under a site: the site with time coordinate
set to `0`. -/
def topPreimage (x : Fin 4 → ZMod N) : LayerSite N :=
  ⟨Function.update x 0 0, by simp⟩

/-- The top extraction of the preimage is the site itself. -/
theorem topSite_topPreimage {x : Fin 4 → ZMod N}
    (hx : (x 0).val = N / 2 - 1) : topSite (topPreimage x) = x := by
  funext j
  by_cases hj : j = 0
  · subst hj
    show ((N / 2 - 1 : ℕ) : ZMod N) = x 0
    rw [← ZMod.natCast_zmod_val (x 0), hx]
  · rw [topSite_of_ne _ hj]
    exact Function.update_of_ne hj _ _

/-- The preimage of the top extraction is the layer site. -/
theorem topPreimage_topSite (c : LayerSite N) :
    topPreimage (topSite c) = c := by
  apply Subtype.ext
  show Function.update (topSite c) 0 0 = c.1
  funext j
  by_cases hj : j = 0
  · subst hj
    rw [Function.update_self, ← ZMod.natCast_zmod_val (c.1 0), c.2,
      Nat.cast_zero]
  · rw [Function.update_of_ne hj]
    exact topSite_of_ne c hj

/-- The layer site over a bottom-layer site: one time step up
(the wrap lands at time `0`). -/
def botPreimage (x : Fin 4 → ZMod N) (hx : (x 0).val = N - 1) :
    LayerSite N :=
  ⟨torusShift N 0 x, torusShift_zero_val_bot hx⟩

/-- The bottom extraction of the preimage is the site itself. -/
theorem botSite_botPreimage {x : Fin 4 → ZMod N}
    (hx : (x 0).val = N - 1) : botSite (botPreimage x hx) = x :=
  Equiv.symm_apply_apply _ _

end LayerData

section Extractions

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {N : ℕ} [NeZero N]

/-- A layer link, read as a link of the full lattice, lies in the
strict positive half. -/
theorem layerLink_mem_posLinks (hN : Even N) (ℓ : LayerLink N) :
    ℓ.1 ∈ posLinks (N := N) := by
  rw [mem_posLinks]
  refine ⟨?_, ?_⟩
  · have h2 : 2 ≤ N := two_le_of_even hN
    rw [ℓ.2.1]; omega
  · show reflLink (ℓ.1.1, ℓ.1.2) ≠ (ℓ.1.1, ℓ.1.2)
    rw [reflLink_of_ne ℓ.2.2]
    intro h
    exact (reflSite_ne_self hN ℓ.1.1) (congrArg Prod.fst h)

/-- **`τ⁺`**: a strict-half configuration read at its top layer —
its spatial links at time `N / 2 - 1`, transported to the layer. -/
def tauTop (hN : Even N) (z : ↥(posLinks (N := N)) → G) :
    LayerLink N → G :=
  fun ℓ => z ⟨(topSite ⟨ℓ.1.1, ℓ.2.1⟩, ℓ.1.2),
    mem_posLinks_top hN (topSite_val _) ℓ.2.2⟩

/-- **`τ₀`**: a strict-half configuration read at its bottom
layer — its spatial links at time `0`. -/
def tauBot (hN : Even N) (z : ↥(posLinks (N := N)) → G) :
    LayerLink N → G :=
  fun ℓ => z ⟨ℓ.1, layerLink_mem_posLinks hN ℓ⟩

/-- The top stratum embedding: a layer site as the time link of
the positive plane stratum based at time `N / 2 - 1`. -/
def embTop (hN : Even N) (c : LayerSite N) :
    ↥(planeHalfLinks (N := N)) :=
  ⟨(topSite c, 0), mem_planeHalfLinks_top hN (topSite_val c)⟩

/-- The bottom stratum embedding: a layer site as the time link
of the negative plane stratum based at time `N - 1` (the link
ending at the layer). -/
def embBot (hN : Even N) (c : LayerSite N) :
    ↥(planeNegLinks (N := N)) :=
  ⟨(botSite c, 0), mem_planeNegLinks_bot hN (botSite_val c)⟩

/-- The top stratum read on the layer. -/
def stratumTop (hN : Even N) (a : ↥(planeHalfLinks (N := N)) → G) :
    LayerSite N → G :=
  fun c => a (embTop hN c)

/-- The bottom stratum read on the layer. -/
def stratumBot (hN : Even N) (a' : ↥(planeNegLinks (N := N)) → G) :
    LayerSite N → G :=
  fun c => a' (embBot hN c)

theorem embTop_injective (hN : Even N) :
    Function.Injective (embTop hN) := by
  intro c c' h
  have h1 : topSite c = topSite c' :=
    congrArg (fun m : ↥(planeHalfLinks (N := N)) => m.1.1) h
  apply Subtype.ext
  funext j
  by_cases hj : j = 0
  · subst hj; rw [layerSite_zero c, layerSite_zero c']
  · rw [← topSite_of_ne c hj, ← topSite_of_ne c' hj, h1]

theorem embBot_injective (hN : Even N) :
    Function.Injective (embBot hN) := by
  intro c c' h
  have h1 : botSite c = botSite c' :=
    congrArg (fun m : ↥(planeNegLinks (N := N)) => m.1.1) h
  apply Subtype.ext
  have h2 := congrArg (torusShift N 0) h1
  rwa [torusShift_zero_botSite, torusShift_zero_botSite] at h2

end Extractions

section LayerConfig

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ)) {N : ℕ} [NeZero N]

/-- **The layer configuration**: the honest configuration of the
full lattice realizing one layer's word — time links at time `0`
read the stratum `α`, spatial links at time `0` read `u`,
spatial links at time `1` read `u'` (pulled back one time step),
everything else is `1`. The plaquette of this configuration at a
layer site is exactly the one-layer word
`α · u' · α_σ⁻¹ · u⁻¹` that Brick β1 found at both crossing
layers. -/
noncomputable def layerConfig (α : LayerSite N → G)
    (u u' : LayerLink N → G) : Config (Fin 4 → ZMod N) G :=
  fun ℓ =>
    if hν : ℓ.2 = 0 then
      if ht : (ℓ.1 0).val = 0 then α ⟨ℓ.1, ht⟩ else 1
    else if ht : (ℓ.1 0).val = 0 then u ⟨ℓ, ht, hν⟩
    else if ht1 : (ℓ.1 0).val = 1 then
      u' ⟨((torusShift N 0).symm ℓ.1, ℓ.2), by
        have h10 : ℓ.1 0 = 1 := by
          rw [← ZMod.natCast_zmod_val (ℓ.1 0), ht1, Nat.cast_one]
        show (((torusShift N 0).symm ℓ.1) 0).val = 0
        rw [torusShift_symm_apply_coord, Pi.single_eq_same, h10,
          sub_self]
        exact ZMod.val_zero, hν⟩
    else 1

/-- The layer configuration at a time link of the layer reads
the stratum. -/
theorem layerConfig_time (α : LayerSite N → G)
    (u u' : LayerLink N → G) (c : LayerSite N) :
    layerConfig α u u' (c.1, 0) = α c := by
  have h1 : (c.1, 0).2 = (0 : Fin 4) := rfl
  have h2 : ((c.1, 0).1 0).val = 0 := c.2
  unfold layerConfig
  rw [dite_eq_left h1, dite_eq_left h2]
  congr 1

/-- The layer configuration at a spatial link of the layer reads
the first boundary datum. -/
theorem layerConfig_spatial (α : LayerSite N → G)
    (u u' : LayerLink N → G) (c : LayerSite N) (ν : Fin 4)
    (hν : ν ≠ 0) :
    layerConfig α u u' (c.1, ν) = u (layerLinkOf c ν hν) := by
  have h1 : ¬ (c.1, ν).2 = (0 : Fin 4) := hν
  have h2 : ((c.1, ν).1 0).val = 0 := c.2
  unfold layerConfig
  rw [dite_eq_right h1, dite_eq_left h2]
  congr 1

/-- The layer configuration one time step above a spatial link
of the layer reads the second boundary datum. -/
theorem layerConfig_up (hN : Even N) (α : LayerSite N → G)
    (u u' : LayerLink N → G) (c : LayerSite N) (ν : Fin 4)
    (hν : ν ≠ 0) :
    layerConfig α u u' (torusShift N 0 c.1, ν)
      = u' (layerLinkOf c ν hν) := by
  have hy0 : torusShift N 0 c.1 0 = 1 := by
    rw [torusShift_apply_coord, Pi.single_eq_same, layerSite_zero c,
      add_zero]
  have hy0val : (torusShift N 0 c.1 0).val = 1 := by
    rw [hy0, ← Nat.cast_one]
    exact ZMod.val_natCast_of_lt
      (by have h2 := two_le_of_even hN; omega)
  have h1 : ¬ (torusShift N 0 c.1, ν).2 = (0 : Fin 4) := hν
  have h2 : ¬ ((torusShift N 0 c.1, ν).1 0).val = 0 := by
    show ¬ (torusShift N 0 c.1 0).val = 0
    rw [hy0val]
    exact Nat.one_ne_zero
  have h3 : ((torusShift N 0 c.1, ν).1 0).val = 1 := hy0val
  unfold layerConfig
  rw [dite_eq_right h1, dite_eq_right h2, dite_eq_left h3]
  congr 1
  apply Subtype.ext
  show ((torusShift N 0).symm (torusShift N 0 c.1), ν) = (c.1, ν)
  rw [Equiv.symm_apply_apply]

/-- The layer configuration at the spatially shifted time link
of the layer reads the stratum at the shifted site. -/
theorem layerConfig_time_shift (α : LayerSite N → G)
    (u u' : LayerLink N → G) (ν : Fin 4) (hν : ν ≠ 0)
    (c : LayerSite N) :
    layerConfig α u u' (torusShift N ν c.1, 0)
      = α (layerShift ν hν c) := by
  have h1 : (torusShift N ν c.1, 0).2 = (0 : Fin 4) := rfl
  have h2 : ((torusShift N ν c.1, 0).1 0).val = 0 := by
    show (torusShift N ν c.1 0).val = 0
    rw [torusShift_apply_zero_of_ne hν]
    exact c.2
  unfold layerConfig
  rw [dite_eq_left h1, dite_eq_left h2]
  congr 1

/-- **The one-layer word**: the plaquette of the layer
configuration at a layer site is
`α c · u' ℓ · (α (σ_ν c))⁻¹ · (u ℓ)⁻¹` — Brick β1's top word
(the bottom word is this word with `u, u'` exchanged). -/
theorem plaquette_layerConfig (hN : Even N) (α : LayerSite N → G)
    (u u' : LayerLink N → G) (c : LayerSite N) (ν : Fin 4)
    (hν : ν ≠ 0) :
    plaquette (torusShift N) (layerConfig α u u') c.1 0 ν
      = α c * u' (layerLinkOf c ν hν) * (α (layerShift ν hν c))⁻¹
        * (u (layerLinkOf c ν hν))⁻¹ := by
  unfold plaquette
  rw [layerConfig_time, layerConfig_up hN, layerConfig_time_shift,
    layerConfig_spatial]

end LayerConfig

section Words

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ)) {N : ℕ} [NeZero N]

/-- **Top density, layer form**: at a top crossing plaquette,
the assembly's density is the layer density of the extracted
data `(τ⁺z, τ⁺z′, stratumTop a)`. The four factors are matched
one by one against Brick β1's four link reads. -/
theorem plaquetteDensity_top_word (hN : Even N) {x : Fin 4 → ZMod N}
    (hx : (x 0).val = N / 2 - 1) {ν : Fin 4} (hν : ν ≠ 0)
    (z z' : ↥(posLinks (N := N)) → G)
    (a : ↥(planeHalfLinks (N := N)) → G)
    (a' : ↥(planeNegLinks (N := N)) → G) :
    plaquetteDensity (torusShift N) ρ (planeAssemble hN z z' a a') x 0 ν
      = plaquetteDensity (torusShift N) ρ
          (layerConfig (stratumTop hN a) (tauTop hN z) (tauTop hN z'))
          (topPreimage x).1 0 ν := by
  have e1 : stratumTop hN a (topPreimage x)
      = a ⟨(x, 0), mem_planeHalfLinks_top hN hx⟩ := by
    show a ⟨(topSite (topPreimage x), 0),
      mem_planeHalfLinks_top hN (topSite_val (topPreimage x))⟩ = _
    congr 1
    exact Subtype.ext (Prod.ext_iff.mpr ⟨topSite_topPreimage hx, rfl⟩)
  have e2 : tauTop hN z' (layerLinkOf (topPreimage x) ν hν)
      = z' ⟨(x, ν), mem_posLinks_top hN hx hν⟩ := by
    show z' ⟨(topSite (topPreimage x), ν),
      mem_posLinks_top hN (topSite_val (topPreimage x)) hν⟩ = _
    congr 1
    exact Subtype.ext (Prod.ext_iff.mpr ⟨topSite_topPreimage hx, rfl⟩)
  have e3 : stratumTop hN a (layerShift ν hν (topPreimage x))
      = a ⟨(torusShift N ν x, 0),
        mem_planeHalfLinks_top_shift hN hx hν⟩ := by
    show a ⟨(topSite (layerShift ν hν (topPreimage x)), 0),
      mem_planeHalfLinks_top hN
        (topSite_val (layerShift ν hν (topPreimage x)))⟩ = _
    have hsite : topSite (layerShift ν hν (topPreimage x))
        = torusShift N ν x := by
      rw [topSite_shift, topSite_topPreimage hx]
    congr 1
    exact Subtype.ext (Prod.ext_iff.mpr ⟨hsite, rfl⟩)
  have e4 : tauTop hN z (layerLinkOf (topPreimage x) ν hν)
      = z ⟨(x, ν), mem_posLinks_top hN hx hν⟩ := by
    show z ⟨(topSite (topPreimage x), ν),
      mem_posLinks_top hN (topSite_val (topPreimage x)) hν⟩ = _
    congr 1
    exact Subtype.ext (Prod.ext_iff.mpr ⟨topSite_topPreimage hx, rfl⟩)
  have hw := plaquette_layerConfig hN (stratumTop hN a) (tauTop hN z)
    (tauTop hN z') (topPreimage x) ν hν
  have hplaq : plaquette (torusShift N) (planeAssemble hN z z' a a')
        x 0 ν
      = plaquette (torusShift N)
          (layerConfig (stratumTop hN a) (tauTop hN z) (tauTop hN z'))
          (topPreimage x).1 0 ν := by
    rw [hw]
    unfold plaquette
    rw [planeAssemble_top_time hN hx z z' a a',
      planeAssemble_top_shift hN hx hν z z' a a',
      planeAssemble_top_time_shift hN hx hν z z' a a',
      planeAssemble_top_spatial hN hx hν z z' a a',
      e1, e2, e3, e4]
  unfold plaquetteDensity
  rw [hplaq]

/-- **Bottom density, layer form**: at a bottom crossing
plaquette, the assembly's density is the layer density of
`(τ₀z′, τ₀z, stratumBot a′)` — the swap against the top word is
Brick β1's bottom word read through 𝒜's word. -/
theorem plaquetteDensity_bot_word (hN : Even N) {x : Fin 4 → ZMod N}
    (hx : (x 0).val = N - 1) {ν : Fin 4} (hν : ν ≠ 0)
    (z z' : ↥(posLinks (N := N)) → G)
    (a : ↥(planeHalfLinks (N := N)) → G)
    (a' : ↥(planeNegLinks (N := N)) → G) :
    plaquetteDensity (torusShift N) ρ (planeAssemble hN z z' a a') x 0 ν
      = plaquetteDensity (torusShift N) ρ
          (layerConfig (stratumBot hN a') (tauBot hN z') (tauBot hN z))
          (botPreimage x hx).1 0 ν := by
  have f1 : stratumBot hN a' (botPreimage x hx)
      = a' ⟨(x, 0), mem_planeNegLinks_bot hN hx⟩ := by
    show a' ⟨(botSite (botPreimage x hx), 0),
      mem_planeNegLinks_bot hN (botSite_val (botPreimage x hx))⟩ = _
    congr 1
    exact Subtype.ext (Prod.ext_iff.mpr ⟨botSite_botPreimage hx, rfl⟩)
  have f2 : tauBot hN z (layerLinkOf (botPreimage x hx) ν hν)
      = z ⟨(torusShift N 0 x, ν),
        mem_posLinks_bot_shift hN hx hν⟩ := by
    show z ⟨(torusShift N 0 x, ν),
      layerLink_mem_posLinks hN (layerLinkOf (botPreimage x hx) ν hν)⟩
      = _
    congr 1
  have f3 : stratumBot hN a' (layerShift ν hν (botPreimage x hx))
      = a' ⟨(torusShift N ν x, 0),
        mem_planeNegLinks_bot_shift hN hx hν⟩ := by
    show a' ⟨(botSite (layerShift ν hν (botPreimage x hx)), 0),
      mem_planeNegLinks_bot hN
        (botSite_val (layerShift ν hν (botPreimage x hx)))⟩ = _
    have hsite : botSite (layerShift ν hν (botPreimage x hx))
        = torusShift N ν x := by
      rw [botSite_shift, botSite_botPreimage hx]
    congr 1
    exact Subtype.ext (Prod.ext_iff.mpr ⟨hsite, rfl⟩)
  have f4 : tauBot hN z' (layerLinkOf (botPreimage x hx) ν hν)
      = z' ⟨(torusShift N 0 x, ν),
        mem_posLinks_bot_shift hN hx hν⟩ := by
    show z' ⟨(torusShift N 0 x, ν),
      layerLink_mem_posLinks hN (layerLinkOf (botPreimage x hx) ν hν)⟩
      = _
    congr 1
  have hw := plaquette_layerConfig hN (stratumBot hN a')
    (tauBot hN z') (tauBot hN z) (botPreimage x hx) ν hν
  have hplaq : plaquette (torusShift N) (planeAssemble hN z z' a a')
        x 0 ν
      = plaquette (torusShift N)
          (layerConfig (stratumBot hN a') (tauBot hN z')
            (tauBot hN z))
          (botPreimage x hx).1 0 ν := by
    rw [hw]
    unfold plaquette
    rw [planeAssemble_bot_time hN hx z z' a a',
      planeAssemble_bot_shift hN hx hν z z' a a',
      planeAssemble_bot_time_shift hN hx hν z z' a a',
      planeAssemble_bot_spatial hN hx hν z z' a a',
      f1, f2, f3, f4]
  unfold plaquetteDensity
  rw [hplaq]

end Words

section Sums

variable {N : ℕ} [NeZero N]

/-- **Top class sum over the layer**: the sum over the top
crossing class of the plaquette index set is the sum over layer
sites and spatial directions. -/
theorem sum_top_class (hN : Even N)
    (f : (Fin 4 → ZMod N) → Fin 4 → Fin 4 → ℝ) :
    ∑ p ∈ plaqIndex.filter (fun p => IsZeroPlaq p ∧ IsTopPlaq p),
        f p.1 p.2.1 p.2.2
      = ∑ c : LayerSite N, ∑ ν ∈ Finset.Ioi (0 : Fin 4),
          f (topSite c) 0 ν := by
  classical
  rw [← Finset.sum_product']
  apply Finset.sum_bij (fun p _ => (topPreimage p.1, p.2.2))
  · intro p hp
    rw [Finset.mem_filter] at hp
    have hμ : p.2.1 = 0 := (isZeroPlaq_dir_base hN p hp.2.1).1
    have hν : p.2.2 ∈ Finset.Ioi (0 : Fin 4) := by
      rw [Finset.mem_Ioi]
      have hlt := mem_plaqIndex hp.1
      omega
    exact Finset.mem_product.mpr ⟨Finset.mem_univ _, hν⟩
  · intro p₁ hp₁ p₂ hp₂ h
    rw [Finset.mem_filter] at hp₁ hp₂
    obtain ⟨x₁, μ₁, ν₁⟩ := p₁
    obtain ⟨x₂, μ₂, ν₂⟩ := p₂
    have hμ₁ : μ₁ = 0 := (isZeroPlaq_dir_base hN _ hp₁.2.1).1
    have hμ₂ : μ₂ = 0 := (isZeroPlaq_dir_base hN _ hp₂.2.1).1
    subst hμ₁; subst hμ₂
    have hν : ν₁ = ν₂ := congrArg Prod.snd h
    have hx : x₁ = x₂ := by
      have hpre : topPreimage x₁ = topPreimage x₂ :=
        congrArg Prod.fst h
      have e1 : topSite (topPreimage x₁) = x₁ :=
        topSite_topPreimage hp₁.2.2
      have e2 : topSite (topPreimage x₂) = x₂ :=
        topSite_topPreimage hp₂.2.2
      rw [← e1, ← e2, hpre]
    exact Prod.ext_iff.mpr ⟨hx, Prod.ext_iff.mpr ⟨rfl, hν⟩⟩
  · intro b hb
    obtain ⟨c, ν⟩ := b
    rw [Finset.mem_product] at hb
    refine ⟨(topSite c, 0, ν), ?_, ?_⟩
    · rw [Finset.mem_filter]
      refine ⟨?_, ?_, topSite_val c⟩
      · exact Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, Finset.mem_Ioi.mp hb.2⟩
      · constructor
        · show ¬ plaqTimeHi (topSite c) 0 < N / 2
          rw [plaqTimeHi_zero, topSite_val]
          have h2 : 2 ≤ N := two_le_of_even hN
          omega
        · rintro ⟨hge, -⟩
          rw [topSite_val] at hge
          have h2 : 2 ≤ N := two_le_of_even hN
          omega
    · exact Prod.ext_iff.mpr ⟨topPreimage_topSite c, rfl⟩
  · intro p hp
    rw [Finset.mem_filter] at hp
    have hμ : p.2.1 = 0 := (isZeroPlaq_dir_base hN p hp.2.1).1
    obtain ⟨x, μ, ν⟩ := p
    subst hμ
    show f x 0 ν = f (topSite (topPreimage x)) 0 ν
    rw [topSite_topPreimage hp.2.2]

/-- **Bottom class sum over the layer**. -/
theorem sum_bot_class (hN : Even N)
    (f : (Fin 4 → ZMod N) → Fin 4 → Fin 4 → ℝ) :
    ∑ p ∈ plaqIndex.filter (fun p => IsZeroPlaq p ∧ IsBotPlaq p),
        f p.1 p.2.1 p.2.2
      = ∑ c : LayerSite N, ∑ ν ∈ Finset.Ioi (0 : Fin 4),
          f (botSite c) 0 ν := by
  classical
  rw [← Finset.sum_product']
  apply Finset.sum_bij
    (fun p hp => (botPreimage p.1
      (Finset.mem_filter.mp hp).2.2, p.2.2))
  · intro p hp
    rw [Finset.mem_filter] at hp
    have hμ : p.2.1 = 0 := (isZeroPlaq_dir_base hN p hp.2.1).1
    have hν : p.2.2 ∈ Finset.Ioi (0 : Fin 4) := by
      rw [Finset.mem_Ioi]
      have hlt := mem_plaqIndex hp.1
      omega
    exact Finset.mem_product.mpr ⟨Finset.mem_univ _, hν⟩
  · intro p₁ hp₁ p₂ hp₂ h
    rw [Finset.mem_filter] at hp₁ hp₂
    obtain ⟨x₁, μ₁, ν₁⟩ := p₁
    obtain ⟨x₂, μ₂, ν₂⟩ := p₂
    have hμ₁ : μ₁ = 0 := (isZeroPlaq_dir_base hN _ hp₁.2.1).1
    have hμ₂ : μ₂ = 0 := (isZeroPlaq_dir_base hN _ hp₂.2.1).1
    subst hμ₁; subst hμ₂
    have hν : ν₁ = ν₂ := congrArg Prod.snd h
    have hx : x₁ = x₂ := by
      have hpre : botPreimage x₁ hp₁.2.2 = botPreimage x₂ hp₂.2.2 :=
        congrArg Prod.fst h
      have hcon := congrArg botSite hpre
      rwa [botSite_botPreimage, botSite_botPreimage] at hcon
    exact Prod.ext_iff.mpr ⟨hx, Prod.ext_iff.mpr ⟨rfl, hν⟩⟩
  · intro b hb
    obtain ⟨c, ν⟩ := b
    rw [Finset.mem_product] at hb
    refine ⟨(botSite c, 0, ν), ?_, ?_⟩
    · rw [Finset.mem_filter]
      refine ⟨?_, ?_, botSite_val c⟩
      · exact Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, Finset.mem_Ioi.mp hb.2⟩
      · constructor
        · show ¬ plaqTimeHi (botSite c) 0 < N / 2
          rw [plaqTimeHi_zero, botSite_val]
          have h2 : 2 ≤ N := two_le_of_even hN
          omega
        · rintro ⟨-, hlt⟩
          rw [plaqTimeHi_zero, botSite_val] at hlt
          omega
    · show (botPreimage (botSite c) (botSite_val c), ν) = (c, ν)
      exact Prod.ext_iff.mpr
        ⟨Subtype.ext (torusShift_zero_botSite c), rfl⟩
  · intro p hp
    rw [Finset.mem_filter] at hp
    have hμ : p.2.1 = 0 := (isZeroPlaq_dir_base hN p hp.2.1).1
    obtain ⟨x, μ, ν⟩ := p
    subst hμ
    show f x 0 ν = f (botSite (botPreimage x hp.2.2)) 0 ν
    rw [botSite_botPreimage]

end Sums

section Actions

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ)) {N : ℕ} [NeZero N]

/-- **The one-layer action**: the Wilson action of one layer's
worth of plaquettes of the layer configuration, with the
coupling — the exponent of Brick β2's kernel `𝒜`. -/
noncomputable def layerAction (β : ℝ) (α : LayerSite N → G)
    (u u' : LayerLink N → G) : ℝ :=
  β * ∑ c : LayerSite N, ∑ ν ∈ Finset.Ioi (0 : Fin 4),
    plaquetteDensity (torusShift N) ρ (layerConfig α u u') c.1 0 ν

/-- **Top action, layer form**: the top crossing action of an
assembly is the one-layer action of its extracted data. -/
theorem wilsonActionZeroTop_eq_layerAction (hN : Even N) (β : ℝ)
    (z z' : ↥(posLinks (N := N)) → G)
    (a : ↥(planeHalfLinks (N := N)) → G)
    (a' : ↥(planeNegLinks (N := N)) → G) :
    wilsonActionZeroTop ρ β (planeAssemble hN z z' a a')
      = layerAction ρ β (stratumTop hN a) (tauTop hN z)
          (tauTop hN z') := by
  unfold wilsonActionZeroTop layerAction
  congr 1
  rw [sum_top_class hN (fun x μ ν =>
    plaquetteDensity (torusShift N) ρ (planeAssemble hN z z' a a')
      x μ ν)]
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro ν hν
  rw [Finset.mem_Ioi] at hν
  have hw := plaquetteDensity_top_word ρ hN (topSite_val c)
    (ne_of_gt hν) z z' a a'
  rw [hw, topPreimage_topSite]

/-- **Bottom action, layer form**: the bottom crossing action of
an assembly is the one-layer action of its extracted data, with
the two boundary data exchanged. -/
theorem wilsonActionZeroBot_eq_layerAction (hN : Even N) (β : ℝ)
    (z z' : ↥(posLinks (N := N)) → G)
    (a : ↥(planeHalfLinks (N := N)) → G)
    (a' : ↥(planeNegLinks (N := N)) → G) :
    wilsonActionZeroBot ρ β (planeAssemble hN z z' a a')
      = layerAction ρ β (stratumBot hN a') (tauBot hN z')
          (tauBot hN z) := by
  unfold wilsonActionZeroBot layerAction
  congr 1
  rw [sum_bot_class hN (fun x μ ν =>
    plaquetteDensity (torusShift N) ρ (planeAssemble hN z z' a a')
      x μ ν)]
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro ν hν
  rw [Finset.mem_Ioi] at hν
  have hw := plaquetteDensity_bot_word ρ hN (botSite_val c)
    (ne_of_gt hν) z z' a a'
  rw [hw]
  exact congrArg (fun y : LayerSite N =>
    plaquetteDensity (torusShift N) ρ
      (layerConfig (stratumBot hN a') (tauBot hN z') (tauBot hN z))
      y.1 0 ν) (Subtype.ext (torusShift_zero_botSite c))

end Actions

section Transport

variable {J ι : Type*} [Fintype J] [Fintype ι] [DecidableEq ι]
  {G : Type*} [Group G] [MeasurableSpace G]
  (μG : Measure G) [IsProbabilityMeasure μG]

/-- The embedding equivalence of an injective map onto its
image finset. -/
noncomputable def embEquiv (e : J → ι) (he : Function.Injective e) :
    J ≃ ↥(Finset.image e Finset.univ) where
  toFun j := ⟨e j, Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩⟩
  invFun ℓ := (Finset.mem_image.mp ℓ.2).choose
  left_inv j := by
    apply he
    exact (Finset.mem_image.mp
      (show e j ∈ Finset.image e Finset.univ from
        Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩)).choose_spec.2
  right_inv ℓ := by
    apply Subtype.ext
    exact (Finset.mem_image.mp ℓ.2).choose_spec.2

theorem embEquiv_apply (e : J → ι) (he : Function.Injective e)
    (j : J) : ((embEquiv e he) j).1 = e j := rfl

/-- **Pi-measure transport along an embedding**: integrating a
function of the restriction `a ∘ e` over the full pi space is
integrating it over the embedded pi space. The two steps are
`integral_pi_restrict` (the integrand does not see the other
coordinates) and the pi-congruence along the embedding
equivalence. -/
theorem integral_comp_emb (e : J → ι) (he : Function.Injective e)
    (F : (J → G) → ℂ) :
    (∫ a : ι → G, F (a ∘ e) ∂(Measure.pi fun _ : ι => μG))
      = ∫ α : J → G, F α ∂(Measure.pi fun _ : J => μG) := by
  classical
  have hcomp : ∀ a : ι → G, a ∘ e
      = (fun ℓ : ↥(Finset.image e Finset.univ) => a ℓ.1)
        ∘ (embEquiv e he) := by
    intro a
    funext j
    show a (e j) = a ((embEquiv e he) j).1
    rw [embEquiv_apply]
  rw [integral_congr_ae (ae_of_all _ fun a => by rw [hcomp a])]
  rw [integral_pi_restrict μG (Finset.image e Finset.univ)
    (fun v => F (v ∘ (embEquiv e he)))]
  have hE : ∀ α : J → G,
      (MeasurableEquiv.piCongrLeft
        (fun _ : ↥(Finset.image e Finset.univ) => G)
        (embEquiv e he)) α ∘ (embEquiv e he) = α := by
    intro α
    funext j
    exact MeasurableEquiv.piCongrLeft_apply_apply
      (β := fun _ : ↥(Finset.image e Finset.univ) => G)
      (embEquiv e he) α j
  have hmp := MeasureTheory.measurePreserving_piCongrLeft
    (μ := fun _ : ↥(Finset.image e Finset.univ) => μG)
    (f := embEquiv e he)
  rw [← hmp.integral_comp
    (MeasurableEquiv.piCongrLeft
      (fun _ : ↥(Finset.image e Finset.univ) => G)
      (embEquiv e he)).measurableEmbedding
    (fun v => F (v ∘ (embEquiv e he)))]
  apply integral_congr_ae
  exact ae_of_all _ fun α => congrArg F (hE α)

end Transport

section Kernel

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ)) {N : ℕ} [NeZero N]

/-- **The one-layer kernel `𝒜`** (Brick β2's object): the Haar
average over one layer's stratum of the one-layer Boltzmann
factor, as a kernel on pairs of layer data. **No positivity is
asserted**: `𝒜 ⪰ 0` is Brick β2, L+ / open. -/
noncomputable def layerKernel (β : ℝ) (u u' : LayerLink N → G) :
    ℂ :=
  ∫ α : LayerSite N → G, (Real.exp (-(layerAction ρ β α u u')) : ℂ)
    ∂(Measure.pi fun _ : LayerSite N => μG)

/-- **Top evaluation**: Brick β1's top factor is `𝒜` evaluated
at the top extractions, `𝒯(z,z′) = 𝒜(τ⁺z, τ⁺z′)`. -/
theorem planeCrossingTop_eq_layerKernel (hN : Even N) (β : ℝ)
    (z z' : ↥(posLinks (N := N)) → G) :
    planeCrossingTop μG ρ hN β z z'
      = layerKernel μG ρ β (tauTop hN z) (tauTop hN z') := by
  unfold planeCrossingTop layerKernel
  rw [integral_congr_ae (ae_of_all _ fun a => by
    rw [wilsonActionZeroTop_eq_layerAction ρ hN β z z' a (fun _ => 1)])]
  exact integral_comp_emb μG (embTop hN) (embTop_injective hN)
    (fun α => (Real.exp
      (-(layerAction ρ β α (tauTop hN z) (tauTop hN z'))) : ℂ))

/-- **Bottom evaluation**: Brick β1's bottom factor is `𝒜`
evaluated at the bottom extractions with the boundary data
exchanged, `ℬ(z,z′) = 𝒜(τ₀z′, τ₀z)` — the swap is β1's bottom
word. -/
theorem planeCrossingBot_eq_layerKernel (hN : Even N) (β : ℝ)
    (z z' : ↥(posLinks (N := N)) → G) :
    planeCrossingBot μG ρ hN β z z'
      = layerKernel μG ρ β (tauBot hN z') (tauBot hN z) := by
  unfold planeCrossingBot layerKernel
  rw [integral_congr_ae (ae_of_all _ fun a' => by
    rw [wilsonActionZeroBot_eq_layerAction ρ hN β z z'
      (fun _ => 1) a'])]
  exact integral_comp_emb μG (embBot hN) (embBot_injective hN)
    (fun α => (Real.exp
      (-(layerAction ρ β α (tauBot hN z') (tauBot hN z))) : ℂ))

/-- **Corollary — the single-𝒜 form of Brick β1's
factorization**: the crossing marginal is the product of two
evaluations of the one kernel `𝒜`, at the two boundary layers,
the bottom one with exchanged arguments. -/
theorem planeCrossingMarginal_layerKernel (hN : Even N) (β : ℝ)
    (z z' : ↥(posLinks (N := N)) → G) :
    planeCrossingMarginal μG ρ hN β z z'
      = layerKernel μG ρ β (tauTop hN z) (tauTop hN z')
        * layerKernel μG ρ β (tauBot hN z') (tauBot hN z) := by
  rw [planeCrossingMarginal_factor_top_bot μG ρ hN β z z',
    planeCrossingTop_eq_layerKernel μG ρ hN β z z',
    planeCrossingBot_eq_layerKernel μG ρ hN β z z']

/-- Per-coordinate inversion of the layer stratum — the in-cube
reflection of one layer. -/
def layerInv : (LayerSite N → G) → (LayerSite N → G) :=
  fun α c => (α c)⁻¹

theorem layerInv_involutive :
    Function.Involutive (layerInv (G := G) (N := N)) := by
  intro α
  funext c
  show ((α c)⁻¹)⁻¹ = α c
  exact inv_inv _

/-- The stratum inversion as a measurable equivalence. -/
def layerInvEquiv : (LayerSite N → G) ≃ᵐ (LayerSite N → G) :=
  { toEquiv := ⟨layerInv, layerInv, layerInv_involutive,
      layerInv_involutive⟩
    measurable_toFun := by
      rw [measurable_pi_iff]
      intro c
      show Measurable (fun α : LayerSite N → G => (α c)⁻¹)
      exact (measurable_pi_apply c).inv
    measurable_invFun := by
      rw [measurable_pi_iff]
      intro c
      show Measurable (fun α : LayerSite N → G => (α c)⁻¹)
      exact (measurable_pi_apply c).inv }

theorem measurePreserving_layerInvEquiv :
    MeasurePreserving layerInvEquiv
      (Measure.pi fun _ : LayerSite N => μG)
      (Measure.pi fun _ : LayerSite N => μG) := by
  refine measurePreserving_pi
    (f := fun (c : LayerSite N) (g : G) => g⁻¹)
    (fun _ : LayerSite N => μG) (fun _ : LayerSite N => μG) fun c => ?_
  show MeasurePreserving (fun g : G => g⁻¹) μG μG
  exact Measure.measurePreserving_inv μG

/-- **Density under stratum inversion**: inverting the stratum
exchanges the two boundary data of the one-layer density. The
mechanism is the two trace identities: with
`A = (α c)⁻¹ · u' ℓ · ((α (σ_ν c))⁻¹)⁻¹ · (u ℓ)⁻¹` the inverted
word and `B = α c · u ℓ · (α (σ_ν c))⁻¹ · (u' ℓ)⁻¹` the swapped
word, `A⁻¹` conjugated by `α c` is `B`, and the representation
trace sees neither inversion nor conjugation. -/
theorem layerDensity_inv (hN : Even N) (α : LayerSite N → G)
    (u u' : LayerLink N → G) (c : LayerSite N) (ν : Fin 4)
    (hν : ν ≠ 0) :
    plaquetteDensity (torusShift N) ρ
        (layerConfig (fun c => (α c)⁻¹) u u') c.1 0 ν
      = plaquetteDensity (torusShift N) ρ
          (layerConfig α u' u) c.1 0 ν := by
  have hw1 := plaquette_layerConfig hN (fun c => (α c)⁻¹) u u' c ν hν
  have hw2 := plaquette_layerConfig hN α u' u c ν hν
  have hinv : ((α c)⁻¹ * u' (layerLinkOf c ν hν)
        * ((α (layerShift ν hν c))⁻¹)⁻¹
        * (u (layerLinkOf c ν hν))⁻¹)⁻¹
      = u (layerLinkOf c ν hν) * (α (layerShift ν hν c))⁻¹
        * (u' (layerLinkOf c ν hν))⁻¹ * α c := by
    group
  have hA : (Matrix.trace (repMatrix ρ ((α c)⁻¹
        * u' (layerLinkOf c ν hν) * ((α (layerShift ν hν c))⁻¹)⁻¹
        * (u (layerLinkOf c ν hν))⁻¹))).re
      = (Matrix.trace (repMatrix ρ (α c * u (layerLinkOf c ν hν)
        * (α (layerShift ν hν c))⁻¹
        * (u' (layerLinkOf c ν hν))⁻¹))).re := by
    calc (Matrix.trace (repMatrix ρ ((α c)⁻¹
            * u' (layerLinkOf c ν hν) * ((α (layerShift ν hν c))⁻¹)⁻¹
            * (u (layerLinkOf c ν hν))⁻¹))).re
        = (Matrix.trace (repMatrix ρ (((α c)⁻¹
            * u' (layerLinkOf c ν hν) * ((α (layerShift ν hν c))⁻¹)⁻¹
            * (u (layerLinkOf c ν hν))⁻¹)⁻¹))).re :=
          (trace_repMatrix_inv ρ _).symm
      _ = (Matrix.trace (repMatrix ρ (α c * (((α c)⁻¹
            * u' (layerLinkOf c ν hν) * ((α (layerShift ν hν c))⁻¹)⁻¹
            * (u (layerLinkOf c ν hν))⁻¹)⁻¹) * (α c)⁻¹))).re := by
          rw [trace_repMatrix_conj]
      _ = (Matrix.trace (repMatrix ρ (α c * u (layerLinkOf c ν hν)
            * (α (layerShift ν hν c))⁻¹
            * (u' (layerLinkOf c ν hν))⁻¹))).re := by
          rw [hinv]
          congr 1
          group
  unfold plaquetteDensity
  rw [hw1, hw2]
  show 1 - (Matrix.trace (repMatrix ρ ((α c)⁻¹
        * u' (layerLinkOf c ν hν) * ((α (layerShift ν hν c))⁻¹)⁻¹
        * (u (layerLinkOf c ν hν))⁻¹))).re / (d : ℝ)
      = 1 - (Matrix.trace (repMatrix ρ (α c * u (layerLinkOf c ν hν)
        * (α (layerShift ν hν c))⁻¹
        * (u' (layerLinkOf c ν hν))⁻¹))).re / (d : ℝ)
  exact congrArg (fun t : ℝ => 1 - t / (d : ℝ)) hA

/-- **Action under stratum inversion**: the one-layer action of
the inverted stratum is the one-layer action with the boundary
data exchanged. -/
theorem layerAction_inv (hN : Even N) (β : ℝ) (α : LayerSite N → G)
    (u u' : LayerLink N → G) :
    layerAction ρ β (fun c => (α c)⁻¹) u u'
      = layerAction ρ β α u' u := by
  unfold layerAction
  congr 1
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro ν hν
  rw [Finset.mem_Ioi] at hν
  exact layerDensity_inv ρ hN α u u' c ν (ne_of_gt hν)

/-- **Per-stratum symmetry of `𝒜`**: `𝒜(u,u′) = 𝒜(u′,u)`, by
the stratum-inversion substitution in the Haar integral and
the density identity. -/
theorem layerKernel_symm (hN : Even N) (β : ℝ)
    (u u' : LayerLink N → G) :
    layerKernel μG ρ β u u' = layerKernel μG ρ β u' u := by
  have hsub : (∫ α : LayerSite N → G,
        (Real.exp (-(layerAction ρ β (layerInvEquiv α) u u')) : ℂ)
        ∂(Measure.pi fun _ : LayerSite N => μG))
      = ∫ α : LayerSite N → G,
        (Real.exp (-(layerAction ρ β α u u')) : ℂ)
        ∂(Measure.pi fun _ : LayerSite N => μG) :=
    (measurePreserving_layerInvEquiv μG).integral_comp
      (layerInvEquiv (G := G) (N := N)).measurableEmbedding
      (fun α => (Real.exp (-(layerAction ρ β α u u')) : ℂ))
  unfold layerKernel
  rw [← hsub]
  apply integral_congr_ae
  exact ae_of_all _ fun α => by
    show (Real.exp (-(layerAction ρ β (fun c => (α c)⁻¹) u u')) : ℂ)
      = (Real.exp (-(layerAction ρ β α u' u)) : ℂ)
    rw [layerAction_inv ρ hN]

end Kernel

end ThetLogos
