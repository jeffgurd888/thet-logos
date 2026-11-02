/-
# F2-GATE-2c engine: the splice / lift engine for the re-pinned gate

Brick F2-GATE-2c engine of the F2 weld line. The F2-W3 gate
was re-pinned at `4 ≤ N` (`ThetLogos.Span3SeatSchurGateRepin`).
Its decision lemma G2c
(`fiberAvgTop_gaugeInvariant_of_twirled_mul_pullback_gate4`)
is OPEN. This module is the ENGINE for its discharge:

* the splice API: `spliceTop` is the configuration appearing
  inside `fiberAvgTop`, named; its values at top links and
  off the top image are pinned (`spliceTop_apply_embLayerTop`,
  `spliceTop_apply_of_forall_ne`), and `fiberAvgTop` is the
  integral of an observable over splices
  (`fiberAvgTop_eq_spliceTop`);
* the disjointness lemma at `4 ≤ N`
  (`tauBot_spliceTop_of_four_le`): the bottom extraction of
  a top splice is the bottom extraction of the unspliced
  configuration, because the embeddings' time coordinates
  `N / 2 - 1 ≥ 1` and `0` are disjoint;
* the two gauge lifts: a layer gauge action `γ` lifts to
  config gauge functions supported at the top time layer
  (`layerGaugeLift`, pos action) resp. the reflected top
  time layer (`layerGaugeLiftMirror`, mirror action), under
  which the splice commutes with the gauge action
  (`spliceTop_gaugePosFun_lift`,
  `spliceTop_gaugeMirrorPos_lift`) and `tauBot` is invariant
  (`tauBot_gaugePosFun_lift`, `tauBot_gaugeMirrorPos_lift`).
  Together with the landed twirl invariances
  (`posGaugeAvg_gauge`, `mirrorGaugeAvg_gauge`) these finish
  the invariance steps the assembly brick consumes.

**Scope fence: this module decides neither G2c nor any gate
item — it is the splice/lift engine; G2c itself remains open
until the assembly brick.**

**NO CLAIM** — parts of any official Millennium statement
closed by this module: 0. Dials: 0/4. Even a completed gate
proves neither FACT nor clause (a). No Gram factorization
of `𝒜` appears or is used anywhere in this module: a Gram
factorization of `𝒜` itself is forbidden here.

This module is NOT in the root import list of the library;
it is verified by a targeted build.
-/

import ThetLogos.Span3SeatSchurGatePost

namespace ThetLogos

open MeasureTheory Finset
open scoped Matrix ENNReal NNReal

section Span3SeatSchurGateLift

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
  {N : ℕ} [NeZero N]

/-- **The top splice.** The configuration inside
`fiberAvgTop`, named: at links in the image of
`embLayerTop` it reads the layer datum `u` (transported
along the embedding), at all other strict-half links it
reads the complementary configuration `z`. -/
noncomputable def spliceTop (hN : Even N)
    (z : ↥(posLinks (N := N)) → G) (u : LayerLink N → G) :
    ↥(posLinks (N := N)) → G :=
  fun m => if h : ∃ ℓ, embLayerTop hN ℓ = m
    then u (Classical.choose h) else z m

/-- `fiberAvgTop` is the integral of the observable over
top splices. -/
theorem fiberAvgTop_eq_spliceTop (hN : Even N)
    (g : (↥(posLinks (N := N)) → G) → ℂ) (u : LayerLink N → G) :
    fiberAvgTop μG hN g u
      = ∫ z, g (spliceTop hN z u)
          ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG) := by
  rfl

/-- The splice at a top link is the layer datum. -/
theorem spliceTop_apply_embLayerTop (hN : Even N)
    (z : ↥(posLinks (N := N)) → G) (u : LayerLink N → G)
    (ℓ : LayerLink N) :
    spliceTop hN z u (embLayerTop hN ℓ) = u ℓ := by
  have hex : ∃ ℓ', embLayerTop hN ℓ' = embLayerTop hN ℓ := ⟨ℓ, rfl⟩
  unfold spliceTop
  rw [dif_pos hex]
  congr 1
  apply embLayerTop_injective hN
  exact Classical.choose_spec hex

/-- The splice off the top image is the complementary
configuration. -/
theorem spliceTop_apply_of_forall_ne (hN : Even N)
    (z : ↥(posLinks (N := N)) → G) (u : LayerLink N → G)
    {m : ↥(posLinks (N := N))}
    (hm : ∀ ℓ, embLayerTop hN ℓ ≠ m) :
    spliceTop hN z u m = z m := by
  unfold spliceTop
  rw [dif_neg (not_exists.mpr hm)]

/-- **Disjointness at `4 ≤ N`.** The bottom extraction of
a top splice is the bottom extraction of the unspliced
configuration: the top embedding's time coordinate
`N / 2 - 1 ≥ 1` is disjoint from the bottom embedding's
time coordinate `0`. -/
theorem tauBot_spliceTop_of_four_le (hN : Even N) (hN4 : 4 ≤ N)
    (z : ↥(posLinks (N := N)) → G) (u : LayerLink N → G) :
    tauBot hN (spliceTop hN z u) = tauBot hN z := by
  funext ℓ
  show spliceTop hN z u (embLayerBot hN ℓ) = z (embLayerBot hN ℓ)
  apply spliceTop_apply_of_forall_ne
  intro ℓ' hcon
  have hv : (topSite (⟨ℓ'.1.1, ℓ'.2.1⟩ : LayerSite N) 0).val
      = (ℓ.1.1 0).val :=
    congrArg (fun m : ↥(posLinks (N := N)) => (m.1.1 0).val) hcon
  have ht : (topSite (⟨ℓ'.1.1, ℓ'.2.1⟩ : LayerSite N) 0).val
      = N / 2 - 1 :=
    topSite_val _
  have hb : (ℓ.1.1 0).val = 0 := ℓ.2.1
  obtain ⟨k, hk⟩ := hN
  omega

/-- **The pos gauge lift.** A layer gauge function `γ`
lifted to a config gauge function supported at the top
time layer: at a site of time `N / 2 - 1` it reads `γ` at
the site with its time coordinate reset to `0`; elsewhere
it is `1`. -/
def layerGaugeLift (γ : (Fin 4 → ZMod N) → G) :
    (Fin 4 → ZMod N) → G :=
  fun x => if (x 0).val = N / 2 - 1 then γ (Function.update x 0 0)
    else 1

/-- The lift at a top site is `γ` at the layer site. -/
theorem layerGaugeLift_apply_topSite
    (γ : (Fin 4 → ZMod N) → G) (c : LayerSite N) :
    layerGaugeLift γ (topSite c) = γ c.1 := by
  unfold layerGaugeLift
  rw [if_pos (topSite_val c)]
  congr 1
  funext j
  by_cases hj : j = 0
  · subst hj
    rw [Function.update_self, layerSite_zero c]
  · rw [Function.update_of_ne hj, topSite_of_ne c hj]

/-- The lift at a spatially shifted top site is `γ` at
the shifted layer site. -/
theorem layerGaugeLift_apply_shift_topSite
    (γ : (Fin 4 → ZMod N) → G) {ν : Fin 4} (hν : ν ≠ 0)
    (c : LayerSite N) :
    layerGaugeLift γ (torusShift N ν (topSite c))
      = γ (torusShift N ν c.1) := by
  have hcond : (torusShift N ν (topSite c) 0).val = N / 2 - 1 := by
    rw [torusShift_apply_zero_of_ne hν]
    exact topSite_val c
  unfold layerGaugeLift
  rw [if_pos hcond]
  congr 1
  funext j
  by_cases hj : j = 0
  · subst hj
    rw [Function.update_self, torusShift_apply_zero_of_ne hν,
      layerSite_zero c]
  · rw [Function.update_of_ne hj, torusShift_apply_coord,
      torusShift_apply_coord, topSite_of_ne c hj]

/-- The lift is `1` off the top time layer. -/
theorem layerGaugeLift_apply_of_time_ne
    (γ : (Fin 4 → ZMod N) → G) {x : Fin 4 → ZMod N}
    (hx : (x 0).val ≠ N / 2 - 1) :
    layerGaugeLift γ x = 1 := by
  unfold layerGaugeLift
  rw [if_neg hx]

/-- `tauBot` is invariant under the pos gauge action of
the lift: both endpoint sites of a bottom link have time
`0 ≠ N / 2 - 1` at `4 ≤ N`, so the lift is `1` at both. -/
theorem tauBot_gaugePosFun_lift (hN : Even N) (hN4 : 4 ≤ N)
    (γ : (Fin 4 → ZMod N) → G) (z : ↥(posLinks (N := N)) → G) :
    tauBot hN (gaugePosFun (layerGaugeLift γ) z) = tauBot hN z := by
  funext ℓ
  have h1 : (ℓ.1.1 0).val ≠ N / 2 - 1 := by
    rw [ℓ.2.1]
    omega
  have h2 : ((torusShift N ℓ.1.2 ℓ.1.1) 0).val ≠ N / 2 - 1 := by
    rw [torusShift_apply_zero_of_ne ℓ.2.2]
    exact h1
  show gaugeLinkVal (layerGaugeLift γ) ℓ.1
      (z (embLayerBot hN ℓ)) = z (embLayerBot hN ℓ)
  unfold gaugeLinkVal
  rw [layerGaugeLift_apply_of_time_ne γ h1,
    layerGaugeLift_apply_of_time_ne γ h2, one_mul, inv_one, mul_one]

/-- **The splice commutes with the pos gauge action of
the lift**, the layer side carrying the layer gauge
action of `γ`. -/
theorem spliceTop_gaugePosFun_lift (hN : Even N)
    (γ : (Fin 4 → ZMod N) → G) (z : ↥(posLinks (N := N)) → G)
    (u : LayerLink N → G) :
    spliceTop hN (gaugePosFun (layerGaugeLift γ) z)
        (layerGaugeAction γ u)
      = gaugePosFun (layerGaugeLift γ) (spliceTop hN z u) := by
  funext m
  by_cases hex : ∃ ℓ, embLayerTop hN ℓ = m
  · obtain ⟨ℓ, rfl⟩ := hex
    rw [spliceTop_apply_embLayerTop]
    show layerGaugeAction γ u ℓ
      = gaugeLinkVal (layerGaugeLift γ) (embLayerTop hN ℓ).1
          (spliceTop hN z u (embLayerTop hN ℓ))
    rw [spliceTop_apply_embLayerTop]
    unfold layerGaugeAction gaugeStratumFun gaugeLinkVal
    show γ ℓ.1.1 * u ℓ * (γ (torusShift N ℓ.1.2 ℓ.1.1))⁻¹
      = layerGaugeLift γ (topSite ⟨ℓ.1.1, ℓ.2.1⟩) * u ℓ
        * (layerGaugeLift γ
            (torusShift N ℓ.1.2 (topSite ⟨ℓ.1.1, ℓ.2.1⟩)))⁻¹
    erw [layerGaugeLift_apply_topSite,
      layerGaugeLift_apply_shift_topSite γ ℓ.2.2]
  · have hm : ∀ ℓ, embLayerTop hN ℓ ≠ m := fun ℓ h => hex ⟨ℓ, h⟩
    rw [spliceTop_apply_of_forall_ne hN _ _ hm]
    show gaugeLinkVal (layerGaugeLift γ) m.1 (z m)
      = gaugeLinkVal (layerGaugeLift γ) m.1 (spliceTop hN z u m)
    rw [spliceTop_apply_of_forall_ne hN z u hm]

/-- **The mirror gauge lift.** A layer gauge function `γ`
lifted to a config gauge function supported at the
reflected top time layer (time `N / 2`): at a site of time
`N / 2` it reads `γ` at the site with its time coordinate
reset to `0`; elsewhere it is `1`. -/
def layerGaugeLiftMirror (γ : (Fin 4 → ZMod N) → G) :
    (Fin 4 → ZMod N) → G :=
  fun x => if (x 0).val = N / 2 then γ (Function.update x 0 0)
    else 1

/-- The reflected top site has time value `N / 2`. -/
theorem reflSite_topSite_time_val (hN : Even N) (c : LayerSite N) :
    ((reflSite (topSite c)) 0).val = N / 2 := by
  have htop : topSite c 0 = ((N / 2 - 1 : ℕ) : ZMod N) :=
    Function.update_self 0 _ _
  have h1 : reflSite (topSite c) 0
      = -1 - ((N / 2 - 1 : ℕ) : ZMod N) := by
    rw [reflSite_apply_self, htop]
  have hcast : ((N / 2 - 1 : ℕ) : ZMod N)
      = ((N / 2 : ℕ) : ZMod N) - 1 := by
    have hle : 1 ≤ N / 2 := by
      obtain ⟨k, hk⟩ := hN
      have hNpos : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
      omega
    rw [Nat.cast_sub hle, Nat.cast_one]
  have hneg : -((N / 2 : ℕ) : ZMod N) = ((N / 2 : ℕ) : ZMod N) := by
    have h2 : ((N / 2 : ℕ) : ZMod N) + ((N / 2 : ℕ) : ZMod N) = 0 := by
      have hcast2 : ((N / 2 : ℕ) : ZMod N) + ((N / 2 : ℕ) : ZMod N)
          = ((2 * (N / 2) : ℕ) : ZMod N) := by
        push_cast
        ring
      rw [hcast2]
      have hNN : 2 * (N / 2) = N := by
        obtain ⟨k, hk⟩ := hN
        omega
      rw [hNN]
      exact ZMod.natCast_self N
    exact neg_eq_of_add_eq_zero_left h2
  have heq : reflSite (topSite c) 0 = ((N / 2 : ℕ) : ZMod N) := by
    rw [h1, hcast]
    calc (-1 : ZMod N) - (((N / 2 : ℕ) : ZMod N) - 1)
        = -((N / 2 : ℕ) : ZMod N) := by ring
      _ = ((N / 2 : ℕ) : ZMod N) := hneg
  rw [heq]
  apply ZMod.val_natCast_of_lt
  obtain ⟨k, hk⟩ := hN
  have hNpos : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  omega

/-- The mirror lift at a reflected top site is `γ` at the
layer site. -/
theorem layerGaugeLiftMirror_apply_refl_topSite (hN : Even N)
    (γ : (Fin 4 → ZMod N) → G) (c : LayerSite N) :
    layerGaugeLiftMirror γ (reflSite (topSite c)) = γ c.1 := by
  unfold layerGaugeLiftMirror
  rw [if_pos (reflSite_topSite_time_val hN c)]
  congr 1
  funext j
  by_cases hj : j = 0
  · subst hj
    rw [Function.update_self, layerSite_zero c]
  · rw [Function.update_of_ne hj, reflSite_apply_of_ne _ hj,
      topSite_of_ne c hj]

/-- The mirror lift at a spatially shifted reflected top
site is `γ` at the shifted layer site. -/
theorem layerGaugeLiftMirror_apply_shift_refl_topSite (hN : Even N)
    (γ : (Fin 4 → ZMod N) → G) {ν : Fin 4} (hν : ν ≠ 0)
    (c : LayerSite N) :
    layerGaugeLiftMirror γ (torusShift N ν (reflSite (topSite c)))
      = γ (torusShift N ν c.1) := by
  have hcond : ((torusShift N ν (reflSite (topSite c))) 0).val
      = N / 2 := by
    rw [torusShift_apply_zero_of_ne hν]
    exact reflSite_topSite_time_val hN c
  unfold layerGaugeLiftMirror
  rw [if_pos hcond]
  congr 1
  funext j
  by_cases hj : j = 0
  · subst hj
    rw [Function.update_self, torusShift_apply_zero_of_ne hν,
      layerSite_zero c]
  · rw [Function.update_of_ne hj, torusShift_apply_coord,
      torusShift_apply_coord, reflSite_apply_of_ne _ hj,
      topSite_of_ne c hj]

/-- `tauBot` is invariant under the mirror gauge action
of the mirror lift: both endpoint sites of the reflected
bottom link have time value `N - 1 ≠ N / 2` at `4 ≤ N`, so
the lift is `1` at both. -/
theorem tauBot_gaugeMirrorPos_lift (hN : Even N) (hN4 : 4 ≤ N)
    (γ : (Fin 4 → ZMod N) → G) (z : ↥(posLinks (N := N)) → G) :
    tauBot hN (gaugeMirrorPos (layerGaugeLiftMirror γ) z)
      = tauBot hN z := by
  funext ℓ
  have hdir : (embLayerBot hN ℓ).1.2 ≠ 0 := ℓ.2.2
  have hval : ((reflSite ℓ.1.1) 0).val = N - 1 := by
    rw [reflSite_val_zero, ℓ.2.1, Nat.sub_zero]
  have h1 : layerGaugeLiftMirror γ (reflSite ℓ.1.1) = 1 := by
    unfold layerGaugeLiftMirror
    exact if_neg (by rw [hval]; omega)
  have h2 : layerGaugeLiftMirror γ
      (torusShift N ℓ.1.2 (reflSite ℓ.1.1)) = 1 := by
    unfold layerGaugeLiftMirror
    exact if_neg (by
      rw [torusShift_apply_zero_of_ne ℓ.2.2, hval]; omega)
  show gaugeMirrorPos (layerGaugeLiftMirror γ) z (embLayerBot hN ℓ)
    = z (embLayerBot hN ℓ)
  rw [gaugeMirrorPos_of_snd_ne_zero _ _ hdir]
  show gaugeLinkVal (layerGaugeLiftMirror γ) (reflLink ℓ.1)
      (z (embLayerBot hN ℓ)) = z (embLayerBot hN ℓ)
  rw [show reflLink ℓ.1 = (reflSite ℓ.1.1, ℓ.1.2)
    from reflLink_of_ne ℓ.2.2]
  unfold gaugeLinkVal
  rw [h1, h2, one_mul, inv_one, mul_one]

/-- **The splice commutes with the mirror gauge action
of the mirror lift**, the layer side carrying the layer
gauge action of `γ`. -/
theorem spliceTop_gaugeMirrorPos_lift (hN : Even N)
    (γ : (Fin 4 → ZMod N) → G) (z : ↥(posLinks (N := N)) → G)
    (u : LayerLink N → G) :
    spliceTop hN (gaugeMirrorPos (layerGaugeLiftMirror γ) z)
        (layerGaugeAction γ u)
      = gaugeMirrorPos (layerGaugeLiftMirror γ)
          (spliceTop hN z u) := by
  funext m
  by_cases hex : ∃ ℓ, embLayerTop hN ℓ = m
  · obtain ⟨ℓ, rfl⟩ := hex
    rw [spliceTop_apply_embLayerTop]
    have hdir : (embLayerTop hN ℓ).1.2 ≠ 0 := ℓ.2.2
    show layerGaugeAction γ u ℓ
      = gaugeMirrorPos (layerGaugeLiftMirror γ) (spliceTop hN z u)
          (embLayerTop hN ℓ)
    rw [gaugeMirrorPos_of_snd_ne_zero _ _ hdir]
    show layerGaugeAction γ u ℓ
      = gaugeLinkVal (layerGaugeLiftMirror γ)
          (reflLink (embLayerTop hN ℓ).1)
          (spliceTop hN z u (embLayerTop hN ℓ))
    rw [spliceTop_apply_embLayerTop,
      show reflLink (embLayerTop hN ℓ).1
          = (reflSite (topSite ⟨ℓ.1.1, ℓ.2.1⟩), ℓ.1.2)
        from reflLink_of_ne ℓ.2.2]
    unfold layerGaugeAction gaugeStratumFun gaugeLinkVal
    show γ ℓ.1.1 * u ℓ * (γ (torusShift N ℓ.1.2 ℓ.1.1))⁻¹
      = layerGaugeLiftMirror γ (reflSite (topSite ⟨ℓ.1.1, ℓ.2.1⟩))
          * u ℓ
        * (layerGaugeLiftMirror γ
            (torusShift N ℓ.1.2
              (reflSite (topSite ⟨ℓ.1.1, ℓ.2.1⟩))))⁻¹
    erw [layerGaugeLiftMirror_apply_refl_topSite hN,
      layerGaugeLiftMirror_apply_shift_refl_topSite hN γ ℓ.2.2]
  · have hm : ∀ ℓ, embLayerTop hN ℓ ≠ m := fun ℓ h => hex ⟨ℓ, h⟩
    rw [spliceTop_apply_of_forall_ne hN _ _ hm]
    by_cases hdir : m.1.2 = 0
    · rw [gaugeMirrorPos_of_snd_eq_zero _ _ hdir,
        gaugeMirrorPos_of_snd_eq_zero _ _ hdir,
        spliceTop_apply_of_forall_ne hN z u hm]
    · rw [gaugeMirrorPos_of_snd_ne_zero _ _ hdir,
        gaugeMirrorPos_of_snd_ne_zero _ _ hdir,
        spliceTop_apply_of_forall_ne hN z u hm]

end Span3SeatSchurGateLift

end ThetLogos
