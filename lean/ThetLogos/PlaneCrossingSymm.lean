import ThetLogos.PlaneAvgKernel
import ThetLogos.LatticeGauge
import ThetLogos.LatticeReflection

/-!
# ThetLogos.PlaneCrossingSymm — Brick α: symmetries of the crossing marginal

**NO CLAIM. Parts of the Clay Yang–Mills statement closed by this
module: 0.** Core (H-PF) positivity at general `(G, ρ)` remains
**L+ / open** and is NOT claimed here. This module proves two
structural symmetries of the crossing marginal found by the
finite-seat computation of 2026-10-26
(`routeb-general-scratch/crossing-sign-seats-2026-10-26.md`, T4
evidence): symmetry in the two arguments, and invariance under
the diagonal gauge action. The theorems stand on proofs, not on
the computation.

## Identification — read this before citing anything here

The analyst's `M(z, z′)` IS this corpus's `planeCrossingMarginal`
(definitionally: the double plane-stratum Haar average of
`exp(−wilsonActionZero (planeAssemble ·))`), and the symmetry
proved below is the symmetry of that object.

The analyst's one-stratum factor `A` (with `M = A ⊙ A` at the
seat) is an **N = 2 seat object**: at the seat the crossing sum
splits by base time into two classes each seeing one plane
stratum, and the wrap at `N = 2` makes each class see both strict
halves. At general even `N` the corpus exposes no such
one-stratum factor: the crossing class (temporal plaquettes based
at times `N−1` and `N/2−1`) is not split by base time anywhere in
the corpus, and `planeAvgKernel_factor` exposes only `M` itself.
The Lean proof of `M`'s symmetry therefore does NOT factor through
an `A`; it goes through the reflection of the assembly plus the
Haar-inversion substitutions — the corpus packaging of the same
mechanism (inside `wilsonActionZero_reflConfig`, the trace
identity `Re tr ρ(P) = Re tr ρ(P⁻¹)`) the computation used.

## Gauge invariance — what is proved, and the named remainder

What is proved is the **diagonal** invariance: one gauge
transformation `g` of the assembled configuration, acting on the
first argument by the linkwise action and on the second argument
by its **mirror transport** (`gaugeMirrorPos`). The mirror
transport is forced: `z'` enters the assembly only through
`joinNeg`'s mirror formula, and the naive same-`g` linkwise
action on `z'` does NOT satisfy the assembly transport identity
(the mirror moves the base site).

**Named remainder (`Brick α-remainder`, open):** *separate*
gauge invariance — an independent gauge function per argument,
the seat-`A` property — and with it the (H-PF) reduction
corollary (the `K̄` pairing sees only gauge-averaged observables;
(H-PF) ⟺ positivity on gauge-invariant strict-half observables).
At general `N` the second argument is a mirrored copy, not an
honest half-configuration, and separate invariance is not the
diagonal statement proved here. Nothing in this module asserts
it.
-/

open MeasureTheory

namespace ThetLogos

section CrossingSymm

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ))
  {N : ℕ} [NeZero N]

/-! ## §1. The crossing action is gauge invariant -/

/-- **Gauge invariance of the crossing action `S₀`**: each
crossing plaquette density is gauge invariant
(`plaquette_gauge` + `trace_repMatrix_conj`), so the filtered
sum is. This is the `wilsonActionZero` analogue of
`wilsonAction_gauge_invariant`. -/
theorem wilsonActionZero_gauge_invariant (g : (Fin 4 → ZMod N) → G)
    (β : ℝ) (U : Config (Fin 4 → ZMod N) G) :
    wilsonActionZero ρ β (gaugeAction (torusShift N) g U)
      = wilsonActionZero ρ β U := by
  unfold wilsonActionZero
  congr 1
  refine Finset.sum_congr rfl fun p _ => ?_
  unfold plaquetteDensity
  rw [plaquette_gauge (torusShift N) (torusShift_comm N) g U p.1 p.2.1
    p.2.2, trace_repMatrix_conj]

/-! ## §2. Stratum gauge actions and the assembly transport -/

/-- The linkwise gauge value at a link `ℓ`: `g` at the base site,
the value, `g⁻¹` at the shifted site. -/
def gaugeLinkVal (g : (Fin 4 → ZMod N) → G) (ℓ : Link (Fin 4 → ZMod N))
    (v : G) : G :=
  g ℓ.1 * v * (g (torusShift N ℓ.2 ℓ.1))⁻¹

/-- The gauge action on a stratum function, coordinatewise through
a base map into links. -/
def gaugeStratumFun {ι : Type*} (base : ι → Link (Fin 4 → ZMod N))
    (g : (Fin 4 → ZMod N) → G) (v : ι → G) (m : ι) : G :=
  gaugeLinkVal g (base m) (v m)

/-- The linkwise gauge action on the first strict-half argument. -/
def gaugePosFun (g : (Fin 4 → ZMod N) → G)
    (z : ↥(posLinks (N := N)) → G) : ↥(posLinks (N := N)) → G :=
  gaugeStratumFun (fun m : ↥(posLinks (N := N)) => m.1) g z

/-- The linkwise gauge action on the closed half's plane stratum. -/
def gaugePlaneHalfFun (g : (Fin 4 → ZMod N) → G)
    (a : ↥(planeHalfLinks (N := N)) → G) :
    ↥(planeHalfLinks (N := N)) → G :=
  gaugeStratumFun (fun m : ↥(planeHalfLinks (N := N)) => m.1) g a

/-- The linkwise gauge action on the negative half's plane stratum. -/
def gaugePlaneNegFun (g : (Fin 4 → ZMod N) → G)
    (a' : ↥(planeNegLinks (N := N)) → G) :
    ↥(planeNegLinks (N := N)) → G :=
  gaugeStratumFun (fun m : ↥(planeNegLinks (N := N)) => m.1) g a'

/-- **The mirror transport of the gauge action to the second
argument.** `z'` enters the assembly through `joinNeg`'s mirror
formula (plainly in direction `≠ 0`, inverted in direction `0`),
so its gauge action is defined as the transport of the linkwise
action at the mirrored link `reflLink m.1`: the value that makes
the assembly transport identity (S4) true. -/
def gaugeMirrorPos (g : (Fin 4 → ZMod N) → G)
    (z' : ↥(posLinks (N := N)) → G) : ↥(posLinks (N := N)) → G :=
  fun m => if m.1.2 = 0
    then (gaugeLinkVal g (reflLink m.1) ((z' m)⁻¹))⁻¹
    else gaugeLinkVal g (reflLink m.1) (z' m)

theorem gaugeMirrorPos_of_snd_eq_zero (g : (Fin 4 → ZMod N) → G)
    (z' : ↥(posLinks (N := N)) → G) {m : ↥(posLinks (N := N))}
    (hm : m.1.2 = 0) :
    gaugeMirrorPos g z' m
      = (gaugeLinkVal g (reflLink m.1) ((z' m)⁻¹))⁻¹ := by
  unfold gaugeMirrorPos
  rw [if_pos hm]

theorem gaugeMirrorPos_of_snd_ne_zero (g : (Fin 4 → ZMod N) → G)
    (z' : ↥(posLinks (N := N)) → G) {m : ↥(posLinks (N := N))}
    (hm : m.1.2 ≠ 0) :
    gaugeMirrorPos g z' m
      = gaugeLinkVal g (reflLink m.1) (z' m) := by
  unfold gaugeMirrorPos
  rw [if_neg hm]

/-- **Assembly gauge transport**: a gauge transformation of the
assembled configuration is the assembly of the stratum-wise gauge
transforms — linkwise on `z`, `a`, `a'`, and mirror-transported
on `z'`. Checked stratum by stratum. -/
theorem gaugeAction_planeAssemble (hN : Even N)
    (g : (Fin 4 → ZMod N) → G)
    (z z' : ↥(posLinks (N := N)) → G)
    (a : ↥(planeHalfLinks (N := N)) → G)
    (a' : ↥(planeNegLinks (N := N)) → G) :
    gaugeAction (torusShift N) g (planeAssemble hN z z' a a')
      = planeAssemble hN (gaugePosFun g z) (gaugeMirrorPos g z')
          (gaugePlaneHalfFun g a) (gaugePlaneNegFun g a') := by
  funext ℓ
  rw [gaugeAction_apply]
  by_cases hhalf : ℓ ∈ halfLinks (N := N)
  · rw [show planeAssemble hN z z' a a' ℓ
          = joinHalf z a ⟨ℓ, hhalf⟩ from splitSymm_apply_mem _ _ hhalf,
        show planeAssemble hN (gaugePosFun g z) (gaugeMirrorPos g z')
            (gaugePlaneHalfFun g a) (gaugePlaneNegFun g a') ℓ
          = joinHalf (gaugePosFun g z) (gaugePlaneHalfFun g a)
              ⟨ℓ, hhalf⟩ from splitSymm_apply_mem _ _ hhalf]
    by_cases hpos : ℓ ∈ posLinks (N := N)
    · rw [joinHalf, dif_pos hpos, joinHalf, dif_pos hpos]
      rfl
    · rw [joinHalf, dif_neg hpos, joinHalf, dif_neg hpos]
      rfl
  · have hneg : ℓ ∈ negLinks (N := N) := Finset.mem_compl.mpr hhalf
    rw [show planeAssemble hN z z' a a' ℓ
          = joinNeg hN z' a' ⟨ℓ, hneg⟩ from
        splitSymm_apply_not_mem _ _ hneg,
        show planeAssemble hN (gaugePosFun g z) (gaugeMirrorPos g z')
            (gaugePlaneHalfFun g a) (gaugePlaneNegFun g a') ℓ
          = joinNeg hN (gaugeMirrorPos g z') (gaugePlaneNegFun g a')
              ⟨ℓ, hneg⟩ from splitSymm_apply_not_mem _ _ hneg]
    by_cases hpl : ℓ ∈ planeLinks (N := N)
    · rw [joinNeg_apply_plane hN _ _ hpl, joinNeg_apply_plane hN _ _ hpl]
      rfl
    · rw [joinNeg_apply_not_plane hN _ _ hpl,
        joinNeg_apply_not_plane hN _ _ hpl]
      split_ifs with hd
      · have hm0 : (⟨reflLink ℓ, reflLink_mem_posLinks hN hneg hpl⟩ :
            ↥(posLinks (N := N))).1.2 = 0 := hd
        rw [gaugeMirrorPos_of_snd_eq_zero _ _ hm0, inv_inv]
        show g ℓ.1
            * (z' ⟨reflLink ℓ, reflLink_mem_posLinks hN hneg hpl⟩)⁻¹
            * (g (torusShift N ℓ.2 ℓ.1))⁻¹
          = gaugeLinkVal g (reflLink (reflLink ℓ))
              ((z' ⟨reflLink ℓ, reflLink_mem_posLinks hN hneg hpl⟩)⁻¹)
        unfold gaugeLinkVal
        rw [congrArg Prod.fst (reflLink_involutive ℓ),
          congrArg Prod.snd (reflLink_involutive ℓ)]
      · have hm0 : (⟨reflLink ℓ, reflLink_mem_posLinks hN hneg hpl⟩ :
            ↥(posLinks (N := N))).1.2 ≠ 0 := hd
        rw [gaugeMirrorPos_of_snd_ne_zero _ _ hm0]
        show g ℓ.1
            * z' ⟨reflLink ℓ, reflLink_mem_posLinks hN hneg hpl⟩
            * (g (torusShift N ℓ.2 ℓ.1))⁻¹
          = gaugeLinkVal g (reflLink (reflLink ℓ))
              (z' ⟨reflLink ℓ, reflLink_mem_posLinks hN hneg hpl⟩)
        unfold gaugeLinkVal
        rw [congrArg Prod.fst (reflLink_involutive ℓ),
          congrArg Prod.snd (reflLink_involutive ℓ)]

/-! ## §3. The stratum gauge substitutions -/

/-- The stratum gauge map as a measurable equivalence of the
pi-Haar space: per-coordinate two-sided translation. -/
def gaugeStratumEquiv {ι : Type*} (base : ι → Link (Fin 4 → ZMod N))
    (g : (Fin 4 → ZMod N) → G) : (ι → G) ≃ᵐ (ι → G) where
  toFun := gaugeStratumFun base g
  invFun v m := (g (base m).1)⁻¹ * v m
    * g (torusShift N (base m).2 (base m).1)
  left_inv v := by
    funext m
    show (g (base m).1)⁻¹ * gaugeLinkVal g (base m) (v m)
        * g (torusShift N (base m).2 (base m).1) = v m
    unfold gaugeLinkVal
    simp [mul_assoc]
  right_inv v := by
    funext m
    show gaugeLinkVal g (base m)
        ((g (base m).1)⁻¹ * v m
          * g (torusShift N (base m).2 (base m).1)) = v m
    unfold gaugeLinkVal
    simp [mul_assoc]
  measurable_toFun := by
    refine measurable_pi_iff.mpr fun m => ?_
    show Measurable (fun v : ι → G => gaugeLinkVal g (base m) (v m))
    unfold gaugeLinkVal
    exact (measurable_const.mul (measurable_pi_apply m)).mul
      measurable_const
  measurable_invFun := by
    refine measurable_pi_iff.mpr fun m => ?_
    exact (measurable_const.mul (measurable_pi_apply m)).mul
      measurable_const

theorem measurePreserving_gaugeStratumEquiv {ι : Type*} [Fintype ι]
    (base : ι → Link (Fin 4 → ZMod N)) (g : (Fin 4 → ZMod N) → G) :
    MeasurePreserving (gaugeStratumEquiv base g)
      (Measure.pi fun _ : ι => μG) (Measure.pi fun _ : ι => μG) := by
  refine measurePreserving_pi
    (f := fun m v => gaugeLinkVal g (base m) v)
    (fun _ : ι => μG) (fun _ : ι => μG) fun m => ?_
  show MeasurePreserving (fun v : G => gaugeLinkVal g (base m) v) μG μG
  unfold gaugeLinkVal
  exact (measurePreserving_mul_right μG _).comp
    (measurePreserving_mul_left μG _)

/-- The gauge substitution on the closed half's plane stratum. -/
def gaugePlaneHalfEquiv (g : (Fin 4 → ZMod N) → G) :
    (↥(planeHalfLinks (N := N)) → G)
      ≃ᵐ (↥(planeHalfLinks (N := N)) → G) :=
  gaugeStratumEquiv (fun m : ↥(planeHalfLinks (N := N)) => m.1) g

/-- The gauge substitution on the negative half's plane stratum. -/
def gaugePlaneNegEquiv (g : (Fin 4 → ZMod N) → G) :
    (↥(planeNegLinks (N := N)) → G)
      ≃ᵐ (↥(planeNegLinks (N := N)) → G) :=
  gaugeStratumEquiv (fun m : ↥(planeNegLinks (N := N)) => m.1) g

theorem measurePreserving_gaugePlaneHalfEquiv
    (g : (Fin 4 → ZMod N) → G) :
    MeasurePreserving (gaugePlaneHalfEquiv g)
      (Measure.pi fun _ : ↥(planeHalfLinks (N := N)) => μG)
      (Measure.pi fun _ : ↥(planeHalfLinks (N := N)) => μG) :=
  measurePreserving_gaugeStratumEquiv μG _ g

theorem measurePreserving_gaugePlaneNegEquiv
    (g : (Fin 4 → ZMod N) → G) :
    MeasurePreserving (gaugePlaneNegEquiv g)
      (Measure.pi fun _ : ↥(planeNegLinks (N := N)) => μG)
      (Measure.pi fun _ : ↥(planeNegLinks (N := N)) => μG) :=
  measurePreserving_gaugeStratumEquiv μG _ g

/-! ## §4. Diagonal gauge invariance of the crossing marginal -/

/-- **Diagonal gauge invariance of the crossing marginal**: one
gauge transformation `g` of the assembled configuration, acting
linkwise on the first argument and by the mirror transport on
the second, leaves `planeCrossingMarginal` unchanged. The plane
strata are reparametrized by the stratum gauge substitutions,
which the pi-Haar measures absorb; the integrand is invariant by
§2 transport and §1. -/
theorem planeCrossingMarginal_gauge_invariant (hN : Even N) (β : ℝ)
    (g : (Fin 4 → ZMod N) → G)
    (z z' : ↥(posLinks (N := N)) → G) :
    planeCrossingMarginal μG ρ hN β (gaugePosFun g z)
        (gaugeMirrorPos g z')
      = planeCrossingMarginal μG ρ hN β z z' := by
  have hpt : ∀ (a : ↥(planeHalfLinks (N := N)) → G)
      (a' : ↥(planeNegLinks (N := N)) → G),
      (Real.exp (-(wilsonActionZero ρ β
        (planeAssemble hN (gaugePosFun g z) (gaugeMirrorPos g z')
          (gaugePlaneHalfEquiv g a) (gaugePlaneNegEquiv g a')))) : ℂ)
      = (Real.exp (-(wilsonActionZero ρ β
          (planeAssemble hN z z' a a'))) : ℂ) := by
    intro a a'
    have h1 : planeAssemble hN (gaugePosFun g z) (gaugeMirrorPos g z')
          (gaugePlaneHalfEquiv g a) (gaugePlaneNegEquiv g a')
        = gaugeAction (torusShift N) g (planeAssemble hN z z' a a') :=
      (gaugeAction_planeAssemble hN g z z' a a').symm
    rw [h1, wilsonActionZero_gauge_invariant ρ g β]
  calc planeCrossingMarginal μG ρ hN β (gaugePosFun g z)
          (gaugeMirrorPos g z')
      = ∫ a, ∫ a', (Real.exp (-(wilsonActionZero ρ β
            (planeAssemble hN (gaugePosFun g z) (gaugeMirrorPos g z')
              a (gaugePlaneNegEquiv g a')))) : ℂ)
          ∂(Measure.pi fun _ : ↥(planeNegLinks (N := N)) => μG)
          ∂(Measure.pi fun _ : ↥(planeHalfLinks (N := N)) => μG) := by
        unfold planeCrossingMarginal
        apply integral_congr_ae
        exact ae_of_all _ fun a =>
          ((measurePreserving_gaugePlaneNegEquiv μG g).integral_comp
            (gaugePlaneNegEquiv g).measurableEmbedding _).symm
    _ = ∫ a, ∫ a', (Real.exp (-(wilsonActionZero ρ β
            (planeAssemble hN (gaugePosFun g z) (gaugeMirrorPos g z')
              (gaugePlaneHalfEquiv g a)
              (gaugePlaneNegEquiv g a')))) : ℂ)
          ∂(Measure.pi fun _ : ↥(planeNegLinks (N := N)) => μG)
          ∂(Measure.pi fun _ : ↥(planeHalfLinks (N := N)) => μG) :=
        ((measurePreserving_gaugePlaneHalfEquiv μG g).integral_comp
          (gaugePlaneHalfEquiv g).measurableEmbedding _).symm
    _ = ∫ a, ∫ a', (Real.exp (-(wilsonActionZero ρ β
            (planeAssemble hN z z' a a'))) : ℂ)
          ∂(Measure.pi fun _ : ↥(planeNegLinks (N := N)) => μG)
          ∂(Measure.pi fun _ : ↥(planeHalfLinks (N := N)) => μG) := by
        exact integral_congr_ae (ae_of_all _ fun a =>
          integral_congr_ae (ae_of_all _ fun a' => hpt a a'))
    _ = planeCrossingMarginal μG ρ hN β z z' := rfl

/-! ## §5. Symmetry of the crossing marginal -/

/-- **Symmetry of the crossing marginal**: reflection of the
assembly with swapped halves, transported through the plane
strata by the inversion substitutions — the same mechanism as
`planeAvgKernel_symm`, applied to the crossing action via
`wilsonActionZero_reflConfig`. -/
theorem planeCrossingMarginal_symm (hN : Even N) (β : ℝ)
    (z z' : ↥(posLinks (N := N)) → G) :
    planeCrossingMarginal μG ρ hN β z z'
      = planeCrossingMarginal μG ρ hN β z' z := by
  have hpt : ∀ (a : ↥(planeHalfLinks (N := N)) → G)
      (a' : ↥(planeNegLinks (N := N)) → G),
      (Real.exp (-(wilsonActionZero ρ β
        (planeAssemble hN z' z (planeInvHalf a) (planeInvNeg a')))) : ℂ)
      = (Real.exp (-(wilsonActionZero ρ β
          (planeAssemble hN z z' a a'))) : ℂ) := by
    intro a a'
    rw [← planeAssemble_reflConfig hN z z' a a',
      wilsonActionZero_reflConfig ρ hN]
  symm
  calc planeCrossingMarginal μG ρ hN β z' z
      = ∫ a, ∫ a', (Real.exp (-(wilsonActionZero ρ β
            (planeAssemble hN z' z a (planeInvNeg a')))) : ℂ)
          ∂(Measure.pi fun _ : ↥(planeNegLinks (N := N)) => μG)
          ∂(Measure.pi fun _ : ↥(planeHalfLinks (N := N)) => μG) := by
        unfold planeCrossingMarginal
        apply integral_congr_ae
        exact ae_of_all _ fun a =>
          ((measurePreserving_planeInvNegEquiv μG).integral_comp
            planeInvNegEquiv.measurableEmbedding _).symm
    _ = ∫ a, ∫ a', (Real.exp (-(wilsonActionZero ρ β
            (planeAssemble hN z' z (planeInvHalf a)
              (planeInvNeg a')))) : ℂ)
          ∂(Measure.pi fun _ : ↥(planeNegLinks (N := N)) => μG)
          ∂(Measure.pi fun _ : ↥(planeHalfLinks (N := N)) => μG) :=
        ((measurePreserving_planeInvHalfEquiv μG).integral_comp
          planeInvHalfEquiv.measurableEmbedding _).symm
    _ = ∫ a, ∫ a', (Real.exp (-(wilsonActionZero ρ β
            (planeAssemble hN z z' a a'))) : ℂ)
          ∂(Measure.pi fun _ : ↥(planeNegLinks (N := N)) => μG)
          ∂(Measure.pi fun _ : ↥(planeHalfLinks (N := N)) => μG) := by
        exact integral_congr_ae (ae_of_all _ fun a =>
          integral_congr_ae (ae_of_all _ fun a' => hpt a a'))
    _ = planeCrossingMarginal μG ρ hN β z z' := rfl

/-- **Reality of the crossing marginal**: the integrand is
real-valued, so the marginal is a real number. -/
theorem planeCrossingMarginal_conj (hN : Even N) (β : ℝ)
    (z z' : ↥(posLinks (N := N)) → G) :
    (starRingEnd ℂ) (planeCrossingMarginal μG ρ hN β z z')
      = planeCrossingMarginal μG ρ hN β z z' := by
  unfold planeCrossingMarginal
  rw [starRingEnd_apply, RCLike.star_def, ← integral_conj]
  apply integral_congr_ae
  refine ae_of_all _ fun a => ?_
  dsimp only
  rw [← integral_conj]
  apply integral_congr_ae
  exact ae_of_all _ fun a' => by
    dsimp only
    rw [starRingEnd_apply, RCLike.star_def]
    exact RCLike.conj_ofReal _

/-- **Conjugate symmetry of the crossing marginal**: symmetry
composed with reality. -/
theorem planeCrossingMarginal_conj_symm (hN : Even N) (β : ℝ)
    (z z' : ↥(posLinks (N := N)) → G) :
    (starRingEnd ℂ) (planeCrossingMarginal μG ρ hN β z z')
      = planeCrossingMarginal μG ρ hN β z' z := by
  rw [planeCrossingMarginal_conj μG ρ hN β z z',
    planeCrossingMarginal_symm μG ρ hN β z z']

end CrossingSymm

end ThetLogos
