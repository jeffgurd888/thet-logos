import ThetLogos.PlaneCrossingSymm

/-!
# ThetLogos.PlaneCrossingSeparate — Brick α-remainder: separate gauge
invariance of the crossing marginal

**NO CLAIM. Parts of the Clay Yang–Mills statement closed by this
module: 0.** Core (H-PF) positivity at general `(G, ρ)` remains
**L+ / open** and is NOT claimed here — this brick is invariance and
reduction only, no positivity anywhere.

## What Brick α left, and what lands here

Brick α (`PlaneCrossingSymm`) proved the **diagonal** invariance of
`planeCrossingMarginal`: one gauge function acting on both arguments
(the second through the mirror transport `gaugeMirrorPos`), and
named the remainder: **separate** invariance — an independent gauge
function per argument — plus the (H-PF) reduction corollary.

Separate invariance holds, and the decoupling is *not* in the strata
substitutions (those were already stratum-local in α). It is one
level up, at the sites: the reflection is **between-sites**
(`reflSite` sends time `t ↦ −1 − t`; it has no fixed sites), so

- `gaugePosFun G z` reads `G` only at sites of time `< N / 2`
  (base and head of a strict-half link both lie in the closed half;
  the head of a time link based at `N / 2 − 1` would leave it, but
  that link is a plane link, excluded from `posLinks`), while
- `gaugeMirrorPos G z'` reads `G` only at sites of time `≥ N / 2`
  (base and head of the reflected link: the corpus's
  `reflLink_fst_zero_val_*` give times `N − 1 − t` and `N − 2 − t`).

The two actions therefore read **disjoint site sets**. Gluing `g`
(on the closed half's sites) and `h` (on the negative half's sites)
into one gauge function `gaugeGlued g h`, α's diagonal theorem
applied to the glued function *is* separate invariance (§2). The
same glue gives separate invariance of the half action and of the
plane-averaged kernel `K̄` (§3–§4), and the pairing of `K̄` is then
invariant under independent gauge transformations of its two
observable slots (§5). §6 defines the two gauge averages (Haar
averages over the gauge group of each slot's action) and proves the
reduction the corpus supports: the pairing of the averages equals
the pairing — the pairing sees only gauge-averaged observables.
-/

open MeasureTheory

namespace ThetLogos

section CrossingSeparate

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ))
  {N : ℕ} [NeZero N]

/-! ## §0. Site-time facts: the two actions read disjoint sites -/

/-- Value of `a + 1` in `ZMod N` when no wrap occurs. -/
theorem val_add_one (a : ZMod N) (h : a.val + 1 < N) :
    (a + 1).val = a.val + 1 := by
  have h1 : (1 : ZMod N) = ((1 : ℕ) : ZMod N) := by simp
  rw [h1]
  rw [ZMod.val_add_of_lt]
  · congr 2
    rw [ZMod.val_natCast]
    exact Nat.mod_eq_of_lt (by omega)
  · rw [ZMod.val_natCast]
    have : 1 % N = 1 := Nat.mod_eq_of_lt (by omega)
    omega

/-- A strict-half **time** link's base time is at most `N / 2 - 2`
(stated in the subtraction-free form `(x 0).val + 2 ≤ N / 2`,
which stays honest at `N = 2`): base time `N / 2 - 1` would make
it a plane link (a time link there is fixed by the reflection,
`reflLink_eq_self_iff`), and `posLinks` excludes plane links.
(Spatial links may sit at `N / 2 - 1`; only the time-link case
needs the bound.) -/
theorem posLink_time_link_le_sub_two (hN : Even N)
    {x : Fin 4 → ZMod N} (hℓ : (x, 0) ∈ posLinks (N := N)) :
    (x 0).val + 2 ≤ N / 2 := by
  have hbase : (x 0).val < N / 2 := (mem_posLinks.mp hℓ).1
  by_contra hcon
  push_neg at hcon
  have hval : (x 0).val = N / 2 - 1 := by omega
  exact (mem_posLinks.mp hℓ).2
    ((reflLink_eq_self_iff hN x 0).mpr ⟨rfl, Or.inl hval⟩)

/-- The head site of a strict-half link still has time `< N / 2`:
a spatial shift does not move time, and a time link in `posLinks`
is based at time `≤ N / 2 - 2`, so its head is at `≤ N / 2 - 1`. -/
theorem posLink_head_time_lt (hN : Even N) {x : Fin 4 → ZMod N}
    {μ : Fin 4} (hℓ : (x, μ) ∈ posLinks (N := N)) :
    ((torusShift N μ x) 0).val < N / 2 := by
  have hbase : (x 0).val < N / 2 := (mem_posLinks.mp hℓ).1
  have hN2 : 2 ≤ N := two_le_of_even hN
  obtain ⟨k, hk⟩ := hN
  have hdiv : N / 2 = k := by
    rw [hk]
    omega
  by_cases hμ : μ = 0
  · subst hμ
    have hle := posLink_time_link_le_sub_two ⟨k, hk⟩ hℓ
    have hshift : torusShift N 0 x 0 = x 0 + 1 := by
      rw [torusShift_apply_coord, Pi.single_eq_same, add_comm]
    have hval : ((x 0 + 1).val) = (x 0).val + 1 :=
      val_add_one _ (by omega)
    rw [hshift, hval]
    omega
  · rw [torusShift_apply_zero_of_ne hμ]
    exact hbase

/-- The base site of a reflected strict-half link has time
`≥ N / 2` (corpus values: `N - 1 - t` spatial, `N - 2 - t` time). -/
theorem reflLink_posLink_base_time_ge (hN : Even N)
    {x : Fin 4 → ZMod N} {μ : Fin 4}
    (hℓ : (x, μ) ∈ posLinks (N := N)) :
    N / 2 ≤ ((reflLink (x, μ)).1 0).val := by
  have hbase : (x 0).val < N / 2 := (mem_posLinks.mp hℓ).1
  have hN2 : 2 ≤ N := two_le_of_even hN
  obtain ⟨k, hk⟩ := hN
  have hdiv : N / 2 = k := by
    rw [hk]
    omega
  by_cases hμ : μ = 0
  · subst hμ
    have hle := posLink_time_link_le_sub_two ⟨k, hk⟩ hℓ
    have hv2 : (x 0).val ≤ N - 2 := by omega
    have hval := reflLink_fst_zero_val_zero (x := x) hv2 hN2
    rw [hval]
    omega
  · have hval := reflLink_fst_zero_val_of_ne (x := x) hμ
    omega

/-- The head site of a reflected strict-half link has time
`≥ N / 2`: spatial shifts fix time; a reflected time link's head
has value `(N - 2 - t) + 1 = N - 1 - t`. -/
theorem reflLink_posLink_head_time_ge (hN : Even N)
    {x : Fin 4 → ZMod N} {μ : Fin 4}
    (hℓ : (x, μ) ∈ posLinks (N := N)) :
    N / 2 ≤ ((torusShift N (reflLink (x, μ)).2 (reflLink (x, μ)).1)
      0).val := by
  have hbase : (x 0).val < N / 2 := (mem_posLinks.mp hℓ).1
  have hN2 : 2 ≤ N := two_le_of_even hN
  obtain ⟨k, hk⟩ := hN
  have hdiv : N / 2 = k := by
    rw [hk]
    omega
  rw [reflLink_snd]
  by_cases hμ : μ = 0
  · subst hμ
    have hshift : torusShift N 0 (reflLink (x, 0)).1 0
        = (reflLink (x, 0)).1 0 + 1 := by
      rw [torusShift_apply_coord, Pi.single_eq_same, add_comm]
    have hv2 : (x 0).val ≤ N - 2 := by omega
    have hval := reflLink_fst_zero_val_zero (x := x) hv2 hN2
    rw [hshift, val_add_one _ (by omega)]
    omega
  · rw [torusShift_apply_zero_of_ne hμ]
    exact reflLink_posLink_base_time_ge ⟨k, hk⟩ hℓ

/-! ## §1. The glued gauge function and the identifications -/

/-- **The glued gauge function**: `g` on the closed half's sites
(time `< N / 2`), `h` on the negative half's sites. -/
def gaugeGlued (g h : (Fin 4 → ZMod N) → G) : (Fin 4 → ZMod N) → G :=
  fun x => if (x 0).val < N / 2 then g x else h x

/-- The glued function acts on the first argument exactly as `g`:
`gaugePosFun` reads only closed-half sites. -/
theorem gaugePosFun_glued (hN : Even N) (g h : (Fin 4 → ZMod N) → G)
    (z : ↥(posLinks (N := N)) → G) :
    gaugePosFun (gaugeGlued g h) z = gaugePosFun g z := by
  funext m
  show gaugeLinkVal (gaugeGlued g h) m.1 (z m)
    = gaugeLinkVal g m.1 (z m)
  unfold gaugeLinkVal gaugeGlued
  rw [if_pos (mem_posLinks.mp m.2).1,
    if_pos (posLink_head_time_lt hN m.2)]

/-- The glued function acts on the second argument exactly as `h`:
`gaugeMirrorPos` reads only negative-half sites. -/
theorem gaugeMirrorPos_glued (hN : Even N)
    (g h : (Fin 4 → ZMod N) → G)
    (z' : ↥(posLinks (N := N)) → G) :
    gaugeMirrorPos (gaugeGlued g h) z' = gaugeMirrorPos h z' := by
  funext m
  have hbase : ¬ ((reflLink m.1).1 0).val < N / 2 :=
    Nat.not_lt.mpr (reflLink_posLink_base_time_ge hN m.2)
  have hhead : ¬ ((torusShift N (reflLink m.1).2 (reflLink m.1).1)
      0).val < N / 2 :=
    Nat.not_lt.mpr (reflLink_posLink_head_time_ge hN m.2)
  have hlink : gaugeLinkVal (gaugeGlued g h) (reflLink m.1)
      = gaugeLinkVal h (reflLink m.1) := by
    funext v
    show gaugeLinkVal (gaugeGlued g h) (reflLink m.1) v
      = gaugeLinkVal h (reflLink m.1) v
    unfold gaugeLinkVal gaugeGlued
    rw [if_neg hbase, if_neg hhead]
  by_cases hm : m.1.2 = 0
  · rw [gaugeMirrorPos_of_snd_eq_zero _ _ hm,
      gaugeMirrorPos_of_snd_eq_zero _ _ hm, hlink]
  · rw [gaugeMirrorPos_of_snd_ne_zero _ _ hm,
      gaugeMirrorPos_of_snd_ne_zero _ _ hm, hlink]

/-! ## §2. Separate gauge invariance of the crossing marginal -/

/-- **Separate gauge invariance of the crossing marginal**
(the α-remainder headline): independent gauge functions per
argument — `g` linkwise on `z`, `h` through the mirror transport
on `z'` — leave `planeCrossingMarginal` unchanged. Proved by
gluing `g, h` into one gauge function (§1: the two actions read
disjoint site sets) and applying Brick α's diagonal invariance
to the glued function. -/
theorem planeCrossingMarginal_gauge_invariant_separate (hN : Even N)
    (β : ℝ) (g h : (Fin 4 → ZMod N) → G)
    (z z' : ↥(posLinks (N := N)) → G) :
    planeCrossingMarginal μG ρ hN β (gaugePosFun g z)
        (gaugeMirrorPos h z')
      = planeCrossingMarginal μG ρ hN β z z' := by
  have key := planeCrossingMarginal_gauge_invariant μG ρ hN β
    (gaugeGlued g h) z z'
  rwa [gaugePosFun_glued hN g h z, gaugeMirrorPos_glued hN g h z']
    at key

/-- The trivial gauge function acts trivially on the first
argument. -/
theorem gaugePosFun_one (z : ↥(posLinks (N := N)) → G) :
    gaugePosFun (1 : (Fin 4 → ZMod N) → G) z = z := by
  funext m
  show gaugeLinkVal (1 : (Fin 4 → ZMod N) → G) m.1 (z m) = z m
  unfold gaugeLinkVal
  simp

/-- The trivial gauge function acts trivially through the mirror
transport. -/
theorem gaugeMirrorPos_one (z' : ↥(posLinks (N := N)) → G) :
    gaugeMirrorPos (1 : (Fin 4 → ZMod N) → G) z' = z' := by
  funext m
  by_cases hm : m.1.2 = 0
  · rw [gaugeMirrorPos_of_snd_eq_zero _ _ hm]
    show (gaugeLinkVal (1 : (Fin 4 → ZMod N) → G) (reflLink m.1)
      ((z' m)⁻¹))⁻¹ = z' m
    unfold gaugeLinkVal
    simp
  · rw [gaugeMirrorPos_of_snd_ne_zero _ _ hm]
    show gaugeLinkVal (1 : (Fin 4 → ZMod N) → G) (reflLink m.1)
      (z' m) = z' m
    unfold gaugeLinkVal
    simp

/-- Separate invariance in the first argument alone. -/
theorem planeCrossingMarginal_gauge_invariant_fst (hN : Even N)
    (β : ℝ) (g : (Fin 4 → ZMod N) → G)
    (z z' : ↥(posLinks (N := N)) → G) :
    planeCrossingMarginal μG ρ hN β (gaugePosFun g z) z'
      = planeCrossingMarginal μG ρ hN β z z' := by
  have key := planeCrossingMarginal_gauge_invariant_separate μG ρ
    hN β g (1 : (Fin 4 → ZMod N) → G) z z'
  rwa [gaugeMirrorPos_one] at key

/-- Separate invariance in the second argument alone. -/
theorem planeCrossingMarginal_gauge_invariant_snd (hN : Even N)
    (β : ℝ) (h : (Fin 4 → ZMod N) → G)
    (z z' : ↥(posLinks (N := N)) → G) :
    planeCrossingMarginal μG ρ hN β z (gaugeMirrorPos h z')
      = planeCrossingMarginal μG ρ hN β z z' := by
  have key := planeCrossingMarginal_gauge_invariant_separate μG ρ
    hN β (1 : (Fin 4 → ZMod N) → G) h z z'
  rwa [gaugePosFun_one] at key

/-! ## §3. Half-action invariances -/

/-- **Gauge invariance of the positive half-action**: the
`wilsonActionPlus` analogue of α's §1 (each positive-class
plaquette density is gauge invariant). -/
theorem wilsonActionPlus_gauge_invariant (g : (Fin 4 → ZMod N) → G)
    (β : ℝ) (U : Config (Fin 4 → ZMod N) G) :
    wilsonActionPlus ρ β (gaugeAction (torusShift N) g U)
      = wilsonActionPlus ρ β U := by
  unfold wilsonActionPlus
  congr 1
  refine Finset.sum_congr rfl fun p _ => ?_
  unfold plaquetteDensity
  rw [plaquette_gauge (torusShift N) (torusShift_comm N) g U p.1
    p.2.1 p.2.2, trace_repMatrix_conj]

/-- **Gauge invariance of the negative half-action**. -/
theorem wilsonActionMinus_gauge_invariant (g : (Fin 4 → ZMod N) → G)
    (β : ℝ) (U : Config (Fin 4 → ZMod N) G) :
    wilsonActionMinus ρ β (gaugeAction (torusShift N) g U)
      = wilsonActionMinus ρ β U := by
  unfold wilsonActionMinus
  congr 1
  refine Finset.sum_congr rfl fun p _ => ?_
  unfold plaquetteDensity
  rw [plaquette_gauge (torusShift N) (torusShift_comm N) g U p.1
    p.2.1 p.2.2, trace_repMatrix_conj]

/-- The half action is invariant under the first argument's gauge
action: on `posLinks`, `extendP (gaugePosFun g z)` agrees with the
full gauge transform of `extendP z` by the glued function
`gaugeGlued g 1` (§1 glue: the glued function is `g` at every site
a strict-half link reads), and `S₊` depends only on `posLinks`
values and is gauge invariant. -/
theorem halfActionP_gaugePosFun (hN : Even N) (β : ℝ)
    (g : (Fin 4 → ZMod N) → G) (z : ↥(posLinks (N := N)) → G) :
    halfActionP ρ β (gaugePosFun g z) = halfActionP ρ β z := by
  unfold halfActionP
  refine (wilsonActionPlus_eq_of_agree_posLinks ρ hN ?_ β).trans
    (wilsonActionPlus_gauge_invariant ρ (gaugeGlued g 1) β
      (extendP z))
  intro ℓ hℓ
  rw [gaugeAction_apply, extendP_apply hℓ, extendP_apply hℓ]
  show gaugeLinkVal g ℓ (z ⟨ℓ, hℓ⟩)
      = gaugeLinkVal (gaugeGlued g 1) ℓ (z ⟨ℓ, hℓ⟩)
  unfold gaugeLinkVal gaugeGlued
  rw [if_pos (mem_posLinks.mp hℓ).1,
    if_pos (posLink_head_time_lt hN hℓ)]

/-- The half action of any assembled configuration, read through
the mirror, depends only on the second argument. -/
theorem wilsonActionMinus_planeAssemble (hN : Even N) (β : ℝ)
    (z₀ : ↥(posLinks (N := N)) → G)
    (a₀ : ↥(planeHalfLinks (N := N)) → G)
    (a₀' : ↥(planeNegLinks (N := N)) → G)
    (w : ↥(posLinks (N := N)) → G) :
    wilsonActionMinus ρ β (planeAssemble hN z₀ w a₀ a₀')
      = halfActionP ρ β w := by
  rw [wilsonActionMinus_eq_halfActionP ρ hN β _]
  congr 1
  rw [show (fun m : ↥(negLinks (N := N)) =>
        planeAssemble hN z₀ w a₀ a₀' m.1)
      = joinNeg hN w a₀' from
    funext fun m => splitSymm_apply_not_mem _ _ m.2,
    mirrorP_joinNeg]

/-- The half action is invariant under the second argument's
mirror gauge action: transport the assembly by the glued function
`gaugeGlued 1 h` (α's transport identity), use §1's mirror
identification and `S₋` gauge invariance, and read `S₋` of an
assembly through the mirror. -/
theorem halfActionP_gaugeMirrorPos (hN : Even N) (β : ℝ)
    (h : (Fin 4 → ZMod N) → G) (z' : ↥(posLinks (N := N)) → G) :
    halfActionP ρ β (gaugeMirrorPos h z') = halfActionP ρ β z' := by
  calc halfActionP ρ β (gaugeMirrorPos h z')
      = wilsonActionMinus ρ β
          (planeAssemble hN (gaugePosFun (gaugeGlued
              (1 : (Fin 4 → ZMod N) → G) h) (fun _ => 1))
            (gaugeMirrorPos (gaugeGlued
              (1 : (Fin 4 → ZMod N) → G) h) z')
            (gaugePlaneHalfFun (gaugeGlued
              (1 : (Fin 4 → ZMod N) → G) h) (fun _ => 1))
            (gaugePlaneNegFun (gaugeGlued
              (1 : (Fin 4 → ZMod N) → G) h) (fun _ => 1))) := by
        rw [gaugeMirrorPos_glued hN (1 : (Fin 4 → ZMod N) → G) h z']
        exact (wilsonActionMinus_planeAssemble ρ hN β _ _ _ _).symm
    _ = wilsonActionMinus ρ β (gaugeAction (torusShift N)
          (gaugeGlued (1 : (Fin 4 → ZMod N) → G) h)
          (planeAssemble hN (fun _ => 1) z' (fun _ => 1)
            (fun _ => 1))) := by
        rw [gaugeAction_planeAssemble]
    _ = wilsonActionMinus ρ β
          (planeAssemble hN (fun _ => 1) z' (fun _ => 1)
            (fun _ => 1)) :=
        wilsonActionMinus_gauge_invariant ρ _ β _
    _ = halfActionP ρ β z' :=
        wilsonActionMinus_planeAssemble ρ hN β _ _ _ _

/-! ## §4. Separate gauge invariance of the plane-averaged kernel -/

/-- **Separate gauge invariance of `K̄`**: by the factorization
`planeAvgKernel_factor`, the kernel is the product of the two
half-action weights and the crossing marginal, each separately
invariant (§2, §3). -/
theorem planeAvgKernel_gauge_invariant_separate (hN : Even N)
    (β : ℝ) (g h : (Fin 4 → ZMod N) → G)
    (z z' : ↥(posLinks (N := N)) → G) :
    planeAvgKernel μG ρ hN β (gaugePosFun g z) (gaugeMirrorPos h z')
      = planeAvgKernel μG ρ hN β z z' := by
  rw [planeAvgKernel_factor, planeAvgKernel_factor,
    halfActionP_gaugePosFun ρ hN β g z,
    halfActionP_gaugeMirrorPos ρ hN β h z',
    planeCrossingMarginal_gauge_invariant_separate μG ρ hN β g h
      z z']

/-- Separate invariance of `K̄` in the first argument alone. -/
theorem planeAvgKernel_gauge_invariant_fst (hN : Even N) (β : ℝ)
    (g : (Fin 4 → ZMod N) → G)
    (z z' : ↥(posLinks (N := N)) → G) :
    planeAvgKernel μG ρ hN β (gaugePosFun g z) z'
      = planeAvgKernel μG ρ hN β z z' := by
  have key := planeAvgKernel_gauge_invariant_separate μG ρ hN β g
    (1 : (Fin 4 → ZMod N) → G) z z'
  rwa [gaugeMirrorPos_one] at key

/-- Separate invariance of `K̄` in the second argument alone. -/
theorem planeAvgKernel_gauge_invariant_snd (hN : Even N) (β : ℝ)
    (h : (Fin 4 → ZMod N) → G)
    (z z' : ↥(posLinks (N := N)) → G) :
    planeAvgKernel μG ρ hN β z (gaugeMirrorPos h z')
      = planeAvgKernel μG ρ hN β z z' := by
  have key := planeAvgKernel_gauge_invariant_separate μG ρ hN β
    (1 : (Fin 4 → ZMod N) → G) h z z'
  rwa [gaugePosFun_one] at key

/-! ## §5. The K̄ pairing and its slot-wise gauge invariance -/

/-- Composition law for the first argument's action. -/
theorem gaugePosFun_mul (a b : (Fin 4 → ZMod N) → G)
    (z : ↥(posLinks (N := N)) → G) :
    gaugePosFun (a * b) z = gaugePosFun a (gaugePosFun b z) := by
  funext m
  show gaugeLinkVal (a * b) m.1 (z m)
    = gaugeLinkVal a m.1 (gaugeLinkVal b m.1 (z m))
  unfold gaugeLinkVal
  simp only [Pi.mul_apply, mul_inv_rev]
  group

/-- Composition law for the mirror action: in direction `≠ 0` it
is the linkwise law at the reflected link; in direction `0` the
two inversions compose to the same law (checked by `group` after
unfolding). -/
theorem gaugeMirrorPos_mul (a b : (Fin 4 → ZMod N) → G)
    (z' : ↥(posLinks (N := N)) → G) :
    gaugeMirrorPos (a * b) z'
      = gaugeMirrorPos a (gaugeMirrorPos b z') := by
  funext m
  by_cases hm : m.1.2 = 0
  · rw [gaugeMirrorPos_of_snd_eq_zero _ _ hm,
      gaugeMirrorPos_of_snd_eq_zero _ _ hm,
      gaugeMirrorPos_of_snd_eq_zero _ _ hm, inv_inv]
    show (gaugeLinkVal (a * b) (reflLink m.1) ((z' m)⁻¹))⁻¹
      = (gaugeLinkVal a (reflLink m.1)
          (gaugeLinkVal b (reflLink m.1) ((z' m)⁻¹)))⁻¹
    unfold gaugeLinkVal
    simp only [Pi.mul_apply, mul_inv_rev, inv_inv]
    group
  · rw [gaugeMirrorPos_of_snd_ne_zero _ _ hm,
      gaugeMirrorPos_of_snd_ne_zero _ _ hm,
      gaugeMirrorPos_of_snd_ne_zero _ _ hm]
    show gaugeLinkVal (a * b) (reflLink m.1) (z' m)
      = gaugeLinkVal a (reflLink m.1)
          (gaugeLinkVal b (reflLink m.1) (z' m))
    unfold gaugeLinkVal
    simp only [Pi.mul_apply, mul_inv_rev]
    group

/-- Measurability of one coordinate of the mirror action. -/
theorem measurable_gaugeMirrorPos_apply
    (h : (Fin 4 → ZMod N) → G) (m : ↥(posLinks (N := N))) :
    Measurable (fun z' : ↥(posLinks (N := N)) → G =>
      gaugeMirrorPos h z' m) := by
  by_cases hm : m.1.2 = 0
  · have e : (fun z' : ↥(posLinks (N := N)) → G =>
        gaugeMirrorPos h z' m)
      = fun z' => (gaugeLinkVal h (reflLink m.1) ((z' m)⁻¹))⁻¹ :=
      funext fun z' => gaugeMirrorPos_of_snd_eq_zero h z' hm
    rw [e]
    exact measurable_inv.comp
      ((measurable_const.mul
        (measurable_inv.comp (measurable_pi_apply m))).mul
        measurable_const)
  · have e : (fun z' : ↥(posLinks (N := N)) → G =>
        gaugeMirrorPos h z' m)
      = fun z' => gaugeLinkVal h (reflLink m.1) (z' m) :=
      funext fun z' => gaugeMirrorPos_of_snd_ne_zero h z' hm
    rw [e]
    exact (measurable_const.mul (measurable_pi_apply m)).mul
      measurable_const

/-- **The mirror gauge substitution**: the mirror action as a
measurable equivalence of the strict-half configuration space
(the `gaugeStratumEquiv` analogue for the mirrored argument;
α needed only the diagonal substitution, the remainder needs
this one separately). -/
def mirrorGaugeEquiv (h : (Fin 4 → ZMod N) → G) :
    (↥(posLinks (N := N)) → G) ≃ᵐ (↥(posLinks (N := N)) → G) where
  toFun := gaugeMirrorPos h
  invFun := gaugeMirrorPos (fun x => (h x)⁻¹)
  left_inv z' := by
    have e : gaugeMirrorPos (fun x => (h x)⁻¹) (gaugeMirrorPos h z')
        = gaugeMirrorPos ((fun x => (h x)⁻¹) * h) z' :=
      (gaugeMirrorPos_mul _ _ _).symm
    rw [e]
    have e2 : (fun x => (h x)⁻¹) * h = (1 : (Fin 4 → ZMod N) → G) := by
      funext x
      simp [Pi.mul_apply]
    rw [e2, gaugeMirrorPos_one]
  right_inv z' := by
    have e : gaugeMirrorPos h (gaugeMirrorPos (fun x => (h x)⁻¹) z')
        = gaugeMirrorPos (h * (fun x => (h x)⁻¹)) z' :=
      (gaugeMirrorPos_mul _ _ _).symm
    rw [e]
    have e2 : h * (fun x => (h x)⁻¹)
        = (1 : (Fin 4 → ZMod N) → G) := by
      funext x
      simp [Pi.mul_apply]
    rw [e2, gaugeMirrorPos_one]
  measurable_toFun := measurable_pi_iff.mpr fun m =>
    measurable_gaugeMirrorPos_apply h m
  measurable_invFun := measurable_pi_iff.mpr fun m =>
    measurable_gaugeMirrorPos_apply (fun x => (h x)⁻¹) m

/-- The mirror gauge substitution preserves the pi-Haar measure:
per coordinate it is a two-sided translation (in direction `0`,
of the inverted value, which the outer inversion turns back into
a two-sided translation). -/
theorem measurePreserving_mirrorGaugeEquiv
    (h : (Fin 4 → ZMod N) → G) :
    MeasurePreserving (mirrorGaugeEquiv h)
      (Measure.pi fun _ : ↥(posLinks (N := N)) => μG)
      (Measure.pi fun _ : ↥(posLinks (N := N)) => μG) := by
  refine measurePreserving_pi
    (f := fun m v => if m.1.2 = 0
      then (h ((reflLink m.1).1) * v⁻¹
        * (h (torusShift N (reflLink m.1).2 (reflLink m.1).1))⁻¹)⁻¹
      else h ((reflLink m.1).1) * v
        * (h (torusShift N (reflLink m.1).2 (reflLink m.1).1))⁻¹)
    (fun _ : ↥(posLinks (N := N)) => μG)
    (fun _ : ↥(posLinks (N := N)) => μG) fun m => ?_
  by_cases hm : m.1.2 = 0
  · have e0 : (fun v : G => if m.1.2 = 0
          then (h ((reflLink m.1).1) * v⁻¹
            * (h (torusShift N (reflLink m.1).2
                (reflLink m.1).1))⁻¹)⁻¹
          else h ((reflLink m.1).1) * v
            * (h (torusShift N (reflLink m.1).2
                (reflLink m.1).1))⁻¹)
        = fun v => (h ((reflLink m.1).1) * v⁻¹
            * (h (torusShift N (reflLink m.1).2
                (reflLink m.1).1))⁻¹)⁻¹ :=
      funext fun v => if_pos hm
    have e : (fun v : G => (h ((reflLink m.1).1) * v⁻¹
          * (h (torusShift N (reflLink m.1).2
              (reflLink m.1).1))⁻¹)⁻¹)
        = fun v => h (torusShift N (reflLink m.1).2
              (reflLink m.1).1) * v
            * (h ((reflLink m.1).1))⁻¹ := by
      funext v
      group
    rw [e0, e]
    exact (measurePreserving_mul_right μG _).comp
      (measurePreserving_mul_left μG _)
  · have e0 : (fun v : G => if m.1.2 = 0
          then (h ((reflLink m.1).1) * v⁻¹
            * (h (torusShift N (reflLink m.1).2
                (reflLink m.1).1))⁻¹)⁻¹
          else h ((reflLink m.1).1) * v
            * (h (torusShift N (reflLink m.1).2
                (reflLink m.1).1))⁻¹)
        = fun v => h ((reflLink m.1).1) * v
            * (h (torusShift N (reflLink m.1).2
                (reflLink m.1).1))⁻¹ :=
      funext fun v => if_neg hm
    rw [e0]
    exact (measurePreserving_mul_right μG _).comp
      (measurePreserving_mul_left μG _)

/-- **The `K̄` pairing** of two strict-half observables: the
integrand of `osForm_eq_planeAvgKernel` (which states
`osForm F F = Z⁻¹ ∫ r, conj (f r.2) * (K̄ r.1 r.2 * f r.1)`;
the pairing here is the same integral with the two slots named
separately and the factors commuted). -/
noncomputable def planeAvgPairing (hN : Even N) (β : ℝ)
    (k₁ k₂ : (↥(posLinks (N := N)) → G) → ℂ) : ℂ :=
  ∫ r : (↥(posLinks (N := N)) → G) × (↥(posLinks (N := N)) → G),
      k₁ r.1 * (planeAvgKernel μG ρ hN β r.1 r.2
        * (starRingEnd ℂ) (k₂ r.2))
    ∂((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
      (Measure.pi fun _ : ↥(posLinks (N := N)) => μG))

/-- **Slot-wise gauge invariance of the pairing**: transforming
the first observable by the linkwise action and the second by
the mirror action does not change the pairing — the two
substitutions (α's stratum substitution on the first factor,
the mirror substitution on the second) preserve the product
measure, and `K̄` is separately invariant (§4). -/
theorem planeAvgPairing_gauge (hN : Even N) (β : ℝ)
    (g h : (Fin 4 → ZMod N) → G)
    (k₁ k₂ : (↥(posLinks (N := N)) → G) → ℂ) :
    planeAvgPairing μG ρ hN β (fun z => k₁ (gaugePosFun g z))
        (fun z' => k₂ (gaugeMirrorPos h z'))
      = planeAvgPairing μG ρ hN β k₁ k₂ := by
  have hpt : ∀ s : (↥(posLinks (N := N)) → G)
        × (↥(posLinks (N := N)) → G),
      k₁ (gaugePosFun g s.1)
          * (planeAvgKernel μG ρ hN β s.1 s.2
            * (starRingEnd ℂ) (k₂ (gaugeMirrorPos h s.2)))
        = k₁ (((gaugeStratumEquiv
              (fun m : ↥(posLinks (N := N)) => m.1) g).prodCongr
              (mirrorGaugeEquiv h)) s).1
          * (planeAvgKernel μG ρ hN β
              (((gaugeStratumEquiv
                (fun m : ↥(posLinks (N := N)) => m.1) g).prodCongr
                (mirrorGaugeEquiv h)) s).1
              (((gaugeStratumEquiv
                (fun m : ↥(posLinks (N := N)) => m.1) g).prodCongr
                (mirrorGaugeEquiv h)) s).2
            * (starRingEnd ℂ) (k₂
              (((gaugeStratumEquiv
                (fun m : ↥(posLinks (N := N)) => m.1) g).prodCongr
                (mirrorGaugeEquiv h)) s).2)) := by
    intro s
    show k₁ (gaugePosFun g s.1)
          * (planeAvgKernel μG ρ hN β s.1 s.2
            * (starRingEnd ℂ) (k₂ (gaugeMirrorPos h s.2)))
        = k₁ (gaugePosFun g s.1)
          * (planeAvgKernel μG ρ hN β (gaugePosFun g s.1)
              (gaugeMirrorPos h s.2)
            * (starRingEnd ℂ) (k₂ (gaugeMirrorPos h s.2)))
    rw [planeAvgKernel_gauge_invariant_separate μG ρ hN β g h
      s.1 s.2]
  unfold planeAvgPairing
  calc (∫ s, k₁ (gaugePosFun g s.1)
          * (planeAvgKernel μG ρ hN β s.1 s.2
            * (starRingEnd ℂ) (k₂ (gaugeMirrorPos h s.2)))
        ∂((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
          (Measure.pi fun _ : ↥(posLinks (N := N)) => μG)))
      = ∫ s, k₁ (((gaugeStratumEquiv
              (fun m : ↥(posLinks (N := N)) => m.1) g).prodCongr
              (mirrorGaugeEquiv h)) s).1
          * (planeAvgKernel μG ρ hN β
              (((gaugeStratumEquiv
                (fun m : ↥(posLinks (N := N)) => m.1) g).prodCongr
                (mirrorGaugeEquiv h)) s).1
              (((gaugeStratumEquiv
                (fun m : ↥(posLinks (N := N)) => m.1) g).prodCongr
                (mirrorGaugeEquiv h)) s).2
            * (starRingEnd ℂ) (k₂
              (((gaugeStratumEquiv
                (fun m : ↥(posLinks (N := N)) => m.1) g).prodCongr
                (mirrorGaugeEquiv h)) s).2))
        ∂((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
          (Measure.pi fun _ : ↥(posLinks (N := N)) => μG)) :=
        integral_congr_ae (ae_of_all _ hpt)
    _ = ∫ s, k₁ s.1 * (planeAvgKernel μG ρ hN β s.1 s.2
          * (starRingEnd ℂ) (k₂ s.2))
        ∂((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
          (Measure.pi fun _ : ↥(posLinks (N := N)) => μG)) :=
        (show MeasurePreserving
            ((gaugeStratumEquiv
              (fun m : ↥(posLinks (N := N)) => m.1) g).prodCongr
              (mirrorGaugeEquiv h))
            ((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
              (Measure.pi fun _ : ↥(posLinks (N := N)) => μG))
            ((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
              (Measure.pi fun _ : ↥(posLinks (N := N)) => μG)) from
          (measurePreserving_gaugeStratumEquiv μG
            (fun m : ↥(posLinks (N := N)) => m.1) g).prod
            (measurePreserving_mirrorGaugeEquiv μG h)).integral_comp
          (((gaugeStratumEquiv
            (fun m : ↥(posLinks (N := N)) => m.1) g).prodCongr
            (mirrorGaugeEquiv h)).measurableEmbedding)
          (fun t => k₁ t.1 * (planeAvgKernel μG ρ hN β t.1 t.2
            * (starRingEnd ℂ) (k₂ t.2)))


/-! ## §6. Gauge averages and the reduction corollary -/

/-- Right multiplication by a fixed gauge function, as a
measurable equivalence of the gauge-function space. -/
def gaugeMulRightEquiv (g₀ : (Fin 4 → ZMod N) → G) :
    ((Fin 4 → ZMod N) → G) ≃ᵐ ((Fin 4 → ZMod N) → G) :=
  MeasurableEquiv.piCongrRight
    (fun x => MeasurableEquiv.mulRight (g₀ x))

/-- Right multiplication preserves the pi-Haar measure on gauge
functions (per coordinate it is right translation). -/
theorem measurePreserving_gaugeMulRightEquiv
    (g₀ : (Fin 4 → ZMod N) → G) :
    MeasurePreserving (gaugeMulRightEquiv g₀)
      (Measure.pi fun _ : (Fin 4 → ZMod N) => μG)
      (Measure.pi fun _ : (Fin 4 → ZMod N) => μG) := by
  have e : ((gaugeMulRightEquiv g₀) :
        ((Fin 4 → ZMod N) → G) → ((Fin 4 → ZMod N) → G))
      = fun a i => a i * g₀ i := rfl
  rw [e]
  exact measurePreserving_pi
    (f := fun x (v : G) => v * g₀ x)
    (fun _ : (Fin 4 → ZMod N) => μG)
    (fun _ : (Fin 4 → ZMod N) => μG)
    fun x => measurePreserving_mul_right μG _

/-- **The gauge average** (Haar twirl) of a strict-half
observable under the first argument's gauge action. -/
noncomputable def posGaugeAvg
    (k : (↥(posLinks (N := N)) → G) → ℂ) :
    (↥(posLinks (N := N)) → G) → ℂ :=
  fun z => ∫ g : (Fin 4 → ZMod N) → G, k (gaugePosFun g z)
    ∂(Measure.pi fun _ : (Fin 4 → ZMod N) => μG)

/-- **The mirror gauge average** of a strict-half observable
under the second argument's mirror gauge action. -/
noncomputable def mirrorGaugeAvg
    (k : (↥(posLinks (N := N)) → G) → ℂ) :
    (↥(posLinks (N := N)) → G) → ℂ :=
  fun z' => ∫ h : (Fin 4 → ZMod N) → G, k (gaugeMirrorPos h z')
    ∂(Measure.pi fun _ : (Fin 4 → ZMod N) => μG)

/-- The gauge average is invariant under the action it averages:
Haar invariance under right multiplication in the gauge group,
through the composition law (§5). -/
theorem posGaugeAvg_gauge (k : (↥(posLinks (N := N)) → G) → ℂ)
    (g₀ : (Fin 4 → ZMod N) → G) (z : ↥(posLinks (N := N)) → G) :
    posGaugeAvg μG k (gaugePosFun g₀ z) = posGaugeAvg μG k z := by
  unfold posGaugeAvg
  have hpt : ∀ g : (Fin 4 → ZMod N) → G,
      k (gaugePosFun g (gaugePosFun g₀ z))
        = k (gaugePosFun (g * g₀) z) := by
    intro g
    rw [← gaugePosFun_mul]
  rw [integral_congr_ae (ae_of_all _ hpt)]
  exact (measurePreserving_gaugeMulRightEquiv μG g₀).integral_comp
    (gaugeMulRightEquiv g₀).measurableEmbedding
    (fun g => k (gaugePosFun g z))

/-- The mirror gauge average is invariant under the mirror
action. -/
theorem mirrorGaugeAvg_gauge (k : (↥(posLinks (N := N)) → G) → ℂ)
    (h₀ : (Fin 4 → ZMod N) → G) (z' : ↥(posLinks (N := N)) → G) :
    mirrorGaugeAvg μG k (gaugeMirrorPos h₀ z')
      = mirrorGaugeAvg μG k z' := by
  unfold mirrorGaugeAvg
  have hpt : ∀ h : (Fin 4 → ZMod N) → G,
      k (gaugeMirrorPos h (gaugeMirrorPos h₀ z'))
        = k (gaugeMirrorPos (h * h₀) z') := by
    intro h
    rw [← gaugeMirrorPos_mul]
  rw [integral_congr_ae (ae_of_all _ hpt)]
  exact (measurePreserving_gaugeMulRightEquiv μG h₀).integral_comp
    (gaugeMulRightEquiv h₀).measurableEmbedding
    (fun h => k (gaugeMirrorPos h z'))

/-- The crossing action has the same two-sided bound as the full
action (each density is in `[-2, 2]` when `0 < d`). -/
theorem wilsonActionZero_abs_le (hd : 0 < d) (β : ℝ)
    (U : Config (Fin 4 → ZMod N) G) :
    |wilsonActionZero ρ β U|
      ≤ |β| * (2 * ((plaqIndex (N := N)).card : ℝ)) := by
  have hd2 : ∀ p : (Fin 4 → ZMod N) × Fin 4 × Fin 4,
      |plaquetteDensity (torusShift N) ρ U p.1 p.2.1 p.2.2|
        ≤ 2 := fun p =>
    abs_le.mpr
      ⟨by linarith [(Set.mem_Icc.mp
          (plaquetteDensity_mem_Icc (torusShift N) ρ hd U
            p.1 p.2.1 p.2.2)).1],
       (Set.mem_Icc.mp (plaquetteDensity_mem_Icc (torusShift N) ρ
          hd U p.1 p.2.1 p.2.2)).2⟩
  unfold wilsonActionZero
  rw [abs_mul]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg β)
  refine ((Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum fun p _ => hd2 p)).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  have hc : (((plaqIndex (N := N)).filter IsZeroPlaq).card : ℝ)
      ≤ ((plaqIndex (N := N)).card : ℝ) :=
    by exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
  linarith [hc]

/-- The crossing marginal is measurable in its two arguments
(the integrand is measurable in all four, by the corpus's
assembly measurability; two applications of the integral
measurability lemma). -/
theorem measurable_planeCrossingMarginal
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ) :
    Measurable (fun p : (↥(posLinks (N := N)) → G)
        × (↥(posLinks (N := N)) → G) =>
      planeCrossingMarginal μG ρ hN β p.1 p.2) := by
  have hAsm : Measurable
      (fun q : (((↥(posLinks (N := N)) → G)
          × (↥(posLinks (N := N)) → G))
          × (↥(planeHalfLinks (N := N)) → G))
          × (↥(planeNegLinks (N := N)) → G) =>
        planeAssemble hN q.1.1.1 q.1.1.2 q.1.2 q.2) := by
    show Measurable
      (fun q : (((↥(posLinks (N := N)) → G)
          × (↥(posLinks (N := N)) → G))
          × (↥(planeHalfLinks (N := N)) → G))
          × (↥(planeNegLinks (N := N)) → G) =>
        (splitEquiv (halfLinks (N := N))).symm
          (joinHalf q.1.1.1 q.1.2, joinNeg hN q.1.1.2 q.2))
    exact (splitEquiv (halfLinks (N := N))).symm.measurable.comp
      ((measurable_joinHalf.comp
        ((measurable_fst.comp (measurable_fst.comp
          measurable_fst)).prodMk
          (measurable_snd.comp measurable_fst))).prodMk
        (measurable_joinNeg hN |>.comp
          ((measurable_snd.comp (measurable_fst.comp
            measurable_fst)).prodMk measurable_snd)))
  have hInt : Measurable
      (fun q : (((↥(posLinks (N := N)) → G)
          × (↥(posLinks (N := N)) → G))
          × (↥(planeHalfLinks (N := N)) → G))
          × (↥(planeNegLinks (N := N)) → G) =>
        (Real.exp (-(wilsonActionZero ρ β
          (planeAssemble hN q.1.1.1 q.1.1.2 q.1.2 q.2))) : ℂ)) :=
    Complex.measurable_ofReal.comp
      (Real.measurable_exp.comp
        ((measurable_wilsonActionZero_lf ρ hρcont β).comp
          hAsm).neg)
  have step1 : StronglyMeasurable
      (fun r : ((↥(posLinks (N := N)) → G)
          × (↥(posLinks (N := N)) → G))
          × (↥(planeHalfLinks (N := N)) → G) =>
        ∫ a' : ↥(planeNegLinks (N := N)) → G,
          (Real.exp (-(wilsonActionZero ρ β
            (planeAssemble hN r.1.1 r.1.2 r.2 a'))) : ℂ)
          ∂(Measure.pi fun _ : ↥(planeNegLinks (N := N)) => μG)) :=
    hInt.stronglyMeasurable.integral_prod_right'
  have step2 : StronglyMeasurable
      (fun p : (↥(posLinks (N := N)) → G)
          × (↥(posLinks (N := N)) → G) =>
        ∫ a : ↥(planeHalfLinks (N := N)) → G,
          ∫ a' : ↥(planeNegLinks (N := N)) → G,
            (Real.exp (-(wilsonActionZero ρ β
              (planeAssemble hN p.1 p.2 a a'))) : ℂ)
            ∂(Measure.pi fun _ : ↥(planeNegLinks (N := N)) => μG)
          ∂(Measure.pi fun _ : ↥(planeHalfLinks (N := N)) => μG)) :=
    step1.integral_prod_right'
  exact step2.measurable

/-- The plane-averaged kernel is measurable in its two
arguments, through its factorization. -/
theorem measurable_planeAvgKernel
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ) :
    Measurable (fun p : (↥(posLinks (N := N)) → G)
        × (↥(posLinks (N := N)) → G) =>
      planeAvgKernel μG ρ hN β p.1 p.2) := by
  have hfac : (fun p : (↥(posLinks (N := N)) → G)
        × (↥(posLinks (N := N)) → G) =>
        planeAvgKernel μG ρ hN β p.1 p.2)
      = fun p => ((Real.exp (-(halfActionP ρ β p.1)) : ℂ)
          * (Real.exp (-(halfActionP ρ β p.2)) : ℂ))
        * planeCrossingMarginal μG ρ hN β p.1 p.2 :=
    funext fun p => planeAvgKernel_factor μG ρ hN β p.1 p.2
  rw [hfac]
  exact ((Complex.measurable_ofReal.comp
      (Real.measurable_exp.comp
        ((measurable_halfActionP_lf ρ hρcont β).comp
          measurable_fst).neg)).mul
    (Complex.measurable_ofReal.comp
      (Real.measurable_exp.comp
        ((measurable_halfActionP_lf ρ hρcont β).comp
          measurable_snd).neg))).mul
    (measurable_planeCrossingMarginal μG ρ hρcont hN β)

/-- The half action has the same two-sided bound (the filtered
sum estimate of `LatticeGramAssembly.abs_halfActionP_le`, which
is not in this module's import chain; proved here in place). -/
theorem halfActionP_abs_le_brick (hd : 0 < d) (β : ℝ)
    (z : ↥(posLinks (N := N)) → G) :
    |halfActionP ρ β z|
      ≤ |β| * (2 * ((plaqIndex (N := N)).card : ℝ)) := by
  have hd2 : ∀ p : (Fin 4 → ZMod N) × Fin 4 × Fin 4,
      |plaquetteDensity (torusShift N) ρ (extendP z)
        p.1 p.2.1 p.2.2| ≤ 2 := fun p =>
    abs_le.mpr
      ⟨by linarith [(Set.mem_Icc.mp
          (plaquetteDensity_mem_Icc (torusShift N) ρ hd
            (extendP z) p.1 p.2.1 p.2.2)).1],
       (Set.mem_Icc.mp (plaquetteDensity_mem_Icc (torusShift N) ρ
          hd (extendP z) p.1 p.2.1 p.2.2)).2⟩
  unfold halfActionP wilsonActionPlus
  rw [abs_mul]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg β)
  refine ((Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum fun p _ => hd2 p)).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  have hc : (((plaqIndex (N := N)).filter IsPosPlaq).card : ℝ)
      ≤ ((plaqIndex (N := N)).card : ℝ) :=
    by exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
  linarith [hc]

/-- The Boltzmann factor of a real action is bounded by the
exponential of the action's two-sided bound. -/
theorem exp_neg_le_of_abs_le {B : ℝ} (hB : 0 ≤ B) {x : ℝ}
    (hx : |x| ≤ B) : Real.exp (-x) ≤ Real.exp B :=
  Real.exp_le_exp.mpr (by linarith [abs_le.mp hx])

/-- **Uniform bound on the plane-averaged kernel**: through the
factorization, each of the three factors is bounded by
`exp (|β| · 2 · #plaquettes)`. -/
theorem planeAvgKernel_norm_le (hd : 0 < d) (hN : Even N) (β : ℝ)
    (z z' : ↥(posLinks (N := N)) → G) :
    ‖planeAvgKernel μG ρ hN β z z'‖
      ≤ (Real.exp (|β| * (2 * ((plaqIndex (N := N)).card : ℝ)))
          * Real.exp (|β| * (2 * ((plaqIndex (N := N)).card : ℝ))))
        * Real.exp (|β| * (2 * ((plaqIndex (N := N)).card : ℝ))) := by
  have hM : ‖planeCrossingMarginal μG ρ hN β z z'‖
      ≤ Real.exp (|β| * (2 * ((plaqIndex (N := N)).card : ℝ))) := by
    have hinner : ∀ a : ↥(planeHalfLinks (N := N)) → G,
        ‖∫ a' : ↥(planeNegLinks (N := N)) → G,
            (Real.exp (-(wilsonActionZero ρ β
              (planeAssemble hN z z' a a'))) : ℂ)
            ∂(Measure.pi fun _ : ↥(planeNegLinks (N := N)) => μG)‖
          ≤ Real.exp (|β| * (2 * ((plaqIndex (N := N)).card : ℝ))) := by
      intro a
      refine (norm_integral_le_of_norm_le_const
        (C := Real.exp (|β| * (2 * ((plaqIndex (N := N)).card : ℝ))))
        (ae_of_all _ fun a' => ?_)).trans ?_
      · have h1 : ‖(Real.exp (-(wilsonActionZero ρ β
            (planeAssemble hN z z' a a'))) : ℂ)‖
            = Real.exp (-(wilsonActionZero ρ β
              (planeAssemble hN z z' a a'))) :=
          (RCLike.norm_ofReal _).trans (Real.abs_exp _)
        rw [h1]
        exact exp_neg_le_of_abs_le
          (mul_nonneg (abs_nonneg β) (by positivity))
          (wilsonActionZero_abs_le ρ hd β _)
      · simp
    unfold planeCrossingMarginal
    refine (norm_integral_le_of_norm_le_const
      (ae_of_all _ hinner)).trans ?_
    simp
  have hE : ∀ w : ↥(posLinks (N := N)) → G,
      ‖(Real.exp (-(halfActionP ρ β w)) : ℂ)‖
        ≤ Real.exp (|β| * (2 * ((plaqIndex (N := N)).card : ℝ))) := by
    intro w
    have h1 : ‖(Real.exp (-(halfActionP ρ β w)) : ℂ)‖
        = Real.exp (-(halfActionP ρ β w)) :=
      (RCLike.norm_ofReal _).trans (Real.abs_exp _)
    rw [h1]
    exact exp_neg_le_of_abs_le
      (mul_nonneg (abs_nonneg β) (by positivity))
      (halfActionP_abs_le_brick ρ hd β w)
  rw [planeAvgKernel_factor μG ρ hN β z z']
  refine ((norm_mul_le _ _).trans
    (mul_le_mul_of_nonneg_right (norm_mul_le _ _)
      (norm_nonneg _))).trans ?_
  refine mul_le_mul
    (mul_le_mul (hE z) (hE z') (norm_nonneg _)
      (le_trans (norm_nonneg _) (hE z))) hM (norm_nonneg _)
    (mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _))

/-- The gauge action, as a map of (gauge function, strict-half
configuration), preserves the product measure: at each gauge
function it is α's stratum substitution. -/
theorem measurePreserving_gaugePosFun_prod :
    MeasurePreserving
      (fun p : ((Fin 4 → ZMod N) → G)
          × (↥(posLinks (N := N)) → G) => gaugePosFun p.1 p.2)
      ((Measure.pi fun _ : (Fin 4 → ZMod N) => μG).prod
        (Measure.pi fun _ : ↥(posLinks (N := N)) => μG))
      (Measure.pi fun _ : ↥(posLinks (N := N)) => μG) := by
  have hmeas : Measurable
      (fun p : ((Fin 4 → ZMod N) → G)
          × (↥(posLinks (N := N)) → G) => gaugePosFun p.1 p.2) := by
    refine measurable_pi_iff.mpr fun m => ?_
    show Measurable
      (fun p : ((Fin 4 → ZMod N) → G)
          × (↥(posLinks (N := N)) → G) =>
        gaugeLinkVal p.1 m.1 (p.2 m))
    unfold gaugeLinkVal
    exact (((measurable_pi_apply (m.1.1)).comp measurable_fst).mul
      ((measurable_pi_apply m).comp measurable_snd)).mul
      (measurable_inv.comp
        ((measurable_pi_apply
          (torusShift N m.1.2 m.1.1)).comp measurable_fst))
  refine ⟨hmeas, ?_⟩
  ext s hs
  rw [Measure.map_apply hmeas hs, Measure.prod_apply (hmeas hs)]
  have hpre : ∀ g : (Fin 4 → ZMod N) → G,
      (Measure.pi fun _ : ↥(posLinks (N := N)) => μG)
          (Prod.mk g ⁻¹'
            ((fun p : ((Fin 4 → ZMod N) → G)
                × (↥(posLinks (N := N)) → G) =>
              gaugePosFun p.1 p.2) ⁻¹' s))
        = (Measure.pi fun _ : ↥(posLinks (N := N)) => μG) s := by
    intro g
    have hmp := measurePreserving_gaugeStratumEquiv μG
      (fun m : ↥(posLinks (N := N)) => m.1) g
    have e : Prod.mk g ⁻¹'
          ((fun p : ((Fin 4 → ZMod N) → G)
              × (↥(posLinks (N := N)) → G) =>
            gaugePosFun p.1 p.2) ⁻¹' s)
        = (gaugeStratumEquiv
            (fun m : ↥(posLinks (N := N)) => m.1) g) ⁻¹' s := rfl
    have h2 : (Measure.pi fun _ : ↥(posLinks (N := N)) => μG)
          ((gaugeStratumEquiv
            (fun m : ↥(posLinks (N := N)) => m.1) g) ⁻¹' s)
        = (Measure.map
            (gaugeStratumEquiv
              (fun m : ↥(posLinks (N := N)) => m.1) g)
            (Measure.pi fun _ : ↥(posLinks (N := N)) => μG)) s :=
      (Measure.map_apply hmp.measurable hs).symm
    rw [e, h2, hmp.map_eq]
  rw [lintegral_congr_ae (ae_of_all _ hpre)]
  simp [lintegral_const]

/-- The mirror gauge action, as a map of (gauge function,
strict-half configuration), preserves the product measure: at
each gauge function it is the mirror substitution (§5). -/
theorem measurePreserving_gaugeMirrorPos_prod :
    MeasurePreserving
      (fun p : ((Fin 4 → ZMod N) → G)
          × (↥(posLinks (N := N)) → G) => gaugeMirrorPos p.1 p.2)
      ((Measure.pi fun _ : (Fin 4 → ZMod N) => μG).prod
        (Measure.pi fun _ : ↥(posLinks (N := N)) => μG))
      (Measure.pi fun _ : ↥(posLinks (N := N)) => μG) := by
  have hmeas : Measurable
      (fun p : ((Fin 4 → ZMod N) → G)
          × (↥(posLinks (N := N)) → G) =>
        gaugeMirrorPos p.1 p.2) := by
    refine measurable_pi_iff.mpr fun m => ?_
    by_cases hm : m.1.2 = 0
    · have e : (fun p : ((Fin 4 → ZMod N) → G)
            × (↥(posLinks (N := N)) → G) =>
          gaugeMirrorPos p.1 p.2 m)
        = fun p => (gaugeLinkVal p.1 (reflLink m.1)
            ((p.2 m)⁻¹))⁻¹ :=
        funext fun p => gaugeMirrorPos_of_snd_eq_zero p.1 p.2 hm
      rw [e]
      refine measurable_inv.comp ?_
      show Measurable
        (fun p : ((Fin 4 → ZMod N) → G)
            × (↥(posLinks (N := N)) → G) =>
          gaugeLinkVal p.1 (reflLink m.1) ((p.2 m)⁻¹))
      unfold gaugeLinkVal
      exact (((measurable_pi_apply
          ((reflLink m.1).1)).comp measurable_fst).mul
        (measurable_inv.comp
          ((measurable_pi_apply m).comp measurable_snd))).mul
        (measurable_inv.comp
          ((measurable_pi_apply
            (torusShift N (reflLink m.1).2
              (reflLink m.1).1)).comp measurable_fst))
    · have e : (fun p : ((Fin 4 → ZMod N) → G)
            × (↥(posLinks (N := N)) → G) =>
          gaugeMirrorPos p.1 p.2 m)
        = fun p => gaugeLinkVal p.1 (reflLink m.1) (p.2 m) :=
        funext fun p => gaugeMirrorPos_of_snd_ne_zero p.1 p.2 hm
      rw [e]
      show Measurable
        (fun p : ((Fin 4 → ZMod N) → G)
            × (↥(posLinks (N := N)) → G) =>
          gaugeLinkVal p.1 (reflLink m.1) (p.2 m))
      unfold gaugeLinkVal
      exact (((measurable_pi_apply
          ((reflLink m.1).1)).comp measurable_fst).mul
        ((measurable_pi_apply m).comp measurable_snd)).mul
        (measurable_inv.comp
          ((measurable_pi_apply
            (torusShift N (reflLink m.1).2
              (reflLink m.1).1)).comp measurable_fst))
  refine ⟨hmeas, ?_⟩
  ext s hs
  rw [Measure.map_apply hmeas hs, Measure.prod_apply (hmeas hs)]
  have hpre : ∀ g : (Fin 4 → ZMod N) → G,
      (Measure.pi fun _ : ↥(posLinks (N := N)) => μG)
          (Prod.mk g ⁻¹'
            ((fun p : ((Fin 4 → ZMod N) → G)
                × (↥(posLinks (N := N)) → G) =>
              gaugeMirrorPos p.1 p.2) ⁻¹' s))
        = (Measure.pi fun _ : ↥(posLinks (N := N)) => μG) s := by
    intro g
    have hmp := measurePreserving_mirrorGaugeEquiv μG g
    have e : Prod.mk g ⁻¹'
          ((fun p : ((Fin 4 → ZMod N) → G)
              × (↥(posLinks (N := N)) → G) =>
            gaugeMirrorPos p.1 p.2) ⁻¹' s)
        = (mirrorGaugeEquiv g) ⁻¹' s := rfl
    have h2 : (Measure.pi fun _ : ↥(posLinks (N := N)) => μG)
          ((mirrorGaugeEquiv g) ⁻¹' s)
        = (Measure.map (mirrorGaugeEquiv g)
            (Measure.pi fun _ : ↥(posLinks (N := N)) => μG)) s :=
      (Measure.map_apply hmp.measurable hs).symm
    rw [e, h2, hmp.map_eq]
  rw [lintegral_congr_ae (ae_of_all _ hpre)]
  simp [lintegral_const]

/-- The gauge average of an a.e. strongly measurable observable
is a.e. strongly measurable. -/
theorem aestronglyMeasurable_posGaugeAvg
    (k : (↥(posLinks (N := N)) → G) → ℂ)
    (hk : AEStronglyMeasurable k
      (Measure.pi fun _ : ↥(posLinks (N := N)) => μG)) :
    AEStronglyMeasurable (posGaugeAvg μG k)
      (Measure.pi fun _ : ↥(posLinks (N := N)) => μG) := by
  have hF : AEStronglyMeasurable
      (fun p : (↥(posLinks (N := N)) → G)
          × ((Fin 4 → ZMod N) → G) => k (gaugePosFun p.2 p.1))
      ((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
        (Measure.pi fun _ : (Fin 4 → ZMod N) => μG)) :=
    hk.comp_measurePreserving
      ((measurePreserving_gaugePosFun_prod μG).comp
        Measure.measurePreserving_swap)
  exact hF.integral_prod_right'

/-- The mirror gauge average of an a.e. strongly measurable
observable is a.e. strongly measurable. -/
theorem aestronglyMeasurable_mirrorGaugeAvg
    (k : (↥(posLinks (N := N)) → G) → ℂ)
    (hk : AEStronglyMeasurable k
      (Measure.pi fun _ : ↥(posLinks (N := N)) => μG)) :
    AEStronglyMeasurable (mirrorGaugeAvg μG k)
      (Measure.pi fun _ : ↥(posLinks (N := N)) => μG) := by
  have hF : AEStronglyMeasurable
      (fun p : (↥(posLinks (N := N)) → G)
          × ((Fin 4 → ZMod N) → G) => k (gaugeMirrorPos p.2 p.1))
      ((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
        (Measure.pi fun _ : (Fin 4 → ZMod N) => μG)) :=
    hk.comp_measurePreserving
      ((measurePreserving_gaugeMirrorPos_prod μG).comp
        Measure.measurePreserving_swap)
  exact hF.integral_prod_right'

/-- The gauge average inherits the observable's uniform bound. -/
theorem norm_posGaugeAvg_le (C : ℝ)
    (k : (↥(posLinks (N := N)) → G) → ℂ)
    (hC : ∀ z, ‖k z‖ ≤ C) (z : ↥(posLinks (N := N)) → G) :
    ‖posGaugeAvg μG k z‖ ≤ C := by
  unfold posGaugeAvg
  refine (norm_integral_le_of_norm_le_const
    (ae_of_all _ fun g => hC _)).trans (by simp)

/-- The mirror gauge average inherits the observable's uniform
bound. -/
theorem norm_mirrorGaugeAvg_le (C : ℝ)
    (k : (↥(posLinks (N := N)) → G) → ℂ)
    (hC : ∀ z, ‖k z‖ ≤ C) (z : ↥(posLinks (N := N)) → G) :
    ‖mirrorGaugeAvg μG k z‖ ≤ C := by
  unfold mirrorGaugeAvg
  refine (norm_integral_le_of_norm_le_const
    (ae_of_all _ fun h => hC _)).trans (by simp)


/-- A three-factor norm bound, packaged for the pairing
integrands. -/
theorem norm_mul3_le {a b c : ℂ} {A B C : ℝ}
    (ha : ‖a‖ ≤ A) (hb : ‖b‖ ≤ B) (hc : ‖c‖ ≤ C)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) :
    ‖a * (b * c)‖ ≤ A * (B * C) :=
  ((norm_mul_le _ _).trans
    (mul_le_mul_of_nonneg_left (norm_mul_le _ _)
      (norm_nonneg _))).trans
    (mul_le_mul ha
      (mul_le_mul hb hc (norm_nonneg _) hB)
      (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hA)

/-- **The (H-PF) reduction corollary** (the form the corpus
supports): the `K̄` pairing of two bounded a.e. strongly
measurable strict-half observables depends only on their gauge
averages — pairing the averages gives the same value as pairing
the observables themselves. Combined with §5 (the pairing is
slot-wise gauge invariant) and §6 (each average is invariant
under its own slot's action), this says exactly: the pairing
factors through the two twirls, i.e. it vanishes on the
complement of the gauge-invariant parts in the sense that
replacing either observable by its average changes nothing.
No positivity is asserted; core (H-PF) remains L+ / open. -/
theorem planeAvgPairing_averages
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (hd : 0 < d) (β : ℝ)
    (k₁ k₂ : (↥(posLinks (N := N)) → G) → ℂ)
    (hk₁ : AEStronglyMeasurable k₁
      (Measure.pi fun _ : ↥(posLinks (N := N)) => μG))
    (hk₁bdd : ∃ C₁ : ℝ, ∀ z, ‖k₁ z‖ ≤ C₁)
    (hk₂ : AEStronglyMeasurable k₂
      (Measure.pi fun _ : ↥(posLinks (N := N)) => μG))
    (hk₂bdd : ∃ C₂ : ℝ, ∀ z, ‖k₂ z‖ ≤ C₂) :
    planeAvgPairing μG ρ hN β (posGaugeAvg μG k₁)
        (mirrorGaugeAvg μG k₂)
      = planeAvgPairing μG ρ hN β k₁ k₂ := by
  obtain ⟨C₁, hC₁⟩ := hk₁bdd
  obtain ⟨C₂, hC₂⟩ := hk₂bdd
  have hC₁0 : 0 ≤ C₁ := le_trans (norm_nonneg _) (hC₁ (fun _ => 1))
  have hC₂0 : 0 ≤ C₂ := le_trans (norm_nonneg _) (hC₂ (fun _ => 1))
  -- The kernel bound, abbreviated.
  have hKB : ∀ z z' : ↥(posLinks (N := N)) → G,
      ‖planeAvgKernel μG ρ hN β z z'‖
        ≤ (Real.exp (|β| * (2 * ((plaqIndex (N := N)).card : ℝ)))
            * Real.exp (|β| * (2 * ((plaqIndex (N := N)).card : ℝ))))
          * Real.exp (|β| * (2 * ((plaqIndex (N := N)).card : ℝ))) :=
    fun z z' => planeAvgKernel_norm_le μG ρ hd hN β z z'
  have hKB0 : 0 ≤ (Real.exp (|β| * (2 * ((plaqIndex (N := N)).card : ℝ)))
        * Real.exp (|β| * (2 * ((plaqIndex (N := N)).card : ℝ))))
      * Real.exp (|β| * (2 * ((plaqIndex (N := N)).card : ℝ))) :=
    mul_nonneg (mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _))
      (Real.exp_nonneg _)
  -- Regularity of the pieces.
  have hKmeas : Measurable
      (fun p : (↥(posLinks (N := N)) → G)
          × (↥(posLinks (N := N)) → G) =>
        planeAvgKernel μG ρ hN β p.1 p.2) :=
    measurable_planeAvgKernel μG ρ hρcont hN β
  have hKaes : AEStronglyMeasurable
      (fun p : (↥(posLinks (N := N)) → G)
          × (↥(posLinks (N := N)) → G) =>
        planeAvgKernel μG ρ hN β p.1 p.2)
      ((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
        (Measure.pi fun _ : ↥(posLinks (N := N)) => μG)) :=
    hKmeas.aestronglyMeasurable
  have hF₁ : AEStronglyMeasurable
      (fun p : ((Fin 4 → ZMod N) → G)
          × (↥(posLinks (N := N)) → G) =>
        k₁ (gaugePosFun p.1 p.2))
      ((Measure.pi fun _ : (Fin 4 → ZMod N) => μG).prod
        (Measure.pi fun _ : ↥(posLinks (N := N)) => μG)) :=
    hk₁.comp_measurePreserving (measurePreserving_gaugePosFun_prod μG)
  have hF₃ : AEStronglyMeasurable
      (fun p : ((Fin 4 → ZMod N) → G)
          × (↥(posLinks (N := N)) → G) =>
        k₂ (gaugeMirrorPos p.1 p.2))
      ((Measure.pi fun _ : (Fin 4 → ZMod N) => μG).prod
        (Measure.pi fun _ : ↥(posLinks (N := N)) => μG)) :=
    hk₂.comp_measurePreserving
      (measurePreserving_gaugeMirrorPos_prod μG)
  have hA_aes : AEStronglyMeasurable (posGaugeAvg μG k₁)
      (Measure.pi fun _ : ↥(posLinks (N := N)) => μG) :=
    aestronglyMeasurable_posGaugeAvg μG k₁ hk₁
  have hC_aes : AEStronglyMeasurable (mirrorGaugeAvg μG k₂)
      (Measure.pi fun _ : ↥(posLinks (N := N)) => μG) :=
    aestronglyMeasurable_mirrorGaugeAvg μG k₂ hk₂
  have hA_bdd : ∀ z, ‖posGaugeAvg μG k₁ z‖ ≤ C₁ :=
    fun z => norm_posGaugeAvg_le μG C₁ k₁ hC₁ z
  have hC_bdd : ∀ z, ‖mirrorGaugeAvg μG k₂ z‖ ≤ C₂ :=
    fun z => norm_mirrorGaugeAvg_le μG C₂ k₂ hC₂ z
  have hstar : ∀ w : ℂ, ‖(starRingEnd ℂ) w‖ = ‖w‖ := by
    intro w
    rw [show (starRingEnd ℂ) w = star w from rfl]
    exact norm_star w
  -- Integrability of the two pairing integrands and the middle one.
  have hIntAC : Integrable
      (fun p : (↥(posLinks (N := N)) → G)
          × (↥(posLinks (N := N)) → G) =>
        (posGaugeAvg μG k₁) p.1
          * (planeAvgKernel μG ρ hN β p.1 p.2
            * (starRingEnd ℂ) ((mirrorGaugeAvg μG k₂) p.2)))
      ((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
        (Measure.pi fun _ : ↥(posLinks (N := N)) => μG)) := by
    refine Integrable.of_bound
      ((hA_aes.comp_measurePreserving measurePreserving_fst).mul
        (hKaes.mul
          ((hC_aes.star).comp_measurePreserving
            measurePreserving_snd)))
      (C₁ * ((Real.exp (|β| * (2 * ((plaqIndex (N := N)).card : ℝ)))
            * Real.exp (|β| * (2 * ((plaqIndex (N := N)).card : ℝ))))
          * Real.exp (|β| * (2 * ((plaqIndex (N := N)).card : ℝ)))
        * C₂)) (ae_of_all _ fun p => ?_)
    refine norm_mul3_le (hA_bdd _) (hKB _ _)
      (by rw [hstar]; exact hC_bdd _) hC₁0 hKB0 hC₂0
  have hIntFinal : Integrable
      (fun p : (↥(posLinks (N := N)) → G)
          × (↥(posLinks (N := N)) → G) =>
        k₁ p.1
          * (planeAvgKernel μG ρ hN β p.1 p.2
            * (starRingEnd ℂ) (k₂ p.2)))
      ((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
        (Measure.pi fun _ : ↥(posLinks (N := N)) => μG)) := by
    refine Integrable.of_bound
      ((hk₁.comp_measurePreserving measurePreserving_fst).mul
        (hKaes.mul
          ((hk₂.star).comp_measurePreserving
            measurePreserving_snd)))
      (C₁ * ((Real.exp (|β| * (2 * ((plaqIndex (N := N)).card : ℝ)))
            * Real.exp (|β| * (2 * ((plaqIndex (N := N)).card : ℝ))))
          * Real.exp (|β| * (2 * ((plaqIndex (N := N)).card : ℝ)))
        * C₂)) (ae_of_all _ fun p => ?_)
    refine norm_mul3_le (hC₁ _) (hKB _ _)
      (by rw [hstar]; exact hC₂ _) hC₁0 hKB0 hC₂0
  have hIntMid : Integrable
      (fun p : (↥(posLinks (N := N)) → G)
          × (↥(posLinks (N := N)) → G) =>
        k₁ p.2
          * (planeAvgKernel μG ρ hN β p.2 p.1
            * (starRingEnd ℂ) ((mirrorGaugeAvg μG k₂) p.1)))
      ((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
        (Measure.pi fun _ : ↥(posLinks (N := N)) => μG)) := by
    refine Integrable.of_bound
      ((hk₁.comp_measurePreserving measurePreserving_snd).mul
        ((hKaes.comp_measurePreserving
          Measure.measurePreserving_swap).mul
          ((hC_aes.star).comp_measurePreserving
            measurePreserving_fst)))
      (C₁ * ((Real.exp (|β| * (2 * ((plaqIndex (N := N)).card : ℝ)))
            * Real.exp (|β| * (2 * ((plaqIndex (N := N)).card : ℝ))))
          * Real.exp (|β| * (2 * ((plaqIndex (N := N)).card : ℝ)))
        * C₂)) (ae_of_all _ fun p => ?_)
    refine norm_mul3_le (hC₁ _) (hKB _ _)
      (by rw [hstar]; exact hC_bdd _) hC₁0 hKB0 hC₂0
  -- Step A: the first slot's average can be removed, pointwise
  -- in the second argument.
  have hswapA : ∀ z' : ↥(posLinks (N := N)) → G,
      ∫ z, (posGaugeAvg μG k₁) z
          * (planeAvgKernel μG ρ hN β z z'
            * (starRingEnd ℂ) ((mirrorGaugeAvg μG k₂) z'))
          ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG)
        = ∫ z, k₁ z
            * (planeAvgKernel μG ρ hN β z z'
              * (starRingEnd ℂ) ((mirrorGaugeAvg μG k₂) z'))
            ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG) := by
    intro z'
    have hpt : ∀ z : ↥(posLinks (N := N)) → G,
        (posGaugeAvg μG k₁) z
            * (planeAvgKernel μG ρ hN β z z'
              * (starRingEnd ℂ) ((mirrorGaugeAvg μG k₂) z'))
          = ∫ g, k₁ (gaugePosFun g z)
              * (planeAvgKernel μG ρ hN β z z'
                * (starRingEnd ℂ) ((mirrorGaugeAvg μG k₂) z'))
              ∂(Measure.pi fun _ : (Fin 4 → ZMod N) => μG) := by
      intro z
      unfold posGaugeAvg
      rw [← integral_mul_const]
    have hIntA : Integrable
        (fun p : (↥(posLinks (N := N)) → G)
            × ((Fin 4 → ZMod N) → G) =>
          k₁ (gaugePosFun p.2 p.1)
            * (planeAvgKernel μG ρ hN β p.1 z'
              * (starRingEnd ℂ) ((mirrorGaugeAvg μG k₂) z')))
        ((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
          (Measure.pi fun _ : (Fin 4 → ZMod N) => μG)) := by
      have hsec : AEStronglyMeasurable
          (fun p : (↥(posLinks (N := N)) → G)
              × ((Fin 4 → ZMod N) → G) =>
            planeAvgKernel μG ρ hN β p.1 z'
              * (starRingEnd ℂ) ((mirrorGaugeAvg μG k₂) z'))
          ((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
            (Measure.pi fun _ : (Fin 4 → ZMod N) => μG)) :=
        (((hKmeas.comp
          (measurable_id.prodMk measurable_const)).mul
          measurable_const).aestronglyMeasurable
          ).comp_measurePreserving measurePreserving_fst
      refine Integrable.of_bound
        ((hF₁.comp_measurePreserving
          Measure.measurePreserving_swap).mul hsec)
        (C₁ * ((Real.exp (|β| * (2 * ((plaqIndex (N := N)).card : ℝ)))
              * Real.exp (|β| * (2 * ((plaqIndex (N := N)).card : ℝ))))
            * Real.exp (|β| * (2 * ((plaqIndex (N := N)).card : ℝ)))
          * ‖(starRingEnd ℂ) ((mirrorGaugeAvg μG k₂) z')‖))
        (ae_of_all _ fun p => ?_)
      refine norm_mul3_le (hC₁ _) (hKB _ _) le_rfl hC₁0 hKB0
        (norm_nonneg _)
    have hsub : ∀ g : (Fin 4 → ZMod N) → G,
        ∫ z, k₁ z
            * (planeAvgKernel μG ρ hN β z z'
              * (starRingEnd ℂ) ((mirrorGaugeAvg μG k₂) z'))
            ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG)
          = ∫ z, k₁ (gaugePosFun g z)
              * (planeAvgKernel μG ρ hN β z z'
                * (starRingEnd ℂ) ((mirrorGaugeAvg μG k₂) z'))
              ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG) := by
      intro g
      have hcomp : ∀ w : ↥(posLinks (N := N)) → G,
          gaugePosFun g (gaugePosFun (fun x => (g x)⁻¹) w) = w := by
        intro w
        have e : gaugePosFun g (gaugePosFun (fun x => (g x)⁻¹) w)
            = gaugePosFun (g * (fun x => (g x)⁻¹)) w :=
          (gaugePosFun_mul g _ w).symm
        rw [e, show g * (fun x => (g x)⁻¹)
            = (1 : (Fin 4 → ZMod N) → G) from
          funext fun x => mul_inv_cancel (g x), gaugePosFun_one]
      have hptw : ∀ w : ↥(posLinks (N := N)) → G,
          k₁ w * (planeAvgKernel μG ρ hN β w z'
              * (starRingEnd ℂ) ((mirrorGaugeAvg μG k₂) z'))
            = k₁ (gaugePosFun g (gaugePosFun (fun x => (g x)⁻¹) w))
              * (planeAvgKernel μG ρ hN β
                  (gaugePosFun (fun x => (g x)⁻¹) w) z'
                * (starRingEnd ℂ) ((mirrorGaugeAvg μG k₂) z')) := by
        intro w
        rw [hcomp w,
          planeAvgKernel_gauge_invariant_fst μG ρ hN β
            (fun x => (g x)⁻¹) w z']
      calc ∫ z, k₁ z
              * (planeAvgKernel μG ρ hN β z z'
                * (starRingEnd ℂ) ((mirrorGaugeAvg μG k₂) z'))
              ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG)
          = ∫ w, k₁ (gaugePosFun g (gaugePosFun (fun x => (g x)⁻¹) w))
              * (planeAvgKernel μG ρ hN β
                  (gaugePosFun (fun x => (g x)⁻¹) w) z'
                * (starRingEnd ℂ) ((mirrorGaugeAvg μG k₂) z'))
              ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG) :=
            integral_congr_ae (ae_of_all _ hptw)
        _ = ∫ w, k₁ (gaugePosFun g w)
              * (planeAvgKernel μG ρ hN β w z'
                * (starRingEnd ℂ) ((mirrorGaugeAvg μG k₂) z'))
              ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG) :=
            (measurePreserving_gaugeStratumEquiv μG
              (fun m : ↥(posLinks (N := N)) => m.1)
              (fun x => (g x)⁻¹)).integral_comp'
              (fun w => k₁ (gaugePosFun g w)
                * (planeAvgKernel μG ρ hN β w z'
                  * (starRingEnd ℂ) ((mirrorGaugeAvg μG k₂) z')))
        _ = ∫ z, k₁ (gaugePosFun g z)
              * (planeAvgKernel μG ρ hN β z z'
                * (starRingEnd ℂ) ((mirrorGaugeAvg μG k₂) z'))
              ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG) := rfl
    calc ∫ z, (posGaugeAvg μG k₁) z
            * (planeAvgKernel μG ρ hN β z z'
              * (starRingEnd ℂ) ((mirrorGaugeAvg μG k₂) z'))
            ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG)
        = ∫ z, ∫ g, k₁ (gaugePosFun g z)
            * (planeAvgKernel μG ρ hN β z z'
              * (starRingEnd ℂ) ((mirrorGaugeAvg μG k₂) z'))
            ∂(Measure.pi fun _ : (Fin 4 → ZMod N) => μG)
            ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG) :=
          integral_congr_ae (ae_of_all _ hpt)
      _ = ∫ g, ∫ z, k₁ (gaugePosFun g z)
            * (planeAvgKernel μG ρ hN β z z'
              * (starRingEnd ℂ) ((mirrorGaugeAvg μG k₂) z'))
            ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG)
            ∂(Measure.pi fun _ : (Fin 4 → ZMod N) => μG) :=
          integral_integral_swap hIntA
      _ = ∫ g, ∫ z, k₁ z
            * (planeAvgKernel μG ρ hN β z z'
              * (starRingEnd ℂ) ((mirrorGaugeAvg μG k₂) z'))
            ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG)
            ∂(Measure.pi fun _ : (Fin 4 → ZMod N) => μG) :=
          integral_congr_ae (ae_of_all _ fun g => (hsub g).symm)
      _ = ∫ z, k₁ z
            * (planeAvgKernel μG ρ hN β z z'
              * (starRingEnd ℂ) ((mirrorGaugeAvg μG k₂) z'))
            ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG) := by
          simp [integral_const]
  -- Step B: the second slot's average can be removed, pointwise
  -- in the first argument.
  have hconj : ∀ z' : ↥(posLinks (N := N)) → G,
      (starRingEnd ℂ) ((mirrorGaugeAvg μG k₂) z')
        = ∫ h, (starRingEnd ℂ) (k₂ (gaugeMirrorPos h z'))
            ∂(Measure.pi fun _ : (Fin 4 → ZMod N) => μG) := by
    intro z'
    unfold mirrorGaugeAvg
    exact integral_conj.symm
  have hswapB : ∀ z : ↥(posLinks (N := N)) → G,
      ∫ z', k₁ z
          * (planeAvgKernel μG ρ hN β z z'
            * (starRingEnd ℂ) ((mirrorGaugeAvg μG k₂) z'))
          ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG)
        = ∫ z', k₁ z
            * (planeAvgKernel μG ρ hN β z z'
              * (starRingEnd ℂ) (k₂ z'))
            ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG) := by
    intro z
    have hpt : ∀ z' : ↥(posLinks (N := N)) → G,
        k₁ z * (planeAvgKernel μG ρ hN β z z'
            * (starRingEnd ℂ) ((mirrorGaugeAvg μG k₂) z'))
          = ∫ h, k₁ z
              * (planeAvgKernel μG ρ hN β z z'
                * (starRingEnd ℂ) (k₂ (gaugeMirrorPos h z')))
              ∂(Measure.pi fun _ : (Fin 4 → ZMod N) => μG) := by
      intro z'
      calc k₁ z * (planeAvgKernel μG ρ hN β z z'
              * (starRingEnd ℂ) ((mirrorGaugeAvg μG k₂) z'))
          = (k₁ z * planeAvgKernel μG ρ hN β z z')
              * ∫ h, (starRingEnd ℂ) (k₂ (gaugeMirrorPos h z'))
                ∂(Measure.pi fun _ : (Fin 4 → ZMod N) => μG) := by
            rw [hconj z', mul_assoc]
        _ = ∫ h, (k₁ z * planeAvgKernel μG ρ hN β z z')
              * (starRingEnd ℂ) (k₂ (gaugeMirrorPos h z'))
              ∂(Measure.pi fun _ : (Fin 4 → ZMod N) => μG) := by
            rw [← integral_const_mul]
        _ = ∫ h, k₁ z
              * (planeAvgKernel μG ρ hN β z z'
                * (starRingEnd ℂ) (k₂ (gaugeMirrorPos h z')))
              ∂(Measure.pi fun _ : (Fin 4 → ZMod N) => μG) :=
            integral_congr_ae (ae_of_all _ fun h => mul_assoc _ _ _)
    have hIntB : Integrable
        (fun p : (↥(posLinks (N := N)) → G)
            × ((Fin 4 → ZMod N) → G) =>
          k₁ z * (planeAvgKernel μG ρ hN β z p.1
            * (starRingEnd ℂ) (k₂ (gaugeMirrorPos p.2 p.1))))
        ((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
          (Measure.pi fun _ : (Fin 4 → ZMod N) => μG)) := by
      have hsec : AEStronglyMeasurable
          (fun p : (↥(posLinks (N := N)) → G)
              × ((Fin 4 → ZMod N) → G) =>
            planeAvgKernel μG ρ hN β z p.1)
          ((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
            (Measure.pi fun _ : (Fin 4 → ZMod N) => μG)) :=
        ((hKmeas.comp
          (measurable_const.prodMk
            measurable_id)).aestronglyMeasurable
          ).comp_measurePreserving measurePreserving_fst
      have hstarF : AEStronglyMeasurable
          (fun p : (↥(posLinks (N := N)) → G)
              × ((Fin 4 → ZMod N) → G) =>
            (starRingEnd ℂ) (k₂ (gaugeMirrorPos p.2 p.1)))
          ((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
            (Measure.pi fun _ : (Fin 4 → ZMod N) => μG)) :=
        (hF₃.comp_measurePreserving
          Measure.measurePreserving_swap).star
      refine Integrable.of_bound
        ((measurable_const.aestronglyMeasurable).mul
          (hsec.mul hstarF))
        (C₁ * ((Real.exp (|β| * (2 * ((plaqIndex (N := N)).card : ℝ)))
              * Real.exp (|β| * (2 * ((plaqIndex (N := N)).card : ℝ))))
            * Real.exp (|β| * (2 * ((plaqIndex (N := N)).card : ℝ)))
          * C₂)) (ae_of_all _ fun p => ?_)
      refine norm_mul3_le (hC₁ z) (hKB _ _)
        (by rw [hstar]; exact hC₂ _) hC₁0 hKB0 hC₂0
    have hsub : ∀ h : (Fin 4 → ZMod N) → G,
        ∫ z', k₁ z
            * (planeAvgKernel μG ρ hN β z z'
              * (starRingEnd ℂ) (k₂ z'))
            ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG)
          = ∫ z', k₁ z
              * (planeAvgKernel μG ρ hN β z z'
                * (starRingEnd ℂ) (k₂ (gaugeMirrorPos h z')))
              ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG) := by
      intro h
      have hcomp : ∀ w' : ↥(posLinks (N := N)) → G,
          gaugeMirrorPos h (gaugeMirrorPos (fun x => (h x)⁻¹) w')
            = w' := by
        intro w'
        have e : gaugeMirrorPos h
              (gaugeMirrorPos (fun x => (h x)⁻¹) w')
            = gaugeMirrorPos (h * (fun x => (h x)⁻¹)) w' :=
          (gaugeMirrorPos_mul h _ w').symm
        rw [e, show h * (fun x => (h x)⁻¹)
            = (1 : (Fin 4 → ZMod N) → G) from
          funext fun x => mul_inv_cancel (h x), gaugeMirrorPos_one]
      have hptw : ∀ w' : ↥(posLinks (N := N)) → G,
          k₁ z * (planeAvgKernel μG ρ hN β z w'
              * (starRingEnd ℂ) (k₂ w'))
            = k₁ z * (planeAvgKernel μG ρ hN β z
                  (gaugeMirrorPos (fun x => (h x)⁻¹) w')
                * (starRingEnd ℂ)
                    (k₂ (gaugeMirrorPos h
                      (gaugeMirrorPos (fun x => (h x)⁻¹) w')))) := by
        intro w'
        rw [hcomp w',
          planeAvgKernel_gauge_invariant_snd μG ρ hN β
            (fun x => (h x)⁻¹) z w']
      calc ∫ z', k₁ z
              * (planeAvgKernel μG ρ hN β z z'
                * (starRingEnd ℂ) (k₂ z'))
              ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG)
          = ∫ w', k₁ z * (planeAvgKernel μG ρ hN β z
                  (gaugeMirrorPos (fun x => (h x)⁻¹) w')
                * (starRingEnd ℂ)
                    (k₂ (gaugeMirrorPos h
                      (gaugeMirrorPos (fun x => (h x)⁻¹) w'))))
              ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG) :=
            integral_congr_ae (ae_of_all _ hptw)
        _ = ∫ w', k₁ z
              * (planeAvgKernel μG ρ hN β z w'
                * (starRingEnd ℂ) (k₂ (gaugeMirrorPos h w')))
              ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG) :=
            (measurePreserving_mirrorGaugeEquiv μG
              (fun x => (h x)⁻¹)).integral_comp'
              (fun w' => k₁ z
                * (planeAvgKernel μG ρ hN β z w'
                  * (starRingEnd ℂ) (k₂ (gaugeMirrorPos h w'))))
        _ = ∫ z', k₁ z
              * (planeAvgKernel μG ρ hN β z z'
                * (starRingEnd ℂ) (k₂ (gaugeMirrorPos h z')))
              ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG) := rfl
    calc ∫ z', k₁ z
            * (planeAvgKernel μG ρ hN β z z'
              * (starRingEnd ℂ) ((mirrorGaugeAvg μG k₂) z'))
            ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG)
        = ∫ z', ∫ h, k₁ z
            * (planeAvgKernel μG ρ hN β z z'
              * (starRingEnd ℂ) (k₂ (gaugeMirrorPos h z')))
            ∂(Measure.pi fun _ : (Fin 4 → ZMod N) => μG)
            ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG) :=
          integral_congr_ae (ae_of_all _ hpt)
      _ = ∫ h, ∫ z', k₁ z
            * (planeAvgKernel μG ρ hN β z z'
              * (starRingEnd ℂ) (k₂ (gaugeMirrorPos h z')))
            ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG)
            ∂(Measure.pi fun _ : (Fin 4 → ZMod N) => μG) :=
          integral_integral_swap hIntB
      _ = ∫ h, ∫ z', k₁ z
            * (planeAvgKernel μG ρ hN β z z'
              * (starRingEnd ℂ) (k₂ z'))
            ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG)
            ∂(Measure.pi fun _ : (Fin 4 → ZMod N) => μG) :=
          integral_congr_ae (ae_of_all _ fun h => (hsub h).symm)
      _ = ∫ z', k₁ z
            * (planeAvgKernel μG ρ hN β z z'
              * (starRingEnd ℂ) (k₂ z'))
            ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG) := by
          simp [integral_const]
  -- Assemble.
  unfold planeAvgPairing
  calc (∫ p : (↥(posLinks (N := N)) → G)
          × (↥(posLinks (N := N)) → G),
        (posGaugeAvg μG k₁) p.1
          * (planeAvgKernel μG ρ hN β p.1 p.2
            * (starRingEnd ℂ) ((mirrorGaugeAvg μG k₂) p.2))
        ∂((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
          (Measure.pi fun _ : ↥(posLinks (N := N)) => μG)))
      = ∫ z, ∫ z', (posGaugeAvg μG k₁) z
          * (planeAvgKernel μG ρ hN β z z'
            * (starRingEnd ℂ) ((mirrorGaugeAvg μG k₂) z'))
          ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG)
          ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG) :=
        integral_prod _ hIntAC
    _ = ∫ z', ∫ z, (posGaugeAvg μG k₁) z
          * (planeAvgKernel μG ρ hN β z z'
            * (starRingEnd ℂ) ((mirrorGaugeAvg μG k₂) z'))
          ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG)
          ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG) :=
        integral_integral_swap hIntAC
    _ = ∫ z', ∫ z, k₁ z
          * (planeAvgKernel μG ρ hN β z z'
            * (starRingEnd ℂ) ((mirrorGaugeAvg μG k₂) z'))
          ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG)
          ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG) :=
        integral_congr_ae (ae_of_all _ hswapA)
    _ = ∫ z, ∫ z', k₁ z
          * (planeAvgKernel μG ρ hN β z z'
            * (starRingEnd ℂ) ((mirrorGaugeAvg μG k₂) z'))
          ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG)
          ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG) :=
        integral_integral_swap hIntMid
    _ = ∫ z, ∫ z', k₁ z
          * (planeAvgKernel μG ρ hN β z z'
            * (starRingEnd ℂ) (k₂ z'))
          ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG)
          ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG) :=
        integral_congr_ae (ae_of_all _ hswapB)
    _ = ∫ p : (↥(posLinks (N := N)) → G)
          × (↥(posLinks (N := N)) → G),
        k₁ p.1
          * (planeAvgKernel μG ρ hN β p.1 p.2
            * (starRingEnd ℂ) (k₂ p.2))
        ∂((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
          (Measure.pi fun _ : ↥(posLinks (N := N)) => μG)) :=
        (integral_prod _ hIntFinal).symm

end CrossingSeparate

end ThetLogos
