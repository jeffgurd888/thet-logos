import ThetLogos.LatticeReflection
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# ThetLogos.LatticePositivity — Pitch 4, Stage 1b-B: reflection
positivity proper — the OS form, its kernel form, and the positivity
question carried to a single named analytic input (T1, with the
positivity clause itself PARTIAL)

HONESTY LEDGER (read before citing):

- Everything proved in this file is **T1 finite-lattice
  mathematics** on Stage 0's concrete torus (`Fin 4 → ZMod N`,
  shifts `torusShift N`), at general `(G, ρ)`, general even `N`,
  consuming Stage 1b-A's reflection pack (`LatticeReflection.lean`).

- *(what stands)* The Osterwalder–Schrader sesquilinear form
  `osForm β F H = ⟨θF · H⟩_β` is **constructed** for observables
  `F, H` supported on the **strict positive half** (the links
  `posLinks`: base time `< N/2`, not in the reflection's fixed
  stratum), with `θ` on observables the conjugation-composed
  reflection `reflObs F = conj ∘ F ∘ reflConfig` (the parked-fleet
  gauntlet's ruling). Its sesquilinearity, conjugate symmetry, and
  the reality of its diagonal are **proved**. Its **kernel form**
  is proved: the diagonal is `Z⁻¹` times an explicit integral over
  the split configuration space of
  `conj (f (mirrorP uB)) · f (y₊|₊) · exp (−S (unsplit (y₊, uB)))`.
  **Positivity at `β = 0` is proved** (the form collapses to
  `‖∫ f‖²`). A **Gram-factorization criterion** is proved:
  positivity for a given `β` follows if the Gibbs weight, in the
  split variables, is a finite Gram sum over the strict half.

- *(what does NOT stand — the PARTIAL clause)* Positivity
  `0 ≤ (osForm β F F).re` for general `β > 0` and general `(G, ρ)`
  is **not proved in this module**, and no statement in this module
  implies it. The kernel form reduces it — losslessly — to the
  positivity of the stratum-integrated crossing kernel (the
  Boltzmann factor `exp (−S₀)` of Stage 1b-A's crossing action,
  integrated over the plane links it shares between the halves).
  The standard proof of that kernel's positivity (Osterwalder–
  Schrader; Glimm–Jaffe) expands the crossing Boltzmann factor in
  characters of the gauge group and uses **Peter–Weyl
  orthogonality of matrix coefficients on a general compact
  group** to integrate the plane links. That input is **absent
  from the pinned Mathlib (v4.35.0-rc3)**: grep of the pinned
  library finds no Peter–Weyl theorem and no Schur orthogonality
  for compact groups (its representation theory is finite-group /
  algebraic). The missing lemma is named and priced in the dossier
  `whitepaper/pitch-4-stage-1b-b-2026-10-17.md`. Two naive
  strengthenings are FALSE and are killed there with finite
  counterexamples: positivity with the plane links held fixed
  (the fixed-stratum kernel is not positive), and positivity for
  observables depending on the plane-crossing links themselves
  (the strict-half support class is sharp).

- *(finite-lattice discipline)* "Results in this module are about
  a finite lattice at fixed spacing and volume. Nothing here is a
  continuum result; the words 'continuum', 'ℝ⁴', and 'Poincaré' do
  not describe anything proved in this module."

- *(gap discipline)* "Any gap statement in this module is a
  lattice statement at the stated $(a, L, \beta)$. No continuum
  mass gap is claimed; a lattice gap transfers to the continuum
  only with uniformity in the spacing along the tuning curve,
  which is not proved here or anywhere in this corpus." (This
  module proves no gap statement of any kind; the clause travels
  with the pitch.)

- *(gauge discipline)* "Gauge invariance here is exact invariance
  of a finite lattice action and measure under finite gauge
  transformations. It is not a continuum gauge theory, and this
  module contains no quantized continuum gauge field."

- *(standing charter)* "Parts of the official Clay Yang–Mills
  statement closed by this module: 0."

WHAT THIS MODULE IS, AND IS NOT (Stage 1b decomposition of record —
`whitepaper/gauntlet-parked-fleet-2026-10-17.md` §1): this is
campaign **1b-B only**. Stage 1b-A (structure + action split)
stands whole. With the form, its algebra, its kernel form, and
`β = 0` positivity landed here but general positivity reduced to
the named kernel lemma, the pitch-level shape **PARTIAL-δ**
("reflection positivity stands", = A + B) is **not** claimed: it is
recorded as A + B-form, with B's inequality the single open
clause. No OS scalar product or Hilbert space is constructed
(1b-C), no transfer matrix appears (1b-D).

DESIGN CHOICES (disclosed):

- **The support class is the strict positive half.** The two
  reflection planes carry the fixed link stratum of 1b-A (time
  links based at `N/2 - 1` and `N - 1`). Those links cross the
  planes; they belong to neither open half, and the dossier's
  finite counterexample shows the OS form can be negative for
  observables depending on them. `posLinks` is therefore the
  half's links minus the stratum. Spatial links based in the last
  positive slice (`N/2 - 1`) ARE in `posLinks` (they reflect into
  the second half); time links based there are not (they are the
  stratum).
- **The reflection on observables is conjugation-composed**
  (gauntlet ruling): `reflObs F = conj ∘ F ∘ reflConfig`. The
  diagonal in the bare-pullback convention
  `⟨F∘θ · F̄⟩` is proved equal to this module's diagonal
  (`osForm_bare_eq`), the two differing by a conjugation that the
  proved reality of the diagonal collapses.

This module is NOT in the root import list of the library (the
corpus pattern for recent exhibits); it is verified by a targeted
build.
-/

namespace ThetLogos

open MeasureTheory Finset
open scoped Matrix ENNReal NNReal

/-! ## §1. The link trichotomy: strict positive half, negative
half, plane stratum

Links are split by the base time of their base site: the first
half (`halfLinks`, base time `< N/2`, the closed half including
its plane links), its complement (`negLinks`), the fixed stratum
of the reflection (`planeLinks`, characterized in 1b-A), and the
strict positive half `posLinks = halfLinks \ planeLinks`. -/

section Links

variable {G : Type*} [Group G] {N : ℕ} [NeZero N]

/-- The closed positive half of the link set: links whose base
site has time coordinate `< N / 2`. (Includes the plane links
based at time `N/2 - 1`; see `posLinks` for the strict half.) -/
def halfLinks : Finset (Link (Fin 4 → ZMod N)) :=
  Finset.univ.filter (fun ℓ => (ℓ.1 0).val < N / 2)

theorem mem_halfLinks {ℓ : Link (Fin 4 → ZMod N)} :
    ℓ ∈ halfLinks ↔ (ℓ.1 0).val < N / 2 := by
  simp [halfLinks]

/-- The negative half of the link set: the complement of
`halfLinks`. Defined as the complement so that Stage 1a's
`splitEquiv` applies with `s = halfLinks` verbatim. Reducible,
so that the split type `↥(halfLinks)ᶜ` and `↥negLinks` unify
without friction. -/
@[reducible]
def negLinks : Finset (Link (Fin 4 → ZMod N)) :=
  (halfLinks)ᶜ

theorem mem_negLinks {ℓ : Link (Fin 4 → ZMod N)} :
    ℓ ∈ negLinks ↔ N / 2 ≤ (ℓ.1 0).val := by
  rw [negLinks, Finset.mem_compl, mem_halfLinks, not_lt]

/-- The plane stratum: the links fixed by the link reflection
(1b-A: exactly the time links based at `N/2 - 1` and `N - 1`, at
even `N`). -/
def planeLinks : Finset (Link (Fin 4 → ZMod N)) :=
  Finset.univ.filter (fun ℓ => reflLink ℓ = ℓ)

theorem mem_planeLinks {ℓ : Link (Fin 4 → ZMod N)} :
    ℓ ∈ planeLinks ↔ reflLink ℓ = ℓ := by
  simp [planeLinks]

/-- The **strict positive half**: the links of the closed half
that are not plane links. This is 1b-B's support class. -/
def posLinks : Finset (Link (Fin 4 → ZMod N)) :=
  halfLinks \ planeLinks

theorem mem_posLinks {ℓ : Link (Fin 4 → ZMod N)} :
    ℓ ∈ posLinks ↔ (ℓ.1 0).val < N / 2 ∧ reflLink ℓ ≠ ℓ := by
  rw [posLinks, Finset.mem_sdiff, mem_halfLinks, mem_planeLinks]

theorem posLinks_subset_halfLinks :
    posLinks (N := N) ⊆ halfLinks := by
  intro ℓ hℓ
  exact mem_halfLinks.mpr (mem_posLinks.mp hℓ).1

/-- A plane link is a time link (at even extent): the direction
of a fixed link is `0`, by 1b-A's characterization. -/
theorem planeLinks_dir (hN : Even N) {ℓ : Link (Fin 4 → ZMod N)}
    (hℓ : ℓ ∈ planeLinks) : ℓ.2 = 0 := by
  obtain ⟨x, μ⟩ := ℓ
  rw [mem_planeLinks] at hℓ
  exact ((reflLink_eq_self_iff hN x μ).mp hℓ).1

/-- The time value of a reflected spatial link's base:
`N - 1 - (x 0).val`. -/
theorem reflLink_fst_zero_val_of_ne {x : Fin 4 → ZMod N} {μ : Fin 4}
    (hμ : μ ≠ 0) :
    ((reflLink (x, μ)).1 0).val = N - 1 - (x 0).val := by
  rw [reflLink_of_ne hμ]
  exact reflSite_val_zero x

/-- The time value of a reflected time link's base:
`N - 2 - (x 0).val` (valid when `(x 0).val ≤ N - 2`). -/
theorem reflLink_fst_zero_val_zero {x : Fin 4 → ZMod N}
    (hv : (x 0).val ≤ N - 2) (hN2 : 2 ≤ N) :
    ((reflLink (x, 0)).1 0).val = N - 2 - (x 0).val := by
  have h : (reflLink (x, 0)).1 = refPlaqSite x 0 := by
    rw [reflLink_zero, refPlaqSite_zero]
  rw [h]
  exact refPlaqSite_zero_val x hv hN2

/-- **Transport, positive to negative**: the reflection sends the
strict positive half into the negative half. -/
theorem reflLink_mem_negLinks (hN : Even N)
    {ℓ : Link (Fin 4 → ZMod N)} (hℓ : ℓ ∈ posLinks) :
    reflLink ℓ ∈ negLinks := by
  obtain ⟨x, μ⟩ := ℓ
  rw [mem_posLinks] at hℓ
  rw [mem_negLinks]
  obtain ⟨hlt, hne⟩ := hℓ
  change (x 0).val < N / 2 at hlt
  have h2M : N / 2 * 2 = N := div_two_mul hN
  have hN2 : 2 ≤ N := two_le_of_even hN
  by_cases hμ : μ = 0
  · subst hμ
    -- The time link at base time `N/2 - 1` would be a plane link;
    -- excluded, so the base time is `≤ N/2 - 2`.
    have hneval : (x 0).val ≠ N / 2 - 1 := by
      intro hval
      exact hne (((reflLink_eq_self_iff hN x 0).mpr ⟨rfl, Or.inl hval⟩))
    have hv : (x 0).val ≤ N / 2 - 2 := by omega
    have hv2 : (x 0).val ≤ N - 2 := by omega
    have hval := reflLink_fst_zero_val_zero hv2 hN2
    omega
  · have hval := reflLink_fst_zero_val_of_ne hμ (x := x)
    omega

/-- The reflection of a strict-half link is never a plane link
(the involution would fix the original). -/
theorem reflLink_not_mem_planeLinks {ℓ : Link (Fin 4 → ZMod N)}
    (hℓ : ℓ ∈ posLinks) : reflLink ℓ ∉ planeLinks := by
  rw [mem_posLinks] at hℓ
  intro hm
  rw [mem_planeLinks] at hm
  apply hℓ.2
  have h := reflLink_involutive ℓ
  rw [hm] at h
  exact h

/-- **Transport, negative to positive**: the reflection sends a
negative-half link that is not a plane link into the strict
positive half. -/
theorem reflLink_mem_posLinks (hN : Even N)
    {ℓ : Link (Fin 4 → ZMod N)} (hℓ : ℓ ∈ negLinks)
    (hpl : ℓ ∉ planeLinks) : reflLink ℓ ∈ posLinks := by
  obtain ⟨x, μ⟩ := ℓ
  rw [mem_negLinks] at hℓ
  change N / 2 ≤ (x 0).val at hℓ
  rw [mem_posLinks]
  have h2M : N / 2 * 2 = N := div_two_mul hN
  have hN2 : 2 ≤ N := two_le_of_even hN
  have hne : reflLink (x, μ) ≠ (x, μ) := by
    intro hfix
    exact hpl (mem_planeLinks.mpr hfix)
  have hne2 : reflLink (reflLink (x, μ)) ≠ reflLink (x, μ) := by
    rw [reflLink_involutive]
    exact fun h => hne h.symm
  refine ⟨?_, hne2⟩
  by_cases hμ : μ = 0
  · subst hμ
    -- The time link at base time `N - 1` would be a plane link.
    have hneval : (x 0).val ≠ N - 1 := by
      intro hval
      exact hpl (mem_planeLinks.mpr
        ((reflLink_eq_self_iff hN x 0).mpr ⟨rfl, Or.inr hval⟩))
    have hltN := (x 0).val_lt
    have hv : (x 0).val ≤ N - 2 := by omega
    have hval := reflLink_fst_zero_val_zero hv hN2
    omega
  · have hval := reflLink_fst_zero_val_of_ne hμ (x := x)
    omega

end Links

/-! ## §2. The mirror map and the marginal identities

The reflection, read on configurations, identifies the strict
positive half with the non-plane part of the negative half:
`mirrorP` is that identification on half-configurations. The two
marginal identities of this section say that both halves carry
the same product measure under the two transports (restriction
from the closed half; mirroring from the negative half) — the
measure-theoretic content that the `β = 0` theorem and the Gram
criterion consume. -/

section Mirror

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  {N : ℕ} [NeZero N]

/-- The **mirror map**: a negative-half configuration read on the
strict positive half through the link reflection, with inversion
on time links — exactly the restriction of `reflConfig` to the
strict half (see `reflConfig_apply_pos`). -/
def mirrorP (hN : Even N) (w : ↥(negLinks (N := N)) → G) :
    ↥(posLinks (N := N)) → G :=
  fun ℓ => if ℓ.1.2 = 0
    then (w ⟨reflLink ℓ.1, reflLink_mem_negLinks hN ℓ.2⟩)⁻¹
    else w ⟨reflLink ℓ.1, reflLink_mem_negLinks hN ℓ.2⟩

/-- The restriction of a closed-half configuration to the strict
positive half. -/
def restrictPos (y : ↥(halfLinks (N := N)) → G) :
    ↥(posLinks (N := N)) → G :=
  fun ℓ => y ⟨ℓ.1, posLinks_subset_halfLinks ℓ.2⟩

/-- **The mirror property**: on the strict positive half, the
reflected configuration is the mirror of the original
configuration's negative half. -/
theorem reflConfig_apply_pos (hN : Even N)
    (U : Config (Fin 4 → ZMod N) G) (ℓ : ↥(posLinks (N := N))) :
    reflConfig U ℓ.1
      = mirrorP hN (fun m : ↥(negLinks (N := N)) => U m.1) ℓ := by
  by_cases h : ℓ.1.2 = 0
  · rw [show reflConfig U ℓ.1 = (U (reflLink ℓ.1))⁻¹ from if_pos h,
      show mirrorP hN (fun m : ↥(negLinks (N := N)) => U m.1) ℓ
        = (U (reflLink ℓ.1))⁻¹ from if_pos h]
  · rw [show reflConfig U ℓ.1 = U (reflLink ℓ.1) from if_neg h,
      show mirrorP hN (fun m : ↥(negLinks (N := N)) => U m.1) ℓ
        = U (reflLink ℓ.1) from if_neg h]

variable (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsInvInvariant μG]

/-- **Marginal identity, restriction**: integrating a function of
the strict-half restriction over the closed half's product
measure is integrating it over the strict half's own product
measure. -/
theorem integral_restrictPos (Φ : (↥(posLinks (N := N)) → G) → ℂ) :
    ∫ y : ↥(halfLinks (N := N)) → G, Φ (restrictPos y)
        ∂(Measure.pi fun _ : ↥(halfLinks (N := N)) => μG)
      = ∫ z, Φ z ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG) := by
  classical
  -- The strict half, as a finset of the closed half's index type.
  set s : Finset ↥(halfLinks (N := N)) :=
    Finset.univ.filter (fun ℓ => ℓ.1 ∈ posLinks) with hs
  -- The identification `↥s ≃ ↥posLinks`.
  set e : ↥s ≃ ↥(posLinks (N := N)) :=
    { toFun := fun ℓ => ⟨ℓ.1.1, (Finset.mem_filter.mp ℓ.2).2⟩
      invFun := fun m => ⟨⟨m.1, posLinks_subset_halfLinks m.2⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, m.2⟩⟩
      left_inv := fun ℓ => Subtype.ext (Subtype.ext rfl)
      right_inv := fun m => Subtype.ext rfl } with he
  have hrestr : ∀ y : ↥(halfLinks (N := N)) → G,
      restrictPos y = (fun ℓ : ↥s => y ℓ.1) ∘ e.symm := by
    intro y
    funext m
    rfl
  have step1 : ∫ y : ↥(halfLinks (N := N)) → G, Φ (restrictPos y)
        ∂(Measure.pi fun _ : ↥(halfLinks (N := N)) => μG)
      = ∫ v, Φ (v ∘ e.symm) ∂(Measure.pi fun _ : ↥s => μG) := by
    rw [← integral_pi_restrict μG s (fun v => Φ (v ∘ e.symm))]
    apply integral_congr_ae
    exact ae_of_all _ fun y => congrArg Φ (hrestr y)
  rw [step1]
  -- The transport `v ↦ v ∘ e.symm` is the pi-congruence.
  have hfun : ∀ v : ↥s → G, ∀ m : ↥(posLinks (N := N)),
      (MeasurableEquiv.piCongrLeft (fun _ : ↥(posLinks (N := N)) => G)
        e) v m = v (e.symm m) := by
    intro v m
    have h2 : (MeasurableEquiv.piCongrLeft
          (fun _ : ↥(posLinks (N := N)) => G) e) v (e (e.symm m))
        = v (e.symm m) :=
      MeasurableEquiv.piCongrLeft_apply_apply
        (β := fun _ : ↥(posLinks (N := N)) => G) e v (e.symm m)
    have h3 : e (e.symm m) = m := e.apply_symm_apply m
    rw [h3] at h2
    exact h2
  have step2 : ∫ v, Φ (v ∘ e.symm) ∂(Measure.pi fun _ : ↥s => μG)
      = ∫ v, Φ ((MeasurableEquiv.piCongrLeft
          (fun _ : ↥(posLinks (N := N)) => G) e) v)
          ∂(Measure.pi fun _ : ↥s => μG) := by
    apply integral_congr_ae
    exact ae_of_all _ fun v =>
      congrArg Φ (funext fun m => (hfun v m).symm)
  rw [step2]
  exact (measurePreserving_piCongrLeft (fun _ : ↥(posLinks (N := N)) => μG)
    e).integral_comp (MeasurableEquiv.measurableEmbedding _) Φ

/-- **Marginal identity, mirror**: integrating a function of the
mirror over the negative half's product measure is integrating
it over the strict half's own product measure. The mirror is a
measure-preserving bijection: a coordinate permutation (the link
reflection) composed with per-coordinate inversion on time
links. -/
theorem integral_mirrorP (hN : Even N)
    (Φ : (↥(posLinks (N := N)) → G) → ℂ) :
    ∫ w : ↥(negLinks (N := N)) → G, Φ (mirrorP hN w)
        ∂(Measure.pi fun _ : ↥(negLinks (N := N)) => μG)
      = ∫ z, Φ z ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG) := by
  classical
  -- The non-plane part of the negative half, as a finset of its
  -- index type.
  set t : Finset ↥(negLinks (N := N)) :=
    Finset.univ.filter (fun ℓ => ℓ.1 ∉ planeLinks) with ht
  -- The identification `↥posLinks ≃ ↥t` by the link reflection.
  set e : ↥(posLinks (N := N)) ≃ ↥t :=
    { toFun := fun ℓ => ⟨⟨reflLink ℓ.1, reflLink_mem_negLinks hN ℓ.2⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          reflLink_not_mem_planeLinks ℓ.2⟩⟩
      invFun := fun m => ⟨reflLink m.1.1, reflLink_mem_posLinks hN
        m.1.2 (Finset.mem_filter.mp m.2).2⟩
      left_inv := fun ℓ => Subtype.ext (reflLink_involutive ℓ.1)
      right_inv := fun m => Subtype.ext (Subtype.ext
        (reflLink_involutive m.1.1)) } with he
  -- The transport on half-configurations and its two factors.
  set congrMap : (↥t → G) → (↥(posLinks (N := N)) → G) :=
    fun v ℓ => v (e ℓ) with hcongr
  set invMap : (↥(posLinks (N := N)) → G) → (↥(posLinks (N := N)) → G) :=
    fun z ℓ => if ℓ.1.2 = 0 then (z ℓ)⁻¹ else z ℓ with hinv
  have hT : ∀ w : ↥(negLinks (N := N)) → G,
      mirrorP hN w = invMap (congrMap (fun ℓ : ↥t => w ℓ.1)) := by
    intro w
    funext ℓ
    by_cases h : ℓ.1.2 = 0
    · rw [show mirrorP hN w ℓ
          = (w ⟨reflLink ℓ.1, reflLink_mem_negLinks hN ℓ.2⟩)⁻¹ from if_pos h,
        show invMap (congrMap (fun ℓ : ↥t => w ℓ.1)) ℓ
          = (w ⟨reflLink ℓ.1, reflLink_mem_negLinks hN ℓ.2⟩)⁻¹ from if_pos h]
    · rw [show mirrorP hN w ℓ
          = w ⟨reflLink ℓ.1, reflLink_mem_negLinks hN ℓ.2⟩ from if_neg h,
        show invMap (congrMap (fun ℓ : ↥t => w ℓ.1)) ℓ
          = w ⟨reflLink ℓ.1, reflLink_mem_negLinks hN ℓ.2⟩ from if_neg h]
  have step1 : ∫ w : ↥(negLinks (N := N)) → G, Φ (mirrorP hN w)
        ∂(Measure.pi fun _ : ↥(negLinks (N := N)) => μG)
      = ∫ v, Φ (invMap (congrMap v))
          ∂(Measure.pi fun _ : ↥t => μG) := by
    rw [← integral_pi_restrict μG t (fun v => Φ (invMap (congrMap v)))]
    apply integral_congr_ae
    exact ae_of_all _ fun w => congrArg Φ (hT w)
  rw [step1]
  -- The permutation factor is the pi-congruence along `e.symm`.
  have hfun : ∀ v : ↥t → G, ∀ ℓ : ↥(posLinks (N := N)),
      (MeasurableEquiv.piCongrLeft (fun _ : ↥(posLinks (N := N)) => G)
        e.symm) v ℓ = v (e ℓ) := by
    intro v ℓ
    have h2 : (MeasurableEquiv.piCongrLeft
          (fun _ : ↥(posLinks (N := N)) => G) e.symm) v (e.symm (e ℓ))
        = v (e ℓ) :=
      MeasurableEquiv.piCongrLeft_apply_apply
        (β := fun _ : ↥(posLinks (N := N)) => G) e.symm v (e ℓ)
    have h3 : e.symm (e ℓ) = ℓ := Equiv.symm_apply_apply e ℓ
    rw [h3] at h2
    exact h2
  have hcongrEq : congrMap
      = (MeasurableEquiv.piCongrLeft (fun _ : ↥(posLinks (N := N)) => G)
        e.symm) := by
    funext v ℓ
    exact (hfun v ℓ).symm
  have hcongrMP : MeasurePreserving congrMap
      (Measure.pi fun _ : ↥t => μG)
      (Measure.pi fun _ : ↥(posLinks (N := N)) => μG) := by
    rw [hcongrEq]
    exact measurePreserving_piCongrLeft
      (fun _ : ↥(posLinks (N := N)) => μG) e.symm
  have hinvMeas : Measurable invMap := by
    rw [measurable_pi_iff]
    intro ℓ
    by_cases h : ℓ.1.2 = 0
    · have hfun : (fun z : ↥(posLinks (N := N)) → G => invMap z ℓ)
          = fun z => (z ℓ)⁻¹ :=
        funext fun z => if_pos h
      rw [hfun]
      exact (measurable_pi_apply ℓ).inv
    · have hfun : (fun z : ↥(posLinks (N := N)) → G => invMap z ℓ)
          = fun z => z ℓ :=
        funext fun z => if_neg h
      rw [hfun]
      exact measurable_pi_apply ℓ
  have hinvInv : Function.Involutive invMap := by
    intro z
    funext ℓ
    by_cases h : ℓ.1.2 = 0
    · rw [show invMap (invMap z) ℓ = ((invMap z) ℓ)⁻¹ from if_pos h,
        show invMap z ℓ = (z ℓ)⁻¹ from if_pos h, inv_inv]
    · rw [show invMap (invMap z) ℓ = invMap z ℓ from if_neg h,
        show invMap z ℓ = z ℓ from if_neg h]
  set invEquiv : (↥(posLinks (N := N)) → G) ≃ᵐ
      (↥(posLinks (N := N)) → G) :=
    { toEquiv := ⟨invMap, invMap, hinvInv, hinvInv⟩
      measurable_toFun := hinvMeas
      measurable_invFun := hinvMeas } with hinvE
  have hinvEmb : MeasurableEmbedding invMap :=
    invEquiv.measurableEmbedding
  have hinvMP : MeasurePreserving invMap
      (Measure.pi fun _ : ↥(posLinks (N := N)) => μG)
      (Measure.pi fun _ : ↥(posLinks (N := N)) => μG) := by
    refine measurePreserving_pi
      (f := fun (ℓ : ↥(posLinks (N := N))) (g : G) =>
        if ℓ.1.2 = 0 then g⁻¹ else g)
      (fun _ : ↥(posLinks (N := N)) => μG)
      (fun _ : ↥(posLinks (N := N)) => μG) fun ℓ => ?_
    show MeasurePreserving (fun g : G => if ℓ.1.2 = 0 then g⁻¹ else g)
      μG μG
    by_cases hℓ : ℓ.1.2 = 0
    · rw [show (fun g : G => if ℓ.1.2 = 0 then g⁻¹ else g) = Inv.inv from
        funext fun g => if_pos hℓ]
      exact Measure.measurePreserving_inv μG
    · rw [show (fun g : G => if ℓ.1.2 = 0 then g⁻¹ else g) = id from
        funext fun g => if_neg hℓ]
      exact MeasurePreserving.id μG
  have step2 : ∫ v, Φ (invMap (congrMap v))
        ∂(Measure.pi fun _ : ↥t => μG)
      = ∫ z, Φ (invMap z)
          ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG) := by
    rw [hcongrEq]
    exact (measurePreserving_piCongrLeft
      (fun _ : ↥(posLinks (N := N)) => μG)
      e.symm).integral_comp (MeasurableEquiv.measurableEmbedding _)
      (fun z => Φ (invMap z))
  rw [step2]
  exact hinvMP.integral_comp hinvEmb Φ

end Mirror

/-! ## §3. Dependence and factorization of the action pieces

Stage 1b-A's three action pieces, read through the link
trichotomy: the positive action depends only on the strict-half
restriction of the configuration; the negative action, through
1b-A's reflection swap, only on the mirror of the negative-half
restriction. These are the dependence facts the kernel form
(§5) consumes. -/

section Factors

variable {G : Type*} [Group G] {d : ℕ}
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ))
  {N : ℕ} [NeZero N]

/-- The time value of a shifted base site is the plaquette's
time height, when the height does not wrap the torus. -/
theorem torusShift_fst_zero_val (x : Fin 4 → ZMod N) (μ : Fin 4)
    (h : plaqTimeHi x μ < N) :
    ((torusShift N μ x) 0).val = plaqTimeHi x μ := by
  by_cases hμ : μ = 0
  · subst hμ
    rw [plaqTimeHi_zero] at h ⊢
    have hcast : (((x 0).val + 1 : ℕ) : ZMod N) = x 0 + 1 := by
      rw [Nat.cast_add, Nat.cast_one, ZMod.natCast_zmod_val]
    have h1 : (torusShift N 0 x) 0 = x 0 + 1 := by
      rw [torusShift_apply_coord, Pi.single_eq_same, add_comm]
    rw [h1, ← hcast]
    exact ZMod.val_natCast_of_lt h
  · rw [plaqTimeHi_of_ne x hμ, torusShift_apply_zero_of_ne hμ x]

/-- **Positive plaquettes read only strict-half links.** If two
configurations agree on the strict positive half, every positive
plaquette has the same density in both. -/
theorem plaquetteDensity_eq_of_agree_posLinks (hN : Even N)
    {U V : Config (Fin 4 → ZMod N) G}
    (h : ∀ ℓ ∈ posLinks (N := N), U ℓ = V ℓ)
    {x : Fin 4 → ZMod N} {μ ν : Fin 4} (hμν : μ < ν)
    (hp : IsPosPlaq (x, μ, ν)) :
    plaquetteDensity (torusShift N) ρ U x μ ν
      = plaquetteDensity (torusShift N) ρ V x μ ν := by
  have h2M : N / 2 * 2 = N := div_two_mul hN
  have hN2 : 2 ≤ N := two_le_of_even hN
  have hhi : plaqTimeHi x μ < N / 2 := hp
  have hν0 : ν ≠ 0 :=
    Fin.pos_iff_ne_zero.mp (Fin.lt_of_le_of_lt (Fin.zero_le μ) hμν)
  -- Any of the plaquette's four links lies in the strict half:
  -- its base time is `< N / 2`, and it is not a plane link (a
  -- plane link has direction `0` and base time `N/2 - 1` or
  -- `N - 1`; direction-`μ` links of the plaquette sit at base
  -- time `(x 0).val`, one step below the height).
  have hmem : ∀ (y : Fin 4 → ZMod N) (κ : Fin 4),
      (y 0).val < N / 2 →
      (κ = ν ∨ ((y 0).val = (x 0).val ∧ (κ ≠ 0 ∨ (x 0).val + 1 < N / 2))) →
      (y, κ) ∈ posLinks (N := N) := by
    intro y κ hlt hκ
    rw [mem_posLinks]
    refine ⟨hlt, ?_⟩
    intro hfix
    obtain ⟨hκ0, hval⟩ := (reflLink_eq_self_iff hN y κ).mp hfix
    rcases hκ with rfl | ⟨hy, hκ'⟩
    · exact hν0 hκ0
    · rcases hκ' with hκne | hlt2
      · exact hκne hκ0
      · rcases hval with hval | hval <;> omega
  have hκ : μ ≠ 0 ∨ (x 0).val + 1 < N / 2 := by
    by_cases hμ : μ = 0
    · subst hμ
      exact Or.inr (by rwa [plaqTimeHi_zero] at hhi)
    · exact Or.inl hμ
  have hbase : (x 0).val < N / 2 := by
    by_cases hμ : μ = 0
    · subst hμ
      rw [plaqTimeHi_zero] at hhi
      omega
    · rw [plaqTimeHi_of_ne x hμ] at hhi
      exact hhi
  have e1 : U (x, μ) = V (x, μ) :=
    h _ (hmem x μ hbase (Or.inr ⟨rfl, hκ⟩))
  have e2 : U (torusShift N μ x, ν) = V (torusShift N μ x, ν) := by
    have hlt : ((torusShift N μ x) 0).val < N / 2 := by
      rw [torusShift_fst_zero_val x μ (by omega : plaqTimeHi x μ < N)]
      exact hhi
    exact h _ (hmem (torusShift N μ x) ν hlt (Or.inl rfl))
  have e3 : U (torusShift N ν x, μ) = V (torusShift N ν x, μ) := by
    have hlt : ((torusShift N ν x) 0).val < N / 2 := by
      rw [torusShift_apply_zero_of_ne hν0 x]
      exact hbase
    have hy : ((torusShift N ν x) 0).val = (x 0).val := by
      rw [torusShift_apply_zero_of_ne hν0 x]
    exact h _ (hmem (torusShift N ν x) μ hlt (Or.inr ⟨hy, hκ⟩))
  have e4 : U (x, ν) = V (x, ν) :=
    h _ (hmem x ν hbase (Or.inl rfl))
  unfold plaquetteDensity plaquette
  rw [e1, e2, e3, e4]

/-- The positive action depends only on the strict-half
restriction. -/
theorem wilsonActionPlus_eq_of_agree_posLinks (hN : Even N)
    {U V : Config (Fin 4 → ZMod N) G}
    (h : ∀ ℓ ∈ posLinks (N := N), U ℓ = V ℓ) (β : ℝ) :
    wilsonActionPlus ρ β U = wilsonActionPlus ρ β V := by
  unfold wilsonActionPlus
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.mem_filter] at hp
  obtain ⟨hpI, hpP⟩ := hp
  obtain ⟨x, μ, ν⟩ := p
  exact plaquetteDensity_eq_of_agree_posLinks ρ hN h (mem_plaqIndex hpI) hpP

/-- A strict-half configuration extended by `1` off the half. -/
def extendP (z : ↥(posLinks (N := N)) → G) : Config (Fin 4 → ZMod N) G :=
  fun ℓ => if h : ℓ ∈ posLinks then z ⟨ℓ, h⟩ else 1

theorem extendP_apply {z : ↥(posLinks (N := N)) → G}
    {ℓ : Link (Fin 4 → ZMod N)} (hℓ : ℓ ∈ posLinks) :
    extendP z ℓ = z ⟨ℓ, hℓ⟩ := by
  exact dif_pos hℓ

/-- The positive action as a function of the strict-half
configuration alone. -/
noncomputable def halfActionP (β : ℝ) (z : ↥(posLinks (N := N)) → G) : ℝ :=
  wilsonActionPlus ρ β (extendP z)

theorem wilsonActionPlus_eq_halfActionP (hN : Even N) (β : ℝ)
    (U : Config (Fin 4 → ZMod N) G) :
    wilsonActionPlus ρ β U
      = halfActionP ρ β (fun ℓ : ↥(posLinks (N := N)) => U ℓ.1) := by
  unfold halfActionP
  apply wilsonActionPlus_eq_of_agree_posLinks ρ hN _ β
  intro ℓ hℓ
  rw [extendP_apply hℓ]

/-- **The negative action factors through the mirror**: it is
the positive action of the mirrored negative-half restriction.
(1b-A's swap `S₊ ∘ θ = S₋`, the mirror property, and the
positive factorization.) -/
theorem wilsonActionMinus_eq_halfActionP (hN : Even N) (β : ℝ)
    (U : Config (Fin 4 → ZMod N) G) :
    wilsonActionMinus ρ β U
      = halfActionP ρ β
        (mirrorP hN (fun m : ↥(negLinks (N := N)) => U m.1)) := by
  rw [← wilsonActionPlus_reflConfig ρ hN β U,
    wilsonActionPlus_eq_halfActionP ρ hN β (reflConfig U)]
  congr 1

end Factors

/-! ## §4. The Osterwalder–Schrader form

The reflection on observables is the conjugation-composed
pullback (the gauntlet's ruling): `reflObs F = conj ∘ F ∘ θ`.
The OS form is its Gibbs pairing. This section proves the form
is sesquilinear, conjugate-symmetric, and has real diagonal —
the algebraic half of reflection positivity, which needs no
kernel input. (Conjugation is written `starRingEnd ℂ`, the
Mathlib form of `conj` on `ℂ`.) -/

section Form

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ))
  {N : ℕ} [NeZero N]

/-- The reflection on observables: complex conjugation composed
with pullback along the configuration reflection. -/
def reflObs (F : Config (Fin 4 → ZMod N) G → ℂ) :
    Config (Fin 4 → ZMod N) G → ℂ :=
  fun U => (starRingEnd ℂ) (F (reflConfig U))

theorem reflObs_apply (F : Config (Fin 4 → ZMod N) G → ℂ)
    (U : Config (Fin 4 → ZMod N) G) :
    reflObs F U = (starRingEnd ℂ) (F (reflConfig U)) :=
  rfl

/-- Conjugating a reflected observable undoes the conjugation. -/
theorem reflObs_conj (F : Config (Fin 4 → ZMod N) G → ℂ)
    (U : Config (Fin 4 → ZMod N) G) :
    (starRingEnd ℂ) (reflObs F U) = F (reflConfig U) := by
  show (starRingEnd ℂ) ((starRingEnd ℂ) (F (reflConfig U)))
    = F (reflConfig U)
  rw [starRingEnd_apply, starRingEnd_apply, star_star]

/-- Reflecting a reflected observable undoes the reflection. -/
theorem reflObs_reflConfig (F : Config (Fin 4 → ZMod N) G → ℂ)
    (U : Config (Fin 4 → ZMod N) G) :
    reflObs F (reflConfig U) = (starRingEnd ℂ) (F U) := by
  show (starRingEnd ℂ) (F (reflConfig (reflConfig U)))
    = (starRingEnd ℂ) (F U)
  rw [reflConfig_involutive U]

theorem reflObs_norm (F : Config (Fin 4 → ZMod N) G → ℂ)
    (U : Config (Fin 4 → ZMod N) G) :
    ‖reflObs F U‖ = ‖F (reflConfig U)‖ := by
  rw [reflObs_apply, starRingEnd_apply, norm_star]

/-- The reflected observable is AE strongly measurable against
the Gibbs measure whenever the observable is: the Gibbs measure
is reflection-invariant (1b-A). -/
theorem aesm_reflObs (hρcont : Continuous fun g : G => repMatrix ρ g) (hN : Even N) (β : ℝ)
    {F : Config (Fin 4 → ZMod N) G → ℂ}
    (hF : AEStronglyMeasurable F (gibbsMeasure (torusShift N) μG ρ β)) :
    AEStronglyMeasurable (reflObs F)
      (gibbsMeasure (torusShift N) μG ρ β) := by
  have hF2 : AEStronglyMeasurable F
      (Measure.map reflConfig (gibbsMeasure (torusShift N) μG ρ β)) := by
    rw [gibbsMeasure_map_reflConfig ρ μG hρcont hN β]
    exact hF
  exact (RCLike.continuous_conj).comp_aestronglyMeasurable
    (hF2.comp_measurable measurable_reflConfig)

/-- Boundedness and AE strong measurability give integrability
of the OS integrand against the Gibbs measure. -/
theorem integrable_reflObs_mul (hρcont : Continuous fun g : G => repMatrix ρ g) (hN : Even N) (hd : 0 < d) (β : ℝ)
    {F H : Config (Fin 4 → ZMod N) G → ℂ}
    (hF : AEStronglyMeasurable F (gibbsMeasure (torusShift N) μG ρ β))
    (hH : AEStronglyMeasurable H (gibbsMeasure (torusShift N) μG ρ β))
    (CF CH : ℝ) (hCF : ∀ U, ‖F U‖ ≤ CF) (hCH : ∀ U, ‖H U‖ ≤ CH) :
    Integrable (fun U => reflObs F U * H U)
      (gibbsMeasure (torusShift N) μG ρ β) :=
  integrable_gibbsMeasure_of_bounded (torusShift N) μG ρ hρcont hd β _
    ((aesm_reflObs μG ρ hρcont hN β hF).mul hH) (CF * CH)
    (fun U => by
      calc ‖reflObs F U * H U‖ = ‖reflObs F U‖ * ‖H U‖ := norm_mul _ _
      _ ≤ CF * CH := mul_le_mul
          (by rw [reflObs_norm]; exact hCF _)
          (hCH U) (norm_nonneg _)
          ((norm_nonneg _).trans (hCF (reflConfig U))))

/-- **The Osterwalder–Schrader form**: the Gibbs expectation of
the reflected observable times the observable. -/
noncomputable def osForm (β : ℝ) (F H : Config (Fin 4 → ZMod N) G → ℂ) :
    ℂ :=
  gibbsExpect (torusShift N) μG ρ β (fun U => reflObs F U * H U)

theorem osForm_eq_integral (hρcont : Continuous fun g : G => repMatrix ρ g) (hd : 0 < d) (β : ℝ)
    (F H : Config (Fin 4 → ZMod N) G → ℂ) :
    osForm μG ρ β F H
      = ∫ U, reflObs F U * H U ∂(gibbsMeasure (torusShift N) μG ρ β) :=
  gibbsExpect_eq_integral (torusShift N) μG ρ hρcont hd β _

/-- Reflection substitution under the Gibbs integral (the Gibbs
measure is reflection-invariant, 1b-A). -/
theorem integral_comp_reflConfig (hρcont : Continuous fun g : G => repMatrix ρ g) (hN : Even N) (β : ℝ)
    (Φ : Config (Fin 4 → ZMod N) G → ℂ)
    (hΦ : AEStronglyMeasurable Φ (gibbsMeasure (torusShift N) μG ρ β)) :
    ∫ U, Φ (reflConfig U) ∂(gibbsMeasure (torusShift N) μG ρ β)
      = ∫ U, Φ U ∂(gibbsMeasure (torusShift N) μG ρ β) := by
  have hΦ' : AEStronglyMeasurable Φ
      (Measure.map reflConfig (gibbsMeasure (torusShift N) μG ρ β)) := by
    rw [gibbsMeasure_map_reflConfig ρ μG hρcont hN β]
    exact hΦ
  have h := integral_map measurable_reflConfig.aemeasurable hΦ'
  rw [gibbsMeasure_map_reflConfig ρ μG hρcont hN β] at h
  exact h.symm

/-- **Conjugate symmetry of the OS form** (no positivity input:
reflection-invariance of the Gibbs measure and involutivity). -/
theorem osForm_conj_symm (hρcont : Continuous fun g : G => repMatrix ρ g) (hN : Even N) (hd : 0 < d) (β : ℝ)
    {F H : Config (Fin 4 → ZMod N) G → ℂ}
    (hF : AEStronglyMeasurable F (gibbsMeasure (torusShift N) μG ρ β))
    (hH : AEStronglyMeasurable H (gibbsMeasure (torusShift N) μG ρ β)) :
    osForm μG ρ β F H = (starRingEnd ℂ) (osForm μG ρ β H F) := by
  have hpt : ∀ U : Config (Fin 4 → ZMod N) G,
      reflObs F (reflConfig U) * H (reflConfig U)
        = (starRingEnd ℂ) (reflObs H U * F U) := fun U => by
    rw [map_mul, reflObs_conj, reflObs_reflConfig, mul_comm]
  calc osForm μG ρ β F H
      = ∫ U, reflObs F U * H U ∂(gibbsMeasure (torusShift N) μG ρ β) :=
        osForm_eq_integral μG ρ hρcont hd β F H
    _ = ∫ U, reflObs F (reflConfig U) * H (reflConfig U)
          ∂(gibbsMeasure (torusShift N) μG ρ β) :=
        (integral_comp_reflConfig μG ρ hρcont hN β
          (fun U => reflObs F U * H U)
          ((aesm_reflObs μG ρ hρcont hN β hF).mul hH)).symm
    _ = ∫ U, (starRingEnd ℂ) (reflObs H U * F U)
          ∂(gibbsMeasure (torusShift N) μG ρ β) :=
        integral_congr_ae (ae_of_all _ hpt)
    _ = (starRingEnd ℂ) (∫ U, reflObs H U * F U
          ∂(gibbsMeasure (torusShift N) μG ρ β)) :=
        integral_conj
    _ = (starRingEnd ℂ) (osForm μG ρ β H F) := by
        rw [osForm_eq_integral μG ρ hρcont hd β H F]

/-- The diagonal of the OS form is real. -/
theorem osForm_self_im (hρcont : Continuous fun g : G => repMatrix ρ g) (hN : Even N) (hd : 0 < d) (β : ℝ)
    {F : Config (Fin 4 → ZMod N) G → ℂ}
    (hF : AEStronglyMeasurable F (gibbsMeasure (torusShift N) μG ρ β)) :
    (osForm μG ρ β F F).im = 0 := by
  have h := osForm_conj_symm μG ρ hρcont hN hd β hF hF
  have h2 : (starRingEnd ℂ) (osForm μG ρ β F F) = osForm μG ρ β F F :=
    h.symm
  exact Complex.conj_eq_iff_im.mp h2

/-- Additivity in the second argument (under the boundedness
hypotheses that make every integral honest). -/
theorem osForm_add_right (hρcont : Continuous fun g : G => repMatrix ρ g) (hN : Even N) (hd : 0 < d) (β : ℝ)
    {F H₁ H₂ : Config (Fin 4 → ZMod N) G → ℂ}
    (hF : AEStronglyMeasurable F (gibbsMeasure (torusShift N) μG ρ β))
    (hH₁ : AEStronglyMeasurable H₁ (gibbsMeasure (torusShift N) μG ρ β))
    (hH₂ : AEStronglyMeasurable H₂ (gibbsMeasure (torusShift N) μG ρ β))
    (CF C₁ C₂ : ℝ) (hCF : ∀ U, ‖F U‖ ≤ CF) (hC₁ : ∀ U, ‖H₁ U‖ ≤ C₁)
    (hC₂ : ∀ U, ‖H₂ U‖ ≤ C₂) :
    osForm μG ρ β F (H₁ + H₂)
      = osForm μG ρ β F H₁ + osForm μG ρ β F H₂ := by
  rw [osForm_eq_integral μG ρ hρcont hd β F (H₁ + H₂),
    osForm_eq_integral μG ρ hρcont hd β F H₁,
    osForm_eq_integral μG ρ hρcont hd β F H₂,
    ← integral_add
      (integrable_reflObs_mul μG ρ hρcont hN hd β hF hH₁ CF C₁ hCF hC₁)
      (integrable_reflObs_mul μG ρ hρcont hN hd β hF hH₂ CF C₂ hCF hC₂)]
  apply integral_congr_ae
  exact ae_of_all _ fun U => by
    show reflObs F U * (H₁ + H₂) U
      = reflObs F U * H₁ U + reflObs F U * H₂ U
    rw [Pi.add_apply, mul_add]

/-- Homogeneity in the second argument. -/
theorem osForm_smul_right (hρcont : Continuous fun g : G => repMatrix ρ g) (hd : 0 < d) (β : ℝ) (c : ℂ)
    (F H : Config (Fin 4 → ZMod N) G → ℂ) :
    osForm μG ρ β F (c • H) = c * osForm μG ρ β F H := by
  rw [osForm_eq_integral μG ρ hρcont hd β F (c • H),
    osForm_eq_integral μG ρ hρcont hd β F H, ← integral_const_mul]
  apply integral_congr_ae
  exact ae_of_all _ fun U => by
    show reflObs F U * (c • H) U = c * (reflObs F U * H U)
    rw [Pi.smul_apply, smul_eq_mul]
    ring

/-- Additivity in the first (conjugate-linear) argument. -/
theorem osForm_add_left (hρcont : Continuous fun g : G => repMatrix ρ g) (hN : Even N) (hd : 0 < d) (β : ℝ)
    {F₁ F₂ H : Config (Fin 4 → ZMod N) G → ℂ}
    (hF₁ : AEStronglyMeasurable F₁ (gibbsMeasure (torusShift N) μG ρ β))
    (hF₂ : AEStronglyMeasurable F₂ (gibbsMeasure (torusShift N) μG ρ β))
    (hH : AEStronglyMeasurable H (gibbsMeasure (torusShift N) μG ρ β))
    (C₁ C₂ CH : ℝ) (hC₁ : ∀ U, ‖F₁ U‖ ≤ C₁) (hC₂ : ∀ U, ‖F₂ U‖ ≤ C₂)
    (hCH : ∀ U, ‖H U‖ ≤ CH) :
    osForm μG ρ β (F₁ + F₂) H
      = osForm μG ρ β F₁ H + osForm μG ρ β F₂ H := by
  rw [osForm_eq_integral μG ρ hρcont hd β (F₁ + F₂) H,
    osForm_eq_integral μG ρ hρcont hd β F₁ H,
    osForm_eq_integral μG ρ hρcont hd β F₂ H,
    ← integral_add
      (integrable_reflObs_mul μG ρ hρcont hN hd β hF₁ hH C₁ CH hC₁ hCH)
      (integrable_reflObs_mul μG ρ hρcont hN hd β hF₂ hH C₂ CH hC₂ hCH)]
  apply integral_congr_ae
  exact ae_of_all _ fun U => by
    show reflObs (F₁ + F₂) U * H U
      = reflObs F₁ U * H U + reflObs F₂ U * H U
    rw [show reflObs (F₁ + F₂) U = reflObs F₁ U + reflObs F₂ U from
      map_add (starRingEnd ℂ) _ _, add_mul]

/-- Conjugate-homogeneity in the first argument. -/
theorem osForm_smul_left (hρcont : Continuous fun g : G => repMatrix ρ g) (hd : 0 < d) (β : ℝ) (c : ℂ)
    (F H : Config (Fin 4 → ZMod N) G → ℂ) :
    osForm μG ρ β (c • F) H
      = (starRingEnd ℂ) c * osForm μG ρ β F H := by
  rw [osForm_eq_integral μG ρ hρcont hd β (c • F) H,
    osForm_eq_integral μG ρ hρcont hd β F H, ← integral_const_mul]
  apply integral_congr_ae
  exact ae_of_all _ fun U => by
    show reflObs (c • F) U * H U
      = (starRingEnd ℂ) c * (reflObs F U * H U)
    rw [show reflObs (c • F) U
        = (starRingEnd ℂ) c * reflObs F U from by
      show (starRingEnd ℂ) ((c • F) (reflConfig U))
        = (starRingEnd ℂ) c * (starRingEnd ℂ) (F (reflConfig U))
      rw [Pi.smul_apply, smul_eq_mul, map_mul]]
    ring

/-- **The bare-pullback convention agrees on the diagonal.** The
task's literal form `⟨F∘θ · F̄⟩_Gibbs` (bare pullback in the
first factor, conjugate in the second) equals this module's
diagonal — the two conventions differ by a conjugation, and the
diagonal is real. -/
theorem osForm_bare_eq (hρcont : Continuous fun g : G => repMatrix ρ g) (hN : Even N) (hd : 0 < d) (β : ℝ)
    {F : Config (Fin 4 → ZMod N) G → ℂ}
    (hF : AEStronglyMeasurable F (gibbsMeasure (torusShift N) μG ρ β)) :
    gibbsExpect (torusShift N) μG ρ β
        (fun U => F (reflConfig U) * (starRingEnd ℂ) (F U))
      = osForm μG ρ β F F := by
  have hstar : gibbsExpect (torusShift N) μG ρ β
        (fun U => F (reflConfig U) * (starRingEnd ℂ) (F U))
      = (starRingEnd ℂ) (osForm μG ρ β F F) := by
    rw [gibbsExpect_eq_integral (torusShift N) μG ρ hρcont hd β,
      osForm_eq_integral μG ρ hρcont hd β F F, ← integral_conj]
    apply integral_congr_ae
    exact ae_of_all _ fun U => by
      show F (reflConfig U) * (starRingEnd ℂ) (F U)
        = (starRingEnd ℂ) (reflObs F U * F U)
      rw [map_mul, reflObs_conj, mul_comm]
  rw [hstar]
  exact (osForm_conj_symm μG ρ hρcont hN hd β hF hF).symm

end Form

/-! ## §5. The kernel form

The Gibbs integral, opened up: the measure is the normalized
density against the product Haar measure (Stage 1a's
construction), and the product measure splits across the link
trichotomy (Stage 1a's `splitEquiv`). The diagonal of the OS
form is therefore `Z⁻¹` times an explicit integral over the
split configuration space — the **kernel form** of the form.
In the split variables the full action itself factors as
`S₊(half) + S₋(mirror) + S₀(unsplit)` (Stage 1b-A's split, read
through §3). -/

section Kernel

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ))
  {N : ℕ} [NeZero N]

/-- The Gibbs integral as a density integral against the
product Haar measure (the plumbing of Stage 1a's
`gibbsExpect_eq_integral`, opened one step further). -/
theorem integral_gibbsMeasure
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hd : 0 < d)
    (β : ℝ) (Φ : Config (Fin 4 → ZMod N) G → ℂ) :
    ∫ U, Φ U ∂(gibbsMeasure (torusShift N) μG ρ β)
      = ((gibbsPartition (torusShift N) μG ρ β : ℂ))⁻¹
        * ∫ U, (Real.exp (- wilsonAction (torusShift N) ρ β U) : ℂ) * Φ U
            ∂(configMeasure μG) := by
  have hZ := gibbsPartition_pos (torusShift N) μG ρ hρcont hd β
  have htoReal : (ENNReal.ofReal (gibbsPartition (torusShift N) μG ρ β))⁻¹.toReal
      = (gibbsPartition (torusShift N) μG ρ β)⁻¹ := by
    rw [ENNReal.toReal_inv, ENNReal.toReal_ofReal hZ.le]
  have hInt : ∫ U, Φ U ∂(gibbsMeasure (torusShift N) μG ρ β)
      = (gibbsPartition (torusShift N) μG ρ β)⁻¹
        • ∫ U, (Real.exp (- wilsonAction (torusShift N) ρ β U) : ℂ) * Φ U
            ∂(configMeasure μG) := by
    show ∫ U, Φ U ∂((ENNReal.ofReal (gibbsPartition (torusShift N) μG ρ β))⁻¹
        • (configMeasure μG).withDensity
          (fun U => (gibbsDensity (torusShift N) ρ β U : ℝ≥0∞))) = _
    rw [integral_smul_measure, htoReal,
      integral_withDensity_eq_integral_smul
        (measurable_gibbsDensity (torusShift N) ρ hρcont β) Φ]
    congr 1
  rw [hInt, ← Complex.ofReal_inv, ← Complex.real_smul]

/-- The two restrictions of a split configuration: the
strict-half restriction of the unsplit configuration is
`restrictPos` of the first component, and its negative-half
restriction is the second component. -/
theorem splitEquiv_symm_restrict
    (p : (↥(halfLinks (N := N)) → G) × (↥(negLinks (N := N)) → G)) :
    (fun ℓ : ↥(posLinks (N := N)) =>
        ((splitEquiv (halfLinks (N := N))).symm p) ℓ.1) = restrictPos p.1
    ∧ (fun m : ↥(negLinks (N := N)) =>
        ((splitEquiv (halfLinks (N := N))).symm p) m.1) = p.2 := by
  have happ : (splitEquiv (halfLinks (N := N)))
      ((splitEquiv (halfLinks (N := N))).symm p) = p :=
    MeasurableEquiv.apply_symm_apply _ _
  constructor
  · funext ℓ
    show ((splitEquiv (halfLinks (N := N))).symm p) ℓ.1
      = p.1 ⟨ℓ.1, posLinks_subset_halfLinks ℓ.2⟩
    have h := splitEquiv_fst (halfLinks (N := N))
      ((splitEquiv (halfLinks (N := N))).symm p)
    rw [happ] at h
    exact (congrFun h ⟨ℓ.1, posLinks_subset_halfLinks ℓ.2⟩).symm
  · have h := splitEquiv_snd (halfLinks (N := N))
      ((splitEquiv (halfLinks (N := N))).symm p)
    rw [happ] at h
    exact h.symm

/-- **The action in split variables**: Stage 1b-A's three-way
split, with the positive piece read on the strict half and the
negative piece on the mirror. -/
theorem wilsonAction_split_half (hN : Even N) (β : ℝ)
    (p : (↥(halfLinks (N := N)) → G) × (↥(negLinks (N := N)) → G)) :
    wilsonAction (torusShift N) ρ β ((splitEquiv (halfLinks (N := N))).symm p)
      = halfActionP ρ β (restrictPos p.1)
        + halfActionP ρ β (mirrorP hN p.2)
        + wilsonActionZero ρ β ((splitEquiv (halfLinks (N := N))).symm p) := by
  have hr := splitEquiv_symm_restrict p
  rw [wilsonAction_split ρ β ((splitEquiv (halfLinks (N := N))).symm p),
    wilsonActionPlus_eq_halfActionP ρ hN β
      ((splitEquiv (halfLinks (N := N))).symm p),
    wilsonActionMinus_eq_halfActionP ρ hN β
      ((splitEquiv (halfLinks (N := N))).symm p),
    hr.1, hr.2]

/-- **The kernel form of the OS diagonal.** For an observable
supported on the strict positive half (with factor `f`), the
diagonal is `Z⁻¹` times the split-space integral of the Gibbs
weight times `conj (f (mirror)) · f (half)`. Every factor is
explicit; this identity is the lossless reduction of positivity
to the crossing kernel's Gram property. -/
theorem osForm_eq_kernel
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hN : Even N)
    (hd : 0 < d) (β : ℝ)
    (F : Config (Fin 4 → ZMod N) G → ℂ)
    (f : (↥(posLinks (N := N)) → G) → ℂ)
    (hF : ∀ U, F U = f (fun ℓ : ↥(posLinks (N := N)) => U ℓ.1)) :
    osForm μG ρ β F F
      = ((gibbsPartition (torusShift N) μG ρ β : ℂ))⁻¹
        * ∫ p : (↥(halfLinks (N := N)) → G) × (↥(negLinks (N := N)) → G),
            (Real.exp (- wilsonAction (torusShift N) ρ β
              ((splitEquiv (halfLinks (N := N))).symm p)) : ℂ)
            * ((starRingEnd ℂ) (f (mirrorP hN p.2)) * f (restrictPos p.1))
          ∂((Measure.pi fun _ : ↥(halfLinks (N := N)) => μG).prod
            (Measure.pi fun _ : ↥(negLinks (N := N)) => μG)) := by
  rw [osForm_eq_integral μG ρ hρcont hd β F F,
    integral_gibbsMeasure μG ρ hρcont hd β _]
  congr 1
  have htr : ∫ U, (Real.exp (- wilsonAction (torusShift N) ρ β U) : ℂ)
        * (reflObs F U * F U) ∂(configMeasure μG)
      = ∫ p : (↥(halfLinks (N := N)) → G) × (↥(negLinks (N := N)) → G),
          (Real.exp (- wilsonAction (torusShift N) ρ β
              ((splitEquiv (halfLinks (N := N))).symm p)) : ℂ)
          * (reflObs F ((splitEquiv (halfLinks (N := N))).symm p)
            * F ((splitEquiv (halfLinks (N := N))).symm p))
        ∂((Measure.pi fun _ : ↥(halfLinks (N := N)) => μG).prod
          (Measure.pi fun _ : ↥(negLinks (N := N)) => μG)) := by
    show ∫ U, (Real.exp (- wilsonAction (torusShift N) ρ β U) : ℂ)
        * (reflObs F U * F U) ∂(Measure.pi fun _ : Link (Fin 4 → ZMod N) => μG)
      = _
    rw [show (∫ U, (Real.exp (- wilsonAction (torusShift N) ρ β U) : ℂ)
          * (reflObs F U * F U) ∂(Measure.pi fun _ : Link (Fin 4 → ZMod N) => μG))
        = ∫ U, (fun p : (↥(halfLinks (N := N)) → G)
              × (↥(negLinks (N := N)) → G) =>
            (Real.exp (- wilsonAction (torusShift N) ρ β
                ((splitEquiv (halfLinks (N := N))).symm p)) : ℂ)
            * (reflObs F ((splitEquiv (halfLinks (N := N))).symm p)
              * F ((splitEquiv (halfLinks (N := N))).symm p)))
            ((splitEquiv (halfLinks (N := N))) U)
          ∂(Measure.pi fun _ : Link (Fin 4 → ZMod N) => μG) from
      integral_congr_ae (ae_of_all _ fun U =>
        (congrArg (fun U => (Real.exp (- wilsonAction (torusShift N) ρ β U) : ℂ)
          * (reflObs F U * F U))
          (MeasurableEquiv.symm_apply_apply
            (splitEquiv (halfLinks (N := N))) U)).symm)]
    exact (measurePreserving_splitEquiv μG (halfLinks (N := N))).integral_comp
      (splitEquiv (halfLinks (N := N))).measurableEmbedding
      (fun p : (↥(halfLinks (N := N)) → G) × (↥(negLinks (N := N)) → G) =>
        (Real.exp (- wilsonAction (torusShift N) ρ β
            ((splitEquiv (halfLinks (N := N))).symm p)) : ℂ)
        * (reflObs F ((splitEquiv (halfLinks (N := N))).symm p)
          * F ((splitEquiv (halfLinks (N := N))).symm p)))
  rw [htr]
  refine integral_congr_ae (ae_of_all _ fun p => ?_)
  have hr := splitEquiv_symm_restrict p
  have hfun : (fun ℓ : ↥(posLinks (N := N)) =>
        reflConfig ((splitEquiv (halfLinks (N := N))).symm p) ℓ.1)
      = mirrorP hN p.2 := by
    rw [← hr.2]
    funext ℓ
    exact reflConfig_apply_pos hN _ ℓ
  have hr1 : reflObs F ((splitEquiv (halfLinks (N := N))).symm p)
      = (starRingEnd ℂ) (f (mirrorP hN p.2)) := by
    show (starRingEnd ℂ)
      (F (reflConfig ((splitEquiv (halfLinks (N := N))).symm p))) = _
    rw [hF, hfun]
  have hr2 : F ((splitEquiv (halfLinks (N := N))).symm p)
      = f (restrictPos p.1) := by
    rw [hF, hr.1]
  show (Real.exp (- wilsonAction (torusShift N) ρ β
        ((splitEquiv (halfLinks (N := N))).symm p)) : ℂ)
      * (reflObs F ((splitEquiv (halfLinks (N := N))).symm p)
        * F ((splitEquiv (halfLinks (N := N))).symm p))
    = (Real.exp (- wilsonAction (torusShift N) ρ β
        ((splitEquiv (halfLinks (N := N))).symm p)) : ℂ)
      * ((starRingEnd ℂ) (f (mirrorP hN p.2)) * f (restrictPos p.1))
  rw [hr1, hr2]

end Kernel

/-! ## §6. Positivity: what stands, and the Gram criterion

Two results. **At `β = 0` positivity stands**: the Gibbs weight
is `1`, the split integral factors over the two halves, the two
marginal identities identify both factors with integrals over
the strict half, and the diagonal collapses to `W · W̄` with
`W = ∫ f`. **At general `β` the Gram criterion stands**: if the
Gibbs weight in split variables is a finite Gram sum over the
strict half, the diagonal is a positive combination of squared
norms. Supplying that Gram sum for the Wilson weight is exactly
the character-expansion step whose harmonic-analytic input
(Peter–Weyl orthogonality on a general compact group) is absent
from the pinned Mathlib — see the dossier. -/

section Positivity

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ))
  {N : ℕ} [NeZero N]

/-- **Positivity at `β = 0` stands.** The diagonal of the OS
form at zero coupling is `W · W̄`, where `W` is the strict-half
integral of the observable's factor. -/
theorem osForm_zero_eq (hN : Even N)
    (F : Config (Fin 4 → ZMod N) G → ℂ)
    (f : (↥(posLinks (N := N)) → G) → ℂ)
    (hF : ∀ U, F U = f (fun ℓ : ↥(posLinks (N := N)) => U ℓ.1)) :
    osForm μG ρ 0 F F
      = (∫ z, f z ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG))
        * (starRingEnd ℂ)
          (∫ z, f z ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG)) := by
  show gibbsExpect (torusShift N) μG ρ 0 (fun U => reflObs F U * F U) = _
  rw [gibbsExpect_zero]
  show ∫ U, reflObs F U * F U
      ∂(Measure.pi fun _ : Link (Fin 4 → ZMod N) => μG) = _
  have htr : ∫ U, reflObs F U * F U
        ∂(Measure.pi fun _ : Link (Fin 4 → ZMod N) => μG)
      = ∫ p : (↥(halfLinks (N := N)) → G) × (↥(negLinks (N := N)) → G),
          reflObs F ((splitEquiv (halfLinks (N := N))).symm p)
            * F ((splitEquiv (halfLinks (N := N))).symm p)
        ∂((Measure.pi fun _ : ↥(halfLinks (N := N)) => μG).prod
          (Measure.pi fun _ : ↥(negLinks (N := N)) => μG)) := by
    rw [show (∫ U, reflObs F U * F U
          ∂(Measure.pi fun _ : Link (Fin 4 → ZMod N) => μG))
        = ∫ U, (fun p : (↥(halfLinks (N := N)) → G)
              × (↥(negLinks (N := N)) → G) =>
            reflObs F ((splitEquiv (halfLinks (N := N))).symm p)
              * F ((splitEquiv (halfLinks (N := N))).symm p))
            ((splitEquiv (halfLinks (N := N))) U)
          ∂(Measure.pi fun _ : Link (Fin 4 → ZMod N) => μG) from
      integral_congr_ae (ae_of_all _ fun U =>
        (congrArg (fun U => reflObs F U * F U)
          (MeasurableEquiv.symm_apply_apply
            (splitEquiv (halfLinks (N := N))) U)).symm)]
    exact (measurePreserving_splitEquiv μG (halfLinks (N := N))).integral_comp
      (splitEquiv (halfLinks (N := N))).measurableEmbedding
      (fun p : (↥(halfLinks (N := N)) → G) × (↥(negLinks (N := N)) → G) =>
        reflObs F ((splitEquiv (halfLinks (N := N))).symm p)
          * F ((splitEquiv (halfLinks (N := N))).symm p))
  rw [htr]
  have hpt : ∀ p : (↥(halfLinks (N := N)) → G)
        × (↥(negLinks (N := N)) → G),
      reflObs F ((splitEquiv (halfLinks (N := N))).symm p)
          * F ((splitEquiv (halfLinks (N := N))).symm p)
        = f (restrictPos p.1) * (starRingEnd ℂ) (f (mirrorP hN p.2)) := by
    intro p
    have hr := splitEquiv_symm_restrict p
    have hfun : (fun ℓ : ↥(posLinks (N := N)) =>
          reflConfig ((splitEquiv (halfLinks (N := N))).symm p) ℓ.1)
        = mirrorP hN p.2 := by
      rw [← hr.2]
      funext ℓ
      exact reflConfig_apply_pos hN _ ℓ
    have hr1 : reflObs F ((splitEquiv (halfLinks (N := N))).symm p)
        = (starRingEnd ℂ) (f (mirrorP hN p.2)) := by
      show (starRingEnd ℂ)
        (F (reflConfig ((splitEquiv (halfLinks (N := N))).symm p))) = _
      rw [hF, hfun]
    have hr2 : F ((splitEquiv (halfLinks (N := N))).symm p)
        = f (restrictPos p.1) := by
      rw [hF, hr.1]
    rw [hr1, hr2, mul_comm]
  calc ∫ p : (↥(halfLinks (N := N)) → G) × (↥(negLinks (N := N)) → G),
        reflObs F ((splitEquiv (halfLinks (N := N))).symm p)
          * F ((splitEquiv (halfLinks (N := N))).symm p)
        ∂((Measure.pi fun _ : ↥(halfLinks (N := N)) => μG).prod
          (Measure.pi fun _ : ↥(negLinks (N := N)) => μG))
      = ∫ p : (↥(halfLinks (N := N)) → G) × (↥(negLinks (N := N)) → G),
          f (restrictPos p.1) * (starRingEnd ℂ) (f (mirrorP hN p.2))
        ∂((Measure.pi fun _ : ↥(halfLinks (N := N)) => μG).prod
          (Measure.pi fun _ : ↥(negLinks (N := N)) => μG)) :=
        integral_congr_ae (ae_of_all _ hpt)
    _ = (∫ y, f (restrictPos y)
          ∂(Measure.pi fun _ : ↥(halfLinks (N := N)) => μG))
        * (∫ uB, (starRingEnd ℂ) (f (mirrorP hN uB))
          ∂(Measure.pi fun _ : ↥(negLinks (N := N)) => μG)) :=
        MeasureTheory.integral_prod_mul (fun y => f (restrictPos y))
          (fun uB => (starRingEnd ℂ) (f (mirrorP hN uB)))
    _ = (∫ z, f z ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG))
        * (∫ uB, (starRingEnd ℂ) (f (mirrorP hN uB))
          ∂(Measure.pi fun _ : ↥(negLinks (N := N)) => μG)) :=
        congrArg (· * _) (integral_restrictPos μG f)
    _ = (∫ z, f z ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG))
        * (starRingEnd ℂ)
          (∫ z, f z ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG)) := by
        congr 1
        rw [← integral_conj]
        exact integral_mirrorP μG hN (fun z => (starRingEnd ℂ) (f z))

/-- At `β = 0` the diagonal is a squared norm: nonnegative real
part, vanishing imaginary part. -/
theorem osForm_zero_nonneg (hN : Even N)
    (F : Config (Fin 4 → ZMod N) G → ℂ)
    (f : (↥(posLinks (N := N)) → G) → ℂ)
    (hF : ∀ U, F U = f (fun ℓ : ↥(posLinks (N := N)) => U ℓ.1)) :
    0 ≤ (osForm μG ρ 0 F F).re ∧ (osForm μG ρ 0 F F).im = 0 := by
  set W := ∫ z, f z ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG) with hW
  have hform := osForm_zero_eq μG ρ hN F f hF
  constructor
  · have hre : (osForm μG ρ 0 F F).re = W.re ^ 2 + W.im ^ 2 := by
      rw [hform]
      simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re,
        Complex.conj_im]
      ring
    rw [hre]
    exact add_nonneg (sq_nonneg _) (sq_nonneg _)
  · have him : (osForm μG ρ 0 F F).im = 0 := by
      rw [hform]
      simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re,
        Complex.conj_im]
      ring
    exact him

end Positivity

/-! ## §6b. The transports are measure-preserving, and the Gram
criterion

The two marginal identities of §2 are shadows of genuine
measure-preserving transports (split, project, conjugate by the
mirror equivalence). Making them explicit pays for the
integrability bookkeeping in the Gram criterion. -/

section Gram

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ))
  {N : ℕ} [NeZero N]

/-- The restriction transport to the strict half is
measure-preserving: it factors as a split, a first-coordinate
projection, and a `piCongrLeft` reindexing along the inclusion
equivalence `↥(posLinks-in-half) ≃ ↥posLinks`. -/
theorem measurePreserving_restrictPos :
    MeasurePreserving restrictPos
      (Measure.pi fun _ : ↥(halfLinks (N := N)) => μG)
      (Measure.pi fun _ : ↥(posLinks (N := N)) => μG) := by
  classical
  set s : Finset ↥(halfLinks (N := N)) :=
    Finset.univ.filter (fun ℓ => ℓ.1 ∈ posLinks) with hs
  set e : ↥s ≃ ↥(posLinks (N := N)) :=
    { toFun := fun ℓ => ⟨ℓ.1.1, (Finset.mem_filter.mp ℓ.2).2⟩
      invFun := fun m => ⟨⟨m.1, posLinks_subset_halfLinks m.2⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, m.2⟩⟩
      left_inv := fun ℓ => Subtype.ext (Subtype.ext rfl)
      right_inv := fun m => Subtype.ext rfl } with he
  have key : ∀ (v : ↥s → G) (m : ↥(posLinks (N := N))),
      (MeasurableEquiv.piCongrLeft (fun _ : ↥(posLinks (N := N)) => G)
        e) v m = v (e.symm m) := by
    intro v m
    have h2 : (MeasurableEquiv.piCongrLeft
          (fun _ : ↥(posLinks (N := N)) => G) e) v (e (e.symm m))
        = v (e.symm m) :=
      MeasurableEquiv.piCongrLeft_apply_apply
        (β := fun _ : ↥(posLinks (N := N)) => G) e v (e.symm m)
    have h3 : e (e.symm m) = m := e.apply_symm_apply m
    rw [h3] at h2
    exact h2
  have hfun : restrictPos
      = (MeasurableEquiv.piCongrLeft (fun _ : ↥(posLinks (N := N)) => G) e)
        ∘ (Prod.fst ∘ (splitEquiv s)) := by
    funext y m
    show y ⟨m.1, posLinks_subset_halfLinks m.2⟩
      = (MeasurableEquiv.piCongrLeft (fun _ : ↥(posLinks (N := N)) => G)
          e) ((splitEquiv s y).1) m
    rw [key, splitEquiv_fst]
    show y ⟨m.1, posLinks_subset_halfLinks m.2⟩ = y ((e.symm m).1)
    have hes : (e.symm m).1 = ⟨m.1, posLinks_subset_halfLinks m.2⟩ := rfl
    rw [hes]
  rw [hfun]
  exact (measurePreserving_piCongrLeft (fun _ : ↥(posLinks (N := N)) => μG)
    e).comp (MeasureTheory.measurePreserving_fst.comp
      (measurePreserving_splitEquiv μG s))

/-- The mirror transport from the negative half to the strict
half is measure-preserving: it factors as a split, a
first-coordinate projection, the mirror reindexing, and the
orientation-reversing inversion on time links. -/
theorem measurePreserving_mirrorP (hN : Even N) :
    MeasurePreserving (mirrorP hN)
      (Measure.pi fun _ : ↥(negLinks (N := N)) => μG)
      (Measure.pi fun _ : ↥(posLinks (N := N)) => μG) := by
  classical
  set t : Finset ↥(negLinks (N := N)) :=
    Finset.univ.filter (fun ℓ => ℓ.1 ∉ planeLinks) with ht
  set e : ↥(posLinks (N := N)) ≃ ↥t :=
    { toFun := fun ℓ => ⟨⟨reflLink ℓ.1, reflLink_mem_negLinks hN ℓ.2⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          reflLink_not_mem_planeLinks ℓ.2⟩⟩
      invFun := fun m => ⟨reflLink m.1.1, reflLink_mem_posLinks hN
        m.1.2 (Finset.mem_filter.mp m.2).2⟩
      left_inv := fun ℓ => Subtype.ext (reflLink_involutive ℓ.1)
      right_inv := fun m => Subtype.ext (Subtype.ext
        (reflLink_involutive m.1.1)) } with he
  set congrMap : (↥t → G) → (↥(posLinks (N := N)) → G) :=
    fun v ℓ => v (e ℓ) with hcongr
  set invMap : (↥(posLinks (N := N)) → G) → (↥(posLinks (N := N)) → G) :=
    fun z ℓ => if ℓ.1.2 = 0 then (z ℓ)⁻¹ else z ℓ with hinv
  have key : ∀ (v : ↥t → G) (ℓ : ↥(posLinks (N := N))),
      (MeasurableEquiv.piCongrLeft (fun _ : ↥(posLinks (N := N)) => G)
        e.symm) v ℓ = v (e ℓ) := by
    intro v ℓ
    have h2 : (MeasurableEquiv.piCongrLeft
          (fun _ : ↥(posLinks (N := N)) => G) e.symm) v (e.symm (e ℓ))
        = v (e ℓ) :=
      MeasurableEquiv.piCongrLeft_apply_apply
        (β := fun _ : ↥(posLinks (N := N)) => G) e.symm v (e ℓ)
    have h3 : e.symm (e ℓ) = ℓ := Equiv.symm_apply_apply e ℓ
    rw [h3] at h2
    exact h2
  have hcongrMP : MeasurePreserving congrMap
      (Measure.pi fun _ : ↥t => μG)
      (Measure.pi fun _ : ↥(posLinks (N := N)) => μG) := by
    have hfun : congrMap
        = (MeasurableEquiv.piCongrLeft (fun _ : ↥(posLinks (N := N)) => G)
          e.symm) := by
      funext v ℓ
      exact (key v ℓ).symm
    rw [hfun]
    exact measurePreserving_piCongrLeft
      (fun _ : ↥(posLinks (N := N)) => μG) e.symm
  have hinvMP : MeasurePreserving invMap
      (Measure.pi fun _ : ↥(posLinks (N := N)) => μG)
      (Measure.pi fun _ : ↥(posLinks (N := N)) => μG) := by
    refine measurePreserving_pi
      (f := fun (ℓ : ↥(posLinks (N := N))) (g : G) =>
        if ℓ.1.2 = 0 then g⁻¹ else g)
      (fun _ : ↥(posLinks (N := N)) => μG)
      (fun _ : ↥(posLinks (N := N)) => μG) fun ℓ => ?_
    show MeasurePreserving (fun g : G => if ℓ.1.2 = 0 then g⁻¹ else g)
      μG μG
    by_cases hℓ : ℓ.1.2 = 0
    · rw [show (fun g : G => if ℓ.1.2 = 0 then g⁻¹ else g) = Inv.inv from
        funext fun g => if_pos hℓ]
      exact Measure.measurePreserving_inv μG
    · rw [show (fun g : G => if ℓ.1.2 = 0 then g⁻¹ else g) = id from
        funext fun g => if_neg hℓ]
      exact MeasurePreserving.id μG
  have hfun : mirrorP hN
      = invMap ∘ (congrMap ∘ (Prod.fst ∘ (splitEquiv t))) := by
    funext w ℓ
    show mirrorP hN w ℓ = invMap (congrMap ((splitEquiv t w).1)) ℓ
    have hfst : (splitEquiv t w).1 = fun ℓ : ↥t => w ℓ.1 :=
      splitEquiv_fst t w
    rw [hfst]
    by_cases h : ℓ.1.2 = 0
    · rw [show mirrorP hN w ℓ
          = (w ⟨reflLink ℓ.1, reflLink_mem_negLinks hN ℓ.2⟩)⁻¹ from
          if_pos h,
        show invMap (congrMap (fun ℓ : ↥t => w ℓ.1)) ℓ
          = (w ⟨reflLink ℓ.1, reflLink_mem_negLinks hN ℓ.2⟩)⁻¹ from
          if_pos h]
    · rw [show mirrorP hN w ℓ
          = w ⟨reflLink ℓ.1, reflLink_mem_negLinks hN ℓ.2⟩ from if_neg h,
        show invMap (congrMap (fun ℓ : ↥t => w ℓ.1)) ℓ
          = w ⟨reflLink ℓ.1, reflLink_mem_negLinks hN ℓ.2⟩ from
          if_neg h]
  rw [hfun]
  exact hinvMP.comp (hcongrMP.comp
    (MeasureTheory.measurePreserving_fst.comp
      (measurePreserving_splitEquiv μG t)))

end Gram

/-! ## §6c. The Gram criterion

Positivity at general `β` is *exactly* the statement that the
Gibbs weight, written in split variables, admits a Gram
factorization over the strict half. The criterion below is
lossless: it assumes nothing about `β` (not even its sign) and
concludes the diagonal of the OS form is a nonnegative real —
*provided* the weight is a finite Gram sum `∑ᵢ conj(Ξᵢ∘mirror)
· Ξᵢ∘restrict`. Producing that factorization for the Wilson
weight is the character-expansion step: its standard proof
expands the plaquette Boltzmann factors into irreducible
characters with nonnegative coefficients and integrates the
plane (stratum) variables by Peter–Weyl orthogonality, an input
the pinned Mathlib does not contain for a general compact
group. -/

section GramCriterion

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ))
  {N : ℕ} [NeZero N]

/-- **The Gram criterion.** If the Gibbs weight in split
variables is a finite Gram sum over the strict half (with
bounded measurable features `Ξᵢ`), then the diagonal of the OS
form at that `β` — any real `β` — is a nonnegative real number:
`Z⁻¹ · ∑ᵢ ‖∫ f · Ξᵢ‖²`-shaped, proved here as a cast of a
nonnegative real with vanishing imaginary part. -/
theorem osForm_nonneg_of_gram
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hN : Even N)
    (hd : 0 < d) (β : ℝ)
    (F : Config (Fin 4 → ZMod N) G → ℂ)
    (f : (↥(posLinks (N := N)) → G) → ℂ)
    (hF : ∀ U, F U = f (fun ℓ : ↥(posLinks (N := N)) => U ℓ.1))
    (hfA : AEStronglyMeasurable f
      (Measure.pi fun _ : ↥(posLinks (N := N)) => μG))
    (Cf : ℝ) (hfB : ∀ z, ‖f z‖ ≤ Cf)
    {ι : Type*} [Fintype ι]
    (Ξ : ι → (↥(posLinks (N := N)) → G) → ℂ)
    (hΞA : ∀ i, AEStronglyMeasurable (Ξ i)
      (Measure.pi fun _ : ↥(posLinks (N := N)) => μG))
    (CΞ : ℝ) (hΞB : ∀ i z, ‖Ξ i z‖ ≤ CΞ)
    (hgram : ∀ (y : ↥(halfLinks (N := N)) → G)
      (u : ↥(negLinks (N := N)) → G),
      (Real.exp (- wilsonAction (torusShift N) ρ β
        ((splitEquiv (halfLinks (N := N))).symm (y, u))) : ℂ)
      = ∑ i, (starRingEnd ℂ) (Ξ i (mirrorP hN u))
          * Ξ i (restrictPos y)) :
    0 ≤ (osForm μG ρ β F F).re ∧ (osForm μG ρ β F F).im = 0 := by
  classical
  set Φ : ι → (↥(posLinks (N := N)) → G) → ℂ :=
    fun i z => f z * Ξ i z with hΦ
  have hΦA : ∀ i, AEStronglyMeasurable (Φ i)
      (Measure.pi fun _ : ↥(posLinks (N := N)) => μG) :=
    fun i => hfA.mul (hΞA i)
  have hΦB : ∀ i z, ‖Φ i z‖ ≤ Cf * CΞ := fun i z =>
    (norm_mul _ _).le.trans (mul_le_mul (hfB z) (hΞB i z)
      (norm_nonneg _) ((norm_nonneg _).trans (hfB z)))
  have hIntA : ∀ i, Integrable (Φ i ∘ restrictPos)
      (Measure.pi fun _ : ↥(halfLinks (N := N)) => μG) := by
    intro i
    have hmap : Measure.map restrictPos
        (Measure.pi fun _ : ↥(halfLinks (N := N)) => μG)
        = Measure.pi fun _ : ↥(posLinks (N := N)) => μG :=
      (measurePreserving_restrictPos μG).map_eq
    have h2 : Integrable (Φ i) (Measure.map restrictPos
        (Measure.pi fun _ : ↥(halfLinks (N := N)) => μG)) := by
      rw [hmap]
      exact Integrable.of_bound (hΦA i) (Cf * CΞ) (ae_of_all _ (hΦB i))
    have hA' : AEStronglyMeasurable (Φ i) (Measure.map restrictPos
        (Measure.pi fun _ : ↥(halfLinks (N := N)) => μG)) := by
      rw [hmap]
      exact hΦA i
    exact (integrable_map_measure hA'
      (measurePreserving_restrictPos μG).measurable.aemeasurable).mp h2
  have hIntB : ∀ i, Integrable
      (fun u => (starRingEnd ℂ) (Φ i (mirrorP hN u)))
      (Measure.pi fun _ : ↥(negLinks (N := N)) => μG) := by
    intro i
    refine Integrable.of_bound ?_ (Cf * CΞ) (ae_of_all _ ?_)
    · exact (RCLike.continuous_conj).comp_aestronglyMeasurable
        ((hΦA i).comp_measurePreserving (measurePreserving_mirrorP μG hN))
    · intro u
      rw [starRingEnd_apply, norm_star]
      exact hΦB i _
  have hInt : ∀ i, Integrable
      (fun p : (↥(halfLinks (N := N)) → G) × (↥(negLinks (N := N)) → G) =>
        Φ i (restrictPos p.1) * (starRingEnd ℂ) (Φ i (mirrorP hN p.2)))
      ((Measure.pi fun _ : ↥(halfLinks (N := N)) => μG).prod
        (Measure.pi fun _ : ↥(negLinks (N := N)) => μG)) :=
    fun i => (hIntA i).mul_prod (hIntB i)
  have hZ : 0 < gibbsPartition (torusShift N) μG ρ β :=
    gibbsPartition_pos (torusShift N) μG ρ hρcont hd β
  have hmain : osForm μG ρ β F F
      = ((gibbsPartition (torusShift N) μG ρ β : ℂ))⁻¹
        * ∑ i, (∫ z, Φ i z ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG))
            * (starRingEnd ℂ) (∫ z, Φ i z
              ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG)) := by
    rw [osForm_eq_kernel μG ρ hρcont hN hd β F f hF]
    congr 1
    have hpt : ∀ p : (↥(halfLinks (N := N)) → G)
          × (↥(negLinks (N := N)) → G),
        (Real.exp (- wilsonAction (torusShift N) ρ β
            ((splitEquiv (halfLinks (N := N))).symm p)) : ℂ)
          * ((starRingEnd ℂ) (f (mirrorP hN p.2)) * f (restrictPos p.1))
        = ∑ i, Φ i (restrictPos p.1)
            * (starRingEnd ℂ) (Φ i (mirrorP hN p.2)) := by
      intro p
      show (Real.exp (- wilsonAction (torusShift N) ρ β
            ((splitEquiv (halfLinks (N := N))).symm (p.1, p.2))) : ℂ)
          * ((starRingEnd ℂ) (f (mirrorP hN p.2)) * f (restrictPos p.1))
        = ∑ i, Φ i (restrictPos p.1)
            * (starRingEnd ℂ) (Φ i (mirrorP hN p.2))
      rw [hgram p.1 p.2, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      show (starRingEnd ℂ) (Ξ i (mirrorP hN p.2)) * Ξ i (restrictPos p.1)
          * ((starRingEnd ℂ) (f (mirrorP hN p.2)) * f (restrictPos p.1))
        = (f (restrictPos p.1) * Ξ i (restrictPos p.1))
          * (starRingEnd ℂ) (f (mirrorP hN p.2) * Ξ i (mirrorP hN p.2))
      rw [map_mul]; ring
    rw [integral_congr_ae (ae_of_all _ hpt),
      MeasureTheory.integral_finsetSum Finset.univ (fun i _ => hInt i)]
    apply Finset.sum_congr rfl
    intro i _
    calc ∫ p : (↥(halfLinks (N := N)) → G) × (↥(negLinks (N := N)) → G),
          Φ i (restrictPos p.1) * (starRingEnd ℂ) (Φ i (mirrorP hN p.2))
          ∂((Measure.pi fun _ : ↥(halfLinks (N := N)) => μG).prod
            (Measure.pi fun _ : ↥(negLinks (N := N)) => μG))
        = (∫ y, Φ i (restrictPos y)
            ∂(Measure.pi fun _ : ↥(halfLinks (N := N)) => μG))
          * (∫ u, (starRingEnd ℂ) (Φ i (mirrorP hN u))
            ∂(Measure.pi fun _ : ↥(negLinks (N := N)) => μG)) :=
          MeasureTheory.integral_prod_mul (fun y => Φ i (restrictPos y))
            (fun u => (starRingEnd ℂ) (Φ i (mirrorP hN u)))
      _ = (∫ z, Φ i z ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG))
          * (∫ u, (starRingEnd ℂ) (Φ i (mirrorP hN u))
            ∂(Measure.pi fun _ : ↥(negLinks (N := N)) => μG)) :=
          congrArg (· * _) (integral_restrictPos μG (Φ i))
      _ = (∫ z, Φ i z ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG))
          * (starRingEnd ℂ) (∫ z, Φ i z
            ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG)) := by
          congr 1
          rw [← integral_conj]
          exact integral_mirrorP μG hN (fun z => (starRingEnd ℂ) (Φ i z))
  have hsum : ∑ i, (∫ z, Φ i z
        ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG))
        * (starRingEnd ℂ) (∫ z, Φ i z
          ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG))
      = ((∑ i, ‖∫ z, Φ i z
          ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG)‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact (Complex.mul_conj' _).trans (Complex.ofReal_pow _ _).symm
  rw [hmain, hsum, ← Complex.ofReal_inv, ← Complex.ofReal_mul]
  constructor
  · rw [Complex.ofReal_re]
    exact mul_nonneg (inv_nonneg.mpr hZ.le)
      (Finset.sum_nonneg fun i _ => pow_nonneg (norm_nonneg _) _)
  · rw [Complex.ofReal_im]

end GramCriterion
