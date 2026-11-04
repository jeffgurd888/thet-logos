import ThetLogos.PositivityPropagation
import ThetLogos.LatticeBlockingFlow

/-!
# ThetLogos.BlockedKernelDiagNotOne — TCS T4: K-PROP-FORM promoted
to a theorem

Lane build (TCS T4, fired by Jeff's word "Go" 2026-11-04, per the
registered shape in the TCS scoping dossier
`~/workspace/your_files/thermal-charge-separation-scoping-2026-11-04.md`
§3-T4). Built in the isolated worktree `~/workspace/thet-logos-tcs-t4`,
branch `tcs-t4-lane`, from main-tree HEAD `d6f17cf`. NOT integrated —
the parent runs the integration.

## What this module is

**K-PROP-FORM, promoted from T2 to T1.** PROP-2-PROBE (in
`positivity-propagation-landing-2026-11-03.md` §1) fired K-PROP-FORM
at probe grade: at the seat `(N = 2, G = Multiplicative (ZMod 2),
sign character, uniform probability measure)`, the fiber-integrated
blocked layer kernel of PROP-0 (`blockedLayerKernel`, landed in
`PositivityPropagation.lean`) has diagonal `(A'⁸ + B'⁸)³ ≠ 1` at
every sampled `β ≠ 0`, while every Wilson layer kernel at the coarse
seat has diagonal exactly `1` — so the blocked kernel is not of
Wilson layer form. That was a numerical probe (T2). This module
proves, at T1, about the *landed* `blockedLayerKernel` definition
itself, at the probe's exact seat:

> **for every coarse configuration `U` and every `β ≠ 0`,
> `blockedLayerKernel μG₀ flowSignRep hN β U U ≠ 1`.**

The proof does NOT evaluate the probe's closed form `(A'⁸ + B'⁸)³`
(the fiber character sum is not reproduced); it proves the strict
separation directly: the blocked diagonal is a positive real
`J(β)` (an average of Boltzmann factors `exp (−layerAction)` over
the fiber × fiber × stratum probability space), and

* every Boltzmann factor is `≤ 1` when `β > 0` (resp. `≥ 1` when
  `β < 0`), since each plaquette density lies in `[0, 2]`;
* on an explicit rectangle of measure `1/16` (two stratum
  coordinates and one fiber coordinate on each side pinned), one
  plaquette word is forced to the nonidentity element, its density
  is exactly `2`, the action is `≥ 2β` (resp. `≤ 2β`), and the
  factor is `≤ exp (−2β) < 1` (resp. `≥ exp (−2β) > 1`).

Hence `J(β) ≤ 1 − (1 − exp (−2β))/16 < 1` for `β > 0` and
`J(β) ≥ 1 + (exp (−2β) − 1)/16 > 1` for `β < 0`. In particular the
theorem holds at every probe sample point `β ∈ {−1, 0.5, 1, 2}`.

**K-TCS-SCALE did NOT fire**: at no `β ≠ 0` in the stated range
(all of `(0, ∞)` and `(−∞, 0)`) does the promoted computation
return diagonal `= 1`; form-non-preservation under one blocking
step is a theorem at this seat, not a probe.

## Discrepancy note (on the face)

The firing brief named a module `Span3BlockDiagClosedForm.lean`
with declarations `exppoly`, `blockDiagExp`, `block_kernel_diag_eq`,
`diagKernelDiag` and measured values (diagonal `0.48456790192851827`
at `β = 1`; K-side values `0.9305071207660656 / 0.9106595539283076`;
trace `5.7785505194669195`; jump gap `0.019847566837758`). A
tree-wide search of the corpus, the whitepaper, and `your_files`
finds **no such module, declarations, or numbers anywhere**. The
verifiable record of K-PROP-FORM is PROP-2-PROBE (§1 of the
propagation landing dossier and its probe output): seat as above,
closed form `(A'⁸ + B'⁸)³`, `β = 1` diagonal `1.729662e-06`. This
build therefore promotes the *registered* T4 statement (TCS
scoping §3-T4: a proved statement about the landed
`blockedLayerKernel` at the probe's explicit seat data) against
the objects that exist. If a second measured configuration was
intended, it is not in the tree and would need pinning.

NO CLAIM; parts of the Clay statement closed: 0; dials 0/4.
Nothing here proves or refutes `LayerKernelPos`, FACT, or any
continuum statement. One blocking step, one finite seat.
-/

namespace ThetLogos

open MeasureTheory Finset
open scoped ENNReal NNReal

/-! ## §0. The probe seat, pinned

`N = 2` (so the coarse layer is `N / 2 = 1`), the seat group
`Multiplicative (ZMod 2)`, its sign character `flowSignRep`, and
the uniform probability measure `μG₀` — the exact seat data of
PROP-2-PROBE, all landed (`LatticeBlockingFlow`). -/

/-- The evenness datum for the probe seat `N = 2`. -/
theorem blockedSeatH : Even 2 := ⟨1, rfl⟩

instance : NeZero (2 / 2) := ⟨by norm_num⟩

/-- The fiber measure of the blocked kernel at the seat: the pi
measure over coarse links of the pi measure over the `Fin 7`
octet tails, each factor the uniform probability measure `μG₀`.
This is the measure in the landed `blockedLayerKernel` at
`N = 2`, named once for the statements below. -/
noncomputable def blockedSeatFiberMeasure :
    Measure (LayerLink (2 / 2) → (Fin 7 → Multiplicative (ZMod 2))) :=
  Measure.pi fun _ : LayerLink (2 / 2) =>
    Measure.pi fun _ : Fin 7 => μG₀

/-- The stratum measure at the seat: the pi measure over layer
sites of `μG₀`. This is the measure in the landed `layerKernel`
at `N = 2`. -/
noncomputable def blockedSeatStratumMeasure :
    Measure (LayerSite 2 → Multiplicative (ZMod 2)) :=
  Measure.pi fun _ : LayerSite 2 => μG₀

instance : IsProbabilityMeasure blockedSeatFiberMeasure := by
  unfold blockedSeatFiberMeasure
  infer_instance

instance : IsProbabilityMeasure blockedSeatStratumMeasure := by
  unfold blockedSeatStratumMeasure
  infer_instance

/-- The distinguished layer site of the seat: spatial coordinates
`(1, 0, 0)` (time coordinate `0`). Its octet index is `1`, so the
link over it in direction `2` reads a fiber (tail) coordinate of
the assembly, not the corrected head. -/
def blockedSeatSite : LayerSite 2 :=
  ⟨fun j => if j = 1 then (1 : ZMod 2) else 0, by
    show ((if (0 : Fin 4) = 1 then (1 : ZMod 2) else 0)).val = 0
    rw [ite_eq_right (by decide)]
    exact ZMod.val_zero⟩

theorem blockedSeatSite_apply (j : Fin 4) :
    blockedSeatSite.1 j = if j = 1 then (1 : ZMod 2) else 0 := rfl

/-- The spatial shift of the distinguished site in direction `2`:
coordinates `(1, 1, 0)`. A different site. -/
def blockedSeatSite' : LayerSite 2 :=
  layerShift 2 (by decide) blockedSeatSite

theorem blockedSeatSite'_apply (j : Fin 4) :
    blockedSeatSite'.1 j = torusShift 2 2 blockedSeatSite.1 j := rfl

theorem blockedSeatSite'_ne : blockedSeatSite' ≠ blockedSeatSite := by
  have h20 : blockedSeatSite.1 2 = 0 := by
    rw [blockedSeatSite_apply]
    exact ite_eq_right (by decide)
  intro h
  have h2 := congrFun (congrArg Subtype.val h) 2
  rw [blockedSeatSite'_apply, torusShift_apply_coord,
    Pi.single_eq_same, h20, add_zero] at h2
  exact (by decide : ¬ ((1 : ZMod 2) = 0)) h2

/-- The distinguished fine link: over `blockedSeatSite` in
direction `2`. -/
def blockedSeatLink : LayerLink 2 :=
  layerLinkOf blockedSeatSite 2 (by decide)

/-- The octet decomposition of the distinguished link: coarse
link `layerCoarseLink blockedSeatH blockedSeatLink`, offset `1`
(the first tail offset — the site has spatial coordinates
`(1, 0, 0)`, so its octet index is `1`). -/
theorem blockedSeatLink_octet :
    (layerOctetEquiv blockedSeatH) blockedSeatLink
      = (layerCoarseLink blockedSeatH blockedSeatLink, 1) := by
  have h1 : blockedSeatSite.1 1 = 1 := rfl
  have h2 : blockedSeatSite.1 2 = 0 := by
    rw [blockedSeatSite_apply]
    exact ite_eq_right (by decide)
  have h3 : blockedSeatSite.1 3 = 0 := by
    rw [blockedSeatSite_apply]
    exact ite_eq_right (by decide)
  refine Prod.ext rfl (Fin.ext ?_)
  show (blockedSeatSite.1 1).val % 2
      + 2 * ((blockedSeatSite.1 2).val % 2)
      + 4 * ((blockedSeatSite.1 3).val % 2) = (1 : Fin 8).val
  rw [h1, h2, h3]
  decide

/-- The coarse link under the distinguished fine link, named. -/
def blockedSeatCoarseLink : LayerLink (2 / 2) :=
  layerCoarseLink blockedSeatH blockedSeatLink

/-- **Assembly at the distinguished link.** At octet offset `1`
the assembly reads the first tail coordinate of the fiber: for
every coarse datum `U` and fiber `w`, the assembled configuration
at `blockedSeatLink` is `w blockedSeatCoarseLink 0`. This is
what makes the distinguished plaquette word fiber-controllable. -/
theorem blockedSeatAsm_apply (U : LayerLink (2 / 2) → Multiplicative (ZMod 2))
    (w : LayerLink (2 / 2) → (Fin 7 → Multiplicative (ZMod 2))) :
    layerBlockAsm blockedSeatH U w blockedSeatLink
      = w blockedSeatCoarseLink 0 := by
  show layerOctetAsm (U ((layerOctetEquiv blockedSeatH) blockedSeatLink).1)
      (w ((layerOctetEquiv blockedSeatH) blockedSeatLink).1)
      ((layerOctetEquiv blockedSeatH) blockedSeatLink).2 = _
  rw [blockedSeatLink_octet]
  show layerOctetAsm (U blockedSeatCoarseLink) (w blockedSeatCoarseLink) 1
    = w blockedSeatCoarseLink 0
  unfold layerOctetAsm
  rw [show (1 : Fin 8) = Fin.succ 0 from Fin.ext rfl, Fin.cons_succ]

/-! ## §1. The distinguished plaquette word at the seat

The plaquette of the layer configuration at the distinguished
site, in directions `(0, 2)`, is the one-layer word
`α c * u' ℓ * (α c')⁻¹ * (u ℓ)⁻¹` (the corpus's `layerConfig`
reading lemmas), where `c'` is the direction-`2` shift of `c`
and `ℓ` is the distinguished link. At the seat group every
element is self-inverse and the group is abelian, so the sign of
the word is the product of the four signs. -/

/-- The distinguished plaquette word, read off `layerConfig`. -/
theorem blockedSeatPlaquette_word (α : LayerSite 2 → Multiplicative (ZMod 2))
    (v v' : LayerLink 2 → Multiplicative (ZMod 2)) :
    plaquette (torusShift 2) (layerConfig α v v') blockedSeatSite.1 0 2
      = α blockedSeatSite * v' blockedSeatLink
        * (α blockedSeatSite')⁻¹ * (v blockedSeatLink)⁻¹ := by
  have h1 := layerConfig_time α v v' blockedSeatSite
  have h2 := layerConfig_up blockedSeatH α v v' blockedSeatSite 2 (by decide)
  have h3 := layerConfig_time α v v' blockedSeatSite'
  have h4 := layerConfig_spatial α v v' blockedSeatSite 2 (by decide)
  show layerConfig α v v' (blockedSeatSite.1, 0)
      * layerConfig α v v' ((torusShift 2 0) blockedSeatSite.1, 2)
      * (layerConfig α v v' (blockedSeatSite'.1, 0))⁻¹
      * (layerConfig α v v' (blockedSeatSite.1, 2))⁻¹ = _
  rw [h1, h2, h3, h4]
  rfl

/-- Every plaquette density at the seat lies in `[0, 2]`
(the corpus's general bound at `d = 1`). -/
theorem blockedSeatDensity_mem (U : Config (Fin 4 → ZMod 2)
    (Multiplicative (ZMod 2))) (x : Fin 4 → ZMod 2) (μ ν : Fin 4) :
    plaquetteDensity (torusShift 2) flowSignRep U x μ ν ∈ Set.Icc (0 : ℝ) 2 :=
  plaquetteDensity_mem_Icc (torusShift 2) flowSignRep (by norm_num) U x μ ν

/-! ## §2. The seat action: sign and the distinguished plaquette

`layerAction` at the seat is `β` times a sum of densities, each
in `[0, 2]`; so the action has the sign of `β`, and once the
distinguished plaquette's density is known to be `2`, the action
is past `2β` on the appropriate side. The Boltzmann factor
`exp (−action)` inherits both bounds. -/

/-- The density sum inside the seat action, named. -/
noncomputable def blockedSeatDensitySum
    (α : LayerSite 2 → Multiplicative (ZMod 2))
    (v v' : LayerLink 2 → Multiplicative (ZMod 2)) : ℝ :=
  ∑ c : LayerSite 2, ∑ ν ∈ Finset.Ioi (0 : Fin 4),
    plaquetteDensity (torusShift 2) flowSignRep (layerConfig α v v') c.1 0 ν

theorem blockedSeatDensitySum_nonneg
    (α : LayerSite 2 → Multiplicative (ZMod 2))
    (v v' : LayerLink 2 → Multiplicative (ZMod 2)) :
    0 ≤ blockedSeatDensitySum α v v' :=
  Finset.sum_nonneg fun c _ => Finset.sum_nonneg fun ν _ =>
    (blockedSeatDensity_mem _ c.1 0 ν).1

/-- The density sum is at least the distinguished plaquette's
density (every summand is nonnegative). -/
theorem blockedSeatDensitySum_ge
    (α : LayerSite 2 → Multiplicative (ZMod 2))
    (v v' : LayerLink 2 → Multiplicative (ZMod 2)) :
    plaquetteDensity (torusShift 2) flowSignRep (layerConfig α v v')
        blockedSeatSite.1 0 2 ≤ blockedSeatDensitySum α v v' := by
  have hinner : plaquetteDensity (torusShift 2) flowSignRep
        (layerConfig α v v') blockedSeatSite.1 0 2
      ≤ ∑ ν ∈ Finset.Ioi (0 : Fin 4), plaquetteDensity (torusShift 2)
          flowSignRep (layerConfig α v v') blockedSeatSite.1 0 ν :=
    Finset.single_le_sum (fun ν _ =>
      (blockedSeatDensity_mem _ blockedSeatSite.1 0 ν).1)
      (Finset.mem_Ioi.mpr (show (0 : Fin 4) < 2 by decide))
  have houter : (∑ ν ∈ Finset.Ioi (0 : Fin 4), plaquetteDensity
        (torusShift 2) flowSignRep (layerConfig α v v')
          blockedSeatSite.1 0 ν)
      ≤ blockedSeatDensitySum α v v' :=
    Finset.single_le_sum (fun c _ => Finset.sum_nonneg fun ν _ =>
      (blockedSeatDensity_mem _ c.1 0 ν).1) (Finset.mem_univ blockedSeatSite)
  exact hinner.trans houter

/-- **The distinguished plaquette is fully frustrated on the
pinned data.** If the stratum reads `flowSeatS` at the
distinguished site and `1` at its direction-`2` shift, and both
boundary data read `1` at the distinguished link, then the
distinguished plaquette word is the nonidentity element and its
density is exactly `2`: the sign of the word is
`sgnR (α c) * sgnR (v' ℓ) * sgnR (α c') * sgnR (v ℓ)
= (−1) * 1 * 1 * 1`, and the density is `1 − sgnR (word)`. -/
theorem blockedSeatDensity_eq_two
    (α : LayerSite 2 → Multiplicative (ZMod 2))
    (v v' : LayerLink 2 → Multiplicative (ZMod 2))
    (hα : α blockedSeatSite = flowSeatS)
    (hα' : α blockedSeatSite' = 1)
    (hv : v blockedSeatLink = 1) (hv' : v' blockedSeatLink = 1) :
    plaquetteDensity (torusShift 2) flowSignRep (layerConfig α v v')
      blockedSeatSite.1 0 2 = 2 := by
  have hsgn : sgnR (plaquette (torusShift 2) (layerConfig α v v')
        blockedSeatSite.1 0 2) = -1 := by
    rw [blockedSeatPlaquette_word]
    simp only [flow_inv_self, hα, hα', hv, hv', sgnR_seatS, mul_one]
  show 1 - (Matrix.trace (repMatrix flowSignRep
      (plaquette (torusShift 2) (layerConfig α v v')
        blockedSeatSite.1 0 2))).re / ((1 : ℕ) : ℝ) = 2
  rw [trace_flowSignRep_re, hsgn]
  norm_num

/-- **Boltzmann bounds, `β ≥ 0`.** The factor is at most `1`,
and at most `exp (−2β)` once the distinguished plaquette is
fully frustrated. -/
theorem blockedSeatBoltzmann_bounds_pos (hβ : 0 ≤ β)
    (α : LayerSite 2 → Multiplicative (ZMod 2))
    (v v' : LayerLink 2 → Multiplicative (ZMod 2)) :
    Real.exp (-layerAction flowSignRep β α v v') ≤ 1
      ∧ (plaquetteDensity (torusShift 2) flowSignRep (layerConfig α v v')
            blockedSeatSite.1 0 2 = 2 →
          Real.exp (-layerAction flowSignRep β α v v')
            ≤ Real.exp (-(2 * β))) := by
  have hact : layerAction flowSignRep β α v v'
      = β * blockedSeatDensitySum α v v' := rfl
  have hS := blockedSeatDensitySum_nonneg α v v'
  have hge := blockedSeatDensitySum_ge α v v'
  constructor
  · rw [hact, Real.exp_le_one_iff]
    exact neg_nonpos.mpr (mul_nonneg hβ hS)
  · intro h2
    rw [hact, Real.exp_le_exp]
    have h2S : 2 ≤ blockedSeatDensitySum α v v' := h2 ▸ hge
    have hle : β * 2 ≤ β * blockedSeatDensitySum α v v' :=
      mul_le_mul_of_nonneg_left h2S hβ
    rw [mul_comm 2 β]
    exact neg_le_neg hle

/-- **Boltzmann bounds, `β ≤ 0`.** The factor is at least `1`,
and at least `exp (−2β)` once the distinguished plaquette is
fully frustrated. -/
theorem blockedSeatBoltzmann_bounds_neg (hβ : β ≤ 0)
    (α : LayerSite 2 → Multiplicative (ZMod 2))
    (v v' : LayerLink 2 → Multiplicative (ZMod 2)) :
    1 ≤ Real.exp (-layerAction flowSignRep β α v v')
      ∧ (plaquetteDensity (torusShift 2) flowSignRep (layerConfig α v v')
            blockedSeatSite.1 0 2 = 2 →
          Real.exp (-(2 * β))
            ≤ Real.exp (-layerAction flowSignRep β α v v')) := by
  have hact : layerAction flowSignRep β α v v'
      = β * blockedSeatDensitySum α v v' := rfl
  have hS := blockedSeatDensitySum_nonneg α v v'
  have hge := blockedSeatDensitySum_ge α v v'
  constructor
  · rw [hact, Real.one_le_exp_iff]
    exact neg_nonneg.mpr (mul_nonpos_of_nonpos_of_nonneg hβ hS)
  · intro h2
    rw [hact, Real.exp_le_exp]
    have h2S : 2 ≤ blockedSeatDensitySum α v v' := h2 ▸ hge
    have hle : β * blockedSeatDensitySum α v v' ≤ β * 2 :=
      mul_le_mul_of_nonpos_left h2S hβ
    rw [mul_comm 2 β]
    exact neg_le_neg hle

/-! ## §3. The blocked diagonal is a positive real average

`layerKernel` at any seat is the coercion of a real integral
(the Boltzmann factor is a positive real before coercion), and
`blockedLayerKernel` is its fiber average; merging the three
integrals (Fubini) exhibits the diagonal as the coercion of the
real number `blockedSeatJ β U`. -/

/-- The Boltzmann factor of one point of the merged
fiber × fiber × stratum space at the seat. -/
noncomputable def blockedSeatBoltzmann (β : ℝ)
    (U : LayerLink (2 / 2) → Multiplicative (ZMod 2))
    (z : ((LayerLink (2 / 2) → (Fin 7 → Multiplicative (ZMod 2)))
      × (LayerLink (2 / 2) → (Fin 7 → Multiplicative (ZMod 2))))
      × (LayerSite 2 → Multiplicative (ZMod 2))) : ℝ :=
  Real.exp (-layerAction flowSignRep β z.2
    (layerBlockAsm blockedSeatH U z.1.1) (layerBlockAsm blockedSeatH U z.1.2))

/-- The real average of the blocked diagonal at the seat:
the fiber × fiber × stratum integral of the Boltzmann factor
over the product probability measure. -/
noncomputable def blockedSeatJ (β : ℝ)
    (U : LayerLink (2 / 2) → Multiplicative (ZMod 2)) : ℝ :=
  ∫ z, blockedSeatBoltzmann β U z
    ∂((blockedSeatFiberMeasure.prod blockedSeatFiberMeasure).prod
      blockedSeatStratumMeasure)

/-- The merged Boltzmann factor is integrable on the product
probability space (it is measurable — the corpus's
`measurable_layerAction` at the continuous sign character,
composed with the assembly's measurability — and bounded by
`exp (|β| * layerBoundConst 2)` via the corpus's action bound). -/
theorem blockedSeatJ_integrable (β : ℝ)
    (U : LayerLink (2 / 2) → Multiplicative (ZMod 2)) :
    Integrable (blockedSeatBoltzmann β U)
      ((blockedSeatFiberMeasure.prod blockedSeatFiberMeasure).prod
        blockedSeatStratumMeasure) := by
  have hmeas : Measurable (blockedSeatBoltzmann β U) := by
    have hm : Measurable (fun q : (LayerSite 2 → Multiplicative (ZMod 2))
        × (LayerLink 2 → Multiplicative (ZMod 2))
        × (LayerLink 2 → Multiplicative (ZMod 2)) =>
        layerAction flowSignRep β q.1 q.2.1 q.2.2) :=
      measurable_layerAction flowSignRep flowSignRep_continuous β
    have hpair : Measurable (fun p : (LayerLink (2 / 2) → Multiplicative (ZMod 2))
        × (LayerLink (2 / 2) → (Fin 7 → Multiplicative (ZMod 2))) =>
        layerBlockAsm blockedSeatH p.1 p.2) :=
      measurable_layerBlockAsm_pair μG₀ blockedSeatH
    have hf1 : Measurable (fun z : ((LayerLink (2 / 2) → (Fin 7 → Multiplicative (ZMod 2)))
        × (LayerLink (2 / 2) → (Fin 7 → Multiplicative (ZMod 2))))
        × (LayerSite 2 → Multiplicative (ZMod 2)) => (U, z.1.1)) :=
      measurable_const.prodMk (measurable_fst.comp measurable_fst)
    have hf2 : Measurable (fun z : ((LayerLink (2 / 2) → (Fin 7 → Multiplicative (ZMod 2)))
        × (LayerLink (2 / 2) → (Fin 7 → Multiplicative (ZMod 2))))
        × (LayerSite 2 → Multiplicative (ZMod 2)) => (U, z.1.2)) :=
      measurable_const.prodMk (measurable_snd.comp measurable_fst)
    have ha1 : Measurable ((fun p : (LayerLink (2 / 2) → Multiplicative (ZMod 2))
        × (LayerLink (2 / 2) → (Fin 7 → Multiplicative (ZMod 2))) =>
        layerBlockAsm blockedSeatH p.1 p.2) ∘
        (fun z : ((LayerLink (2 / 2) → (Fin 7 → Multiplicative (ZMod 2)))
        × (LayerLink (2 / 2) → (Fin 7 → Multiplicative (ZMod 2))))
        × (LayerSite 2 → Multiplicative (ZMod 2)) => (U, z.1.1))) := hpair.comp hf1
    have ha2 : Measurable ((fun p : (LayerLink (2 / 2) → Multiplicative (ZMod 2))
        × (LayerLink (2 / 2) → (Fin 7 → Multiplicative (ZMod 2))) =>
        layerBlockAsm blockedSeatH p.1 p.2) ∘
        (fun z : ((LayerLink (2 / 2) → (Fin 7 → Multiplicative (ZMod 2)))
        × (LayerLink (2 / 2) → (Fin 7 → Multiplicative (ZMod 2))))
        × (LayerSite 2 → Multiplicative (ZMod 2)) => (U, z.1.2))) := hpair.comp hf2
    have hg : Measurable (fun z : ((LayerLink (2 / 2) → (Fin 7 → Multiplicative (ZMod 2)))
        × (LayerLink (2 / 2) → (Fin 7 → Multiplicative (ZMod 2))))
        × (LayerSite 2 → Multiplicative (ZMod 2)) => (z.2,
        ((fun p : (LayerLink (2 / 2) → Multiplicative (ZMod 2))
        × (LayerLink (2 / 2) → (Fin 7 → Multiplicative (ZMod 2))) =>
          layerBlockAsm blockedSeatH p.1 p.2) ∘
          (fun z : ((LayerLink (2 / 2) → (Fin 7 → Multiplicative (ZMod 2)))
        × (LayerLink (2 / 2) → (Fin 7 → Multiplicative (ZMod 2))))
        × (LayerSite 2 → Multiplicative (ZMod 2)) => (U, z.1.1))) z,
        ((fun p : (LayerLink (2 / 2) → Multiplicative (ZMod 2))
        × (LayerLink (2 / 2) → (Fin 7 → Multiplicative (ZMod 2))) =>
          layerBlockAsm blockedSeatH p.1 p.2) ∘
          (fun z : ((LayerLink (2 / 2) → (Fin 7 → Multiplicative (ZMod 2)))
        × (LayerLink (2 / 2) → (Fin 7 → Multiplicative (ZMod 2))))
        × (LayerSite 2 → Multiplicative (ZMod 2)) => (U, z.1.2))) z)) :=
      measurable_snd.prodMk (ha1.prodMk ha2)
    exact Real.measurable_exp.comp ((hm.comp hg).neg)
  refine Integrable.of_bound hmeas.aestronglyMeasurable
    (Real.exp (|β| * layerBoundConst 2)) ?_
  filter_upwards with z
  show ‖Real.exp (-layerAction flowSignRep β z.2
    (layerBlockAsm blockedSeatH U z.1.1)
    (layerBlockAsm blockedSeatH U z.1.2))‖ ≤ _
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.mpr
    ((neg_le_abs _).trans (layerAction_abs_le flowSignRep β z.2 _ _))

/-- **The blocked diagonal at the seat is a real number.**
`blockedLayerKernel μG₀ flowSignRep blockedSeatH β U U`
is the coercion of `blockedSeatJ β U`. -/
theorem blockedKernelDiag_seat_ofReal (β : ℝ)
    (U : LayerLink (2 / 2) → Multiplicative (ZMod 2)) :
    blockedLayerKernel μG₀ flowSignRep blockedSeatH β U U
      = ((blockedSeatJ β U : ℝ) : ℂ) := by
  have hker : ∀ v v' : LayerLink 2 → Multiplicative (ZMod 2),
      layerKernel μG₀ flowSignRep β v v'
        = ((∫ α, Real.exp (-layerAction flowSignRep β α v v')
            ∂blockedSeatStratumMeasure : ℝ) : ℂ) := by
    intro v v'
    show (∫ α, (Real.exp (-layerAction flowSignRep β α v v') : ℂ)
        ∂blockedSeatStratumMeasure) = _
    exact integral_ofReal
  show (∫ q, layerKernel μG₀ flowSignRep β
        (layerBlockAsm blockedSeatH U q.1) (layerBlockAsm blockedSeatH U q.2)
      ∂(blockedSeatFiberMeasure.prod blockedSeatFiberMeasure))
    = ((blockedSeatJ β U : ℝ) : ℂ)
  rw [integral_congr_ae (Filter.Eventually.of_forall
    fun q => hker _ _)]
  have hreal : (∫ q, (∫ α, Real.exp (-layerAction flowSignRep β α
        (layerBlockAsm blockedSeatH U q.1)
        (layerBlockAsm blockedSeatH U q.2))
      ∂blockedSeatStratumMeasure)
      ∂(blockedSeatFiberMeasure.prod blockedSeatFiberMeasure))
      = blockedSeatJ β U :=
    (integral_prod (blockedSeatBoltzmann β U)
      (blockedSeatJ_integrable β U)).symm
  rw [← hreal]
  exact integral_ofReal

/-! ## §4. The bad rectangle

One rectangle of the merged probability space: each fiber is
pinned at the distinguished coarse link's first tail coordinate
(the coordinate the assembly reads at the distinguished link),
and the stratum is pinned at the two sites of the distinguished
plaquette word. On this rectangle the distinguished plaquette
is fully frustrated (§2), whatever the remaining coordinates —
and whatever the coarse datum `U`, since the assembly at the
distinguished link never reads `U`. Its measure is
`(1/2)⁴ = 1/16`. -/

/-- The bad rectangle of the merged space. -/
def blockedSeatBadSet :
    Set (((LayerLink (2 / 2) → (Fin 7 → Multiplicative (ZMod 2)))
      × (LayerLink (2 / 2) → (Fin 7 → Multiplicative (ZMod 2))))
      × (LayerSite 2 → Multiplicative (ZMod 2))) :=
  ({w | w blockedSeatCoarseLink 0 = 1}
      ×ˢ {w | w blockedSeatCoarseLink 0 = 1})
    ×ˢ {α | α blockedSeatSite = flowSeatS ∧ α blockedSeatSite' = 1}

theorem blockedSeatBadSet_measurable :
    MeasurableSet blockedSeatBadSet := by
  have hfiber : MeasurableSet
      {w : LayerLink (2 / 2) → (Fin 7 → Multiplicative (ZMod 2)) |
        w blockedSeatCoarseLink 0 = 1} := by
    have hm : Measurable (fun w : LayerLink (2 / 2)
        → (Fin 7 → Multiplicative (ZMod 2)) =>
        w blockedSeatCoarseLink 0) :=
      (measurable_pi_apply (0 : Fin 7)).comp
        (measurable_pi_apply blockedSeatCoarseLink)
    exact hm (measurableSet_singleton 1)
  have hs1 : MeasurableSet
      {α : LayerSite 2 → Multiplicative (ZMod 2) |
        α blockedSeatSite = flowSeatS} := by
    have hm : Measurable (fun α : LayerSite 2
        → Multiplicative (ZMod 2) => α blockedSeatSite) :=
      measurable_pi_apply blockedSeatSite
    exact hm (measurableSet_singleton flowSeatS)
  have hs2 : MeasurableSet
      {α : LayerSite 2 → Multiplicative (ZMod 2) |
        α blockedSeatSite' = 1} := by
    have hm : Measurable (fun α : LayerSite 2
        → Multiplicative (ZMod 2) => α blockedSeatSite') :=
      measurable_pi_apply blockedSeatSite'
    exact hm (measurableSet_singleton 1)
  have hstrat : MeasurableSet
      {α : LayerSite 2 → Multiplicative (ZMod 2) |
        α blockedSeatSite = flowSeatS ∧ α blockedSeatSite' = 1} :=
    hs1.inter hs2
  exact (hfiber.prod hfiber).prod hstrat

/-- The bad rectangle has measure `(1/2)⁴`, and its real
measure is `1/16`. Each pinned coordinate contributes one
factor of `μG₀ {g} = 2⁻¹` under `Measure.pi_pi`; the two
`prod` splittings contribute the rest. -/
theorem blockedSeatBadSet_measure :
    ((blockedSeatFiberMeasure.prod blockedSeatFiberMeasure).prod
        blockedSeatStratumMeasure) blockedSeatBadSet
      = 2⁻¹ * 2⁻¹ * (2⁻¹ * 2⁻¹)
    ∧ (((blockedSeatFiberMeasure.prod blockedSeatFiberMeasure).prod
        blockedSeatStratumMeasure) blockedSeatBadSet).toReal
      = 1 / 16 := by
  have htail : (Measure.pi fun _ : Fin 7 => μG₀)
        {t : Fin 7 → Multiplicative (ZMod 2) | t 0 = 1} = 2⁻¹ := by
    have hset : {t : Fin 7 → Multiplicative (ZMod 2) | t 0 = 1}
        = Set.univ.pi (fun j => if j = 0 then {1} else Set.univ) := by
      ext t
      simp only [Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, forall_true_left]
      constructor
      · intro h j
        by_cases hj : j = 0
        · rw [ite_eq_left hj]; exact hj ▸ h
        · rw [ite_eq_right hj]; exact Set.mem_univ _
      · intro h
        have := h 0
        rwa [ite_eq_left rfl, Set.mem_singleton_iff] at this
    rw [hset, Measure.pi_pi, Finset.prod_eq_single (0 : Fin 7)
      (fun b _ hb => by
        rw [ite_eq_right hb]
        exact measure_univ)
      (fun h => (h (Finset.mem_univ 0)).elim),
      ite_eq_left rfl]
    exact μG₀_singleton 1
  have hfiber : blockedSeatFiberMeasure
        {w : LayerLink (2 / 2) → (Fin 7 → Multiplicative (ZMod 2)) |
          w blockedSeatCoarseLink 0 = 1} = 2⁻¹ := by
    classical
    have hset : {w : LayerLink (2 / 2) → (Fin 7 → Multiplicative (ZMod 2)) |
          w blockedSeatCoarseLink 0 = 1}
        = Set.univ.pi (fun ℓ'' => if ℓ'' = blockedSeatCoarseLink
            then {t : Fin 7 → Multiplicative (ZMod 2) | t 0 = 1}
            else Set.univ) := by
      ext w
      simp only [Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, forall_true_left]
      constructor
      · intro h ℓ''
        by_cases hℓ : ℓ'' = blockedSeatCoarseLink
        · rw [ite_eq_left hℓ]; exact hℓ ▸ h
        · rw [ite_eq_right hℓ]; exact Set.mem_univ _
      · intro h
        have := h blockedSeatCoarseLink
        rwa [ite_eq_left rfl] at this
    show (Measure.pi fun _ : LayerLink (2 / 2) =>
      (Measure.pi fun _ : Fin 7 => μG₀)) _ = _
    rw [hset, Measure.pi_pi,
      Finset.prod_eq_single blockedSeatCoarseLink
      (fun b _ hb => by
        rw [ite_eq_right hb]
        exact measure_univ)
      (fun h => (h (Finset.mem_univ blockedSeatCoarseLink)).elim),
      ite_eq_left rfl]
    exact htail
  have hstrat : blockedSeatStratumMeasure
        {α : LayerSite 2 → Multiplicative (ZMod 2) |
          α blockedSeatSite = flowSeatS ∧ α blockedSeatSite' = 1}
      = 2⁻¹ * 2⁻¹ := by
    have hset : {α : LayerSite 2 → Multiplicative (ZMod 2) |
          α blockedSeatSite = flowSeatS ∧ α blockedSeatSite' = 1}
        = Set.univ.pi (fun x => if x = blockedSeatSite then {flowSeatS}
            else if x = blockedSeatSite' then {1} else Set.univ) := by
      ext α
      simp only [Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, forall_true_left]
      constructor
      · rintro ⟨h1, h2⟩ x
        by_cases hx : x = blockedSeatSite
        · rw [ite_eq_left hx]; exact hx ▸ h1
        · by_cases hx' : x = blockedSeatSite'
          · rw [ite_eq_right hx, ite_eq_left hx']; exact hx' ▸ h2
          · rw [ite_eq_right hx, ite_eq_right hx']; exact Set.mem_univ _
      · intro h
        constructor
        · have h1 := h blockedSeatSite
          rwa [ite_eq_left rfl, Set.mem_singleton_iff] at h1
        · have h2 := h blockedSeatSite'
          rw [ite_eq_right blockedSeatSite'_ne, ite_eq_left rfl,
            Set.mem_singleton_iff] at h2
          exact h2
    show (Measure.pi fun _ : LayerSite 2 => μG₀) _ = _
    rw [hset, Measure.pi_pi]
    have hfac : ∀ x : LayerSite 2,
        μG₀ (if x = blockedSeatSite then {flowSeatS}
            else if x = blockedSeatSite' then {1} else Set.univ)
          = (if x = blockedSeatSite then (2⁻¹ : ℝ≥0∞) else 1)
            * (if x = blockedSeatSite' then (2⁻¹ : ℝ≥0∞) else 1) := by
      intro x
      by_cases hx : x = blockedSeatSite
      · subst hx
        rw [ite_eq_left rfl, ite_eq_left rfl,
          ite_eq_right (fun h : blockedSeatSite = blockedSeatSite' =>
            blockedSeatSite'_ne h.symm), μG₀_singleton, mul_one]
      · by_cases hx' : x = blockedSeatSite'
        · subst hx'
          rw [ite_eq_right blockedSeatSite'_ne, ite_eq_left rfl,
            ite_eq_right blockedSeatSite'_ne, ite_eq_left rfl, μG₀_singleton,
            one_mul]
        · rw [ite_eq_right hx, ite_eq_right hx', ite_eq_right hx, ite_eq_right hx']
          simp
    rw [Finset.prod_congr rfl (fun x _ => hfac x), Finset.prod_mul_distrib]
    simp
  have hmeas : ((blockedSeatFiberMeasure.prod blockedSeatFiberMeasure).prod
        blockedSeatStratumMeasure) blockedSeatBadSet
      = 2⁻¹ * 2⁻¹ * (2⁻¹ * 2⁻¹) := by
    show ((blockedSeatFiberMeasure.prod blockedSeatFiberMeasure).prod
        blockedSeatStratumMeasure)
        (({w | w blockedSeatCoarseLink 0 = 1}
            ×ˢ {w | w blockedSeatCoarseLink 0 = 1})
          ×ˢ {α | α blockedSeatSite = flowSeatS
              ∧ α blockedSeatSite' = 1}) = _
    rw [Measure.prod_prod, Measure.prod_prod, hfiber, hstrat]
  refine ⟨hmeas, ?_⟩
  rw [hmeas, ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_inv, ENNReal.toReal_ofNat]
  norm_num

/-! ## §5. The average is strictly separated from `1`

Split the average against the constant `1` comparison function
`1 + (exp (−2β) − 1) · 1_B`: it agrees with the Boltzmann factor's
bounds of §2 on and off the bad rectangle, and its integral is
`1 + (exp (−2β) − 1) / 16`. -/

/-- The comparison function's integral: `1 + (exp (−2β) − 1)/16`. -/
theorem blockedSeatBadAvg (β : ℝ) :
    ∫ z, (1 + (Real.exp (-(2 * β)) - 1)
        * blockedSeatBadSet.indicator 1 z)
      ∂((blockedSeatFiberMeasure.prod blockedSeatFiberMeasure).prod
        blockedSeatStratumMeasure)
    = 1 + (Real.exp (-(2 * β)) - 1) * (1 / 16) := by
  have h1 : ∫ _z : ((LayerLink (2 / 2) → (Fin 7 → Multiplicative (ZMod 2)))
        × (LayerLink (2 / 2) → (Fin 7 → Multiplicative (ZMod 2))))
        × (LayerSite 2 → Multiplicative (ZMod 2)), (1 : ℝ)
      ∂((blockedSeatFiberMeasure.prod blockedSeatFiberMeasure).prod
        blockedSeatStratumMeasure) = 1 := by
    rw [integral_const]
    have hμ : ((blockedSeatFiberMeasure.prod blockedSeatFiberMeasure).prod
        blockedSeatStratumMeasure).real Set.univ = 1 := by
      show (((blockedSeatFiberMeasure.prod blockedSeatFiberMeasure).prod
        blockedSeatStratumMeasure) Set.univ).toReal = 1
      rw [measure_univ, ENNReal.toReal_one]
    rw [hμ, one_smul]
  have h2 : ∫ z, (Real.exp (-(2 * β)) - 1)
        * blockedSeatBadSet.indicator 1 z
      ∂((blockedSeatFiberMeasure.prod blockedSeatFiberMeasure).prod
        blockedSeatStratumMeasure)
      = (Real.exp (-(2 * β)) - 1) * (1 / 16) := by
    rw [integral_const_mul, integral_indicator
      blockedSeatBadSet_measurable]
    simp only [Pi.one_apply]
    rw [setIntegral_const, smul_eq_mul, mul_one]
    congr 1
    exact blockedSeatBadSet_measure.2
  rw [integral_add (integrable_const 1)
    (((integrable_const 1).indicator
      blockedSeatBadSet_measurable).const_mul _), h1, h2]

/-- On the bad rectangle the distinguished plaquette of the
assembled pair is fully frustrated — for every coarse datum. -/
theorem blockedSeatDensity_two_of_mem
    (U : LayerLink (2 / 2) → Multiplicative (ZMod 2))
    (z : ((LayerLink (2 / 2) → (Fin 7 → Multiplicative (ZMod 2)))
      × (LayerLink (2 / 2) → (Fin 7 → Multiplicative (ZMod 2))))
      × (LayerSite 2 → Multiplicative (ZMod 2)))
    (hz : z ∈ blockedSeatBadSet) :
    plaquetteDensity (torusShift 2) flowSignRep
        (layerConfig z.2 (layerBlockAsm blockedSeatH U z.1.1)
          (layerBlockAsm blockedSeatH U z.1.2))
        blockedSeatSite.1 0 2 = 2 := by
  obtain ⟨⟨hw, hw'⟩, hα, hα'⟩ := hz
  exact blockedSeatDensity_eq_two z.2 _ _
    hα hα'
    (by rw [blockedSeatAsm_apply]; exact hw)
    (by rw [blockedSeatAsm_apply]; exact hw')

/-- **`blockedSeatJ β U < 1` for `β > 0`.** -/
theorem blockedSeatJ_lt_one (hβ : 0 < β)
    (U : LayerLink (2 / 2) → Multiplicative (ZMod 2)) :
    blockedSeatJ β U < 1 := by
  have hIntG : Integrable (fun z => 1 + (Real.exp (-(2 * β)) - 1)
        * blockedSeatBadSet.indicator 1 z)
      ((blockedSeatFiberMeasure.prod blockedSeatFiberMeasure).prod
        blockedSeatStratumMeasure) :=
    (integrable_const 1).add
      (((integrable_const 1).indicator
        blockedSeatBadSet_measurable).const_mul _)
  have hle : ∫ z, blockedSeatBoltzmann β U z
        ∂((blockedSeatFiberMeasure.prod blockedSeatFiberMeasure).prod
          blockedSeatStratumMeasure)
      ≤ ∫ z, (1 + (Real.exp (-(2 * β)) - 1)
          * blockedSeatBadSet.indicator 1 z)
        ∂((blockedSeatFiberMeasure.prod blockedSeatFiberMeasure).prod
          blockedSeatStratumMeasure) := by
    refine integral_mono (blockedSeatJ_integrable β U) hIntG (fun z => ?_)
    by_cases hz : z ∈ blockedSeatBadSet
    · have h2 := blockedSeatDensity_two_of_mem U z hz
      have hb := (blockedSeatBoltzmann_bounds_pos hβ.le z.2
        (layerBlockAsm blockedSeatH U z.1.1)
        (layerBlockAsm blockedSeatH U z.1.2)).2 h2
      rw [Set.indicator_of_mem hz]
      show blockedSeatBoltzmann β U z ≤ 1 + (Real.exp (-(2 * β)) - 1) * 1
      have hcomp : (1 : ℝ) + (Real.exp (-(2 * β)) - 1) * 1
          = Real.exp (-(2 * β)) := by ring
      rw [hcomp]
      exact hb
    · have hb := (blockedSeatBoltzmann_bounds_pos hβ.le z.2
        (layerBlockAsm blockedSeatH U z.1.1)
        (layerBlockAsm blockedSeatH U z.1.2)).1
      rw [Set.indicator_of_notMem hz]
      show blockedSeatBoltzmann β U z ≤ 1 + (Real.exp (-(2 * β)) - 1) * 0
      rw [mul_zero, add_zero]
      exact hb
  have hexp : Real.exp (-(2 * β)) < 1 :=
    Real.exp_lt_one_iff.mpr (by linarith)
  rw [blockedSeatBadAvg β] at hle
  have hJ : blockedSeatJ β U
      ≤ 1 + (Real.exp (-(2 * β)) - 1) * (1 / 16) := hle
  have : (Real.exp (-(2 * β)) - 1) * (1 / 16) < 0 :=
    mul_neg_of_neg_of_pos (sub_neg.mpr hexp) (by norm_num)
  linarith

/-- **`blockedSeatJ β U > 1` for `β < 0`.** -/
theorem blockedSeatJ_gt_one (hβ : β < 0)
    (U : LayerLink (2 / 2) → Multiplicative (ZMod 2)) :
    1 < blockedSeatJ β U := by
  have hIntG : Integrable (fun z => 1 + (Real.exp (-(2 * β)) - 1)
        * blockedSeatBadSet.indicator 1 z)
      ((blockedSeatFiberMeasure.prod blockedSeatFiberMeasure).prod
        blockedSeatStratumMeasure) :=
    (integrable_const 1).add
      (((integrable_const 1).indicator
        blockedSeatBadSet_measurable).const_mul _)
  have hle : ∫ z, (1 + (Real.exp (-(2 * β)) - 1)
          * blockedSeatBadSet.indicator 1 z)
        ∂((blockedSeatFiberMeasure.prod blockedSeatFiberMeasure).prod
          blockedSeatStratumMeasure)
      ≤ ∫ z, blockedSeatBoltzmann β U z
        ∂((blockedSeatFiberMeasure.prod blockedSeatFiberMeasure).prod
          blockedSeatStratumMeasure) := by
    refine integral_mono hIntG (blockedSeatJ_integrable β U) (fun z => ?_)
    by_cases hz : z ∈ blockedSeatBadSet
    · have h2 := blockedSeatDensity_two_of_mem U z hz
      have hb := (blockedSeatBoltzmann_bounds_neg hβ.le z.2
        (layerBlockAsm blockedSeatH U z.1.1)
        (layerBlockAsm blockedSeatH U z.1.2)).2 h2
      rw [Set.indicator_of_mem hz]
      show 1 + (Real.exp (-(2 * β)) - 1) * 1 ≤ blockedSeatBoltzmann β U z
      have hcomp : (1 : ℝ) + (Real.exp (-(2 * β)) - 1) * 1
          = Real.exp (-(2 * β)) := by ring
      rw [hcomp]
      exact hb
    · have hb := (blockedSeatBoltzmann_bounds_neg hβ.le z.2
        (layerBlockAsm blockedSeatH U z.1.1)
        (layerBlockAsm blockedSeatH U z.1.2)).1
      rw [Set.indicator_of_notMem hz]
      show 1 + (Real.exp (-(2 * β)) - 1) * 0 ≤ blockedSeatBoltzmann β U z
      rw [mul_zero, add_zero]
      exact hb
  have hexp : 1 < Real.exp (-(2 * β)) :=
    Real.one_lt_exp_iff.mpr (by linarith)
  rw [blockedSeatBadAvg β] at hle
  have hJ : 1 + (Real.exp (-(2 * β)) - 1) * (1 / 16)
      ≤ blockedSeatJ β U := hle
  have : 0 < (Real.exp (-(2 * β)) - 1) * (1 / 16) :=
    mul_pos (sub_pos.mpr hexp) (by norm_num)
  linarith

/-! ## §6. Headlines: K-PROP-FORM at T1 -/

/-- **TCS T4 HEADLINE — K-PROP-FORM, promoted to a theorem.**
At the PROP-2-PROBE seat `(N = 2, G = Multiplicative (ZMod 2),
sign character, uniform probability measure)`, the diagonal of
the landed fiber-integrated blocked layer kernel differs from
`1` at **every** `β ≠ 0`, for **every** coarse configuration
`U`. The blocked kernel is therefore not of Wilson layer form
at any coarse datum at this seat — the probe's T2 kill
(K-PROP-FORM, PROP-2-PROBE) is now a T1 theorem about the
landed `blockedLayerKernel` definition. K-TCS-SCALE did not
fire: the diagonal is not `1` at any `β ≠ 0` in the range. -/
theorem blockedKernelDiag_seat_ne_one (β : ℝ) (hβ : β ≠ 0)
    (U : LayerLink (2 / 2) → Multiplicative (ZMod 2)) :
    blockedLayerKernel μG₀ flowSignRep blockedSeatH β U U ≠ 1 := by
  rw [blockedKernelDiag_seat_ofReal]
  intro h
  have hJ : blockedSeatJ β U = 1 := by
    have hre := congrArg Complex.re h
    simpa using hre
  rcases lt_or_gt_of_ne hβ with hneg | hpos
  · exact absurd hJ (ne_of_gt (blockedSeatJ_gt_one hneg U))
  · exact absurd hJ (ne_of_lt (blockedSeatJ_lt_one hpos U))

/-- **The measured configuration, promoted.** At `β = 1` — the
probe's canonical sample point, where PROP-2-PROBE measured the
blocked diagonal `(A'⁸ + B'⁸)³ = 1.729662e-06` — the diagonal
of the landed blocked kernel is not `1`, as a theorem. -/
theorem blockedKernelDiag_seat_one_ne_one
    (U : LayerLink (2 / 2) → Multiplicative (ZMod 2)) :
    blockedLayerKernel μG₀ flowSignRep blockedSeatH 1 U U ≠ 1 :=
  blockedKernelDiag_seat_ne_one 1 one_ne_zero U

end ThetLogos
