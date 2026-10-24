/-
# Assembly, part 2′: occurrence features, mirror side (Route B, step T4b′)

Companion brick to the Gram-clause campaign (Pitch 4, Stage 1b-B).
Charter: the T4c obstruction dossier
(`whitepaper/gram-route-b-t4c-obstruction-2026-10-23.md`, §§2–4) and
the T4a′ landing (`whitepaper/gram-route-b-t4ap-occurrence-features-2026-10-24.md`).
Steps T4a (`ThetLogos.GramAssembly`), T4b (`ThetLogos.GramMirror`)
and T4a′ (`ThetLogos.GramAssemblyOcc` — the A-side occurrence layer)
stand entire; the word-entry closer T4c stopped on a proved
obstruction: a crossing plaquette's closed-half arc is a
**stratum · strict · stratum sandwich**, whose monomials are
*occurrence* (tensor) coefficients, not word entries. This module
builds the repair's B side: occurrence features on the negative
half, the mirror of T4a′.

## Content

* **The mirror arc datum (§1).** Per crossing plaquette, the
  two-slot occurrence datum on the negative stratum: the
  `dualSlot`/`dualFlag` transport of T4a′'s arc datum — slot `0`
  is the stratum mirror of `linkA` (direct flavor `ρ`), slot `1`
  the stratum mirror of `linkC` (conjugate flavor) — which is the
  upper plane's datum: at the upper plane `linkA` and `linkC` lie
  in the negative stratum (`linkA_mem_negStratumLinks`,
  `linkC_mem_negStratumLinks`). The endpoint convention is pinned
  by proof (`occArcNeg_apply`): at endpoints `(![i, j], ![a, k])`
  the coefficient is `(ρAᵐ)_{i a} · (ρCᵐ⁻¹)_{k j}`, the mirror
  sandwich monomial.
* **The coefficient identity (§2).** The occMat-level analogue of
  T4b's `dual_gamma`: the negative-stratum integral of the
  conjugated mirror occurrence coefficient is the *same*
  averaging coefficient `γᵒᶜᶜ` of T4a′
  (`occGamma_arc_dual_conj`). Proof: the landed occMat dual
  transport (`GramMirror.integral_occMat_dual`) moves the integral
  to the positive stratum at the `Fin.rev`-transported endpoints,
  and conjugation swaps the endpoints because the averaging
  operator is self-adjoint (`occGamma_conj_symm`, via T2). No
  path sums: occurrence coefficients need none.
* **Features (§3).** The negative-half feature `featBOcc` —
  T4b's `featB` shape with the conjugated mirror occurrence
  coefficient in place of the conjugated dual word entry, the
  scalar factor read through `mirrorStrictMap` — with
  `featBOcc_marginal` in the criterion's `hmargB` shape,
  per-datum factor `dB = 1`, pairing with the *same*
  `GramAssemblyOcc.featXiOcc` as T4a′'s A-side marginal (at the
  arc datum this sameness is literal: `featBOccArc_marginal` has
  exactly T4a′'s `featXiOcc (arcSlot) (arcΨ) ![k, a] ![j, i]` on
  its right-hand side), plus the `hBA`/`hBB`-shape companions and
  the concrete `phiD` feature's strong measurability.

## What remains

T4c′ (the closer on the `ᵒᶜᶜ` family: assembly of the concrete
feature family from `exp (−S₀)`, `hgram` by construction, `hsum`,
discharge through `osForm_nonneg_of_gram_integrated`). This module
does no series assembly, no domination, and no discharge.

## Fences

Finite volume only; the corpus's unitary-valued `ρ` throughout.
**NO CLAIM** — parts of any official Clay statement closed by
this module: 0.
-/

import ThetLogos.GramAssemblyOcc
import ThetLogos.GramMirror

open MeasureTheory
open scoped InnerProductSpace

namespace ThetLogos

namespace GramMirrorOcc

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] [CompactSpace G] [LocallyCompactSpace G]
  {d : ℕ} (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ)) {N : ℕ} [NeZero N]

/-! ## §1. The mirror arc datum -/

/-- The **dual flavor pattern**: T4a′'s `arcFlag` read under
`Fin.rev` — slot `0` (the mirror of `linkA`) is direct, slot `1`
(the mirror of `linkC`) is inverted. -/
def arcFlagNeg : Fin 2 → Bool := GramMirror.dualFlag GramAssemblyOcc.arcFlag

/-- The **flavor family of the mirror arc datum**: per-slot
representations `ρ` (at the mirror of `linkA`) and
`flavRep ρ false` (at the mirror of `linkC`), via `dualFlag`
transport of the arc flavors. -/
def arcΨNeg : Fin 2 → G →* ↥(Matrix.unitaryGroup (Fin d) ℂ) :=
  fun j => GramWordTensor.flavRep ρ (arcFlagNeg j)

/-- The mirror arc flavor family is continuous in the group
element, per slot. -/
theorem arcΨNeg_continuous
    (hρcont : Continuous fun g : G => repMatrix ρ g) :
    ∀ occ, Continuous fun g : G => repMatrix (arcΨNeg ρ occ) g :=
  fun occ => GramWordTensor.flavRep_continuous ρ arcFlagNeg hρcont occ

/-- Slot `0` of the mirror arc flavor family is `ρ` itself (the
direct seat at the mirror of `linkA`). -/
theorem arcΨNeg_zero : arcΨNeg ρ 0 = ρ := rfl

/-- Slot `1` of the mirror arc flavor family is the conjugated
representation (the `flavRep ρ false` seat at the mirror of
`linkC`). -/
theorem arcΨNeg_one : arcΨNeg ρ 1 = GramWordTensor.conjRep ρ := rfl

section Plaquette

variable {p : (Fin 4 → ZMod N) × Fin 4 × Fin 4}

/-- The **slot map of the mirror arc datum**: the `dualSlot`
transport of T4a′'s `arcSlot` — slot `0` is the stratum mirror
of `linkA`, slot `1` the stratum mirror of `linkC`, as elements
of the negative stratum. -/
def arcSlotNeg (hN : Even N)
    (hpC : linkC p ∈ GramAssembly.stratumLinks (N := N))
    (hpA : linkA p ∈ GramAssembly.stratumLinks (N := N)) :
    Fin 2 → ↥(GramMirror.negStratumLinks (N := N)) :=
  GramMirror.dualSlot hN (GramAssemblyOcc.arcSlot hpC hpA)

/-- Slot `0` of the mirror arc datum is the stratum mirror of
`linkA` (the `Fin.rev` reversal puts the `A` slot first). -/
theorem arcSlotNeg_zero (hN : Even N)
    (hpC : linkC p ∈ GramAssembly.stratumLinks (N := N))
    (hpA : linkA p ∈ GramAssembly.stratumLinks (N := N)) :
    arcSlotNeg hN hpC hpA 0
      = GramMirror.stratumMirror hN ⟨linkA p, hpA⟩ := rfl

/-- Slot `1` of the mirror arc datum is the stratum mirror of
`linkC`. -/
theorem arcSlotNeg_one (hN : Even N)
    (hpC : linkC p ∈ GramAssembly.stratumLinks (N := N))
    (hpA : linkA p ∈ GramAssembly.stratumLinks (N := N)) :
    arcSlotNeg hN hpC hpA 1
      = GramMirror.stratumMirror hN ⟨linkC p, hpC⟩ := rfl

/-- At the upper plane, `linkA` lies in the negative stratum
(the corpus's link pattern, `zero_link_pattern`). -/
theorem linkA_mem_negStratumLinks (hN : Even N) (hp : p ∈ zeroFinset)
    (hup : (p.1 0).val = N - 1) :
    linkA p ∈ GramMirror.negStratumLinks (N := N) := by
  rcases zero_link_pattern hN p hp with h | h
  · exfalso
    obtain ⟨r, hr⟩ := hN
    have hN0 : N ≠ 0 := NeZero.ne N
    omega
  · exact Finset.mem_inter.mpr ⟨h.2.1, h.2.2.1⟩

/-- At the upper plane, `linkC` lies in the negative stratum. -/
theorem linkC_mem_negStratumLinks (hN : Even N) (hp : p ∈ zeroFinset)
    (hup : (p.1 0).val = N - 1) :
    linkC p ∈ GramMirror.negStratumLinks (N := N) := by
  rcases zero_link_pattern hN p hp with h | h
  · exfalso
    obtain ⟨r, hr⟩ := hN
    have hN0 : N ≠ 0 := NeZero.ne N
    omega
  · exact Finset.mem_inter.mpr ⟨h.2.2.2.1, h.2.2.2.2.1⟩

/-- **The mirror endpoint convention, pinned by proof**: the
occurrence coefficient of the mirror arc datum at endpoint
functions `(![i, j], ![a, k])` is the mirror arc monomial
`(ρAᵐ)_{i a} · (ρCᵐ⁻¹)_{k j}` — the upper plane's sandwich read
on the negative stratum, endpoint-swapped against T4a′'s
`occArc_apply` (whose monomial is `(ρC⁻¹)_{j k} · (ρA)_{a i}`). -/
theorem occArcNeg_apply (hN : Even N)
    (hpC : linkC p ∈ GramAssembly.stratumLinks (N := N))
    (hpA : linkA p ∈ GramAssembly.stratumLinks (N := N))
    (i j a k : Fin d) (u : ↥(GramMirror.negStratumLinks (N := N)) → G) :
    GramWordTensor.occMat (arcSlotNeg hN hpC hpA) (arcΨNeg ρ) u ![i, j] ![a, k]
      = (repMatrix ρ (u (arcSlotNeg hN hpC hpA 0))) i a
        * (repMatrix ρ ((u (arcSlotNeg hN hpC hpA 1)))⁻¹) k j := by
  rw [GramWordTensor.occMat_apply, Fin.prod_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [arcΨNeg_zero, arcΨNeg_one, ← GramWordTensor.repMatrix_inv_entry]

end Plaquette

/-! ## §2. Occurrence coefficients on the negative stratum,
    and the dual coefficient identity -/

section OccNeg

variable {κ : Type*} [Fintype κ] [DecidableEq κ]
  (slotN : κ → ↥(GramMirror.negStratumLinks (N := N)))
  (ΨN : κ → G →* ↥(Matrix.unitaryGroup (Fin d) ℂ))
  (A B : κ → Fin d)

/-- The **occurrence coefficient** of a negative-stratum
configuration: the `(A, B)` entry of the joint occurrence matrix
— the mirror of `GramAssemblyOcc.occEntry`. -/
def occEntryNeg (u : ↥(GramMirror.negStratumLinks (N := N)) → G) : ℂ :=
  GramWordTensor.occMat slotN ΨN u A B

/-- The negative-stratum occurrence coefficient is continuous in
the stratum configuration. -/
theorem occEntryNeg_continuous
    (hΨcont : ∀ occ, Continuous fun g : G => repMatrix (ΨN occ) g) :
    Continuous (occEntryNeg slotN ΨN A B) := by
  show Continuous fun u : ↥(GramMirror.negStratumLinks (N := N)) → G =>
    GramWordTensor.occMat slotN ΨN u A B
  simp only [GramWordTensor.occMat_apply]
  refine continuous_finsetProd _ fun occ _ => ?_
  exact (continuous_apply (B occ)).comp ((continuous_apply (A occ)).comp
    ((hΨcont occ).comp (continuous_apply (slotN occ))))

/-- The negative-stratum occurrence coefficient is bounded by
`1`: a product of unitary entries, each of norm `≤ 1`. -/
theorem occEntryNeg_norm_le_one
    (u : ↥(GramMirror.negStratumLinks (N := N)) → G) :
    ‖occEntryNeg slotN ΨN A B u‖ ≤ 1 := by
  rw [occEntryNeg, GramWordTensor.occMat_apply, norm_prod]
  refine Finset.prod_le_one₀ (fun occ _ => norm_nonneg _) fun occ _ => ?_
  exact GramAssembly.repMatrix_entry_norm_le_one (ΨN occ) _ _ _

end OccNeg

/-- **Conjugation swaps the endpoints of `γᵒᶜᶜ`**: the averaging
operator of T2 is self-adjoint, so the averaging coefficient of
an occurrence datum satisfies
`conj (γ (A, B)) = γ (B, A)`. (For word data this symmetry is
spread across T4b's path-reversal machinery; for occurrence
coefficients it is one adjointness computation.) -/
theorem occGamma_conj_symm {κ : Type*} [Fintype κ] [DecidableEq κ]
    (slot : κ → ↥(GramAssembly.stratumLinks (N := N)))
    (Ψ : κ → G →* ↥(Matrix.unitaryGroup (Fin d) ℂ))
    (hΨcont : ∀ occ, Continuous fun g : G => repMatrix (Ψ occ) g)
    (A B : κ → Fin d) :
    (starRingEnd ℂ) (GramAssemblyOcc.occGamma slot Ψ A B)
      = GramAssemblyOcc.occGamma slot Ψ B A := by
  rw [GramAssemblyOcc.occGamma_eq slot Ψ A B hΨcont,
    GramAssemblyOcc.occGamma_eq slot Ψ B A hΨcont, inner_conj_symm]
  exact AveragingProjection.self_adjoint_inner _ _
    (GramWordTensor.occRepCLM_continuous slot Ψ hΨcont)
    (fun s t v => by
      rw [GramWordTensor.occRepCLM_mul, ContinuousLinearMap.mul_apply])
    (fun v => by
      rw [GramWordTensor.occRepCLM_one, ContinuousLinearMap.one_apply])
    (GramWordTensor.occRepCLM_unitary slot Ψ) _ _

/-- **The dual coefficient identity (the occMat analogue of
`dual_gamma`).** The negative-stratum integral of the conjugated
dual occurrence coefficient of a datum `(slot, flag)` is the
averaging coefficient of the original datum at the
endpoint-swapped, `Fin.rev`-transported endpoints. Proof: the
landed dual transport `integral_occMat_dual` moves the integral
to the positive stratum at `(X ∘ rev, Y ∘ rev)`, and
`occGamma_conj_symm` discharges the conjugation. -/
theorem occGamma_dual_conj {n : ℕ}
    (slot : Fin n → ↥(GramAssembly.stratumLinks (N := N)))
    (flag : Fin n → Bool) (hN : Even N)
    (hρcont : Continuous fun g : G => repMatrix ρ g) (X Y : Fin n → Fin d) :
    ∫ u, (starRingEnd ℂ) (occEntryNeg (GramMirror.dualSlot hN slot)
          (fun j => GramWordTensor.flavRep ρ (GramMirror.dualFlag flag j))
          X Y u)
        ∂(Measure.pi fun _ : ↥(GramMirror.negStratumLinks (N := N))
          => haarProb G)
      = GramAssemblyOcc.occGamma slot
          (fun j => GramWordTensor.flavRep ρ (flag j))
          (Y ∘ Fin.rev) (X ∘ Fin.rev) := by
  show ∫ u, (starRingEnd ℂ) (GramWordTensor.occMat
        (GramMirror.dualSlot hN slot)
        (fun j => GramWordTensor.flavRep ρ (GramMirror.dualFlag flag j))
        u X Y)
      ∂(Measure.pi fun _ : ↥(GramMirror.negStratumLinks (N := N))
        => haarProb G)
    = GramAssemblyOcc.occGamma slot
        (fun j => GramWordTensor.flavRep ρ (flag j))
        (Y ∘ Fin.rev) (X ∘ Fin.rev)
  rw [integral_conj, GramMirror.integral_occMat_dual ρ slot flag hN X Y]
  exact occGamma_conj_symm slot
    (fun j => GramWordTensor.flavRep ρ (flag j))
    (fun j => GramWordTensor.flavRep_continuous ρ flag hρcont j)
    (X ∘ Fin.rev) (Y ∘ Fin.rev)

/-- **The coefficient identity at the arc datum (headline).**
The mirror arc coefficient, integrated conjugated over the
negative stratum, is exactly T4a′'s `γᵒᶜᶜ` at the arc endpoints
`(![k, a], ![j, i])` — one coefficient family for both halves,
which is what lets the two marginals pair against a single
`featXiOcc`. -/
theorem occGamma_arc_dual_conj {p : (Fin 4 → ZMod N) × Fin 4 × Fin 4}
    (hpC : linkC p ∈ GramAssembly.stratumLinks (N := N))
    (hpA : linkA p ∈ GramAssembly.stratumLinks (N := N))
    (hN : Even N) (hρcont : Continuous fun g : G => repMatrix ρ g)
    (k a j i : Fin d) :
    ∫ u, (starRingEnd ℂ) (occEntryNeg (arcSlotNeg hN hpC hpA) (arcΨNeg ρ)
          ![i, j] ![a, k] u)
        ∂(Measure.pi fun _ : ↥(GramMirror.negStratumLinks (N := N))
          => haarProb G)
      = GramAssemblyOcc.occGamma (GramAssemblyOcc.arcSlot hpC hpA)
          (GramAssemblyOcc.arcΨ ρ) ![k, a] ![j, i] := by
  have hY : (![a, k] : Fin 2 → Fin d) ∘ Fin.rev = ![k, a] := by
    funext x
    fin_cases x <;> simp
  have hX : (![i, j] : Fin 2 → Fin d) ∘ Fin.rev = ![j, i] := by
    funext x
    fin_cases x <;> simp
  have h := occGamma_dual_conj ρ (GramAssemblyOcc.arcSlot hpC hpA)
    GramAssemblyOcc.arcFlag hN hρcont ![i, j] ![a, k]
  rw [hY, hX] at h
  exact h

/-! ## §3. The B-side occurrence features -/

section FeatBOcc

variable {n : ℕ} (slot : Fin n → ↥(GramAssembly.stratumLinks (N := N)))
  (flag : Fin n → Bool) (X Y : Fin n → Fin d)

/-- **The negative-half occurrence feature** (the criterion's
`𝒝`-side feature shape, repaired): the mirror scalar factor —
the observable read through the strict mirror map of the strict
part (at instantiation, `phiD`'s strict matrix coefficient, the
`exp (−halfActionP)` factor and the series weight, read on the
mirror side) — times the conjugated mirror occurrence
coefficient of the stratum part. T4b's `featB` shape with
occurrence coefficients in place of word entries. -/
def featBOcc (φ₀ : (↥(posLinks (N := N)) → G) → ℂ) (hN : Even N)
    (u : ↥(negLinks (N := N)) → G) : ℂ :=
  φ₀ (GramMirror.mirrorStrictMap hN (GramMirror.strictPartNeg u))
    * (starRingEnd ℂ) (occEntryNeg (GramMirror.dualSlot hN slot)
        (fun j => GramWordTensor.flavRep ρ (GramMirror.dualFlag flag j))
        X Y (GramMirror.negStratPart u))

/-- Features are continuous. -/
theorem featBOcc_continuous
    (φ₀ : (↥(posLinks (N := N)) → G) → ℂ)
    (hφ₀ : Continuous φ₀) (hN : Even N)
    (hρcont : Continuous fun g : G => repMatrix ρ g) :
    Continuous (featBOcc ρ slot flag X Y φ₀ hN) := by
  have h1 : Continuous fun u : ↥(negLinks (N := N)) → G =>
      φ₀ (GramMirror.mirrorStrictMap hN (GramMirror.strictPartNeg u)) :=
    (hφ₀.comp (GramMirror.mirrorStrictMap_continuous hN)).comp
      GramMirror.continuous_strictPartNeg
  have h2 : Continuous fun u : ↥(negLinks (N := N)) → G =>
      (starRingEnd ℂ) (occEntryNeg (GramMirror.dualSlot hN slot)
        (fun j => GramWordTensor.flavRep ρ (GramMirror.dualFlag flag j))
        X Y (GramMirror.negStratPart u)) :=
    (continuous_star.comp (occEntryNeg_continuous
      (GramMirror.dualSlot hN slot)
      (fun j => GramWordTensor.flavRep ρ (GramMirror.dualFlag flag j))
      X Y (fun j => GramWordTensor.flavRep_continuous ρ
        (GramMirror.dualFlag flag) hρcont j))).comp
      GramMirror.continuous_negStratPart
  exact h1.mul h2

/-- Features are bounded by the observable's bound (the mirror
occurrence coefficient contributes a factor `≤ 1`,
conjugation-invisible; the criterion's `hBB` shape). -/
theorem featBOcc_norm_le
    (φ₀ : (↥(posLinks (N := N)) → G) → ℂ)
    {Cφ : ℝ} (hφ₀ : ∀ z, ‖φ₀ z‖ ≤ Cφ) (hN : Even N)
    (u : ↥(negLinks (N := N)) → G) :
    ‖featBOcc ρ slot flag X Y φ₀ hN u‖ ≤ Cφ := by
  have hnorm : ‖(starRingEnd ℂ) (occEntryNeg (GramMirror.dualSlot hN slot)
        (fun j => GramWordTensor.flavRep ρ (GramMirror.dualFlag flag j))
        X Y (GramMirror.negStratPart u))‖
      = ‖occEntryNeg (GramMirror.dualSlot hN slot)
          (fun j => GramWordTensor.flavRep ρ (GramMirror.dualFlag flag j))
          X Y (GramMirror.negStratPart u)‖ := by
    simp
  have h1 : ‖featBOcc ρ slot flag X Y φ₀ hN u‖
      = ‖φ₀ (GramMirror.mirrorStrictMap hN (GramMirror.strictPartNeg u))‖
        * ‖occEntryNeg (GramMirror.dualSlot hN slot)
            (fun j => GramWordTensor.flavRep ρ (GramMirror.dualFlag flag j))
            X Y (GramMirror.negStratPart u)‖ := by
    rw [featBOcc, norm_mul, hnorm]
  rw [h1]
  have h2 := mul_le_mul
    (hφ₀ (GramMirror.mirrorStrictMap hN (GramMirror.strictPartNeg u)))
    (occEntryNeg_norm_le_one (GramMirror.dualSlot hN slot)
      (fun j => GramWordTensor.flavRep ρ (GramMirror.dualFlag flag j))
      X Y (GramMirror.negStratPart u))
    (norm_nonneg _)
    (le_trans (norm_nonneg _)
      (hφ₀ (GramMirror.mirrorStrictMap hN (GramMirror.strictPartNeg u))))
  simpa using h2

/-- Features are almost-everywhere strongly measurable against
the negative-half product measure (the criterion's `hBA`-side
shape, per feature). -/
theorem featBOcc_aestronglyMeasurable
    (φ₀ : (↥(posLinks (N := N)) → G) → ℂ)
    (hφ₀ : Continuous φ₀) (hN : Even N)
    (hρcont : Continuous fun g : G => repMatrix ρ g) :
    AEStronglyMeasurable (featBOcc ρ slot flag X Y φ₀ hN)
      (Measure.pi fun _ : ↥(negLinks (N := N)) => haarProb G) :=
  (featBOcc_continuous ρ slot flag X Y φ₀ hφ₀ hN hρcont).aestronglyMeasurable

/-- **The B-side occurrence marginal (the criterion's `hmargB`
shape, for one occurrence datum, per-datum factor `dB = 1`)**:
integrating the feature against a positive-half observable
composed with `mirrorP` over the negative half leaves the
strict-half feature `featXiOcc` — T4a′'s `Ξ`-side shape at the
endpoint-swapped datum — paired with the same observable. The
strict factor is transported by the corpus's `integral_mirrorP`
through the factoring of `mirrorP` over the strict part (as in
`featB_marginal`); the stratum factor is the dual coefficient
identity `occGamma_dual_conj`. -/
theorem featBOcc_marginal
    (φ₀ : (↥(posLinks (N := N)) → G) → ℂ) (hN : Even N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (f : (↥(posLinks (N := N)) → G) → ℂ) :
    ∫ u, featBOcc ρ slot flag X Y φ₀ hN u * f (mirrorP hN u)
        ∂(Measure.pi fun _ : ↥(negLinks (N := N)) => haarProb G)
      = ((1 : ℝ) : ℂ) * ∫ z, GramAssemblyOcc.featXiOcc slot
          (fun j => GramWordTensor.flavRep ρ (flag j))
          (Y ∘ Fin.rev) (X ∘ Fin.rev) φ₀ z * f z
          ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => haarProb G) := by
  classical
  have hstrict : ∫ v, φ₀ (GramMirror.mirrorStrictMap hN v)
          * f (GramMirror.mirrorStrictMap hN v)
        ∂(Measure.pi fun _ : ↥(GramMirror.mirrorStrictLinks (N := N))
          => haarProb G)
      = ∫ z, φ₀ z * f z
          ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => haarProb G) := by
    calc ∫ v, φ₀ (GramMirror.mirrorStrictMap hN v)
              * f (GramMirror.mirrorStrictMap hN v)
            ∂(Measure.pi fun _ : ↥(GramMirror.mirrorStrictLinks (N := N))
              => haarProb G)
        = ∫ u, φ₀ (GramMirror.mirrorStrictMap hN
              (GramMirror.strictPartNeg u))
              * f (GramMirror.mirrorStrictMap hN
                (GramMirror.strictPartNeg u))
            ∂(Measure.pi fun _ : ↥(negLinks (N := N)) => haarProb G) :=
          (GramMirror.integral_strictPartNeg
            (fun v => φ₀ (GramMirror.mirrorStrictMap hN v)
              * f (GramMirror.mirrorStrictMap hN v))).symm
      _ = ∫ u, (φ₀ * f) (mirrorP hN u)
            ∂(Measure.pi fun _ : ↥(negLinks (N := N)) => haarProb G) := by
          refine integral_congr_ae (ae_of_all _ fun u => ?_)
          dsimp only
          rw [GramMirror.mirrorP_eq_mirrorStrictMap]
          rfl
      _ = ∫ z, (φ₀ * f) z
            ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => haarProb G) :=
          integral_mirrorP (haarProb G) hN _
      _ = ∫ z, φ₀ z * f z
            ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => haarProb G) := by
          refine integral_congr_ae (ae_of_all _ fun z => ?_)
          dsimp only
          rfl
  have hcomp : ∫ u, featBOcc ρ slot flag X Y φ₀ hN u * f (mirrorP hN u)
        ∂(Measure.pi fun _ : ↥(negLinks (N := N)) => haarProb G)
      = ∫ u, (φ₀ (GramMirror.mirrorStrictMap hN
            (GramMirror.splitNegEquiv u).1)
            * f (GramMirror.mirrorStrictMap hN
              (GramMirror.splitNegEquiv u).1))
          * (starRingEnd ℂ) (occEntryNeg (GramMirror.dualSlot hN slot)
            (fun j => GramWordTensor.flavRep ρ
              (GramMirror.dualFlag flag j)) X Y
            (GramMirror.splitNegEquiv u).2)
        ∂(Measure.pi fun _ : ↥(negLinks (N := N)) => haarProb G) := by
    congr 1
    funext u
    show φ₀ (GramMirror.mirrorStrictMap hN (GramMirror.strictPartNeg u))
        * (starRingEnd ℂ) (occEntryNeg (GramMirror.dualSlot hN slot)
            (fun j => GramWordTensor.flavRep ρ
              (GramMirror.dualFlag flag j)) X Y
            (GramMirror.negStratPart u)) * f (mirrorP hN u)
      = (φ₀ (GramMirror.mirrorStrictMap hN (GramMirror.splitNegEquiv u).1)
          * f (GramMirror.mirrorStrictMap hN
            (GramMirror.splitNegEquiv u).1))
        * (starRingEnd ℂ) (occEntryNeg (GramMirror.dualSlot hN slot)
            (fun j => GramWordTensor.flavRep ρ
              (GramMirror.dualFlag flag j)) X Y
            (GramMirror.splitNegEquiv u).2)
    rw [GramMirror.mirrorP_eq_mirrorStrictMap, ← GramMirror.splitNegEquiv_fst,
      ← GramMirror.splitNegEquiv_snd]
    ring
  calc ∫ u, featBOcc ρ slot flag X Y φ₀ hN u * f (mirrorP hN u)
          ∂(Measure.pi fun _ : ↥(negLinks (N := N)) => haarProb G)
      = ∫ u, (φ₀ (GramMirror.mirrorStrictMap hN
            (GramMirror.splitNegEquiv u).1)
            * f (GramMirror.mirrorStrictMap hN
              (GramMirror.splitNegEquiv u).1))
          * (starRingEnd ℂ) (occEntryNeg (GramMirror.dualSlot hN slot)
            (fun j => GramWordTensor.flavRep ρ
              (GramMirror.dualFlag flag j)) X Y
            (GramMirror.splitNegEquiv u).2)
        ∂(Measure.pi fun _ : ↥(negLinks (N := N)) => haarProb G) := hcomp
    _ = ∫ p, (φ₀ (GramMirror.mirrorStrictMap hN p.1)
            * f (GramMirror.mirrorStrictMap hN p.1))
          * (starRingEnd ℂ) (occEntryNeg (GramMirror.dualSlot hN slot)
            (fun j => GramWordTensor.flavRep ρ
              (GramMirror.dualFlag flag j)) X Y p.2)
          ∂((Measure.pi fun _ : ↥(GramMirror.mirrorStrictLinks (N := N))
              => haarProb G).prod
            (Measure.pi fun _ : ↥(GramMirror.negStratumLinks (N := N))
              => haarProb G)) := by
        rw [← (GramMirror.measurePreserving_splitNegEquiv
          (haarProb G)).integral_comp
          (MeasurableEquiv.measurableEmbedding _)
          (fun p : (↥(GramMirror.mirrorStrictLinks (N := N)) → G)
            × (↥(GramMirror.negStratumLinks (N := N)) → G) =>
            (φ₀ (GramMirror.mirrorStrictMap hN p.1)
              * f (GramMirror.mirrorStrictMap hN p.1))
            * (starRingEnd ℂ) (occEntryNeg (GramMirror.dualSlot hN slot)
              (fun j => GramWordTensor.flavRep ρ
                (GramMirror.dualFlag flag j)) X Y p.2))]
    _ = (∫ v, φ₀ (GramMirror.mirrorStrictMap hN v)
            * f (GramMirror.mirrorStrictMap hN v)
          ∂(Measure.pi fun _ : ↥(GramMirror.mirrorStrictLinks (N := N))
            => haarProb G))
        * ∫ w, (starRingEnd ℂ) (occEntryNeg
            (GramMirror.dualSlot hN slot)
            (fun j => GramWordTensor.flavRep ρ
              (GramMirror.dualFlag flag j)) X Y w)
          ∂(Measure.pi fun _ : ↥(GramMirror.negStratumLinks (N := N))
            => haarProb G) :=
        MeasureTheory.integral_prod_mul
          (fun v => φ₀ (GramMirror.mirrorStrictMap hN v)
            * f (GramMirror.mirrorStrictMap hN v))
          (fun w => (starRingEnd ℂ) (occEntryNeg
            (GramMirror.dualSlot hN slot)
            (fun j => GramWordTensor.flavRep ρ
              (GramMirror.dualFlag flag j)) X Y w))
    _ = (∫ z, φ₀ z * f z
          ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => haarProb G))
        * GramAssemblyOcc.occGamma slot
            (fun j => GramWordTensor.flavRep ρ (flag j))
            (Y ∘ Fin.rev) (X ∘ Fin.rev) := by
        rw [hstrict, occGamma_dual_conj ρ slot flag hN hρcont X Y]
    _ = ((1 : ℝ) : ℂ) * ∫ z, GramAssemblyOcc.featXiOcc slot
            (fun j => GramWordTensor.flavRep ρ (flag j))
            (Y ∘ Fin.rev) (X ∘ Fin.rev) φ₀ z * f z
          ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => haarProb G) := by
        have e : (∫ z, GramAssemblyOcc.featXiOcc slot
              (fun j => GramWordTensor.flavRep ρ (flag j))
              (Y ∘ Fin.rev) (X ∘ Fin.rev) φ₀ z * f z
              ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => haarProb G))
            = GramAssemblyOcc.occGamma slot
                (fun j => GramWordTensor.flavRep ρ (flag j))
                (Y ∘ Fin.rev) (X ∘ Fin.rev)
              * ∫ z, φ₀ z * f z
                ∂(Measure.pi fun _ : ↥(posLinks (N := N))
                  => haarProb G) := by
          rw [show (fun z => GramAssemblyOcc.featXiOcc slot
                (fun j => GramWordTensor.flavRep ρ (flag j))
                (Y ∘ Fin.rev) (X ∘ Fin.rev) φ₀ z * f z)
              = fun z => GramAssemblyOcc.occGamma slot
                  (fun j => GramWordTensor.flavRep ρ (flag j))
                  (Y ∘ Fin.rev) (X ∘ Fin.rev) * (φ₀ z * f z) from
            funext fun z => by
              simp only [GramAssemblyOcc.featXiOcc]; ring]
          exact MeasureTheory.integral_const_mul _ _
        rw [e, Complex.ofReal_one, one_mul, mul_comm]

end FeatBOcc

/-- **The arc B-side marginal (headline).** At the arc datum with
dual endpoints `(![i, j], ![a, k])`, the B-side occurrence
marginal pairs with **exactly T4a′'s strict-half feature**
`featXiOcc (arcSlot) (arcΨ) ![k, a] ![j, i]` — the same function
the A-side marginal `featAOcc_marginal` produces at the arc
datum with endpoints `(![k, a], ![j, i])`. This shared `Ξ` is
what the closer (T4c′) pairs the two halves against. -/
theorem featBOccArc_marginal {p : (Fin 4 → ZMod N) × Fin 4 × Fin 4}
    (hpC : linkC p ∈ GramAssembly.stratumLinks (N := N))
    (hpA : linkA p ∈ GramAssembly.stratumLinks (N := N))
    (φ₀ : (↥(posLinks (N := N)) → G) → ℂ) (hN : Even N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (k a j i : Fin d)
    (f : (↥(posLinks (N := N)) → G) → ℂ) :
    ∫ u, featBOcc ρ (GramAssemblyOcc.arcSlot hpC hpA)
          GramAssemblyOcc.arcFlag ![i, j] ![a, k] φ₀ hN u
          * f (mirrorP hN u)
        ∂(Measure.pi fun _ : ↥(negLinks (N := N)) => haarProb G)
      = ((1 : ℝ) : ℂ) * ∫ z, GramAssemblyOcc.featXiOcc
            (GramAssemblyOcc.arcSlot hpC hpA) (GramAssemblyOcc.arcΨ ρ)
            ![k, a] ![j, i] φ₀ z * f z
          ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => haarProb G) := by
  have hY : (![a, k] : Fin 2 → Fin d) ∘ Fin.rev = ![k, a] := by
    funext x
    fin_cases x <;> simp
  have hX : (![i, j] : Fin 2 → Fin d) ∘ Fin.rev = ![j, i] := by
    funext x
    fin_cases x <;> simp
  have h := featBOcc_marginal ρ (GramAssemblyOcc.arcSlot hpC hpA)
    GramAssemblyOcc.arcFlag ![i, j] ![a, k] φ₀ hN hρcont f
  rw [hY, hX] at h
  exact h

/-- **The concrete B-side occurrence feature of one crossing
plaquette is strongly measurable**: the §3 feature at the mirror
arc datum, dual endpoints `(![i, j], ![a, k])` — `(k, a)` the
strict pair, `(j, i)` the mirror pair — with strict factor
`φ₀ᴰ` read through the mirror. This is the shape the closer
(T4c′) integrates. -/
theorem featBOccD_stronglyMeasurable
    {p : (Fin 4 → ZMod N) × Fin 4 × Fin 4}
    (hpC : linkC p ∈ GramAssembly.stratumLinks (N := N))
    (hpA : linkA p ∈ GramAssembly.stratumLinks (N := N))
    (hpD : linkD p ∈ posLinks (N := N)) (k a j i : Fin d) (w : ℝ)
    (β : ℝ) (hN : Even N)
    (hρcont : Continuous fun g : G => repMatrix ρ g) :
    StronglyMeasurable (featBOcc ρ (GramAssemblyOcc.arcSlot hpC hpA)
      GramAssemblyOcc.arcFlag ![i, j] ![a, k]
      (GramAssemblyOcc.phiD ρ hpD k a w β) hN) := by
  unfold featBOcc
  refine StronglyMeasurable.mul ?_ ?_
  · exact (GramAssemblyOcc.phiD_stronglyMeasurable ρ hpD k a w β
      hρcont).comp_measurable
      ((GramMirror.mirrorStrictMap_continuous hN).measurable.comp
        GramMirror.continuous_strictPartNeg.measurable)
  · exact (continuous_star.comp
      ((occEntryNeg_continuous (GramMirror.dualSlot hN
          (GramAssemblyOcc.arcSlot hpC hpA))
        (fun j => GramWordTensor.flavRep ρ
          (GramMirror.dualFlag GramAssemblyOcc.arcFlag j))
        ![i, j] ![a, k]
        (fun j => GramWordTensor.flavRep_continuous ρ
          (GramMirror.dualFlag GramAssemblyOcc.arcFlag) hρcont j)).comp
        GramMirror.continuous_negStratPart)).stronglyMeasurable

end GramMirrorOcc

end ThetLogos
