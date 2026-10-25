/-
# The factored pairings `Π₁`, `Π₂` on `𝔸_slice` (Stage 2, brick S2-2a)

Built 2026-10-24 under the REVISED S2-2 gate
(`whitepaper/stage2-s22-gate-revision-2026-10-24.md`, §3.3, §5
brick S2-2a, priced M). The gate's original two-step pairing
`P₂` is DEAD (S2-1: it reads representatives, not classes);
this module builds the replacement pairings in the gate's
S1-consistent factored form:

* `slicePairOne` — `Π₁(φ, χ) := ⟪sliceState β φ,
  transferOp (sliceState β χ)⟫`, and the theorem
  `slicePairOne_eq_osForm`: `Π₁ = osForm` on `𝔸_slice`, S1's
  polarized identity `osForm_depthOne_transfer_pair`
  consumed, so T2.3ʳ depth-one consistency is definitional.
* `slicePairTwo` — `Π₂(φ, χ) := ⟪sliceState β φ,
  transferOp (transferOp (sliceState β χ))⟫`, defined by
  iteration of the landed operator on slice states, nothing
  else. Its Hermiticity and sesquilinearity are proved here;
  at `β = 0`, `Π₂ = Π₁` by `T₀`'s landed idempotence, and the
  `β = 0` values are the §3.7 acceptance-test pairings
  `conj (sliceCoord φ) * sliceCoord χ` (labeled as such).

## Fences (on the face)

* **Descent of `Π₂` at general `β` is NOT asserted.** It is
  the named claim (D-desc)ʳ, brick S2-2b's to discharge.
  What is proved here is descent at `β = 0` only, consumed
  from S2-1's landed computation.
* **`twoPointOp 2 = transferOp^2` is not consumed or
  implied** — it is unlanded for `m ≥ 2`; `Π₂` is defined by
  the iteration itself.
* **H-pos(1)ʳ and H-pos(2)ʳ remain hypotheses.** Nothing in
  this brick discharges or assumes them; no positivity of
  either pairing's diagonal is asserted at any `β > 0`.
* **The plane test (§4 of the gate): passed by exclusion.**
  These pairings see only `sliceState` images of slice
  observables; `sliceLinks` is disjoint from the plane
  stratum, so no plane coordinate is ever read. The
  quantifiers run over `sliceState` images of named slice
  observables only — nothing is asserted about `transferOp`
  on arbitrary `L²(sliceMeasure)` vectors (TM R2 fence).
* Bricks S2-2b (descent/boundedness), S2-2c (assembly),
  S2-2d (regression suite) are out of scope; their claims
  are stated in the gate, not consumed here.

NO CLAIM. Parts of any official Clay statement closed: 0.
Stage 1b-B label untouched (OPEN at general `(G, ρ)`;
U(1) T1 at all `β ≥ 0` on its support class).

This module is NOT in the root import list of the library
(the corpus pattern for recent exhibits); it is verified by
a targeted build.

- Status: brick S2-2a — built 2026-10-24 under the revised
  S2-2 gate; verdict STANDS; parent-verified 2026-10-24
  (targeted build exit 0, strict recount, axiom check).
  Dossier: `whitepaper/stage2-s22a-pairings-2026-10-24.md`.
-/

import ThetLogos.LatticeTransferIdent
import ThetLogos.LatticeReconZero

namespace ThetLogos

open MeasureTheory Finset
open scoped Matrix ENNReal NNReal InnerProduct

section FactoredPairings

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ))
  {N : ℕ} [NeZero N]

/-- **The one-step pairing `Π₁`** (gate §3.3): the OS pairing
on `𝔸_slice` in descended, factored form — the inner product
of the prepared slice state of `φ` against one transfer
step of the prepared slice state of `χ`. -/
noncomputable def slicePairOne (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g) (β : ℝ)
    (φ : (↥(sliceLinks (N := N)) → G) → ℂ)
    (hφ : MemLp φ 2 (sliceMeasure (N := N) μG ρ β))
    (χ : (↥(sliceLinks (N := N)) → G) → ℂ)
    (hχ : MemLp χ 2 (sliceMeasure (N := N) μG ρ β)) : ℂ :=
  inner ℂ (sliceState μG ρ β φ hφ)
    (transferOp μG ρ hN2 hρcont β (sliceState μG ρ β χ hχ))

/-- **The two-step pairing `Π₂`** (gate §3.3): defined by
iteration of the landed `transferOp` on slice states — two
applications, nothing else. Not R3's `twoPointOp 2`, whose
identification with `transferOp^2` is unlanded and is not
consumed here. -/
noncomputable def slicePairTwo (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g) (β : ℝ)
    (φ : (↥(sliceLinks (N := N)) → G) → ℂ)
    (hφ : MemLp φ 2 (sliceMeasure (N := N) μG ρ β))
    (χ : (↥(sliceLinks (N := N)) → G) → ℂ)
    (hχ : MemLp χ 2 (sliceMeasure (N := N) μG ρ β)) : ℂ :=
  inner ℂ (sliceState μG ρ β φ hφ)
    (transferOp μG ρ hN2 hρcont β
      (transferOp μG ρ hN2 hρcont β (sliceState μG ρ β χ hχ)))

/-- **`Π₁ = osForm` on `𝔸_slice`** (polarized): S1's landed
polarized identity, consumed — the gate's T2.3ʳ depth-one
consistency is definitional from here on. -/
theorem slicePairOne_eq_osForm (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (hd : 0 < d) (β : ℝ)
    (φ χ : (↥(sliceLinks (N := N)) → G) → ℂ)
    (hφ : MemLp φ 2 (sliceMeasure (N := N) μG ρ β))
    (hχ : MemLp χ 2 (sliceMeasure (N := N) μG ρ β)) :
    slicePairOne μG ρ hN2 hρcont β φ hφ χ hχ
      = osForm μG ρ β (sliceObs φ) (sliceObs χ) :=
  (osForm_depthOne_transfer_pair μG ρ hρcont hN hN2 hd β
    φ χ hφ hχ).symm

/-- **`Π₁ = osForm` on `𝔸_slice`** (diagonal form):
`Π₁(φ, φ) = osForm F_φ F_φ` — the quantity H-pos(1)ʳ is
about. Stated, not discharged: no nonnegativity is asserted
at any `β > 0`. -/
theorem slicePairOne_self_eq_osForm (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (hd : 0 < d) (β : ℝ)
    (φ : (↥(sliceLinks (N := N)) → G) → ℂ)
    (hφ : MemLp φ 2 (sliceMeasure (N := N) μG ρ β)) :
    slicePairOne μG ρ hN2 hρcont β φ hφ φ hφ
      = osForm μG ρ β (sliceObs φ) (sliceObs φ) :=
  slicePairOne_eq_osForm μG ρ hN2 hρcont hN hd β φ φ hφ hφ

/-- **The stepped reading of `Π₂`**: the two-step pairing is
the inner product of the two once-stepped slice states —
`transferOp`'s symmetry (`transferOp_inner_symm`, the same
reflection symmetry `bdry_mirror` states for the seam
kernel) consumed once. -/
theorem slicePairTwo_eq_inner_steps (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (φ χ : (↥(sliceLinks (N := N)) → G) → ℂ)
    (hφ : MemLp φ 2 (sliceMeasure (N := N) μG ρ β))
    (hχ : MemLp χ 2 (sliceMeasure (N := N) μG ρ β)) :
    slicePairTwo μG ρ hN2 hρcont β φ hφ χ hχ
      = inner ℂ
          (transferOp μG ρ hN2 hρcont β (sliceState μG ρ β φ hφ))
          (transferOp μG ρ hN2 hρcont β (sliceState μG ρ β χ hχ)) :=
  (transferOp_inner_symm μG ρ hN2 hρcont hN β
    (sliceState μG ρ β φ hφ)
    (transferOp μG ρ hN2 hρcont β (sliceState μG ρ β χ hχ))).symm

/-- **Hermiticity of `Π₁`** (the gate's (D-symm)ʳ shape at
one step): `Π₁(φ, χ) = conj (Π₁(χ, φ))`, from
`transferOp`'s symmetry. -/
theorem slicePairOne_conj_symm (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (φ χ : (↥(sliceLinks (N := N)) → G) → ℂ)
    (hφ : MemLp φ 2 (sliceMeasure (N := N) μG ρ β))
    (hχ : MemLp χ 2 (sliceMeasure (N := N) μG ρ β)) :
    slicePairOne μG ρ hN2 hρcont β φ hφ χ hχ
      = (starRingEnd ℂ) (slicePairOne μG ρ hN2 hρcont β χ hχ φ hφ) := by
  calc slicePairOne μG ρ hN2 hρcont β φ hφ χ hχ
      = inner ℂ
          (transferOp μG ρ hN2 hρcont β (sliceState μG ρ β φ hφ))
          (sliceState μG ρ β χ hχ) :=
        (transferOp_inner_symm μG ρ hN2 hρcont hN β
          (sliceState μG ρ β φ hφ) (sliceState μG ρ β χ hχ)).symm
    _ = (starRingEnd ℂ) (inner ℂ (sliceState μG ρ β χ hχ)
          (transferOp μG ρ hN2 hρcont β (sliceState μG ρ β φ hφ))) :=
        (inner_conj_symm _ _).symm
    _ = (starRingEnd ℂ)
          (slicePairOne μG ρ hN2 hρcont β χ hχ φ hφ) := rfl

/-- **Hermiticity of `Π₂`** (gate §3.3, (D-symm)ʳ's content
at the pairing level): `Π₂(φ, χ) = conj (Π₂(χ, φ))`, from
`transferOp`'s symmetry consumed through the factored
form — twice, once per step. -/
theorem slicePairTwo_conj_symm (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (φ χ : (↥(sliceLinks (N := N)) → G) → ℂ)
    (hφ : MemLp φ 2 (sliceMeasure (N := N) μG ρ β))
    (hχ : MemLp χ 2 (sliceMeasure (N := N) μG ρ β)) :
    slicePairTwo μG ρ hN2 hρcont β φ hφ χ hχ
      = (starRingEnd ℂ) (slicePairTwo μG ρ hN2 hρcont β χ hχ φ hφ) := by
  calc slicePairTwo μG ρ hN2 hρcont β φ hφ χ hχ
      = inner ℂ
          (transferOp μG ρ hN2 hρcont β (sliceState μG ρ β φ hφ))
          (transferOp μG ρ hN2 hρcont β (sliceState μG ρ β χ hχ)) :=
        slicePairTwo_eq_inner_steps μG ρ hN2 hρcont hN β φ χ hφ hχ
    _ = (starRingEnd ℂ) (inner ℂ
          (transferOp μG ρ hN2 hρcont β (sliceState μG ρ β χ hχ))
          (transferOp μG ρ hN2 hρcont β (sliceState μG ρ β φ hφ))) :=
        (inner_conj_symm _ _).symm
    _ = (starRingEnd ℂ) (inner ℂ (sliceState μG ρ β χ hχ)
          (transferOp μG ρ hN2 hρcont β
            (transferOp μG ρ hN2 hρcont β (sliceState μG ρ β φ hφ)))) := by
        congr 1
        exact transferOp_inner_symm μG ρ hN2 hρcont hN β
          (sliceState μG ρ β χ hχ)
          (transferOp μG ρ hN2 hρcont β (sliceState μG ρ β φ hφ))
    _ = (starRingEnd ℂ)
          (slicePairTwo μG ρ hN2 hρcont β χ hχ φ hφ) := rfl

/-- `sliceState` is additive in the observable: the prepared
state of a sum is the sum of the prepared states (proof
irrelevance makes the `MemLp` witnesses agree). -/
theorem sliceState_add (β : ℝ)
    (φ χ : (↥(sliceLinks (N := N)) → G) → ℂ)
    (hφ : MemLp φ 2 (sliceMeasure (N := N) μG ρ β))
    (hχ : MemLp χ 2 (sliceMeasure (N := N) μG ρ β)) :
    sliceState μG ρ β (φ + χ) (hφ.add hχ)
      = sliceState μG ρ β φ hφ + sliceState μG ρ β χ hχ :=
  MemLp.toLp_add hφ hχ

/-- `sliceState` is homogeneous in the observable. -/
theorem sliceState_smul (β : ℝ) (c : ℂ)
    (φ : (↥(sliceLinks (N := N)) → G) → ℂ)
    (hφ : MemLp φ 2 (sliceMeasure (N := N) μG ρ β)) :
    sliceState μG ρ β (c • φ) (hφ.const_smul c)
      = c • sliceState μG ρ β φ hφ :=
  MemLp.toLp_const_smul c hφ

/-- **`Π₁` is additive in its second argument.** -/
theorem slicePairOne_add_right (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g) (β : ℝ)
    (φ χ₁ χ₂ : (↥(sliceLinks (N := N)) → G) → ℂ)
    (hφ : MemLp φ 2 (sliceMeasure (N := N) μG ρ β))
    (hχ₁ : MemLp χ₁ 2 (sliceMeasure (N := N) μG ρ β))
    (hχ₂ : MemLp χ₂ 2 (sliceMeasure (N := N) μG ρ β)) :
    slicePairOne μG ρ hN2 hρcont β φ hφ (χ₁ + χ₂) (hχ₁.add hχ₂)
      = slicePairOne μG ρ hN2 hρcont β φ hφ χ₁ hχ₁
        + slicePairOne μG ρ hN2 hρcont β φ hφ χ₂ hχ₂ := by
  show inner ℂ (sliceState μG ρ β φ hφ)
      (transferOp μG ρ hN2 hρcont β
        (sliceState μG ρ β (χ₁ + χ₂) (hχ₁.add hχ₂)))
    = inner ℂ (sliceState μG ρ β φ hφ)
        (transferOp μG ρ hN2 hρcont β (sliceState μG ρ β χ₁ hχ₁))
      + inner ℂ (sliceState μG ρ β φ hφ)
          (transferOp μG ρ hN2 hρcont β (sliceState μG ρ β χ₂ hχ₂))
  rw [sliceState_add μG ρ β χ₁ χ₂ hχ₁ hχ₂, map_add, inner_add_right]

/-- **`Π₁` is homogeneous in its second argument.** -/
theorem slicePairOne_smul_right (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g) (β : ℝ)
    (c : ℂ) (φ χ : (↥(sliceLinks (N := N)) → G) → ℂ)
    (hφ : MemLp φ 2 (sliceMeasure (N := N) μG ρ β))
    (hχ : MemLp χ 2 (sliceMeasure (N := N) μG ρ β)) :
    slicePairOne μG ρ hN2 hρcont β φ hφ (c • χ) (hχ.const_smul c)
      = c * slicePairOne μG ρ hN2 hρcont β φ hφ χ hχ := by
  show inner ℂ (sliceState μG ρ β φ hφ)
      (transferOp μG ρ hN2 hρcont β
        (sliceState μG ρ β (c • χ) (hχ.const_smul c)))
    = c * inner ℂ (sliceState μG ρ β φ hφ)
        (transferOp μG ρ hN2 hρcont β (sliceState μG ρ β χ hχ))
  rw [sliceState_smul μG ρ β c χ hχ, map_smul, inner_smul_right]

/-- **`Π₁` is conjugate-additive in its first argument**
(the sesquilinear first slot). -/
theorem slicePairOne_add_left (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g) (β : ℝ)
    (φ₁ φ₂ χ : (↥(sliceLinks (N := N)) → G) → ℂ)
    (hφ₁ : MemLp φ₁ 2 (sliceMeasure (N := N) μG ρ β))
    (hφ₂ : MemLp φ₂ 2 (sliceMeasure (N := N) μG ρ β))
    (hχ : MemLp χ 2 (sliceMeasure (N := N) μG ρ β)) :
    slicePairOne μG ρ hN2 hρcont β (φ₁ + φ₂) (hφ₁.add hφ₂) χ hχ
      = slicePairOne μG ρ hN2 hρcont β φ₁ hφ₁ χ hχ
        + slicePairOne μG ρ hN2 hρcont β φ₂ hφ₂ χ hχ := by
  show inner ℂ (sliceState μG ρ β (φ₁ + φ₂) (hφ₁.add hφ₂))
      (transferOp μG ρ hN2 hρcont β (sliceState μG ρ β χ hχ))
    = inner ℂ (sliceState μG ρ β φ₁ hφ₁)
        (transferOp μG ρ hN2 hρcont β (sliceState μG ρ β χ hχ))
      + inner ℂ (sliceState μG ρ β φ₂ hφ₂)
          (transferOp μG ρ hN2 hρcont β (sliceState μG ρ β χ hχ))
  rw [sliceState_add μG ρ β φ₁ φ₂ hφ₁ hφ₂, inner_add_left]

/-- **`Π₁` is conjugate-homogeneous in its first
argument.** -/
theorem slicePairOne_smul_left (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g) (β : ℝ)
    (c : ℂ) (φ χ : (↥(sliceLinks (N := N)) → G) → ℂ)
    (hφ : MemLp φ 2 (sliceMeasure (N := N) μG ρ β))
    (hχ : MemLp χ 2 (sliceMeasure (N := N) μG ρ β)) :
    slicePairOne μG ρ hN2 hρcont β (c • φ) (hφ.const_smul c) χ hχ
      = (starRingEnd ℂ) c
        * slicePairOne μG ρ hN2 hρcont β φ hφ χ hχ := by
  show inner ℂ (sliceState μG ρ β (c • φ) (hφ.const_smul c))
      (transferOp μG ρ hN2 hρcont β (sliceState μG ρ β χ hχ))
    = (starRingEnd ℂ) c * inner ℂ (sliceState μG ρ β φ hφ)
        (transferOp μG ρ hN2 hρcont β (sliceState μG ρ β χ hχ))
  rw [sliceState_smul μG ρ β c φ hφ, inner_smul_left]

/-- **`Π₂` is additive in its second argument.** -/
theorem slicePairTwo_add_right (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g) (β : ℝ)
    (φ χ₁ χ₂ : (↥(sliceLinks (N := N)) → G) → ℂ)
    (hφ : MemLp φ 2 (sliceMeasure (N := N) μG ρ β))
    (hχ₁ : MemLp χ₁ 2 (sliceMeasure (N := N) μG ρ β))
    (hχ₂ : MemLp χ₂ 2 (sliceMeasure (N := N) μG ρ β)) :
    slicePairTwo μG ρ hN2 hρcont β φ hφ (χ₁ + χ₂) (hχ₁.add hχ₂)
      = slicePairTwo μG ρ hN2 hρcont β φ hφ χ₁ hχ₁
        + slicePairTwo μG ρ hN2 hρcont β φ hφ χ₂ hχ₂ := by
  show inner ℂ (sliceState μG ρ β φ hφ)
      (transferOp μG ρ hN2 hρcont β (transferOp μG ρ hN2 hρcont β
        (sliceState μG ρ β (χ₁ + χ₂) (hχ₁.add hχ₂))))
    = inner ℂ (sliceState μG ρ β φ hφ)
        (transferOp μG ρ hN2 hρcont β (transferOp μG ρ hN2 hρcont β
          (sliceState μG ρ β χ₁ hχ₁)))
      + inner ℂ (sliceState μG ρ β φ hφ)
          (transferOp μG ρ hN2 hρcont β (transferOp μG ρ hN2 hρcont β
            (sliceState μG ρ β χ₂ hχ₂)))
  rw [sliceState_add μG ρ β χ₁ χ₂ hχ₁ hχ₂, map_add, map_add,
    inner_add_right]

/-- **`Π₂` is homogeneous in its second argument.** -/
theorem slicePairTwo_smul_right (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g) (β : ℝ)
    (c : ℂ) (φ χ : (↥(sliceLinks (N := N)) → G) → ℂ)
    (hφ : MemLp φ 2 (sliceMeasure (N := N) μG ρ β))
    (hχ : MemLp χ 2 (sliceMeasure (N := N) μG ρ β)) :
    slicePairTwo μG ρ hN2 hρcont β φ hφ (c • χ) (hχ.const_smul c)
      = c * slicePairTwo μG ρ hN2 hρcont β φ hφ χ hχ := by
  show inner ℂ (sliceState μG ρ β φ hφ)
      (transferOp μG ρ hN2 hρcont β (transferOp μG ρ hN2 hρcont β
        (sliceState μG ρ β (c • χ) (hχ.const_smul c))))
    = c * inner ℂ (sliceState μG ρ β φ hφ)
        (transferOp μG ρ hN2 hρcont β (transferOp μG ρ hN2 hρcont β
          (sliceState μG ρ β χ hχ)))
  rw [sliceState_smul μG ρ β c χ hχ, map_smul, map_smul,
    inner_smul_right]

/-- **`Π₂` is conjugate-additive in its first argument.** -/
theorem slicePairTwo_add_left (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g) (β : ℝ)
    (φ₁ φ₂ χ : (↥(sliceLinks (N := N)) → G) → ℂ)
    (hφ₁ : MemLp φ₁ 2 (sliceMeasure (N := N) μG ρ β))
    (hφ₂ : MemLp φ₂ 2 (sliceMeasure (N := N) μG ρ β))
    (hχ : MemLp χ 2 (sliceMeasure (N := N) μG ρ β)) :
    slicePairTwo μG ρ hN2 hρcont β (φ₁ + φ₂) (hφ₁.add hφ₂) χ hχ
      = slicePairTwo μG ρ hN2 hρcont β φ₁ hφ₁ χ hχ
        + slicePairTwo μG ρ hN2 hρcont β φ₂ hφ₂ χ hχ := by
  show inner ℂ (sliceState μG ρ β (φ₁ + φ₂) (hφ₁.add hφ₂))
      (transferOp μG ρ hN2 hρcont β (transferOp μG ρ hN2 hρcont β
        (sliceState μG ρ β χ hχ)))
    = inner ℂ (sliceState μG ρ β φ₁ hφ₁)
        (transferOp μG ρ hN2 hρcont β (transferOp μG ρ hN2 hρcont β
          (sliceState μG ρ β χ hχ)))
      + inner ℂ (sliceState μG ρ β φ₂ hφ₂)
          (transferOp μG ρ hN2 hρcont β (transferOp μG ρ hN2 hρcont β
            (sliceState μG ρ β χ hχ)))
  rw [sliceState_add μG ρ β φ₁ φ₂ hφ₁ hφ₂, inner_add_left]

/-- **`Π₂` is conjugate-homogeneous in its first
argument.** -/
theorem slicePairTwo_smul_left (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g) (β : ℝ)
    (c : ℂ) (φ χ : (↥(sliceLinks (N := N)) → G) → ℂ)
    (hφ : MemLp φ 2 (sliceMeasure (N := N) μG ρ β))
    (hχ : MemLp χ 2 (sliceMeasure (N := N) μG ρ β)) :
    slicePairTwo μG ρ hN2 hρcont β (c • φ) (hφ.const_smul c) χ hχ
      = (starRingEnd ℂ) c
        * slicePairTwo μG ρ hN2 hρcont β φ hφ χ hχ := by
  show inner ℂ (sliceState μG ρ β (c • φ) (hφ.const_smul c))
      (transferOp μG ρ hN2 hρcont β (transferOp μG ρ hN2 hρcont β
        (sliceState μG ρ β χ hχ)))
    = (starRingEnd ℂ) c * inner ℂ (sliceState μG ρ β φ hφ)
        (transferOp μG ρ hN2 hρcont β (transferOp μG ρ hN2 hρcont β
          (sliceState μG ρ β χ hχ)))
  rw [sliceState_smul μG ρ β c φ hφ, inner_smul_left]

/-- **`Π₂ = Π₁` at `β = 0`** (gate §3.3): `T₀` is idempotent
(the landed `transferOp_zero_comp_self` — `T₀` is the
vacuum projection), so the second step adds nothing. This
is the identity §3.7's acceptance test checks on the slice
seat. -/
theorem slicePairTwo_zero_eq_pairOne (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hd : 0 < d)
    (φ χ : (↥(sliceLinks (N := N)) → G) → ℂ)
    (hφ : MemLp φ 2 (sliceMeasure (N := N) μG ρ 0))
    (hχ : MemLp χ 2 (sliceMeasure (N := N) μG ρ 0)) :
    slicePairTwo μG ρ hN2 hρcont 0 φ hφ χ hχ
      = slicePairOne μG ρ hN2 hρcont 0 φ hφ χ hχ := by
  have hid : transferOp μG ρ hN2 hρcont 0
        (transferOp μG ρ hN2 hρcont 0 (sliceState μG ρ 0 χ hχ))
      = transferOp μG ρ hN2 hρcont 0 (sliceState μG ρ 0 χ hχ) := by
    have h := ContinuousLinearMap.ext_iff.mp
      (transferOp_zero_comp_self μG ρ hN2 hρcont hd)
      (sliceState μG ρ 0 χ hχ)
    simpa using h
  show inner ℂ (sliceState μG ρ 0 φ hφ)
      (transferOp μG ρ hN2 hρcont 0
        (transferOp μG ρ hN2 hρcont 0 (sliceState μG ρ 0 χ hχ)))
    = inner ℂ (sliceState μG ρ 0 φ hφ)
        (transferOp μG ρ hN2 hρcont 0 (sliceState μG ρ 0 χ hχ))
  rw [hid]

/-- **Acceptance-test content (§3.7, slice seat): `Π₁` at
`β = 0`** is the coordinate pairing
`conj (sliceCoord φ) * sliceCoord χ` — S2-1's landed
`osForm_zero_slice_pair`, restated for `Π₁` through
`slicePairOne_eq_osForm`. Labeled acceptance-test content:
2d's regression suite consumes it mechanically. -/
theorem slicePairOne_zero (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (hd : 0 < d)
    (φ χ : (↥(sliceLinks (N := N)) → G) → ℂ)
    (hφ : MemLp φ 2 (sliceMeasure (N := N) μG ρ 0))
    (hχ : MemLp χ 2 (sliceMeasure (N := N) μG ρ 0)) :
    slicePairOne μG ρ hN2 hρcont 0 φ hφ χ hχ
      = (starRingEnd ℂ) (sliceCoord μG φ) * sliceCoord μG χ := by
  rw [slicePairOne_eq_osForm μG ρ hN2 hρcont hN hd 0 φ χ hφ hχ]
  exact osForm_zero_slice_pair μG ρ hρcont hN hN2 hd φ χ hφ hχ

/-- **Acceptance-test content (§3.7, slice seat): `Π₂` at
`β = 0`** is the same coordinate pairing — through
`Π₂ = Π₁` at `β = 0`. The pairing that characterizes `T̂₀`
therefore agrees with the one that characterizes the
identity on classes: the pairing-level shadow of S2-1's
`T̂₀ = id`, whose operator statement is 2c/2d's to
reproduce. -/
theorem slicePairTwo_zero (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (hd : 0 < d)
    (φ χ : (↥(sliceLinks (N := N)) → G) → ℂ)
    (hφ : MemLp φ 2 (sliceMeasure (N := N) μG ρ 0))
    (hχ : MemLp χ 2 (sliceMeasure (N := N) μG ρ 0)) :
    slicePairTwo μG ρ hN2 hρcont 0 φ hφ χ hχ
      = (starRingEnd ℂ) (sliceCoord μG φ) * sliceCoord μG χ := by
  rw [slicePairTwo_zero_eq_pairOne μG ρ hN2 hρcont hd φ χ hφ hχ]
  exact slicePairOne_zero μG ρ hN2 hρcont hN hd φ χ hφ hχ

/-- **Descent of `Π₂` at `β = 0`** (gate §3.3: at `β = 0`
descent *is* S2-1's landed descent, consumed here in
pairing form): a `Π₁`-null slice observable at `β = 0` —
its coordinate vanishes, by S2-1's
`osForm_zero_slice_null` content — pairs to zero under
`Π₂` against every slice observable. At general `β` this
statement is (D-desc)ʳ, brick S2-2b's claim, and is NOT
asserted here. -/
theorem slicePairTwo_zero_eq_zero_of_coord_eq_zero (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (hd : 0 < d)
    (φ χ : (↥(sliceLinks (N := N)) → G) → ℂ)
    (hφ : MemLp φ 2 (sliceMeasure (N := N) μG ρ 0))
    (hχ : MemLp χ 2 (sliceMeasure (N := N) μG ρ 0))
    (hcoord : sliceCoord μG φ = 0) :
    slicePairTwo μG ρ hN2 hρcont 0 φ hφ χ hχ = 0 := by
  rw [slicePairTwo_zero μG ρ hN2 hρcont hN hd φ χ hφ hχ,
    hcoord]
  simp

end FactoredPairings

end ThetLogos
