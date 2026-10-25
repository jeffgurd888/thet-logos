/-
# Stage 2, brick S2-2d — the β = 0 regression suite

**READ THIS FIRST — what this module is, and what it is NOT.**

This module executes the β = 0 acceptance test of the REVISED
S2-2 gate (`whitepaper/stage2-s22-gate-revision-2026-10-24.md`,
§3.7) against the assembled conditional slice GNS engine of
brick S2-2c (`LatticeSliceEngine`: the quotient
`ℋ := 𝔸_slice ⧸ null` with the descended `Π₁` inner product,
the descended transfer operator `T̂`, the vacuum class `Ω`),
specialized at `β = 0`, and against S2-1's landed β = 0
packages (`LatticeReconZero`). Everything is at general
`(G, ρ)`, even `N`.

**What is proved here.**

* **The engine's hypothesis is DISCHARGED at `β = 0`.**
  `SliceHPosOne` (H-pos(1)ʳ) at `β = 0` is a theorem of this
  module (`sliceHPosOne_zero`): the one-step diagonal is
  `‖sliceCoord φ‖²` by 2a's labeled acceptance value
  `slicePairOne_zero`. It is not re-assumed anywhere below;
  every engine object in this module is instantiated with
  the discharged proof. (At general `β` H-pos(1)ʳ remains a
  hypothesis — its discharge is S2-3's business, untouched
  here.)
* **Slice seat (§3.7, first bullet list).** The engine's
  inner product on classes at `β = 0` is the coordinate
  pairing `conj (coord a) * coord b`; the engine's null
  submodule is exactly `ker coord`; every class is
  `[a] = coord a • Ω`, so the quotient is `ℂ·Ω₀` with states
  given by `coord` (surjective); the descended operator is
  the identity, `T̂₀ = id`, proved through 2c's uniqueness
  clause from 2a's `Π₂ = Π₁` at `β = 0`; the vacuum clauses
  agree (`‖Ω‖ = 1`, `T̂₀ Ω = Ω`); and the `Ĥ₀ = 0` /
  `exp(−Ĥ₀) = T̂₀` package is reproduced in S2-1's own
  phrasing — `hamZero` and `transferHatZero` on `ℂ`, read
  through `coord` — with the bridge identity
  `⟪coord b, T̂₀ (coord a)⟫ = ⟪[b], T̂₀ [a]⟫` tying the
  coordinate operators to the engine's operator. S2-1's
  bundle `recon_zero_slice_package` is restated verbatim
  as a clause of the headline package. **No mismatch was
  found: regression kill K-S2-2(d)ʳ does not fire.**
* **Strict seat (§3.7, second bullet list).** The engine is
  built on `𝔸_slice` only and asserts nothing on the strict
  seat; the suite therefore re-proves the strict seat's
  acceptance bullets verbatim from S2-1's landed theorems —
  the pairing `conj (strictState χ) * strictState φ`, the
  diagonal `‖strictState φ‖²` with its nonnegativity, the
  null space `ker strictState`, the surjectivity of
  `strictState` (quotient `ℂ·Ω₀`), and the identity operator
  carrying the pairing (`strict_transferHat_pairing`) — and
  records that the same one-dimensional operators
  (`transferHatZero`, `hamZero`) carry both seats.
  **No mismatch was found: regression kill K-S2-2(e)ʳ does
  not fire.**

**Fences.** No new positivity of the OS form `osForm` is
asserted anywhere in this module: the β = 0 values of
`osForm` quoted below are S2-1's landed computations,
restated as regression targets, and the only positivity
proved here is the discharged `SliceHPosOne` at `β = 0`,
whose content is the coordinate square `‖coord‖²`. This
module is **not** a discharge of Stage 1b-B (whose label is
untouched), and it proves nothing at general `β` beyond
what the `β = 0` specialization consumes. **Plane-test
clearance (§4), by exclusion, on the face:** every statement
below quantifies over slice observables, classes of slice
observables, or plane-independent observables (lifts through
`restrictPos`); no plane-seeing class — no `𝔸⁺`, no
observable reading a plane coordinate — is in any
quantifier's range, so S2-1's plane witness is excluded
structurally, exactly as in 2a/2b/2c. The unlanded depth-two
identification of R3's two-point operator with
`transferOp^2` is not consumed. NO CLAIM; Clay parts
closed: 0.

This module is NOT in the root import list of the library
(the corpus pattern for recent exhibits); it is verified by
a targeted build.

- Status: brick S2-2d — built 2026-10-24 under the
  revised S2-2 gate; verdict STANDS (agreement on both
  seats; SliceHPosOne DISCHARGED at beta = 0);
  parent-verified 2026-10-24 (targeted build exit 0,
  strict recount, axiom check). Dossier:
  `whitepaper/stage2-s22d-regression-2026-10-24.md`.
-/

import ThetLogos.LatticeSliceEngine
import ThetLogos.LatticeReconZero

namespace ThetLogos

open MeasureTheory Finset
open scoped Matrix ENNReal NNReal InnerProduct

section SliceRegression

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ))
  {N : ℕ} [NeZero N]

/-! ## §1. The discharge: H-pos(1)ʳ at `β = 0` is a theorem -/

/-- **H-pos(1)ʳ at `β = 0`, DISCHARGED.** The engine's one
named hypothesis, at `β = 0`, follows from landed material:
2a's labeled acceptance value `slicePairOne_zero` computes
the one-step diagonal as `conj (coord φ) * coord φ`, a
squared norm. This is the only positivity proved in this
module, and it is proved, not assumed — every engine object
below is instantiated with this term. (At general `β` the
hypothesis stands; its discharge is S2-3's.) -/
theorem sliceHPosOne_zero (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (hd : 0 < d) :
    SliceHPosOne μG ρ hN2 hρcont 0 := by
  intro φ hφ
  have hdiag : slicePairOne μG ρ hN2 hρcont 0 φ hφ φ hφ
      = ((‖sliceCoord μG φ‖ : ℂ) ^ 2) := by
    rw [slicePairOne_zero μG ρ hN2 hρcont hN hd φ φ hφ hφ]
    exact RCLike.conj_mul _
  rw [hdiag, ← Complex.ofReal_pow, Complex.ofReal_re]
  exact sq_nonneg _

/-! ## §2. The slice seat: the engine at `β = 0` against S2-1 -/

/-- **Acceptance, slice seat — the pairing.** The engine's
inner product on classes at `β = 0` is S2-1's coordinate
pairing: `⟪[a], [b]⟫ = conj (coord a) * coord b`. (Engine
clause 1, `sliceQuotient_inner_mk`, chained with 2a's
`slicePairOne_zero` — which is S2-1's
`osForm_zero_slice_pair` restated for `Π₁`.) -/
theorem sliceRegression_inner_zero (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (hd : 0 < d)
    (a b : ↥(sliceObsSubmodule (N := N) μG ρ 0)) :
    inner ℂ
        (sliceMk μG ρ hN2 hρcont hN 0
          (sliceHPosOne_zero μG ρ hN2 hρcont hN hd) a)
        (sliceMk μG ρ hN2 hρcont hN 0
          (sliceHPosOne_zero μG ρ hN2 hρcont hN hd) b)
      = (starRingEnd ℂ) (sliceCoord μG a.1) * sliceCoord μG b.1 := by
  rw [sliceQuotient_inner_mk]
  show slicePairOne μG ρ hN2 hρcont 0 a.1 a.2 b.1 b.2
      = (starRingEnd ℂ) (sliceCoord μG a.1) * sliceCoord μG b.1
  exact slicePairOne_zero μG ρ hN2 hρcont hN hd a.1 b.1 a.2 b.2

/-- **Acceptance, slice seat — the vacuum pairing.** The
engine's vacuum class pairs against a class as the
conjugate coordinate: `⟪[b], Ω⟫ = conj (coord b)` — the
coordinate of the vacuum representative is `1`
(S2-1's `sliceCoord_one`). -/
theorem sliceRegression_inner_omega_zero (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (hd : 0 < d)
    (b : ↥(sliceObsSubmodule (N := N) μG ρ 0)) :
    inner ℂ
        (sliceMk μG ρ hN2 hρcont hN 0
          (sliceHPosOne_zero μG ρ hN2 hρcont hN hd) b)
        (sliceOmega μG ρ hN2 hρcont hN 0
          (sliceHPosOne_zero μG ρ hN2 hρcont hN hd) hd)
      = (starRingEnd ℂ) (sliceCoord μG b.1) := by
  show inner ℂ
      (sliceMk μG ρ hN2 hρcont hN 0
        (sliceHPosOne_zero μG ρ hN2 hρcont hN hd) b)
      (sliceMk μG ρ hN2 hρcont hN 0
        (sliceHPosOne_zero μG ρ hN2 hρcont hN hd)
        (sliceOneObs μG ρ 0 hd hρcont)) = _
  rw [sliceQuotient_inner_mk]
  have h2 := slicePairOne_zero μG ρ hN2 hρcont hN hd b.1
    (sliceOneObs μG ρ 0 hd hρcont).1 b.2
    (sliceOneObs μG ρ 0 hd hρcont).2
  have h3 : sliceCoord μG (sliceOneObs μG ρ 0 hd hρcont).1
      = 1 :=
    sliceCoord_one (N := N) μG
  show slicePairOne μG ρ hN2 hρcont 0 b.1 b.2
      (sliceOneObs μG ρ 0 hd hρcont).1
      (sliceOneObs μG ρ 0 hd hρcont).2
    = (starRingEnd ℂ) (sliceCoord μG b.1)
  rw [h2, h3, mul_one]

/-- **Acceptance, slice seat — classes are coordinate
multiples of the vacuum.** `[a] = coord a • Ω` in the
engine space at `β = 0`: the class of an observable is its
coordinate times the vacuum class. Detected by pairings
(the engine's definiteness workhorse): against every `[b]`
both sides give `conj (coord b) * coord a`. -/
theorem sliceRegression_mk_eq_coord_smul_omega (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (hd : 0 < d)
    (a : ↥(sliceObsSubmodule (N := N) μG ρ 0)) :
    sliceMk μG ρ hN2 hρcont hN 0
        (sliceHPosOne_zero μG ρ hN2 hρcont hN hd) a
      = sliceCoord μG a.1 • sliceOmega μG ρ hN2 hρcont hN 0
          (sliceHPosOne_zero μG ρ hN2 hρcont hN hd) hd := by
  apply sliceQuotient_inner_eq_of_forall_eq μG ρ hN2 hρcont
    hN 0 (sliceHPosOne_zero μG ρ hN2 hρcont hN hd)
  intro z
  refine Submodule.Quotient.induction_on _ z ?_
  intro b
  rw [sliceRegression_inner_zero μG ρ hN2 hρcont hN hd b a,
    inner_smul_right,
    sliceRegression_inner_omega_zero μG ρ hN2 hρcont hN hd b]
  exact mul_comm _ _

/-- **Acceptance, slice seat — the null space is
`ker coord`.** An observable lies in the engine's
`Π₁`-null submodule at `β = 0` iff its coordinate vanishes
— S2-1's `osForm_zero_slice_null` content, reproduced on
the engine's own null submodule. -/
theorem sliceRegression_mem_null_iff (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (hd : 0 < d)
    (a : ↥(sliceObsSubmodule (N := N) μG ρ 0)) :
    (a ∈ sliceNullSubmodule μG ρ hN2 hρcont hN 0
        (sliceHPosOne_zero μG ρ hN2 hρcont hN hd))
      ↔ sliceCoord μG a.1 = 0 := by
  have hΩ : sliceOmega μG ρ hN2 hρcont hN 0
        (sliceHPosOne_zero μG ρ hN2 hρcont hN hd) hd ≠ 0 := by
    intro h
    have hn := sliceOmega_norm μG ρ hN2 hρcont hN 0
      (sliceHPosOne_zero μG ρ hN2 hρcont hN hd) hd
    rw [h, norm_zero] at hn
    exact zero_ne_one hn
  constructor
  · intro ha
    have hmk : sliceMk μG ρ hN2 hρcont hN 0
          (sliceHPosOne_zero μG ρ hN2 hρcont hN hd) a = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr ha
    rw [sliceRegression_mk_eq_coord_smul_omega μG ρ hN2
      hρcont hN hd a] at hmk
    rcases smul_eq_zero.mp hmk with h | h
    · exact h
    · exact absurd h hΩ
  · intro hcoord
    have hmk : sliceMk μG ρ hN2 hρcont hN 0
          (sliceHPosOne_zero μG ρ hN2 hρcont hN hd) a = 0 := by
      rw [sliceRegression_mk_eq_coord_smul_omega μG ρ hN2
        hρcont hN hd a, hcoord]
      exact zero_smul _ _
    exact (Submodule.Quotient.mk_eq_zero _).mp hmk

/-- **Acceptance, slice seat — the quotient is `ℂ·Ω₀`.**
Every class of the engine space at `β = 0` is a scalar
multiple of the vacuum class; with
`sliceRegression_mk_eq_coord_smul_omega` the scalar is the
representative's coordinate, and `coord` is surjective
(S2-1's `sliceCoord_surjective`), so the states of the
quotient are exactly the coordinates. -/
theorem sliceRegression_quotient_eq_vacuum_line (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (hd : 0 < d) :
    ∀ x : sliceQuotient μG ρ hN2 hρcont hN 0
        (sliceHPosOne_zero μG ρ hN2 hρcont hN hd),
      ∃ c : ℂ, x = c • sliceOmega μG ρ hN2 hρcont hN 0
        (sliceHPosOne_zero μG ρ hN2 hρcont hN hd) hd := by
  intro x
  obtain ⟨a, rfl⟩ := sliceMk_surjective μG ρ hN2 hρcont hN 0
    (sliceHPosOne_zero μG ρ hN2 hρcont hN hd) x
  exact ⟨sliceCoord μG a.1,
    sliceRegression_mk_eq_coord_smul_omega μG ρ hN2 hρcont
      hN hd a⟩

/-- **Acceptance, slice seat — `T̂₀ = id`.** The engine's
descended operator at `β = 0` is the identity of the engine
space: by 2c's uniqueness clause, since the identity
satisfies the pairing characterization at `β = 0` — its
pairing is `Π₁`, and `Π₂ = Π₁` at `β = 0` is 2a's landed
`slicePairTwo_zero_eq_pairOne`. This is S2-1's `T̂₀ = id`
(T1.4 of the fallback seat), reproduced on the engine. -/
theorem sliceRegression_hat_eq_id (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (hd : 0 < d) :
    sliceHat μG ρ hN2 hρcont hN 0
        (sliceHPosOne_zero μG ρ hN2 hρcont hN hd)
      = LinearMap.id := by
  apply (sliceHat_unique μG ρ hN2 hρcont hN 0
    (sliceHPosOne_zero μG ρ hN2 hρcont hN hd)
    LinearMap.id ?_).symm
  intro a b
  simp only [LinearMap.id_apply]
  rw [sliceQuotient_inner_mk]
  show slicePairOne μG ρ hN2 hρcont 0 b.1 b.2 a.1 a.2
      = slicePairTwo μG ρ hN2 hρcont 0 b.1 b.2 a.1 a.2
  exact (slicePairTwo_zero_eq_pairOne μG ρ hN2 hρcont hd
    b.1 a.1 b.2 a.2).symm

/-- **Acceptance, slice seat — the vacuum clauses.** At
`β = 0` the engine's vacuum is a unit vector fixed by the
descended operator, agreeing with S2-1's package (and, by
`sliceRegression_hat_eq_id`, the fixed-point clause is also
the identity's). -/
theorem sliceRegression_vacuum_zero (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (hd : 0 < d) :
    ‖sliceOmega μG ρ hN2 hρcont hN 0
        (sliceHPosOne_zero μG ρ hN2 hρcont hN hd) hd‖ = 1
      ∧ sliceHat μG ρ hN2 hρcont hN 0
          (sliceHPosOne_zero μG ρ hN2 hρcont hN hd)
          (sliceOmega μG ρ hN2 hρcont hN 0
            (sliceHPosOne_zero μG ρ hN2 hρcont hN hd) hd)
        = sliceOmega μG ρ hN2 hρcont hN 0
            (sliceHPosOne_zero μG ρ hN2 hρcont hN hd) hd :=
  ⟨sliceOmega_norm μG ρ hN2 hρcont hN 0
      (sliceHPosOne_zero μG ρ hN2 hρcont hN hd) hd,
    sliceHat_sliceOmega μG ρ hN2 hρcont hN 0
      (sliceHPosOne_zero μG ρ hN2 hρcont hN hd) hd⟩

/-- **Acceptance, slice seat — the `Ĥ₀` bridge.** S2-1
phrases the reconstructed operators at `β = 0` on `ℂ`
itself, through the coordinate: `transferHatZero` carrying
the pairing, `hamZero` the zero operator, with
`exp(−Ĥ₀) = T̂₀` (`exp_neg_hamZero`). The bridge identity:
the coordinate pairing of `transferHatZero` is the engine's
own pairing of its descended operator — the two readings
of `T̂₀` agree, through `osForm_zero_slice_pair` and
`sliceRegression_hat_eq_id`. -/
theorem sliceRegression_coord_bridge (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (hd : 0 < d)
    (a b : ↥(sliceObsSubmodule (N := N) μG ρ 0)) :
    inner ℂ (sliceCoord μG b.1)
        (transferHatZero (sliceCoord μG a.1))
      = inner ℂ
          (sliceMk μG ρ hN2 hρcont hN 0
            (sliceHPosOne_zero μG ρ hN2 hρcont hN hd) b)
          (sliceHat μG ρ hN2 hρcont hN 0
            (sliceHPosOne_zero μG ρ hN2 hρcont hN hd)
            (sliceMk μG ρ hN2 hρcont hN 0
              (sliceHPosOne_zero μG ρ hN2 hρcont hN hd) a)) := by
  calc inner ℂ (sliceCoord μG b.1)
        (transferHatZero (sliceCoord μG a.1))
      = osForm μG ρ 0 (sliceObs b.1) (sliceObs a.1) :=
        transferHatZero_pairing μG ρ hρcont hN hN2 hd b.1
          a.1 b.2 a.2
    _ = (starRingEnd ℂ) (sliceCoord μG b.1)
          * sliceCoord μG a.1 :=
        osForm_zero_slice_pair μG ρ hρcont hN hN2 hd b.1 a.1
          b.2 a.2
    _ = inner ℂ
          (sliceMk μG ρ hN2 hρcont hN 0
            (sliceHPosOne_zero μG ρ hN2 hρcont hN hd) b)
          (sliceMk μG ρ hN2 hρcont hN 0
            (sliceHPosOne_zero μG ρ hN2 hρcont hN hd) a) :=
        (sliceRegression_inner_zero μG ρ hN2 hρcont hN hd
          b a).symm
    _ = inner ℂ
          (sliceMk μG ρ hN2 hρcont hN 0
            (sliceHPosOne_zero μG ρ hN2 hρcont hN hd) b)
          (sliceHat μG ρ hN2 hρcont hN 0
            (sliceHPosOne_zero μG ρ hN2 hρcont hN hd)
            (sliceMk μG ρ hN2 hρcont hN 0
              (sliceHPosOne_zero μG ρ hN2 hρcont hN hd) a)) := by
        rw [sliceRegression_hat_eq_id μG ρ hN2 hρcont hN hd,
          LinearMap.id_apply]

/-! ## §3. The strict seat: S2-1's package, re-proved verbatim

The engine of 2c is built on `𝔸_slice` only; it asserts
nothing on the strict (plane-independent) seat. The gate's
§3.7 acceptance test nevertheless has a strict bullet list,
and the suite executes it here by re-proving each bullet
from S2-1's landed theorems — the regression content is
that the bullets still hold, verbatim, in the engine's
presence, and that the same one-dimensional operators of
S2-1's `ReconOps` carry both seats. -/

/-- **Acceptance, strict seat — the pairing.** On
plane-independent observables at `β = 0`, the OS form is the
product of the conjugate strict state and the strict state
(S2-1's `osForm_zero_strict_pair`, verbatim). -/
theorem sliceRegression_strict_pair
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (hd : 0 < d)
    (φ χ : (↥(posLinks (N := N)) → G) → ℂ)
    (hφ : Measurable φ) (hχ : Measurable χ) :
    osForm μG ρ 0 (halfLift (χ ∘ restrictPos))
        (halfLift (φ ∘ restrictPos))
      = (starRingEnd ℂ) (strictState μG χ)
        * strictState μG φ :=
  osForm_zero_strict_pair μG ρ hρcont hN hd φ χ hφ hχ

/-- **Acceptance, strict seat — the diagonal.** A squared
norm (S2-1's `osForm_zero_strict_diag`, verbatim): the
exact value behind strict-seat positivity. -/
theorem sliceRegression_strict_diag
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (hd : 0 < d)
    (φ : (↥(posLinks (N := N)) → G) → ℂ) (hφ : Measurable φ) :
    osForm μG ρ 0 (halfLift (φ ∘ restrictPos))
        (halfLift (φ ∘ restrictPos))
      = ((‖strictState μG φ‖ : ℂ) ^ 2) :=
  osForm_zero_strict_diag μG ρ hρcont hN hd φ hφ

/-- **Acceptance, strict seat — positivity.** The diagonal
is real and nonnegative (S2-1's
`osForm_zero_strict_diag_nonneg`, verbatim). -/
theorem sliceRegression_strict_diag_nonneg
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (hd : 0 < d)
    (φ : (↥(posLinks (N := N)) → G) → ℂ) (hφ : Measurable φ) :
    (osForm μG ρ 0 (halfLift (φ ∘ restrictPos))
        (halfLift (φ ∘ restrictPos))).im = 0
      ∧ 0 ≤ (osForm μG ρ 0 (halfLift (φ ∘ restrictPos))
        (halfLift (φ ∘ restrictPos))).re :=
  osForm_zero_strict_diag_nonneg μG ρ hρcont hN hd φ hφ

/-- **Acceptance, strict seat — the null space is
`ker strictState`** (S2-1's `osForm_zero_strict_null`,
verbatim). -/
theorem sliceRegression_strict_null
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (hd : 0 < d)
    (φ : (↥(posLinks (N := N)) → G) → ℂ) (hφ : Measurable φ) :
    osForm μG ρ 0 (halfLift (φ ∘ restrictPos))
        (halfLift (φ ∘ restrictPos)) = 0
      ↔ strictState μG φ = 0 :=
  osForm_zero_strict_null μG ρ hρcont hN hd φ hφ

/-- **Acceptance, strict seat — the identity carries the
pairing.** On strict states, `transferHatZero` (the
identity on `ℂ`) reproduces the OS pairing (S2-1's
`strict_transferHat_pairing`, verbatim): the descended
operator of the strict seat is `T̂₀ = id` on its
one-dimensional quotient, the same operator that carries
the slice seat by `sliceRegression_coord_bridge`. -/
theorem sliceRegression_strict_transferHat_pairing
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (hd : 0 < d)
    (φ χ : (↥(posLinks (N := N)) → G) → ℂ)
    (hφ : Measurable φ) (hχ : Measurable χ) :
    inner ℂ (strictState μG χ)
        (transferHatZero (strictState μG φ))
      = osForm μG ρ 0 (halfLift (χ ∘ restrictPos))
          (halfLift (φ ∘ restrictPos)) :=
  strict_transferHat_pairing μG ρ hρcont hN hd φ χ hφ hχ

/-! ## §4. The headline regression package -/

/-- **★ THE β = 0 REGRESSION PACKAGE (S2-2d).**

The gate's §3.7 acceptance test, executed on both
surviving seats, against the engine of S2-2c specialized
at `β = 0` with its hypothesis discharged
(`sliceHPosOne_zero`), and against S2-1's landed packages
in `LatticeReconZero`. At general `(G, ρ)`, even `N`:

*Slice seat.* (1) `SliceHPosOne` holds at `β = 0` —
discharged, not assumed. (2) The engine's inner product on
classes is the coordinate pairing
`conj (coord a) * coord b`. (3) The engine's null submodule
is `ker coord`. (4) Every class is its coordinate multiple
of the vacuum, `[a] = coord a • Ω`. (5) The quotient is the
vacuum line `ℂ·Ω₀`. (6) The states are given by `coord`,
which is surjective. (7) The descended operator is the
identity, `T̂₀ = id`. (8) The vacuum clauses: `‖Ω‖ = 1` and
`T̂₀ Ω = Ω`. (9) The coordinate bridge: S2-1's
`transferHatZero` on coordinates carries the engine's
`T̂₀`-pairing. (10) The `Ĥ₀` package in S2-1's phrasing:
`hamZero` is the zero operator and
`exp(−Ĥ₀) = transferHatZero = T̂₀`. (11) S2-1's bundle
`recon_zero_slice_package`, verbatim, for all `L²` slice
observables.

*Strict seat.* (12) The pairing
`conj (strictState χ) * strictState φ`. (13) The null space
is `ker strictState`. (14) Positivity: the diagonal is
real and nonnegative. (15) `strictState` is surjective
with constants mapping to themselves — the strict quotient
is `ℂ·Ω₀`. (16) The identity operator carries the strict
pairing.

**Regression verdict of this package:** agreement on both
seats; kills K-S2-2(d)ʳ and K-S2-2(e)ʳ do not fire.
**Fences:** the only positivity in the package is clause
(1) (the coordinate square at `β = 0`) and S2-1's landed
strict-seat diagonal (14); no OS-form positivity at general
`β` or on any plane-seeing class is asserted, and this
package is not a discharge of Stage 1b-B. NO CLAIM; Clay
parts closed: 0. -/
theorem sliceRegression_package (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (hd : 0 < d) :
    SliceHPosOne μG ρ hN2 hρcont 0
    ∧ (∀ a b : ↥(sliceObsSubmodule (N := N) μG ρ 0),
        inner ℂ
            (sliceMk μG ρ hN2 hρcont hN 0
              (sliceHPosOne_zero μG ρ hN2 hρcont hN hd) a)
            (sliceMk μG ρ hN2 hρcont hN 0
              (sliceHPosOne_zero μG ρ hN2 hρcont hN hd) b)
          = (starRingEnd ℂ) (sliceCoord μG a.1)
            * sliceCoord μG b.1)
    ∧ (∀ a : ↥(sliceObsSubmodule (N := N) μG ρ 0),
        (a ∈ sliceNullSubmodule μG ρ hN2 hρcont hN 0
            (sliceHPosOne_zero μG ρ hN2 hρcont hN hd))
          ↔ sliceCoord μG a.1 = 0)
    ∧ (∀ a : ↥(sliceObsSubmodule (N := N) μG ρ 0),
        sliceMk μG ρ hN2 hρcont hN 0
            (sliceHPosOne_zero μG ρ hN2 hρcont hN hd) a
          = sliceCoord μG a.1 • sliceOmega μG ρ hN2 hρcont
              hN 0
              (sliceHPosOne_zero μG ρ hN2 hρcont hN hd) hd)
    ∧ (∀ x : sliceQuotient μG ρ hN2 hρcont hN 0
          (sliceHPosOne_zero μG ρ hN2 hρcont hN hd),
        ∃ c : ℂ, x = c • sliceOmega μG ρ hN2 hρcont hN 0
          (sliceHPosOne_zero μG ρ hN2 hρcont hN hd) hd)
    ∧ Function.Surjective (sliceCoord μG (N := N))
    ∧ sliceHat μG ρ hN2 hρcont hN 0
          (sliceHPosOne_zero μG ρ hN2 hρcont hN hd)
        = LinearMap.id
    ∧ (‖sliceOmega μG ρ hN2 hρcont hN 0
          (sliceHPosOne_zero μG ρ hN2 hρcont hN hd) hd‖ = 1
        ∧ sliceHat μG ρ hN2 hρcont hN 0
            (sliceHPosOne_zero μG ρ hN2 hρcont hN hd)
            (sliceOmega μG ρ hN2 hρcont hN 0
              (sliceHPosOne_zero μG ρ hN2 hρcont hN hd) hd)
          = sliceOmega μG ρ hN2 hρcont hN 0
              (sliceHPosOne_zero μG ρ hN2 hρcont hN hd) hd)
    ∧ (∀ a b : ↥(sliceObsSubmodule (N := N) μG ρ 0),
        inner ℂ (sliceCoord μG b.1)
            (transferHatZero (sliceCoord μG a.1))
          = inner ℂ
              (sliceMk μG ρ hN2 hρcont hN 0
                (sliceHPosOne_zero μG ρ hN2 hρcont hN hd) b)
              (sliceHat μG ρ hN2 hρcont hN 0
                (sliceHPosOne_zero μG ρ hN2 hρcont hN hd)
                (sliceMk μG ρ hN2 hρcont hN 0
                  (sliceHPosOne_zero μG ρ hN2 hρcont hN hd)
                  a)))
    ∧ ((∀ z : ℂ, hamZero z = 0)
        ∧ NormedSpace.exp (-hamZero) = transferHatZero)
    ∧ (∀ (φ χ : (↥(sliceLinks (N := N)) → G) → ℂ)
          (hφ : MemLp φ 2 (sliceMeasure (N := N) μG ρ 0))
          (hχ : MemLp χ 2 (sliceMeasure (N := N) μG ρ 0)),
        (osForm μG ρ 0 (sliceObs φ) (sliceObs χ)
            = (starRingEnd ℂ) (sliceCoord μG φ)
              * sliceCoord μG χ)
          ∧ (osForm μG ρ 0 (sliceObs φ) (sliceObs φ) = 0
              ↔ sliceCoord μG φ = 0)
          ∧ sliceCoord μG
              (1 : (↥(sliceLinks (N := N)) → G) → ℂ) = 1
          ∧ transferHatZero (sliceCoord μG χ)
              = sliceCoord μG χ
          ∧ hamZero (sliceCoord μG χ) = 0)
    ∧ (∀ (φ χ : (↥(posLinks (N := N)) → G) → ℂ)
          (hφ : Measurable φ) (hχ : Measurable χ),
        osForm μG ρ 0 (halfLift (χ ∘ restrictPos))
            (halfLift (φ ∘ restrictPos))
          = (starRingEnd ℂ) (strictState μG χ)
            * strictState μG φ)
    ∧ (∀ (φ : (↥(posLinks (N := N)) → G) → ℂ)
          (hφ : Measurable φ),
        osForm μG ρ 0 (halfLift (φ ∘ restrictPos))
            (halfLift (φ ∘ restrictPos)) = 0
          ↔ strictState μG φ = 0)
    ∧ (∀ (φ : (↥(posLinks (N := N)) → G) → ℂ)
          (hφ : Measurable φ),
        (osForm μG ρ 0 (halfLift (φ ∘ restrictPos))
            (halfLift (φ ∘ restrictPos))).im = 0
          ∧ 0 ≤ (osForm μG ρ 0 (halfLift (φ ∘ restrictPos))
            (halfLift (φ ∘ restrictPos))).re)
    ∧ (Function.Surjective (strictState μG (N := N))
        ∧ ∀ c : ℂ, strictState μG
            (fun _ : ↥(posLinks (N := N)) → G => c) = c)
    ∧ (∀ (φ χ : (↥(posLinks (N := N)) → G) → ℂ)
          (hφ : Measurable φ) (hχ : Measurable χ),
        inner ℂ (strictState μG χ)
            (transferHatZero (strictState μG φ))
          = osForm μG ρ 0 (halfLift (χ ∘ restrictPos))
              (halfLift (φ ∘ restrictPos))) := by
  refine ⟨sliceHPosOne_zero μG ρ hN2 hρcont hN hd,
    fun a b => sliceRegression_inner_zero μG ρ hN2 hρcont
      hN hd a b,
    fun a => sliceRegression_mem_null_iff μG ρ hN2 hρcont
      hN hd a,
    fun a => sliceRegression_mk_eq_coord_smul_omega μG ρ
      hN2 hρcont hN hd a,
    sliceRegression_quotient_eq_vacuum_line μG ρ hN2 hρcont
      hN hd,
    sliceCoord_surjective μG,
    sliceRegression_hat_eq_id μG ρ hN2 hρcont hN hd,
    sliceRegression_vacuum_zero μG ρ hN2 hρcont hN hd,
    fun a b => sliceRegression_coord_bridge μG ρ hN2
      hρcont hN hd a b,
    ⟨fun z => hamZero_apply z, exp_neg_hamZero⟩,
    fun φ χ hφ hχ => recon_zero_slice_package μG ρ hρcont
      hN hN2 hd φ χ hφ hχ,
    fun φ χ hφ hχ => sliceRegression_strict_pair μG ρ
      hρcont hN hd φ χ hφ hχ,
    fun φ hφ => sliceRegression_strict_null μG ρ hρcont
      hN hd φ hφ,
    fun φ hφ => sliceRegression_strict_diag_nonneg μG ρ
      hρcont hN hd φ hφ,
    ⟨strictState_surjective μG,
      fun c => strictState_const μG c⟩,
    fun φ χ hφ hχ =>
      sliceRegression_strict_transferHat_pairing μG ρ
        hρcont hN hd φ χ hφ hχ⟩

end SliceRegression

end ThetLogos
