/-
# Stage 2, brick S2-2c — the conditional slice GNS engine, assembled

**READ THIS FIRST — what this module is, and what it is NOT.**

This module assembles the conditional Osterwalder–Schrader / GNS
engine of the REVISED S2-2 gate
(`whitepaper/stage2-s22-gate-revision-2026-10-24.md`, §3.6) from the
landed bricks S2-2a (`LatticeSlicePairing`: the factored pairings
`Π₁`, `Π₂` on the slice algebra `𝔸_slice`) and S2-2b
(`LatticeSliceDescent`: descent, Cauchy–Schwarz, diagonal
domination, the norm bound). Everything is at general `(G, ρ)`,
every real `β`, even `N`.

**The engine is CONDITIONAL. Its one named hypothesis is
`SliceHPosOne` (H-pos(1)ʳ): the one-step diagonal form `Π₁` is
positive on `𝔸_slice`.** That hypothesis is *assumed* here, never
proved — its discharge is the business of the downstream brick
S2-3 (the re-aimed Route-C clause `(R-C2)ʳ` at `Π₂`), not of this
module. **This module is NOT a discharge of Stage 1b-B positivity,
and no statement in it asserts positivity of the OS form
`osForm` on any algebra.** A reader must not be able to mistake
the conditional engine for positivity proved: the hypothesis
`SliceHPosOne` appears explicitly in every headline below.

Under that single hypothesis, this module proves:

* the `Π₁`-null space is a submodule of `𝔸_slice` (it is the
  radical of `Π₁`, by 2b's Cauchy–Schwarz);
* the quotient `ℋ := 𝔸_slice ⧸ null` carries a genuine inner
  product (the descended `Π₁`), making it a pre-Hilbert space —
  completion is deliberately NOT taken (gate §3.6 policy);
* the descended transfer operator `T̂` exists on `ℋ` as a bounded
  self-adjoint operator with `‖T̂‖ ≤ 1`, characterized on classes
  by `⟪[χ], T̂[φ]⟫ = Π₂(χ, φ)`;
* `T̂ ≥ 0` in **factored form only**: `0 ≤ ⟪x, T̂ x⟫.re` holds
  because `Π₂`'s diagonal is a norm square by construction
  (2b's `sliceHPosTwo_proved`). This is positivity of the
  *factored* two-step pairing — it is **not** OS-form positivity
  and it is **not** an input to, or a discharge of, 1b-B;
* the vacuum class `Ω = [1]` is a unit vector with `T̂ Ω = Ω`
  (the vacuum clause consumes 2b's `(D-vac)ʳ`, which carries the
  side condition `0 < d`);
* `Ω` is cyclic in the gate's stated sense by construction:
  every class of `ℋ` is `[φ]` for an observable `φ`, so the
  classes — in particular the orbit of `Ω`'s representatives —
  exhaust `ℋ` (no completion, no closure is taken).

**Fences held throughout.** `SliceHPosOne` is never discharged.
No `osForm` positivity is asserted anywhere. `T̂ ≥ 0` is stated
as factored-form positivity and labeled as such. The unlanded
identification of R3's two-point operator at depth two with
`transferOp^2` is not consumed — the name `twoPointOp` does not
occur in this module; `Π₂` is used only in its landed factored
form (bare iteration of `transferOp` on slice states). TM R2
stays fenced (no Markov/layer factorization is used or implied).
The plane test is passed by structural exclusion: the engine
sees only slice states (`sliceState` images), never
plane-supported observables.

**Status:** brick S2-2c — verdict STANDS, parent-verified
2026-10-24 (targeted build exit 0, strict recount, axiom
check). Dossier:
`whitepaper/stage2-s22c-engine-2026-10-24.md`.
NO CLAIM. Clay parts closed: 0. The Yang–Mills mass
gap is not touched by this module; the continuum theory
(road-map Items 4–5) does not exist in the corpus.

## What is proved here, in order

§1 the observable submodule `𝔸_slice` as a `Submodule`, the
pairings restricted to its elements, the null submodule and the
radical characterization. §2 the quotient and its inner product
(well-definedness = the radical vanishing), the
`InnerProductSpace` instance stack. §3 the step observable and
the descended operator `T̂` (linear map, then continuous linear
map), self-adjointness, factored positivity, the operator norm
bound. §4 the vacuum. §5 the bundled engine package
(`sliceEngine_package`), stated in the form brick S2-2d
regresses against S2-1's `β = 0` package and S2-3 consumes:
S2-3's discharge of H-pos(1)ʳ plugs into exactly the
`SliceHPosOne` hypothesis of that theorem.
-/

import ThetLogos.LatticeSliceDescent

namespace ThetLogos

open MeasureTheory Finset
open scoped Matrix ENNReal NNReal InnerProduct

section SliceEngine

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ))
  {N : ℕ} [NeZero N]

/-! ## §1. The observable submodule, the null submodule, the radical -/

/-- **The slice observable algebra `𝔸_slice`, as a submodule** of
the slice function space: the `L²` slice observables — exactly the
elements `2a`'s pairings are evaluated on. (The algebra structure
is not needed by the engine; the module structure is what the
quotient consumes.) -/
def sliceObsSubmodule (β : ℝ) :
    Submodule ℂ ((↥(sliceLinks (N := N)) → G) → ℂ) where
  carrier := {φ | MemLp φ 2 (sliceMeasure (N := N) μG ρ β)}
  zero_mem' := MemLp.zero
  add_mem' := by
    intro φ χ hφ hχ
    exact hφ.add hχ
  smul_mem' := by
    intro c φ hφ
    exact hφ.const_smul c

/-- `Π₁` evaluated on elements of `𝔸_slice` (2a's
`slicePairOne`, witnesses read off the elements). -/
noncomputable def slicePairOneObs (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g) (β : ℝ)
    (a b : ↥(sliceObsSubmodule (N := N) μG ρ β)) : ℂ :=
  slicePairOne μG ρ hN2 hρcont β a.1 a.2 b.1 b.2

/-- `Π₂` evaluated on elements of `𝔸_slice` (2a's
`slicePairTwo`, witnesses read off the elements). -/
noncomputable def slicePairTwoObs (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g) (β : ℝ)
    (a b : ↥(sliceObsSubmodule (N := N) μG ρ β)) : ℂ :=
  slicePairTwo μG ρ hN2 hρcont β a.1 a.2 b.1 b.2

/-- **Vanishing, left slot:** a `Π₁`-null observable pairs to zero
against everything on the left — the radical property, from 2b's
`slicePairOne_cauchy_schwarz` under H-pos(1)ʳ. -/
theorem slicePairOneObs_eq_zero_of_self_eq_zero_left (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    {a : ↥(sliceObsSubmodule (N := N) μG ρ β)}
    (ha : slicePairOneObs μG ρ hN2 hρcont β a a = 0)
    (b : ↥(sliceObsSubmodule (N := N) μG ρ β)) :
    slicePairOneObs μG ρ hN2 hρcont β a b = 0 := by
  have hcs := slicePairOne_cauchy_schwarz μG ρ hN2 hρcont hN β hpos
    a.1 b.1 a.2 b.2
  have ha' : slicePairOne μG ρ hN2 hρcont β a.1 a.2 a.1 a.2 = 0 := ha
  rw [ha'] at hcs
  simp only [Complex.zero_re, zero_mul] at hcs
  have hsq : ‖slicePairOneObs μG ρ hN2 hρcont β a b‖ ^ 2 = 0 :=
    le_antisymm hcs (sq_nonneg _)
  have hnorm : ‖slicePairOneObs μG ρ hN2 hρcont β a b‖ = 0 := by
    by_contra hne
    have hpos' : 0 < ‖slicePairOneObs μG ρ hN2 hρcont β a b‖ :=
      lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
    exact ne_of_gt (pow_pos hpos' 2) hsq
  exact norm_eq_zero.mp hnorm

/-- **Vanishing, right slot:** a `Π₁`-null observable pairs to
zero against everything on the right (same Cauchy–Schwarz,
slots swapped). -/
theorem slicePairOneObs_eq_zero_of_self_eq_zero_right (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    {a : ↥(sliceObsSubmodule (N := N) μG ρ β)}
    (ha : slicePairOneObs μG ρ hN2 hρcont β a a = 0)
    (b : ↥(sliceObsSubmodule (N := N) μG ρ β)) :
    slicePairOneObs μG ρ hN2 hρcont β b a = 0 := by
  have hleft : slicePairOne μG ρ hN2 hρcont β a.1 a.2 b.1 b.2 = 0 :=
    slicePairOneObs_eq_zero_of_self_eq_zero_left μG ρ hN2 hρcont hN β
      hpos ha b
  have hsymm : slicePairOne μG ρ hN2 hρcont β b.1 b.2 a.1 a.2
      = (starRingEnd ℂ)
          (slicePairOne μG ρ hN2 hρcont β a.1 a.2 b.1 b.2) :=
    slicePairOne_conj_symm μG ρ hN2 hρcont hN β b.1 a.1 b.2 a.2
  show slicePairOne μG ρ hN2 hρcont β b.1 b.2 a.1 a.2 = 0
  rw [hsymm, hleft, map_zero]

/-- **The null submodule of `Π₁`** (under H-pos(1)ʳ): the
observables whose one-step diagonal vanishes. Closure under
addition is exactly the radical property (2b's Cauchy–Schwarz
through 2a's sesquilinearity); closure under scaling is 2a's
sesquilinearity alone. This is the submodule the engine
quotients by. -/
def sliceNullSubmodule (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) :
    Submodule ℂ ↥(sliceObsSubmodule (N := N) μG ρ β) where
  carrier := {a | slicePairOneObs μG ρ hN2 hρcont β a a = 0}
  zero_mem' := by
    show slicePairOne μG ρ hN2 hρcont β
      (0 : ((↥(sliceLinks (N := N)) → G) → ℂ)) MemLp.zero
      (0 : ((↥(sliceLinks (N := N)) → G) → ℂ)) MemLp.zero = 0
    simp only [slicePairOne, sliceState, MemLp.toLp_zero, map_zero,
      inner_zero_left]
  add_mem' := by
    intro a b ha hb
    have haa : slicePairOne μG ρ hN2 hρcont β a.1 a.2 a.1 a.2 = 0 := ha
    have hbb : slicePairOne μG ρ hN2 hρcont β b.1 b.2 b.1 b.2 = 0 := hb
    have hab : slicePairOne μG ρ hN2 hρcont β a.1 a.2 b.1 b.2 = 0 :=
      slicePairOneObs_eq_zero_of_self_eq_zero_left μG ρ hN2 hρcont
        hN β hpos ha b
    have hba : slicePairOne μG ρ hN2 hρcont β b.1 b.2 a.1 a.2 = 0 :=
      slicePairOneObs_eq_zero_of_self_eq_zero_left μG ρ hN2 hρcont
        hN β hpos hb a
    show slicePairOne μG ρ hN2 hρcont β (a.1 + b.1) (a.2.add b.2)
      (a.1 + b.1) (a.2.add b.2) = 0
    rw [slicePairOne_add_left μG ρ hN2 hρcont β a.1 b.1 (a.1 + b.1)
        a.2 b.2 (a.2.add b.2),
      slicePairOne_add_right μG ρ hN2 hρcont β a.1 a.1 b.1 a.2 a.2 b.2,
      slicePairOne_add_right μG ρ hN2 hρcont β b.1 a.1 b.1 b.2 a.2 b.2,
      haa, hab, hba, hbb]
    simp
  smul_mem' := by
    intro c a ha
    have haa : slicePairOne μG ρ hN2 hρcont β a.1 a.2 a.1 a.2 = 0 := ha
    show slicePairOne μG ρ hN2 hρcont β (c • a.1) (a.2.const_smul c)
      (c • a.1) (a.2.const_smul c) = 0
    rw [slicePairOne_smul_left μG ρ hN2 hρcont β c a.1 (c • a.1) a.2
        (a.2.const_smul c),
      slicePairOne_smul_right μG ρ hN2 hρcont β c a.1 a.1 a.2 a.2,
      haa]
    simp

/-- Membership in the null submodule is the vanishing of the
diagonal, by definition. -/
theorem mem_sliceNullSubmodule {hN2 : 2 ≤ N}
    {hρcont : Continuous fun g : G => repMatrix ρ g}
    {hN : Even N} {β : ℝ}
    {hpos : SliceHPosOne μG ρ hN2 hρcont β}
    (a : ↥(sliceObsSubmodule (N := N) μG ρ β)) :
    a ∈ sliceNullSubmodule μG ρ hN2 hρcont hN β hpos ↔
      slicePairOneObs μG ρ hN2 hρcont β a a = 0 :=
  Iff.rfl

/-- **The null space is the radical of `Π₁`:** the diagonal
vanishes iff every pairing against `a` vanishes (under
H-pos(1)ʳ, by 2b's Cauchy–Schwarz). -/
theorem slicePairOneObs_self_eq_zero_iff_forall (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (a : ↥(sliceObsSubmodule (N := N) μG ρ β)) :
    slicePairOneObs μG ρ hN2 hρcont β a a = 0 ↔
      ∀ b : ↥(sliceObsSubmodule (N := N) μG ρ β),
        slicePairOneObs μG ρ hN2 hρcont β a b = 0 := by
  constructor
  · intro ha b
    exact slicePairOneObs_eq_zero_of_self_eq_zero_left μG ρ hN2
      hρcont hN β hpos ha b
  · intro h
    exact h a

/-- Coercion of a sum of observables is the sum of the
functions (definitional for the SetLike subtype). -/
theorem sliceObs_coe_add (a b : ↥(sliceObsSubmodule (N := N) μG ρ β)) :
    ((a + b : ↥(sliceObsSubmodule (N := N) μG ρ β)) :
      ((↥(sliceLinks (N := N)) → G) → ℂ)) = a.1 + b.1 :=
  rfl

/-- Coercion of a scalar multiple of an observable
(definitional). -/
theorem sliceObs_coe_smul (c : ℂ)
    (a : ↥(sliceObsSubmodule (N := N) μG ρ β)) :
    ((c • a : ↥(sliceObsSubmodule (N := N) μG ρ β)) :
      ((↥(sliceLinks (N := N)) → G) → ℂ)) = c • a.1 :=
  rfl

/-- Coercion of the zero observable (definitional). -/
theorem sliceObs_coe_zero :
    ((0 : ↥(sliceObsSubmodule (N := N) μG ρ β)) :
      ((↥(sliceLinks (N := N)) → G) → ℂ)) = 0 :=
  rfl

/-- Coercion of a difference of observables (definitional). -/
theorem sliceObs_coe_sub (a b : ↥(sliceObsSubmodule (N := N) μG ρ β)) :
    ((a - b : ↥(sliceObsSubmodule (N := N) μG ρ β)) :
      ((↥(sliceLinks (N := N)) → G) → ℂ)) = a.1 - b.1 :=
  rfl

/-! ## §2. The quotient space and its inner product -/

/-- **Congruence of `Π₁` in the first function:** the pairing
depends on the function, not on the chosen representative or
witness (proof irrelevance). -/
theorem slicePairOne_congr_left (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g) (β : ℝ)
    {φ φ' : ((↥(sliceLinks (N := N)) → G) → ℂ)} (hφφ' : φ = φ')
    (hφ : MemLp φ 2 (sliceMeasure (N := N) μG ρ β))
    (hφ' : MemLp φ' 2 (sliceMeasure (N := N) μG ρ β))
    (χ : ((↥(sliceLinks (N := N)) → G) → ℂ))
    (hχ : MemLp χ 2 (sliceMeasure (N := N) μG ρ β)) :
    slicePairOne μG ρ hN2 hρcont β φ hφ χ hχ
      = slicePairOne μG ρ hN2 hρcont β φ' hφ' χ hχ := by
  subst hφφ'
  rfl

/-- **Congruence of `Π₁` in the second function.** -/
theorem slicePairOne_congr_right (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g) (β : ℝ)
    (φ : ((↥(sliceLinks (N := N)) → G) → ℂ))
    (hφ : MemLp φ 2 (sliceMeasure (N := N) μG ρ β))
    {χ χ' : ((↥(sliceLinks (N := N)) → G) → ℂ)} (hχχ' : χ = χ')
    (hχ : MemLp χ 2 (sliceMeasure (N := N) μG ρ β))
    (hχ' : MemLp χ' 2 (sliceMeasure (N := N) μG ρ β)) :
    slicePairOne μG ρ hN2 hρcont β φ hφ χ hχ
      = slicePairOne μG ρ hN2 hρcont β φ hφ χ' hχ' := by
  subst hχχ'
  rfl

/-- **Congruence of `Π₂` in the first function.** -/
theorem slicePairTwo_congr_left (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g) (β : ℝ)
    {φ φ' : ((↥(sliceLinks (N := N)) → G) → ℂ)} (hφφ' : φ = φ')
    (hφ : MemLp φ 2 (sliceMeasure (N := N) μG ρ β))
    (hφ' : MemLp φ' 2 (sliceMeasure (N := N) μG ρ β))
    (χ : ((↥(sliceLinks (N := N)) → G) → ℂ))
    (hχ : MemLp χ 2 (sliceMeasure (N := N) μG ρ β)) :
    slicePairTwo μG ρ hN2 hρcont β φ hφ χ hχ
      = slicePairTwo μG ρ hN2 hρcont β φ' hφ' χ hχ := by
  subst hφφ'
  rfl

/-- **Congruence of `Π₂` in the second function.** -/
theorem slicePairTwo_congr_right (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g) (β : ℝ)
    (φ : ((↥(sliceLinks (N := N)) → G) → ℂ))
    (hφ : MemLp φ 2 (sliceMeasure (N := N) μG ρ β))
    {χ χ' : ((↥(sliceLinks (N := N)) → G) → ℂ)} (hχχ' : χ = χ')
    (hχ : MemLp χ 2 (sliceMeasure (N := N) μG ρ β))
    (hχ' : MemLp χ' 2 (sliceMeasure (N := N) μG ρ β)) :
    slicePairTwo μG ρ hN2 hρcont β φ hφ χ hχ
      = slicePairTwo μG ρ hN2 hρcont β φ hφ χ' hχ' := by
  subst hχχ'
  rfl

/-- **The engine's pre-Hilbert space** (gate §3.6): the
quotient of `𝔸_slice` by the `Π₁`-null submodule, under
H-pos(1)ʳ. No completion is taken (the gate's completion
policy): the descended operator acts on this pre-Hilbert
space itself. -/
abbrev sliceQuotient (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) : Type _ :=
  ↥(sliceObsSubmodule (N := N) μG ρ β) ⧸
    sliceNullSubmodule μG ρ hN2 hρcont hN β hpos

/-- The class of an observable in the engine space. -/
abbrev sliceMk (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (a : ↥(sliceObsSubmodule (N := N) μG ρ β)) :
    sliceQuotient μG ρ hN2 hρcont hN β hpos :=
  Submodule.Quotient.mk a

/-- Classes respect addition of representatives. -/
theorem sliceMk_add (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (a b : ↥(sliceObsSubmodule (N := N) μG ρ β)) :
    sliceMk μG ρ hN2 hρcont hN β hpos (a + b)
      = sliceMk μG ρ hN2 hρcont hN β hpos a
        + sliceMk μG ρ hN2 hρcont hN β hpos b :=
  (sliceNullSubmodule μG ρ hN2 hρcont hN β hpos).mkQ.map_add a b

/-- Classes respect scaling of representatives. -/
theorem sliceMk_smul (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (c : ℂ)
    (a : ↥(sliceObsSubmodule (N := N) μG ρ β)) :
    sliceMk μG ρ hN2 hρcont hN β hpos (c • a)
      = c • sliceMk μG ρ hN2 hρcont hN β hpos a :=
  (sliceNullSubmodule μG ρ hN2 hρcont hN β hpos).mkQ.map_smul c a

/-- **The descended inner product on classes:** `Π₁` read on
representatives. Well-definedness is the radical property:
a null difference pairs to zero on both sides (2b's
Cauchy–Schwarz), through 2a's sesquilinearity. -/
noncomputable def sliceQuotientInnerFn (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) :
    sliceQuotient μG ρ hN2 hρcont hN β hpos →
    sliceQuotient μG ρ hN2 hρcont hN β hpos → ℂ :=
  Quotient.lift₂ (fun a b => slicePairOneObs μG ρ hN2 hρcont β a b)
    (by
      intro a b a' b' ha hb
      have ha' : a - a' ∈ sliceNullSubmodule μG ρ hN2 hρcont hN β
          hpos :=
        (Submodule.quotientRel_def (p :=
          sliceNullSubmodule μG ρ hN2 hρcont hN β hpos)).mp ha
      have hb' : b - b' ∈ sliceNullSubmodule μG ρ hN2 hρcont hN β
          hpos :=
        (Submodule.quotientRel_def (p :=
          sliceNullSubmodule μG ρ hN2 hρcont hN β hpos)).mp hb
      have ha0 : slicePairOneObs μG ρ hN2 hρcont β (a - a') (a - a')
          = 0 :=
        (mem_sliceNullSubmodule μG ρ (a - a')).mp ha'
      have hb0 : slicePairOneObs μG ρ hN2 hρcont β (b - b') (b - b')
          = 0 :=
        (mem_sliceNullSubmodule μG ρ (b - b')).mp hb'
      -- step 1: first slot, a vs a'
      have hvan1 : slicePairOne μG ρ hN2 hρcont β (a.1 - a'.1)
          (a - a').2 b.1 b.2 = 0 :=
        slicePairOneObs_eq_zero_of_self_eq_zero_left μG ρ hN2
          hρcont hN β hpos ha0 b
      have e1 := slicePairOne_add_left μG ρ hN2 hρcont β a'.1
        (a.1 - a'.1) b.1 a'.2 (a - a').2 b.2
      rw [hvan1, add_zero] at e1
      have hstep1 : slicePairOne μG ρ hN2 hρcont β a.1 a.2 b.1 b.2
          = slicePairOne μG ρ hN2 hρcont β a'.1 a'.2 b.1 b.2 :=
        (slicePairOne_congr_left μG ρ hN2 hρcont β
          (add_sub_cancel a'.1 a.1).symm a.2 (a'.2.add (a - a').2)
          b.1 b.2).trans e1
      -- step 2: second slot, b vs b'
      have hvan2 : slicePairOne μG ρ hN2 hρcont β a'.1 a'.2
          (b.1 - b'.1) (b - b').2 = 0 :=
        slicePairOneObs_eq_zero_of_self_eq_zero_right μG ρ hN2
          hρcont hN β hpos hb0 a'
      have e2 := slicePairOne_add_right μG ρ hN2 hρcont β a'.1 b'.1
        (b.1 - b'.1) a'.2 b'.2 (b - b').2
      rw [hvan2, add_zero] at e2
      have hstep2 : slicePairOne μG ρ hN2 hρcont β a'.1 a'.2 b.1 b.2
          = slicePairOne μG ρ hN2 hρcont β a'.1 a'.2 b'.1 b'.2 :=
        (slicePairOne_congr_right μG ρ hN2 hρcont β a'.1 a'.2
          (add_sub_cancel b'.1 b.1).symm b.2
          (b'.2.add (b - b').2)).trans e2
      exact hstep1.trans hstep2)

/-- The descended inner product on classes is `Π₁` on
representatives. -/
theorem sliceQuotientInnerFn_mk (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (a b : ↥(sliceObsSubmodule (N := N) μG ρ β)) :
    sliceQuotientInnerFn μG ρ hN2 hρcont hN β hpos
        (sliceMk μG ρ hN2 hρcont hN β hpos a)
        (sliceMk μG ρ hN2 hρcont hN β hpos b)
      = slicePairOneObs μG ρ hN2 hρcont β a b :=
  rfl

/-- Hermitian symmetry of the descended inner product (2a's
Hermiticity of `Π₁`, descended). -/
theorem sliceQuotientInnerFn_conj_symm (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (x y : sliceQuotient μG ρ hN2 hρcont hN β hpos) :
    (starRingEnd ℂ) (sliceQuotientInnerFn μG ρ hN2 hρcont hN β hpos
        y x)
      = sliceQuotientInnerFn μG ρ hN2 hρcont hN β hpos x y := by
  refine Submodule.Quotient.induction_on _ x ?_
  intro a
  refine Submodule.Quotient.induction_on _ y ?_
  intro b
  rw [sliceQuotientInnerFn_mk, sliceQuotientInnerFn_mk]
  exact (slicePairOne_conj_symm μG ρ hN2 hρcont hN β a.1 b.1 a.2
    b.2).symm

/-- Additivity of the descended inner product in the first
slot (2a's sesquilinearity, descended). -/
theorem sliceQuotientInnerFn_add_left (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (x y z : sliceQuotient μG ρ hN2 hρcont hN β hpos) :
    sliceQuotientInnerFn μG ρ hN2 hρcont hN β hpos (x + y) z
      = sliceQuotientInnerFn μG ρ hN2 hρcont hN β hpos x z
        + sliceQuotientInnerFn μG ρ hN2 hρcont hN β hpos y z := by
  refine Submodule.Quotient.induction_on _ x ?_
  intro a
  refine Submodule.Quotient.induction_on _ y ?_
  intro b
  refine Submodule.Quotient.induction_on _ z ?_
  intro c
  rw [← sliceMk_add, sliceQuotientInnerFn_mk,
    sliceQuotientInnerFn_mk, sliceQuotientInnerFn_mk]
  exact slicePairOne_add_left μG ρ hN2 hρcont β a.1 b.1 c.1 a.2 b.2
    c.2

/-- Conjugate-linearity of the descended inner product in the
first slot (2a's sesquilinearity, descended). -/
theorem sliceQuotientInnerFn_smul_left (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (c : ℂ)
    (x y : sliceQuotient μG ρ hN2 hρcont hN β hpos) :
    sliceQuotientInnerFn μG ρ hN2 hρcont hN β hpos (c • x) y
      = (starRingEnd ℂ) c
        * sliceQuotientInnerFn μG ρ hN2 hρcont hN β hpos x y := by
  refine Submodule.Quotient.induction_on _ x ?_
  intro a
  refine Submodule.Quotient.induction_on _ y ?_
  intro b
  rw [← sliceMk_smul, sliceQuotientInnerFn_mk,
    sliceQuotientInnerFn_mk]
  exact slicePairOne_smul_left μG ρ hN2 hρcont β c a.1 b.1 a.2 b.2

/-- Additivity of the descended inner product in the second
slot (from Hermitian symmetry and first-slot additivity). -/
theorem sliceQuotientInnerFn_add_right (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (x y z : sliceQuotient μG ρ hN2 hρcont hN β hpos) :
    sliceQuotientInnerFn μG ρ hN2 hρcont hN β hpos x (y + z)
      = sliceQuotientInnerFn μG ρ hN2 hρcont hN β hpos x y
        + sliceQuotientInnerFn μG ρ hN2 hρcont hN β hpos x z := by
  calc sliceQuotientInnerFn μG ρ hN2 hρcont hN β hpos x (y + z)
      = (starRingEnd ℂ) (sliceQuotientInnerFn μG ρ hN2 hρcont hN
          β hpos (y + z) x) :=
        (sliceQuotientInnerFn_conj_symm μG ρ hN2 hρcont hN β hpos
          x (y + z)).symm
    _ = (starRingEnd ℂ) (sliceQuotientInnerFn μG ρ hN2 hρcont hN
          β hpos y x + sliceQuotientInnerFn μG ρ hN2 hρcont hN β
          hpos z x) := by
        rw [sliceQuotientInnerFn_add_left μG ρ hN2 hρcont hN β hpos
          y z x]
    _ = (starRingEnd ℂ) (sliceQuotientInnerFn μG ρ hN2 hρcont hN
          β hpos y x) + (starRingEnd ℂ)
          (sliceQuotientInnerFn μG ρ hN2 hρcont hN β hpos z x) :=
        map_add _ _ _
    _ = sliceQuotientInnerFn μG ρ hN2 hρcont hN β hpos x y
        + sliceQuotientInnerFn μG ρ hN2 hρcont hN β hpos x z := by
        rw [sliceQuotientInnerFn_conj_symm μG ρ hN2 hρcont hN β
          hpos x y, sliceQuotientInnerFn_conj_symm μG ρ hN2 hρcont
          hN β hpos x z]

/-- Linearity of the descended inner product in the second
slot (from Hermitian symmetry and first-slot
conjugate-linearity). -/
theorem sliceQuotientInnerFn_smul_right (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (c : ℂ)
    (x y : sliceQuotient μG ρ hN2 hρcont hN β hpos) :
    sliceQuotientInnerFn μG ρ hN2 hρcont hN β hpos x (c • y)
      = c * sliceQuotientInnerFn μG ρ hN2 hρcont hN β hpos x y := by
  calc sliceQuotientInnerFn μG ρ hN2 hρcont hN β hpos x (c • y)
      = (starRingEnd ℂ) (sliceQuotientInnerFn μG ρ hN2 hρcont hN
          β hpos (c • y) x) :=
        (sliceQuotientInnerFn_conj_symm μG ρ hN2 hρcont hN β hpos
          x (c • y)).symm
    _ = (starRingEnd ℂ) ((starRingEnd ℂ) c
          * sliceQuotientInnerFn μG ρ hN2 hρcont hN β hpos y x) := by
        rw [sliceQuotientInnerFn_smul_left μG ρ hN2 hρcont hN β
          hpos c y x]
    _ = (starRingEnd ℂ) ((starRingEnd ℂ) c)
          * (starRingEnd ℂ) (sliceQuotientInnerFn μG ρ hN2 hρcont
            hN β hpos y x) :=
        map_mul _ _ _
    _ = c * sliceQuotientInnerFn μG ρ hN2 hρcont hN β hpos x
          y := by
        rw [starRingEnd_self_apply,
          sliceQuotientInnerFn_conj_symm μG ρ hN2 hρcont hN β hpos
            x y]

/-- Subtraction in the second slot of the descended inner
product. -/
theorem sliceQuotientInnerFn_sub_right (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (x y z : sliceQuotient μG ρ hN2 hρcont hN β hpos) :
    sliceQuotientInnerFn μG ρ hN2 hρcont hN β hpos x (y - z)
      = sliceQuotientInnerFn μG ρ hN2 hρcont hN β hpos x y
        - sliceQuotientInnerFn μG ρ hN2 hρcont hN β hpos x z := by
  have hneg : sliceQuotientInnerFn μG ρ hN2 hρcont hN β hpos x (-z)
      = - sliceQuotientInnerFn μG ρ hN2 hρcont hN β hpos x z := by
    have hs := sliceQuotientInnerFn_smul_right μG ρ hN2 hρcont hN
      β hpos (-1) x z
    rwa [neg_one_smul, neg_one_mul] at hs
  conv_lhs => rw [sub_eq_add_neg]
  rw [sliceQuotientInnerFn_add_right, hneg, sub_eq_add_neg]

/-- Positivity of the descended inner product — this is
exactly H-pos(1)ʳ read on classes; the hypothesis is
consumed, not discharged. -/
theorem sliceQuotientInnerFn_re_nonneg (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (x : sliceQuotient μG ρ hN2 hρcont hN β hpos) :
    0 ≤ (sliceQuotientInnerFn μG ρ hN2 hρcont hN β hpos x x).re := by
  refine Submodule.Quotient.induction_on _ x ?_
  intro a
  rw [sliceQuotientInnerFn_mk]
  exact hpos a.1 a.2

/-- Definiteness of the descended inner product: a class with
vanishing self-pairing is zero — its representative lies in
the null submodule by definition. -/
theorem sliceQuotientInnerFn_self_eq_zero (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (x : sliceQuotient μG ρ hN2 hρcont hN β hpos) :
    sliceQuotientInnerFn μG ρ hN2 hρcont hN β hpos x x = 0
      → x = 0 := by
  refine Submodule.Quotient.induction_on _ x ?_
  intro a h
  rw [sliceQuotientInnerFn_mk] at h
  have hmem : a ∈ sliceNullSubmodule μG ρ hN2 hρcont hN β hpos :=
    (mem_sliceNullSubmodule μG ρ a).mpr h
  rw [Submodule.Quotient.mk_eq_zero]
  exact hmem

/-- **Equality of classes is detected by pairings:** if two
classes pair identically against every class, they are equal
(definiteness applied to the difference). This is the workhorse
for descending the operator in §3 without ever choosing
representatives of differences. -/
theorem sliceQuotientInnerFn_eq_of_forall_eq (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    {x y : sliceQuotient μG ρ hN2 hρcont hN β hpos}
    (h : ∀ z : sliceQuotient μG ρ hN2 hρcont hN β hpos,
      sliceQuotientInnerFn μG ρ hN2 hρcont hN β hpos z x
        = sliceQuotientInnerFn μG ρ hN2 hρcont hN β hpos z y) :
    x = y := by
  have hself : sliceQuotientInnerFn μG ρ hN2 hρcont hN β hpos
      (x - y) (x - y) = 0 := by
    have hxy := h (x - y)
    have hsub := sliceQuotientInnerFn_sub_right μG ρ hN2 hρcont hN
      β hpos (x - y) x y
    rw [hsub, hxy, sub_self]
  have hzero := sliceQuotientInnerFn_self_eq_zero μG ρ hN2 hρcont
    hN β hpos (x - y) hself
  exact eq_of_sub_eq_zero hzero

/-! ## §2b. The inner-product-space instance stack -/

/-- The descended inner product as the `Inner` instance of
the engine space. (Parameterized by the gate data, like every
hypothesis-dependent instance: all parameters are read off
the type.) -/
noncomputable instance sliceQuotientInnerInst (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) :
    Inner ℂ (sliceQuotient μG ρ hN2 hρcont hN β hpos) :=
  ⟨sliceQuotientInnerFn μG ρ hN2 hρcont hN β hpos⟩

/-- The descended inner product as an `InnerProductSpace.Core`:
positivity is H-pos(1)ʳ on classes (consumed), definiteness
is the null-submodule definition. -/
noncomputable instance sliceQuotientCore (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) :
    InnerProductSpace.Core ℂ
      (sliceQuotient μG ρ hN2 hρcont hN β hpos) where
  inner := sliceQuotientInnerFn μG ρ hN2 hρcont hN β hpos
  conj_inner_symm :=
    sliceQuotientInnerFn_conj_symm μG ρ hN2 hρcont hN β hpos
  re_inner_nonneg :=
    sliceQuotientInnerFn_re_nonneg μG ρ hN2 hρcont hN β hpos
  add_left :=
    sliceQuotientInnerFn_add_left μG ρ hN2 hρcont hN β hpos
  smul_left := fun x y r =>
    sliceQuotientInnerFn_smul_left μG ρ hN2 hρcont hN β hpos r x y
  definite :=
    sliceQuotientInnerFn_self_eq_zero μG ρ hN2 hρcont hN β hpos

/-- The normed-group structure of the engine space, from
the Core (the norm is the square root of the self-pairing;
definiteness is the Core's, so this is a genuine norm, not
a seminorm). -/
noncomputable instance sliceQuotientNormedAddCommGroup
    (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) :
    NormedAddCommGroup
      (sliceQuotient μG ρ hN2 hρcont hN β hpos) :=
  InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)

/-- The normed-space structure of the engine space, from
the Core. -/
noncomputable instance sliceQuotientNormedSpace (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) :
    NormedSpace ℂ (sliceQuotient μG ρ hN2 hρcont hN β hpos) :=
  InnerProductSpace.Core.toNormedSpace (𝕜 := ℂ)

/-- **The engine space is a pre-Hilbert space:** the quotient
`𝔸_slice ⧸ null` with the descended `Π₁` is an
`InnerProductSpace ℂ` — under the single hypothesis
`SliceHPosOne`, which is consumed here and never discharged.
No completion is taken. -/
noncomputable instance sliceQuotientInnerProductSpace
    (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) :
    InnerProductSpace ℂ
      (sliceQuotient μG ρ hN2 hρcont hN β hpos) where
  toNormedSpace :=
    sliceQuotientNormedSpace μG ρ hN2 hρcont hN β hpos
  toInner :=
    sliceQuotientInnerInst μG ρ hN2 hρcont hN β hpos
  norm_sq_eq_re_inner := by
    intro x
    have h₁ : ‖x‖ = Real.sqrt ((inner ℂ x x).re) :=
      InnerProductSpace.Core.norm_eq_sqrt_re_inner x
    have hnn : 0 ≤ RCLike.re (inner ℂ x x) :=
      sliceQuotientInnerFn_re_nonneg μG ρ hN2 hρcont hN β hpos x
    rw [h₁]
    exact Real.sq_sqrt hnn
  conj_inner_symm :=
    sliceQuotientInnerFn_conj_symm μG ρ hN2 hρcont hN β hpos
  add_left :=
    sliceQuotientInnerFn_add_left μG ρ hN2 hρcont hN β hpos
  smul_left := fun x y r =>
    sliceQuotientInnerFn_smul_left μG ρ hN2 hρcont hN β hpos r x y

/-- The norm on a class is the square root of its
self-pairing (the Core norm, unfolded). -/
theorem sliceQuotient_norm_eq (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (x : sliceQuotient μG ρ hN2 hρcont hN β hpos) :
    ‖x‖ = Real.sqrt ((inner ℂ x x).re) :=
  InnerProductSpace.Core.norm_eq_sqrt_re_inner x

/-- The squared norm on a class is its self-pairing's real
part. -/
theorem sliceQuotient_norm_sq (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (x : sliceQuotient μG ρ hN2 hρcont hN β hpos) :
    ‖x‖ ^ 2 = (inner ℂ x x).re := by
  have hnn : 0 ≤ (inner ℂ x x).re :=
    sliceQuotientInnerFn_re_nonneg μG ρ hN2 hρcont hN β hpos x
  rw [sliceQuotient_norm_eq μG ρ hN2 hρcont hN β hpos x,
    Real.sq_sqrt hnn]

/-- The class inner product (`inner ℂ` of the instance) on
representatives is `Π₁`. -/
theorem sliceQuotient_inner_mk (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (a b : ↥(sliceObsSubmodule (N := N) μG ρ β)) :
    inner ℂ (sliceMk μG ρ hN2 hρcont hN β hpos a)
        (sliceMk μG ρ hN2 hρcont hN β hpos b)
      = slicePairOneObs μG ρ hN2 hρcont β a b :=
  sliceQuotientInnerFn_mk μG ρ hN2 hρcont hN β hpos a b

/-- Equality of classes is detected by the class inner
product (the `inner ℂ` form of
`sliceQuotientInnerFn_eq_of_forall_eq`). -/
theorem sliceQuotient_inner_eq_of_forall_eq (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    {x y : sliceQuotient μG ρ hN2 hρcont hN β hpos}
    (h : ∀ z : sliceQuotient μG ρ hN2 hρcont hN β hpos,
      inner ℂ z x = inner ℂ z y) :
    x = y :=
  sliceQuotientInnerFn_eq_of_forall_eq μG ρ hN2 hρcont hN β hpos h

/-! ## §3. The step observable and the descended operator `T̂` -/

/-- **The step observable:** the observable whose slice state
is one transfer step of `a`'s slice state. It exists because
`sliceState` is definitionally `MemLp.toLp`: the stepped
vector's own coefficient function, read back through
`MemLp.toLp_coeFn`, is the step. -/
noncomputable def sliceStepObs (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g) (β : ℝ)
    (a : ↥(sliceObsSubmodule (N := N) μG ρ β)) :
    ↥(sliceObsSubmodule (N := N) μG ρ β) :=
  ⟨⇑(transferOp μG ρ hN2 hρcont β (sliceState μG ρ β a.1 a.2)),
    MeasureTheory.Lp.memLp _⟩

/-- The slice state of the step observable is the step of
the slice state (its defining property). -/
theorem sliceState_sliceStepObs (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g) (β : ℝ)
    (a : ↥(sliceObsSubmodule (N := N) μG ρ β)) :
    sliceState μG ρ β
        (sliceStepObs μG ρ hN2 hρcont β a).1
        (sliceStepObs μG ρ hN2 hρcont β a).2
      = transferOp μG ρ hN2 hρcont β (sliceState μG ρ β a.1
        a.2) :=
  Lp.toLp_coeFn _ _

/-- **The pairing characterization of the step:**
`Π₁(χ, step φ) = Π₂(χ, φ)` — one pairing step against the
stepped observable is the two-step pairing. This is the
identity the descended operator is built to satisfy. -/
theorem slicePairOneObs_step (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g) (β : ℝ)
    (a b : ↥(sliceObsSubmodule (N := N) μG ρ β)) :
    slicePairOneObs μG ρ hN2 hρcont β b
        (sliceStepObs μG ρ hN2 hρcont β a)
      = slicePairTwoObs μG ρ hN2 hρcont β b a := by
  have e : slicePairOne μG ρ hN2 hρcont β b.1 b.2
        (sliceStepObs μG ρ hN2 hρcont β a).1
        (sliceStepObs μG ρ hN2 hρcont β a).2
      = inner ℂ (sliceState μG ρ β b.1 b.2)
          (transferOp μG ρ hN2 hρcont β
            (transferOp μG ρ hN2 hρcont β
              (sliceState μG ρ β a.1 a.2))) := by
    show inner ℂ (sliceState μG ρ β b.1 b.2)
        (transferOp μG ρ hN2 hρcont β
          (sliceState μG ρ β
            (sliceStepObs μG ρ hN2 hρcont β a).1
            (sliceStepObs μG ρ hN2 hρcont β a).2)) = _
    rw [sliceState_sliceStepObs μG ρ hN2 hρcont β a]
  exact e

/-- **The step descends to classes:** if `a - a'` is
`Π₁`-null, the step classes agree. Proved by pairings:
against every `χ`, both sides pair to `Π₂(χ, ·)`, which is
invariant under null additions in the second slot by 2b's
descent (`slicePairTwo_add_right_of_null`); definiteness
then identifies the classes. No representative of a
difference of stepped observables is ever chosen. -/
theorem sliceStepObs_mk_congr (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    {a a' : ↥(sliceObsSubmodule (N := N) μG ρ β)}
    (h : a - a' ∈ sliceNullSubmodule μG ρ hN2 hρcont hN β
      hpos) :
    sliceMk μG ρ hN2 hρcont hN β hpos
        (sliceStepObs μG ρ hN2 hρcont β a)
      = sliceMk μG ρ hN2 hρcont hN β hpos
        (sliceStepObs μG ρ hN2 hρcont β a') := by
  have hnull : slicePairOneObs μG ρ hN2 hρcont β (a - a')
      (a - a') = 0 :=
    (mem_sliceNullSubmodule μG ρ (a - a')).mp h
  have hnull' : slicePairOne μG ρ hN2 hρcont β (a.1 - a'.1)
      (a - a').2 (a.1 - a'.1) (a - a').2 = 0 := hnull
  apply sliceQuotient_inner_eq_of_forall_eq μG ρ hN2 hρcont hN
    β hpos
  intro z
  refine Submodule.Quotient.induction_on _ z ?_
  intro c
  rw [sliceQuotient_inner_mk, sliceQuotient_inner_mk,
    slicePairOneObs_step, slicePairOneObs_step]
  have e := slicePairTwo_add_right_of_null μG ρ hN2 hρcont hN
    β hpos c.1 a'.1 (a.1 - a'.1) c.2 a'.2 (a - a').2 hnull'
  have e' : slicePairTwo μG ρ hN2 hρcont β c.1 c.2 a.1 a.2
      = slicePairTwo μG ρ hN2 hρcont β c.1 c.2
          (a'.1 + (a.1 - a'.1)) (a'.2.add (a - a').2) :=
    slicePairTwo_congr_right μG ρ hN2 hρcont β c.1 c.2
      (add_sub_cancel a'.1 a.1).symm a.2 (a'.2.add (a - a').2)
  exact e'.trans e

/-- The descended operator, as a function on classes:
`[φ] ↦ [step φ]`. -/
noncomputable def sliceHatFun (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) :
    sliceQuotient μG ρ hN2 hρcont hN β hpos →
    sliceQuotient μG ρ hN2 hρcont hN β hpos :=
  Quotient.lift
    (fun a => sliceMk μG ρ hN2 hρcont hN β hpos
      (sliceStepObs μG ρ hN2 hρcont β a))
    (fun a a' h => sliceStepObs_mk_congr μG ρ hN2 hρcont hN β
      hpos ((Submodule.quotientRel_def (p :=
        sliceNullSubmodule μG ρ hN2 hρcont hN β hpos)).mp h))

/-- The descended operator on a class is the class of the
step. -/
theorem sliceHatFun_mk (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (a : ↥(sliceObsSubmodule (N := N) μG ρ β)) :
    sliceHatFun μG ρ hN2 hρcont hN β hpos
        (sliceMk μG ρ hN2 hρcont hN β hpos a)
      = sliceMk μG ρ hN2 hρcont hN β hpos
        (sliceStepObs μG ρ hN2 hρcont β a) :=
  rfl

/-- **The pairing characterization of the descended
operator:** `⟪[χ], T̂[φ]⟫ = Π₂(χ, φ)` on representatives. -/
theorem sliceHatFun_pairing (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (a b : ↥(sliceObsSubmodule (N := N) μG ρ β)) :
    inner ℂ (sliceMk μG ρ hN2 hρcont hN β hpos b)
        (sliceHatFun μG ρ hN2 hρcont hN β hpos
          (sliceMk μG ρ hN2 hρcont hN β hpos a))
      = slicePairTwoObs μG ρ hN2 hρcont β b a := by
  rw [sliceHatFun_mk, sliceQuotient_inner_mk]
  exact slicePairOneObs_step μG ρ hN2 hρcont β a b

/-- The descended operator is additive (by pairings: both
sides pair against every class to the same `Π₂` value, by
2a's additivity of `Π₂` in the second slot). -/
theorem sliceHatFun_add (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (x y : sliceQuotient μG ρ hN2 hρcont hN β hpos) :
    sliceHatFun μG ρ hN2 hρcont hN β hpos (x + y)
      = sliceHatFun μG ρ hN2 hρcont hN β hpos x
        + sliceHatFun μG ρ hN2 hρcont hN β hpos y := by
  refine Submodule.Quotient.induction_on _ x ?_
  intro a
  refine Submodule.Quotient.induction_on _ y ?_
  intro b
  apply sliceQuotient_inner_eq_of_forall_eq μG ρ hN2 hρcont hN
    β hpos
  intro z
  refine Submodule.Quotient.induction_on _ z ?_
  intro c
  rw [← sliceMk_add, sliceHatFun_mk, sliceHatFun_mk,
    sliceHatFun_mk, inner_add_right, sliceQuotient_inner_mk,
    sliceQuotient_inner_mk, sliceQuotient_inner_mk,
    slicePairOneObs_step, slicePairOneObs_step,
    slicePairOneObs_step]
  exact slicePairTwo_add_right μG ρ hN2 hρcont β c.1 a.1 b.1
    c.2 a.2 b.2

/-- The descended operator is homogeneous (by pairings,
through 2a's homogeneity of `Π₂` in the second slot). -/
theorem sliceHatFun_smul (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (c : ℂ)
    (x : sliceQuotient μG ρ hN2 hρcont hN β hpos) :
    sliceHatFun μG ρ hN2 hρcont hN β hpos (c • x)
      = c • sliceHatFun μG ρ hN2 hρcont hN β hpos x := by
  refine Submodule.Quotient.induction_on _ x ?_
  intro a
  apply sliceQuotient_inner_eq_of_forall_eq μG ρ hN2 hρcont hN
    β hpos
  intro z
  refine Submodule.Quotient.induction_on _ z ?_
  intro b
  rw [← sliceMk_smul, sliceHatFun_mk, sliceHatFun_mk,
    inner_smul_right, sliceQuotient_inner_mk,
    sliceQuotient_inner_mk, slicePairOneObs_step,
    slicePairOneObs_step]
  exact slicePairTwo_smul_right μG ρ hN2 hρcont β c b.1 a.1 b.2
    a.2

/-- **The descended transfer operator `T̂`** on the engine
space: the linear map `[φ] ↦ [step φ]`. -/
noncomputable def sliceHat (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) :
    sliceQuotient μG ρ hN2 hρcont hN β hpos →ₗ[ℂ]
    sliceQuotient μG ρ hN2 hρcont hN β hpos where
  toFun := sliceHatFun μG ρ hN2 hρcont hN β hpos
  map_add' := sliceHatFun_add μG ρ hN2 hρcont hN β hpos
  map_smul' := sliceHatFun_smul μG ρ hN2 hρcont hN β hpos

/-- `T̂` on a class is the class of the step. -/
theorem sliceHat_apply_mk (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (a : ↥(sliceObsSubmodule (N := N) μG ρ β)) :
    sliceHat μG ρ hN2 hρcont hN β hpos
        (sliceMk μG ρ hN2 hρcont hN β hpos a)
      = sliceMk μG ρ hN2 hρcont hN β hpos
        (sliceStepObs μG ρ hN2 hρcont β a) :=
  sliceHatFun_mk μG ρ hN2 hρcont hN β hpos a

/-- **The pairing characterization of `T̂`:**
`⟪[χ], T̂[φ]⟫ = Π₂(χ, φ)` — the gate's T2.1ʳ headline, in
the descended factored form of 2a/2b. -/
theorem sliceHat_pairing (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (a b : ↥(sliceObsSubmodule (N := N) μG ρ β)) :
    inner ℂ (sliceMk μG ρ hN2 hρcont hN β hpos b)
        (sliceHat μG ρ hN2 hρcont hN β hpos
          (sliceMk μG ρ hN2 hρcont hN β hpos a))
      = slicePairTwoObs μG ρ hN2 hρcont β b a :=
  sliceHatFun_pairing μG ρ hN2 hρcont hN β hpos a b

/-- **Uniqueness of `T̂`:** any linear operator on the
engine space satisfying the pairing characterization is
`T̂` (pairings detect equality of classes). -/
theorem sliceHat_unique (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (S : sliceQuotient μG ρ hN2 hρcont hN β hpos →ₗ[ℂ]
      sliceQuotient μG ρ hN2 hρcont hN β hpos)
    (hS : ∀ a b : ↥(sliceObsSubmodule (N := N) μG ρ β),
      inner ℂ (sliceMk μG ρ hN2 hρcont hN β hpos b)
          (S (sliceMk μG ρ hN2 hρcont hN β hpos a))
        = slicePairTwoObs μG ρ hN2 hρcont β b a) :
    S = sliceHat μG ρ hN2 hρcont hN β hpos := by
  apply LinearMap.ext
  intro x
  apply sliceQuotient_inner_eq_of_forall_eq μG ρ hN2 hρcont hN
    β hpos
  intro z
  refine Submodule.Quotient.induction_on _ z ?_
  intro c
  refine Submodule.Quotient.induction_on _ x ?_
  intro a
  rw [hS a c, sliceHat_pairing]

/-- **`T̂` is self-adjoint** (as a symmetric operator on the
pre-Hilbert space; no adjoint existence is claimed or
needed): `⟪T̂x, y⟫ = ⟪x, T̂y⟫`. From the pairing
characterization and 2b's descended Hermitian symmetry of
`Π₂`. -/
theorem sliceHat_isSymmetric (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) :
    LinearMap.IsSymmetric
      (sliceHat μG ρ hN2 hρcont hN β hpos) := by
  intro x y
  refine Submodule.Quotient.induction_on _ x ?_
  intro a
  refine Submodule.Quotient.induction_on _ y ?_
  intro b
  rw [sliceHat_apply_mk, sliceHat_apply_mk,
    sliceQuotient_inner_mk, sliceQuotient_inner_mk,
    slicePairOneObs_step μG ρ hN2 hρcont β b a]
  have e1 : slicePairOneObs μG ρ hN2 hρcont β
        (sliceStepObs μG ρ hN2 hρcont β a) b
      = (starRingEnd ℂ) (slicePairTwoObs μG ρ hN2 hρcont β
        b a) := by
    have h1 : slicePairOne μG ρ hN2 hρcont β
          (sliceStepObs μG ρ hN2 hρcont β a).1
          (sliceStepObs μG ρ hN2 hρcont β a).2 b.1 b.2
        = (starRingEnd ℂ) (slicePairOne μG ρ hN2 hρcont β
            b.1 b.2 (sliceStepObs μG ρ hN2 hρcont β a).1
            (sliceStepObs μG ρ hN2 hρcont β a).2) :=
      slicePairOne_conj_symm μG ρ hN2 hρcont hN β _ _ _ _
    have h2 := slicePairOneObs_step μG ρ hN2 hρcont β a b
    exact h1.trans (congrArg (starRingEnd ℂ) h2)
  exact e1.trans
    (slicePairTwo_conj_symm_descended μG ρ hN2 hρcont hN β
      a.1 b.1 a.2 b.2).symm

/-- **`T̂ ≥ 0` in factored form only:** for every class `x`,
`0 ≤ ⟪x, T̂ x⟫.re`. The content is 2b's
`sliceHPosTwo_proved`: `Π₂`'s diagonal is a norm square by
construction (`Π₂(φ, φ) = ‖transferOp (sliceState φ)‖²`
through the stepped identity). **This is positivity of the
factored two-step pairing — it is NOT positivity of the OS
form, and it is not an input to, or a discharge of,
Stage 1b-B.** -/
theorem sliceHat_inner_nonneg (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (x : sliceQuotient μG ρ hN2 hρcont hN β hpos) :
    0 ≤ (inner ℂ x
      (sliceHat μG ρ hN2 hρcont hN β hpos x)).re := by
  refine Submodule.Quotient.induction_on _ x ?_
  intro a
  rw [sliceHat_apply_mk, sliceQuotient_inner_mk,
    slicePairOneObs_step]
  exact sliceHPosTwo_proved μG ρ hN2 hρcont hN β a.1 a.2

/-- **The operator bound, squared form:** `‖T̂x‖² ≤ ‖x‖²`.
The chain is 2b's, read on classes: the stepped form's real
part is at most the stepped vector's norm square (2b's
`inner_transferOp_step_le`), which is `Π₂`'s diagonal
(2b's `inner_transferOp_iter_eq`), which is dominated by
`Π₁`'s diagonal (2b's diagonal domination
`slicePairTwo_self_re_le`). -/
theorem sliceHat_norm_sq_le (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (x : sliceQuotient μG ρ hN2 hρcont hN β hpos) :
    ‖sliceHat μG ρ hN2 hρcont hN β hpos x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
  refine Submodule.Quotient.induction_on _ x ?_
  intro a
  rw [sliceHat_apply_mk, sliceQuotient_norm_sq,
    sliceQuotient_norm_sq, sliceQuotient_inner_mk,
    sliceQuotient_inner_mk]
  have hA : (slicePairOneObs μG ρ hN2 hρcont β
        (sliceStepObs μG ρ hN2 hρcont β a)
        (sliceStepObs μG ρ hN2 hρcont β a)).re
      = (inner ℂ
          (transferOp μG ρ hN2 hρcont β
            (sliceState μG ρ β a.1 a.2))
          (transferOp μG ρ hN2 hρcont β
            (transferOp μG ρ hN2 hρcont β
              (sliceState μG ρ β a.1 a.2)))).re := by
    show (inner ℂ
        (sliceState μG ρ β
          (sliceStepObs μG ρ hN2 hρcont β a).1
          (sliceStepObs μG ρ hN2 hρcont β a).2)
        (transferOp μG ρ hN2 hρcont β
          (sliceState μG ρ β
            (sliceStepObs μG ρ hN2 hρcont β a).1
            (sliceStepObs μG ρ hN2 hρcont β a).2))).re = _
    rw [sliceState_sliceStepObs μG ρ hN2 hρcont β a]
  have hB := inner_transferOp_step_le μG ρ hN2 hρcont hN β
    hpos (sliceState μG ρ β a.1 a.2)
  have hC : ‖transferOp μG ρ hN2 hρcont β
        (sliceState μG ρ β a.1 a.2)‖ ^ 2
      = (slicePairTwoObs μG ρ hN2 hρcont β a a).re := by
    have e := inner_transferOp_iter_eq μG ρ hN2 hρcont hN β
      (sliceState μG ρ β a.1 a.2)
    show ‖transferOp μG ρ hN2 hρcont β
          (sliceState μG ρ β a.1 a.2)‖ ^ 2
        = (slicePairTwo μG ρ hN2 hρcont β a.1 a.2 a.1 a.2).re
    rw [show slicePairTwo μG ρ hN2 hρcont β a.1 a.2 a.1 a.2
        = ((‖transferOp μG ρ hN2 hρcont β
            (sliceState μG ρ β a.1 a.2)‖ ^ 2 : ℝ) : ℂ) from e,
      Complex.ofReal_re]
  have hD := slicePairTwo_self_re_le μG ρ hN2 hρcont hN β
    hpos a.1 a.2
  calc (slicePairOneObs μG ρ hN2 hρcont β
        (sliceStepObs μG ρ hN2 hρcont β a)
        (sliceStepObs μG ρ hN2 hρcont β a)).re
      = (inner ℂ
          (transferOp μG ρ hN2 hρcont β
            (sliceState μG ρ β a.1 a.2))
          (transferOp μG ρ hN2 hρcont β
            (transferOp μG ρ hN2 hρcont β
              (sliceState μG ρ β a.1 a.2)))).re := hA
    _ ≤ ‖transferOp μG ρ hN2 hρcont β
          (sliceState μG ρ β a.1 a.2)‖ ^ 2 := hB
    _ = (slicePairTwoObs μG ρ hN2 hρcont β a a).re := hC
    _ ≤ (slicePairOneObs μG ρ hN2 hρcont β a a).re := hD

/-- **The operator bound:** `‖T̂x‖ ≤ ‖x‖` — the descended
operator is a contraction (operator norm `≤ 1`), at every
real `β`, under H-pos(1)ʳ. -/
theorem sliceHat_norm_le (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (x : sliceQuotient μG ρ hN2 hρcont hN β hpos) :
    ‖sliceHat μG ρ hN2 hρcont hN β hpos x‖ ≤ ‖x‖ :=
  le_of_pow_le_pow_left₀ (by norm_num) (norm_nonneg x)
    (sliceHat_norm_sq_le μG ρ hN2 hρcont hN β hpos x)

/-- **`T̂` as a continuous linear map** (operator norm
`≤ 1`): the descended transfer operator is a bounded
self-adjoint contraction on the pre-Hilbert engine space,
under the single hypothesis `SliceHPosOne`. -/
noncomputable def sliceHatCLM (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) :=
  LinearMap.mkContinuous (sliceHat μG ρ hN2 hρcont hN β hpos)
    1 (fun x => by
      have h := sliceHat_norm_le μG ρ hN2 hρcont hN β hpos x
      simpa using h)

/-- The continuous linear map `T̂` applies as the linear
map `T̂`. -/
theorem sliceHatCLM_apply (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (x : sliceQuotient μG ρ hN2 hρcont hN β hpos) :
    sliceHatCLM μG ρ hN2 hρcont hN β hpos x
      = sliceHat μG ρ hN2 hρcont hN β hpos x :=
  rfl

/-! ## §4. The vacuum -/

/-- The constant-one observable is `L²` against the slice
measure (bounded by `1`, and the slice measure is a
probability). -/
theorem memLp_one_slice (β : ℝ) (hd : 0 < d)
    (hρcont : Continuous fun g : G => repMatrix ρ g) :
    MemLp (1 : ((↥(sliceLinks (N := N)) → G) → ℂ)) 2
      (sliceMeasure (N := N) μG ρ β) := by
  apply memLp_of_bounded μG ρ hρcont hd β
    (1 : ((↥(sliceLinks (N := N)) → G) → ℂ))
    measurable_const.aestronglyMeasurable (1 : ℝ)
  intro z
  simp

/-- **The vacuum representative:** the constant-one
observable. -/
def sliceOneObs (β : ℝ) (hd : 0 < d)
    (hρcont : Continuous fun g : G => repMatrix ρ g) :
    ↥(sliceObsSubmodule (N := N) μG ρ β) :=
  ⟨1, memLp_one_slice μG ρ β hd hρcont⟩

/-- **The vacuum class** `Ω = [1]` in the engine space. -/
noncomputable def sliceOmega (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (hd : 0 < d) :
    sliceQuotient μG ρ hN2 hρcont hN β hpos :=
  sliceMk μG ρ hN2 hρcont hN β hpos
    (sliceOneObs μG ρ β hd hρcont)

/-- The vacuum's self-pairing is `1`:
`Π₁(1, 1) = ⟪Ω₀, T Ω₀⟫ = ⟪Ω₀, Ω₀⟫ = ‖Ω₀‖² = 1` (the slice
state of `1` is the OS vacuum, which the transfer operator
fixes — the landed `sliceState_one_eq_osVacuum` and
`transferOp_vacuum`). -/
theorem slicePairOneObs_one_one (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g) (β : ℝ)
    (hd : 0 < d) :
    slicePairOneObs μG ρ hN2 hρcont β
        (sliceOneObs μG ρ β hd hρcont)
        (sliceOneObs μG ρ β hd hρcont) = 1 := by
  show inner ℂ
      (sliceState μG ρ β 1 (memLp_one_slice μG ρ β hd hρcont))
      (transferOp μG ρ hN2 hρcont β
        (sliceState μG ρ β 1
          (memLp_one_slice μG ρ β hd hρcont))) = 1
  rw [sliceState_one_eq_osVacuum μG ρ hρcont hd β
      (memLp_one_slice μG ρ β hd hρcont),
    transferOp_vacuum μG ρ hN2 hρcont hd β,
    inner_self_eq_norm_sq_to_K, norm_osVacuum]
  simp

/-- **The vacuum is a unit vector:** `‖Ω‖ = 1`. -/
theorem sliceOmega_norm (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (hd : 0 < d) :
    ‖sliceOmega μG ρ hN2 hρcont hN β hpos hd‖ = 1 := by
  show ‖sliceMk μG ρ hN2 hρcont hN β hpos
      (sliceOneObs μG ρ β hd hρcont)‖ = 1
  rw [sliceQuotient_norm_eq, sliceQuotient_inner_mk,
    slicePairOneObs_one_one μG ρ hN2 hρcont β hd]
  simp

/-- **`T̂ Ω = Ω`:** the vacuum class is fixed by the
descended operator. By pairings: against every `[χ]`,
`⟪[χ], T̂Ω⟫ = Π₂(χ, 1) = Π₁(χ, 1) = ⟪[χ], Ω⟫` — the middle
equality is 2b's `(D-vac)ʳ` (`slicePairTwo_one_right`),
which is where the side condition `0 < d` enters. -/
theorem sliceHat_sliceOmega (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (hd : 0 < d) :
    sliceHat μG ρ hN2 hρcont hN β hpos
        (sliceOmega μG ρ hN2 hρcont hN β hpos hd)
      = sliceOmega μG ρ hN2 hρcont hN β hpos hd := by
  apply sliceQuotient_inner_eq_of_forall_eq μG ρ hN2 hρcont
    hN β hpos
  intro z
  refine Submodule.Quotient.induction_on _ z ?_
  intro c
  show inner ℂ (sliceMk μG ρ hN2 hρcont hN β hpos c)
      (sliceHat μG ρ hN2 hρcont hN β hpos
        (sliceMk μG ρ hN2 hρcont hN β hpos
          (sliceOneObs μG ρ β hd hρcont)))
    = inner ℂ (sliceMk μG ρ hN2 hρcont hN β hpos c)
      (sliceMk μG ρ hN2 hρcont hN β hpos
        (sliceOneObs μG ρ β hd hρcont))
  rw [sliceHat_pairing, sliceQuotient_inner_mk]
  exact slicePairTwo_one_right μG ρ hN2 hρcont hd β c.1 c.2
    (memLp_one_slice μG ρ β hd hρcont)

/-- **Cyclicity, in the gate's stated sense (by
construction):** every class of the engine space is the
class of an observable — the classes exhaust the space, so
in particular the vacuum's fellow classes are all reached
without any completion or closure operation (none is
taken). -/
theorem sliceMk_surjective (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) :
    Function.Surjective
      (sliceMk μG ρ hN2 hρcont hN β hpos) := by
  intro x
  refine Submodule.Quotient.induction_on _ x ?_
  intro a
  exact ⟨a, rfl⟩

/-! ## §5. The engine package -/

/-- **★ THE CONDITIONAL SLICE GNS ENGINE (S2-2c package).**

Under the single explicit hypothesis `SliceHPosOne`
(H-pos(1)ʳ) — together with the standing gate data
`2 ≤ N`, continuity of `ρ`'s matrices, even `N`, at every
real `β` and general `(G, ρ)`; the side condition `0 < d`
enters only through the vacuum clauses, exactly as in 2b's
landed `(D-vac)ʳ` interface — the following hold:

1. **The space.** The quotient `ℋ = 𝔸_slice ⧸ null` (with
`null` the `Π₁`-null submodule, which is the radical of
`Π₁`) carries the descended inner product: on classes it is
`Π₁` on representatives; it is positive (this is
H-pos(1)ʳ itself, consumed) and definite.
2. **The operator.** `T̂` is the unique linear operator on
`ℋ` with `⟪[χ], T̂[φ]⟫ = Π₂(χ, φ)` on representatives; it
is self-adjoint; it satisfies `0 ≤ ⟪x, T̂x⟫.re`
(**factored-form positivity only** — `Π₂`'s diagonal is a
norm square by construction; this is not OS-form
positivity); and it is a contraction, `‖T̂x‖ ≤ ‖x‖`,
realized by the continuous linear map `sliceHatCLM`.
3. **The vacuum.** `Ω = [1]` is a unit vector and
`T̂ Ω = Ω`.
4. **Cyclicity (gate's sense, by construction).** The
class map is surjective: every class is `[φ]` for an
observable `φ`.

**Fences, restated on the package itself.** `SliceHPosOne`
is a hypothesis of this theorem, not a conclusion: nothing
here discharges H-pos(1)ʳ, and **this package is not a
discharge of Stage 1b-B positivity** — no clause asserts
positivity of the OS form on any algebra. `T̂ ≥ 0` appears
only as the factored-form clause 2 above. The unlanded
depth-two identification of R3's two-point operator with
`transferOp^2` is not used; `Π₂` appears only in its
landed factored form. NO CLAIM; Clay parts closed: 0.

**Where the discharge plugs in.** Brick S2-3's re-aimed
Route-C clause `(R-C2)ʳ` is exactly a proof of
`SliceHPosOne` at the seats it covers; feeding such a proof
as `hpos` instantiates this package unconditionally there.
Brick S2-2d regresses this package at `β = 0` against
S2-1's landed `recon_zero_slice_package`. -/
theorem sliceEngine_package (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (hd : 0 < d) :
    (∀ a b : ↥(sliceObsSubmodule (N := N) μG ρ β),
      inner ℂ (sliceMk μG ρ hN2 hρcont hN β hpos a)
          (sliceMk μG ρ hN2 hρcont hN β hpos b)
        = slicePairOneObs μG ρ hN2 hρcont β a b)
    ∧ (∀ x : sliceQuotient μG ρ hN2 hρcont hN β hpos,
        0 ≤ (inner ℂ x x).re)
    ∧ (∀ x : sliceQuotient μG ρ hN2 hρcont hN β hpos,
        inner ℂ x x = 0 → x = 0)
    ∧ (∀ a : ↥(sliceObsSubmodule (N := N) μG ρ β),
        (a ∈ sliceNullSubmodule μG ρ hN2 hρcont hN β hpos)
          ↔ ∀ b : ↥(sliceObsSubmodule (N := N) μG ρ β),
              slicePairOneObs μG ρ hN2 hρcont β a b = 0)
    ∧ (∀ a b : ↥(sliceObsSubmodule (N := N) μG ρ β),
        inner ℂ (sliceMk μG ρ hN2 hρcont hN β hpos b)
            (sliceHat μG ρ hN2 hρcont hN β hpos
              (sliceMk μG ρ hN2 hρcont hN β hpos a))
          = slicePairTwoObs μG ρ hN2 hρcont β b a)
    ∧ (∀ S : sliceQuotient μG ρ hN2 hρcont hN β hpos →ₗ[ℂ]
          sliceQuotient μG ρ hN2 hρcont hN β hpos,
        (∀ a b : ↥(sliceObsSubmodule (N := N) μG ρ β),
          inner ℂ (sliceMk μG ρ hN2 hρcont hN β hpos b)
              (S (sliceMk μG ρ hN2 hρcont hN β hpos a))
            = slicePairTwoObs μG ρ hN2 hρcont β b a)
          → S = sliceHat μG ρ hN2 hρcont hN β hpos)
    ∧ LinearMap.IsSymmetric
        (sliceHat μG ρ hN2 hρcont hN β hpos)
    ∧ (∀ x : sliceQuotient μG ρ hN2 hρcont hN β hpos,
        0 ≤ (inner ℂ x
          (sliceHat μG ρ hN2 hρcont hN β hpos x)).re)
    ∧ (∀ x : sliceQuotient μG ρ hN2 hρcont hN β hpos,
        ‖sliceHat μG ρ hN2 hρcont hN β hpos x‖ ≤ ‖x‖)
    ∧ (∀ x : sliceQuotient μG ρ hN2 hρcont hN β hpos,
        sliceHatCLM μG ρ hN2 hρcont hN β hpos x
          = sliceHat μG ρ hN2 hρcont hN β hpos x)
    ∧ ‖sliceOmega μG ρ hN2 hρcont hN β hpos hd‖ = 1
    ∧ sliceHat μG ρ hN2 hρcont hN β hpos
        (sliceOmega μG ρ hN2 hρcont hN β hpos hd)
      = sliceOmega μG ρ hN2 hρcont hN β hpos hd
    ∧ Function.Surjective
        (sliceMk μG ρ hN2 hρcont hN β hpos) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_⟩
  · exact sliceQuotient_inner_mk μG ρ hN2 hρcont hN β hpos
  · intro x
    exact sliceQuotientInnerFn_re_nonneg μG ρ hN2 hρcont hN
      β hpos x
  · intro x h
    exact sliceQuotientInnerFn_self_eq_zero μG ρ hN2 hρcont
      hN β hpos x h
  · intro a
    constructor
    · intro ha b
      exact slicePairOneObs_eq_zero_of_self_eq_zero_left
        μG ρ hN2 hρcont hN β hpos
        ((mem_sliceNullSubmodule μG ρ a).mp ha) b
    · intro h
      exact (mem_sliceNullSubmodule μG ρ a).mpr (h a)
  · exact sliceHat_pairing μG ρ hN2 hρcont hN β hpos
  · intro S hS
    exact sliceHat_unique μG ρ hN2 hρcont hN β hpos S hS
  · exact sliceHat_isSymmetric μG ρ hN2 hρcont hN β hpos
  · exact sliceHat_inner_nonneg μG ρ hN2 hρcont hN β hpos
  · exact sliceHat_norm_le μG ρ hN2 hρcont hN β hpos
  · exact sliceHatCLM_apply μG ρ hN2 hρcont hN β hpos
  · exact sliceOmega_norm μG ρ hN2 hρcont hN β hpos hd
  · exact sliceHat_sliceOmega μG ρ hN2 hρcont hN β hpos hd
  · exact sliceMk_surjective μG ρ hN2 hρcont hN β hpos

end SliceEngine

end ThetLogos
