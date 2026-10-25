/-
# FG-2c-1 — THE RESOLVENT FAMILY AT GENERAL `λ > 0`

Brick FG-2c-1 of the FG-2c gate paper
(`whitepaper/stage2-fg2c-gate-2026-10-25.md`, §4–§5): the
resolvent family for the FG-2b Friedrichs Hamiltonian.
PLACEMENT LABEL (consumed from the gate, not re-decided
here): **Stage 2 completeness** work at fixed volume. It
is NOT frontier progress: Items 3 (uniform estimates) and
4 (continuum) are untouched, and nothing here moves any
dial. Dials 0/4. NO CLAIM.

## What this brick consumes

* FG-2a (`LatticeSliceFormClosed`): the completed form
  `sliceHamFormC` is closed — the form domain with the
  `λ = 1` form inner product
  `sliceFormInner x y = ⟪x.val, y.val⟫ + sliceFormB x y`
  is a Hilbert space (`sliceFormDomainCompleteSpace`),
  with the continuous inclusion of bound `1`.
* FG-2b (`LatticeSliceFriedrichs`): the carrier
  `H' := sliceFormClosure`, the resolvent at `λ = 1`
  (`sliceFriedrichsResolventLin`, Riesz via
  `InnerProductSpace.toDual`), and the Hamiltonian
  `sliceHamOperator` on `D(Ĥ) = range R₁`, symmetric,
  positive, with the form identity and `Ĥ + 1`
  surjective onto `H'`. FG-2c-0 (`LatticeSliceCfc`)
  identified the carrier: `H' = (ker T̂_c)ᗮ`; this brick
  does not consume that identification — the family is
  built on `H'` exactly as FG-2b left it.

## The one new lemma (the gate's price)

The gate (§5) priced this brick M: "a replay at a real
price — not verbatim, not new analysis." The Riesz step
is literally FG-2b's, applied to the form Hilbert space
of the shifted form

  `J_λ(u, v) := sliceFormB u v + λ • ⟪u, v⟫`   (`λ > 0`).

The genuinely new content is **completeness transport**:
`J_λ`'s diagonal is `λ‖u‖² + form(u)`, against `J_1`'s
`‖u‖² + form(u)`; both summands are nonnegative, so the
two norms dominate each other with the explicit
constants `√(max 1 λ)` and `√(max 1 λ⁻¹)`, and the form
domain — complete in the `J_1` norm by FG-2a — is
complete in the `J_λ` norm because the identity map is
a uniform equivalence between the two (§1).

## What it delivers

* The `J_λ` form domain as a Hilbert space in its own
  right (§1): a synonym type carrying the `J_λ` inner
  product, with `‖x‖²_λ = λ‖x.val‖² + form(x)`, the
  inclusion bound `‖x.val‖ ≤ √λ⁻¹ ‖x‖_λ`, and
  completeness transported from FG-2a.
* The resolvent `R_λ : H' →L[ℂ] H'` at every `λ > 0`
  (§2): the Riesz representative of `v ↦ ⟪f, v⟫` for
  `J_λ`, satisfying the resolvent equation
  `sliceFormB (R_λ f) v + λ⟪R_λ f, v⟫ = ⟪f, v⟫` on the
  form domain; symmetric; of bound `‖R_λ f‖ ≤ λ⁻¹‖f‖`;
  with nonnegative diagonal pairing
  `0 ≤ (⟪f, R_λ f⟫).re`.
* **Domain independence** (§3): `range R_λ = range R₁`
  as submodules of `H'` — the operator domain of `Ĥ`
  does not depend on `λ` — and the resolvent equation
  in operator form: for `u = R_λ f`,
  `Ĥ u = f − λ • u`, i.e. `(Ĥ + λ) R_λ = id` in the
  Friedrichs sense of FG-2b; consequently `Ĥ + λ` is
  surjective from `D(Ĥ)` onto `H'`.
* Consistency at `λ = 1` (§4): `R_1` agrees with
  FG-2b's `sliceFriedrichsResolventLin` on every input.
* The vacuum (§5): `R_λ Ω = (λ:ℂ)⁻¹ • Ω` (from
  `Ĥ Ω = 0`).
* Packages (§6): general `(G, ρ)` under exactly
  `SliceHPosOne`; the U(1) seat hypothesis-free at
  `β ≥ 0`; at `β = 0`, `R_λ = λ⁻¹ • id`.

## What is named, NOT asserted

* NO resolvent identity
  `R_λ − R_μ = (μ − λ) R_λ R_μ`: deliberately out of
  scope per the gate (§5) — neither semigroup route
  priced in the gate consumes it.
* NO semigroup statement: `exp(−Ĥ) = T̂_c` is FG-2c's
  remaining bricks (CONSTRUCT × IDENTIFY); this brick
  only builds the family those routes consume.
* NO spectral statement about `Ĥ`, no gap, no
  uniformity in `N` or `β`, no continuum object.

NO CLAIM; Clay parts closed: 0.
-/

import ThetLogos.LatticeSliceCfc

namespace ThetLogos

open MeasureTheory Finset
open scoped Matrix ENNReal NNReal InnerProduct

section SliceResolvent

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ))
  {N : ℕ} [NeZero N]

/-! ## §1. The `J_λ` form domain -/

/-- **The form domain at weight `λ`, as a type in its own
right**: the synonym of `sliceHamFormDomainC` that will
carry the `J_λ` inner product
`sliceFormB x y + λ • ⟪x.val, y.val⟫`. (A synonym, not
the subtype itself, for the same reason as FG-2a's
`sliceFormDomain`: structures ascribed over packaged
types pick the wrong topology. The synonym's algebra is
transported from the subtype, and every transport below
is `rfl`.) The weight `λ` and its positivity proof are
carried as parameters — the corpus idiom (compare
`sliceHilbertSpace`'s `hpos`) — so that each weight has
its own type and its own instances, with the proof
inferable from the type by unification. -/
def sliceFormDomainLam (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (lam : ℝ)
    (hlam : 0 < lam) :
    Type _ :=
  ↥(sliceHamFormDomainC μG ρ hN2 hρcont hN β hpos)

/-- The domain element underlying a `λ`-form-domain
point. -/
def sliceFormDomainLam.toSub (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (lam : ℝ)
    (hlam : 0 < lam)
    (x : sliceFormDomainLam μG ρ hN2 hρcont hN β hpos
      lam hlam) :
    ↥(sliceHamFormDomainC μG ρ hN2 hρcont hN β hpos) :=
  x

/-- A domain element, viewed in the `λ`-form domain. -/
def sliceFormDomainLam.ofSub (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (lam : ℝ)
    (hlam : 0 < lam)
    (w : ↥(sliceHamFormDomainC μG ρ hN2 hρcont hN β
      hpos)) :
    sliceFormDomainLam μG ρ hN2 hρcont hN β hpos lam
      hlam :=
  w

/-- The ambient vector of a `λ`-form-domain point. -/
def sliceFormDomainLam.val (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (lam : ℝ)
    (hlam : 0 < lam)
    (x : sliceFormDomainLam μG ρ hN2 hρcont hN β hpos
      lam hlam) :
    sliceHilbertSpace μG ρ hN2 hρcont hN β hpos :=
  (sliceFormDomainLam.toSub μG ρ hN2 hρcont hN β hpos
    lam hlam x).1

noncomputable instance sliceFormDomainLamAddCommGroup
    (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (lam : ℝ)
    (hlam : 0 < lam) :
    AddCommGroup (sliceFormDomainLam μG ρ hN2 hρcont
      hN β hpos lam hlam) :=
  inferInstanceAs (AddCommGroup
    ↥(sliceHamFormDomainC μG ρ hN2 hρcont hN β hpos))

noncomputable instance sliceFormDomainLamModule
    (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (lam : ℝ)
    (hlam : 0 < lam) :
    Module ℂ (sliceFormDomainLam μG ρ hN2 hρcont hN β
      hpos lam hlam) :=
  inferInstanceAs (Module ℂ
    ↥(sliceHamFormDomainC μG ρ hN2 hρcont hN β hpos))

theorem sliceFormDomainLam.toSub_ofSub (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (lam : ℝ)
    (hlam : 0 < lam)
    (w : ↥(sliceHamFormDomainC μG ρ hN2 hρcont hN β
      hpos)) :
    (sliceFormDomainLam.ofSub μG ρ hN2 hρcont hN β hpos
        lam hlam w).toSub = w :=
  rfl

theorem sliceFormDomainLam.ofSub_toSub (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (lam : ℝ)
    (hlam : 0 < lam)
    (x : sliceFormDomainLam μG ρ hN2 hρcont hN β hpos
      lam hlam) :
    sliceFormDomainLam.ofSub μG ρ hN2 hρcont hN β hpos
        lam hlam x.toSub = x :=
  rfl

theorem sliceFormDomainLam.val_ofSub (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (lam : ℝ)
    (hlam : 0 < lam)
    (w : ↥(sliceHamFormDomainC μG ρ hN2 hρcont hN β
      hpos)) :
    (sliceFormDomainLam.ofSub μG ρ hN2 hρcont hN β hpos
        lam hlam w).val = w.1 :=
  rfl

theorem sliceFormDomainLam.val_eq (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (lam : ℝ)
    (hlam : 0 < lam)
    (x : sliceFormDomainLam μG ρ hN2 hρcont hN β hpos
      lam hlam) :
    x.val = x.toSub.1 :=
  rfl

theorem sliceFormDomainLam.toSub_inj (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (lam : ℝ)
    (hlam : 0 < lam)
    {x y : sliceFormDomainLam μG ρ hN2 hρcont hN β hpos
      lam hlam} :
    x.toSub = y.toSub → x = y :=
  fun h => h

theorem sliceFormDomainLam.toSub_zero (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (lam : ℝ)
    (hlam : 0 < lam) :
    (0 : sliceFormDomainLam μG ρ hN2 hρcont hN β hpos
        lam hlam).toSub = 0 :=
  rfl

theorem sliceFormDomainLam.toSub_add (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (lam : ℝ)
    (hlam : 0 < lam)
    (x y : sliceFormDomainLam μG ρ hN2 hρcont hN β hpos
      lam hlam) :
    (x + y).toSub = x.toSub + y.toSub :=
  rfl

theorem sliceFormDomainLam.toSub_sub (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (lam : ℝ)
    (hlam : 0 < lam)
    (x y : sliceFormDomainLam μG ρ hN2 hρcont hN β hpos
      lam hlam) :
    (x - y).toSub = x.toSub - y.toSub :=
  rfl

theorem sliceFormDomainLam.toSub_smul (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (lam : ℝ)
    (hlam : 0 < lam) (c : ℂ)
    (x : sliceFormDomainLam μG ρ hN2 hρcont hN β hpos
      lam hlam) :
    (c • x).toSub = c • x.toSub :=
  rfl

theorem sliceFormDomainLam.val_zero (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (lam : ℝ)
    (hlam : 0 < lam) :
    (0 : sliceFormDomainLam μG ρ hN2 hρcont hN β hpos
        lam hlam).val = 0 :=
  rfl

theorem sliceFormDomainLam.val_add (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (lam : ℝ)
    (hlam : 0 < lam)
    (x y : sliceFormDomainLam μG ρ hN2 hρcont hN β hpos
      lam hlam) :
    (x + y).val = x.val + y.val :=
  rfl

theorem sliceFormDomainLam.val_sub (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (lam : ℝ)
    (hlam : 0 < lam)
    (x y : sliceFormDomainLam μG ρ hN2 hρcont hN β hpos
      lam hlam) :
    (x - y).val = x.val - y.val :=
  rfl

theorem sliceFormDomainLam.val_smul (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (lam : ℝ)
    (hlam : 0 < lam) (c : ℂ)
    (x : sliceFormDomainLam μG ρ hN2 hρcont hN β hpos
      lam hlam) :
    (c • x).val = c • x.val :=
  rfl

/-- **The shifted form** `J_λ` on the domain: the
polarized form plus `λ` times the ambient pairing.
At `λ = 1` it is FG-2a's `sliceFormInner` (with the two
summands in the other order). -/
noncomputable def sliceFormInnerLam (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (lam : ℝ)
    (hlam : 0 < lam)
    (x y : sliceFormDomainLam μG ρ hN2 hρcont hN β hpos
      lam hlam) :
    ℂ :=
  sliceFormB μG ρ hN2 hρcont hN β hpos x.toSub y.toSub
    + (lam : ℂ) * inner ℂ x.val y.val

theorem sliceFormInnerLam_conj_symm (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (lam : ℝ)
    (hlam : 0 < lam)
    (x y : sliceFormDomainLam μG ρ hN2 hρcont hN β hpos
      lam hlam) :
    (starRingEnd ℂ) (sliceFormInnerLam μG ρ hN2 hρcont
        hN β hpos lam hlam y x)
      = sliceFormInnerLam μG ρ hN2 hρcont hN β hpos lam
          hlam x y := by
  unfold sliceFormInnerLam
  rw [map_add, sliceFormB_conj_symm, map_mul,
    inner_conj_symm]
  congr 1
  simp only [Complex.conj_ofReal]

theorem sliceFormInnerLam_add_left (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (lam : ℝ)
    (hlam : 0 < lam)
    (x y z : sliceFormDomainLam μG ρ hN2 hρcont hN β
      hpos lam hlam) :
    sliceFormInnerLam μG ρ hN2 hρcont hN β hpos lam
        hlam (x + y) z
      = sliceFormInnerLam μG ρ hN2 hρcont hN β hpos lam
          hlam x z
        + sliceFormInnerLam μG ρ hN2 hρcont hN β hpos
            lam hlam y z := by
  unfold sliceFormInnerLam
  rw [sliceFormDomainLam.val_add,
    sliceFormDomainLam.toSub_add, inner_add_left,
    sliceFormB_add_left]
  ring

theorem sliceFormInnerLam_smul_left (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (lam : ℝ)
    (hlam : 0 < lam) (c : ℂ)
    (x y : sliceFormDomainLam μG ρ hN2 hρcont hN β hpos
      lam hlam) :
    sliceFormInnerLam μG ρ hN2 hρcont hN β hpos lam
        hlam (c • x) y
      = (starRingEnd ℂ) c * sliceFormInnerLam μG ρ hN2
          hρcont hN β hpos lam hlam x y := by
  unfold sliceFormInnerLam
  rw [sliceFormDomainLam.val_smul,
    sliceFormDomainLam.toSub_smul, inner_smul_left,
    sliceFormB_smul_left]
  ring

/-- The `J_λ` diagonal real part:
`λ‖x‖² + form(x)` — the two nonnegative summands whose
comparison against `J_1`'s diagonal is the completeness
transport. -/
theorem sliceFormInnerLam_self_re (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (lam : ℝ)
    (hlam : 0 < lam)
    (x : sliceFormDomainLam μG ρ hN2 hρcont hN β hpos
      lam hlam) :
    (sliceFormInnerLam μG ρ hN2 hρcont hN β hpos lam
        hlam x x).re
      = lam * ‖x.val‖ ^ 2 + sliceFormVal μG ρ hN2
          hρcont hN β hpos x.val := by
  unfold sliceFormInnerLam
  rw [sliceFormDomainLam.val_eq, Complex.add_re,
    sliceFormB_self, Complex.ofReal_re,
    Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero,
    sliceCompleted_inner_self_re]
  ring

theorem sliceFormInnerLam_re_nonneg (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (lam : ℝ)
    (hlam : 0 < lam)
    (x : sliceFormDomainLam μG ρ hN2 hρcont hN β hpos
      lam hlam) :
    0 ≤ (sliceFormInnerLam μG ρ hN2 hρcont hN β hpos
        lam hlam x x).re := by
  rw [sliceFormInnerLam_self_re]
  exact add_nonneg (mul_nonneg hlam.le (sq_nonneg _))
    (sliceFormVal_nonneg μG ρ hN2 hρcont hN β hpos
      x.val)

theorem sliceFormInnerLam_self_eq_zero (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (lam : ℝ)
    (hlam : 0 < lam)
    (x : sliceFormDomainLam μG ρ hN2 hρcont hN β hpos
      lam hlam) :
    sliceFormInnerLam μG ρ hN2 hρcont hN β hpos lam
        hlam x x = 0
      → x = 0 := by
  intro h
  have hre : (sliceFormInnerLam μG ρ hN2 hρcont hN β
      hpos lam hlam x x).re = 0 := by
    rw [h]
    simp
  rw [sliceFormInnerLam_self_re] at hre
  have h1 : lam * ‖x.val‖ ^ 2 = 0 :=
    (add_eq_zero_iff_of_nonneg
      (mul_nonneg hlam.le (sq_nonneg _))
      (sliceFormVal_nonneg μG ρ hN2 hρcont hN β hpos
        x.val)).mp hre |>.1
  have hsq : ‖x.val‖ ^ 2 = 0 := by
    rcases mul_eq_zero.mp h1 with h2 | h2
    · exact absurd h2 (ne_of_gt hlam)
    · exact h2
  have hval : x.val = 0 :=
    norm_eq_zero.mp (sq_eq_zero_iff.mp hsq)
  have hsub : x.toSub = 0 := Subtype.ext hval
  have h0 : (0 : sliceFormDomainLam μG ρ hN2 hρcont hN
      β hpos lam hlam).toSub = 0 :=
    sliceFormDomainLam.toSub_zero μG ρ hN2 hρcont hN β
      hpos lam hlam
  exact sliceFormDomainLam.toSub_inj μG ρ hN2 hρcont hN
    β hpos lam hlam (by rwa [← h0] at hsub)

/-- **The `J_λ` Core**: the shifted form as an
`InnerProductSpace.Core` on the `λ`-domain synonym.
Definiteness is exactly where `λ > 0` is consumed. -/
noncomputable def sliceFormCoreLam (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (lam : ℝ)
    (hlam : 0 < lam) :
    InnerProductSpace.Core ℂ (sliceFormDomainLam μG ρ
      hN2 hρcont hN β hpos lam hlam) where
  inner := sliceFormInnerLam μG ρ hN2 hρcont hN β hpos
    lam hlam
  conj_inner_symm := sliceFormInnerLam_conj_symm μG ρ
    hN2 hρcont hN β hpos lam hlam
  re_inner_nonneg := sliceFormInnerLam_re_nonneg μG ρ
    hN2 hρcont hN β hpos lam hlam
  add_left := sliceFormInnerLam_add_left μG ρ hN2
    hρcont hN β hpos lam hlam
  smul_left := fun x y r => sliceFormInnerLam_smul_left
    μG ρ hN2 hρcont hN β hpos lam hlam r x y
  definite := sliceFormInnerLam_self_eq_zero μG ρ hN2
    hρcont hN β hpos lam hlam

noncomputable instance sliceFormDomainLamNormedAddCommGroup
    (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (lam : ℝ)
    (hlam : 0 < lam) :
    NormedAddCommGroup (sliceFormDomainLam μG ρ hN2
      hρcont hN β hpos lam hlam) :=
  (sliceFormCoreLam μG ρ hN2 hρcont hN β hpos lam
    hlam).toNormedAddCommGroup

noncomputable instance sliceFormDomainLamInnerProductSpace
    (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (lam : ℝ)
    (hlam : 0 < lam) :
    InnerProductSpace ℂ (sliceFormDomainLam μG ρ hN2
      hρcont hN β hpos lam hlam) :=
  InnerProductSpace.ofCore (sliceFormCoreLam μG ρ hN2
    hρcont hN β hpos lam hlam).toCore

/-- The class inner product of the `λ`-domain is the
`J_λ` shifted form. -/
theorem sliceFormDomainLam_inner_eq (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (lam : ℝ)
    (hlam : 0 < lam)
    (x y : sliceFormDomainLam μG ρ hN2 hρcont hN β hpos
      lam hlam) :
    inner ℂ x y
      = sliceFormInnerLam μG ρ hN2 hρcont hN β hpos lam
          hlam x y :=
  rfl

/-- **The `J_λ` norm, squared**:
`‖x‖²_λ = λ‖x.val‖² + form(x)`. -/
theorem sliceFormDomainLam_norm_sq (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (lam : ℝ)
    (hlam : 0 < lam)
    (x : sliceFormDomainLam μG ρ hN2 hρcont hN β hpos
      lam hlam) :
    ‖x‖ ^ 2 = lam * ‖x.val‖ ^ 2 + sliceFormVal μG ρ
        hN2 hρcont hN β hpos x.val := by
  have h1 : ‖x‖ ^ 2 = (sliceFormInnerLam μG ρ hN2
      hρcont hN β hpos lam hlam x x).re :=
    InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ) x
  rwa [sliceFormInnerLam_self_re] at h1

/-- **The `λ`-inclusion bound**: the ambient norm is
dominated by the `J_λ` norm with constant `√λ⁻¹` —
the continuity input for the pairing functional of
§2. -/
theorem sliceFormDomainLam_val_norm_le (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (lam : ℝ)
    (hlam : 0 < lam)
    (x : sliceFormDomainLam μG ρ hN2 hρcont hN β hpos
      lam hlam) :
    ‖x.val‖ ≤ Real.sqrt lam⁻¹ * ‖x‖ := by
  have hnn : (0 : ℝ) ≤ lam⁻¹ := inv_nonneg.mpr hlam.le
  have hsq : ‖x.val‖ ^ 2
      ≤ (Real.sqrt lam⁻¹ * ‖x‖) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hnn,
      sliceFormDomainLam_norm_sq μG ρ hN2 hρcont hN β
        hpos lam hlam]
    have heq : lam⁻¹ * (lam * ‖x.val‖ ^ 2
        + sliceFormVal μG ρ hN2 hρcont hN β hpos x.val)
        = ‖x.val‖ ^ 2 + lam⁻¹ * sliceFormVal μG ρ hN2
            hρcont hN β hpos x.val := by
      rw [mul_add, ← mul_assoc,
        inv_mul_cancel₀ hlam.ne', one_mul]
    rw [heq]
    exact le_add_of_nonneg_right (mul_nonneg hnn
      (sliceFormVal_nonneg μG ρ hN2 hρcont hN β hpos
        x.val))
  rw [sq_le_sq] at hsq
  rwa [abs_of_nonneg (norm_nonneg _),
    abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _)
      (norm_nonneg _))] at hsq

/-! ### Completeness transport

The gate's one new lemma. The `J_λ` and `J_1` norms
dominate each other on the nose (the same two
nonnegative diagonal summands, one rescaled), so the
identity between the two domain synonyms is a uniform
equivalence, and FG-2a's completeness of the `J_1`
domain transports across it. -/

/-- Squared-norm domination, `J_λ` by `J_1`: on the
shared diagonal summands, `λa + b ≤ max(1, λ)(a + b)`. -/
theorem sliceFormDomainLam_norm_sq_le (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (lam : ℝ)
    (hlam : 0 < lam)
    (x : sliceFormDomainLam μG ρ hN2 hρcont hN β hpos
      lam hlam) :
    ‖x‖ ^ 2 ≤ max 1 lam
      * ‖sliceFormDomain.ofSub μG ρ hN2 hρcont hN β
          hpos x.toSub‖ ^ 2 := by
  rw [sliceFormDomainLam_norm_sq μG ρ hN2 hρcont hN β
      hpos lam hlam,
    sliceFormDomain_norm_sq μG ρ hN2 hρcont hN β hpos,
    sliceFormDomain.val_ofSub μG ρ hN2 hρcont hN β
      hpos]
  have e1 : lam * ‖x.val‖ ^ 2
      ≤ max 1 lam * ‖x.val‖ ^ 2 :=
    mul_le_mul_of_nonneg_right (le_max_right 1 lam)
      (sq_nonneg _)
  have e2 : sliceFormVal μG ρ hN2 hρcont hN β hpos
        x.val
      ≤ max 1 lam * sliceFormVal μG ρ hN2 hρcont hN β
          hpos x.val :=
    le_mul_of_one_le_left
      (sliceFormVal_nonneg μG ρ hN2 hρcont hN β hpos
        x.val) (le_max_left 1 lam)
  calc lam * ‖x.val‖ ^ 2 + sliceFormVal μG ρ hN2
        hρcont hN β hpos x.val
      ≤ max 1 lam * ‖x.val‖ ^ 2
        + max 1 lam * sliceFormVal μG ρ hN2 hρcont hN
            β hpos x.val := add_le_add e1 e2
    _ = max 1 lam * (‖x.val‖ ^ 2 + sliceFormVal μG ρ
          hN2 hρcont hN β hpos x.val) := by ring

/-- Squared-norm domination, `J_1` by `J_λ`:
`a + b ≤ max(1, λ⁻¹)(λa + b)`. -/
theorem sliceFormDomain_norm_sq_le_lam (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (lam : ℝ)
    (hlam : 0 < lam)
    (x : sliceFormDomainLam μG ρ hN2 hρcont hN β hpos
      lam hlam) :
    ‖sliceFormDomain.ofSub μG ρ hN2 hρcont hN β hpos
        x.toSub‖ ^ 2
      ≤ max 1 lam⁻¹ * ‖x‖ ^ 2 := by
  rw [sliceFormDomain_norm_sq μG ρ hN2 hρcont hN β
      hpos, sliceFormDomain.val_ofSub μG ρ hN2 hρcont
        hN β hpos,
    sliceFormDomainLam_norm_sq μG ρ hN2 hρcont hN β
      hpos lam hlam]
  have e1 : ‖x.val‖ ^ 2
      ≤ max 1 lam⁻¹ * (lam * ‖x.val‖ ^ 2) := by
    calc ‖x.val‖ ^ 2
        = lam⁻¹ * (lam * ‖x.val‖ ^ 2) := by
          rw [← mul_assoc, inv_mul_cancel₀ hlam.ne',
            one_mul]
      _ ≤ max 1 lam⁻¹ * (lam * ‖x.val‖ ^ 2) :=
          mul_le_mul_of_nonneg_right
            (le_max_right 1 lam⁻¹)
            (mul_nonneg hlam.le (sq_nonneg _))
  have e2 : sliceFormVal μG ρ hN2 hρcont hN β hpos
        x.val
      ≤ max 1 lam⁻¹ * sliceFormVal μG ρ hN2 hρcont hN
          β hpos x.val :=
    le_mul_of_one_le_left
      (sliceFormVal_nonneg μG ρ hN2 hρcont hN β hpos
        x.val) (le_max_left 1 lam⁻¹)
  calc ‖x.val‖ ^ 2 + sliceFormVal μG ρ hN2 hρcont hN
        β hpos x.val
      ≤ max 1 lam⁻¹ * (lam * ‖x.val‖ ^ 2)
        + max 1 lam⁻¹ * sliceFormVal μG ρ hN2 hρcont
            hN β hpos x.val := add_le_add e1 e2
    _ = max 1 lam⁻¹ * (lam * ‖x.val‖ ^ 2
          + sliceFormVal μG ρ hN2 hρcont hN β hpos
            x.val) := by ring

/-- Norm domination from the squared domination. -/
theorem sliceFormDomainLam_norm_le (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (lam : ℝ)
    (hlam : 0 < lam)
    (x : sliceFormDomainLam μG ρ hN2 hρcont hN β hpos
      lam hlam) :
    ‖x‖ ≤ Real.sqrt (max 1 lam)
      * ‖sliceFormDomain.ofSub μG ρ hN2 hρcont hN β
          hpos x.toSub‖ := by
  have hsq := sliceFormDomainLam_norm_sq_le μG ρ hN2
    hρcont hN β hpos lam hlam x
  have e : (Real.sqrt (max 1 lam)
      * ‖sliceFormDomain.ofSub μG ρ hN2 hρcont hN β
          hpos x.toSub‖) ^ 2
      = max 1 lam
        * ‖sliceFormDomain.ofSub μG ρ hN2 hρcont hN β
            hpos x.toSub‖ ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (le_trans (by norm_num)
      (le_max_left 1 lam))]
  have h1 : |‖x‖| ≤ |Real.sqrt (max 1 lam)
      * ‖sliceFormDomain.ofSub μG ρ hN2 hρcont hN β
          hpos x.toSub‖| := by
    rw [← sq_le_sq, e]
    exact hsq
  rwa [abs_of_nonneg (norm_nonneg _),
    abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _)
      (norm_nonneg _))] at h1

/-- The reverse norm domination. -/
theorem sliceFormDomain_transfer_norm_le (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (lam : ℝ)
    (hlam : 0 < lam)
    (x : sliceFormDomainLam μG ρ hN2 hρcont hN β hpos
      lam hlam) :
    ‖sliceFormDomain.ofSub μG ρ hN2 hρcont hN β hpos
        x.toSub‖
      ≤ Real.sqrt (max 1 lam⁻¹) * ‖x‖ := by
  have hsq := sliceFormDomain_norm_sq_le_lam μG ρ hN2
    hρcont hN β hpos lam hlam x
  have e : (Real.sqrt (max 1 lam⁻¹) * ‖x‖) ^ 2
      = max 1 lam⁻¹ * ‖x‖ ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (le_trans (by norm_num)
      (le_max_left 1 lam⁻¹))]
  have h1 : |‖sliceFormDomain.ofSub μG ρ hN2 hρcont
      hN β hpos x.toSub‖|
      ≤ |Real.sqrt (max 1 lam⁻¹) * ‖x‖| := by
    rw [← sq_le_sq, e]
    exact hsq
  rwa [abs_of_nonneg (norm_nonneg _),
    abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _)
      (norm_nonneg _))] at h1

/-- The identity transfer from the `λ`-domain to the
`J_1` domain, as a bare function: re-read the same
domain element in the other synonym. -/
def sliceFormDomainLam.toForm (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (lam : ℝ)
    (hlam : 0 < lam)
    (x : sliceFormDomainLam μG ρ hN2 hρcont hN β hpos
      lam hlam) :
    sliceFormDomain μG ρ hN2 hρcont hN β hpos :=
  sliceFormDomain.ofSub μG ρ hN2 hρcont hN β hpos
    x.toSub

/-- The identity transfer back, from the `J_1` domain
to the `λ`-domain. -/
def sliceFormDomain.ofSub_toLam (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (lam : ℝ)
    (hlam : 0 < lam)
    (w : sliceFormDomain μG ρ hN2 hρcont hN β hpos) :
    sliceFormDomainLam μG ρ hN2 hρcont hN β hpos lam
      hlam :=
  sliceFormDomainLam.ofSub μG ρ hN2 hρcont hN β hpos
    lam hlam w.toSub

theorem sliceFormDomainLam.toForm_sub (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (lam : ℝ)
    (hlam : 0 < lam)
    (x y : sliceFormDomainLam μG ρ hN2 hρcont hN β
      hpos lam hlam) :
    sliceFormDomainLam.toForm μG ρ hN2 hρcont hN β
        hpos lam hlam (x - y)
      = sliceFormDomainLam.toForm μG ρ hN2 hρcont hN β
          hpos lam hlam x
        - sliceFormDomainLam.toForm μG ρ hN2 hρcont hN
            β hpos lam hlam y :=
  rfl

theorem sliceFormDomain.ofSub_toLam_sub (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (lam : ℝ)
    (hlam : 0 < lam)
    (w₁ w₂ : sliceFormDomain μG ρ hN2 hρcont hN β
      hpos) :
    sliceFormDomain.ofSub_toLam μG ρ hN2 hρcont hN β
        hpos lam hlam (w₁ - w₂)
      = sliceFormDomain.ofSub_toLam μG ρ hN2 hρcont hN
          β hpos lam hlam w₁
        - sliceFormDomain.ofSub_toLam μG ρ hN2 hρcont
            hN β hpos lam hlam w₂ :=
  rfl

/-- The two transfers are inverse to each other (both
are the identity on the underlying domain element). -/
theorem sliceFormDomainLam.toForm_toLam (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (lam : ℝ)
    (hlam : 0 < lam)
    (w : sliceFormDomain μG ρ hN2 hρcont hN β hpos) :
    sliceFormDomainLam.toForm μG ρ hN2 hρcont hN β
        hpos lam hlam
        (sliceFormDomain.ofSub_toLam μG ρ hN2 hρcont
          hN β hpos lam hlam w) = w :=
  rfl

theorem sliceFormDomain.ofSub_toLam_toForm
    (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (lam : ℝ)
    (hlam : 0 < lam)
    (x : sliceFormDomainLam μG ρ hN2 hρcont hN β hpos
      lam hlam) :
    sliceFormDomain.ofSub_toLam μG ρ hN2 hρcont hN β
        hpos lam hlam
        (sliceFormDomainLam.toForm μG ρ hN2 hρcont hN
          β hpos lam hlam x) = x :=
  rfl

/-- **Uniform continuity of the transfer** from the
`λ`-domain to the `J_1` domain: distance in the `J_1`
norm is controlled by distance in the `J_λ` norm,
through the domination of the difference. -/
theorem sliceFormDomainLam.toForm_uniformContinuous
    (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (lam : ℝ)
    (hlam : 0 < lam) :
    UniformContinuous (sliceFormDomainLam.toForm μG ρ
      hN2 hρcont hN β hpos lam hlam) := by
  rw [Metric.uniformContinuous_iff]
  intro ε hε
  have hC : (0 : ℝ) < Real.sqrt (max 1 lam⁻¹) :=
    Real.sqrt_pos.mpr (lt_of_lt_of_le (by norm_num)
      (le_max_left 1 lam⁻¹))
  refine ⟨ε / Real.sqrt (max 1 lam⁻¹),
    div_pos hε hC, ?_⟩
  intro x y hxy
  have hle : ‖sliceFormDomainLam.toForm μG ρ hN2
        hρcont hN β hpos lam hlam (x - y)‖
      ≤ Real.sqrt (max 1 lam⁻¹) * ‖x - y‖ :=
    sliceFormDomain_transfer_norm_le μG ρ hN2 hρcont
      hN β hpos lam hlam (x - y)
  have hdist : dist (sliceFormDomainLam.toForm μG ρ
        hN2 hρcont hN β hpos lam hlam x)
        (sliceFormDomainLam.toForm μG ρ hN2 hρcont hN
          β hpos lam hlam y)
      = ‖sliceFormDomainLam.toForm μG ρ hN2 hρcont hN
          β hpos lam hlam (x - y)‖ := by
    rw [dist_eq_norm, sliceFormDomainLam.toForm_sub]
  rw [hdist]
  calc ‖sliceFormDomainLam.toForm μG ρ hN2 hρcont hN
        β hpos lam hlam (x - y)‖
      ≤ Real.sqrt (max 1 lam⁻¹) * ‖x - y‖ := hle
    _ = Real.sqrt (max 1 lam⁻¹) * dist x y := by
        rw [dist_eq_norm]
    _ < Real.sqrt (max 1 lam⁻¹)
          * (ε / Real.sqrt (max 1 lam⁻¹)) :=
        mul_lt_mul_of_pos_left hxy hC
    _ = ε := mul_div_cancel₀ ε hC.ne'

/-- **Uniform continuity of the transfer back**: distance
in the `J_λ` norm is controlled by distance in the
`J_1` norm. -/
theorem sliceFormDomain.ofSub_toLam_uniformContinuous
    (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (lam : ℝ)
    (hlam : 0 < lam) :
    UniformContinuous (sliceFormDomain.ofSub_toLam μG
      ρ hN2 hρcont hN β hpos lam hlam) := by
  rw [Metric.uniformContinuous_iff]
  intro ε hε
  have hC : (0 : ℝ) < Real.sqrt (max 1 lam) :=
    Real.sqrt_pos.mpr (lt_of_lt_of_le (by norm_num)
      (le_max_left 1 lam))
  refine ⟨ε / Real.sqrt (max 1 lam), div_pos hε hC, ?_⟩
  intro w₁ w₂ hw
  have hle : ‖sliceFormDomain.ofSub_toLam μG ρ hN2
        hρcont hN β hpos lam hlam (w₁ - w₂)‖
      ≤ Real.sqrt (max 1 lam) * ‖w₁ - w₂‖ := by
    have h := sliceFormDomainLam_norm_le μG ρ hN2
      hρcont hN β hpos lam hlam
      (sliceFormDomain.ofSub_toLam μG ρ hN2 hρcont hN
        β hpos lam hlam (w₁ - w₂))
    have e : sliceFormDomain.ofSub μG ρ hN2 hρcont hN
          β hpos
          (sliceFormDomain.ofSub_toLam μG ρ hN2
            hρcont hN β hpos lam hlam
              (w₁ - w₂)).toSub
        = w₁ - w₂ :=
      sliceFormDomain.ofSub_toSub μG ρ hN2 hρcont hN β
        hpos (w₁ - w₂)
    rwa [e] at h
  have hdist : dist
        (sliceFormDomain.ofSub_toLam μG ρ hN2 hρcont
          hN β hpos lam hlam w₁)
        (sliceFormDomain.ofSub_toLam μG ρ hN2 hρcont
          hN β hpos lam hlam w₂)
      = ‖sliceFormDomain.ofSub_toLam μG ρ hN2 hρcont
          hN β hpos lam hlam (w₁ - w₂)‖ := by
    rw [dist_eq_norm, sliceFormDomain.ofSub_toLam_sub]
  rw [hdist]
  calc ‖sliceFormDomain.ofSub_toLam μG ρ hN2 hρcont
        hN β hpos lam hlam (w₁ - w₂)‖
      ≤ Real.sqrt (max 1 lam) * ‖w₁ - w₂‖ := hle
    _ = Real.sqrt (max 1 lam) * dist w₁ w₂ := by
        rw [dist_eq_norm]
    _ < Real.sqrt (max 1 lam)
          * (ε / Real.sqrt (max 1 lam)) :=
        mul_lt_mul_of_pos_left hw hC
    _ = ε := mul_div_cancel₀ ε hC.ne'

/-- **The identity uniform equivalence** between the
`λ`-domain and the `J_1` domain: the two norms define
the same uniformity — the analytic content of the
gate's completeness transport. -/
noncomputable def sliceFormDomainLam.uniformEquivForm
    (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (lam : ℝ)
    (hlam : 0 < lam) :
    sliceFormDomainLam μG ρ hN2 hρcont hN β hpos lam
        hlam
      ≃ᵤ sliceFormDomain μG ρ hN2 hρcont hN β hpos where
  toFun := sliceFormDomainLam.toForm μG ρ hN2 hρcont
    hN β hpos lam hlam
  invFun := sliceFormDomain.ofSub_toLam μG ρ hN2
    hρcont hN β hpos lam hlam
  left_inv := sliceFormDomain.ofSub_toLam_toForm μG ρ
    hN2 hρcont hN β hpos lam hlam
  right_inv := sliceFormDomainLam.toForm_toLam μG ρ
    hN2 hρcont hN β hpos lam hlam
  uniformContinuous_toFun :=
    sliceFormDomainLam.toForm_uniformContinuous μG ρ
      hN2 hρcont hN β hpos lam hlam
  uniformContinuous_invFun :=
    sliceFormDomain.ofSub_toLam_uniformContinuous μG ρ
      hN2 hρcont hN β hpos lam hlam

/-- **COMPLETENESS TRANSPORT (the gate's one new
lemma).** The `λ`-form domain is complete: FG-2a's
completeness of the `J_1` domain, transported across
the identity uniform equivalence. No new Cauchy
argument is made — the `J_λ` norm and the `J_1` norm
have the same Cauchy sequences because they dominate
each other. -/
noncomputable instance sliceFormDomainLamCompleteSpace
    (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (lam : ℝ)
    (hlam : 0 < lam) :
    CompleteSpace (sliceFormDomainLam μG ρ hN2 hρcont
      hN β hpos lam hlam) :=
  (sliceFormDomainLam.uniformEquivForm μG ρ hN2 hρcont
    hN β hpos lam hlam).completeSpace_iff.mpr
    (sliceFormDomainCompleteSpace μG ρ hN2 hρcont hN β
      hpos)

/-! ## §2. The resolvent at weight `λ` -/

/-- The inclusion of the `λ`-form domain into the
completed space, as a linear map: the `val`
projection. -/
noncomputable def sliceFormInclusionLamLin (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (lam : ℝ)
    (hlam : 0 < lam) :
    sliceFormDomainLam μG ρ hN2 hρcont hN β hpos lam
        hlam
      →ₗ[ℂ] sliceHilbertSpace μG ρ hN2 hρcont hN β
        hpos where
  toFun := sliceFormDomainLam.val μG ρ hN2 hρcont hN β
    hpos lam hlam
  map_add' := fun x y => sliceFormDomainLam.val_add μG
    ρ hN2 hρcont hN β hpos lam hlam x y
  map_smul' := fun c x => sliceFormDomainLam.val_smul
    μG ρ hN2 hρcont hN β hpos lam hlam c x

/-- **The continuous inclusion** of the `λ`-form domain
into the completed space, with bound `√λ⁻¹`. -/
noncomputable def sliceFormInclusionLam (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (lam : ℝ)
    (hlam : 0 < lam) :
    sliceFormDomainLam μG ρ hN2 hρcont hN β hpos lam
        hlam
      →L[ℂ] sliceHilbertSpace μG ρ hN2 hρcont hN β
        hpos :=
  (sliceFormInclusionLamLin μG ρ hN2 hρcont hN β hpos
    lam hlam).mkContinuous (Real.sqrt lam⁻¹) (fun x =>
      sliceFormDomainLam_val_norm_le μG ρ hN2 hρcont
        hN β hpos lam hlam x)

theorem sliceFormInclusionLam_apply (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (lam : ℝ)
    (hlam : 0 < lam)
    (x : sliceFormDomainLam μG ρ hN2 hρcont hN β hpos
      lam hlam) :
    sliceFormInclusionLam μG ρ hN2 hρcont hN β hpos
        lam hlam x = x.val :=
  rfl

/-- **The pairing functional of `f ∈ H'`** on the
`λ`-form Hilbert space: `v ↦ ⟪f, v⟫`, continuous by
the `λ`-inclusion bound. This is the functional the
Friedrichs argument at weight `λ` feeds to Riesz. -/
noncomputable def sliceResolventFunctional (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (lam : ℝ)
    (hlam : 0 < lam)
    (f : ↥(sliceFormClosure μG ρ hN2 hρcont hN β
      hpos)) :
    sliceFormDomainLam μG ρ hN2 hρcont hN β hpos lam
        hlam
      →L[ℂ] ℂ :=
  (innerSL ℂ f.1).comp
    (sliceFormInclusionLam μG ρ hN2 hρcont hN β hpos
      lam hlam)

theorem sliceResolventFunctional_apply (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (lam : ℝ)
    (hlam : 0 < lam)
    (f : ↥(sliceFormClosure μG ρ hN2 hρcont hN β
      hpos))
    (v : sliceFormDomainLam μG ρ hN2 hρcont hN β hpos
      lam hlam) :
    sliceResolventFunctional μG ρ hN2 hρcont hN β hpos
        lam hlam f v
      = inner ℂ f.1 v.val :=
  rfl

/-- **The Riesz representative at weight `λ`**: the
unique `λ`-form-domain vector `u_f` with
`J_λ(u_f, v) = ⟪f, v⟫` for all `v` — Mathlib's
Fréchet–Riesz theorem (`InnerProductSpace.toDual`)
applied to the `J_λ` form Hilbert space of §1. -/
noncomputable def sliceResolventRep (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (lam : ℝ)
    (hlam : 0 < lam)
    (f : ↥(sliceFormClosure μG ρ hN2 hρcont hN β
      hpos)) :
    sliceFormDomainLam μG ρ hN2 hρcont hN β hpos lam
      hlam :=
  (InnerProductSpace.toDual ℂ
    (sliceFormDomainLam μG ρ hN2 hρcont hN β hpos
      lam hlam)).symm
    (sliceResolventFunctional μG ρ hN2 hρcont hN β
      hpos lam hlam f)

/-- **The resolvent equation at weight `λ`, in weak
form**: `J_λ(u_f, v) = ⟪f, v⟫` for every form-domain
`v` — i.e. `sliceFormB u_f v + λ⟪u_f, v⟫ = ⟪f, v⟫`,
the weak form of `(Ĥ + λ) u_f = f`. -/
theorem sliceResolventRep_spec (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (lam : ℝ)
    (hlam : 0 < lam)
    (f : ↥(sliceFormClosure μG ρ hN2 hρcont hN β
      hpos))
    (v : sliceFormDomainLam μG ρ hN2 hρcont hN β hpos
      lam hlam) :
    sliceFormInnerLam μG ρ hN2 hρcont hN β hpos lam
        hlam
        (sliceResolventRep μG ρ hN2 hρcont hN β hpos
          lam hlam f) v
      = inner ℂ f.1 v.val := by
  have h := InnerProductSpace.toDual_symm_apply
    (𝕜 := ℂ)
    (E := sliceFormDomainLam μG ρ hN2 hρcont hN β hpos
      lam hlam)
    (x := v) (y := sliceResolventFunctional μG ρ hN2
      hρcont hN β hpos lam hlam f)
  show inner ℂ (sliceResolventRep μG ρ hN2 hρcont hN
      β hpos lam hlam f) v = inner ℂ f.1 v.val
  exact h

/-- Uniqueness of `λ`-form-domain vectors by their
`J_λ` pairings — the definiteness that makes the
Riesz representative a well-defined function of `f`. -/
theorem sliceResolventRep_unique (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (lam : ℝ)
    (hlam : 0 < lam)
    {u₁ u₂ : sliceFormDomainLam μG ρ hN2 hρcont hN β
      hpos lam hlam}
    (h : ∀ v : sliceFormDomainLam μG ρ hN2 hρcont hN
        β hpos lam hlam,
      sliceFormInnerLam μG ρ hN2 hρcont hN β hpos lam
          hlam u₁ v
        = sliceFormInnerLam μG ρ hN2 hρcont hN β hpos
            lam hlam u₂ v) :
    u₁ = u₂ := by
  have h' : ∀ v : sliceFormDomainLam μG ρ hN2 hρcont
      hN β hpos lam hlam, inner ℂ u₁ v = inner ℂ u₂ v :=
    fun v => h v
  have hsub : ∀ v : sliceFormDomainLam μG ρ hN2
      hρcont hN β hpos lam hlam,
      inner ℂ (u₁ - u₂) v = 0 := fun v => by
    rw [inner_sub_left, h' v, sub_self]
  have hself := hsub (u₁ - u₂)
  rw [inner_self_eq_zero] at hself
  exact sub_eq_zero.mp hself

/-- **The resolvent at weight `λ`**, as a bare map
`H' → H'`: `R_λ f` is the ambient vector of the Riesz
representative `u_f`, which lies in the form domain,
hence in its closure `H'`. -/
noncomputable def sliceResolvent (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (lam : ℝ)
    (hlam : 0 < lam)
    (f : ↥(sliceFormClosure μG ρ hN2 hρcont hN β
      hpos)) :
    ↥(sliceFormClosure μG ρ hN2 hρcont hN β hpos) :=
  ⟨(sliceResolventRep μG ρ hN2 hρcont hN β hpos lam
      hlam f).toSub.1,
    sliceFormDomain_le_closure μG ρ hN2 hρcont hN β
      hpos (sliceResolventRep μG ρ hN2 hρcont hN β
        hpos lam hlam f).toSub.2⟩

/-- The resolvent's ambient vector is the
representative's ambient vector. -/
theorem sliceResolvent_coe (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (lam : ℝ)
    (hlam : 0 < lam)
    (f : ↥(sliceFormClosure μG ρ hN2 hρcont hN β
      hpos)) :
    (sliceResolvent μG ρ hN2 hρcont hN β hpos lam hlam
        f).1
      = (sliceResolventRep μG ρ hN2 hρcont hN β hpos
          lam hlam f).val :=
  rfl

/-- The Riesz representative at weight `λ` is
additive: the two conjugate-linearities (of the
pairing in `f`, of Riesz in the functional) cancel.
Proved by the characterization plus uniqueness. -/
theorem sliceResolventRep_add (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (lam : ℝ)
    (hlam : 0 < lam)
    (f g : ↥(sliceFormClosure μG ρ hN2 hρcont hN β
      hpos)) :
    sliceResolventRep μG ρ hN2 hρcont hN β hpos lam
        hlam (f + g)
      = sliceResolventRep μG ρ hN2 hρcont hN β hpos
          lam hlam f
        + sliceResolventRep μG ρ hN2 hρcont hN β hpos
            lam hlam g := by
  apply sliceResolventRep_unique μG ρ hN2 hρcont hN β
    hpos lam hlam
  intro v
  rw [sliceFormInnerLam_add_left μG ρ hN2 hρcont hN β
      hpos lam hlam,
    sliceResolventRep_spec μG ρ hN2 hρcont hN β hpos
      lam hlam (f + g) v,
    sliceResolventRep_spec μG ρ hN2 hρcont hN β hpos
      lam hlam f v,
    sliceResolventRep_spec μG ρ hN2 hρcont hN β hpos
      lam hlam g v, Submodule.coe_add, inner_add_left]

/-- The Riesz representative at weight `λ` is
homogeneous, by the same uniqueness argument. -/
theorem sliceResolventRep_smul (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (lam : ℝ)
    (hlam : 0 < lam) (c : ℂ)
    (f : ↥(sliceFormClosure μG ρ hN2 hρcont hN β
      hpos)) :
    sliceResolventRep μG ρ hN2 hρcont hN β hpos lam
        hlam (c • f)
      = c • sliceResolventRep μG ρ hN2 hρcont hN β
          hpos lam hlam f := by
  apply sliceResolventRep_unique μG ρ hN2 hρcont hN β
    hpos lam hlam
  intro v
  rw [sliceFormInnerLam_smul_left μG ρ hN2 hρcont hN
      β hpos lam hlam,
    sliceResolventRep_spec μG ρ hN2 hρcont hN β hpos
      lam hlam (c • f) v,
    sliceResolventRep_spec μG ρ hN2 hρcont hN β hpos
      lam hlam f v, Submodule.coe_smul,
    inner_smul_left]

/-- **The resolvent at weight `λ` as a linear map**
`H' →ₗ[ℂ] H'`. -/
noncomputable def sliceResolventLin (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (lam : ℝ)
    (hlam : 0 < lam) :
    ↥(sliceFormClosure μG ρ hN2 hρcont hN β hpos)
      →ₗ[ℂ] ↥(sliceFormClosure μG ρ hN2 hρcont hN β
        hpos) where
  toFun := sliceResolvent μG ρ hN2 hρcont hN β hpos
    lam hlam
  map_add' := by
    intro f g
    apply Subtype.ext
    show (sliceResolventRep μG ρ hN2 hρcont hN β hpos
          lam hlam (f + g)).val
      = (sliceResolventRep μG ρ hN2 hρcont hN β hpos
            lam hlam f).val
        + (sliceResolventRep μG ρ hN2 hρcont hN β
            hpos lam hlam g).val
    rw [sliceResolventRep_add μG ρ hN2 hρcont hN β
        hpos lam hlam f g,
      sliceFormDomainLam.val_add μG ρ hN2 hρcont hN β
        hpos lam hlam]
  map_smul' := by
    intro c f
    apply Subtype.ext
    show (sliceResolventRep μG ρ hN2 hρcont hN β hpos
          lam hlam (c • f)).val
      = c • (sliceResolventRep μG ρ hN2 hρcont hN β
          hpos lam hlam f).val
    rw [sliceResolventRep_smul μG ρ hN2 hρcont hN β
        hpos lam hlam c f,
      sliceFormDomainLam.val_smul μG ρ hN2 hρcont hN
        β hpos lam hlam]

theorem sliceResolventLin_apply (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (lam : ℝ)
    (hlam : 0 < lam)
    (f : ↥(sliceFormClosure μG ρ hN2 hρcont hN β
      hpos)) :
    sliceResolventLin μG ρ hN2 hρcont hN β hpos lam
        hlam f
      = sliceResolvent μG ρ hN2 hρcont hN β hpos lam
          hlam f :=
  rfl

/-- **Symmetry of the resolvent at weight `λ`**: the
ambient pairing `⟪R_λ f, g⟫ = ⟪f, R_λ g⟫` — the
conjugate-symmetry of `J_λ`, transported through the
Riesz characterization on both sides. -/
theorem sliceResolvent_symmetric (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (lam : ℝ)
    (hlam : 0 < lam)
    (f g : ↥(sliceFormClosure μG ρ hN2 hρcont hN β
      hpos)) :
    inner ℂ (sliceResolvent μG ρ hN2 hρcont hN β hpos
        lam hlam f).1 g.1
      = inner ℂ f.1 (sliceResolvent μG ρ hN2 hρcont
          hN β hpos lam hlam g).1 := by
  rw [sliceResolvent_coe μG ρ hN2 hρcont hN β hpos
      lam hlam f,
    sliceResolvent_coe μG ρ hN2 hρcont hN β hpos lam
      hlam g]
  have h1 := sliceResolventRep_spec μG ρ hN2 hρcont
    hN β hpos lam hlam g (sliceResolventRep μG ρ hN2
      hρcont hN β hpos lam hlam f)
  have h2 := sliceResolventRep_spec μG ρ hN2 hρcont
    hN β hpos lam hlam f (sliceResolventRep μG ρ hN2
      hρcont hN β hpos lam hlam g)
  have h3 : sliceFormInnerLam μG ρ hN2 hρcont hN β
        hpos lam hlam
        (sliceResolventRep μG ρ hN2 hρcont hN β hpos
          lam hlam f)
        (sliceResolventRep μG ρ hN2 hρcont hN β hpos
          lam hlam g)
      = (starRingEnd ℂ) (sliceFormInnerLam μG ρ hN2
          hρcont hN β hpos lam hlam
          (sliceResolventRep μG ρ hN2 hρcont hN β
            hpos lam hlam g)
          (sliceResolventRep μG ρ hN2 hρcont hN β
            hpos lam hlam f)) :=
    (sliceFormInnerLam_conj_symm μG ρ hN2 hρcont hN β
      hpos lam hlam _ _).symm
  rw [h2, h1] at h3
  rw [h3, inner_conj_symm]

/-- **The resolvent bound at weight `λ`**:
`‖R_λ f‖ ≤ λ⁻¹‖f‖`. The representative absorbs one
factor `√λ⁻¹` through the inclusion bound on its
ambient vector and a second through the energy
estimate `‖u_f‖²_λ = ⟪f, u_f⟫ ≤ ‖f‖ · ‖u_f‖_val`. -/
theorem sliceResolvent_norm_le (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (lam : ℝ)
    (hlam : 0 < lam)
    (f : ↥(sliceFormClosure μG ρ hN2 hρcont hN β
      hpos)) :
    ‖sliceResolventLin μG ρ hN2 hρcont hN β hpos lam
        hlam f‖ ≤ lam⁻¹ * ‖f‖ := by
  have hnn : (0 : ℝ) ≤ lam⁻¹ := inv_nonneg.mpr hlam.le
  have hfnorm : ‖f.1‖ = ‖f‖ := rfl
  have hspec := sliceResolventRep_spec μG ρ hN2
    hρcont hN β hpos lam hlam f
    (sliceResolventRep μG ρ hN2 hρcont hN β hpos lam
      hlam f)
  have hnorm : ‖sliceResolventRep μG ρ hN2 hρcont hN
        β hpos lam hlam f‖ ^ 2
      = (sliceFormInnerLam μG ρ hN2 hρcont hN β hpos
          lam hlam
          (sliceResolventRep μG ρ hN2 hρcont hN β
            hpos lam hlam f)
          (sliceResolventRep μG ρ hN2 hρcont hN β
            hpos lam hlam f)).re := by
    rw [sliceFormDomainLam_norm_sq μG ρ hN2 hρcont hN
        β hpos lam hlam,
      sliceFormInnerLam_self_re μG ρ hN2 hρcont hN β
        hpos lam hlam]
  have hle1 : ‖sliceResolventRep μG ρ hN2 hρcont hN β
        hpos lam hlam f‖ ^ 2
      ≤ ‖f‖ * ‖(sliceResolventRep μG ρ hN2 hρcont hN
          β hpos lam hlam f).val‖ := by
    rw [hnorm, hspec]
    calc (inner ℂ f.1 (sliceResolventRep μG ρ hN2
            hρcont hN β hpos lam hlam f).val).re
        ≤ ‖inner ℂ f.1 (sliceResolventRep μG ρ hN2
            hρcont hN β hpos lam hlam f).val‖ :=
          Complex.re_le_norm _
      _ ≤ ‖f‖ * ‖(sliceResolventRep μG ρ hN2 hρcont
            hN β hpos lam hlam f).val‖ := by
          rw [← hfnorm]
          exact norm_inner_le_norm _ _
  have hle : ‖sliceResolventRep μG ρ hN2 hρcont hN β
        hpos lam hlam f‖
        * ‖sliceResolventRep μG ρ hN2 hρcont hN β hpos
            lam hlam f‖
      ≤ (Real.sqrt lam⁻¹ * ‖f‖)
        * ‖sliceResolventRep μG ρ hN2 hρcont hN β
            hpos lam hlam f‖ := by
    calc ‖sliceResolventRep μG ρ hN2 hρcont hN β hpos
          lam hlam f‖
          * ‖sliceResolventRep μG ρ hN2 hρcont hN β
              hpos lam hlam f‖
        = ‖sliceResolventRep μG ρ hN2 hρcont hN β
            hpos lam hlam f‖ ^ 2 := (pow_two _).symm
      _ ≤ ‖f‖ * ‖(sliceResolventRep μG ρ hN2 hρcont
            hN β hpos lam hlam f).val‖ := hle1
      _ ≤ ‖f‖ * (Real.sqrt lam⁻¹
            * ‖sliceResolventRep μG ρ hN2 hρcont hN β
                hpos lam hlam f‖) :=
          mul_le_mul_of_nonneg_left
            (sliceFormDomainLam_val_norm_le μG ρ hN2
              hρcont hN β hpos lam hlam _)
            (norm_nonneg _)
      _ = (Real.sqrt lam⁻¹ * ‖f‖)
          * ‖sliceResolventRep μG ρ hN2 hρcont hN β
              hpos lam hlam f‖ := by ring
  have hrep_le : ‖sliceResolventRep μG ρ hN2 hρcont
        hN β hpos lam hlam f‖
      ≤ Real.sqrt lam⁻¹ * ‖f‖ := by
    rcases eq_or_ne ‖sliceResolventRep μG ρ hN2
        hρcont hN β hpos lam hlam f‖ 0 with hu0 | hu0
    · rw [hu0]
      exact mul_nonneg (Real.sqrt_nonneg _)
        (norm_nonneg _)
    · have hpos' : 0 < ‖sliceResolventRep μG ρ hN2
          hρcont hN β hpos lam hlam f‖ :=
        lt_of_le_of_ne (norm_nonneg _) (Ne.symm hu0)
      exact le_of_mul_le_mul_right hle hpos'
  have hval : ‖(sliceResolventLin μG ρ hN2 hρcont hN
        β hpos lam hlam f).1‖
      = ‖(sliceResolventRep μG ρ hN2 hρcont hN β
          hpos lam hlam f).val‖ := by
    rw [sliceResolventLin_apply μG ρ hN2 hρcont hN β
        hpos lam hlam f,
      sliceResolvent_coe μG ρ hN2 hρcont hN β hpos lam
        hlam f]
  show ‖(sliceResolventLin μG ρ hN2 hρcont hN β hpos
      lam hlam f).1‖ ≤ lam⁻¹ * ‖f‖
  rw [hval]
  calc ‖(sliceResolventRep μG ρ hN2 hρcont hN β hpos
        lam hlam f).val‖
      ≤ Real.sqrt lam⁻¹ * ‖sliceResolventRep μG ρ hN2
          hρcont hN β hpos lam hlam f‖ :=
        sliceFormDomainLam_val_norm_le μG ρ hN2
          hρcont hN β hpos lam hlam _
    _ ≤ Real.sqrt lam⁻¹ * (Real.sqrt lam⁻¹ * ‖f‖) :=
        mul_le_mul_of_nonneg_left hrep_le
          (Real.sqrt_nonneg _)
    _ = lam⁻¹ * ‖f‖ := by
        rw [← mul_assoc, Real.mul_self_sqrt hnn]

/-- **The resolvent at weight `λ` as a continuous
linear map** of bound `λ⁻¹` on `H'`. -/
noncomputable def sliceResolventCLM (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (lam : ℝ)
    (hlam : 0 < lam) :
    ↥(sliceFormClosure μG ρ hN2 hρcont hN β hpos)
      →L[ℂ] ↥(sliceFormClosure μG ρ hN2 hρcont hN β
        hpos) :=
  (sliceResolventLin μG ρ hN2 hρcont hN β
    hpos lam hlam).mkContinuous lam⁻¹ (fun f =>
      sliceResolvent_norm_le μG ρ hN2 hρcont hN β hpos
        lam hlam f)

theorem sliceResolventCLM_apply (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (lam : ℝ)
    (hlam : 0 < lam)
    (f : ↥(sliceFormClosure μG ρ hN2 hρcont hN β
      hpos)) :
    sliceResolventCLM μG ρ hN2 hρcont hN β hpos lam
        hlam f
      = sliceResolvent μG ρ hN2 hρcont hN β hpos lam
          hlam f :=
  rfl

/-- **Positivity of the resolvent pairing**:
`(⟪f, R_λ f⟫).re ≥ 0` — it is the `J_λ` energy of the
representative, `λ‖u_f‖² + form(u_f)`. -/
theorem sliceResolvent_pairing_nonneg (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (lam : ℝ)
    (hlam : 0 < lam)
    (f : ↥(sliceFormClosure μG ρ hN2 hρcont hN β
      hpos)) :
    0 ≤ (inner ℂ f (sliceResolventLin μG ρ hN2 hρcont
        hN β hpos lam hlam f)).re := by
  have hspec := sliceResolventRep_spec μG ρ hN2
    hρcont hN β hpos lam hlam f
    (sliceResolventRep μG ρ hN2 hρcont hN β hpos lam
      hlam f)
  have h1 : inner ℂ f (sliceResolventLin μG ρ hN2
        hρcont hN β hpos lam hlam f)
      = sliceFormInnerLam μG ρ hN2 hρcont hN β hpos
          lam hlam
          (sliceResolventRep μG ρ hN2 hρcont hN β
            hpos lam hlam f)
          (sliceResolventRep μG ρ hN2 hρcont hN β
            hpos lam hlam f) := by
    rw [sliceFormClosure_inner μG ρ hN2 hρcont hN β
        hpos, sliceResolventLin_apply μG ρ hN2 hρcont
        hN β hpos lam hlam,
      sliceResolvent_coe μG ρ hN2 hρcont hN β hpos lam
        hlam]
    exact hspec.symm
  rw [h1]
  exact sliceFormInnerLam_re_nonneg μG ρ hN2 hρcont
    hN β hpos lam hlam _
/-! ## §3. Domain independence -/

/-- The character `↑λ − 1` arising from shifting
between resolvents is real: its conjugate is itself. -/
theorem sliceLam_sub_one_conj (lam : ℝ) :
    (starRingEnd ℂ) ((lam : ℂ) - 1) = (lam : ℂ) - 1 := by
  have h : ((lam : ℂ) - 1) = ((lam - 1 : ℝ) : ℂ) := by
    push_cast
    ring
  rw [h]
  exact Complex.conj_ofReal _

/-- **The pairing transfer, `J_λ → J_1`**: the
`J_1`-pairings of the transferred `λ`-representative
of `f` are the pairings of the shifted data
`f − (λ − 1) • R_λ f`. The form values cancel against
the shift; this identity is the whole mechanism of
domain independence. -/
theorem sliceResolventRep_transfer_pairing (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (lam : ℝ)
    (hlam : 0 < lam)
    (f : ↥(sliceFormClosure μG ρ hN2 hρcont hN β
      hpos))
    (v : sliceFormDomain μG ρ hN2 hρcont hN β hpos) :
    sliceFormInner μG ρ hN2 hρcont hN β hpos
        (sliceFormDomainLam.toForm μG ρ hN2 hρcont hN
          β hpos lam hlam
          (sliceResolventRep μG ρ hN2 hρcont hN β hpos
            lam hlam f)) v
      = inner ℂ (f - ((lam : ℂ) - 1)
          • sliceResolventLin μG ρ hN2 hρcont hN β
            hpos lam hlam f).1 v.val := by
  have hB : sliceFormB μG ρ hN2 hρcont hN β hpos
        (sliceResolventRep μG ρ hN2 hρcont hN β hpos
          lam hlam f).toSub v.toSub
      + (lam : ℂ) * inner ℂ (sliceResolventRep μG ρ
          hN2 hρcont hN β hpos lam hlam f).val v.val
      = inner ℂ f.1 v.val := by
    have h := sliceResolventRep_spec μG ρ hN2 hρcont
      hN β hpos lam hlam f
      (sliceFormDomainLam.ofSub μG ρ hN2 hρcont hN β
        hpos lam hlam v.toSub)
    exact h
  have hF : sliceFormInner μG ρ hN2 hρcont hN β hpos
        (sliceFormDomainLam.toForm μG ρ hN2 hρcont hN
          β hpos lam hlam
          (sliceResolventRep μG ρ hN2 hρcont hN β hpos
            lam hlam f)) v
      = inner ℂ (sliceResolventRep μG ρ hN2 hρcont hN
          β hpos lam hlam f).val v.val
        + sliceFormB μG ρ hN2 hρcont hN β hpos
            (sliceResolventRep μG ρ hN2 hρcont hN β
              hpos lam hlam f).toSub v.toSub := rfl
  rw [hF, Submodule.coe_sub, Submodule.coe_smul,
    sliceResolventLin_apply μG ρ hN2 hρcont hN β hpos
      lam hlam f,
    sliceResolvent_coe μG ρ hN2 hρcont hN β hpos lam
      hlam f,
    inner_sub_left, inner_smul_left,
    sliceLam_sub_one_conj lam]
  linear_combination hB

/-- **The representative transfer, `J_λ → J_1`**: the
weight-`1` Riesz representative of the shifted data
`f − (λ − 1) • R_λ f` is the transferred
`λ`-representative of `f`. -/
theorem sliceResolventRep_transfer (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (lam : ℝ)
    (hlam : 0 < lam)
    (f : ↥(sliceFormClosure μG ρ hN2 hρcont hN β
      hpos)) :
    sliceFriedrichsRep μG ρ hN2 hρcont hN β hpos
        (f - ((lam : ℂ) - 1) • sliceResolventLin μG ρ
          hN2 hρcont hN β hpos lam hlam f)
      = sliceFormDomainLam.toForm μG ρ hN2 hρcont hN β
          hpos lam hlam
          (sliceResolventRep μG ρ hN2 hρcont hN β hpos
            lam hlam f) := by
  apply sliceFriedrichsRep_unique μG ρ hN2 hρcont hN
    β hpos
  intro v
  rw [sliceFriedrichsRep_spec μG ρ hN2 hρcont hN β
    hpos]
  exact (sliceResolventRep_transfer_pairing μG ρ hN2
    hρcont hN β hpos lam hlam f v).symm

/-- **The pairing transfer, `J_1 → J_λ`**: the
`J_λ`-pairings of the transferred weight-`1`
representative of `f` are the pairings of the shifted
data `f + (λ − 1) • R_1 f`. -/
theorem sliceFriedrichsRep_transfer_pairing
    (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (lam : ℝ)
    (hlam : 0 < lam)
    (f : ↥(sliceFormClosure μG ρ hN2 hρcont hN β
      hpos))
    (v : sliceFormDomainLam μG ρ hN2 hρcont hN β hpos
      lam hlam) :
    sliceFormInnerLam μG ρ hN2 hρcont hN β hpos lam
        hlam
        (sliceFormDomain.ofSub_toLam μG ρ hN2 hρcont
          hN β hpos lam hlam
          (sliceFriedrichsRep μG ρ hN2 hρcont hN β
            hpos f)) v
      = inner ℂ (f + ((lam : ℂ) - 1)
          • sliceFriedrichsResolventLin μG ρ hN2
            hρcont hN β hpos f).1 v.val := by
  have hB : inner ℂ (sliceFriedrichsRep μG ρ hN2
        hρcont hN β hpos f).val v.val
      + sliceFormB μG ρ hN2 hρcont hN β hpos
          (sliceFriedrichsRep μG ρ hN2 hρcont hN β
            hpos f).toSub v.toSub
      = inner ℂ f.1 v.val := by
    have h := sliceFriedrichsRep_spec μG ρ hN2 hρcont
      hN β hpos f
      (sliceFormDomain.ofSub μG ρ hN2 hρcont hN β hpos
        v.toSub)
    exact h
  have hF : sliceFormInnerLam μG ρ hN2 hρcont hN β
        hpos lam hlam
        (sliceFormDomain.ofSub_toLam μG ρ hN2 hρcont
          hN β hpos lam hlam
          (sliceFriedrichsRep μG ρ hN2 hρcont hN β
            hpos f)) v
      = sliceFormB μG ρ hN2 hρcont hN β hpos
          (sliceFriedrichsRep μG ρ hN2 hρcont hN β
            hpos f).toSub v.toSub
        + (lam : ℂ) * inner ℂ (sliceFriedrichsRep μG
            ρ hN2 hρcont hN β hpos f).val v.val := rfl
  rw [hF, Submodule.coe_add, Submodule.coe_smul,
    sliceFriedrichsResolventLin_apply μG ρ hN2 hρcont
      hN β hpos f,
    sliceFriedrichsResolvent_coe μG ρ hN2 hρcont hN β
      hpos f,
    inner_add_left, inner_smul_left,
    sliceLam_sub_one_conj lam]
  linear_combination hB

/-- **The representative transfer, `J_1 → J_λ`**: the
`λ`-representative of the shifted data
`f + (λ − 1) • R_1 f` is the transferred weight-`1`
representative of `f`. -/
theorem sliceFriedrichsRep_transfer (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (lam : ℝ)
    (hlam : 0 < lam)
    (f : ↥(sliceFormClosure μG ρ hN2 hρcont hN β
      hpos)) :
    sliceResolventRep μG ρ hN2 hρcont hN β hpos lam
        hlam
        (f + ((lam : ℂ) - 1)
          • sliceFriedrichsResolventLin μG ρ hN2
            hρcont hN β hpos f)
      = sliceFormDomain.ofSub_toLam μG ρ hN2 hρcont hN
          β hpos lam hlam
          (sliceFriedrichsRep μG ρ hN2 hρcont hN β
            hpos f) := by
  apply sliceResolventRep_unique μG ρ hN2 hρcont hN
    β hpos lam hlam
  intro v
  exact (sliceResolventRep_spec μG ρ hN2 hρcont hN β
      hpos lam hlam _ v).trans
    (sliceFriedrichsRep_transfer_pairing μG ρ hN2
      hρcont hN β hpos lam hlam f v).symm

/-- **Range inclusion, `range R_λ ⊆ dom(Ĥ)`**: the
shifted representative construction lands every
`R_λ f` in the FG-2b operator domain. -/
theorem sliceResolvent_range_le (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (lam : ℝ)
    (hlam : 0 < lam) :
    LinearMap.range (sliceResolventLin μG ρ hN2
        hρcont hN β hpos lam hlam)
      ≤ sliceHamOperatorDomain μG ρ hN2 hρcont hN β
        hpos := by
  rintro z ⟨f, rfl⟩
  refine ⟨f - ((lam : ℂ) - 1) • sliceResolventLin
    μG ρ hN2 hρcont hN β hpos lam hlam f, ?_⟩
  apply Subtype.ext
  show (sliceFriedrichsRep μG ρ hN2 hρcont hN β hpos
      (f - ((lam : ℂ) - 1) • sliceResolventLin μG ρ
        hN2 hρcont hN β hpos lam hlam f)).val
    = (sliceResolventRep μG ρ hN2 hρcont hN β hpos
        lam hlam f).val
  rw [sliceResolventRep_transfer μG ρ hN2 hρcont hN β
    hpos lam hlam f]
  show (sliceResolventRep μG ρ hN2 hρcont hN β hpos
      lam hlam f).toSub.1
    = (sliceResolventRep μG ρ hN2 hρcont hN β hpos
        lam hlam f).val
  rfl

/-- **Range inclusion, `dom(Ĥ) ⊆ range R_λ`**: every
operator-domain vector is an `R_λ` value, of the
shifted weight-`1` data. -/
theorem sliceFriedrichs_range_le (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (lam : ℝ)
    (hlam : 0 < lam) :
    sliceHamOperatorDomain μG ρ hN2 hρcont hN β hpos
      ≤ LinearMap.range (sliceResolventLin μG ρ hN2
          hρcont hN β hpos lam hlam) := by
  rintro z ⟨f, rfl⟩
  refine ⟨f + ((lam : ℂ) - 1)
    • sliceFriedrichsResolventLin μG ρ hN2 hρcont hN
      β hpos f, ?_⟩
  apply Subtype.ext
  rw [sliceResolventLin_apply μG ρ hN2 hρcont hN β
      hpos lam hlam,
    sliceResolvent_coe μG ρ hN2 hρcont hN β hpos lam
      hlam,
    sliceFriedrichsRep_transfer μG ρ hN2 hρcont hN β
      hpos lam hlam f,
    sliceFriedrichsResolventLin_apply μG ρ hN2 hρcont
      hN β hpos f,
    sliceFriedrichsResolvent_coe μG ρ hN2 hρcont hN β
      hpos f]
  show (sliceFriedrichsRep μG ρ hN2 hρcont hN β hpos
      f).toSub.1
    = (sliceFriedrichsRep μG ρ hN2 hρcont hN β hpos
        f).val
  rfl

/-- **DOMAIN INDEPENDENCE**: the range of the
resolvent is the Friedrichs operator domain at EVERY
weight `λ > 0` — the domain of `Ĥ` does not depend
on the resolvent weight. -/
theorem sliceResolvent_range_eq (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (lam : ℝ)
    (hlam : 0 < lam) :
    LinearMap.range (sliceResolventLin μG ρ hN2
        hρcont hN β hpos lam hlam)
      = sliceHamOperatorDomain μG ρ hN2 hρcont hN β
        hpos :=
  le_antisymm
    (sliceResolvent_range_le μG ρ hN2 hρcont hN β hpos
      lam hlam)
    (sliceFriedrichs_range_le μG ρ hN2 hρcont hN β
      hpos lam hlam)

/-- **The resolvent equation at weight `λ`, in
operator form**: for `u` in the operator domain with
`u = R_λ f`, `(Ĥ + λ)u = f` — i.e.
`sliceHamOperator u + (λ:ℂ) • u = f`, FG-2b's
Friedrichs characterization of `Ĥ` applied to the
shifted representative. -/
theorem sliceHamOperator_add_lam_smul (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (lam : ℝ)
    (hlam : 0 < lam)
    (u : ↥(sliceHamOperatorDomain μG ρ hN2 hρcont hN
      β hpos))
    (f : ↥(sliceFormClosure μG ρ hN2 hρcont hN β
      hpos))
    (hf : sliceResolventLin μG ρ hN2 hρcont hN β hpos
        lam hlam f = u.1) :
    sliceHamOperator μG ρ hN2 hρcont hN β hpos u
        + (lam : ℂ) • u.1
      = f := by
  have hR : sliceFriedrichsResolventLin μG ρ hN2
        hρcont hN β hpos
        (f - ((lam : ℂ) - 1) • sliceResolventLin μG ρ
          hN2 hρcont hN β hpos lam hlam f)
      = u.1 := by
    have h1 : sliceFriedrichsResolventLin μG ρ hN2
          hρcont hN β hpos
          (f - ((lam : ℂ) - 1) • sliceResolventLin
            μG ρ hN2 hρcont hN β hpos lam hlam f)
        = sliceResolventLin μG ρ hN2 hρcont hN β hpos
            lam hlam f := by
      apply Subtype.ext
      show (sliceFriedrichsRep μG ρ hN2 hρcont hN β
          hpos
          (f - ((lam : ℂ) - 1) • sliceResolventLin
            μG ρ hN2 hρcont hN β hpos lam hlam
              f)).val
        = (sliceResolventRep μG ρ hN2 hρcont hN β
            hpos lam hlam f).val
      rw [sliceResolventRep_transfer μG ρ hN2 hρcont
        hN β hpos lam hlam f]
      show (sliceResolventRep μG ρ hN2 hρcont hN β
          hpos lam hlam f).toSub.1
        = (sliceResolventRep μG ρ hN2 hρcont hN β
            hpos lam hlam f).val
      rfl
    rw [h1]
    exact hf
  rw [sliceHamOperator_eq μG ρ hN2 hρcont hN β hpos
    u _ hR, hf]
  have hsm : ((lam : ℂ) - 1) • u.1 + u.1
      = (lam : ℂ) • u.1 := by
    have h1 : ((lam : ℂ) - 1) • u.1 + (1 : ℂ) • u.1
        = (lam : ℂ) • u.1 := by
      rw [← add_smul, sub_add_cancel]
    rwa [one_smul] at h1
  rw [sub_sub, hsm, sub_add_cancel]

/-- **The Hamiltonian of a resolvent value**:
`Ĥ(R_λ f) = f − λ • R_λ f`, stated at domain elements
via the `R_λ f = u` presentation. -/
theorem sliceHamOperator_resolventLam (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (lam : ℝ)
    (hlam : 0 < lam)
    (u : ↥(sliceHamOperatorDomain μG ρ hN2 hρcont hN
      β hpos))
    (f : ↥(sliceFormClosure μG ρ hN2 hρcont hN β
      hpos))
    (hf : sliceResolventLin μG ρ hN2 hρcont hN β hpos
        lam hlam f = u.1) :
    sliceHamOperator μG ρ hN2 hρcont hN β hpos u
      = f - (lam : ℂ) • u.1 :=
  eq_sub_of_add_eq (sliceHamOperator_add_lam_smul μG
    ρ hN2 hρcont hN β hpos lam hlam u f hf)

/-- **`Ĥ + λ` is surjective at every weight** — the
operator-form resolvent equation, solvable for every
`f ∈ H'` by the resolvent value `R_λ f` itself. -/
theorem sliceHamOperator_add_lam_surjective
    (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (lam : ℝ)
    (hlam : 0 < lam)
    (f : ↥(sliceFormClosure μG ρ hN2 hρcont hN β
      hpos)) :
    ∃ u : ↥(sliceHamOperatorDomain μG ρ hN2 hρcont
        hN β hpos),
      sliceHamOperator μG ρ hN2 hρcont hN β hpos u
          + (lam : ℂ) • u.1
        = f :=
  ⟨⟨sliceResolventLin μG ρ hN2 hρcont hN β hpos lam
      hlam f,
    sliceResolvent_range_le μG ρ hN2 hρcont hN β hpos
      lam hlam (LinearMap.mem_range_self
        (sliceResolventLin μG ρ hN2 hρcont hN β hpos
          lam hlam) f)⟩,
   sliceHamOperator_add_lam_smul μG ρ hN2 hρcont hN β
     hpos lam hlam _ f rfl⟩

/-! ## §4. Consistency at `λ = 1` -/

/-- **Representative consistency at weight one**: the
`λ = 1` Riesz representative of `f` is the
transferred FG-2b representative — the `J_1` form of
FG-2a IS `J_λ` at `λ = 1`, transported across the
`ofSub`/`toSub` identification. -/
theorem sliceResolventRep_one (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (hlam : (0 : ℝ) < 1)
    (f : ↥(sliceFormClosure μG ρ hN2 hρcont hN β
      hpos)) :
    sliceResolventRep μG ρ hN2 hρcont hN β hpos 1
        hlam f
      = sliceFormDomainLam.ofSub μG ρ hN2 hρcont hN β
          hpos 1 hlam
          (sliceFriedrichsRep μG ρ hN2 hρcont hN β
            hpos f).toSub := by
  apply sliceResolventRep_unique μG ρ hN2 hρcont hN β
    hpos 1 hlam
  intro v
  rw [sliceResolventRep_spec μG ρ hN2 hρcont hN β
    hpos 1 hlam]
  have h1 : sliceFormInnerLam μG ρ hN2 hρcont hN β
        hpos 1 hlam
        (sliceFormDomainLam.ofSub μG ρ hN2 hρcont hN
          β hpos 1 hlam
          (sliceFriedrichsRep μG ρ hN2 hρcont hN β
            hpos f).toSub) v
      = sliceFormInner μG ρ hN2 hρcont hN β hpos
          (sliceFriedrichsRep μG ρ hN2 hρcont hN β
            hpos f)
          (sliceFormDomain.ofSub μG ρ hN2 hρcont hN β
            hpos v.toSub) := by
    show sliceFormB μG ρ hN2 hρcont hN β hpos
          (sliceFriedrichsRep μG ρ hN2 hρcont hN β
            hpos f).toSub v.toSub
        + (1 : ℂ) * inner ℂ (sliceFriedrichsRep μG ρ
            hN2 hρcont hN β hpos f).val v.val
      = inner ℂ (sliceFriedrichsRep μG ρ hN2 hρcont
            hN β hpos f).val v.val
        + sliceFormB μG ρ hN2 hρcont hN β hpos
            (sliceFriedrichsRep μG ρ hN2 hρcont hN β
              hpos f).toSub v.toSub
    rw [one_mul, add_comm]
  rw [h1, sliceFriedrichsRep_spec μG ρ hN2 hρcont hN
    β hpos, sliceFormDomain.val_ofSub μG ρ hN2 hρcont
    hN β hpos, sliceFormDomainLam.val_eq μG ρ hN2
    hρcont hN β hpos 1 hlam]

/-- **CONSISTENCY AT `λ = 1`**: the resolvent at
weight one IS FG-2b's `sliceFriedrichsResolventLin` —
the actions agree on every input. -/
theorem sliceResolvent_one_apply (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (hlam : (0 : ℝ) < 1)
    (f : ↥(sliceFormClosure μG ρ hN2 hρcont hN β
      hpos)) :
    sliceResolventLin μG ρ hN2 hρcont hN β hpos 1
        hlam f
      = sliceFriedrichsResolventLin μG ρ hN2 hρcont
          hN β hpos f := by
  apply Subtype.ext
  rw [sliceResolventLin_apply μG ρ hN2 hρcont hN β
      hpos 1 hlam f,
    sliceResolvent_coe μG ρ hN2 hρcont hN β hpos 1
      hlam f,
    sliceResolventRep_one μG ρ hN2 hρcont hN β hpos
      hlam f,
    sliceFormDomainLam.val_ofSub μG ρ hN2 hρcont hN β
      hpos 1 hlam,
    sliceFriedrichsResolventLin_apply μG ρ hN2 hρcont
      hN β hpos f,
    sliceFriedrichsResolvent_coe μG ρ hN2 hρcont hN β
      hpos f,
    sliceFormDomain.val_eq μG ρ hN2 hρcont hN β
      hpos]

/-! ## §5. The vacuum at weight `λ` -/

/-- The `λ`-representative of the scaled vacuum
`(λ:ℂ) • Ω` is the transferred vacuum form-domain
element — the form part vanishes on the vacuum
(`sliceFormB_vacuum_left`) and the mass term
`λ⟪Ω, ·⟫` is exactly the pairing. -/
theorem sliceResolventRep_vacuum_smul (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (lam : ℝ)
    (hlam : 0 < lam) (hd : 0 < d) :
    sliceResolventRep μG ρ hN2 hρcont hN β hpos lam
        hlam
        ((lam : ℂ) • ⟨sliceOmegaCompleted μG ρ hN2
          hρcont hN β hpos hd,
          sliceFormDomain_le_closure μG ρ hN2 hρcont
            hN β hpos
            (sliceHamC_vacuum_mem_domain μG ρ hN2
              hρcont hN β hpos hd)⟩)
      = sliceFormDomainLam.ofSub μG ρ hN2 hρcont hN β
          hpos lam hlam
          ⟨sliceOmegaCompleted μG ρ hN2 hρcont hN β
            hpos hd,
            sliceHamC_vacuum_mem_domain μG ρ hN2
              hρcont hN β hpos hd⟩ := by
  apply sliceResolventRep_unique μG ρ hN2 hρcont hN β
    hpos lam hlam
  intro v
  rw [sliceResolventRep_spec μG ρ hN2 hρcont hN β
    hpos lam hlam]
  have hF : sliceFormInnerLam μG ρ hN2 hρcont hN β
        hpos lam hlam
        (sliceFormDomainLam.ofSub μG ρ hN2 hρcont hN
          β hpos lam hlam
          ⟨sliceOmegaCompleted μG ρ hN2 hρcont hN β
            hpos hd,
            sliceHamC_vacuum_mem_domain μG ρ hN2
              hρcont hN β hpos hd⟩) v
      = sliceFormB μG ρ hN2 hρcont hN β hpos
          ⟨sliceOmegaCompleted μG ρ hN2 hρcont hN β
            hpos hd,
            sliceHamC_vacuum_mem_domain μG ρ hN2
              hρcont hN β hpos hd⟩ v.toSub
        + (lam : ℂ) * inner ℂ (sliceOmegaCompleted μG
            ρ hN2 hρcont hN β hpos hd) v.val := rfl
  have hB0 : sliceFormB μG ρ hN2 hρcont hN β hpos
      ⟨sliceOmegaCompleted μG ρ hN2 hρcont hN β hpos
        hd,
        sliceHamC_vacuum_mem_domain μG ρ hN2 hρcont
          hN β hpos hd⟩ v.toSub = 0 :=
    sliceFormB_vacuum_left μG ρ hN2 hρcont hN β hpos
      hd (sliceFormDomain.ofSub μG ρ hN2 hρcont hN β
        hpos v.toSub)
  rw [hF, hB0, zero_add, Submodule.coe_smul,
    inner_smul_left]
  congr 1
  simp only [Complex.conj_ofReal]

/-- **THE VACUUM AT WEIGHT `λ`**: `R_λ Ω = λ⁻¹ • Ω`
— the vacuum is an eigenvector of the resolvent with
eigenvalue `1/λ`, because `ĤΩ = 0`. -/
theorem sliceResolvent_vacuum (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (lam : ℝ)
    (hlam : 0 < lam) (hd : 0 < d) :
    sliceResolventLin μG ρ hN2 hρcont hN β hpos lam
        hlam
        ⟨sliceOmegaCompleted μG ρ hN2 hρcont hN β
          hpos hd,
          sliceFormDomain_le_closure μG ρ hN2 hρcont
            hN β hpos
            (sliceHamC_vacuum_mem_domain μG ρ hN2
              hρcont hN β hpos hd)⟩
      = ((lam : ℂ))⁻¹ • ⟨sliceOmegaCompleted μG ρ
          hN2 hρcont hN β hpos hd,
          sliceFormDomain_le_closure μG ρ hN2 hρcont
            hN β hpos
            (sliceHamC_vacuum_mem_domain μG ρ hN2
              hρcont hN β hpos hd)⟩ := by
  have h1 : (lam : ℂ) • sliceResolventLin μG ρ hN2
        hρcont hN β hpos lam hlam
        ⟨sliceOmegaCompleted μG ρ hN2 hρcont hN β
          hpos hd,
          sliceFormDomain_le_closure μG ρ hN2 hρcont
            hN β hpos
            (sliceHamC_vacuum_mem_domain μG ρ hN2
              hρcont hN β hpos hd)⟩
      = ⟨sliceOmegaCompleted μG ρ hN2 hρcont hN β
          hpos hd,
          sliceFormDomain_le_closure μG ρ hN2 hρcont
            hN β hpos
            (sliceHamC_vacuum_mem_domain μG ρ hN2
              hρcont hN β hpos hd)⟩ := by
    rw [← map_smul]
    apply Subtype.ext
    rw [sliceResolventLin_apply μG ρ hN2 hρcont hN β
        hpos lam hlam,
      sliceResolvent_coe μG ρ hN2 hρcont hN β hpos lam
        hlam,
      sliceResolventRep_vacuum_smul μG ρ hN2 hρcont
        hN β hpos lam hlam hd]
    rfl
  calc sliceResolventLin μG ρ hN2 hρcont hN β hpos
        lam hlam
        ⟨sliceOmegaCompleted μG ρ hN2 hρcont hN β
          hpos hd,
          sliceFormDomain_le_closure μG ρ hN2 hρcont
            hN β hpos
            (sliceHamC_vacuum_mem_domain μG ρ hN2
              hρcont hN β hpos hd)⟩
      = ((lam : ℂ))⁻¹ • ((lam : ℂ)
          • sliceResolventLin μG ρ hN2 hρcont hN β
            hpos lam hlam
            ⟨sliceOmegaCompleted μG ρ hN2 hρcont hN β
              hpos hd,
              sliceFormDomain_le_closure μG ρ hN2
                hρcont hN β hpos
                (sliceHamC_vacuum_mem_domain μG ρ hN2
                  hρcont hN β hpos hd)⟩) := by
        rw [smul_smul,
          inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr
            hlam.ne'), one_smul]
    _ = ((lam : ℂ))⁻¹ • ⟨sliceOmegaCompleted μG ρ
          hN2 hρcont hN β hpos hd,
          sliceFormDomain_le_closure μG ρ hN2 hρcont
            hN β hpos
            (sliceHamC_vacuum_mem_domain μG ρ hN2
              hρcont hN β hpos hd)⟩ := by
        rw [h1]

/-! ## §6. Packages; the free temperature; the circle -/

/-- **The FG-2c-1 package** (a `Prop`): at every
weight `λ > 0` on the FG-2b carrier — (i) the
`λ`-form Hilbert space is complete (norm transport
from `J_1`); (ii) the Riesz representative solves
the weak resolvent equation `J_λ(u_f, v) = ⟪f, v⟫`;
(iii) the resolvent bound `‖R_λ‖ ≤ λ⁻¹`; (iv)
symmetry of the ambient pairing; (v) DOMAIN
INDEPENDENCE `range R_λ = dom(Ĥ)`; (vi) the operator
equation `(Ĥ + λ)u = f` at resolvent values; (vii)
surjectivity of `Ĥ + λ`; (viii) consistency at
`λ = 1` with FG-2b's resolvent; (ix) the vacuum law
`R_λ Ω = λ⁻¹ • Ω`; (x) positivity of the resolvent
pairing. -/
def sliceResolventPackage (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (hd : 0 < d) : Prop :=
  (∀ lam : ℝ, ∀ hlam : 0 < lam,
    CompleteSpace (sliceFormDomainLam μG ρ hN2
      hρcont hN β hpos lam hlam))
  ∧ (∀ lam : ℝ, ∀ hlam : 0 < lam,
    ∀ f : ↥(sliceFormClosure μG ρ hN2 hρcont hN β
        hpos),
    ∀ v : sliceFormDomainLam μG ρ hN2 hρcont hN β
        hpos lam hlam,
      sliceFormInnerLam μG ρ hN2 hρcont hN β hpos
          lam hlam
          (sliceResolventRep μG ρ hN2 hρcont hN β
            hpos lam hlam f) v
        = inner ℂ f.1 v.val)
  ∧ (∀ lam : ℝ, ∀ hlam : 0 < lam,
    ∀ f : ↥(sliceFormClosure μG ρ hN2 hρcont hN β
        hpos),
      ‖sliceResolventLin μG ρ hN2 hρcont hN β hpos
          lam hlam f‖ ≤ lam⁻¹ * ‖f‖)
  ∧ (∀ lam : ℝ, ∀ hlam : 0 < lam,
    ∀ f g : ↥(sliceFormClosure μG ρ hN2 hρcont hN β
        hpos),
      inner ℂ (sliceResolvent μG ρ hN2 hρcont hN β
          hpos lam hlam f).1 g.1
        = inner ℂ f.1 (sliceResolvent μG ρ hN2
            hρcont hN β hpos lam hlam g).1)
  ∧ (∀ lam : ℝ, ∀ hlam : 0 < lam,
      LinearMap.range (sliceResolventLin μG ρ hN2
          hρcont hN β hpos lam hlam)
        = sliceHamOperatorDomain μG ρ hN2 hρcont hN
          β hpos)
  ∧ (∀ lam : ℝ, ∀ hlam : 0 < lam,
    ∀ u : ↥(sliceHamOperatorDomain μG ρ hN2 hρcont
        hN β hpos),
    ∀ f : ↥(sliceFormClosure μG ρ hN2 hρcont hN β
        hpos),
      sliceResolventLin μG ρ hN2 hρcont hN β hpos
          lam hlam f = u.1
        → sliceHamOperator μG ρ hN2 hρcont hN β
            hpos u + (lam : ℂ) • u.1 = f)
  ∧ (∀ lam : ℝ, ∀ hlam : 0 < lam,
    ∀ f : ↥(sliceFormClosure μG ρ hN2 hρcont hN β
        hpos),
      ∃ u : ↥(sliceHamOperatorDomain μG ρ hN2
          hρcont hN β hpos),
        sliceHamOperator μG ρ hN2 hρcont hN β hpos u
            + (lam : ℂ) • u.1 = f)
  ∧ (∀ hlam : (0 : ℝ) < 1,
    ∀ f : ↥(sliceFormClosure μG ρ hN2 hρcont hN β
        hpos),
      sliceResolventLin μG ρ hN2 hρcont hN β hpos 1
          hlam f
        = sliceFriedrichsResolventLin μG ρ hN2
            hρcont hN β hpos f)
  ∧ (∀ lam : ℝ, ∀ hlam : 0 < lam,
      sliceResolventLin μG ρ hN2 hρcont hN β hpos
          lam hlam
          ⟨sliceOmegaCompleted μG ρ hN2 hρcont hN β
            hpos hd,
            sliceFormDomain_le_closure μG ρ hN2
              hρcont hN β hpos
              (sliceHamC_vacuum_mem_domain μG ρ hN2
                hρcont hN β hpos hd)⟩
        = ((lam : ℂ))⁻¹ • ⟨sliceOmegaCompleted μG ρ
            hN2 hρcont hN β hpos hd,
            sliceFormDomain_le_closure μG ρ hN2
              hρcont hN β hpos
              (sliceHamC_vacuum_mem_domain μG ρ hN2
                hρcont hN β hpos hd)⟩)
  ∧ (∀ lam : ℝ, ∀ hlam : 0 < lam,
    ∀ f : ↥(sliceFormClosure μG ρ hN2 hρcont hN β
        hpos),
      0 ≤ (inner ℂ f (sliceResolventLin μG ρ hN2
        hρcont hN β hpos lam hlam f)).re)

/-- **The FG-2c-1 package holds** at general
`(G, ρ)` under the standing positivity hypothesis
(needs `0 < d` only for the vacuum clause). -/
theorem sliceResolvent_package (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (hd : 0 < d) :
    sliceResolventPackage μG ρ hN2 hρcont hN β hpos
      hd :=
  ⟨fun lam hlam => sliceFormDomainLamCompleteSpace
      μG ρ hN2 hρcont hN β hpos lam hlam,
   fun lam hlam => sliceResolventRep_spec μG ρ hN2
     hρcont hN β hpos lam hlam,
   fun lam hlam => sliceResolvent_norm_le μG ρ hN2
     hρcont hN β hpos lam hlam,
   fun lam hlam => sliceResolvent_symmetric μG ρ hN2
     hρcont hN β hpos lam hlam,
   fun lam hlam => sliceResolvent_range_eq μG ρ hN2
     hρcont hN β hpos lam hlam,
   fun lam hlam => sliceHamOperator_add_lam_smul μG
     ρ hN2 hρcont hN β hpos lam hlam,
   fun lam hlam => sliceHamOperator_add_lam_surjective
     μG ρ hN2 hρcont hN β hpos lam hlam,
   fun hlam => sliceResolvent_one_apply μG ρ hN2
     hρcont hN β hpos hlam,
   fun lam hlam => sliceResolvent_vacuum μG ρ hN2
     hρcont hN β hpos lam hlam hd,
   fun lam hlam => sliceResolvent_pairing_nonneg μG
     ρ hN2 hρcont hN β hpos lam hlam⟩

/-- **The circle package**: the whole FG-2c-1
package at the circle seat (`G = Circle`,
`ρ = circleRep`), hypothesis-free at every
`β ≥ 0`. -/
theorem sliceResolvent_circle_package (hN2 : 2 ≤ N)
    (hN : Even N) (β : ℝ) (hβ : 0 ≤ β) :
    sliceResolventPackage (haarProb Circle) circleRep
      hN2 circleRep_continuous hN β
      (sliceHPosOne_circle hN2 hN β hβ)
      zero_lt_one :=
  sliceResolvent_package (haarProb Circle) circleRep
    hN2 circleRep_continuous hN β
    (sliceHPosOne_circle hN2 hN β hβ) zero_lt_one

/-- The `λ`-representative of the scaled datum
`(λ:ℂ) • f` at `β = 0` is the transferred whole-space
element of `f` itself: at zero temperature the form
vanishes and only the mass term speaks
(`sliceFormB_beta_zero`). -/
theorem sliceResolventRep_beta_zero_smul
    (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (hd : 0 < d) (lam : ℝ)
    (hlam : 0 < lam)
    (f : ↥(sliceFormClosure μG ρ hN2 hρcont hN 0
      (sliceHPosOne_zero μG ρ hN2 hρcont hN hd))) :
    sliceResolventRep μG ρ hN2 hρcont hN 0
        (sliceHPosOne_zero μG ρ hN2 hρcont hN hd) lam
        hlam ((lam : ℂ) • f)
      = sliceFormDomainLam.ofSub μG ρ hN2 hρcont hN 0
          (sliceHPosOne_zero μG ρ hN2 hρcont hN hd)
          lam hlam
          ⟨f.1, sliceFormDomain_beta_zero_top μG ρ
            hN2 hρcont hN hd f.1⟩ := by
  apply sliceResolventRep_unique μG ρ hN2 hρcont hN 0
    (sliceHPosOne_zero μG ρ hN2 hρcont hN hd) lam
    hlam
  intro v
  rw [sliceResolventRep_spec μG ρ hN2 hρcont hN 0
    (sliceHPosOne_zero μG ρ hN2 hρcont hN hd) lam
    hlam]
  have hF : sliceFormInnerLam μG ρ hN2 hρcont hN 0
        (sliceHPosOne_zero μG ρ hN2 hρcont hN hd) lam
        hlam
        (sliceFormDomainLam.ofSub μG ρ hN2 hρcont hN
          0 (sliceHPosOne_zero μG ρ hN2 hρcont hN hd)
          lam hlam
          ⟨f.1, sliceFormDomain_beta_zero_top μG ρ
            hN2 hρcont hN hd f.1⟩) v
      = sliceFormB μG ρ hN2 hρcont hN 0
          (sliceHPosOne_zero μG ρ hN2 hρcont hN hd)
          ⟨f.1, sliceFormDomain_beta_zero_top μG ρ
            hN2 hρcont hN hd f.1⟩ v.toSub
        + (lam : ℂ) * inner ℂ f.1 v.val := rfl
  rw [hF, sliceFormB_beta_zero μG ρ hN2 hρcont hN hd
    _ v.toSub, zero_add, Submodule.coe_smul,
    inner_smul_left]
  congr 1
  simp only [Complex.conj_ofReal]

/-- **The `β = 0` package**: at zero temperature the
resolvent is scalar at every weight,
`R_λ = λ⁻¹ • id` on the whole space — the
Hamiltonian is zero (FG-2b), so `(Ĥ + λ)⁻¹ = λ⁻¹`. -/
theorem sliceResolvent_beta_zero (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (hd : 0 < d) (lam : ℝ)
    (hlam : 0 < lam)
    (f : ↥(sliceFormClosure μG ρ hN2 hρcont hN 0
      (sliceHPosOne_zero μG ρ hN2 hρcont hN hd))) :
    sliceResolventLin μG ρ hN2 hρcont hN 0
        (sliceHPosOne_zero μG ρ hN2 hρcont hN hd) lam
        hlam f
      = ((lam : ℂ))⁻¹ • f := by
  have h1 : (lam : ℂ) • sliceResolventLin μG ρ hN2
        hρcont hN 0
        (sliceHPosOne_zero μG ρ hN2 hρcont hN hd) lam
        hlam f
      = f := by
    rw [← map_smul]
    apply Subtype.ext
    rw [sliceResolventLin_apply μG ρ hN2 hρcont hN 0
        (sliceHPosOne_zero μG ρ hN2 hρcont hN hd) lam
        hlam,
      sliceResolvent_coe μG ρ hN2 hρcont hN 0
        (sliceHPosOne_zero μG ρ hN2 hρcont hN hd) lam
        hlam,
      sliceResolventRep_beta_zero_smul μG ρ hN2
        hρcont hN hd lam hlam f]
    rfl
  calc sliceResolventLin μG ρ hN2 hρcont hN 0
        (sliceHPosOne_zero μG ρ hN2 hρcont hN hd) lam
        hlam f
      = ((lam : ℂ))⁻¹ • ((lam : ℂ)
          • sliceResolventLin μG ρ hN2 hρcont hN 0
            (sliceHPosOne_zero μG ρ hN2 hρcont hN hd)
            lam hlam f) := by
        rw [smul_smul,
          inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr
            hlam.ne'), one_smul]
    _ = ((lam : ℂ))⁻¹ • f := by
        rw [h1]

end SliceResolvent

end ThetLogos
