/-
# FG-2b — THE FRIEDRICHS CONSTRUCTION: the Hamiltonian from
# the closed form, via Riesz

Brick FG-2b of the frontier gate paper
(`whitepaper/frontier-gate-scoping-2026-10-25.md`, §2.2): the
second brick of the FG-2 hand-built unbounded-operator
project. PLACEMENT LABEL (consumed from the gate, not
re-decided here): this is a **Stage 2 completeness** item —
it finishes the operator seat of S2-4(b) at fixed volume. It
is NOT frontier progress: Items 3 (uniform estimates) and 4
(continuum) are untouched, and nothing here moves any dial.
Dials 0/4. NO CLAIM.

## What this brick consumes

* FG-2a (`LatticeSliceFormClosed`): the completed form
  `sliceHamFormC` is CLOSED — its domain
  `sliceFormDomain`, with the form inner product
  `⟪x, y⟫ + sliceFormB x y`, is a Hilbert space
  (`sliceFormDomainCompleteSpace`), and the inclusion into
  the completed space is a CLM of bound `1`
  (`sliceFormInclusion`). Also consumed: the proved density
  obstruction `sliceFormDomain_orthogonal_ker` (the form
  domain lies inside `(ker T̂_c)⊥`).
* S2-4(b) (`LatticeSliceOperator`): the completed Hilbert
  space, the completed transfer operator `sliceHatCompleted`
  (self-adjoint contraction), the completed vacuum
  `sliceOmegaCompleted` (fixed by `T̂_c`, invisible to the
  form, in the form domain).
* Mathlib's Fréchet–Riesz representation
  (`InnerProductSpace.toDual`): the one engine of the
  classical Friedrichs / Kato first representation theorem
  that Mathlib supplies. The rest of the classical theorem
  (an unbounded-operator typeclass, a Friedrichs
  representation theorem, a Borel functional calculus) does
  not exist in the pinned Mathlib; this brick builds what
  the theorem's proof builds, with the operator carried as
  a linear map on its domain submodule — the honest
  Mathlib-available form, named as such below.

## Step 0 (the FG-2a density residue): OBSTRUCTED, named

The commission's step 0 asked for density of the form
domain inside `(ker T̂_c)⊥` via the truncations
`p_n(T̂_c) = 1 − A_c^n`. Every route reduces to the mixed
form inequality `(⟪x, T̂_c A_c^j x⟫).re ≥ 0` — equivalently
monotonicity of the defect pairings `a_j = (⟪x, A_c^j x⟫).re`,
equivalently `(⟪x, T̂_c² x⟫).re ≤ (⟪x, T̂_c x⟫).re` (form
order `T̂_c² ≤ T̂_c`). The landed record contains the pure
pairings only: factored positivity of `T̂_c`
(`sliceHatCompletedFun_inner_nonneg`) and the defect
iterates (`sliceHamCompletedDefect_iter_diag`); NO mixed
pairing and NO monotonicity is landed, and self-adjoint +
contraction + factored positivity do not yield `T̂² ≤ T̂`
without a spectral theorem, a bounded-operator functional
calculus assembled for `sliceHatCompleted`, or a completed
weld factorization (S2-5's `W` lives on the quotient, valued
in `osSpace`; no completed weld is landed). Per the
commission, step 0 stops here with the obstruction named;
it does not burn the brick.

## The carrier (step 1's licensed choice)

The construction runs on

  `H' := sliceFormClosure` = the closure of the form
  domain inside the completed Hilbert space.

On this carrier NO density hypothesis is needed anywhere:
density of the form domain in `H'` is by construction, and
FG-2a gives `H' ⊆ (ker T̂_c)⊥`. The unproved residue is
exactly the equality `H' = (ker T̂_c)⊥` (equivalent to the
step-0 density clause); it is recorded here as a residue,
NOT carried as a hypothesis, because no clause of the
construction consumes it.

## What it delivers

* The resolvent at the Friedrichs seat `λ = 1`: for
  `f ∈ H'`, the Riesz representative `sliceFriedrichsRep f`
  of the functional `v ↦ ⟪f, v⟫` on the form Hilbert space,
  its characterization, the resolvent
  `sliceFriedrichsResolvent` (a CLM `H' →L[ℂ] H'` of bound
  `1`), symmetric, injective, with range characterized
  (§2, §3).
* The Hamiltonian `sliceHamOperator`: a linear map on the
  domain submodule `D(Ĥ) := range R`, defined by
  `Ĥ (R f) = f − R f`. It is symmetric, positive with the
  exact diagonal `⟪Ĥu, u⟫ = form(u)`, and satisfies the
  FORM IDENTITY `sliceFormB u v = ⟪Ĥu, v⟫` on the form
  domain — Kato's first representation theorem, in the
  parts Mathlib's Riesz engine supports (§4).
* Self-adjointness in the resolvent sense:
  `range(Ĥ + 1) = ⊤` of `H'`, by construction (the Riesz
  assignment is defined on all of `H'`) (§4).
* The vacuum: `Ω ∈ D(Ĥ)` with `Ĥ Ω = 0` (§5).
* Packages: general `(G, ρ)` under exactly `SliceHPosOne`;
  the U(1) seat hypothesis-free at `β ≥ 0`; at `β = 0` the
  form vanishes, `H'` is the whole space, `R = id` and
  `Ĥ = 0` (§6).

## What is named, NOT asserted

* NO typeclass self-adjointness for `Ĥ`: Mathlib reserves
  `IsSelfAdjoint` / the adjoint machinery for bounded,
  everywhere-defined operators (and `LinearPMap` adjoints
  are a different, unconnected formalism). What is proved
  is the resolvent-sense statement: `Ĥ` is symmetric on its
  domain and `Ĥ + 1` is surjective onto `H'` — the
  classical content of self-adjointness for the Friedrichs
  operator at the seat `λ = 1`.
* NO semigroup identification `exp(−Ĥ) = T̂_c` (that is
  FG-2c, uncommissioned here), no `Ĥ^{1/2}`, no spectral
  statement about `Ĥ`.
* NO equality `H' = (ker T̂_c)⊥` (the step-0 residue,
  above); `H'` is the closure of the form domain, full
  stop.
* NO positivity beyond landed labels; TM R2 untouched;
  Stage 1b-B untouched.

NO CLAIM; Clay parts closed: 0.
-/

import ThetLogos.LatticeSliceFormClosed

namespace ThetLogos

open MeasureTheory Finset
open scoped Matrix ENNReal NNReal InnerProduct

section SliceFriedrichs

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ))
  {N : ℕ} [NeZero N]

/-! ## §1. The carrier `H'` -/

/-- **The Friedrichs carrier** `H'`: the closure of the
completed form domain inside the completed Hilbert space.
The Friedrichs construction runs on `H'`; the form domain
is dense in `H'` by construction, and `H' ⊆ (ker T̂_c)⊥`
by FG-2a's obstruction theorem. Equality
`H' = (ker T̂_c)⊥` is NOT asserted (step-0 residue). -/
noncomputable def sliceFormClosure (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) :
    Submodule ℂ (sliceHilbertSpace μG ρ hN2 hρcont hN β
      hpos) :=
  (sliceHamFormDomainC μG ρ hN2 hρcont hN β
    hpos).topologicalClosure

/-- The form domain sits inside its closure. -/
theorem sliceFormDomain_le_closure (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) :
    sliceHamFormDomainC μG ρ hN2 hρcont hN β hpos
      ≤ sliceFormClosure μG ρ hN2 hρcont hN β hpos := by
  show sliceHamFormDomainC μG ρ hN2 hρcont hN β hpos
    ≤ (sliceHamFormDomainC μG ρ hN2 hρcont hN β
      hpos).topologicalClosure
  exact (sliceHamFormDomainC μG ρ hN2 hρcont hN β
    hpos).le_topologicalClosure

/-- Membership in the carrier is closure membership in the
ambient space. -/
theorem sliceFormClosure_mem_iff (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (x : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos) :
    x ∈ sliceFormClosure μG ρ hN2 hρcont hN β hpos
      ↔ x ∈ closure (sliceHamFormDomainC μG ρ hN2 hρcont
          hN β hpos : Set (sliceHilbertSpace μG ρ hN2
            hρcont hN β hpos)) :=
  Iff.rfl

/-- The inner product on the carrier is the ambient inner
product of the underlying vectors. -/
theorem sliceFormClosure_inner (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (x y : ↥(sliceFormClosure μG ρ hN2 hρcont hN β
      hpos)) :
    inner ℂ x y = inner ℂ x.1 y.1 :=
  rfl

/-- The carrier is a Hilbert space in its own right: a
closed subspace of a complete space. -/
theorem sliceFormClosure_completeSpace (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) :
    CompleteSpace ↥(sliceFormClosure μG ρ hN2 hρcont hN β
      hpos) :=
  (Submodule.isClosed_topologicalClosure _).isComplete
    |>.completeSpace_coe

/-- **Density of the form domain in the carrier** — by
construction of `H'` as the closure: every point of `H'`
is approximated in the ambient norm by form-domain
vectors. (Density inside the possibly larger
`(ker T̂_c)⊥` is the step-0 residue, not asserted.) -/
theorem sliceFormClosure_dense (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (z : ↥(sliceFormClosure μG ρ hN2 hρcont hN β hpos))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ x : sliceFormDomain μG ρ hN2 hρcont hN β hpos,
      dist z.1 x.val < ε := by
  have hz : z.1 ∈ closure (sliceHamFormDomainC μG ρ hN2
      hρcont hN β hpos : Set (sliceHilbertSpace μG ρ hN2
        hρcont hN β hpos)) := z.2
  rw [Metric.mem_closure_iff] at hz
  obtain ⟨y, hy, hdy⟩ := hz ε hε
  refine ⟨sliceFormDomain.ofSub μG ρ hN2 hρcont hN β hpos
    ⟨y, hy⟩, ?_⟩
  rw [sliceFormDomain.val_ofSub]
  exact hdy

/-- **The carrier lies inside `(ker T̂_c)⊥`**: FG-2a's
obstruction theorem, transported across the closure — the
vanishing set of the pairing against a fixed vector is
closed and contains the form domain. -/
theorem sliceFormClosure_orthogonal_ker (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (z : ↥(sliceFormClosure μG ρ hN2 hρcont hN β hpos))
    {w : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos}
    (hw : sliceHatCompleted μG ρ hN2 hρcont hN β hpos w
      = 0) :
    inner ℂ z.1 w = 0 := by
  have hsub : (sliceHamFormDomainC μG ρ hN2 hρcont hN β
        hpos : Set (sliceHilbertSpace μG ρ hN2 hρcont hN
          β hpos))
      ⊆ {x | inner ℂ x w = 0} := by
    intro x hx
    exact sliceFormDomain_orthogonal_ker μG ρ hN2 hρcont
      hN β hpos hx hw
  have hclosed : IsClosed
      {x : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos |
        inner ℂ x w = 0} :=
    isClosed_eq (continuous_id.inner continuous_const)
      continuous_const
  have hz : z.1 ∈ closure (sliceHamFormDomainC μG ρ hN2
      hρcont hN β hpos : Set (sliceHilbertSpace μG ρ hN2
        hρcont hN β hpos)) := z.2
  exact closure_minimal hsub hclosed hz

/-! ## §2. The Riesz representative -/

/-- The class inner product of the form domain (FG-2a's
Hilbert-space instance) is the form inner product
`⟪x, y⟫ + sliceFormB x y`. -/
theorem sliceFormDomain_inner_eq (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (x y : sliceFormDomain μG ρ hN2 hρcont hN β hpos) :
    inner ℂ x y
      = sliceFormInner μG ρ hN2 hρcont hN β hpos x y :=
  rfl

/-- **The pairing functional of `f ∈ H'`** on the form
Hilbert space: `v ↦ ⟪f, v⟫`, continuous by the FG-2a
inclusion bound `‖v‖ ≤ ‖v‖_form`. This is the functional
the Friedrichs argument feeds to Riesz. -/
noncomputable def sliceFriedrichsFunctional (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (f : ↥(sliceFormClosure μG ρ hN2 hρcont hN β hpos)) :
    sliceFormDomain μG ρ hN2 hρcont hN β hpos →L[ℂ] ℂ :=
  (innerSL ℂ f.1).comp
    (sliceFormInclusion μG ρ hN2 hρcont hN β hpos)

theorem sliceFriedrichsFunctional_apply (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (f : ↥(sliceFormClosure μG ρ hN2 hρcont hN β hpos))
    (v : sliceFormDomain μG ρ hN2 hρcont hN β hpos) :
    sliceFriedrichsFunctional μG ρ hN2 hρcont hN β hpos f v
      = inner ℂ f.1 v.val :=
  rfl

/-- **The Riesz representative**: the unique form-domain
vector `u_f` with `⟪u_f, v⟫_form = ⟪f, v⟫` for all `v` —
existence and uniqueness are Mathlib's Fréchet–Riesz
theorem (`InnerProductSpace.toDual`) applied to the
FG-2a form Hilbert space. -/
noncomputable def sliceFriedrichsRep (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (f : ↥(sliceFormClosure μG ρ hN2 hρcont hN β hpos)) :
    sliceFormDomain μG ρ hN2 hρcont hN β hpos :=
  (InnerProductSpace.toDual ℂ
    (sliceFormDomain μG ρ hN2 hρcont hN β hpos)).symm
    (sliceFriedrichsFunctional μG ρ hN2 hρcont hN β hpos f)

/-- **The Riesz characterization** of the representative:
the form inner product against any form-domain vector is
the ambient pairing with `f`. At `λ = 1` this is the
resolvent equation `(Ĥ + 1) u_f = f` in weak form. -/
theorem sliceFriedrichsRep_spec (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (f : ↥(sliceFormClosure μG ρ hN2 hρcont hN β hpos))
    (v : sliceFormDomain μG ρ hN2 hρcont hN β hpos) :
    sliceFormInner μG ρ hN2 hρcont hN β hpos
        (sliceFriedrichsRep μG ρ hN2 hρcont hN β hpos f) v
      = inner ℂ f.1 v.val := by
  have h := InnerProductSpace.toDual_symm_apply (𝕜 := ℂ)
    (E := sliceFormDomain μG ρ hN2 hρcont hN β hpos)
    (x := v) (y := sliceFriedrichsFunctional μG ρ hN2
      hρcont hN β hpos f)
  show inner ℂ (sliceFriedrichsRep μG ρ hN2 hρcont hN β
      hpos f) v = inner ℂ f.1 v.val
  exact h

/-- Uniqueness of form-domain vectors by their form-inner
pairings — the definiteness that makes the Riesz
representative a well-defined function of `f`. -/
theorem sliceFriedrichsRep_unique (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    {u₁ u₂ : sliceFormDomain μG ρ hN2 hρcont hN β hpos}
    (h : ∀ v : sliceFormDomain μG ρ hN2 hρcont hN β hpos,
      sliceFormInner μG ρ hN2 hρcont hN β hpos u₁ v
        = sliceFormInner μG ρ hN2 hρcont hN β hpos u₂ v) :
    u₁ = u₂ := by
  have h' : ∀ v : sliceFormDomain μG ρ hN2 hρcont hN β
      hpos, inner ℂ u₁ v = inner ℂ u₂ v := fun v => h v
  have hsub : ∀ v : sliceFormDomain μG ρ hN2 hρcont hN β
      hpos, inner ℂ (u₁ - u₂) v = 0 := fun v => by
    rw [inner_sub_left, h' v, sub_self]
  have hself := hsub (u₁ - u₂)
  rw [inner_self_eq_zero] at hself
  exact sub_eq_zero.mp hself

/-! ## §3. The resolvent -/

/-- **The Friedrichs resolvent at `λ = 1`**, as a bare map
`H' → H'`: `R f` is the ambient vector of the Riesz
representative `u_f`, which lies in the form domain,
hence in its closure `H'`. -/
noncomputable def sliceFriedrichsResolvent (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (f : ↥(sliceFormClosure μG ρ hN2 hρcont hN β hpos)) :
    ↥(sliceFormClosure μG ρ hN2 hρcont hN β hpos) :=
  ⟨(sliceFriedrichsRep μG ρ hN2 hρcont hN β hpos
      f).toSub.1,
    sliceFormDomain_le_closure μG ρ hN2 hρcont hN β hpos
      (sliceFriedrichsRep μG ρ hN2 hρcont hN β hpos
        f).toSub.2⟩

/-- The resolvent's ambient vector is the representative's
ambient vector. -/
theorem sliceFriedrichsResolvent_coe (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (f : ↥(sliceFormClosure μG ρ hN2 hρcont hN β hpos)) :
    (sliceFriedrichsResolvent μG ρ hN2 hρcont hN β hpos
        f).1
      = (sliceFriedrichsRep μG ρ hN2 hρcont hN β hpos
          f).val :=
  rfl

/-- The Riesz representative is additive: the two
conjugate-linearities (of the pairing in `f`, of Riesz in
the functional) cancel. Proved by the characterization
plus uniqueness. -/
theorem sliceFriedrichsRep_add (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (f g : ↥(sliceFormClosure μG ρ hN2 hρcont hN β
      hpos)) :
    sliceFriedrichsRep μG ρ hN2 hρcont hN β hpos (f + g)
      = sliceFriedrichsRep μG ρ hN2 hρcont hN β hpos f
        + sliceFriedrichsRep μG ρ hN2 hρcont hN β hpos
            g := by
  apply sliceFriedrichsRep_unique μG ρ hN2 hρcont hN β
    hpos
  intro v
  rw [sliceFormInner_add_left μG ρ hN2 hρcont hN β hpos,
    sliceFriedrichsRep_spec μG ρ hN2 hρcont hN β hpos
      (f + g) v,
    sliceFriedrichsRep_spec μG ρ hN2 hρcont hN β hpos f v,
    sliceFriedrichsRep_spec μG ρ hN2 hρcont hN β hpos
      g v, Submodule.coe_add, inner_add_left]

/-- The Riesz representative is homogeneous, by the same
uniqueness argument. -/
theorem sliceFriedrichsRep_smul (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (c : ℂ)
    (f : ↥(sliceFormClosure μG ρ hN2 hρcont hN β hpos)) :
    sliceFriedrichsRep μG ρ hN2 hρcont hN β hpos (c • f)
      = c • sliceFriedrichsRep μG ρ hN2 hρcont hN β hpos
          f := by
  apply sliceFriedrichsRep_unique μG ρ hN2 hρcont hN β
    hpos
  intro v
  rw [sliceFormInner_smul_left μG ρ hN2 hρcont hN β hpos,
    sliceFriedrichsRep_spec μG ρ hN2 hρcont hN β hpos
      (c • f) v,
    sliceFriedrichsRep_spec μG ρ hN2 hρcont hN β hpos
      f v, Submodule.coe_smul, inner_smul_left]

/-- **The resolvent as a linear map** `H' →ₗ[ℂ] H'`. -/
noncomputable def sliceFriedrichsResolventLin
    (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) :
    ↥(sliceFormClosure μG ρ hN2 hρcont hN β hpos) →ₗ[ℂ]
      ↥(sliceFormClosure μG ρ hN2 hρcont hN β hpos) where
  toFun := sliceFriedrichsResolvent μG ρ hN2 hρcont hN β
    hpos
  map_add' := by
    intro f g
    apply Subtype.ext
    show (sliceFriedrichsRep μG ρ hN2 hρcont hN β hpos
          (f + g)).val
      = (sliceFriedrichsRep μG ρ hN2 hρcont hN β hpos
            f).val
        + (sliceFriedrichsRep μG ρ hN2 hρcont hN β hpos
            g).val
    rw [sliceFriedrichsRep_add μG ρ hN2 hρcont hN β hpos
        f g,
      sliceFormDomain.val_add μG ρ hN2 hρcont hN β hpos]
  map_smul' := by
    intro c f
    apply Subtype.ext
    show (sliceFriedrichsRep μG ρ hN2 hρcont hN β hpos
          (c • f)).val
      = c • (sliceFriedrichsRep μG ρ hN2 hρcont hN β
          hpos f).val
    rw [sliceFriedrichsRep_smul μG ρ hN2 hρcont hN β hpos
        c f,
      sliceFormDomain.val_smul μG ρ hN2 hρcont hN β hpos]

theorem sliceFriedrichsResolventLin_apply (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (f : ↥(sliceFormClosure μG ρ hN2 hρcont hN β hpos)) :
    sliceFriedrichsResolventLin μG ρ hN2 hρcont hN β hpos
        f
      = sliceFriedrichsResolvent μG ρ hN2 hρcont hN β
          hpos f :=
  rfl

/-- **Symmetry of the resolvent**: the ambient pairing
`⟪R f, g⟫ = ⟪f, R g⟫` — the conjugate-symmetry of the
form inner product, transported through the Riesz
characterization on both sides. -/
theorem sliceFriedrichsResolvent_symmetric (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (f g : ↥(sliceFormClosure μG ρ hN2 hρcont hN β
      hpos)) :
    inner ℂ (sliceFriedrichsResolvent μG ρ hN2 hρcont hN
        β hpos f).1 g.1
      = inner ℂ f.1 (sliceFriedrichsResolvent μG ρ hN2
          hρcont hN β hpos g).1 := by
  rw [sliceFriedrichsResolvent_coe μG ρ hN2 hρcont hN β
      hpos f,
    sliceFriedrichsResolvent_coe μG ρ hN2 hρcont hN β
      hpos g]
  have h1 := sliceFriedrichsRep_spec μG ρ hN2 hρcont hN
    β hpos g (sliceFriedrichsRep μG ρ hN2 hρcont hN β
      hpos f)
  have h2 := sliceFriedrichsRep_spec μG ρ hN2 hρcont hN
    β hpos f (sliceFriedrichsRep μG ρ hN2 hρcont hN β
      hpos g)
  have h3 : sliceFormInner μG ρ hN2 hρcont hN β hpos
        (sliceFriedrichsRep μG ρ hN2 hρcont hN β hpos f)
        (sliceFriedrichsRep μG ρ hN2 hρcont hN β hpos g)
      = (starRingEnd ℂ) (sliceFormInner μG ρ hN2 hρcont
          hN β hpos
          (sliceFriedrichsRep μG ρ hN2 hρcont hN β hpos
            g)
          (sliceFriedrichsRep μG ρ hN2 hρcont hN β hpos
            f)) :=
    (sliceFormInner_conj_symm μG ρ hN2 hρcont hN β hpos
      _ _).symm
  rw [h2, h1] at h3
  rw [h3, inner_conj_symm]

/-- **The resolvent bound** `‖R f‖ ≤ ‖f‖` at the seat
`λ = 1`: the form-norm estimate
`‖u_f‖²_form = ⟪f, u_f⟫ ≤ ‖f‖ · ‖u_f‖_form` (Cauchy–
Schwarz plus the inclusion bound), divided through. -/
theorem sliceFriedrichsResolvent_norm_le (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (f : ↥(sliceFormClosure μG ρ hN2 hρcont hN β hpos)) :
    ‖sliceFriedrichsResolventLin μG ρ hN2 hρcont hN β
        hpos f‖ ≤ ‖f‖ := by
  have hspec := sliceFriedrichsRep_spec μG ρ hN2 hρcont
    hN β hpos f (sliceFriedrichsRep μG ρ hN2 hρcont hN
      β hpos f)
  have hnorm : ‖sliceFriedrichsRep μG ρ hN2 hρcont hN β
        hpos f‖ ^ 2
      = (sliceFormInner μG ρ hN2 hρcont hN β hpos
          (sliceFriedrichsRep μG ρ hN2 hρcont hN β hpos
            f)
          (sliceFriedrichsRep μG ρ hN2 hρcont hN β hpos
            f)).re := by
    rw [sliceFormDomain_norm_sq μG ρ hN2 hρcont hN β
        hpos,
      sliceFormInner_self_re μG ρ hN2 hρcont hN β hpos]
  have hfnorm : ‖f.1‖ = ‖f‖ := rfl
  have hle : ‖sliceFriedrichsRep μG ρ hN2 hρcont hN β
        hpos f‖ ^ 2
      ≤ ‖f‖ * ‖sliceFriedrichsRep μG ρ hN2 hρcont hN β
          hpos f‖ := by
    rw [hnorm, hspec]
    calc (inner ℂ f.1 (sliceFriedrichsRep μG ρ hN2
            hρcont hN β hpos f).val).re
        ≤ ‖inner ℂ f.1 (sliceFriedrichsRep μG ρ hN2
            hρcont hN β hpos f).val‖ :=
          Complex.re_le_norm _
      _ ≤ ‖f‖ * ‖sliceFriedrichsRep μG ρ hN2 hρcont hN
            β hpos f‖ := by
          refine le_trans (norm_inner_le_norm _ _) ?_
          rw [hfnorm]
          exact mul_le_mul_of_nonneg_left
            (sliceFormDomain_val_norm_le μG ρ hN2 hρcont
              hN β hpos _) (norm_nonneg _)
  have hval : ‖(sliceFriedrichsResolventLin μG ρ hN2
        hρcont hN β hpos f).1‖
      ≤ ‖sliceFriedrichsRep μG ρ hN2 hρcont hN β hpos
          f‖ := by
    have hcoe : (sliceFriedrichsResolventLin μG ρ hN2
          hρcont hN β hpos f).1
        = (sliceFriedrichsRep μG ρ hN2 hρcont hN β hpos
            f).val := by
      rw [sliceFriedrichsResolventLin_apply μG ρ hN2
        hρcont hN β hpos f]
      exact sliceFriedrichsResolvent_coe μG ρ hN2 hρcont
        hN β hpos f
    rw [hcoe]
    exact sliceFormDomain_val_norm_le μG ρ hN2 hρcont hN
      β hpos _
  show ‖(sliceFriedrichsResolventLin μG ρ hN2 hρcont hN
      β hpos f).1‖ ≤ ‖f‖
  rcases eq_or_ne ‖sliceFriedrichsRep μG ρ hN2 hρcont hN
      β hpos f‖ 0 with hu0 | hu0
  · calc ‖(sliceFriedrichsResolventLin μG ρ hN2 hρcont
          hN β hpos f).1‖
        ≤ ‖sliceFriedrichsRep μG ρ hN2 hρcont hN β hpos
            f‖ := hval
      _ = 0 := hu0
      _ ≤ ‖f‖ := norm_nonneg f
  · have hpos' : 0 < ‖sliceFriedrichsRep μG ρ hN2
        hρcont hN β hpos f‖ :=
      lt_of_le_of_ne (norm_nonneg _) (Ne.symm hu0)
    have hu_le : ‖sliceFriedrichsRep μG ρ hN2 hρcont hN
        β hpos f‖ ≤ ‖f‖ := by
      have h2 : ‖sliceFriedrichsRep μG ρ hN2 hρcont hN
            β hpos f‖
          * ‖sliceFriedrichsRep μG ρ hN2 hρcont hN β
              hpos f‖
          ≤ ‖f‖ * ‖sliceFriedrichsRep μG ρ hN2 hρcont
              hN β hpos f‖ := by
        rwa [pow_two] at hle
      exact le_of_mul_le_mul_right h2 hpos'
    exact le_trans hval hu_le

/-- **The resolvent as a continuous linear map** of bound
`1` on `H'`. -/
noncomputable def sliceFriedrichsResolventCLM
    (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) :
    ↥(sliceFormClosure μG ρ hN2 hρcont hN β hpos) →L[ℂ]
      ↥(sliceFormClosure μG ρ hN2 hρcont hN β hpos) :=
  (sliceFriedrichsResolventLin μG ρ hN2 hρcont hN β
    hpos).mkContinuous 1 (fun f => by
      rw [one_mul]
      exact sliceFriedrichsResolvent_norm_le μG ρ hN2
        hρcont hN β hpos f)

theorem sliceFriedrichsResolventCLM_apply (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (f : ↥(sliceFormClosure μG ρ hN2 hρcont hN β hpos)) :
    sliceFriedrichsResolventCLM μG ρ hN2 hρcont hN β hpos
        f
      = sliceFriedrichsResolvent μG ρ hN2 hρcont hN β
          hpos f :=
  rfl

/-- **Range characterization of the resolvent**: `z` is
in the range iff `z` is the ambient vector of a
form-domain element `w` satisfying the resolvent
equation `⟪w, v⟫_form = ⟪f, v⟫` for some `f ∈ H'` — the
weak form of `(Ĥ + 1) w = f`. -/
theorem sliceFriedrichsResolvent_range (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (z : ↥(sliceFormClosure μG ρ hN2 hρcont hN β hpos)) :
    z ∈ LinearMap.range (sliceFriedrichsResolventLin μG
        ρ hN2 hρcont hN β hpos)
      ↔ ∃ w : sliceFormDomain μG ρ hN2 hρcont hN β hpos,
        ∃ f : ↥(sliceFormClosure μG ρ hN2 hρcont hN β
          hpos), w.val = z.1
          ∧ ∀ v : sliceFormDomain μG ρ hN2 hρcont hN β
              hpos,
            sliceFormInner μG ρ hN2 hρcont hN β hpos w v
              = inner ℂ f.1 v.val := by
  constructor
  · rintro ⟨f, rfl⟩
    refine ⟨sliceFriedrichsRep μG ρ hN2 hρcont hN β hpos
      f, f, ?_, fun v => sliceFriedrichsRep_spec μG ρ
        hN2 hρcont hN β hpos f v⟩
    rw [sliceFriedrichsResolventLin_apply μG ρ hN2
      hρcont hN β hpos f]
    exact (sliceFriedrichsResolvent_coe μG ρ hN2 hρcont
      hN β hpos f).symm
  · rintro ⟨w, f, hw, hspec⟩
    have hrep : sliceFriedrichsRep μG ρ hN2 hρcont hN β
        hpos f = w :=
      sliceFriedrichsRep_unique μG ρ hN2 hρcont hN β
        hpos (fun v => (sliceFriedrichsRep_spec μG ρ hN2
          hρcont hN β hpos f v).trans (hspec v).symm)
    refine ⟨f, ?_⟩
    apply Subtype.ext
    show (sliceFriedrichsResolvent μG ρ hN2 hρcont hN β
        hpos f).1 = z.1
    rw [sliceFriedrichsResolvent_coe μG ρ hN2 hρcont hN
      β hpos f, hrep]
    exact hw

/-- **Injectivity of the resolvent**: if `R f = 0` then
the representative is zero, so `f` pairs trivially with
the whole form domain; the pairing set is closed and the
domain dense in `H'`, so `f = 0`. -/
theorem sliceFriedrichsResolventLin_injective
    (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) :
    Function.Injective (sliceFriedrichsResolventLin μG ρ
      hN2 hρcont hN β hpos) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro f hf
  have h1 : (sliceFriedrichsRep μG ρ hN2 hρcont hN β
      hpos f).val = 0 := by
    have h2 := congrArg Subtype.val hf
    rw [sliceFriedrichsResolventLin_apply μG ρ hN2
      hρcont hN β hpos f,
      sliceFriedrichsResolvent_coe μG ρ hN2 hρcont hN β
        hpos f] at h2
    exact h2
  have hrep0 : sliceFriedrichsRep μG ρ hN2 hρcont hN β
      hpos f = 0 := by
    have hsub : (sliceFriedrichsRep μG ρ hN2 hρcont hN
        β hpos f).toSub = 0 := Subtype.ext h1
    have h0 : (0 : sliceFormDomain μG ρ hN2 hρcont hN β
        hpos).toSub = 0 :=
      sliceFormDomain.toSub_zero μG ρ hN2 hρcont hN β
        hpos
    exact sliceFormDomain.toSub_inj μG ρ hN2 hρcont hN
      β hpos (by rwa [← h0] at hsub)
  have hpair : ∀ v : sliceFormDomain μG ρ hN2 hρcont hN
      β hpos, inner ℂ f.1 v.val = 0 := by
    intro v
    have h := sliceFriedrichsRep_spec μG ρ hN2 hρcont
      hN β hpos f v
    rw [hrep0] at h
    have h0 : sliceFormInner μG ρ hN2 hρcont hN β hpos
        0 v = 0 := by
      have hz : inner ℂ (0 : sliceFormDomain μG ρ hN2
          hρcont hN β hpos) v = 0 :=
        inner_zero_left (𝕜 := ℂ) v
      exact hz
    rw [h0] at h
    exact h.symm
  have hsub2 : (sliceHamFormDomainC μG ρ hN2 hρcont hN
        β hpos : Set (sliceHilbertSpace μG ρ hN2 hρcont
          hN β hpos))
      ⊆ {x | inner ℂ f.1 x = 0} := by
    intro x hx
    show inner ℂ f.1 x = 0
    have h := hpair (sliceFormDomain.ofSub μG ρ hN2
      hρcont hN β hpos ⟨x, hx⟩)
    rwa [sliceFormDomain.val_ofSub μG ρ hN2 hρcont hN β
      hpos] at h
  have hclosed : IsClosed
      {x : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos |
        inner ℂ f.1 x = 0} :=
    isClosed_eq (continuous_const.inner continuous_id)
      continuous_const
  have hfmem : f.1
      ∈ {x : sliceHilbertSpace μG ρ hN2 hρcont hN β
          hpos | inner ℂ f.1 x = 0} :=
    closure_minimal hsub2 hclosed f.2
  have hself : inner ℂ f.1 f.1 = 0 := hfmem
  rw [inner_self_eq_zero] at hself
  exact Subtype.ext hself

/-! ## §4. The Hamiltonian -/

/-- **The operator domain** `D(Ĥ)`: the range of the
resolvent, as a submodule of `H'`. (An `abbrev`: the
resolvent's `LinearEquiv.ofInjective` lands in
`↥(range R)`, and the operator's assembly needs the two
presentations to unify on sight.) -/
noncomputable abbrev sliceHamOperatorDomain (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) :
    Submodule ℂ ↥(sliceFormClosure μG ρ hN2 hρcont hN β
      hpos) :=
  LinearMap.range (sliceFriedrichsResolventLin μG ρ hN2
    hρcont hN β hpos)

/-- **The Friedrichs Hamiltonian** `Ĥ`: the linear map on
`D(Ĥ)` with `Ĥ (R f) = f − R f` — the inverse of the
resolvent, minus the identity. Carried as a bare linear
map on its domain submodule: Mathlib has no unbounded-
operator typeclass this could inhabit, and no
typeclass self-adjointness is claimed for it; its
self-adjointness content is the symmetry below plus the
surjectivity of `Ĥ + 1` (the resolvent seat). -/
noncomputable def sliceHamOperator (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) :
    ↥(sliceHamOperatorDomain μG ρ hN2 hρcont hN β hpos)
      →ₗ[ℂ] ↥(sliceFormClosure μG ρ hN2 hρcont hN β
        hpos) :=
  (LinearEquiv.ofInjective (sliceFriedrichsResolventLin
      μG ρ hN2 hρcont hN β hpos)
    (sliceFriedrichsResolventLin_injective μG ρ hN2
      hρcont hN β hpos)).symm.toLinearMap
    - (sliceHamOperatorDomain μG ρ hN2 hρcont hN β
        hpos).subtype

/-- The resolvent preimage of a domain element: the
unique `f ∈ H'` with `R f = u`. -/
noncomputable def sliceHamPreimage (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (u : ↥(sliceHamOperatorDomain μG ρ hN2 hρcont hN β
      hpos)) :
    ↥(sliceFormClosure μG ρ hN2 hρcont hN β hpos) :=
  (LinearEquiv.ofInjective (sliceFriedrichsResolventLin
      μG ρ hN2 hρcont hN β hpos)
    (sliceFriedrichsResolventLin_injective μG ρ hN2
      hρcont hN β hpos)).symm u

/-- The preimage really is a preimage. -/
theorem sliceHamResolvent_preimage (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (u : ↥(sliceHamOperatorDomain μG ρ hN2 hρcont hN β
      hpos)) :
    sliceFriedrichsResolventLin μG ρ hN2 hρcont hN β
        hpos (sliceHamPreimage μG ρ hN2 hρcont hN β hpos
          u)
      = u.1 := by
  have h := LinearEquiv.apply_symm_apply
    (LinearEquiv.ofInjective (sliceFriedrichsResolventLin
        μG ρ hN2 hρcont hN β hpos)
      (sliceFriedrichsResolventLin_injective μG ρ hN2
        hρcont hN β hpos)) u
  have h2 := congrArg Subtype.val h
  rwa [LinearEquiv.ofInjective_apply] at h2

/-- **The defining equation of `Ĥ`**: `Ĥ u = f − u`
whenever `u = R f`. -/
theorem sliceHamOperator_eq (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (u : ↥(sliceHamOperatorDomain μG ρ hN2 hρcont hN β
      hpos))
    (f : ↥(sliceFormClosure μG ρ hN2 hρcont hN β hpos))
    (hf : sliceFriedrichsResolventLin μG ρ hN2 hρcont hN
        β hpos f = u.1) :
    sliceHamOperator μG ρ hN2 hρcont hN β hpos u
      = f - u.1 := by
  have hpre : sliceHamPreimage μG ρ hN2 hρcont hN β
      hpos u = f :=
    (sliceFriedrichsResolventLin_injective μG ρ hN2
      hρcont hN β hpos) (by
        rw [sliceHamResolvent_preimage μG ρ hN2 hρcont
          hN β hpos u]
        exact hf.symm)
  show (sliceHamPreimage μG ρ hN2 hρcont hN β hpos u)
      - u.1 = f - u.1
  rw [hpre]

/-- The defining equation at the resolvent's own points:
`Ĥ (R f) = f − R f`. -/
theorem sliceHamOperator_resolvent (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (f : ↥(sliceFormClosure μG ρ hN2 hρcont hN β hpos)) :
    sliceHamOperator μG ρ hN2 hρcont hN β hpos
        ⟨sliceFriedrichsResolventLin μG ρ hN2 hρcont hN
          β hpos f, LinearMap.mem_range_self _ f⟩
      = f - sliceFriedrichsResolventLin μG ρ hN2 hρcont
          hN β hpos f :=
  sliceHamOperator_eq μG ρ hN2 hρcont hN β hpos _ f rfl

/-- **Symmetry of `Ĥ`** on its domain — pure algebra from
the symmetry of the resolvent and the defining
equation. -/
theorem sliceHamOperator_symmetric (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (u v : ↥(sliceHamOperatorDomain μG ρ hN2 hρcont hN
      β hpos)) :
    inner ℂ (sliceHamOperator μG ρ hN2 hρcont hN β hpos
        u) v.1
      = inner ℂ u.1 (sliceHamOperator μG ρ hN2 hρcont
          hN β hpos v) := by
  obtain ⟨f, hf⟩ : ∃ f : ↥(sliceFormClosure μG ρ hN2
      hρcont hN β hpos), sliceFriedrichsResolventLin μG
        ρ hN2 hρcont hN β hpos f = u.1 := u.2
  obtain ⟨g, hg⟩ : ∃ g : ↥(sliceFormClosure μG ρ hN2
      hρcont hN β hpos), sliceFriedrichsResolventLin μG
        ρ hN2 hρcont hN β hpos g = v.1 := v.2
  have hf1 : (u.1).1 = (sliceFriedrichsResolvent μG ρ
      hN2 hρcont hN β hpos f).1 := by
    have h := congrArg Subtype.val hf
    rw [sliceFriedrichsResolventLin_apply μG ρ hN2
      hρcont hN β hpos f] at h
    exact h.symm
  have hg1 : (v.1).1 = (sliceFriedrichsResolvent μG ρ
      hN2 hρcont hN β hpos g).1 := by
    have h := congrArg Subtype.val hg
    rw [sliceFriedrichsResolventLin_apply μG ρ hN2
      hρcont hN β hpos g] at h
    exact h.symm
  rw [sliceHamOperator_eq μG ρ hN2 hρcont hN β hpos u f
      hf,
    sliceHamOperator_eq μG ρ hN2 hρcont hN β hpos v g
      hg,
    sliceFormClosure_inner μG ρ hN2 hρcont hN β hpos,
    sliceFormClosure_inner μG ρ hN2 hρcont hN β hpos,
    Submodule.coe_sub, Submodule.coe_sub, hf1, hg1,
    inner_sub_left, inner_sub_right,
    sliceFriedrichsResolvent_symmetric μG ρ hN2 hρcont
      hN β hpos f g]

/-- **The diagonal of `Ĥ` is the form**: for `u ∈ D(Ĥ)`,
`⟪Ĥu, u⟫` is exactly the Hamiltonian form value of `u` —
in particular a nonnegative real. This is the
`‖Ĥ^{1/2} u‖² = form(u)` identity of the representation
theorem, at the level the form itself defines. -/
theorem sliceHamOperator_inner_self (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (u : ↥(sliceHamOperatorDomain μG ρ hN2 hρcont hN β
      hpos)) :
    inner ℂ (sliceHamOperator μG ρ hN2 hρcont hN β hpos
        u) u.1
      = ((sliceFormVal μG ρ hN2 hρcont hN β hpos
          (u.1).1 : ℝ) : ℂ) := by
  obtain ⟨f, hf⟩ : ∃ f : ↥(sliceFormClosure μG ρ hN2
      hρcont hN β hpos), sliceFriedrichsResolventLin μG
        ρ hN2 hρcont hN β hpos f = u.1 := u.2
  have hf1 : (u.1).1 = (sliceFriedrichsRep μG ρ hN2
      hρcont hN β hpos f).val := by
    have h := congrArg Subtype.val hf
    rw [sliceFriedrichsResolventLin_apply μG ρ hN2
      hρcont hN β hpos f,
      sliceFriedrichsResolvent_coe μG ρ hN2 hρcont hN β
        hpos f] at h
    exact h.symm
  have hspec := sliceFriedrichsRep_spec μG ρ hN2
    hρcont hN β hpos f (sliceFriedrichsRep μG ρ hN2
      hρcont hN β hpos f)
  have hB : sliceFormInner μG ρ hN2 hρcont hN β hpos
        (sliceFriedrichsRep μG ρ hN2 hρcont hN β hpos f)
        (sliceFriedrichsRep μG ρ hN2 hρcont hN β hpos f)
      = inner ℂ (sliceFriedrichsRep μG ρ hN2 hρcont hN
          β hpos f).val (sliceFriedrichsRep μG ρ hN2
            hρcont hN β hpos f).val
        + ((sliceFormVal μG ρ hN2 hρcont hN β hpos
            (sliceFriedrichsRep μG ρ hN2 hρcont hN β
              hpos f).val : ℝ) : ℂ) := by
    unfold sliceFormInner
    rw [sliceFormDomain.val_eq μG ρ hN2 hρcont hN β
        hpos,
      sliceFormB_self μG ρ hN2 hρcont hN β hpos]
  rw [sliceHamOperator_eq μG ρ hN2 hρcont hN β hpos u f
      hf,
    sliceFormClosure_inner μG ρ hN2 hρcont hN β hpos,
    Submodule.coe_sub, hf1, inner_sub_left]
  linear_combination hB - hspec

/-- **`Ĥ ≥ 0`**: the diagonal pairing has nonnegative
real part (it is the form value, by the previous
theorem). -/
theorem sliceHamOperator_inner_self_nonneg (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (u : ↥(sliceHamOperatorDomain μG ρ hN2 hρcont hN β
      hpos)) :
    0 ≤ (inner ℂ (sliceHamOperator μG ρ hN2 hρcont hN β
        hpos u) u.1).re := by
  rw [sliceHamOperator_inner_self μG ρ hN2 hρcont hN β
    hpos u]
  rw [Complex.ofReal_re]
  exact sliceFormVal_nonneg μG ρ hN2 hρcont hN β hpos _

/-- The form-domain lift of a domain element: the Riesz
representative of its resolvent preimage. -/
noncomputable def sliceHamLift (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (u : ↥(sliceHamOperatorDomain μG ρ hN2 hρcont hN β
      hpos)) :
    sliceFormDomain μG ρ hN2 hρcont hN β hpos :=
  sliceFriedrichsRep μG ρ hN2 hρcont hN β hpos
    (sliceHamPreimage μG ρ hN2 hρcont hN β hpos u)

/-- The lift's ambient vector is the domain element's
ambient vector. -/
theorem sliceHamLift_val (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (u : ↥(sliceHamOperatorDomain μG ρ hN2 hρcont hN β
      hpos)) :
    (sliceHamLift μG ρ hN2 hρcont hN β hpos u).val
      = (u.1).1 := by
  show (sliceFriedrichsRep μG ρ hN2 hρcont hN β hpos
      (sliceHamPreimage μG ρ hN2 hρcont hN β hpos
        u)).val = (u.1).1
  rw [← sliceFriedrichsResolvent_coe μG ρ hN2 hρcont hN
      β hpos,
    ← sliceFriedrichsResolventLin_apply μG ρ hN2 hρcont
      hN β hpos]
  exact congrArg Subtype.val
    (sliceHamResolvent_preimage μG ρ hN2 hρcont hN β
      hpos u)

/-- **The form identity, resolvent form**: the polarized
form of the representative against any form-domain
vector is the pairing of `f − R f` — i.e. of `Ĥ (R f)` —
against it. -/
theorem sliceFriedrichs_form_identity (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (f : ↥(sliceFormClosure μG ρ hN2 hρcont hN β hpos))
    (v : sliceFormDomain μG ρ hN2 hρcont hN β hpos) :
    sliceFormB μG ρ hN2 hρcont hN β hpos
        (sliceFriedrichsRep μG ρ hN2 hρcont hN β hpos
          f).toSub v.toSub
      = inner ℂ (f.1 - (sliceFriedrichsResolvent μG ρ
          hN2 hρcont hN β hpos f).1) v.val := by
  have hspec := sliceFriedrichsRep_spec μG ρ hN2
    hρcont hN β hpos f v
  have hF : sliceFormInner μG ρ hN2 hρcont hN β hpos
        (sliceFriedrichsRep μG ρ hN2 hρcont hN β hpos f)
        v
      = inner ℂ (sliceFriedrichsRep μG ρ hN2 hρcont hN
          β hpos f).val v.val
        + sliceFormB μG ρ hN2 hρcont hN β hpos
            (sliceFriedrichsRep μG ρ hN2 hρcont hN β
              hpos f).toSub v.toSub := rfl
  rw [sliceFriedrichsResolvent_coe μG ρ hN2 hρcont hN β
      hpos f, inner_sub_left]
  linear_combination hspec - hF

/-- **THE FORM IDENTITY** (Kato's first representation
theorem, form clause): for `u ∈ D(Ĥ)` with form-domain
lift `û`, and every form-domain vector `v`,
`sliceFormB û v = ⟪Ĥu, v⟫`. -/
theorem sliceHamOperator_form_identity (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (u : ↥(sliceHamOperatorDomain μG ρ hN2 hρcont hN β
      hpos))
    (v : sliceFormDomain μG ρ hN2 hρcont hN β hpos) :
    sliceFormB μG ρ hN2 hρcont hN β hpos
        (sliceHamLift μG ρ hN2 hρcont hN β hpos u).toSub
        v.toSub
      = inner ℂ (sliceHamOperator μG ρ hN2 hρcont hN β
          hpos u) ⟨v.val, sliceFormDomain_le_closure μG
            ρ hN2 hρcont hN β hpos v.toSub.2⟩ := by
  obtain ⟨f, hf⟩ : ∃ f : ↥(sliceFormClosure μG ρ hN2
      hρcont hN β hpos), sliceFriedrichsResolventLin μG
        ρ hN2 hρcont hN β hpos f = u.1 := u.2
  have hpre : sliceHamPreimage μG ρ hN2 hρcont hN β
      hpos u = f :=
    (sliceFriedrichsResolventLin_injective μG ρ hN2
      hρcont hN β hpos) (by
        rw [sliceHamResolvent_preimage μG ρ hN2 hρcont
          hN β hpos u]
        exact hf.symm)
  have hf1 : (u.1).1 = (sliceFriedrichsResolvent μG ρ
      hN2 hρcont hN β hpos f).1 := by
    have h := congrArg Subtype.val hf
    rw [sliceFriedrichsResolventLin_apply μG ρ hN2
      hρcont hN β hpos f] at h
    exact h.symm
  show sliceFormB μG ρ hN2 hρcont hN β hpos
      (sliceFriedrichsRep μG ρ hN2 hρcont hN β hpos
        (sliceHamPreimage μG ρ hN2 hρcont hN β hpos
          u)).toSub v.toSub
    = inner ℂ (sliceHamOperator μG ρ hN2 hρcont hN β
        hpos u) ⟨v.val, sliceFormDomain_le_closure μG ρ
          hN2 hρcont hN β hpos v.toSub.2⟩
  rw [hpre, sliceFormClosure_inner μG ρ hN2 hρcont hN β
      hpos,
    sliceHamOperator_eq μG ρ hN2 hρcont hN β hpos u f
      hf, Submodule.coe_sub, hf1]
  exact sliceFriedrichs_form_identity μG ρ hN2 hρcont
    hN β hpos f v

/-- **Self-adjointness in the resolvent sense**:
`Ĥ + 1` maps `D(Ĥ)` onto all of `H'` — every `f` is
`u + Ĥu` for `u = R f`. This surjectivity is by
construction (the Riesz assignment is defined on all of
`H'`); it is the honest Mathlib-available form of the
Friedrichs operator's self-adjointness, and it is NOT a
typeclass statement. -/
theorem sliceHamOperator_add_surjective (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (f : ↥(sliceFormClosure μG ρ hN2 hρcont hN β hpos)) :
    ∃ u : ↥(sliceHamOperatorDomain μG ρ hN2 hρcont hN β
        hpos), u.1 + sliceHamOperator μG ρ hN2 hρcont hN
          β hpos u = f := by
  refine ⟨⟨sliceFriedrichsResolventLin μG ρ hN2 hρcont
    hN β hpos f, LinearMap.mem_range_self _ f⟩, ?_⟩
  rw [sliceHamOperator_resolvent μG ρ hN2 hρcont hN β
    hpos f]
  show sliceFriedrichsResolventLin μG ρ hN2 hρcont hN β
      hpos f + (f - sliceFriedrichsResolventLin μG ρ hN2
        hρcont hN β hpos f) = f
  exact add_sub_cancel _ _

/-! ## §5. The vacuum -/

/-- Helper: a polarized form whose approximants all
vanish is zero — its defining sequence is constantly
zero. -/
theorem sliceFormB_eq_zero_of_forall_approxB (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    {x y : ↥(sliceHamFormDomainC μG ρ hN2 hρcont hN β
      hpos)}
    (h : ∀ K : ℕ, sliceApproxB μG ρ hN2 hρcont hN β hpos
      K x.1 y.1 = 0) :
    sliceFormB μG ρ hN2 hρcont hN β hpos x y = 0 :=
  tendsto_nhds_unique (sliceFormB_tendsto μG ρ hN2
    hρcont hN β hpos x y)
    (Filter.Tendsto.congr (fun K => (h K).symm)
      tendsto_const_nhds)

/-- The polarized form vanishes against the vacuum on
the left: every approximant pairing does, since the
defect iterates kill the vacuum and the defect moves
across the pairing. -/
theorem sliceFormB_vacuum_left (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (hd : 0 < d)
    (v : sliceFormDomain μG ρ hN2 hρcont hN β hpos) :
    sliceFormB μG ρ hN2 hρcont hN β hpos
        ⟨sliceOmegaCompleted μG ρ hN2 hρcont hN β hpos
          hd, sliceHamC_vacuum_mem_domain μG ρ hN2
            hρcont hN β hpos hd⟩ v.toSub = 0 := by
  apply sliceFormB_eq_zero_of_forall_approxB μG ρ hN2
    hρcont hN β hpos
  intro K
  show sliceApproxB μG ρ hN2 hρcont hN β hpos K
      (sliceOmegaCompleted μG ρ hN2 hρcont hN β hpos hd)
      v.toSub.1 = 0
  unfold sliceApproxB
  apply Finset.sum_eq_zero
  intro j hj
  rw [Finset.mem_Icc] at hj
  rw [sliceHamCompletedDefect_iter_inner μG ρ hN2
      hρcont hN β hpos j
      (sliceOmegaCompleted μG ρ hN2 hρcont hN β hpos hd)
      v.toSub.1,
    sliceHamCompletedDefect_iter_vacuum μG ρ hN2 hρcont
      hN β hpos hd hj.1, inner_zero_left, mul_zero]

/-- **The Riesz representative of the vacuum is the
vacuum**: the vacuum, as a form-domain element,
satisfies the resolvent equation for `f = Ω` because
its form pairings are the ambient pairings (the form
part vanishes). -/
theorem sliceFriedrichsRep_vacuum (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (hd : 0 < d) :
    sliceFriedrichsRep μG ρ hN2 hρcont hN β hpos
        ⟨sliceOmegaCompleted μG ρ hN2 hρcont hN β hpos
          hd, sliceFormDomain_le_closure μG ρ hN2
            hρcont hN β hpos
            (sliceHamC_vacuum_mem_domain μG ρ hN2
              hρcont hN β hpos hd)⟩
      = sliceFormDomain.ofSub μG ρ hN2 hρcont hN β hpos
          ⟨sliceOmegaCompleted μG ρ hN2 hρcont hN β hpos
            hd, sliceHamC_vacuum_mem_domain μG ρ hN2
              hρcont hN β hpos hd⟩ := by
  apply sliceFriedrichsRep_unique μG ρ hN2 hρcont hN β
    hpos
  intro v
  rw [sliceFriedrichsRep_spec μG ρ hN2 hρcont hN β
    hpos]
  show inner ℂ (sliceOmegaCompleted μG ρ hN2 hρcont hN
      β hpos hd) v.val
    = sliceFormInner μG ρ hN2 hρcont hN β hpos
        (sliceFormDomain.ofSub μG ρ hN2 hρcont hN β
          hpos ⟨sliceOmegaCompleted μG ρ hN2 hρcont hN
            β hpos hd, sliceHamC_vacuum_mem_domain μG ρ
              hN2 hρcont hN β hpos hd⟩) v
  unfold sliceFormInner
  rw [sliceFormDomain.val_ofSub μG ρ hN2 hρcont hN β
      hpos,
    sliceFormDomain.toSub_ofSub μG ρ hN2 hρcont hN β
      hpos,
    sliceFormB_vacuum_left μG ρ hN2 hρcont hN β hpos hd
      v, add_zero]

/-- **The resolvent fixes the vacuum**: `R Ω = Ω`. -/
theorem sliceFriedrichsResolvent_vacuum (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (hd : 0 < d) :
    sliceFriedrichsResolventLin μG ρ hN2 hρcont hN β
        hpos ⟨sliceOmegaCompleted μG ρ hN2 hρcont hN β
          hpos hd, sliceFormDomain_le_closure μG ρ hN2
            hρcont hN β hpos
            (sliceHamC_vacuum_mem_domain μG ρ hN2
              hρcont hN β hpos hd)⟩
      = ⟨sliceOmegaCompleted μG ρ hN2 hρcont hN β hpos
          hd, sliceFormDomain_le_closure μG ρ hN2
            hρcont hN β hpos
            (sliceHamC_vacuum_mem_domain μG ρ hN2
              hρcont hN β hpos hd)⟩ := by
  apply Subtype.ext
  rw [sliceFriedrichsResolventLin_apply μG ρ hN2 hρcont
      hN β hpos,
    sliceFriedrichsResolvent_coe μG ρ hN2 hρcont hN β
      hpos,
    sliceFriedrichsRep_vacuum μG ρ hN2 hρcont hN β hpos
      hd,
    sliceFormDomain.val_ofSub μG ρ hN2 hρcont hN β
      hpos]

/-- **The vacuum is in the operator domain and `Ĥ`
kills it**: `Ω ∈ D(Ĥ)` with `Ĥ Ω = 0` — the Friedrichs
Hamiltonian has the vacuum as a ground state of energy
zero. -/
theorem sliceHamOperator_vacuum (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (hd : 0 < d) :
    ∃ u : ↥(sliceHamOperatorDomain μG ρ hN2 hρcont hN
        β hpos), u.1
        = ⟨sliceOmegaCompleted μG ρ hN2 hρcont hN β
            hpos hd, sliceFormDomain_le_closure μG ρ
              hN2 hρcont hN β hpos
              (sliceHamC_vacuum_mem_domain μG ρ hN2
                hρcont hN β hpos hd)⟩
      ∧ sliceHamOperator μG ρ hN2 hρcont hN β hpos u
        = 0 := by
  have hmem : (⟨sliceOmegaCompleted μG ρ hN2 hρcont hN
        β hpos hd, sliceFormDomain_le_closure μG ρ hN2
          hρcont hN β hpos
          (sliceHamC_vacuum_mem_domain μG ρ hN2 hρcont
            hN β hpos hd)⟩ :
      ↥(sliceFormClosure μG ρ hN2 hρcont hN β hpos))
      ∈ sliceHamOperatorDomain μG ρ hN2 hρcont hN β
        hpos :=
    ⟨⟨sliceOmegaCompleted μG ρ hN2 hρcont hN β hpos hd,
      sliceFormDomain_le_closure μG ρ hN2 hρcont hN β
        hpos (sliceHamC_vacuum_mem_domain μG ρ hN2
          hρcont hN β hpos hd)⟩,
      sliceFriedrichsResolvent_vacuum μG ρ hN2 hρcont
        hN β hpos hd⟩
  refine ⟨⟨⟨sliceOmegaCompleted μG ρ hN2 hρcont hN β
    hpos hd, sliceFormDomain_le_closure μG ρ hN2
      hρcont hN β hpos (sliceHamC_vacuum_mem_domain μG
        ρ hN2 hρcont hN β hpos hd)⟩, hmem⟩, rfl, ?_⟩
  have h := sliceHamOperator_eq μG ρ hN2 hρcont hN β
    hpos ⟨⟨sliceOmegaCompleted μG ρ hN2 hρcont hN β hpos
      hd, sliceFormDomain_le_closure μG ρ hN2 hρcont hN
        β hpos (sliceHamC_vacuum_mem_domain μG ρ hN2
          hρcont hN β hpos hd)⟩, hmem⟩
    ⟨sliceOmegaCompleted μG ρ hN2 hρcont hN β hpos hd,
      sliceFormDomain_le_closure μG ρ hN2 hρcont hN β
        hpos (sliceHamC_vacuum_mem_domain μG ρ hN2
          hρcont hN β hpos hd)⟩
    (sliceFriedrichsResolvent_vacuum μG ρ hN2 hρcont hN
      β hpos hd)
  rw [h]
  exact sub_self _

/-! ## §6. The β = 0 seat and the packages -/

/-- At `β = 0` the completed defect is identically
zero: the completed transfer operator is the identity
there. -/
theorem sliceHamCompletedDefect_beta_zero (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (hd : 0 < d)
    (z : sliceHilbertSpace μG ρ hN2 hρcont hN 0
      (sliceHPosOne_zero μG ρ hN2 hρcont hN hd)) :
    sliceHamCompletedDefect μG ρ hN2 hρcont hN 0
        (sliceHPosOne_zero μG ρ hN2 hρcont hN hd) z
      = 0 := by
  rw [sliceHamCompletedDefect_apply,
    sliceHatCompletedFun_beta_zero μG ρ hN2 hρcont hN
      hd z, sub_self]

/-- At `β = 0` the polarized form vanishes identically
(the defect does, in every positive degree). -/
theorem sliceFormB_beta_zero (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (hd : 0 < d)
    (x y : ↥(sliceHamFormDomainC μG ρ hN2 hρcont hN 0
      (sliceHPosOne_zero μG ρ hN2 hρcont hN hd))) :
    sliceFormB μG ρ hN2 hρcont hN 0
        (sliceHPosOne_zero μG ρ hN2 hρcont hN hd) x y
      = 0 := by
  apply sliceFormB_eq_zero_of_forall_approxB μG ρ hN2
    hρcont hN 0 (sliceHPosOne_zero μG ρ hN2 hρcont hN
      hd)
  intro K
  unfold sliceApproxB
  apply Finset.sum_eq_zero
  intro j hj
  rw [Finset.mem_Icc] at hj
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  rw [Function.iterate_succ_apply',
    sliceHamCompletedDefect_beta_zero μG ρ hN2 hρcont
      hN hd, inner_zero_right, mul_zero]

/-- At `β = 0` the resolvent is the identity on the
carrier (the form inner product is the ambient one
there, so the Riesz representative of `f` is `f`
itself). -/
theorem sliceFriedrichsResolvent_beta_zero (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (hd : 0 < d)
    (f : ↥(sliceFormClosure μG ρ hN2 hρcont hN 0
      (sliceHPosOne_zero μG ρ hN2 hρcont hN hd))) :
    sliceFriedrichsResolventLin μG ρ hN2 hρcont hN 0
        (sliceHPosOne_zero μG ρ hN2 hρcont hN hd) f
      = f := by
  have hmem : f.1 ∈ sliceHamFormDomainC μG ρ hN2
      hρcont hN 0 (sliceHPosOne_zero μG ρ hN2 hρcont hN
        hd) :=
    sliceFormDomain_beta_zero_top μG ρ hN2 hρcont hN
      hd f.1
  have hrep : sliceFriedrichsRep μG ρ hN2 hρcont hN 0
        (sliceHPosOne_zero μG ρ hN2 hρcont hN hd) f
      = sliceFormDomain.ofSub μG ρ hN2 hρcont hN 0
          (sliceHPosOne_zero μG ρ hN2 hρcont hN hd)
          ⟨f.1, hmem⟩ := by
    apply sliceFriedrichsRep_unique μG ρ hN2 hρcont hN
      0 (sliceHPosOne_zero μG ρ hN2 hρcont hN hd)
    intro v
    rw [sliceFriedrichsRep_spec μG ρ hN2 hρcont hN 0
      (sliceHPosOne_zero μG ρ hN2 hρcont hN hd)]
    show inner ℂ f.1 v.val
      = sliceFormInner μG ρ hN2 hρcont hN 0
          (sliceHPosOne_zero μG ρ hN2 hρcont hN hd)
          (sliceFormDomain.ofSub μG ρ hN2 hρcont hN 0
            (sliceHPosOne_zero μG ρ hN2 hρcont hN hd)
            ⟨f.1, hmem⟩) v
    unfold sliceFormInner
    rw [sliceFormDomain.val_ofSub μG ρ hN2 hρcont hN 0
        (sliceHPosOne_zero μG ρ hN2 hρcont hN hd),
      sliceFormDomain.toSub_ofSub μG ρ hN2 hρcont hN 0
        (sliceHPosOne_zero μG ρ hN2 hρcont hN hd),
      sliceFormB_beta_zero μG ρ hN2 hρcont hN hd,
      add_zero]
  apply Subtype.ext
  rw [sliceFriedrichsResolventLin_apply μG ρ hN2
      hρcont hN 0 (sliceHPosOne_zero μG ρ hN2 hρcont hN
        hd),
    sliceFriedrichsResolvent_coe μG ρ hN2 hρcont hN 0
      (sliceHPosOne_zero μG ρ hN2 hρcont hN hd), hrep,
    sliceFormDomain.val_ofSub μG ρ hN2 hρcont hN 0
      (sliceHPosOne_zero μG ρ hN2 hρcont hN hd)]

/-- At `β = 0` the Hamiltonian is zero (the resolvent is
the identity, so `Ĥ u = f − u = 0` on the domain). -/
theorem sliceHamOperator_beta_zero (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (hd : 0 < d)
    (u : ↥(sliceHamOperatorDomain μG ρ hN2 hρcont hN 0
      (sliceHPosOne_zero μG ρ hN2 hρcont hN hd))) :
    sliceHamOperator μG ρ hN2 hρcont hN 0
        (sliceHPosOne_zero μG ρ hN2 hρcont hN hd) u
      = 0 := by
  obtain ⟨f, hf⟩ : ∃ f : ↥(sliceFormClosure μG ρ hN2
      hρcont hN 0 (sliceHPosOne_zero μG ρ hN2 hρcont hN
        hd)), sliceFriedrichsResolventLin μG ρ hN2
        hρcont hN 0 (sliceHPosOne_zero μG ρ hN2 hρcont
          hN hd) f = u.1 := u.2
  have hfu : f = u.1 := by
    rw [← hf]
    exact (sliceFriedrichsResolvent_beta_zero μG ρ hN2
      hρcont hN hd f).symm
  rw [sliceHamOperator_eq μG ρ hN2 hρcont hN 0
    (sliceHPosOne_zero μG ρ hN2 hρcont hN hd) u f hf,
    hfu, sub_self]

/-- **FG-2b FRIEDRICHS PACKAGE.** What this brick
proves, bundled at the standing generality (general
`(G, ρ)`, every real `β`, under exactly
`SliceHPosOne`, on the carrier `H'` = the closure of
the form domain): (1) `H'` is complete; (2) the form
domain is dense in `H'`; (3) `H' ⊆ (ker T̂_c)⊥`; (4) the
resolvent is symmetric; (5) the resolvent has bound
`1`; (6) `Ĥ` is symmetric on `D(Ĥ)`; (7) the diagonal
`⟪Ĥu, u⟫` is the form value; (8) the FORM IDENTITY
`sliceFormB û v = ⟪Ĥu, v⟫`; (9) `Ĥ + 1` is surjective
onto `H'` (self-adjointness in the resolvent sense);
(10) the vacuum lies in `D(Ĥ)` and `Ĥ Ω = 0`. NOT
clauses of this package: the equality
`H' = (ker T̂_c)⊥` (step-0 residue), any typeclass
self-adjointness for `Ĥ`, and `exp(−Ĥ) = T̂_c` (FG-2c). -/
def sliceFriedrichsPackage (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (hd : 0 < d) :
    Prop :=
  CompleteSpace ↥(sliceFormClosure μG ρ hN2 hρcont hN β
      hpos)
    ∧ (∀ z : ↥(sliceFormClosure μG ρ hN2 hρcont hN β
        hpos), ∀ ε : ℝ, 0 < ε →
        ∃ x : sliceFormDomain μG ρ hN2 hρcont hN β hpos,
          dist z.1 x.val < ε)
    ∧ (∀ z : ↥(sliceFormClosure μG ρ hN2 hρcont hN β
        hpos), ∀ w : sliceHilbertSpace μG ρ hN2 hρcont
          hN β hpos, sliceHatCompleted μG ρ hN2 hρcont
            hN β hpos w = 0 → inner ℂ z.1 w = 0)
    ∧ (∀ f g : ↥(sliceFormClosure μG ρ hN2 hρcont hN β
        hpos), inner ℂ (sliceFriedrichsResolvent μG ρ
            hN2 hρcont hN β hpos f).1 g.1
          = inner ℂ f.1 (sliceFriedrichsResolvent μG ρ
              hN2 hρcont hN β hpos g).1)
    ∧ (∀ f : ↥(sliceFormClosure μG ρ hN2 hρcont hN β
        hpos), ‖sliceFriedrichsResolventLin μG ρ hN2
            hρcont hN β hpos f‖ ≤ ‖f‖)
    ∧ (∀ u v : ↥(sliceHamOperatorDomain μG ρ hN2 hρcont
        hN β hpos), inner ℂ (sliceHamOperator μG ρ hN2
            hρcont hN β hpos u) v.1
          = inner ℂ u.1 (sliceHamOperator μG ρ hN2
              hρcont hN β hpos v))
    ∧ (∀ u : ↥(sliceHamOperatorDomain μG ρ hN2 hρcont
        hN β hpos), inner ℂ (sliceHamOperator μG ρ hN2
            hρcont hN β hpos u) u.1
          = ((sliceFormVal μG ρ hN2 hρcont hN β hpos
              (u.1).1 : ℝ) : ℂ))
    ∧ (∀ u : ↥(sliceHamOperatorDomain μG ρ hN2 hρcont
        hN β hpos), ∀ v : sliceFormDomain μG ρ hN2
          hρcont hN β hpos,
          sliceFormB μG ρ hN2 hρcont hN β hpos
              (sliceHamLift μG ρ hN2 hρcont hN β hpos
                u).toSub v.toSub
            = inner ℂ (sliceHamOperator μG ρ hN2 hρcont
                hN β hpos u) ⟨v.val,
                  sliceFormDomain_le_closure μG ρ hN2
                    hρcont hN β hpos v.toSub.2⟩)
    ∧ (∀ f : ↥(sliceFormClosure μG ρ hN2 hρcont hN β
        hpos), ∃ u : ↥(sliceHamOperatorDomain μG ρ hN2
          hρcont hN β hpos), u.1 + sliceHamOperator μG ρ
            hN2 hρcont hN β hpos u = f)
    ∧ (∃ u : ↥(sliceHamOperatorDomain μG ρ hN2 hρcont
        hN β hpos), u.1
          = ⟨sliceOmegaCompleted μG ρ hN2 hρcont hN β
              hpos hd, sliceFormDomain_le_closure μG ρ
                hN2 hρcont hN β hpos
                (sliceHamC_vacuum_mem_domain μG ρ hN2
                  hρcont hN β hpos hd)⟩
        ∧ sliceHamOperator μG ρ hN2 hρcont hN β hpos u
          = 0)

theorem sliceFriedrichs_package (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (hd : 0 < d) :
    sliceFriedrichsPackage μG ρ hN2 hρcont hN β hpos
      hd :=
  ⟨sliceFormClosure_completeSpace μG ρ hN2 hρcont hN β
      hpos,
    fun z ε hε => sliceFormClosure_dense μG ρ hN2
      hρcont hN β hpos z hε,
    fun z w hw => sliceFormClosure_orthogonal_ker μG ρ
      hN2 hρcont hN β hpos z hw,
    fun f g => sliceFriedrichsResolvent_symmetric μG ρ
      hN2 hρcont hN β hpos f g,
    fun f => sliceFriedrichsResolvent_norm_le μG ρ hN2
      hρcont hN β hpos f,
    fun u v => sliceHamOperator_symmetric μG ρ hN2
      hρcont hN β hpos u v,
    fun u => sliceHamOperator_inner_self μG ρ hN2
      hρcont hN β hpos u,
    fun u v => sliceHamOperator_form_identity μG ρ hN2
      hρcont hN β hpos u v,
    fun f => sliceHamOperator_add_surjective μG ρ hN2
      hρcont hN β hpos f,
    sliceHamOperator_vacuum μG ρ hN2 hρcont hN β hpos
      hd⟩

/-- The package at the U(1) seat: hypothesis-free in
`β ≥ 0`. -/
theorem sliceFriedrichs_circle_package (hN2 : 2 ≤ N)
    (hN : Even N) (β : ℝ) (hβ : 0 ≤ β) :
    sliceFriedrichsPackage (haarProb Circle) circleRep
      hN2 circleRep_continuous hN β
      (sliceHPosOne_circle hN2 hN β hβ) zero_lt_one :=
  sliceFriedrichs_package (haarProb Circle) circleRep
    hN2 circleRep_continuous hN β
    (sliceHPosOne_circle hN2 hN β hβ) zero_lt_one

/-- **The `β = 0` package:** the carrier is the whole
space, the polarized form vanishes, the resolvent is
the identity, and the Hamiltonian is zero. -/
def sliceFriedrichsBetaZeroPackage (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (hd : 0 < d) : Prop :=
  (∀ z : sliceHilbertSpace μG ρ hN2 hρcont hN 0
      (sliceHPosOne_zero μG ρ hN2 hρcont hN hd),
    z ∈ sliceFormClosure μG ρ hN2 hρcont hN 0
      (sliceHPosOne_zero μG ρ hN2 hρcont hN hd))
    ∧ (∀ x y : ↥(sliceHamFormDomainC μG ρ hN2 hρcont hN
        0 (sliceHPosOne_zero μG ρ hN2 hρcont hN hd)),
      sliceFormB μG ρ hN2 hρcont hN 0
          (sliceHPosOne_zero μG ρ hN2 hρcont hN hd) x y
        = 0)
    ∧ (∀ f : ↥(sliceFormClosure μG ρ hN2 hρcont hN 0
        (sliceHPosOne_zero μG ρ hN2 hρcont hN hd)),
      sliceFriedrichsResolventLin μG ρ hN2 hρcont hN 0
          (sliceHPosOne_zero μG ρ hN2 hρcont hN hd) f
        = f)
    ∧ (∀ u : ↥(sliceHamOperatorDomain μG ρ hN2 hρcont
        hN 0 (sliceHPosOne_zero μG ρ hN2 hρcont hN
          hd)), sliceHamOperator μG ρ hN2 hρcont hN 0
          (sliceHPosOne_zero μG ρ hN2 hρcont hN hd) u
        = 0)

theorem sliceFriedrichs_beta_zero_package (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (hd : 0 < d) :
    sliceFriedrichsBetaZeroPackage μG ρ hN2 hρcont hN
      hd :=
  ⟨fun z => sliceFormDomain_le_closure μG ρ hN2
      hρcont hN 0 (sliceHPosOne_zero μG ρ hN2 hρcont hN
        hd) (sliceFormDomain_beta_zero_top μG ρ hN2
          hρcont hN hd z),
    fun x y => sliceFormB_beta_zero μG ρ hN2 hρcont hN
      hd x y,
    fun f => sliceFriedrichsResolvent_beta_zero μG ρ
      hN2 hρcont hN hd f,
    fun u => sliceHamOperator_beta_zero μG ρ hN2
      hρcont hN hd u⟩

end SliceFriedrichs

end ThetLogos
