import ThetLogos.ProductTriple
import ThetLogos.AnalyticTriple

-- The `[BoundedManifold]` / `[BoundedFinite]` section variables below trigger
-- the overlapping-instances linter (both extend `TripleData` via
-- `BoundedAnalyticTriple`); the two factors are never unified in this file,
-- so it is a false positive (same pattern as ProductTriple.lean).
set_option linter.overlappingInstances false

namespace ThetLogos

open TensorProduct

/-!
# ThetLogos.BoundedTriple — Rung 4 prep, Track B: bounded commutators + compact resolvent (2026-10-10)

Rung 4 prep campaign, Track B (bounded commutators + compact resolvent —
narrowed scope). Local-only; nothing here pushes to public.

## What this file IS
- §1: `HasCompactResolvent` — the compact-resolvent axiom as an OPAQUE T2
  def (no consequences faked from it).
- §2: `BoundedAnalyticTriple` — `AnalyticTripleData` plus the analytic
  debt as T2 class data: bounded commutators (`hbddComm`), bounded
  representation (`hbddRep`), compact resolvent (`hcompactRes`).
  `BoundedManifold` / `BoundedFinite` are marker subclasses (see below).
- §3: single-factor T1 lemmas — `nrm` bounds compose (`nrm_comp_bound`);
  the analytic T1s apply definitionally (`bounded_nrm_triangle`).
- §4: the product for bounded factors (T1) — `DprodB` / `πprodB`, the
  Rung-2 Dirac identity re-run on enriched data (`Dprod_sq_analytic`),
  the commutator decomposition (`prod_commutator_decomp_analytic`), its
  pointwise action on elementary tensors
  (`prod_commutator_tmul_analytic`), and the factor-component norm bounds
  (`prod_commutator_factorBounds`).

## Why the marker subclasses
The two product factors must have *distinct* types: with two
`[M F : BoundedAnalyticTriple]` variables, TC must guess which one
supplies `AddCommGroup M.toTripleData.S` — it picks one without
backtracking and fails. Distinct marker subclasses
(`BoundedManifold`, `BoundedFinite` — mirroring
`ManifoldFactor`/`FiniteFactor`) make the choice unambiguous. Both are
`BoundedAnalyticTriple`s; the split carries no new mathematics.

## HONESTY NOTE
Boundedness of `[D, π(f)]` / `π(a)` in `nrm` and compactness of the
resolvent cannot be *proved* from algebraic data — they are properties,
not theorems. "Genuine, not assumed" is met the same way as in
`AnalyticTriple.lean`: the norm is constructed from existing data
(`iprod`), and everything else is proved; a concrete model (L², finite
matrix triple) would discharge `hbddComm` / `hbddRep` / `hcompactRes` —
that is Rung 4 proper.

## What is NOT here (explicitly scoped out)
- The full estimate `‖[DprodB, πprodB (f⊗a)] z‖ ≤ K ‖z‖` is NOT proved:
  it needs a norm on the tensor-product spinor module
  `S_M ⊗[ℂ] S_F`, i.e. a tensor-product inner product — a separate task,
  NOT introduced here. What IS proved: the decomposition identity, its
  pointwise action on elementary tensors, and `nrm`-bounds on every
  factor component the class data controls.
- The `π_M(f) * Γ_M` summand's first factor is NOT norm-bounded here:
  that needs boundedness of `Γ` in `nrm`, analytic debt alongside
  `HasCompactResolvent` (a concrete model discharges it; in any
  C*-representation `Γ` is a self-adjoint unitary, `‖Γ‖ = 1`).
- `hcompactRes` is carried, never used: no theorem below depends on it.

## Tier ledger
T2 (definitions/axioms): `HasCompactResolvent` (opaque),
  `BoundedAnalyticTriple` (with `hbddComm`, `hbddRep`, `hcompactRes`),
  `BoundedManifold`, `BoundedFinite` (marker subclasses),
  `DprodB`, `πprodB`.
T1 (proved, zero sorrys): `nrm_comp_bound`, `bounded_nrm_triangle`,
  `Dprod_sq_analytic`, `prod_commutator_decomp_analytic`,
  `prod_commutator_tmul_analytic`, `prod_commutator_factorBounds`.
-/

-- ============================================================================
-- §1. Compact resolvent (T2, opaque)
-- ============================================================================

/-- Compactness of the resolvent (Tier T2 — opaque definition).

    Packages exactly this analytic content: compactness of the resolvent
    `(D − λ)⁻¹` on the Hilbert completion — i.e. the part of the analytic
    axioms that needs functional analysis beyond this algebraic setting
    (Rung 4 proper). It is carried as opaque class data (`hcompactRes`
    below); NO consequences are derived from it in this file. -/
opaque HasCompactResolvent {S : Type*} [AddCommGroup S] [Module ℂ S]
    (D : Module.End ℂ S) : Prop

-- ============================================================================
-- §2. The bounded analytic triple (T2 class) + marker subclasses
-- ============================================================================

/-- The bounded analytic triple (Tier T2 class): `AnalyticTripleData` plus
    the boundedness/compactness debt, stated honestly as properties (see
    HONESTY NOTE above).
    - `hbddComm`: bounded commutators — the first analytic axiom;
    - `hbddRep`: bounded representation — the zeroth analytic axiom;
    - `hcompactRes`: compact resolvent — opaque T2 (`HasCompactResolvent`),
      the functional-analysis part (Rung 4 proper). -/
class BoundedAnalyticTriple extends AnalyticTripleData where
  /-- Bounded commutators (Tier T2 — class field): for every `f : A` there
      is `C ≥ 0` with `nrm ([D, π f] x) ≤ C * nrm x` for all `x`. -/
  hbddComm : ∀ f : A, ∃ C : ℝ, 0 ≤ C ∧ ∀ x : S,
    @nrm toAnalyticTripleData ((D * π f - π f * D) x) ≤ C * @nrm toAnalyticTripleData x
  /-- Bounded representation (Tier T2 — class field): for every `a : A`
      there is `C ≥ 0` with `nrm (π a x) ≤ C * nrm x` for all `x`. -/
  hbddRep : ∀ a : A, ∃ C : ℝ, 0 ≤ C ∧ ∀ x : S,
    @nrm toAnalyticTripleData ((π a) x) ≤ C * @nrm toAnalyticTripleData x
  /-- Compact resolvent (Tier T2 — class field): `HasCompactResolvent D`
      (opaque — carried, never used; see §1). -/
  hcompactRes : @HasCompactResolvent S addS modS D

/-- A bounded manifold factor (Tier T2 — marker subclass): a
    `BoundedAnalyticTriple` playing the manifold role in the product.
    Exists so the two factors have distinct types (see the module
    docstring); carries no new mathematics. -/
class BoundedManifold extends BoundedAnalyticTriple

/-- A bounded finite factor (Tier T2 — marker subclass): a
    `BoundedAnalyticTriple` playing the finite role in the product.
    Exists so the two factors have distinct types (see the module
    docstring); carries no new mathematics. -/
class BoundedFinite extends BoundedAnalyticTriple

-- Projection instances, per marker subclass (high priority so TC takes
-- the unambiguous path first): the class's instance-fields are not found
-- by TC automatically, so they are re-exported here (same pattern as
-- ProductTriple.lean / AnalyticTriple.lean).
instance (priority := high) BoundedManifold.instAddS [β : BoundedManifold] :
    AddCommGroup β.toTripleData.S := β.toTripleData.addS
instance (priority := high) BoundedManifold.instModS [β : BoundedManifold] :
    Module ℂ β.toTripleData.S := β.toTripleData.modS
instance (priority := high) BoundedFinite.instAddS [β : BoundedFinite] :
    AddCommGroup β.toTripleData.S := β.toTripleData.addS
instance (priority := high) BoundedFinite.instModS [β : BoundedFinite] :
    Module ℂ β.toTripleData.S := β.toTripleData.modS

-- ============================================================================
-- §3. Single-factor T1 lemmas (one variable: TC is unambiguous here)
-- ============================================================================

section SingleFactor

variable [β : BoundedAnalyticTriple]

/-- Pointwise `nrm`-bounds compose multiplicatively (Tier T1 — proved):
    if `nrm (R x) ≤ C₁ * nrm x` and `nrm (T x) ≤ C₂ * nrm x` with
    `0 ≤ C₁`, then `nrm ((R * T) x) ≤ (C₁ * C₂) * nrm x`.
    The operator-norm-style lemma behind the `K = C_M * C'_F + C''_M * C_F`
    bookkeeping for the product commutator. -/
theorem nrm_comp_bound (R T : Module.End ℂ β.toTripleData.S) (C₁ C₂ : ℝ)
    (hR : ∀ x, @nrm β.toAnalyticTripleData (R x) ≤ C₁ * @nrm β.toAnalyticTripleData x)
    (hT : ∀ x, @nrm β.toAnalyticTripleData (T x) ≤ C₂ * @nrm β.toAnalyticTripleData x)
    (hC₁ : 0 ≤ C₁) :
    ∀ x, @nrm β.toAnalyticTripleData ((R * T) x)
      ≤ (C₁ * C₂) * @nrm β.toAnalyticTripleData x := by
  intro x
  have e : (R * T) x = R (T x) := rfl
  rw [e]
  calc @nrm β.toAnalyticTripleData (R (T x))
        ≤ C₁ * @nrm β.toAnalyticTripleData (T x) := hR _
    _ ≤ C₁ * (C₂ * @nrm β.toAnalyticTripleData x) :=
        mul_le_mul_of_nonneg_left (hT x) hC₁
    _ = (C₁ * C₂) * @nrm β.toAnalyticTripleData x := by ring

/-- Enrichment breaks nothing at the analytic level (Tier T1 — proved):
    the `AnalyticTriple` T1s apply definitionally to
    `BoundedAnalyticTriple` (here the triangle inequality). -/
theorem bounded_nrm_triangle (x y : β.toTripleData.S) :
    @nrm β.toAnalyticTripleData (x + y)
      ≤ @nrm β.toAnalyticTripleData x + @nrm β.toAnalyticTripleData y :=
  @nrm_triangle β.toAnalyticTripleData x y

end SingleFactor

-- ============================================================================
-- §4. The product for bounded factors (T1)
-- ============================================================================

section ProductFactors

-- The two bounded factors, as section variables with distinct types
-- (see the module docstring on why they must differ).
variable [μ : BoundedManifold] [φ : BoundedFinite]

/-- The product Dirac on bounded factors (Tier T2 — definition):
    `DprodB = D_M ⊗ 1 + Γ_M ⊗ D_F`, built directly on the enriched
    factors' underlying `TripleData`. The Rung-2 product constructions
    need only `TripleData` fields — no `ManifoldFactor`/`FiniteFactor`
    structure — so they re-run verbatim on enriched data. -/
noncomputable def DprodB :
    Module.End ℂ (μ.toTripleData.S ⊗[ℂ] φ.toTripleData.S) :=
  opTensor μ.toTripleData.D 1 + opTensor μ.toTripleData.Γ φ.toTripleData.D

/-- The product representation on elementary tensors, bounded factors
    (Tier T2 — definition): `πprodB f a = π_M(f) ⊗ π_F(a)`. -/
noncomputable def πprodB (f : μ.toTripleData.A) (a : φ.toTripleData.A) :
    Module.End ℂ (μ.toTripleData.S ⊗[ℂ] φ.toTripleData.S) :=
  opTensor (μ.toTripleData.π f) (φ.toTripleData.π a)

/-- **Stability under analytic enrichment** (Tier T1 — proved): the Rung-2
    product Dirac identity re-run on enriched factors —
    `DprodB² = D_M² ⊗ 1 + 1 ⊗ D_F²`. Same proof pattern as `Dprod_sq`
    (cross terms vanish by `hΓD`); enrichment adds data and breaks
    nothing. -/
theorem Dprod_sq_analytic :
    DprodB * DprodB
      = opTensor (μ.toTripleData.D * μ.toTripleData.D) 1
        + opTensor 1 (φ.toTripleData.D * φ.toTripleData.D) := by
  unfold DprodB
  rw [add_mul, mul_add, mul_add, ← opTensor_mul, ← opTensor_mul, ← opTensor_mul,
    ← opTensor_mul]
  simp only [one_mul, mul_one]
  rw [μ.toTripleData.hΓsq, μ.toTripleData.hΓD, opTensor_neg_left]
  abel

/-- **Inner-fluctuation decomposition, bounded factors** (Tier T1 —
    proved): re-runs `prod_commutator_decomp` on enriched data.
    `[DprodB, πprodB f a] = [D_M, π_M f] ⊗ π_F(a)
      + (π_M(f) Γ_M) ⊗ [D_F, π_F a]`.
    Uses evenness of the manifold representation (`hπeven`). -/
theorem prod_commutator_decomp_analytic (f : μ.toTripleData.A) (a : φ.toTripleData.A) :
    DprodB * πprodB f a - πprodB f a * DprodB
      = opTensor (μ.toTripleData.D * μ.toTripleData.π f - μ.toTripleData.π f * μ.toTripleData.D)
          (φ.toTripleData.π a)
        + opTensor (μ.toTripleData.π f * μ.toTripleData.Γ)
          (φ.toTripleData.D * φ.toTripleData.π a - φ.toTripleData.π a * φ.toTripleData.D) := by
  unfold DprodB πprodB
  rw [add_mul, mul_add, ← opTensor_mul, ← opTensor_mul, ← opTensor_mul,
    ← opTensor_mul, one_mul, mul_one, μ.toTripleData.hπeven f, opTensor_sub_left,
    opTensor_sub_right]
  abel

/-- The product commutator on elementary tensors (Tier T1 — proved):
    the decomposition evaluated at `x ⊗ₜ y`. Each summand is an elementary
    tensor whose factor components are individually `nrm`-bounded
    (`prod_commutator_factorBounds`); the two elementary tensors cannot be
    norm-compared without a tensor-product inner product (scoped out —
    see the module docstring). -/
theorem prod_commutator_tmul_analytic (f : μ.toTripleData.A) (a : φ.toTripleData.A)
    (x : μ.toTripleData.S) (y : φ.toTripleData.S) :
    (DprodB * πprodB f a - πprodB f a * DprodB) (x ⊗ₜ[ℂ] y)
      = ((μ.toTripleData.D * μ.toTripleData.π f - μ.toTripleData.π f * μ.toTripleData.D) x
          ⊗ₜ[ℂ] (φ.toTripleData.π a) y)
        + ((μ.toTripleData.π f * μ.toTripleData.Γ) x
          ⊗ₜ[ℂ] (φ.toTripleData.D * φ.toTripleData.π a - φ.toTripleData.π a * φ.toTripleData.D) y) := by
  rw [prod_commutator_decomp_analytic, LinearMap.add_apply]
  unfold opTensor
  rw [TensorProduct.map_tmul, TensorProduct.map_tmul]

/-- **Factor-component norm bounds** (Tier T1 — proved): the constants from
    `hbddComm` / `hbddRep` packaged for the two summands of
    `prod_commutator_tmul_analytic`. With `K = C₁ * C₂ + C₃ * C₄` (via
    `nrm_comp_bound` and the triangle inequality on factor norms) this is
    everything the class data yields toward
    `‖[DprodB, πprodB (f⊗a)](x⊗y)‖ ≤ K · (factor norms)`; the honest
    remainder — a norm on `x ⊗ₜ y` itself, and boundedness of `Γ_M` for
    the `π_M(f) * Γ_M` factor — is pinned in the module docstring. -/
theorem prod_commutator_factorBounds (f : μ.toTripleData.A) (a : φ.toTripleData.A) :
    ∃ C₁ C₂ C₃ : ℝ, 0 ≤ C₁ ∧ 0 ≤ C₂ ∧ 0 ≤ C₃ ∧
      (∀ x : μ.toTripleData.S,
        @nrm μ.toAnalyticTripleData
            ((μ.toTripleData.D * μ.toTripleData.π f - μ.toTripleData.π f * μ.toTripleData.D) x)
          ≤ C₁ * @nrm μ.toAnalyticTripleData x) ∧
      (∀ y : φ.toTripleData.S,
        @nrm φ.toAnalyticTripleData ((φ.toTripleData.π a) y)
          ≤ C₂ * @nrm φ.toAnalyticTripleData y) ∧
      (∀ y : φ.toTripleData.S,
        @nrm φ.toAnalyticTripleData
            ((φ.toTripleData.D * φ.toTripleData.π a - φ.toTripleData.π a * φ.toTripleData.D) y)
          ≤ C₃ * @nrm φ.toAnalyticTripleData y) := by
  obtain ⟨C₁, hC₁, h1⟩ := μ.hbddComm f
  obtain ⟨C₂, hC₂, h2⟩ := φ.hbddRep a
  obtain ⟨C₃, hC₃, h3⟩ := φ.hbddComm a
  exact ⟨C₁, C₂, C₃, hC₁, hC₂, hC₃, h1, h2, h3⟩

end ProductFactors

-- PIN: the full product estimate `‖[DprodB, πprodB (f⊗a)] z‖ ≤ K ‖z‖`
-- needs a tensor-product inner product on `S_M ⊗[ℂ] S_F` (separate task)
-- and boundedness of `Γ` in `nrm` (analytic debt, Rung 4 proper).

#print axioms nrm_comp_bound
#print axioms bounded_nrm_triangle
#print axioms Dprod_sq_analytic
#print axioms prod_commutator_decomp_analytic
#print axioms prod_commutator_tmul_analytic
#print axioms prod_commutator_factorBounds

end ThetLogos
