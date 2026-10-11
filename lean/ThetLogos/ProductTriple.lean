import Mathlib.Tactic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.Algebra.Star.TensorProduct
import Mathlib.RingTheory.TensorProduct.Basic

-- The `[ManifoldFactor]` / `[FiniteFactor]` section variables below trigger
-- the overlapping-instances linter (both extend `TripleData`); the two
-- factors are never unified in this file, so it is a false positive.
set_option linter.overlappingInstances false

namespace ThetLogos

open TensorProduct

/-!
# ThetLogos.ProductTriple — Rung 2: the almost-commutative product (2026-10-08)

MISSION REPivot context: the mission is now rigorous 4D QFT — "succeed where
nobody else has." Rung 1 (finite triple + Connes–Kreimer Hopf skeleton) is
built (`Renormalization.lean`). This module is **Rung 2**: the
almost-commutative product `C^∞(M) ⊗ A_F` with an **axiomatized** manifold
factor (T2) — NOT a continuum construction (that is Rung 3).

Supersession note: the previous `ProductTriple.lean` was T5 scaffolding
(`axiom SpinorHilbert`, `axiom product_sum_of_squares`, ...). It is replaced
by this file: the manifold enters as a T2 class, and the sum-of-squares is
now a T1 theorem (`Dprod_sq`). Per the relabeling rule the old T5 axioms are
dead; the new entries below stand on their own proofs.

## What this file IS
- §1: `TripleData` — axiomatized spectral-triple data as a T2 class
  (algebra, spinor module, representation, Dirac, grading, real structure
  packaged as the LINEAR anti-automorphism `X ↦ JXJ⁻¹`, KO signs —
  PLUS the analytic enrichment: an ALGEBRAIC sesquilinear form `sesq`,
  the true antilinear `Janti` with KO-relation axioms, and the fundamental
  symmetry `ηsym` with `η² = 1` and form-self-adjointness; no
  completeness/boundedness/compact-resolvent assumed).
  `ManifoldFactor` (commutative algebra, KO-dim 4 signs) and `FiniteFactor`
  (KO-dim 6 signs) extend it. NO continuum is constructed: no manifold, no
  spin geometry, no elliptic analysis, no Hilbert inner product.
- §2: operator tensor-product toolkit (`opTensor`, mixed-product law).
- §3: the product triple — `Dprod = D_M ⊗ 1 + Γ_M ⊗ D_F`, `Gprod`,
  product representation; `Gprod² = 1`, `Dprod` odd, sum-of-squares.
- §4: THE KEY THEOREM — the DLM flip twist extends to the product:
  `flipProd` on the doubled product algebra, CM-regular unconditionally;
  on diagonal pairs the twisted commutator IS the ordinary commutator;
  the correct product twist equals `id_M ⊗ flip_F` on common-manifold-factor
  pairs (the naive `ρ_M ⊗ ρ_F` verdict, derived not assumed).
- §6b: the opposite representation as the `conjJ`-shadow (T2:
  `oppProd`, `oppgrandProd`), flip-compatibility discharged in the statable
  DLM form (T1: `oppgrandProd_flip`), the diagonal reduction of the twisted
  FOC to the ordinary product FOC (T1: `prodTwistedFOC_diag_reduce`); the
  true `J·*J⁻¹` opposite is unstatable (exact Lean failures quoted) and the
  ordinary product FOC (`ProdFirstOrderCond`) stays pinned on missing
  factor-level order-one.
- §5: inner-fluctuation decomposition — `[Dprod, f⊗a]` splits into the
  manifold 1-form `[D_M,f]⊗a` (gauge fields) and the finite 1-form
  `Γ_M f⊗[D_F,a]` (scalars); pure-manifold and pure-finite corollaries;
  the honest 6-dim-caveat ledger.
- §6: KO product — signs multiply to KO-dim 2 `(−1,+1,−1)`; the
  conjJ-relations close T1 on elementary tensors; the TRUE antilinear
  `J_prod = J_M ⊗ J_F` (T2) with `J_prod² = −1`, `J_prod Dprod = Dprod J_prod`,
  `J_prod Γ_prod = −Γ_prod J_prod` (T1, from `koProd_signs`); the product
  sesquilinear form `sesqProd` and fundamental symmetry `η_prod = η_M ⊗ η_F`
  (T2) with `η_prod² = 1` and form-self-adjointness (T1).
- §7: one T5 pin with exact obstruction (twisted first-order for the
  product — refined 2026-10-10: `conjJ`-shadow opposite constructed,
  diagonal reduction proved, remaining pins named); promotion notes for
  the two PROMOTED pins (`AntilinearJProd`, `KreinProdPin` — now T2-axiomatized
  with T1 consequences proved).

## Tier ledger
T2 (definitions): `KOSignature`, `TripleData`, `ManifoldFactor`,
  `FiniteFactor`, `opTensor`, `Dprod`, `Gprod`, `πprod`, `πprodLin`,
  `flipProd`, `GprojPlus`, `GprojMinus`, `πgrandProd`, `twistedCommProd`,
  `koProd`, `conjJprodBil`, `conjJprodElem`, `ProdTwistedFirstOrderCond`
  (T5 pin), `Jprod`, `Dprod_tmul`, `Gprod_tmul` (T1 companion lemmas),
  `sesqProdBil`, `sesqProd`, `ηprod`, `oppProd`, `oppgrandProd`,
  `ProdFirstOrderCond` (T2 stated/pinned).
T1 (proved, zero sorrys): `compTriple_starRingEnd`, `opTensor_mul`, `opTensor_one`,
  `opTensor_add_left`, `opTensor_add_right`, `opTensor_smul_left`,
  `opTensor_smul_right`, `opTensor_neg_left`, `opTensor_neg_right`,
  `opTensor_sub_left`, `opTensor_sub_right`, `opTensor_zero_left`,
  `opTensor_zero_right`, `Gprod_sq`, `Dprod_odd`, `Dprod_sq`,
  `πprod_even`, `πprodLin_tmul`, `Gproj_add`, `flipProd_involutive`,
  `flipProd_CM_regular`, `prodTwist_diag_is_ordinary`,
  `prodTwist_factorform`, `prodTwist_general_pair`,
  `prod_commutator_decomp`, `prod_commutator_pureManifold`,
  `prod_commutator_pureFinite`, `koM_valid`, `koF_valid`,
  `koProd_signs`, `koDim_add`, `conjJprodElem_tmul`,
  `conjJprodElem_mul`, `conjJprod_D`, `conjJprod_Γ`,
  `Jprod_tmul`, `Janti_sq_M`, `Janti_sq_F`, `Janti_D_M`, `Janti_Γ_M`,
  `Janti_D_F`, `Janti_Γ_F`, `eps_prod`, `eps''_prod`, `hsignC`, `hsign'C`,
  `Jprod_sq`, `Jprod_D`, `Jprod_Γ`, `Jprod_comp_sq`, `Jprod_comp_D`,
  `Jprod_comp_Γ`, `sesqProd_tmul`, `ηprod_tmul`, `ηprod_sq`, `ηprod_selfadj`,
  `oppProd_tmul`, `oppProd_anti_tmul`, `oppgrandProd_flip`, `oppgrandProd_diag`,
  `prodTwistedFOC_diag_reduce`.
T5 (pinned, not claimed): `ProdTwistedFirstOrderCond` (true `J·*J⁻¹` opposite
  unstatable — no operator adjoint; `conjJ`-shadow opposite constructed T2,
  diagonal reduction T1 — see §6b) and `ProdFirstOrderCond` (needs
  factor-level order-one, absent from `TripleData`); the analytic axioms
  (bounded commutators, compact resolvent — need the continuum: Rung 3).
  PROMOTED (were T5, now T2+T1): `AntilinearJProd` → `Jprod` + KO-relation
  T1s; `KreinProdPin` → `sesqProd`/`ηprod` + T1s (see §7 promotion notes).

NO Lorentzian-signature claims: the Krein/twist structure is carried over
explicitly (§4, §6); `η_prod` is an abstract fundamental symmetry with
`η² = 1` and form-self-adjointness — no spacetime signature is claimed
(the finite Krein signature was (32,32); the killed Lorentzian language
stays killed). The swap fundamental symmetry of `TwistedTriple` is
not re-proved here, only its product-level fate is ledgered.
-/

-- ============================================================================
-- §1. KO signatures and axiomatized triple data (T2)
-- ============================================================================

/-- KO signs `(ε, ε′, ε″)`: `J² = ε`, `JD = ε′DJ`, `JΓ = ε″ΓJ`.
    Tier T2 (structure). -/
structure KOSignature where
  eps : ℤ
  eps' : ℤ
  eps'' : ℤ
deriving DecidableEq, Repr

/-- A KO signature is valid when every sign is `±1`. -/
def KOSignature.Valid (s : KOSignature) : Prop :=
  s.eps ^ 2 = 1 ∧ s.eps' ^ 2 = 1 ∧ s.eps'' ^ 2 = 1

/-- `star ∘ star = id` on ℂ as a `RingHomCompTriple` (Tier T1 — proved).
    This is the instance that lets antilinear maps compose: the composite
    of two `→ₛₗ[starRingEnd ℂ]` maps is `→ₛₗ[RingHom.id ℂ]`, i.e. linear. -/
instance compTriple_starRingEnd : RingHomCompTriple (starRingEnd ℂ) (starRingEnd ℂ) (RingHom.id ℂ) :=
  ⟨by ext x; simp⟩

/-- Axiomatized spectral-triple data (Tier T2 class).

    This is the algebraic shadow of a spectral triple `(A, H, D, Γ, J)`:
    - `A`: the algebra (`C^∞(M)` for the manifold factor, `A_F` finite);
    - `S`: the spinor module (`L²(M,𝓢)` resp. `H_F`) — a bare ℂ-module
      carrying ALGEBRAIC structure only (see `sesq`, `Janti`, `ηsym`
      below): no completeness, no boundedness, no compact resolvent
      (that is Rung-3/continuum data);
    - `π`: the representation; `D`: the Dirac; `Γ`: the grading;
    - `conjJ`: the real structure packaged as the LINEAR anti-automorphism
      `X ↦ JXJ⁻¹` of the operator algebra;
    - `sesq`: a sesquilinear form on `S` — antilinear in the first
      argument, linear in the second. ALGEBRAIC ONLY: NOT assumed
      positive-definite, nondegenerate, or complete (the Krein form is not
      positive anyway);
    - `Janti`: the TRUE antilinear real structure
      (`S →ₛₗ[starRingEnd ℂ] S`), with the KO relations as axioms
      (`hJanti_sq`, `hJanti_D`, `hJanti_Γ`) keyed to `ko`. This promotes
      the old T5 pin `AntilinearJProd` (§7) to T2 data. Note: `conjJ` and
      `Janti` are INDEPENDENT T2 data — their compatibility
      (`conjJ X = JXJ⁻¹`) is not axiomatized;
    - `ηsym`: a fundamental symmetry (`η² = 1`, self-adjoint FOR THE FORM:
      `sesq (ηx) y = sesq x (ηy)` — the honest algebraic content of
      `ηᴴ = η`, with no adjoint operator constructed). This promotes the
      old T5 pin `KreinProdPin` (§7) to T2 data;
    - `ko`: the KO signs, with the `J`-relations as axioms
      (`hkoD`, `hkoΓ`).

    The analytic axioms (bounded `[D, π(f)]`, compact resolvent) are NOT
    part of this class — they need the continuum (Rung 3). -/
class TripleData where
  A : Type
  S : Type
  [addS : AddCommGroup S]
  [modS : Module ℂ S]
  [ringA : Ring A]
  [starA : StarRing A]
  [algA : Algebra ℂ A]
  [starModA : StarModule ℂ A]
  π : A →ₐ[ℂ] Module.End ℂ S
  D : Module.End ℂ S
  Γ : Module.End ℂ S
  hΓsq : Γ * Γ = 1
  hΓD : D * Γ = -(Γ * D)
  hπeven : ∀ f : A, Γ * π f = π f * Γ
  conjJ : Module.End ℂ S →ₗ[ℂ] Module.End ℂ S
  hconjJ_mul : ∀ x y : Module.End ℂ S, conjJ (x * y) = conjJ y * conjJ x
  hconjJ_inv : ∀ x : Module.End ℂ S, conjJ (conjJ x) = x
  hconjJ_one : conjJ 1 = 1
  ko : KOSignature
  hkoD : conjJ D = (ko.eps' : ℂ) • D
  hkoΓ : conjJ Γ = (ko.eps'' : ℂ) • Γ
  sesq : S →ₛₗ[starRingEnd ℂ] (S →ₗ[ℂ] ℂ)
  Janti : S →ₛₗ[starRingEnd ℂ] S
  hJanti_sq : Janti.comp Janti = (ko.eps : ℂ) • LinearMap.id
  hJanti_D : Janti.comp D = (ko.eps' : ℂ) • (D.comp Janti)
  hJanti_Γ : Janti.comp Γ = (ko.eps'' : ℂ) • (Γ.comp Janti)
  ηsym : Module.End ℂ S
  hηsym_sq : ηsym * ηsym = 1
  hηsym_selfadj : ∀ x y : S, sesq (ηsym x) y = sesq x (ηsym y)

/-- The manifold factor (Tier T2 class): a compact spin 4-manifold as
    opaque class data. `M` itself is never constructed — the working
    shadow is the commutative *-algebra `A = C^∞(M)`. KO-dim 4 signs:
    `J_M² = −1`, `J_M D_M = D_M J_M`, `J_M Γ_M = Γ_M J_M`. -/
class ManifoldFactor extends TripleData where
  M : Type
  [commA : CommRing A]
  ko4 : ko = ⟨-1, 1, 1⟩

/-- The finite factor (Tier T2 class): KO-dim 6 signs (the finite SM
    triple: `J_F² = +1`, `J_F D_F = D_F J_F`, `J_F Γ_F = −Γ_F J_F`).
    Kept abstract: instantiating it from the lab's concrete
    `Matrix (Fin 32)` triple is future work (needs the finite real
    structure as `conjJ` data). -/
class FiniteFactor extends TripleData where
  ko6 : ko = ⟨1, 1, -1⟩

-- Projection instances: the class's instance-fields are not found by TC
-- automatically, so they are re-exported here.
instance ManifoldFactor.instAddS [M : ManifoldFactor] :
    AddCommGroup M.toTripleData.S := M.toTripleData.addS
instance ManifoldFactor.instModS [M : ManifoldFactor] :
    Module ℂ M.toTripleData.S := M.toTripleData.modS
instance ManifoldFactor.instRingA [M : ManifoldFactor] :
    Ring M.toTripleData.A := M.toTripleData.ringA
instance ManifoldFactor.instStarA [M : ManifoldFactor] :
    StarRing M.toTripleData.A := M.toTripleData.starA
instance ManifoldFactor.instAlgA [M : ManifoldFactor] :
    Algebra ℂ M.toTripleData.A := M.toTripleData.algA
instance ManifoldFactor.instStarModA [M : ManifoldFactor] :
    StarModule ℂ M.toTripleData.A := M.toTripleData.starModA
-- NOTE: `commA` is deliberately NOT projected as an instance: `Ring A`
-- (via `ringA`) and `CommRing A` (via `commA`) would give two
-- non-definitionally-equal `Semiring A` paths (diamond), breaking
-- `AlgHom.toLinearMap` unification. Commutativity is T2 data, used
-- through the field, not through TC.

instance FiniteFactor.instAddS [F : FiniteFactor] :
    AddCommGroup F.toTripleData.S := F.toTripleData.addS
instance FiniteFactor.instModS [F : FiniteFactor] :
    Module ℂ F.toTripleData.S := F.toTripleData.modS
instance FiniteFactor.instRingA [F : FiniteFactor] :
    Ring F.toTripleData.A := F.toTripleData.ringA
instance FiniteFactor.instStarA [F : FiniteFactor] :
    StarRing F.toTripleData.A := F.toTripleData.starA
instance FiniteFactor.instAlgA [F : FiniteFactor] :
    Algebra ℂ F.toTripleData.A := F.toTripleData.algA
instance FiniteFactor.instStarModA [F : FiniteFactor] :
    StarModule ℂ F.toTripleData.A := F.toTripleData.starModA

/-- The manifold KO signs are valid (Tier T1). -/
theorem koM_valid [μ : ManifoldFactor] : μ.toTripleData.ko.Valid := by
  unfold KOSignature.Valid
  rw [μ.ko4]
  decide

/-- The finite KO signs are valid (Tier T1). -/
theorem koF_valid [φ : FiniteFactor] : φ.toTripleData.ko.Valid := by
  unfold KOSignature.Valid
  rw [φ.ko6]
  decide

-- ============================================================================
-- §2. Operator tensor products (T1 toolkit)
-- ============================================================================

/-- The tensor product of two operators (Tier T2 — definition). -/
noncomputable def opTensor {S₁ S₂ : Type*} [AddCommGroup S₁] [Module ℂ S₁]
    [AddCommGroup S₂] [Module ℂ S₂]
    (X : Module.End ℂ S₁) (Y : Module.End ℂ S₂) :
    Module.End ℂ (S₁ ⊗[ℂ] S₂) :=
  TensorProduct.map X Y

/-- Mixed-product law (Tier T1 — proved). -/
theorem opTensor_mul {S₁ S₂ : Type*} [AddCommGroup S₁] [Module ℂ S₁]
    [AddCommGroup S₂] [Module ℂ S₂]
    (X₁ X₂ : Module.End ℂ S₁) (Y₁ Y₂ : Module.End ℂ S₂) :
    opTensor (X₁ * X₂) (Y₁ * Y₂) = opTensor X₁ Y₁ * opTensor X₂ Y₂ := by
  unfold opTensor
  exact TensorProduct.map_mul X₁ X₂ Y₁ Y₂

/-- `1 ⊗ 1 = 1` (Tier T1 — proved). -/
theorem opTensor_one {S₁ S₂ : Type*} [AddCommGroup S₁] [Module ℂ S₁]
    [AddCommGroup S₂] [Module ℂ S₂] :
    opTensor (1 : Module.End ℂ S₁) (1 : Module.End ℂ S₂) = 1 := by
  unfold opTensor
  exact TensorProduct.map_one

/-- Additivity in the left factor (Tier T1 — proved). -/
theorem opTensor_add_left {S₁ S₂ : Type*} [AddCommGroup S₁] [Module ℂ S₁]
    [AddCommGroup S₂] [Module ℂ S₂]
    (X₁ X₂ : Module.End ℂ S₁) (Y : Module.End ℂ S₂) :
    opTensor (X₁ + X₂) Y = opTensor X₁ Y + opTensor X₂ Y := by
  unfold opTensor
  exact TensorProduct.map_add_left X₁ X₂ Y

/-- Additivity in the right factor (Tier T1 — proved). -/
theorem opTensor_add_right {S₁ S₂ : Type*} [AddCommGroup S₁] [Module ℂ S₁]
    [AddCommGroup S₂] [Module ℂ S₂]
    (X : Module.End ℂ S₁) (Y₁ Y₂ : Module.End ℂ S₂) :
    opTensor X (Y₁ + Y₂) = opTensor X Y₁ + opTensor X Y₂ := by
  unfold opTensor
  exact TensorProduct.map_add_right X Y₁ Y₂

/-- Scalar homogeneity in the left factor (Tier T1 — proved). -/
theorem opTensor_smul_left {S₁ S₂ : Type*} [AddCommGroup S₁] [Module ℂ S₁]
    [AddCommGroup S₂] [Module ℂ S₂]
    (c : ℂ) (X : Module.End ℂ S₁) (Y : Module.End ℂ S₂) :
    opTensor (c • X) Y = c • opTensor X Y := by
  unfold opTensor
  exact TensorProduct.map_smul_left c X Y

/-- Scalar homogeneity in the right factor (Tier T1 — proved). -/
theorem opTensor_smul_right {S₁ S₂ : Type*} [AddCommGroup S₁] [Module ℂ S₁]
    [AddCommGroup S₂] [Module ℂ S₂]
    (c : ℂ) (X : Module.End ℂ S₁) (Y : Module.End ℂ S₂) :
    opTensor X (c • Y) = c • opTensor X Y := by
  unfold opTensor
  exact TensorProduct.map_smul_right c X Y

/-- `0 ⊗ Y = 0` (Tier T1 — proved). -/
theorem opTensor_zero_left {S₁ S₂ : Type*} [AddCommGroup S₁] [Module ℂ S₁]
    [AddCommGroup S₂] [Module ℂ S₂]
    (Y : Module.End ℂ S₂) : opTensor (0 : Module.End ℂ S₁) Y = 0 := by
  have h : (0 : Module.End ℂ S₁) = (0 : ℂ) • 1 := (zero_smul _ _).symm
  rw [h, opTensor_smul_left, zero_smul]

/-- `X ⊗ 0 = 0` (Tier T1 — proved). -/
theorem opTensor_zero_right {S₁ S₂ : Type*} [AddCommGroup S₁] [Module ℂ S₁]
    [AddCommGroup S₂] [Module ℂ S₂]
    (X : Module.End ℂ S₁) : opTensor X (0 : Module.End ℂ S₂) = 0 := by
  have h : (0 : Module.End ℂ S₂) = (0 : ℂ) • 1 := (zero_smul _ _).symm
  rw [h, opTensor_smul_right, zero_smul]

/-- Negation in the left factor (Tier T1 — proved). -/
theorem opTensor_neg_left {S₁ S₂ : Type*} [AddCommGroup S₁] [Module ℂ S₁]
    [AddCommGroup S₂] [Module ℂ S₂]
    (X : Module.End ℂ S₁) (Y : Module.End ℂ S₂) :
    opTensor (-X) Y = -opTensor X Y := by
  apply eq_neg_of_add_eq_zero_left
  rw [← opTensor_add_left, neg_add_cancel, opTensor_zero_left]

/-- Negation in the right factor (Tier T1 — proved). -/
theorem opTensor_neg_right {S₁ S₂ : Type*} [AddCommGroup S₁] [Module ℂ S₁]
    [AddCommGroup S₂] [Module ℂ S₂]
    (X : Module.End ℂ S₁) (Y : Module.End ℂ S₂) :
    opTensor X (-Y) = -opTensor X Y := by
  apply eq_neg_of_add_eq_zero_left
  rw [← opTensor_add_right, neg_add_cancel, opTensor_zero_right]

/-- Subtraction in the left factor (Tier T1 — proved). -/
theorem opTensor_sub_left {S₁ S₂ : Type*} [AddCommGroup S₁] [Module ℂ S₁]
    [AddCommGroup S₂] [Module ℂ S₂]
    (X₁ X₂ : Module.End ℂ S₁) (Y : Module.End ℂ S₂) :
    opTensor (X₁ - X₂) Y = opTensor X₁ Y - opTensor X₂ Y := by
  rw [sub_eq_add_neg, opTensor_add_left, opTensor_neg_left, ← sub_eq_add_neg]

/-- Subtraction in the right factor (Tier T1 — proved). -/
theorem opTensor_sub_right {S₁ S₂ : Type*} [AddCommGroup S₁] [Module ℂ S₁]
    [AddCommGroup S₂] [Module ℂ S₂]
    (X : Module.End ℂ S₁) (Y₁ Y₂ : Module.End ℂ S₂) :
    opTensor X (Y₁ - Y₂) = opTensor X Y₁ - opTensor X Y₂ := by
  rw [sub_eq_add_neg, opTensor_add_right, opTensor_neg_right, ← sub_eq_add_neg]

-- The two factors, as section variables for §§3–7.
variable [μ : ManifoldFactor] [φ : FiniteFactor]

-- ============================================================================
-- §3. The product triple (T2 defs, T1 theorems)
-- ============================================================================

/-- The product Dirac `Dprod = D_M ⊗ 1 + Γ_M ⊗ D_F` (Tier T2 — definition).
    The almost-commutative Dirac: the manifold Dirac tensored with the
    identity, plus the grading-twisted finite Dirac. -/
noncomputable def Dprod :
    Module.End ℂ (μ.toTripleData.S ⊗[ℂ] φ.toTripleData.S) :=
  opTensor μ.toTripleData.D 1 + opTensor μ.toTripleData.Γ φ.toTripleData.D

/-- The product grading `Γ_prod = Γ_M ⊗ Γ_F` (Tier T2 — definition). -/
noncomputable def Gprod :
    Module.End ℂ (μ.toTripleData.S ⊗[ℂ] φ.toTripleData.S) :=
  opTensor μ.toTripleData.Γ φ.toTripleData.Γ

/-- The product representation on elementary tensors (Tier T2 — definition):
    `πprod f a = π_M(f) ⊗ π_F(a)`. -/
noncomputable def πprod (f : μ.toTripleData.A) (a : φ.toTripleData.A) :
    Module.End ℂ (μ.toTripleData.S ⊗[ℂ] φ.toTripleData.S) :=
  opTensor (μ.toTripleData.π f) (φ.toTripleData.π a)

/-- `Γ_prod² = 1` (Tier T1 — proved). -/
theorem Gprod_sq : Gprod * Gprod = 1 := by
  unfold Gprod
  rw [← opTensor_mul, μ.toTripleData.hΓsq, φ.toTripleData.hΓsq, opTensor_one]

/-- `Dprod` is odd for the product grading (Tier T1 — proved):
    `Dprod * Γ_prod = −Γ_prod * Dprod`. -/
theorem Dprod_odd : Dprod * Gprod = -(Gprod * Dprod) := by
  rw [eq_neg_iff_add_eq_zero]
  unfold Dprod Gprod
  rw [add_mul, mul_add, ← opTensor_mul, ← opTensor_mul, ← opTensor_mul,
    ← opTensor_mul]
  simp only [one_mul, mul_one]
  rw [μ.toTripleData.hΓsq, μ.toTripleData.hΓD, φ.toTripleData.hΓD,
    opTensor_neg_left, opTensor_neg_right]
  abel

/-- Sum-of-squares (Tier T1 — proved):
    `Dprod² = D_M² ⊗ 1 + 1 ⊗ D_F²`.
    The cross terms `(D_M Γ_M + Γ_M D_M) ⊗ D_F` vanish by the oddness
    axiom `hΓD`. This is the T1 upgrade of the old file's T5
    `product_sum_of_squares` axiom (now dead, per the supersession note). -/
theorem Dprod_sq :
    Dprod * Dprod
      = opTensor (μ.toTripleData.D * μ.toTripleData.D) 1
        + opTensor 1 (φ.toTripleData.D * φ.toTripleData.D) := by
  unfold Dprod
  rw [add_mul, mul_add, mul_add, ← opTensor_mul, ← opTensor_mul, ← opTensor_mul,
    ← opTensor_mul]
  simp only [one_mul, mul_one]
  rw [μ.toTripleData.hΓsq, μ.toTripleData.hΓD, opTensor_neg_left]
  abel

/-- The product representation lands in even operators (Tier T1 — proved):
    `Γ_prod` commutes with `πprod f a` (both factors even). -/
theorem πprod_even (f : μ.toTripleData.A) (a : φ.toTripleData.A) :
    Gprod * πprod f a = πprod f a * Gprod := by
  unfold Gprod πprod
  rw [← opTensor_mul, ← opTensor_mul, μ.toTripleData.hπeven f,
    φ.toTripleData.hπeven a]

/-- The linear extension of `πprod` to the tensor-product algebra
    (Tier T2 — definition): `πprodLin (f ⊗ₜ a) = πprod f a`. -/
noncomputable def opTensorLin :
    Module.End ℂ μ.toTripleData.S ⊗[ℂ] Module.End ℂ φ.toTripleData.S →ₗ[ℂ]
      Module.End ℂ (μ.toTripleData.S ⊗[ℂ] φ.toTripleData.S) :=
  TensorProduct.lift
    (LinearMap.mk₂ ℂ (fun X Y => opTensor X Y)
      (fun X₁ X₂ Y => by
        show opTensor (X₁ + X₂) Y = _
        rw [opTensor_add_left])
      (fun c X Y => by
        show opTensor (c • X) Y = _
        rw [opTensor_smul_left])
      (fun X Y₁ Y₂ => by
        show opTensor X (Y₁ + Y₂) = _
        rw [opTensor_add_right])
      (fun c X Y => by
        show opTensor X (c • Y) = _
        rw [opTensor_smul_right]))

/-- The product representation as a linear map on `A_M ⊗ A_F`
    (Tier T2 — definition). -/
noncomputable def πprodLin :
    μ.toTripleData.A ⊗[ℂ] φ.toTripleData.A →ₗ[ℂ]
      Module.End ℂ (μ.toTripleData.S ⊗[ℂ] φ.toTripleData.S) :=
  opTensorLin.comp
    (TensorProduct.map μ.toTripleData.π.toLinearMap φ.toTripleData.π.toLinearMap)

/-- `πprodLin` agrees with `πprod` on elementary tensors (Tier T1 — proved). -/
theorem πprodLin_tmul (f : μ.toTripleData.A) (a : φ.toTripleData.A) :
    πprodLin (f ⊗ₜ[ℂ] a) = πprod f a := by
  unfold πprodLin πprod opTensorLin
  rw [LinearMap.comp_apply, TensorProduct.map_tmul, TensorProduct.lift.tmul]
  rfl

-- ============================================================================
-- §4. THE KEY THEOREM: the DLM flip twist extends to the product
-- ============================================================================

/-!
**The product-twist verdict (derived, not assumed).**

The DLM minimal twist by grading applies to ANY graded triple — hence to
the product triple `(A_M ⊗ A_F, S_M ⊗ S_F, Dprod, Gprod)`: the grand
product algebra is the DOUBLED product algebra
`(A_M ⊗ A_F) × (A_M ⊗ A_F)`, and the twist is the FLIP
(`flipProd`, T2 below).

What about the naive `ρ_M ⊗ ρ_F`?
- The manifold factor is UNTWISTED (the canonical triple carries no
  twist), so `ρ_M = id`.
- The finite twist `ρ_F = flip_F` acts on the doubled FINITE algebra.
- On elementary pairs sharing the manifold tensor factor,
  `flipProd ((f⊗a),(f⊗a')) = ((f⊗a'),(f⊗a))` — exactly `id_M ⊗ flip_F`
  (`prodTwist_factorform`, T1, by `rfl`).
- On general pairs `((f⊗a),(g⊗b))` the flip gives `((g⊗b),(f⊗a))`
  (`prodTwist_general_pair`, T1, by `rfl`), while the factorwise candidate
  would give `((f⊗b),(g⊗a))` — genuinely different. The flip does NOT
  factor across the tensor product.

So: the correct product twist IS the flip on the doubled product algebra;
it restricts to `id_M ⊗ flip_F` precisely on the subalgebra of pairs with
common manifold factor — which contains the physical diagonal, where the
twisted commutator is the ordinary commutator
(`prodTwist_diag_is_ordinary`, T1). The twisted first-order condition for
the product is pinned T5 (`ProdTwistedFirstOrderCond`) with the exact
obstruction.
-/

omit μ φ in
/-- The product twist: the FLIP on the doubled product algebra
    (Tier T2 — definition). The DLM minimal twist by grading applied to
    the product triple. -/
def flipProd {T : Type*} (x : T × T) : T × T := (x.2, x.1)

omit μ φ in
/-- The flip is involutive (Tier T1 — proved). -/
theorem flipProd_involutive {T : Type*} (x : T × T) :
    flipProd (flipProd x) = x := by
  obtain ⟨a, b⟩ := x
  rfl

omit μ φ in
/-- Connes–Moscovici regularity for the product flip (Tier T1 — proved):
    UNCONDITIONAL — the flip is its own inverse and commutes with `⋆`
    componentwise. Same one-line proof as
    `TwistedTriple.flipTwist_CM_regular`; the Krein/twist structure is
    carried over explicitly, with no Lorentzian claim. -/
theorem flipProd_CM_regular {T : Type*} [Star T] (x : T × T) :
    flipProd (star x) = star (flipProd x) := by
  obtain ⟨a, b⟩ := x
  rfl

/-- CM-regularity for the flip on the doubled product algebra (Tier T1):
    the general `flipProd_CM_regular` applied to
    `(A_M ⊗ A_F) × (A_M ⊗ A_F)` (the `Star` instance is
    `Mathlib.Algebra.Star.TensorProduct`, via the `StarModule ℂ`
    class fields). -/
theorem prodFlip_CM_regular
    (x : (μ.toTripleData.A ⊗[ℂ] φ.toTripleData.A) × (μ.toTripleData.A ⊗[ℂ] φ.toTripleData.A)) :
    flipProd (star x) = star (flipProd x) :=
  flipProd_CM_regular x

/-- The product grading projectors `P₊ = (1+Γ_prod)/2`, `P₋ = (1−Γ_prod)/2`
    (Tier T2 — definitions). -/
noncomputable def GprojPlus :
    Module.End ℂ (μ.toTripleData.S ⊗[ℂ] φ.toTripleData.S) :=
  (2 : ℂ)⁻¹ • (1 + Gprod)

noncomputable def GprojMinus :
    Module.End ℂ (μ.toTripleData.S ⊗[ℂ] φ.toTripleData.S) :=
  (2 : ℂ)⁻¹ • (1 - Gprod)

/-- `P₊ + P₋ = 1` (Tier T1 — proved). -/
theorem Gproj_add : GprojPlus + GprojMinus = 1 := by
  unfold GprojPlus GprojMinus
  have e : (1 + Gprod) + (1 - Gprod)
      = (2 : ℂ) • (1 : Module.End ℂ (μ.toTripleData.S ⊗[ℂ] φ.toTripleData.S)) := by
    have h2 : (2 : ℂ) = (1 : ℂ) + 1 := by norm_num
    rw [h2, add_smul, one_smul]
    abel
  rw [← smul_add, e, smul_smul, inv_mul_cancel₀ (by norm_num : (2 : ℂ) ≠ 0),
    one_smul]

/-- The doubled product representation (Tier T2 — definition):
    `πgrandProd (t,t') = P₊ πprodLin(t) + P₋ πprodLin(t')`. -/
noncomputable def πgrandProd
    (x : (μ.toTripleData.A ⊗[ℂ] φ.toTripleData.A) × (μ.toTripleData.A ⊗[ℂ] φ.toTripleData.A)) :
    Module.End ℂ (μ.toTripleData.S ⊗[ℂ] φ.toTripleData.S) :=
  GprojPlus * πprodLin x.1 + GprojMinus * πprodLin x.2

/-- The twisted commutator for the product (Tier T2 — definition):
    `[Dprod, x]_flip = Dprod · πgrandProd(x) − πgrandProd(flipProd x) · Dprod`. -/
noncomputable def twistedCommProd
    (x : (μ.toTripleData.A ⊗[ℂ] φ.toTripleData.A) × (μ.toTripleData.A ⊗[ℂ] φ.toTripleData.A)) :
    Module.End ℂ (μ.toTripleData.S ⊗[ℂ] φ.toTripleData.S) :=
  Dprod * πgrandProd x - πgrandProd (flipProd x) * Dprod

/-- On diagonal pairs the twisted commutator IS the ordinary commutator
    (Tier T1 — proved): the flip fixes `(t,t)`, and `P₊ + P₋ = 1`.
    This is the product analog of `TwistedTriple.twistedCommGrand_diag`. -/
theorem prodTwist_diag_is_ordinary (t : μ.toTripleData.A ⊗[ℂ] φ.toTripleData.A) :
    twistedCommProd (t, t)
      = Dprod * πprodLin t - πprodLin t * Dprod := by
  unfold twistedCommProd πgrandProd
  have hflip : flipProd (t, t) = (t, t) := rfl
  rw [hflip]
  have hproj : GprojPlus * πprodLin (t, t).1 + GprojMinus * πprodLin (t, t).2
      = πprodLin t := by
    show GprojPlus * πprodLin t + GprojMinus * πprodLin t = πprodLin t
    rw [← add_mul, Gproj_add, one_mul]
  rw [hproj]

/-- The product twist verdict, factor form (Tier T1 — proved): on pairs
    sharing the manifold tensor factor, the flip IS `id_M ⊗ flip_F`.
    By `rfl` — definitional. -/
theorem prodTwist_factorform (f : μ.toTripleData.A) (a a' : φ.toTripleData.A) :
    flipProd ((f ⊗ₜ[ℂ] a : μ.toTripleData.A ⊗[ℂ] φ.toTripleData.A), (f ⊗ₜ[ℂ] a'))
      = ((f ⊗ₜ[ℂ] a'), (f ⊗ₜ[ℂ] a)) :=
  rfl

/-- The flip on a general elementary pair (Tier T1 — proved): it gives
    `((g⊗b),(f⊗a))` — compare the factorwise candidate `((f⊗b),(g⊗a))`.
    The flip does not factor across the tensor product. By `rfl`. -/
theorem prodTwist_general_pair (f g : μ.toTripleData.A) (a b : φ.toTripleData.A) :
    flipProd ((f ⊗ₜ[ℂ] a : μ.toTripleData.A ⊗[ℂ] φ.toTripleData.A), (g ⊗ₜ[ℂ] b))
      = ((g ⊗ₜ[ℂ] b), (f ⊗ₜ[ℂ] a)) :=
  rfl

/-- The twisted first-order condition for the product (Tier T5 — PINNED):
    `[[Dprod,x]_flip, y°] = 0` for the doubled product algebra.
    REFINED obstruction (2026-10-10, Rung 3 Worker 2): the `conjJ`-shadow
    opposite representations ARE now constructed T2 (`oppProd` undoubled,
    `oppgrandProd` doubled, §6b), flip-compatibility is discharged in the
    statable DLM form (`oppgrandProd_flip`, T1), and the condition reduces
    T1 on diagonal pairs to the ordinary product FOC
    (`prodTwistedFOC_diag_reduce`, T1). What remains pinned:
    (a) the TRUE opposite `a° = J a* J⁻¹` is unstatable — no operator
    adjoint (`Star (Module.End ℂ _)` fails to synthesize), `Jprod` is
    semilinear (no `HMul`/`Inv` instances), and (b) `ProdFirstOrderCond`
    needs factor-level order-one relations absent from `TripleData`. -/
def ProdTwistedFirstOrderCond
    (opp : ((μ.toTripleData.A ⊗[ℂ] φ.toTripleData.A) × (μ.toTripleData.A ⊗[ℂ] φ.toTripleData.A))
      → Module.End ℂ (μ.toTripleData.S ⊗[ℂ] φ.toTripleData.S)) : Prop :=
  ∀ x y : (μ.toTripleData.A ⊗[ℂ] φ.toTripleData.A) × (μ.toTripleData.A ⊗[ℂ] φ.toTripleData.A),
    twistedCommProd x * opp y - opp (flipProd y) * twistedCommProd x = 0

-- ============================================================================
-- §5. Inner fluctuations of the product (T1 decomposition + honest ledger)
-- ============================================================================

/-!
## Honest ledger: what the product gives vs the finite algebra alone

- The finite factor alone: inner fluctuations `Σ a_k[D_F,b_k]` are
  CONSTANT matrices — gauge parameters, not gauge fields. Per the
  gauge-data reconciliation flag in `UltimateReduction.lean`, the
  represented finite gauge algebra is 6-dimensional real (Option-A kills
  `M₃(ℂ)` in the representation) — the full SM symmetry claim needs the
  manifold factor. The finite algebra alone cannot produce
  spacetime-dependent gauge fields.
- The product: 1-forms `Σ (f_k⊗a_k)[Dprod, g_k⊗b_k]` decompose
  (`prod_commutator_decomp`, T1) into `[D_M,f]⊗a` terms — genuine gauge
  fields (Lie-algebra-valued 1-forms on `M`) — and `Γ_M f⊗[D_F,a]` terms
  (scalars, the Higgs sector). The manifold factor is what promotes
  constant gauge parameters to spacetime-dependent gauge fields.
- `prod_commutator_pureManifold` / `prod_commutator_pureFinite` exhibit
  the two summands separately: the finite fluctuations sit inside the
  product dressed by `Γ_M`; the manifold fluctuations are untouched by
  the finite factor.
-/

/-- **Inner-fluctuation decomposition (Tier T1 — proved).**
    `[Dprod, πprod f a] = [D_M, π_M f] ⊗ π_F(a) + (π_M(f) Γ_M) ⊗ [D_F, π_F a]`.
    The first summand is the manifold 1-form (gauge fields); the second is
    the finite 1-form (scalars), dressed by `Γ_M`. Uses evenness of the
    manifold representation (`hπeven`) to move `Γ_M` past `π_M(f)`. -/
theorem prod_commutator_decomp (f : μ.toTripleData.A) (a : φ.toTripleData.A) :
    Dprod * πprod f a - πprod f a * Dprod
      = opTensor (μ.toTripleData.D * μ.toTripleData.π f - μ.toTripleData.π f * μ.toTripleData.D)
          (φ.toTripleData.π a)
        + opTensor (μ.toTripleData.π f * μ.toTripleData.Γ)
          (φ.toTripleData.D * φ.toTripleData.π a - φ.toTripleData.π a * φ.toTripleData.D) := by
  unfold Dprod πprod
  rw [add_mul, mul_add, ← opTensor_mul, ← opTensor_mul, ← opTensor_mul,
    ← opTensor_mul, one_mul, mul_one, μ.toTripleData.hπeven f, opTensor_sub_left,
    opTensor_sub_right]
  abel

/-- Pure-manifold fluctuations (Tier T1 — proved): for `a = 1`,
    `[Dprod, f⊗1] = [D_M, f] ⊗ 1` — the finite factor is untouched. -/
theorem prod_commutator_pureManifold (f : μ.toTripleData.A) :
    Dprod * πprod f 1 - πprod f 1 * Dprod
      = opTensor (μ.toTripleData.D * μ.toTripleData.π f - μ.toTripleData.π f * μ.toTripleData.D) 1 := by
  have h := prod_commutator_decomp f 1
  rw [map_one, mul_one, one_mul, sub_self, opTensor_zero_right, add_zero] at h
  exact h

/-- Pure-finite fluctuations (Tier T1 — proved): for `f = 1`,
    `[Dprod, 1⊗a] = Γ_M ⊗ [D_F, a]` — the finite 1-forms embed into the
    product dressed by the manifold grading. -/
theorem prod_commutator_pureFinite (a : φ.toTripleData.A) :
    Dprod * πprod 1 a - πprod 1 a * Dprod
      = opTensor μ.toTripleData.Γ
          (φ.toTripleData.D * φ.toTripleData.π a - φ.toTripleData.π a * φ.toTripleData.D) := by
  have h := prod_commutator_decomp 1 a
  rw [map_one, mul_one, one_mul, sub_self, opTensor_zero_left, zero_add] at h
  exact h

-- ============================================================================
-- §6. KO-dimension of the product (T2 defs, T1 on the sign data)
-- ============================================================================

/-!
KO-dimension adds mod 8 across the product. The manifold factor has
KO-dim 4, the finite factor KO-dim 6; `4 + 6 = 10 ≡ 2 (mod 8)`, and the
sign data multiplies to the KO-dim-2 row `(ε,ε′,ε″) = (−1,+1,−1)`:
`J_prod² = −1`, `J_prod Dprod = Dprod J_prod`, `J_prod Γ_prod = −Γ_prod J_prod`.
The `ε′` and `ε″` relations close T1 on elementary tensors via
`conjJprodElem` (`conjJprod_D`, `conjJprod_Γ`); the true antilinear `J_prod`
closes T1 below (`Jprod_sq`, `Jprod_D`, `Jprod_Γ` — the `AntilinearJProd`
promotion), as does the Krein fundamental symmetry (`ηprod_sq`,
`ηprod_selfadj` — the `KreinProdPin` promotion).
-/

/-- The product KO signature (Tier T2 — definition): signs multiply.
    `ε′_prod = +1` is forced by the factor relations (proved in
    `conjJprod_D`); it is not an independent axiom. -/
def koProd : KOSignature :=
  ⟨μ.toTripleData.ko.eps * φ.toTripleData.ko.eps, 1,
    μ.toTripleData.ko.eps'' * φ.toTripleData.ko.eps''⟩

/-- The product signs are the KO-dim-2 row `(−1,+1,−1)` (Tier T1 — proved). -/
theorem koProd_signs : koProd = ⟨-1, 1, -1⟩ := by
  unfold koProd
  rw [μ.ko4, φ.ko6]
  decide

omit μ φ in
/-- KO-dimension adds mod 8: `4 + 6 ≡ 2` (Tier T1 — proved). -/
theorem koDim_add : (4 + 6) % 8 = 2 := rfl

/-- The product real-structure shadow on elementary operator tensors
    (Tier T2 — definition):
    `conjJprodElem (X ⊗ₜ Y) = conjJ_M(X) ⊗ₜ conjJ_F(Y)`.
    The true antilinear `J_prod = J_M ⊗ J_F` is now T2+T1 below (`Jprod`);
    this linear anti-automorphism remains its shadow, sufficient for the
    KO-sign relations on its own. -/
noncomputable def conjJprodBil :
    Module.End ℂ μ.toTripleData.S →ₗ[ℂ] Module.End ℂ φ.toTripleData.S →ₗ[ℂ]
      Module.End ℂ (μ.toTripleData.S ⊗[ℂ] φ.toTripleData.S) :=
  LinearMap.mk₂ ℂ (fun X Y => opTensor (μ.toTripleData.conjJ X) (φ.toTripleData.conjJ Y))
    (fun X₁ X₂ Y => by
      show opTensor (μ.toTripleData.conjJ (X₁ + X₂)) (φ.toTripleData.conjJ Y) = _
      rw [map_add, opTensor_add_left])
    (fun c X Y => by
      show opTensor (μ.toTripleData.conjJ (c • X)) (φ.toTripleData.conjJ Y) = _
      rw [map_smul, opTensor_smul_left])
    (fun X Y₁ Y₂ => by
      show opTensor (μ.toTripleData.conjJ X) (φ.toTripleData.conjJ (Y₁ + Y₂)) = _
      rw [map_add, opTensor_add_right])
    (fun c X Y => by
      show opTensor (μ.toTripleData.conjJ X) (φ.toTripleData.conjJ (c • Y)) = _
      rw [map_smul, opTensor_smul_right])

/-- The product `conjJ` as a linear map on operator tensors
    (Tier T2 — definition). -/
noncomputable def conjJprodElem :
    Module.End ℂ μ.toTripleData.S ⊗[ℂ] Module.End ℂ φ.toTripleData.S →ₗ[ℂ]
      Module.End ℂ (μ.toTripleData.S ⊗[ℂ] φ.toTripleData.S) :=
  TensorProduct.lift conjJprodBil

/-- Evaluation on elementary tensors (Tier T1 — proved). -/
theorem conjJprodElem_tmul (X : Module.End ℂ μ.toTripleData.S)
    (Y : Module.End ℂ φ.toTripleData.S) :
    conjJprodElem (X ⊗ₜ[ℂ] Y)
      = opTensor (μ.toTripleData.conjJ X) (φ.toTripleData.conjJ Y) := by
  unfold conjJprodElem
  rw [TensorProduct.lift.tmul]
  rfl

/-- `conjJprodElem` is anti-multiplicative on elementary tensors
    (Tier T1 — proved): the shadow is a genuine anti-automorphism. -/
theorem conjJprodElem_mul (X₁ X₂ : Module.End ℂ μ.toTripleData.S)
    (Y₁ Y₂ : Module.End ℂ φ.toTripleData.S) :
    conjJprodElem ((X₁ ⊗ₜ[ℂ] Y₁) * (X₂ ⊗ₜ[ℂ] Y₂))
      = conjJprodElem (X₂ ⊗ₜ[ℂ] Y₂) * conjJprodElem (X₁ ⊗ₜ[ℂ] Y₁) := by
  rw [Algebra.TensorProduct.tmul_mul_tmul, conjJprodElem_tmul, conjJprodElem_tmul,
    conjJprodElem_tmul, μ.toTripleData.hconjJ_mul, φ.toTripleData.hconjJ_mul,
    ← opTensor_mul]

/-- The product KO relation for `D` (Tier T1 — proved):
    `conjJ_prod(D_M ⊗ₜ 1 + Γ_M ⊗ₜ D_F) = Dprod`, i.e. `ε′_prod = +1`.
    Uses `ε′_M = ε″_M = ε′_F = 1` from the sign data (`μ.ko4`, `φ.ko6`). -/
theorem conjJprod_D :
    conjJprodElem
        ((μ.toTripleData.D ⊗ₜ[ℂ] (1 : Module.End ℂ φ.toTripleData.S))
          + (μ.toTripleData.Γ ⊗ₜ[ℂ] φ.toTripleData.D))
      = Dprod := by
  have hD : μ.toTripleData.conjJ μ.toTripleData.D = μ.toTripleData.D := by
    have hcast : (μ.toTripleData.ko.eps' : ℂ) = 1 := by rw [μ.ko4]; norm_num
    rw [μ.toTripleData.hkoD, hcast]; simp
  have hΓ : μ.toTripleData.conjJ μ.toTripleData.Γ = μ.toTripleData.Γ := by
    have hcast : (μ.toTripleData.ko.eps'' : ℂ) = 1 := by rw [μ.ko4]; norm_num
    rw [μ.toTripleData.hkoΓ, hcast]; simp
  have hDF : φ.toTripleData.conjJ φ.toTripleData.D = φ.toTripleData.D := by
    have hcast : (φ.toTripleData.ko.eps' : ℂ) = 1 := by rw [φ.ko6]; norm_num
    rw [φ.toTripleData.hkoD, hcast]; simp
  have h1 : φ.toTripleData.conjJ (1 : Module.End ℂ φ.toTripleData.S) = 1 :=
    φ.toTripleData.hconjJ_one
  rw [map_add, conjJprodElem_tmul, conjJprodElem_tmul, hD, hΓ, hDF, h1]
  rfl

/-- The product KO relation for `Γ` (Tier T1 — proved):
    `conjJ_prod(Γ_M ⊗ₜ Γ_F) = −Γ_prod`, i.e. `ε″_prod = −1 = ε″_M · ε″_F`. -/
theorem conjJprod_Γ :
    conjJprodElem (μ.toTripleData.Γ ⊗ₜ[ℂ] φ.toTripleData.Γ) = -Gprod := by
  have hΓM : μ.toTripleData.conjJ μ.toTripleData.Γ = μ.toTripleData.Γ := by
    have hcast : (μ.toTripleData.ko.eps'' : ℂ) = 1 := by rw [μ.ko4]; norm_num
    rw [μ.toTripleData.hkoΓ, hcast]; simp
  have hΓF : φ.toTripleData.conjJ φ.toTripleData.Γ = -φ.toTripleData.Γ := by
    have hcast : (φ.toTripleData.ko.eps'' : ℂ) = -1 := by rw [φ.ko6]; norm_num
    rw [φ.toTripleData.hkoΓ, hcast]; simp
  rw [conjJprodElem_tmul, hΓM, hΓF, opTensor_neg_right]
  rfl

/-!
## The true antilinear `J_prod` (T2+T1) — promotes the `AntilinearJProd` pin

The T2 enrichment of `TripleData` carries the antilinear real structures
as class data (`Janti`, with the KO relations as axioms keyed to `ko`).
The product `J_prod = J_M ⊗ J_F` is then a genuine antilinear map
(semilinear over `starRingEnd ℂ`), built with the semilinear
`TensorProduct.map`. Its KO relations close T1:
- `J_prod² = −1`: `(ε_M · ε_F) = −1` is the `ε`-component of `koProd_signs`
  (KO-dim 2 mod 8);
- `J_prod Dprod = Dprod J_prod`: from `ε′_M = ε″_M = ε′_F = 1` (factor data);
- `J_prod Γ_prod = −Γ_prod J_prod`: `(ε″_M · ε″_F) = −1` is the `ε″`-component
  of `koProd_signs`.

ASSUMED (T2 class data): `Janti`, `hJanti_sq`, `hJanti_D`, `hJanti_Γ` per factor.
PROVED (T1): everything below.
-/

/-- The true product real structure `J_prod = J_M ⊗ J_F` (Tier T2 — definition).
    A genuine ANTILINEAR map (`→ₛₗ[starRingEnd ℂ]`), via the semilinear
    `TensorProduct.map`. -/
noncomputable def Jprod : (μ.toTripleData.S ⊗[ℂ] φ.toTripleData.S) →ₛₗ[starRingEnd ℂ]
    (μ.toTripleData.S ⊗[ℂ] φ.toTripleData.S) :=
  TensorProduct.map μ.toTripleData.Janti φ.toTripleData.Janti

/-- `J_prod` on elementary tensors (Tier T1 — proved). -/
theorem Jprod_tmul (x : μ.toTripleData.S) (y : φ.toTripleData.S) :
    Jprod (x ⊗ₜ[ℂ] y) = μ.toTripleData.Janti x ⊗ₜ[ℂ] φ.toTripleData.Janti y :=
  TensorProduct.map_tmul _ _ _ _

/-- `Dprod` on elementary tensors (Tier T1 — proved). -/
theorem Dprod_tmul (x : μ.toTripleData.S) (y : φ.toTripleData.S) :
    Dprod (x ⊗ₜ[ℂ] y)
      = (μ.toTripleData.D x ⊗ₜ[ℂ] y) + (μ.toTripleData.Γ x ⊗ₜ[ℂ] φ.toTripleData.D y) := by
  unfold Dprod opTensor
  rw [LinearMap.add_apply, TensorProduct.map_tmul, TensorProduct.map_tmul]
  simp

/-- `Gprod` on elementary tensors (Tier T1 — proved). -/
theorem Gprod_tmul (x : μ.toTripleData.S) (y : φ.toTripleData.S) :
    Gprod (x ⊗ₜ[ℂ] y) = μ.toTripleData.Γ x ⊗ₜ[ℂ] φ.toTripleData.Γ y := by
  unfold Gprod opTensor
  exact TensorProduct.map_tmul _ _ _ _

-- Pointwise forms of the factor KO axioms (Tier T1 — proved from class data).
omit φ in
theorem Janti_sq_M (x : μ.toTripleData.S) :
    μ.toTripleData.Janti (μ.toTripleData.Janti x) = (μ.toTripleData.ko.eps : ℂ) • x := by
  have h := congrFun (congrArg DFunLike.coe μ.toTripleData.hJanti_sq) x
  simpa [LinearMap.comp_apply] using h

omit μ in
theorem Janti_sq_F (y : φ.toTripleData.S) :
    φ.toTripleData.Janti (φ.toTripleData.Janti y) = (φ.toTripleData.ko.eps : ℂ) • y := by
  have h := congrFun (congrArg DFunLike.coe φ.toTripleData.hJanti_sq) y
  simpa [LinearMap.comp_apply] using h

omit φ in
theorem Janti_D_M (x : μ.toTripleData.S) :
    μ.toTripleData.Janti (μ.toTripleData.D x)
      = (μ.toTripleData.ko.eps' : ℂ) • μ.toTripleData.D (μ.toTripleData.Janti x) := by
  have h := congrFun (congrArg DFunLike.coe μ.toTripleData.hJanti_D) x
  simpa [LinearMap.comp_apply] using h

omit φ in
theorem Janti_Γ_M (x : μ.toTripleData.S) :
    μ.toTripleData.Janti (μ.toTripleData.Γ x)
      = (μ.toTripleData.ko.eps'' : ℂ) • μ.toTripleData.Γ (μ.toTripleData.Janti x) := by
  have h := congrFun (congrArg DFunLike.coe μ.toTripleData.hJanti_Γ) x
  simpa [LinearMap.comp_apply] using h

omit μ in
theorem Janti_D_F (y : φ.toTripleData.S) :
    φ.toTripleData.Janti (φ.toTripleData.D y)
      = (φ.toTripleData.ko.eps' : ℂ) • φ.toTripleData.D (φ.toTripleData.Janti y) := by
  have h := congrFun (congrArg DFunLike.coe φ.toTripleData.hJanti_D) y
  simpa [LinearMap.comp_apply] using h

omit μ in
theorem Janti_Γ_F (y : φ.toTripleData.S) :
    φ.toTripleData.Janti (φ.toTripleData.Γ y)
      = (φ.toTripleData.ko.eps'' : ℂ) • φ.toTripleData.Γ (φ.toTripleData.Janti y) := by
  have h := congrFun (congrArg DFunLike.coe φ.toTripleData.hJanti_Γ) y
  simpa [LinearMap.comp_apply] using h

/-- `ε_M · ε_F = −1`: the `ε`-component of `koProd_signs` (Tier T1 — proved). -/
theorem eps_prod : μ.toTripleData.ko.eps * φ.toTripleData.ko.eps = -1 := by
  have h2 := congrArg KOSignature.eps koProd_signs
  simp only [koProd] at h2
  exact h2

/-- `ε″_M · ε″_F = −1`: the `ε″`-component of `koProd_signs` (Tier T1 — proved). -/
theorem eps''_prod : μ.toTripleData.ko.eps'' * φ.toTripleData.ko.eps'' = -1 := by
  have h2 := congrArg KOSignature.eps'' koProd_signs
  simp only [koProd] at h2
  exact h2

/-- Cast of `eps_prod` to ℂ (Tier T1 — proved). -/
theorem hsignC : (μ.toTripleData.ko.eps : ℂ) * (φ.toTripleData.ko.eps : ℂ) = -1 := by
  have h : ((μ.toTripleData.ko.eps * φ.toTripleData.ko.eps : ℤ) : ℂ) = -1 := by
    rw [eps_prod]; norm_num
  rwa [Int.cast_mul] at h

/-- Cast of `eps''_prod` to ℂ (Tier T1 — proved). -/
theorem hsign'C : (μ.toTripleData.ko.eps'' : ℂ) * (φ.toTripleData.ko.eps'' : ℂ) = -1 := by
  have h : ((μ.toTripleData.ko.eps'' * φ.toTripleData.ko.eps'' : ℤ) : ℂ) = -1 := by
    rw [eps''_prod]; norm_num
  rwa [Int.cast_mul] at h

/-- `J_prod² = −1`, pointwise (Tier T1 — proved).
    The sign is `(ε_M · ε_F) = −1` from `koProd_signs` (KO-dim 2 mod 8). -/
theorem Jprod_sq (t : μ.toTripleData.S ⊗[ℂ] φ.toTripleData.S) :
    Jprod (Jprod t) = -t := by
  induction t using TensorProduct.inductionOn with
  | tmul x y =>
    rw [Jprod_tmul, Jprod_tmul, Janti_sq_M, Janti_sq_F,
      TensorProduct.smul_tmul_smul, hsignC, neg_smul, one_smul]
  | add a b ha hb =>
    simp only [map_add, ha, hb, neg_add]

/-- `J_prod Dprod = Dprod J_prod`, pointwise (Tier T1 — proved).
    Uses `ε′_M = ε″_M = ε′_F = 1` from the factor sign data. -/
theorem Jprod_D (t : μ.toTripleData.S ⊗[ℂ] φ.toTripleData.S) :
    Jprod (Dprod t) = Dprod (Jprod t) := by
  induction t using TensorProduct.inductionOn with
  | tmul x y =>
    have e1 : (μ.toTripleData.ko.eps' : ℂ) = 1 := by rw [μ.ko4]; norm_num
    have e2 : (μ.toTripleData.ko.eps'' : ℂ) = 1 := by rw [μ.ko4]; norm_num
    have e3 : (φ.toTripleData.ko.eps' : ℂ) = 1 := by rw [φ.ko6]; norm_num
    rw [Dprod_tmul, map_add, Jprod_tmul, Jprod_tmul,
      Janti_D_M, Janti_Γ_M, Janti_D_F, e1, e2, e3, one_smul, one_smul, one_smul,
      Jprod_tmul, Dprod_tmul]
  | add a b ha hb =>
    simp only [map_add, ha, hb]

/-- `J_prod Γ_prod = −Γ_prod J_prod`, pointwise (Tier T1 — proved).
    The sign is `(ε″_M · ε″_F) = −1` from `koProd_signs` (KO-dim 2 mod 8). -/
theorem Jprod_Γ (t : μ.toTripleData.S ⊗[ℂ] φ.toTripleData.S) :
    Jprod (Gprod t) = -(Gprod (Jprod t)) := by
  induction t using TensorProduct.inductionOn with
  | tmul x y =>
    rw [Gprod_tmul, Jprod_tmul, Janti_Γ_M, Janti_Γ_F,
      TensorProduct.smul_tmul_smul, hsign'C, neg_smul, one_smul,
      Jprod_tmul, Gprod_tmul]
  | add a b ha hb =>
    simp only [map_add, ha, hb, neg_add]

/-- `J_prod² = −1` as operators (Tier T1 — proved). -/
theorem Jprod_comp_sq : Jprod.comp Jprod = -LinearMap.id := by
  apply LinearMap.ext
  intro t
  simp only [LinearMap.comp_apply, LinearMap.neg_apply, LinearMap.id_apply, Jprod_sq]

/-- `J_prod Dprod = Dprod J_prod` as operators (Tier T1 — proved). -/
theorem Jprod_comp_D : Jprod.comp Dprod = Dprod.comp Jprod := by
  apply LinearMap.ext
  intro t
  simp only [LinearMap.comp_apply, Jprod_D]

/-- `J_prod Γ_prod = −Γ_prod J_prod` as operators (Tier T1 — proved). -/
theorem Jprod_comp_Γ : Jprod.comp Gprod = -(Gprod.comp Jprod) := by
  apply LinearMap.ext
  intro t
  simp only [LinearMap.comp_apply, LinearMap.neg_apply, Jprod_Γ]

/-!
## The Krein fundamental symmetry (T2+T1) — promotes the `KreinProdPin` pin

The T2 enrichment carries a sesquilinear form `sesq` on each spinor module
(ALGEBRAIC ONLY: antilinear in the first argument, linear in the second;
NOT assumed positive-definite, nondegenerate, or complete — the analytic
axioms stay out, per the Analytic-boundary note) and a fundamental symmetry
`η` with `η² = 1`, self-adjoint FOR THE FORM
(`sesq (ηx) y = sesq x (ηy)` — the honest algebraic content of `ηᴴ = η`,
with no adjoint operator constructed).

The product form `sesqProd` satisfies
`sprod(x₁⊗y₁, x₂⊗y₂) = s_M(x₁,x₂)·s_F(y₁,y₂)` (T1: `sesqProd_tmul`), and
`η_prod = η_M ⊗ η_F` satisfies `η_prod² = 1` and is self-adjoint for the
product form (T1: `ηprod_sq`, `ηprod_selfadj`).

Signature honesty: the finite Krein structure had algebraic signature
(32,32); here `η_prod` is an abstract fundamental symmetry — NO
spacetime-signature claim is made. The killed Lorentzian language stays
killed.

ASSUMED (T2 class data): `sesq`, `ηsym`, `hηsym_sq`, `hηsym_selfadj` per factor.
PROVED (T1): everything below.
-/

/-- The linear pairing `(f ⊗ₜ g) ↦ (a⊗b ↦ f(a)·g(b))` (Tier T2 — definition).
    Bilinearity is `TensorProduct.map`'s additivity/homogeneity in each factor. -/
noncomputable def sesqProdBil :
    (μ.toTripleData.S →ₗ[ℂ] ℂ) →ₗ[ℂ] (φ.toTripleData.S →ₗ[ℂ] ℂ) →ₗ[ℂ]
      ((μ.toTripleData.S ⊗[ℂ] φ.toTripleData.S) →ₗ[ℂ] ℂ) :=
  LinearMap.mk₂ ℂ
    (fun f g => (TensorProduct.lid ℂ ℂ).comp (TensorProduct.map f g))
    (fun f₁ f₂ g => by rw [TensorProduct.map_add_left, LinearMap.comp_add])
    (fun c f g => by rw [TensorProduct.map_smul_left, LinearMap.comp_smul])
    (fun f g₁ g₂ => by rw [TensorProduct.map_add_right, LinearMap.comp_add])
    (fun c f g => by rw [TensorProduct.map_smul_right, LinearMap.comp_smul])

/-- The product sesquilinear form (Tier T2 — definition): antilinear in the
    first tensor argument, linear in the second. -/
noncomputable def sesqProd : (μ.toTripleData.S ⊗[ℂ] φ.toTripleData.S) →ₛₗ[starRingEnd ℂ]
    ((μ.toTripleData.S ⊗[ℂ] φ.toTripleData.S) →ₗ[ℂ] ℂ) :=
  (TensorProduct.lift sesqProdBil).comp (TensorProduct.map μ.toTripleData.sesq φ.toTripleData.sesq)

/-- The product form on elementary tensors (Tier T1 — proved):
    `sprod(x₁⊗y₁, x₂⊗y₂) = s_M(x₁,x₂)·s_F(y₁,y₂)`. -/
theorem sesqProd_tmul (x₁ x₂ : μ.toTripleData.S) (y₁ y₂ : φ.toTripleData.S) :
    sesqProd (x₁ ⊗ₜ[ℂ] y₁) (x₂ ⊗ₜ[ℂ] y₂)
      = μ.toTripleData.sesq x₁ x₂ * φ.toTripleData.sesq y₁ y₂ := by
  show ((TensorProduct.lift sesqProdBil).comp
      (TensorProduct.map μ.toTripleData.sesq φ.toTripleData.sesq)) (x₁ ⊗ₜ[ℂ] y₁) (x₂ ⊗ₜ[ℂ] y₂) = _
  rw [LinearMap.comp_apply, TensorProduct.map_tmul, TensorProduct.lift.tmul]
  show ((TensorProduct.lid ℂ ℂ).comp
    (TensorProduct.map (μ.toTripleData.sesq x₁) (φ.toTripleData.sesq y₁))) (x₂ ⊗ₜ[ℂ] y₂) = _
  rw [LinearMap.comp_apply, TensorProduct.map_tmul]
  show (TensorProduct.lid ℂ ℂ) ((μ.toTripleData.sesq x₁ x₂) ⊗ₜ[ℂ] (φ.toTripleData.sesq y₁ y₂)) = _
  rw [TensorProduct.lid_tmul, smul_eq_mul]

/-- The product fundamental symmetry `η_prod = η_M ⊗ η_F` (Tier T2 — definition). -/
noncomputable def ηprod : Module.End ℂ (μ.toTripleData.S ⊗[ℂ] φ.toTripleData.S) :=
  opTensor μ.toTripleData.ηsym φ.toTripleData.ηsym

/-- `η_prod` on elementary tensors (Tier T1 — proved). -/
theorem ηprod_tmul (x : μ.toTripleData.S) (y : φ.toTripleData.S) :
    ηprod (x ⊗ₜ[ℂ] y) = μ.toTripleData.ηsym x ⊗ₜ[ℂ] φ.toTripleData.ηsym y := by
  unfold ηprod opTensor
  exact TensorProduct.map_tmul _ _ _ _

/-- `η_prod² = 1` (Tier T1 — proved). -/
theorem ηprod_sq : ηprod * ηprod = 1 := by
  unfold ηprod
  rw [← opTensor_mul, μ.toTripleData.hηsym_sq, φ.toTripleData.hηsym_sq, opTensor_one]

/-- `η_prod` is self-adjoint for the product form (Tier T1 — proved):
    `sprod(ηt₁, t₂) = sprod(t₁, ηt₂)`. This is the honest algebraic content
    of `η_prodᴴ = η_prod` — no adjoint operator is constructed (the form is
    not assumed nondegenerate). -/
theorem ηprod_selfadj (t₁ t₂ : μ.toTripleData.S ⊗[ℂ] φ.toTripleData.S) :
    sesqProd (ηprod t₁) t₂ = sesqProd t₁ (ηprod t₂) := by
  induction t₁ using TensorProduct.inductionOn with
  | tmul x₁ y₁ =>
    induction t₂ using TensorProduct.inductionOn with
    | tmul x₂ y₂ =>
      rw [ηprod_tmul, ηprod_tmul, sesqProd_tmul, sesqProd_tmul,
        μ.toTripleData.hηsym_selfadj, φ.toTripleData.hηsym_selfadj]
    | add a b ha hb =>
      simp only [map_add, ha, hb]
  | add a b ha hb =>
    simp only [map_add, LinearMap.add_apply, ha, hb]

-- ============================================================================
-- §6b. The opposite representation: `conjJ`-shadow (T2) + diagonal reduction (T1)
-- ============================================================================

/-!
## The opposite representation — what is statable, and the exact obstruction

The textbook opposite representation `a° = J a* J⁻¹` is NOT statable in
`TripleData`, for three independent hard failures (probed 2026-10-10):
1. `star X` for `X : Module.End ℂ (S_M ⊗[ℂ] S_F)` fails:
   `failed to synthesize Star (Module.End ℂ (TripleData.S ⊗[ℂ] TripleData.S))` —
   the enrichment gives form-self-adjointness of `η` only, never a general
   operator adjoint;
2. `Jprod * X` fails: `Jprod : S⊗S →ₛₗ[starRingEnd ℂ] S⊗S` is semilinear, not
   a `Module.End` — no `HMul` instance — so `J X J⁻¹` conjugation of
   operators cannot be written;
3. `Jprod⁻¹` fails: no `Inv` instance on the semilinear map.

So `opp y = Jprod (πgrandProd y)* Jprod⁻¹` cannot even be written down.
What IS statable is the `conjJ`-shadow: `conjJ` packages `X ↦ JXJ⁻¹` as a
linear anti-automorphism (class data; its compatibility with the true
`Janti` is not axiomatized). The opposite representations below are that
shadow — derived, not assumed:
- `oppProd`: undoubled product algebra, via the factored representation
  and `conjJprodElem`;
- `oppgrandProd`: doubled product algebra, the DLM doubled pattern
  `P₊ opp(y.1) + P₋ opp(y.2)` mirroring `πgrandProd`.

Flip-compatibility: the old pin text's `opp (flipProd y) = flipProd (opp y)`
is ILL-TYPED — `opp y` is a single operator, not a pair, so
`flipProd (opp y)` does not typecheck. The statable DLM content is
`ρ°(y°) = (ρ⁻¹(y))°` with `ρ⁻¹ = ρ = flip`, i.e. `oppgrandProd (flipProd y)`
computes to the projector-swapped opposite (`oppgrandProd_flip`, T1).

What closes T1: on diagonal pairs the twisted FOC is the ordinary product
FOC (`prodTwistedFOC_diag_reduce`), which is stated (`ProdFirstOrderCond`,
T2) but PINNED — its remaining need is the factor-level order-one
relations, absent from `TripleData` (the concrete finite order-one
`OrderOneHolds_smDirac` in `OrderOne.lean` is for the `Matrix I32` triple,
not the abstract `FiniteFactor` class). The finite-level pin
`TwistedTriple.TwistedFirstOrderCondGrand` stays pinned for its own reason
(the true real structure is antilinear, unstatable in the linear matrix
model); the product pin inherits nothing from it and is refined here on
its own terms.
-/

/-- The opposite representation of the UNDOUBLED product algebra (Tier T2):
    the `conjJ`-shadow of `t° = J t* J⁻¹`. -/
noncomputable def oppProd : μ.toTripleData.A ⊗[ℂ] φ.toTripleData.A →ₗ[ℂ]
    Module.End ℂ (μ.toTripleData.S ⊗[ℂ] φ.toTripleData.S) :=
  conjJprodElem.comp
    (TensorProduct.map μ.toTripleData.π.toLinearMap φ.toTripleData.π.toLinearMap)

/-- On elementary tensors (Tier T1 — proved). -/
theorem oppProd_tmul (f : μ.toTripleData.A) (a : φ.toTripleData.A) :
    oppProd (f ⊗ₜ[ℂ] a)
      = opTensor (μ.toTripleData.conjJ (μ.toTripleData.π f))
          (φ.toTripleData.conjJ (φ.toTripleData.π a)) := by
  unfold oppProd
  rw [LinearMap.comp_apply, TensorProduct.map_tmul, conjJprodElem_tmul]
  rfl

/-- `oppProd` reverses multiplication on elementary tensors (Tier T1 —
    proved): the opposite-algebra law, from `hconjJ_mul` and the
    mixed-product law. -/
theorem oppProd_anti_tmul (f g : μ.toTripleData.A) (a b : φ.toTripleData.A) :
    oppProd ((f ⊗ₜ[ℂ] a) * (g ⊗ₜ[ℂ] b))
      = oppProd (g ⊗ₜ[ℂ] b) * oppProd (f ⊗ₜ[ℂ] a) := by
  rw [Algebra.TensorProduct.tmul_mul_tmul, oppProd_tmul, oppProd_tmul, oppProd_tmul,
    map_mul (μ.toTripleData.π) f g, map_mul (φ.toTripleData.π) a b,
    μ.toTripleData.hconjJ_mul, φ.toTripleData.hconjJ_mul, ← opTensor_mul]

/-- The opposite representation of the DOUBLED product algebra (Tier T2):
    the DLM doubled pattern `P₊ opp(y.1) + P₋ opp(y.2)`, mirroring
    `πgrandProd`. This derives the form the twisted setting needs. -/
noncomputable def oppgrandProd
    (y : (μ.toTripleData.A ⊗[ℂ] φ.toTripleData.A) × (μ.toTripleData.A ⊗[ℂ] φ.toTripleData.A)) :
    Module.End ℂ (μ.toTripleData.S ⊗[ℂ] φ.toTripleData.S) :=
  GprojPlus * oppProd y.1 + GprojMinus * oppProd y.2

/-- Flip-compatibility, statable form (Tier T1 — proved): `opp (flip y)` is
    the projector-swapped opposite — the DLM `ρ°(y°) = (ρ⁻¹(y))°` for the
    involutive flip. -/
theorem oppgrandProd_flip
    (y : (μ.toTripleData.A ⊗[ℂ] φ.toTripleData.A) × (μ.toTripleData.A ⊗[ℂ] φ.toTripleData.A)) :
    oppgrandProd (flipProd y) = GprojPlus * oppProd y.2 + GprojMinus * oppProd y.1 := by
  obtain ⟨y1, y2⟩ := y
  rfl

/-- On diagonal pairs (Tier T1 — proved): `opp (t,t) = oppProd t`, via
    `P₊ + P₋ = 1`. -/
theorem oppgrandProd_diag (t : μ.toTripleData.A ⊗[ℂ] φ.toTripleData.A) :
    oppgrandProd (t, t) = oppProd t := by
  unfold oppgrandProd
  have hproj : GprojPlus * oppProd (t, t).1 + GprojMinus * oppProd (t, t).2
      = oppProd t := by
    show GprojPlus * oppProd t + GprojMinus * oppProd t = oppProd t
    rw [← add_mul, Gproj_add, one_mul]
  exact hproj

/-- The ordinary product first-order condition (Tier T2 — stated, PINNED):
    `[[Dprod, πprodLin t], oppProd s] = 0`. The twisted FOC reduces to this
    on diagonal pairs (`prodTwistedFOC_diag_reduce`, T1). PINNED: the
    factor-level order-one relations are not part of `TripleData`. -/
def ProdFirstOrderCond : Prop :=
  ∀ t s : μ.toTripleData.A ⊗[ℂ] φ.toTripleData.A,
    (Dprod * πprodLin t - πprodLin t * Dprod) * oppProd s
      - oppProd s * (Dprod * πprodLin t - πprodLin t * Dprod) = 0

/-- **Diagonal reduction (Tier T1 — proved).** The twisted first-order
    condition on diagonal pairs IS the ordinary product first-order
    condition: the flip fixes `(t,t)` and `(s,s)` (`rfl`),
    `twistedCommProd (t,t)` is the ordinary commutator
    (`prodTwist_diag_is_ordinary`), and `oppgrandProd (t,t) = oppProd t`
    (`oppgrandProd_diag`). -/
theorem prodTwistedFOC_diag_reduce :
    (∀ t s : μ.toTripleData.A ⊗[ℂ] φ.toTripleData.A,
      twistedCommProd (t, t) * oppgrandProd (s, s)
        - oppgrandProd (flipProd (s, s)) * twistedCommProd (t, t) = 0)
    ↔ ProdFirstOrderCond := by
  have key : ∀ t s : μ.toTripleData.A ⊗[ℂ] φ.toTripleData.A,
      twistedCommProd (t, t) * oppgrandProd (s, s)
        - oppgrandProd (flipProd (s, s)) * twistedCommProd (t, t)
      = (Dprod * πprodLin t - πprodLin t * Dprod) * oppProd s
        - oppProd s * (Dprod * πprodLin t - πprodLin t * Dprod) := by
    intro t s
    have hflip : flipProd (s, s) = (s, s) := rfl
    rw [hflip, prodTwist_diag_is_ordinary, oppgrandProd_diag]
  unfold ProdFirstOrderCond
  simp only [key]

-- ============================================================================
-- §7. Pins: one T5 remains; two PROMOTED to T2+T1
-- ============================================================================

/-!
## Promotion notes (2026-10-10, Rung 3 Worker 1)

`AntilinearJProd` and `KreinProdPin` are PROMOTED from "pinned T5,
unstatable" to "T2-axiomatized with T1 consequences proved". The old pin
statements are dead (per the relabeling rule); what stands:

### `AntilinearJProd` → PROMOTED
- ASSUMED (T2, `TripleData` class data): the antilinear maps `Janti`
  (`S →ₛₗ[starRingEnd ℂ] S`) with `hJanti_sq` (`J² = ε`), `hJanti_D`
  (`JD = ε′DJ`), `hJanti_Γ` (`JΓ = ε″ΓJ`), keyed to the factor KO signs
  (`μ.ko4`, `φ.ko6`). The sesquilinear form is NOT needed for J.
- PROVED (T1): `Jprod = J_M ⊗ J_F` (T2 def) with `Jprod_sq` (`J² = −1`),
  `Jprod_D` (`JD = DJ`), `Jprod_Γ` (`JΓ = −ΓJ`), plus the
  operator-composition versions `Jprod_comp_sq`, `Jprod_comp_D`,
  `Jprod_comp_Γ`. The `−1` signs come from `koProd_signs` (KO-dim 2 mod 8).
- NOT assumed/proved: compatibility of the linear shadow `conjJ` with the
  true `Janti` (`conjJ X = JXJ⁻¹` is not axiomatized); the analytic axioms.

### `KreinProdPin` → PROMOTED
- ASSUMED (T2, `TripleData` class data): sesquilinear forms `sesq`
  (algebraic only — antilinear in the first argument, linear in the
  second; NOT assumed positive-definite, nondegenerate, or complete) and
  fundamental symmetries `ηsym` with `hηsym_sq` (`η² = 1`) and
  `hηsym_selfadj` (`sesq (ηx) y = sesq x (ηy)` — the algebraic content of
  `ηᴴ = η`; no adjoint operator is constructed).
- PROVED (T1): `sesqProd` (T2 def) with `sesqProd_tmul`
  (`sprod(x₁⊗y₁,x₂⊗y₂) = s_M(x₁,x₂)·s_F(y₁,y₂)`); `ηprod = η_M ⊗ η_F`
  (T2 def) with `ηprod_sq` (`η² = 1`) and `ηprod_selfadj` (self-adjoint for
  the product form).
- NOT claimed: any spacetime signature. The finite Krein structure had
  algebraic signature (32,32); `η_prod` is an abstract fundamental
  symmetry. The killed Lorentzian language stays killed.

### Remaining T5 pin (refined 2026-10-10, Rung 3 Worker 2)
`ProdTwistedFirstOrderCond` stays pinned, but the obstruction is now precise
(§6b): the `conjJ`-shadow opposite representations ARE constructed T2
(`oppProd`, `oppgrandProd`), flip-compatibility is discharged in the statable
DLM form (`oppgrandProd_flip`, T1), and the diagonal case reduces T1 to the
ordinary product FOC (`prodTwistedFOC_diag_reduce`, T1). Two pins remain:
(a) the TRUE opposite `a° = J a* J⁻¹` is unstatable — `star` on
`Module.End ℂ _` fails to synthesize, `Jprod` is semilinear (no `HMul`/`Inv`
instances), so `Jprod (πgrandProd y)* Jprod⁻¹` cannot be written; the
enrichment gives form-self-adjointness of `η`, never a general operator
adjoint; (b) `ProdFirstOrderCond` needs factor-level order-one relations
(`[[D_M, π_M f], conjJ_M (π_M g)] = 0`, `[[D_F, π_F a], conjJ_F (π_F b)] = 0`)
absent from `TripleData` — the concrete finite order-one
(`OrderOneHolds_smDirac`, `OrderOne.lean`) is for the `Matrix I32` triple,
not the abstract `FiniteFactor` class. The old pin text's flip-compatibility
`opp (flipProd y) = flipProd (opp y)` was ill-typed (`opp y` is a single
operator, not a pair) and is superseded by `oppgrandProd_flip`.
-/

/-! ## Analytic boundary (T5, not axiomatized)

The analytic spectral-triple axioms — boundedness of `[D_M, π_M(f)]` for
all `f`, compact resolvent of `D_M` — are NOT part of `TripleData` /
`ManifoldFactor`. They need the continuum (Rung 3: the manifold factor as
analysis, not just algebra). The class axiomatizes only the algebraic
relations; nothing in this file claims analytic control. In particular
the sesquilinear form `sesq` is PURELY algebraic (no completeness, no
continuity, no positivity/nondegeneracy) — it is the algebraic shadow of
the Hilbert/Krein inner product, not the inner product itself.
-/

#print axioms opTensor_mul
#print axioms opTensor_one
#print axioms Gprod_sq
#print axioms Dprod_odd
#print axioms Dprod_sq
#print axioms πprod_even
#print axioms πprodLin_tmul
#print axioms Gproj_add
#print axioms flipProd_CM_regular
#print axioms prodTwist_diag_is_ordinary
#print axioms prod_commutator_decomp
#print axioms prod_commutator_pureManifold
#print axioms prod_commutator_pureFinite
#print axioms koProd_signs
#print axioms conjJprodElem_mul
#print axioms conjJprod_D
#print axioms conjJprod_Γ
#print axioms compTriple_starRingEnd
#print axioms Jprod_tmul
#print axioms Jprod_sq
#print axioms Jprod_D
#print axioms Jprod_Γ
#print axioms Jprod_comp_sq
#print axioms Jprod_comp_D
#print axioms Jprod_comp_Γ
#print axioms sesqProd_tmul
#print axioms ηprod_tmul
#print axioms ηprod_sq
#print axioms ηprod_selfadj
#print axioms oppProd_tmul
#print axioms oppProd_anti_tmul
#print axioms oppgrandProd_flip
#print axioms oppgrandProd_diag
#print axioms prodTwistedFOC_diag_reduce

end ThetLogos
