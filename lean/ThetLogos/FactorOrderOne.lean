import ThetLogos.ProductTriple

-- The `[ManifoldFactor]` / `[FiniteFactor]` section variables below trigger
-- the overlapping-instances linter (both extend `TripleData`); the two
-- factors are never unified in this file, so it is a false positive.
set_option linter.overlappingInstances false

namespace ThetLogos

open TensorProduct

/-!
# ThetLogos.FactorOrderOne — Rung 4 prep, Track C (2026-10-10)

Discharge of the ordinary product first-order condition
(`ProdFirstOrderCond`, stated T2 and pinned in `ProductTriple.lean` §6b)
and documentation of the Star pin (PIN (a)).

## The honest finding (verified, not wished)

Order-one alone does NOT suffice for the product FOC. Expanding
`[[D_M,π_M f]⊗π_F(a) + π_M(f)Γ_M⊗[D_F,π_F a], J_M(π_M g)⊗J_F(π_F b)]`
via the mixed-product law, the cross terms need:
- `[π_F(a), J_F(π_F b)] = 0` (order-zero on F) to combine the first summand;
- `[π_M(f)Γ_M, J_M(π_M g)] = 0` (Γ-dressed order-zero on M) to combine the
  second summand.
The Γ dressing is discharged T1 (`repGamma_comm_conjJ_M`): `Γ_M` commutes
with `conjJ_M (π_M g)` from `hπeven` + `hkoΓ` + the KO-dim 4 signs
(`conjJ_M Γ_M = Γ_M`) + contravariance/involution of `conjJ_M` — no extra
T2 needed. So the product FOC needs order-zero AND order-one on BOTH
factors; all four relations are used in `prodFOC_elem`. No path needing
less was found.

## Tier ledger
T2 (class data): `FactorOrderZeroOne` (`hord0`, `hord1`).
T1 (proved, zero sorrys): `Gamma_comm_conjJ_M`, `repGamma_comm_conjJ_M`,
  `prodFOC_elem`, `prodFirstOrderCond_discharge`.
Pinned (documented, not claimed): PIN (a) `Star (Module.End ℂ S)` (§3).
-/

-- ============================================================================
-- §1. Factor-level order-zero and order-one as T2 class data
-- ============================================================================

-- The class is generic over `T : TripleData`. Its fields need the operator
-- algebra on `Module.End ℂ T.S`; the instances used are `T`'s OWN instance
-- fields (`T.addS`, `T.modS`) installed as local instances — NOT fresh
-- binders, which would be definitionally distinct from the instances in
-- `T.D`, `T.π`, `T.conjJ` and break elaboration.
section
variable (T : TripleData)
local instance instAddS_T : AddCommGroup T.S := T.addS
local instance instModS_T : Module ℂ T.S := T.modS

/-- Factor-level order-zero and order-one (Tier T2 — class data).

    The two relations the product FOC needs and `TripleData` does not
    supply (the pin documented in `ProductTriple.lean` §6b):
    - `hord0` (order-zero): the representation commutes with the opposite
      (real-structure shadow) representation,
      `[π(f), conjJ (π(g))] = 0`;
    - `hord1` (order-one): the 1-form `[D, π(f)]` commutes with the
      opposite representation, `[[D, π(f)], conjJ (π(g))] = 0`.
    Both are axiomatized (T2); their product-level consequence
    (`prodFirstOrderCond_discharge`) is proved (T1). -/
class FactorOrderZeroOne : Prop where
  hord0 : ∀ f g : T.A, T.π f * T.conjJ (T.π g) = T.conjJ (T.π g) * T.π f
  hord1 : ∀ f g : T.A, (T.D * T.π f - T.π f * T.D) * T.conjJ (T.π g)
    = T.conjJ (T.π g) * (T.D * T.π f - T.π f * T.D)

end

variable [μ : ManifoldFactor] [φ : FiniteFactor]

-- ============================================================================
-- §2. T1 consequences: Γ commutation, the dressed order-zero, FOC discharge
-- ============================================================================

/-!
## The Γ commutation lemmas omit `φ`: they are purely manifold-factor statements.
-/

omit φ in
/-- `Γ_M` commutes with the real-structure shadow of a represented element
    (Tier T1 — proved). From `hπeven` (`Γ` even), `hkoΓ` + the KO-dim 4
    signs (`conjJ_M Γ_M = Γ_M`), contravariance (`hconjJ_mul`) and
    involution (`hconjJ_inv`) of `conjJ_M`: apply the injective `conjJ_M`
    to both sides and the two sides agree by `hπeven`. -/
theorem Gamma_comm_conjJ_M (g : μ.toTripleData.A) :
    μ.toTripleData.Γ * μ.toTripleData.conjJ (μ.toTripleData.π g)
      = μ.toTripleData.conjJ (μ.toTripleData.π g) * μ.toTripleData.Γ := by
  have hΓJ : μ.toTripleData.conjJ μ.toTripleData.Γ = μ.toTripleData.Γ := by
    have hcast : (μ.toTripleData.ko.eps'' : ℂ) = 1 := by rw [μ.ko4]; norm_num
    rw [μ.toTripleData.hkoΓ, hcast, one_smul]
  have key : μ.toTripleData.conjJ
        (μ.toTripleData.Γ * μ.toTripleData.conjJ (μ.toTripleData.π g))
      = μ.toTripleData.conjJ
        (μ.toTripleData.conjJ (μ.toTripleData.π g) * μ.toTripleData.Γ) := by
    rw [μ.toTripleData.hconjJ_mul, μ.toTripleData.hconjJ_mul, hΓJ,
      μ.toTripleData.hconjJ_inv, μ.toTripleData.hπeven g]
  have h2 := congrArg (μ.toTripleData.conjJ) key
  rwa [μ.toTripleData.hconjJ_inv, μ.toTripleData.hconjJ_inv] at h2

omit φ in
/-- The Γ-dressed manifold representation commutes with the opposite
    representation (Tier T1 — proved):
    `(π_M f * Γ_M)` commutes with `conjJ_M (π_M g)`.
    Uses order-zero on M (`hord0`) for the `π_M f` part and
    `Gamma_comm_conjJ_M` for the `Γ_M` part — this is what discharges the
    Γ dressing, so no Γ-dressed order-zero needs axiomatizing. -/
theorem repGamma_comm_conjJ_M [FactorOrderZeroOne μ.toTripleData]
    (f g : μ.toTripleData.A) :
    (μ.toTripleData.π f * μ.toTripleData.Γ) * μ.toTripleData.conjJ (μ.toTripleData.π g)
      = μ.toTripleData.conjJ (μ.toTripleData.π g) * (μ.toTripleData.π f * μ.toTripleData.Γ) := by
  have h0 := FactorOrderZeroOne.hord0 (T := μ.toTripleData) f g
  have hΓ := Gamma_comm_conjJ_M (μ := μ) g
  calc (μ.toTripleData.π f * μ.toTripleData.Γ) * μ.toTripleData.conjJ (μ.toTripleData.π g)
      = μ.toTripleData.π f * (μ.toTripleData.Γ * μ.toTripleData.conjJ (μ.toTripleData.π g)) := by
        rw [mul_assoc]
    _ = μ.toTripleData.π f * (μ.toTripleData.conjJ (μ.toTripleData.π g) * μ.toTripleData.Γ) := by
        rw [hΓ]
    _ = (μ.toTripleData.π f * μ.toTripleData.conjJ (μ.toTripleData.π g)) * μ.toTripleData.Γ := by
        rw [mul_assoc]
    _ = (μ.toTripleData.conjJ (μ.toTripleData.π g) * μ.toTripleData.π f) * μ.toTripleData.Γ := by
        rw [h0]
    _ = μ.toTripleData.conjJ (μ.toTripleData.π g) * (μ.toTripleData.π f * μ.toTripleData.Γ) := by
        rw [← mul_assoc]

/-- **Product FOC on elementary tensors (Tier T1 — proved).**
    For `t = f ⊗ₜ a`, `s = g ⊗ₜ b`:
    `[[Dprod, πprodLin t], oppProd s] = 0`.
    Proof: expand via `prod_commutator_decomp` + `oppProd_tmul` + the
    mixed-product law (`← opTensor_mul`); the first summand vanishes by
    order-one on M (`hord1`) after aligning the untouched F-factors with
    order-zero on F (`hord0`); the second summand vanishes by order-one on
    F (`hord1`) after aligning the untouched M-factors with the Γ-dressed
    order-zero on M (`repGamma_comm_conjJ_M`, T1). -/
theorem prodFOC_elem [FactorOrderZeroOne μ.toTripleData] [FactorOrderZeroOne φ.toTripleData]
    (f : μ.toTripleData.A) (a : φ.toTripleData.A)
    (g : μ.toTripleData.A) (b : φ.toTripleData.A) :
    (Dprod * πprodLin (f ⊗ₜ[ℂ] a) - πprodLin (f ⊗ₜ[ℂ] a) * Dprod) * oppProd (g ⊗ₜ[ℂ] b)
      - oppProd (g ⊗ₜ[ℂ] b) * (Dprod * πprodLin (f ⊗ₜ[ℂ] a) - πprodLin (f ⊗ₜ[ℂ] a) * Dprod) = 0 := by
  have h1M := FactorOrderZeroOne.hord1 (T := μ.toTripleData) f g
  have h0F := FactorOrderZeroOne.hord0 (T := φ.toTripleData) a b
  have h1F := FactorOrderZeroOne.hord1 (T := φ.toTripleData) a b
  have hΓd := repGamma_comm_conjJ_M f g
  rw [πprodLin_tmul, oppProd_tmul, prod_commutator_decomp, add_mul, mul_add]
  simp only [← opTensor_mul]
  rw [h0F, hΓd, h1F, add_sub_add_comm,
    ← opTensor_sub_left, ← opTensor_sub_right,
    sub_eq_zero.mpr h1M, sub_self, opTensor_zero_left, opTensor_zero_right, add_zero]

/-- **Product first-order condition discharged (Tier T1 — proved).**
    Given factor-level order-zero AND order-one on both factors
    (`FactorOrderZeroOne`, T2 class data), `ProdFirstOrderCond` holds:
    `[[Dprod, πprodLin t], oppProd s] = 0` for all `t s : A_M ⊗ A_F`.
    The elementary-tensor case is `prodFOC_elem`; the general case follows
    by `TensorProduct.inductionOn` since everything in sight is linear
    (the FOC expression is additive in each argument separately). -/
theorem prodFirstOrderCond_discharge [FactorOrderZeroOne μ.toTripleData]
    [FactorOrderZeroOne φ.toTripleData] : ProdFirstOrderCond := by
  unfold ProdFirstOrderCond
  intro t s
  induction t using TensorProduct.inductionOn with
  | tmul f a =>
    induction s using TensorProduct.inductionOn with
    | tmul g b => exact prodFOC_elem f a g b
    | add s₁ s₂ ih₁ ih₂ =>
      have hadd : (Dprod * πprodLin (f ⊗ₜ[ℂ] a) - πprodLin (f ⊗ₜ[ℂ] a) * Dprod) * oppProd (s₁ + s₂)
            - oppProd (s₁ + s₂) * (Dprod * πprodLin (f ⊗ₜ[ℂ] a) - πprodLin (f ⊗ₜ[ℂ] a) * Dprod)
          = ((Dprod * πprodLin (f ⊗ₜ[ℂ] a) - πprodLin (f ⊗ₜ[ℂ] a) * Dprod) * oppProd s₁
              - oppProd s₁ * (Dprod * πprodLin (f ⊗ₜ[ℂ] a) - πprodLin (f ⊗ₜ[ℂ] a) * Dprod))
            + ((Dprod * πprodLin (f ⊗ₜ[ℂ] a) - πprodLin (f ⊗ₜ[ℂ] a) * Dprod) * oppProd s₂
              - oppProd s₂ * (Dprod * πprodLin (f ⊗ₜ[ℂ] a) - πprodLin (f ⊗ₜ[ℂ] a) * Dprod)) := by
        rw [map_add, mul_add, add_mul, add_sub_add_comm]
      rw [hadd, ih₁, ih₂, add_zero]
  | add t₁ t₂ ih₁ ih₂ =>
    have hC : Dprod * πprodLin (t₁ + t₂) - πprodLin (t₁ + t₂) * Dprod
        = (Dprod * πprodLin t₁ - πprodLin t₁ * Dprod)
          + (Dprod * πprodLin t₂ - πprodLin t₂ * Dprod) := by
      rw [map_add, mul_add, add_mul, add_sub_add_comm]
    have hadd : (Dprod * πprodLin (t₁ + t₂) - πprodLin (t₁ + t₂) * Dprod) * oppProd s
          - oppProd s * (Dprod * πprodLin (t₁ + t₂) - πprodLin (t₁ + t₂) * Dprod)
        = ((Dprod * πprodLin t₁ - πprodLin t₁ * Dprod) * oppProd s
            - oppProd s * (Dprod * πprodLin t₁ - πprodLin t₁ * Dprod))
          + ((Dprod * πprodLin t₂ - πprodLin t₂ * Dprod) * oppProd s
            - oppProd s * (Dprod * πprodLin t₂ - πprodLin t₂ * Dprod)) := by
      rw [hC, add_mul, mul_add, add_sub_add_comm]
    rw [hadd, ih₁, ih₂, add_zero]

-- ============================================================================
-- §3. The Star attempt — PIN (a), documented (no sorry)
-- ============================================================================

-- PIN (a): Star (Module.End ℂ S) — REMAINS PINNED (was T5, ProductTriple §7).
-- Attempted 2026-10-10 (Rung 4 prep, Track C). Both paths below were actually
-- probed in Lean; exact failures are quoted. No sorry.

/-!
## The Star attempt — why `Star (Module.End ℂ S)` stays pinned

The textbook opposite representation `a° = J a* J⁻¹` needs the Hilbert
adjoint `a*`. Two paths were tried:

### Attempt A: the adjoint star — FAILS (definitional, before instance synthesis)

`example : Star (Module.End ℂ T.S) := inferInstance` fails with the exact
error (verified 2026-10-10):
  `error(lean.synthInstanceFailed): failed to synthesize instance of type class`
  `Star (Module.End ℂ TripleData.S)`
There is no `LinearMap.adjoint` in this Mathlib version at all
(`error(lean.unknownIdentifier): Unknown constant 'LinearMap.adjoint'`);
the adjoint exists only as `ContinuousLinearMap.adjoint`
(`Mathlib/Analysis/InnerProductSpace/Adjoint.lean`), which demands
`[CompleteSpace E]`, `InnerProductSpace`, and continuous linear maps —
Hilbert-space data that `TripleData` deliberately does not carry. `S`
has only the ALGEBRAIC sesquilinear form `sesq` (not assumed positive,
nondegenerate, or complete), so no Riesz map `S → S` exists and no term
of type `Module.End ℂ S → Module.End ℂ S` giving the adjoint can be
written. The failure is definitional, not a missing instance argument.

### Attempt B: `star := conjJ` — TYPECHECKS but is the WRONG star (rejected)

The `conjJ`-shadow CAN be packaged as a star operation (verified
2026-10-10 — the following elaborates):
```lean
def conjJStarAttempt : StarMul (Module.End ℂ μ.toTripleData.S) where
  star := fun X => μ.toTripleData.conjJ X
  star_involutive := fun X => μ.toTripleData.hconjJ_inv X
  star_mul := fun X Y => μ.toTripleData.hconjJ_mul X Y
```
(`star_mul` is `hconjJ_mul`, involution is `hconjJ_inv`.) It is
deliberately NOT installed: `conjJ` packages `X ↦ JXJ⁻¹` (the
real-structure shadow), so `J (star a) J⁻¹` with this `star` collapses to
`a` itself (via `J² = ±1`, i.e. `hconjJ_inv`) — the "opposite
representation" would BE the representation, a degenerate opposite that
commutes trivially and proves nothing. Installing it as THE `Star`
instance would mislabel the shadow as the adjoint: every Mathlib `star`
lemma would then speak about `JXJ⁻¹`, not `X*`.

### Priced conclusion

PIN (a) remains, exactly priced: producing the true adjoint star needs
`CompleteSpace S` + inner-product structure — i.e. the Hilbert-enriched
`TripleData` of Rung 4 proper — or restriction to finite-dimensional /
concrete models (e.g. `Matrix`, where the conjugate-transpose star
exists). Note the pins are distinct: even WITH a true adjoint star,
`J·*J⁻¹` still needs `J` as an operator on endomorphisms, but `Janti` is
semilinear (no `HMul`/`Inv`) — the §6b obstruction.
-/

#print axioms Gamma_comm_conjJ_M
#print axioms repGamma_comm_conjJ_M
#print axioms prodFOC_elem
#print axioms prodFirstOrderCond_discharge

end ThetLogos
