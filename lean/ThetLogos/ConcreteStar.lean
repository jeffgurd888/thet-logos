import ThetLogos.ConcreteFiniteModel

namespace ThetLogos

open scoped InnerProductSpace

/-!
# ThetLogos.ConcreteStar — EVOLVE Track 2: the true star (2026-10-11)

Closes PIN (a) from `FactorOrderOne.lean` §3 for the concrete Pauli model
(EVOLVE Track 1, `ConcreteFiniteModel.lean`).

## What this delivers
- `pauliStarInst`: the TRUE adjoint `Star` on
  `Module.End ℂ (EuclideanSpace ℂ (Fin 2))`, transported from matrix
  conjugate-transpose along `endAlgEquiv`. This is NOT the `conjJ` shadow —
  `FactorOrderOne.lean` §3 documents why `star := conjJ` would be the wrong
  star (it packages `X ↦ JXJ⁻¹`, so `J (star a) J⁻¹` would collapse to `a`
  itself, a degenerate opposite).
- `pauliStar_is_adjoint` (T1): the transported star IS the Hilbert adjoint:
  `⟪X x, y⟫ = ⟪x, X⋆ y⟫` for the Mathlib inner product.
- `jOpConj` (T2): J-conjugation on operators, `X ↦ J X J⁻¹`, as entrywise
  `star` on matrices; `jOpConj_apply` (T1) proves it really is
  `Janti2`-conjugation. It is conjugate-linear in the scalar action — hence
  a plain function, not a `→ₗ[ℂ]` — which is exactly why the textbook `a°`
  cannot be written as operator multiplication in the abstract setting.
- `pauli_opp_star` (T1): the textbook `X° = J X* J⁻¹` —
  `conjJ2 X = jOpConj (star X)`. The `conjJ`-shadow used across the product
  FOC machinery COINCIDES with the textbook construction wherever both are
  available. This validates the shadow approach.
- `pauli_oppRep_scal` (T1): on scalars, `a° = a` (honest: the scalar
  algebra is commutative and real-structure-trivial).

## Tier ledger
T2 (definitions/instances): `pauliStarInst`, `pauliStarMulInst`,
  `pauliInvolutiveStarInst`, `jOpConj`.
T1 (proved, zero sorrys): `pauliStar_apply`, `pauliStar_involutive`,
  `pauliStar_mul`, `inner_coord`, `pauliStar_is_adjoint`, `jOpConj_apply`,
  `pauli_opp_star`, `pauli_oppRep_scal`.
-/

-- ============================================================================
-- §1. The true adjoint star (T2 instance + T1 laws)
-- ============================================================================

/-- The TRUE adjoint star on endomorphisms (Tier T2 — instance).

    Transported from matrix conjugate-transpose along `endAlgEquiv`.
    Deliberately NOT `star := conjJ`: the shadow is the wrong star
    (`FactorOrderOne.lean` §3). -/
noncomputable instance pauliStarInst :
    Star (Module.End ℂ (EuclideanSpace ℂ (Fin 2))) where
  star X := endAlgEquiv.symm (star (endAlgEquiv X))

/-- The star unfolds as matrix conjugate-transpose (Tier T1 — proved). -/
theorem pauliStar_apply (X : Module.End ℂ (EuclideanSpace ℂ (Fin 2))) :
    endAlgEquiv (star X) = star (endAlgEquiv X) :=
  AlgEquiv.apply_symm_apply _ _

/-- Involutive (Tier T1 — proved): from `star_star` on matrices. -/
theorem pauliStar_involutive (X : Module.End ℂ (EuclideanSpace ℂ (Fin 2))) :
    star (star X) = X := by
  apply endAlgEquiv.injective
  rw [pauliStar_apply, pauliStar_apply, star_star]

/-- Contravariant (Tier T1 — proved): from `(MN)ᴴ = NᴴMᴴ` on matrices. -/
theorem pauliStar_mul (X Y : Module.End ℂ (EuclideanSpace ℂ (Fin 2))) :
    star (X * Y) = star Y * star X := by
  apply endAlgEquiv.injective
  rw [pauliStar_apply, map_mul, map_mul, pauliStar_apply, pauliStar_apply,
    Matrix.star_eq_conjTranspose, Matrix.star_eq_conjTranspose,
    Matrix.star_eq_conjTranspose]
  exact Matrix.conjTranspose_mul _ _

/-- `InvolutiveStar` (Tier T2 — instance). -/
noncomputable instance pauliInvolutiveStarInst :
    InvolutiveStar (Module.End ℂ (EuclideanSpace ℂ (Fin 2))) where
  star_involutive := pauliStar_involutive

/-- `StarMul` (Tier T2 — instance). -/
noncomputable instance pauliStarMulInst :
    StarMul (Module.End ℂ (EuclideanSpace ℂ (Fin 2))) where
  star_mul := pauliStar_mul

-- ============================================================================
-- §2. The transported star IS the Hilbert adjoint (T1)
-- ============================================================================

/-- Inner product in coordinates (Tier T1 — proved). -/
theorem inner_coord (x y : EuclideanSpace ℂ (Fin 2)) :
    ⟪x, y⟫_ℂ = ∑ i : Fin 2, star (x.ofLp i) * y.ofLp i := by
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [RCLike.inner_apply', starRingEnd_apply]

/-- The transported star IS the Hilbert adjoint (Tier T1 — proved):
    `⟪X x, y⟫ = ⟪x, X⋆ y⟫`. This is the content that makes the installed
    star the CORRECT one: it is characterized by the inner product, not
    merely transported. -/
theorem pauliStar_is_adjoint (X : Module.End ℂ (EuclideanSpace ℂ (Fin 2)))
    (x y : EuclideanSpace ℂ (Fin 2)) :
    ⟪X x, y⟫_ℂ = ⟪x, star X y⟫_ℂ := by
  have hX : ∀ i : Fin 2, (X x).ofLp i
      = ∑ j : Fin 2, (endAlgEquiv X) i j * x.ofLp j := by
    intro i
    have hXeq : X = endAlgEquiv.symm (endAlgEquiv X) :=
      (AlgEquiv.symm_apply_apply _ _).symm
    conv_lhs => rw [hXeq, symmM_apply]
    simp only [Matrix.mulVec, dotProduct]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [basis2_repr_apply]
  have hS : ∀ i : Fin 2, (star X y).ofLp i
      = ∑ j : Fin 2, star ((endAlgEquiv X) j i) * y.ofLp j := by
    intro i
    show ((endAlgEquiv.symm (star (endAlgEquiv X))) y).ofLp i = _
    rw [symmM_apply]
    simp only [Matrix.mulVec, dotProduct]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [basis2_repr_apply, Matrix.star_apply]
  rw [inner_coord, inner_coord]
  simp only [hX, hS, star_sum, star_mul, Finset.sum_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
  ring

-- ============================================================================
-- §3. J-conjugation on operators (T2 def + T1 characterization)
-- ============================================================================

/-- J-conjugation on operators, `X ↦ J X J⁻¹` (Tier T2 — definition).

    For coordinate-conjugation `Janti2` this is entrywise `star` on
    matrices (the `conjJ2` docstring records that J-conjugation acts on
    matrices as entrywise `star`). It is conjugate-linear in the scalar
    action — hence a plain function, not a `→ₗ[ℂ]`. This is exactly why
    the textbook `a° = J a* J⁻¹` cannot be written as operator
    multiplication in the abstract `TripleData` setting: `Janti` is
    semilinear (no `HMul`/`Inv`), and the adjoint piece is conjugate-linear
    too. Only their COMPOSITE (`conjJ2`) is linear. -/
noncomputable def jOpConj (X : Module.End ℂ (EuclideanSpace ℂ (Fin 2))) :
    Module.End ℂ (EuclideanSpace ℂ (Fin 2)) :=
  endAlgEquiv.symm ((endAlgEquiv X).map star)

/-- `jOpConj` really is `Janti2`-conjugation (Tier T1 — proved):
    `jOpConj X x = J (X (J x))`. -/
theorem jOpConj_apply (X : Module.End ℂ (EuclideanSpace ℂ (Fin 2)))
    (x : EuclideanSpace ℂ (Fin 2)) :
    jOpConj X x = Janti2 (X (Janti2 x)) := by
  have hXeq : X = endAlgEquiv.symm (endAlgEquiv X) :=
    (AlgEquiv.symm_apply_apply _ _).symm
  ext k
  rw [Janti2_apply]
  show ((endAlgEquiv.symm ((endAlgEquiv X).map star)) x).ofLp k
    = star ((X (Janti2 x)).ofLp k)
  rw [symmM_apply]
  conv_rhs => rw [hXeq, symmM_apply]
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, star_sum, star_mul]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Janti2_repr, basis2_repr_apply, star_star]
  ring

-- ============================================================================
-- §4. The textbook `a° = J a* J⁻¹` (T1)
-- ============================================================================

/-- The textbook opposite `X° = J X* J⁻¹` (Tier T1 — proved):
    the `conjJ`-shadow unfolds as J-conjugation of the TRUE adjoint star.

    This is what makes `a°` statable for the concrete model — and it shows
    the shadow machinery used across the product FOC (`oppProd`,
    `prodFirstOrderCond_discharge`) coincides with the textbook
    construction wherever both are available. -/
theorem pauli_opp_star (X : Module.End ℂ (EuclideanSpace ℂ (Fin 2))) :
    conjJ2 X = jOpConj (star X) := by
  show endAlgEquiv.symm (Matrix.transpose (endAlgEquiv X))
    = endAlgEquiv.symm ((endAlgEquiv (star X)).map star)
  rw [pauliStar_apply]
  congr 1
  ext i j
  simp [Matrix.map_apply, Matrix.transpose_apply, Matrix.star_apply]

/-- The true opposite representation on scalars: `a° = J a* J⁻¹ = a`
    (Tier T1 — proved). Honest: the scalar algebra is commutative and
    real-structure-trivial, so the opposite representation is the
    representation itself. The content is that `a°` is now STATABLE with
    the correct star — the pin was statability, not nontriviality. -/
theorem pauli_oppRep_scal (a : ℂ) : jOpConj (star (repScal a)) = repScal a := by
  rw [← pauli_opp_star]
  have hcg : conjJ2 (repScal a)
      = a • (1 : Module.End ℂ (EuclideanSpace ℂ (Fin 2))) := by
    rw [repScal_smul_one a, map_smul, conjJ2_one]
  rw [hcg, ← repScal_smul_one a]

-- ============================================================================
-- §5. Twisted-FOC re-run — as far as it now goes (honest)
-- ============================================================================

/-!
## Twisted-FOC re-run

`ProdTwistedFirstOrderCond` (`ProductTriple.lean` §4) stays pinned for the
ABSTRACT product, re-priced. Its obstruction (a) was: "the TRUE opposite
`a° = J a* J⁻¹` is unstatable — no operator adjoint
(`Star (Module.End ℂ _)` fails to synthesize), `Jprod` is semilinear
(no `HMul`/`Inv`)".

For the concrete Pauli model, (a) is now CLOSED: `pauli_opp_star` states
`X° = J X* J⁻¹` with the true adjoint star, and `jOpConj_apply` exhibits
the J-conjugation. What remains for the abstract pin:

1. The pin quantifies over abstract `ManifoldFactor`/`FiniteFactor` — the
   concrete star does not transfer. But the obstruction is now a TEMPLATE,
   not an impossibility: matrix-transport along a basis equivalence works
   for any finite-dimensional concrete factor. "No star can exist" →
   "instantiate per concrete factor".
2. `Jprod` semilinearity: `J·J⁻¹` cannot be operator multiplication
   abstractly. The `jOpConj` packaging (a plain function, conjugate-linear
   in scalars) shows the statable pattern — installing it abstractly would
   need the J/matrix compatibility as class data.

So: pin (a) discharged for the concrete model; the abstract product pin is
re-priced, not closed. This is a priced remainder, not a failure.
-/

-- ============================================================================
-- §6. Tier ledger check
-- ============================================================================

#print axioms pauliStar_apply
#print axioms pauliStar_involutive
#print axioms pauliStar_mul
#print axioms inner_coord
#print axioms pauliStar_is_adjoint
#print axioms jOpConj_apply
#print axioms pauli_opp_star
#print axioms pauli_oppRep_scal

end ThetLogos
