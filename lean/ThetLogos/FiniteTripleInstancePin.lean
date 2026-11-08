/-
# ThetLogos.FiniteTripleInstancePin — the ℂ³² instance of the generic triple
  framework: frozen shape, discharge map, and the lane's STOP record

Fired by Jeff, 2026-11-07 17:26 EST ("Fire the triple instance"), on the
mirror-shadows audit's priced gap (source of record:
`your_files/mirror-shadows-audit-2026-11-07.md`): build the `TripleData` /
`FiniteFactor` (KO row ⟨1, 1, −1⟩) instance of `ProductTriple` from the
concrete ℂ³² seat, assembly only — every field discharging from a theorem
already landed at the concrete seat.

## Lane verdict (stated on the pin's face, full rank)

**STOP — the A-side does not discharge. The audit mispriced the gap.**
The operator side (D, Γ, conjJ, KO row, sesq, Janti, ηsym and all their
relation fields) discharges completely from landed theorems; the discharge
map is frozen in §3 below and the packaging definitions in §1 are in place.
But the class also demands an algebra side that the corpus does not carry:

1. **No instances exist on the algebra.** `SMAlgebra` carries no `Ring`,
   `StarRing`, `Algebra ℂ`, or `StarModule ℂ` instance anywhere in the
   tree — by explicit corpus design: `PreOptionARepresentation` §0 states
   on its face that "`SMAlgebra` carries no `Mul`/`Add`/`Star` instances
   in the corpus" and makes its representation statements against the
   componentwise operations `afMul`/`afAdd`/`afStar` instead. The fields
   `ringA`, `starA`, `algA`, `starModA` therefore have no landed discharge;
   they could only be filled by new in-brick instance constructions with
   new axiom proofs — outside the assembly-only charter of this brick.

2. **The audit's headline π candidate is provably not an algebra map.**
   The `π` field is an `AlgHom`, which requires additivity. The Option-A
   `ThetLogos.FiniteSpectralTriple.pi` is landed as "multiplicative and
   unital but not additive" (`PreOptionARepresentation`, T1 verdict; its
   sibling `pi0`'s non-additivity is moreover FORCED by the landed
   obstruction `additive_rep_u1_eL_trivial`). `pi` can never fill the
   field, under any ring structure on `SMAlgebra`.

3. **The additive candidates are the wrong species for `AlgHom`.** The
   only additive candidates with landed law bundles are the Dial-One
   chapter's `pi1` / `piAnti` (`dialOneBase_pi1`, `dialOneBase_piAnti`:
   multiplicative, additive, star-preserving, unital, γ-even w.r.t.
   `afMul`/`afAdd`/`afStar`). But `AlgHom` also requires scalar
   compatibility (`commutes'`), which no landed theorem gives — and the
   entry forms show it is FALSE for the diagonal ℂ-algebra structure:
   every such rep sends the U(1) entry to `star a.u1` at the e_R slot
   (conjugation), while ν_R receives `a.u1`; no `Algebra ℂ SMAlgebra`
   structure makes both slots scalar-correct. The corpus's SM
   representations are *-representations of a real *-algebra, not
   ℂ-algebra maps; the species mismatch is structural, not a missing
   lemma.

Per the lane charter, a field that does not discharge is a STOP-and-report
event, not a license to prove new mathematics quietly and not a license to
fill by fiat. **Kills: K-MIR-FIAT NOT FIRED (nothing postulated — the lane
stopped instead); K-MIR-PROXY NOT FIRED (no re-declared copy was built);
K-MIR-DUP NOT FIRED.** What a successor brick needs is priced in the lane
report: (i) an A-side brick installing the af-operation instance bundle
with componentwise axiom proofs, and (ii) a species decision — either a
genuinely ℂ-algebra-map representation (new mathematics, constrained by
the landed `additive_rep_u1_eL_trivial` obstruction) or a framework change
to `TripleData` itself. Both are above a lane's pay grade.

## Faces

NO CLAIM. Dials 0/4. Pre-registered DIAL-INELIGIBLE. Working label only —
the public name is Jeff's hand. Pin: 0 strict.
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import ThetLogos.ProductTriple
import ThetLogos.MartinettiRep
import ThetLogos.FiniteSpectralTriple
import ThetLogos.Scaffold32

namespace ThetLogos.FiniteTripleInstancePin

open scoped ComplexOrder

/-! ## §1. Operator-side packaging definitions (these DO discharge)

Pure definitions (Tier T2), mirroring `ConcreteFiniteModel`'s Pauli
packaging at `I32`: the operators of the concrete seat transported to
`Module.End ℂ (EuclideanSpace ℂ I32)` through the standard basis. No
relations are asserted here; §3 names the landed theorem that discharges
each relation field. -/

/-- The standard basis of `ℂ³²` as a Euclidean space. -/
noncomputable def basis32 : Module.Basis I32 ℂ (EuclideanSpace ℂ I32) :=
  (EuclideanSpace.basisFun I32 ℂ).toBasis

/-- Matrices on `I32` as endomorphisms of `EuclideanSpace ℂ I32`. -/
noncomputable def endAlgEquiv32 :
    Module.End ℂ (EuclideanSpace ℂ I32) ≃ₐ[ℂ] Matrix I32 I32 ℂ :=
  LinearMap.toMatrixAlgEquiv basis32

/-- The grading as an endomorphism: the seat's `gammaF`. -/
noncomputable def smGrading : Module.End ℂ (EuclideanSpace ℂ I32) :=
  endAlgEquiv32.symm gammaF

/-- The Dirac operator as an endomorphism: the seat's `smDirac` at fixed
(opaque) Yukawa parameters. -/
noncomputable def smDiracOp (yNu yE yU yD yR : ℂ) :
    Module.End ℂ (EuclideanSpace ℂ I32) :=
  endAlgEquiv32.symm (smDirac yNu yE yU yD yR)

/-- The Framework-G conjugation on endomorphisms, at the seat: the
`piOp` form `X ↦ UJ * Xᵀ * UJ` (transpose, NOT conjugate-transpose). -/
noncomputable def conjJ32 :
    Module.End ℂ (EuclideanSpace ℂ I32) →ₗ[ℂ]
      Module.End ℂ (EuclideanSpace ℂ I32) where
  toFun X := endAlgEquiv32.symm
    (UJ * (endAlgEquiv32 X).transpose * UJ)
  map_add' X Y := by
    simp [Matrix.transpose_add, Matrix.mul_add, Matrix.add_mul]
  map_smul' r X := by
    simp [Matrix.transpose_smul, Matrix.mul_smul, smul_mul_assoc]

/-- The antilinear real structure at the seat: `J = UJ ∘ conjugation`,
coordinate form `x ↦ (i ↦ conj (x (partner i)))`. -/
noncomputable def Janti32 :
    EuclideanSpace ℂ I32 →ₛₗ[starRingEnd ℂ] EuclideanSpace ℂ I32 where
  toFun x := WithLp.toLp 2 (fun i => star (x (partner i)))
  map_add' x y := by
    ext i
    simp [PiLp.add_apply, star_add]
  map_smul' r x := by
    ext i
    simp [PiLp.smul_apply, star_mul, smul_eq_mul, mul_comm]

/-- The sesquilinear form: the standard ℓ² inner product, as in the
Pauli instance (`innerₛₗ ℂ`). -/
noncomputable def sesq32 :
    EuclideanSpace ℂ I32 →ₛₗ[starRingEnd ℂ]
      (EuclideanSpace ℂ I32 →ₗ[ℂ] ℂ) :=
  innerₛₗ ℂ

/-- The KO row of the seat: `⟨ε, ε′, ε″⟩ = ⟨+1, +1, −1⟩` (KO-dimension 6). -/
def ko6sig : KOSignature := ⟨1, 1, -1⟩

/-! ## §2. The frozen target

What a completed brick would have to exhibit: a `FiniteFactor` whose
operator data is exactly §1's packaging of the concrete seat. Frozen as a
`Prop`; this pin asserts nothing about its truth. -/

/-- **The frozen instance target.** The operator equalities are stated with
`HEq`: `D`, `Γ`, `ηsym` live in `Module.End ℂ F.toTripleData.S`, which only
becomes `EuclideanSpace ℂ I32` after the `S` clause — plain `Eq` does not
elaborate (formulation defect found at this pin's first build, 2026-11-07,
and repaired here before any content existed; the proposition denoted is
the same). -/
def smInstanceTarget (yNu yE yU yD yR : ℂ) : Prop :=
  ∃ F : FiniteFactor,
    F.toTripleData.A = SMAlgebra ∧
    F.toTripleData.S = EuclideanSpace ℂ I32 ∧
    HEq F.toTripleData.D (smDiracOp yNu yE yU yD yR) ∧
    HEq F.toTripleData.Γ smGrading ∧
    HEq F.toTripleData.ηsym smGrading ∧
    F.toTripleData.ko = ko6sig

/-! ## §3. The discharge map (frozen)

Operator side — every field discharges from a landed theorem:

* `hΓsq` ← `gammaF_involutive` (Scaffold32).
* `hΓD` ← `smDirac_grading_odd` (MartinettiRep), rearranged.
* `hconjJ_mul` / `hconjJ_inv` / `hconjJ_one` ← transpose laws
  (`Matrix.transpose_mul`, `Matrix.transpose_transpose`) + `UJ_mul_self`.
* `hkoD` (ε′ = +1) ← `smDirac_J_compat` (linear form
  `UJ * D.map star = D * UJ`) + `smDirac_self_adjoint` (bridge
  `Dᵀ = D.map star`).
* `hkoΓ` (ε″ = −1) ← `UJ_gammaF_anticommute` + `UJ_mul_self`, with
  `gammaFᵀ = gammaF` from `gammaF_apply_diag` / `gammaF_apply_off_diag`.
* `hJanti_sq` (ε = +1) ← `partner_involutive`.
* `hJanti_D` ← `smDirac_J_compat` (mulVec form).
* `hJanti_Γ` ← `UJ_gammaF_anticommute` + diagonality of `gammaF`.
* `hηsym_sq` ← `gammaF_involutive`.
* `hηsym_selfadj` ← `gammaF_self_adjoint` in entry form.
* `hπeven` ← clause 7 of a landed `DialOneBase` package
  (`dialOneBase_pi1` / `dialOneBase_piAnti`) — for the π those packages
  are about; see §4 for why this does not complete the field.

Algebra side — NO discharge exists (the STOP):

* `ringA`, `starA`, `algA`, `starModA` — no instances on `SMAlgebra`
  in-tree (see the verdict block above, item 1).
* `π` as `AlgHom` — `map_mul` / `map_add` / `map_one` would cite
  `DialOneBase` clauses 1 / 2 / 4 for `pi1` or `piAnti`, but
  `commutes'` has no landed discharge and is false for the diagonal
  ℂ-algebra structure (verdict block, item 3); the audit's headline
  candidate `pi` is landed non-additive (item 2).
-/

end ThetLogos.FiniteTripleInstancePin
