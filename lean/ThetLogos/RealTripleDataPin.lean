/-
# ThetLogos.RealTripleDataPin — ROPE BRIDGE (B): the real-species triple
  class and the frozen ℂ³² target (interface-first pin; 0 strict)

Fired by Zero, 2026-11-08 ("scope build and run" → "Both — scope both
now"), on the design scoping `your_files/rope-bridge-b-design-scope-2026-11-08.md`
(verdict: BUILD WITH CHANGES, band M, 22–32 strict). This pin freezes
the class shape and the target; the content module
(`ThetLogos.RealTripleInstance`) builds behind it. Working label only —
the public name is Zero's hand.

## The §0 adoption record (on the face, dated and attributed)

`PreOptionARepresentation` §0 decided, as corpus design, that `SMAlgebra`
carries no `Mul`/`Add`/`Star` instances and that the corpus's
representations are stated against the componentwise operations
`afMul`/`afAdd`/`afStar`; the FiniteTripleInstance lane STOPPED at that
design (2026-11-07): the generic framework's `TripleData` demands a
ℂ-algebra map, and the seat's representations are *-representations of
a REAL *-algebra — the ℂ-scalar law (`AlgHom.commutes'`) is false at the
seat (the e_R leaf receives `star a.u1` against ν_R's `a.u1`).

Zero's direction of 2026-11-08 reverses that design decision **in
ADOPTION form**: `TripleData` is NOT edited; a second class,
`RealTripleData`, is built BESIDE it, identical field-by-field except
that the algebra's scalar species is ℝ (`Algebra ℝ A`,
`StarModule ℝ A`) and `π` is a law bundle over ℝ whose scalar law
`hπ_smul` is the exact ℝ-analogue of the false `commutes'` — true at
the seat because `star (r : ℂ) = (r : ℂ)` for real `r`, and because
`pi1`'s leaves are summand-pure (the Route B changes). §0's face text
is likewise NOT edited: it stands as the historical record of the
design this module reverses by addition, exactly as the 2026-11-07
class amendment adopted `RealCentralizingClass` beside
`CentralizingClass` and left the original class and the (α) verdict
standing.

## What this pin is, and is not

Definitions and the frozen target ONLY (0 strict). It asserts nothing
about the target's truth. The operator packaging of the seat is NOT
re-declared here: `basis32`, `endAlgEquiv32`, `smGrading`, `smDiracOp`,
`conjJ32`, `Janti32`, `sesq32`, `ko6sig` are imported from
`FiniteTripleInstancePin` §1 (K-MIR-DUP hygiene).

Design decisions frozen here, from the design scoping:

* **S does not change species.** The Hilbert space stays a ℂ-module;
  reality lives in the algebra species and in `J`. The "real" of
  `RealTripleData` is the algebra species and the form-level star law.
* **Exactly two instance fields re-species** vs `TripleData`:
  `algA : Algebra ℂ A` → `algR : Algebra ℝ A`, and
  `starModA : StarModule ℂ A` → `starModR : StarModule ℝ A`.
* **π is the §1.3 law bundle** (bare map + `hπ_one`, `hπ_mul`,
  `hπ_add`, `hπ_star` through the class's own `sesq`, `hπ_smul`).
  The `StarAlgHom`-over-ℝ and `AlgHom`-over-ℝ shapes are rejected for
  the reasons recorded in the design scoping §1.3. No `hπ_zero` field
  (it follows from `hπ_add`); no faithfulness or order-condition
  fields — `RealTripleData` mirrors `TripleData`'s field set, not
  `DialOneBase`'s.
* **One ordering note**: `sesq` is declared BEFORE `π` in this class
  (in `TripleData` it comes after), because `hπ_star` is stated
  through `sesq` and a structure field may only reference earlier
  fields. The field SET is unchanged from the design; only the
  declaration order moves, for elaboration.

## The frozen discharge map (for the content module)

Instance: `A := SMAlgebra`, `S := EuclideanSpace ℂ I32`, at the stop
pin's frozen Yukawa parameters; `π := endAlgEquiv32.symm ∘ pi1`.

* Algebra bundle (ALL NEW, from the af-operations, so that `afMul`,
  `afAdd`, `afStar`, `afOne`, `afZero` become the operations of record
  definitionally): `Mul/Add/Zero/One/Star/Neg` on `AF` componentwise;
  `AddCommGroup`, `Ring`, `StarRing` by `PreOptionARepresentation.ext_iff`
  + the components' landed instances; `Algebra ℝ AF` with
  `algebraMap ℝ AF r = ⟨(r : ℂ), (r : ℂ) • 1, (r : ℂ) • 1⟩` and
  `r • a = ⟨(r : ℂ) * a.u1, (r : ℂ) • a.q, (r : ℂ) • a.color⟩`;
  `StarModule ℝ AF` componentwise.
* `hπ_one` ← `DialOneBase` clause 4 (`pi1_one`), transported.
  `hπ_mul` ← clause 1 (`pi1_afMul`) + the definitional identification
  `* = afMul`, transported. `hπ_add` ← clause 2 (`pi1_afAdd`), same
  route. `hπeven` ← clause 7, transported.
* `hπ_star` ← clause 3 (`pi1_afStar`) at matrix level + NEW bridge
  `sesq32_end_adjoint` (the Euclidean adjoint identity under
  `endAlgEquiv32`). NEW PROOF, one of exactly two in the package.
* `hπ_smul` ← NEW entry proof over `pi1`'s table (every leaf ℂ-linear
  or star-twisted in a single component; star-twisted leaves scale by
  `star (r : ℂ) = (r : ℂ)`). NEW PROOF, the second.
* Operator fields ← the stop pin's frozen §3 discharge map, verbatim:
  `hΓsq` ← `gammaF_involutive`; `hΓD` ← `smDirac_grading_odd`
  rearranged; `hconjJ_mul/inv/one` ← transpose laws + `UJ_mul_self`;
  `hkoD` (ε′ = +1) ← `smDirac_J_compat` + the `Dᵀ = D.map star` bridge
  from `smDirac_self_adjoint`; `hkoΓ` (ε″ = −1) ←
  `UJ_gammaF_anticommute` + `UJ_mul_self` + `gammaFᵀ = gammaF`;
  `hJanti_sq` ← `partner_involutive`; `hJanti_D` ← `smDirac_J_compat`
  (mulVec form); `hJanti_Γ` ← `UJ_gammaF_anticommute` + diagonality of
  `gammaF`; `hηsym_sq` ← `gammaF_involutive`; `hηsym_selfadj` ←
  `gammaF_self_adjoint` in entry form.
* C1's certificates (`gammaF_isRealMat`, `UJ_isRealMat`,
  `DF_oneGen_isRealMat`) discharge NO field of this class — recorded
  here as the design scoping records it: C1 retired risk, its
  mechanical effect on this build is 0 theorems.

## Kills armed

* **K-ROPE-BUNDLE**: fires if any componentwise axiom of the algebra
  bundle fails (or surfaces as an elaboration diamond downstream —
  the integration root build is that check).
* **K-ROPE-SPECIES**: fires if any field stated in the real species
  fails at the seat for a reason the ℂ species was masking. Named
  watch-list: `hπ_smul` (at a star-twisted leaf), the
  `sesq32_end_adjoint` bridge, the `hπeven` transport.
* **K-MIR-FIAT / K-MIR-PROXY / K-MIR-DUP**: stay armed, do not fire by
  construction — nothing is postulated, π is the seat's own `pi1`,
  and the operator packaging is imported, not re-declared.

## Faces

NO CLAIM. Dials 0/4; Dial 1 = 0. Pre-registered DIAL-INELIGIBLE
(framework unification: this packages proved relations into a second
framework class and instantiates it; it proves no new seat relation
and moves no dial). What the landed instance will prove: that `pi1`'s
concrete seat carries a `RealFiniteFactor` whose operator data is
exactly the stop pin's packaging. What it will not prove: anything
about `TripleData` itself, any new relation at the seat, or any dial.
Pin: 0 strict.
-/

import ThetLogos.ProductTriple
import ThetLogos.FiniteTripleInstancePin
import ThetLogos.FiniteSpectralTriple
import ThetLogos.PreOptionARepresentation

namespace ThetLogos.RealTripleDataPin

open ThetLogos.FiniteTripleInstancePin

/-- **The real-species spectral-triple class** (Tier T2 design, in
    adoption form beside `TripleData`).

    Field-by-field the mirror of `TripleData` (ProductTriple), with
    exactly these changes: the algebra's scalar species is ℝ
    (`algR`, `starModR` in place of `algA`, `starModA`); `π` is a
    law bundle over ℝ instead of an `AlgHom` over ℂ; and `sesq` is
    declared before `π` because `hπ_star` is stated through it. The
    Hilbert space `S` remains a ℂ-module — see the module face. -/
class RealTripleData where
  A : Type
  S : Type
  [addS : AddCommGroup S]
  [modS : Module ℂ S]
  [ringA : Ring A]
  [starA : StarRing A]
  [algR : Algebra ℝ A]
  [starModR : StarModule ℝ A]
  sesq : S →ₛₗ[starRingEnd ℂ] (S →ₗ[ℂ] ℂ)
  π : A → Module.End ℂ S
  hπ_one : π 1 = 1
  hπ_mul : ∀ a b : A, π (a * b) = π a * π b
  hπ_add : ∀ a b : A, π (a + b) = π a + π b
  hπ_star : ∀ (a : A) (x y : S), sesq (π (star a) x) y = sesq x (π a y)
  hπ_smul : ∀ (r : ℝ) (a : A), π (r • a) = (r : ℂ) • π a
  D : Module.End ℂ S
  Γ : Module.End ℂ S
  hΓsq : Γ * Γ = 1
  hΓD : D * Γ = -(Γ * D)
  hπeven : ∀ a : A, Γ * π a = π a * Γ
  conjJ : Module.End ℂ S →ₗ[ℂ] Module.End ℂ S
  hconjJ_mul : ∀ x y : Module.End ℂ S, conjJ (x * y) = conjJ y * conjJ x
  hconjJ_inv : ∀ x : Module.End ℂ S, conjJ (conjJ x) = x
  hconjJ_one : conjJ 1 = 1
  ko : KOSignature
  hkoD : conjJ D = (ko.eps' : ℂ) • D
  hkoΓ : conjJ Γ = (ko.eps'' : ℂ) • Γ
  Janti : S →ₛₗ[starRingEnd ℂ] S
  hJanti_sq : Janti.comp Janti = (ko.eps : ℂ) • LinearMap.id
  hJanti_D : Janti.comp D = (ko.eps' : ℂ) • (D.comp Janti)
  hJanti_Γ : Janti.comp Γ = (ko.eps'' : ℂ) • (Γ.comp Janti)
  ηsym : Module.End ℂ S
  hηsym_sq : ηsym * ηsym = 1
  hηsym_selfadj : ∀ x y : S, sesq (ηsym x) y = sesq x (ηsym y)

/-- **The real finite factor** (Tier T2 design): KO-dimension 6 signs
    (the finite SM triple: `J_F² = +1`, `J_F D_F = D_F J_F`,
    `J_F Γ_F = −Γ_F J_F`), the exact mirror of `FiniteFactor`. -/
class RealFiniteFactor extends RealTripleData where
  ko6 : ko = ⟨1, 1, -1⟩

-- Projection instances: the class's instance-fields are not found by
-- TC automatically, so they are re-exported here (mirroring
-- ProductTriple's projections for `FiniteFactor`, with the two
-- re-speciesed fields in place of their ℂ forms).
instance RealFiniteFactor.instAddS [F : RealFiniteFactor] :
    AddCommGroup F.toRealTripleData.S := F.toRealTripleData.addS
instance RealFiniteFactor.instModS [F : RealFiniteFactor] :
    Module ℂ F.toRealTripleData.S := F.toRealTripleData.modS
instance RealFiniteFactor.instRingA [F : RealFiniteFactor] :
    Ring F.toRealTripleData.A := F.toRealTripleData.ringA
instance RealFiniteFactor.instStarA [F : RealFiniteFactor] :
    StarRing F.toRealTripleData.A := F.toRealTripleData.starA
instance RealFiniteFactor.instAlgR [F : RealFiniteFactor] :
    Algebra ℝ F.toRealTripleData.A := F.toRealTripleData.algR
instance RealFiniteFactor.instStarModR [F : RealFiniteFactor] :
    StarModule ℝ F.toRealTripleData.A := F.toRealTripleData.starModR

/-! ## The frozen target

What the content module has to exhibit: a `RealFiniteFactor` whose
algebra is `SMAlgebra`, whose spinor module is `EuclideanSpace ℂ I32`,
and whose operator data is exactly the stop pin's §1 packaging.
Frozen as a `Prop` (the `HEq` form is inherited from the stop pin's
frozen target, for the reason recorded on that pin's face); this pin
asserts nothing about its truth. -/

/-- **The frozen real-instance target.** -/
def realSmInstanceTarget (yNu yE yU yD yR : ℂ) : Prop :=
  ∃ F : RealFiniteFactor,
    F.toRealTripleData.A = SMAlgebra ∧
    F.toRealTripleData.S = EuclideanSpace ℂ I32 ∧
    HEq F.toRealTripleData.D (smDiracOp yNu yE yU yD yR) ∧
    HEq F.toRealTripleData.Γ smGrading ∧
    HEq F.toRealTripleData.ηsym smGrading ∧
    F.toRealTripleData.ko = ko6sig

end ThetLogos.RealTripleDataPin
