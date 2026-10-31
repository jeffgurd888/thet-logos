import Mathlib.Tactic
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import ThetLogos.Q7C4R4Charge
import ThetLogos.Q7C4R4Linker

/-!
# ThetLogos.Q7C4R4LinkC4 — the C4-sector correspondence (Q7CR-6b)

**Status: T1 bookkeeping brick. BOOKKEEPING-GRADE, on the face:
this module's content is a conjugation computation and a
factorwise carriage — honest bookkeeping about landed objects,
labeled as such, not a discovery claim. NO CLAIM. Dials 0/4.
No measured number is claimed by this line. Parts of any
Millennium statement closed by this line: 0.**

Governing pack: `pack-q7cr-6b.md`; line scoping:
`scoping-q7cr-6-linker-2026-10-30.md` §2(b) (the sector /
correspondence form). Gates consumed, not re-chosen: Q7CR-3
(`ThetLogos.Q7C4R4Charge`: `shiftC4`, `fourierC4`, `chargeC4`,
`chargeComp`, `sectorComp`), Q7CR-6a
(`ThetLogos.Q7C4R4Linker`: `q7Rep`, `q7ShiftR`), Q7CR-1b
(`ThetLogos.Q7C4R4Assembly`: `opTensorQ` and its algebra).

## The standing sentence, verbatim

**"via C4" survives only as "graded by C4."**

That sentence is the whole claim-shape of this brick. The C4
Fourier transform `F4` built in §1 acts only on the C4 factor.
The Q7 and R4 factors are spectators in the C4 clause: §2
carries the C7 action (6a's `q7ShiftR`) and the C4 shift
factorwise on the composite and proves the two carried actions
commute because they act on different tensor factors; §3 states
the graded correspondence — the composite's C4 sectors
(Q7CR-3's `sectorComp j`) are exactly the character eigenspaces
of the carried C4 shift, tensored with the spectator factors.
Nothing here relates the C7 action to any R4 action, and
nothing here upgrades the grading to anything stronger than a
grading.

## What is proved

1. **The F4 conjugation (§1).** The character vectors
   `fourierC4 j` are a ℂ-basis of the C4 factor
   (`fourierBasisC4`: eigenvectors of the shift for pairwise
   distinct eigenvalues, hence linearly independent, in
   dimension 4). The associated coefficient equiv is `F4`
   (`fourierEquivC4`). The conjugation is stated in the
   equiv-applied-to-vectors form the landed objects support,
   and then as an operator identity: the ℂ-linear shift is
   `F4 ∘ diagCharC4 ∘ F4⁻¹`, where `diagCharC4` is the
   character diagonal, multiplying the `j`-th coefficient by
   `i^j`. This restates Q7CR-3's `shiftC4_fourierC4` as a
   conjugation; the eigenvalues are the character values.
2. **Factorwise carriage (§2).** `actQ7Comp = q7ShiftR ⊗ 1 ⊗ 1`
   and `actC4Comp = 1 ⊗ shiftC4 ⊗ 1` on the composite, with
   pure-tensor formulas, the tensor-factor commutation of the
   two carried actions, and the carried order laws
   (`actQ7Comp ^ 7 = 1`, `actC4Comp ^ 4 = 1`, the latter from
   the shift permutation's fourth iterate).
3. **The graded correspondence (§3).** A pure tensor lies in
   composite sector `j` exactly when its C4 factor lies in
   factor sector `j` (the spectator factors unconstrained);
   the carried C4 shift acts on a pure tensor in sector `j`'s
   character line by the character value `i^j`; and the
   correspondence is equivariant: the carried shift preserves
   every composite sector, and on the character line it is
   multiplication by `i^j`, while `chargeComp` reads the same
   line with eigenvalue `j`. The sectors ARE the character
   eigenspaces of the carried shift, tensored with the
   spectator factors — correspondence by grading, only.

## Fences

- BOOKKEEPING-GRADE, as labeled above: a conjugation
  computation and a factorwise carriage about landed objects.
- The standing sentence above stands verbatim. F4 acts only
  on the C4 factor; Q7 and R4 are spectators in the C4 clause,
  and this module says so on its face.
- Jeff's headline stands as his T5 on Q7CR-0's face, untouched
  by this brick in either direction beyond the scoping record.
- NO CLAIM; dials 0/4; no measured number.
-/

namespace ThetLogos

open TensorProduct

/-! ## §1. The F4 conjugation on the C4 factor

The landed shift `shiftC4` is ℝ-linear (it lives on the
realified factor). Its underlying function is ℂ-linear; we
register that ℂ-linear form once (`shiftC4C`), prove it agrees
with `shiftC4` on every vector, and run the conjugation over
ℂ, where the character basis is a basis. -/

/-- **The C4 cyclic shift, ℂ-linear form**: the same function
as Q7CR-3's ℝ-linear `shiftC4`, registered as a ℂ-linear map
(permutation of sites is ℂ-linear). -/
def shiftC4C : (Fin 4 → ℂ) →ₗ[ℂ] (Fin 4 → ℂ) where
  toFun := fun x k => x (c4ShiftPerm k)
  map_add' := fun x y => rfl
  map_smul' := fun r x => by
    funext k
    simp [Pi.smul_apply, smul_eq_mul]

/-- The ℂ-linear shift agrees with the landed ℝ-linear shift
on every vector. -/
theorem shiftC4C_eq_shiftC4 (x : Fin 4 → ℂ) :
    shiftC4C x = shiftC4 x := by
  funext k
  show x (c4ShiftPerm k) = shiftC4 x k
  rw [shiftC4_apply]

/-- The ℂ-linear shift's character eigenvectors, restated from
Q7CR-3's `shiftC4_fourierC4`. -/
theorem shiftC4C_fourierC4 (j : Fin 4) :
    shiftC4C (fourierC4 j) = (Complex.I ^ (j.val)) • fourierC4 j := by
  rw [shiftC4C_eq_shiftC4]
  exact shiftC4_fourierC4 j

/-- **The character diagonal**: the ℂ-linear operator on
coefficient vectors multiplying the `j`-th coefficient by the
character value `i^j`. This is the diagonal that §1's
conjugation produces. -/
def diagCharC4 : (Fin 4 → ℂ) →ₗ[ℂ] (Fin 4 → ℂ) where
  toFun := fun x j => (Complex.I ^ (j.val)) * x j
  map_add' := fun x y => by
    funext j
    simp [Pi.add_apply, mul_add]
  map_smul' := fun r x => by
    funext j
    simp [Pi.smul_apply, smul_eq_mul]
    ring

/-- The character diagonal, pointwise. -/
theorem diagCharC4_apply (x : Fin 4 → ℂ) (j : Fin 4) :
    diagCharC4 x j = (Complex.I ^ (j.val)) * x j :=
  rfl

/-- The character values `i^j` for `j : Fin 4` are pairwise
distinct: the four eigenvalues of the shift are different. -/
theorem charValueC4_injective :
    Function.Injective (fun j : Fin 4 => Complex.I ^ (j.val)) := by
  intro a b hab
  fin_cases a <;> fin_cases b <;>
    simp_all [Complex.ext_iff] <;> norm_num at hab

/-- Each character vector is an eigenvector of the ℂ-linear
shift, for its character value, in the pin's eigenvector
form. -/
theorem shiftC4C_hasEigenvector (j : Fin 4) :
    Module.End.HasEigenvector shiftC4C (Complex.I ^ (j.val))
      (fourierC4 j) :=
  ⟨Module.End.mem_eigenspace_iff.mpr (shiftC4C_fourierC4 j),
    fourierC4_ne_zero j⟩

/-- **The character vectors are linearly independent** over ℂ:
eigenvectors for pairwise distinct eigenvalues of one
operator. -/
theorem fourierC4_linearIndependent :
    LinearIndependent ℂ fourierC4 :=
  Module.End.eigenvectors_linearIndependent' shiftC4C
    (fun j : Fin 4 => Complex.I ^ (j.val)) charValueC4_injective
    fourierC4 shiftC4C_hasEigenvector

/-- **The character basis of the C4 factor**: the four
character vectors form a ℂ-basis (linear independence in
dimension 4, at full rank). -/
noncomputable def fourierBasisC4 : Module.Basis (Fin 4) ℂ (Fin 4 → ℂ) :=
  basisOfLinearIndependentOfCardEqFinrank fourierC4_linearIndependent
    (by simp)

/-- The character basis's vectors are the character vectors. -/
theorem fourierBasisC4_apply (j : Fin 4) :
    fourierBasisC4 j = fourierC4 j :=
  congrFun (coe_basisOfLinearIndependentOfCardEqFinrank
    fourierC4_linearIndependent (by simp)) j

/-- **F4, the C4 Fourier transform**: the linear equiv sending
a coefficient vector to the character combination it names —
the equiv whose `j`-th basis vector is `fourierC4 j`. This is
the form the landed objects support: `fourierC4` landed as a
family of vectors, and `F4` is its coefficient equiv
(`fourierBasisC4.equivFun.symm`). -/
noncomputable def fourierEquivC4 :
    (Fin 4 → ℂ) ≃ₗ[ℂ] (Fin 4 → ℂ) :=
  fourierBasisC4.equivFun.symm

/-- F4 on a coefficient vector, as a character combination:
`F4 x = ∑ j, x j • fourierC4 j`. -/
theorem fourierEquivC4_apply (x : Fin 4 → ℂ) :
    fourierEquivC4 x = ∑ j, x j • fourierC4 j := by
  show fourierBasisC4.equivFun.symm x = _
  rw [Module.Basis.equivFun_symm_apply]
  exact Finset.sum_congr rfl fun j _ => by
    rw [fourierBasisC4_apply]

/-- F4, pointwise: `(F4 x) k = ∑ j, x j * fourierC4 j k`. -/
theorem fourierEquivC4_apply_apply (x : Fin 4 → ℂ) (k : Fin 4) :
    fourierEquivC4 x k = ∑ j, x j * fourierC4 j k := by
  rw [fourierEquivC4_apply, Finset.sum_apply]
  exact Finset.sum_congr rfl fun j _ => by
    simp [Pi.smul_apply, smul_eq_mul]

/-- **The conjugation, vector form**: the shift of a character
combination is the character combination of the diagonally
scaled coefficients — `shiftC4 (F4 x) = F4 (diagCharC4 x)`,
with the landed ℝ-linear shift on the left. This is
Q7CR-3's `shiftC4_fourierC4`, restated as a conjugation on
every vector, not only on the character vectors themselves. -/
theorem shiftC4_fourierEquivC4 (x : Fin 4 → ℂ) :
    shiftC4 (fourierEquivC4 x) = fourierEquivC4 (diagCharC4 x) := by
  funext k
  rw [shiftC4_apply, fourierEquivC4_apply_apply,
    fourierEquivC4_apply_apply]
  apply Finset.sum_congr rfl
  intro j _
  have hpt : fourierC4 j (c4ShiftPerm k)
      = (Complex.I ^ (j.val)) * fourierC4 j k := by
    have h := congrFun (shiftC4_fourierC4 j) k
    rw [shiftC4_apply] at h
    rw [h]
    simp [Pi.smul_apply, smul_eq_mul]
  rw [hpt, diagCharC4_apply]
  ring

/-- **The conjugation, ℂ-linear vector form**: the same
identity for the ℂ-linear shift. -/
theorem shiftC4C_fourierEquivC4 (x : Fin 4 → ℂ) :
    shiftC4C (fourierEquivC4 x) = fourierEquivC4 (diagCharC4 x) := by
  rw [shiftC4C_eq_shiftC4]
  exact shiftC4_fourierEquivC4 x

/-- **The conjugation, operator form**: the ℂ-linear shift is
the conjugate of the character diagonal by F4,
`shiftC4C = F4 ∘ₗ diagCharC4 ∘ₗ F4⁻¹`. The shift is diagonal
in the character basis, with eigenvalues the character
values `i^j`. -/
theorem shiftC4C_eq_conj_diagCharC4 :
    shiftC4C = (fourierEquivC4 : (Fin 4 → ℂ) →ₗ[ℂ] (Fin 4 → ℂ))
      ∘ₗ diagCharC4
      ∘ₗ (fourierEquivC4.symm : (Fin 4 → ℂ) →ₗ[ℂ] (Fin 4 → ℂ)) := by
  apply LinearMap.ext
  intro x
  have hx : x = fourierEquivC4 (fourierEquivC4.symm x) := by
    rw [LinearEquiv.apply_symm_apply]
  conv_lhs => rw [hx]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  exact shiftC4C_fourierEquivC4 _

/-- **The conjugation, inverse operator form**: F4 conjugates
the shift back to the diagonal,
`diagCharC4 = F4⁻¹ ∘ₗ shiftC4C ∘ₗ F4`. -/
theorem diagCharC4_eq_conj_shiftC4C :
    diagCharC4 = (fourierEquivC4.symm : (Fin 4 → ℂ) →ₗ[ℂ] (Fin 4 → ℂ))
      ∘ₗ shiftC4C
      ∘ₗ (fourierEquivC4 : (Fin 4 → ℂ) →ₗ[ℂ] (Fin 4 → ℂ)) := by
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  have h := shiftC4C_fourierEquivC4 x
  have h2 : fourierEquivC4.symm (fourierEquivC4 (diagCharC4 x))
      = diagCharC4 x :=
    LinearEquiv.symm_apply_apply _ _
  rw [← h] at h2
  exact h2.symm

/-! ## §2. Factorwise carriage on the composite

Both factor actions are carried factorwise via `opTensorQ`:
the C7 register shift (6a's realified `q7ShiftR`) as
`q7ShiftR ⊗ 1 ⊗ 1`, and the C4 shift as `1 ⊗ shiftC4 ⊗ 1`.
They act on different tensor factors, and their commutation
is the tensor-factor commutation of the landed `opTensorQ`
algebra (`opTensorQ_mul`), not an extra hypothesis. -/

/-- The general tensor-factor commutation, from the landed
`opTensorQ_mul`: an operator carried on the Q7 factor alone
commutes with an operator carried on the C4 factor alone. -/
theorem opTensorQ_left_mid_commute (X : Module.End ℝ (Fin 7 → ℂ))
    (Y : Module.End ℝ (Fin 4 → ℂ)) :
    opTensorQ X 1 1 * opTensorQ 1 Y 1
      = opTensorQ 1 Y 1 * opTensorQ X 1 1 := by
  rw [← opTensorQ_mul, ← opTensorQ_mul]
  simp

/-- `1 ⊗ 1 ⊗ 1 = 1` at the registered factors, from the
landed `opTensor3_one`. -/
theorem opTensorQ_one :
    opTensorQ (1 : Module.End ℝ (Fin 7 → ℂ))
      (1 : Module.End ℝ (Fin 4 → ℂ)) (1 : Module.End ℝ Minkowski)
      = 1 :=
  opTensor3_one

/-- **The carried C7 action**: 6a's realified register shift
`q7ShiftR`, carried factorwise on the composite as
`q7ShiftR ⊗ 1 ⊗ 1` — identity on the C4 and R4 factors. -/
noncomputable def actQ7Comp : Module.End ℝ q7c4r4Composite :=
  opTensorQ q7ShiftR 1 1

/-- **The carried C4 action**: Q7CR-3's `shiftC4`, carried
factorwise on the composite as `1 ⊗ shiftC4 ⊗ 1` — identity
on the Q7 and R4 factors, the spectator factors of the C4
clause. -/
noncomputable def actC4Comp : Module.End ℝ q7c4r4Composite :=
  opTensorQ 1 shiftC4 1

/-- The carried C7 action on pure tensors: it shifts the Q7
factor and leaves the other two factors untouched. -/
theorem actQ7Comp_tmul (x : Fin 7 → ℂ) (y : Fin 4 → ℂ)
    (z : Minkowski) :
    actQ7Comp ((x ⊗ₜ[ℝ] y) ⊗ₜ[ℝ] z)
      = (q7ShiftR x ⊗ₜ[ℝ] y) ⊗ₜ[ℝ] z := by
  unfold actQ7Comp
  rw [opTensorQ_tmul]
  simp [Module.End.one_apply]

/-- The carried C4 action on pure tensors: it shifts the C4
factor and leaves the other two factors untouched. -/
theorem actC4Comp_tmul (x : Fin 7 → ℂ) (y : Fin 4 → ℂ)
    (z : Minkowski) :
    actC4Comp ((x ⊗ₜ[ℝ] y) ⊗ₜ[ℝ] z)
      = (x ⊗ₜ[ℝ] shiftC4 y) ⊗ₜ[ℝ] z := by
  unfold actC4Comp
  rw [opTensorQ_tmul]
  simp [Module.End.one_apply]

/-- **The carried actions commute** (tensor-factor
commutation): the carried C7 action and the carried C4
action act on different factors of the composite, so they
commute — proved from `opTensorQ_mul`, the landed algebra. -/
theorem actQ7Comp_comm_actC4Comp :
    actQ7Comp * actC4Comp = actC4Comp * actQ7Comp :=
  opTensorQ_left_mid_commute q7ShiftR shiftC4

/-- The carried C7 action at the power of a register power:
carriage respects powers of the factor action. -/
theorem actQ7Comp_pow (k : ℕ) :
    actQ7Comp ^ k = opTensorQ (q7ShiftR ^ k) 1 1 := by
  induction k with
  | zero =>
    simp only [pow_zero]
    exact opTensorQ_one.symm
  | succ k ih =>
    rw [pow_succ, ih]
    show opTensorQ (q7ShiftR ^ k) 1 1 * opTensorQ q7ShiftR 1 1 = _
    rw [← opTensorQ_mul]
    simp [pow_succ]

/-- **The carried C7 action has order dividing 7**, carried
from 6a's `q7ShiftR_pow_seven` through the tensor carriage. -/
theorem actQ7Comp_pow_seven : actQ7Comp ^ 7 = 1 := by
  rw [actQ7Comp_pow, q7ShiftR_pow_seven]
  exact opTensorQ_one

/-- The shift permutation's fourth iterate is the identity
(the 4-cycle closes). -/
theorem c4ShiftPerm_iterate_four (k : Fin 4) :
    c4ShiftPerm^[4] k = k := by
  fin_cases k <;> rfl

/-- **The C4 shift has order dividing 4**: `shiftC4 ^ 4 = 1`,
from the fourth iterate of its permutation. -/
theorem shiftC4_pow_four : shiftC4 ^ 4 = 1 := by
  apply LinearMap.ext
  intro x
  funext k
  rw [shiftC4_pow_apply, c4ShiftPerm_iterate_four]
  rfl

/-- The carried C4 action at the power of a shift power:
carriage respects powers of the factor action. -/
theorem actC4Comp_pow (k : ℕ) :
    actC4Comp ^ k = opTensorQ 1 (shiftC4 ^ k) 1 := by
  induction k with
  | zero =>
    simp only [pow_zero]
    exact opTensorQ_one.symm
  | succ k ih =>
    rw [pow_succ, ih]
    show opTensorQ 1 (shiftC4 ^ k) 1 * opTensorQ 1 shiftC4 1 = _
    rw [← opTensorQ_mul]
    simp [pow_succ]

/-- **The carried C4 action has order dividing 4**, carried
from `shiftC4_pow_four` through the tensor carriage. -/
theorem actC4Comp_pow_four : actC4Comp ^ 4 = 1 := by
  rw [actC4Comp_pow, shiftC4_pow_four]
  exact opTensorQ_one

/-! ## §3. The graded correspondence

The composite's C4 grading is Q7CR-3's `chargeComp` with
sectors `sectorComp j`. The correspondence, in the exact form
the landed sector definitions support: on pure tensors the
sector membership is read entirely off the C4 factor; the
carried C4 shift's character eigenspaces, tensored with the
spectator factors, are the sectors' character lines; and the
carried shift preserves every sector. The Q7 and R4 factors
are spectators throughout: no condition on them appears in
any statement in this section. -/

/-- **Sector membership of a pure tensor is read off the C4
factor alone**: for nonzero spectator factors, a pure tensor
lies in composite sector `j` exactly when its C4 factor lies
in factor sector `j`. The Q7 and R4 factors are otherwise
unconstrained — spectators. (The nonzero hypotheses are
necessary: a zero pure tensor lies in every sector.) The
forward direction is read off by Q7CR-3's evaluation
contractions `contractC` at a site where each spectator is
nonzero. -/
theorem mem_sectorComp_tmul {x : Fin 7 → ℂ} {y : Fin 4 → ℂ}
    {z : Minkowski} {j : Fin 4} (hx : x ≠ 0) (hz : z ≠ 0) :
    ((x ⊗ₜ[ℝ] y) ⊗ₜ[ℝ] z) ∈ sectorComp j ↔ y ∈ sectorC4 j := by
  rw [mem_sectorComp, mem_sectorC4]
  constructor
  · intro h
    obtain ⟨s₇, hs₇⟩ := Function.ne_iff.mp hx
    obtain ⟨sR, hsR⟩ := Function.ne_iff.mp hz
    simp only [Pi.zero_apply] at hs₇ hsR
    have hzC : (z sR : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hsR
    funext s₄
    have hcon := congrArg (contractC s₇ s₄ sR) h
    rw [chargeComp_tmul, contractC_tmul] at hcon
    have hsmul : contractC s₇ s₄ sR
          ((j.val : ℝ) • ((x ⊗ₜ[ℝ] y) ⊗ₜ[ℝ] z))
        = ((j.val : ℝ) : ℂ) * (x s₇ * y s₄ * (z sR : ℂ)) := by
      rw [map_smul]
      simp [Complex.real_smul, contractC_tmul]
    rw [hsmul] at hcon
    have hne : x s₇ * (z sR : ℂ) ≠ 0 := mul_ne_zero hs₇ hzC
    have key : (x s₇ * (z sR : ℂ)) * chargeC4 y s₄
        = (x s₇ * (z sR : ℂ)) * (((j.val : ℝ) : ℂ) * y s₄) := by
      linear_combination hcon
    have hval := mul_left_cancel₀ hne key
    rw [hval]
    simp [Pi.smul_apply, Complex.real_smul]
  · intro h
    rw [chargeComp_tmul, h]
    simp [TensorProduct.tmul_smul, TensorProduct.smul_tmul]

/-- **The factor-level commutation behind sector
preservation**: `chargeC4` commutes with `shiftC4` — the
charge operator is a polynomial in the shift (Q7CR-3 §2), and
the pointwise computation is the same four site values on
both sides. -/
theorem chargeC4_mul_shiftC4 : chargeC4 * shiftC4 = shiftC4 * chargeC4 := by
  apply LinearMap.ext
  intro x
  funext k
  simp only [Module.End.mul_apply, chargeC4_apply, shiftC4_apply]

/-- **The carried commutation of the grading with the
carried shift**: `chargeComp` commutes with `actC4Comp` on
the composite, by the factor commutation carried through
`opTensorQ_mul`. -/
theorem chargeComp_mul_actC4Comp :
    chargeComp * actC4Comp = actC4Comp * chargeComp := by
  show opTensorQ 1 chargeC4 1 * opTensorQ 1 shiftC4 1
    = opTensorQ 1 shiftC4 1 * opTensorQ 1 chargeC4 1
  rw [← opTensorQ_mul, ← opTensorQ_mul]
  simp [chargeC4_mul_shiftC4]

/-- **The carried C4 shift preserves every composite
sector**: the grading and the carried shift commute, so the
shift carries each `chargeComp`-eigenspace into itself.
This is the equivariance of the graded correspondence. -/
theorem actC4Comp_mem_sectorComp {j : Fin 4}
    {v : q7c4r4Composite} (hv : v ∈ sectorComp j) :
    actC4Comp v ∈ sectorComp j := by
  rw [mem_sectorComp] at hv ⊢
  have hcomm : chargeComp (actC4Comp v) = actC4Comp (chargeComp v) := by
    have h := LinearMap.congr_fun chargeComp_mul_actC4Comp v
    simpa [Module.End.mul_apply] using h
  rw [hcomm, hv, map_smul]

/-- **The character line under the carried shift**: on a
pure tensor whose C4 factor is the `j`-th character vector,
the carried C4 shift acts by the character value `i^j` on
that factor — the carried action's character decomposition,
read on pure tensors. -/
theorem actC4Comp_tmul_fourierC4 (x : Fin 7 → ℂ) (j : Fin 4)
    (z : Minkowski) :
    actC4Comp ((x ⊗ₜ[ℝ] fourierC4 j) ⊗ₜ[ℝ] z)
      = (x ⊗ₜ[ℝ] ((Complex.I ^ (j.val)) • fourierC4 j)) ⊗ₜ[ℝ] z := by
  rw [actC4Comp_tmul, shiftC4_fourierC4]

/-- **The character line under the composite grading**: the
same pure tensor is a `chargeComp`-eigenvector with real
eigenvalue `j` — it lies in composite sector `j`, and the
grading reads the character line with the charge `j` while
the carried shift reads it with the character value `i^j`.
The two readings are the two sides of the graded
correspondence. -/
theorem chargeComp_tmul_fourierC4 (x : Fin 7 → ℂ) (j : Fin 4)
    (z : Minkowski) :
    chargeComp ((x ⊗ₜ[ℝ] fourierC4 j) ⊗ₜ[ℝ] z)
      = (j.val : ℝ) • ((x ⊗ₜ[ℝ] fourierC4 j) ⊗ₜ[ℝ] z) := by
  rw [chargeComp_tmul, chargeC4_fourierC4_real]
  simp [TensorProduct.tmul_smul, TensorProduct.smul_tmul]

end ThetLogos
