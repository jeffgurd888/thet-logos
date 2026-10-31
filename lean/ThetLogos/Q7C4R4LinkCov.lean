import Mathlib.Tactic
import ThetLogos.Q7C4R4Linker
import ThetLogos.Q7C4R4Spectrum
import ThetLogos.Q7C4R4Charge

/-!
# ThetLogos.Q7C4R4LinkCov - the covariance / visibility decision (Q7CR-6c)

**Status: T1 decision brick. NO CLAIM. Dials 0/4. No measured
number is claimed by this line. Parts of any Millennium statement
closed by this line: 0.**

Governing memo: `scoping-q7cr-6-linker-2026-10-30.md` section 2(c)
(the covariance / visibility form), section 3 (brick 6c), section 4
(kills). Gates consumed, not re-chosen: Q7CR-6a
(`ThetLogos.Q7C4R4Linker`: `q7Shift`, `q7ShiftCyc = finRotate 7`,
`q7Rep`, `q7ShiftR`), Q7CR-2 (`ThetLogos.Q7C4R4Spectrum`:
`factorQ7`, `factorQ7_D : factorQ7.D = diagOpC a₇`, with
`a₇ = (3, -3, 2, -2, 1, -1, 0)`), Q7CR-3 (`ThetLogos.Q7C4R4Charge`:
`sectorComp`, `chargeComp`, `diracInst`), Q7CR-1b
(`ThetLogos.Q7C4R4Assembly`: `diracQ7C4R4`).

## The decision, and the verdict (T1)

The registered decision (memo section 2(c)): at Q7CR-2's
instantiated `D₇ = factorQ7.D`, prove exactly one of (i) symmetry
(`S₇ D₇ S₇⁻¹ = D₇`) or (ii) orbit covariance (conjugation by the
`C₇` action permutes the family of diagonal packages by the stated
permutation of their clock diagonals, and the instantiated package
is not a symmetry fixed point).

**VERDICT: (ii) ORBIT COVARIANCE.** The conjugation identity is
proved for every diagonal parameter `d` and every power `k`
(`q7ConjPow_diagOpC`): conjugation by `S₇^k` sends `diagOpC d` to
`diagOpC (d ∘ cyc₇^k)`. At the instantiated seat the permuted
diagonal differs from the original - the entry at site `0` moves
from `3` to `-3` - so the non-symmetry corollary holds at full
rank (`factorQ7_not_symm`): **the supplied action is not a symmetry
of the instantiated package.** This is a finding about the
instantiated package, not a defect of the action or of the object:
the action is visible exactly as an orbit action on the family.

**K-Q7CR-6b (invisibility / decoration): DISARMED.** It was armed
for the case where the action neither leaves the packages
invariant, nor permutes them in a stated orbit, nor preserves any
stated charge / spectral reading. The orbit outcome is precisely
what disarms it: the action permutes the family by the stated
cyclic permutation of the clock diagonal (`q7ConjPow_diagOpC`),
carries the diagonal spectrum as a multiset to itself
(`q7ConjPow_diagSpectrum`), and preserves every composite charge
sector (`actQ7Comp_mem_sectorComp`). The action is visible, as an
orbit action; it is not decoration.

**K-Q7CR-6c (mediation) already FIRED at scoping** - not re-fired
or revived here. Jeff's headline stays his T5 interpretation on
Q7CR-0's face, untouched in either direction.

## The standing sentence, verbatim

"via C4" survives only as "graded by C4."

The C⁴ factor is this composite's grading clock: its character
sectors (`sectorComp j`, Q7CR-3) are the sectors inside which the
covariance verdict's charge clause is stated, and the Q⁷ action
is a spectator of that grading (section 3). C⁴ grades this
composite; no proved statement in this line makes C⁴ mediate
between its Q⁷ and R⁴ factors.

**Bounded-commutator vacuity caveat (line discipline).** In finite
dimension every operator here is bounded; the testable content of
this line is spectrum, grading behavior, and stated identities,
never bounded commutators. Nothing in this module states or
implies a bounded-commutator fact.

**Composite package transport: FULL, no seam.** Conjugation of
the instantiated composite Dirac by the factorwise action
`U₇ ⊗ 1 ⊗ 1` is proved to be exactly the stated partner package
built from the conjugated pair `(S₇ D₇ S₇⁻¹, S₇ γ₇ S₇⁻¹)`
(`composite_package_transport`, section 4): the grading transport
lands in the stated form (`q7Conj_one_gamma`), so the
pre-authorized PARTIAL at the grading-transport seam is not
needed.
-/

namespace ThetLogos

open TensorProduct

/-! ## Section 1. Powers of the shift, their inverses, conjugation -/

/-- Powers of the realified shift, read on vectors:
`((S₇ᴿ)^k x) i = x ((cyc₇^k) i)`, transported from the matrix law
`q7Shift_pow_mulVec_apply` through realification. -/
theorem q7ShiftPow_apply (k : ℕ) (x : Fin 7 → ℂ) (i : Fin 7) :
    ((q7ShiftR ^ k) x) i = x ((q7ShiftCyc ^ k) i) := by
  have h1 : ((q7ShiftR ^ k) x) i = ((q7ShiftLin ^ k) x) i := by
    rw [show q7ShiftR = realifyOp q7ShiftLin from rfl,
      realifyOp_pow_apply]
  rw [h1, q7ShiftLin_pow_apply, q7Shift_pow_mulVec_apply]

/-- The inverse-shift operator at power `k`: the permutation
operator of `(cyc₇^k)⁻¹`. -/
def q7ShiftPowInv (k : ℕ) : (Fin 7 → ℂ) →ₗ[ℝ] (Fin 7 → ℂ) :=
  permOpC (⇑(q7ShiftCyc ^ k)⁻¹)

/-- Pointwise formula for the inverse shift. -/
theorem q7ShiftPowInv_apply (k : ℕ) (x : Fin 7 → ℂ) (i : Fin 7) :
    (q7ShiftPowInv k x) i = x ((q7ShiftCyc ^ k)⁻¹ i) :=
  permOpC_apply _ _ _

/-- The power of the shift times its stated inverse is `1`. -/
theorem q7ShiftPow_mul_inv (k : ℕ) :
    (q7ShiftR ^ k) * q7ShiftPowInv k = 1 := by
  apply LinearMap.ext
  intro x
  funext i
  rw [Module.End.mul_apply, q7ShiftPow_apply, q7ShiftPowInv_apply]
  simp

/-- The stated inverse times the power of the shift is `1`. -/
theorem q7ShiftPow_inv_mul (k : ℕ) :
    q7ShiftPowInv k * (q7ShiftR ^ k) = 1 := by
  apply LinearMap.ext
  intro x
  funext i
  rw [Module.End.mul_apply, q7ShiftPowInv_apply, q7ShiftPow_apply]
  simp

/-- **Conjugation by the `k`-th power of the supplied action:**
`T ↦ (S₇ᴿ)^k * T * (S₇ᴿ)^{-k}`, with the inverse in the stated
permutation form of `q7ShiftPowInv`. -/
noncomputable def q7ConjPow (k : ℕ) (T : (Fin 7 → ℂ) →ₗ[ℝ] (Fin 7 → ℂ)) :
    (Fin 7 → ℂ) →ₗ[ℝ] (Fin 7 → ℂ) :=
  (q7ShiftR ^ k) * T * q7ShiftPowInv k

/-! ## Section 2. The factor-level decision: orbit covariance -/

/-- **THE FAMILY IDENTITY (T1).** Conjugation by the `k`-th power
of the supplied action permutes the diagonal family by the stated
cyclic permutation of the parameters: for every diagonal parameter
`d`, `(S₇^k) (diagOpC d) (S₇^k)⁻¹ = diagOpC (d ∘ cyc₇^k)`. This
is the orbit-covariance half of the registered decision, at the
full family level. -/
theorem q7ConjPow_diagOpC (k : ℕ) (d : Fin 7 → ℝ) :
    q7ConjPow k (diagOpC d) = diagOpC (d ∘ ⇑(q7ShiftCyc ^ k)) := by
  apply LinearMap.ext
  intro x
  funext i
  show ((q7ShiftR ^ k) * diagOpC d * q7ShiftPowInv k) x i
      = diagOpC (d ∘ ⇑(q7ShiftCyc ^ k)) x i
  rw [Module.End.mul_apply, Module.End.mul_apply, q7ShiftPow_apply,
    diagOpC_apply, q7ShiftPowInv_apply, diagOpC_apply]
  simp

/-- The generator's conjugation of the instantiated `D₇`, in
proved form: `S₇ D₇ S₇⁻¹ = diagOpC (a₇ ∘ cyc₇)`, the same
construction with its clock diagonal cyclically permuted. -/
theorem q7Conj_one_factorQ7_D :
    q7ConjPow 1 factorQ7.D = diagOpC (a₇ ∘ ⇑q7ShiftCyc) := by
  rw [factorQ7_D]
  have h := q7ConjPow_diagOpC 1 a₇
  rwa [pow_one] at h

/-- The moved entry, exhibited: at site `0` the permuted diagonal
carries `a₇ 1 = -3`, not `a₇ 0 = 3`. -/
theorem a₇_moved_entry : a₇ (q7ShiftCyc 0) ≠ a₇ 0 := by
  rw [q7ShiftCyc_apply]
  norm_num [a₇]

/-- The seven entries of `a₇` are pairwise distinct (T1): the
clock diagonal has no repeated entry, so no nontrivial cyclic
permutation of it can fix it. -/
theorem a₇_injective : Function.Injective a₇ := by
  intro i j h
  fin_cases i <;> fin_cases j <;> (try rfl) <;> norm_num [a₇] at h

/-- **THE NON-SYMMETRY COROLLARY (T1), at full rank.** The
generator's conjugation does NOT fix the instantiated package:
`S₇ D₇ S₇⁻¹ ≠ D₇`. The deciding entry is site `0`, moved from
`3` to `-3` (`a₇_moved_entry`). A finding about the instantiated
package, not a defect of the action or of the object. Together
with `q7ConjPow_diagOpC` this settles the registered decision:
the verdict is (ii) orbit covariance, not (i) symmetry. -/
theorem factorQ7_not_symm : q7ConjPow 1 factorQ7.D ≠ factorQ7.D := by
  intro h
  rw [q7Conj_one_factorQ7_D, factorQ7_D] at h
  have h0 := congrFun (LinearMap.congr_fun h (fun _ => (1 : ℂ))) 0
  rw [diagOpC_apply, diagOpC_apply] at h0
  simp only [mul_one] at h0
  have hval : ((a₇ ∘ ⇑q7ShiftCyc) 0 : ℂ) = -3 := by
    show ((a₇ (q7ShiftCyc 0) : ℝ) : ℂ) = -3
    rw [q7ShiftCyc_apply]
    norm_num [a₇]
  rw [hval] at h0
  have hval0 : ((a₇ 0 : ℝ) : ℂ) = 3 := by norm_num [a₇]
  rw [hval0] at h0
  norm_num at h0

/-! ## Section 2b. The spectrum corollary: carried, as a multiset -/

/-- The diagonal spectrum as a multiset: the entries of `d`, with
multiplicity. -/
def diagSpectrum (d : Fin 7 → ℝ) : Multiset ℝ :=
  Finset.univ.val.map d

/-- A permutation of the register does not move the multiset of
diagonal entries: conjugation by `cyc₇^k` carries the spectrum of
`diagOpC d` to the spectrum of the permuted package, the same
multiset - the entries are permuted, none created or destroyed. -/
theorem q7ConjPow_diagSpectrum (k : ℕ) (d : Fin 7 → ℝ) :
    diagSpectrum (d ∘ ⇑(q7ShiftCyc ^ k)) = diagSpectrum d := by
  have hmap : Multiset.map (⇑(q7ShiftCyc ^ k)) Finset.univ.val
      = Finset.univ.val := by
    have h := Finset.univ_map_embedding (α := Fin 7)
      (Equiv.toEmbedding (q7ShiftCyc ^ k))
    have h2 := congrArg Finset.val h
    rw [Finset.map_val] at h2
    exact h2
  unfold diagSpectrum
  rw [← Multiset.map_map, hmap]

/-- The instantiated spectrum corollary: the permuted package
`diagOpC (a₇ ∘ cyc₇)` has exactly `a₇`'s spectrum as a multiset.
What is preserved: the multiset of entries (hence every symmetric
reading of it). What is moved: which site carries which entry -
site `0` carries `-3` after conjugation, not `3`. -/
theorem factorQ7_spectrum_carried :
    diagSpectrum (a₇ ∘ ⇑q7ShiftCyc) = diagSpectrum a₇ := by
  have h := q7ConjPow_diagSpectrum 1 a₇
  rwa [pow_one] at h

/-! ## Section 3. The charge clause: the C4 grading is a spectator -/

/-- The composite Q⁷ action: the supplied action lifted
factorwise, `U₇ ⊗ 1 ⊗ 1` in the corpus's registered form
`opTensorQ q7ShiftR 1 1`. -/
noncomputable def actQ7Comp : Module.End ℝ q7c4r4Composite :=
  opTensorQ q7ShiftR 1 1

/-- The composite Q⁷ action on pure tensors: it moves only the
Q⁷ factor. -/
theorem actQ7Comp_tmul (x : Fin 7 → ℂ) (y : Fin 4 → ℂ)
    (z : Minkowski) :
    actQ7Comp ((x ⊗ₜ[ℝ] y) ⊗ₜ[ℝ] z)
      = ((q7ShiftR x ⊗ₜ[ℝ] y) ⊗ₜ[ℝ] z) := by
  unfold actQ7Comp
  rw [opTensorQ_tmul]
  simp [Module.End.one_apply]

/-- The composite Q⁷ action commutes with the composite charge
operator: both products are `opTensorQ q7ShiftR chargeC4 1`,
because the two operators act on different tensor factors. -/
theorem chargeComp_mul_actQ7Comp :
    chargeComp * actQ7Comp = actQ7Comp * chargeComp := by
  unfold chargeComp actQ7Comp
  rw [← opTensorQ_mul, ← opTensorQ_mul]
  simp

/-- **THE CHARGE CLAUSE (T1), proved at the composite level.**
The factorwise Q⁷ action preserves every `sectorComp j`: the
C⁴ charge grading is a spectator of the Q⁷ action - inside each
charge sector (the sectors of the composite's grading clock) the
action acts without moving the charge reading. No seam: this
clause is proved, not stated at the factor level only. -/
theorem actQ7Comp_mem_sectorComp {j : Fin 4}
    {v : q7c4r4Composite} (hv : v ∈ sectorComp j) :
    actQ7Comp v ∈ sectorComp j := by
  rw [mem_sectorComp] at hv ⊢
  have hcomm : chargeComp (actQ7Comp v) = actQ7Comp (chargeComp v) := by
    have h := LinearMap.congr_fun chargeComp_mul_actQ7Comp v
    simpa [Module.End.mul_apply] using h
  rw [hcomm, hv, map_smul]

/-! ## Section 4. The partner package and composite transport -/

/-- The permuted clock diagonal: `a₇` read through the 7-cycle,
`a₇ ∘ cyc₇` - the defining data of the partner package that
conjugation by `S₇` carries `factorQ7` to. -/
def a₇Orbit : Fin 7 → ℝ := a₇ ∘ ⇑q7ShiftCyc

/-- The partner grading permutation: the conjugate of the
pairing permutation `p₇` by the 7-cycle,
`cyc₇⁻¹ ∘ p₇ ∘ cyc₇` as a function. -/
def p₇Orbit : Fin 7 → Fin 7 :=
  fun k => (q7ShiftCyc⁻¹) (p₇ (q7ShiftCyc k))

/-- The partner pairing law: `a₇Orbit (p₇Orbit k) = - a₇Orbit k`,
by transport of `a₇_anti` through the conjugation. -/
theorem a₇Orbit_anti : ∀ k, a₇Orbit (p₇Orbit k) = - a₇Orbit k := by
  intro k
  show a₇ (q7ShiftCyc ((q7ShiftCyc⁻¹) (p₇ (q7ShiftCyc k))))
      = - a₇ (q7ShiftCyc k)
  rw [show q7ShiftCyc ((q7ShiftCyc⁻¹) (p₇ (q7ShiftCyc k)))
      = p₇ (q7ShiftCyc k) from Equiv.apply_symm_apply _ _]
  exact a₇_anti _

/-- The partner grading permutation is involutive, by transport
of `p₇_inv` through the conjugation. -/
theorem p₇Orbit_inv : ∀ k, p₇Orbit (p₇Orbit k) = k := by
  intro k
  show (q7ShiftCyc⁻¹) (p₇ (q7ShiftCyc
      ((q7ShiftCyc⁻¹) (p₇ (q7ShiftCyc k))))) = k
  rw [show q7ShiftCyc ((q7ShiftCyc⁻¹) (p₇ (q7ShiftCyc k)))
        = p₇ (q7ShiftCyc k) from Equiv.apply_symm_apply _ _,
    p₇_inv,
    show (q7ShiftCyc⁻¹) (q7ShiftCyc k) = k
      from Equiv.symm_apply_apply _ _]

/-- **The partner Q⁷ factor package**: the same diagonal-package
construction as `factorQ7`, at the conjugated data
`(a₇Orbit, p₇Orbit)`. This is the stated partner that the memo's
package-transport formula names. -/
def factorQ7Orbit : FactorOp 7 :=
  diagFactorOp a₇Orbit p₇Orbit a₇Orbit_anti p₇Orbit_inv

/-- The partner package's operator is the permuted diagonal. -/
theorem factorQ7Orbit_D : factorQ7Orbit.D = diagOpC a₇Orbit := rfl

/-- The partner package's grading is the conjugated pairing
permutation operator. -/
theorem factorQ7Orbit_γ : factorQ7Orbit.γ = permOpC p₇Orbit := rfl

/-- The instantiated package's grading, in its stated form. -/
theorem factorQ7_γ : factorQ7.γ = permOpC p₇ := rfl

/-- **The grading transport, in the stated form (T1).**
Conjugation by `S₇` carries the grading `γ₇ = permOpC p₇` to the
partner grading `permOpC p₇Orbit`: the grading transport does
not resist the stated form, so no seam opens here. -/
theorem q7Conj_one_gamma :
    q7ConjPow 1 factorQ7.γ = factorQ7Orbit.γ := by
  rw [factorQ7_γ, factorQ7Orbit_γ]
  apply LinearMap.ext
  intro x
  funext i
  show ((q7ShiftR ^ 1) * permOpC p₇ * q7ShiftPowInv 1) x i
      = permOpC p₇Orbit x i
  rw [Module.End.mul_apply, Module.End.mul_apply, q7ShiftPow_apply,
    permOpC_apply, q7ShiftPowInv_apply, permOpC_apply, pow_one]
  rfl

/-- Conjugation on one tensor factor, at the composite seat:
conjugating `opTensorQ X Y Z` by the factorwise action and its
stated inverse conjugates exactly the Q⁷ entry. -/
theorem actQ7Comp_conj_opTensorQ (X : Module.End ℝ (Fin 7 → ℂ))
    (Y : Module.End ℝ (Fin 4 → ℂ)) (Z : Module.End ℝ Minkowski) :
    actQ7Comp * opTensorQ X Y Z
        * opTensorQ (q7ShiftPowInv 1) 1 1
      = opTensorQ (q7ConjPow 1 X) Y Z := by
  unfold actQ7Comp q7ConjPow
  rw [← opTensorQ_mul, ← opTensorQ_mul]
  simp only [pow_one, one_mul, mul_one]

/-- **COMPOSITE PACKAGE TRANSPORT (T1), FULL.** Conjugation of
Q7CR-1b's instantiated composite Dirac by the factorwise action
`U₇ ⊗ 1 ⊗ 1` is exactly the stated partner package: the whole
instantiated pair `(D₇, γ₇)` is carried to
`(S₇ D₇ S₇⁻¹, S₇ γ₇ S₇⁻¹) = (factorQ7Orbit.D, factorQ7Orbit.γ)`,
i.e. `U diracInst U⁻¹ = diracQ7C4R4 factorQ7Orbit factorC4
factorR`, per the memo's formula
`D ↦ (S₇D₇S₇⁻¹) ⊗ 1 ⊗ 1 + (S₇γ₇S₇⁻¹) ⊗ D₄ ⊗ 1
+ (S₇γ₇S₇⁻¹)γ₄ ⊗ D_R`. No PARTIAL: the grading-transport seam
pre-authorized by the pack does not open - both entries of the
pair land in their stated conjugate forms. -/
theorem composite_package_transport :
    actQ7Comp * diracInst * opTensorQ (q7ShiftPowInv 1) 1 1
      = diracQ7C4R4 factorQ7Orbit factorC4 factorR := by
  have hD : q7ConjPow 1 factorQ7.D = factorQ7Orbit.D := by
    rw [q7Conj_one_factorQ7_D, factorQ7Orbit_D]
    rfl
  have hγ : q7ConjPow 1 factorQ7.γ = factorQ7Orbit.γ :=
    q7Conj_one_gamma
  show actQ7Comp * diracQ7C4R4 factorQ7 factorC4 factorR
      * opTensorQ (q7ShiftPowInv 1) 1 1 = _
  unfold diracQ7C4R4
  rw [mul_add, mul_add, add_mul, add_mul,
    actQ7Comp_conj_opTensorQ, actQ7Comp_conj_opTensorQ,
    actQ7Comp_conj_opTensorQ, hD, hγ]

/-! ## Section 5. The verdict, assembled -/

/-- **Q7CR-6c VERDICT (T1): (ii) ORBIT COVARIANCE.** Assembled
at full rank: (1) the family identity - conjugation by `S₇`
permutes the diagonal family by the cyclic permutation of its
parameters, instantiated at `a₇`; (2) the non-symmetry corollary
- the instantiated package is not fixed; (3) the spectrum
corollary - the diagonal spectrum is carried to itself as a
multiset; (4) the charge clause - every composite charge sector
is preserved by the factorwise action; (5) composite package
transport - the instantiated composite Dirac is carried to the
stated partner package. K-Q7CR-6b is DISARMED by (1), (3) and
(4): the action is visible, as an orbit action. The standing
sentence stands verbatim on this module's face: "via C4"
survives only as "graded by C4." -/
theorem q7cr6c_verdict :
    q7ConjPow 1 factorQ7.D = diagOpC (a₇ ∘ ⇑q7ShiftCyc)
      ∧ q7ConjPow 1 factorQ7.D ≠ factorQ7.D
      ∧ diagSpectrum (a₇ ∘ ⇑q7ShiftCyc) = diagSpectrum a₇
      ∧ (∀ (j : Fin 4) (v : q7c4r4Composite), v ∈ sectorComp j →
          actQ7Comp v ∈ sectorComp j)
      ∧ actQ7Comp * diracInst * opTensorQ (q7ShiftPowInv 1) 1 1
          = diracQ7C4R4 factorQ7Orbit factorC4 factorR :=
  ⟨q7Conj_one_factorQ7_D, factorQ7_not_symm,
    factorQ7_spectrum_carried,
    (by intro j v hv; exact actQ7Comp_mem_sectorComp hv),
    composite_package_transport⟩

end ThetLogos

#print axioms ThetLogos.q7ConjPow_diagOpC
#print axioms ThetLogos.factorQ7_not_symm
#print axioms ThetLogos.q7ConjPow_diagSpectrum
#print axioms ThetLogos.actQ7Comp_mem_sectorComp
#print axioms ThetLogos.composite_package_transport
#print axioms ThetLogos.q7cr6c_verdict
