import Mathlib.Tactic
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import ThetLogos.Q7C4R4Spectrum

/-!
# ThetLogos.Q7C4R4Charge — the charge grading on the Q⁷C⁴R⁴
composite and the separation test (Q7CR-3)

**Status: T1 test brick at Q7CR-2's instantiated seat.
NO CLAIM. Dials 0/4. No measured number is claimed by this line.**

Governing scoping: `scoping-q7c4r4-gauntlet-2026-10-30.md` §3
(Q7CR-3, tests gauntlet Item 2 and the first half of Item 7),
pack `pack-q7cr-3.md`. Gates consumed, not re-chosen:
Q7CR-1b (`Q7C4R4Assembly`: `diracQ7C4R4`, `diracQ7C4R4_sq`) and
Q7CR-2 (`Q7C4R4Spectrum`: the instantiated packages `factorQ7`,
`factorC4`, `factorR`, the eigenvalue functions `s₇/s₄/s_R`,
`spectrumQ7CR2`, the composite eigenbasis `basisComp` with
`dirac_sq_basisComp_eig`).

## What this brick states and tests

**The charge grading (§§1–2).** The charge side of the composite
is the C⁴ factor. Its character decomposition is the eigenspace
decomposition of the cyclic shift on `Fin 4 → ℂ`: the four
character vectors `fourierC4 j` (the functions `k ↦ (i^j)^k`,
i.e. the characters of `ZMod 4` read on sites; the pin's
Pontryagin identification `AddChar.zmodAddEquiv` at `n = 4` is
registered in §1, cited, not rebuilt). The **charge operator**
`chargeC4` is the real form of the character grading: the
ℝ-linear operator on the realified C⁴ factor with
`chargeC4 (fourierC4 j) = j • fourierC4 j`, given explicitly as a
polynomial in the shift with complex coefficients (§2). Its
**sectors** are its four eigenspaces `sectorC4 j` (real
submodules). The composite charge operator is
`chargeComp = 1 ⊗ chargeC4 ⊗ 1` on the registered composite,
with sectors `sectorComp j`.

**The separation criterion, stated exactly (§5).** The charge
sectors are *spectrally resolved by `D`* at the instantiated
seat — separated — iff (C1) every composite sector is invariant
under `D²` (the registered spectral operator of Q7CR-2), and
(C2) the `D²`-eigenvalues realized in distinct sectors are
disjoint. Stated as the `Prop` `ChargeSpectrallyResolved`.

**The test (§§3–5).** The criterion FAILS — clause (C1) is
falsified outright at the composite seat, and the spectral
half is obstructed already in the charge factor:

- The C⁴ factor's sectors contain **no `D₄²`-eigenvector at
  all**: no nonzero `y` with `chargeC4 y = j • y` is an
  eigenvector of `factorC4.D ^ 2`, for any `j` and any
  eigenvalue (§3). The charge factor's own spectral data does
  not read the charge sectors — there is no spectral reading
  to be disjoint.
- At the composite seat, `D` and `D²` both **mix** the
  sectors: the sector-`0` vector `v₀` (a pure tensor built from
  `fourierC4 0`) is carried by both `D` and `D²` out of
  sector `0` (§4); equivalently `chargeComp` commutes with
  neither `D` nor `D²`. So (C1) fails outright and
  `ChargeSpectrallyResolved` is false.

## Kill K-Q7CR-3 — evaluated on the face: FIRES, in the stated form

The stated character grading does not commute trivially with
`D` (it is genuinely mixed, §4), and it is mixed **with no
invariant spectral reading**: the sectors are not `D²`-invariant
and the charge factor's sectors carry no `D₄²`-eigenvectors at
all. By the pre-registered kill, "charge separation" **dies in
the stated form** at full rank: the four character sectors of
the C⁴ character grading, at Q7CR-2's instantiated seat, are
not separated by the registered operators. What survives is
narrow and is reported narrowly: the grading itself, its four
sectors as submodules, and the exact mixing/non-eigenvector
facts above — sector/spectrum facts about this instantiated
operator, **never a mechanism claim**. Any other weighting of
the characters (coarsened sectors) is a different stated form
and would enter as a new entry under the relabeling rule. The
object ℝ⁴⁴⁸ and its landed spectrum are untouched.

## Relations and fences

- The SEP line's composite form is deferred to this brick;
  SEP's miniature (`Qsep` at the Z4 seat) is a separate,
  smaller object — not conflated, and no SEP/PUMP language is
  imported into this brick's claims.
- The Connes-distance second half of Item 7 **queues behind
  Q7CR-4** (no algebra action has landed): nothing about it is
  stated here beyond this deferral note.
- Bounded-commutator caveat: in finite dimension that
  criterion is vacuous; the testable content here is spectrum,
  grading behavior, and the `D²` identity.
- "No measured number is claimed by this line." No entropy
  language. NO CLAIM; dials 0/4.
-/

namespace ThetLogos

open TensorProduct

/-! ## §1. The C⁴ character side: pin, shift, character vectors -/

/-- **The Pontryagin side, cited as a registration (T1
registration).** The pin's `AddChar.zmodAddEquiv` at `n = 4`:
the dual group of `ZMod 4` is `ZMod 4` itself. Cited from the
pin — not rebuilt — exactly as Q7CR-0 cites the same theorem
for C⁴ and `Q7C4R4Linker` registers it at `n = 7`. -/
noncomputable def c4Pontryagin : ZMod 4 ≃+ AddChar (ZMod 4) ℂ :=
  AddChar.zmodAddEquiv (n := 4)

/-- **The C⁴ cyclic shift permutation (CHOSEN form):**
`k ↦ k + 1` on the four sites, as a literal permutation. The
character decomposition of the C⁴ factor is the eigenspace
decomposition of this shift. -/
def c4ShiftPerm : Fin 4 → Fin 4 := ![1, 2, 3, 0]

/-- **The C⁴ cyclic shift**, as an ℝ-linear operator on the
realified C⁴ factor (the permutation operator of `c4ShiftPerm`,
via Q7CR-2's `permOpC`). -/
def shiftC4 : (Fin 4 → ℂ) →ₗ[ℝ] (Fin 4 → ℂ) := permOpC c4ShiftPerm

/-- The shift, pointwise: `(shiftC4 x) k = x (k + 1)`. -/
theorem shiftC4_apply (x : Fin 4 → ℂ) (k : Fin 4) :
    shiftC4 x k = x (c4ShiftPerm k) :=
  permOpC_apply c4ShiftPerm x k

/-- **The four character vectors of the C⁴ factor:**
`fourierC4 j` is the function `k ↦ (i^j)^k` on sites — the
`j`-th character of `ZMod 4`, read in the site basis:
`fourierC4 0 = (1, 1, 1, 1)`, `fourierC4 1 = (1, i, -1, -i)`,
`fourierC4 2 = (1, -1, 1, -1)`, `fourierC4 3 = (1, -i, -1, i)`. -/
def fourierC4 : Fin 4 → (Fin 4 → ℂ) :=
  ![![1, 1, 1, 1], ![1, Complex.I, -1, -Complex.I],
    ![1, -1, 1, -1], ![1, -Complex.I, -1, Complex.I]]

/-- Every character vector is nonzero (its value at site `0`
is `1`). -/
theorem fourierC4_ne_zero (j : Fin 4) : fourierC4 j ≠ 0 := by
  intro h
  have h0 : fourierC4 j 0 = 0 := by rw [h]; rfl
  fin_cases j <;> simp [fourierC4] at h0

/-- The shift commutes with complex scalar multiplication
(it is the realification of a ℂ-linear map). -/
theorem shiftC4_complex_smul (c : ℂ) (x : Fin 4 → ℂ) :
    shiftC4 (c • x) = c • shiftC4 x := by
  funext k
  simp [shiftC4_apply, Pi.smul_apply, smul_eq_mul]

/-- **The character vectors are shift eigenvectors:** the
`j`-th character vector has shift eigenvalue `i^j`. This is
the character decomposition of the C⁴ factor, in the site
basis. -/
theorem shiftC4_fourierC4 (j : Fin 4) :
    shiftC4 (fourierC4 j) = (Complex.I ^ (j.val)) • fourierC4 j := by
  funext k
  fin_cases j <;> fin_cases k <;>
    simp [shiftC4_apply, c4ShiftPerm, fourierC4, Pi.smul_apply,
      smul_eq_mul, Complex.I_mul_I]

/-- Powers of the shift, pointwise: `(shiftC4 ^ t) x k =
x (p ^[t] k)`, the `t`-fold iterate of the shift permutation. -/
theorem shiftC4_pow_apply (t : ℕ) (x : Fin 4 → ℂ) (k : Fin 4) :
    (shiftC4 ^ t) x k = x (c4ShiftPerm^[t] k) := by
  induction t generalizing x k with
  | zero => simp
  | succ t ih =>
    rw [pow_succ, Module.End.mul_apply, ih, shiftC4_apply,
      Function.iterate_succ_apply']

/-- Powers of the shift commute with complex scalar
multiplication. -/
theorem shiftC4_pow_complex_smul (t : ℕ) (c : ℂ) (x : Fin 4 → ℂ) :
    (shiftC4 ^ t) (c • x) = c • (shiftC4 ^ t) x := by
  funext k
  rw [shiftC4_pow_apply]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [shiftC4_pow_apply]

/-- Powers of the shift act on character vectors by the power
of the character value. -/
theorem shiftC4_pow_fourierC4 (j : Fin 4) (t : ℕ) :
    (shiftC4 ^ t) (fourierC4 j)
      = ((Complex.I ^ (j.val)) ^ t) • fourierC4 j := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [pow_succ, Module.End.mul_apply, shiftC4_fourierC4,
      shiftC4_pow_complex_smul, ih, smul_smul, ← pow_succ']

/-! ## §2. The charge operator on the C⁴ factor

The charge operator is the real form of the character
grading: the operator whose eigenvalue on the `j`-th
character line is the charge `j ∈ {0, 1, 2, 3}`. It is a
polynomial in the shift with complex coefficients,
`chargeC4 = (3/2)•1 + ((-1+i)/2)•S + (-1/2)•S² + ((-1-i)/2)•S³`
(the Lagrange-interpolation polynomial of `j ↦ i^j` read
backwards: `∑ₜ cₜ ζ^{jt} = j` for `ζ = i`, each `j`), where
`c • A` for a complex `c` is pointwise multiplication by `c`
composed with `A`. -/

/-- Pointwise multiplication by a complex constant, as an
ℝ-linear operator on the realified factor. -/
def csmulC {n : ℕ} (c : ℂ) : (Fin n → ℂ) →ₗ[ℝ] (Fin n → ℂ) where
  toFun := fun x k => c * x k
  map_add' := fun x y => by
    funext k
    simp [mul_add]
  map_smul' := fun r x => by
    funext k
    show c * ((r : ℂ) * x k) = (r : ℂ) * (c * x k)
    ring

/-- Pointwise formula for `csmulC`. -/
theorem csmulC_apply {n : ℕ} (c : ℂ) (x : Fin n → ℂ) (k : Fin n) :
    csmulC c x k = c * x k :=
  rfl

/-- **The charge operator on the C⁴ factor** (the real form
of the C⁴ character grading): the polynomial
`(3/2)•1 + ((-1+i)/2)•S + (-1/2)•S² + ((-1-i)/2)•S³` in the
cyclic shift `S = shiftC4`, with `•` pointwise complex
multiplication. Stated content of this brick: this real
operator grades the realified composite by charge (§4). -/
noncomputable def chargeC4 : (Fin 4 → ℂ) →ₗ[ℝ] (Fin 4 → ℂ) :=
  csmulC (3 / 2) + csmulC ((-1 + Complex.I) / 2) ∘ₗ (shiftC4 ^ 1)
    + csmulC (-1 / 2) ∘ₗ (shiftC4 ^ 2)
    + csmulC ((-1 - Complex.I) / 2) ∘ₗ (shiftC4 ^ 3)

/-- The charge operator, pointwise: at site `k` it reads the
four sites `k, k+1, k+2, k+3` (cyclically) with the stated
complex weights. -/
theorem chargeC4_apply (x : Fin 4 → ℂ) (k : Fin 4) :
    chargeC4 x k = (3 / 2) * x k
      + ((-1 + Complex.I) / 2) * x (c4ShiftPerm k)
      + (-1 / 2) * x (c4ShiftPerm (c4ShiftPerm k))
      + ((-1 - Complex.I) / 2)
        * x (c4ShiftPerm (c4ShiftPerm (c4ShiftPerm k))) := by
  have h1 : (shiftC4 ^ 1) x k = x (c4ShiftPerm k) := by
    rw [shiftC4_pow_apply]
    rfl
  have h2 : (shiftC4 ^ 2) x k = x (c4ShiftPerm (c4ShiftPerm k)) := by
    rw [shiftC4_pow_apply]
    rfl
  have h3 : (shiftC4 ^ 3) x k
      = x (c4ShiftPerm (c4ShiftPerm (c4ShiftPerm k))) := by
    rw [shiftC4_pow_apply]
    rfl
  simp only [chargeC4, LinearMap.add_apply, LinearMap.comp_apply,
    Pi.add_apply, csmulC_apply, h1, h2, h3]

/-- **The charge operator grades the characters:** the
`j`-th character vector is a `chargeC4`-eigenvector with
eigenvalue the charge `j` (as a complex scalar). The four
scalar identities `∑ₜ cₜ (i^j)^t = j` are the finite checks
at the end of the proof. -/
theorem chargeC4_fourierC4 (j : Fin 4) :
    chargeC4 (fourierC4 j) = (j.val : ℂ) • fourierC4 j := by
  have hterm : ∀ (c : ℂ) (t : ℕ),
      (csmulC c ∘ₗ (shiftC4 ^ t)) (fourierC4 j)
        = (c * (Complex.I ^ (j.val)) ^ t) • fourierC4 j := by
    intro c t
    rw [LinearMap.comp_apply, shiftC4_pow_fourierC4]
    funext k
    simp only [csmulC_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have h0 : csmulC (3 / 2 : ℂ) (fourierC4 j)
      = ((3 / 2 : ℂ) * (Complex.I ^ (j.val)) ^ 0) • fourierC4 j := by
    funext k
    simp only [csmulC_apply, Pi.smul_apply, smul_eq_mul]
    ring
  unfold chargeC4
  rw [LinearMap.add_apply, LinearMap.add_apply, LinearMap.add_apply,
    h0, hterm, hterm, hterm, ← add_smul, ← add_smul, ← add_smul]
  congr 1
  fin_cases j <;>
    norm_num [Complex.ext_iff, Complex.I_mul_I, pow_succ]

/-- The charge eigenvalue, in real form: the `j`-th character
vector is an eigenvector of `chargeC4` for the **real**
scalar `j`. -/
theorem chargeC4_fourierC4_real (j : Fin 4) :
    chargeC4 (fourierC4 j) = (j.val : ℝ) • fourierC4 j := by
  rw [chargeC4_fourierC4]
  funext k
  simp [Pi.smul_apply, Complex.real_smul, smul_eq_mul]

/-! ## §3. The C⁴ charge sectors and the factor-level test -/

/-- The shift permutation on literal sites. -/
theorem c4ShiftPerm_zero : c4ShiftPerm 0 = 1 := by simp [c4ShiftPerm]

/-- The shift permutation on literal sites. -/
theorem c4ShiftPerm_one : c4ShiftPerm 1 = 2 := by simp [c4ShiftPerm]

/-- The shift permutation on literal sites. -/
theorem c4ShiftPerm_two : c4ShiftPerm 2 = 3 := by simp [c4ShiftPerm]

/-- The shift permutation on literal sites. -/
theorem c4ShiftPerm_three : c4ShiftPerm 3 = 0 := by simp [c4ShiftPerm]

/-- Eigenspaces of one operator for two distinct real
eigenvalues meet only at `0`. -/
theorem ker_sub_smul_one_disjoint {V : Type*} [AddCommGroup V]
    [Module ℝ V] (A : Module.End ℝ V) {a b : ℝ} (hab : a ≠ b) :
    Disjoint (LinearMap.ker (A - a • 1)) (LinearMap.ker (A - b • 1)) := by
  rw [Submodule.disjoint_def]
  intro x hxa hxb
  rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    Module.End.one_apply, sub_eq_zero] at hxa hxb
  have hsub : (a - b) • x = 0 := by
    rw [sub_smul, ← hxa, ← hxb, sub_self]
  have hx : x = 0 := by
    rcases smul_eq_zero.mp hsub with h | h
    · exact absurd (sub_eq_zero.mp h) hab
    · exact h
  rw [hx]

/-- **The `j`-th charge sector of the C⁴ factor**: the
`chargeC4`-eigenspace for the real eigenvalue `j`, as a real
submodule of the realified factor. The four sectors are the
sectors of the composite's charge grading (§4). -/
noncomputable def sectorC4 (j : Fin 4) : Submodule ℝ (Fin 4 → ℂ) :=
  LinearMap.ker (chargeC4 - (j.val : ℝ) • 1)

/-- Membership in a charge sector is the eigen equation. -/
theorem mem_sectorC4 {j : Fin 4} {y : Fin 4 → ℂ} :
    y ∈ sectorC4 j ↔ chargeC4 y = (j.val : ℝ) • y := by
  rw [sectorC4, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero]

/-- The `j`-th character vector lies in the `j`-th sector. -/
theorem fourierC4_mem_sectorC4 (j : Fin 4) :
    fourierC4 j ∈ sectorC4 j :=
  mem_sectorC4.mpr (chargeC4_fourierC4_real j)

/-- Distinct charge sectors are disjoint submodules. -/
theorem sectorC4_disjoint {j j' : Fin 4} (h : j ≠ j') :
    Disjoint (sectorC4 j) (sectorC4 j') := by
  apply ker_sub_smul_one_disjoint chargeC4
  intro hjj
  apply h
  have hval : j.val = j'.val := by exact_mod_cast hjj
  exact Fin.ext hval

/-- From the `D₄²`-eigen equation at a site whose
factor-square value differs from `μ`, the vector vanishes
at that site. -/
theorem factor_eig_zero_of_ne {y : Fin 4 → ℂ} {μ : ℝ} {k : Fin 4}
    (hD : (factorC4.D ^ 2) y = μ • y) (hk : d₄ k ^ 2 ≠ μ) :
    y k = 0 := by
  have h := congrFun hD k
  rw [factorC4_D_sq_apply, Pi.smul_apply, Complex.real_smul] at h
  have hne : (((d₄ k) ^ 2 : ℂ) - (μ : ℂ)) ≠ 0 := by
    rw [sub_ne_zero]
    have hk' : ((d₄ k ^ 2 : ℝ) : ℂ) ≠ (μ : ℂ) := by exact_mod_cast hk
    push_cast at hk'
    exact hk'
  have hzero : (((d₄ k) ^ 2 : ℂ) - (μ : ℂ)) * y k = 0 := by
    rw [sub_mul, h, sub_self]
  exact (mul_eq_zero.mp hzero).resolve_left hne

/-- **The factor-level spectral test: the charge sectors of
the C⁴ factor contain no `D₄²`-eigenvector at all.** If `y`
lies in a charge sector (`chargeC4 y = j • y`, any `j`) and
is an eigenvector of the instantiated `D₄²` (any real
eigenvalue `μ`), then `y = 0`. The proof is the site
computation: a `D₄²`-eigenvector is supported on one level
set of `d₄²` (`{0, 3}` for `9/64`, `{1, 2}` for `1/64`,
empty otherwise), and the charge equation at the two
vanishing sites then forces the remaining two sites to
vanish as well, for every `j`. -/
theorem factor_sector_no_eigenvector (j : Fin 4) (μ : ℝ)
    (y : Fin 4 → ℂ) (hQ : chargeC4 y = (j.val : ℝ) • y)
    (hD : (factorC4.D ^ 2) y = μ • y) : y = 0 := by
  have hQk : ∀ k : Fin 4, (3 / 2) * y k
      + ((-1 + Complex.I) / 2) * y (c4ShiftPerm k)
      + (-1 / 2) * y (c4ShiftPerm (c4ShiftPerm k))
      + ((-1 - Complex.I) / 2)
        * y (c4ShiftPerm (c4ShiftPerm (c4ShiftPerm k)))
      = ((j.val : ℝ) : ℂ) * y k := by
    intro k
    have h := congrFun hQ k
    rw [chargeC4_apply] at h
    exact h
  have hd : ∀ k : Fin 4, d₄ k ^ 2 = 9 / 64 ∨ d₄ k ^ 2 = 1 / 64 := by
    intro k
    fin_cases k <;> norm_num [d₄, z4Energy]
  by_cases h9 : μ = 9 / 64
  · subst h9
    have hy1 : y 1 = 0 :=
      factor_eig_zero_of_ne hD (by norm_num [d₄, z4Energy])
    have hy2 : y 2 = 0 :=
      factor_eig_zero_of_ne hD (by norm_num [d₄, z4Energy])
    have e1 := hQk 1
    rw [c4ShiftPerm_one, c4ShiftPerm_two, c4ShiftPerm_three] at e1
    simp only [hy1, hy2, mul_zero, add_zero, zero_add] at e1
    have hy3 : y 3 = -(1 + Complex.I) * y 0 := by
      linear_combination -2 * e1
    have e2 := hQk 2
    rw [c4ShiftPerm_two, c4ShiftPerm_three, c4ShiftPerm_zero] at e2
    simp only [hy1, hy2, mul_zero, add_zero, zero_add] at e2
    rw [hy3] at e2
    have hcoef : (((-1 + Complex.I) / 2) * (-(1 + Complex.I))
        + (-1 / 2)) * y 0 = 0 := by linear_combination e2
    have hhalf : ((-1 + Complex.I) / 2) * (-(1 + Complex.I))
        + (-1 / 2) = (1 / 2 : ℂ) := by
      norm_num [Complex.ext_iff, Complex.I_mul_I]
    rw [hhalf] at hcoef
    have hy0 : y 0 = 0 :=
      (mul_eq_zero.mp hcoef).resolve_left (by norm_num)
    rw [hy0] at hy3
    simp only [mul_zero] at hy3
    funext k
    fin_cases k <;> simp [hy0, hy1, hy2, hy3]
  · by_cases h1 : μ = 1 / 64
    · subst h1
      have hy0 : y 0 = 0 :=
        factor_eig_zero_of_ne hD (by norm_num [d₄, z4Energy])
      have hy3 : y 3 = 0 :=
        factor_eig_zero_of_ne hD (by norm_num [d₄, z4Energy])
      have e0 := hQk 0
      rw [c4ShiftPerm_zero, c4ShiftPerm_one, c4ShiftPerm_two] at e0
      simp only [hy0, hy3, mul_zero, add_zero, zero_add] at e0
      have hy2 : y 2 = (-1 + Complex.I) * y 1 := by
        linear_combination -2 * e0
      have e3 := hQk 3
      rw [c4ShiftPerm_three, c4ShiftPerm_zero, c4ShiftPerm_one] at e3
      simp only [hy0, hy3, mul_zero, add_zero, zero_add] at e3
      rw [hy2] at e3
      have hcoef : (((-1 - Complex.I) / 2) * (-1 + Complex.I)
          + (-1 / 2)) * y 1 = 0 := by linear_combination e3
      have hhalf : ((-1 - Complex.I) / 2) * (-1 + Complex.I)
          + (-1 / 2) = (1 / 2 : ℂ) := by
        norm_num [Complex.ext_iff, Complex.I_mul_I]
      rw [hhalf] at hcoef
      have hy1 : y 1 = 0 :=
        (mul_eq_zero.mp hcoef).resolve_left (by norm_num)
      rw [hy1] at hy2
      simp only [mul_zero] at hy2
      funext k
      fin_cases k <;> simp [hy0, hy1, hy2, hy3]
    · have hy : ∀ k : Fin 4, y k = 0 := by
        intro k
        apply factor_eig_zero_of_ne hD
        rcases hd k with hh | hh
        · rw [hh]; exact fun h => h9 h.symm
        · rw [hh]; exact fun h => h1 h.symm
      funext k
      simp [hy k]

/-- The charge of `D₄² (fourierC4 0)` at site `0` is the
explicit nonzero value `(2 - i) / 16`: `D₄²` carries the
sector-`0` character vector out of sector `0`. -/
theorem chargeC4_factorD_sq_fourierC4_zero_apply :
    chargeC4 ((factorC4.D ^ 2) (fourierC4 0)) 0
      = (2 - Complex.I) / 16 := by
  rw [chargeC4_apply, c4ShiftPerm_zero, c4ShiftPerm_one,
    c4ShiftPerm_two]
  simp only [factorC4_D_sq_apply]
  norm_num [fourierC4, d₄, z4Energy, Complex.ext_iff, Complex.I_mul_I]

/-- **Factor-level non-preservation:** `D₄²` does not
preserve the `0`-th charge sector — the sector's own
character vector is carried out of it. -/
theorem factorD_sq_fourierC4_zero_not_mem :
    (factorC4.D ^ 2) (fourierC4 0) ∉ sectorC4 0 := by
  rw [mem_sectorC4]
  intro h
  have h0 := chargeC4_factorD_sq_fourierC4_zero_apply
  rw [h] at h0
  norm_num [Complex.ext_iff] at h0

/-! ## §4. The composite charge grading and the mixing test -/

/-- The `0`-th character vector is the constant `1` function. -/
theorem fourierC4_zero_apply (k : Fin 4) : fourierC4 0 k = 1 := by
  fin_cases k <;> simp [fourierC4]

/-- **The instantiated composite Dirac** (Q7CR-2's seat):
`diracQ7C4R4` at the instantiated factor packages. -/
noncomputable def diracInst :
    q7c4r4Composite →ₗ[ℝ] q7c4r4Composite :=
  diracQ7C4R4 factorQ7 factorC4 factorR

/-- **The composite charge operator**: `1 ⊗ chargeC4 ⊗ 1` on
the registered composite — the C⁴ character grading of §2,
tensored with identities on the Q⁷ and R⁴ factors. -/
noncomputable def chargeComp :
    q7c4r4Composite →ₗ[ℝ] q7c4r4Composite :=
  opTensorQ 1 chargeC4 1

/-- The composite charge operator on pure tensors. -/
theorem chargeComp_tmul (x : Fin 7 → ℂ) (y : Fin 4 → ℂ)
    (z : Minkowski) :
    chargeComp ((x ⊗ₜ[ℝ] y) ⊗ₜ[ℝ] z)
      = (x ⊗ₜ[ℝ] chargeC4 y) ⊗ₜ[ℝ] z := by
  unfold chargeComp
  rw [opTensorQ_tmul]
  simp [Module.End.one_apply]

/-- The difference map `chargeComp - j • id`, built pointwise
(subtraction of linear maps *into the composite* is not an
instance in this Mathlib pin; subtraction of composite
vectors is). -/
noncomputable def chargeCompSub (j : Fin 4) :
    q7c4r4Composite →ₗ[ℝ] q7c4r4Composite where
  toFun := fun v => chargeComp v - (j.val : ℝ) • v
  map_add' := fun v w => by
    simp only [map_add, smul_add]
    abel
  map_smul' := fun r v => by
    simp [map_smul, smul_sub, smul_smul, mul_comm]

/-- Pointwise formula for the difference map. -/
theorem chargeCompSub_apply (j : Fin 4) (v : q7c4r4Composite) :
    chargeCompSub j v = chargeComp v - (j.val : ℝ) • v :=
  rfl

/-- **The `j`-th charge sector of the composite**: the
`chargeComp`-eigenspace for the real eigenvalue `j`. -/
noncomputable def sectorComp (j : Fin 4) :
    Submodule ℝ q7c4r4Composite :=
  LinearMap.ker (chargeCompSub j)

/-- Membership in a composite charge sector is the eigen
equation. -/
theorem mem_sectorComp {j : Fin 4} {v : q7c4r4Composite} :
    v ∈ sectorComp j ↔ chargeComp v = (j.val : ℝ) • v := by
  rw [sectorComp, LinearMap.mem_ker, chargeCompSub_apply,
    sub_eq_zero]

/-- Distinct composite charge sectors are disjoint. -/
theorem sectorComp_disjoint {j j' : Fin 4} (h : j ≠ j') :
    Disjoint (sectorComp j) (sectorComp j') := by
  rw [Submodule.disjoint_def]
  intro x hx hx'
  rw [mem_sectorComp] at hx hx'
  have hsub : ((j.val : ℝ) - (j'.val : ℝ)) • x = 0 := by
    have e : ((j.val : ℝ) - (j'.val : ℝ)) • x
        = (j.val : ℝ) • x - (j'.val : ℝ) • x := by
      convert sub_smul (j.val : ℝ) (j'.val : ℝ) x using 1
    rw [e, ← hx, ← hx', sub_self]
  have hx0 : x = 0 := by
    rcases smul_eq_zero.mp hsub with hh | hh
    · exfalso
      apply h
      have hval : j.val = j'.val := by
        have := sub_eq_zero.mp hh
        exact_mod_cast this
      exact Fin.ext hval
    · exact hh
  exact (Submodule.mem_bot ℝ).mpr hx0

/-- The C⁴ grading fixes the `0`-th character vector
(reversal of the constant vector). -/
theorem factorC4_gamma_fourierC4_zero :
    factorC4.γ (fourierC4 0) = fourierC4 0 := by
  funext k
  show permOpC p₄ (fourierC4 0) k = fourierC4 0 k
  rw [permOpC_apply]
  fin_cases k <;> simp [p₄, fourierC4]

/-- The Q⁷ grading carries the site-`0` real basis vector to
the site-`1` one (the grading permutation swaps `0, 1`). -/
theorem factorQ7_gamma_basisC_zero :
    factorQ7.γ (basisC 7 (0, 0)) = basisC 7 (1, 0) := by
  funext j
  show permOpC p₇ (basisC 7 (0, 0)) j = basisC 7 (1, 0) j
  rw [permOpC_apply, basisC_apply, basisC_apply]
  fin_cases j <;> simp [p₇]

/-! ### Contraction functionals

Pure tensors of nonzero factor vectors are detected by the
evaluation contractions below: `contractC s₇ s₄ sR` reads
the `(s₇, s₄, sR)` site values of the three factors and
multiplies them. -/

/-- The middle contraction: site values on the Q⁷ and C⁴
factors, multiplied. -/
noncomputable def contractMid (s₇ : Fin 7) (s₄ : Fin 4) :
    ((Fin 7 → ℂ) ⊗[ℝ] (Fin 4 → ℂ)) →ₗ[ℝ] ℂ :=
  TensorProduct.lift (LinearMap.mk₂ ℝ (fun x y => x s₇ * y s₄)
    (fun x x' y => by simp [Pi.add_apply, add_mul])
    (fun r x y => by
      simp only [Pi.smul_apply, Complex.real_smul]
      ring)
    (fun x y y' => by simp [Pi.add_apply, mul_add])
    (fun r x y => by
      simp only [Pi.smul_apply, Complex.real_smul]
      ring))

/-- **The evaluation contraction on the composite.** -/
noncomputable def contractC (s₇ : Fin 7) (s₄ : Fin 4) (sR : Fin 4) :
    q7c4r4Composite →ₗ[ℝ] ℂ :=
  TensorProduct.lift (LinearMap.mk₂ ℝ
    (fun w z => contractMid s₇ s₄ w * (z sR : ℂ))
    (fun w w' z => by simp [map_add, add_mul])
    (fun r w z => by
      simp only [map_smul, Complex.real_smul]
      ring)
    (fun w z z' => by
      simp [Pi.add_apply, Complex.ofReal_add, mul_add])
    (fun r w z => by
      simp only [Pi.smul_apply, Complex.ofReal_mul, Complex.real_smul,
        smul_eq_mul]
      ring))

/-- The contraction on pure tensors is the product of the
three site values. -/
theorem contractC_tmul (s₇ : Fin 7) (s₄ : Fin 4) (sR : Fin 4)
    (x : Fin 7 → ℂ) (y : Fin 4 → ℂ) (z : Minkowski) :
    contractC s₇ s₄ sR ((x ⊗ₜ[ℝ] y) ⊗ₜ[ℝ] z)
      = x s₇ * y s₄ * (z sR : ℂ) := by
  simp only [contractC, contractMid, TensorProduct.lift.tmul,
    LinearMap.mk₂_apply]

/-- **The sector-`0` test vector**: the pure tensor of the
Q⁷ site-`0` real basis vector, the `0`-th character vector,
and the R⁴ site-`0` basis vector. -/
noncomputable def v₀ : q7c4r4Composite :=
  ((basisC 7 (0, 0)) ⊗ₜ[ℝ] (fourierC4 0))
    ⊗ₜ[ℝ] ((Pi.basisFun ℝ (Fin 4)) 0)

/-- The test vector is nonzero (its `(0, 0, 0)` contraction
is `1`). -/
theorem v₀_ne_zero : v₀ ≠ 0 := by
  intro hv
  have h1 : contractC 0 0 0 v₀ = 1 := by
    rw [v₀, contractC_tmul]
    simp [basisC_apply, fourierC4, Pi.basisFun_apply]
  rw [hv, map_zero] at h1
  norm_num at h1

/-- The charge operator kills the test vector's charge:
`chargeComp v₀ = 0`, i.e. `v₀` lies in sector `0`. -/
theorem chargeComp_v₀ : chargeComp v₀ = 0 := by
  have h0 : chargeC4 (fourierC4 0) = 0 := by
    have h := chargeC4_fourierC4_real 0
    simpa using h
  rw [v₀, chargeComp_tmul, h0]
  simp [TensorProduct.tmul_zero]

/-- The test vector lies in composite sector `0`. -/
theorem v₀_mem_sectorComp_zero : v₀ ∈ sectorComp 0 := by
  rw [mem_sectorComp, chargeComp_v₀]
  simp

/-! ### The mixing computation

`D` and `D²` both carry the sector-`0` test vector out of
sector `0`: in each case the charge of the image is a single
explicit pure tensor whose middle factor is the charge of a
`D₄`- (resp. `D₄²`-) image of the character vector, detected
nonzero by a contraction. -/

/-- The charge of `D₄ (fourierC4 0)` at site `0` is the
explicit nonzero value `(-3 - i) / 4`. -/
theorem chargeC4_factorD_fourierC4_zero_apply :
    chargeC4 (factorC4.D (fourierC4 0)) 0
      = (-3 - Complex.I) / 4 := by
  rw [chargeC4_apply, c4ShiftPerm_zero, c4ShiftPerm_one,
    c4ShiftPerm_two]
  simp only [factorC4_D, diagOpC_apply, fourierC4_zero_apply,
    mul_one]
  norm_num [d₄, z4Energy, Complex.ext_iff, Complex.I_mul_I]

/-- The charge operator kills the `0`-th character vector
(sector `0` is the kernel of `chargeC4` on the factor). -/
theorem chargeC4_fourierC4_zero : chargeC4 (fourierC4 0) = 0 := by
  have h := chargeC4_fourierC4_real 0
  simpa using h

/-- **The charge of `D v₀`**: a single pure tensor, whose
middle factor is `chargeC4 (D₄ (fourierC4 0))` — the first
and third summands of `D v₀` have middle factor `fourierC4 0`
or its grading image (itself), both killed by `chargeC4`. -/
theorem chargeComp_dirac_v₀ :
    chargeComp (diracInst v₀)
      = ((factorQ7.γ (basisC 7 (0, 0)))
          ⊗ₜ[ℝ] (chargeC4 (factorC4.D (fourierC4 0))))
          ⊗ₜ[ℝ] ((Pi.basisFun ℝ (Fin 4)) 0) := by
  simp only [v₀, diracInst, diracQ7C4R4_tmul, map_add,
    chargeComp_tmul, chargeC4_fourierC4_zero,
    factorC4_gamma_fourierC4_zero, TensorProduct.tmul_zero,
    TensorProduct.zero_tmul, add_zero, zero_add]

/-- The charge of `D v₀` is nonzero (its `(1, 0, 0)`
contraction is `(-3 - i) / 4`). -/
theorem chargeComp_dirac_v₀_ne_zero :
    chargeComp (diracInst v₀) ≠ 0 := by
  have hval : contractC 1 0 0
      (((factorQ7.γ (basisC 7 (0, 0)))
          ⊗ₜ[ℝ] (chargeC4 (factorC4.D (fourierC4 0))))
          ⊗ₜ[ℝ] ((Pi.basisFun ℝ (Fin 4)) 0))
      = (-3 - Complex.I) / 4 := by
    rw [contractC_tmul, factorQ7_gamma_basisC_zero,
      chargeC4_factorD_fourierC4_zero_apply]
    simp [basisC_apply, Pi.basisFun_apply]
  rw [chargeComp_dirac_v₀]
  intro hcon
  have h2 := congrArg (contractC 1 0 0) hcon
  have h3 : contractC 1 0 0 (0 : q7c4r4Composite) = 0 := map_zero _
  rw [hval, h3] at h2
  norm_num [Complex.ext_iff] at h2

/-- **`D` does not preserve sector `0`**: the sector's test
vector is carried out of the sector. -/
theorem dirac_v₀_not_mem_sectorComp_zero :
    diracInst v₀ ∉ sectorComp 0 := by
  rw [mem_sectorComp]
  intro h
  have h0 : chargeComp (diracInst v₀) = 0 := by
    rw [h]
    simp
  exact chargeComp_dirac_v₀_ne_zero h0

/-- **`D²` on the test vector**, from the landed `D²`
identity `diracQ7C4R4_sq`: the sum of the three factor-square
pure tensors. -/
theorem diracInst_sq_v₀ :
    (diracInst ^ 2) v₀
      = (((factorQ7.D ^ 2) (basisC 7 (0, 0))) ⊗ₜ[ℝ] (fourierC4 0))
          ⊗ₜ[ℝ] ((Pi.basisFun ℝ (Fin 4)) 0)
        + ((basisC 7 (0, 0))
            ⊗ₜ[ℝ] ((factorC4.D ^ 2) (fourierC4 0)))
            ⊗ₜ[ℝ] ((Pi.basisFun ℝ (Fin 4)) 0)
        + ((basisC 7 (0, 0)) ⊗ₜ[ℝ] (fourierC4 0))
            ⊗ₜ[ℝ] ((factorR.D ^ 2) ((Pi.basisFun ℝ (Fin 4)) 0)) := by
  show ((diracQ7C4R4 factorQ7 factorC4 factorR) ^ 2) v₀ = _
  rw [diracQ7C4R4_sq]
  simp only [v₀, LinearMap.add_apply, opTensorQ_tmul,
    Module.End.one_apply]

/-- **The charge of `D² v₀`**: a single pure tensor, whose
middle factor is `chargeC4 (D₄² (fourierC4 0))`. -/
theorem chargeComp_dirac_sq_v₀ :
    chargeComp ((diracInst ^ 2) v₀)
      = ((basisC 7 (0, 0))
          ⊗ₜ[ℝ] (chargeC4 ((factorC4.D ^ 2) (fourierC4 0))))
          ⊗ₜ[ℝ] ((Pi.basisFun ℝ (Fin 4)) 0) := by
  rw [diracInst_sq_v₀]
  simp only [map_add, chargeComp_tmul, chargeC4_fourierC4_zero,
    TensorProduct.tmul_zero, TensorProduct.zero_tmul, add_zero,
    zero_add]

/-- The charge of `D² v₀` is nonzero (its `(0, 0, 0)`
contraction is `(2 - i) / 16`, §3). -/
theorem chargeComp_dirac_sq_v₀_ne_zero :
    chargeComp ((diracInst ^ 2) v₀) ≠ 0 := by
  have hval : contractC 0 0 0
      (((basisC 7 (0, 0))
          ⊗ₜ[ℝ] (chargeC4 ((factorC4.D ^ 2) (fourierC4 0))))
          ⊗ₜ[ℝ] ((Pi.basisFun ℝ (Fin 4)) 0))
      = (2 - Complex.I) / 16 := by
    rw [contractC_tmul, chargeC4_factorD_sq_fourierC4_zero_apply]
    simp [basisC_apply, Pi.basisFun_apply]
  rw [chargeComp_dirac_sq_v₀]
  intro hcon
  have h2 := congrArg (contractC 0 0 0) hcon
  have h3 : contractC 0 0 0 (0 : q7c4r4Composite) = 0 := map_zero _
  rw [hval, h3] at h2
  norm_num [Complex.ext_iff] at h2

/-- **`D²` does not preserve sector `0`.** -/
theorem dirac_sq_v₀_not_mem_sectorComp_zero :
    (diracInst ^ 2) v₀ ∉ sectorComp 0 := by
  rw [mem_sectorComp]
  intro h
  have h0 : chargeComp ((diracInst ^ 2) v₀) = 0 := by
    rw [h]
    simp
  exact chargeComp_dirac_sq_v₀_ne_zero h0

/-- **The charge operator does not commute with `D`** (the
grading is genuinely mixed by the dynamics-bearing
operator, not invisible to it): on `v₀`, `chargeComp ∘ D`
is nonzero while `D ∘ chargeComp` is zero. -/
theorem chargeComp_not_commute_dirac :
    chargeComp * diracInst ≠ diracInst * chargeComp := by
  intro h
  have happly : (chargeComp * diracInst) v₀
      = (diracInst * chargeComp) v₀ := by rw [h]
  rw [Module.End.mul_apply, Module.End.mul_apply, chargeComp_v₀,
    map_zero] at happly
  exact chargeComp_dirac_v₀_ne_zero happly

/-- **The charge operator does not commute with `D²`**
either. -/
theorem chargeComp_not_commute_dirac_sq :
    chargeComp * (diracInst ^ 2) ≠ (diracInst ^ 2) * chargeComp := by
  intro h
  have happly : (chargeComp * (diracInst ^ 2)) v₀
      = ((diracInst ^ 2) * chargeComp) v₀ := by rw [h]
  rw [Module.End.mul_apply, Module.End.mul_apply, chargeComp_v₀,
    map_zero] at happly
  exact chargeComp_dirac_sq_v₀_ne_zero happly

/-! ## §5. The separation criterion and the K-Q7CR-3 verdict -/

/-- **The separation criterion, stated exactly.** The
charge sectors are *spectrally resolved by `D`* at the
instantiated seat — separated — iff both:

- **(C1) invariance:** every composite charge sector is
  invariant under `D²`, the registered spectral operator of
  Q7CR-2;
- **(C2) disjoint spectral data:** no real eigenvalue of
  `D²` is realized by nonzero eigenvectors in two distinct
  sectors.

This is the criterion the test below evaluates. (Its
factor-level shadow is decided in §3: the C⁴ factor's
sectors contain no `D₄²`-eigenvector at all, so there is no
spectral reading of the sectors in the charge factor itself,
disjoint or otherwise.) -/
def ChargeSpectrallyResolved : Prop :=
  (∀ j, ∀ v ∈ sectorComp j, (diracInst ^ 2) v ∈ sectorComp j)
    ∧ (∀ j j' : Fin 4, j ≠ j' → ∀ μ : ℝ,
        ¬ ((∃ v ∈ sectorComp j, v ≠ 0 ∧ (diracInst ^ 2) v = μ • v)
          ∧ (∃ w ∈ sectorComp j', w ≠ 0
              ∧ (diracInst ^ 2) w = μ • w)))

/-- **The criterion fails**: clause (C1) is false at the
instantiated seat — sector `0` is not `D²`-invariant
(`dirac_sq_v₀_not_mem_sectorComp_zero`, §4). -/
theorem criterion_fails : ¬ ChargeSpectrallyResolved := by
  intro h
  exact dirac_sq_v₀_not_mem_sectorComp_zero
    (h.1 0 v₀ v₀_mem_sectorComp_zero)

/-- **K-Q7CR-3, discharged in the landed form: the kill
FIRES, in the stated form.** The stated C⁴-character charge
grading at Q7CR-2's instantiated seat:

- does **not** commute trivially with the dynamics-bearing
  operator: `chargeComp` commutes with neither `D` nor
  `D²` (the grading is genuinely mixed, not invisible);
- is mixed **with no invariant spectral reading**: sector
  `0` is carried out of itself by both `D` and `D²`, so no
  `D²`-invariant sector decomposition exists; and in the
  charge factor itself, no charge sector contains any
  `D₄²`-eigenvector, for any charge and any eigenvalue
  (§3) — the sectors correspond to no spectral data of the
  registered operators at all.

"Charge separation" in this stated form — the four
character sectors of the C⁴ character grading, separated by
the registered operators at this seat — is therefore dead
at full rank. The grading, its sectors, and the exact
mixing facts above survive as sector/spectrum facts about
this instantiated operator; no mechanism claim is made.
Any different weighting of the characters is a new stated
form, entering as a new entry under the relabeling rule. -/
theorem k_q7cr3_fires :
    ¬ ChargeSpectrallyResolved
      ∧ chargeComp * diracInst ≠ diracInst * chargeComp
      ∧ chargeComp * (diracInst ^ 2) ≠ (diracInst ^ 2) * chargeComp
      ∧ (∀ (j : Fin 4) (μ : ℝ) (y : Fin 4 → ℂ),
          chargeC4 y = (j.val : ℝ) • y
            → (factorC4.D ^ 2) y = μ • y → y = 0)
      ∧ v₀ ∈ sectorComp 0
      ∧ diracInst v₀ ∉ sectorComp 0
      ∧ (diracInst ^ 2) v₀ ∉ sectorComp 0 :=
  ⟨criterion_fails, chargeComp_not_commute_dirac,
    chargeComp_not_commute_dirac_sq, factor_sector_no_eigenvector,
    v₀_mem_sectorComp_zero, dirac_v₀_not_mem_sectorComp_zero,
    dirac_sq_v₀_not_mem_sectorComp_zero⟩

end ThetLogos
