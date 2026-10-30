import Mathlib.Tactic
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.LinearAlgebra.UnitaryGroup
import ThetLogos.FluxTwist
import ThetLogos.Q7C4R4Realify

/-!
# ThetLogos.Q7C4R4Linker — the C₇ register-shift action, registered (Q7CR-6a)

**Status: T1 construction brick. NO CLAIM. Dials 0/4. No measured
number is claimed by this line. Parts of any Millennium statement
closed by this line: 0.**

Governing scoping: `scoping-q7cr-6-linker-2026-10-30.md` §§1, 3 (6a),
4. Gates: Q7CR-0 landed (`ThetLogos.Q7C4R4Post`), Q7CR-1a landed
(`ThetLogos.Q7C4R4Realify`, realification).

## The supplied action (record of authority, on the face)

Action supplied by BONES under Jeff's 2026-10-30 delegation;
superseded by any different name from Jeff. The action is **supplied
by BONES under Jeff's 2026-10-30 delegation** ("supply") — recorded
as such here, NOT as Jeff's coinage; any different name from Jeff
supersedes it.

The supplied action is the additive cyclic group `C₇ = ZMod 7`
acting on the Q⁷ register (`Fin 7 → ℂ`, as Q7CR-0 registers it) by
translation, with generator the 7-cycle `S₇ eₖ = eₖ₊₁ mod 7`.
Rejected alternatives, one line each: `U(7)` — vacuous (every
unitary is a symmetry of a bare inner-product space; no canonical
generator, no finite Fourier dual); the full symmetric group on 7
letters — no canonical generator and no Pontryagin shortcut (its
irreducible theory is Specht theory, a different price). The Weyl /
Heisenberg enrichment (clock-and-shift) is NOT built here; it is
priced only on a demonstrated need from Q7CR-6c.

## How the action is built: specialization, not rebuilding

The corpus owns the shape in `ThetLogos.FluxTwist`: `cyc =
finRotate (n+1)`, `wpMat`, `uniformShift`. This module SPECIALIZES
that machinery at `n = 6`, `θ = 0` and cites it:

- `q7ShiftCyc := cyc (n := 6) = finRotate 7`;
- `q7Shift := uniformShift (n := 6) 0`, the `θ = 0` uniform weighted
  permutation (constant weight `phaseOf 0 = 1`);
- unitarity is CITED from `FluxTwist.uniformShift_unitary` at
  `θ = 0` (§2), not re-proved;
- Fourier diagonalization is the specialization of
  `FluxTwist.uniformShift_mulVec_fourierVec` at `θ = 0` (§3);
- the Pontryagin dual side is the pin's `AddChar.zmodAddEquiv` at
  `n = 7`, cited as a registration (§3), as Q7CR-0 did at `n = 4`.

**Row convention, fixed on the face.** With the corpus's row
convention, `(S₇ *ᵥ v) i = v (cyc₇ i) = v (i + 1)`: the shift pulls
the value from the successor site. The inverse convention is the
same group with the generator replaced by its inverse; this module
uses the successor convention throughout.

## Face labels (verbatim-tier, required)

- "Action supplied by BONES under Jeff's 2026-10-30 delegation;
  superseded by any different name from Jeff."
- "Regular representation — every character once; its Fourier
  completeness is a property of the action, not of the composite."
  (The weakness is on the face, not blurred: over ℂ the action
  decomposes as the direct sum of all seven characters, each once,
  `ℂ⁷ ≅ ⊕_{m} χ_m` in registration form in §3 — complete, and close
  to tautological for a bare register.)
- The standing sentence: **"via C4" survives only as "graded
  by C4"** — and this line's reporting sentence: no proved
  statement in this line makes C⁴ mediate between the Q⁷ and R⁴
  factors (K-Q7CR-6c fired at scoping against the mediation form;
  Jeff's headline stands untouched as his T5 interpretation on
  Q7CR-0's face).
- **Bounded-commutator vacuity caveat (line discipline).** In
  finite dimension the bounded-commutator criterion is VACUOUS —
  every operator here is bounded; the testable content of this
  line is spectrum, grading behavior, and stated identities,
  never bounded commutators. Nothing in this module states or
  implies a bounded-commutator fact.
- NO CLAIM; dials 0/4; no measured number is claimed by this line.

## The representation package (form landed)

The package is landed in **matrix-unitary form**:
`q7Rep : Multiplicative (ZMod 7) →* Matrix.unitaryGroup (Fin 7) ℂ`,
sending `a` to the unitary matrix `S₇ ^ (a.val)`, with the group
law proved from `S₇ ^ 7 = 1` (§2). Here `Multiplicative (ZMod 7)`
is the additive group `C₇` presented multiplicatively, as a group
homomorphism's domain requires. This is a genuine action — a group
homomorphism, faithful (§2) — not merely a named matrix.
-/

namespace ThetLogos

open scoped Matrix

/-! ## §1. The generator: the 7-cycle and its shift matrix -/

/-- **The 7-cycle.** The cyclic successor on the Q⁷ register,
specialized from the corpus's `FluxTwist.cyc` at `n = 6`; it is
`finRotate 7` on the nose. -/
def q7ShiftCyc : Equiv.Perm (Fin 7) :=
  cyc (n := 6)

/-- The 7-cycle is `finRotate 7`, on the nose. -/
theorem q7ShiftCyc_eq_finRotate : q7ShiftCyc = finRotate 7 :=
  rfl

/-- The 7-cycle sends site `i` to its successor `i + 1` (in `Fin 7`). -/
theorem q7ShiftCyc_apply (i : Fin 7) : q7ShiftCyc i = i + 1 :=
  finRotate_apply i

/-- The `k`-th power of the 7-cycle sends site `0` to the site of
value `k` (for `k < 7`): read on values. (This pin has no natural
cast into `Fin 7`, so the power law is stated on values.) -/
theorem q7ShiftCyc_pow_zero_val : ∀ (k : ℕ), k < 7 →
    ((q7ShiftCyc ^ k) 0).val = k := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro hk
    have ih' := ih (by omega)
    rw [pow_succ', Equiv.Perm.mul_apply]
    by_cases hlast : (q7ShiftCyc ^ k) 0 = Fin.last 6
    · rw [hlast] at ih'
      simp only [Fin.val_last] at ih'
      omega
    · rw [q7ShiftCyc_apply, Fin.val_add, Fin.val_one, ih']
      exact Nat.mod_eq_of_lt hk

/-- **The 7-cycle has order exactly 7** (T1): `finRotate 7` is a
cycle (`isCycle_finRotate_of_le`) whose support is everything. -/
theorem q7ShiftCyc_orderOf : orderOf q7ShiftCyc = 7 := by
  have hcyc : (finRotate 7).IsCycle :=
    isCycle_finRotate_of_le (by norm_num)
  have hsupp : (finRotate 7).support = Finset.univ :=
    support_finRotate_of_le (by norm_num)
  show orderOf (finRotate 7) = 7
  rw [hcyc.orderOf, hsupp, Finset.card_univ, Fintype.card_fin]

/-- **The shift matrix `S₇`.** The `θ = 0` uniform twist of
`FluxTwist` at `n = 6`: the weighted permutation of `q7ShiftCyc`
with constant weight `phaseOf 0 = 1`. -/
noncomputable def q7Shift : Matrix (Fin 7) (Fin 7) ℂ :=
  uniformShift (n := 6) 0

/-- `S₇` is the plain (unweighted) permutation matrix of the
7-cycle: `wpMat cyc₇ (fun _ => 1)`. -/
theorem q7Shift_eq_wpMat : q7Shift = wpMat q7ShiftCyc (fun _ => 1) := by
  unfold q7Shift uniformShift q7ShiftCyc
  congr 1
  funext i
  simp [phaseOf_zero]

/-- **Row convention, as a theorem.** `(S₇ *ᵥ v) i = v (cyc₇ i)`:
the shift pulls the value from the successor site. -/
theorem q7Shift_mulVec_apply (v : Fin 7 → ℂ) (i : Fin 7) :
    (q7Shift *ᵥ v) i = v (q7ShiftCyc i) := by
  rw [q7Shift_eq_wpMat, wpMat_mulVec_apply]
  simp

/-- Powers of the shift, read on vectors: `(S₇ ^ k *ᵥ v) i =
v ((cyc₇ ^ k) i)`, the `k`-fold successor. -/
theorem q7Shift_pow_mulVec_apply (k : ℕ) (v : Fin 7 → ℂ) (i : Fin 7) :
    (q7Shift ^ k *ᵥ v) i = v ((q7ShiftCyc ^ k) i) := by
  induction k generalizing v with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ← Matrix.mulVec_mulVec, ih, q7Shift_mulVec_apply]
    congr 1
    rw [pow_succ', Equiv.Perm.mul_apply]

/-! ## §2. First properties: order, faithfulness, unitarity, the package -/

/-- **`S₇ ^ 7 = 1` (T1).** The 7-fold successor is the identity on
`Fin 7`, read through `Matrix.ext_iff_mulVec`. -/
theorem q7Shift_pow_seven : q7Shift ^ 7 = 1 := by
  have hcyc7 : q7ShiftCyc ^ 7 = 1 := by
    have h := pow_orderOf_eq_one q7ShiftCyc
    rw [q7ShiftCyc_orderOf] at h
    exact h
  rw [Matrix.ext_iff_mulVec]
  intro v
  funext i
  rw [q7Shift_pow_mulVec_apply, hcyc7, Matrix.one_mulVec]
  rfl

/-- **Faithfulness (T1): exact order 7.** For `1 ≤ k < 7`,
`S₇ ^ k ≠ 1`: the `k`-th power moves the basis vector at site `0`
to site `k ≠ 0`. -/
theorem q7Shift_pow_ne_one {k : ℕ} (h1 : 1 ≤ k) (hk : k < 7) :
    q7Shift ^ k ≠ 1 := by
  intro h
  have hcast : (q7ShiftCyc ^ k) 0 = ⟨k, hk⟩ :=
    Fin.ext (q7ShiftCyc_pow_zero_val k hk)
  have key1 : (q7Shift ^ k *ᵥ Pi.single ⟨k, hk⟩ (1 : ℂ)) 0 = 1 := by
    rw [q7Shift_pow_mulVec_apply, hcast]
    exact Pi.single_eq_same _ _
  have key0 : (q7Shift ^ k *ᵥ Pi.single ⟨k, hk⟩ (1 : ℂ)) 0 = 0 := by
    rw [h, Matrix.one_mulVec]
    have hne : (0 : Fin 7) ≠ ⟨k, hk⟩ := by
      intro hh
      have hv := congrArg Fin.val hh
      simp only [Fin.val_zero] at hv
      omega
    exact Pi.single_eq_of_ne hne _
  exact one_ne_zero (key1.symm.trans key0)

/-- **Unitarity, by citation (T1).** `S₇` is unitary for the
standard inner product: this is `FluxTwist.uniformShift_unitary`
at `θ = 0`, specialized — cited, not re-proved. -/
theorem q7Shift_unitary :
    q7Shift * q7Shiftᴴ = 1 ∧ q7Shiftᴴ * q7Shift = 1 :=
  uniformShift_unitary (n := 6) 0

/-- `S₇` is a member of the unitary group of matrices (T1), by the
same citation. -/
theorem q7Shift_mem_unitary :
    q7Shift ∈ unitary (Matrix (Fin 7) (Fin 7) ℂ) := by
  rw [Unitary.mem_iff, Matrix.star_eq_conjTranspose]
  exact ⟨q7Shift_unitary.2, q7Shift_unitary.1⟩

/-- **The group law of the package, at the level of exponents
(T1).** Powers of `S₇` add exponents through `ZMod 7` addition:
`S₇ ^ (x + y).val = S₇ ^ x.val * S₇ ^ y.val`, from `S₇ ^ 7 = 1`. -/
theorem q7Shift_zmod_pow_add (x y : ZMod 7) :
    q7Shift ^ (x + y).val = q7Shift ^ x.val * q7Shift ^ y.val := by
  rw [ZMod.val_add]
  have hsum : q7Shift ^ ((x.val + y.val) % 7) = q7Shift ^ (x.val + y.val) := by
    rcases lt_or_ge (x.val + y.val) 7 with h | h
    · rw [Nat.mod_eq_of_lt h]
    · have hlt : x.val + y.val < 14 := by
        have hx := ZMod.val_lt x
        have hy := ZMod.val_lt y
        omega
      have hmod : (x.val + y.val) % 7 = x.val + y.val - 7 := by
        rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]
      rw [hmod]
      conv_rhs => rw [← Nat.sub_add_cancel h, pow_add, q7Shift_pow_seven,
        mul_one]
  rw [hsum, pow_add]

/-- **The representation package (T1), matrix-unitary form.**
`q7Rep : Multiplicative (ZMod 7) →* Matrix.unitaryGroup (Fin 7) ℂ`
sends `a` to the unitary matrix `S₇ ^ (a.val)`; the group law is
`q7Shift_zmod_pow_add`, i.e. it is proved from `S₇ ^ 7 = 1`. A
genuine action of `C₇`, not merely a named matrix. -/
noncomputable def q7Rep :
    Multiplicative (ZMod 7) →* Matrix.unitaryGroup (Fin 7) ℂ where
  toFun a := ⟨q7Shift ^ (Multiplicative.toAdd a).val,
    pow_mem q7Shift_mem_unitary _⟩
  map_one' := by
    apply Subtype.ext
    show q7Shift ^ (Multiplicative.toAdd (1 : Multiplicative (ZMod 7))).val = 1
    simp
  map_mul' a b := by
    apply Subtype.ext
    show q7Shift ^ (Multiplicative.toAdd (a * b)).val
      = q7Shift ^ (Multiplicative.toAdd a).val
        * q7Shift ^ (Multiplicative.toAdd b).val
    exact q7Shift_zmod_pow_add _ _

/-- The package's underlying matrix is the stated power of `S₇`. -/
theorem q7Rep_apply (a : Multiplicative (ZMod 7)) :
    (q7Rep a : Matrix (Fin 7) (Fin 7) ℂ)
      = q7Shift ^ (Multiplicative.toAdd a).val :=
  rfl

/-- The package's generator (at the additive `1` of `ZMod 7`) is
`S₇` itself. -/
theorem q7Rep_generator :
    (q7Rep (Multiplicative.ofAdd 1) : Matrix (Fin 7) (Fin 7) ℂ) = q7Shift := by
  rw [q7Rep_apply,
    show Multiplicative.toAdd (Multiplicative.ofAdd (1 : ZMod 7)) = 1 from rfl,
    show (1 : ZMod 7).val = 1 by decide, pow_one]

/-- **The package is faithful (T1).** `q7Rep` is injective: its
kernel is trivial because `S₇` has exact order 7
(`q7Shift_pow_ne_one`). -/
theorem q7Rep_injective : Function.Injective q7Rep := by
  intro a b hab
  have h1 : q7Rep (a * b⁻¹) = 1 := by
    rw [map_mul, map_inv, hab, mul_inv_cancel]
  have h2 : q7Shift ^ (Multiplicative.toAdd (a * b⁻¹)).val = 1 := by
    have h := congrArg
      (fun U : Matrix.unitaryGroup (Fin 7) ℂ => (U : Matrix (Fin 7) (Fin 7) ℂ)) h1
    rw [q7Rep_apply] at h
    exact h
  have hx : Multiplicative.toAdd (a * b⁻¹) = 0 := by
    by_contra hne
    have hval : (Multiplicative.toAdd (a * b⁻¹)).val ≠ 0 := by
      intro hv
      apply hne
      conv_lhs => rw [← ZMod.natCast_zmod_val (Multiplicative.toAdd (a * b⁻¹))]
      rw [hv]
      simp
    have hge : 1 ≤ (Multiplicative.toAdd (a * b⁻¹)).val :=
      Nat.one_le_iff_ne_zero.mpr hval
    exact q7Shift_pow_ne_one hge (ZMod.val_lt _) h2
  have hab1 : a * b⁻¹ = 1 := by
    have h : a * b⁻¹
        = Multiplicative.ofAdd (Multiplicative.toAdd (a * b⁻¹)) := rfl
    rw [hx] at h
    exact h
  exact mul_inv_eq_one.mp hab1

/-! ## §3. Fourier diagonalization and the Pontryagin side

By specialization of `FluxTwist.uniformShift_mulVec_fourierVec` at
`θ = 0`, the Fourier vectors diagonalize `S₇`. Hence, in
registration form: the complex spectrum of `S₇` is
`{ζ₇ ^ m : m = 0, …, 6}` with `ζ₇ = phaseOf (2π / 7)`, the seven
eigenvalues are pairwise distinct (proved below via the pin's
primitive-root API), and there are seven of them in dimension 7 —
each eigenvalue has multiplicity one — and the character
decomposition is `ℂ⁷ ≅ ⊕_{m : ZMod 7} χ_m`, the regular
representation's decomposition, every character once. -/

/-- **Fourier diagonalization (T1).** The `m`-th Fourier vector is
an eigenvector of `S₇` with eigenphase `phaseOf (2π m / 7)`:
`FluxTwist.uniformShift_mulVec_fourierVec` at `θ = 0`,
specialized. -/
theorem q7Shift_mulVec_fourierVec (m : Fin 7) :
    q7Shift *ᵥ fourierVec m
      = phaseOf (2 * Real.pi * (m.val : ℝ) / 7) • fourierVec m := by
  have h := uniformShift_mulVec_fourierVec (n := 6) 0 m
  convert h using 2
  · exact rfl
  · push_cast
    ring

/-- Fourier vectors are nonzero (their `0`-component is `1`). -/
theorem q7_fourierVec_ne_zero (m : Fin 7) : fourierVec (n := 6) m ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  simp only [Pi.zero_apply] at h0
  rw [show fourierVec (n := 6) m 0 = 1 by simp [fourierVec, phaseOf_zero]] at h0
  exact one_ne_zero h0

/-- **The spectrum of `S₇`, formal part (T1).** Every Fourier
vector is a nonzero eigenvector, with the stated eigenphase. -/
theorem q7Shift_spectrum (m : Fin 7) :
    q7Shift *ᵥ fourierVec m
        = phaseOf (2 * Real.pi * (m.val : ℝ) / 7) • fourierVec m
      ∧ fourierVec m ≠ 0 :=
  ⟨q7Shift_mulVec_fourierVec m, q7_fourierVec_ne_zero m⟩

/-- The eigenphase is the `m`-th power of the primitive 7th root
`ζ₇ = exp (2π i / 7)`. -/
theorem q7_eigenvalue_eq_zeta_pow (m : Fin 7) :
    phaseOf (2 * Real.pi * (m.val : ℝ) / 7)
      = (Complex.exp (2 * Real.pi * Complex.I / ((7 : ℕ) : ℂ))) ^ m.val := by
  rw [phaseOf, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- **The seven eigenphases are pairwise distinct (T1)**, via the
pin's primitivity of `exp (2π i / 7)` (`Complex.isPrimitiveRoot_exp`)
and `IsPrimitiveRoot.pow_inj`. With §3's eigenvector statement this
pins the spectrum as `{ζ₇ ^ m}`, each eigenvalue of multiplicity
one, in dimension 7. -/
theorem q7_eigenvalues_injective :
    Function.Injective
      fun m : Fin 7 => phaseOf (2 * Real.pi * (m.val : ℝ) / 7) := by
  intro a b hab
  have hab2 : phaseOf (2 * Real.pi * (a.val : ℝ) / 7)
      = phaseOf (2 * Real.pi * (b.val : ℝ) / 7) := hab
  rw [q7_eigenvalue_eq_zeta_pow, q7_eigenvalue_eq_zeta_pow] at hab2
  have hζ : IsPrimitiveRoot
      (Complex.exp (2 * Real.pi * Complex.I / ((7 : ℕ) : ℂ))) 7 :=
    Complex.isPrimitiveRoot_exp 7 (by norm_num)
  have h := hζ.pow_inj a.isLt b.isLt hab2
  exact Fin.ext h

/-- **Conjugate pairing of the eigenphases (T1).** The conjugate of
the `m`-th eigenphase is the `(7 − m)`-th eigenphase: the spectrum
is closed under conjugation in the pairs `(m, 7 − m)`. This is the
complex-side fact behind the real block form of §4. -/
theorem q7_eigenvalue_conj_pair (m : Fin 7) :
    (starRingEnd ℂ) (phaseOf (2 * Real.pi * (m.val : ℝ) / 7))
      = phaseOf (2 * Real.pi * ((7 - m.val : ℕ) : ℝ) / 7) := by
  have hm : m.val ≤ 7 := le_of_lt m.isLt
  have harg : 2 * Real.pi * ((7 - m.val : ℕ) : ℝ) / 7
      = 2 * Real.pi * ((1 : ℕ) : ℝ) + (-(2 * Real.pi * (m.val : ℝ) / 7)) := by
    rw [Nat.cast_sub hm]
    push_cast
    ring
  rw [conj_phaseOf, harg, phaseOf_add, phaseOf_two_pi_mul_nat, one_mul]

/-- **The Pontryagin side, cited as a registration (T1
registration).** The pin's `AddChar.zmodAddEquiv` at `n = 7`:
the dual group of `ZMod 7` is `ZMod 7` itself. This is the
action's dual-side registration, cited from the pin — not rebuilt
— exactly as Q7CR-0 cites the same theorem for C⁴ at `n = 4`. -/
noncomputable def q7Pontryagin : ZMod 7 ≃+ AddChar (ZMod 7) ℂ :=
  AddChar.zmodAddEquiv (n := 7)

/-! ## §4. The realified action

Via Q7CR-1a's `realifyOp`, the shift's ℂ-linear map realifies to
an ℝ-linear operator `S₇ᴿ` on the realified register (ℝ¹⁴ as a
real space: `Fin 7 → ℂ` in its real module structure).

**Block form, stated exactly.** Over ℝ, the realified action has
**four** real isotypic blocks, `1 ⊕ 2 ⊕ 2 ⊕ 2`: the trivial real
character (1-dimensional), and the three conjugate character pairs
`χ₁ ⊕ χ₆`, `χ₂ ⊕ χ₅`, `χ₃ ⊕ χ₄` as three 2-dimensional rotation
blocks, at angles `2π/7`, `4π/7`, `6π/7` respectively (the pairing
is `q7_eigenvalue_conj_pair`). Any statement speaking of seven
real character sectors is FALSE and is not written here: over ℝ
the conjugate pairs fuse into 2-dimensional blocks. -/

/-- The shift as a ℂ-linear map: the linear map of the matrix
`S₇` (`Matrix.toLin'`). -/
noncomputable def q7ShiftLin : (Fin 7 → ℂ) →ₗ[ℂ] (Fin 7 → ℂ) :=
  Matrix.toLin' q7Shift

/-- The ℂ-linear shift map acts as the matrix does. -/
theorem q7ShiftLin_apply (v : Fin 7 → ℂ) :
    q7ShiftLin v = q7Shift *ᵥ v :=
  Matrix.toLin'_apply _ _

/-- Powers of the ℂ-linear shift map act as the matrix powers do. -/
theorem q7ShiftLin_pow_apply (k : ℕ) (v : Fin 7 → ℂ) :
    (q7ShiftLin ^ k) v = (q7Shift ^ k) *ᵥ v := by
  induction k generalizing v with
  | zero => simp [Matrix.one_mulVec]
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, ih, q7ShiftLin_apply, pow_succ',
      Matrix.mulVec_mulVec]

/-- The ℂ-linear shift has order dividing 7, transported from the
matrix law `S₇ ^ 7 = 1`. -/
theorem q7ShiftLin_pow_seven : q7ShiftLin ^ 7 = 1 := by
  apply LinearMap.ext
  intro v
  rw [q7ShiftLin_pow_apply, q7Shift_pow_seven, Matrix.one_mulVec]
  rfl

/-- Transport of powers across realification, pointwise: powers of
a realified operator act as the realification of the powers. -/
theorem realifyOp_pow_apply {n : ℕ} (A : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ))
    (k : ℕ) (v : Fin n → ℂ) :
    ((realifyOp A) ^ k) v = (A ^ k) v := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, ih, realifyOp_apply, pow_succ',
      Module.End.mul_apply]

/-- **The realified shift `S₇ᴿ`.** Q7CR-1a's `realifyOp` applied
to the ℂ-linear shift: an ℝ-linear operator on the realified
register. -/
noncomputable def q7ShiftR : (Fin 7 → ℂ) →ₗ[ℝ] (Fin 7 → ℂ) :=
  realifyOp q7ShiftLin

/-- **`(S₇ᴿ) ^ 7 = 1` (T1)**, by transport from the complex law
through realification. -/
theorem q7ShiftR_pow_seven : q7ShiftR ^ 7 = 1 := by
  apply LinearMap.ext
  intro v
  show ((realifyOp q7ShiftLin) ^ 7) v
    = (1 : (Fin 7 → ℂ) →ₗ[ℝ] (Fin 7 → ℂ)) v
  rw [realifyOp_pow_apply, q7ShiftLin_pow_seven]
  rfl

/-- The realified shift commutes with the complex structure `J`
(Q7CR-1a's `complexStructure`): the real-side shadow of
ℂ-linearity, and the operator-level reason the real form's
nontrivial blocks are the conjugate-paired 2-dimensional rotation
blocks of the block-form statement above. -/
theorem q7ShiftR_comm_complexStructure :
    q7ShiftR ∘ₗ complexStructure 7
      = complexStructure 7 ∘ₗ q7ShiftR :=
  realifyOp_comm_complexStructure q7ShiftLin

end ThetLogos
