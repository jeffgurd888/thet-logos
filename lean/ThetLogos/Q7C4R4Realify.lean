import Mathlib.Tactic
import ThetLogos.Q7C4R4Post

/-!
# ThetLogos.Q7C4R4Realify — realification of factor operators + gradings (Q7CR-1a)

**Status: T1 construction brick (general, over factor operators).
NO CLAIM. Dials 0/4. No measured number is claimed by this line.**

Governing scoping: `scoping-q7c4r4-gauntlet-2026-10-30.md` §§2, 3
(Q7CR-1), 5. Gate: Q7CR-0 landed (`ThetLogos.Q7C4R4Post`, the
registration of Q⁷C⁴R⁴ as one real space ℝ⁴⁴⁸ under DQ1 = ALL-REAL).

## What this brick is

The corpus owns the product-Dirac pattern over ℂ (`ProductTriple`)
and Kronecker machinery; it owned NOTHING over ℝ for realified
complex factors. This brick builds that realification layer, for a
general finite complex factor `Fin n → ℂ` carried in its real module
structure (the two complex factors of the registration are the seats
`n = 7` (Q⁷) and `n = 4` (C⁴); the R⁴ factor is already real and is
not this brick's concern).

**Seat landed: linear maps.** Operators are linear maps on
`Fin n → ℂ` (ℂ-linear on the complex side, ℝ-linear after
realification); self-adjointness is stated FOR THE FORM — symmetry
with respect to a stated pairing — the corpus's own seat in
`ThetLogos.ProductTriple` (form-self-adjointness `ηᴴ = η`, no adjoint
operator constructed). The real pairing is Q7CR-0's registered real
pairing (the real part of the standard Hermitian form), in its
general-`n` form (§2 below); at `n = 7` and `n = 4` it is exactly
`q7c4r4PairQ7` / `q7c4r4PairC4`.

Content, in order: the complex structure `J` as a real-linear map
with `J² = −1` (§1); realification of operators with its transport
kit — one / add / comp / zero, and commutation with `J` (§2);
self-adjointness transport across realification (§3); the grading
transport theorem (§4 — the seat of the pre-registered kill
K-Q7CR-1); and the `FactorOp` real factor package with its
constructor from a complex factor package (§5).

## Fences, on the face

- **Bounded-commutator vacuity caveat (verbatim-tier).** In finite
  dimension the bounded-commutator criterion is VACUOUS — every
  operator on ℝ⁴⁴⁸ is bounded; the testable content of this line is
  spectrum, grading behavior, and the D² identity, never bounded
  commutators. Nothing in this module states or implies a
  bounded-commutator fact.
- **Factor operators are CHOICES.** This brick is general over
  factor operators: nothing here singles out a specific operator on
  any factor (nothing singles out D₇; the clock-data diagonal is
  measured input, and any instantiation of it is a later, labeled
  step carrying the D1 fence). No specific factor operator is
  instantiated anywhere in this module.
- **Kill K-Q7CR-1 (armed at scoping, watched here).** If the
  realified grading could not be made to anticommute in the stated
  shape — a sign obstruction in the realification — the
  product-Dirac shape dies at full rank and the anticommutation
  field is NOT weakened to make it pass. Status at landing: the
  kill does NOT fire — anticommutation transports exactly (§4),
  because realification is restriction of scalars and preserves
  addition and composition on the nose.
- NO CLAIM; dials 0/4; no measured number is claimed by this line.
-/

namespace ThetLogos

open scoped ComplexConjugate

/-! ## §1. The complex structure as a real-linear map -/

/-- **The complex structure.** Multiplication by `i`, pointwise, as a
real-linear map on the realified factor `Fin n → ℂ`. This is the data
that remembers the factor was complex: it is an ℝ-linear operator,
not a scalar. -/
def complexStructure (n : ℕ) : (Fin n → ℂ) →ₗ[ℝ] (Fin n → ℂ) where
  toFun := fun x k => Complex.I * x k
  map_add' := by
    intro x y
    funext k
    simp [mul_add]
  map_smul' := by
    intro r x
    funext k
    show Complex.I * ((r : ℂ) * x k) = (r : ℂ) * (Complex.I * x k)
    rw [mul_left_comm]

/-- Pointwise formula for the complex structure. -/
theorem complexStructure_apply (n : ℕ) (x : Fin n → ℂ) (k : Fin n) :
    complexStructure n x k = Complex.I * x k :=
  rfl

/-- **The complex structure squares to `−1`** (as real-linear maps):
`J ∘ₗ J = -1`. -/
theorem complexStructure_sq (n : ℕ) :
    complexStructure n ∘ₗ complexStructure n = -1 := by
  ext x k
  simp only [LinearMap.comp_apply, complexStructure_apply, LinearMap.neg_apply,
    Module.End.one_apply, Pi.neg_apply]
  rw [← mul_assoc, Complex.I_mul_I, neg_one_mul]

/-! ## §2. Realification of operators and its transport kit -/

/-- **Realification of an operator.** A ℂ-linear operator on the
factor, carried as an ℝ-linear operator by restriction of scalars.
The underlying function is unchanged; only the scalar field it is
linear over shrinks. -/
noncomputable def realifyOp {n : ℕ} (A : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) :
    (Fin n → ℂ) →ₗ[ℝ] (Fin n → ℂ) :=
  A.restrictScalars ℝ

/-- Realification does not move a vector: `(realifyOp A) x = A x`. -/
theorem realifyOp_apply {n : ℕ} (A : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ))
    (x : Fin n → ℂ) :
    realifyOp A x = A x :=
  rfl

/-- Transport of zero: the realification of `0` is `0`. -/
theorem realifyOp_zero {n : ℕ} :
    realifyOp (0 : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) = 0 := by
  ext x k
  simp [realifyOp_apply]

/-- Transport of one: the realification of `1` is `1`. -/
theorem realifyOp_one {n : ℕ} :
    realifyOp (1 : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) = 1 := by
  ext x k
  simp [realifyOp_apply]

/-- Transport of addition: realification preserves sums of
operators. -/
theorem realifyOp_add {n : ℕ} (A B : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) :
    realifyOp (A + B) = realifyOp A + realifyOp B := by
  ext x k
  simp [realifyOp_apply]

/-- Transport of composition: realification preserves composition
of operators, as real composition. -/
theorem realifyOp_comp {n : ℕ} (A B : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) :
    realifyOp (A ∘ₗ B) = realifyOp A ∘ₗ realifyOp B := by
  ext x k
  simp [realifyOp_apply]

/-- **Every realified ℂ-linear operator commutes with the complex
structure `J`.** This is the real-side shadow of ℂ-linearity itself:
an operator that was linear over ℂ respects multiplication by `i`
after its scalars are restricted to ℝ. -/
theorem realifyOp_comm_complexStructure {n : ℕ}
    (A : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) :
    realifyOp A ∘ₗ complexStructure n
      = complexStructure n ∘ₗ realifyOp A := by
  apply LinearMap.ext
  intro x
  show realifyOp A (complexStructure n x) = complexStructure n (realifyOp A x)
  rw [realifyOp_apply, realifyOp_apply,
    show complexStructure n x = Complex.I • x from rfl, map_smul]
  rfl

/-! ## §3. The pairings and self-adjointness transport

Self-adjointness is taken with respect to a stated pairing (the
form seat): the complex Hermitian form on the complex side, and
Q7CR-0's registered REAL pairing — its real part — on the real
side. -/

/-- The standard Hermitian form on the factor, complex-valued:
`(x, y) ↦ ∑ k, x k * conj (y k)` (linear in the first argument,
conjugate-linear in the second). -/
def cplxPair (n : ℕ) (x y : Fin n → ℂ) : ℂ :=
  ∑ k, x k * star (y k)

/-- **The registered real pairing, in general-`n` form**: the real
part of the standard Hermitian form. At `n = 7` and `n = 4` this is
exactly Q7CR-0's `q7c4r4PairQ7` / `q7c4r4PairC4` (proved as
`factorPair_seven` / `factorPair_four` below). -/
def factorPair (n : ℕ) (x y : Fin n → ℂ) : ℝ :=
  (cplxPair n x y).re

/-- At `n = 7` the general real pairing is Q7CR-0's registered Q⁷
pairing, on the nose. -/
theorem factorPair_seven (x y : Fin 7 → ℂ) :
    factorPair 7 x y = q7c4r4PairQ7 x y :=
  rfl

/-- At `n = 4` the general real pairing is Q7CR-0's registered C⁴
pairing, on the nose. -/
theorem factorPair_four (x y : Fin 4 → ℂ) :
    factorPair 4 x y = q7c4r4PairC4 x y :=
  rfl

/-- Conjugate symmetry of the Hermitian form:
`pair y x = conj (pair x y)`. -/
theorem cplxPair_comm_star (n : ℕ) (x y : Fin n → ℂ) :
    cplxPair n y x = star (cplxPair n x y) := by
  simp only [cplxPair, star_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [star_mul, star_star, mul_comm]

/-- The real pairing is symmetric (the real shadow of conjugate
symmetry). -/
theorem factorPair_symm (n : ℕ) (x y : Fin n → ℂ) :
    factorPair n x y = factorPair n y x := by
  show (cplxPair n x y).re = (cplxPair n y x).re
  rw [cplxPair_comm_star n y x]
  exact RCLike.conj_re (cplxPair n y x)

/-- The real pairing is additive in its first argument. -/
theorem factorPair_add_left (n : ℕ) (x x' y : Fin n → ℂ) :
    factorPair n (x + x') y = factorPair n x y + factorPair n x' y := by
  simp only [factorPair, cplxPair, Pi.add_apply, add_mul,
    Finset.sum_add_distrib, Complex.add_re]

/-- The real pairing vanishes in the first argument at zero. -/
theorem factorPair_zero_left (n : ℕ) (y : Fin n → ℂ) :
    factorPair n 0 y = 0 := by
  simp [factorPair, cplxPair]

/-- **Self-adjointness over ℂ, for the form**: an operator `A` is
self-adjoint when the Hermitian form satisfies
`pair (A x) y = pair x (A y)` for all `x y`. -/
def CplxSelfAdjoint {n : ℕ} (A : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) : Prop :=
  ∀ x y, cplxPair n (A x) y = cplxPair n x (A y)

/-- **Self-adjointness over ℝ, for the form**: an operator `B` is
self-adjoint when the registered real pairing satisfies
`pair (B x) y = pair x (B y)` for all `x y`. -/
def RealSelfAdjoint {n : ℕ} (B : (Fin n → ℂ) →ₗ[ℝ] (Fin n → ℂ)) : Prop :=
  ∀ x y, factorPair n (B x) y = factorPair n x (B y)

/-- **Self-adjointness transport.** If `A` is self-adjoint with
respect to the complex Hermitian form, then its realification is
self-adjoint with respect to Q7CR-0's registered real pairing (the
real part of that form). The proof is one line of content: the
complex identity, read through `Complex.re`. -/
theorem realifyOp_selfAdjoint {n : ℕ}
    {A : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)} (hA : CplxSelfAdjoint A) :
    RealSelfAdjoint (realifyOp A) := by
  intro x y
  show (cplxPair n (A x) y).re = (cplxPair n x (A y)).re
  rw [hA x y]

/-- The complex structure is skew-adjoint for the real pairing:
`pair (J x) y = - pair x (J y)` — the real-side record that `J` is
multiplication by a purely imaginary scalar. -/
theorem complexStructure_skew (n : ℕ) (x y : Fin n → ℂ) :
    factorPair n (complexStructure n x) y
      = - factorPair n x (complexStructure n y) := by
  have hsum : (∑ k, x k * star (Complex.I * y k))
      = - ∑ k, Complex.I * x k * star (y k) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro k _
    have hI : star (Complex.I : ℂ) = -Complex.I := by
      exact Complex.conj_I
    rw [star_mul, hI]
    ring
  show (cplxPair n (complexStructure n x) y).re
    = - (cplxPair n x (complexStructure n y)).re
  simp only [cplxPair, complexStructure_apply]
  rw [hsum, Complex.neg_re, neg_neg]

/-! ## §4. Grading transport — the seat of kill K-Q7CR-1

Realification is restriction of scalars: it preserves addition and
composition on the nose (§2), so involution and anticommutation —
pure equational laws in `+` and `∘ₗ` — transport exactly. There is
no sign to lose: the kill does not fire. -/

/-- Involution transport: if `γ ∘ₗ γ = 1` over ℂ, the realified
grading satisfies `γ̄ ∘ₗ γ̄ = 1` over ℝ. -/
theorem realifyOp_involutive {n : ℕ}
    {γ : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)} (h : γ ∘ₗ γ = 1) :
    realifyOp γ ∘ₗ realifyOp γ = 1 := by
  rw [← realifyOp_comp, h, realifyOp_one]

/-- **Anticommutation transport (the kill's exact seat).** If
`γ ∘ₗ D + D ∘ₗ γ = 0` over ℂ, the realifications anticommute over
ℝ in the same shape. K-Q7CR-1 would have fired here if a sign
obstruction existed; none does — the law is equational in `+` and
`∘ₗ`, both preserved on the nose by §2. -/
theorem realifyOp_anticomm {n : ℕ}
    {D γ : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)}
    (h : γ ∘ₗ D + D ∘ₗ γ = 0) :
    realifyOp γ ∘ₗ realifyOp D + realifyOp D ∘ₗ realifyOp γ = 0 := by
  rw [← realifyOp_comp, ← realifyOp_comp, ← realifyOp_add, h, realifyOp_zero]

/-- **The grading transport theorem (one package).** Let `γ` and
`D` be ℂ-linear operators on the factor with `γ` self-adjoint,
`D` self-adjoint, `γ ∘ₗ γ = 1`, and `γ` anticommuting with `D`.
Then the realifications over ℝ satisfy the same four laws:
real-self-adjointness of both, the involution, and the
anticommutation — in the stated shape, with the anticommutation
field unweakened. -/
theorem grading_transport {n : ℕ}
    {D γ : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)}
    (hγsa : CplxSelfAdjoint γ) (hDsa : CplxSelfAdjoint D)
    (hinv : γ ∘ₗ γ = 1) (hanti : γ ∘ₗ D + D ∘ₗ γ = 0) :
    RealSelfAdjoint (realifyOp γ) ∧ RealSelfAdjoint (realifyOp D) ∧
      realifyOp γ ∘ₗ realifyOp γ = 1 ∧
      realifyOp γ ∘ₗ realifyOp D + realifyOp D ∘ₗ realifyOp γ = 0 :=
  ⟨realifyOp_selfAdjoint hγsa, realifyOp_selfAdjoint hDsa,
    realifyOp_involutive hinv, realifyOp_anticomm hanti⟩

/-! ## §5. The factor packages

`FactorOp` is the gauntlet §5 draft adapted to this brick's seat:
the space is the realified factor `Fin n → ℂ` as a real space,
operators are ℝ-linear maps on it, and self-adjointness is for the
registered real pairing of §3 (form seat, as in `ProductTriple`).
The anticommutation field is carried in exactly the stated shape. -/

/-- A complex factor package: a ℂ-linear operator and grading on
the factor, the grading an involution, both self-adjoint for the
Hermitian form, anticommuting. -/
structure CplxFactorOp (n : ℕ) where
  /-- The factor operator (a choice, in every instantiation). -/
  D : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)
  /-- The factor grading. -/
  γ : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)
  γ_invol : γ ∘ₗ γ = 1
  γ_selfadj : CplxSelfAdjoint γ
  D_selfadj : CplxSelfAdjoint D
  anticomm : γ ∘ₗ D + D ∘ₗ γ = 0

/-- **A real factor package** (the gauntlet §5 `FactorOp`, adapted
to the linear-map / form seat): an ℝ-linear operator and grading
on the realified factor, the grading an involution, both
self-adjoint for the registered real pairing, anticommuting in the
stated shape `γ ∘ₗ D + D ∘ₗ γ = 0`. -/
structure FactorOp (n : ℕ) where
  /-- The factor operator (a choice, in every instantiation). -/
  D : (Fin n → ℂ) →ₗ[ℝ] (Fin n → ℂ)
  /-- The factor grading. -/
  γ : (Fin n → ℂ) →ₗ[ℝ] (Fin n → ℂ)
  γ_invol : γ ∘ₗ γ = 1
  γ_selfadj : RealSelfAdjoint γ
  D_selfadj : RealSelfAdjoint D
  anticomm : γ ∘ₗ D + D ∘ₗ γ = 0

/-- **The constructor.** A complex factor package realifies to a
real factor package on the realified factor: operator and grading
are the realifications, and every field is discharged by the
transport kit — involution and anticommutation by §4,
self-adjointness by §3. -/
noncomputable def FactorOp.ofCplx {n : ℕ} (F : CplxFactorOp n) : FactorOp n where
  D := realifyOp F.D
  γ := realifyOp F.γ
  γ_invol := realifyOp_involutive F.γ_invol
  γ_selfadj := realifyOp_selfAdjoint F.γ_selfadj
  D_selfadj := realifyOp_selfAdjoint F.D_selfadj
  anticomm := realifyOp_anticomm F.anticomm

/-- The constructed package's operator is the realification of the
complex package's operator. -/
theorem FactorOp.ofCplx_D {n : ℕ} (F : CplxFactorOp n) :
    (FactorOp.ofCplx F).D = realifyOp F.D :=
  rfl

/-- The constructed package's grading is the realification of the
complex package's grading. -/
theorem FactorOp.ofCplx_γ {n : ℕ} (F : CplxFactorOp n) :
    (FactorOp.ofCplx F).γ = realifyOp F.γ :=
  rfl

/-- Transport of negation: realification preserves negation of
operators. -/
theorem realifyOp_neg {n : ℕ} (A : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) :
    realifyOp (-A) = - realifyOp A := by
  ext x k
  simp [realifyOp_apply]

/-- Transport of subtraction: realification preserves differences
of operators. -/
theorem realifyOp_sub {n : ℕ} (A B : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) :
    realifyOp (A - B) = realifyOp A - realifyOp B := by
  ext x k
  simp [realifyOp_apply]

/-- Transport of real scalar multiplication: realifying a real
scalar multiple (the scalar read in ℂ) is the real scalar multiple
of the realification. -/
theorem realifyOp_real_smul {n : ℕ} (r : ℝ)
    (A : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) :
    realifyOp ((r : ℂ) • A) = r • realifyOp A := by
  apply LinearMap.ext
  intro x
  funext k
  show ((r : ℂ) • A) x k = (r • realifyOp A x) k
  rw [LinearMap.smul_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul,
    Complex.real_smul]
  rfl

end ThetLogos
