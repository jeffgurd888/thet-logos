/-
# SHELF-7a - spectral mapping, rational clause (working label)

Brick SHELF-7a of the SHELF rotation (pack
`routeb-general-scratch/pack-shelf-7a.md`): spectral mapping
for the corpus's operator seats, rational clause. NO CLAIM
beyond the theorems below; no dial is touched.

## Step 0 - the probe (done first, 2026-11-01)

Pin: Mathlib v4.35.0-rc3 (this tree). Inventory of spectral
mapping already owned - cited boundaries, NOT targets:

* Pin, `cfc` polynomial/continuous spectral mapping for
  NORMAL elements of C*-algebras (predicate-gated):
  `cfcHom_map_spectrum` in
  `Mathlib/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Unital.lean`.
  Continuous functions, normal elements only: no rational
  clause and no non-normal seat.
* Pin, POLYNOMIAL spectral mapping for a general complex
  Banach-algebra element:
  `spectrum.map_polynomial_aeval` in
  `Mathlib/Analysis/Normed/Algebra/GelfandFormula.lean`
  (line 175 at probe time):
  `spectrum C (aeval a p) = (fun k => eval k p) '' spectrum C a`.
  No inverse / rational form anywhere in the pin (grep of
  the full Mathlib tree for spectrum + RatFunc / rational
  spectral mapping: no hit).
* SHELF-8a (landed, `ThetLogos.HolomorphicFunctionalCalculus`):
  the disc fragment `hfcDisc`; its section 7 owns (i) the
  full POLYNOMIAL spectral mapping transferred through
  `hfcDisc_polynomial` (`spectrum_hfcDisc_polynomial`) and
  (ii) the FORWARD inclusion only for the disc series
  fragment (`scalarEval_mem_spectrum`). The reverse disc
  inclusion and any rational clause are named remainders
  there, not landed material.
* Corpus seats owning their spectra DIRECTLY (cite, don't
  redo): `tripotent_selfadjoint_spectrum` in
  `ThetLogos.TRO` (self-adjoint tripotent matrices:
  `spectrum C X ⊆ {-1, 0, 1}`); the transfer-operator seats
  (`LatticeTransferCompact`, `DoeblinGap`, `Span3GapPins`)
  bound `spectrum C (transferOp ...)` directly.

## The gap, as named

RATIONAL spectral mapping is owned nowhere above: for
`a` in a complex Banach algebra, polynomials `p q` with
`eval lam q ≠ 0` at every `lam ∈ spectrum C a`, the element
`p(a) / q(a)` (formed with the ring inverse of `q(a)`,
which is then a genuine unit) should satisfy
`spectrum C (p(a)/q(a)) = (fun lam => eval lam p / eval lam q)
'' spectrum C a`, denominator hypothesis on the face.
This holds in particular at every finite-dimensional seat
the corpus computes with (matrix algebras), with no
normality and no continuous/holomorphic calculus.

## What is landed here

* `ratEval a p q`: the rational evaluation, total (junk
  value `aeval a p * 0`-form when the denominator is not a
  unit, in the style of SHELF-8a's `hfcDisc`); every theorem
  carries its denominator hypothesis explicitly.
* The denominator criterion: `eval q` nonvanishing on
  `spectrum C a` iff `aeval a q` is a unit (one direction is
  the load-bearing one; both are proved from the pin's
  polynomial mapping).
* Headline: the full rational spectral mapping equality
  (`spectrum_ratEval`), proved by reducing
  `mu ∈ spectrum C (ratEval a p q)` to the polynomial
  `p - C mu * q` having a root in `spectrum C a`, via the
  pin's polynomial mapping - no eigenvalues, no Jordan form.
* Corollaries: the inverse case `p = 1`
  (`spectrum_ringInverse_aeval`) and the resolvent-shaped
  case `q = X` (`spectrum_ringInverse`, the spectrum of
  `Ring.inverse a` is the pointwise inverse of the spectrum
  of `a`, under `0 ∉ spectrum C a`).
* Read-back weld at an owned seat: for a self-adjoint
  tripotent matrix `X` (hypothesis supplied by
  `tripotent_selfadjoint_spectrum`, cited verbatim), the
  spectrum of the rational value `ratEval X 1 (C 2 - X)`
  lies in `{1/3, 1/2, 1}` - a bound no landed theorem
  stated before, derived through the new mapping theorem,
  not by restating the seat's own spectrum.

Named remainder (never silently dropped): SHELF-7b
(continuous / holomorphic spectral mapping in full) stays
gated on SHELF-8a's general contour form, untouched here.
-/

import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.CStarAlgebra.Matrix
import ThetLogos.TRO

namespace ThetLogos

open Polynomial

noncomputable section

variable {A : Type*} [NormedRing A] [NormOneClass A] [NormedAlgebra ℂ A]
  [CompleteSpace A] {a : A}

/-! ## 1. The rational evaluation -/

/-- The rational evaluation of `p / q` at `a`: the numerator
polynomial value times the ring inverse of the denominator
polynomial value (denominator on the LEFT inverse form, so
that cancelling it against scalar multiples needs no
commutation with the inverse). When `aeval a q` is not a
unit, `Ring.inverse` is `0` and this is a junk value; every
theorem below carries the hypothesis that makes it a unit. -/
def ratEval (a : A) (p q : ℂ[X]) : A :=
  Ring.inverse (aeval a q) * aeval a p

/-- Polynomial values at the same element commute. -/
theorem aeval_commute (p q : ℂ[X]) :
    Commute (aeval a p) (aeval a q) := by
  show aeval a p * aeval a q = aeval a q * aeval a p
  rw [← map_mul, ← map_mul, mul_comm p q]

/-- The rational value clears its denominator on the right:
`ratEval a p q * aeval a q = aeval a p` whenever the
denominator value is a unit. -/
theorem ratEval_mul_aeval (p q : ℂ[X]) (hq : IsUnit (aeval a q)) :
    ratEval a p q * aeval a q = aeval a p := by
  rw [ratEval, mul_assoc, (aeval_commute p q).eq, ← mul_assoc,
    Ring.inverse_mul_cancel _ hq, one_mul]

/-- With denominator `1`, rational evaluation is polynomial
evaluation. -/
theorem ratEval_one (p : ℂ[X]) : ratEval a p 1 = aeval a p := by
  rw [ratEval, map_one, Ring.inverse_one, one_mul]

/-! ## 2. The denominator criterion -/

section Nontrivial

variable [Nontrivial A]

/-- The denominator hypothesis, stated exactly: if `eval q`
never vanishes on `spectrum ℂ a`, then `aeval a q` is a
unit. Proved from the pin's polynomial spectral mapping:
`0 ∈ spectrum ℂ (aeval a q)` would be `eval lam q = 0` for
some spectral `lam`. -/
theorem isUnit_aeval_of_eval_ne_zero (q : ℂ[X])
    (hq : ∀ lam ∈ spectrum ℂ a, eval lam q ≠ 0) :
    IsUnit (aeval a q) := by
  rw [← spectrum.zero_notMem_iff ℂ]
  intro h0
  rw [spectrum.map_polynomial_aeval a q] at h0
  obtain ⟨lam, hlam, hlam0⟩ := h0
  exact hq lam hlam hlam0

/-- Conversely, if `aeval a q` is a unit, `eval q` never
vanishes on `spectrum ℂ a`. -/
theorem eval_ne_zero_of_isUnit_aeval (q : ℂ[X])
    (hq : IsUnit (aeval a q)) :
    ∀ lam ∈ spectrum ℂ a, eval lam q ≠ 0 := by
  intro lam hlam hzero
  have h0 : (0 : ℂ) ∈ spectrum ℂ (aeval a q) := by
    rw [spectrum.map_polynomial_aeval a q]
    exact ⟨lam, hlam, hzero⟩
  rw [spectrum.zero_mem_iff ℂ] at h0
  exact h0 hq

/-! ## 3. The rational spectral mapping theorem -/

/-- **Rational spectral mapping.** For `a` in a complex
Banach algebra and polynomials `p q` whose denominator
satisfies the exact hypothesis `eval lam q ≠ 0` at every
`lam ∈ spectrum ℂ a`,
`spectrum ℂ (ratEval a p q)
  = (fun lam => eval lam p / eval lam q) '' spectrum ℂ a`. -/
theorem spectrum_ratEval (p q : ℂ[X])
    (hq : ∀ lam ∈ spectrum ℂ a, eval lam q ≠ 0) :
    spectrum ℂ (ratEval a p q)
      = (fun lam => eval lam p / eval lam q) '' spectrum ℂ a := by
  have hqunit : IsUnit (aeval a q) := isUnit_aeval_of_eval_ne_zero q hq
  have hInv : IsUnit (Ring.inverse (aeval a q)) :=
    isUnit_ringInverse.mpr hqunit
  -- Key identity: for each `mu`, membership of `mu` in the
  -- spectrum of the rational value is the non-unitness of
  -- the polynomial value of `C mu * q - p`. The inverse
  -- cancels against the denominator on the nose (the
  -- scalar `mu` passes through by `mul_smul_comm`), so no
  -- commutation with the inverse is ever needed.
  have key : ∀ mu : ℂ, mu ∈ spectrum ℂ (ratEval a p q)
      ↔ ¬ IsUnit (aeval a (C mu * q - p)) := by
    intro mu
    have hid : algebraMap ℂ A mu - ratEval a p q
        = Ring.inverse (aeval a q) * aeval a (C mu * q - p) := by
      have h1 : aeval a (C mu * q - p) = mu • aeval a q - aeval a p := by
        rw [map_sub, map_mul, Polynomial.aeval_C,
          Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
      show algebraMap ℂ A mu - Ring.inverse (aeval a q) * aeval a p
        = Ring.inverse (aeval a q) * aeval a (C mu * q - p)
      rw [h1, mul_sub, mul_smul_comm, Ring.inverse_mul_cancel _ hqunit,
        Algebra.algebraMap_eq_smul_one]
    rw [spectrum.mem_iff, hid, hInv.mul_left_iff]
  ext mu
  constructor
  · intro hmu
    have hnot : ¬ IsUnit (aeval a (C mu * q - p)) := (key mu).mp hmu
    have h0 : (0 : ℂ) ∈ spectrum ℂ (aeval a (C mu * q - p)) := by
      rwa [spectrum.zero_mem_iff ℂ]
    rw [spectrum.map_polynomial_aeval a (C mu * q - p)] at h0
    obtain ⟨lam, hlam, hlam0⟩ := h0
    have hlam0' : eval lam p = mu * eval lam q := by
      have h := hlam0
      simp only [eval_sub, eval_mul, eval_C] at h
      exact (sub_eq_zero.mp h).symm
    refine ⟨lam, hlam, ?_⟩
    show eval lam p / eval lam q = mu
    exact (div_eq_iff (hq lam hlam)).mpr hlam0'
  · rintro ⟨lam, hlam, rfl⟩
    apply (key _).mpr
    intro hunit
    have h0 : (0 : ℂ) ∉ spectrum ℂ (aeval a (C (eval lam p / eval lam q) * q - p)) := by
      rwa [spectrum.zero_mem_iff ℂ, Classical.not_not]
    rw [spectrum.map_polynomial_aeval a _] at h0
    apply h0
    refine ⟨lam, hlam, ?_⟩
    simp only [eval_sub, eval_mul, eval_C]
    rw [div_mul_cancel₀ _ (hq lam hlam), sub_self]

/-! ## 4. Corollaries: the inverse cases -/

/-- Spectral mapping for the inverse of a polynomial value:
`p = 1` in `spectrum_ratEval`. -/
theorem spectrum_ringInverse_aeval (q : ℂ[X])
    (hq : ∀ lam ∈ spectrum ℂ a, eval lam q ≠ 0) :
    spectrum ℂ (Ring.inverse (aeval a q))
      = (fun lam => (eval lam q)⁻¹) '' spectrum ℂ a := by
  have h := spectrum_ratEval (1 : ℂ[X]) q hq
  rw [ratEval, map_one, mul_one] at h
  refine h.trans (Set.image_congr fun lam _ => ?_)
  simp

/-- Spectral mapping for the inverse of `a` itself:
if `0 ∉ spectrum ℂ a`, the spectrum of `Ring.inverse a`
is the pointwise inverse of the spectrum of `a`. -/
theorem spectrum_ringInverse (h0 : (0 : ℂ) ∉ spectrum ℂ a) :
    spectrum ℂ (Ring.inverse a) = (·⁻¹) '' spectrum ℂ a := by
  have h := spectrum_ringInverse_aeval (X : ℂ[X]) (a := a) (by
    intro lam hlam hzero
    simp only [eval_X] at hzero
    exact h0 (hzero ▸ hlam))
  rw [aeval_X] at h
  simpa using h

end Nontrivial

/-! ## 5. Read-back weld at the TRO seat

`tripotent_selfadjoint_spectrum` is cited verbatim below:
`ThetLogos.tripotent_selfadjoint_spectrum` in
`ThetLogos.TRO`. -/

section TripotentWeld

open scoped Matrix.Norms.L2Operator

/-- Read-back: for a self-adjoint tripotent matrix `M`, the
rational value `1 / (2 - M)` (as `ratEval M 1 (C 2 - X)`)
has spectrum contained in `{1/3, 1/2, 1}`. The seat's own
landed theorem supplies `spectrum ℂ M ⊆ {-1, 0, 1}`, the
denominator `2 - lam` is nonzero at each of those points,
and the new rational mapping theorem transports the bound.
No landed theorem stated this bound before. The matrix
seat carries the L2 operator norm (scoped instances,
opened for this section only). -/
theorem spectrum_ratEval_tripotent {n : ℕ} [Nonempty (Fin n)]
    (M : Matrix (Fin n) (Fin n) ℂ) (hsa : M.conjTranspose = M)
    (htrip : ternaryMat M M M = M) :
    spectrum ℂ (ratEval M (1 : ℂ[X]) (C 2 - X)) ⊆ {1 / 3, 1 / 2, 1} := by
  have hspec : spectrum ℂ M ⊆ {-1, 0, 1} :=
    tripotent_selfadjoint_spectrum M hsa htrip
  have hq : ∀ lam ∈ spectrum ℂ M, eval lam (C 2 - X) ≠ 0 := by
    intro lam hlam hzero
    have hmem := hspec hlam
    simp only [eval_sub, eval_C, eval_X] at hzero
    rw [Set.mem_insert_iff, Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    rcases hmem with rfl | rfl | rfl <;> norm_num at hzero
  rw [spectrum_ratEval (1 : ℂ[X]) (C 2 - X) hq]
  intro y hy
  obtain ⟨lam, hlam, rfl⟩ := hy
  have hmem := hspec hlam
  rw [Set.mem_insert_iff, Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  simp only [eval_one, eval_sub, eval_C, eval_X]
  rw [Set.mem_insert_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
  rcases hmem with rfl | rfl | rfl <;> norm_num

end TripotentWeld

end

end ThetLogos
