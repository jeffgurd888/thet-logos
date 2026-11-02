/-
# SHELF-8b, extension 8B-5 - disc-calculus decomposition at an isolated point

Brick 8B-5 of SHELF-8b (registration
`whitepaper/shelf-8b345-registration-2026-11-02.md`; scoping
`whitepaper/shelf-8b-scoping-2026-11-02.md` SS2, 8B-5
paragraph): the decomposition of the SHELF-8a disc calculus
(`ThetLogos.HolomorphicFunctionalCalculus`) against the
Riesz projection of GATE-A1/GATE-A2 at an isolated spectral
point `lam`. NO CLAIM beyond the theorems below; no dial is
touched.

Content: right-multiply the landed factorisation
`hfcDisc_sub_scalarEval`
(`hfcDisc a c - scalarEval c lam • 1
  = (a - lam • 1) * hfcDisc a (discTail c lam)`)
by `rieszProj a lam r`, and split `hfcDisc a c` against the
complementary projection of 8B-1
(`ThetLogos.RieszComplementary`). The disc radius (here
`Rd`) and the isolation radius (here `Ri`) are DISTINCT
variables throughout: the scoping flags confusing them as
the one clerical risk of this brick, and the isolation
hypotheses `(hR : specIsolatedWithin a lam Ri) (hr : 0 < r)
(hrR : r <= Ri)` are carried on the face of the first
headline even though the rearrangement itself is pure
algebra over the landed factorisation.

Fences on the face:

* The `(1 - P)` term (spelled `rieszComplProj a lam r`) is
  carried UNEVALUATED: no calculus on the complement
  exists, and the identification of `hfcDisc a c * P` with
  any circle-integral local calculus (REM-CIRCLE-ID) is
  NOT part of this brick - that is 8B-3 territory and a
  separate registration.
* K-8B-SCALAR-ONLY stands: the `(a - lam • 1)` term is
  load-bearing; no `f(a) = f(lam) • P` form is stated.
* K-8B-KILLED-FORM binds: nothing here consumes the killed
  form `circleIntegrable_resolvent`; this brick needs no
  integrability at all.

No `sorry`, no `native_decide`.
-/

import ThetLogos.HolomorphicFunctionalCalculus
import ThetLogos.RieszGate
import ThetLogos.RieszGateIdem
import ThetLogos.RieszComplementary

namespace ThetLogos

noncomputable section

variable {A : Type*} [NormedRing A] [NormOneClass A] [NormedAlgebra ℂ A]
  [CompleteSpace A]

variable (a : A)

/-! ## Scalar factor bookkeeping -/

/-- A scalar multiple of `1`, right-multiplied by the Riesz
projection, is the scalar action on the projection:
`(z • 1) * P = z • P`. -/
theorem smul_one_mul_rieszProj (z : ℂ) (lam : ℂ) (r : ℝ) :
    (z • (1 : A)) * rieszProj a lam r = z • rieszProj a lam r := by
  rw [smul_mul_assoc, one_mul]

/-! ## Headline 1: the factorisation right-multiplied by `P` -/

/-- The landed factorisation `hfcDisc_sub_scalarEval`,
right-multiplied by `rieszProj a lam r` (subtraction form).
The disc hypotheses are verbatim those of
`hfcDisc_sub_scalarEval` at disc radius `Rd`; the isolation
hypotheses concern the distinct radius `Ri` and the circle
radius `r`. -/
theorem hfcDisc_sub_scalarEval_mul_rieszProj {Rd Ri : ℝ} (hRd : 0 < Rd)
    {c : ℕ → ℂ} (hc : DiscSummable Rd c) (haRd : ‖a‖ < Rd)
    {lam : ℂ} (hlam : ‖lam‖ ≤ Rd)
    (hR : specIsolatedWithin a lam Ri) {r : ℝ} (hr : 0 < r) (hrR : r ≤ Ri) :
    (hfcDisc a c - scalarEval c lam • (1 : A)) * rieszProj a lam r
      = (a - lam • (1 : A))
        * (hfcDisc a (discTail c lam) * rieszProj a lam r) := by
  have hfact := hfcDisc_sub_scalarEval (a := a) hRd hc haRd hlam
  rw [hfact, mul_assoc]

/-- HEADLINE (8B-5, first form): the disc calculus at `a`,
right-multiplied by the Riesz projection at the isolated
point `lam`, decomposes as the scalar value at `lam` on the
projection plus the `(a - lam • 1)` factor (load-bearing,
K-8B-SCALAR-ONLY) times the tail calculus on the
projection. -/
theorem hfcDisc_mul_rieszProj {Rd Ri : ℝ} (hRd : 0 < Rd)
    {c : ℕ → ℂ} (hc : DiscSummable Rd c) (haRd : ‖a‖ < Rd)
    {lam : ℂ} (hlam : ‖lam‖ ≤ Rd)
    (hR : specIsolatedWithin a lam Ri) {r : ℝ} (hr : 0 < r) (hrR : r ≤ Ri) :
    hfcDisc a c * rieszProj a lam r
      = scalarEval c lam • rieszProj a lam r
        + (a - lam • (1 : A))
          * (hfcDisc a (discTail c lam) * rieszProj a lam r) := by
  have h := hfcDisc_sub_scalarEval_mul_rieszProj a hRd hc haRd hlam hR hr hrR
  rw [sub_mul, smul_one_mul_rieszProj a] at h
  calc hfcDisc a c * rieszProj a lam r
      = (hfcDisc a c * rieszProj a lam r
          - scalarEval c lam • rieszProj a lam r)
        + scalarEval c lam • rieszProj a lam r := (sub_add_cancel _ _).symm
    _ = ((a - lam • (1 : A))
          * (hfcDisc a (discTail c lam) * rieszProj a lam r))
        + scalarEval c lam • rieszProj a lam r := congrArg (· + _) h
    _ = scalarEval c lam • rieszProj a lam r
        + (a - lam • (1 : A))
          * (hfcDisc a (discTail c lam) * rieszProj a lam r) :=
        add_comm _ _

/-! ## Headline 2: the split against the complementary projection -/

/-- Generic split of any element against the Riesz
projection and its complement (`rieszComplProj` is
`1 - P` by definition). No isolation hypothesis: this is
`rieszProj_add_rieszComplProj` / `mul_one` bookkeeping. -/
theorem eq_mul_rieszProj_add (x : A) (lam : ℂ) (r : ℝ) :
    x = x * rieszProj a lam r + x * rieszComplProj a lam r := by
  calc x = x * 1 := (mul_one x).symm
    _ = x * (rieszProj a lam r + rieszComplProj a lam r) := by
          rw [rieszProj_add_rieszComplProj a lam r]
    _ = x * rieszProj a lam r + x * rieszComplProj a lam r := mul_add _ _ _

/-- The same split, stated as a sum collapsing to `x`. -/
theorem mul_rieszProj_add_mul_rieszComplProj (x : A) (lam : ℂ) (r : ℝ) :
    x * rieszProj a lam r + x * rieszComplProj a lam r = x :=
  (eq_mul_rieszProj_add a x lam r).symm

/-- The complementary term, carried unevaluated, is the
difference of the whole and the projected part. -/
theorem hfcDisc_mul_rieszComplProj (c : ℕ → ℂ) (lam : ℂ) (r : ℝ) :
    hfcDisc a c * rieszComplProj a lam r
      = hfcDisc a c - hfcDisc a c * rieszProj a lam r := by
  show hfcDisc a c * (1 - rieszProj a lam r)
    = hfcDisc a c - hfcDisc a c * rieszProj a lam r
  rw [mul_sub, mul_one]

/-- HEADLINE (8B-5, second form): the 8B-1 split of the disc
calculus. The complementary term is carried UNEVALUATED -
no calculus on the complement exists (see the header). -/
theorem hfcDisc_eq_mul_rieszProj_add (c : ℕ → ℂ) (lam : ℂ) (r : ℝ) :
    hfcDisc a c
      = hfcDisc a c * rieszProj a lam r
        + hfcDisc a c * rieszComplProj a lam r :=
  eq_mul_rieszProj_add a (hfcDisc a c) lam r

/-- The two headlines combined: the full three-term
decomposition of `hfcDisc a c` - scalar value on `P`, the
`(a - lam • 1)` tail term on `P`, and the unevaluated
complementary term. -/
theorem hfcDisc_eq_decomp {Rd Ri : ℝ} (hRd : 0 < Rd)
    {c : ℕ → ℂ} (hc : DiscSummable Rd c) (haRd : ‖a‖ < Rd)
    {lam : ℂ} (hlam : ‖lam‖ ≤ Rd)
    (hR : specIsolatedWithin a lam Ri) {r : ℝ} (hr : 0 < r) (hrR : r ≤ Ri) :
    hfcDisc a c
      = scalarEval c lam • rieszProj a lam r
        + (a - lam • (1 : A))
          * (hfcDisc a (discTail c lam) * rieszProj a lam r)
        + hfcDisc a c * rieszComplProj a lam r := by
  calc hfcDisc a c
      = hfcDisc a c * rieszProj a lam r
        + hfcDisc a c * rieszComplProj a lam r :=
        hfcDisc_eq_mul_rieszProj_add a c lam r
    _ = (scalarEval c lam • rieszProj a lam r
          + (a - lam • (1 : A))
            * (hfcDisc a (discTail c lam) * rieszProj a lam r))
        + hfcDisc a c * rieszComplProj a lam r := by
          rw [hfcDisc_mul_rieszProj a hRd hc haRd hlam hR hr hrR]

/-! ## Commutation of the disc calculus with the projection -/

/-- Powers of `a` commute with the Riesz projection (from
the landed `commute_a_rieszProj`). -/
theorem commute_pow_rieszProj (n : ℕ) (lam : ℂ) (r : ℝ) :
    Commute (a ^ n) (rieszProj a lam r) :=
  (commute_a_rieszProj a lam r).pow_left n

/-- Scalar multiples of powers of `a` commute with the
Riesz projection. -/
theorem commute_smul_pow_rieszProj (z : ℂ) (n : ℕ) (lam : ℂ) (r : ℝ) :
    Commute (z • a ^ n) (rieszProj a lam r) := by
  have h := commute_pow_rieszProj a n lam r
  show (z • a ^ n) * rieszProj a lam r
    = rieszProj a lam r * (z • a ^ n)
  rw [smul_mul_assoc, mul_smul_comm, h.eq]

/-- The disc calculus at `a` commutes with the Riesz
projection at any centre and radius: it is a series in `a`,
and `a` commutes with its own projection. -/
theorem commute_hfcDisc_rieszProj (c : ℕ → ℂ) (lam : ℂ) (r : ℝ) :
    Commute (hfcDisc a c) (rieszProj a lam r) := by
  show Commute (∑' n, c n • a ^ n) (rieszProj a lam r)
  exact Commute.tsum_left _ fun n => commute_smul_pow_rieszProj a (c n) n lam r

/-- The commuted product form of the disc calculus against
the projection. -/
theorem rieszProj_mul_hfcDisc (c : ℕ → ℂ) (lam : ℂ) (r : ℝ) :
    rieszProj a lam r * hfcDisc a c = hfcDisc a c * rieszProj a lam r :=
  (commute_hfcDisc_rieszProj a c lam r).eq.symm

/-- The tail disc calculus (the factor in headline 1) also
commutes with the projection. -/
theorem commute_hfcDisc_discTail_rieszProj (c : ℕ → ℂ) (lam : ℂ) (r : ℝ) :
    Commute (hfcDisc a (discTail c lam)) (rieszProj a lam r) :=
  commute_hfcDisc_rieszProj a (discTail c lam) lam r

/-- The tail factor's product with the projection, in
commuted form. -/
theorem hfcDisc_discTail_mul_rieszProj_eq (c : ℕ → ℂ) (lam : ℂ) (r : ℝ) :
    hfcDisc a (discTail c lam) * rieszProj a lam r
      = rieszProj a lam r * hfcDisc a (discTail c lam) :=
  (commute_hfcDisc_discTail_rieszProj a c lam r).eq

/-- Headline 1 in left-multiplied form: the projection times
the disc calculus equals the same decomposition (via
`commute_hfcDisc_rieszProj`). This is still the series-side
identity - no circle-integral local calculus is identified
(REM-CIRCLE-ID is not part of this brick). -/
theorem rieszProj_mul_hfcDisc_eq {Rd Ri : ℝ} (hRd : 0 < Rd)
    {c : ℕ → ℂ} (hc : DiscSummable Rd c) (haRd : ‖a‖ < Rd)
    {lam : ℂ} (hlam : ‖lam‖ ≤ Rd)
    (hR : specIsolatedWithin a lam Ri) {r : ℝ} (hr : 0 < r) (hrR : r ≤ Ri) :
    rieszProj a lam r * hfcDisc a c
      = scalarEval c lam • rieszProj a lam r
        + (a - lam • (1 : A))
          * (hfcDisc a (discTail c lam) * rieszProj a lam r) := by
  rw [rieszProj_mul_hfcDisc a c lam r]
  exact hfcDisc_mul_rieszProj a hRd hc haRd hlam hR hr hrR

end

end ThetLogos
