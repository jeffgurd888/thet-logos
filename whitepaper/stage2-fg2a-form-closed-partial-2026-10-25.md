# FG-2a — Closedness of the completed −log form — PARTIAL (top of band)

*Landed 2026-10-25. Module `ThetLogos.LatticeSliceFormClosed`
(78 strict / 14 defs). Parent-verified: targeted build exit 0, olean
present, zero `sorry`/`admit`, `#print axioms` on the package
theorems returns exactly [propext, Classical.choice, Quot.sound].
Program census after landing: 5,368 strict / 177 counted modules.*

## Placement

Stage 2 completeness work (frontier-gate §2.2, FG-2 line). Fixed
volume, fixed lattice. **Not frontier progress; Items 3/4 untouched.
NO CLAIM. Dials 0/4.**

## What stands (T1)

Under exactly the standing hypothesis `SliceHPosOne`, at general
(G, ρ) and every real β (`0 < d` only for the weld clause):

1. **Closedness in full.** `sliceFormDomain` — the finiteness domain
   of the completed form `sliceHamFormC`, equipped with the form
   inner product ⟪x,y⟫ + `sliceFormB x y` — is complete in the form
   norm (instance `sliceFormDomainCompleteSpace`). The engine is
   `sliceFormClosed_lim`: a form-Cauchy sequence converging in the
   ambient space has its limit back in the domain with the form
   bound, derived from uniform-in-K approximant bounds via
   continuity of each `q_K` (the defect realized as the CLM
   `1 − T̂_c`) and the landed domain characterization. Nothing about
   the limit's form value is assumed. This is closedness in exactly
   the sense the Friedrichs / Kato first representation theorem
   consumes.
2. **Continuous inclusion.** The carrier map into the ambient
   Hilbert space is a CLM of bound 1
   (`sliceFormInclusion`, ‖x.val‖ ≤ ‖x‖_form).
3. **Weld clause.** `q₁(embed x) = ‖x‖² − ‖W x‖²` at K = 1 on
   quotient vectors, consuming the S2-5 weld interface identity.

Specializations: the U(1) seat package (hypothesis-free at β ≥ 0)
and the β = 0 package (domain = ⊤, inclusion surjective, dense
range).

## The density clause — resolved, mostly negatively (T1)

The charter asked for dense range of the inclusion "where the
record supports it." The record supports a sharp answer:

* **Obstruction (theorem, not a gap).** For every `x` in the form
  domain and every `w` with `T̂_c w = 0`: ⟪x, w⟫ = 0
  (`sliceFormDomain_orthogonal_ker`). Proof idea: on kernel
  vectors the approximant forms are harmonic sums,
  `q_K w = H_K ‖w‖²` with `H_K → ∞`, and Cauchy–Schwarz against a
  finite-form `x` forces the pairing to vanish. Hence
  **dom(form) ⊆ (ker T̂_c)^⊥ always** — dense range in the ambient
  space is *disproved* wherever ker T̂_c ≠ 0. This is the correct
  physics, formalized: states annihilated by one transfer step
  carry infinite −log energy.
* **Dense at β = 0** (there T̂_c = id, ker = 0, domain = ⊤).
* **Open residue, named:** density of the domain inside
  `(ker T̂_c)^⊥` at general β. Missing ingredient, named exactly:
  a form-bounded truncation / polynomial functional calculus for
  `T̂_c` giving `T̂² ≤ T̂` in form order. This residue is FG-2b's
  step 0.

## What this is not

No Friedrichs operator (FG-2b), no semigroup identification
(FG-2c), no positivity beyond landed labels, no uniformity, no
continuum object. The form is closed; the Hamiltonian does not yet
exist as an object.
