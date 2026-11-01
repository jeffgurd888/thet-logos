# SHELF-8a LANDING — 2026-11-01

## Holomorphic functional calculus: PARTIAL at the pre-registered seam (working label: SHELF line)

**Module:** `ThetLogos.HolomorphicFunctionalCalculus` —
strict 34 / defs 6, parent-verified (independent count,
main-tree build, headline axiom checks on exactly
`[propext, Classical.choice, Quot.sound]`).

**Census at this landing: 10,691 strict / 10,768 total /
360 modules, zero sorrys.**

Shelf discipline: stock GRADE-1 gaps only — world
mathematics the house did not own, formalized to house
grade. The pin does not move; NO CLAIM; no dial touched.

## The probe (the gap, verified in this tree's pin)

Mathlib v4.35.0-rc3 owns: the continuous functional
calculus for *normal* C*-algebra elements only (`cfc` /
`cfcHom`); `spectrum` / resolvent API; spectral radius and
the Gelfand formula; polynomial spectral mapping; the
normed Cauchy product; circle integrals and the
Banach-valued Cauchy integral formula. It owns **no
holomorphic functional calculus and no Dunford material**
(`Dunford` in the pin is the finite-dimensional Jordan–
Chevalley decomposition and one unrelated measure file).
That absence is what this brick stocks — cited and
consumed where owned, never rebuilt (K-SHELF-RENAME
respected throughout).

## What landed — the disc fragment, in full

For a complete complex normed algebra `A` (with
`NormOneClass A`) and coefficients `c : ℕ → ℂ` summable
against a disc of radius `r ≥ ‖a‖` (`DiscSummable r c`):

- `hfcDisc a c := ∑' n, c n • a ^ n` — the power-series
  (disc) functional calculus, with its norm bound
  (`hfcDisc_norm_le`).
- Values: zero, constants (`hfcDisc_const`: the unit,
  scaled), monomials (`hfcDisc_monomial`: `a ^ n`), and
  **polynomial agreement** (`hfcDisc_polynomial`:
  `hfcDisc a (fun n => p.coeff n) = Polynomial.aeval a p`)
  — the calculus extends the elementary polynomial one.
- **Homomorphism rules:** `hfcDisc_add`, `hfcDisc_smul`,
  and `hfcDisc_mul` (multiplication is disc convolution
  `discConv`; its summability is proved through the pin's
  normed Cauchy product) — plus commutation
  (`commute_a_hfcDisc`, `commute_hfcDisc_hfcDisc`) and the
  exponential (`hfcDisc_exp`: the calculus of the
  exponential series is `NormedSpace.exp a`).
- **Spectral mapping at two grades:** FULL for
  polynomials (`spectrum_hfcDisc_polynomial`, transferred
  from the pin's `spectrum.map_polynomial_aeval`), and
  the **forward inclusion** for the disc fragment
  (`scalarEval_mem_spectrum`: if `λ ∈ spectrum ℂ a` then
  the scalar series value at λ lies in
  `spectrum ℂ (hfcDisc a c)`), proved through the
  factorization identity `hfcDisc_sub_scalarEval`
  (`f(a) − f(λ)·1 = (a − λ·1)·(tail value)`).

## The named remainder (on the module's face)

The **general contour (Dunford–Riesz) definition** and
contour-system independence; the reverse spectral
inclusion for the disc fragment; sharpening the scale
hypothesis from `‖a‖ ≤ r` to `spectralRadius ℂ a < r`;
the bundled `AlgHom` package; the identification of
`hfcDisc` with the circle integral of `f · resolvent`.
**SHELF-8b (Riesz projections) still gates on the
general form** — it does not fire off this fragment; the
shelf rotation continues to SHELF-12.

One build note, disclosed on the module's face: a scoped
`set_option maxHeartbeats 1600000 in` on one proof
(`norm_discTail_le`; house precedent exists) — statements
unaffected; the axiom sweep is the certification.

## Backers since last landing

The backer roll (`BACKERS.md`) is unchanged since the last
landing; no new confirmed gift is on the record. Thank you
to everyone reading the stream — the corpus is free for
everyone, forever.

*End of dossier.*
