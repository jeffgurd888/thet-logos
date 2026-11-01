# SHELF-7a LANDING DOSSIER — 2026-11-01

**Item:** SHELF-7a (spectral mapping, polynomial/rational), per
the SHELF rotation and the coordinator's probe-first pack
(`pack-shelf-7a.md`). The builder's handoff was not delivered to
the coordinator session; the landing is processed from the
module's on-face probe record and disk build/axiom logs (the
house delivery-slip pattern — disk is authoritative), with the
parent build re-run in the main tree.

**Status: FULL — the probed gap was genuine and is closed.**
Probe verdict: polynomial spectral mapping is owned (the pin's
`spectrum.map_polynomial_aeval` for general Banach-algebra
elements; SHELF-8a's disc-fragment mapping). **Rational spectral
mapping was owned nowhere** — no inverse/rational form in the pin
(full-tree grep), none in the shelf. That gap is this brick.

**Artifact:** `lean/ThetLogos/SpectralMapping.lean` — strict 9,
defs 1. Verified by the coordinator in the main tree (build green,
3543 jobs); all 7 axiom prints on exactly
`[propext, Classical.choice, Quot.sound]`.

## What landed

- `ratEval a p q` — the rational value, defined honestly: the
  `aeval a p * (aeval a q)⁻¹`-form, legitimate exactly when the
  denominator is a unit; every theorem carries its denominator
  hypothesis explicitly.
- The denominator criterion: `eval q` nonvanishing on
  `spectrum ℂ a` ⟺ `aeval a q` is a unit (both directions, from
  the pin's polynomial mapping).
- `spectrum_ratEval` — the headline: the full rational spectral
  mapping equality, proved by reducing membership in
  `spectrum ℂ (ratEval a p q)` to the polynomial `p − C μ * q`
  having a root in `spectrum ℂ a` — no eigenvalues, no Jordan form.
- Corollaries: `spectrum_ringInverse_aeval` (the p = 1 inverse
  case) and `spectrum_ringInverse` (the resolvent-shaped case:
  spectrum of `Ring.inverse a` = pointwise inverse of the
  spectrum, under `0 ∉ spectrum ℂ a`).
- Read-back weld at an owned seat: for a self-adjoint tripotent
  matrix X (via the landed `tripotent_selfadjoint_spectrum`, cited
  verbatim), `spectrum ℂ (ratEval X 1 (C 2 − X)) ⊆ {1/3, 1/2, 1}`
  — a bound no landed theorem stated before, derived through the
  new mapping theorem.

## Fences

SHELF-7b (continuous/holomorphic spectral mapping in full) stays
gated on SHELF-8a's general contour form — untouched here, as
registered. NO CLAIM — no Millennium problem is claimed solved or
advanced. Dials 0/4.

**Census after landing: 10,847 strict / 10,951 total / 366 counted
modules; zero `sorry` terms tree-wide.**

## Backers since last landing

None new on the record since the last landing.
