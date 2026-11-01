# SHELF-1c LANDING DOSSIER — 2026-11-01

**Item:** SHELF-1c (analytic semigroups / sectorial), per the
SHELF rotation and the coordinator pack (`pack-shelf-1c.md`).

**Status: PARTIAL at the pre-named seam.** The bounded/finite
seat landed in full — stronger than the registered sector form —
and the unbounded sectorial theory is the named open seam
(missing pin API, below).

**Artifact:** `lean/ThetLogos/AnalyticSemigroup.lean` — strict 23,
defs 1. Verified by the coordinator in the main tree (build green,
2849 jobs); all 10 headlines on exactly
`[propext, Classical.choice, Quot.sound]`.

## What landed (bounded seat, complex Banach space)

`cexpSemigroup A z := NormedSpace.exp (z • A)` for bounded
`A : E →L[ℂ] E`:

- **Entire extension** (at this seat, stronger than a sector):
  group law for all z, w : ℂ; two-sided inverse at −z; growth
  bound `‖cexpSemigroup A z‖ ≤ Real.exp (‖z‖ * ‖A‖)` in every
  direction.
- **Holomorphicity:** `hasDerivAt_cexpSemigroup` (derivative
  `cexpSemigroup A z * A`), differentiability and analyticity
  everywhere (`analyticAt_cexpSemigroup`).
- **Read-backs, stated exactly:** `A` intertwines the extension;
  the extension is surjective (range = all of E); the orbit form
  of the derivative at every x (domain = all of E at this seat);
  real-axis additivity and norm bound (no contraction claimed —
  `A` is not assumed `DissBound`); resolvent exterior facts
  (`‖A‖ < ‖λ‖ ⇒ λ ∈ resolventSet ℂ A`; resolvent → 0 along the
  cobounded filter, all directions). Finite-dimensional ℂ seats
  are instances of the bounded seat — stated on the face.

## The seam (PARTIAL, named exactly)

Unbounded sectorial operators proper, fractional powers of such
operators, maximal regularity — NOT landed. Missing API in the pin
(v4.35.0-rc3): no `sectorial` definition or sectorial
resolvent-estimate lemma (grep over `Mathlib/Analysis`: nothing);
no analytic-semigroup definition for unbounded generators; no
operator `cpow`/`rpow` API. Corpus-side: SHELF-1a's
`HasGen`/`genDom` dialect is real-scalar only, so there is no
complex unbounded-generator vocabulary to state the theory in.
Also on the record: SHELF-1a's Laplace resolvent integral formula
remainder is untouched by this brick (still open, as registered).

## Fences

NO CLAIM — no Millennium problem is claimed solved or advanced.
Dials 0/4.

**Census after landing: 10,870 strict / 10,975 total / 367 counted
modules; zero `sorry` terms tree-wide.**

## Backers since last landing

None new on the record since the last landing.
