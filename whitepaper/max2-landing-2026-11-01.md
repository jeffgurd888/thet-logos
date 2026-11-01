# MAX-2 LANDING — 2026-11-01

## Assembly at general N: FULL — the MAX-2 gate is OPEN (working label: MAX line)

**Module:** `ThetLogos.MaxwellQuadAssembly` — strict 27 /
defs 0, parent-verified (independent count, main-tree
build, headline axiom checks on exactly
`[propext, Classical.choice, Quot.sound]`).

**Census at this landing: 10,437 strict / 10,514 total /
355 modules, zero sorrys.**

MAX-2 is the MAX line's integration point: the finite
Maxwell quadratic operator, assembled at general N from
the MAX-0 pin's definitions and MAX-1's weld and atom. All
five of its registered contents are discharged in the
pin's exact forms. **Its landing opens the MAX-2 gate:
GR-GEO-2, GR-PROP-1, and REM-2 — the three
gravity-vocabulary seats that were hard-gated on it — are
unblocked and in build.**

## What was discharged

- **The operator, read pointwise** (`maxwellOp_apply`):
  `(maxwellOp N θ) ℓ = ∑ P ∈ allPlaqData N, plaqSign P ℓ *
  plaqAngle P θ` — the pin's polarization definition made
  computable; with the bilinear polarization identity
  (`maxwellOp_form`), its symmetry (`maxwellOp_form_symm`
  — coordinate self-adjointness), and its diagonal
  (`maxwellOp_form_self`).
- **(M1) `maxwellM1_proved`** — the form identity
  `⟪θ, maxwellOp N θ⟫ = maxwellQuad N θ` and positivity
  `0 ≤ ⟪θ, maxwellOp N θ⟫`, exactly as registered.
- **(M2) `maxwellM2_proved`** — **the kernel is exactly the
  flat link angles**: `maxwellOp N θ = 0 ↔ ∀ P ∈
  allPlaqData N, plaqAngle P θ = 0`. This iff was failable
  by design — it dies if the pin's plaquette enumeration
  misses a class. **It holds as registered**: the forward
  direction reads flatness off the vanishing sum of
  squares; no enumeration class was missing and nothing
  was repaired.
- **(M3) `maxwellM3_proved`** — gauge modes are flat:
  `plaqAngle P (gaugeAngle φ) = 0` for every P, by additive
  telescoping over the four edges' head/tail corners;
  corollary `maxwellOp_gaugeAngle : maxwellOp N
  (gaugeAngle φ) = 0` (through M2) — the gauge modes lie
  in the operator's kernel, as the corrected REM closure
  and the vocabulary lines consume it.
- **The Wilson tie, as bounds only** (`wilson_cos_bounds`,
  `wilson_tie_plaqAngle`): for `|φ| ≤ 1`,
  `(1/4)φ² ≤ 1 − cos φ ≤ (1/2)φ²`, and the same at
  `φ := plaqAngle P θ`. The quadratic form is tied to the
  Wilson weight's per-plaquette term by two-sided bounds —
  **never** by an equality of actions (proved via the
  half-angle identity and Mathlib's sine estimates).

**K-MAX-1 re-checked at the landing:** `maxwellOp` as
landed is the pin's own polarization definition on the
link-angle space, its form identity proved for this
definition directly; it is not definitionally the transfer
operator, the plaquette block/factor, `magLin`, or the
vertex `lapLin`, and its form is not `osForm`. **K-MAX-2
fence audit:** "Lorentzian"/"bridge" occur only inside the
module's fence sentence; "continuum", "signature",
"dispersion" occur nowhere.

## What this landing is not

The operator's assembly and its kernel — finite algebra at
general N, spacing 1. Not a spectrum (MAX-3's finite
spectrum and gap `4·sin²(π/N)`, labeled finite there, are
still owed), not a photon (OP-1's is a disjoint object),
not a continuum or gravity statement of any kind. The
three seats its gate opens are vocabulary seats — the
corpus becomes able to *state* more of the gravity
questions precisely; nothing is thereby answered. Dial 2
= 0; NO CLAIM; dials 0/4.

Next on the line: MAX-3 (the cube spectrum, L) — the
claims registry's last verdict brick, gating GR-PROP-2.

## Backers since last landing

The backer roll (`BACKERS.md`) is unchanged since the last
landing; no new confirmed gift is on the record. Thank you
to everyone reading the stream — the corpus is free for
everyone, forever.

*End of dossier.*
