# The Spectral Chamber Former — gauntlet dossier (2026-10-25)

**Status: EXHIBIT / INSTRUMENT. NO CLAIM.** A working design instrument in the
macroscope line, built at Jeff Gurd's commission ("imagine using the rapid
forming on a spectral metric reflective variable geometry spectral resonance
chamber" — the ICAD homage: design knowledge encoded as rules, geometry
generated from them, the spectrum as the grade). Proves nothing; measures
truly. Live at `exhibits/spectral-chamber-former/`.

## What it is

A knowledge-based former over a 2D reflective cavity family (superellipse
|x/a|^p + |y/b|^p ≤ 1, p ∈ [2,6], boundary ripple r ∈ [0, 0.15], k lobes),
with the design rules carried as data and enforced on every candidate. Each
candidate's mode spectrum is computed from a finite-difference Dirichlet
Laplacian; a seeded search rapid-forms the chamber whose gap ratios
(λᵢ/λ₁, i = 2..6) best match a chosen TARGET HUM — the harmonic ladder
(2,3,4,5,6) or the clock chord (the measured optical-clock ratios entered
2026-10-25 as T4 input, used here as a target SHAPE only).

## Gauntlet results (bench, Brick A; page, Brick B — FULL)

- **Solver verified:** rectangle test vs the exact discrete spectrum —
  max relative error **1.2×10⁻¹⁵** over λ₁..λ₈. Continuum square λ₁ error
  shrinks 1.43×10⁻³ → 6.34×10⁻⁴ under refinement (factor 2.249; O(h²)
  predicts 2.25). Eigen-residuals ≤ 1.0×10⁻¹¹ relative. Search deterministic.
- **Rules bite:** an out-of-rules candidate is rejected with named
  violations (aspect, p-range, ripple bounds, wall clearance).
- **The harmonic floor (the headline result):** best achievable mismatch
  to the ladder is **≈ 0.0657** RMS-log, measured four independent ways
  (two optimizers, a 5× budget run, 600 random chambers). Achieved ratios
  ≈ (2.157, 2.872, 3.725, 4.597, 5.751). Within the commissioned family,
  a 2D room cannot hum a 1D string's ladder — the floor is the family's,
  and it is printed on the exhibit's face.
- **Clock chord:** bench mismatch **0.533** — the measured ratios sit below
  this family's λ₂/λ₁ reach. Reported, not rounded.
- **Isospectral twin FOUND:** a smooth (p≈2.0, k=0) chamber and a rippled
  (p≈3.1, k=4) chamber, parameter distance 0.829, matching within 2% —
  the page's Twin check reproduces the phenomenon live (distance 1.214,
  identical Match 0.0751 on the page grid). A spectrum does not pick a shape;
  the exhibit demonstrates it instead of asserting it.
- **Page verification (Brick B, FULL):** script parses, 26/26 element ids,
  Form chamber reaches Match 0.0751 in exactly its 80-evaluation budget on
  the printed 23×23 grid; slider changes move λ₁ as expected; the word
  "gravity" appears nowhere on the page.

## Fences

Exhibit tier throughout. The finite grid is a picture of the mathematics,
labeled with its grid size. No theorem is claimed, no dial moves, and the
spectral-trap vision's killed payload stays killed — this is a chamber that
hears resonances, built as an instrument, nothing more.
