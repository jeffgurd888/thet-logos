# Toy periodic table, block 1 (Z = 1–36) — verdict, 2026-10-23

Commissioned by Jeff ("make the toys run through the periodic table for
correlations"); charter + verdict rule registered before computing in
`~/workspace/toy-atom-scratch/PERIODIC-CHARTER.md`. Run completed
2026-10-23 ~22:24 EDT. Results: `toy-periodic-results.json`.

## Verdict: NO CORRELATION

- Pearson r = −0.248; Spearman ρ = −0.140 (registered bar for HOLDS:
  ρ ≥ 0.90 and r ≥ 0.85; PARTIAL bar ρ ≥ 0.75 — both missed by a wide
  margin).
- Partial pattern only: toy maxima at He, Ne, Kr (3 of the 4 noble-gas
  slots), minima at Li, Na — but the potassium drop is missing and the
  magnitudes fail outright: toy IEs inflate with Z (Ne 149 eV vs real
  21.6; Fe 466 vs 7.9).

## Diagnosis (mechanical, on the record)

The single fixed screening length (1 bohr for every element) cannot
represent shell structure. Real core screening switches over the core
radius, which shrinks like 1/Z; the toy's valence levels therefore sit
far too deep, the deeper the heavier the element, and the sawtooth is
drowned by the inflation. The toy atom (Z = 1, where no screening
exists) is unaffected by this failure.

## Doors

1. Run the same toy out to Z = 118 unchanged — completes the table
   under the registered protocol; expected to extend the failure.
2. Fix the toy first (screening length set by the core scale, an a
   priori choice, still no fit to IE data), re-run the WHOLE table
   once, one verdict.
Jeff's call. NO CLAIM either way; derived-number dial unmoved.
