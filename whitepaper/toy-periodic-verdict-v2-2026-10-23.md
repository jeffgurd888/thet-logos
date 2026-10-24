# Toy periodic table v2 (Hartree toy, whole table) — verdict, 2026-10-23

Jeff's ruling: "Fix the toy first, then run the whole table once."
Fixed toy registered in `PERIODIC-CHARTER-AMENDMENT.md` (spherical
Hartree; screening cloud counted at Z − 1 electrons — the bring-up
correction that restored the hydrogen anchor). Run: Z = 1..118, all
rows computed (a runtime restart killed the first pass at Z = 77;
rows were preserved in the log and a resume job finished the table).
Results: `toy-periodic2-results.json`.

## Verdict: NO CORRELATION

Registered bar (unchanged): Spearman ρ ≥ 0.90 AND Pearson r ≥ 0.85
over the measured rows. Scored over the 101 measured rows as they
stand: **Pearson 0.252, Spearman 0.403**, median |error| 1.56 eV.
Both bars missed by a wide margin.

## What the run actually shows (diagnostics — NOT the verdict)

- **48 of 118 rows never converged** in the 14-round cap, concentrated
  exactly in the open d- and f-shell blocks (Sc–Zn, much of the 4d and
  lanthanide rows, actinides, superheavies): the self-consistency loop
  oscillates — near-degenerate shells (3d/4s, 4f/5d/6s) swap order
  every round and the potential sloshes. Those rows' values are
  whichever phase the oscillation stopped in (e.g. Re 17.6 vs real
  7.8). Iron is one of them: the 7.896 "hit" quoted during spot checks
  was a non-converged row landing on the real number by phase. It is
  corrected here, on the record.
- The **61 converged measured rows** score Pearson 0.864 / Spearman
  0.621, median |err| 0.93 eV — better, still under the bar.
- The **sawtooth skeleton is present** in the raw series: toy maxima
  at noble gases 2, 10, 18, 36, 54 (radon missed) and minima at the
  alkali starts 3, 11, 19, 37, 55. The pattern exists; the magnitudes
  in open-shell and heavy rows destroy the scored correlation.
- Even converged heavy rows drift systematically shallow (Xe 5.7 vs
  12.1; Hg 4.5 vs 10.4; Kr 8.2 vs 14.0; Au 3.8 vs 9.2) — the disclosed
  missing physics (exchange, relativity) is not a footnote at high Z,
  it is the dominant error.

## Standing

The Chemistry room's TOY shelf now holds: the toy atom (stands, at
its registered bar) and two full-table runs, both **NO CORRELATION**
under their registered rules. Standard remedies exist (occupation
smearing + stronger damping for the oscillation; exchange for the
heavy-row shallowness) — any of them is a NEW registered run, Jeff's
call, not a repair of this one. NO CLAIM; derived-number dial
unmoved.
