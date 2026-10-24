# Toy Atom — verdict note (2026-10-23)

Commissioned by Jeff 2026-10-23 ~21:25 EDT ("build the atoms own
spectrum") under the Three Empty Rooms charter, Digital Chemistry
door 1. Charter + verdict rule registered BEFORE computing:
`~/workspace/toy-atom-scratch/CHARTER.md`. Script and raw results:
`~/workspace/toy-atom-scratch/toy_atom.py`, `toy-atom-results.json`.

## Verdict: RHYME — the door-frame holds

The toy: s-wave radial hydrogen, finite-differenced
(H u = −½u″ − u/r, u(0)=u(80)=0, atomic units), grids of
200 / 400 / 800 interior points, sparse diagonalization.

Levels converge on the exact hydrogen ladder −1/(2n²):

| grid | worst relative error, n ≤ 4 |
|------|------------------------------|
| 200  | 3.68% |
| 400  | 0.98% |
| 800  | 0.25% |

Error shrinks ~×4 per doubling — clean second-order convergence.

Line wavelengths at the finest grid vs the real atom (vacuum values):

| line | toy (nm) | real (nm) | off by |
|------|----------|-----------|--------|
| Lyman-α (2→1) | 121.880 | 121.567 | 0.26% |
| Lyman-β (3→1) | 102.801 | 102.572 | 0.22% |
| Lyman-γ (4→1) | 97.459 | 97.254 | 0.21% |
| Balmer-α (3→2) | 656.703 | 656.461 | 0.04% |
| Balmer-β (4→2) | 486.388 | 486.269 | 0.02% |

Every clause of the pre-registered rule passed.

## The fence, at the same volume

This is the numerical method working on the REAL hydrogen
Hamiltonian — agreement is what finite differences are for. It is
NOT a derivation of any spectrum from thet primitives; the derived-
measured-number dial stays at 0 of 4, and the Digital Chemistry room
holds exactly one TOY chair, labeled as such: a working finite
spectrum machine whose gaps check against the real atom's lines,
plus a verified comparison harness for whatever sits in the room
next. NO CLAIM on anything beyond that.
