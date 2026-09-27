---
title: "The Three-Generation Map: Complete Order-One Classification of the Finite Spectral Triple"
author: "Jeffrey Gurd"
affiliation: "Nexus Research (independent research)"
date: "2026-09-27"
version: "v1.0"
status: "Research report. Numerical results (T4) unless marked machine-proven (T3). Not peer-reviewed."
---

# The Three-Generation Map

## Complete Order-One Classification of the Finite Spectral Triple

## Abstract

We report the complete classification of the order-one nullspace of the
finite spectral triple Dirac operator for three generations
(H_F = C^96 = C^32 x C^3). The order-one condition [[D_F, pi(a)], pi deg(b)]
= 0 admits a 402-real-dimensional space of Dirac operators: 3 x 46
generation-diagonal plus 3 x 88 generation-mixing directions (residuals
~10^-15). Every direction is classified by support, species, and generation
structure. Applying charge conservation and one-Higgs minimality selects
84 directions: 4 x 18 Yukawa plus 12 Majorana — exactly the Standard Model
flavour parameter count. The triplication is imposed, not derived; flavour
structure is input. Order-one admits; physics selects; the count matches.

## 1. The framework

The finite spectral triple (A_F, H_F, D_F, J, Gamma) with
A_F = C (+) H (+) M_3(C) encodes the Standard Model's internal geometry.
Two consistency conditions govern the Dirac operator:

- **Order-zero:** [pi(a), pi deg(b)] = 0 — the left and right actions commute.
- **Order-one:** [[D_F, pi(a)], pi deg(b)] = 0 — the Dirac operator is a
  first-order differential operator in the noncommutative sense.

Machine-proven in Lean 4 (T3): order-zero for all 144 selected generator
pairs, the KO signs (J^2 = 1, J Gamma = -Gamma J), full unitality, and
order-one for the imposed one-generation Dirac ansatz (all 144 pairs, zero
sorrys). The Dirac ansatz itself — the five-block Yukawa/Majorana structure —
is imposed as physical input, not derived.

## 2. One generation: 46 directions

Scanning the full 24-real-dimensional generator algebra (T4 numerical), the
admissible Dirac space is 272 real-dimensional, and the order-one nullspace
is 46-dimensional. Classified (DIRECTIONS_36.md):

| Family | Real dims | Fate |
|---|---|---|
| SM Yukawa + Majorana | 10 | selected (physical input) |
| Flipped Yukawas | 8 | shelved (one-Higgs minimality) |
| Exotic Majorana | 28 | 27 killed by charge conservation |

Structural invariants: C-block numerically zero; B = conj(A); the 36 extras
are grading-odd, J-compatible, self-adjoint — genuine order-one directions,
not artifacts. Verdict: order-one does not select the SM; it admits a
46-dimensional space in which the SM's 10 directions sit.

## 3. Triplication: C^96 and the 402 census

Imposing three generations, H_F = C^32 (x) C^3, with arbitrary 3x3 complex
Yukawa matrices (Y_nu, Y_e, Y_u, Y_d) and a symmetric 3x3 Majorana matrix:

- Admissible Dirac space: **2352** real dimensions (= 3 x 272 + 3 x 512).
- Order-one nullity: **402** = 3 x 46 (diagonal) + 3 x 88 (mixing).
- Verified over 3 random trials: grading-oddness, self-adjointness,
  J-compatibility, and order-one all return exact zeros (residuals ~10^-15);
  the tests are non-vacuous (probed commutators of order ~17-19).

The count 402 — not 9 x 46 = 414 — confirms the mixing structure is
nontrivial: generation-mixing is constrained differently than naive
triplication would suggest.

## 4. Classifying the 264 mixing directions

Per unordered generation pair, the 88 real mixing dimensions form a direct
sum of slot-disjoint subspaces (joint projection residual 4.7 x 10^-15):

| Family | Real dims | Complex | Fate |
|---|---|---|---|
| SM-like mixing | 18 | 8 Yukawa + 1 MR | **survives** |
| Flipped Yukawa mixing | 16 | 8 | shelved (one-Higgs minimality) |
| Exotic Majorana mixing | 54 | 27 | **killed by charge conservation** |

The 18 SM-like mixing directions per pair are the off-diagonal entries of
the flavour matrices — the CKM/PMNS-type directions. Structural facts:
B = conj(A) exactly; C = 0 forced; colour locking holds in all sectors;
E-symmetry drops in the mixing sector (max ||E - E^T|| = 1.15, vs exactly 0
in one generation) with an "L-shaped" support of 28 entries. Direct
order-one recheck: max residual 1.62 x 10^-15 over 88 x 576 pairs.

No genuinely new structures appear: the mixing classification is the
one-generation verdict crossed with 3x3 flavour. Yukawa parameters double
via (g,g')/(g',g) ordering (16 -> 32); the Majorana sector relaxes (30 -> 56).

## 5. The selection: 84

| Sector | Directions | Count |
|---|---|---|
| Diagonal SM (3 x 10) | Yukawa + Majorana per generation | 30 |
| Mixing SM-like (3 x 18) | off-diagonal flavour entries | 54 |
| **Total selected** | | **84** |

84 = 4 x 18 (four 3x3 complex Yukawa matrices) + 12 (symmetric 3x3 M_R) —
**exactly the Standard Model flavour parameter count.** Order-one admits 402;
charge conservation plus one-Higgs minimality selects 84; the Standard Model
uses 84.

## 6. Numerical rigor

- All residuals at or below ~10^-14; direct rechecks at ~10^-15.
- Two measurement artifacts were caught and corrected by an independent
  verification script before publication (sector-rank overlap bug; complex
  pattern construction bug). Corrected values are recorded with notes;
  uncorrected numbers are not trusted.
- Brute-force 96x96 enumeration was used where structural reduction was
  unavailable; the user authorized brute force explicitly.

## 7. Honesty ledger

| Claim | Tier | Status |
|---|---|---|
| Order-zero, 144/144 pairs | T3 | machine-proven (Lean 4, zero sorrys) |
| Order-one, one-gen ansatz | T3 | machine-proven (Lean 4, zero sorrys) |
| 46-dim nullspace, one gen | T4 | numerical (full 24-generator scan) |
| 402-dim nullspace, three gen | T4 | numerical (3 random trials) |
| 264-direction classification | T4 | numerical (residuals ~10^-15) |
| Triplication to 3 generations | imposed | not derived from the axioms |
| Flavour structure (CKM/PMNS) | input | not derived; arbitrary matrices |
| "Order-one selects the SM" | false | order-one admits; physics selects |

## 8. Next steps

1. Composition theorem for thet-language v2 (order-one analog for composed
   thet events), precisely stated — K3.
2. Second instantiation of the repeat operator R beyond the finite triple — K1.
3. Spectral action / EFT over the selected 84-direction space.
4. Pre-registered harmonic series for one mass ratio, or permanent quarantine
   of the mass-ratio program — K2.

*Repository: github.com/jeffgurd888/thet-logos. Reports: attack4_corrected/
DIRECTIONS_36.md, THREE_GEN.md, MIXING_264.md. Lean sources:
lean/ThetLogos/MartinettiRep.lean, ThreeGen.lean.*
