# Brick β2-0 — The Column Obstruction, as a Theorem

*Landing dossier, 2026-10-26. Module:
`lean/ThetLogos/PlaneCrossingColumn.lean` (strict 22, defs 8,
zero `sorry`, zero `native_decide`; main-tree build green,
3,400 jobs, parent-verified). **Parts of the Clay Yang–Mills
statement closed by this landing: 0.** This module proves a
negative about a sub-object; the sign of `layerKernel` 𝒜
itself is untouched, and (H-PF) at general (G, ρ) remains
L+/open.*

## What landed

- **(F) The column factorization** — `exp(−layerAction)` is,
  pointwise in the stratum, the product over columns of
  `columnKernel` factors, each column's density identified as
  the word density of β1's word.
- **(N) The negative theorem** — `columnKernelSym_not_psd`:
  the symmetrized single-column kernel is **not** positive
  semidefinite. Witness, exact and minimal: the group
  `Multiplicative (ZMod 2)` with its sign character, β = 1,
  the weld factor frozen at the element of trace −1. The
  kernel is exactly `[[e^{−2}, 1], [1, e^{−2}]]`, and paired
  against the sign test vector it is exactly
  **2e^{−2} − 2 ≈ −1.7293 < 0** — every value proved by exact
  evaluation, no floating point involved.

## The weld is load-bearing — proved, not asserted

With the middle (weld) factor set to 1, the same computation
gives `[[1, e^{−2}], [e^{−2}, 1]]`, which is positive. The
indefiniteness is exactly the weld factor's trace value −1
flipping the coupling. The corollary, stated as labeled prose
over the two theorems: **no proof of 𝒜 ⪰ 0 can proceed by
summing positive per-column contributions; any proof must
use the joint stratum average essentially.** A whole family
of plausible arguments is now excluded at theorem grade —
the same service a good counterexample always renders.

Axiom sets on the headlines: exactly
`[propext, Classical.choice, Quot.sound]`.

## Census effect

Strict 6,195 → **6,217**; attribute-inclusive 6,273 → **6,295**;
modules 211 → **212**; `sorry` placeholders unchanged at **6**.

## Backers since last landing

No new backers inscribed in this interval; the roll stands as
recorded in `BACKERS.md`. Every gift is published with the proof
stream, named as the giver wishes, amounts only with the giver's
permission — the standing reciprocity of this house.
