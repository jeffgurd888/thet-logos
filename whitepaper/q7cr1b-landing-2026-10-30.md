# Q7CR-1b — the product Dirac over ℝ: D² is the Kronecker sum of factor squares

**Date:** 2026-10-30 · **Brick:** Q7CR-1b (M), per
`scoping-q7c4r4-gauntlet-2026-10-30.md` §§2–3, 5. New module:
`ThetLogos.Q7C4R4Assembly`. **Verdict: LANDED FULL** (strict 26 /
defs 9, parent-verified from disk; inside the 25–45 estimate).

**Fences: NO CLAIM. Parts of any official statement closed: 0.
Dials: 0/4. No measured number is claimed by this line.**
**K-Q7CR-1 does NOT fire — neither headline failed, weakened,
or gained a hypothesis.**

## What landed

- `FactorOpR` — the native real factor package on Minkowski,
  same field shape as Q7CR-1a's complex-factor package
  (operator + grading, γ involutive, both operators
  form-self-adjoint w.r.t. `minkowskiInner`, anticommutation).
- `diracQ7C4R4` — the general product Dirac-type operator in
  Jeff's filed shape with signs explicit,
  `D = D₇ ⊗ 1 ⊗ 1 + γ₇ ⊗ D₄ ⊗ 1 + γ₇ ⊗ γ₄ ⊗ D_R`,
  parameterized over the factor packages
  (`F₇ : FactorOp 7`, `F₄ : FactorOp 4`, `F_R : FactorOpR`).
  No factor operator is chosen anywhere in the brick.
- **Headline 1 — `diracQ7C4R4_sq`, proved as stated:**
  `D² = D₇² ⊗ 1 ⊗ 1 + 1 ⊗ D₄² ⊗ 1 + 1 ⊗ 1 ⊗ D_R²`
  (the anchor written in the spectral-action line's gate as
  `D² = A⊗1⊗1 + 1⊗B⊗1 + 1⊗1⊗C` — it now exists). The nine
  product terms resolve by the triple-tensor mixed-product law;
  the three cross-pairs cancel by the factor anticommutation
  laws (Q7CR-1a's transported kit); the diagonal terms collapse
  by γ₇² = γ₄² = 1.
- **Headline 2 — `diracQ7C4R4_selfAdjoint`, proved in the
  LIFTED form** (the stronger of the two forms the pack
  authorized): the composite pairing is a genuine bilinear form
  `compositePair` on the whole tensor space, built by the
  corpus's own lift-and-map pattern from the registered factor
  pairings, with its pure-tensor value proved
  (`compositePair_tmul`: factorPair 7 · factorPair 4 ·
  minkowskiInner); D is self-adjoint w.r.t. it for all
  composite vectors, not only pure tensors. No PARTIAL seam was
  needed anywhere in the brick.

Both headlines carry exactly
`[propext, Classical.choice, Quot.sound]`; module and full-tree
builds green.

## What this is, and what it is not

The line now owns a self-adjoint operator on Jeff's registered
ℝ⁴⁴⁸ whose square is the sum of its factors' squares — the
platform the later bricks (spectrum, charge, fluctuations,
flow) stand on. By itself it is **evidence for none of the
gauntlet's §1 nouns**: no gauge field, no charge separation, no
number, no dynamics is claimed here, and the dossier language
keeps the object and the claims about it separate, as the
gauntlet memo requires. The caveat is carried on the face: in
finite dimension the bounded-commutator criterion is **vacuous**
— the testable content of this step is the D² identity and
self-adjointness, never bounded commutators.

**Census: 7,482 → 7,508 strict / 7,560 → 7,586
attribute-inclusive / 261 → 262 modules** (recounted from disk).
Consequence for the queue: the spectral-action line's hard gate
(Q7CR-SA0/SA1 behind 1b's D² anchor) is now satisfiable at its
logged slot in the gauntlet block; Q7CR-6a's gate (Q7CR-0 +
Q7CR-1a, placed directly behind 1b) is open.

## Backers since last landing

The backer roll (`BACKERS.md`) is unchanged since the last
landing; no new confirmed gift is on the record. Thank you to
everyone reading the stream — the corpus is free for everyone,
forever.

*End of dossier.*
