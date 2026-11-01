# PHI-C2 LANDING DOSSIER — 2026-11-01

**Item:** PHI-C2 (face-split independence), third brick of the
PHI-C salvage line (memo `scoping-phi-icosa-2026-10-30.md`;
PHI-C0 model and PHI-C1 chain identity landed).

**Status: PARTIAL in its pre-registered shape.** Independence
and the signed-sum relation landed FULL; the uniqueness of the
relation is NOT proved and is named on the module's face as
PHI-C3's remainder.

**Artifact:** `lean/ThetLogos/IcosidodecaFaceSplit.lean` —
strict 15, defs 7 (in the memo's 10–22 band). Verified by the
coordinator in the main tree (build green, 1402 jobs); the
independence/relation headlines on exactly
`[propext, Classical.choice, Quot.sound]`, finite decide lemmas
on cleaner subsets.

## What landed

- `triCol_linearIndependent` — the 20 triangle boundary columns
  of ∂₂ are linearly independent over ℚ.
- `penCol_linearIndependent` — the 12 pentagon boundary columns
  likewise.
- The signed-sum relation: `d2_faceSumVec_zero` /
  `faceSumVec_mem_ker` — the all-ones vector of C₂ lies in
  ker ∂₂ (each edge is hit once by its triangle and once by its
  pentagon with opposite signs).

**Route (the memo's disjoint supports):** each face's witness
edge is the first edge of its signed boundary; by PHI-C0's
each-edge-in-exactly-one-triangle/pentagon data that edge occurs
in no other same-family face, so evaluating a relation at the
witness edge collapses the sum to `g i * (±1) = 0`. Finite
incidence facts are checked over ℤ by kernel `decide` and cast
to ℚ — kernel `decide` never touches Rat arithmetic.

## The remainder (named, not hidden)

Uniqueness — that the signed-sum relation is the ONLY relation
among the 32 columns, equivalently `ker ∂₂ = ℚ • (1,…,1)` — is
PHI-C3's content, by coefficient propagation over the connected
dual graph. K-PHI-4 (the census guard) forbids closing it by
citing a machine rank computation; C2 does not reach for it.

## Fences

NO CLAIM — no Millennium problem is claimed solved or advanced;
combinatorics only; no dial moves.

**Census after landing: 10,993 strict / 11,142 total / 374 counted
modules; zero `sorry` terms tree-wide.**

## Backers since last landing

None new on the record since the last landing.
