# PHI-C0 LANDING DOSSIER — 2026-11-01

**Item:** PHI-C0 (the combinatorial model), first brick of the
PHI-C salvage line per the ratified scoping memo
(`scoping-phi-icosa-2026-10-30.md`) and the coordinator pack
(`pack-phi-c0.md`). The probe landed 2026-10-30 (BR1-010).

**Status: FULL.** COMBINATORICS ONLY — the salvage label is on
the module's face: T1-about-the-polyhedron, zero NCG content,
not a promotion of the mnemonic. The bridge form was killed at
scoping (K-PHI-1/2/3 fired there); this line never mentions W₂₂.

**Artifact:** `lean/ThetLogos/IcosidodecaChain.lean` — strict 21,
defs 16. Strict runs above the memo's 5–15 estimate; the excess
is the read-back layer (2 general basis-column lemmas, 7 spot
entries, 5 data read-backs) over the 7 sanity theorems and the
16-def data core — disclosed here and on the builder's report.
Verified by the coordinator in the main tree (build green,
1401 jobs); headlines on exactly
`[propext, Classical.choice, Quot.sound]`, two data-count
theorems on the cleaner subset `[propext]`.

## What landed

The model over ℚ (the probe's field; C1–C3 consume it): index
types Fin 30 / Fin 60 / Fin 32; `edgeList` and `faceList` as
explicit decidable data with the probe's orientation convention
(edges lower→higher; ∂₁ = −1 tail / +1 head; faces 0–19
triangles, 20–31 pentagons, outward cycles, recorded signs);
`d1Mat`/`d2Mat` as explicit matrices, `d1`/`d2` as
`Matrix.mulVecLin` maps. Sanity theorems proved in-kernel: the
60/32 list lengths, the 20-triangle / 12-pentagon split,
tail < head for every edge, and every edge in exactly one
triangle and exactly one pentagon. Read-backs: named spot entries
of both boundary maps against the tables, plus the general
basis-column lemmas C1 will consume.

**Transcription was generated, not hand-typed:** the generator
(`routeb-general-scratch/phic0-gen.py`) reads BR1-010's tables
directly, asserts the counts/split/boundary lengths, and emits
the Lean literals; the in-kernel `decide` self-checks then
re-derive the probe's own checks independently.

∂₁ ∘ ∂₂ = 0 was NOT proved — that is PHI-C1's brick, fenced in
the module header.

## Fences

NO CLAIM — no Millennium problem is claimed solved or advanced;
no dial moves. K-PHI-4 (the census guard) binds PHI-C3, ahead.

**Census after landing: 10,969 strict / 11,109 total / 372 counted
modules; zero `sorry` terms tree-wide.**

## Backers since last landing

None new on the record since the last landing.
