# XYZ-2 — the boundary marker: a tripotent R5 cannot touch (a kill of the kill-route)

**Date:** 2026-10-30 · **Brick:** XYZ-2 (M, boundary
marker), per `scoping-xyz-tripotents-2026-10-30.md` §4.
Module: `ThetLogos.XYZBoundaryMarker`. **Verdict:
LANDED** (strict 20 / defs 3, parent-verified from disk;
module build green; `tripotent_tripT` and
`r5_cannot_exclude_tripT` on exactly [propext,
Classical.choice, Quot.sound]).

**Fences: NO CLAIM. Parts of any official statement closed: 0.
Dials: 0/4.** `xyz_tripotents_exist` stays OPEN; no triple
is exhibited and no generation claim is made for the
marker — it is a candidate ingredient for XYZ-3's live
families, nothing more. This brick kills a kill-route's
extension, by construction; it is recorded at the same
volume as a win.

## The marker

`tripT = e₁₈ · ((1,1,1)/√3)ᴴ` — a rank-one partial
isometry over the M-sector colour triplet (18, 20, 22):
only row 18 is nonzero, with entries exactly
(((√3 : ℝ) : ℂ))⁻¹ at (18,18), (18,20), (18,22) — the
same closed form as genM 7's exhibiting entry.
Tripotency is proved by direct entry computation
following the corpus's `Tripotent`/`ternaryMat`
definitions literally (the self-product collapses to the
support projector: 3·(1/√3·star(1/√3)) = 3·(1/3) = 1).

## The boundary, and its honest extent

- `tripT_entry_not_gaussInt` + `r5_cannot_exclude_tripT`:
  R5's hypotheses can never jointly hold for a triple
  containing tripT. **The ℤ[i] species boundary is now a
  theorem with a concrete object sitting outside it** —
  XYZ-1's kill cannot be extended by R5's method.
- Checked honestly against the rest of the rubric, on
  the module's face: **R1 cannot touch it either**
  (`tripT_not_diagonal` — the (18,20) entry is nonzero);
  **R4 cannot touch it** (`tripT_not_pairSupported`);
  R2 closes by the same diagonality fact. **R3 stays
  honestly open per-triple**: the support invariant is
  fully general and could still kill a SPECIFIC triple
  {tripT, Y, Z} whose partners share a restrictive
  support — nothing landed instances it against tripT,
  and R3 gives no species-level exclusion. The marker
  claims exactly the boundaries proved, no more.

**Census: 8,242 → 8,262 strict / 8,320 → 8,340
attribute-inclusive / 284 modules** (recounted from disk).

## Backers since last landing

The backer roll (`BACKERS.md`) is unchanged since the last
landing; no new confirmed gift is on the record. Thank you to
everyone reading the stream — the corpus is free for everyone,
forever.

*End of dossier.*
