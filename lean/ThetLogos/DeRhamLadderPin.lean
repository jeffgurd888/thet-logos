/-
# ThetLogos.DeRhamLadderPin — LAD-0: THE PIN (0 strict — charter only)

**WORKING LABEL "De Rham ladder" — naming is Jeff's.** This file is the
pin for the ladder line: header only, NO definitions, NO proofs, per
the scoping `derham-ladder-scoping-2026-11-06.md` §4 (LAD-0) and the
house subdivision directive (interface-first connectivity module:
definitions + statement pins only, frozen names, its own verified
commit, landed BEFORE parallel work).

## Origin

Jeff's fragment "infinite supersymmetry" (2026-11-06 13:09 EST,
filed T5) → flagged by BONES under Jeff's standing scoping-flag
order (2026-11-04) → Jeff tapped "Scope the ladder — partner sector
in every degree" (2026-11-06 13:10 EST) → scoping
`derham-ladder-scoping-2026-11-06.md` → **Jeff fired the core menu
2026-11-06 17:57 EST ("fire DeRham")**. LAD-5 (the general seat)
was OPTIONAL and NOT fired; it is not built in this line.

## The shape (scoping §0)

The partner sector pairs degree 0 (vertices) with degree 1 (edges)
through one operator `d` and its adjoint: a supercharge `Q` on the
graded sum, `Q² = H_v ⊕ H_e`, zero modes on both sides, an index
theorem (SP-4), spectral pairing (SP-5). The LADDER is that same
package at every degree of a finite cell complex. The two halves
have never met in-tree: the partner sector owns the ℝ Hodge
machinery at a graph seat with no faces; the PHI-C line owns a
genuine 2-cell complex (`d² = 0`, exactness, Betti (1, 0, 1)) at a
seat with no adjoints, no ℝ, no supercharge. This line is the JOIN.

## Seat decision (scoping §2, stated on the face)

**PHI-C seat, degrees 0–2, ℝ-cast.** The icosidodecahedron complex
(`IcosidodecaChain`, `IcosidodecaBoundary`, `IcosidodecaCensus`:
V = Fin 30, E = Fin 60, F = Fin 32 over ℚ, `d1_comp_d2` proved,
census (H₀, H₁, H₂) = (1, 0, 1)) carried to ℝ — its own header
licenses the cast (same integer matrices, same ranks). Degrees ≥ 3:
no seat exists; none is built here. Plaquettes are NOT 2-cells
(holonomy, "no topology yet" — scoping §1.2(ii)) and do not seat
this ladder.

## Bricks (scoping §4; sizes are the scoping's priced bands)

- LAD-1 — the ℝ Hodge seat at PHI-C: `d₁`, `d₂` as ℝ linear maps;
  per-degree adjoints as linear maps with the adjoint identity;
  Laplacians Δ₀, Δ₁, Δ₂ := d* d + d d*; `d² = 0` transported.
  K-LAD-SEAT assessed here. (M, ~10–18 strict)
- LAD-2 — the supercharge package: total space C⁰ × C¹ × C²;
  Q := d + d*; **Q² = Δ₀ ⊕ Δ₁ ⊕ Δ₂**; per-degree energy = sum of
  squares; ker Δ_k = ker d_k ∩ ker d*; harmonic = cohomology,
  finranks (1, 0, 1) against PHI-C3's census (consumed, not
  re-proved). K-LAD-FIAT assessed here. (M, ~12–20 strict)
- LAD-3 — the index at the seat: χ both ways,
  finrank ker Δ₀ − finrank ker Δ₁ + finrank ker Δ₂ = 30 − 60 + 32
  (= 2). SP-4 cited as the 2-term truncation — a remark on the
  face, NOT re-proved. (S, ~3–6 strict)
- LAD-4 — spectral pairing (the SP-5 analog): per adjacent pair,
  (i) algebraic half — charpoly identities for the up/down parts
  via `Matrix.charpoly_mul_comm'`; (ii) geometric half —
  eigenspace multiplicity matching at λ ≠ 0. The halves land
  independently, as SP-5's did; either may land without the
  other, labeled PARTIAL if so. (M–L, ~15–30 strict)
- LAD-5 — NOT FIRED, NOT BUILT (the general `FiniteComplex`
  record; the family reading of §3(d) lands only there).

## Citations (scoping §1.1 note — the two records cited TOGETHER)

Partner sector FULL SP-0..SP-5 at T1: ledger records
`axiom-tet-partner-sector` (SP-0..SP-4; its face still reads
"SP-5 OPEN" — STALE, never updated) AND `sp5-isospectrality`
(SP-5 landed FULL 2026-11-03). Citing the first alone understates
the corpus. PHI-C0/C1/C2/C3: complex, `d² = 0`, face-split,
census — all landed, price 0 here, consumed by citation only.

## Kills armed (scoping §5, from this pin onward)

- **K-LAD-FIAT** — the notation kill: fires if the ≥2-degree
  content collapses to citation of SP / PHI-C results restated
  in ladder vocabulary. The ladder's new content is the Hodge
  half and the χ-identity as a decl. Assessed first at LAD-2.
- **K-LAD-SEAT** — the degenerate-seat kill: fires if any seat
  has cell structure with no incidence content (zero or identity
  boundary maps), making `d² = 0` vacuous. At the PHI-C seat
  `d² = 0` has content (signed face data; both `d₁`, `d₂`
  nonzero with proved composition zero). Assessed at LAD-1.
- **K-LAD-NAME** — the naming kill: (a) no collision with the
  three landed `d`-families (PHI-C `d1/d2/d1Mat`, partner
  `diffOp/supercharge/index_eq`, BRST `d1/d2/brstQ`) — ladder
  names are a FOURTH, distinct family (`lad*` prefix, namespace
  `ThetLogos.DeRhamLadder`); (b) "infinite supersymmetry" is
  BARRED as a module name, claim name, or public title — it may
  not name a finite object; (c) a seat-level landing is named
  at its seat: "at the icosidodecahedron, degrees 0–2" is the
  whole truth of LAD-1..LAD-4 without LAD-5.
- **K-LAD-INF** — the infinity kill: fires if any statement,
  header, or public text presents the family reading as an
  infinite object (built infinite complex, limit,
  infinite-dimensional seat) or the ladder as N-extended
  supersymmetry, supergravity, or a higher-spin tower
  (scoping §3(e): category error — none of that work is this
  seat's). The ladder is FINITE at every seat; "infinite"
  survives only as "no bound across the family," never as a
  built object — and the family reading itself lands only
  via LAD-5, which is not fired.
- **K-LAD-GRAV** — the laundering kill: fires if any text
  presents the ladder, its χ, or its Betti numbers as a gravity
  candidate, a response law, a derived measured number, or Dial
  evidence of any species. χ = 2 at the icosidodecahedron is a
  finite combinatorial invariant of a chosen seat: not Dial-1
  (not a derived measured number), not Dial-3 (no continuum
  limit taken or approached), not Dial-4 (nothing predicted
  about an uncontrolled system).

## Claim discipline (scoping §6)

A full landing of LAD-0..LAD-4 proves, at T1: a finite Hodge /
de Rham package at ONE explicit seat (the word "de Rham" names
the finite combinatorial analogy — the same fence the partner
scoping put on "supersymmetry"); the index theorem at that seat
in full 3-term form, SP-4 visible as its 2-term truncation;
adjacent-degree spectral pairing at (0,1) and (1,2) in SP-5's
two forms. It does NOT prove or suggest: any infinite object;
continuum de Rham or Hodge theory (no manifolds, no smooth
forms, no continuum limit stated, taken, or approached); any
physical supersymmetry (no spinors, no spacetime symmetry, no
superpartners, no N-extension — the corpus's SUSY is finite
SUSY quantum mechanics: a grading, a supercharge, Q² = Δ).

**NO CLAIM; dials 0/4; Dial 2 = 0.**
-/
