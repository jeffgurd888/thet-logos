# VL-4b LANDING DOSSIER — 2026-11-01

**Item:** VL-4b (Vortex Locus line, brick 4b) — the full
dimension count at the VL-4a seat. The VL line is COMPLETE.

## VERDICT: FULL — `Module.finrank ℝ locusB = 156`, the registered d_full, proved

**Artifact:** `lean/ThetLogos/VortexLocusFullCount.lean` —
strict 140, defs 26 (the per-root separation and five-block
assembly infrastructure; reported as counted). Verified by
the coordinator in the main tree (build green, 3140 jobs);
the headlines (`finrank_centQ`, `finrank_locusB`,
`vl4b_headline`) on exactly
`[propext, Classical.choice, Quot.sound]`. The pre-named
PARTIAL seam did NOT trigger.

**What was proved.** L is the odd (γ-odd) part of the
commutant of K0 = (smDirac y₀)² at Seat B,
y₀ = (1, 2, 3, 5, 7). Both registered obligations discharged:

1. **Per-root separation:** each irrational root
   (51 ± √2597)/2 of μ² − 51μ + 1 has complex eigenspace
   finrank 2 with γ-split (1, 1) (`finrank_eig_mu`) — the
   joint (2, 2) of VL-4a separated per root, as the pack's
   deciding subtlety required (the naive plug of the joint
   split into the Σ 2·m⁺m⁻ formula gives 8, not the count).
2. **Five-block assembly:** the distinct-eigenvalue blocks
   contribute 8 + 72 + 72 + 2 + 2 = 156
   (`finrank ℝ ↥locusB = 2 * 78 = 156`).

**The VL line, closed.** VL-0..VL-3 (pin; Seat A formula;
P-VL1 finrank = 10 = d₀; the family-locus iff yR = 7·yNu with
real dimension 8), VL-4 Step 0 (BR1-027 probe), VL-4a (the
full γ-split table at y₀, T1), VL-4b (d_full = 156, T1). The
registered fences all held: d₀ = 10 ≤ 156 — the W22 locus is
a proper subspace of the full odd commutant; no scoped
heartbeat raised; the irrational pair was carried only as
roots of its quadratic, per-root splits now proved.

## Fences

Finite-seat spectral bookkeeping at one named point of the
moduli. NO CLAIM; dials 0/4 — nothing here touches a dial:
d_full counts a commutant's odd part, not a measured number,
not a gravity object, not a continuum limit.

**Census after landing: 11,805 strict / 12,137 total / 399 counted
modules; zero `sorry` terms tree-wide.**

## Backers since last landing

None new on the record since the last landing.
