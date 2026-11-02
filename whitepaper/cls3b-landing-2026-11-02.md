# CLS-3b LANDING DOSSIER — 2026-11-02

**Item:** CLS-3b (Dial-1 classification lane) — sector-wise
realizability: the single-colour quark swap's full status at
each condition-set grade, per colour.

## VERDICT: FULL — no seam; every cell decided for all three colours

**Artifact:** `lean/ThetLogos/DialOneSwapColourChapter.lean`
— strict 43, defs 2. Verified by the coordinator in the main
tree (build green, 3529 jobs); all audited headlines on
exactly `[propext, Classical.choice, Quot.sound]`.

**The chapter (proved separately per colour — generic-c
lemmas plus explicit per-colour theorems `swap_colour0/1/2_status`,
assembled as `swap_colour_chapter`):**

| Cell | Verdict (all three colours) |
|---|---|
| Clean family `GammaFamily (piSwap c)` | **HOLDS** |
| Base `DialOneBase (piSwap c)` | **FAILS at order-zero** — witnesses: colour 0 entry (uSeat 0, uSeat 1) via `single 1 0 1`, `star i` vs `i`; colour 1 entry (uSeat 1, uSeat 2) via `single 2 1 1`; colour 2 entry (uSeat 2, uSeat 0) via `single 0 2 1` |
| Strengthened | **FAILS** (assembled from the base failure) |
| Own weights `weightAt (piSwap c) (swappedWeightVector c)` | **HOLDS** — new proof: the swap's lifted weights are the table's with the colour-c u_R/d_R entries exchanged (4 ↔ −2 at both particle and partner seats; determinant unchanged, `exp((−4α−12β)ti)`); the pre-named PARTIAL seam did not trigger |
| Common weights `weightAt (piSwap c) commonWeightVector` | **FAILS** — det forces (α,β) = ±(3,−1), the up-seat character is exp(∓2ti) against the table's 4, closed by CLS-2b's character rigidity |

**The classification content:** a single-colour quark swap is
a perfectly realizable representation — it holds the whole
clean family and carries its own well-defined weight vector.
It is excluded from the table **by the BASE, at order-zero**
(ρ₁'s colour-matrix quark block does not commute with the
single-colour toggle), NOT by the family and NOT by
weightlessness. The uniform triple swap stands as the
chapter's boundary contrast (CLS-2b: in base + family, wrong
weights). **K-CMP-F1 stays silent**; no forcing consequence
is claimed in either direction from this chapter.

## Fences

NO CLAIM; **Dial 1: 0.** Grade T's quark-colour chapter is
closed; the lepton chapter closed at CLS-3a; the orbit
classification closed at CLS-2b. Remaining Lane-1 item:
CLS-3c (antiparticle axis, S).

**Census after landing: 12,217 strict / 12,593 total / 416 counted
modules; zero `sorry` terms tree-wide.**

## Backers since last landing

None new on the record since the last landing.
