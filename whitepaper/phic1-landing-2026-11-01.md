# PHI-C1 LANDING DOSSIER — 2026-11-01

**Item:** PHI-C1 (∂₁ ∘ ∂₂ = 0 over the explicit model), second
brick of the PHI-C salvage line (memo
`scoping-phi-icosa-2026-10-30.md`; PHI-C0 landed as
`IcosidodecaChain.lean`).

**Status: FULL.** COMBINATORICS ONLY — salvage label on the face
(T1-about-the-polyhedron, zero NCG content).

**Artifact:** `lean/ThetLogos/IcosidodecaBoundary.lean` —
strict 9, defs 2 (in the memo's 8–20 band). Verified by the
coordinator in the main tree (build green, 1402 jobs); all five
headlines on exactly `[propext, Classical.choice, Quot.sound]`.

## What landed

The chain identity in every consumable form: the entry form over
ℚ (`(d1Mat * d2Mat) v f = 0` for all v, f), the matrix form
(`d1Mat * d2Mat = 0`), the linear-map form (`d1 ∘ₗ d2 = 0`), and
the column form (`d1 (d2 (Pi.single f 1)) = 0` for every face f)
that C2/C3 consume.

**Proof route, on the record:** the finite entry check is run
over ℤ by kernel `decide` — deliberately avoiding kernel `decide`
on rational arithmetic (the pin's known Rat-reduction stall) —
and transferred to ℚ by showing the rational entries are
`Int.cast` of the integer entries. The probe is never cited as a
hypothesis; the check is recomputed from PHI-C0's own
definitions. One scoped disclosure: the full 30×32 integer check
carries `set_option maxRecDepth 16384 in` on that single theorem
(kernel recursion depth for the 60-term sums; statements
unaffected) — the same disclosure class as the house's scoped
`maxHeartbeats` precedent.

## Fences

NO CLAIM — no Millennium problem is claimed solved or advanced;
no dial moves. K-PHI-4 binds PHI-C3's census, ahead.

**Census after landing: 10,978 strict / 11,120 total / 373 counted
modules; zero `sorry` terms tree-wide.**

## Backers since last landing

None new on the record since the last landing.
