# BSD3-2 PIN LANDING DOSSIER — 2026-11-02

**Item:** BSD3-2 pin (BSD statement-grade line, Lane 3) —
the third worked curve's statement pin, from the BSD3-2
study (closure separates; K-BSD3-2 did not fire).

## VERDICT: PIN LANDED — statement grade, no deviations from the study's §4 shapes

**Artifact:** `lean/ThetLogos/BSDRefinedE3Pin.lean` —
strict 0, defs 8 (pin-only by design). Verified by the
coordinator in the main tree (build green, 3797 jobs). The
study memo rides into `whitepaper/` with this landing
(`scoping-bsd3-2-2026-11-02.md`).

**The curve:** E3 = LMFDB 11.a1, `E3 : WeierstrassCurve ℚ
:= ⟨0, -1, 1, -10, -20⟩` (y² + y = x³ − x² − 10x − 20),
conductor 11, rank 0 — chosen on seam coverage: torsion
ℤ/5, ∏c_p = 5 ≠ 1, c₁₁ = 5 at split multiplicative I₅;
the first worked curve exercising multiplicative
Tamagawa > 1, odd-prime torsion, and in-pass L + period
at rank 0 together.

**Frozen in the pin:** `BSDRefinedE3` reusing the existing
`refinedRHS` at (Reg, tam, tors) = (1, 5, 5), tolerance
5e-3, sha derived-not-input. Named seams: `E3RankZeroSeam`
(rank 0 rides as a T4 recorded input, LMFDB 11.a1,
corroborated in-pass — the computed L interval excludes 0);
`NagellLutzCriterionE3` in the **literal shared E1/E2
form** (integer coordinates with `yi = 0 ∨ yi² ∣ 161051`,
161051 = |Δ(E3)| = 11⁵ — K-BSD3-2b satisfied by
construction); `E3ShaFiniteSeam` (B1 licence);
`E3TamagawaValue` (tam = 5, per-prime record on the face).
Interval Props with provenance on the face (study-computed
in-pass by AFE/quadrature, bars ±1e-7, recorded here two
orders looser per B2-5 discipline; K-BSD3-2d fence):
`E3LValue`: |Lval − 0.2538418609| ≤ 1e-5;
`E3PeriodValue`: Ω ∈ [1.2692092, 1.2692094].

**Next in flow:** BSDTorsionE3Sweep (Δ = −11⁵ in-tree;
torsion card 5 by the NL enumeration — (5,5), (16,60),
(16,−61), (5,−6), O; **K-BSD3-2c armed**: the card may not
be carried as a bare T4 value) and BSDRefinedE3Assembly
(the iff, sha derived by interval arithmetic).

## Fences

NO CLAIM; **parts of Clay BSD closed: 0**; seams B1/B4
stand labeled as on rungs 2–3; B2-7 FRONTIER, untouched.
All dials 0/4.

**Census after landing: 12,217 strict / 12,601 total / 417 counted
modules; zero `sorry` terms tree-wide.** (Defs-only pin:
the strict headline figure is unchanged, so the README
census is not edited by this landing, per house rule.)

## Backers since last landing

None new on the record since the last landing.
