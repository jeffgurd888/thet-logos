# NS-1a LANDING DOSSIER — Navier–Stokes definitions brick — 2026-11-02

**Item:** NS-1a (Millennium Lane 3) — the definitions half of
NS-1, per NS-0's priced split. Gate record: NS-0's audit
(committed alongside) — K-NS-0 did not fire; the September
2026 (C)/(D) claim is unverified and contested; the charter
stands.

## VERDICT: DEFINITIONS LANDED — every K-NS-1 fence item carried at Clay grade

**Artifact:** `lean/ThetLogos/NavierStokesDefs.lean` —
strict 2 (two `Iff.rfl` unfold self-checks), defs 28 (house
counter). Verified by the coordinator in the main tree
(build green); both proved lemmas on exactly
`[propext, Classical.choice, Quot.sound]`. Definitions
only: no A/B/C/D Props, no board disjunction, no existence
content — those are NS-1b's, against these frozen names.

Fields are time-first (`u f : ℝ → NSpace → NSpace`,
`p : ℝ → NSpace → ℝ` over `NSpace := EuclideanSpace ℝ
(Fin 3)`); `nsDiv` is owned from `fderiv` (none exists
in-pin); the convective term is the Jacobian contraction;
the Laplacian is the pin's own, cited componentwise;
`NavierStokesSystem` carries `0 < ν` as its first conjunct.

**K-NS-1 checklist (the audit's fence, item by item):**
1. (4) initial decay, all α and all K, + smooth div-free
   u° — **CARRIED** (`NSInitialDecay` in the pin's own
   Schwartz form; `NSInitialSmoothDivFree`; both initial
   packages).
2. (5)/(9) forcing decay all α,m,K; f ≡ 0 named for A/B —
   **CARRIED** (ℝ³ weight `(1+‖x‖+t)^K`; torus `(1+t)^K`;
   `NSZeroForcing` pointwise).
3. (6) genuine C^∞ on [0,∞) — **CARRIED**
   (`NSSolutionSmooth`: joint ContDiffOn at order ∞ on the
   full half-line).
4. (7) uniform bounded energy — **CARRIED**
   (`NSBoundedEnergy`, one C for all t ≥ 0; torus analogue
   over the unit cube).
5. (8) periodicity incl. the errata pressure clause —
   **CARRIED** (`NSPressurePeriodic` as its own named Prop,
   joined in `NSSolutionPeriodic`).
6. C/D quantifier shape — NS-1b's by the registered split;
   the packages here are shaped as its predicates,
   unweakened.
7. ν > 0, n = 3 — **CARRIED**.

**Named resistances (named, never weakened):** the torus
has no packaged ℝ³/ℤ³ PDE setting in-pin — periodicity is
encoded on ℝ³ fields directly, which is Fefferman's own
(B)/(D) formulation; half-line smoothness uses the pin's
native `ContDiffOn` at order ∞ (boundary formalism only —
full order, joint, global); a numbering variance between
the pack and the audit drops nothing (all four contents
carried as separate named packages).

## Fences

NO CLAIM; **parts of Clay Navier–Stokes closed: 0.** This
brick states vocabulary; it asserts nothing about
existence or breakdown.

**Census after landing: 12,551 strict / 13,020 total / 434 counted
modules; zero `sorry` terms tree-wide.**

## Backers since last landing

None new on the record since the last landing.
