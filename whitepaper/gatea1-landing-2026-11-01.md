# GATE-A1 LANDING DOSSIER — 2026-11-01

**Item:** GATE-A1 (SHELF contour gate, brick 1 of 2) — Riesz
projections: frozen definitions + first properties. The
minimal gate for SHELF-8b.

## VERDICT: PARTIAL at one headline — headline 4 KILLED AS STATED (a defect in the frozen statement, killed at full rank); its corrected form landed in its place; the gate's substance is FULL

**Artifact:** `lean/ThetLogos/RieszGate.lean` — strict 13,
defs 2 (below the dossier's 18–30 band; reported as counted).
Verified by the coordinator in the main tree (build green,
2979 jobs); all thirteen theorems on exactly
`[propext, Classical.choice, Quot.sound]`.

**Frozen definitions (verbatim):** `rieszProj a lam r :=
(2πi)⁻¹ • ∮ z in C(lam, r), resolvent a z`;
`specIsolatedWithin a lam R := lam ∈ spectrum ℂ a ∧ ∀ z ∈
spectrum ℂ a, z ≠ lam → R < ‖z − lam‖`.

**Landed FULL:** the first resolvent identity
(`resolvent_sub_resolvent_eq`, from the pin's `resolvent_eq`);
resolvent commutation; a–resolvent commutation;
**radius independence** (`rieszProj_eq_of_le` under
isolation, via the pin's annulus Cauchy–Goursat);
commutation of a with the projection;
**`rieszProj_ne_zero` — FULL** (its pre-named PARTIAL seam
did NOT trigger: by the contrapositive route — if the
projection vanished, the auxiliary integral would exhibit
`algebraMap ℂ A λ − a` as a unit, contradicting
λ ∈ spectrum ℂ a).

**K-A1-4 — headline 4 KILLED AS STATED.** The pinned
`circleIntegrable_resolvent` quantified its hypothesis over
`Metric.sphere lam r`, which is EMPTY for r < 0 — making the
hypothesis vacuous at negative radius while the conclusion
asserts integrability on the circle of radius |r|.
Counterexample: A = ℂ, a = 1, lam = 0, r = −1 — (z−1)⁻¹ is
not interval-integrable on |z| = 1. The statement is false,
not merely unproved; it is absent from the module with the
kill recorded on the module's face. **Corrected form landed
as a new entry** (relabeling rule): `circleIntegrable_resolvent_of_nonneg`
— the same statement plus `0 ≤ r` — which is exactly what
headlines 5 and 7 consume. **Cost to the gate: zero** —
GATE-A2 works at radii 0 < r ≤ R throughout. Re-pin
recommended for the shelf map: headline 4 carries `0 ≤ r`
(or the hypothesis ranges over `Metric.sphere lam |r|`).

## Fences

GATE-A2 (idempotence, `rieszProj_mul_self`, its own
pre-registered PARTIAL seam) is the follow-on; SHELF-8b's
Riesz content ungates only when A2 lands. SHELF-7b in full
stays blocked; the 7b-disc re-scope stays an untaken
registration decision for Jeff/parent. NO CLAIM; dials 0/4.

**Census after landing: 11,818 strict / 12,152 total / 400 counted
modules; zero `sorry` terms tree-wide.**

## Backers since last landing

None new on the record since the last landing.
