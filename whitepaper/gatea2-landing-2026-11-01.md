# GATE-A2 LANDING DOSSIER — 2026-11-01

**Item:** GATE-A2 (SHELF contour gate, brick 2 of 2) — Riesz
projection idempotence. **The GATE-A chain is COMPLETE:
SHELF-8b's Riesz-projection content is ungated.**

## VERDICT: FULL — `rieszProj_mul_self` proved; the pre-registered PARTIAL seam did not trigger

**Artifact:** `lean/ThetLogos/RieszGateIdem.lean` — strict
28, defs 0 (in the 20–35 band). Verified by the coordinator
in the main tree (build green, 2980 jobs); the headlines on
exactly `[propext, Classical.choice, Quot.sound]`.

**Headline (exact landed form):** under
`specIsolatedWithin a lam R`, for 0 < r ≤ R,

```
rieszProj a lam r * rieszProj a lam r = rieszProj a lam r
```

proved via the two-radii form
(`rieszProj_mul_rieszProj_of_lt`: 0 < r₁ < r₂ ≤ R ⇒
P(r₁)·P(r₂) = P(r₁)) and the single-radius form at r/2 < r by
GATE-A1's radius independence. **Route as landed — every step
cited, none asserted:** the product pulled to a double circle
integral (GATE-A1's scalar-pull lemmas); split by GATE-A1's
first resolvent identity; the first piece's inner integral by
`circleIntegral.integral_sub_inv_of_mem_ball`; the second
piece swapped by Fubini over the angle rectangle (joint
integrability proved — disjoint circles, resolvent continuous
on the outer circle) and its inner integral killed by disc
Cauchy–Goursat. The one non-obvious integrability is
discharged by a proved closed form from the auxiliary
identity `(algebraMap ℂ A z − a) * H z = (2πi) • 1 − J₂`.
**Only GATE-A1's corrected integrability form was consumed;
the killed headline-4 form was never touched.**

**Consequence:** with GATE-A1 (definitions, radius
independence, commutations, nonvanishing — all FULL) the
minimal gate for SHELF-8b stands complete: a Riesz projection
at an isolated spectral point now exists in the tree as a
bona fide projection. SHELF-8b itself (the projection form of
the general contour statement at isolated points) is the
follow-on brick, to be scoped from the shelf map. The
optional two-point orthogonality was not attempted
(explicitly outside the minimal gate). SHELF-7b in full
remains blocked (no winding-number/contour-system vocabulary
in the pin); the 7b-disc re-scope remains an untaken
registration decision for Jeff/parent.

## Fences

NO CLAIM; dials 0/4. Functional-calculus infrastructure at
one-variable generality — no dial, no Millennium part, is
touched by a projection existing.

**Census after landing: 11,897 strict / 12,247 total / 403 counted
modules; zero `sorry` terms tree-wide.**

## Backers since last landing

None new on the record since the last landing.
