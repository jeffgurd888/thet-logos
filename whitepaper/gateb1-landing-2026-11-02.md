# GATE-B1 LANDING DOSSIER — 2026-11-02

**Item:** GATE-B1 (SHELF-7b-disc, brick 1) — the disc
coefficient layer at the sharp scale.

## VERDICT: PARTIAL — B1a, B1b, B1d FULL (the B1d seam did not trigger); B1c KILLED AS FROZEN, its corrected interior form landed in its place; B2/B3 as frozen stand under the same cloud and do NOT fire

**Artifact:** `lean/ThetLogos/HfcDiscSharp.lean` — strict
18, defs 0 (at the 18–32 band floor). Verified by the
coordinator in the main tree (build green, 2981 jobs); all
ten checked headlines on exactly
`[propext, Classical.choice, Quot.sound]`.

**Landed FULL:** `discCoeff_indep` (B1a — radius
independence of the coefficients, annulus Cauchy–Goursat on
the scalar kernel); `discSummable_discCoeff` (B1b —
Cauchy-estimate summability at every interior scale);
`summable_smul_pow_of_spectralRadius_lt` (B1d — the sharp
spectral-radius summability via Gelfand's formula and
geometric comparison at an intermediate scale; **the
pre-registered B1d PARTIAL seam did not trigger**).

**K-B1c — `Shelf7bB1ScalarEval` is FALSE as frozen, killed
with an in-tree counterexample.** The frozen Prop presents
the coefficients at the *boundary* radius
(`discCoeff f R` integrates over the circle ‖z‖ = R), but
`DiscHolomorphic f R` constrains f only on the OPEN ball.
Proved in-module: for f = 0 off the unit circle and f = 1 on
it, `discCoeff f 1 0 = 1` while the interior value is 0 —
`shelf7bB1ScalarEval_not : ¬ Shelf7bB1ScalarEval f 1`.
**Corrected form landed as a new entry** (relabeling rule):
for every interior presenting radius R' < R,
`scalarEval (discCoeff f R') z = f z` on the disc
(`scalarEval_discCoeff_eq_of_lt`, plus the presentation-free
`scalarEval_discCoeff_eq_of_indep` via B1a). B1d is
unaffected (it consumes B1b only; the boundary-radius Cauchy
bound is valid as proved).

**The cloud over B2/B3 as frozen — stated exactly:** the
pin's `Shelf7bB2Forward` and `Shelf7bDisc` also evaluate
`hfcDisc` at the boundary presentation `discCoeff f R`, so
they inherit the defect: with the same witness shape (a = 0,
whose spectrum is {0} and whose `hfcDisc` reads the constant
boundary coefficient 1, against f '' {0} = {0}) the forward
inclusion is refutable in principle. Their formal decision
(refutation in-tree, or salvage under a stated side
condition) is assigned to the repair brick — **B2/B3 do not
fire off the frozen forms.** The repair (7B-PIN-2, a new
entry): re-freeze B2′/B3′ against an **interior
presentation** — a presenting radius R₀ with
`(spectralRadius ℂ a).toReal < R₀ < R` — where B1a + the
corrected B1c make the chain sound.

**Citation note (minor, on the record):** the refresh's
`HasFPowerSeriesOnBall` citations were off by a few lines
(actual :668/:686/:697; the last is the one used); all other
citations verified exact.

## Fences

7b-disc only; NOT 7b-in-full (gated at XL on the pin's
face). NO CLAIM; dials 0/4.

**Census after landing: 12,108 strict / 12,476 total / 412 counted
modules; zero `sorry` terms tree-wide.**

## Backers since last landing

None new on the record since the last landing.
