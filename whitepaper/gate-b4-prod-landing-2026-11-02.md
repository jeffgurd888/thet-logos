# B4-PROD LANDING DOSSIER — 2026-11-02

**Item:** B4-PROD (SHELF-7b-disc chain, GATE-B discharge
campaign) — the coefficient-product identity, ingredient 2's
core lemma.

## VERDICT: FULL at the registered interior form — and the boundary-radius form is REFUTED in-tree, by the B1c mechanism

**Artifact:** `lean/ThetLogos/DiscCoeffProduct.lean` —
strict 9, defs 0. Verified by the coordinator in the main
tree (build green, 2984 jobs); all six named results on
exactly `[propext, Classical.choice, Quot.sound]`. The
pack's pre-named PARTIAL seam did NOT trigger.

**Landed:** `discCoeff_mul` — for `DiscHolomorphic h R`,
`DiscHolomorphic k R`, and every interior presenting radius
0 < P < R:
`discCoeff (fun z => h z * k z) P = discConv (discCoeff h P)
(discCoeff k P)` (funext over n), with `discConv` = 8a's
antidiagonal Cauchy product. **Product holomorphicity at R
is PROVED** (`discHolomorphic_mul`), not assumed; the
same-radius corollary (`discCoeff_mul_of_lt_radius`) holds
under holomorphicity on a strictly larger disc. The
existence half landed standalone
(`hasFPowerSeriesOnBall_discConv_mul`: the product's power
series IS the ofScalars Cauchy-product series), and
uniqueness closed by `HasFPowerSeriesAt.eq_formalMultilinearSeries`
against `DifferentiableOn.hasFPowerSeriesOnBall` — the
scoping's registered route, step for step.

**The deviation, proved not papered:** the pack's literal
target — the identity presented AT the holomorphicity
radius R itself — is **FALSE**, by exactly the GATE-B1
mechanism: `discCoeff f R` reads only circle values at
‖z‖ = R, which open-disc holomorphicity does not
constrain. Refuted in-module at full rank:
`discCoeff_mul_boundary_not` (witness h = z⁻¹ on the
circle / 0 inside, k = id: the product's 0th coefficient
is 1 by the landed boundary computation; the convolution's
is 0, via the new `discCoeff_id_zero`). The landed interior
form is what the scoping registered (§2b: holomorphic on a
larger disc, presenting strictly inside) and exactly
B4-UNIT's consumption shape. Cost to the campaign: zero —
every consumer presents at an interior radius.

**Campaign state:** REPAIR ✔, FIN ✔, PROD ✔; B4-TAIL
(multiplicity iteration + tail identification) fires next;
then B4-UNIT (zero-free ⇒ unit, consuming PROD + TAIL),
B4-ASM ⇒ unconditional equality, GATE-B closes for the
disc chain.

## Fences

NO CLAIM; all dials 0/4. 7b-in-full remains pin-blocked.

**Census after landing: 12,270 strict / 12,677 total / 424 counted
modules; zero `sorry` terms tree-wide.**

## Backers since last landing

None new on the record since the last landing.
