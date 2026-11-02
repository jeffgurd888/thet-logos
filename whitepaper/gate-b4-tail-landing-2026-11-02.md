# B4-TAIL LANDING DOSSIER — 2026-11-02

**Item:** B4-TAIL (SHELF-7b-disc chain, GATE-B discharge
campaign) — multiplicity iteration + tail identification:
ingredient 3's factorisation half.

## VERDICT: FULL — the pre-named PARTIAL seam did not trigger; the factorisation landed stronger than the pack required

**Artifact:** `lean/ThetLogos/DiscFactorisationTail.lean`
— strict 14, defs 0. Verified by the coordinator in the
main tree (build green, 3001 jobs); both headlines on
exactly `[propext, Classical.choice, Quot.sound]`.

**Headlines:** `discFactorisationTail` — there exist a
list `lam` and a function `h` with: `lam.count l` =
`analyticOrderNatAt (fun z => f z - mu) l` on B4-FIN's
`zeroFinsetClosedBall` and 0 off it (support exactly that
Finset); `DiscHolomorphic h R`; **h zero-free on
`closedBall 0 R₂`**; and the factorisation
`f z - mu = (lam.map fun l => z - l).prod * h z` for
**all z** — stronger than the pack's ball-0-R form, because
the dslope identity is global. And
`discCoeff_factorisationTail`: at 0 < R₀ < R, the
coefficient identity in the two-factor form B4-ASM will
consume, via B4-PROD applied once to the global
factorisation.

**The hard step, as it actually went:** multiplicity is
the pin's `analyticOrderNatAt`; removal is the
order-fold iterated `dslope`
(`HasFPowerSeriesAt.eq_pow_order_mul_iterate_dslope` +
`iterate_dslope_fslope_ne_zero`); order transport across
distinct points goes through `analyticOrderNatAt_mul` with
the already-removed factor a unit at the next point. The
scoping called this the hardest glue in the campaign and
priced it M with a named seam; the pin's API carried it
whole. Supporting lemmas landed for the single-zero step
(`discFactorStep`), the distinct-list induction
(`exists_discFactorisation_of_list`), and the B2′
summability transport packaging
(`discHolomorphic_factorisationTail` — cited to B2′'s
`summable_norm_smul_pow_discCoeff_interior`, not reproved,
per the pack).

**Campaign state:** REPAIR ✔, FIN ✔, PROD ✔, TAIL ✔.
B4-UNIT (zero-free ⇒ unit, via the reciprocal series and
PROD) fires next; B4-ASM then assembles DiscFactorisationHyp′
and the unconditional disc spectral mapping equality —
GATE-B closes for the disc chain.

## Fences

NO CLAIM; all dials 0/4. 7b-in-full remains pin-blocked.

**Census after landing: 12,284 strict / 12,691 total / 425 counted
modules; zero `sorry` terms tree-wide.**

## Backers since last landing

None new on the record since the last landing.
