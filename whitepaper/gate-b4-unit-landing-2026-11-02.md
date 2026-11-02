# B4-UNIT LANDING DOSSIER — 2026-11-02

**Item:** B4-UNIT (SHELF-7b-disc chain, GATE-B discharge
campaign) — ingredient 2's conclusion: a zero-free factor's
calculus value is a unit.

## VERDICT: FULL — the pre-named seam did not trigger

**Artifact:** `lean/ThetLogos/DiscZeroFreeUnit.lean` —
strict 3, defs 0. Verified by the coordinator in the main
tree (build green, 2986 jobs); headline and both helpers
on exactly `[propext, Classical.choice, Quot.sound]`.

**Headline:** `isUnit_hfcDisc_of_zeroFree` — in the
chain's standing Banach-algebra context, for
`(spectralRadius ℂ a).toReal < R₀ < R₂ < R`,
`DiscHolomorphic h R`, and h zero-free on
`closedBall 0 R₂`: `IsUnit (hfcDisc a (discCoeff h R₀))`.
No hypotheses beyond the pack's statement. The reciprocal
packaging — the pre-named friction point — went through
directly (`DifferentiableOn.inv`; `DiscHolomorphic` is
0 < R ∧ DifferentiableOn on the open ball): the reciprocal
is DiscHolomorphic at an intermediate R₁; the product's
coefficients are the delta sequence (circle-integral
congruence on the presenting sphere ‖z‖ = R₀ < R₂, where
h z · (h z)⁻¹ = 1, plus B3′'s `discCoeff_const`); B4-PROD
at the presenting radius, B3′'s multiplicativity with
B2′'s sharp summabilities for h and for the reciprocal,
and 8a's commutativity make the inverse two-sided — an
explicit `Units` witness.

**Campaign state:** REPAIR ✔, FIN ✔, PROD ✔, TAIL ✔,
UNIT ✔. **B4-ASM is the last brick:** assemble
`DiscFactorisationHyp'` from TAIL (factorisation + zeros
off the spectrum) and UNIT (the unit clause), feed
B4-REPAIR's adapter, and land `shelf7bDiscInterior_proved`
— the disc spectral mapping equality, unconditional.
GATE-B then closes for the disc chain.

## Fences

NO CLAIM; all dials 0/4. 7b-in-full remains pin-blocked.

**Census after landing: 12,287 strict / 12,694 total / 426 counted
modules; zero `sorry` terms tree-wide.**

## Backers since last landing

None new on the record since the last landing.
