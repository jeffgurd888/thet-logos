# Period Stage N1 — The Quadrature Period and Its Finiteness

*Landing dossier, 2026-10-26. Module:
`lean/ThetLogos/SolidBodyPeriodQuad.lean` (strict 4, defs 3, zero
`sorry`, zero `native_decide`; main-tree build green, 3,482 jobs,
parent-verified on the shipped text). **Parts of the Clay
Yang–Mills statement closed by this landing: 0.** Classical
mechanics, abstract body only, frozen coefficients.*

## What landed

The quadrature period, derived — not postulated. From the Euler
equations, the middle momentum component obeys Ṁ₁ = c·M₀·M₂ with
c = `quadCoeff` = (I₃−I₁)/(I₁I₃) > 0; the quarter-orbit integral
under u = M₁², times four quarters, gives

  periodQuad b Λ E = (2/c) · ∫₀^uMax (u · m1SqOfU · m3SqOfU)^(−1/2) du

— agreeing with the scoping's registered form, with the constant
made explicit (no discrepancy finding).

**Finiteness in both regular bands**
(`periodQuad_intervalIntegrable_top` / `_bot`): the analytic core
`intervalIntegrable_inv_sqrt_vanish` — one affine factor vanishing
at the endpoint, the other bounded below by a positive constant —
makes the −1/2-power product interval-integrable; the bands'
endpoint values from N0 and the portrait supply the positivity
the argument consumes.

Axiom sets: exactly `[propext, Classical.choice, Quot.sound]`.

## Fences

This is the **quadrature** period. Its identification with
trajectory return times is stage N4 — deferred, classical T4 —
and the module says so on its face. No divergence is claimed
here: that is stage N2, next on the bench — the statement that
periodQuad(E) ≥ c₁·|log|E − E_sep|| − c₂ as E approaches the
separatrix level, by the comparison the scoping registered.

## Census effect

Strict 6,034 → **6,038**; attribute-inclusive 6,112 → **6,116**;
modules 204 → **205**; `sorry` placeholders unchanged at **6**.

## Backers since last landing

No new backers inscribed in this interval; the roll stands as
recorded in `BACKERS.md`. Every gift is published with the proof
stream, named as the giver wishes, amounts only with the giver's
permission — the standing reciprocity of this house.
