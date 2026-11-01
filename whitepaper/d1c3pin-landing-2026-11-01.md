# D1-C3 PIN LANDING DOSSIER — 2026-11-01

**Item:** D1-C3 (Dial-1 lane) — statement pin, gauntlet stage 1,
per the escape scoping
(`dial1-escape-scoping-2026-11-01.md`, Family 3, rank #1) and
Jeff's fire order under the 2026-11-01 FULL SEND. A NEW ENTRY
under the relabeling rule: D1-A's kill and D1-A′'s kill stand
untouched beside it.

**Status: PIN LANDED.** The pin asserts neither pre-check; the
gauntlet's gate is the checks module that follows.

**Artifact:** `lean/ThetLogos/DialOneGammaTracePin.lean` —
strict 5, defs 5 (in the pack's band). Verified by the
coordinator in the main tree (build green, 3135 jobs);
headlines on exactly `[propext, Classical.choice, Quot.sound]`.

## What is pinned

- `u1Gen (α β : ℤ) : AF` — the Lie-algebra element whose
  exponential curve is the landed `u1ParamGen` (ℂ-component
  `(α:ℂ)·I`, zero ℍ-component, scalar M₃-component
  `(β:ℂ)·I • 1`); α, β bound, no value named.
- `C3 (π) : Prop := ∀ α β : ℤ, Matrix.trace (gammaF * π
  (u1Gen α β)) = 0` — π at the FIRST power against the
  partner-ODD `gammaF` (`gammaF_partner_flip`, T1): the two
  features that escape `lifted_diag_partner`, stated on the
  face with the R2 contrast (γ against the lifted product
  vanishes identically — K-ESC-7). C3 names no weight, no
  sector, no Yukawa, no table.
- `DialOneStrengthenedC3 := DialOneBase ∧ C3`. The D1-A′
  SeatTie is omitted on the face: it is a theorem for every π
  (`seatTie_universal`), so including it would add nothing.
- The forcing target is cited unchanged:
  `DialOneForcing` over the COMMON HYPERCHARGE MATRIX from
  the D1-A′ pin. **No new forcing Prop is stated and no
  forcing is attempted** — K-ESC-6 (the ν_R+e_R compensator)
  is registered on the face against any forcing claim at
  base + C3; this entry is pin + pre-checks only, as scoped.

## Kills registered on the pin's face

K-ESC-4 (π₁ fails C3 ⇒ mis-posed, entry dies); K-ESC-5
(piFlip passes C3 ⇒ no discrimination, entry dies); K-ESC-6
(compensator, against forcing claims). Pre-check expectations
from the scoping's T2 arithmetic: C3(π₁) holds (coefficients
(0, 0)); `Tr (γ_F · piFlip (u1Gen α β)) = 2α·i`, nonzero at
(1, 0). The proofs, not the arithmetic, are the verdict.

**Dial 1: 0 — on every outcome of this entry, including FULL.**
NO CLAIM.

**Census after landing: 11,364 strict / 11,597 total / 388 counted
modules; zero `sorry` terms tree-wide.**

## Backers since last landing

None new on the record since the last landing.
