# D1-C3 CHECKS LANDING DOSSIER — 2026-11-01

**Item:** D1-C3 (Dial-1 lane) — the pre-check gauntlet,
stage 2, per the escape scoping §4.3 and the entry's pin
(`d1c3pin-landing-2026-11-01.md`).

## VERDICT: BOTH PRE-CHECKS PASS — THE GATE IS CLEARED

Where D1-A′ died at this exact gate (its tie was a theorem
for every π), D1-C3's condition discriminates. Neither kill
fires: **K-ESC-4 does not fire** (π₁ satisfies C3);
**K-ESC-5 does not fire** (piFlip fails C3).

**Artifact:** `lean/ThetLogos/DialOneGammaTraceChecks.lean` —
strict 13, defs 1 (in the pack's 6–14 band). Verified by the
coordinator in the main tree (build green, 3136 jobs); all
seven headlines on exactly
`[propext, Classical.choice, Quot.sound]`.

## The proved values

- `Tr (γ_F · π₁ (u1Gen α β)) = 0` identically: `π₁ (u1Gen α β)`
  is seat-diagonal with diagonal `i·(Aᵢα + Bᵢβ)`, and the
  γ-weighted table sums are exactly (0, 0) — discharged by ℤ
  shadows over the landed A/B tables. (`c3_pi1_holds`.)
- `Tr (γ_F · piFlip (u1Gen α β)) = 2α·i` **exactly**: the π₁
  trace plus the seat-8 `Matrix.single` perturbation
  (γ_F(8,8) = −1 against star(αi) − αi = −2αi). At (1, 0):
  2i ≠ 0. (`c3_piFlip_fails`.)
- The exclusion corollary, at exactly its registered rank:
  `DialOneStrengthenedC3 pi1` holds (base assembled
  clause-by-clause from π₁'s landed theorems; C3 by this
  module), and **`¬ DialOneStrengthenedC3 piFlip` — the
  strengthened set base + C3 EXCLUDES piFlip. It is the first
  Dial-1 condition set to do so.**

## Rank fence — what this is NOT

This is **not a forcing theorem and not a Dial-1
derivation.** C3 is one linear equation; the ν_R+e_R
double-flip compensator stands pre-registered as **K-ESC-6**
against any forcing claim at base + C3 (flipping both seats
restores the trace by +2α − 2α arithmetic; whether the
double-flip representation satisfies the full base set is
unproved — it is the Dial-1 lane's named next test, a new
scoping question, not part of this entry). **Dial 1: 0.**
NO CLAIM. Entry D1-C3 is COMPLETE as scoped (pin +
pre-checks); D1-A's and D1-A′'s kills stand untouched beside
it under the relabeling rule.

**Census after landing: 11,377 strict / 11,614 total / 390 counted
modules; zero `sorry` terms tree-wide.**

## Backers since last landing

None new on the record since the last landing.
