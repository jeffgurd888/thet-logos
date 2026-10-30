# A2-2-PROBE Landing — the telescoping seat check: PASS (K-A2 does not fire)

**Date:** 2026-10-29 · **Brick:** A2-2-PROBE (S–M), per
`scoping-a2-2-telescoping-2026-10-29.md` §3, against the statement registered by A2-2a.
**Verdict: PROBE PASS — seat evidence only, at two nonabelian seats.** The pre-registered
kill **K-A2 does NOT fire**. Cross-check registry entry: **BR1-005**.

**Fences, on the face: NO CLAIM. Parts of the official statement closed: 0. Dials 0/4.**
A PASS asserts nothing at general (G, ρ); it unlocks Route B's proof bricks (A2-2b
onward), it does not land them. Simulations audit and probe; they do not move the dials.

## Method

Python exact side (`routeb-general-scratch/a22probe_seat.py`, deterministic, seed
20261029): every block value is a polynomial in t = e^{−1/2} with rational coefficients,
recovered exactly by evaluation–interpolation (counts sanity-checked to sum to exactly
|G|⁴); identity checks are ℚ[t] polynomial identities; sign checks interval-certified
(50-digit enclosure). **Parent re-ran the script at landing: output byte-identical.**
Control first: Seat C (ℤ₅, 1-dim character) PASS — (T) exact on 6,550 checks, the abelian
quotient collapse exact, the fourth-power coefficient law exact in ℚ(ζ₅). The instrument
is trustworthy; the kill-bearing seats' verdicts stand on it.

## Results at the kill-bearing seats (β = 1)

- **Seat A (S₃, std):** (T) exact — 0 nonzero residuals over 17,552 checks (all u ×
  section u′, sections × all u′, 2,000 seeded random pairs). (P) PASS — Ψ's eigenvalues
  {0,0,0, 6.38×10⁻⁵, 1.686×10⁻³, 0.19572} (zeros exact), interval lower bound −1.0×10⁻⁹
  under the stated tolerance discipline, backed by the structural certificate (every
  c_π interval-certified ≥ 0); separate class-invariance exact.
- **Seat B (D₄, std):** (T) exact — 0 nonzero residuals over 67,536 checks. (P) PASS —
  eigenvalues {0,0,0, 4.979×10⁻⁵ (×3), 1.092×10⁻³, 0.24382}; class-invariance exact.
- **Coefficient law:** `c_π = (ĉ_π/dim π)⁴` holds as polynomial identities at both
  kill-bearing seats. Certified refinement from the control: at non-self-dual labels the
  law pairs k ↔ −k (`c_k = (ĉ_k·ĉ_{−k})²`); the §1.4 form is the self-dual special case.
  This caveat is strategy-bearing for A2-2c; the A₄ stretch was not run (its t-exponents
  are non-integral, outside the ℚ[t] discipline; information-only in any case).

## Certified correction, at the same volume

**R1 — the claim-path memo's literal quotient form `PlaqBlock = Φ(Hol(u)⁻¹ Hol(u′))` —
is CERTIFIED DEAD** at both kill-bearing seats: equal-quotient configuration pairs whose
block values differ by (1−t³)⁴/324 ≈ 1.1242×10⁻³ (Seat A: sections (e,e) vs (τ,τ)) and
(1−t⁴)⁴/1024 ≈ 5.4587×10⁻⁴ (Seat B: (e,e) vs (r,r)), intervals excluding 0. The A2-2a
registration's conditional correction is now discharged: the live statement is the
revised entry R2, registered in `ThetLogos.PlaquetteTelescoping`. The already-dead
readings R0/R3 stay dead regardless.

## Information-only records (no verdict attaches)

β = −1: (T) persists at both seats (0 residuals over the full re-run check sets) and Ψ
stays PSD there — as the fourth-power law predicts; a negative there would have falsified
the coefficient law, not (T). Leading order: the block's β⁰–β³ coefficients are
(u,u′)-independent at both seats; the first dependent coefficient is at β⁴, factoring as
const + (1/256)·χ_std(Hol u)·χ_std(Hol u′) at both seats (R4's shadow; A2-2d's fallback
label).

## Census

Unchanged (Python probe; no Lean content): **7,431 strict / 7,509 attribute-inclusive /
254 modules.**

## Backers since last landing

None recorded in this interval. (The backer roll is unchanged; gifts are named in
`BACKERS.md` exactly as each giver wishes, only after Jeff confirms a gift arrived.)
