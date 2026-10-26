# Brick β1 — The Factorization M = 𝒯 · ℬ (PARTIAL by registered split)

*Landing dossier, 2026-10-26. Module:
`lean/ThetLogos/PlaneCrossingFactor.lean` (strict 41, zero
`sorry`, zero `native_decide`; main-tree build green, 3,398 jobs,
parent-verified). **Parts of the Clay Yang–Mills statement
closed by this landing: 0.** No positivity is claimed anywhere
in this module; 𝒜 ⪰ 0 (β2) remains L+/open.*

## What landed — the factorization itself, in full

- **`wilsonActionZero_split`** — the crossing action splits by
  base layer on *every* configuration: S₀ = S₀^top + S₀^bot, at
  every even N, all real β. No mixing term exists; the β
  scoping's reading of `IsZeroPlaq` is confirmed by proof.
- **The mechanism, eight link-value formulas.** The top word is
  `a·z'·a⁻¹·z⁻¹`; the bottom word is `a'·z·a'⁻¹·z'⁻¹` — the
  memo's swap, proved at density level: the two factors are the
  same shape of word with the roles of the two strata exchanged,
  read on different layers.
- **`planeCrossingMarginal_factor_top_bot`** — M = 𝒯 · ℬ at
  general (G, ρ): 𝒯 reads only time N/2−1, ℬ reads only time 0,
  each is independent of the other stratum, both equal 1 at
  β = 0, and the product reproduces Brick α's symmetry.

## The named remainder — β1-remainder (M)

One functional `𝒜` on *abstract* layer data with
`ℬ(z,z′) = 𝒜(τ₀z′, τ₀z)` as a theorem, and per-stratum symmetry
`𝒜(u,u′) = 𝒜(u′,u)`. What is missing is plumbing only: the cube
parametrization and the pi-measure transport (plus an in-cube
reflection for the symmetry). The mathematical risk — the
density-level identity — is discharged by this landing. There is
no contradiction with the scoping memo: 𝒯 and ℬ read different
layers, and the swap lives in the words, which is exactly why the
seat's square (one layer, twice) could not generalize as stated.

Axiom sets on spot-checked headlines: exactly
`[propext, Classical.choice, Quot.sound]`.

## Census effect

Strict 6,100 → **6,141**; attribute-inclusive 6,178 → **6,219**;
modules 208 → **209**; `sorry` placeholders unchanged at **6**.

## Backers since last landing

No new backers inscribed in this interval; the roll stands as
recorded in `BACKERS.md`. Every gift is published with the proof
stream, named as the giver wishes, amounts only with the giver's
permission — the standing reciprocity of this house.
