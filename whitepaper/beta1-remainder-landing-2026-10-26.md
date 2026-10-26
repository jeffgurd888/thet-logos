# Brick β1-Remainder — One Kernel 𝒜, Two Evaluations

*Landing dossier, 2026-10-26. Module:
`lean/ThetLogos/PlaneCrossingCube.lean` (strict 34, defs 19,
zero `sorry`, zero `native_decide`; main-tree build green, 3,399
jobs, parent-verified). **Parts of the Clay Yang–Mills statement
closed by this landing: 0.** No positivity is claimed; 𝒜 ⪰ 0
(β2) remains L+/open — this landing makes that question exactly
statable, nothing more.*

## What landed

Layer data in corpus-native types — `LayerSite N`, `LayerLink N`,
exactly the link set of one time-0 Wilson-action class — the two
extractions `tauTop` (layer N/2−1) and `tauBot` (layer 0), and
the one functional:

- **`layerKernel` 𝒜** — the stratum Haar integral of the
  one-layer Boltzmann factor, defined intrinsically on layer
  data.
- **`planeCrossingTop_eq_layerKernel`** — 𝒯(z,z′) =
  𝒜(τ⁺z, τ⁺z′).
- **`planeCrossingBot_eq_layerKernel`** — ℬ(z,z′) =
  𝒜(τ₀z′, τ₀z), with the swap β1's bottom word requires.
- **`planeCrossingMarginal_layerKernel`** — the single-𝒜 form:
  M(z,z′) = 𝒜(τ⁺z, τ⁺z′) · 𝒜(τ₀z′, τ₀z), at general (G, ρ),
  every even N, all real β.
- **`layerKernel_symm`** — 𝒜(u,u′) = 𝒜(u′,u). The reflection
  that proves it is *stratum inversion*, measure-preserving in
  corpus terms: the inverted word's inverse, conjugated by the
  stratum value, is the swapped word, and the trace sees neither
  inversion nor conjugation.

Axiom sets on all four headlines: exactly
`[propext, Classical.choice, Quot.sound]`.

## The state of the finite theory's last wall, exactly

Everything around (H-PF) is now proved structure: the pairing
factors through the gauge twirls (α-remainder), the marginal
factors through the one-layer kernel (β1 + this landing), and by
Schur's product theorem the remaining question is one sentence:

> **Is `layerKernel` 𝒜 positive semidefinite as a kernel on
> layer data, on gauge-invariant observables, at general (G, ρ)?**

That is β2 — L+/open, with its mechanism scoping (S) fired
alongside this landing. At U(1) the answer is yes (Route C,
2026-10-23). At the (S₃, std) seat the computation says yes with
the null directions exactly the non-invariant ones. The general
proof is the wall.

## Census effect

Strict 6,141 → **6,175**; attribute-inclusive 6,219 → **6,253**;
modules 209 → **210**; `sorry` placeholders unchanged at **6**.

## Backers since last landing

No new backers inscribed in this interval; the roll stands as
recorded in `BACKERS.md`. Every gift is published with the proof
stream, named as the giver wishes, amounts only with the giver's
permission — the standing reciprocity of this house.
