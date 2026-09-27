# Chromatic Flow — the 10-rung ladder

Source: Gurd, *The Ontological Thet–LOGOS Framework* (Revised Draft, Nexus
Research, Sept 2026), §2. Attribution: **Jeffrey Michael Gurd, Nexus
Research.**

## Status of the diagram

> The 10-rung Chromatic Flow is an **organizational and mnemonic device**.
> It does **not** constitute a formalized Möbius-bundle construction with
> explicit transition maps (Framework §2, Abstract). The return loop
> (Rung 6 → Rung 4) is indicated diagrammatically only.

Each rung's *mathematical content* is tiered independently in
`../epistemic-ledger/LEDGER.md`. The ladder itself organizes; it proves
nothing.

## The ladder

| Rung | Name | Color | Content (tier) |
|---|---|---|---|
| 1 | Void (∅) | Black | Assumed pre-metric origin — T1 |
| 2 | Distinction ⟨a,b,c⟩ = ab†c | Cobalt | Ternary product, three-point context — T2/T3 |
| 3 | Thet Primitive Θ = (θ, θ†) | Purple | Forward projection y = θx; five-step nilpotent ladder = **working hypothesis** — T1 |
| 4 | LOGOS Engine K = −log ∆ | Crimson | Modular flow σ_s(X) = e^{isK}Xe^{−isK}, KMS — T2/T3 |
| 5 | Tripotent Variety N₀³ = N₀ | Amber | Reference element; **dim ker L = 4 claim WITHDRAWN** — T1/T5 |
| 6 | 32-State Spectrum H_F = ℂ³² | Magenta | One generation ℂ⁸⊕ℂ⁸⊕ℂ⁸⊕ℂ⁸; three generations need ℂ⁹⁶ or ℂ³²⊗ℂ³ — T2/T3/T5 |
| 7 | Spectral Triple D_F | Cyan | 32×32 block matrix (A, B, C, E) — T2/T3 |
| 8 | Order Conditions | Emerald | Order-zero vs order-one; C, E vanish or restricted → Yukawa Y_u,Y_d,Y_e,Y_ν, Majorana Y_R — T3/T4 |
| 9 | Thet Engine (∆gap) | Indigo | Conceptual discrete state machine perturbing ∆ = min{\|λ\|>0}; **no hardware realization asserted** |
| 10 | Epistemic Ledger | White | This ledger — the tier system itself |

See `rungs.md` for per-rung detail.

## Thet Engine (Rung 9) — computational realization

The "Thet Engine" is realized in this repository as the numerical
perturbation engine in `../python/thet_logos/spectral_gap.py`:

```
D_H = D_F + H,   H = H†   →   Δ(H) = min { |λ| ∈ spec(D_H) : |λ| > 0 }
```

It sweeps perturbations and tracks the gap. It is a **simulation**
(T3 numerical); per the strict epistemic rule
(Theorem ≠ Simulation ≠ Experiment ≠ Device) it is not a device, and no
hardware realization is asserted.

## Lean mirror

`lean/ThetLogos/Chromatic.lean` — `ChromaticRung` structure (index, name,
color, content tier) and the rung table as data. No rung-transition
theorems are claimed (that would be the formal Möbius topology — T5).
