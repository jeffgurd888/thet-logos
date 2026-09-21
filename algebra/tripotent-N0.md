# Tripotent N₀ and the linearization L

**Tier T1 — Assumed Primitive** (`N₀³ = N₀`);
**Tier T2 — Defined Operation** (`L(X) = X + N₀XN₀`);
**Tier T5 — Open/Withdrawn** (the `dim ker L = 4` claim).
Source: Gurd, *The Ontological Thet–LOGOS Framework* (Revised Draft, Nexus
Research, Sept 2026), §2.1.5 (Rung 5, Amber) — including the author's
explicit caveat.

## Setup

Let `N₀ ∈ M₂(ℝ)` be a tripotent: `N₀³ = N₀` (i.e. `N₀ N₀† N₀ = N₀`).

Define the real-linear operator on the ambient operator space:

```
L(X) = X + N₀ X N₀
```

## The withdrawn claim

An earlier version of the framework claimed:

```
dim_ℝ ker L = 4   ⟹   spacetime dimension fixed at 4        [WITHDRAWN]
```

The revised draft withdraws this as inconsistent in the form stated:
on `M₂(ℝ)`, a four-dimensional kernel would force `L ≡ 0`, hence
`N₀XN₀ = −X` for all `X`, implying `N₀ = −I`, which contradicts
`N₀³ = N₀` unless `N₀ = 0`.

**Consequences for this repository:**

1. `dim_ℝ ker L = 4` is **not asserted anywhere** — not in docs, not in
   Lean (no `sorry` target pretends it), not in Python.
2. It is logged in `../epistemic-ledger/LEDGER.md` as **Tier T5
   (Withdrawn)**.
3. The correct geometric meaning of `N₀`, if any, is an **open question**
   (Tier T5).

## What IS verified here (Tier T3)

`python/thet_logos/tro.py` checks on concrete matrix models:

- The TRO associativity law on random complex matrices.
- Tripotent identity `e e* e = e` for constructed tripotents
  (e.g. partial isometries from SVD with 0/1 singular values).
- The **inconsistency argument itself**: for random tripotents
  `N₀ ∈ M₂(ℝ)`, the kernel of the concrete `L(X) = X + N₀XN₀` is computed
  numerically, confirming the kernel dimension is *not* 4 in general —
  consistent with the withdrawal.

## Lean mirror

`lean/ThetLogos/TRO.lean` — `N0_tripotent : [N₀ N₀ N₀] = N₀` (T1 axiom),
`L` (T2 definition). No dimension theorem is stated.
