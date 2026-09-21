# Ternary TRO theory

**Tier T2 — Defined Operations** (product, tripotent, linearization);
**Tier T3 — Proved/Checked** (identities on models);
**Tier T5 — Open/Withdrawn** (the dim ker L = 4 claim — WITHDRAWN).
Source: Gurd, *The Ontological Thet–LOGOS Framework* (Revised Draft, Nexus
Research, Sept 2026), §2.1.2 / §2.1.5.

## The product (T2)

```
⟨a, b, c⟩ := a b† c
```

- Linear in `a` and `c`, conjugate-linear in `b`.
- Associativity law: `[[a b c] d e] = [a b [c d e]] = [a [d c b] e]`.

## Tripotents (T1/T2)

An element `e` is a **tripotent** if `[e e e] = e`, i.e. `e e† e = e`.
The distinguished tripotent `N₀` with `N₀³ = N₀` is a **T1 assumed
primitive** (Framework §2.1.5: reference element `N₀ ∈ M₂(ℝ)`).

## Linearization (T2 definition; T5 withdrawn consequence)

The **linearization** at `N₀` is the real-linear map

```
L(X) = X + N₀ X N₀
```

### Withdrawal notice (Tier T5)

The earlier claim — that `L(X) = X + N₀XN₀` yields `dim_ℝ ker L = 4` and
thereby fixes spacetime dimension — is **withdrawn** following the
author's revised draft (§2.1.5): as stated on `M₂(ℝ)` the assertion is
inconsistent, since a four-dimensional kernel would force `L ≡ 0`,
implying `N₀ = −I`, which contradicts the tripotent relation unless
`N₀ = 0`. **This repository does not assert `dim_ℝ ker L = 4`.** The
correct geometric meaning of `N₀`, if any, remains an open question
(Tier T5). See `tripotent-N0.md`.

## Lean mirror

`lean/ThetLogos/TRO.lean`:
- `ternary (a b c : ℂ) : ℂ := a * conj b * c` (T2)
- `ternary_assoc_scalar` — proved (T3 after build)
- `N0_tripotent` (T1 axiom); `L` (T2 def); the withdrawn dimension claim
  is **absent** — no `sorry` pretends to prove it.
