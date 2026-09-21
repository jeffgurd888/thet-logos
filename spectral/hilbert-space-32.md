# The 32-state finite Hilbert space

**Tier T2 — Defined Operations** (the space, grading, real structure as
definitions); **Tier T3 — Proved/Checked** (their algebraic relations).
Source: Gurd, *The Ontological Thet–LOGOS Framework* (Revised Draft, Nexus
Research, Sept 2026), §2.1.6 (Rung 6, Magenta).

## H_F = ℂ³² — four chiral 8-blocks (T2)

```
ℂ³² = H_L ⊕ H_R ⊕ H_L^c ⊕ H_R^c = ℂ⁸ ⊕ ℂ⁸ ⊕ ℂ⁸ ⊕ ℂ⁸
```

Index ranges: `H_L = 0–7`, `H_R = 8–15`, `H_L^c = 16–23`, `H_R^c = 24–31`.

Each 8-block splits into a **2-dimensional lepton block** and a
**6-dimensional quark block** (2 isospin × 3 color triplet).

> **One generation only.** This is the standard one-generation finite
> space of the Connes–Chamseddine–Marcolli construction (including a
> right-handed neutrino and charge conjugates). Three generations require
> `ℂ⁹⁶` or `ℂ³² ⊗ ℂ³` with generation-mixing Yukawa matrices —
> **Tier T5 (Open)**.

## Partner map (T3: `p² = 1` checked)

```
p(k) = k + 16   for k < 16
p(k) = k − 16   for k ≥ 16
```

Particle ↔ antiparticle index swap. Proved in Lean
(`partner_involutive`), checked numerically in Python.

## Grading γ_F (T3: `γ_F² = 1`, self-adjoint, checked)

```
γ_F = diag(χ_k),   χ = (+1 on 0–7, −1 on 8–15, −1 on 16–23, +1 on 24–31)
```

`χ_{p(k)} = −χ_k`: grading flips under particle conjugation.

## Real structure J_F (T3: checked)

`(J_F v)_k = v_{p(k)}`, anti-unitary charge conjugation mapping states to
antiparticles. In the Lean/Python linear models it is represented by the
permutation matrix `U_J`, `(U_J)_{ij} = δ_{j,p(i)}`:

- `U_J² = 1` (Lean: `UJ_mul_self`; Python: exact integer matrix check).
- KO sign: `U_J · conj(γ_F) · U_J = −γ_F` (Lean T3, proof pending build).

## Lean mirror

`lean/ThetLogos/Scaffold32.lean` — `partner`, `gammaF`, `UJ_matrix` and
the theorems above. Proofs ported from unity-theory `CGurd/Spectral.lean`;
build pending in this repo (T3 until `lake build` succeeds).
