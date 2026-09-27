# Gauge algebra A_F = ℂ ⊕ ℍ ⊕ M₃(ℂ)

**Tier T2 — Defined Operations** (algebra, representations);
**Tier T3 — Proved/Checked** (order-zero identity: Lean proof + numerical
check).
Source: Gurd, *The Ontological Thet–LOGOS Framework* (Revised Draft, Nexus
Research, Sept 2026), §§2.1.6, 2.1.8, §3.

## The algebra and its representation (T2)

```
A_F = ℂ ⊕ ℍ ⊕ M₃(ℂ)
```

`π : A_F → End(ℂ³²)` is **asymmetric**: the quaternion algebra `ℍ` acts
non-trivially on `H_L` (indices 0–7) and is replaced by complex-scalar
actions on the conjugate sectors, so that order-zero is preserved under
`J_F`. Concretely (Option A ordering):

- `H_L` (0–7): `0,1 = ν_L, e_L` carry the quaternionic doublet `q`;
  `2–7` carry `q ⊗ color` (color-diagonal).
- `H_R` (8–15): `8 = ν_R` carries `u1`, `9 = e_R` carries `conj u1`;
  `10–15` carry `u1 · color` / `conj u1 · color`.
- Antiparticle blocks (16–31): `π(a)` acts as zero (reached via the
  opposite representation).

The **opposite representation** (Framework §2.1.8, explicit convention):

```
π°(b) = J_F π(b)* J_F⁻¹        (Lean: piOp via U_J · π(b)ᵀ · U_J)
```

## Order-zero condition (T3: proved/checked)

```
[π(a), π°(b)] = 0    for all a, b ∈ A_F
```

Uncouples matter and antimatter actions.

- **Lean:** `ThetLogos.FiniteSpectralTriple.order_zero_condition` — proof
  ported from unity-theory `CGurd/Spectral.lean`. The argument is
  structural: `π(a)` is supported on indices `< 16` while `π°(b)` is
  supported on indices `≥ 16`, so both products vanish termwise.
  T3 after a successful build; "proof pending build" until then.
- **Numerical:** `python/thet_logos/order_zero.py` checks
  `‖[π(a), π°(b)]‖ < 1e-14` for generators and random algebra elements —
  T3 (numerical), following the framework's illustrative fragment (§4).

## Generator count (for the order-one census)

A convenient real generating set of `A_F`:

- `ℂ`: 2 real generators (1, i)
- `ℍ`: 4 real generators (1, i, j, k as 2×2 complex matrices)
- `M₃(ℂ)`: 18 real generators (matrix units E_ij and iE_ij)

**Total: 24 real generators.** The full order-one condition must hold for
all pairs `(a, b)` of generators: **24 × 24 = 576 commutator pairs**.
Any claim of "order-one verified" that checks fewer pairs — e.g. the
single-probe `[[D_F, P₊], P₋] = 0` — is a *probe*, not the full condition.
