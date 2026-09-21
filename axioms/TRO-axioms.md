# TRO ternary product axioms

**Tier T2 — Defined Operations** (the product itself);
**Tier T3 — Proved/Checked** (associativity on models: numerical check +
scalar Lean proof).
Source: Gurd, *The Ontological Thet–LOGOS Framework* (Revised Draft, Nexus
Research, Sept 2026), §2.1.2 (Rung 2, Cobalt).

## Definition (T2)

A **ternary ring of operators (TRO)** is a complex vector space `T` with a
ternary product

```
⟨a, b, c⟩ = a b† c
```

linear in the outer slots, conjugate-linear in the middle slot.
Plain-English (Framework Table 1): *contextual measurement of c via a
and b* — a minimal three-point context for observation.

## Axioms — associativity law (T3: standard NCG facts)

For all `a, b, c, d, e ∈ T`:

```
[[a b c] d e]  =  [a b [c d e]]  =  [a [d c b] e]
```

i.e. in operator notation:

```
(a b† c) d† e  =  a b† (c d† e)  =  a (d c† b)† e
```

## Canonical model (T3: checked)

`M_{m,n}(ℂ)` with `[a b c] = a b* c` satisfies the TRO axioms. Checked
numerically in `python/thet_logos/tro.py` on random matrices.

The scalar case `T = ℂ`, `[a b c] = a · conj(b) · c`, is proved in Lean
(`ThetLogos.TRO.ternary_assoc_scalar`; Tier T3, machine-check pending
build).

## Lean mirror

`lean/ThetLogos/TRO.lean` — `ternary` definition, `IsTRO` class,
`ternary_assoc_scalar` theorem.
