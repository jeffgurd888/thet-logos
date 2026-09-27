# Modular time: the corrected formal core

**Status.** Tier T1 (proved) + Tier T2 (definitions) in
`lean/ThetLogos/ModularTime.lean`; numerical checks Tier T3/T4 in
`python/thet_logos/`. This document records four mathematical corrections
(2026-09-25) to the Heat–Gravity–Time program, plus the proved T1
scalar-flow triviality (2026-09-26). Nothing here is a physical
derivation: see *Three claims* below.

**Proved 2026-09-26 (Tier T1, no sorry).** In the eigenbasis, with
σ_s(a) = ρ^{is}aρ^{−is}:
- `[ρ,a] = 0 ⟹ σ_s(a) = a` (`diagFlow_trivial_of_commute`): where two
  weights coincide the modular phases cancel; where they differ, the
  commutator forces the matrix entry to vanish.
- Scalar modular unitaries act trivially (`scalar_conj_trivial`).
- At constant weights the flow is scalar conjugation
  (`diagFlow_const_eq_scalarConj`), hence trivial
  (`diagFlow_trivial_of_const`).
- **Maximal ignorance gives trivial modular flow**
  (`maximallyMixed_flow_trivial`); non-central information gives temporal
  flow. The converse (trivial flow on all of an algebra ⟹ ρ = I/N) is
  deliberately not formalized: on a proper subalgebra a non-scalar ρ can
  lie in the commutant.

## 1. The synthesis

The architecture, corrected:

```
(ρ, D_F, β)  →  K(ρ, D_F, β)  →  σ_s  →  T
```

Conceptually:

```
Information + Heat + Geometry  →  Modular Time.
```

Time is **derived**, not primitive. Given a faithful state ρ, a Dirac
operator D_F, and an inverse temperature β, the thermal state

```
ρ_β = e^{−βD_F²} / Z,   Z = Tr(e^{−βD_F²})
```

determines the modular generator K_ρ = −ln ρ_β, which determines the
modular flow σ_s, which **is** the time parameter (Connes–Rovelli thermal
time). No independent operator T is postulated. This removes the weakest
primitive of the earlier ternary formulation: the old T-step (a probe
readout) is the observable trace of the derived flow, not a fourth input.

## 2. Correction: the condition for time is non-centrality, not ρ ≠ I/N

For σ_s(a) = ρ^{is} a ρ^{−is}, the flow acts trivially on a **given**
observable iff [ρ, a] = 0. The flow is trivial as an automorphism iff ρ
is central. For the full matrix algebra M_N(ℂ) the center is ℂ·I, so for a
state (Tr ρ = 1):

```
ρ = I/N   ⟹   σ_s(a) = a   for every a.
```

The converse direction needs care: ρ ≠ I/N guarantees the flow is
nontrivial *somewhere* (ρ is non-central, so some observable sees it),
but it does **not** guarantee nontrivial flow on every subalgebra. The
relevant condition is whether ρ is non-central **relative to the algebra
being acted upon** — this matters for the 32×32 model, where we may probe
subalgebras of M_32(ℂ).

Note the sign of the slogan: ρ = I/N is the maximally mixed state —
maximal von Neumann entropy, maximal ignorance. Time stops at maximal
ignorance and flows where information is present. (An earlier draft had
this backwards.)

## 3. Correction: K_ρ := −ln ρ, and ln Z drops out of the flow

For the thermal state ρ = e^{−βD_F²}/Z:

```
−ln ρ = βD_F² + (ln Z)·I.
```

Define the modular Hamiltonian as

```
K_ρ := −ln ρ,   so   K_ρ = βD_F² + (ln Z)·I   (thermal case).
```

The scalar (ln Z)·I commutes with everything, hence cancels in
conjugation:

```
σ_s(a) = e^{isK_ρ} a e^{−isK_ρ} = e^{isβD_F²} a e^{−isβD_F²}.
```

The flow sees only βD_F². Calling βD_F² + ln Z "the modular Hamiltonian"
was imprecise terminology; the object is K_ρ, and its traceless part drives
the flow. (Lean: `modularEigenvalue_diff` — the ln Z cancellation in
spectral form, proved.)

## 4. The precise ternary architecture

Primitive inputs:

```
𝔗 = ρ        (Information — the state)
ℌ = β        (Heat — the inverse temperature)
𝔊 = D_F      (Geometry — the finite Dirac operator)
```

Synthesized temporal generator:

```
K_{𝔗,ℌ,𝔊} = −ln ρ,     𝔗_s(a) = e^{isK} a e^{−isK}.
```

At the thermal fixed point:

```
K_{𝔗,ℌ,𝔊} = βD_F² + (ln Z)·I.
```

The conceptual equation:

```
TIME = ModularFlow[Information, Heat, Geometry].
```

The fixed-point iteration is therefore reformulated without a primitive T:

```
X_n = (D_n, ρ_n, β_n, Δ_n, …)
ρ_{n+1} = e^{−β_n D_n²} / Tr(e^{−β_n D_n²})
K_{n+1} = −ln ρ_{n+1}
σ_s^{(n+1)}(a) = e^{isK_{n+1}} a e^{−isK_{n+1}}      (derived, not postulated)
```

Fixed point:

```
X_* = C(ρ_*, β_*, D_*, σ_*, Δ_*),
ρ_* = e^{−β_*D_*²} / Tr(e^{−β_*D_*²}),   Δ_* > 0.
```

Engines #9 (Triple Point) and #10 (Synthesis) implement exactly this
iteration; their old "T_dt" docstring language is superseded by the above.

## 5. The spectral gap gives a scale, not a theorem

For D_F ψ_j = λ_j ψ_j: D_F² ψ_j = λ_j² ψ_j, and

```
ρ ψ_j = e^{−βλ_j²}/Z · ψ_j,    κ_j = βλ_j² + ln Z.
```

Hence the modular eigenvalue differences (the ln Z cancels — §3):

```
κ_i − κ_j = β(λ_i² − λ_j²),
```

so the modular oscillation between two spectral modes has (dimensionless)
frequency set by β(λ_i²−λ_j²). The gap Δ = min_{λ_j≠0}|λ_j| enters through
Δ² as the characteristic scale:

```
D_F → D_F² → βD_F² → modular frequency.
```

**Caution (do not promote):** we do NOT claim ω_modular = c_T·Δ²/ℏ as a
theorem. The gap gives a characteristic scale; an actual physical time
calibration c_T has to be defined and justified theoretically or
experimentally. This is a physical-interpretation claim (see below), not a
model property.

## 6. Correction: the KMS check is the identity, not the commutator

[ρ_0, K] = 0 with K = −ln ρ_0 is nearly automatic and proves nothing. The
check that matters is the KMS identity itself:

```
ω(a σ_{−i}(b)) = ω(ba),    ω(a) = Tr(ρ_0 a).
```

For finite-dimensional systems this is exactly implementable — and it is
what the engines already test (`modular_flow.py`, `engine_cycle.py`,
`thermalize.py`, `ternary.py`, `integration.py` all verify the cyclicity
form directly, to 1e-15–1e-20). The formal core adopts the identity, not
the commutator, as the stationarity check.

## 7. The zero-sorry verification target (finite-dimensional)

1. Construct D_F. → engine `spectral_gap.py`; Lean `Scaffold32` (T2/T3)
2. Construct a faithful 32×32 ρ. → `thermalize.py` (T4)
3. Calculate S(ρ). → `thermalize.py`: S_* = 3.234039 (T4)
4. Construct the thermal ρ_β. → all thermal engines (T4)
5. Verify normalization and positivity. → `thermalize.py` (T4); Lean target (T1)
6. Verify the KMS identity. → engines, 1e-15–1e-20 (T4); Lean target (T1)
7. Construct the modular automorphism. → `modular_flow.py` (T3)
8. Measure nontriviality on selected observables. → non-centrality test,
   §2 (engine target; Lean target)
9. Track Δ(D_F) under iteration. → `ternary.py`, `integration.py` (T4)
10. Test whether the fixed point exists. → Triple Point Modes A/C,
    Synthesis Modes A/B (T4: exists in the antiperiodic sector)

## 8. Three claims

```
MATHEMATICAL THEOREM ≠ MODEL PROPERTY ≠ PHYSICAL INTERPRETATION.
```

- **Theorem** (Tier T1): proved in Lean, no sorry. Example: the ln Z
  cancellation in spectral form.
- **Model property** (Tiers T2/T3/T4): defined, checked, or numerically
  realized *inside the stipulated model*. Example: the locking fixed
  point with ℓ_*Δ_* = 1.000000. Rigorous relative to the model; the
  model itself is stipulated.
- **Physical interpretation** (Tier T5): what the mathematics would mean
  *if* the model described nature. Example: "modular frequency calibrates
  to physical time." Open until a calibration exists.

The Heat–Gravity–Time program is rigorous exactly to the extent that these
three are never conflated.
