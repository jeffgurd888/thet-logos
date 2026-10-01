# Modular-Thermal Dynamics: Finite Core and Interpretive Layer (Corrected)

**Date:** 2026-10-01
**Status:** Corrected technical document. Incorporates the 2026-10-01 gauntlet:
φ/Φ doctrine fix, [D_F²,D_F] = 0 for the correct reason, Connes metric
re-attributed to D_M, Weyl gap bound with no-crossing proviso, tier splits.
**Notation doctrine:** φ = working-math modular flux i[K, D_F] (lowercase);
Φ = ontological glyph only, never used for the flux operator.

---

## 1. Structural separation: analytic core vs. interpretive layer

### 1A. Connes metric attribution (corrective)

The Connes spectral distance formula

d(p,q) = sup { |f(p) − f(q)| : f ∈ C^∞(M_4), ‖[D_M, f]‖ ≤ 1 }

operates strictly on the continuum factor M_4 via the manifold Dirac operator
D_M. The finite Dirac operator D_F on H_F = ℂ³² has no spatial points p, q;
its spectral entries fix internal mass scales, Yukawa couplings, and
gauge-sector representations — not spatial separations. Any use of d(p,q) in
this program refers to D_M, which is unformalized in the Lean repository.

---

## 2. Modular flux φ: equilibrium triviality and driven active mode

### 2A. Triviality of the canonical Gibbs generator (Tier-1 identity)

For any linear operator, [D_F², D_F] = 0 — a structural identity of polynomial
operator algebras. Self-adjointness of D_F is irrelevant to this vanishing.

With the canonical Gibbs generator K_0 = βD_F² + (ln Z)·I_32, the modular flux

φ_0 = i[K_0, D_F] = iβ[D_F², D_F] ≡ 0

vanishes **identically, in every state**. It is not a property of equilibrium;
it is an operator identity. (Machine-checked kin: `modularFlux_selfAdjoint`
and `eigenvalue_rigidity` in `ModularTime.lean`.)

### 2B. Active driven mode (operator identity Tier-1; physics reading Tier-5)

Non-zero flux requires a generator that does not commute with D_F. Take a
Hermitian perturbation H = H* with [H, D_F] ≠ 0, D_H = D_F + H, and

K_active = βD_H² + (ln Z)·I_32 = β(D_F² + {D_F, H} + H²) + (ln Z)·I_32.

Then

φ = i[K_active, D_F] = iβ[{D_F, H} + H², D_F],

which is **generically** non-zero when [H, D_F] ≠ 0 (specific H may still
commute; "generically" is load-bearing). The equilibrium/active distinction
is drawn at the state level (KMS state ρ_0 = Z⁻¹e^{−βD_F²} vs. driven
ρ_active ≠ ρ_0) and at the generator level (K_0 vs. K_active) — never via a
state-dependent φ_0, which does not exist.

| | Canonical KMS equilibrium | Active driven mode |
|---|---|---|
| State | ρ_0 = Z⁻¹ e^{−βD_F²} | ρ_active ≠ ρ_0 (driven) |
| Generator | K_0 = βD_F² + ln Z | K_active = β(D_F+H)² + ln Z, H = H*, [H,D_F] ≠ 0 |
| Flux | φ_0 ≡ 0 (identity) | φ = iβ[{D_F,H} + H², D_F], generically ≠ 0 |
| Flow on D_F | σ_s(D_F) = D_F | non-trivial spectral rotation |

### 2C. Weyl perturbation bound on spectral gap shifts (corrected)

Let Δ(D_F) = min spec(|D_F|) \ {0} be the baseline spectral gap. For Hermitian
D_F, H = H*, Weyl's inequality gives eigenvalue-wise

|λ_k(D_F + H) − λ_k(D_F)| ≤ ‖H‖_op  for each ordered eigenvalue.

**The gap bound requires a no-crossing proviso.** Unconditional
Δ(D_F+H) ≥ Δ(D_F) − ‖H‖_op is FALSE: a zero mode drifting to small nonzero
values becomes the new gap (counterexample: D_F = diag(0,10),
H = diag(0.1,0) gives Δ(D_H) = 0.1 < 9.9 = Δ(D_F) − ‖H‖_op).
The correct statement:

if ‖H‖_op < Δ(D_F)/2, then Δ(D_F + H) ≥ Δ(D_F) − ‖H‖_op > 0.

Without the proviso, only the eigenvalue-wise bound may be claimed.

---

## 3. Explicit substitutions and thermal equations

### 3A. Modular flow substitution

σ_s(a) = e^{isK_0} a e^{−isK_0} = e^{isβD_F²} a e^{−isβD_F²};

the scalar central term (ln Z)·I_32 cancels identically (it commutes with
everything). Flow frequencies are the D_F² eigenvalue gaps
ω_ij = λ_i − λ_j, β-scaled.

### 3B. Tolman thermal-time scaling (Tier-5)

Under the thermal-time hypothesis, dimensionless modular parameter s relates
to local observer proper time τ via the local Tolman temperature
T(x) = T_0/√(−g_00(x)):

dτ = [ℏ / (k_B T(x))] ds = [ℏ√(−g_00(x)) / (k_B T_0)] ds.

This is the Connes–Rovelli reading; it is interpretive, not derived.

### 3C. Thermal product Matsubara spectrum (Tier-4 model)

On M_4 × S¹_β × F (thermal circle circumference β = ℏ/(k_B T)):

D_thermal,n² = D_M² + ω_n² + (D_F^{(A)})²,

ω_n = (2n+1)π/β (fermionic), ω_n = 2nπ/β (bosonic), n ∈ ℤ.

Standard finite-temperature decomposition; D_M unformalized in-repo.

---

## 4. Phase-space emergence (Tier-5 program vision)

Extracting continuous coordinates x^μ and momenta p_μ from the operator
spectrum D_thermal,n² is a research target, not a result. D_M and any
continuum phase-space projection are unformalized; deriving a 4D manifold
from finite matrix data remains an unproven conjecture. The finite triple
yields internal hierarchies and gauge connections on ℂ³² — nothing more,
until the continuum bridge (SA-3) is built.

---

## 5. Epistemic ledger (revised)

| Object / claim | Formula | Tier |
|---|---|---|
| Finite Gibbs state | ρ_0 = Z⁻¹ e^{−βD_F²} on ℂ³² | **Tier-1** exact analytic core |
| Modular generator & flow | K_0 = βD_F² + ln Z; σ_s(a) = e^{isβD_F²}ae^{−isβD_F²} | **Tier-1** exact matrix automorphism |
| Equilibrium flux vanishing | φ_0 = i[K_0,D_F] ≡ 0 | **Tier-1** identity ([D_F²,D_F] = 0) |
| Active flux commutator | φ = iβ[{D_F,H} + H², D_F], H = H*, generically ≠ 0 | **Tier-1** matrix identity |
| "Non-equilibrium driving" reading of the active mode | physical interpretation of K_active, ρ_active | **Tier-5** interpretive |
| Weyl gap bound | Δ(D_F+H) ≥ Δ(D_F) − ‖H‖_op **iff** ‖H‖_op < Δ(D_F)/2, H = H* | **Tier-1** with stated proviso |
| Thermal Matsubara product | D_thermal,n² = D_M² + ω_n² + (D_F^{(A)})² | **Tier-4** field-theoretic model |
| Thermal-time reading | dτ = ℏ√(−g_00)/(k_B T_0) ds | **Tier-5** (Connes–Rovelli hypothesis) |
| Emergent spacetime projection | x^μ, p_μ from D_thermal,n² | **Tier-5** program vision |
| Polyhedral emblem | icosidodecahedron (F=32, V=30, E=60) | **Tier-5** mnemonic only |

---

## Corrections applied (audit trail)

1. Φ → φ throughout (notation doctrine: case encodes tier).
2. φ_0 = 0 justified by [D_F²,D_F] = 0 identically — not by self-adjointness;
   passive/active redrawn at state and generator level.
3. Connes distance re-attributed to (C^∞(M_4), D_M); D_F has no points.
4. Weyl gap bound: unconditional form refuted by explicit 2×2
   counterexample; replaced with proviso ‖H‖_op < Δ(D_F)/2 and H = H*.
5. "φ ≠ 0" → "generically ≠ 0"; "non-equilibrium" split out of the Tier-1
   label into its own Tier-5 row.
6. All blank formula slots filled (flow substitution, Tolman, Matsubara).
