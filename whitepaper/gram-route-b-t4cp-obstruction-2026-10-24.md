# Gram clause, Route B, step T4c′ — OBSTRUCTION (the strict pair vs the mirror pair)

**Date:** 2026-10-24. **Verdict: T4c′ does NOT land.** No module was
built, no proved file was touched, no statement was weakened. The
stop is the brief's own kill clause, triggered in the design phase.
Full memo: builder's verdict memo (scratch archive,
`routeb-general-scratch/verdict-memo-t4cp.md`); the parent checked
the concrete instance's arithmetic independently. Census
unchanged: **4,339 strict / 4,388 attribute-inclusive / 143
modules.** Landing label unchanged: Stage 1b-B positivity T1 for
U(1); general (G, ρ) **OPEN**.

## What the discharge forces

The integrated criterion needs one family (A, B, Ξ) whose marginals
hold for arbitrary observables `f`. On token summands (pure tensors
Y(y)·U(u)), `hgram` forces the factored shape, and the marginals
then pin the shared feature pointwise:

  `dA • Ξ = γ_A • Φ^A`,   `dB • Ξ = γ_B • Φ^B`,

where Φ^A, Φ^B are the strict factors each half is forced to carry.
The closer stands or falls on the two strict readings being
proportional. They are not.

## Face one: the strict pair vs the mirror pair

At one lower crossing plaquette, the monomial
`(ρA)_{a i} (ρB)_{i j} (ρC⁻¹)_{j k} (ρD⁻¹)_{k a}` gives:

- **Closed half:** Φ^A carries `(ρ(z linkD)⁻¹)_{k a}` — the pair
  **(k, a)**, T4a′'s `phiD`, named "the strict pair" in
  `occArc_apply`'s endpoint convention.
- **Mirror half:** reading through `mirrorStrictMap`
  (`mirrorP_eq_mirrorStrictMap`; at the spatial link `linkD` the
  mirror read is plain, no inversion), Φ^B is forced to carry
  `conj((ρ(z linkD))_{i j}) = (ρ(z linkD)⁻¹)_{j i}` — the **mirror
  pair (j, i)** of the same matrix.

One shared φ₀ carries one entry of `ρ(z linkD)⁻¹`, not both
transposed entries; carrying both plants a spurious pointwise
factor in `hgram`.

**Concrete instance.** (G, ρ) = (SU(2), defining), one lower
plaquette, two direct copies with tuples (0,0,0,1) and (1,1,1,0):
γ_A = (−1/2)·(1/2) = −1/4 (from ∫ρ^⊗2 = (1/2) ε⊗ε), γ_B = 1
(empty mirror datum), Φ^A ∝ (ρD⁻¹)₁₀(ρD⁻¹)₀₁,
Φ^B ∝ (ρD⁻¹)₀₀(ρD⁻¹)₁₁. At ρ(z linkD)⁻¹ = diag(i, −i) ∈ SU(2):
γ_A·Φ^A = 0 (off-diagonals vanish) but γ_B·Φ^B ≠ 0 (diagonal
product i·(−i) = 1). No (Ξ, dA, dB) exists at that index.

## Face two: tied tensor data

The alternative assembly — B side by T4b′'s dual transport —
determines each upper plaquette's tokens from its lower mirror's.
But `exp(−S₀)` is a product of **independent** per-plaquette
series; the tied family sums only the diagonal configurations and
omits pointwise-nonzero off-diagonal terms (power 1 upstairs,
power 0 at its mirror). `hgram` fails for the tied family.
Independent data break the marginals (face one); tied data break
the identity (face two). The two faces are independent.

## Why d = 1 escapes — the same miracle, one level down

At d = 1 the pairs (k, a) and (j, i) coincide and Φ^A = Φ^B
literally — Route C closes. T4c located the word-entry failure in
the **stratum** factor; occurrence coefficients repaired exactly
that. T4c′ locates the surviving failure in the **strict** factor:
its two readings differ by the index-pair swap (k, a) ↔ (j, i),
invisible iff d = 1. The sandwich has two ends; the repair held
one, and the other gives.

## What stands; scope of the kill

- `osForm_nonneg_of_gram_integrated` stands — a true conditional.
  This memo shows the factored occurrence family is not one of its
  models at d ≥ 2; it does not show the criterion has no model (a
  regrouped, non-token decomposition is a different, unpriced
  charter), and it does not touch OS positivity itself, which is
  classical by other routes (transfer matrix / Markov property —
  likewise a different charter).
- T4a′ and T4b′ stand entire: their marginals are true integral
  identities at a shared abstract φ₀. What fails is instantiating
  that φ₀ with the kernel's strict content on both halves at once.
- `hsum`/domination was verified feasible in the design pass —
  not the blocker.

**Route B's factored-family road ends here, with the obstruction
located to a single index-pair swap.** General (G, ρ) stays OPEN
on the record. **NO CLAIM** — parts of any official Clay statement
closed: 0.
