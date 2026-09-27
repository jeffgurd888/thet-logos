# Attack 3 — Axiom Ablation (Q3)

**Date:** 2026-09-26
**Status:** Complete. Local only; no commits, no pushes, no Lean changes.
**Files:** `python/thet_logos/axiom_scan.py`, `attack3_results.json`, this report.

## Question

Which spectral-triple axiom, added on top of order-zero + order-one, isolates
\(A_F=\mathbb C\oplus\mathbb H\oplus M_3(\mathbb C)\) from the 6,494 finite
real *-algebras (real dim ≤ 32)?

## Answer (short)

**None of them — under the canonical numerical probes.** The ablation table:

| Stage | Survivors / 6,494 | A_F survives? |
|---|---|---|
| Baseline (order-zero + order-one) | 6,494 | yes |
| + Irreducibility | **6,494** | yes |
| + Orientability | **0** | **no** |
| + Poincaré duality | not scannable | **no (control fails)** |
| KO-sign controls | D-independent | pass (all, by construction) |

Irreducibility passes for every algebra (not selective). Orientability fails for
every algebra including A_F (probe-limited, not algebra-selective). Poincaré's
A_F control is identically zero for representation-convention reasons, so it
cannot be ablated at all.

**Verdict: NO-GO on isolation through these axioms with these probes.**
No axiom was shown to isolate \(A_F\). This is a probe-limitation result, not a
result about the algebras.

## What was actually tested

All scans use the **asymmetric order-one probe**: the first block of each
algebra is placed in the 0..d−1 sector (d = irrep dim of the first block),
\(D_F\) is sampled from the admissible order-one nullspace for that placement
(3 deterministic seeded samples per algebra, seed 2026), and the remaining
sectors carry a fixed decoupled \(D\).

- **Irreducibility:** full real-linear commutant of
  \(\{\pi(a),\,\pi(a)^\circ,\,D_F,\,J_F,\,\Gamma_F\}\) has real nullity exactly
  1 (only complex scalars). Computed in a reduced exact parametrization
  (D-independent commutant first, then restrict); validated against the full
  32×32 system on type (1,C): reduced nullity = full nullity = 1, and the
  reduced solve is ~680× faster (0.2 s vs 136 s).
- **Orientability (proxy):** \(\Gamma_F\) lies in the matrix *-algebra generated
  by \(\{\pi(a),\,[D_F,\pi(a)]\}\), tested via exact bicommutant
  (\(M''\) = algebra; membership by least-squares residual < 1e−8).
- **Poincaré (literal):** \(\cap_{ij}=\mathrm{Tr}(\Gamma_F\pi(p_i)
  J_F\pi(p_j)J_F^{-1})\) with the repository's literal Option-A `common.pi`
  and central projections, \(|\det\cap|>0\).
- **KO signs:** \(J_F^2=+1,\;J_FD_F=D_FJ_F,\;J_F\Gamma_F=-\Gamma_FJ_F\) on the
  reference Dirac and the full 272-dim order-one basis (all residuals 0.0).

Tolerances: nullity cutoff and residuals at \(10^{-8}\) (relative to leading
singular value). Deterministic: fixed seed, no randomness in the pipeline.

## Controls (A_F first, as required)

1. **Irreducibility:** A_F asymmetric probe, 3 samples → nullities [1,1,1].
   **PASS.** (D-independent complex commutant nullity is 452 — the
   D-samples are doing the real work.)
2. **Orientability:** A_F asymmetric probe → residual 1.78. **FAIL.**
   This is a **probe limitation, proven**: the folded probe puts \(\pi\) and
   \([D,\pi]\) in the first d-sector, and \(\Gamma_F\) is supported in the
   16..31 sector, so \(\Gamma_F\) can never lie in the generated algebra —
   for **every** algebra, not just A_F. The 0/6494 scan result confirms it.
3. **Poincaré:** A_F literal → \(\cap=0_{3\times3}\), \(|\det|=0\). **FAIL —
   convention obstruction.** With the repo's literal Option-A `common.pi`,
   \(\pi(p_i)\) and \(J_F\pi(p_j)J_F^{-1}\) have disjoint support (first
   16-sector vs second), so the trace is identically zero; duplicating the
   projection into both sectors gives cancelling \(\pm\) contributions because
   \(\Gamma_-=-\Gamma_+\). This is a representation-convention obstruction, not
   evidence about \(A_F\). Per the stopping rule, Poincaré was **not**
   manufactured into an ablation column.
4. **KO signs:** all residuals 0.0. **PASS** (D-independent).

## The full scan (6,494 algebras, 2 workers, ~41 min wall)

- **Irreducibility (all-3-samples pass required): 6,494/6,494.**
  Split distribution: every algebra passed all 3 samples ({3: 6494}).
  A_F: [1,1,1], pass.
- **Orientability (1 sample; provably universal-fail): 0/6,494.**
  A_F residual 1.64, fail.
- **Both: 0/6,494.** Errors: 0.

## Residual family / diagnostics

- After irreducibility: the full 6,494 (no selection).
- After orientability: empty (no selection possible — probe-limited).
- No algebra is distinguished from A_F by any tested axiom under these
  probes. A_F's irreducibility nullities [1,1,1] are shared by all 6,493 others.

## Why this happened (plain language)

The probes are too coarse, in opposite directions:

- **Irreducibility** with a *generic* sampled \(D_F\) is too easy: a random
  admissible Dirac breaks every symmetry, so every algebra's triple looks
  irreducible. It cannot see the difference between algebras.
- **Orientability** with the *folded* probe is impossible: the probe crams the
  algebra into one corner of the 32-dim space while \(\Gamma_F\) lives in the
  opposite corner. Nothing can pass, so it cannot select either.
- **Poincaré** needs the true faithful SM representation with its specific
  Yukawa Dirac — the folded/asymmetric probes don't carry that structure, and
  the literal Option-A embedding gives a structurally zero intersection form.

## What would be needed (not done)

- A **faithful** per-algebra representation (all blocks, not just the first)
  with a compatible order-one \(D_F\) per algebra — the current probes fold
  everything into the first block.
- For Poincaré: the actual finite-geometry intersection form on
  \(K_0(A_F)\), which requires the unimodular/classical-basis conventions,
  not the literal Option-A matrix embedding.
- For orientability: a probe where \(\pi(A)\) and \(\Gamma_F\) can interact
  (e.g. the full SM triple, where orientability is known to hold).

## Bottom line

Attack 3 is **complete and NO-GO**: under every canonical numerical probe
available, no spectral-triple axiom isolates \(A_F\) from the 6,494 candidates.
Irreducibility is universal-pass, orientability is universal-fail
(probe-limited), Poincaré is convention-blocked. Combined with Attacks 1–2,
the Q3 campaign finds no order-zero, order-one, or axiom-level selector for
\(A_F\) at T4 numerical fidelity with these probes. The selection, if it
exists, lives in finer structure (faithful representations, specific Yukawa
data, or the actual K-theoretic intersection form) that these probes do not
resolve.
