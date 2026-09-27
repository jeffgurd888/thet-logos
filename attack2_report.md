# Attack 2 Report: Order-One + D_F Moduli (Q3)

**Date:** 2026-09-26
**Tier:** T4 (numerical exploration — not a theorem, not a Lean proof)
**Local only:** no commits, no pushes, no Lean changes.
**Module:** `python/thet_logos/dirac_scan.py`
**Status:** COMPLETE (primary scan + calibration; secondary mirrored probe below)

---

## 1. Question (Q3)

> Determine whether the current Thet axioms mathematically constrain the
> admissible finite real *-algebra strongly enough to isolate the
> Standard Model algebra.

**Attack 2** probes this via the order-one condition
`[[D_F, π(a)], π°(b)] = 0` and the dimension of the surviving Dirac
moduli space: if the axioms + order-one isolated `A_F = C ⊕ H ⊕ M_3(C)`,
we would expect `A_F` to be distinguished — e.g. uniquely minimal
nullity or a qualitatively different moduli space — from the 6,494
candidate algebras (real dimension ≤ 32) catalogued in Attack 1.

---

## 2. Calibration (on the actual SM representation) — PASS

The calibration uses the repo's canonical SM embedding
(`common.pi` / `common.piOp`, mirroring `FiniteSpectralTriple.lean`
"Option-A"), with the 24 real generators of `A_F`.

| Check | Result |
|---|---|
| 272-dim D-basis: self-adjointness violations | 0.0 |
| 272-dim D-basis: grading-oddness violations | 0.0 |
| 272-dim D-basis: J-compatibility violations | 0.0 |
| J-convention (`J D J⁻¹ = D`) on `DF_oneGen` | residual 0.0 |
| `DF_oneGen` 576-pair order-one residual | 0.0 (admissible ✓) |
| **Admissible-D_F nullity** | **260** |
| SVD relative tolerance | 1e-8 |
| Calibration runtime | 134 s (576 pairs, 1 worker) |

**Why 260, not 128.** An early estimate expected nullity 128 (A-block
free, C = E = 0 forced). That estimate assumed `pi` is a
\*-representation, so generator-pair constraints extend to the algebra
identity and force `C = E = 0`. This assumption is **false** for the
repo's Option-A embedding: it carries bilinear cross terms `q·color`
and `u1·color` (Lean `FiniteSpectralTriple.lean` lines 49, 60), so `pi`
is not additive and all 18 `M_3(C)` generators map to **zero**.
Consequently only the H-generators constrain `C` (its 2×2 lepton
corner: 6 real params) and only the C-generators constrain `E` (its 2×2
corner: 6 real params). The A-block (128 real params) is exactly free;
`(C,E)` retain `144 − 12 = 132` params. Total: `128 + 132 = 260`. The
pipeline's SVD confirms nullity exactly 260, and the corner analysis
below reproduces it. **260 is the correct calibration value for this
established embedding.**

---

## 3. Primary scan: 6,494 algebras, canonical asymmetric probe

Each candidate algebra is probed with Attack 1's canonical asymmetric
representation (first-block irrep at indices 0..d−1, zero-padded).
For this probe the order-one system provably reduces (validated
against brute-force 32×32 commutators on 4 diverse cases — exact
agreement) to real-linear equations on the `d×d` corner of the
symmetric `C` block:

- per generator pair `(a,b)`: `X_d^a C_dd (X_d^b)ᵀ = 0` and
  `(X_d^b)ᵀ C_dd† X_d^a = 0`;
- the Yukawa `A`-block (128 params) is **exactly unconstrained**;
- the `E`-block (72 params) is **fully unconstrained**;
- `C` outside the `d×d` corner is unconstrained.

Hence `nullity = 272 − rank_C` with `rank_C ≤ d(d+1)`.

### Results

| Nullity | # algebras | First-block dim `d` | Interpretation |
|---|---|---|---|
| 270 | 6,277 | 1 | `C`-corner (2 params) forced |
| 266 | 203 | 2 | `C`-corner (6 params) forced |
| 260 | 6 | 3 | `C`-corner (12 params) forced |
| 252 | 7 | 4 | `C`-corner (20 params) forced |
| 242 | 1 (`M_5(R)`) | 5 | `C`-corner (30 params) forced |

- **Pattern `nullity = 272 − d(d+1)` holds with ZERO violations** across
  all 6,494 algebras.
- **C-corner fully forced** (`rank_C = d(d+1)`, i.e. `C_dd = 0`) for
  **all 6,494** algebras.
- **Every algebra admits a nonzero `D_F`** (min nullity 242).
- `A_F` ("C + H + M3(C)") via the uniform asymmetric probe: **nullity
  270** — identical to 6,276 other algebras. It is **not distinguished**.
- Worst singular-value gap at the nullity cut: `inf` (clean split;
  zero singular values are exactly ~0).
- Scan runtime: **1 s wall** (2 workers; validated fast corner method).

### Verdict for Q3 (Attack 2)

**NO-GO on isolation via this probe.** Under the canonical asymmetric
representation probe, the order-one condition does not isolate the
Standard Model algebra: all 6,494 candidate algebras retain large
Dirac moduli spaces (nullity 242–270), the nullity depends **only** on
the first-block irrep dimension `d` (not on any SM-specific
structure), and `A_F` is nullity-degenerate with 6,276 other algebras.
Combined with Attack 1 (order-zero: 6,494/6,494 survive), the current
axioms + order-one, as numerically probed here, do **not** single out
`A_F`.

This does **not** prove `A_F` cannot be isolated — it proves that
*these* representation probes (canonical asymmetric; one mirrored
pattern — see §4) lack the selective power. Stronger representation
requirements (exhaustive enumeration, balanced scans, inter-block
structure) or additional axioms would be needed.

---

## 4. Secondary: canonical mirrored balanced probe (rdim ≤ 24) — COMPLETE

A second, clearly labeled probe: first-block irrep at indices 0..d−1
**and** 16..16+d−1 (mirrored into the antiparticle sector), for the
1,791 algebras with real dimension ≤ 24. Uses the full 272-parameter
brute-force nullity (`general_nullity`). This is ONE mirrored pattern,
not exhaustive representation enumeration — do not overgeneralize.

| Check | Result |
|---|---|
| Algebras probed | 1,791 |
| Order-zero pass | **1,709 / 1,791** |
| Order-zero fail | 82 (all with noncommutative d≥2 first blocks: H, M2(R), M2(C), …) |
| Nullity among passers | **uniformly 242** (all 1,709) |
| `A_F` ("C + H + M3(C)") | order-zero PASS, nullity **242** |
| Runtime | 420 s wall (2 workers) |

**Interpretation.** The mirrored pattern is more selective than the
asymmetric probe at order-zero (82 algebras ruled out vs 0), and more
constraining at order-one (nullity 242 vs 270 for d=1 first blocks).
The uniformity (242 for all passers) reflects that only the first
(d=1) block is mirrored; the constraint rank (30) is set by that block
alone. **Crucially, `A_F` is nullity-degenerate with the other 1,708
passers** — the mirrored pattern also fails to isolate it.

**Verdict for Q3 (Attack 2, both probes):** NO-GO on isolation. Neither
the canonical asymmetric probe (6,494 algebras) nor the canonical
mirrored probe (1,791 algebras, rdim ≤ 24) distinguishes the Standard
Model algebra by order-one Dirac moduli nullity.

---

## 5. Runtime summary

| Step | Wall time |
|---|---|
| Self-tests (Dup/commutation + 8-block reduction) | < 1 s |
| Calibration (576-pair SM census) | 134 s |
| Corner-method validation (4 brute-force checks) | 10 s |
| Primary scan (6,494 algebras, 2 workers) | 1 s |
| Secondary mirrored probe (1,791 algebras, 2 workers) | 420 s |
| **Total** | **~10 min** |

Deterministic seed 2026; `OMP_NUM_THREADS=1`; SVD relative tol 1e-8.

---

## 6. Limitations (honesty)

1. **Representation dependence.** Both probes use canonical
   representations (asymmetric zero-padded; one mirrored pattern).
   This is not exhaustive representation enumeration. A different
   representation of the same algebra could give different nullities.
2. **`pi` is not a \*-representation.** The repo's Option-A SM
   embedding has bilinear `q·color` / `u1·color` cross terms; the 18
   `M_3(C)` generators map to zero. Generator-pair order-one
   constraints therefore do not extend to algebra elements as they
   would for a true representation. This is an established repo
   convention (Lean + Python agree), not something Attack 2 changes.
3. **Fixed `J_F`, `Γ_F`.** The real structure and grading are the
   repo's canonical ones; no variation over real structures.
4. **T4 exploratory.** Numerical SVD nullity at stated tolerance, not
   a Lean theorem. No Lean certification of the scan.
5. **SVD tolerance.** Nullity is defined by relative singular-value
   cutoff 1e-8. The gap diagnostic (`inf` worst case) indicates a
   clean split, but tolerance-dependence is inherent.
6. **Candidate algebras only.** Real dimension ≤ 32, canonical block
   ordering, one irrep orientation per simple factor (inherited from
   Attack 1).

---

## 7. Files

- `python/thet_logos/dirac_scan.py` — module (self-tests, calibration,
  corner method, brute-force nullity, scans). **Local only.**
- `attack2_scan_results.json` — per-algebra results (name, rdim, d,
  rank_C, nullity, gap). **Local only.**
- `attack2_secondary_results.json` — secondary probe results.
  **Local only.**
- `attack2_report.md` — this file. **Local only.**

Nothing committed, nothing pushed, no Lean changes.
