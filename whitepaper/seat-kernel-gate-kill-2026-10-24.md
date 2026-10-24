# The Seat-Kernel Gate — Option 1 KILLED by Computation; the Gate Closes 2 and 5 with It; One Statement-Level Question Remains

**Date:** 2026-10-24 · **Charter:** `whitepaper/stage1bb-new-direction-scoping-2026-10-24.md` (Option 1, direct kernel assembly, priced M, seat computation as its pre-registered gate; kill: a negative eigenvalue of the mirror-transported seam kernel at (S₃, standard irrep, N = 2, β = 1)). Commissioned by Jeff 2026-10-24 with the gate as the condition.
**Verdict: KILL.** Computation-grade (T4 numerical with exact group arithmetic), the same evidentiary standard as the F2 damping finite check: the model is extracted from the corpus's own definitions and cross-validated entry-by-entry against them (< 1e-12 on hundreds of random entries per section); group data exact (densities ∈ {0, 1, 3/2} in permutation arithmetic); transport identities verified exactly (S₀ ∘ reflConfig = S₀; mirrorP(θy′) = restrictPos(y′)); controls below. Scripts and full report: `~/workspace/routeb-general-scratch/seat-kernel-s3.py`, `seat-kernel-s3-part2.py`, `seat-kernel-s3-report.md`.

**NO CLAIM.** Parts of any official Clay statement closed: **0**. Stage 1b-B label unchanged: positivity T1 for U(1) at all β ≥ 0; general (G, ρ) **OPEN**. In particular this computation does **not** disprove OS positivity as the corpus states it — see §3 for exactly what died and what did not.

## 1. The numbers

The full closed-half space at the seat is 6³² ≈ 7.96×10²⁴ configurations (stated, not shrunk); the computation diagonalizes nested principal sections — a principal section of a PSD kernel is PSD, so negativity in any section kills the whole. At β = 1, for the symmetrized kernel (the quadratic form's object):

| section | configs | min eigenvalue |
|---|---|---|
| A (time-inclusive) | 216 | **−3.7408** |
| B (time-inclusive) | 1,296 | **−5.6002** |
| E (time-inclusive) | 1,296 | **−2.3772** |
| C (time-inclusive) | 7,776 | **−8.3837** |

Monotone under nesting, as interlacing requires. The kernel is also **not symmetric** (asymmetry 1.000, the maximum at these entries): reflection inverts the first argument's time links while θ ignores them, and no twist repairs it. The memo's weight folding is a positive-diagonal congruence (verified) and does not rescue indefiniteness. The witness eigenvector is, to four decimals, a function of the window **time links alone** (marginals ≈ 0.50 on the identity, ≈ 0.10 on each other value; every spatial marginal uniform 1/6): **the indefiniteness lives entirely in the plane-link sector.**

## 2. Controls

- **β = 0:** 𝒦̃ ≡ 1 exactly (min eigenvalue −5.8×10⁻¹² ≈ 0, rank one as DB1's `bdry_zero` requires). The model reproduces the landed zero-coupling truth.
- **β = −1:** strongly negative in both kernel objects (−1.81×10⁹; −4.85×10⁶) — the pipeline detects negativity when present, and the β < 0 behavior matches the corpus's standing fence (R2 dossier: the seam kernel is not positive-definite for β < 0).
- The β = +1 spatial positivity in §3 is therefore not an artifact of a pipeline that only finds negatives.

## 3. Adjudication — what died, what did not

- **Option 1 (direct kernel assembly, as chartered): KILLED.** Its charter identified positivity with PSD of this closed-half kernel. The identification fails at the first seat, by a wide margin, with the witness localized.
- **Options 2 and 5: closed by the same gate**, per the scoping memo's pre-registered gating (the three options were staked on this one computation; Option 3 was already dead standalone and survives only as an amplifier to a live option, of which there are now none in this memo).
- **What did NOT die:** OS positivity as the corpus states it. The corpus's `osForm` does not pair closed-half deltas through this kernel — its plane links are Haar-averaged by the Gibbs measure, so its effective kernel is a **third object** (the plane-averaged kernel), computed nowhere yet. The time-frozen spatial kernel 𝒦̃₀ (time links frozen at identity in both arguments; exactly symmetric) is **PSD-clean on every section computed** (min eigenvalues +0.4810 / +0.2314 / +0.1605 on 36 / 1,296 / 7,776 configs — evidence only, T4, with a downward interlacing trend and no theorem behind it). Whether the averaged kernel deserves its own seat is a **statement-level scoping question** — precisely the residue the scoping memo predicted a negative gate would leave. It is a new entry if it ever opens (relabeling rule); it is not a continuation of Option 1.
- **Item 1 state:** Stage 1b-B general (G, ρ) remains **EXHAUSTED-FOR-NOW / OPEN**, now with **five** closures around it (factored Route B, regrouped, TM R2, third family, Option 1 by computation). The bench's aim stays on Item 2.
