# Attack 1 run report — Q3 algebra-uniqueness candidate scan

**Tier: T4** — exploratory numerical computation. Not a theorem, not a Lean proof.

**Module:** `python/thet_logos/algebra_scan.py`
**Date:** 2026-09-26
**Seed:** 2026 (deterministic; balanced probe uses deterministic enumeration order, no RNG)
**Runtime:** ~43 min wall (2 workers, 2-CPU machine), exit 0
**Raw output:** `/tmp/attack1_report.txt` (ephemeral); this file is the persistent record.

## What was done

Enumerated all finite real *-algebras A = (+) M_{n_i}(K_i), K in {R, C, H},
with total real dimension <= 32 (**6,494** isomorphism classes,
Artin–Wedderburn over R), and for each tested *-representations pi on C^32
(direct sums of irreps under a multiplicity scheme, zero-padded to dim 32)
against the order-zero condition [pi(a), pi^circ(b)] = 0, with
pi^circ(b) = J_F pi(b)^T J_F^{-1} and J_F FIXED to the SM triple's real
structure (`python/thet_logos/common.py`: UJ, piOp).

Order-zero was tested on small real-algebra GENERATING sets per block
(generator-pair checks imply the full condition by the subalgebra argument
in `block_generators`' docstring; all generator sets verified to span their
blocks by exact-dimension closure test).

Two probes per algebra:
- (a) **asymmetric probe** (exact, all 6,494): one canonical rep supported
  in a single J_F 16-sector (the SM Option-A pattern).
- (b) **balanced probe** (stratified deterministic slices): multiplicity
  patterns with rep mass in BOTH J_F sectors. rdim == 24 (A_F's dimension):
  budget 600 patterns; rdim < 24: budget 120; rdim > 24: asymmetric only.
  For commutative (R/C-block) algebras every balanced pattern passes by the
  proved diagonal-matrix argument (no sampling needed).

Theta filter: J theta J^-1 = theta^dagger, Gamma theta Gamma = -theta are
triple-level (theta is a T1 primitive, independent of A). The real solution
space on C^32 was computed EXACTLY (integer dimension 544, via orbit
counting under the involution sigma(a,b) = (p(b), p(a)) on the admissible
support); an explicit solution verifies both relations to 0.00e+00.

## Controls

- SM triple (`common.pi`, 24 generators): order-zero residual 0.00e+00 — PASS
- SM algebra with doubled (balanced) rep: residual 2.00e+00 — FAIL
  (the SM's full 16-dim rep cannot sit on both sectors; asymmetry forced)

## Results

- **Survivor list (nonzero rep satisfying order-zero): 6,494 / 6,494.**
  Every candidate algebra admits one, via the asymmetric probe. The
  assert in `report_results` enforces this; the run exited 0.
- **Theta filter changes the survivor list: NO.** Theta relations are
  triple-level (solution space real dim 544 > 0); they do not involve A.
- **Balanced reps:** 584 / 6,494 algebras have a passing balanced rep in the
  tested slices: 168 commutative (proved — diagonal-matrix argument) plus
  416 noncommutative (found in slice). An additional 120 commutative
  rdim > 24 algebras are covered by the same theorem (not probe-tested).
  Total with a known passing balanced rep: 704.
- **A_F = C + H + M3(C):** asymmetric PASS (resid 0.00e+00); balanced PASS
  in the rdim=24 slice (18 passes / 448 tested; first example mults
  (2, 8, 0), resid 0.00e+00). In the deeper exhaustive check (budget 4000,
  all 1,035 patterns): 303 pass.
- **Balanced search genuinely truncated (deterministic slice): 1,594**
  noncommutative algebras. A further 166 commutative algebras were
  slice-truncated but are fully resolved by the diagonal-matrix theorem.
  4,703 algebras (rdim > 24) got the asymmetric probe only.

## Lock-and-key finding (T4)

Balanced passes are not random: order-zero with fixed J_F forces either
sector-asymmetry (the SM pattern) or a fine "lock-and-key" alignment of the
detailed dim layout — e.g. for A_F, sector-2 noncommutative content must
land on sector-1 dims where pi_1 acts centrally (via the C-block scalars).
Pure noncommutative algebras with no commutative padding (e.g. H^6,
M2(C)^2, M2(R)^4) admit NO balanced passing pattern in the tested slices.
This is a constraint on the (algebra, representation, J_F) triple, not a
selection of the algebra: it does not single out A_F.

## Limitations (honesty)

1. J_F held FIXED to the SM triple. A candidate failing here might satisfy
   order-zero with a different real structure. This scan tests compatibility
   with the SM triple, not absolute admissibility.
2. Order-one and D_F moduli NOT tested (that's Attack 2).
3. Balanced probe is budget-capped (600/120 deterministic patterns) for
   1,594 noncommutative algebras; truncated cases are flagged, not claimed
   exhaustive. The survivor list (asymmetric probe) is exact, not sampled.
4. Zero representation excluded from survivor criterion (trivially passes).
5. One canonical block ordering per algebra; with J_F fixed, permuting
   non-identical blocks can change balanced results (unitary inequivalence
   relative to J_F). The asymmetric result is order-independent.
6. M_n(C) blocks use one complex-irrep orientation; conjugate orientations
   not separately enumerated (audit before claiming exhaustive rep
   enumeration).
7. Tolerance 1e-8 on max-abs commutator entries (float64).

## Interpretation for Q3

**Attack 1 does NOT isolate A_F.** Under the repo's SM triple conventions
(fixed J_F, zero-padded asymmetric representations allowed), the current
Thet axioms + representation existence + order-zero admit all 6,494
candidate algebras. The theta relations add no algebra-selective power
(triple-level). Selecting A_F will require Attack 2 (order-one / D_F
moduli) and/or strengthened representation requirements
(unitality, faithfulness, or a principled ban on zero-padding).
