# LOC-3 — The Polymer Partition Function Stands; the Bridge Stops Exactly Where the Core Begins

*Landing dossier, 2026-10-27. Module:
`lean/ThetLogos/PolymerPartition.lean` (strict 17,
defs 2; zero placeholders, zero `native_decide`;
main-tree build green, 3,526 jobs, parent-verified;
headline axiom sets exactly `[propext, Classical.choice, Quot.sound]`). **Parts of the Clay
Yang–Mills statement closed by this landing: 0.**
The polymer partition function now exists as an
object; its log-density expansion converges
absolutely and uniformly in the volume inside the
LOC-2 radius; and the bridge to the layer kernel 𝒜
stops at exactly the pre-registered seam — the same
wall the finite core itself stands behind.*

## What is proved (Parts 1 and 3, FULL)

- **The object.** `colZ β u u' P` — the single-column
  polymer sum (vacuum term 1), with its column bridge
  `colZ_eq_integral_exp`: the series sums under the
  integral to ∫ exp(−β·dens_P), dominated by LOC-1's
  landed majorant; and `zPolymer := ∏ P, colZ P`, the
  product over columns.
- **The internal bridge.** `zpolymer_eq_sum_supports`:
  zPolymer equals the sum over column-supports of the
  support activities (via LOC-2's degree-assignment
  equivalence); `log zPolymer = colCount N · log (colZ P)`.
- **The KS implication.** `ks_implication`: inside
  |β| < β₀, the per-volume density
  (log zPolymer)/colCount N equals the
  volume-independent log (colZ P), whose
  activity-sum series converges absolutely with total
  majorant (exp(2|β|) − 1)/(1 − (exp(2|β|) − 1)) —
  depending only on |β|: **uniform in N, volume, and
  boundary links**. Finite-volume sums only;
  no infinite-volume or continuum language anywhere
  (KL3-2 respected).

## The seam (Part 2, PARTIAL — KL3-1 fired, as pre-registered)

The bridge to the layer kernel 𝒜 is **not** proved,
and the obstruction is named exactly, on the
module's face: 𝒜 = ∫ exp(−layerAction) dα is an
integral over the **shared** stratum variable α, and
the columns are correlated through α — so 𝒜 does not
factor over columns in the owned vocabulary; only
integrated single-column moments factor (LOC-1's
level). **Missing definition, named:** a
column-factorization of the stratum integral — a
product form of 𝒜 over columns, or an independence
hypothesis on the stratum measure with respect to
the column filtration.

This is not an accident of the LOC line. The
correlation through the shared stratum is the same
structure that makes the remaining finite core —
𝒜 ⪰ 0 on gauge-invariant observables — the core.
The uniformity program's last brick and the core
meet at one wall, and the wall now has a name on
both sides of it.

## The fence

Uniformity is landed for the polymer free-energy
density built from single-column activities. It is
not landed for log 𝒜, and no sentence in this corpus
may borrow the polymer radius for the kernel until
the factorization exists. NO CLAIM; dials 0/4.

## Census effect

Strict 6,675 → **6,692**; attribute-inclusive 6,753 →
**6,770**; modules 229 → **230**; placeholders unchanged
at **7**.

## Backers since last landing

No new backers inscribed in this interval; the roll stands
as recorded in `BACKERS.md`. Every gift is published with
the proof stream, named as the giver wishes, amounts only
with the giver's permission — the standing reciprocity of
this house.
