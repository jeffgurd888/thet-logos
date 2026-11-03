# GATE-0 ITEM 5 — CORE-CHAIN RUN LANDING DOSSIER — 2026-11-03

**Item:** GATE-0 item 5 (`pullBotKernel_seatFactorApproxExpansion`,
the frozen `SeatFactorApproxExpansion` target of GATE-3):
the approximating-expansion discharge attempt via the
compression route — the `𝒜 ⪰ 0` core chain, single lane
always. **Commission:** Jeff 2026-11-02 ("run them" — the
previously untaken core-chain chair option), re-fired
2026-11-03 ("build and run"). Built in the isolated
worktree lane `~/workspace/thet-logos-item5`, branch
`item5-lane`, from main-tree HEAD `f57a107` (the item-6
ceremony commit); NOT integrated — the parent runs the
ceremony.

## VERDICT: PARTIAL (at full rank)

The headline `SeatFactorApproxExpansion` as frozen is
NOT discharged. What is discharged, at full rank:

- **The compression route is built and its adapted HS
  convergence is PROVED** — at the level of a general
  `L²` kernel carrying two explicit hypotheses:
  positivity on ALL of `L²` (`PosKernel`, SHELF-3b's
  registered notion) and self-adjointness of its
  integral operator. The pre-named GATE-3 seam
  ("compressions built + finite Grams landed, HS
  convergence stalls") does NOT stall: under the
  route's hypotheses the convergence lands — the HS
  distance of a finite stage is at most the sum of the
  operator and adjoint HS tails over the stage's
  complement, and both tails vanish.
- **The seat assembly is PROVED conditionally**: under
  the corpus's kernel-measurability input
  (`Continuous fun g => repMatrix ρ g`, the same
  hypothesis item 6's regular-case instances carry)
  and the explicitly named all-of-`L²` positivity
  hypothesis `LayerKernelPosAll`, the frozen
  `SeatFactorApproxExpansion μG ρ hN β` HOLDS at every
  `Even N`, hence in particular on GATE-4C's re-pinned
  `4 ≤ N` domain (corollary
  `seatFactorApproxExpansion_of_layerKernelPosAll_of_four_le`).

Item 5 as frozen assumes only `LayerKernelPos` —
positivity of the `𝒜`-pairing on gauge-invariant layer
observables. The seam is exactly `LayerKernelPosAll`:
positivity of the layer-kernel operator on all of
`L²(layer)` — per the GATE-4C dossier's equivalence,
item 5's arbitrary-factor form is equivalent to that
all-of-`L²` PSD fact about `𝒜` itself. This run touches
the equivalence from the sufficient side
(`LayerKernelPosAll ⇒ SeatFactorApproxExpansion`,
under `hρcont`); it neither proves nor refutes anything
about `LayerKernelPos` itself. No kill fired. `hMarg`
is not needed by any step of this run and is NOT
discharged; it stays open on the G2b route. W3
(`seatSchurProductStepOpen`) is NOT closed by this
package. NO CLAIM; dials 0/4.

Module: `lean/ThetLogos/Span3SeatSchurGateItem5.lean`
— **40 strict theorems + 6 defs, zero sorrys** (no
`sorry` token anywhere in the file); targeted build
green, warning-clean for the module (the only build
warnings are pre-existing ones in dependency modules);
`#print axioms` on the 13 headlines returns exactly
`[propext, Classical.choice, Quot.sound]`, no
`sorryAx`. Per the gate-module house pattern the
module is not in the root import list; it is verified
by targeted build.

## Per-part landings

### C1 — compression matrix is PSD: LANDED

`compressionMatrix` (`A i j = ⟪b i, T (b j)⟫` on a
finite `F`), `compressionMatrix_posSemidef`: Hermitian
by self-adjointness; the quadratic form at `v` is the
`T`-pairing of the basis combination `∑ j, v j • b j`
with itself — real part `≥ 0` by `PosKernel`, imaginary
part `0` by self-adjointness. Note `PosKernel` alone
does not imply self-adjointness (it controls only the
real part of the form); the route carries `hSA` as an
explicit hypothesis at the general level.

### C2 — finite Gram factorization: LANDED

`exists_compression_gram`: `A = ∑ k, vecMulVec (v k)
(star (v k))` via the finite-dimensional
`Matrix.posSemidef_iff_eq_sum_vecMulVec`. That is the
only diagonalization consumed anywhere in the module
(K-GATE-2 respected: no infinite-dimensional spectral
theorem is cited or needed).

### C3 — Gram kernel and its operator: LANDED

`gramFactor` (the basis combinations `φ k = ∑ j, v k j
• b j`), `gramKernelOf` (`∑ k, φ k (x) * conj (φ k
(y))`), `gramTerm_memLp`, `gramKernelOf_memLp`;
operator identifications `inner_integralKernelOp_gramKernelOf`
(the Gram operator is the projection-shaped sum
`f ↦ ∑ k, ⟪φ k, f⟫ • φ k` in pairing form),
`integralKernelOp_gramKernelOf_apply_basis_mem`
(on basis vectors of the stage it acts as the
Hilbert–Schmidt projection sum of `T (b i)`) and
`integralKernelOp_gramKernelOf_apply_basis_not_mem`
(it vanishes on basis vectors outside the stage);
`integralKernelOp_sub_apply` for the difference
operator.

### C4 — the HS bound: LANDED

`eLpNorm_sub_gram_sq_le`: `(eLpNorm (K − G) 2
(μ.prod μ)).toReal ^ 2 ≤ hsTailSq T b F + hsTailSq
(adjoint T) b F`, where `G` is the stage's Gram kernel.
Proved on the `ℝ≥0∞` side by Parseval
(`hsParseval_tsum`), the exact coefficient majorant
`gramMajorant` (the difference coefficients equal the
majorant exactly — zero on the stage block by the C3
projection identity, `T`'s own coefficients
elsewhere), and `ENNReal.tsum_comm`.

### C5 — stage and sequence: LANDED (the GATE-3 seam, closed under the route's hypotheses)

`exists_approx_stage` (both tails `< ε²/2` along
`atTop`, then C4 and `lt_of_pow_lt_pow_left₀`);
`exists_seq_tendsto`: a sequence of finite Gram
kernels whose HS distance to `K` tends to `0`
(the `ε = 1/(n+1)` extraction). This is the adapted
convergence the generic tensor approximation of
`IntegralKernelHS` does not provide: the approximants
are Gram kernels of compressions of `T` itself. No
countable basis is needed; stages are finite subsets
of an arbitrary Hilbert basis.

### S1 — the layer kernel as an `L²` kernel: LANDED (under `hρcont`)

`layerKernelFun` (the layer kernel as a kernel on
pairs of layer configurations), `layerKernelFun_memLp`:
joint measurability of the Boltzmann factor by item
6's `measurable_layerAction` and the parametrized
integral (`integral_prod_right'`, item 6's idiom);
the pointwise bound is `layerKernel_norm_le`.

### S2 — self-adjointness at the seat: LANDED

`layerKernelFun_conj_swap` (the kernel is real —
`layerKernel_eq_ofReal` — and symmetric —
`layerKernel_symm`, at `Even N`);
`layerKernelFun_selfAdjoint`: the layer operator
satisfies the compression route's `hSA` hypothesis,
via `integralKernelOp_inner`, conjugation of the
integral, and the product swap.

### S3 — `LayerKernelPosAll`: NAMED, NOT PROVED (the seam)

`LayerKernelPosAll μG ρ hρcont β := PosKernel
(layerKernelFun μG ρ β) (layerKernelFun_memLp μG ρ
hρcont β)`. Positivity of the layer-kernel operator
on ALL of `L²(layer)`. Strictly stronger than
`LayerKernelPos` (gauge-invariant pairings only);
proved nowhere in the corpus. The invariant-subspace
variant of the route cannot substitute: Gram sums
built from gauge-invariant factors are invariant in
the first kernel slot separately, HS limits preserve
that invariance, and `layerKernel` is not separately
first-slot invariant in general (G2c dossier
obstruction, on record).

### S4 — the pullback transports: LANDED

`measurePreserving_tauBot`: the bottom extraction is
measure-preserving — it factors as the coordinate
split at the image finset of `embLayerBot hN`, the
first projection, and the pi-congruence along
`embEquiv` (the same factorization pattern as
`measurePreserving_restrictPos`).
`measurePreserving_swapTauBot`: the swapped double
pullback `p ↦ (tauBot hN p.2, tauBot hN p.1)` is
measure-preserving from the product seat measure to
the product layer measure.

### S5 — the stage identity: LANDED

`seatDiff_eq`, `seat_stage_fun_eq`: one stage's seat
difference kernel is the conjugate of the layer
difference kernel pulled back along the swapped
`tauBot` map. The conjugation is the slot bookkeeping
of `pullBotKernel` (it evaluates the layer kernel at
the swapped extractions) composed with the Gram
kernel's own conjugation; the layer kernel's reality
(S2) removes it on the kernel part.

### S6 — stage transport: LANDED

`seat_stage_memLp` (the layer stage's `MemLp`
transports along the measure-preserving swapped
pullback; conjugation preserves `MemLp`) and
`seat_stage_eLpNorm` (the stage's HS distance at the
seat equals its HS distance at the layer:
`eLpNorm_star` + `eLpNorm_comp_measurePreserving`).

### S7 — the conditional headline: LANDED (conditional)

`seatFactorApproxExpansion_of_layerKernelPosAll`:
`LayerKernelPosAll` + `hρcont` ⇒ the frozen
`SeatFactorApproxExpansion μG ρ hN β`, at every
`Even N`. The expansion's data are the compression
stages': index types `Fin (mseq n)`, coefficients
all `1 ≥ 0`, factors `⇑(gramFactor …)` — layer
functions pulled back along `tauBot hN`, per the
§2.2 audit point on the target's face. Corollary
`seatFactorApproxExpansion_of_layerKernelPosAll_of_four_le`:
the same on the `4 ≤ N` domain.

## Kills — status

- **K-GATE-3** (exact-finite smuggling): NOT fired,
  NOT committed. No approximating sequence is fed to
  `seatSchurTarget_of_finiteRankProductStep`; that
  theorem is not cited anywhere in this module. The
  "adapted HS-convergence lemma is false as needed"
  clause does NOT fire: the adapted convergence is
  proved (C5) — under the stronger all-of-`L²`
  hypothesis, which is exactly why the run is PARTIAL
  rather than FULL.
- **K-GATE-2** (spectral smuggling): NOT committed.
  No infinite-dimensional spectral theorem is cited;
  the finite-dimensional `Matrix.PosSemidef`
  factorization (C2) is the scoping's prescribed
  compression engine.
- **K-F2-2**: the audit point is met head-on and
  reported, not shipped as a weld brick: the
  conditional headline (S7) is exactly a Gram/PSD
  fact about `𝒜` (through `LayerKernelPosAll`),
  re-tiered here as a CORE-CHAIN result — this lane
  is the core chain's own lane. The fence inside the
  route itself: the expansion produced is a LIMIT of
  finite Grams; no single `MemLp` Gram family for
  `𝒜` is produced (a positive HS operator's square
  root need not be HS), so `posKernel_gram` does not
  apply to it and `LayerKernelPos` is NOT proved by
  this module.
- **K-F2-3** (generality creep): respected — the
  conditional headline is at general `(G, ρ)`, every
  `Even N`; no finite-seat or finite-`G` retreat.
- **K-F2-4** (buy inflation): respected — nothing in
  this module is progress on FACT, `𝒜 ⪰ 0`, clause
  (a), or uniformity beyond what the theorems
  literally state. `LayerKernelPosAll` is a
  hypothesis, not a result.

## What W3 still needs (after items 6 and 5)

W3 (`seatSchurProductStepOpen`) does NOT fire.

1. **Item 5's expansion at the frozen generality.**
   GATE-4C's hypothesis package consumes the expansion
   under its own hypotheses. This lane lands the
   expansion only under `LayerKernelPosAll` +
   `hρcont`; under `LayerKernelPos` alone item 5
   remains open, so W3's GATE-3 input is still
   missing at the frozen generality. Closing it is
   equivalent to the all-of-`L²` PSD fact about `𝒜`
   (the equivalence in the GATE-4C dossier) — a core
   result, not a weld step.
2. **GATE-4C hypothesis 6.** Item 6 reduced it to
   five named inputs (`hCross`, `hCrossFold`,
   `hInvFold`, the two dressed integrabilities) over
   banked `hMarg` — all unlanded; `hMarg` itself
   remains open on the G2b route. This lane neither
   needs nor touches `hMarg`.
3. **GATE-4C hypotheses 4/5 beyond the regular case.**
   Item 6 discharges them under `hρcont` (hypothesis
   4 additionally requires factor measurability and
   boundedness). This lane's compression factors are
   finite Hilbert-basis combinations carried as `Lp`
   classes; they do not automatically carry the
   measurability/boundedness representatives
   hypothesis 4 wants.

Frozen GATE-4 remains unproved. NO CLAIM — parts of
any official Millennium statement closed by this
module: 0. Dials: 0/4.

## CEREMONY (parent, main tree, 2026-11-03)

- Lane files copied byte-identical from worktree
  `~/workspace/thet-logos-item5` (branch `item5-lane`, commit
  `228f69b`) into the main tree at local HEAD `9c74042`
  (the census-restatement commit); identity verified by diff.
- Targeted main-tree build
  `lake build ThetLogos.Span3SeatSchurGateItem5`: **green**
  (3674 jobs), zero sorrys (no `sorry` token in the module);
  no errors or warnings originating in this module (the only
  build warnings are pre-existing linter warnings in
  dependency modules).
- Independent strict recount of the module (method of record:
  comment/string-stripped, `^(theorem|lemma)` at column 0):
  **40 strict + 6 defs**, matching the lane count exactly.
- Axiom fence: the 13 checked headlines admitted to
  `lean/scripts/axiom-fence.txt` WITH their import line
  (`import ThetLogos.Span3SeatSchurGateItem5`) in the SAME
  commit as the module (CI lesson). Official fence runner:
  **FENCE PASS 95/95** (82 → 95), every admitted headline,
  old and new, on exactly
  {propext, Classical.choice, Quot.sound}, no sorryAx.
- Corpus census (method of record; FILES-TRUE since today's
  restatement): 12,940 strict / 469 modules → **12,980 strict /
  470 modules**, zero sorrys (whole-tree recount 13,649 strict
  over 485 files, minus the frozen pre-ledger remainder
  669 / 15). README prose census updated (12,940 → 12,980
  declarations; 469 → 470 modules) and the shields badge
  updated to the same files-true figure (12,980); prose and
  badge kept equal.
- Ledger record `gate-item5-corechain` (partial, T3) added
  with the PARTIAL verdict, the CORE-CHAIN grading, the
  `LayerKernelPosAll` seam, and the W3 remainder list on its
  face; validator PASS, 16 records conform.
- Verdict stands as landed: **PARTIAL** — the compression
  route and its adapted HS convergence are proved under the
  route's hypotheses (all-of-`L²` positivity +
  self-adjointness, the latter discharged at the seat); the
  conditional headline holds under `hρcont` +
  `LayerKernelPosAll`. Item 5 as frozen is NOT discharged;
  GATE-3 is NOT discharged; `LayerKernelPos` is neither
  proved nor refuted; no kill fired; `hMarg` open on its own
  route; W3 stays open. This is core-chain work, NOT weld
  progress. NO CLAIM; dials 0/4.
