# Proof-Status Ledger: the 46 → 22 Order-One Classification

**Date:** 2026-10-01
**Scope:** the machine-checked classification `ThetLogos.cf_kernel_classification_46_22`
**Purpose:** a single ledger of what is established, what is conditional numerical work,
and what has been explicitly killed — so rejected speculation cannot walk back into
the research program. Extends (does not replace) the README five-tier honesty ledger,
the paper's honesty ledger, and the open-hypotheses catalog kill log (§3, V1–V7).

## Canonical lineage

```
dirs22  →  CFKernel22.lean / CFKernelRetarget.lean  →  OrderOne.lean
```

Any proposal referencing `E₁–E₁₂`, `Nullspace22.lean`, or `MatrixDecomp.lean`
is using the rejected sketch's vocabulary (see §4), not this lineage.

## The proved object (read this first)

The classification covers the **full 22-dimensional** real order-one subspace:
**10 SM directions + 12 exotic survivor directions.** The 12 exotics are the novel
part, but the theorem is about all 22.

> **Semantic law:** 12-dimensional algebraic kernel ≠ 12 physical fields.
> The exotic directions are explicit matrices with proved properties.
> They are **not** claimed to be particles, forces, dark matter, leptoquarks,
> or any other physical entity.

## §1 — Established (Tier 1, machine-checked)

| # | Claim | Evidence |
|---|-------|----------|
| 1.1 | `cf_kernel_classification_46_22`: every `D` with `IsW22 D` lies in the ℝ-span of `dirs22` | `lean/ThetLogos/CFKernel22.lean:1065`, proved via `finrank_span_eq_card dirs22_independent` |
| 1.2 | `finrank ℝ` of the order-one subspace = 22 | Same theorem; `finrank_W22_le_22` + spanning |
| 1.3 | 12 explicit `OrderOneHolds` proofs (one per exotic direction) | `exotic*mem` theorems, `CFKernel22.lean:272–` |
| 1.4 | Each exotic is proved self-adjoint, J-compatible, grading-odd, and commuting with `cfMat` | `CFKernelRetarget.lean`: 48 proved lemmas |
| 1.5 | 10 SM directions = 5 complex moduli × 2 real (`yNu, yE, yU, yD, yR`) | `OrderOneHolds_smDirac`, `OrderOne.lean:90` |
| 1.6 | Zero `sorry`s in the classification files | `CFKernel22.lean`, `CFKernelRetarget.lean`, `OrderOne.lean`, `CFKernelClassification.lean` (verified 2026-10-01; the only matches are the words "zero sorrys" in comments) |
| 1.7 | Axiom footprint: `propext`, `Classical.choice`, `Quot.sound` | `#print axioms`, 2026-10-01 |
| 1.8 | Lake build green | 2026-10-01: 3323 jobs, exit 0 |
| 1.9 | Scale of the checked system: `smGen : Fin 12`, 12² = 144 pairs, 144 × 1024 = 147,456 complex component equations | Source-verified 2026-10-01 (the 576-pair figure belongs only to the separate Tier-4 Python scan) |

The 12 exotic survivors (proved objects, **not** physical fields):
`exotic{Re,Im}NuLeR`, `exotic{Re,Im}ELNuR`, `exotic{Re,Im}ULDR`,
`exotic{Re,Im}DLUR`, `exotic{Re,Im}NuREbarR`, `exotic{Re,Im}EREbarR`.

## §2 — Established (Tier 2, hand-verified)

| # | Claim | Evidence |
|---|-------|----------|
| 2.1 | `dim_R ker L = 4`, where `L` is the chirality-odd Yukawa-consistency operator on a single Dirac block — a different operator from the order-one commutator stack | VORTEX-005; hand-verified, **not** a spacetime claim |

## §3 — Conditional numerical work (Tier 4, scoped, kill criteria required)

| # | Item | Status |
|---|------|--------|
| 3.1 | Python census corroboration of the classification (24-generator scan) | Supporting evidence only; never a substitute for §1 |
| 3.2 | Effective spectral potential `V_eff(D_F)` minimized over the 22-dim moduli space | **CONDITIONAL GO** as Tier-4 numerical exploration with explicit kill criteria. Must **not** be advertised as deriving physical selection rules. Not yet built. |

## §4 — Explicitly killed or declined (do not revive by fiat)

Per the relabeling rule, killed claims return only as new, weaker entries with fresh
proof or evidence — never by rewording.

| # | Item | Verdict | Date / ref |
|---|------|---------|------------|
| 4.1 | Old 46 → 10 chain (`cf_kernel_classification_46_10`, `ccm_classification`, etc.) | **UNSOUND AS STATED** — preserved unmodified, flagged in source | 2026-09-30 |
| 4.2 | H-φflow-1: finite thermal-flow probe as gauge-force differentiator | **KILLED** — the flow sees mass splitting, not forces | 2026-09-30 |
| 4.3 | Golden-ratio / Fibonacci φ-tower as the physical mass hierarchy | **KILLED** — Tier-5 symbolic toy model only; unkill request refused under the relabeling rule | 2026-09-29 / 2026-10-01 |
| 4.4 | Icosahedron numerology (12+20=32, 30-vertex W₂₂, 60-edge order-one, ℂ⁷ derivations) | **NO-GO** — invented derivations | 2026-09-30 |
| 4.5 | "Complete Formalization" sketch (`SpectralTriple.*` namespace, ~30 sorrys, E₁–E₂₂, `Nullspace22.lean`) | **DECLINED** — its four "blocking issues" do not exist in our source (verified by grep 2026-10-01); proposes replacing a zero-sorry proved theorem with ~1,500 lines of unwritten work | 2026-10-01 |
| 4.6 | Seven-item roadmap, item 1: exotic "field sectors" (leptoquark/diquark/dark-sector quantum numbers) | **NO-GO** — violates the semantic law above | 2026-10-01 |
| 4.7 | Seven-item roadmap, item 3: M₄ × S¹_β product + Seeley–DeWitt "exact gravitational-Higgs cross-couplings" | **NO-GO as stated** — new speculative geometry; VORTEX-006 blocks the gravity extraction; overlaps frozen SA-2/SA-4 | 2026-10-01 |
| 4.8 | Seven-item roadmap, item 4: RG flow of the 22 moduli from Λ_GUT | **NO-GO** — no formalized GUT exists; no beta functions defined for the moduli | 2026-10-01 |
| 4.9 | Seven-item roadmap, item 5: molecular chemistry as inner Dirac fluctuations | **NO-GO** — category error; Engine #12 (finite-lattice DFT) is the legitimate chemistry-adjacent direction | 2026-10-01 |
| 4.10 | Seven-item roadmap, item 6: R_θ(x,y) = θx − y "correspondence computing" | **NO-GO** — undefined in the framework; invented terminology | 2026-10-01 |
| 4.11 | Seven-item roadmap, item 7: "publish Nullspace22.lean / MatrixDecomp.lean" | **REDUNDANT / INVALID** — wrong filenames, wrong lineage; the kernel is already public | 2026-10-01 |

## §5 — Standing boundaries referenced by this ledger

- **Interpretive Conservation Principle** (2026-10-01): every Tier-5 term must anchor to a
  Tier-1 object or theorem; interpretation never alters an operator identity.
- **Relabeling rule:** killed/vetoed claims return only as new, weaker entries by proof.
- **No formalized GUT** exists as of 2026-10-01.
- Never call the entire physical theory fully computer-verified: the finite 46 → 22
  classification is machine-checked; continuum physics, empirical predictions, GUT
  claims, and physical identification of the exotic directions are not.
- φ (modular flux, working math) ≠ Φ (ontological glyph); golden-ratio φ ≠ flux φ.

## §6 — Maintenance

New entries go here with date and verdict before they enter any paper, proposal, or
announcement. An external proposal is recorded in §4 with its audit result even when
declined — the record of refusal is part of the ledger.

## §7 — Audited future research program (conditional, 2026-10-01)

Source: external 11-item future-program sketch. Audit verdict: **CONDITIONAL GO**
with the corrections below. Its governing distinction is adopted as ledger law:

> "If the research succeeds, what door does that open?" ≠ "therefore the theory predicts X."

A positive result at any step makes the next direction more interesting; it does not
by itself establish a physical interpretation. This matches the relabeling rule:
every step earns the next.

**Corrections applied at audit (the sketch as received is not adopted verbatim):**

- C1 — Notation. The sketch writes "ker L" / "dim ker L = 12" throughout. In this
  source, `dim_R ker L = 4` (Tier-2, VORTEX-005, §2.1). The "12" is the exotic part
  of the 22-dimensional order-one subspace `W22`. All eleven items are re-lettered
  accordingly; the research questions transfer, the notation does not.
- C2 — Item 7 (complete Lean formalization, zero sorrys) is **already true** of the
  current theorem (§1.6–§1.8). Future formalization work targets the *next* theorems
  (deformations, N-generation extensions), not this one.
- C3 — Item 2 (N generations) must credit `ThreeGen.lean`: 16 proved three-generation
  inheritance theorems already exist. N = 3 is partially covered, not open territory.
- C4 — Item 5 (spectral-action fingerprints) is tied to the frozen SA program
  (SA-1…SA-7), specifically SA-4 (finite spectral action). It does not float free.
- C5 — Item 8 (independent reproduction) notes the existing Python Tier-4 census as
  partial independent corroboration, not a blank slate.

**The eleven directions (corrected):**

| # | Direction | Door it would open |
|---|-----------|-------------------|
| 7.1 | Decompose the 12-dim exotic part into canonical invariant pieces | "12" becomes architecture, not a number; possible classification theorem |
| 7.2 | Generalize the construction to N generations (`H_F ⊗ ℂ^N`) | A family-level framework; does **not** by itself explain why N = 3 in nature |
| 7.3 | Representation-theoretic classification of the exotic part | Selection rules; connection to established representation theory |
| 7.4 | Stability of the 12-dim exotic part under symmetry-preserving perturbations | Rigidity: axioms ⇒ the structure, vs. one calculation giving 12 |
| 7.5 | Spectral-action consequences (`Tr f(D²/Λ²)` fingerprints) | First bridge from the finite result to the larger framework — via SA-4 |
| 7.6 | `V_eff` moduli exploration over the 22-dim space | Preferred configurations *within the model*; **numerical minimum ≠ physical vacuum** |
| 7.7 | Formalize the *next* theorems in Lean | Reusable foundation; already achieved for the current theorem |
| 7.8 | Full independent reproduction (definitions → matrices → constraints → kernel) | Implementation-independence; exact divergence-point diagnosis |
| 7.9 | Classify admissible deformations `D_F → D_F + δD` (all axioms preserved) | Finite-dimensional moduli space of valid spectral geometries |
| 7.10 | Finite-to-continuum correspondence | A controlled route toward physical equations — a major program, not an assumption |
| 7.11 | Experimental prediction | The final gate: abstract structure → quantitative, testable prediction |

**Ladder (adopted):** Find → Understand → Prove → Stress-test → Generalize →
Connect → Predict → Test. Each rung is conditional on the previous one; no rung
assumes the final physical interpretation.

**Boundary:** no item in §7 may be cited as an established result, a prediction of
the theory, or evidence for a physical interpretation of the exotic directions
until its own proof or measurement exists. Items graduate to §1–§3 only by meeting
those sections' evidence bars.

## §8 — Temporary lifting of the SA freeze and K2/H22 quarantines (2026-10-02)

**Authority:** Jeff, 2026-10-02 ("unfreeze and lift quarantines temporarily";
terms confirmed; E13-E Phase 4 commissioned).

**Lifted, temporarily and scoped:** the spectral-action program freeze
(incl. SA-4), the K2 continuum quarantine, and H22's quarantine — for
E13-E Phase 4 (product Seeley–DeWitt computation on M₄ × S¹_β × F₃₂) and
directly supporting continuum-bridge work only.

**Not lifted:** the semantic law (12-dim algebraic exotic component ≠ 12
physical fields); rejected vocabulary (E₁–E₁₂, `Nullspace22.lean`,
`MatrixDecomp.lean`); killed claims (relabeling rule stands); the honesty
tiers themselves. This is permission to investigate, not a promotion of any
claim.

**Re-freeze condition:** the lifting expires when Phase 4 returns its verdict
(PASS/FAIL/KILL) or on Jeff's word, whichever comes first. Surviving results
keep whatever tier they earn; the wall then goes back up.

**Status:** LOCAL amendment — not pushed. Public ledger update requires
Jeff's explicit push authorization.

### §8.1 — Re-freeze (2026-10-02)

E13-E Phase 4 returned its verdict: **PASS** (no kill condition triggered;
cross term derived, anchors green, assumptions explicit;
`whitepaper/e13e-phase4-seeley-dewitt.md`). Per §8's re-freeze condition, the
temporary lifting **expires with this verdict**: the spectral-action program
freeze and the K2/H22 quarantines are reinstated in full. Surviving Phase 4
results keep their earned tiers (Tier-2 computation; Tier-5 physical
reading). Any further SA/continuum work requires a new lifting under the
same terms.

**Status:** LOCAL amendment — not pushed. Public ledger update requires
Jeff's explicit push authorization.
