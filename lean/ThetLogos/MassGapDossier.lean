import Mathlib.Basic.Real.Basic
import Mathlib.Tactic
import ThetLogos.ClayStatement

namespace ThetLogos

/-!
# ThetLogos.MassGapDossier — the Clay mass-gap problem's precise shape

Source: the QFT rungs map (`whitepaper/qft-rungs-map-2026-10-06.md`,
Rungs 3–4), Rung 4 dossier run (2026-10-07).

**What this file IS.** A machine-checked *dossier* on the Clay Yang–Mills
mass-gap problem: the known partial results pinned with their exact scope,
and the four transfer obstructions — the load-bearing walls between our T1
finite-matrix results and the prize — stated as precise Props. Every pinned
statement carries its scope and its source citation.

**What this file is NOT.** A proof of the mass gap, an "approach" to it, or
any suggestion that the proof is near. The dossier documents the problem;
it does not solve it. Per the map: no interacting 4D QFT satisfying the
Wightman axioms has ever been constructed, by anyone.

Honesty tiers in this file:
- **T1 (proved):** `obstruction2_is_T1` — references the checked
  `gap_closes` in `ThetLogos.ClayStatement` (branch crossings close
  finite-matrix gaps).
- **T5 (theorem-shaped, content opaque or open):** everything else — the
  partial results are *statements with exact scope*, the bridge implications
  are *open problems*, never claimed proved.
-/

/-! ## Pinned partial results (exact scope) -/

/-- Lattice Yang–Mills at strong coupling HAS a mass gap.
    Source: Osterwalder–Seiler, "Gauge field theories on a lattice,"
    *Ann. Phys.* 110 (1978) 440–471; Seiler, *Gauge Theories as a Problem
    of Constructive Quantum Field Theory*, Lect. Notes Phys. 159 (1982).
    At small β (strong coupling): exponential clustering (the lattice mass
    gap) and Wilson-loop area law. -/
structure LatticeStrongCouplingGap where
  /-- Exponential clustering of correlations at strong coupling — the
      lattice mass gap. -/
  latticeGap : Prop
  /-- Wilson-loop area law at strong coupling. -/
  areaLaw : Prop
  /-- Scope: the theorem is about the lattice-regularized theory. -/
  latticeOnly : Prop
  /-- Scope: strong coupling (small β) only. -/
  strongCouplingOnly : Prop
  /-- NOT claimed: the continuum limit (a → 0). -/
  continuumLimitNotIncluded : Prop

/-- Balaban's renormalization-group program.
    Source: T. Balaban, series in *Commun. Math. Phys.* (1987–1995,
    ~500 pages): block-spin RG for lattice gauge theory. It proves
    existence and convergence to the continuum limit at small bare
    coupling — the closest any program has come to the Clay existence
    half. It does NOT prove a positive mass gap, and critics (including
    Jaffe) note open issues at the large-field control step. -/
structure BalabanRGProgram where
  /-- Block-spin RG proves existence of the continuum limit at small
      bare coupling. -/
  continuumExistenceSmallCoupling : Prop
  /-- Convergence of the RG flow, as proved. -/
  rgConvergence : Prop
  /-- NOT proved: a positive mass gap. -/
  massGapNotProved : Prop
  /-- Open issues at the large-field control step (critics incl. Jaffe). -/
  largeFieldControlOpen : Prop
  /-- Scope: small bare coupling only. -/
  smallCouplingOnly : Prop

/-- φ⁴₄ is trivial.
    Source: Aizenman–Duminil-Copin, "Marginal triviality of the scaling
    limits of critical 4D Ising and φ⁴ models," *Ann. Math.* 194 (2021)
    163–235. The 4D scalar route is closed — which sharpens why YM₄ is
    the only remaining candidate for a non-trivial interacting 4D QFT. -/
structure Phi4Triviality where
  /-- The scaling limits of critical 4D Ising / φ⁴ models are Gaussian
      (trivial). -/
  scalingLimitGaussian : Prop
  /-- Consequence: the scalar route to a non-trivial interacting 4D QFT
      is closed. -/
  scalarRouteClosed : Prop
  /-- NOT claimed: anything about Yang–Mills. -/
  saysNothingAboutYM : Prop

/-- The 2D abelian Higgs model: the only complete example of an
    interacting gauge theory satisfying the axioms.
    Source: Brydges–Fröhlich–Seiler, "On the construction of quantized
    gauge fields," *Ann. Phys.* 121 (1979) and sequels — as the
    Jaffe–Witten problem description itself notes. -/
structure AbelianHiggs2D where
  /-- Complete construction satisfying the axioms. -/
  constructionComplete : Prop
  /-- Scope: two spacetime dimensions only. -/
  twoDimensionsOnly : Prop
  /-- Status: the nearest existing construction to what the Clay problem
      demands. -/
  nearestExistingConstruction : Prop
  /-- NOT claimed: anything in four dimensions. -/
  fourDimensionsOpen : Prop

/-- Undecidability of the *general* spectral gap.
    Source: Cubitt–Perez-Garcia–Wolf, "Undecidability of the spectral
    gap," *Nature* 528 (2015) 207–211 (arXiv:1502.04573; full version
    *Forum of Mathematics, Pi* 10 (2022) e14): no algorithm decides, for
    an *arbitrary* translation-invariant 2D lattice Hamiltonian, whether
    it is gapped or gapless in the thermodynamic limit (reduction from
    the halting problem). -/
structure SpectralGapUndecidability where
  /-- No gap-deciding algorithm for arbitrary translation-invariant 2D
      lattice Hamiltonians. -/
  noGapDecidingAlgorithm : Prop
  /-- The proof is a reduction from the halting problem. -/
  haltingReduction : Prop

/-- Ledger caution (pinned): the undecidability result is about the
    *class* of Hamiltonians — it does NOT imply the YM mass gap is
    undecidable or unprovable. YM is one specific Hamiltonian, not an
    arbitrary one. It warns against expecting a *generic* gap-deciding
    algorithm, nothing more. -/
structure GapUndecidabilityScope where
  /-- The result quantifies over arbitrary Hamiltonians. -/
  aboutArbitraryHamiltonians : Prop
  /-- It is silent about any one specific Hamiltonian (in particular YM). -/
  silentOnSpecificYM : Prop

/-! ## Transfer obstructions: why finite-matrix gaps do not transfer

The four load-bearing walls between our T1 finite results and the prize
(rungs map, Rung 4). Each is named in Lean; the bridge implications are
pinned OPEN, never claimed. -/

/-- The four transfer obstructions. -/
inductive TransferObstruction where
  | differentObjects : TransferObstruction
  | branchCrossings : TransferObstruction
  | noContinuumLimit : TransferObstruction
  | conditionalLemmas : TransferObstruction

/-- Obstruction 1 (different objects): a uniform gap in a finite Dirac
    spectrum. The Clay gap is `inf (spec H ∖ {0})` for H the Hamiltonian
    of a *constructed* 4D QFT — a different mathematical object. -/
structure FiniteDiracGap where
  /-- The finite matrix size (e.g. 32). -/
  matrixSize : ℕ
  /-- A uniform positive lower bound on its spectrum. -/
  gapBound : ℝ
  /-- Positivity of the bound. -/
  gapPos : 0 < gapBound

/-- Obstruction 1, precise: the bridge implication — a finite Dirac gap
    yields the Clay mass gap. OPEN: no such theorem exists. -/
def FiniteGapImpliesClayGap (G : CompactSimpleGroup) : Prop :=
  FiniteDiracGap → ClayYangMills G

/-- Obstruction 2 (branch crossings) is T1: `gap_closes` in
    `ThetLogos.ClayStatement` — for D(t) = diag(t, 2−t) the naive gap
    closes at t = 1. Referenced here, proved there. -/
theorem obstruction2_is_T1 : ∃ t : ℝ, diagGap t = 0 := gap_closes

/-- Obstruction 3 (no continuum/thermodynamic limit): a gap uniform in
    the lattice spacing, surviving with OS-axiom control, would give the
    continuum gap — but the hypotheses are Rung 3's open problems
    (reflection positivity and clustering for gauge-invariant
    observables; gauge-fixing vs. gauge-invariance tension). Pinned OPEN. -/
structure UniformContinuumBridge where
  /-- Gap uniform in lattice spacing a → 0. -/
  uniformGap : Prop
  /-- OS axioms (reflection positivity, clustering) verified in the limit. -/
  osControlInLimit : Prop
  /-- Conclusion: continuum YM has mass gap Δ > 0. -/
  continuumGap : Prop

/-- Obstruction 4 (conditional lemmas don't compose): the thet-logos
    spectral-gap result is a conditional finite-matrix lemma (Q4 amendment,
    `BlockedQuestions.lean`), not a mass-gap theorem. Pinned as a scope
    remark. -/
structure ConditionalLemmaScope where
  /-- The lemma's hypotheses are not discharged. -/
  conditional : Prop
  /-- It is about finite matrices, not QFT Hamiltonians. -/
  finiteMatrixOnly : Prop

/-!
## Where the prize stands relative to our work (one line)

The Clay mass gap is `inf (spec H ∖ {0}) > 0` for a *constructed*,
non-trivial 4D quantum Yang–Mills theory satisfying the axioms; we have
pinned its statement (`ClayProblem`), proved finite-matrix gap algebra
(`gap_closes`, the gap lemmas), and named the four walls between the two
(`TransferObstruction`). Nothing in this file shortens the distance —
it measures it.
-/

end ThetLogos
