# thet-logos — Active Cartesian Modular Dynamics (ACMD)

[![License: MIT](https://img.shields.io/badge/license-MIT-green.svg)](LICENSE)
[![Paper v2 — DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.23427964.svg)](https://doi.org/10.5281/zenodo.23427964)
![Theorem declarations](https://img.shields.io/badge/theorem%20declarations-2%2C216-blue)
![Lean](https://img.shields.io/badge/Lean%204%20%2B%20Mathlib-formal%20proofs-purple)

> "If we don't stop worrying about the Almighty dollar, we'd never
> gonna change the world!"
> — Caleb Gurd, as remembered by his father. The standard this
> program answers to at home.

**Machine-verified foundations for quantum field theory, in Lean 4.**

An independent research program (Nexus Research) building rigorous
foundations for 4D quantum field theory one machine-checked rung at a
time. Every theorem is verified by the Lean kernel. Every claim is
labeled by its evidence tier, and every killed claim is published next
to the proofs, with the kill on record.

**2,216 verified theorem declarations**\*
across 98 Lean modules, with whitepaper dossiers for every campaign.

\* *Theorem count and verification scope subject to reproducible build
and proof-dependency audit. Count method: theorem/lemma declarations in
the program's counted modules, each verified by targeted `lake build`;
headline results additionally checked with `#print axioms` (only
`propext`, `Classical.choice`, `Quot.sound`).*

## Credit

This program formalizes; it did not originate the ideas, the
problems, or most of the mathematics it verifies. The staircase is
named in [ACKNOWLEDGMENTS.md](ACKNOWLEDGMENTS.md) — Dirac, Connes,
Tomita–Takesaki, Wightman, Osterwalder–Schrader, Wilson, and the
Lean/Mathlib community among them. If this corpus is ever cited,
cite the originators first.

## The paper

**Active Cartesian Modular Dynamics: Machine-Verified Foundations**

- Current version (v2): [doi.org/10.5281/zenodo.23427964](https://doi.org/10.5281/zenodo.23427964)
- v1: [doi.org/10.5281/zenodo.23408680](https://doi.org/10.5281/zenodo.23408680)
- Author: Jeffrey Michael Gurd, Nexus Research —
  [ORCID 0009-0008-0188-5150](https://orcid.org/0009-0008-0188-5150)
- Paper license: CC BY 4.0. Code license: MIT.

## What stands (all T1 unless noted)

- **Rungs 1–8** — finite spectral triple with three-generation
  inheritance; almost-commutative product geometry; fermionic and
  bosonic Fock spaces with the CAR/CCR algebra proved. (Paper v2.)
- **Rungs 9–10** — second quantization Γ/dΓ for both statistics; the
  free Hamiltonian gap **derived**, not assumed (finite modes).
- **Standard Model match** — 3 MATCH + 1 PARTIAL, caveats *proved*,
  not hidden ([dossier](whitepaper/sm-match-2026-10-11.md)).
- **Pitch 2** — the free theory at **countably many modes**: the gap
  survives the infinite-mode limit, in the
  eigenvalue-on-finite-particle-domain sense
  ([A](whitepaper/pitch-2-campaign-a-2026-10-16.md),
  [B](whitepaper/pitch-2-campaign-b-2026-10-16.md)).
- **Pitch 3** — the program's **first interacting Hamiltonians**.
  Fermionic: complete, gap persistence proved at finite modes
  ([dossier](whitepaper/pitch-3-campaign-1-2026-10-16.md)). Bosonic:
  interaction calculus, exact diagonal gap, windowed persistence —
  with **essential self-adjointness still open and labeled as such**
  ([dossier](whitepaper/pitch-3-campaign-2-2026-10-17.md)).
- **Schrödinger dynamics** — time evolution, unitarity, picture
  equivalence; the interacting gap clusters proved invariant in time
  ([dossier](whitepaper/schrodinger-dynamics-2026-10-17.md)).
- **Rung 7 completion** — the free one-particle mass-shell measure is
  invariant under the **full restricted Lorentz group** (boosts
  discharged 2026-10-17)
  ([dossier](whitepaper/mass-shell-boost-discharge-2026-10-17.md)).
- **Bridge exhibit** — finite graph bridge algebra: L = dᵀσd,
  Kirchhoff's laws, the Fiedler variational bound
  ([dossier](whitepaper/bridge-laplacian-2026-10-17.md)).
- **Pitch 4, Stage 0** — **finite lattice gauge theory STANDS**:
  group-valued links, Wilson action, product-Haar measure, and
  **exact gauge invariance proved for every gauge transformation** —
  the corpus's first quantized gauge sector (finite lattice only;
  reflection positivity is Stage 1b, priced)
  ([dossier](whitepaper/pitch-4-stage-0-2026-10-17.md),
  [scoping](whitepaper/pitch-4-continuum-scoping-DRAFT-2026-10-17.md)).
- **Pitch 4, Stage 1a** — **lattice correlations STAND**: the Gibbs
  measure constructed, covariance and Cauchy–Schwarz proved, and
  **Elitzur's theorem**: gauge-variant insertions have expectation
  zero at every coupling, for a general gauge group
  ([dossier](whitepaper/pitch-4-stage-1a-2026-10-17.md)).

**Foundational results**

- **22-direction classification of the order-one commutant W₂₂** —
  `cf_kernel_classification_46_22`, zero `sorry`s, unconditional: the
  order-one constraint system admits exactly a 22-dimensional real
  solution space (10 SM + 12 exotic directions; the exotic directions
  are explicit non-claims). `lean/ThetLogos/CFKernel22.lean`.
- **Order-zero for all 144 generator pairs** — machine-checked, zero
  `sorry`s. `lean/ThetLogos/MartinettiRep.lean`.

**Background algebra (all T1)** — Weld duality (the boundary pair
algebra: idempotents, trace rigidity, resting-place theorems;
[dossier](whitepaper/weld-duality-2026-10-16.md)) · FluxTwist
(flux-twisted ring spectrum) · TritGrading (ℤ₃ grading) ·
SexagesimalClock (mod-60 CRT grading). Theories intake, Round 1:
KMS/Tomita–Takesaki and classical Yang–Mills FIT at the finite level;
continuum claims NO-FIT, on record
([dossier](whitepaper/theories-intake-2026-10-11.md)).

## Not claimed

- **Not claimed: the continuum limit, interacting 4D QFT, the
  Yang–Mills mass gap.**
- Parts of any official Clay Millennium statement closed by this
  program: **0**. Yang–Mills is the program's horizon, not a result.
- The gap results above are finite-mode / finite-lattice statements in
  the eigenvalue sense stated in their dossiers — scaffolding toward
  the continuum problem, not the continuum problem solved.
- Masses and couplings in the Standard Model match are labeled inputs,
  not predictions.

## Verify it yourself

```bash
cd lean
export PATH="$HOME/.elan/bin:$PATH"
lake build ThetLogos.BridgeLaplacian   # any module, targeted build
```

Headline theorems carry `#print axioms` checks in their dossiers
(standard three axioms only). Tiers: **T1** machine-checked proof ·
**T2** axiomatized input, labeled · **T5** quarantined speculation ·
**KILL** tested and refuted, published as a result · **FRONTIER**
open, obstruction named. Strict rule: Theorem ≠ Simulation ≠
Experiment ≠ Device. (Numerical engines live in `python/` and are
numerical-tier, not proofs.)

## License

MIT — see [LICENSE](LICENSE).

## Support this research

Independent research, no institutional funding. Donations are voluntary
and never a toll — the work is free for everyone, forever:

- **Cash App:** [$Gurd888](https://cash.app/$Gurd888)

— Jeffrey Michael Gurd, Nexus Research
