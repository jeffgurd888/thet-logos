# thet-logos — Active Cartesian Modular Dynamics (ACMD)

**Machine-verified foundations for quantum field theory, in Lean 4.**

This repository is the working record of an independent research program
(Nexus Research) building rigorous foundations for 4D quantum field theory
one machine-checked rung at a time. Every theorem here is verified by the
Lean kernel. Every claim is labeled by its evidence tier (see
[Tiers](#tiers-as-used-in-this-repository)), and every killed claim is
published next to the proofs, with the kill on record.

**2,080 verified theorem declarations**\*
across 98 Lean modules, with whitepaper dossiers for every campaign.

\* *Theorem count and verification scope subject to reproducible build and
proof-dependency audit. Count method: theorem/lemma declarations in the
program's counted modules, each verified by targeted `lake build`;
headline results additionally checked with `#print axioms` (only
`propext`, `Classical.choice`, `Quot.sound`).*

## The paper

**Active Cartesian Modular Dynamics: Machine-Verified Foundations**

- Current version (v2): [doi.org/10.5281/zenodo.23427964](https://doi.org/10.5281/zenodo.23427964)
  — Rungs 1–10, second quantization for both statistics, appendices.
- v1: [doi.org/10.5281/zenodo.23408680](https://doi.org/10.5281/zenodo.23408680)
- Author: Jeffrey Michael Gurd, Nexus Research —
  [ORCID 0009-0008-0188-5150](https://orcid.org/0009-0008-0188-5150)
- Paper license: CC BY 4.0. Code license: MIT (see below).

## What stands (all T1 unless noted)

- **Rungs 1–8** — finite spectral triple with three-generation
  inheritance; almost-commutative product geometry; fermionic and
  bosonic Fock spaces with the CAR/CCR algebra proved. (Paper v2.)
- **Rung 9** — second quantization Γ/dΓ for fermions; the free
  Hamiltonian gap **derived**, not assumed (finite modes).
- **Rung 10** — the same for bosons. Finite-mode second quantization is
  complete for **both statistics**.
- **Standard Model match** — 3 MATCH + 1 PARTIAL against the finite
  spectral-triple data, with the caveats *proved*, not hidden
  ([dossier](whitepaper/sm-match-2026-10-11.md)).
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
  invariant under the **full restricted Lorentz group**: rotations
  (2026-10-11) and boosts (discharged 2026-10-17)
  ([dossier](whitepaper/mass-shell-boost-discharge-2026-10-17.md)).
- **Bridge exhibit** — finite graph bridge algebra: the Laplacian as
  L = dᵀσd (boundary operator, Ohm's law, divergence), Kirchhoff's laws,
  and the Fiedler variational bound
  ([dossier](whitepaper/bridge-laplacian-2026-10-17.md)).
- **Pitch 4 is scoped, not built** — the continuum passage, staged and
  priced (finite lattice gauge theory first)
  ([scoping](whitepaper/pitch-4-continuum-scoping-DRAFT-2026-10-17.md)).

## Not claimed

- **Not claimed: the continuum limit, interacting 4D QFT, the
  Yang–Mills mass gap.**
- Parts of any official Clay Millennium statement closed by this
  program: **0**. The Yang–Mills problem is the program's horizon and
  direction, not a result.
- The interacting gap results above are finite-mode / finite-lattice
  statements in the eigenvalue sense stated in their dossiers. They are
  scaffolding toward the continuum problem, not the continuum problem
  solved.
- Masses and couplings in the Standard Model match are labeled inputs,
  not predictions.

## Verify it yourself

```bash
cd lean
export PATH="$HOME/.elan/bin:$PATH"
lake build ThetLogos.BridgeLaplacian   # any module, targeted build
```

Recent campaign modules are verified by targeted builds as above;
headline theorems carry `#print axioms` checks in their dossiers
(standard three axioms only, no `sorry` anywhere in the modules cited
above). Numerical engines (separate, Python, *numerical* tier — not
proofs):

```bash
cd python && pip install -r requirements.txt && python3 run_all.py
```

## Foundational results (2026-09/10)

- **22-direction classification of the order-one commutant W₂₂** —
  `cf_kernel_classification_46_22`, zero `sorry`s, unconditional.
  The finite spectral triple's order-one constraint system admits
  exactly a 22-dimensional real solution space (10 SM + 12 exotic
  directions). The exotic directions are explicit non-claims — not
  physical fields. `lean/ThetLogos/CFKernel22.lean`.
- **Order-zero for all 144 generator pairs** — machine-checked, zero
  `sorry`s. `lean/ThetLogos/MartinettiRep.lean`. Order-zero is one
  axiom, not a Standard Model derivation.
- **Thet engine (numerical)** — a quantum Otto cycle on the finite
  Dirac operator closes with positive net work (W_net = 0.155,
  η = 0.50 < Carnot 0.83). A numerical engine *design*, not a device.
  `python/thet_logos/engine_cycle.py`.

## Tiers, as used in this repository

| Tier | Meaning |
|---|---|
| **T1** | Machine-checked Lean proof (kernel-verified, axioms audited) |
| **T2** | Axiomatized / assumed input, labeled as such wherever used |
| **T5** | Quarantined speculation — ontology, interpretation, vision |
| **KILL** | Tested and refuted; published as a result |
| **FRONTIER / PRICED** | Open, with its obstruction named and its cost estimated |

Strict rule: **Theorem ≠ Simulation ≠ Experiment ≠ Device.** A Lean
`sorry` is never a proof, and numerical checks establish consistency,
not physical evidence.

## The framework behind the program

The program grew out of the **Ontological Thet–LOGOS Framework** —
operator-algebraic foundations and finite spectral-triple geometry
originating from a ternary structure (thet θ → ternary TRO → ker L →
ℂ³² → spectral triple). The framework's ontology — including the
10-rung chromatic ladder in `chromatic/` — is retained in this
repository as its organizational and historical record. Where framework
language and the proof ledger differ, **the ledger governs**: e.g., the
early claim that dim ker L = 4 fixes spacetime dimension is
**withdrawn** on record (the weld analysis replaced it: signature is
extra data, machine-checked in `lean/ThetLogos/EdgeSignature.lean`).

## Layout

```
lean/              Lean 4 + Mathlib project (ThetLogos.*, 98 modules)
whitepaper/        campaign dossiers, gauntlets, scopings (92 documents)
python/            numerical engines (run: python3 python/run_all.py)
docs/              audit, reproducibility, ontology, bridge maps
epistemic-ledger/  tier ledger of claims
axioms/ algebra/ spectral/ chromatic/   framework record (see above)
examples/ scripts/ worked examples and tooling
```

## License

MIT — see [LICENSE](LICENSE).

## Support this research

Independent research, no institutional funding. Donations are voluntary
and never a toll — the work is free for everyone, forever:

- **Cash App:** [$Gurd888](https://cash.app/$Gurd888)

— Jeffrey Michael Gurd, Nexus Research
