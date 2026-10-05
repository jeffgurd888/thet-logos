# Foundations, Rebuilt from Proofs

**Date:** 2026-10-05
**Status:** working whitepaper — replaces the 2026-10-04 "Spectral Enclosure" draft (audited NO-GO, withdrawn).
**Rule of this document:** nothing is asserted beyond its evidence tier. Every section
carries its tier in its heading. Unlabeled claims do not appear here.

---

## 0. Ground rules

These are load-bearing, not decorative. They are the reason the previous draft died,
and the reason this one can live.

- **Tiers.** T1 = machine-checked in Lean 4 (zero `sorry`s). T2 = hand-verified proof.
  T3 = formalized with `sorry`s (explicit IOUs). T4 = numerical exploration.
  T5 = interpretation, hypothesis, narrative.
- **Semantic law.** A 12-dimensional algebraic kernel is not 12 physical fields.
  The exotic directions are explicit matrices with proved properties — not particles,
  not forces, not dark matter.
- **Relabeling rule.** Killed claims return only as *new, weaker* entries supported
  by fresh proof — never by rewording, never by fiat.
- **Interpretive Conservation Principle.** Every Tier-5 term must anchor to a Tier-1
  object or theorem. Interpretation never alters an operator identity.
- **Notation (locked).** `φ` = modular flux `i[K,D]` (working mathematics).
  `Φ` = the ontological glyph (never a flux operator). Golden-ratio `φ` ≠ flux `φ`.
  Two distinct modular Hamiltonians appear in the codebase and must not be conflated:
  `K_β = β·D²` (Gibbs-type, §1.2) vs. `K_ρ = −ln ρ` (synthesized, `ModularTime.lean`).
- **Ladder.** Find → Understand → Prove → Stress-test → Generalize → Connect →
  Predict → Test. Each rung is conditional on the previous one. No rung assumes
  the final physical interpretation.

---

## 1. Tier 1 — machine-checked (Lean 4, zero `sorry`s)

### 1.1 The W22 classification (the centerpiece)

`ThetLogos.cf_kernel_classification_46_22` (`CFKernel22.lean`, `CFKernelRetarget.lean`,
`OrderOne.lean`, `CFKernelClassification.lean`):

- Every `D` with `IsW22 D` lies in the ℝ-span of `dirs22`; `finrank ℝ` of the
  order-one subspace is **22** — 10 SM directions + 12 exotic survivor directions.
- 12 explicit `OrderOneHolds` proofs, one per exotic direction (`exotic*mem`
  theorems); each exotic proved self-adjoint, J-compatible, grading-odd, and
  commuting with `cfMat` (48 lemmas in `CFKernelRetarget.lean`).
- The 10 SM directions are 5 complex moduli × 2 real (`yNu, yE, yU, yD, yR`).
- Axiom footprint: `propext`, `Classical.choice`, `Quot.sound` (`#print axioms`).
- Scale: `smGen : Fin 12`; 12² = 144 pairs; 144 × 1024 = 147,456 complex component
  equations. The 46-dimensional census ran in the 272-real-dimensional admissible
  Dirac space. (The 576-pair figure belongs only to the separate Tier-4 Python scan.)
- Lake build green (2026-10-04: 3324 jobs, exit 0). Pushed to public master.

The exotic survivors, as proved objects: `exotic{Re,Im}NuLeR`, `exotic{Re,Im}ELNuR`,
`exotic{Re,Im}ULDR`, `exotic{Re,Im}DLUR`, `exotic{Re,Im}NuREbarR`, `exotic{Re,Im}EREbarR`.

### 1.2 Thermal flux vanishes (`ModularFlux.lean`)

```lean
theorem thermal_flux_vanishes {N : ℕ} (D : Matrix (Fin N) (Fin N) ℂ) (β : ℝ) :
    modularFlux ((β : ℂ) • D ^ 2) D = 0
```

For the Gibbs-type modular Hamiltonian `K_β = β·D²`, which commutes with `D`,
the modular flux `φ = i[K_β, D]` is identically zero. This promotes the old audit
claim A1 to Tier 1. Note: this is a statement about `K_β`, not about `K_ρ = −ln ρ`.

### 1.3 The active driver exists (`ModularFlux.lean`)

```lean
theorem exists_activeDriver {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℂ) (hM : M ≠ 0) :
    ∃ G, Gᴴ = G ∧ G * D ≠ D * G   -- D = fromBlocks 0 M Mᴴ 0, off-diagonal Dirac
```

with `activeDriver_selfAdjoint` proving the witness self-adjoint. A self-adjoint
block driver provably does not commute with the off-diagonal Dirac operator when
`M ≠ 0`. This closes the old Gate-G existence placeholder. It proves a mechanism;
it proves nothing about physics.

### 1.4 Spectral gap — conditional lemma, not a mass gap

`spectralGap_pos` (`ThermalKMS.lean`): the gap `Δ = min positive eigenvalue` of a
Hermitian `D` is positive **when `D` is invertible on its support**. The hypothesis
is the content. There is **no** unconditional mass-gap theorem for `D_F`;
`BlockedQuestions.lean` Q4 records the closed-form spectral gap as blocked.

### 1.5 Supporting machine-checked infrastructure

- `order_zero_condition` (`FiniteSpectralTriple.lean:118`): `[π(a), π°(b)] = 0`.
- `modularFlux_selfAdjoint` (`ModularTime.lean:229`): the flux `φ = i[K,D]` is
  self-adjoint — the machine-checked fact behind the notation doctrine.
- Ternary TRO identities (`TRO.lean`); three-generation inheritance theorems
  (`ThreeGen.lean`: 16 proved, zero `sorry`s).

---

## 2. Tier 2 — hand-verified

### 2.1 `dim_R ker L = 4` — the careful version

VORTEX-005 hand-verifies `dim_R ker L = 4` where `L` is the **chirality-odd
Yukawa-consistency operator on a single Dirac block**. This is explicitly:

- a *different operator* from the order-one commutator stack of §1.1;
- a *different operator* from `linL(X) = X + N₀XN₀` on `M₂(ℝ)`, for which the
  `dim ker L = 4` claim was **withdrawn as inconsistent** (`Axioms.lean` —
  it must not be reintroduced, with or without `sorry`);
- **not a spacetime claim.** No derivation of manifold dimension is asserted here.

### 2.2 E13-E Phase 4 (Seeley–DeWitt)

Tier-2 computation on `M₄ × S¹_β × F₃₂`; verdict PASS with explicit assumptions
(`whitepaper/e13e-phase4-seeley-dewitt.md`, 2026-10-02). The temporary lifting
of the spectral-action freeze expired with that verdict; the freeze is reinstated.
Surviving results keep Tier 2 (computation) / Tier 5 (physical reading).

---

## 3. Tier 4 — numerical, fenced

- **Python census** (24-generator scan): corroboration of §1.1 only. Supporting
  evidence; never a substitute for machine proof.
- **`V_eff` moduli exploration**: conditional GO with explicit kill criteria.
  A numerical minimum is not a physical vacuum and must never be advertised as
  deriving selection rules. Not yet built.

---

## 4. Tier 5 — interpretation, fenced

- **Gurd Law** (meta-tier, 2026-10-02): "Before information can be processed or
  communicated, the boundary must first be drawn and contained." A methodological
  law. It is not a physics postulate and is not cited as one.
- **Thet ontology / color mnemonics** (θ forward, σ_s modular flow, θ† return;
  Blue/Red/Green cast): storytelling layer over the Tier-1 objects above.
  The operators and the flow are real mathematics; the color names point at
  structure that is independently real. Wonder labeled as wonder.

---

## 5. Withdrawn and killed — do not reintroduce

| Item | Status |
|---|---|
| `dim ker linL = 4` for `linL(X) = X + N₀XN₀` on `M₂(ℝ)` | **Withdrawn as inconsistent** (`Axioms.lean`) |
| Spacetime manifold dimension derived from any kernel dimension | **Killed** — built on the withdrawn claim |
| Unconditional mass gap `Δ > 0` for `D_F` | **Killed** — no theorem; Q4 blocked; only §1.4's conditional lemma exists |
| Old 46 → 10 chain | **Unsound as stated**, preserved and flagged |
| Golden-ratio/Fibonacci φ-tower as physical mass hierarchy | **Killed** (2026-09-29; unkill refused 2026-10-01) |
| MOND derivation; parameter-free Higgs/top predictions; claimed RG results | **Killed** |
| C⁷ torsion stabilizer; Gate-L experimental numbers; "ACMD resolves spacetime, mass gaps, entropy" | **Killed** |
| Correspondence Memory / Spectral Technology as built systems | **Killed** |

Full kill log: `whitepaper/proof-status-ledger-46-22-2026-10-01.md` §4 and
`~/workspace/audit/acmd-claim-audit-2026-10-03.md` (66 claims: 27 stand, 17 need
fixes, 13 killed, 9 background/meta).

---

## 6. Open questions — the ladder (each rung conditional)

1. Decompose the 12-dim exotic part into canonical invariant pieces → architecture, not a number.
2. Generalize to N generations (`H_F ⊗ ℂ^N`) → a family framework; does not explain N = 3.
3. Representation-theoretic classification of the exotics → selection rules.
4. Stability under symmetry-preserving perturbations → rigidity.
5. Spectral-action fingerprints (`Tr f(D²/Λ²)`) → first bridge, via frozen SA-4 only.
6. `V_eff` over the 22-dim moduli → preferred configurations *within the model*.
7. Formalize the *next* theorems → §1.1 is done; the next ones are not.
8. Full independent reproduction → implementation-independence.
9. Admissible deformations `D_F → D_F + δD` → moduli space of valid geometries.
10. Finite-to-continuum correspondence → a program, not an assumption.
11. Experimental prediction → the final gate.

Boundary: no item here may be cited as an established result or a prediction
until its own proof or measurement exists.

---

## 7. What this document is not

It is not a physical theory. It claims no continuum physics, no particles, no
masses, no cosmology. It is a ledger with a narrative spine: here is what the
machine proved, here is what hands verified, here is what numbers suggest, here
is what we wonder, here is what died. The proofs are the floor. Everything else
is scaffolding or sky.
