# Active Cartesian Modular Dynamics: Machine-Verified Foundations

**DRAFT — 2026-10-10. Local only. Not for publication until reviewed.**

Rungs 1–3: finite spectral triple → almost-commutative product → Lorentzian-structure pins.

## Abstract

This document states exactly what the machine has verified in the ACMD program
through Rung 3, with nothing else. Every theorem named here is proved in Lean 4
with zero `sorry`s (T1), or explicitly labeled with its tier. The finite spectral
triple and its W22 classification are machine-checked. The Connes–Kreimer Hopf
algebra of renormalization is formalized, with the corrected antipode axiom
proved. The almost-commutative product is built, its twist derived (not
assumed), and its real structure and Krein structure promoted from pins to
proved consequences. The twisted first-order condition is partially built with
its exact obstruction priced. The Wightman axioms are stated as opaque
propositions — unproved, by design. No continuum limit is claimed. No mass gap
is claimed. No four-dimensional quantum field theory is claimed. What follows
is the inventory.

**Tier key.** T1: proved in Lean 4, zero sorrys. T2: axiomatized, with proved
(T1) consequences. T3: theorem stated with assumptions, proof open (one such
theorem exists in the corpus and is labeled). T5: opaque or quarantined —
theorem-shaped, content not established. Killed: refuted or withdrawn; stays
dead unless returned as a new entry by proof.

---

## 1. Rung 1 — The finite spectral triple (T1)

The finite factor is a concrete matrix spectral triple. Its classification and
constraint census are machine-checked.

**Classification and census.** The generator family `smGen : Fin 12` gives
12² = 144 pairs; the order-zero condition is checked machine-side over
144 × 1024 = 147,456 complex components
(`order_zero_comm`, `InnerFluctuations.lean`; scale per
`whitepaper/foundations-from-proofs-2026-10-05.md`). The three-generation
inheritance is proved in `ThreeGen.lean` (20 theorems, zero sorrys), including
`smGen3_order_zero`, `smDirac3diag_order_one`, and the Kronecker-factorization
identities (`smGen3_eq_kronecker`, `smDirac3diag_eq_kronecker`). The 576-pair
order-one census (24 × 24 doubled elements) is a T4 Python scan, not a Lean
proof (`whitepaper/bridge-span-2-involutive-twist-2026-10-07.md`).

**Modular dynamics.** `ModularFlux.lean` proves `thermal_flux_vanishes`: the
modular flux vanishes identically on Gibbs states, for every inverse
temperature β. `exists_activeDriver` proves a non-equilibrium driver exists
that produces nonzero flux. `modularFlux_selfAdjoint` (`ModularTime.lean:229`)
proves the flux φ = i[K, D] is Hermitian. Gauge covariance
(`modularFlux_gaugeCovariant`) and trace gauge-invariance
(`modularFlux_trace_gaugeInvariant`) are proved.

**The ultimate reduction.** `UltimateReduction.lean` proves 6 T1 theorems,
zero sorrys: `dynamicallyFrozen_of_noHeat_noGauge` (no state and no
fluctuation implies a frozen construction), `equilibriumKillsFlux` (equilibrium
kills flux for arbitrary fluctuated D_A), `activeFlux_nonzero_on_gaugeBackground`,
`activeDriver_pushes_against_gauge`, `modularFlux_scalarShift`, and
`thet_universal`. The same file records what died at finite level:
micro-vortices (no vorticity operator exists in the finite triple) and
vortices→matter→gravity (needs continuum, stress-energy, Einstein dynamics).

**Connes–Kreimer Hopf algebra.** `Renormalization.lean` (60 theorems, zero
sorrys) formalizes the Hopf algebra of rooted trees: coproduct, B₊ grafting,
`counity_left`, `counity_right`, and `coassociativity_theorem`. On the
antipode, the record is two-sided and both sides are kept: the as-stated
antipode axiom was **refuted** (`antipodeAxiom_false`), and the corrected
evaluation-into-the-group-ring version was **proved**
(`antipodeAxiomEval_proved`, `Renormalization.lean:1446`, T5→T1). The refuted
statement is not laundered into the proved one; they are different claims.

**One T3.** `kms_identity_diagonal` (`ModularTime.lean:206`) is stated with a
`sorry`, explicitly labeled a Tier T3 target, and numerically verified to
1e-15–1e-20. It is the only open proof obligation among the Rung 1 T1/T3
results inventoried here; six further T5-conjecture sorrys are documented in
`BlockedQuestions.lean` (5) and `XYZTripotents.lean` (1) — all pre-existing,
all labeled in-file. "Zero new sorrys across Rungs 1–3" holds.

---

## 2. Rung 2 — The almost-commutative product (T1)

`ProductTriple.lean` (63 theorems/lemmas, zero sorrys) builds the product of an
axiomatized manifold factor with the finite triple.

**Product Dirac identity.** `Dprod_sq` proves
D_prod² = D_M² ⊗ 1 + 1 ⊗ D_F². The old dead T5 axiom `product_sum_of_squares`
was promoted to this proved T1 — upgraded, not resurrected.

**Twist derived, not assumed.** The product twist is the flip on the doubled
product algebra (`flipProd_involutive`, `flipProd_CM_regular`,
`prodFlip_CM_regular` — the DLM flip is Connes–Moscovici regular
unconditionally). The candidate ρ_M ⊗ ρ_F as product twist was killed: it does
not typecheck, because a flip acts on pairs and a tensor-twist on factors.

**Inner fluctuations decompose.** `prod_commutator_decomp` splits fluctuations
into manifold and finite parts (`prod_commutator_pureManifold`,
`prod_commutator_pureFinite`). Finite fluctuations alone give scalar-type
terms; the manifold factor gives gauge parameters a field-valued address.

**KO data.** `koProd_signs` proves the KO signs ⟨−1, 1, −1⟩
(`koDim_add`: (4 + 6) % 8 = 2).

**Causality re-entry.** `CausalProduct.lean` proves the Span-5 finite causality
obstruction does **not** carry to the product: `trace_collapse_hypothesis_fails`
(the kill's unstated finite-trace hypothesis cannot fire where [D, f] is not
trace-class) and `product_not_forced_central` (the finite conclusion is false
on the product). Genuine causal order is pinned, with its exact price: global
hyperbolicity.

**The 6-dim caveat.** The surviving finite represented gauge algebra is six
real dimensions: Option-A kills the represented M₃(ℂ) summand. The full SM
gauge group is not claimed from the finite factor
(`whitepaper/rung-2-manifold-factor-2026-10-08.md`, §5 honest ledger).

---

## 3. Rung 3 — Lorentzian-structure pins (T2+T1, one partial)

Rung 3 attacked the three items Rung 2 left pinned, plus cleanup. Verdicts per
`whitepaper/rung-3-verdicts-2026-10-10.md`.

**Antilinear J — PROMOTED (T2+T1).** The pin's root obstruction (bare ℂ-modules;
J not even statable) was removed by honest enrichment of `TripleData`:
sesquilinear form (positivity, nondegeneracy, completeness all explicitly NOT
assumed), antilinear `Janti` with KO axioms keyed to sign data. Product
theorems proved T1: `Jprod_sq` (J² = −1), `Jprod_D` (JD = DJ), `Jprod_Γ`
(JΓ = −ΓJ), via Mathlib semilinear `TensorProduct.map`. Flagged, not claimed:
`conjJ`↔`Janti` compatibility.

**Krein inner product — PROMOTED (T2+T1).** `ηsym` with η² = 1 and
form-self-adjointness (`ηprod_sq`, `ηprod_selfadj` proved T1). No adjoint
operator is constructed; no Hilbert identity is claimed. The killed
Lorentzian language stays killed: η_prod is an abstract fundamental symmetry,
not a spacetime signature.

**Twisted first-order condition — PARTIAL.** Built: the opposite
representation in the `conjJ`-shadow of a° = Ja*J⁻¹ (`oppProd`,
`oppgrandProd` — multiplication reverses, T1); flip-compatibility discharged
in its statable form; diagonal reduction proved
(`prodTwistedFOC_diag_reduce`: twisted FOC on the physical diagonal ⟺
ordinary product FOC). Re-pinned with exact obstruction: (1) no `Star` instance
on `Module.End` over the tensor module — the textbook Ja*J⁻¹ cannot even be
written; (2) factor-level order-one absent from `TripleData` (the finite
factor's proved order-one is for the concrete matrix triple, not the abstract
class).

**Continuum scoping — STANDS as priced roadmap, no limit claimed.**
`whitepaper/rung-3-continuum-scoping-2026-10-10.md`: AF-algebras least
tractable (one triple, not a directed system); lattice refinement buys
validation only; analytic per-axiom inventory most tractable. "Finite triple
converges" language killed with reason. Cheapest next step: Hilbert-enrichment
of `TripleData`.

**Cleanup.** Antipode closed (T5→T1, verified). Fock advanced: `FreeField.lean`
gains 8 fermionic T1s — `fermionExp_vacuum`, `fermion_onePoint_vanishes`,
`fermion_twoPoint_algebraic_trivial`, `ferm_ι_anticomm`,
`createFerm_anticommute`, `pauli_exclusion`, `fermion_mem_adjoin_range`,
`fermion_vacuum_cyclic` (mixed CAR / number operators still open on the
`fockInnerProduct` Mathlib gap; `satisfiesDestruction` untouched pending the
Yukawa modeling decision).

**Promotion honesty.** The Rung 3 promotions are T2-axiomatization plus T1
consequences — not derivation from analysis. The dossier states this; so does
this paper.

---

## 4. Tier ledger

| Result | Tier | Evidence |
|---|---|---|
| Finite triple classification, 144-pair order-zero | T1 | `order_zero_comm`, `ThreeGen.lean` (20 thms) |
| Modular flux vanishes on Gibbs states; active driver exists; flux Hermitian | T1 | `thermal_flux_vanishes`, `exists_activeDriver`, `modularFlux_selfAdjoint` |
| Ultimate reduction (6 theorems) | T1 | `UltimateReduction.lean`, zero sorrys |
| Connes–Kreimer: coproduct, B₊, counity, coassociativity | T1 | `Renormalization.lean` (60 thms) |
| Corrected antipode axiom (eval version) | T1 (was T5) | `antipodeAxiomEval_proved` (:1446) |
| As-stated antipode axiom | Killed (refuted) | `antipodeAxiom_false` |
| Product Dirac identity; flip twist; fluctuation decomposition; KO signs | T1 | `ProductTriple.lean` (63 thms) |
| Span-5 obstruction does not carry to product | T1 from T2 product axioms | `trace_collapse_hypothesis_fails`, `product_not_forced_central` (footprint incl. `CausalProduct` axioms) |
| Antilinear J on product; Krein structure | T2+T1 | `Jprod_sq/D/Γ`, `ηprod_sq/selfadj` |
| Twisted FOC: opposite rep, diagonal reduction | T2+T1 (partial) | `oppProd`, `prodTwistedFOC_diag_reduce` |
| Twisted FOC (general) | Pinned | priced: Star-on-End, factor order-one |
| Fock space (bosonic + fermionic core) | T1 | `FreeField.lean` (14 thms, 8 new) |
| KMS identity (diagonal) | T3 | `kms_identity_diagonal` — sorry, numerically verified |
| Wightman axioms | T5 (opaque Props) | `WightmanAxioms.lean` — stated, unproved by design |
| Clay Yang–Mills statement | T5 (theorem-shaped) | `ClayStatement.lean` — fixed target; `gap_closes` T1 shows finite-matrix gaps don't transfer |
| Mass gap | T5 (quarantined) | `massGapNotProved : Prop` (`MassGapDossier.lean:68`) |
| Continuum limit | T5 (quarantined) | priced roadmap only |

**Axiom footprint.** All `#print axioms` on new theorems in the
Mathlib-transitive-clean files: `[propext, Classical.choice, Quot.sound]`
(per Rung 3 verdict dossier). Exception, stated plainly: the two
CausalProduct theorems (`trace_collapse_hypothesis_fails`,
`product_not_forced_central`) are T1-proved *consequences of the
T2-axiomatized product structure* — their footprint includes the
`CausalProduct` file-level axioms (`prod_nonzero_causal_commutator` et al.).
Genuine proofs; wider footprint; labeled as such in the tier table.
**Build.** Full `lake build` green per the Rung 3 dossier; zero new sorrys
across Rungs 1–3. [VERIFY: re-run `#print axioms` sweep and full build before
publication.]

**T1 count.** 177 proved theorems/lemmas across the six inventoried files
(ProductTriple 63, Renormalization 60, ThreeGen 20, FreeField 14,
FiniteSpectralTriple 14, UltimateReduction 6), plus the ModularFlux/ModularTime
and CausalProduct T1s named above. Every count verified by grep over the
repository on 2026-10-10.

---

## 5. Kill ledger

- **Span 1 (twist-from-flow).** Killed: Connes–Moscovici regularity,
  preservation, and J-compatibility fail numerically for the modular-flow
  twist. The DLM minimal twist by grading survives; the twisted 576-pair
  order-one census is kept as a ledger entry.
- **Span 5 (finite causal cone).** Killed at finite level — and proved not to
  carry to the product. Causality is re-priced at global hyperbolicity, not
  abandoned.
- **φ-tower.** Killed: real fermion mass ratios do not scale by powers of φ.
  Restricted to an isolated symbolic toy.
- **Icosahedral hypothesis.** Killed structurally: explicit A₅ subgroups exist
  in degeneracy sectors but act trivially on the represented gauge algebra; no
  natural 12-object orbit.
- **Micro-vortices.** Killed: no vorticity operator exists in the finite
  triple.
- **"Finite triple converges."** Killed as language: no continuum limit is
  claimed; the lattice toy buys validation only.
- **Finite thermal phase transitions.** Killed: no thermodynamic-limit
  machinery; the magnetophase landscape is ruled/linear.

Killed claims return only as new, weaker entries with new proof. The originals
stay dead.

---

## 6. What is NOT claimed

This section is the paper's immune system.

- **No 4D QFT.** The finite triple is zero-dimensional. The Connes–Kreimer
  Hopf algebra is the combinatorics of renormalization, not a field theory.
- **No Wightman proof.** The six axioms are opaque Props by design. Stating
  them is not proving them.
- **No continuum limit.** The continuum is a priced roadmap. Nothing converges
  in this paper.
- **No mass gap.** `massGapNotProved` is declared, not proved. The Clay
  statement is a fixed target so future partial results measure against an
  unmoving goal.
- **No full SM gauge group from the finite factor.** Six real dimensions
  survive in the representation. The full symmetry needs the manifold factor,
  and the Yukawa sector (`satisfiesDestruction`) is untouched pending a
  modeling decision — Yukawas remain empirical inputs.
- **No derivation from analysis.** The Rung 3 promotions axiomatize structure
  and prove consequences. Boundedness, compact resolvent, and completeness are
  not established.
- **No physical predictions.** Spectral distances, flux values, and thermal
  numbers in this corpus are properties of the mathematical model, not
  measurements of nature, until a physical correspondence is established and
  tested.

---

## 7. The road ahead (priced, not promised)

Rung 4's admission price, from the Rung 3 verdict:

1. **Hilbert-enriched `TripleData`.** Inner product with positivity —
   the debt Rung 3 explicitly left open.
2. **Bounded commutators** as class data.
3. **Compact resolvent** as class data.
4. **Factor-level order-one** as class data — discharges the twisted FOC's
   remaining pin.

Then the Wightman axioms, still quarantined as opaque Props until the analysis
exists. The summit — Yang–Mills existence and mass gap — is the mission
target. It gets claimed when the machine says so.

---

*Notation.* φ denotes modular flux (Hermitian, `modularFlux_selfAdjoint`).
Φ is reserved for the ontological glyph and is not used in this paper.
