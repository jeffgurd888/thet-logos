# Thermal Clock — Dossier (2026-10-17)

**Verdict: STANDS — all four charter deliverables at finite level.**
Module: `lean/ThetLogos/ThermalClock.lean`. Charter:
`whitepaper/thermal-clock-charter-DRAFT-2026-10-17.md` (NO CLAIM; this
brick is foundations packaging, like the Bridge exhibit — no Millennium
statement is touched, no continuum is claimed).

## Counts and verification

- **29 theorems/lemmas** (STRICT count: `^(theorem|lemma) ` on
  comment-stripped source), **12 definitions/structures**, zero
  `sorry`/`admit` in code (the single raw grep hit is the word "sorry"
  in the header prose describing the quarantine below).
- Targeted build green: `lake build ThetLogos.ThermalClock` —
  **3,310 jobs**.
- `#print axioms` on nine headlines (`ThermalClock.flow_add`,
  `diagFlow_add`, `modularFlow_add`, `gibbs_conversion`,
  `diagFlow_gibbs_eq_hamiltonianFlow`, `gibbs_K_eigenvalue_diff`,
  `maximallyMixedClock_stopped`, `GibbsClock.kms`,
  `ThermalClock.K_isHermitian`): each **exactly**
  `[propext, Classical.choice, Quot.sound]`. In particular **no
  `sorryAx`** — see the quarantine note in §3.
- Not root-imported (house pattern for newer modules); verified by
  targeted build.

## §1. What was built, per charter deliverable

**Deliverable 1 — the definition, pinned.** `ThermalClock N`: a faithful
finite state packaged by its eigenbasis weights, with fields
`weights`, `faithful : ∀ j, 0 < weights j`, `normalized : ∑ j, weights j
= 1`. The state's ρ (`ThermalClock.state` = `diagState`), its modular
Hamiltonian K = −ln ρ (`ThermalClock.K` = `diagModularK`), and its flow
(`ThermalClock.flow` = `diagFlow`) are **derived** definitions, not
fields — the charter's stop condition ("stipulate the flow rather than
derive it") was not triggered. `ThermalClock.K_apply_diag` proves K's
diagonal entries are exactly −log of ρ's diagonal entries (K really is
−ln ρ in the eigenbasis), and `ThermalClock.K_isHermitian` proves the
generator is Hermitian. Thermal time is the flow parameter s, by
definition. The matrix-picture companion package `GibbsClock N` carries
what that formalism carries: Hamiltonian K, Hermiticity, and the
temperature field β (with β > 0), state = `gibbsState K β`, generator =
β·K.

**Deliverable 2 — clock additivity.** Thermal time composes: flowing
s + t is flowing t then s. Proved three times, once per picture:
`diagFlow_add` / `ThermalClock.flow_add` (eigenbasis, entrywise from the
phase law `cpowI_add`), `modularFlow_add` (matrix picture, via
`Matrix.exp_add_of_commute` + the corpus's `commute_smul_K`), and
`ModularData.flow_additive` (transport of `ThermalKMS.ModularData`'s
group law, restated in clock language). Zero-time identities
(`diagFlow_zero`, `modularFlow_zero`, `ThermalClock.flow_zero`) included.
Supporting clock properties: `diagFlow_scale_weights` (rescaling all
weights by a positive constant — a change of normalization — does not
change the clock) and `cpowI_norm` (the phase factors have unit modulus;
stated unconditionally, with the docstring recording that faithfulness
is what ties `cpowI` to ρ^{is}, not what makes the phase unitary).

**Deliverable 3 — the Gibbs conversion: physical time = β × thermal
time.** Proved in three forms, §2 below. The rate β is constant —
independent of time and observable — so the Gibbs clock ticks uniformly;
temperature is the exchange rate. At β = 1 the clocks coincide.

**Deliverable 4 — the stopped clock (the H21 caution, as theorems).**
`maximallyMixedClock` (the tracial state ρ = I/N, packaged as a
`ThermalClock`) has identically trivial flow:
`maximallyMixedClock_stopped`. Also `ThermalClock.stopped_of_const_weights`
(any constant-weight clock is stopped) and
`ThermalClock.flow_fixes_of_commute` (any observable commuting with the
state is fixed by its clock). A stopped clock is a proved case, stated
in clock language — a deliverable, per the charter. Companion:
`gibbs_flux_vanishing` (transport of `thermal_flux_vanishes`): at
equilibrium the Gibbs clock's flux is zero — its hands exert no force —
and `GibbsClock.kms` (transport of `gibbs_kms`): the Gibbs state is the
KMS equilibrium state of its own clock.

## §2. The conversion, in its three proved forms

1. **Eigenvalue form** — `gibbs_K_eigenvalue_diff`: for Gibbs weights
   w_j = exp(−(βλ_j² + logZ)), the clock generator's level spacings are
   K_i − K_j = β·(λ_i² − λ_j²). This is the corpus anchor
   `modularEigenvalue_diff` composed with `gibbsDiagWeights_log`; the
   partition-function constant logZ cancels here, in the open.
2. **Eigenbasis flow form** — `diagFlow_gibbs_eq_hamiltonianFlow`:
   `diagFlow (gibbs weights) s = hamiltonianFlow (λ²) (β·s)` as maps on
   all observables, proved entrywise (the logZ phases cancel in the
   product of the two phase factors). Companion:
   `diagFlow_gibbs_logZ_independent` — the Gibbs clock does not depend
   on the logZ convention at all (via `diagFlow_scale_weights`).
3. **Matrix form** — `gibbs_conversion` /
   `GibbsClock.conversion`: `modularFlow (β·K) s = modularFlow K (β·s)`,
   by scalar congruence of the exponential arguments
   (`smul_smul` + cast arithmetic). No diagonalization is used, so this
   form is basis-free.

Faithfulness side conditions, stated exactly: Gibbs weights are
*proved* faithful (`gibbsDiagWeights_pos`: exp is positive), so the
Gibbs clock never needs faithfulness as an extra hypothesis; a general
`ThermalClock` carries faithfulness as a structure field, because at a
zero weight −log w is not the generator of anything.

## §3. Anchors re-verified this run — and the quarantine

Each charter anchor address was re-read in the source this run before
being built on: `ThermalTriple` (ModularTime.lean:44),
`modularEigenvalue`/`modularEigenvalue_diff`, `diagFlow`,
`diagModularK`, `diagFlow_trivial_of_commute`, `diagFlow_trivial_of_const`,
`maximallyMixed_flow_trivial`, `modularFlux_selfAdjoint`;
`ModularData.flow_add` (ThermalKMS.lean); plus the KMSBridge material the
build actually consumed (`gibbsState`, `gibbs_kms`, `commute_smul_K`,
`exp_smul_mul_exp_neg_smul`, `gibbsWeight_stationary`) and
`thermal_flux_vanishes` (ModularFlux.lean). All present as chartered;
ThermalKMS's own tier labels (definitions T2) are not upgraded anywhere.

**Quarantine held:** the pre-existing T3 `sorry` inside
`ModularTime.kms_identity_diagonal` (ModularTime.lean:206) is **not**
routed through by anything in this module — the conversion is assembled
from `modularEigenvalue_diff` and direct phase algebra instead, and the
axiom checks above (`sorryAx` absent from all nine headlines) are the
machine-checked proof of that statement. The charter's kill condition
("if the Gibbs conversion needs a new sorry, it lands PARTIAL with the
gap named") therefore does not fire: no new sorry exists, and none was
needed.

## §4. Fences and deviations, named plainly

- Finite level / finite modes only; the clock is a property of a
  **state**, not of spacetime; the Connes–Rovelli thermal-time
  hypothesis remains T4/T5 literature and is neither proved nor assumed;
  no continuum; not a solution to the problem of time. All in the module
  header, verbatim substance from the charter.
- **One scoping precision, not a gap:** in the matrix picture the
  conversion is stated for the generator β·K exactly (the non-scalar
  part of −ln ρ_{β,K} = βK + (ln Z)·I). A separate matrix-level lemma
  "adding a scalar multiple of I to the generator does not change
  `modularFlow`" was *not* formalized; the scalar cancellation itself
  *is* formalized — in the eigenbasis picture, where it is
  `gibbs_K_eigenvalue_diff` and `diagFlow_gibbs_logZ_independent`. If a
  future brick needs the matrix-level scalar-shift lemma, it is priced
  S (route: `exp_add_of_commute` + scalar conjugation triviality,
  cf. `scalar_conj_trivial`).
- The eigenbasis KMS identity (`kms_identity_diagonal`) remains exactly
  as it was: T3, quarantined, untouched. Discharging it via the
  KMSBridge route is a separate priced item, not part of this brick.
- The travel clock (orbit/spin metrology) has no Lean content here, by
  charter design; the summer/biology exchange is T5 conversation and
  appears nowhere in the module.
