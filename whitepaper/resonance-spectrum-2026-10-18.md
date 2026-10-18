# Resonance Spectrum — the pin, landed (2026-10-18)

**Module:** `lean/ThetLogos/ResonanceSpectrum.lean` — new, nothing existing modified.
**Build:** targeted `lake build ThetLogos.ResonanceSpectrum` green, **3,317 jobs**, `.olean` present.
**Counts:** **15 strict T1** (house method: line-initial `^(theorem|lemma) ` on comment-stripped source) **+ 2 defs**; **0 `@[simp]`**; **0 sorry/admit**.
**Axioms:** `#print axioms` on all 15 headlines — each exactly `[propext, Classical.choice, Quot.sound]` (standard three; nothing routes through the quarantined `ModularTime` sorry, despite that file being a transitive dependency).
**Program total:** 3,261 + 15 = **3,276 strict**.

## Origin and the pin

Jeff (2026-10-18): *"instead of an orbifold we are electro resonance field operators"* — gauntlet: *"prove it."* Priced S–M, ratified into the bench line as item 3.5. The sentence has two load-bearing clauses, and the pin gives each its theorem:

- **(I) Organisation** = the operator's fixed-point set.
- **(II) Resonance** = the system's resonance spectrum is the **gap set of its generator**.

## Verdicts per part

### Part I — Organisation (assembly + naming): STANDS

- `dephase_fixed_iff_diagonal` — for every dephasing level `l ≠ 1`, `dephase l A = A ↔ ∀ i j, i ≠ j → A i j = 0`. Assembled from `PreCompensation.dephase_apply_off`/`dephase_diag` at the entry level; the `l = 0` case restates `DecoherenceToy.pinch_eq_self_iff`.
- `dephase_fixed_iff_pinch_fixed` — at every `l ≠ 1` the family has the *same* fixed-point set as the pinching: partial forgetting erases exactly what full forgetfulness erases.
- The `l = 1` endpoint is the identity (`dephase_one`, pre-existing): everything is fixed there — the trivial endpoint, stated, not hidden.

**Operator framing (the dossier statement of Part I):** the organised (diagonal) states are the eigenvalue-1 space of the environment's channel, simultaneously at every nonzero forgetting strength. Unorganised content is not merely shrunk — at `l = 0` it is erased in one application, and at every `l ≠ 1` nothing off-diagonal is fixed.

### Part II — Resonance (new proof): STANDS, with one named narrowing

- `phaseFlow` (def, T2) — the diagonal-generator flow over a general finite index type: conjugation by the diagonal phase unitary. `phaseFlow_eq_hamiltonianFlow` — on `Fin N` it is *definitionally* `ThermalClock.hamiltonianFlow` (proved by `rfl`): the general form and the corpus object are the same flow.
- `resonanceSpectrum` (def, T2) — the gap set `{lam i − lam j}`; `gap_mem_resonanceSpectrum` — every gap is a member.
- `phaseFlow_apply` — **the phase law**: `(flow t A) i j = exp(−it(lam i − lam j)) • A i j`. Every coherence is a mode of the flow; its frequency is the gap.
- `phaseFlow_apply_eq_iff` — one entry is unmoved at *all* times iff it is a zero-gap mode or zero. The proof's key step: at `t = π/(gap)` the phase is `exp(−iπ) = −1`, which moves every nonzero entry.
- `phaseFlow_stationary_iff` — **stationarity**: fixed at all times iff supported on the equal-eigenvalue blocks.
- `phaseFlow_stationary_iff_diagonal` — under a nondegenerate (injective) generator, stationary iff diagonal.

**Named narrowing (the commission's parenthetical, corrected):** the commission stated the stationarity target as "iff A is diagonal". That is false as stated when the generator has degenerate eigenvalues: a coherence *inside* an equal-eigenvalue block has gap zero and is stationary without being diagonal. The proved theorem is the block form (`phaseFlow_stationary_iff`), and "diagonal" is recovered exactly under injectivity (`phaseFlow_stationary_iff_diagonal`). Degeneracy is not an edge case to hide — it is precisely where stationary coherences can live off the diagonal, and the theorem says where.

### Part III — The thermal instance: STANDS whole, including the β scaling

- `diagFlow_phase` — the corpus's own modular flow, entrywise: frequencies are the differences `log w_i − log w_j` of the state's weights.
- `diagFlow_eq_phaseFlow` — `diagFlow w` *is* `phaseFlow` at the eigenvalue function `j ↦ −log (w j)`: the modular flow is the phase flow of `K = −ln ρ`.
- `thermalClock_flow_eq_phaseFlow`, `thermalClock_phase` — for a packaged `ThermalClock`: `(flow s a) i j = exp(−is(K_i − K_j)) • a i j` with `K_j = −log (weights j)`. **The resonance spectrum of a state ρ is the gap set of `−ln ρ`.**
- `thermalClock_stationary_iff` — fixed by the clock at all thermal times iff entries vanish between distinct-weight levels (log-injectivity on the faithful weights).
- `gibbs_resonance_phase` — **the β scaling fell out**: for Gibbs weights, the `(i, j)` coherence rotates at `β·(lam i² − lam j²)` (via the corpus anchor `gibbs_K_eigenvalue_diff`). The thermal resonance spectrum is the laboratory D² gap set rescaled by β — `ThermalClock`'s conversion theorem (physical time = β × thermal time) restated as a frequency law.
- `gibbs_stationary_iff` — Gibbs stationarity read in the laboratory levels `β·lam²`.

## The two fixed-point theorems, side by side

| | Operator | Fixed points | Theorem |
|---|---|---|---|
| Environment | `dephase l`, any `l ≠ 1` | exactly the diagonal matrices | `dephase_fixed_iff_diagonal` |
| System itself | `phaseFlow lam`, all times | exactly the equal-eigenvalue-block matrices; the diagonal matrices iff `lam` is injective | `phaseFlow_stationary_iff`, `phaseFlow_stationary_iff_diagonal` |

Organisation = invariance under the environment's channel **and** under the system's own dynamics. In the nondegenerate case the two sets are the same set, characterised twice. That is the proved content of the pin's circle.

## Fences

- Finite level, finite index types throughout. No continuum field is constructed anywhere in this module.
- The proved core of Part II is the **diagonal generator**. A general Hermitian generator reduces to the diagonal case in its eigenbasis; that reduction is **not** formalized here (named remainder, not attempted). The thermal instance stands because the corpus's clocks are already in the eigenbasis picture.
- This module is **not** a claim that these finite operators are electromagnetism. What stands at T1 is the operator content of Jeff's sentence: fixed points = the organised set; frequencies = the generator's gap set. The EM reading of "electro resonance field operators" stays T5.
- The `diagFlow` used throughout is the eigenbasis picture of `ModularTime`/`ThermalClock`; nothing here touches the quarantined T3 `sorry` in `ModularTime.kms_identity_diagonal` (axiom lists verify this).

## Deviations and surprises

- One narrowing vs the commission text (Part II stationarity "iff diagonal"), corrected to the block form with the diagonal case recovered under injectivity — see Part II above. No other deviations.
- No mathematical surprises. One engineering note: the `t = π/(gap)` step needs the cast product `↑(π/gap) * ↑(gap)` collapsed via `ofReal_mul` after `mul_assoc`, and `exp(−(π·I)) = −1` via `Complex.exp_neg` + `Complex.exp_pi_mul_I`; both are recorded in the proof of `phaseFlow_apply_eq_iff`.
