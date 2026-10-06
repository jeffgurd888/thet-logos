# Gauntlet Report — ACMD Formalization Targets (2026-10-06)

**Source:** Section II of `whitepaper/acmd-next-phase-CORRECTED-2026-10-06.md`.
**Rule:** each target either falls (zero sorrys, axiom footprint within
`propext`/`Classical.choice`/`Quot.sound`) or gets a precise obstruction.
**Build root:** `~/workspace/thet-logos/lean`, verified with `lake build`.
**Notation:** φ (lowercase) for flux throughout. No Φ-for-flux anywhere.

---

## Target 1 — Driver commutant characterization: PROVED ✓

**Theorems:**
- `ThetLogos.modularFlux_gaugeCovariant` — for unitary `U` with `U * G = G * U`:
  `U * modularFlux G D * Uᴴ = modularFlux G (U * D * Uᴴ)`.
  The commutant constraint supplies `hcomm` for gauge unitaries.
- `ThetLogos.modularFlux_trace_gaugeInvariant` — corollary:
  `trace (modularFlux G (U * D * Uᴴ)) = trace (modularFlux G D)`.
  The flux trace is gauge-invariant.

**Axiom footprints** (`#print axioms`, build-verified):
- `modularFlux_gaugeCovariant`: `[propext, Classical.choice, Quot.sound]`
- `modularFlux_trace_gaugeInvariant`: `[propext, Classical.choice, Quot.sound]`

**Location:** merged into `lean/ThetLogos/ModularFlux.lean` (build-verified,
3239 jobs). Temp modules `GauntletT1.lean`/`GauntletT2.lean` removed after merge.

**Caveat:** the build replays `ModularTime.lean` with a pre-existing warning —
`ModularTime.lean:201:8: declaration uses 'sorry'`. That sorry lives in the
imported module and predates this work; none of the new theorems depend on it
(their footprints are clean).

**Scoping note (honest):** the gauge group `U(A_F)` itself is not formalized —
the codebase represents `A_F = ℂ ⊕ ℍ ⊕ M₃(ℂ)` only via the 12 explicit
generator matrices `smGen : Fin 12 → Matrix I32 I32 ℂ` (`MartinettiRep.lean`).
The theorem is therefore stated abstractly: *any* unitary commuting with `G`
covariantizes the flux. The bridge "∀g, [G, smGen g] = 0 ⟹ [U, G] = 0 for
gauge unitaries U" requires formalizing the gauge group (via exponentials or
the universal property) — named as future work, not a blocker.

---

## Target 2 — Inter-sectoral driver construction: PROVED ✓

**Theorems** (merged into `lean/ThetLogos/ModularFlux.lean`):
- `ThetLogos.interSectoralDriver` — def: `fromBlocks 0 1 0 0` over
  `Fin m ⊕ Fin m` (single-parameter square version; the two-parameter form
  does not elaborate since rectangular matrices have no `1` — recorded in
  the def's doc comment).
- `ThetLogos.interSectoralDriver_offdiag` — the (1,2)-block is entrywise
  nonzero across the bipartition.
- `ThetLogos.interSectoral_flux_nonzero` — for `D = fromBlocks 0 M Mᴴ 0`,
  `M ≠ 0`: `Complex.I • (G * D - D * G) ≠ 0`. Block arithmetic:
  `[G,D] = fromBlocks Mᴴ 0 0 (-Mᴴ)`; nonzero entry extracted from `M`
  following the `exists_activeDriver` pattern.

**Axiom footprints** (`#print axioms`, build-verified on merged file):
- `interSectoralDriver_offdiag`: `[propext, Classical.choice, Quot.sound]`
- `interSectoral_flux_nonzero`: `[propext, Classical.choice, Quot.sound]`

---

## Target 3 — φ_act trace identities: PROVED ✓

**File:** `lean/ThetLogos/ActiveFlux.lean` (new, builds clean).

**Theorems:**
- `ThetLogos.trace_fromBlocks` — `trace (fromBlocks A B C D) = trace A + trace D`.
- `ThetLogos.commutator_fromBlocks` — `[G,D]` of block matrices, in explicit
  block components.
- `ThetLogos.trace_blockSq` — `trace (C^2) = trace(C₁₁·C₁₁) + trace(C₂₂·C₂₂)
  + 2·trace(C₁₂·C₂₁)` via cyclicity of trace.
- `ThetLogos.trace_fluxSq_block` (main) — `Tr(φ_act²) = -(Tr(C₁₁²) + Tr(C₂₂²)
  + 2·Tr(C₁₂·C₂₁))` with the `Cᵢⱼ` the commutator blocks; the overall sign
  from `i² = -1`.

**Axiom footprints** (`#print axioms`, build-verified): all four
`[propext, Classical.choice, Quot.sound]`. Zero sorrys.

---

## Target 4 — Spectral-action flux coupling: NOT ATTEMPTED (Tier 4 numerical)

Per the whitepaper: numerical exploration, not proof. Out of scope for the
Lean gauntlet by design.

---

## Explicit non-targets (not attempted, per standing kill list)

No mass floors, no `w(z)` drift, no Higgs shifts, no continuum limit, no
Yang–Mills gap claim. The struck sections stay struck.

---

## Merge checklist (for parent agent)

- [x] Merged `GauntletT1.lean` theorems into `ModularFlux.lean`; temp file deleted.
- [x] Merged `GauntletT2.lean` defs/theorems into `ModularFlux.lean`; temp file deleted.
- [x] `ActiveFlux.lean` is a permanent new module (kept).
- [x] `lake build ThetLogos.ModularFlux` and `lake build ThetLogos.ActiveFlux` green;
      no new axioms, no sorrys in new code. No other module imports
      `ModularFlux`, so nothing downstream is affected.
- [ ] Commit locally (do NOT push without Jeff's explicit approval).
