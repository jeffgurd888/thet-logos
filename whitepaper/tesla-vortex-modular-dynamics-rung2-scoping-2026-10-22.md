# Tesla Vortex Modular Dynamics — Rung 2 scoping (2026-10-22)

**Commission:** Jeff, 2026-10-22 17:45 EDT — "both tvmd and Stokes" (both
Rung 2s launched together; builds sequenced one heavy build at a time).
Rung 1 stands whole (18 T1; dossier
`tesla-vortex-modular-dynamics-rung1-2026-10-22.md`). This rung generalizes
Rung 1's link 1 only — the same fences bind, plus one new one.

## Scope — multi-sector separation and ground-sector selection

Finite house style. A finite nonempty family of sectors indexed by ι, with
INPUT energies E : ι → ℝ and INPUT charges q : ι → ℝ, at inverse
temperature β ≥ 0. Separation := the Gibbs expectation of the charge,

S(β) = (Σᵢ qᵢ·e^{−βEᵢ}) / (Σᵢ e^{−βEᵢ}).

Targets:

1. **Well-definedness and bound** — the denominator is positive, and
   |S(β)| ≤ maxᵢ |qᵢ| for all β ≥ 0 (a weighted average of input charges
   lies inside their range).
2. **Infinite temperature** — S(0) = (Σᵢ qᵢ) / (card ι): the flat average.
3. **Ground-sector selection (β → ∞)** — S(β) tends to the average of the
   charges over the ground sectors alone:
   (Σ_{i : Eᵢ = min E} qᵢ) / (card {i : Eᵢ = min E}).
   The zero-temperature state selects the ground sectors; every excited
   sector's weight dies. (Rung 1's saturation is the two-sector shadow of
   this selection.)
4. **Two-sector recovery** — for ι = Fin 2 with charges (+q, −q), S(β)
   equals Rung 1's `thermalSeparation q E β` exactly: the generalization
   welds back onto the brick it generalizes.
5. **Flux hook, restated at N sectors** — only if it comes cheaply from
   FluxClassification's general form; otherwise explicitly deferred, not
   pinned.

## Fences

- **K-TV1 (carried):** q and the energies are INPUTS. No charge values are
  derived; nothing here models a nucleus or an atom.
- **K-TV2 (carried):** Links 2–3 of Jeff's chain are NOT modeled; they
  stand as T5 picture with standing NO-GOs where the record holds them.
- **K-TV3 (carried):** "Tesla Vortex" is Jeff's coinage — not Tesla's
  devices, not 3-6-9.
- **K-TV4 (new):** Monotonicity in β is a TWO-SECTOR theorem (Rung 1).
  It is not claimed for N sectors, and no N-sector counterexample is
  claimed either — the property is simply not on this rung's face.

## Status

NO CLAIM beyond the finite identities above. Priced M. Landing follows the
house protocol (parent verification, dossier, README + counts refresh,
commit/push, LinkedIn conveyor, memory).
