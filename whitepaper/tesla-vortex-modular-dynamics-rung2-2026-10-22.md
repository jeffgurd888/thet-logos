# Tesla Vortex Modular Dynamics — Rung 2: multi-sector separation and ground-sector selection (2026-10-22)

**Verdict: STANDS WHOLE (T1).** Module `ThetLogos.TeslaVortexMultiSector`
(15 strict theorems, 4 definitions, 0 sorry, standard axioms only).
Commissioned by Jeff 2026-10-22 ("both tvmd and Stokes"); charter:
`whitepaper/tesla-vortex-modular-dynamics-rung2-scoping-2026-10-22.md`.
Generalizes Rung 1 (`ThetLogos.TeslaVortexSeparation`, imported,
unmodified) from two sectors to any finite nonempty family of sectors
with INPUT energies E : ι → ℝ and INPUT charges q : ι → ℝ:
S(β) = (Σᵢ qᵢ·e^{−βEᵢ}) / (Σᵢ e^{−βEᵢ}).

## What stands

- **T1 — well-definedness and bound, stronger than chartered.**
  `sepN_denominator_pos`: the denominator is positive at every β.
  `sepN_abs_le`: |S(β)| ≤ maxᵢ |qᵢ| at **every real β** (the charter
  asked β ≥ 0; the bound is free at all β since Gibbs weights are
  positive everywhere). A weighted average of input charges lies inside
  their range.
- **T2 — infinite temperature.** `sepN_zero_beta`: S(0) = (Σᵢ qᵢ)/(card ι)
  — the flat average of the input charges.
- **T3 — ground-sector selection (headline), in full, no pin.**
  `tendsto_sepN_atTop`: as β → ∞, S(β) → (Σ_{i ∈ ground} qᵢ)/(card ground),
  where ground = {i : E i = min E}. Proved by the chartered route:
  shift by the ground energy; relative weights tend to 1 on ground
  sectors and 0 off them. At zero temperature the state selects the
  ground sectors alone — Rung 1's saturation is this selection's
  two-sector shadow.
- **T4 — two-sector recovery.** `sepN_fin_two_eq_thermalSeparation`:
  at Fin 2 with charges (+q, −q), sepN equals Rung 1's
  `thermalSeparation` exactly. The generalization welds back onto the
  brick it generalizes.
- **T5 — flux hook at N sectors (proved, with its pin on the face).**
  Over Fin n (FluxClassification's index type):
  `gibbs_flux_eq_zero_iff_sectors` — at β > 0 the modular flux at the
  N-sector Gibbs K vanishes ⟺ D has no entries across distinct
  *energy* sectors; `gibbs_flux_ne_zero_of_cross_entry` — a nonzero
  cross-sector entry switches the flux on.

## Fences (on the module's face)

- **K-TV1:** q and E are INPUTS. No charge values are derived; nothing
  here models a nucleus or an atom. The selected sectors are the input
  energies' minimizers.
- **K-TV2:** Links 2–3 of Jeff's chain are NOT modeled; T5 picture with
  standing NO-GOs.
- **K-TV3:** "Tesla Vortex" is Jeff's coinage — not Tesla's devices,
  not 3-6-9.
- **K-TV4:** Monotonicity in β is a TWO-SECTOR theorem (Rung 1). It is
  not claimed for N sectors, and no N-sector counterexample is claimed
  either.

## Verification (parent, independent of the build agent)

- Candidate md5 `7dd76c3383fe1875ec700f5c648f56e9`; shipped file md5
  `99ec48b5f92ebc11c2112cb5670f3686` (differs only by the header status
  flip at landing).
- Own comment-stripped scan: 15 strict, 0 @[simp]-attribute
  declarations, 0 sorry, 0 admit; 4 defs.
- Own `#print axioms` on all seven headlines (denominator, bound,
  β = 0, selection limit, two-sector recovery, flux iff, flux witness):
  each exactly [propext, Classical.choice, Quot.sound].
- In-tree build on the exact shipped text: `lake build
  ThetLogos.TeslaVortexMultiSector`, exit 0, 3,587 jobs, .olean present.

## Census step

Program total: **3,577 → 3,592 strict** (3,617 → 3,632
attribute-inclusive), **129 → 130 counted modules**.

NO CLAIM beyond the finite identities and the one limit above.
