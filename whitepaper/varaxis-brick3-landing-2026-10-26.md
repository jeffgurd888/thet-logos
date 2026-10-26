# Variable-Axis Brick 3 — Honest Time-Varying Moments

*Landing dossier, 2026-10-26. Module:
`lean/ThetLogos/SolidBodyVarMoments.lean` (strict 10,
attribute-inclusive 18, defs 6 + 1 structure, zero `sorry`, zero
`native_decide`; main-tree build green, 3,229 jobs,
parent-verified on the shipped text). Scoped in
routeb-general-scratch/varaxis-scoping-2026-10-26 §C. **Parts of
the Clay Yang–Mills statement closed by this landing: 0.**
Classical mechanics, abstract body only.*

## What landed

The narrow honest model: `VarBody` — principal axes fixed in the
body, moments prescribed differentiable functions `Iᵢ(t) > 0` — and
the corrected field `eulerRHSCorr`: the frozen `eulerRHS` at the
instantaneous body, minus `(İᵢ/Iᵢ)·ωᵢ`. Four derivative laws, in
the foundation's `hasDerivAt` pattern:

- **Corrected model, energy:** `dT/dt = −½ Σ İᵢωᵢ²` — rotational
  energy is *not* conserved; the missing power is exactly the work
  exchanged with whatever process prescribes the changing inertia.
- **Corrected model, momentum:** `d|L|²/dt = 0` — body-frame
  `|L|²` survives, proved by the *new* chain-rule calculation (the
  drift term `İᵢωᵢ` cancels the correction exactly). The
  foundation's `angMomSq_const` is nowhere cited: its proof omits
  the `İ` terms and does not transfer.
- **Postulated model (the contrast):** under the naive
  `ω̇ = eulerRHS(I(t), ω)` with no correction,
  `dT/dt = +½ Σ İᵢωᵢ²` (opposite sign) and
  `d|L|²/dt = 2 Σ Iᵢİᵢωᵢ²` — neither frozen law transfers.

Axiom sets on the headlines: exactly
`[propext, Classical.choice, Quot.sound]`.

## Fences

Axes fixed in the body; no products of inertia; no mass flux.
Rotating principal axes or mass leaving the body need more than
`İ` and are **outside this model**, stated on its face. With
Bricks 1–3 landed, the variable-axis program's buildable content
is complete; what remains is only the L+ nonlinear separatrix
period (elliptic-integral machinery the pin does not carry) and
the min-axis mirror seat, named in the scoping as unbuilt.

## Census effect

Strict 5,912 → **5,922**; attribute-inclusive 5,982 → **6,000**;
modules 197 → **198**; `sorry` placeholders unchanged at **6**.

## Backers since last landing

No new backers inscribed in this interval; the roll stands as
recorded in `BACKERS.md`. Every gift is published with the proof
stream, named as the giver wishes, amounts only with the giver's
permission — the standing reciprocity of this house.
