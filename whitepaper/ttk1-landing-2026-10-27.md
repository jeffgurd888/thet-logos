# Ternary Thermal Kernel Dynamics, Brick 1 — the Kernel Gets Its Update Rule

*Landing dossier, 2026-10-27. Module:
`lean/ThetLogos/TernaryThermalDynamics.lean`
(strict 20, defs 2; zero placeholders, zero
`native_decide`; main-tree build green, 3,584 jobs,
parent-verified; headline axiom sets exactly
`[propext, Classical.choice, Quot.sound]`). **Parts
of the Clay Yang–Mills statement closed by this
landing: 0.** Jeff's fragment "Ternary Thermal
Kernel dynamics" — reading confirmed by Jeff
2026-10-27 (the ternary operation as the
ThermalKernel's update rule over time), scoped the
same day, built the same day. The kernel, which
owned a semigroup law in t but no action on states,
now has its update rule — at the finite diagonal
seat, in owned vocabulary only.*

## What landed

Two definitions: `heatKernelC`, the complex cast of
the heat kernel (the one bridge the ℝ/ℂ type seam
required, named in the scoping as missing and built
here), and `ternaryStep lam t X = K_t Xᴴ K_t` — the
ternary product with the kernel on both outer seats.

- **Ternary closure.** The kernel family is closed
  under the ternary product with times adding:
  ⟨K_s, K_t, K_u⟩ = K_{s+t+u}; with middle argument
  `1` the semigroup law `heatKernel_add` is
  recovered as a ternary law.
- **The clock's state curve.** For a ThermalClock
  C, the complex kernel at rates −log w is the
  diagonal of the weights' real powers w^t — the
  jewel e^{−K} = ρ restated in ℂ form, with t = 0
  the identity.
- **Relaxation.** A diagonal state moves entrywise,
  w i ↦ exp(−2t·λ i)·w i. The trace is accounted,
  not preserved: it is the sum of the relaxed
  weights, ≤ 1, with equality iff the support lies
  on zero-rate modes.
- **Fixed points (the centerpiece).** For t > 0, a
  diagonal state is fixed by the step **iff every
  occupied mode has rate zero** — everything else
  relaxes to the ground line. Pre-registered kill
  K-TTK-2 resolved in favor of the relaxation
  reading; K-TTK-1 did not fire (closure holds at
  the cast); K-TTK-3 honored (no trace- or
  payoff-preservation claim is stated for the raw
  step — the scoping's two-mode computation kills
  any such claim).

## One correction, on the record

The step at t = 0 is `Xᴴ`, not `X`: `ternaryMat`
conjugates its middle argument and K_0 = 1. It is
stated honestly as `ternaryStep_zero` — the identity
on Hermitian inputs — rather than dressed as a unit
law. On the diagonal seat (real weights) the
distinction is invisible; at the general seat it is
the truth.

## Fences

Finite, diagonal, corpus-internal. The step is
dissipative where the modular flow `diagFlow` is
automorphic: no raw ternary step preserves KMS, and
nothing here identifies the two — the scoping's
negative stands. "Dynamics" means exactly the maps
above; Jeff's reading is the T5 gloss in the module
prose. NO CLAIM; dials 0/4, unchanged — this brick
computes no measured number and proves no limit
theorem.

Census effect: 6,779 → **6,799 strict** /
6,857 → **6,877 attribute-inclusive** / 232 → **233
modules**; the seven quarantined placeholders are
unchanged.

Brick 2, as scoped (not fired): the normalized step
(fixed points exactly the states inside a single
λ-level), the generator theorem, and a KMS-failure
quantification against `kms_identity_diagonal`.

## Backers since last landing

No new backers inscribed in this interval; the roll
stands as recorded in `BACKERS.md`. Every gift is
published with the proof stream, named as the giver
wishes, amounts only with the giver's permission —
the standing reciprocity of this house.
