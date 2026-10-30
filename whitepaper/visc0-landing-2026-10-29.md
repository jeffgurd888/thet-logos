# VISC-0 LANDING — 2026-10-29

**Verdict: FULL (registration).** New module
`ThetLogos/ViscousLine.lean` (strict 6 / defs 0) opens the
viscous line.

**NO CLAIM. Parts of any Millennium statement closed by this
landing: 0. Dials 0/4.**

## What was registered

The diagonal one-signedness pack, assembled from landed
facts (cited, not re-proved): for `lam i ≥ 0`, `t ≥ 0`, the
heat kernel's diagonal entries lie in (0, 1]
(`heatKernel_diag_mem_Ioc`, from `heatKernel_apply_diag` +
`Real.exp_pos`); the ternary step's diagonal multipliers
`exp(−2t·lam i)` lie in (0, 1]
(`ternaryStep_diag_multiplier_mem_Ioc`, read off the landed
`ternaryStep_diag`); the diagonal generator values are
one-signed (`diag_generator_nonpos`: `−lam i ≤ 0`); and the
packaging corollary — a stepped nonnegative diagonal state
keeps its entries' signs and does not grow
(`ternaryStep_diag_entry_nonneg_le`, entries read through
their real parts).

## Honest fences (on the module's face, and here)

This is a registration/formality brick and says so: its
kill K-VISC-0 (a diagonal multiplier outside (0,1]) is
vacuous by `Real.exp_pos`, so the brick's content is the
assembly and naming of owned facts, priced S. "Viscosity"
is Jeff's T5 gloss for the line's subject (one-signed
dissipation of the owned heat/ternary step); the line earns
the name only at VISC-2 with the dissipativity form
(VISC-1's generator theorem is the next brick). Finite
level only; no signature-transition vocabulary is spent
anywhere in this line. The master kill K-VISC stays armed
for the general seat (VISC-2), where amplification is a
live possibility. TTK-2 remains parked on Jeff's word —
none of its remaining components is built by this line;
VISC-1's generator theorem is the one brick the two lines
share, built here under the viscous line only.

## Verification (parent, independent, from disk)

- Parent count: strict 6, defs 0. Census after this
  landing: **7,346 strict / 7,424 attribute-inclusive /
  251 counted modules** (from 7,340 / 7,418 / 250).
- Main-tree build green (3,325 jobs). Parent axiom check
  on the packaging corollary: exactly
  `[propext, Classical.choice, Quot.sound]`.
- Parent grep: the placeholder tactic, `native_decide`,
  and the banned signature word occur 0 times in the
  module.

## Backers since last landing

No new backers recorded since the A2-1 landing (earlier
today). The backers roll in `BACKERS.md` is unchanged.
