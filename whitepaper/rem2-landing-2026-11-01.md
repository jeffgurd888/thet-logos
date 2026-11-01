# REM-2 LANDING — 2026-11-01

## The corrected closure characterization: FULL (working label: REM line)

**Module:** `ThetLogos.LayerCubeRemainderClosure` —
strict 23 / defs 3, parent-verified (independent count,
main-tree build, headline axiom checks on exactly
`[propext, Classical.choice, Quot.sound]`).

**Census at this landing: 10,491 strict / 10,568 total /
357 modules, zero sorrys.**

Headline: `remClosure_proved (hN : Even N) : RemClosure N`
— the REM-0 pin's corrected closure Prop, discharged at
general even N **in its exact registered form** (the
conservative all-base-sites wrap quantifier intact;
nothing narrowed — K-GR-STAB did not fire). In the pin's
registered words (`remClosure_iff`): for every link-angle
field θ,

**(flat at every plaquette) ∧ (all three wrap holonomies
vanish at every base site) ⟺ θ = gaugeAngle φ for some
site potential φ.**

## The proof's shape

- **⟹ by path integration.** `remPotential` sums θ along
  the 1-, 2-, then 3-coordinate runs from the root
  (`potential_increment`, dispatched to
  `potential_incr1/2/3`: the potential grows by exactly
  the traversed link's value, in every spatial direction).
  Plaquette swaps telescope the cross-run changes
  (`stepSum_shift_base`, `stepSum_iterate_base`, from
  `flat_swap` — the flatness relation read through the
  edge definitions), and each wrap case reduces to a
  partial wrap sum closed by the vanishing wrap holonomy
  at the wrapped site (`stepSum_eq_neg_of_wrap`). Flatness
  is spent exactly on plaquette independence; the vanishing
  wraps exactly on cycle independence — the two halves of
  the remainder are the two obstructions, and both are
  necessary, as REM-1's kill already showed for the wraps.
- **⟸ from landed material.** MAX-2's `maxwellM3_proved`
  (gauge modes are flat) and REM-1's
  `wrapHolonomy_gaugeAngle` (a gradient's wraps telescope
  to zero).
- **Honest note, on the record:** the argument needs no
  evenness beyond the registered hypothesis — `Even N` is
  carried exactly as the pin and pack registered it and is
  not load-bearing in the proof. The registration stands
  as written; the stronger fact is noted here, not
  silently substituted into the statement.

## What this completes

The REM line's arc: Jeff's seeing asked where balance
fails to close. The answer is now a theorem with both
ends proved. A configuration's failure to be pure gauge
is *exactly* the pair the pin registered — its
plaquette-defect field (the local remainder) and its
three wrap holonomies (the global remainder). The naive
form ("flat ⟹ pure gauge") is dead (REM-1, at theorem
grade); the corrected form is true (this landing). The
remainder is not a metaphor for the obstruction — it is
the obstruction, characterized.

**Fences:** K-REM-MERGE respected (zero occurrences of
the fenced signature vocabulary in the module — Jeff's
opposition sign was never spent as a signature sign);
K-REM-SMUG/K-GR-LAUNDER bind the reading: this is finite
combinatorics on the owned cube — a discrete Hodge-shaped
determination at this seat — not a gravity, field-equation,
or continuum statement. Dial 2 = 0; NO CLAIM; dials 0/4.

With REM-2 landed, the REM line is COMPLETE (REM-0 pin,
REM-1 kill, REM-2 characterization). The gravity-vocabulary
program's remaining bricks: GEO-2 (in build), PROP-2 and
PROP-3 (behind MAX-3, in build), PROP-4 (optional, not
fired).

## Backers since last landing

The backer roll (`BACKERS.md`) is unchanged since the last
landing; no new confirmed gift is on the record. Thank you
to everyone reading the stream — the corpus is free for
everyone, forever.

*End of dossier.*
