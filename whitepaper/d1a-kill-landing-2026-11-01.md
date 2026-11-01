# D1-A′ KILL DOSSIER — K-D1A′-1 FIRES (gauntlet stage 2, the pre-check gate) — 2026-11-01

**Item:** D1-A′, the ranked first brick of the Dial-1 scoping
pass, fired by Jeff's order 2026-11-01 14:59 EST. Stage 1 (the
pin, with Step 0's COMMON HYPERCHARGE MATRIX and commonality
proved) landed on its own commit. This is stage 2, the
pre-check gate.

**VERDICT: K-D1A′-1 FIRES by piFlip at the strengthened set.
K-D1A′-2's vacuity prong is proved alongside. K-D1A′-3 does not
fire. The gauntlet STOPS at the gate, per the fire order.
`DialOneForcing` is REFUTED — `¬ DialOneForcing` is a theorem.
D1-A′ is dead at the strengthened set, permanently, under its
pre-registered kills. Dial 1 stays 0.**

**Artifact:** `lean/ThetLogos/DialOneSeatTieChecks.lean` —
strict 10, defs 0. Verified by the coordinator in the main tree
(build green, 3135 jobs); all seven headlines on exactly
`[propext, Classical.choice, Quot.sound]`.

## The mechanism, exactly

The core lemma `lifted_diag_partner`: for EVERY matrix M and
every seat s, `(M * piOp M) s s = (M * piOp M) (partner s)
(partner s)` — both sides are the same sum up to reindexing by
the partner involution and commuting each product. The seat tie
was stated (by the pin, faithfully, in the only π-general
lift-weight form the landed forcing vocabulary owns) as equality
of exactly those diagonal entries. Therefore:

- **`SeatTie π` holds for every π** (`seatTie_universal`). The
  tie is a symmetry of the J-opposite construction itself, not a
  condition on representations.
- Pre-check (i): `SeatTie pi1` HOLDS — by the π-independent
  symmetry, no specifics of π₁ used. **K-D1A′-3 does not fire**
  (π₁ is not excluded; it was never at risk).
- Pre-check (ii): `SeatTie piFlip` HOLDS, by the same symmetry.
  The gate's required failure does not occur.
- piFlip also satisfies the base set (`dialOneBase_piFlip`,
  assembled from the landed piFlip theorems, unimodular
  direction (−2, 1)). Hence `DialOneStrengthened piFlip`.
- The forcing conclusion fails for piFlip
  (`piFlip_forcing_conclusion_fails`): at direction (−2, 1),
  seat ν_R, t = π/4, piFlip's lifted eigenvalue is exactly **−1**,
  while the COMMON HYPERCHARGE MATRIX entry at ν_R is 0, which
  would force `exp(κ·t·0·I) = 1` for every κ. Contradiction —
  hence `kD1A1_fires_by_piFlip : ¬ DialOneForcing`.
- `kD1A2_vacuity_reading : ∀ π, SeatTie π` records the K-D1A′-2
  prong in theorem form: a tie every π satisfies constrains
  nothing and fixes no seat's weight.

## What this kill is, at full rank

D1-A died because first-order's teeth (the antiparticle
agreement ties) do not reach the right-handed particle seats.
D1-A′ proposed to supply the missing tie by hand — mirror
equality of lifted weights. The gauntlet's pre-checks show the
proposed tie, in the form the landed vocabulary can state it,
is **already a theorem about the J-opposite construction for
every representation**: it holds of piFlip exactly as it holds
of π₁, so it cannot discriminate them, and the known
counterexample walks through the strengthened gate unchanged
(ν_R lifted eigenvalue −1 at the test point against the matrix's
0). The door the scoping named is closed — not by a missing
proof effort, but by a proved symmetry. Per the fire order, the
tie is NOT re-posed inside this entry; any differently-posed
tie is a NEW entry under the relabeling rule, behind a fresh
scoping that must first explain how its statement escapes the
`lifted_diag_partner` symmetry. D1-B remains gated behind a
forcing theorem (none has landed; this kill changes nothing
there).

**What survives of the gauntlet:** Step 0 stands untouched —
the COMMON HYPERCHARGE MATRIX is a pinned named object and its
commonality (the three-generation weight operator is its
triplication) is a proved corpus fact. The kill is about the
tie, not the matrix.

## Fences

NO CLAIM — no Millennium problem is claimed solved or advanced.
This kill is reported at the same volume as a landing would
have been (Jeff's verdict directive; the Wrong-at-Bats
doctrine). **Dial 1: 0. All dials: 0/4.**

**Census after landing: 11,067 strict / 11,253 total / 378 counted
modules; zero `sorry` terms tree-wide.**

## Backers since last landing

None new on the record since the last landing.
