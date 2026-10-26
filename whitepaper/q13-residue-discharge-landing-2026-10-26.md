# The Q13 Residue, Discharged — the Doubled-Link Class at General Geometry

*Landing dossier, 2026-10-26. Module:
`lean/ThetLogos/LatticeContrDoubledLink.lean` (strict 7, defs 2,
zero `sorry`, zero `native_decide`; main-tree build green, 3,534
jobs, parent-verified on the shipped text). **Parts of the Clay
Yang–Mills statement closed by this landing: 0.***

## What the residue was

Q13 (the twirl/contraction line, Pitch 4 Stage 1c-0 clause (ii))
closed standing with **one named partial**: the *evaluated*
twirl-entry form of the contraction was unasserted on the
doubled-link class at general geometry — a plaquette base site fixed
by the transverse shift, whose doubled link is also read by the other
word, where the combined fiber has cardinality 3 or 4 and the link
factor is a higher Haar moment tensor, not a pair twirl. In
`LatticeContr`, `linkContr_classify` required
`sA.card + sB.card ≤ 2`, excluding exactly the patterns (2,1), (1,2),
(2,2), and the plaquette lift carried the hypothesis `hgood`,
dischargeable only at the not-fixed seat.

## What landed

The next two J-moment tensors in the family's own entry form —
`haarTwirl3` (triple) and `haarTwirl4` (quadruple) — and the three
excluded evaluations:

- `linkContr_pair_singleton` (2,1) = the triple-twirl entry
  𝒥(M, M′, N);
- `linkContr_singleton_pair` (1,2) = 𝒥(M, N, N′);
- `linkContr_pair_pair` (2,2) = the quadruple-twirl entry
  𝒥(M, M′, N, N′).

Capstones: `linkContr_classify_general` — the link classification
with the cardinality-sum hypothesis **dropped**, all nine patterns —
and the headline **`plaqLinkContr_classify_general`**: the plaquette
classification with `hgood` dropped entirely. Every plaquette pair,
no fixed-base hypothesis, both signs, every link factor one of the
nine evaluated J values.

Axiom check on all five headlines: exactly
`[propext, Classical.choice, Quot.sound]`. The only hypotheses
removed are the two that constituted the residue; the seat data and
conventions are the Q13 family's own.

## State of the line

**Q13 now stands with no named partial.** Fences kept: this is
evaluation only — no Schur/Clebsch–Gordan expansion of the higher
tensors is built or implied; fixed finite lattice; the Stage 1c-0
clause-(ii) *assembly* (brick Q13-4: substituting the identity into
the landed link-sharing sum for κ_p, with checks C1/C2) remains its
own named brick, not part of this landing.

## Census effect

Strict 5,811 → **5,818**; attribute-inclusive 5,878 → **5,885**;
modules 191 → **192**; `sorry` placeholders unchanged at **6**.

## Backers since last landing

No new backers inscribed in this interval; the roll stands as
recorded in `BACKERS.md`. Every gift is published with the proof
stream, named as the giver wishes, amounts only with the giver's
permission — the standing reciprocity of this house.
