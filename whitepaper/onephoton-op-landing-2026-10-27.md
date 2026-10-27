# OP-0 + OP-1 — The One-Photon Line: The Photon Is the Unique Massless Direction (Under the Hypothesis the Algebra Demands)

*Landing dossier, 2026-10-27. Modules:
`lean/ThetLogos/OnePhotonPost.lean` (OP-0: strict 0,
defs 3) and `lean/ThetLogos/PhotonUniqueMassless.lean`
(OP-1: strict 6, defs 0); zero placeholders, zero
`native_decide` in either; main-tree builds green,
parent-verified. **Parts of the Clay Yang–Mills
statement closed by this landing: 0.** OP-0 landed FULL
as priced. OP-1 landed PARTIAL by its pre-named seam:
the exactness is FULL and stronger than priced; the
priced uniqueness hypothesis set was KILLED by a proved
counterexample (kill condition K1 fired), and uniqueness
landed under the corrected hypothesis. The correction
is on the module's face. And the standing fence: this
is a **photon object — Dial 2 stays 0; the gravity
chair stays empty.***

## OP-1: what is proved

- **Exactness, at minimal hypotheses.**
  `higgsMassQuad_eq_zero_iff` — under v ≠ 0 *alone*, the
  zero set of the Higgs mass form is exactly
  g·W¹ = 0 ∧ g·W² = 0 ∧ g·W³ = g′·B. This was the
  un-owned field-side piece the scoping identified; the
  corpus owned the decomposition and the generator-side
  statements, and no zero-set characterization existed
  (K2 checked by grep: did not fire).
- **Neutral sector as priced.**
  `higgsMassQuad_neutral_eq_zero_iff` — under the
  scoping's exact hypotheses (v ≠ 0, (g,g′) ≠ (0,0)),
  the neutral form vanishes exactly on (W³, B) ∝ (g′, g)
  — the photon line.
- **The kill that fired.**
  `higgsMassQuad_charged_massless_of_g_eq_zero` — at
  g = 0, *every charged direction is massless* (proved;
  witness (g,g′,v) = (0,1,1), direction (1,0,0,0)).
  Physically honest — g = 0 switches the SU(2) coupling
  off — but it refutes uniqueness under the scoping's
  literal hypothesis set. K1 fired exactly as pre-named.
- **Uniqueness, under the corrected hypothesis.**
  `photon_unique_massless_direction` — under v ≠ 0 ∧
  g ≠ 0, the mass form vanishes exactly on the photon
  line, and the line is attained. With landed
  `higgs_stabilizer_is_Q`, the sharpened question R3′ —
  *within the finite assembly, the photon is the unique
  massless gauge direction* — is **closed inside the
  assembly**. Degenerate honesty included:
  `higgsMassQuad_v_eq_zero` (v = 0 ⇒ form ≡ 0).
  Axiom sets exactly `[propext, Classical.choice,
  Quot.sound]` throughout.

The hypothesis change (adding g ≠ 0) is reported as a
verdict change on the scoping memo, per house rule:
derivations outrank memos, and hypotheses are never
strengthened silently to rescue a claim.

## OP-0: the post

Defs-only, on the Q7DFTPost convention: the R3′ question
in its corrected form; the Wheeler one-photon reading
recorded as KILLED with its three obstructions (O1 the
own-antiparticle tautology, O2 the null path, O3
non-conserved photon number); R2 marked true-and-
standard, R3 marked T5 doctrine; Jeff's coinage ("one
photon theory") and his filed line — the phrase is the
room's door, not its furniture — on its face; and the
fence that a photon object is not a gravity object.

## Census effect

Strict 6,444 → **6,450**; attribute-inclusive 6,522 →
**6,528**; modules 220 → **222**; placeholders unchanged
at **7** (all T5 question-posts by design).

## Backers since last landing

No new backers inscribed in this interval; the roll stands
as recorded in `BACKERS.md`. Every gift is published with
the proof stream, named as the giver wishes, amounts only
with the giver's permission — the standing reciprocity of
this house.
