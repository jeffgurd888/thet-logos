# T-ENT landing — the tree owns entropy now (finite von Neumann, weight form)

Filed: 2026-10-31. Brick: T-ENT (M priced), the Q7CR line's entropy
brick — every entropy consequence in the line gated on this landing,
and no Q7CR dossier used entropy language in proved content before it.
Module: `ThetLogos.FiniteEntropy` (new), strict 26 / defs 5, build
green, headlines on exactly [propext, Classical.choice, Quot.sound]
(coordinator-verified: `entropyW_eq_log_card_iff`,
`entropyW_z4Weight_lt_log_four`, `tendsto_entropyW_z4Weight`).

**NO CLAIM** is made by this landing. Parts closed: 0 on every board.
All four dials stand at **0/4**. Sibling discipline on the face: SE's
continuous differential entropy (`DiffEntropy`) is a different object
in a different line — not imported, not cited; neither gates the other.

## What landed (FULL on every item; no PARTIAL used)

- **The definition.** `entropyW w := −∑ i, w i * Real.log (w i)` over a
  finite index, log base e, with `IsProbWeight` registered; the
  0·log 0 convention is Mathlib's `Real.log 0 = 0`, stated as a lemma.
- **Bounds with saturation, BOTH directions:** `entropyW_nonneg`;
  `entropyW_le_log_card`; `entropyW_eq_log_card_iff` — equality holds
  iff the weight is maximally mixed. (The pack's PARTIAL authorization
  at the (⇒) clause was not needed.) Route, named: the Gibbs route —
  pointwise `log t ≤ t − 1` summed against the weights, with its strict
  companion for saturation. No Jensen lemma was used; no analysis fact
  the brick needed is absent from the pin.
- **Pure weights, both directions:** `entropyW_eq_zero_iff` — entropy
  zero iff the weight is a basis weight.
- **Invariance:** relabeling by equivalence and by permutation
  (`entropyW_comp_equiv`, `entropyW_comp_perm`), with the named Gibbs
  instance (any rung permutation of the Z4 Gibbs weights, incl. the
  cyclic shift) — the modular-flow invariance in weight form.
- **Density/list form:** `entropyD` defined AS `entropyW` of the
  weights; `entropyOfList` over eigenvalue lists, proved equal to
  `entropyW` of the Fin-indexed weight function. Basis-independence
  beyond the list is explicitly NOT claimed.
- **The Gibbs instance, complete:** `entropyW (z4Weight 0) = log 4`;
  the closed form `entropyW (z4Weight β) = log (z4Partition β) + β·(mean
  energy)`; the LIMIT `Tendsto (entropyW ∘ z4Weight) (𝓝 0) (𝓝 (log 4))`;
  and the strict clause `entropyW (z4Weight β) < log 4` for β > 0.

The trifecta tests (T-Q7-1 first) and the LOOP chain are unblocked:
their entropy consequences may now be stated against an owned
definition.

## Backers since last landing

The backer roll is unchanged since the previous landing. Backers are named
in `BACKERS.md` exactly as each wishes to be named, only after Jeff
confirms a gift arrived; amounts only with the giver's permission.

Census after this landing: 8,835 strict / 8,913 attribute-inclusive /
300 modules (parent-verified from disk; README badge and body updated and
grep-verified in the committed blob).
