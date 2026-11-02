# CLS-2G LANDING DOSSIER — the orbit group law: the seam closes PROVED — 2026-11-02

**Item:** CLS-2G (Lane 1 bookkeeping) — the group-law seam
named open since CLS-2b's dossier ("the orbit is classified
as a set with membership and weights; the composition law
is bookkeeping the lane has not needed"). Fired as the
registered lane-filler when both lanes stood free.

## VERDICT: PROVED IN FULL — the toggle orbit is a (ℤ/2)⁴ group action; K-CLS-2G does not fire

**Artifact:** `lean/ThetLogos/DialOneSwapOrbitGroupLaw.lean`
— strict 26, defs 4. Verified by the coordinator in the
main tree (build green); all eight headlines on exactly
`[propext, Classical.choice, Quot.sound]`. CLS-2/2b
untouched.

**The frozen form (landed vocabulary, bits `Fin 4 →
Bool`):** `bitsAdd` is pointwise xor; `toggleMap b` is
defined from `orbitRep`'s own construction — entrywise
`star`-conjugation at the diagonal seats `b` selects (bit
0: seats {8,9}; bits 1–3: {10,11}, {12,13}, {14,15} via
`swapIdx`), identity elsewhere. The law:
`toggleMap (bitsAdd b₁ b₂) = toggleMap b₁ ∘ toggleMap b₂`,
with `orbitRep b = toggleMap b pi1`. The mechanism, proved
by the 32-seat split (`toggled_bitsAdd`): the four seat
pairs are disjoint, so toggling is a symmetric difference,
never a double additive correction.

**Corollaries, all proved** (none left unclaimed):
`toggleMap_zero` (T_0 = id), `toggleMap_involutive`,
`toggleMap_bitPat_commute` (distinct bits commute, from
the general `toggleMap_comm`), `orbitRep_bitsAdd`, and
the assembled `orbit_group_action`.

**What closes:** the last named bookkeeping seam of the
Dial-1 classification. The orbit is now, at T1: a set
(membership decided, CLS-2/2b), with weights read
(CLS-2b), and a group action (this brick). Grade T stands
complete in every registered particular.

## Fences

Bookkeeping grade — no membership, weight, or exclusion
changes; CLS-2/2b stand untouched. NO CLAIM; Dial 1 = 0;
all dials 0/4.

**Census after landing: 12,592 strict / 13,087 total / 439 counted
modules; zero `sorry` terms tree-wide (certified at the
landings' headline axiom checks; the tree-wide SORRY-0
sweeps closed earlier this run).**

## Backers since last landing

None new on the record since the last landing.
