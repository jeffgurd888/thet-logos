# (H-PF) at the U(1) Seat — the Averaged Kernel's Pairing Is Nonnegative

*Landing dossier, 2026-10-26. Module:
`lean/ThetLogos/PlaneAvgKernelCircle.lean` (strict 2, defs 0, zero
`sorry`, zero `native_decide`; main-tree build green, 3,441 jobs,
parent-verified on the shipped text). **Parts of the Clay
Yang–Mills statement closed by this landing: 0.***

## What landed

- **`osForm_circle_nonneg_aestrongly`** — Route C's U(1) positivity
  replayed at the relaxed domain: `f` AEStronglyMeasurable and
  bounded, in place of Continuous. (Route C's proof consumed `f`
  only through measurability and the two marginals, which already
  quantify over arbitrary `f` — the relaxation is a true replay, not
  a new argument.)
- **`planeAvgKernel_circle_pairing_nonneg`** — at the U(1) seat
  (haarProb Circle, circleRep, d = 1), for even N, β ≥ 0, and
  bounded AE-strongly-measurable `f`, the plane-averaged kernel's
  pairing is a **nonnegative real**. Proof: the reduction identity
  specialized to the seat, times the positive partition scalar.

Both theorems' axiom sets: exactly
`[propext, Classical.choice, Quot.sound]`.

## What this means, in the (H-PF) ledger

The scoping's chain holds end to end: at the U(1) seat, (H-PF) for
the plane-averaged kernel is a **corollary of work already owned**
— Route C's positivity, transported losslessly through the
reduction identity. The diagonal suffices because `planeAvgKernel`'s
conjugate symmetry makes the pairing a sesquilinear form, whose
positivity is its diagonal condition.

**Unchanged, at full volume:** at general (G, ρ), (H-PF) for K̄ is
the *same wall, losslessly re-encoded* (the scoping memo's verdict,
hpf-kbar-scoping-2026-10-26). K̄'s positivity is equivalent to
`osForm` positivity on strict-half observables; the sign lives
entirely in the crossing marginal, and no owned mechanism supplies
it at general geometry. That target stays L+/open, with the five
closures standing around it.

## Census effect

Strict 5,868 → **5,870**; attribute-inclusive 5,935 → **5,937**;
modules 193 → **194**; `sorry` placeholders unchanged at **6**.

## Backers since last landing

No new backers inscribed in this interval; the roll stands as
recorded in `BACKERS.md`. Every gift is published with the proof
stream, named as the giver wishes, amounts only with the giver's
permission — the standing reciprocity of this house.
