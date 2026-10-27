# D1-A — KILLED: The Forcing Claim Is False at the Landed Condition Set (K-D1A-1)

*Landing dossier, 2026-10-27. Module:
`lean/ThetLogos/HyperchargeForcing.lean` (strict 61,
defs 2; zero placeholders, zero `native_decide`;
main-tree build green, 3,133 jobs, parent-verified;
headline axiom sets exactly `[propext,
Classical.choice, Quot.sound]`). **Parts of the Clay
Yang–Mills statement closed by this landing: 0.
Dial 1 does not move.** This dossier leads with the
kill, at the same volume as any win: the Dial-1
scoping's sharpest near-miss — that the U(1) weight
pattern 3·Y_f might be FORCED by the corpus's landed
condition set rather than entered as a table — is
**refuted**, permanently, at that condition set, by a
machine-checked counterexample. Kill condition
K-D1A-1 fired exactly as pre-registered.*

## The counterexample

`piFlip` is π₁ with exactly one seat changed: the
right-handed-neutrino seat (slot 8) acts by
`star a.u1` where π₁ acts by `a.u1`. It is built from
π₁, `star`, and a matrix unit alone — the hypercharge
table and every Yukawa value appear nowhere upstream
(K-D1A-2 never approached; the flipped direction was
deliberately left unfixed in the hypotheses, avoiding
the K-D1A-3 trap). Every clause of the registered
condition set is discharged in Lean: the
representation laws, faithfulness, grading,
**order-zero**, **first-order with the Yukawas
universally quantified**, and **unimodularity** —
along the direction (−2, 1), where `piFlip`'s
determinant generator is exp((−6α − 12β)ti) against
π₁'s (−4α − 12β).

And the conclusion fails: along (−2, 1) the lifted
ν_R eigenvalue is exp(4ti) — weight **4** — while
3·Y_νR = 0; at t = π/4 it is −1, proportional to the
table's value for **no** κ (`piFlip_weights_not_
proportional`; headline `dial1_forcing_killed`).

## The mechanism (why the seat was free)

First-order's teeth are exactly the antiparticle
agreement ties — the conditions that bind a particle
seat to its antiparticle mirror. The right-handed
*particle* seats (ν_R, e_R, quark_R) have **none**.
The flipped seat's commutator differs from π₁'s only
at (0,8) and (8,0), those units commute with ρ₁ for
the landed reason (ρ₁ b agrees at (0,0) and (8,8)),
and the row/column that could have caught it
vanishes. So the condition set, as landed, simply
does not hold the ν_R seat's hand — and a condition
set that cannot see a flip cannot force the
unflipped value.

## Consequences, at fence strength

- **D1-B does not fire.** Its gate was a landed
  forcing theorem; there are no forced weights to
  consume. It stays gated, permanently on this route.
- Any strengthened condition set — e., a clause tying
  particle seats to their antiparticle seats — is a
  **new entry** under the relabeling rule. It is not
  a rescue of D1-A, and D1-A's kill stands beside any
  future attempt at full rank.
- Dial 1's state after a full day's honest work:
  eighteen candidates traced and killed in scoping;
  the nineteenth — the strongest, the forcing route —
  attempted in Lean and killed by counterexample.
  The dial reads **0**, and now the *reason* is
  theorem-grade: what would have to change is named
  (a seat-tying clause the corpus does not currently
  impose), and whether nature's condition set imposes
  it is a question this landing sharpens without
  answering. NO CLAIM; dials 0/4.

## Census effect

Strict 6,506 → **6,567**; attribute-inclusive 6,584 →
**6,645**; modules 226 → **227**; placeholders unchanged
at **7**.

## Backers since last landing

No new backers inscribed in this interval; the roll stands
as recorded in `BACKERS.md`. Every gift is published with
the proof stream, named as the giver wishes, amounts only
with the giver's permission — the standing reciprocity of
this house.
