# CLS-0 LANDING DOSSIER — 2026-11-01

**Item:** CLS-0 (Dial-1 classification lane, ranked first in
the next-rotation scoping) — the classification registration
pin. COMPLETE as a pin; it asserts no classification result.

## VERDICT: PIN LANDED — the classification question is frozen in three grades, never to be conflated

**Artifact:** `lean/ThetLogos/DialOneClassificationPin.lean` —
strict 6, defs 6 (in bands). Verified by the coordinator in
the main tree (build green, 3141 jobs); read-back headlines
are `rfl`-grade by construction.

**Grade W — weight realizability.** `weightAt π v` reuses the
landed lifted-eigenvalue vocabulary verbatim: ∃ primitive
(α, β), determinant 1 along the family, and the per-seat
character equation `(π (u1Gen…) * piOp (π (u1Gen…))) s s =
exp (v s · t · i)` — defined for EVERY π, no hypothesis on π.
`commonWeightVector` is the common hypercharge matrix's
lifted diagonal in ℤ (`W i + W (partner i)`; fermion-seat
entries 3·Y_f by the landed diagonal theorem). The open
question is pinned as
`WeightQuestionW := ∃ π, DialOneStrengthenedFam π ∧ π ≠ pi1 ∧
weightAt π commonWeightVector` — asserted neither way; π₁ is
noted on the face as the trivial point.

**Grade T — toggle-orbit.** Pinned in record form
(`π = piFlip ∨ π = piDouble ∨ ∃ c, π = piSwap c`), with the
decided status recorded in the header, the section comment,
and the question's docstring: **Grade T is already decided
negatively at T1 by `toggle_exclusion`** (FAM checks) — the
pin proves nothing about it and re-opens nothing; widening
the general toggle notion is CLS-2's.

**Grade R — prose only, by design.** The equivalence notion
is UNCHOSEN and the grade UNPRICED; the module carries Grade
R in prose only — deliberately no definition, no Prop, no
placeholder, and no Grade-R identifier exists in code. Its
absence is explicit and named rather than faked.

**K-CLS-0 (costume kill) does not fire:** `weightAt` is a
relation over all π and all v — no character-ness,
sector-constancy, or diagonality appears as a hypothesis
anywhere; the character equation is the content asked, not
an assumption. The extraction question (does every base π
admit a weight vector at all?) is named as CLS-1, open and
unassumed.

## Fences

NO CLAIM; **Dial 1: 0.** The classification frontier stands
exactly as pinned: Grade W open, Grade T closed negatively,
Grade R unposed. Nothing in this pin is a forcing theorem or
evidence toward one.

**Census after landing: 11,665 strict / 11,971 total / 398 counted
modules; zero `sorry` terms tree-wide.**

## Backers since last landing

None new on the record since the last landing.
