# CLS-3c-A LANDING DOSSIER — the piAnti cell decided: Grade T complete — 2026-11-02

**Item:** CLS-3c-A (Lane 1) — CLS-3c's named open cell:
piAnti's own base status. Priced by the CLS-3c-A scoping
(S–M); landed by its primary route.

## VERDICT: LANDED FULL — piAnti satisfies base AND the strengthened family AND carries the common weights; WeightQuestionW answered YES

**Artifact:** `lean/ThetLogos/DialOneAntiparticleBase.lean`
— strict 21, defs 1 (below the 35–55 estimate; the
transport was cheaper than priced — the count is the
count). Verified by the coordinator in the main tree
(build green); all headlines on exactly
`[propext, Classical.choice, Quot.sound]`.

**The mechanism, proved in-tree:** `colourTwist` is an
AF-automorphism (its afMul/afAdd/afStar/afOne/afZero laws
proved; involutive; flips only β in `u1Gen`/`u1ParamGen`),
and `piAnti_eq_pi1_colourTwist : ∀ a, piAnti a =
pi1 (colourTwist a)` — piAnti is π₁ read through colour
conjugation. Every clause then transported from π₁'s
landed proofs (clause 10's witness flips to (3, 1)).

**The three frozen headlines, all FULL:**
1. `dialOneBase_piAnti : DialOneBase piAnti`
2. `strengthenedFam_piAnti : DialOneStrengthenedFam piAnti`
3. `weightAt_piAnti_common : weightAt piAnti
   commonWeightVector`

plus `piAnti_not_orbit` (piAnti is NOT a toggle-orbit
point) and `weightQuestionW_piAnti`.

**What this settles, at exact rank:**
- **Grade T is COMPLETE — no open cells.** The antiparticle
  chapter closes: the strengthened set contains, beyond
  the orbit's two points, the antiparticle point piAnti —
  distinct from π₁, off-orbit, satisfying the full
  strengthened family.
- **`WeightQuestionW` is answered YES** (its standing
  pose): a strengthened point other than π₁ carrying the
  common weight vector exists — piAnti is that point. The
  common weights are attained by (at least) two distinct
  lifts. **This derives no measured number** — piAnti's
  weights ARE the table's weights, transported; the table
  remains input. Dial 1 = 0.
- No contradiction with CLS-3c (its uniqueness boundary
  was fenced to toggles; piAnti is not a toggle — the
  module says so on its face) and none with CLS-2b (the
  orbit classification is orbit-scoped; piAnti is proved
  not an orbit point).
- **K-CLS-3c-A does not fire** — the scoping's transport
  claim is confirmed by the landing it priced.

**Flag for the W′ decision item (parent/Jeff):** the
CLS-1b registration decision (re-posing Grade W as
WeightQuestionW′ over the strengthened ∧ regular class)
is still open. piAnti's lift is a character lift with
witness (3, 1) — the parent may want the W′ pose re-read
against this landing before registering it. Nothing
about W′ is decided here.

## Fences

NO CLAIM; Dial 1 = 0; all dials 0/4.

**Census after landing: 12,483 strict / 12,916 total / 432 counted
modules; zero `sorry` terms tree-wide.**

## Backers since last landing

None new on the record since the last landing.
