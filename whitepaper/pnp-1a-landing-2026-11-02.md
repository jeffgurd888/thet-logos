# PNP-1a LANDING DOSSIER — P vs NP definitions brick — 2026-11-02

**Item:** PNP-1a (Millennium Lane 3) — the definitions half
of PNP-1, per PNP-0's priced split. Audit committed
alongside.

## VERDICT: DEFINITIONS LANDED — verifier-form NP, honest both-directions PeqNP, K-PNP-1 Part A inherited

**Artifact:** `lean/ThetLogos/PvsNPDefs.lean` — strict 3
(the three `Iff.rfl` unfold self-checks, labeled as such),
defs 7 (house counter). Verified by the coordinator in the
main tree (build green); all three proved items on exactly
`[propext, Classical.choice, Quot.sound]`.

Every audit name landed at its audited shape: `PolyDecider`
(a structure over the pin's `TM2ComputableAux`, a
`Polynomial ℕ` time bound, totality via
`TM2OutputsInTime` in the pin's genuine step-count unit),
`InP`, `PClass`, `pairStr`, `InNP`, `NPClass`, `PeqNP`,
`NPSubsetP`. No NDTM form, no equivalence statement, no
membership theorems.

**The two NP guards, verbatim as coded** (the audit's
load-bearing pair): the certificate bound is in |x| alone
— `w.length ≤ (x.length + 1) ^ c` — and the verifier
language is itself required to be in `InP` (a polytime
decider over paired inputs). Weaken either and the class
inflates; both stay.

**`PeqNP := PClass = NPClass`** — set equality, the honest
both-directions form. The one-way form was forbidden by
the audit and is not used: it would bake in the unproved
P ⊆ NP.

**K-PNP-1 status:** Part A (genuine step-count unit +
decider totality block construction artifacts) — PASS at
audit, inherited by these defs exactly while both
properties stay as coded; the fence is on the module's
face. Part B (the time-hierarchy witness must be statable
outside P) remains CONDITIONAL on D5, which is PNP-1c's
brick; PNP-1a names its exact interface (the pin's
`Nat.Partrec.Code` route — nothing needs extracting from
`PolyDecider`).

**One named plumbing deviation (on the module's face):**
the audit's literal membership-`if` does not elaborate
in-pin (no `Decidable (x ∈ L)`); supplied via
`open Classical in` on `PolyDecider`, the field text
otherwise character-for-character the audit's.

## Fences

NO CLAIM; **parts of P vs NP closed: 0.** Definitions
only — the board statement lands in PNP-1b against these
names. Jeff's T5 identification is excluded from the pin,
per the audit.

**Census after landing: 12,554 strict / 13,030 total / 435 counted
modules; zero `sorry` terms tree-wide.**

## Backers since last landing

None new on the record since the last landing.
