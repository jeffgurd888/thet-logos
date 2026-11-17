/-!
# ReadingRulePin — the IF/AND/OR reading rule, pinned at the olean level

A RECORD PIN (band S). It freezes, in kernel-checked form, the procedure
Zero set for reading his own absolute words ("always" / "never") in this
record. Scoping: `~/workspace/your_files/if-and-or-reading-rule-scope-2026-11-12.md`
(Form A). Commissioned by Zero, 2026-11-12 12:21 EST: "build it" —
Form A only; the Form B companion audit is not part of this pin.

## The rule (Zero's setting, 2026-11-12 12:16 EST, by tap: "Set the IF/AND/OR rule")

An absolute of Zero's reads AS WRITTEN if it is spoken as a ruling
(doctrine, pin, verdict, standing instruction) OR he marks that he has
to mean it ("I would never say never unless I had too" — his own
2026-11-10 hatch, the OR in his sentence). It reads MOST GENERALLY
(the strongest presumption, not a wall) if it is NOT a ruling AND NOT
marked. AND if a neither-case absolute is about to change an action or
enter the record as law, the reader asks once at that joint before it
hardens.

Zero's gloss, verbatim (2026-11-12 12:17): "that to me smells like a
primitive at the binary Olean level". Classification graded 2026-11-12
at his ask: a PRIMITIVE (Register A — a definition he may declare),
not a primordial (its jurisdiction is local: Zero's words → this
record; a primordial's is root and universal, and is never compiled —
a primitive is exactly what gets compiled).

## What this pin proves, and what it does not

The five theorems below prove the procedure is total and deterministic
and that its truth table is the one Zero set: `readingOf` returns
`asWritten` exactly in the ruling-or-marked cases, `mostGenerally`
exactly in the neither case, and the ask state arises only in the
neither case at a joint.

The pin proves NOTHING about language, communication, or cognition in
general (the rule as a universal law of communication is the scope
sheet's Form C — FRONTIER, not stateable here). It does not prove the
rule CORRECT: a primitive is declared, not derived.

FENCE ON THE FACE: the three Bool fields of `ReadingUtterance` are
supplied by the record-keeper from the record. Whether a given
utterance was spoken as a ruling is a record act, not a theorem;
the kernel checks the table, not the classification.

## Pre-registered kills (from the scope sheet)

- K-IFOR-VACUITY — fires if the pin's inputs cannot be anchored to
  record-facts. Guard: the two instances below, both drawn from the
  dated record. Neither fired at drafting.
- K-IFOR-THIRD — fires if an honest formalization forces `Reading`
  itself to be three-valued (the ask becoming a reading instead of a
  procedure state). In this module `Reading` has exactly two
  constructors and the ask lives in `NeedsAsk`, a predicate on
  utterances — the separation the kill watches. Not fired.
- K-IFOR-SELF (consistency note) — the rule was set AS a ruling, so
  under itself it reads as written. An observation, never a proof.

## The instances

(1) The Tet ruling, 2026-10-16 — "Tet is the name of the equality,
never the value" — spoken as a ruling: `isRuling = true`.
(2) The joint case, exhibited by the record of 2026-11-12: the
challenge that reopened this rule ("we need to check the never most
generally challenge", 12:13 EST) arrived as working talk — neither a
ruling nor marked — at a joint where the reading was about to be
re-set in the record; the procedure asked (options put to Zero), and
Zero ruled. `⟨false, false, true⟩`.

PRE-REGISTERED DIAL-INELIGIBLE. NO CLAIM. The pin moves no dial,
closes no part of any official statement, and assimilates nothing.
-/

namespace ThetLogos

/-- An utterance carrying an absolute, classified by the record.
The fields are record-facts supplied by the record-keeper:
`isRuling` — spoken as a ruling (doctrine, pin, verdict, standing
instruction); `isMarked` — Zero marked that he has to mean it;
`atJoint` — the reading is about to change an action or enter the
record as law. -/
structure ReadingUtterance where
  isRuling : Bool
  isMarked : Bool
  atJoint : Bool
deriving DecidableEq, Repr

/-- The two readings. Exactly two constructors, by design —
K-IFOR-THIRD watches this type. -/
inductive Reading where
  | asWritten
  | mostGenerally
deriving DecidableEq, Repr

/-- The rule as a total function: AS WRITTEN if ruling OR marked,
MOST GENERALLY otherwise. -/
def readingOf (u : ReadingUtterance) : Reading :=
  if u.isRuling || u.isMarked then .asWritten else .mostGenerally

/-- The ask state — a state of the PROCEDURE, not a third reading:
at a joint, in the neither case, the reader asks before the word
hardens into the record. -/
structure NeedsAsk (u : ReadingUtterance) : Prop where
  atJoint : u.atJoint = true
  notRuling : u.isRuling = false
  notMarked : u.isMarked = false

/-- Truth table, as-written side: `readingOf` returns `asWritten`
exactly when the utterance is a ruling or is marked. -/
theorem readingOf_asWritten_iff (u : ReadingUtterance) :
    readingOf u = .asWritten ↔ u.isRuling = true ∨ u.isMarked = true := by
  cases u with
  | mk a b c => cases a <;> cases b <;> cases c <;> decide

/-- Truth table, most-generally side: `readingOf` returns
`mostGenerally` exactly in the neither case. -/
theorem readingOf_mostGenerally_iff (u : ReadingUtterance) :
    readingOf u = .mostGenerally ↔ u.isRuling = false ∧ u.isMarked = false := by
  cases u with
  | mk a b c => cases a <;> cases b <;> cases c <;> decide

/-- The ask arises only in the most-generally seat: any utterance in
the ask state reads most generally — the ask guards a presumption,
never a wall. -/
theorem needsAsk_reading (u : ReadingUtterance) (h : NeedsAsk u) :
    readingOf u = .mostGenerally := by
  rw [readingOf_mostGenerally_iff]
  exact ⟨h.notRuling, h.notMarked⟩

/-- Instance (1): the Tet ruling of 2026-10-16, spoken as a ruling,
reads as written. -/
theorem tetRuling_reading : readingOf ⟨true, false, false⟩ = .asWritten := by
  decide

/-- Instance (2): the joint case of 2026-11-12 — working talk at a
joint, neither ruling nor marked — is in the ask state. -/
theorem jointCase_needsAsk : NeedsAsk ⟨false, false, true⟩ :=
  ⟨rfl, rfl, rfl⟩

end ThetLogos
