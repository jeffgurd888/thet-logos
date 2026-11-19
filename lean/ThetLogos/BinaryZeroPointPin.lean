/-
# BinaryZeroPointPin — the Binary Zero Point, with its other half

**Commissioned by Zero, 2026-11-13 ("build it and mix it
with the other half"), following his naming of
2026-11-13 19:34–19:35 EST (scope:
~/workspace/your_files/binary-zero-point-pin-scope-2026-11-13.md).
NO CLAIM. Dial-ineligible. Register-A naming card.**

THE NAMING (Zero's, declared, Register A): the BINARY
ZERO POINT, addressed **0.1.0** in Zero's dotted
address form (boundary seat 0, then 1, then 0) — the
contained centre point of the "(.)" ball, where the
binary pair {0, 1} sits at its origin. The name and
the address ride this module's face as Zero's naming.
No theorem states the address; names are not theorems.

THE MIXING, both halves of it (the reading stated to
Zero at the commission): inside the math, the point
is never built alone — the pin builds the two-state
type, the designated zero point, and the complement
("other half") map as one object. On the board, this
pin is queued mixed with the TetWitnessPin — the root
board's other half — and lands immediately after it.

FIDELITY, stated plainly: the mathematics here is
trivial BY DESIGN. The honest content of a pointed
two-element set is small — a swap that is an
involution, has no fixed point, and exhausts the
pair with no residual — and the pin proves exactly
that and no more. Its value is the card: Zero's root
naming seated in the corpus beside its witness half,
at exactly its weight.

FENCES: K-BZP-PHYS stands armed — this pin claims
NOTHING about physics, computation, or the nature of
binary; it is a naming with elementary content, never
a discovery. The Tet absolute is untouched: this
module does not state, imply, or use any Tet identity
(K-TETE-IDENTITY armed as always); the root string
itself is not in this module.

STATUS: STATUS-BZP.md.
-/

import Mathlib.Data.Fintype.Card

namespace ThetLogos

/-! ## §1 — the two states, the zero point, the other half -/

/-- The binary states: the two elements of the pair.
`zero` is the designated zero point's underlying
state; `one` is the other half. -/
inductive BinaryState where
  | zero : BinaryState
  | one : BinaryState
  deriving DecidableEq

/-- The states form a finite type, by enumeration. -/
instance : Fintype BinaryState where
  elems := {BinaryState.zero, BinaryState.one}
  complete := by
    intro x
    cases x <;> simp

/-- **The zero point**: the designated element of the
pair (Zero's naming: the point at address 0.1.0). -/
def zeroPoint : BinaryState := BinaryState.zero

/-- **The other half**: the complement map, swapping
the two states. -/
def otherHalf : BinaryState → BinaryState
  | .zero => .one
  | .one => .zero

/-! ## §2 — the pair card: the two halves, nothing else -/

/-- B-1: the swap is an involution — the other half of
the other half is the point itself. -/
theorem otherHalf_involutive : Function.Involutive otherHalf := by
  intro x
  cases x <;> rfl

/-- B-2: the swap has no fixed point — the other half
is genuinely other. -/
theorem otherHalf_ne_self (x : BinaryState) : otherHalf x ≠ x := by
  cases x <;> decide

/-- B-3: exhaustion — every state is the zero point or
its other half; the pair is all there is. -/
theorem eq_zeroPoint_or (x : BinaryState) :
    x = zeroPoint ∨ x = otherHalf zeroPoint := by
  cases x
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- B-4a: the pair card — the type has exactly two
elements. -/
theorem binaryState_card : Fintype.card BinaryState = 2 := by
  decide

/-- B-4b: no residual — from either point, the pair
{x, other half of x} is the whole type. -/
theorem pair_eq_univ (x : BinaryState) :
    ({x, otherHalf x} : Finset BinaryState) = Finset.univ := by
  cases x <;> decide

end ThetLogos
