import Mathlib.Tactic
import ThetLogos.ShapedRimFivePin

/-!
# ThetLogos.ShapedRimVerdictPin — the shaped-rim line, closed (T5)

Brick F-3 of the shaped-rim Fin 4+ line: the verdict /
preservation brick, and the line's closing module. Scope of
record: `~/workspace/your_files/shaped-rim-fin4-scope-DRAFT-2026-11-24.md`
(Zero's decision 2026-11-24 09:53 EST; scope approved 2026-11-24
10:00 EST; F-3 fired by Zero's explicit word 2026-11-24 16:08 EST,
after F-0, F-1, F-2 banked at lane grade).

TIER: T5 design study. NO CLAIM. Dials 0/4 — Dial 2 (derived
gravity object) stays 0 under EVERY outcome of this line,
including total success. `dropVec` is not G; the gravitational
constant appears nowhere in this line; no gravity object is
constructed, fed, or identified. "Shaped rim" remains the
working label from Zero's mirror image; final module naming is
his hand.

## The three NOs, beside each other — each at its own scope

This module assembles the shaped-rim line's three negative
verdicts into one closing object (`shapedRimLineVerdict`). Each
conjunct is cited from its banked verdict theorem; nothing here
is re-proved, and nothing here is re-graded. **The
seat-relativity is on the face:** each NO is a statement about
its own question — its own seat, its own field regime — not a
universal claim about pairings, and no conjunct amends another.

1. **Fin 3** (`shapedRimVerdict`, `ShapedRimPin`, hb `9847cef`;
   in the census as of the T11 integration): no rim weighting
   makes the pairing exact for all fields (K-RIM-NONE); the
   currents' unique exact weight is the constant `ρ ≡ 2`;
   the pinned rule is exact only at `R = univ ∧ φ₀ = 0`, with
   the field-shadow identically zero, and the pumped route's
   supply IS S-2's correction term (K-RIM-TRIVIAL, both
   routes). The seat's own reason: at `Fin 3` every vertex is
   rim — there is no interior for a shaped boundary to
   protect.
2. **F-1, seat-general** (`shapedRim4F1Verdict` at `Fin 4`;
   `shapedRimGen_no_weight` at an arbitrary finite seat): the
   unrestricted question re-asked at seats WITH an interior
   has the same answer, for the same reason, at every finite
   seat with two distinct vertices — K-RIM4-NONE and
   K-RIM4-TRIVIAL both fired seat-generally. The deciding
   exhibits are unrestricted fields, admissible at interior
   vertices too; the interior's existence changes nothing
   while the fields are free. The trivial forms are named in
   the conjuncts: the pinned rule exact only at the empty
   region and the zero datum; Q-anti's unique exact weight
   the constant `ρ ≡ 2`, S-2's factor, not a profile.
3. **F-2, restricted, at `Fin 5`** (`shapedRim5F2Verdict`,
   `ShapedRimFivePin`): the one regime F-1 does not touch —
   fields restricted to the face/rim support, the rim pinned
   to a datum, the face-relative interior vertex free. NO
   again: K-RIM4-NONE fired in restricted form. The
   restriction buys nothing — the diagonal exhibit is
   genuinely excluded by the support, and a crossing exhibit
   inside the support does its work instead: exactness at one
   supported crossing pair forces the interior value to zero,
   against the pinned rule's defining freedom. Even the zero
   datum fails; K-RIM4-TRIVIAL does not fire, because
   exactness is not bought by a degenerate form — it is not
   bought at all.

Read together: at every seat this line asked — the seat with
no interior, any seat with the fields unrestricted, and the
first seat where a face-relative interior exists with the
fields restricted to the rim's own support — shaping the rim
does not make the pairing exact with content of its own.
That is the line's designed outcome, reported at full rank:
a proved NO, in three scopes, beside the two honest landings
the wider line keeps at theirs (the antisymmetric weight `2`,
the pumped identity — both bookkeeping the flat seat already
knew, stated as such in the Fin 3 verdict's fourth conjunct).

## Charge 4 — the Fin 3 result, preserved

Zero's fourth charge is discharged below as a theorem-shaped
citation (`shapedRimFin3Preserved`): this module STATES the
Fin 3 verdict, verbatim, as its own first theorem, and
discharges it by citing `shapedRimVerdict` alone. The Fin 4+
line extends the map — new seats, new regimes, new exhibits —
and changes nothing about the Fin 3 result: the Fin 3 NO
stands at `Fin 3` exactly as banked and as integrated at T11
(census 16,431 strict / 736 modules, ledger 168). Neither
direction amends the other: Fin 3's NO was never a universal
obstruction (its seat has no interior), and the Fin 4+ NOs
do not reach back to widen or narrow it.

The universality fence, restated as the scope charged:
everything in this line holds for every potential and is
stated at finite seats — it shapes a mirror, never an object.
No gravity object was constructed, fed, or identified by any
brick of this line. There is no F-4.
-/

namespace ThetLogos

/-- **Charge 4 — the Fin 3 verdict, preserved.** The Fin 3
line's verdict, stated verbatim in this closing module and
discharged by citation alone (`shapedRimVerdict`,
`ShapedRimPin`): (1) no rim weighting is exact for all
fields; (2) the currents' unique exact weight is the
constant `2`; (3) the pinned rule is exact only at the
whole seat and the zero datum; (4) the pumped rim's supply
is S-2's correction term itself. The Fin 4+ line cites this
verdict; it does not re-prove it, re-grade it, or amend it,
and nothing in F-1 or F-2 reaches back to it. -/
theorem shapedRimFin3Preserved :
    (¬ ∃ ρ, shapedRimExactAll ρ) ∧
    (∀ ρ, shapedRimExactAnti ρ → ρ = fun _ => 2) ∧
    (∀ (R : Finset (Fin 3)) (φ₀ : Fin 3 → ℝ),
      (∀ φ, shapedRimPinned R φ₀ φ → ∀ X,
        shapedRimPairing φ X = ∑ i, φ i * diverge X i) →
      R = Finset.univ ∧ φ₀ = 0) ∧
    (∀ (φ : Fin 3 → ℝ) (X : Fin 3 → Fin 3 → ℝ),
      (∑ i, shapedRimPump φ X i) = ∑ i, φ i * gravShadowOutflow X i) :=
  shapedRimVerdict

/-- **F-1's NO at its general scope.** At an arbitrary
finite seat with two distinct vertices, no rim weighting
makes the pairing exact for all (unrestricted) fields —
K-RIM4-NONE, seat-general. Cited from
`shapedRimGen_no_weight`; the `Fin 4` verdict form is the
next-but-one conjunct of the closing assembly. -/
theorem shapedRimNoWeight_seatGeneral :
    ∀ (V : Type*) [Fintype V] [DecidableEq V] (i₀ j₀ : V),
      i₀ ≠ j₀ → ¬ ∃ ρ : V → ℝ, shapedRimGenExactAll ρ := by
  intro V _ _ i₀ j₀ h
  exact shapedRimGen_no_weight h

/-- **The shaped-rim line's closing verdict.** The three
NOs beside each other, each cited from its banked verdict
and each at its own scope — no conjunct re-proved, none
re-graded, none amending another:

(1) the **Fin 3 verdict** verbatim (charge 4's object:
preserved, per `shapedRimFin3Preserved`);
(2) **F-1's NO at its general scope** — no rim weighting at
any finite seat with two distinct vertices is exact for all
unrestricted fields;
(3) **F-1's verdict at `Fin 4`** — the same NO in its
banked instance, with the trivial forms named: Q-anti's
unique exact weight the constant `2`, and the pinned rule
exact only at the empty region and the zero datum;
(4) **F-2's verdict at `Fin 5`** — the restricted NO: no
pinned datum is exact over the support-restricted fields,
exactness at the supported crossing exhibit forces the
interior value to zero, and even the zero datum fails.

The seat-relativity is part of the statement: (1) is about
`Fin 3`, where no interior exists; (2)–(3) are about
unrestricted fields, where an interior's existence changes
nothing; (4) is about the restricted regime at the first
seat with a face-relative interior, where the restriction
buys nothing. Together they close the question this line
was scoped to ask, and no wider claim is made. -/
theorem shapedRimLineVerdict :
    ((¬ ∃ ρ, shapedRimExactAll ρ) ∧
    (∀ ρ, shapedRimExactAnti ρ → ρ = fun _ => 2) ∧
    (∀ (R : Finset (Fin 3)) (φ₀ : Fin 3 → ℝ),
      (∀ φ, shapedRimPinned R φ₀ φ → ∀ X,
        shapedRimPairing φ X = ∑ i, φ i * diverge X i) →
      R = Finset.univ ∧ φ₀ = 0) ∧
    (∀ (φ : Fin 3 → ℝ) (X : Fin 3 → Fin 3 → ℝ),
      (∑ i, shapedRimPump φ X i) = ∑ i, φ i * gravShadowOutflow X i)) ∧
    (∀ (V : Type*) [Fintype V] [DecidableEq V] (i₀ j₀ : V),
      i₀ ≠ j₀ → ¬ ∃ ρ : V → ℝ, shapedRimGenExactAll ρ) ∧
    ((¬ ∃ ρ : Fin 4 → ℝ, shapedRim4ExactAll ρ) ∧
    (∀ ρ : Fin 4 → ℝ, shapedRim4ExactAnti ρ → ρ = fun _ => 2) ∧
    (∀ (S : Finset (Fin 4)) (φ₀ : Fin 4 → ℝ),
      (∀ φ, shapedRim4Pinned S φ₀ φ → ∀ X,
        shapedRim4Pairing φ X = ∑ i, φ i * diverge X i) →
      S = ∅ ∧ φ₀ = 0)) ∧
    ((∀ φ₀ : Fin 5 → ℝ, ¬ shapedRim5PinnedExact φ₀)
      ∧ (∀ φ : Fin 5 → ℝ, shapedRimGenPairing φ (shapedRim5Cross 1)
          = ∑ i, φ i * diverge (shapedRim5Cross 1) i → φ 4 = 0)
      ∧ ¬ shapedRim5PinnedExact 0) :=
  ⟨shapedRimVerdict, shapedRimNoWeight_seatGeneral,
   shapedRim4F1Verdict, shapedRim5F2Verdict⟩

end ThetLogos
