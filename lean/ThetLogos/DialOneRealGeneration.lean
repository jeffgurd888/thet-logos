import Mathlib.Tactic
import ThetLogos.DialOneGradeRConjPin
import ThetLogos.DialOneGradeRConjAmend
import ThetLogos.DialOneAntiparticleBase
import ThetLogos.DialOnePiAntiPackage

open Matrix Complex
open ThetLogos.Track1RouteB
open ThetLogos.PreOptionARepresentation
open ThetLogos.DialOneGradeRConjPin
open ThetLogos.DialOneGradeRConjAmend
open ThetLogos.DialOneConjugationCounterexample
open ThetLogos.DialOneAntiparticleChapter
open ThetLogos.DialOneAntiparticleBase

namespace ThetLogos.DialOneRealGeneration

/-!
# ThetLogos.DialOneRealGeneration — ROPE BRIDGE brick: Dial-1 real generation

Working label only ("Dial-1 real generation"); public naming
is Jeff's hand. Commissioned by Jeff, 2026-11-07 22:22 EST
("scope rope bridge build and run"); built to the statement
shapes of the ROPE BRIDGE scoping
(`rope-bridge-scope-2026-11-07.md`, §B (A) + (C2)), which is
the build's governing text. NO CLAIM; dials 0/4; Dial 1 = 0 —
generation and transport facts about the classification
derive no measured number.

## What this brick is

The scoping's recommended build, (A) + (C2) as one brick:

1. **The generation predicate** (§B (A)). Every exhibited
   member of the Dial-1 menagerie — `pi1`, `piU`, `piAnti`,
   `conjRep conjU piAnti` — is generated from `pi1` by the
   two bridge operation species: conjugation by a member of
   the amended class `RealCentralizingClass`, and the colour
   twist. The four cases discharge from landed facts alone:
   `piU_eq_conjRep` (Grade R pin read-back) with
   `conjU_realCentralizing` (the amendment);
   `piAnti_eq_pi1_colourTwist` (AntiparticleBase; pointwise,
   funext here); and case 4 by rewriting case 3's equality
   through `conjRep`. Registered kill **K-ROPE-GEN**: fires
   if any case needs an operation outside the two named
   species; the generator set is never widened quietly.

2. **The twist's certificate** (§B (C2)). The colour twist
   is a PARTIAL conjugation — entrywise conjugation of the
   colour summand alone — and the scoping's refinement is
   carried exactly: it is certified as a **real-form
   operation**, NOT as a real-matrix action. The certificate
   is the total conjugation `totalConj` (entrywise
   conjugation of all three summands of `AF`; no such
   definition existed in the tree before this module):
   `totalConj` is involutive and respects `afMul` / `afAdd`
   / `afStar` — a *-automorphism of `(AF, af-ops)` — it
   commutes with `colourTwist`, and its fixed-point
   predicate `totalConj a = a` (the real form of `AF`) is
   closed under the af-operations. Registered kill
   **K-ROPE-TWIST**: fires if the commutation computation
   fails.

Tier: T1 packaging of T1 facts (part 1); T1 (part 2). The
thread this brick pins is T5 as a whole — "the real layer
generates; the complex layer is generated" — and the dead
strengthening stays dead: `piU` is honestly complex
(`piU_entry_two = -(16/25) * I`, ledger
`dial-one-pianti-package`); generation, not reality of the
generated, is what is proved here.
-/

/-- **The generation predicate** (ROPE BRIDGE scoping
§B (A), verbatim shape): `π` is generated from `pi1` by the
bridge operations — it is `pi1` itself, or a
`RealCentralizingClass` conjugate of `pi1`, or `pi1` after
the colour twist, or a `RealCentralizingClass` conjugate
of that. -/
def RealGeneratedFromPi1 (π : AF → Matrix (Fin 32) (Fin 32) ℂ) : Prop :=
  π = pi1
    ∨ (∃ U, RealCentralizingClass U ∧ π = conjRep U pi1)
    ∨ π = pi1 ∘ colourTwist
    ∨ (∃ U, RealCentralizingClass U ∧ π = conjRep U (pi1 ∘ colourTwist))

/-- **Total conjugation on `AF`** (ROPE BRIDGE scoping
§B (C2), verbatim shape): entrywise conjugation of all
three summands — the ℂ summand by `star`, the ℍ and colour
matrix summands by `Matrix.map (starRingEnd ℂ)`. The
colour twist is the same operation restricted to the
colour summand alone. -/
def totalConj (a : AF) : AF :=
  ⟨star a.u1, a.q.map (starRingEnd ℂ), a.color.map (starRingEnd ℂ)⟩

/-! ## §1. The generation predicate, discharged (scope §B (A))

Registered kill **K-ROPE-GEN** watches this section: it
fires if any case discharge needs an operation outside the
two named generator species {conjugation by a
`RealCentralizingClass` member; `colourTwist`}. All four
cases discharge from landed facts; the kill does not fire.
-/

/-- Case `pi1`: the generator itself, by the identity
disjunct. -/
theorem realGenerated_pi1 : RealGeneratedFromPi1 pi1 :=
  Or.inl rfl

/-- Case `piU`: the read-back `piU = conjRep conjU pi1`
(Grade R pin), with `conjU` a member of the amended class
(`conjU_realCentralizing`). -/
theorem realGenerated_piU : RealGeneratedFromPi1 piU :=
  Or.inr (Or.inl ⟨conjU, conjU_realCentralizing, piU_eq_conjRep⟩)

/-- Case `piAnti`: the twist disjunct. The landed
`piAnti_eq_pi1_colourTwist` is pointwise; `funext` gives
the function equality the predicate states (the same
funext form the chapter bundle `antiparticle_base_chapter`
carries as its first component). -/
theorem realGenerated_piAnti : RealGeneratedFromPi1 piAnti :=
  Or.inr (Or.inr (Or.inl (funext piAnti_eq_pi1_colourTwist)))

/-- Case `conjRep conjU piAnti`: the fourth disjunct, at
the same witness `conjU` — rewrite the landed funext
equality `piAnti = pi1 ∘ colourTwist` through `conjRep`.
No operation outside the two named species is used;
**K-ROPE-GEN does not fire**. -/
theorem realGenerated_conjRep_piAnti :
    RealGeneratedFromPi1 (conjRep conjU piAnti) :=
  Or.inr (Or.inr (Or.inr ⟨conjU, conjU_realCentralizing,
    by rw [show piAnti = pi1 ∘ colourTwist from
      funext piAnti_eq_pi1_colourTwist]⟩))

/-- **HEADLINE (§B (A)) — Dial-1 real generation**: all
four exhibited members of the Dial-1 menagerie are
generated from `pi1` by the bridge operations —
conjugation by a member of the amended real class, and
the colour twist. Bundled in the genus of
`antiparticle_base_chapter`. What is proved is
generation, not reality of the generated: `piU` stays
honestly complex (`piU_entry_two`). -/
theorem realGeneration_chapter :
    RealGeneratedFromPi1 pi1 ∧ RealGeneratedFromPi1 piU
      ∧ RealGeneratedFromPi1 piAnti
      ∧ RealGeneratedFromPi1 (conjRep conjU piAnti) :=
  ⟨realGenerated_pi1, realGenerated_piU, realGenerated_piAnti,
   realGenerated_conjRep_piAnti⟩

/-! ## §2. The twist's certificate: `totalConj` (scope §B (C2))

`totalConj` — entrywise conjugation of ALL three summands
— is the real form of `(AF, af-ops)` made an operation:
the theorems below certify it as a *-automorphism of the
real species, and its commutation with `colourTwist`
certifies the twist as a REAL-FORM OPERATION in the
precise sense: the partial conjugation (colour summand
alone) is the restriction of the total conjugation to a
summand subset, and subset conjugations commute.
Registered kill **K-ROPE-TWIST** watches the commutation
computation; it does not fire.
-/

/-- `totalConj` is involutive, entrywise (`star_star` on
each summand). -/
theorem totalConj_involutive : Function.Involutive totalConj := by
  intro a
  refine (ThetLogos.PreOptionARepresentation.ext_iff).mpr ⟨?_, ?_, ?_⟩
  · show star (star a.u1) = a.u1
    exact star_star a.u1
  · ext k l
    show star (star (a.q k l)) = a.q k l
    exact star_star _
  · ext k l
    show star (star (a.color k l)) = a.color k l
    exact star_star _

/-- `totalConj` respects `afMul`: entrywise, `star` over
each finite sum of products, with ℂ-entry commutativity
absorbing the `star_mul` order flip — the
`colourTwist_afMul` computation, on all three summands. -/
theorem totalConj_afMul (a b : AF) :
    totalConj (afMul a b) = afMul (totalConj a) (totalConj b) := by
  refine (ThetLogos.PreOptionARepresentation.ext_iff).mpr ⟨?_, ?_, ?_⟩
  · show star (a.u1 * b.u1) = star a.u1 * star b.u1
    rw [star_mul]; exact mul_comm _ _
  · ext k l
    show star ((a.q * b.q) k l)
      = ((a.q.map (starRingEnd ℂ)) * (b.q.map (starRingEnd ℂ))) k l
    rw [Matrix.mul_apply, Matrix.mul_apply, star_sum]
    apply Finset.sum_congr rfl
    intro x _
    show star (a.q k x * b.q x l) = star (a.q k x) * star (b.q x l)
    rw [star_mul]; exact mul_comm _ _
  · ext k l
    show star ((a.color * b.color) k l)
      = ((a.color.map (starRingEnd ℂ))
        * (b.color.map (starRingEnd ℂ))) k l
    rw [Matrix.mul_apply, Matrix.mul_apply, star_sum]
    apply Finset.sum_congr rfl
    intro x _
    show star (a.color k x * b.color x l)
      = star (a.color k x) * star (b.color x l)
    rw [star_mul]; exact mul_comm _ _

/-- `totalConj` respects `afAdd`, entrywise (`star_add`
on each summand). -/
theorem totalConj_afAdd (a b : AF) :
    totalConj (afAdd a b) = afAdd (totalConj a) (totalConj b) := by
  refine (ThetLogos.PreOptionARepresentation.ext_iff).mpr ⟨?_, ?_, ?_⟩
  · show star (a.u1 + b.u1) = star a.u1 + star b.u1
    exact star_add a.u1 b.u1
  · ext k l
    show star (a.q k l + b.q k l) = star (a.q k l) + star (b.q k l)
    exact star_add _ _
  · ext k l
    show star (a.color k l + b.color k l)
      = star (a.color k l) + star (b.color k l)
    exact star_add _ _

/-- `totalConj` respects `afStar`: on the matrix summands
this is the commutation of entrywise conjugation with
`conjTranspose` — both orders give `star (star (M l k))`
at entry `(k, l)`, closed by `star_star`; the ℂ summand
is `star_star` against itself. -/
theorem totalConj_afStar (a : AF) :
    totalConj (afStar a) = afStar (totalConj a) := by
  refine (ThetLogos.PreOptionARepresentation.ext_iff).mpr ⟨?_, ?_, ?_⟩
  · show star (star a.u1) = star (star a.u1)
    rfl
  · ext k l
    simp only [totalConj, afStar, Matrix.map_apply,
      Matrix.conjTranspose_apply, starRingEnd_apply, star_star]
  · ext k l
    simp only [totalConj, afStar, Matrix.map_apply,
      Matrix.conjTranspose_apply, starRingEnd_apply, star_star]

/-- **The twist's certificate**: `colourTwist` commutes
with `totalConj`. Both maps conjugate a subset of the
summands — `totalConj` all three, the twist the colour
summand alone — and subset conjugations commute:
componentwise the two orders agree on the nose (the ℂ
summand sees only `totalConj`'s `star`, the ℍ summand
only its `map star`, the colour summand the same double
conjugation in both orders). This is the theorem that
makes "the colour twist is a real-form operation" a
theorem-grade sentence. **K-ROPE-TWIST does not fire.** -/
theorem totalConj_colourTwist_comm (a : AF) :
    totalConj (colourTwist a) = colourTwist (totalConj a) := by
  refine (ThetLogos.PreOptionARepresentation.ext_iff).mpr ⟨?_, ?_, ?_⟩
  · show star a.u1 = star a.u1
    rfl
  · show a.q.map (starRingEnd ℂ) = a.q.map (starRingEnd ℂ)
    rfl
  · show (a.color.map (starRingEnd ℂ)).map (starRingEnd ℂ)
      = (a.color.map (starRingEnd ℂ)).map (starRingEnd ℂ)
    rfl

/-- **The real form is af-closed**: the fixed-point
predicate `totalConj a = a` — the real form of `AF`, as a
predicate — is closed under `afMul`, `afAdd`, and
`afStar`, by the three respect theorems above. -/
theorem totalConj_fixed_afClosed {a b : AF}
    (ha : totalConj a = a) (hb : totalConj b = b) :
    totalConj (afMul a b) = afMul a b
      ∧ totalConj (afAdd a b) = afAdd a b
      ∧ totalConj (afStar a) = afStar a :=
  ⟨by rw [totalConj_afMul, ha, hb],
   by rw [totalConj_afAdd, ha, hb],
   by rw [totalConj_afStar, ha]⟩

-- Axiom audit for the headlines (expected:
-- [propext, Classical.choice, Quot.sound] throughout).
#print axioms realGeneration_chapter
#print axioms totalConj_involutive
#print axioms totalConj_afMul
#print axioms totalConj_afAdd
#print axioms totalConj_afStar
#print axioms totalConj_colourTwist_comm
#print axioms totalConj_fixed_afClosed

end ThetLogos.DialOneRealGeneration
