import Mathlib.Tactic
import ThetLogos.ShapedRimFourPin

/-!
# ThetLogos.ShapedRimFivePin — the shaped rim restricted: `Fin 5` (T5)

Brick F-2 of the shaped-rim Fin 4+ line. Scope of record:
`~/workspace/your_files/shaped-rim-fin4-scope-DRAFT-2026-11-24.md`
(Zero's decision 2026-11-24 09:53 EST; scope approved 2026-11-24
10:00 EST; F-2 fired by Zero's explicit word 2026-11-24 15:01 EST,
after F-1 banked seat-general — the scope's queue rule).

TIER: T5 design study. NO CLAIM. Dials 0/4 — Dial 2 (derived
gravity object) stays 0 under EVERY outcome of this line,
including total success. `dropVec` is not G; the gravitational
constant appears nowhere in this line; no gravity object is
constructed, fed, or identified. "Shaped rim" remains the
working label from Zero's mirror image; final module naming is
his hand.

## What is preserved (cited — never re-proved, never re-graded)

- **The Fin 3 verdict** (`ShapedRimPin`, hb `9847cef`; in the
  census as of T11): K-RIM-NONE and K-RIM-TRIVIAL both fired at
  `Fin 3`, where every vertex is rim and no interior exists.
  It stands exactly as banked; charge 4 (its preservation
  citation) is F-3's, beside `shapedRimVerdict`.
- **F-0's registrations** (`ShapedRimFourPin`): the two
  interiors registered distinctly — the region-split interior,
  which exists at `Fin 4`, and the face-relative interior,
  which is EMPTY at `Fin 4` (`shapedRim4FaceSplit_not_region`)
  and first exists at `Fin 5`. This brick sits at `Fin 5`
  because its question is face-shaped.
- **F-1's seat-general NO** (`shapedRim4F1Verdict` and the
  `shapedRimGen*` theorems): for UNRESTRICTED fields, no rim
  weighting and no pinned rule at any finite seat makes the
  pairing exact, except the pinned rule's degenerate seat
  (rim = whole seat, datum = 0, family = {0}) and Q-anti's
  constant weight `ρ ≡ 2`. F-1's deciding exhibits are
  unrestricted fields; a result about unrestricted fields at
  `Fin 5` is already dead by F-1 and is NOT re-asked here.

## This brick's question (the restricted one, as scoped)

At `Fin 5`, with the square face `⟨0, 1, 2, 3⟩` as the rim and
vertex `4` the face-relative interior:

- the **pinned rule** fixes a potential's values on the rim
  `{0, 1, 2, 3}` to a datum `φ₀` and leaves the interior
  vertex `4` FREE;
- the **fields are restricted to the face/rim support**: an
  admissible field vanishes off the boundary loop's edges and
  the rim crossings (the pairs between the rim and vertex 4).

Does a datum exist under which the pairing is exact for every
pinned potential and every supported field — with genuine
content as pre-registered (a nonzero datum, a nonzero interior
field-shadow, the field class not emptied by the rule)? The
diagonal exhibit at the interior vertex is NOT admissible
here — it is off the support — so F-1's argument does not
decide this question, and the scope prices it as the line's
one live sub-question. The mirrored kills are pre-registered
in their restricted forms: **K-RIM4-NONE** (no boundary rule
at this seat makes the pairing exact for all admissible
fields) and **K-RIM4-TRIVIAL** (exactness bought only by the
named degenerate forms: zero potential, constant weight,
correction re-injected, or a restriction so tight the field
class is trivial).

Registration comes first in this file (the seat, the rim, the
support, the pinned rule, the frozen exactness question, and
the receipts that the interior exists here and that the
support is what the scope says it is); the decision is the
section after it.
-/

namespace ThetLogos

/-- **The face at `Fin 5`**: the square `⟨0, 1, 2, 3⟩`, the
Vortex line's exhibit (`vortexSquareFace` at `Fin 4`, cited)
re-registered at this seat in `BridgeCompletion`'s dress. Its
boundary loop is `0 → 1 → 2 → 3 → 0`; vertex `4` is on no
edge of it. -/
def shapedRim5Face : GraphFace (Fin 5) :=
  ⟨0, 1, 2, 3⟩

/-- **The rim at `Fin 5`**: the square face's four vertices
`{0, 1, 2, 3}` — the boundary side of this seat. The pinned
rule fixes a potential here; the face-relative interior is
its complement, `{4}`. -/
def shapedRim5Rim : Finset (Fin 5) :=
  {0, 1, 2, 3}

/-- **The face/rim support at `Fin 5`**: the ordered pairs an
admissible field of this brick may use — the boundary loop's
edges in both directions (`0↔1`, `1↔2`, `2↔3`, `3↔0`, as
`edgeCirculation` reads the loop and its reverse) and the rim
crossings in both directions (each rim vertex against the
interior vertex `4`). Everything else is off-support: in
particular the interior diagonal `(4, 4)` — the exhibit that
decided F-1 at interior vertices is not admissible here — and
the non-loop rim pairs `(0, 2)`, `(1, 3)`. -/
def shapedRim5Support : Finset (Fin 5 × Fin 5) :=
  {(0, 1), (1, 0), (1, 2), (2, 1), (2, 3), (3, 2), (3, 0), (0, 3),
   (0, 4), (4, 0), (1, 4), (4, 1), (2, 4), (4, 2), (3, 4), (4, 3)}

/-- **A supported field**: an edge field at `Fin 5` vanishing
off the face/rim support. The restricted field class of this
brick — restricted, not emptied: it carries the loop units,
the swaps on loop edges, and the crossing units, as the
receipts and the decision section use them. -/
def shapedRim5Supported (X : Fin 5 → Fin 5 → ℝ) : Prop :=
  ∀ i j, (i, j) ∉ shapedRim5Support → X i j = 0

/-- **The pinned rule at `Fin 5`.** A potential's values on
the rim `{0, 1, 2, 3}` are fixed to the datum `φ₀`; its value
at the interior vertex `4` is constrained by nothing in the
rule. This asymmetry — rim fixed, interior free — is the
rule F-2 prices: the family it admits always has a free
interior coordinate, for every datum. (F-0's region-reading
rule is `shapedRim4Pinned`, cited; F-1 decided its
unrestricted form seat-generally.) -/
def shapedRim5Pinned (φ₀ φ : Fin 5 → ℝ) : Prop :=
  ∀ i ∈ shapedRim5Rim, φ i = φ₀ i

/-- **The restricted exactness question, frozen.** The datum
`φ₀` is exact at `Fin 5` if every pinned potential's pairing
(the seat-general pairing of F-1, `shapedRimGenPairing`,
cited) against every SUPPORTED field equals the unweighted
divergence pairing — no correction term, no weight, the
restriction doing whatever work is done. Registered as a
`Prop`; the decision section settles it. -/
def shapedRim5PinnedExact (φ₀ : Fin 5 → ℝ) : Prop :=
  ∀ φ, shapedRim5Pinned φ₀ φ → ∀ X, shapedRim5Supported X →
    shapedRimGenPairing φ X = ∑ i, φ i * diverge X i

/-- **The face-relative interior exists at `Fin 5`** — the
receipt F-0's disagreement theorem pointed at: vertex `4` is
off the rim, the rim together with `4` is the whole seat,
and the face's loop runs `0 → 1 → 2 → 3 → 0` over the rim
alone. A registration receipt (finite check): the seat this
brick's question needs is the seat it has. -/
theorem shapedRim5_interior_exists :
    (4 : Fin 5) ∉ shapedRim5Rim ∧ shapedRim5Rim ∪ {4} = Finset.univ
      ∧ shapedRim5Face.a = 0 ∧ shapedRim5Face.b = 1
      ∧ shapedRim5Face.c = 2 ∧ shapedRim5Face.d = 3 := by
  decide

/-- **The support is what the scope says it is** — receipts:
the crossings are admissible in both directions (`(4, 0)`,
`(0, 4)`), the loop's edges are admissible (`(0, 1)`,
`(3, 0)`), and the excluded pairs are excluded: the interior
diagonal `(4, 4)` (F-1's deciding exhibit, off-support here),
the rim diagonal `(0, 0)`, and the non-loop rim pairs
`(0, 2)`, `(1, 3)`. A registration receipt (finite check). -/
theorem shapedRim5Support_facts :
    (4, 0) ∈ shapedRim5Support ∧ (0, 4) ∈ shapedRim5Support
      ∧ (0, 1) ∈ shapedRim5Support ∧ (3, 0) ∈ shapedRim5Support
      ∧ (4, 4) ∉ shapedRim5Support ∧ (0, 0) ∉ shapedRim5Support
      ∧ (0, 2) ∉ shapedRim5Support ∧ (1, 3) ∉ shapedRim5Support := by
  decide

/-! ## F-2 — the restricted question, decided (this brick)

THE RESTRICTED QUESTION AT `Fin 5`, ANSWERED — AND THE ANSWER
IS NO, FOR EVERY DATUM. **K-RIM4-NONE fires in restricted
form**: no pinned datum makes the pairing exact over the
supported fields (`shapedRim5_no_pinned`).

The deciding exhibit is not the diagonal. The interior
diagonal `(4, 4)` is off the support — the restriction really
does exclude F-1's exhibit — and it is not needed, because
the rim's own crossings read the interior value directly.
The crossing unit `shapedRim5Cross 1` (one unit flowing from
the interior vertex `4` into the rim vertex `0`) is a
supported field, and against ANY potential its pairing is
`φ 0 − φ 4` while its divergence pairing is `φ 0`: exactness
at this one admissible pair forces `φ 4 = 0`
(`shapedRim5_exact_forces_interior_zero`). But the pinned
rule leaves the interior free — every pinned family contains
the potential with `φ 4 = 1` — so exactness fails for every
datum. The interior's freedom, the whole point of the seat,
is exactly what exactness would have to spend; the rim's
crossings force the interior value the rule refuses to fix.
This is the scope's named death mode for the restricted
question: the exhibits re-built inside the support, the
interior forced to zero by the rim's own crossings.

Two contrasts, stated so the verdict cannot be misread:

- **Against F-1.** There, the degenerate pinned seat (rim =
  the whole seat, datum = 0) WAS exact — vacuously, because
  its family was the single zero potential. Here the family
  is never a singleton: the interior coordinate is free under
  every datum, so **even the zero datum fails**
  (`shapedRim5F2Verdict`, third conjunct). The restriction did
  not merely fail to buy genuine content; it removed the one
  degenerate seat the unrestricted question had.
- **K-RIM4-TRIVIAL does not fire.** Exactness is not bought
  by a degenerate form — the zero potential, a constant
  weight, the correction re-injected, a trivial field class
  (the supported class is not trivial: it carries the loop
  units, the loop swaps, and the crossings). Exactness is not
  bought at all. The genuine-content criterion is therefore
  not engaged: there is no exact datum whose content could be
  audited.

What survives of the line is F-3's charge, unchanged: the
closing verdict assembly, and charge 4 — the Fin 3 verdict's
preservation citation beside `shapedRimVerdict`. The Fin 3
verdict, F-0's registrations, and F-1's seat-general kills
are preserved verbatim above and in `ShapedRimFourPin`;
nothing here restates or re-grades them. NO CLAIM; Dial 2
stays 0; no gravity object.
-/

/-- **The crossing exhibit**: `c` units flowing on the single
crossing edge `4 → 0` — from the interior vertex into the
rim — and zero elsewhere. A supported field for every `c`
(the support registration's receipt `(4, 0) ∈
shapedRim5Support` is its admissibility), and the restricted
question's deciding exhibit: the rim crossing that reads the
interior value. -/
def shapedRim5Cross (c : ℝ) : Fin 5 → Fin 5 → ℝ :=
  fun i j => if i = 4 ∧ j = 0 then c else 0

/-- The crossing exhibit is admissible: supported, for every
amplitude. Its only nonzero entry sits on the crossing
`(4, 0)`, which the support contains. -/
theorem shapedRim5Cross_supported (c : ℝ) :
    shapedRim5Supported (shapedRim5Cross c) := by
  intro i j hij
  by_cases h : i = 4 ∧ j = 0
  · exfalso
    obtain ⟨h1, h2⟩ := h
    subst h1
    subst h2
    exact hij (by decide)
  · show shapedRim5Cross c i j = 0
    unfold shapedRim5Cross
    exact if_neg h

/-- The crossing exhibit's pairing, against any potential:
the pairing reads the drop on the crossing edge — `c` times
`φ 0 − φ 4`, the rim value minus the INTERIOR value. The
interior value enters the pairing through the crossing,
which is the whole mechanism of this brick's verdict. -/
theorem shapedRim5Cross_pairing (φ : Fin 5 → ℝ) (c : ℝ) :
    shapedRimGenPairing φ (shapedRim5Cross c) = c * (φ 0 - φ 4) := by
  unfold shapedRimGenPairing
  have houter : (∑ i, ∑ j, dropVec φ i j * shapedRim5Cross c i j)
      = ∑ j, dropVec φ 4 j * shapedRim5Cross c 4 j := by
    apply Finset.sum_eq_single 4
    · intro b _ hb
      apply Finset.sum_eq_zero
      intro j _
      have hX : shapedRim5Cross c b j = 0 := by
        unfold shapedRim5Cross
        exact if_neg (fun hh => hb hh.1)
      rw [hX, mul_zero]
    · simp
  rw [houter]
  have hinner : (∑ j, dropVec φ 4 j * shapedRim5Cross c 4 j)
      = dropVec φ 4 0 * shapedRim5Cross c 4 0 := by
    apply Finset.sum_eq_single 0
    · intro b _ hb
      have hX : shapedRim5Cross c 4 b = 0 := by
        unfold shapedRim5Cross
        exact if_neg (fun hh => hb hh.2)
      rw [hX, mul_zero]
    · simp
  rw [hinner, dropVec_apply]
  have hX : shapedRim5Cross c 4 0 = c := by
    unfold shapedRim5Cross
    exact if_pos ⟨rfl, rfl⟩
  rw [hX]
  ring

/-- The crossing exhibit's divergence, vertex by vertex: `c`
at the rim vertex `0` it flows into, `0` elsewhere — in
particular `0` at the interior vertex `4`. The divergence
side of the identity never reads the interior value; the
pairing side does. That asymmetry is the obstruction. -/
theorem shapedRim5Cross_diverge (c : ℝ) (a : Fin 5) :
    diverge (shapedRim5Cross c) a = if a = 0 then c else 0 := by
  rw [diverge_apply]
  by_cases ha : a = 0
  · rw [ha, if_pos rfl]
    have hsum : (∑ j, shapedRim5Cross c j 0) = shapedRim5Cross c 4 0 := by
      apply Finset.sum_eq_single 4
      · intro b _ hb
        unfold shapedRim5Cross
        exact if_neg (fun hh => hb hh.1)
      · simp
    rw [hsum]
    unfold shapedRim5Cross
    exact if_pos ⟨rfl, rfl⟩
  · rw [if_neg ha]
    apply Finset.sum_eq_zero
    intro j _
    unfold shapedRim5Cross
    exact if_neg (fun hh => ha hh.2)

/-- The crossing exhibit's divergence pairing, against any
potential: `c * φ 0` — the rim value alone, read at the
vertex the crossing flows into. Beside
`shapedRim5Cross_pairing` (which reads `φ 0 − φ 4`), this is
the exactness equation of the restricted question at its
deciding pair. -/
theorem shapedRim5Cross_rhs (φ : Fin 5 → ℝ) (c : ℝ) :
    (∑ i, φ i * diverge (shapedRim5Cross c) i) = c * φ 0 := by
  have hsum : (∑ i, φ i * diverge (shapedRim5Cross c) i)
      = φ 0 * diverge (shapedRim5Cross c) 0 := by
    apply Finset.sum_eq_single 0
    · intro b _ hb
      rw [shapedRim5Cross_diverge, if_neg hb, mul_zero]
    · simp
  rw [hsum, shapedRim5Cross_diverge, if_pos rfl]
  ring

/-- **Exactness at the crossing exhibit forces the interior
value to zero** — for ANY potential, pinned or not. If a
potential's pairing against the crossing unit equals its
divergence pairing, then `φ 4 = 0`: the pairing reads
`φ 0 − φ 4`, the divergence side reads `φ 0`, and the two
agree only when the interior value vanishes. The mechanism
theorem of this brick: the rim's own crossings force the
interior value that the pinned rule leaves free. -/
theorem shapedRim5_exact_forces_interior_zero (φ : Fin 5 → ℝ)
    (h : shapedRimGenPairing φ (shapedRim5Cross 1)
      = ∑ i, φ i * diverge (shapedRim5Cross 1) i) : φ 4 = 0 := by
  rw [shapedRim5Cross_pairing, shapedRim5Cross_rhs] at h
  simp only [one_mul] at h
  linarith

/-- **K-RIM4-NONE — FIRED in restricted form at `Fin 5`.**
No datum makes the pinned family exact over the supported
fields. Whatever the datum, the family contains the
potential agreeing with it on the rim and taking the value
`1` at the free interior vertex; against the supported
crossing unit, exactness would force that value to `0` —
contradiction. The restriction buys nothing: the diagonal
exhibit is excluded by the support, and a crossing exhibit
inside the support does its work instead. -/
theorem shapedRim5_no_pinned (φ₀ : Fin 5 → ℝ) :
    ¬ shapedRim5PinnedExact φ₀ := by
  intro h
  have hpin : shapedRim5Pinned φ₀ (Function.update φ₀ 4 1) := by
    intro i hi
    have hi4 : i ≠ (4 : Fin 5) := by
      rintro rfl
      exact shapedRim5_interior_exists.1 hi
    rw [Function.update_of_ne hi4]
  have hzero := shapedRim5_exact_forces_interior_zero _
    (h _ hpin _ (shapedRim5Cross_supported 1))
  have h4 : Function.update φ₀ 4 1 4 = 1 :=
    Function.update_self 4 1 φ₀
  rw [h4] at hzero
  exact one_ne_zero hzero

/-- **F-2's verdict, assembled.** The restricted question at
`Fin 5`, in one statement: (1) no pinned datum is exact over
the supported fields — K-RIM4-NONE in restricted form; (2)
the mechanism: exactness at the supported crossing exhibit
forces the interior value to zero, for any potential; (3)
even the ZERO datum is not exact — the contrast with F-1,
whose degenerate pinned seat (whole-seat rim, zero datum)
was exact vacuously because its family was the single zero
potential. Here the interior coordinate is free under every
datum, the family is never emptied, and the restriction
removes the one degenerate seat the unrestricted question
had. What remains for F-3 is the closing assembly and
charge 4, the Fin 3 preservation citation. -/
theorem shapedRim5F2Verdict :
    (∀ φ₀ : Fin 5 → ℝ, ¬ shapedRim5PinnedExact φ₀)
      ∧ (∀ φ : Fin 5 → ℝ, shapedRimGenPairing φ (shapedRim5Cross 1)
          = ∑ i, φ i * diverge (shapedRim5Cross 1) i → φ 4 = 0)
      ∧ ¬ shapedRim5PinnedExact 0 :=
  ⟨shapedRim5_no_pinned,
   fun φ h => shapedRim5_exact_forces_interior_zero φ h,
   shapedRim5_no_pinned 0⟩

end ThetLogos
