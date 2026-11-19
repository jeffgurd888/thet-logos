import Mathlib.Tactic
import Mathlib.Data.Finset.Prod

/-!
# ID-2 — boundary vocabulary on the subset seat (both forms)

## Standing

Zero's adjacency ruling (2026-11-10) is **Option C — ID-2 builds
BOTH boundary forms**: the vertex boundary (card form) and the
edge cut (weighted form), with one form named primary for the
Idensity definition at ID-3. ID-2 is **UNGATED** and enrolled
after ID-1 (landed: `ThetLogos.IdensityCoincidence`). The
adjacency is handed in as **declared input structure**
(`a : κ → κ → ℝ`); an adjacency as input is not itself a locality
hypothesis (H-3 stays Zero's separate open decision, untouched
by this brick).

## The discussion that brought it about

The ID scoping (`idensity-scope-2026-11-09.md`, §2.3) found the
Idensity denominator was the gap: the corpus's subset vocabulary
(H-1/H-2 region entropies) has **no boundary at all** — "a subset
`s` is any `Finset κ`, distinguished by nothing" — and the only
counting it performs is bulk. **K-IDENSITY-PROXY** is armed
against calling any bulk count "boundary volume". This brick is
the one new-vocabulary brick the scoping priced (ID-2, §6) so
that a genuine boundary measure exists: sites outside a region
adjacent to it, and the edges crossing its cut.

## Conventions carried on the face

- Orientation: the vertex boundary collects outside sites `x`
  with a nonzero adjacency `a x y` to some inside site `y`; the
  edge cut is oriented out of the region (`s ×ˢ (univ \ s)`).
  For a symmetric adjacency the orientations coincide in
  content; nothing here assumes symmetry.
- **Zero-boundary convention:** boundary volume CAN be zero
  here — `boundaryCard a univ = 0`, `boundaryCard a ∅ = 0`, both
  proved below. What the Idensity *ratio* does at a
  zero-boundary region (restrict the domain, or define by
  cases) is **Zero's pin, reserved to ID-3**, stated here so no
  later text can pretend the question away.

Dial-ineligible by pre-registration; NO CLAIM; dials 0/4.
-/

namespace ThetLogos

section VertexBoundary

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/- **The vertex boundary of a region** (Tier T2 — definition):
   the sites outside `s` adjacent (by a nonzero weight of the
   declared adjacency `a`) to some site inside `s`. The
   adjacency is input structure, declared, not derived. (Plain
   comment, not a docstring: a docstring cannot precede the
   `open Classical in` this filter definition needs.) -/
open Classical in
noncomputable def vertexBoundary (a : κ → κ → ℝ) (s : Finset κ) :
    Finset κ :=
  Finset.univ.filter (fun x => x ∉ s ∧ ∃ y ∈ s, a x y ≠ 0)

/-- Membership in the vertex boundary, by definition. -/
theorem mem_vertexBoundary {a : κ → κ → ℝ} {s : Finset κ} {x : κ} :
    x ∈ vertexBoundary a s ↔ x ∉ s ∧ ∃ y ∈ s, a x y ≠ 0 := by
  simp [vertexBoundary]

/-- The empty region has empty vertex boundary: nothing is
    inside to be adjacent to. -/
theorem vertexBoundary_empty (a : κ → κ → ℝ) :
    vertexBoundary a ∅ = ∅ := by
  ext x
  simp [vertexBoundary]

/-- The full region has empty vertex boundary: there is no
    outside. -/
theorem vertexBoundary_univ (a : κ → κ → ℝ) :
    vertexBoundary a Finset.univ = ∅ := by
  ext x
  simp [vertexBoundary]

/-- The vertex boundary is disjoint from its region, by
    construction. -/
theorem vertexBoundary_disjoint (a : κ → κ → ℝ) (s : Finset κ) :
    Disjoint (vertexBoundary a s) s := by
  rw [Finset.disjoint_left]
  intro x hx
  exact (mem_vertexBoundary.mp hx).1

/-- **Boundary volume, card form** (Tier T2 — definition): the
    number of boundary sites. This is the denominator form the
    vertex side of ruling C supplies. -/
noncomputable def boundaryCard (a : κ → κ → ℝ) (s : Finset κ) :
    ℕ :=
  (vertexBoundary a s).card

/-- Zero-boundary face, empty region: the boundary volume of
    `∅` is `0` (the convention question this raises for the
    ratio is Zero's ID-3 pin, on this module's header). -/
theorem boundaryCard_empty (a : κ → κ → ℝ) :
    boundaryCard a ∅ = 0 := by
  rw [boundaryCard, vertexBoundary_empty, Finset.card_empty]

/-- Zero-boundary face, full region: the boundary volume of
    `univ` is `0`. -/
theorem boundaryCard_univ (a : κ → κ → ℝ) :
    boundaryCard a Finset.univ = 0 := by
  rw [boundaryCard, vertexBoundary_univ, Finset.card_empty]

end VertexBoundary

section EdgeCut

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/- **The edge cut of a region** (Tier T2 — definition): the
   ordered pairs `(x, y)` with `x ∈ s`, `y ∉ s` and nonzero
   adjacency weight `a x y` — the edges crossing out of the
   region. Oriented out of `s`; for a symmetric adjacency this
   is the crossing set read once. (Plain comment, not a
   docstring: same `open Classical in` parse constraint as
   `vertexBoundary`.) -/
open Classical in
noncomputable def edgeCut (a : κ → κ → ℝ) (s : Finset κ) :
    Finset (κ × κ) :=
  (s ×ˢ (Finset.univ \ s)).filter (fun p => a p.1 p.2 ≠ 0)

/-- Membership in the edge cut, by definition. -/
theorem mem_edgeCut {a : κ → κ → ℝ} {s : Finset κ} {p : κ × κ} :
    p ∈ edgeCut a s ↔ p.1 ∈ s ∧ p.2 ∉ s ∧ a p.1 p.2 ≠ 0 := by
  simp only [edgeCut, Finset.mem_filter, Finset.mem_product,
    Finset.mem_sdiff, Finset.mem_univ, true_and, and_assoc]

/-- The empty region has an empty cut: no inside endpoint
    exists. -/
theorem edgeCut_empty (a : κ → κ → ℝ) :
    edgeCut a ∅ = ∅ := by
  simp [edgeCut]

/-- **Boundary volume, weighted form** (Tier T2 — definition):
    the total adjacency weight crossing the region's cut. This
    is the denominator form the weighted side of ruling C
    supplies. The raw sum is signed if the adjacency is; it is
    a weight under a nonnegative adjacency (proved below). -/
noncomputable def cutWeight (a : κ → κ → ℝ) (s : Finset κ) :
    ℝ :=
  ∑ p ∈ edgeCut a s, a p.1 p.2

/-- The empty region's cut weight is zero. -/
theorem cutWeight_empty (a : κ → κ → ℝ) :
    cutWeight a ∅ = 0 := by
  simp [cutWeight, edgeCut_empty]

/-- Under a nonnegative adjacency the cut weight is a genuine
    weight: nonnegative at every region. -/
theorem cutWeight_nonneg {a : κ → κ → ℝ} (ha : ∀ x y, 0 ≤ a x y)
    (s : Finset κ) :
    0 ≤ cutWeight a s :=
  Finset.sum_nonneg (fun p _ => ha p.1 p.2)

end EdgeCut

end ThetLogos
