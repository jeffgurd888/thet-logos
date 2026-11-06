import Mathlib.Tactic
import ThetLogos.WritingDirection
import ThetLogos.PlaneCrossingCube
import ThetLogos.LayerKernelPosSeatProbe

/-!
# ThetLogos.WritingDirectionCompass — WD-3: the compass exhibit (WORKING LABEL — naming is Jeff's)

HONESTY LEDGER (read before citing):

- WHAT THIS MODULE IS. WD-3 of the writing-direction layer
  (commission: Jeff, 2026-11-06 13:25 EST; scoping:
  `writing-direction-scoping-2026-11-06.md` §3.5; fired by
  Jeff's tap 2026-11-06 13:33 EST, "Fire the core plus the
  compass"). A GEOMETRY exhibit at the corpus's owned N = 2
  LayerCube seat, wearing the writing-direction pin. It proves
  things about a CUBE. **It claims NO writing content**: the
  compass is the direction SPACE — every direction at once,
  radiating from a center — while a written unit has ONE path.
  Collapsing the compass into the writing datum would be the
  category error the scoping refused on the record; this module
  exists so Jeff's two pictures have a proved home, not so the
  writing layer can borrow the cube's authority (K-WD-CREST).
- THE TWO PICTURES, WITH UNCERTAINTIES INTACT. Jeff's drawing
  (2026-11-06 13:19 EST): a circle with three axes crossing
  INSIDE it; six ends — Up / Down (vertical), Bwd (underlined) /
  Fwd (NW–SE diagonal), and the SW–NE diagonal's ends carrying
  circled glyphs, NE read as "L", SW read as "R" OR "P"
  (UNCERTAIN — not resolved here); at the right, a letter layout
  around a circled "+": "B", "U" above; "L", the circled plus,
  "R" in a row; "D" and an upward wedge/caret below (the
  wedge's role UNCERTAIN — not resolved here). Jeff's caption,
  verbatim: "I think that we are missing the up down Japanese
  style writing Chinese writing but a unified language writing
  model". The screenshot sent with the commission (Wikipedia,
  "Symbol of Chaos"): EIGHT arrows radiating from a center —
  Michael Moorcock's symbol (designed by Moorcock for his
  Eternal Champion books, drawn by Jim Cawthorn, first on an
  Elric cover, Science Fantasy, 1962; popularized through
  Warhammer and chaos magic). NOT Jeff's coinage, NOT program
  property. Jeff's own seeing over the eight-arrowed form
  (2026-11-01): "3 contained by 8".
- THE RECONCILIATION (elementary, and it is the whole content).
  The drawing's six directions — ±Up/Down, ±Fwd/Bwd, ±L/R — are
  the six FACE NORMALS of a cube: the signed directions of
  three axes (6 = 2·3). The emblem's eight, read in 3-D as
  Jeff's "3 contained by 8" already reads them, are the cube's
  eight VERTICES: the sign triples (±, ±, ±) (8 = 2^3). One cube
  carries both counts, and the corpus OWNS the cube: the
  LayerCube seat at N = 2 (`LayerSite 2`: the spatial cube
  `(ZMod 2)^3`, time coordinate pinned to 0) has exactly 8
  sites — LANDED, price 0 (`layerSite_card`,
  `LayerKernelPosSeatProbe.lean`). "3 contained by 8" is, at
  geometry grade, literally true of this seat: the three axes
  generate the eight vertices — a vertex IS a sign choice per
  axis, which is the equiv `compassEquiv` below. This is a
  reconciliation of Jeff's two drawings filed against an owned
  object — the cube was in the corpus before either drawing
  was sent; it is not a discovery, and the direction of
  authority runs from his drawings to the geometry's filing
  cabinet, never back (K-WD-EXACT / K-WD-CREST).
- THE FACE REMARK (honesty about the seat). At N = 2 the torus
  identifies the two signed steps along an axis: shifting by
  +1 and by −1 land on the same site (1 = −1 in `ZMod 2`). The
  six below are therefore face-normal LABELS of the geometric
  cube — signed axis directions as data — NOT six distinct
  torus steps. The counts are the cube's; the seat is a torus;
  both sentences are on this face so neither can be quoted
  without the other.
- KILLS. K-WD-EXACT guards the 2^3 reading: finite cube
  arithmetic only — it is not evidence about the emblem's
  meaning. K-WD-CREST: this exhibit is never authority for the
  writing layer's mathematics, nor is the writing layer
  authority for the drawings' meaning. K-WD-GRAV: nothing here
  is a gravity object, a response law, a derived number, a
  continuum statement, or Dial evidence. K-WD-NAME: the Chaos
  Star is never presented as program insignia or property.
- NO CLAIM; dials 0/4; Dial 2 = 0.
-/

namespace ThetLogos

/-! ## §1. The compass data at the N = 2 seat (DEFINITIONAL)

The axes are the seat's three spatial coordinates — indices
1, 2, 3 of the site function (index 0 is the time coordinate,
pinned to 0 by the seat's definition). A face direction is an
axis with a sign. The vertices are the seat's sites themselves. -/

/-- **A compass axis (DEFINITIONAL).** One of the three spatial
axes of the LayerCube seat: a coordinate index in `Fin 4` other
than the time coordinate 0. There are exactly 3 (proved in §2). -/
def CompassAxis : Type := {ν : Fin 4 // ν ≠ 0}

/-- **A compass face direction (DEFINITIONAL).** A signed axis:
an axis together with a sign (`Bool` as the sign label — `true`
for the positive sense, `false` for the negative). These are
the six face normals of the geometric cube, as LABELS (see the
header's face remark: at N = 2 the two signed torus steps along
an axis coincide; the six are directions of the cube, not six
distinct steps of the torus). There are exactly 6 (proved in
§2): 6 = 2·3, two signs over three axes. -/
def CompassFaceDir : Type := CompassAxis × Bool

/-- **A vertex read by its spatial coordinates
(DEFINITIONAL).** A site of the N = 2 seat, read at its three
spatial coordinates (indices 1, 2, 3) — the vertex as a sign
triple. Packaged as the equiv `compassEquiv` in §2: a vertex IS
a sign choice per axis, which is the exact content of "3
contained by 8" at this seat. -/
def compassCoord (c : LayerSite 2) : Fin 3 → ZMod 2 :=
  fun i => c.1 ⟨i.1 + 1, by omega⟩

/-- **Vertices ARE sign choices per axis (the axes-generate-
vertices content).** The spatial-coordinate read is an
equivalence between the seat's sites and the sign triples
`Fin 3 → ZMod 2`: every vertex is exactly a choice of sign
along each of the three axes, and every such choice is a
vertex. (The inverse rebuilds a site by pinning the time
coordinate to 0 — the seat's own membership condition.) -/
def compassEquiv : LayerSite 2 ≃ (Fin 3 → ZMod 2) where
  toFun := compassCoord
  invFun := fun s => ⟨fun j => if h : j = 0 then 0 else s ⟨j.1 - 1, by
    have hj : j.1 ≠ 0 := fun h0 => h (Fin.ext h0)
    omega⟩, by simp⟩
  left_inv := by
    intro c
    apply Subtype.ext
    funext j
    by_cases hj : j = 0
    · subst hj
      show (0 : ZMod 2) = c.1 0
      exact (layerSite_zero c).symm
    · have hj1 : j.1 ≠ 0 := fun h0 => hj (Fin.ext h0)
      simp only [dite_eq_right hj]
      show c.1 ⟨j.1 - 1 + 1, by omega⟩ = c.1 j
      have hidx : (⟨j.1 - 1 + 1, by omega⟩ : Fin 4) = j := by
        apply Fin.ext
        show j.1 - 1 + 1 = j.1
        omega
      exact congrArg c.1 hidx
  right_inv := by
    intro s
    funext i
    have hi : (⟨i.1 + 1, by omega⟩ : Fin 4) ≠ 0 := by
      intro h
      have := congrArg Fin.val h
      simp at this
    simp only [compassCoord, dite_eq_right hi]
    congr 1

/-- The three axes, counted. -/
instance : Fintype CompassAxis := Subtype.fintype _

/-- The six face directions, counted. -/
instance : Fintype CompassFaceDir := by
  unfold CompassFaceDir CompassAxis
  infer_instance

/-! ## §2. The counts, by decision

Finite combinatorics at the seat: 3 axes, 6 = 2·3 face
directions, 8 = 2^3 vertices. The 8 is the landed
`layerSite_card` (price 0, cited); the rest is `decide` over
the seat's finite types. -/

/-- **Three axes.** The compass has exactly 3 axes — the
seat's three spatial coordinates. -/
theorem compassAxis_card : Fintype.card CompassAxis = 3 := by decide

/-- **Six face directions: 6 = 2·3.** The drawing's six ends —
± of the three axes — counted at the seat. -/
theorem compassFaceDir_card : Fintype.card CompassFaceDir = 6 := by decide

/-- **The reconciliation, in one statement.** At the owned
N = 2 seat: the vertices number 8 = 2^3 (the landed
`layerSite_card`, cited at price 0), the face directions
number 6 = 2·3, and the axes number 3 — one cube carries the
drawing's six and the emblem's eight, generated by the same
three axes. GEOMETRY ONLY: this is a statement about the
cube, and it claims no writing content (see the header). -/
theorem compass_counts :
    Fintype.card (LayerSite 2) = 8 ∧ Fintype.card CompassFaceDir = 6 ∧
      Fintype.card CompassAxis = 3 :=
  ⟨layerSite_card, compassFaceDir_card, compassAxis_card⟩

end ThetLogos
