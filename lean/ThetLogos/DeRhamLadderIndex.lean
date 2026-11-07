/-
# ThetLogos.DeRhamLadderIndex — LAD-3: the index at the seat

**WORKING LABEL — naming is Jeff's.** The Euler characteristic
of the icosidodecahedron computed BOTH ways, as theorems over
LAD-2's harmonic identifications and PHI-C3's landed census:

- the alternating sum of harmonic finranks (the cohomology
  side): `finrank ker Δ₀ − finrank ker Δ₁ + finrank ker Δ₂`;
- the alternating sum of cell counts (the chain side):
  `30 − 60 + 32`;

and the two are equal, both being `2`. Scoping:
`derham-ladder-scoping-2026-11-06.md` §4 (LAD-3). SP-4 (the
partner sector's `index_eq`) is the 2-term truncation of this
identity — the same theorem with the top degree amputated —
stated as a remark here, NOT re-proved (§6 of the scoping).
The general telescoping lemma over a finite-complex record is
LAD-5's, which is NOT fired and NOT built; this brick is the
seat-level identity, named at its seat (K-LAD-NAME (c)).

χ = 2 is a finite combinatorial invariant of this seat: it is
not a derived measured number, not a continuum statement, not
Dial evidence of any species (K-LAD-GRAV). NO CLAIM; dials
0/4; Dial 2 = 0.
-/

import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Tactic.NormNum
import ThetLogos.DeRhamLadderSupercharge

namespace ThetLogos
namespace DeRhamLadder

/-- LAD-3: the cohomology side of χ at the seat — the
    alternating sum of the harmonic (= cohomology) finranks
    is 2, from LAD-2's harmonic census (1, 0, 1). -/
theorem lad_chi_cohomology :
    (Module.finrank ℝ (LinearMap.ker ladLap0) : ℤ)
      - (Module.finrank ℝ (LinearMap.ker ladLap1) : ℤ)
      + (Module.finrank ℝ (LinearMap.ker ladLap2) : ℤ) = 2 := by
  obtain ⟨h0, h1, h2⟩ := lad_harmonic_census
  rw [h0, h1, h2]
  norm_num

/-- LAD-3: the chain side of χ at the seat — the alternating
    sum of cell counts is 2: 30 vertices − 60 edges + 32 faces,
    the PHI-C cell data (PHI-C0: `edgeList_length`,
    and the face count 32 = 20 triangles + 12 pentagons of the
    model's type-level data). -/
theorem lad_chi_cells : (30 : ℤ) - 60 + 32 = 2 := by norm_num

/-- LAD-3: **χ both ways at the icosidodecahedron** — the
    alternating harmonic sum EQUALS the alternating cell
    count. This is the index theorem at this seat in its full
    3-term form; the partner sector's SP-4 `index_eq`
    (`finrank ker H_v + #E = finrank ker H_e + #V`) is its
    2-term truncation, cited here as a remark, not re-proved. -/
theorem lad_chi_both_ways :
    (Module.finrank ℝ (LinearMap.ker ladLap0) : ℤ)
      - (Module.finrank ℝ (LinearMap.ker ladLap1) : ℤ)
      + (Module.finrank ℝ (LinearMap.ker ladLap2) : ℤ)
    = (30 : ℤ) - 60 + 32 := by
  rw [lad_chi_cohomology, lad_chi_cells]

/-- LAD-3: the Betti-number form — with `ker Δ₁ = 0` the
    identity reads `finrank ker Δ₀ + finrank ker Δ₂ = 2`,
    the sphere's `H⁰ ⊕ H²` count, as a single equation over
    the harmonic spaces. -/
theorem lad_chi_betti_form :
    Module.finrank ℝ (LinearMap.ker ladLap0)
      + Module.finrank ℝ (LinearMap.ker ladLap2) = 2 := by
  obtain ⟨h0, _, h2⟩ := lad_harmonic_census
  rw [h0, h2]

end DeRhamLadder
end ThetLogos
