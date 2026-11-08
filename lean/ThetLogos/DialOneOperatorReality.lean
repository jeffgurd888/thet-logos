import Mathlib.Tactic
import ThetLogos.Scaffold32
import ThetLogos.FiniteSpectralTriple
import ThetLogos.DialOneGradeRConjPin

open Matrix
open ThetLogos.DialOneGradeRConjPin

namespace ThetLogos.DialOneOperatorReality

/-!
# ThetLogos.DialOneOperatorReality — ROPE BRIDGE brick (C1): the operator layer's reality, as named theorems

Working label only ("operator reality"); public naming is
Jeff's hand. Commissioned by Jeff, 2026-11-07 22:22 EST
("scope rope bridge build and run"); built to the statement
shapes of the ROPE BRIDGE scoping
(`rope-bridge-scope-2026-11-07.md`, §B (C1)), which is the
build's governing text. NO CLAIM; dials 0/4; Dial 1 = 0.

## What this brick is

The scoping's census (§A.1, §A.3) found that the reality
predicate `IsRealMat` (the Grade R pin's vocabulary: `Uᴴ = Uᵀ`)
lived only inside the Grade R module family, while the ℂ³²
seat's core operators were real BY CONSTRUCTION on their faces
with no named theorem saying so. This brick names the three:

* `gammaF_isRealMat` — the family gamma at the ℂ³² seat is
  real (its entries are in {0, ±1});
* `UJ_isRealMat` — the MATRIX of the real structure J is real
  (its entries are in {0, 1}). J itself is antilinear — a
  BRIDGE OBJECT in the census's vocabulary — and asking for
  `IsRealMat J` would be a species error; the real object is
  its matrix, and that is what is proved here;
* `DF_oneGen_isRealMat` — the one-generation Dirac operator
  is real at EVERY real Yukawa quadruple (exactly the
  generality of Grade R's clause (c), which quantifies over
  all real Yukawas): its blocks are the real diagonal Yukawa
  block A, A's entrywise conjugate (= A, the entries being
  real casts), and 0.

Value (per the scoping): gap (α)'s premise — "the class's
conditions reference real data" — was a reading supported by
the definitions; these theorems make the seat's operator
reality named T1 facts and export `IsRealMat` beyond its one
former wing. Registered kill **K-ROPE-OPREAL**: a single
nonreal entry in any of the three definitions. ARMED, NOT
FIRED — all three proofs are entrywise inspections of the
landed, frozen definitions; no definition was touched.
-/

/-- **Reality is entrywise**: a matrix satisfies the pin's
`IsRealMat` (`Mᴴ = Mᵀ`) iff every entry is star-fixed.
(Entry `i j` of `Mᴴ` is `star (M j i)`; entry `i j` of `Mᵀ`
is `M j i`.) -/
theorem isRealMat_of_forall_star {M : Matrix I32 I32 ℂ}
    (h : ∀ i j, star (M i j) = M i j) : IsRealMat M := by
  ext i j
  rw [Matrix.conjTranspose_apply, Matrix.transpose_apply]
  exact h j i

/-- **The family gamma is real** (T1): `gammaF`'s entries are
0 off the diagonal and ±1 on it — the range split on `i.val`
reads the defining if-chain directly. -/
theorem gammaF_isRealMat : IsRealMat gammaF := by
  apply isRealMat_of_forall_star
  intro i j
  by_cases h : i = j
  · subst h
    by_cases h1 : i.val < 8 <;> by_cases h2 : i.val < 16 <;>
      by_cases h3 : i.val < 24 <;> (unfold gammaF; simp [h1, h2, h3])
  · rw [gammaF_apply_ne h, star_zero]

/-- **The real structure's matrix is real** (T1): `UJ`'s
entries are the partner-permutation indicators, in {0, 1}.
This is the reality statement for J that is well-formed:
J itself is the antilinear bridge; `UJ` is its matrix. -/
theorem UJ_isRealMat : IsRealMat UJ := by
  apply isRealMat_of_forall_star
  intro i j
  rw [UJ_apply]
  unfold UJ_matrix
  split_ifs <;> simp

/-- The one-generation Yukawa diagonal's entries are real
casts — each of the eight entries of the vector in
`DF_oneGen`'s definition is `(Y : ℂ)` for a real `Y`. -/
theorem yukawaDiagVec_star (Ynu Ye Yu Yd : ℝ) (k : Fin 8) :
    star ((![(Ynu : ℂ), (Ye : ℂ), (Yu : ℂ), (Yd : ℂ),
      (Yu : ℂ), (Yd : ℂ), (Yu : ℂ), (Yd : ℂ)] : Fin 8 → ℂ) k)
    = (![(Ynu : ℂ), (Ye : ℂ), (Yu : ℂ), (Yd : ℂ),
      (Yu : ℂ), (Yd : ℂ), (Yu : ℂ), (Yd : ℂ)] : Fin 8 → ℂ) k := by
  fin_cases k <;> simp

/-- A diagonal matrix whose diagonal entries are star-fixed
is entrywise star-fixed (off-diagonal entries are 0). -/
theorem diagonal_star_fixed {v : Fin 8 → ℂ} (hv : ∀ k, star (v k) = v k)
    (x y : Fin 8) :
    star (Matrix.diagonal v x y) = Matrix.diagonal v x y := by
  rw [Matrix.diagonal_apply]
  split_ifs with h
  · exact hv x
  · simp

/-- **The one-generation Dirac operator is real at all real
Yukawas** (T1): `DF_oneGen Ynu Ye Yu Yd` is `buildDirac`
assembled from the real diagonal block `A`, `A`'s entrywise
conjugate (which is `A` again, entrywise, by
`yukawaDiagVec_star`), and the zero blocks — so every entry
of the assembled matrix is star-fixed. Proved by the
sixteen-region entry split on `buildDirac`'s placement
table, the same skeleton as the landed
`buildDirac_self_adjoint`. -/
theorem DF_oneGen_isRealMat (Ynu Ye Yu Yd : ℝ) :
    IsRealMat (DF_oneGen Ynu Ye Yu Yd) := by
  apply isRealMat_of_forall_star
  intro i j
  unfold DF_oneGen buildDirac
  simp only []
  by_cases H1 : i.val < 8
  · by_cases H2 : j.val < 8
    · simp [H1, H2]
    · by_cases H3 : j.val < 16
      · simp [H1, H2, H3, Matrix.conjTranspose_apply, Matrix.map_apply,
          diagonal_star_fixed (yukawaDiagVec_star Ynu Ye Yu Yd)]
      · by_cases H4 : j.val < 24
        · simp [H1, H2, H3, H4]
        · simp [H1, H2, H3, H4]
  · by_cases H5 : i.val < 16
    · by_cases H2 : j.val < 8
      · simp [H1, H5, H2, Matrix.conjTranspose_apply, Matrix.map_apply,
          diagonal_star_fixed (yukawaDiagVec_star Ynu Ye Yu Yd)]
      · by_cases H3 : j.val < 16
        · simp [H1, H5, H2, H3]
        · by_cases H4 : j.val < 24
          · simp [H1, H5, H2, H3, H4]
          · simp [H1, H5, H2, H3, H4, Matrix.conjTranspose_apply,
              Matrix.map_apply,
              diagonal_star_fixed (yukawaDiagVec_star Ynu Ye Yu Yd)]
    · by_cases H6 : i.val < 24
      · by_cases H2 : j.val < 8
        · simp [H1, H5, H6, H2]
        · by_cases H3 : j.val < 16
          · simp [H1, H5, H6, H2, H3]
          · by_cases H4 : j.val < 24
            · simp [H1, H5, H6, H2, H3, H4]
            · simp [H1, H5, H6, H2, H3, H4, Matrix.conjTranspose_apply,
                Matrix.map_apply, starRingEnd_apply,
                diagonal_star_fixed (yukawaDiagVec_star Ynu Ye Yu Yd),
                yukawaDiagVec_star Ynu Ye Yu Yd]
      · by_cases H2 : j.val < 8
        · simp [H1, H5, H6, H2]
        · by_cases H3 : j.val < 16
          · simp [H1, H5, H6, H2, H3, Matrix.conjTranspose_apply,
              Matrix.map_apply,
              diagonal_star_fixed (yukawaDiagVec_star Ynu Ye Yu Yd)]
          · by_cases H4 : j.val < 24
            · simp [H1, H5, H6, H2, H3, H4, Matrix.conjTranspose_apply,
                Matrix.map_apply, starRingEnd_apply,
                diagonal_star_fixed (yukawaDiagVec_star Ynu Ye Yu Yd),
                yukawaDiagVec_star Ynu Ye Yu Yd]
            · simp [H1, H5, H6, H2, H3, H4]

end ThetLogos.DialOneOperatorReality

-- Axiom audit for the three headlines (expected:
-- [propext, Classical.choice, Quot.sound] throughout).
#print axioms ThetLogos.DialOneOperatorReality.gammaF_isRealMat
#print axioms ThetLogos.DialOneOperatorReality.UJ_isRealMat
#print axioms ThetLogos.DialOneOperatorReality.DF_oneGen_isRealMat
