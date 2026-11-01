import Mathlib.Tactic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import ThetLogos.FluxClassification
import ThetLogos.Census96Decoupling

open Matrix Finset

namespace ThetLogos.VortexLocusSeatA

/-!
# ThetLogos.VortexLocusSeatA — VL-1: the Seat A corollary

STATUS: T1 target — the Seat A dimension formula of the vortex-locus
scoping memo (`routeb-general-scratch/scoping-vortex-locus-2026-10-30.md`,
§2 Seat A and the VL-1 line of the firing order), banked as a corollary
brick. Source classification (landed T1, `FluxClassification.lean`):
`classification_diagModularK` — for `K = diagModularK w` and ANY `D`,
`modularFlux (diagModularK w) D = 0 ↔
  ∀ i j, Real.log (w i) ≠ Real.log (w j) → D i j = 0`.
The tree's statement matches the memo's description exactly: the
sectors are the level sets of `j ↦ Real.log (w j)`; no positivity on
`w` is assumed. No discrepancy found.

## The memo's verdict on Seat A, on the face (verbatim in substance)

A true theorem, but its entire content is the input partition. It is
not a discovery engine and is not the pin. (Seat B over the W₂₂ span
is the pin of that memo; nothing about it is stated or proved here.)

## What this brick proves

The locus at the diagonal seat — the real space of Hermitian
grading-odd matrices `X` on `I32` with
`modularFlux (diagModularK w) X = 0` — has real dimension

  `2 * ∑ c, p_c * m_c`,

the sum over the log-weight levels `c` (the fibres of
`j ↦ Real.log (w j)`), where `p_c` counts the level-`c` indices in
the `+` grading sector `P = {0..7} ∪ {24..31}` and `m_c` counts the
level-`c` indices in the `−` sector `M = {8..23}` (the corpus's
`gammaF = diag(+I₈, −I₈, −I₈, +I₈)` grading, via the landed folded
embeddings `plusEmb` / `minusEmb` of `Census96Decoupling`).
Each surviving cross-grading pair carries one free complex entry,
Hermiticity fixing the transpose; the proof is the coordinate
equivalence `vortexLocusEquiv` to the free complex coordinates on
the surviving pairs, plus fibre counting.

## Both K-VORTEX-1 ends, on the face

- **Zero end.** If no log-weight level straddles the grading (every
  level lies wholly in `P` or wholly in `M`, i.e. every
  `p_c * m_c = 0`), the locus is `{0}` (`vortexLocus_eq_bot_of_no_straddle`).
  In particular this fires for injective log-weights (generic `w`:
  32 distinct weights) (`vortexLocus_eq_bot_of_injective_logWeight`),
  and for the grading-aligned example: weights constant on each
  8-block with four distinct log-levels aligned to the blocks
  (`alignedWeights`: log-levels `0, 1, 2, 3` on the four blocks) —
  grading-aligned degeneracy buys nothing, the locus is again `{0}`
  (`vortexLocus_alignedWeights_eq_bot`). Only levels that straddle
  the grading produce middle values, and then the value is a direct
  read-off of the chosen partition: a level contributes iff it
  straddles (`contribution_ne_zero_iff_straddle`), and a straddling
  level forces positive dimension (`finrank_pos_of_straddle`).
- **Whole end.** At constant log-weights (the degenerate weight,
  one level, `p = m = 16`) the locus is the whole odd Hermitian
  space, of real dimension `512 = 2 * 16 * 16`
  (`vortexLocus_eq_oddHermitian_of_log_const`,
  `finrank_vortexLocus_const`). This end is the locus-side companion
  of the landed silence at constant weights
  (`NullStart.silent_iff_log_const` territory, cited in the memo).

## Fences (memo §5)

- NO CLAIM: nothing here touches any Millennium statement; no dial
  moves on any outcome.
- The objects are named as what they are: a commutator condition,
  its kernel inside the Hermitian grading-odd space — a centralizer
  section. "Vortex", "hydrodynamic flow", "circulation" are Jeff's
  T5 vocabulary and appear in this module only in this quotation,
  attributed to him; no statement below uses them.
- The locus is where the flux is ZERO — the silent sector at this
  diagonal seat. This is not a flow result, not a stability result
  in any dynamical sense, and not evidence for a hydrodynamic
  reading of the corpus.
- No W₂₂ content (that is VL-2/VL-3's); no Seat C formulation
  (K-VORTEX-3: a self-referential seat is void on sight).
- Finite level only: matrices over `I32 → ℂ`, the corpus's built
  `diagModularK`. No continuum statement.
-/

/-- The log-weight of an index: `Real.log (w j)`, the fibre
    coordinate of the classification at `diagModularK w` (its
    eigenvalues are `-log (w j)`). Tier T2. -/
noncomputable def logWeight (w : I32 → ℝ) (j : I32) : ℝ := Real.log (w j)

/-- The log-weight levels of `w`: the image of `logWeight w` over
    all 32 indices — the level sets `c` of the memo's formula are
    the fibres over these values. Tier T2. -/
noncomputable def levels (w : I32 → ℝ) : Finset ℝ := Finset.univ.image (logWeight w)

/-- `p_c`: the number of level-`c` indices in the `+` grading
    sector, counted in folded coordinates via `plusEmb`
    (`Fin 16 → I32`, image exactly `P = {0..7} ∪ {24..31}`). -/
noncomputable def plusCount (w : I32 → ℝ) (c : ℝ) : ℕ :=
  (Finset.univ.filter (fun a : Fin 16 => logWeight w (plusEmb a) = c)).card

/-- `m_c`: the number of level-`c` indices in the `−` grading
    sector, counted via `minusEmb` (image exactly
    `M = {8..23}`). -/
noncomputable def minusCount (w : I32 → ℝ) (c : ℝ) : ℕ :=
  (Finset.univ.filter (fun b : Fin 16 => logWeight w (minusEmb b) = c)).card

/-- The surviving cross-grading pairs at weight `w`: pairs
    `(a, b)` of folded plus/minus coordinates whose log-weights
    agree. One free complex locus entry lives on each such pair. -/
abbrev crossPair (w : I32 → ℝ) : Type :=
  { p : Fin 16 × Fin 16 //
    logWeight w (plusEmb p.1) = logWeight w (minusEmb p.2) }

noncomputable instance (w : I32 → ℝ) : Fintype (crossPair w) := by
  classical
  exact Subtype.fintype _

/-- The full Hermitian grading-odd space on `I32`: the ambient
    D-space (i) of the memo at Seat A. A real submodule of the
    complex matrices. Tier T2. -/
def oddHermitianSpace : Submodule ℝ (Matrix I32 I32 ℂ) where
  carrier := {X | X.IsHermitian ∧ gammaF * X + X * gammaF = 0}
  add_mem' := by
    intro X Y hX hY
    obtain ⟨hX1, hX2⟩ := hX
    obtain ⟨hY1, hY2⟩ := hY
    refine ⟨?_, ?_⟩
    · show (X + Y).conjTranspose = X + Y
      rw [Matrix.conjTranspose_add, hX1.eq, hY1.eq]
    · show gammaF * (X + Y) + (X + Y) * gammaF = 0
      rw [Matrix.mul_add, Matrix.add_mul]
      have h3 : (gammaF * X + gammaF * Y) + (X * gammaF + Y * gammaF)
          = (gammaF * X + X * gammaF) + (gammaF * Y + Y * gammaF) := by
        ac_rfl
      rw [h3, hX2, hY2, add_zero]
  zero_mem' := by
    refine ⟨?_, ?_⟩
    · show (0 : Matrix I32 I32 ℂ).conjTranspose = 0; simp
    · show gammaF * (0 : Matrix I32 I32 ℂ) + (0 : Matrix I32 I32 ℂ)
        * gammaF = 0; simp
  smul_mem' := by
    intro c X hX
    obtain ⟨hX1, hX2⟩ := hX
    refine ⟨?_, ?_⟩
    · have hS : (c • X).conjTranspose = c • X.conjTranspose := by
        ext i j
        have e1 : ((c • X) j i) = c • (X j i) := rfl
        have e2 : ((c • X.conjTranspose) i j) = c • (X.conjTranspose i j) :=
          rfl
        rw [Matrix.conjTranspose_apply, e1, census96_star_real_smul, e2,
          Matrix.conjTranspose_apply]
      show (c • X).conjTranspose = c • X
      rw [hS, hX1.eq]
    · have hG : gammaF * (c • X) + (c • X) * gammaF
          = c • (gammaF * X + X * gammaF) := by
        rw [Matrix.mul_smul, Matrix.smul_mul, ← smul_add]
      show gammaF * (c • X) + (c • X) * gammaF = 0
      rw [hG, hX2, smul_zero]

/-- **The Seat A locus** (Tier T2 — definition): the centralizer
    section at the diagonal seat — Hermitian grading-odd matrices
    whose modular flux at the built `K = diagModularK w` vanishes.
    A real submodule of the complex matrices. -/
def vortexLocus (w : I32 → ℝ) : Submodule ℝ (Matrix I32 I32 ℂ) where
  carrier := {X | X.IsHermitian ∧ gammaF * X + X * gammaF = 0 ∧
    modularFlux (diagModularK w) X = 0}
  add_mem' := by
    intro X Y hX hY
    obtain ⟨hX1, hX2, hX3⟩ := hX
    obtain ⟨hY1, hY2, hY3⟩ := hY
    refine ⟨?_, ?_, ?_⟩
    · show (X + Y).conjTranspose = X + Y
      rw [Matrix.conjTranspose_add, hX1.eq, hY1.eq]
    · show gammaF * (X + Y) + (X + Y) * gammaF = 0
      rw [Matrix.mul_add, Matrix.add_mul]
      have h3 : (gammaF * X + gammaF * Y) + (X * gammaF + Y * gammaF)
          = (gammaF * X + X * gammaF) + (gammaF * Y + Y * gammaF) := by
        ac_rfl
      rw [h3, hX2, hY2, add_zero]
    · have hXc := (FluxClassification.classification_diagModularK w X).mp hX3
      have hYc := (FluxClassification.classification_diagModularK w Y).mp hY3
      rw [FluxClassification.classification_diagModularK]
      intro i j hij
      have e : (X + Y) i j = X i j + Y i j := Matrix.add_apply X Y i j
      rw [e, hXc i j hij, hYc i j hij, add_zero]
  zero_mem' := by
    refine ⟨?_, ?_, ?_⟩
    · show (0 : Matrix I32 I32 ℂ).conjTranspose = 0; simp
    · show gammaF * (0 : Matrix I32 I32 ℂ) + (0 : Matrix I32 I32 ℂ)
        * gammaF = 0; simp
    · show modularFlux (diagModularK w) (0 : Matrix I32 I32 ℂ) = 0
      rw [FluxClassification.classification_diagModularK]
      intro i j _
      rfl
  smul_mem' := by
    intro c X hX
    obtain ⟨hX1, hX2, hX3⟩ := hX
    refine ⟨?_, ?_, ?_⟩
    · have hS : (c • X).conjTranspose = c • X.conjTranspose := by
        ext i j
        have e1 : ((c • X) j i) = c • (X j i) := rfl
        have e2 : ((c • X.conjTranspose) i j) = c • (X.conjTranspose i j) :=
          rfl
        rw [Matrix.conjTranspose_apply, e1, census96_star_real_smul, e2,
          Matrix.conjTranspose_apply]
      show (c • X).conjTranspose = c • X
      rw [hS, hX1.eq]
    · have hG : gammaF * (c • X) + (c • X) * gammaF
          = c • (gammaF * X + X * gammaF) := by
        rw [Matrix.mul_smul, Matrix.smul_mul, ← smul_add]
      show gammaF * (c • X) + (c • X) * gammaF = 0
      rw [hG, hX2, smul_zero]
    · have hXc := (FluxClassification.classification_diagModularK w X).mp hX3
      rw [FluxClassification.classification_diagModularK]
      intro i j hij
      have e : (c • X) i j = c • (X i j) := rfl
      rw [e, hXc i j hij, smul_zero]

/-- Membership in the locus, unpacked (the classification form):
    Hermitian, grading-odd, and no entries between distinct
    log-weight levels. This is `classification_diagModularK`
    restated at the locus. -/
theorem mem_vortexLocus_iff (w : I32 → ℝ) (X : Matrix I32 I32 ℂ) :
    X ∈ vortexLocus w ↔ X.IsHermitian ∧ gammaF * X + X * gammaF = 0 ∧
      ∀ i j, logWeight w i ≠ logWeight w j → X i j = 0 := by
  constructor
  · intro h
    obtain ⟨h1, h2, h3⟩ := h
    refine ⟨h1, h2, ?_⟩
    have hc := (FluxClassification.classification_diagModularK w X).mp h3
    intro i j hij
    exact hc i j hij
  · intro h
    obtain ⟨h1, h2, h3⟩ := h
    refine ⟨h1, h2, ?_⟩
    rw [FluxClassification.classification_diagModularK]
    intro i j hij
    exact h3 i j hij

/-- Assembly of a locus matrix from free complex coordinates on
    the surviving cross-grading pairs: the `(+, −)` block is the
    coordinate, the `(−, +)` block is its conjugate transpose, all
    other entries vanish. Tier T2. -/
noncomputable def blockMatOf (w : I32 → ℝ) (f : crossPair w → ℂ) :
    Matrix I32 I32 ℂ := fun i j =>
  if hi : gSign i = 1 then
    if hj : gSign j = 1 then 0
    else if h : logWeight w i = logWeight w j then
      f ⟨(acoord i, flip8 (acoord j)), by
        have hjm : gSign j = -1 :=
          (gSign_eq_one_or_neg_one j).resolve_left hj
        show logWeight w (plusEmb (acoord i))
          = logWeight w (minusEmb (flip8 (acoord j)))
        rw [plusEmb_acoord_of_gSign_eq_one hi,
          minusEmb_flip8_acoord_of_gSign_eq_neg_one hjm]
        exact h⟩
    else 0
  else if hj : gSign j = 1 then
    if h : logWeight w i = logWeight w j then
      star (f ⟨(acoord j, flip8 (acoord i)), by
        have him : gSign i = -1 :=
          (gSign_eq_one_or_neg_one i).resolve_left hi
        show logWeight w (plusEmb (acoord j))
          = logWeight w (minusEmb (flip8 (acoord i)))
        rw [plusEmb_acoord_of_gSign_eq_one hj,
          minusEmb_flip8_acoord_of_gSign_eq_neg_one him]
        exact h.symm⟩)
    else 0
  else 0

theorem blockMatOf_apply (w : I32 → ℝ) (f : crossPair w → ℂ)
    (i j : I32) :
    blockMatOf w f i j =
      if hi : gSign i = 1 then
        if hj : gSign j = 1 then 0
        else if h : logWeight w i = logWeight w j then
          f ⟨(acoord i, flip8 (acoord j)), by
            have hjm : gSign j = -1 :=
              (gSign_eq_one_or_neg_one j).resolve_left hj
            show logWeight w (plusEmb (acoord i))
              = logWeight w (minusEmb (flip8 (acoord j)))
            rw [plusEmb_acoord_of_gSign_eq_one hi,
              minusEmb_flip8_acoord_of_gSign_eq_neg_one hjm]
            exact h⟩
        else 0
      else if hj : gSign j = 1 then
        if h : logWeight w i = logWeight w j then
          star (f ⟨(acoord j, flip8 (acoord i)), by
            have him : gSign i = -1 :=
              (gSign_eq_one_or_neg_one i).resolve_left hi
            show logWeight w (plusEmb (acoord j))
              = logWeight w (minusEmb (flip8 (acoord i)))
            rw [plusEmb_acoord_of_gSign_eq_one hj,
              minusEmb_flip8_acoord_of_gSign_eq_neg_one him]
            exact h.symm⟩)
        else 0
      else 0 := rfl

/-- The assembled matrix lies in the locus: it is Hermitian (the
    `(−, +)` block is the conjugate of the `(+, −)` coordinate),
    grading-odd (same-sign blocks vanish, so the anticommutator
    entry `(gSign i + gSign j) * X i j` is always `0`), and its
    flux vanishes by the classification (entries between distinct
    log-weight levels vanish by construction). -/
theorem blockMatOf_mem_vortexLocus (w : I32 → ℝ) (f : crossPair w → ℂ) :
    blockMatOf w f ∈ vortexLocus w := by
  rw [mem_vortexLocus_iff]
  refine ⟨?_, ?_, ?_⟩
  · -- Hermitian
    show (blockMatOf w f).conjTranspose = blockMatOf w f
    ext i j
    rw [Matrix.conjTranspose_apply]
    rcases gSign_eq_one_or_neg_one i with hi | hi <;>
      rcases gSign_eq_one_or_neg_one j with hj | hj
    · have h1 : blockMatOf w f i j = 0 := by
        rw [blockMatOf_apply, dif_pos hi, dif_pos hj]
      have h2 : blockMatOf w f j i = 0 := by
        rw [blockMatOf_apply, dif_pos hj, dif_pos hi]
      rw [h1, h2, star_zero]
    · by_cases hlog : logWeight w i = logWeight w j
      · have h1 : blockMatOf w f j i
            = star (f ⟨(acoord i, flip8 (acoord j)),
                by
                  have hjm : gSign j = -1 := hj
                  show logWeight w (plusEmb (acoord i))
                    = logWeight w (minusEmb (flip8 (acoord j)))
                  rw [plusEmb_acoord_of_gSign_eq_one hi,
                    minusEmb_flip8_acoord_of_gSign_eq_neg_one hjm]
                  exact hlog⟩) := by
          rw [blockMatOf_apply, dif_neg (by rw [hj]; norm_num),
            dif_pos hi, dif_pos hlog.symm]
        have h2 : blockMatOf w f i j
            = f ⟨(acoord i, flip8 (acoord j)),
                by
                  have hjm : gSign j = -1 := hj
                  show logWeight w (plusEmb (acoord i))
                    = logWeight w (minusEmb (flip8 (acoord j)))
                  rw [plusEmb_acoord_of_gSign_eq_one hi,
                    minusEmb_flip8_acoord_of_gSign_eq_neg_one hjm]
                  exact hlog⟩ := by
          rw [blockMatOf_apply, dif_pos hi, dif_neg (by rw [hj]; norm_num),
            dif_pos hlog]
        rw [h1, h2, star_star]
      · have h1 : blockMatOf w f i j = 0 := by
          rw [blockMatOf_apply, dif_pos hi, dif_neg (by rw [hj]; norm_num),
            dif_neg hlog]
        have h2 : blockMatOf w f j i = 0 := by
          rw [blockMatOf_apply, dif_neg (by rw [hj]; norm_num), dif_pos hi,
            dif_neg (fun h => hlog h.symm)]
        rw [h1, h2, star_zero]
    · by_cases hlog : logWeight w i = logWeight w j
      · have h1 : blockMatOf w f i j
            = star (f ⟨(acoord j, flip8 (acoord i)),
                by
                  have him : gSign i = -1 := hi
                  show logWeight w (plusEmb (acoord j))
                    = logWeight w (minusEmb (flip8 (acoord i)))
                  rw [plusEmb_acoord_of_gSign_eq_one hj,
                    minusEmb_flip8_acoord_of_gSign_eq_neg_one him]
                  exact hlog.symm⟩) := by
          rw [blockMatOf_apply, dif_neg (by rw [hi]; norm_num),
            dif_pos hj, dif_pos hlog]
        have h2 : blockMatOf w f j i
            = f ⟨(acoord j, flip8 (acoord i)),
                by
                  have him : gSign i = -1 := hi
                  show logWeight w (plusEmb (acoord j))
                    = logWeight w (minusEmb (flip8 (acoord i)))
                  rw [plusEmb_acoord_of_gSign_eq_one hj,
                    minusEmb_flip8_acoord_of_gSign_eq_neg_one him]
                  exact hlog.symm⟩ := by
          rw [blockMatOf_apply, dif_pos hj, dif_neg (by rw [hi]; norm_num),
            dif_pos hlog.symm]
        rw [h1, h2]
      · have h1 : blockMatOf w f i j = 0 := by
          rw [blockMatOf_apply, dif_neg (by rw [hi]; norm_num), dif_pos hj,
            dif_neg hlog]
        have h2 : blockMatOf w f j i = 0 := by
          rw [blockMatOf_apply, dif_pos hj, dif_neg (by rw [hi]; norm_num),
            dif_neg (fun h => hlog h.symm)]
        rw [h1, h2, star_zero]
    · have h1 : blockMatOf w f i j = 0 := by
        rw [blockMatOf_apply, dif_neg (by rw [hi]; norm_num),
          dif_neg (by rw [hj]; norm_num)]
      have h2 : blockMatOf w f j i = 0 := by
        rw [blockMatOf_apply, dif_neg (by rw [hj]; norm_num),
          dif_neg (by rw [hi]; norm_num)]
      rw [h1, h2, star_zero]
  · -- grading-odd
    ext i j
    have he : (gammaF * blockMatOf w f + blockMatOf w f * gammaF) i j
        = gSign i * blockMatOf w f i j
          + blockMatOf w f i j * gSign j := by
      rw [Matrix.add_apply, gammaF_mul_apply, mul_gammaF_apply]
      rfl
    rw [he, Matrix.zero_apply]
    rcases gSign_eq_one_or_neg_one i with hi | hi <;>
      rcases gSign_eq_one_or_neg_one j with hj | hj
    · have h0 : blockMatOf w f i j = 0 := by
        rw [blockMatOf_apply, dif_pos hi, dif_pos hj]
      rw [h0, mul_zero, zero_mul, add_zero]
    · rw [hi, hj]; ring
    · rw [hi, hj]; ring
    · have h0 : blockMatOf w f i j = 0 := by
        rw [blockMatOf_apply, dif_neg (by rw [hi]; norm_num),
          dif_neg (by rw [hj]; norm_num)]
      rw [h0, mul_zero, zero_mul, add_zero]
  · -- no entries between distinct log-weight levels
    intro i j hij
    rcases gSign_eq_one_or_neg_one i with hi | hi <;>
      rcases gSign_eq_one_or_neg_one j with hj | hj
    · rw [blockMatOf_apply, dif_pos hi, dif_pos hj]
    · rw [blockMatOf_apply, dif_pos hi, dif_neg (by rw [hj]; norm_num),
        dif_neg hij]
    · rw [blockMatOf_apply, dif_neg (by rw [hi]; norm_num), dif_pos hj,
        dif_neg hij]
    · rw [blockMatOf_apply, dif_neg (by rw [hi]; norm_num),
        dif_neg (by rw [hj]; norm_num)]

/-- The coordinate read-off: the entry of `X` at a surviving
    cross-grading pair. Tier T2. -/
def coordOf (w : I32 → ℝ) (X : Matrix I32 I32 ℂ) (p : crossPair w) :
    ℂ :=
  X (plusEmb p.1.1) (minusEmb p.1.2)

/-- The coordinate extraction map: a locus matrix is read off at
    its surviving `(+, −)` entries. Tier T2. -/
def coordMap (w : I32 → ℝ) :
    vortexLocus w →ₗ[ℝ] (crossPair w → ℂ) where
  toFun := fun X p => coordOf w X.1 p
  map_add' := by
    intro X Y
    funext p
    rfl
  map_smul' := by
    intro c X
    funext p
    rfl

private theorem blockMatOf_add (w : I32 → ℝ) (f g : crossPair w → ℂ) :
    blockMatOf w (f + g) = blockMatOf w f + blockMatOf w g := by
  ext i j
  rw [Matrix.add_apply]
  rcases gSign_eq_one_or_neg_one i with hi | hi <;>
    rcases gSign_eq_one_or_neg_one j with hj | hj
  · rw [blockMatOf_apply, dif_pos hi, dif_pos hj,
      blockMatOf_apply, dif_pos hi, dif_pos hj,
      blockMatOf_apply, dif_pos hi, dif_pos hj, add_zero]
  · by_cases hlog : logWeight w i = logWeight w j
    · rw [blockMatOf_apply, dif_pos hi, dif_neg (by rw [hj]; norm_num),
        dif_pos hlog, blockMatOf_apply, dif_pos hi,
        dif_neg (by rw [hj]; norm_num), dif_pos hlog,
        blockMatOf_apply, dif_pos hi, dif_neg (by rw [hj]; norm_num),
        dif_pos hlog, Pi.add_apply]
    · rw [blockMatOf_apply, dif_pos hi, dif_neg (by rw [hj]; norm_num),
        dif_neg hlog, blockMatOf_apply, dif_pos hi,
        dif_neg (by rw [hj]; norm_num), dif_neg hlog,
        blockMatOf_apply, dif_pos hi, dif_neg (by rw [hj]; norm_num),
        dif_neg hlog, add_zero]
  · by_cases hlog : logWeight w i = logWeight w j
    · rw [blockMatOf_apply, dif_neg (by rw [hi]; norm_num), dif_pos hj,
        dif_pos hlog, blockMatOf_apply, dif_neg (by rw [hi]; norm_num),
        dif_pos hj, dif_pos hlog, blockMatOf_apply,
        dif_neg (by rw [hi]; norm_num), dif_pos hj, dif_pos hlog,
        Pi.add_apply, star_add]
    · rw [blockMatOf_apply, dif_neg (by rw [hi]; norm_num), dif_pos hj,
        dif_neg hlog, blockMatOf_apply, dif_neg (by rw [hi]; norm_num),
        dif_pos hj, dif_neg hlog, blockMatOf_apply,
        dif_neg (by rw [hi]; norm_num), dif_pos hj, dif_neg hlog,
        add_zero]
  · rw [blockMatOf_apply, dif_neg (by rw [hi]; norm_num),
      dif_neg (by rw [hj]; norm_num), blockMatOf_apply,
      dif_neg (by rw [hi]; norm_num), dif_neg (by rw [hj]; norm_num),
      blockMatOf_apply, dif_neg (by rw [hi]; norm_num),
      dif_neg (by rw [hj]; norm_num), add_zero]

private theorem blockMatOf_smul (w : I32 → ℝ) (c : ℝ)
    (f : crossPair w → ℂ) :
    blockMatOf w (c • f) = c • blockMatOf w f := by
  ext i j
  have e : (c • blockMatOf w f) i j = c • (blockMatOf w f i j) := rfl
  rw [e]
  rcases gSign_eq_one_or_neg_one i with hi | hi <;>
    rcases gSign_eq_one_or_neg_one j with hj | hj
  · rw [blockMatOf_apply, dif_pos hi, dif_pos hj,
      blockMatOf_apply, dif_pos hi, dif_pos hj, smul_zero]
  · by_cases hlog : logWeight w i = logWeight w j
    · rw [blockMatOf_apply, dif_pos hi, dif_neg (by rw [hj]; norm_num),
        dif_pos hlog, blockMatOf_apply, dif_pos hi,
        dif_neg (by rw [hj]; norm_num), dif_pos hlog, Pi.smul_apply]
    · rw [blockMatOf_apply, dif_pos hi, dif_neg (by rw [hj]; norm_num),
        dif_neg hlog, blockMatOf_apply, dif_pos hi,
        dif_neg (by rw [hj]; norm_num), dif_neg hlog, smul_zero]
  · by_cases hlog : logWeight w i = logWeight w j
    · rw [blockMatOf_apply, dif_neg (by rw [hi]; norm_num), dif_pos hj,
        dif_pos hlog, blockMatOf_apply, dif_neg (by rw [hi]; norm_num),
        dif_pos hj, dif_pos hlog, Pi.smul_apply,
        census96_star_real_smul]
    · rw [blockMatOf_apply, dif_neg (by rw [hi]; norm_num), dif_pos hj,
        dif_neg hlog, blockMatOf_apply, dif_neg (by rw [hi]; norm_num),
        dif_pos hj, dif_neg hlog, smul_zero]
  · rw [blockMatOf_apply, dif_neg (by rw [hi]; norm_num),
      dif_neg (by rw [hj]; norm_num), blockMatOf_apply,
      dif_neg (by rw [hi]; norm_num), dif_neg (by rw [hj]; norm_num),
      smul_zero]

/-- The assembly map, as a real-linear map into the locus. -/
noncomputable def blockMap (w : I32 → ℝ) :
    (crossPair w → ℂ) →ₗ[ℝ] vortexLocus w where
  toFun := fun f => ⟨blockMatOf w f, blockMatOf_mem_vortexLocus w f⟩
  map_add' := by
    intro f g
    apply Subtype.ext
    show blockMatOf w (f + g) = blockMatOf w f + blockMatOf w g
    exact blockMatOf_add w f g
  map_smul' := by
    intro c f
    apply Subtype.ext
    show blockMatOf w (c • f) = c • blockMatOf w f
    exact blockMatOf_smul w c f

/-- Extraction after assembly is the identity: the assembled
    matrix's `(+, −)` entry at `(plusEmb a, minusEmb b)` is the
    coordinate `f ⟨(a, b), _⟩` itself (folded coordinates recover
    via `acoord_plusEmb`, `acoord_minusEmb`, `flip8_flip8`). -/
theorem coordMap_blockMap (w : I32 → ℝ) (f : crossPair w → ℂ) :
    coordMap w (blockMap w f) = f := by
  funext p
  show blockMatOf w f (plusEmb p.1.1) (minusEmb p.1.2) = f p
  have h1 : blockMatOf w f (plusEmb p.1.1) (minusEmb p.1.2)
      = f ⟨(acoord (plusEmb p.1.1), flip8 (acoord (minusEmb p.1.2))),
          by
            have hjm : gSign (minusEmb p.1.2) = -1 := gSign_minusEmb _
            show logWeight w (plusEmb (acoord (plusEmb p.1.1)))
              = logWeight w (minusEmb (flip8 (acoord (minusEmb p.1.2))))
            rw [plusEmb_acoord_of_gSign_eq_one (gSign_plusEmb _),
              minusEmb_flip8_acoord_of_gSign_eq_neg_one hjm]
            exact p.2⟩ := by
    rw [blockMatOf_apply, dif_pos (gSign_plusEmb _),
      dif_neg (by rw [gSign_minusEmb]; norm_num), dif_pos p.2]
  rw [h1]
  have hp : (⟨(acoord (plusEmb p.1.1), flip8 (acoord (minusEmb p.1.2))),
      by
        have hjm : gSign (minusEmb p.1.2) = -1 := gSign_minusEmb _
        show logWeight w (plusEmb (acoord (plusEmb p.1.1)))
          = logWeight w (minusEmb (flip8 (acoord (minusEmb p.1.2))))
        rw [plusEmb_acoord_of_gSign_eq_one (gSign_plusEmb _),
          minusEmb_flip8_acoord_of_gSign_eq_neg_one hjm]
        exact p.2⟩ : crossPair w) = p := by
    apply Subtype.ext
    show (acoord (plusEmb p.1.1), flip8 (acoord (minusEmb p.1.2))) = p.1
    rw [acoord_plusEmb, acoord_minusEmb, flip8_flip8]
  rw [hp]

/-- Assembly after extraction is the identity: a locus matrix is
    rebuilt from its surviving `(+, −)` entries — same-sign entries
    vanish by grading-oddness, cross-level entries vanish by the
    classification, and the `(−, +)` block is the conjugate
    transpose by Hermiticity. -/
theorem blockMap_coordMap (w : I32 → ℝ) (X : vortexLocus w) :
    blockMap w (coordMap w X) = X := by
  obtain ⟨X, hX⟩ := X
  obtain ⟨hHerm, hGamma, hLevels⟩ := (mem_vortexLocus_iff w X).mp hX
  apply Subtype.ext
  show blockMatOf w (coordOf w X) = X
  ext i j
  rcases gSign_eq_one_or_neg_one i with hi | hi <;>
    rcases gSign_eq_one_or_neg_one j with hj | hj
  · have h0 : X i j = 0 :=
      gammaOdd_entry_eq_zero_of_gSign_eq X hGamma (by rw [hi, hj])
    rw [h0]
    rw [blockMatOf_apply, dif_pos hi, dif_pos hj]
  · by_cases hlog : logWeight w i = logWeight w j
    · have e : blockMatOf w (coordOf w X) i j
          = X (plusEmb (acoord i)) (minusEmb (flip8 (acoord j))) := by
        rw [blockMatOf_apply, dif_pos hi, dif_neg (by rw [hj]; norm_num),
          dif_pos hlog]
        rfl
      rw [e, plusEmb_acoord_of_gSign_eq_one hi,
        minusEmb_flip8_acoord_of_gSign_eq_neg_one hj]
    · have h0 : X i j = 0 := hLevels i j hlog
      rw [h0]
      rw [blockMatOf_apply, dif_pos hi, dif_neg (by rw [hj]; norm_num),
        dif_neg hlog]
  · by_cases hlog : logWeight w i = logWeight w j
    · have e : blockMatOf w (coordOf w X) i j
          = star (X (plusEmb (acoord j)) (minusEmb (flip8 (acoord i)))) := by
        rw [blockMatOf_apply, dif_neg (by rw [hi]; norm_num), dif_pos hj,
          dif_pos hlog]
        rfl
      rw [e, plusEmb_acoord_of_gSign_eq_one hj,
        minusEmb_flip8_acoord_of_gSign_eq_neg_one hi]
      exact (selfAdjoint_entry X hHerm.eq i j).symm
    · have h0 : X i j = 0 := hLevels i j hlog
      rw [h0]
      rw [blockMatOf_apply, dif_neg (by rw [hi]; norm_num), dif_pos hj,
        dif_neg hlog]
  · have h0 : X i j = 0 :=
      gammaOdd_entry_eq_zero_of_gSign_eq X hGamma (by rw [hi, hj])
    rw [h0]
    rw [blockMatOf_apply, dif_neg (by rw [hi]; norm_num),
      dif_neg (by rw [hj]; norm_num)]

/-- **The coordinate equivalence** (Tier T1 target): the Seat A
    locus is real-linearly equivalent to the free complex
    coordinates on the surviving cross-grading pairs. -/
noncomputable def vortexLocusEquiv (w : I32 → ℝ) :
    vortexLocus w ≃ₗ[ℝ] (crossPair w → ℂ) :=
  LinearEquiv.ofLinearMap (coordMap w) (blockMap w)
    (LinearMap.ext fun f => coordMap_blockMap w f)
    (LinearMap.ext fun X => blockMap_coordMap w X)

/-- The locus dimension is twice the number of surviving
    cross-grading pairs (one free complex entry per pair). -/
theorem finrank_vortexLocus_eq_two_mul_card (w : I32 → ℝ) :
    Module.finrank ℝ (vortexLocus w) = 2 * Fintype.card (crossPair w) := by
  rw [(vortexLocusEquiv w).finrank_eq, Module.finrank_pi_fintype]
  simp only [Complex.finrank_real_complex, Finset.sum_const, Finset.card_univ,
    smul_eq_mul]
  rw [Nat.mul_comm]

/-- Fibre counting: the surviving pairs partition by their common
    log-weight level `c`, and the `c`-fibre is the product of the
    plus fibre and the minus fibre over `c`. -/
theorem card_crossPair_eq_sum (w : I32 → ℝ) :
    Fintype.card (crossPair w)
      = ∑ c ∈ levels w, plusCount w c * minusCount w c := by
  classical
  have hS : Fintype.card (crossPair w)
      = (Finset.univ.filter
          (fun p : Fin 16 × Fin 16 =>
            logWeight w (plusEmb p.1) = logWeight w (minusEmb p.2))).card :=
    Fintype.card_subtype _
  rw [hS]
  rw [Finset.card_eq_sum_card_fiberwise
    (f := fun p : Fin 16 × Fin 16 => logWeight w (plusEmb p.1))
    (t := levels w) (by
      intro p _
      show logWeight w (plusEmb p.1) ∈ levels w
      rw [levels]
      exact Finset.mem_image.mpr
        ⟨plusEmb p.1, Finset.mem_univ _, rfl⟩)]
  apply Finset.sum_congr rfl
  intro c _
  have hfib : (Finset.univ.filter
        (fun p : Fin 16 × Fin 16 =>
          logWeight w (plusEmb p.1) = logWeight w (minusEmb p.2))).filter
        (fun p : Fin 16 × Fin 16 => logWeight w (plusEmb p.1) = c)
      = (Finset.univ.filter
          (fun a : Fin 16 => logWeight w (plusEmb a) = c)) ×ˢ
        (Finset.univ.filter
          (fun b : Fin 16 => logWeight w (minusEmb b) = c)) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_product]
    constructor
    · intro h
      exact ⟨h.2, h.1.symm.trans h.2⟩
    · intro h
      exact ⟨h.1.trans h.2.symm, h.1⟩
  rw [hfib, Finset.card_product]
  rfl

/-- **THE SEAT A FORMULA** (Tier T1 target): the real dimension of
    the locus at `diagModularK w` over the Hermitian grading-odd
    space is `2 * ∑ c, p_c * m_c`, the sum over the log-weight
    levels, `p_c` / `m_c` the level-`c` counts in the `+` / `−`
    grading sectors. Its entire content is the input partition:
    it is not a discovery engine and is not the pin. -/
theorem finrank_vortexLocus (w : I32 → ℝ) :
    Module.finrank ℝ (vortexLocus w)
      = 2 * ∑ c ∈ levels w, plusCount w c * minusCount w c := by
  rw [finrank_vortexLocus_eq_two_mul_card, card_crossPair_eq_sum]

/-! ## The K-VORTEX-1 ends and the straddle read-off -/

/-- A level contributes iff it straddles the grading: its term
    `p_c * m_c` is nonzero iff the level meets both sectors. -/
theorem contribution_ne_zero_iff_straddle (w : I32 → ℝ) (c : ℝ) :
    plusCount w c * minusCount w c ≠ 0 ↔
      (∃ a : Fin 16, logWeight w (plusEmb a) = c) ∧
        (∃ b : Fin 16, logWeight w (minusEmb b) = c) := by
  constructor
  · intro h
    have hp : plusCount w c ≠ 0 := by
      intro h0; rw [h0, zero_mul] at h; exact h rfl
    have hm : minusCount w c ≠ 0 := by
      intro h0; rw [h0, mul_zero] at h; exact h rfl
    constructor
    · by_contra hcon
      push_neg at hcon
      have h0 : plusCount w c = 0 := by
        rw [plusCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro a _
        exact hcon a
      exact hp h0
    · by_contra hcon
      push_neg at hcon
      have h0 : minusCount w c = 0 := by
        rw [minusCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro b _
        exact hcon b
      exact hm h0
  · intro h
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := h
    have hp : 0 < plusCount w c := by
      rw [plusCount, Finset.card_pos]
      exact ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ a, ha⟩⟩
    have hm : 0 < minusCount w c := by
      rw [minusCount, Finset.card_pos]
      exact ⟨b, Finset.mem_filter.mpr ⟨Finset.mem_univ b, hb⟩⟩
    exact Nat.mul_ne_zero (Nat.pos_iff_ne_zero.mp hp)
      (Nat.pos_iff_ne_zero.mp hm)

/-- A straddling level forces a middle value: the locus dimension
    is positive as soon as one level meets both sectors. -/
theorem finrank_pos_of_straddle (w : I32 → ℝ) {c : ℝ} (hc : c ∈ levels w)
    (h : plusCount w c * minusCount w c ≠ 0) :
    0 < Module.finrank ℝ (vortexLocus w) := by
  rw [finrank_vortexLocus]
  have hsum : 0 < ∑ c' ∈ levels w, plusCount w c' * minusCount w c' :=
    Finset.sum_pos' (fun c' _ => Nat.zero_le _)
      ⟨c, hc, Nat.pos_of_ne_zero h⟩
  omega

/-- **K-VORTEX-1, zero end** (Tier T1 target): if no log-weight
    level straddles the grading — every plus-sector log-weight
    differs from every minus-sector log-weight — the locus is
    `{0}`. The framing is empty at this end, reported at full
    rank: grading-aligned degeneracy buys nothing. -/
theorem vortexLocus_eq_bot_of_no_straddle (w : I32 → ℝ)
    (h : ∀ a : Fin 16, ∀ b : Fin 16,
      logWeight w (plusEmb a) ≠ logWeight w (minusEmb b)) :
    vortexLocus w = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro X hX
  obtain ⟨hHerm, hGamma, hLevels⟩ := (mem_vortexLocus_iff w X).mp hX
  ext i j
  show X i j = (0 : Matrix I32 I32 ℂ) i j
  rw [Matrix.zero_apply]
  rcases gSign_eq_one_or_neg_one i with hi | hi <;>
    rcases gSign_eq_one_or_neg_one j with hj | hj
  · exact gammaOdd_entry_eq_zero_of_gSign_eq X hGamma (by rw [hi, hj])
  · -- i plus, j minus: recover indices and use h
    have hi' : i = plusEmb (acoord i) :=
      (plusEmb_acoord_of_gSign_eq_one hi).symm
    have hj' : j = minusEmb (flip8 (acoord j)) :=
      (minusEmb_flip8_acoord_of_gSign_eq_neg_one hj).symm
    apply hLevels i j
    rw [hi', hj']
    exact h (acoord i) (flip8 (acoord j))
  · have hi' : i = minusEmb (flip8 (acoord i)) :=
      (minusEmb_flip8_acoord_of_gSign_eq_neg_one hi).symm
    have hj' : j = plusEmb (acoord j) :=
      (plusEmb_acoord_of_gSign_eq_one hj).symm
    apply hLevels i j
    rw [hi', hj']
    exact fun hEq => h (acoord j) (flip8 (acoord i)) hEq.symm
  · exact gammaOdd_entry_eq_zero_of_gSign_eq X hGamma (by rw [hi, hj])

/-- Zero end, generic weights: injective log-weights (e.g. 32
    distinct weights) leave no straddling level, so the locus is
    `{0}` — K-VORTEX-1 fires at the lower end. -/
theorem vortexLocus_eq_bot_of_injective_logWeight (w : I32 → ℝ)
    (h : Function.Injective (logWeight w)) :
    vortexLocus w = ⊥ := by
  apply vortexLocus_eq_bot_of_no_straddle
  intro a b hEq
  have hEq2 : plusEmb a = minusEmb b := h hEq
  -- plusEmb a ≠ minusEmb b: their values lie in disjoint ranges
  have hval : (plusEmb a).val ≠ (minusEmb b).val := by
    rw [plusEmb_val, minusEmb_val]
    split_ifs with ha <;> have hb := b.isLt <;> omega
  exact hval (congrArg Fin.val hEq2)

/-- **K-VORTEX-1, whole end** (Tier T1 target): at constant
    log-weights there is a single level meeting both sectors in
    full, the classification condition is vacuous, and the locus
    is the whole Hermitian grading-odd space. -/
theorem vortexLocus_eq_oddHermitian_of_log_const (w : I32 → ℝ)
    (h : ∀ i j : I32, logWeight w i = logWeight w j) :
    vortexLocus w = oddHermitianSpace := by
  ext X
  constructor
  · intro hX
    obtain ⟨h1, h2, _⟩ := hX
    exact ⟨h1, h2⟩
  · intro hX
    obtain ⟨h1, h2⟩ := hX
    refine ⟨h1, h2, ?_⟩
    rw [FluxClassification.classification_diagModularK]
    intro i j hij
    exact (hij (h i j)).elim

private theorem plusCount_const (c : ℝ) :
    plusCount (fun _ => c) (Real.log c) = 16 := by
  rw [plusCount]
  have : Finset.univ.filter
        (fun a : Fin 16 => logWeight (fun _ => c) (plusEmb a)
          = Real.log c)
      = Finset.univ := by
    apply Finset.filter_true_of_mem
    intro a _
    rfl
  rw [this]
  simp

private theorem minusCount_const (c : ℝ) :
    minusCount (fun _ => c) (Real.log c) = 16 := by
  rw [minusCount]
  have : Finset.univ.filter
        (fun b : Fin 16 => logWeight (fun _ => c) (minusEmb b)
          = Real.log c)
      = Finset.univ := by
    apply Finset.filter_true_of_mem
    intro b _
    rfl
  rw [this]
  simp

/-- The whole end, counted: at constant weights the formula reads
    `2 * 16 * 16 = 512`, the real dimension of the full Hermitian
    grading-odd space (one free complex `16 × 16` cross-block). -/
theorem finrank_vortexLocus_const (c : ℝ) :
    Module.finrank ℝ (vortexLocus (fun _ => c)) = 512 := by
  rw [finrank_vortexLocus]
  have hlev : levels (fun _ => c) = {Real.log c} := by
    rw [levels]
    apply Finset.image_const
    exact Finset.univ_nonempty
  rw [hlev, Finset.sum_singleton, plusCount_const, minusCount_const]

/-- The grading-aligned example: weights whose log-weights are
    the block indices `0, 1, 2, 3` on the four 8-blocks —
    constant on each block, four distinct levels, every level
    aligned with the grading. Tier T2 (chosen example). -/
noncomputable def alignedWeights : I32 → ℝ := fun j => Real.exp ((j.val / 8 : ℕ) : ℝ)

private theorem logWeight_alignedWeights (j : I32) :
    logWeight alignedWeights j = ((j.val / 8 : ℕ) : ℝ) := by
  show Real.log (Real.exp ((j.val / 8 : ℕ) : ℝ)) = _
  rw [Real.log_exp]

/-- The grading-aligned example lands at the zero end: its levels
    are `{0, 3}` on the plus sector and `{1, 2}` on the minus
    sector, no level straddles, and the locus is `{0}` despite
    the fourfold degeneracy. Only straddling levels produce
    middle values. -/
theorem vortexLocus_alignedWeights_eq_bot :
    vortexLocus alignedWeights = ⊥ := by
  apply vortexLocus_eq_bot_of_no_straddle
  intro a b hEq
  rw [logWeight_alignedWeights, logWeight_alignedWeights] at hEq
  have ha : (plusEmb a).val / 8 = 0 ∨ (plusEmb a).val / 8 = 3 := by
    rw [plusEmb_val]
    split_ifs with h1
    · left; omega
    · right; have h2 := a.isLt; omega
  have hb : (minusEmb b).val / 8 = 1 ∨ (minusEmb b).val / 8 = 2 := by
    rw [minusEmb_val]
    have h2 := b.isLt
    omega
  rcases ha with ha | ha <;> rcases hb with hb | hb <;>
    rw [ha, hb] at hEq <;> norm_num at hEq

#print axioms finrank_vortexLocus
#print axioms vortexLocus_eq_bot_of_no_straddle
#print axioms vortexLocus_eq_bot_of_injective_logWeight
#print axioms vortexLocus_eq_oddHermitian_of_log_const
#print axioms finrank_vortexLocus_const
#print axioms vortexLocus_alignedWeights_eq_bot

end ThetLogos.VortexLocusSeatA
