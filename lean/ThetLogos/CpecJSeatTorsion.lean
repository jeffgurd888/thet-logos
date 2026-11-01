import Mathlib.Tactic
import ThetLogos.DiracTorsionMap
import ThetLogos.CpecBridgePost

open Matrix Finset

namespace ThetLogos

/-!
# ThetLogos.CpecJSeatTorsion - CPEC-CC-1: the J-seat torsion map

**Working label only.** The module name `CpecJSeatTorsion` and
the brick name CPEC-CC-1 are working labels; Jeff names.

**Status: BUILT for parent landing - the seat verdict is
DECIDED below in both of the seat's two tests. NO CLAIM.
No gravity object is defined, constructed, or asserted to
exist. Dial 2 = 0, dials 0/4.**

Governing texts: the pack
`routeb-general-scratch/pack-cpec-cc-1.md`, the frozen pin
`CpecBridgePost` (CPEC-0, commit 35d5d6e; its registered
names are cited, never renamed), and the home module
`DiracTorsionMap`, whose seat discipline this module mirrors.
Gates, both cleared on the record before this build: the
CPEC-0 pin landed, and the `EdgeSignature` direct axiom
sweep completed BAD = 0 (dossier
`whitepaper/sorry0-landing-2026-10-30.md`, addendum
2026-11-01).

## What this brick is

`DiracTorsionMap` built the torsion map at two seats of
EdgeSignature's defect law (`defect eta T = eta * T + T * eta
+ T * T`, flat iff `defect = 0` when `eta * eta = 1`) and
named the third seat as its remainder R2: the real structure
`UJ` also satisfies `UJ * UJ = 1` (`UJ_mul_self`,
Scaffold32), so `eta := UJ` is a fundamental-symmetry
candidate whose torsion map was unbuilt. This module builds
it and decides its verdict, mirroring the home module's two
instantiation methods one seat over:

- **The seat's own induced map (inner fluctuations).**
  Exactly as the grading seat's torsion map is the correction
  to `gammaF` induced by `D -> fluctuatedDirac D A`, the
  J-seat torsion map `torsionJ D A` is the correction to the
  seat operator induced by the same fluctuation: the
  difference of the seat readings of the fluctuated and the
  original operator. The seat reading is the triple's real
  structure itself (T2 identification, on the face: `jSeat D
  := UJ` for every `D` - the corpus's triples carry `UJ` as
  fixed data, and `fluctuatedDirac` is built from that same
  `UJ` through `oppositeOneForm`). **Verdict: SURVIVAL - the
  torsion map is the zero map and the defect vanishes**
  (`j_seat_survival`). As at the grading seat, the content is
  not the trivial difference arithmetic but the invariance
  theorem licensing the constant reading: inner fluctuations
  preserve J-compatibility (`fluctuatedDirac_j_compat`, for
  every `D` with `IsJCompatible D` and every `A`, no
  hypothesis on `A`), instantiated at the corpus's ansatz by
  `smDirac_fluctuated_j_compat`. The same `UJ` remains the
  real structure of the fluctuated operator, so no correction
  is induced.

- **The cross-seat stress test (T2 choice, on the face).**
  The sign seat's one-parameter family - the Majorana line's
  correction `torsionMajorana y s`, the family that killed
  flatness at the sign seat for every `s != 0` - is NOT this
  seat's induced map; it is imported here as a stress test of
  the J seat, and the choice to test this family at this seat
  is labelled T2. Its defect at `eta = UJ` is computed
  entrywise exactly (`j_majorana_defect_apply`): the defect
  is supported on the two diagonal entries `(8, 8)` and
  `(24, 24)` - the partner pair that `UJ` swaps and that the
  Majorana block couples - with common value
  `(y)^-1 * (s + star s) + (y)^-2 * (s * star s)`, a real
  number (twice the real part of `s`, scaled, plus the
  squared norm, scaled). **Verdict: flatness along the
  imported family is decided by that real equation**
  (`j_majorana_survival_iff`): it fails at the canonical
  point `y = 1`, `s = 1`, where the defect entry is `3`
  (`j_majorana_obstruction_point`), and it holds at the
  isolated nonzero point `y = 1`, `s = -2`
  (`j_majorana_flat_point`) - in sharp contrast with the
  sign seat, where the same family is flat only at `s = 0`.
  The Majorana obstruction is a property of the seat, not of
  the Majorana block alone.

## Fences

Finite level only: `Matrix I32 I32 ℂ`, the corpus's own
blocks, no continuum operator, **no connection**. This
"torsion" is the algebraic defect of a deformed fundamental
symmetry under inner fluctuation, in `EdgeSignature`'s and
`DiracTorsionMap`'s fenced sense: it is NOT the
antisymmetric part of an affine connection, and the defect
law's "Maurer-Cartan-type" label is ring algebra, not
differential geometry (K-CPEC-CARTAN-NAME and
K-CPEC-TORSION-IMPORT, carried from the pin). Program
ceiling: a decided seat on the Connes-Cartan wire's
remainder; this seats NO gravity object; Dial 2 = 0;
NO CLAIM.
-/

-- ============================================================================
-- Section 0. The J seat in EdgeSignature's frame
-- ============================================================================

/-- **The J-seat reading** (Tier T2 definition - the seat
    identification): the seat operator read off a Dirac
    operator `D` at the J seat is the corpus's real structure
    `UJ` itself. The corpus's triples carry `UJ` as fixed
    data, independent of `D`; that this constant reading
    remains valid for fluctuated operators is the invariance
    theorem `fluctuatedDirac_j_compat` below, not a definition
    smuggled past a proof. -/
def jSeat (_D : Matrix I32 I32 ℂ) : Matrix I32 I32 ℂ := UJ

/-- The J seat is an involution (T1 - proved, by citation):
    the seat operator squares to `1`, by the landed
    `UJ_mul_self` of Scaffold32. This is the only hypothesis
    EdgeSignature's defect law asks of a seat. -/
theorem jSeat_involutive (D : Matrix I32 I32 ℂ) :
    jSeat D * jSeat D = 1 :=
  UJ_mul_self

/-- The J seat's edge pair is perfect (T1 - proved, by
    citation): in EdgeSignature's frame, `eta = UJ` yields
    the complementary orthogonal idempotent pair
    `(edgePlus UJ, edgeMinus UJ)`, by the landed Morley core
    `edgePair_of_symm` at `UJ_mul_self`. -/
theorem j_seat_edge_pair : IsEdgePair (edgePlus UJ) (edgeMinus UJ) :=
  edgePair_of_symm UJ UJ_mul_self

/-- Left multiplication by `UJ` reads the partner row
    (T1 target): `(UJ * M) i j = M (partner i) j`, since row
    `i` of `UJ` is the unit row at column `partner i`. -/
theorem uj_mul_apply (M : Matrix I32 I32 ℂ) (i j : I32) :
    (UJ * M) i j = M (partner i) j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (partner i)]
  · have h1 : UJ i (partner i) = 1 := by
      rw [UJ_apply]; unfold UJ_matrix; exact ite_eq_left rfl
    rw [h1, one_mul]
  · intro k _ hk
    have h0 : UJ i k = 0 := by
      rw [UJ_apply]; unfold UJ_matrix; exact ite_eq_right hk
    rw [h0, zero_mul]
  · intro hcon
    exact absurd (Finset.mem_univ (partner i)) hcon

/-- Right multiplication by `UJ` reads the partner column
    (T1 target): `(M * UJ) i j = M i (partner j)`. -/
theorem mul_uj_apply (M : Matrix I32 I32 ℂ) (i j : I32) :
    (M * UJ) i j = M i (partner j) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (partner j)]
  · have h1 : UJ (partner j) j = 1 := by
      rw [UJ_apply]; unfold UJ_matrix
      exact ite_eq_left (partner_involutive j).symm
    rw [h1, mul_one]
  · intro k _ hk
    have hkj : j ≠ partner k := by
      intro hcon
      apply hk
      rw [hcon, partner_involutive]
    have h0 : UJ k j = 0 := by
      rw [UJ_apply]; unfold UJ_matrix; exact ite_eq_right hkj
    rw [h0, mul_zero]
  · intro hcon
    exact absurd (Finset.mem_univ (partner j)) hcon

/-- The partner of index `8` is index `24` (T1 target): the
    two indices the Majorana block couples are exactly a
    `UJ`-partner pair. -/
theorem partner_8 : partner ⟨8, by norm_num⟩ = ⟨24, by norm_num⟩ := by
  decide

/-- The partner of index `24` is index `8` (T1 target). -/
theorem partner_24 : partner ⟨24, by norm_num⟩ = ⟨8, by norm_num⟩ := by
  decide

-- ============================================================================
-- Section 1. The seat's own torsion map: inner fluctuations
-- ============================================================================

/-- **The J-seat torsion map** (Tier T2 definition): the
    correction to the seat operator induced by an inner
    fluctuation `D -> fluctuatedDirac D A`, defined as the
    difference of the seat readings - exactly the
    construction `DiracTorsionMap` used for the sign seat's
    `torsionMajorana` (there, the difference of the
    normalised deformed and flat operators). Here both
    readings are the real structure `UJ`, because the
    fluctuated Dirac is built from that same `UJ`. -/
def torsionJ (D A : Matrix I32 I32 ℂ) : Matrix I32 I32 ℂ :=
  jSeat (fluctuatedDirac D A) - jSeat D

/-- The opposite 1-form is J-conjugation invariant in the
    transpose sense (T1 target): conjugating the transpose of
    `A° = UJ * A^T * UJ` by `UJ` returns `A`. The engine of
    the invariance theorem below. -/
theorem oppositeOneForm_jConj (A : Matrix I32 I32 ℂ) :
    UJ * (oppositeOneForm A).transpose * UJ = A := by
  have hT : (oppositeOneForm A).transpose = UJ * A * UJ := by
    simp only [oppositeOneForm, Matrix.transpose_mul, UJ_transpose_eq,
      Matrix.transpose_transpose, Matrix.mul_assoc]
  rw [hT]
  exact UJ_invol A

/-- **Inner fluctuations preserve J-compatibility**
    (T1 target): if `D` satisfies the real-structure relation
    `UJ * D^T * UJ = D`, so does every inner fluctuation
    `fluctuatedDirac D A = D + A + A°`, for every `A` with no
    hypothesis on `A` - the `A` term and the `A°` term swap
    under the conjugation, by `oppositeOneForm_jConj`. This
    is the J seat's invariance theorem, the analogue of the
    grading seat's `fluctuatedDirac_gamma_odd`. -/
theorem fluctuatedDirac_j_compat (D A : Matrix I32 I32 ℂ)
    (hD : IsJCompatible D) :
    IsJCompatible (fluctuatedDirac D A) := by
  have key : ∀ X Y : Matrix I32 I32 ℂ,
      UJ * (X + Y).transpose * UJ
        = UJ * X.transpose * UJ + UJ * Y.transpose * UJ := by
    intro X Y
    rw [Matrix.transpose_add, Matrix.mul_add, Matrix.add_mul]
  unfold IsJCompatible at hD ⊢
  unfold fluctuatedDirac
  rw [key, key, hD, oppositeOneForm_jConj]
  unfold oppositeOneForm
  abel

/-- J-compatibility of the fluctuated ansatz (T1 target):
    every inner fluctuation of the corpus's `smDirac` ansatz
    remains J-compatible, instantiating
    `fluctuatedDirac_j_compat` at the landed
    `smDirac_IsJCompatible`. -/
theorem smDirac_fluctuated_j_compat (yNu yE yU yD yR : ℂ)
    (A : Matrix I32 I32 ℂ) :
    IsJCompatible (fluctuatedDirac (smDirac yNu yE yU yD yR) A) :=
  fluctuatedDirac_j_compat _ A (smDirac_IsJCompatible yNu yE yU yD yR)

/-- The J-seat torsion map is the zero map (T1 target): both
    seat readings are `UJ`, so their difference vanishes for
    every `D` and every fluctuation `A`. -/
theorem torsionJ_eq_zero (D A : Matrix I32 I32 ℂ) :
    torsionJ D A = 0 := by
  unfold torsionJ jSeat
  exact sub_self UJ

/-- **Seat verdict, the seat's own map (T1 target):
    SURVIVAL.** For every Dirac operator `D` and every inner
    fluctuation `A`: the induced correction `torsionJ D A`
    is zero, its EdgeSignature defect at `eta = UJ` vanishes,
    the deformed seat operator `UJ + torsionJ D A` is again a
    fundamental symmetry, and J-compatibility - the relation
    that makes `UJ` the real structure of `D` - is preserved
    by the fluctuation whenever it holds for `D`. The
    substance is the preservation clause
    (`fluctuatedDirac_j_compat`): the constant seat reading
    is licensed for the fluctuated operator, so the zero
    correction is a theorem about the seat, not an
    oversight. -/
theorem j_seat_survival (D A : Matrix I32 I32 ℂ) :
    torsionJ D A = 0
      ∧ defect UJ (torsionJ D A) = 0
      ∧ (UJ + torsionJ D A) * (UJ + torsionJ D A) = 1
      ∧ (IsJCompatible D → IsJCompatible (fluctuatedDirac D A)) :=
  ⟨torsionJ_eq_zero D A,
   by rw [torsionJ_eq_zero]; simp [defect],
   by rw [torsionJ_eq_zero, add_zero]; exact UJ_mul_self,
   fun hD => fluctuatedDirac_j_compat D A hD⟩

/-- **Pin read-back.** The J seat's vanishing defect, stated
    through the CPEC-0 pin's frozen registered name
    `cpecCartanDefect` (the pillar-Cartan defect at the Dirac
    arena): the registered defect of the J seat's induced
    correction is zero. Pin-grade only - a restatement of
    `j_seat_survival`'s defect clause through the pin's
    definition. -/
theorem j_seat_pin_readback (D A : Matrix I32 I32 ℂ) :
    cpecCartanDefect UJ (torsionJ D A) = 0 := by
  unfold cpecCartanDefect
  exact (j_seat_survival D A).2.1

-- ============================================================================
-- Section 2. Cross-seat stress test: the Majorana family at eta = UJ
-- ============================================================================

/-- The Majorana correction at `(24, 8)` (T1 target): the
    `E`-block entry of `torsionMajorana y s` is
    `(y)^-1 * s` - the partner-swapped companion of the home
    module's `torsionMajorana_apply_8_24`. -/
theorem torsionMajorana_apply_24_8 (y : ℝ) (s : ℂ) :
    torsionMajorana y s ⟨24, by norm_num⟩ ⟨8, by norm_num⟩
      = (↑y)⁻¹ * s := by
  have hE : buildDirac 0 0 0 (majoranaBlock s)
        ⟨24, by norm_num⟩ ⟨8, by norm_num⟩ = s := by
    have hgen : ∀ (E : Block8) (i j : I32),
        (hi1 : ¬ i.val < 8) → (hi2 : ¬ i.val < 16) → (hi3 : ¬ i.val < 24) →
        (hj1 : ¬ j.val < 8) → (hj2 : j.val < 16) →
        buildDirac 0 0 0 E i j
          = E ⟨i.val - 24, by omega⟩ ⟨j.val - 8, by omega⟩ := by
      intro E i j hi1 hi2 hi3 hj1 hj2
      unfold buildDirac
      simp only []
      simp [hi1, hi2, hi3, hj1, hj2]
    rw [hgen _ _ _ (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)]
    have h1 : (⟨24 - 24, by norm_num⟩ : Fin 8) = 0 := Fin.ext rfl
    have h2 : (⟨8 - 8, by norm_num⟩ : Fin 8) = 0 := Fin.ext rfl
    rw [h1, h2, majoranaBlock_val]
  unfold torsionMajorana
  rw [Matrix.smul_apply, deltaDirac_eq, hE]
  show ((y⁻¹ : ℝ) : ℂ) * s = (↑y)⁻¹ * s
  rw [Complex.ofReal_inv]

/-- The Majorana correction vanishes off its partner pair
    (T1 target): at every entry other than `(8, 24)` and
    `(24, 8)`, `torsionMajorana y s` is zero - its only
    possible support is the `E` and `E`-dagger blocks, and
    the Majorana block itself is supported only at its
    `(0, 0)` entry. -/
theorem torsionMajorana_eq_zero_of (y : ℝ) (s : ℂ) (i j : I32)
    (h : ¬ ((i = ⟨8, by norm_num⟩ ∧ j = ⟨24, by norm_num⟩)
      ∨ (i = ⟨24, by norm_num⟩ ∧ j = ⟨8, by norm_num⟩))) :
    torsionMajorana y s i j = 0 := by
  have hz : buildDirac 0 0 0 (majoranaBlock s) i j = 0 := by
    by_cases H1 : i.val < 8 <;> by_cases H2 : i.val < 16 <;>
      by_cases H3 : i.val < 24 <;> by_cases J1 : j.val < 8 <;>
      by_cases J2 : j.val < 16 <;> by_cases J3 : j.val < 24 <;>
      (unfold buildDirac; simp only [];
        simp only [H1, H2, H3, J1, J2, J3, dite_true, dite_false,
          Matrix.conjTranspose_zero, Matrix.zero_apply])
    · -- The E-dagger region (i in [8,16), j in [24,32)): the only
      -- region besides E where the entry can be nonzero.
      by_cases h0 : (majoranaBlock s).conjTranspose
          ⟨i.val - 8, by omega⟩ ⟨j.val - 24, by omega⟩ = 0
      · exact h0
      · exfalso
        obtain ⟨ha, hb⟩ := majoranaBlock_conjT_supp _ _ h0
        have h1 : i.val - 8 = 0 := congrArg Fin.val ha
        have h2 : j.val - 24 = 0 := congrArg Fin.val hb
        exact h (Or.inl ⟨Fin.ext (by show i.val = 8; omega),
          Fin.ext (by show j.val = 24; omega)⟩)
    · -- The E-dagger region again: the H3 split leaves an
      -- inconsistent-hypothesis twin of the same goal.
      by_cases h0 : (majoranaBlock s).conjTranspose
          ⟨i.val - 8, by omega⟩ ⟨j.val - 24, by omega⟩ = 0
      · exact h0
      · exfalso
        obtain ⟨ha, hb⟩ := majoranaBlock_conjT_supp _ _ h0
        have h1 : i.val - 8 = 0 := congrArg Fin.val ha
        have h2 : j.val - 24 = 0 := congrArg Fin.val hb
        exact h (Or.inl ⟨Fin.ext (by show i.val = 8; omega),
          Fin.ext (by show j.val = 24; omega)⟩)
    · -- The E region (i in [24,32), j in [8,16)).
      by_cases h0 : majoranaBlock s
          ⟨i.val - 24, by omega⟩ ⟨j.val - 8, by omega⟩ = 0
      · exact h0
      · exfalso
        obtain ⟨ha, hb⟩ := majoranaBlock_supp _ _ h0
        have h1 : i.val - 24 = 0 := congrArg Fin.val ha
        have h2 : j.val - 8 = 0 := congrArg Fin.val hb
        exact h (Or.inr ⟨Fin.ext (by show i.val = 24; omega),
          Fin.ext (by show j.val = 8; omega)⟩)
    · -- The E region again: the J3 split leaves an
      -- inconsistent-hypothesis twin of the same goal.
      by_cases h0 : majoranaBlock s
          ⟨i.val - 24, by omega⟩ ⟨j.val - 8, by omega⟩ = 0
      · exact h0
      · exfalso
        obtain ⟨ha, hb⟩ := majoranaBlock_supp _ _ h0
        have h1 : i.val - 24 = 0 := congrArg Fin.val ha
        have h2 : j.val - 8 = 0 := congrArg Fin.val hb
        exact h (Or.inr ⟨Fin.ext (by show i.val = 24; omega),
          Fin.ext (by show j.val = 8; omega)⟩)
  unfold torsionMajorana
  rw [Matrix.smul_apply, deltaDirac_eq, hz, smul_zero]

/-- Support of the Majorana correction (T1 target): every
    nonzero entry of `torsionMajorana y s` sits on the
    partner pair `(8, 24)` or `(24, 8)`. -/
theorem torsionMajorana_support (y : ℝ) (s : ℂ) (i j : I32)
    (h : torsionMajorana y s i j ≠ 0) :
    (i = ⟨8, by norm_num⟩ ∧ j = ⟨24, by norm_num⟩)
      ∨ (i = ⟨24, by norm_num⟩ ∧ j = ⟨8, by norm_num⟩) := by
  by_contra hcon
  exact h (torsionMajorana_eq_zero_of y s i j hcon)

/-- The square of the Majorana correction, on the diagonal
    of its partner pair (T1 target): at `(8, 8)` and at
    `(24, 24)` it is the single product of the two partner
    entries. -/
theorem torsionMajorana_sq_diag (y : ℝ) (s : ℂ) :
    (torsionMajorana y s * torsionMajorana y s)
        ⟨8, by norm_num⟩ ⟨8, by norm_num⟩
      = (↑y)⁻¹ * star s * ((↑y)⁻¹ * s)
    ∧ (torsionMajorana y s * torsionMajorana y s)
        ⟨24, by norm_num⟩ ⟨24, by norm_num⟩
      = (↑y)⁻¹ * star s * ((↑y)⁻¹ * s) := by
  constructor
  · rw [Matrix.mul_apply, Finset.sum_eq_single ⟨24, by norm_num⟩]
    · rw [torsionMajorana_apply_8_24, torsionMajorana_apply_24_8]
    · intro k _ hk
      have e1 : torsionMajorana y s ⟨8, by norm_num⟩ k = 0 := by
        apply torsionMajorana_eq_zero_of
        rintro (⟨-, h2⟩ | ⟨h1, -⟩)
        · exact hk h2
        · exact absurd h1 (by decide)
      rw [e1, zero_mul]
    · intro hcon
      exact absurd (Finset.mem_univ _) hcon
  · rw [Matrix.mul_apply, Finset.sum_eq_single ⟨8, by norm_num⟩]
    · rw [torsionMajorana_apply_24_8, torsionMajorana_apply_8_24]
      ring
    · intro k _ hk
      have e1 : torsionMajorana y s ⟨24, by norm_num⟩ k = 0 := by
        apply torsionMajorana_eq_zero_of
        rintro (⟨h1, -⟩ | ⟨-, h2⟩)
        · exact absurd h1 (by decide)
        · exact hk h2
      rw [e1, zero_mul]
    · intro hcon
      exact absurd (Finset.mem_univ _) hcon

/-- The square of the Majorana correction vanishes off the
    partner-pair diagonal (T1 target). -/
theorem torsionMajorana_sq_eq_zero_of (y : ℝ) (s : ℂ) (i j : I32)
    (h : ¬ ((i = ⟨8, by norm_num⟩ ∧ j = ⟨8, by norm_num⟩)
      ∨ (i = ⟨24, by norm_num⟩ ∧ j = ⟨24, by norm_num⟩))) :
    (torsionMajorana y s * torsionMajorana y s) i j = 0 := by
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  by_cases hk1 : torsionMajorana y s i k = 0
  · rw [hk1, zero_mul]
  · by_cases hk2 : torsionMajorana y s k j = 0
    · rw [hk2, mul_zero]
    · exfalso
      apply h
      have p1 := torsionMajorana_support y s i k hk1
      have p2 := torsionMajorana_support y s k j hk2
      rcases p1 with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rcases p2 with ⟨e3, e4⟩ | ⟨e3, e4⟩
      · exact absurd (e2.symm.trans e3) (by decide)
      · exact Or.inl ⟨e1, e4⟩
      · exact Or.inr ⟨e1, e4⟩
      · exact absurd (e2.symm.trans e3) (by decide)

/-- **The defect at the J seat, computed entrywise**
    (T1 target): for the imported Majorana family,
    `defect UJ (torsionMajorana y s)` is supported on the
    two diagonal entries `(8, 8)` and `(24, 24)` of the
    partner pair, with common value
    `(y)^-1 * (s + star s) + (y)^-2 * (s * star s)`.
    The anticommutator terms read the partner entries
    through `UJ` (`uj_mul_apply`, `mul_uj_apply`), and the
    square contributes the single partner product
    (`torsionMajorana_sq_diag`). -/
theorem j_majorana_defect_apply (y : ℝ) (s : ℂ) (i j : I32) :
    defect UJ (torsionMajorana y s) i j
      = if (i = ⟨8, by norm_num⟩ ∧ j = ⟨8, by norm_num⟩)
            ∨ (i = ⟨24, by norm_num⟩ ∧ j = ⟨24, by norm_num⟩)
        then (↑y)⁻¹ * (s + star s) + (↑y)⁻¹ * (↑y)⁻¹ * (s * star s)
        else 0 := by
  unfold defect
  rw [Matrix.add_apply, Matrix.add_apply, uj_mul_apply, mul_uj_apply]
  by_cases hp : (i = ⟨8, by norm_num⟩ ∧ j = ⟨8, by norm_num⟩)
      ∨ (i = ⟨24, by norm_num⟩ ∧ j = ⟨24, by norm_num⟩)
  · rw [if_pos hp]
    rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [partner_8, torsionMajorana_apply_24_8,
        torsionMajorana_apply_8_24, (torsionMajorana_sq_diag y s).1]
      ring
    · rw [partner_24, torsionMajorana_apply_8_24,
        torsionMajorana_apply_24_8, (torsionMajorana_sq_diag y s).2]
      ring
  · rw [if_neg hp, torsionMajorana_sq_eq_zero_of y s i j hp]
    have e1 : torsionMajorana y s (partner i) j = 0 := by
      apply torsionMajorana_eq_zero_of
      rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · apply hp
        refine Or.inr ⟨?_, h2⟩
        have h3 : i = partner (partner i) := (partner_involutive i).symm
        rw [h3, h1, partner_8]
      · apply hp
        refine Or.inl ⟨?_, h2⟩
        have h3 : i = partner (partner i) := (partner_involutive i).symm
        rw [h3, h1, partner_24]
    have e2 : torsionMajorana y s i (partner j) = 0 := by
      apply torsionMajorana_eq_zero_of
      rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · apply hp
        refine Or.inl ⟨h1, ?_⟩
        have h3 : j = partner (partner j) := (partner_involutive j).symm
        rw [h3, h2, partner_24]
      · apply hp
        refine Or.inr ⟨h1, ?_⟩
        have h3 : j = partner (partner j) := (partner_involutive j).symm
        rw [h3, h2, partner_8]
    rw [e1, e2]
    simp

/-- The J-seat Majorana defect vanishes exactly on the
    displayed real equation (T1 target): the defect is zero
    iff `(y)^-1 * (s + star s) + (y)^-2 * (s * star s) = 0`,
    read off at the single entry `(8, 8)` in one direction
    and entrywise in the other. -/
theorem j_majorana_defect_eq_zero_iff (y : ℝ) (s : ℂ) :
    defect UJ (torsionMajorana y s) = 0
      ↔ (↑y)⁻¹ * (s + star s) + (↑y)⁻¹ * (↑y)⁻¹ * (s * star s) = 0 := by
  constructor
  · intro h
    have h0 : defect UJ (torsionMajorana y s)
        ⟨8, by norm_num⟩ ⟨8, by norm_num⟩ = 0 := by
      rw [h, Matrix.zero_apply]
    rw [j_majorana_defect_apply] at h0
    rwa [if_pos (Or.inl ⟨rfl, rfl⟩)] at h0
  · intro h
    ext i j
    rw [j_majorana_defect_apply, Matrix.zero_apply]
    by_cases hp : (i = ⟨8, by norm_num⟩ ∧ j = ⟨8, by norm_num⟩)
        ∨ (i = ⟨24, by norm_num⟩ ∧ j = ⟨24, by norm_num⟩)
    · rwa [if_pos hp]
    · rw [if_neg hp]

/-- **Seat verdict, the imported Majorana family (T1
    target): flatness at the J seat is decided by the real
    equation.** For every real scale `y` (no nonzero
    hypothesis is needed - the statement is in terms of
    `(y)^-1`, which is `0` at `y = 0`) and every Majorana
    parameter `s`, the deformed seat operator
    `UJ + torsionMajorana y s` is a fundamental symmetry if
    and only if
    `(y)^-1 * (s + star s) + (y)^-2 * (s * star s) = 0`.
    Contrast the sign seat (`majorana_survival_iff`): there
    the same family is flat only at `s = 0`; here the
    equation is one real condition - the displayed value is
    `(y)^-1 * (2 * Re s) + (y)^-2 * |s|^2` - with nonzero
    solutions, named in the next two results. -/
theorem j_majorana_survival_iff (y : ℝ) (s : ℂ) :
    (UJ + torsionMajorana y s) * (UJ + torsionMajorana y s) = 1
      ↔ (↑y)⁻¹ * (s + star s) + (↑y)⁻¹ * (↑y)⁻¹ * (s * star s) = 0 :=
  (dirac_torsion_flat_iff UJ (torsionMajorana y s) UJ_mul_self).trans
    (j_majorana_defect_eq_zero_iff y s)

/-- **The obstruction at the canonical point (T1 target):**
    at `y = 1`, `s = 1` the J-seat Majorana defect entry at
    `(8, 8)` is `3`, and the deformed seat operator is not a
    fundamental symmetry. The imported family does obstruct
    this seat at its canonical point - the seat's survival
    is under its own induced map (Section 1), not under this
    family. -/
theorem j_majorana_obstruction_point :
    defect UJ (torsionMajorana 1 1) ⟨8, by norm_num⟩ ⟨8, by norm_num⟩ = 3
      ∧ ¬ ((UJ + torsionMajorana 1 1) * (UJ + torsionMajorana 1 1) = 1) := by
  constructor
  · rw [j_majorana_defect_apply, if_pos (Or.inl ⟨rfl, rfl⟩), star_one,
      Complex.ofReal_one]
    norm_num
  · intro hcon
    have h1 := (j_majorana_survival_iff 1 1).mp hcon
    rw [star_one, Complex.ofReal_one] at h1
    norm_num at h1

/-- **The isolated flat point (T1 target):** at `y = 1`,
    `s = -2` (a real parameter) the imported family's
    defect at the J seat vanishes and the deformed seat
    operator is a fundamental symmetry - a nonzero flat
    point of a shape the sign seat does not have, where
    flatness holds only at `s = 0`. -/
theorem j_majorana_flat_point :
    (UJ + torsionMajorana 1 ((-2 : ℝ) : ℂ))
        * (UJ + torsionMajorana 1 ((-2 : ℝ) : ℂ)) = 1 := by
  have hstar : star (((-2 : ℝ) : ℂ)) = ((-2 : ℝ) : ℂ) := by
    rw [RCLike.star_def]
    exact RCLike.conj_ofReal _
  rw [j_majorana_survival_iff, hstar, Complex.ofReal_one]
  norm_num

end ThetLogos
