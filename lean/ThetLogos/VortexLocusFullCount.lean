import ThetLogos.VortexLocusFullTable
import ThetLogos.Census96Decoupling
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Tactic

/-!
# Vortex-locus full count (VL-4b): the full-space locus dimension is 156

Governing texts: the VL scoping memo §(i)
(`routeb-general-scratch/scoping-vortex-locus-2026-10-30.md`), BR1-027,
the VL-4a dossier (`whitepaper/vl4a-landing-2026-11-01.md`), and the pack
`routeb-general-scratch/pack-vl-4b.md`.  NO CLAIM on this module's face;
the K-VORTEX fences of the memo §5 are inherited: nothing below asserts
that a Yukawa block "is" a circulation flux, and "vortex" is Jeff's T5
vocabulary carried by the inherited module names only.

**Seat (T2 chosen input, stated on the face).**  Seat B:
`y₀ = (1, 2, 3, 5, 7)`, `K0 = (smDirac y₀)^2` — the landed names from
`VortexLocusPin.lean` / `VortexLocusFullTable.lean` (VL-4a), cited,
never redefined.

**The locus.**  `locusB` is the real submodule of Hermitian,
grading-odd matrices on `I32` commuting with `K0` — the odd part of
the commutant of `D_F(y₀)^2` in the full Hermitian odd space (the
memo's D-space (i) at Seat B).

**Headline.**  `Module.finrank ℝ locusB = 156`, the value registered
by BR1-027 (`Σ_μ 2·m_μ⁺·m_μ⁻` over the five distinct eigenvalues of
`K0`).

**The deciding subtlety (pack VL-4b).**  The sum runs over the five
DISTINCT eigenvalues.  VL-4a landed the irrational pair's JOINT split
(2, 2) for `ker (M² - 51M + 1)`; plugging the joint numbers in would
give `2·2·2 = 8` for that block — wrong.  The commutant preserves
each root's eigenspace separately (the spectral projectors are
polynomials in `K0`), and the per-root splits are (1, 1) each,
contributing `2·1·1 + 2·1·1 = 4`.  Obligation 1 (§3) proves the
per-root separation first: for each of `μ± = (51 ± √2597)/2`, the
eigenspace of `K0` has complex finrank 2 with γ-split (1, 1).  The
block sum is then `8 + 72 + 72 + 2 + 2 = 156`.

**Proof route (folded coordinates).**  In the folded coordinates of
`Census96Decoupling` (`plusEmb` / `minusEmb ∘ flip8`), a Hermitian
odd matrix is its cross-block `B (u, v) = X (plusEmb u) (minusEmb
(flip8 v))`, a plain `16 × 16` complex matrix.  Both grading sectors
of `K0` read, in these coordinates, as ONE AND THE SAME folded seat
matrix `Qmat` (§1: diagonal `qd` with a single coupled `2 × 2` block
`[[1, 7], [7, 50]]` on the folded seats `{0, 8}`; the `flip8` twist
in the minus-sector coordinate is exactly what identifies the two
sector blocks `[[1, 7], [7, 50]]` and `[[50, 7], [7, 1]]`).  Hence
`X` commutes with `K0` iff its cross-block commutes with `Qmat`:
`locusB` is real-linearly equivalent to the complex centralizer of
`Qmat`, whose complex dimension is `78 = 4 + 36 + 36 + 2` (§4: the
`μ = 4, 9, 25` coordinate blocks contribute `2², 6², 6²`, and the
coupled block's commutant is 2-dimensional — one complex parameter
per irrational root, §3's (1, 1) splits in folded form).  The real
dimension is twice the complex one: `156`.

No `sorry`, no `native_decide`; no scoped heartbeat raises were used.
-/

namespace ThetLogos

open Matrix

/-! ## §1. The folded seat matrix

`qd a = dval (plusEmb a)` is the diagonal of `K0`'s plus-sector block
in folded coordinates, `qc a` its coupling.  The minus-sector block,
read in the twisted coordinate `minusEmb (flip8 a)`, has the SAME
diagonal and coupling (`dval_minusEmb_flip8`, `cval_minusEmb_flip8`),
so a single folded matrix `Qmat` governs both sectors. -/

/-- Diagonal value of the folded seat matrix at `a`. -/
def qd (a : Fin 16) : ℂ := dval (plusEmb a)

/-- Coupling value of the folded seat matrix at `a`. -/
def qc (a : Fin 16) : ℂ := cval (plusEmb a)

theorem qd_zero : qd (0 : Fin 16) = 1 := by
  norm_num [qd, plusEmb, dval, bOf, aOf, wvec, wvec']

theorem qd_eight : qd (8 : Fin 16) = 50 := by
  norm_num [qd, plusEmb, dval, bOf, aOf, wvec, wvec']

theorem qc_zero : qc (0 : Fin 16) = 7 := by
  norm_num [qc, plusEmb, cval, aOf]

theorem qc_eight : qc (8 : Fin 16) = 7 := by
  norm_num [qc, plusEmb, cval, aOf]

theorem flip8_zero : flip8 (0 : Fin 16) = 8 := by decide
theorem flip8_eight : flip8 (8 : Fin 16) = 0 := by decide

theorem flip8_ne_self (a : Fin 16) : flip8 a ≠ a := by
  intro h
  have hv := congrArg Fin.val h
  rw [flip8_val] at hv
  split_ifs at hv <;> omega

theorem pIdx_plusEmb (a : Fin 16) : pIdx (plusEmb a) = plusEmb (flip8 a) := by
  fin_cases a <;> decide

theorem pIdx_minusEmb_flip8 (a : Fin 16) :
    pIdx (minusEmb (flip8 a)) = minusEmb a := by
  fin_cases a <;> decide

theorem dval_minusEmb_flip8 (a : Fin 16) : dval (minusEmb (flip8 a)) = qd a := by
  fin_cases a <;> norm_num [qd, plusEmb, minusEmb, flip8, dval, bOf, aOf, wvec, wvec']

theorem cval_minusEmb_flip8 (a : Fin 16) : cval (minusEmb (flip8 a)) = qc (flip8 a) := by
  fin_cases a <;> norm_num [qc, plusEmb, minusEmb, flip8, cval, aOf]

theorem pb_val (b : Fin 4) : (pb b).val = 3 - b.val := by
  fin_cases b <;> decide

theorem gSign_pIdx (i : I32) : gSign (pIdx i) = gSign i := by
  have hval : (pIdx i).val = (aOf i).val + (pb (bOf i)).val * 8 := rfl
  have ha : (aOf i).val = i.val % 8 := rfl
  have hb : (bOf i).val = i.val / 8 := rfl
  have hi32 : i.val < 32 := i.isLt
  rw [gSign_apply, gSign_apply, hval, ha, pb_val]
  rcases fin4_cases (bOf i) with h | h | h | h <;>
    split_ifs <;> first | rfl | (exfalso; omega)

theorem plusEmb_inj : Function.Injective plusEmb := by
  intro a a' h
  apply Fin.ext
  have hv := congrArg Fin.val h
  rw [plusEmb_val, plusEmb_val] at hv
  split_ifs at hv <;> omega

theorem minusEmb_inj : Function.Injective minusEmb := by
  intro a a' h
  apply Fin.ext
  have hv := congrArg Fin.val h
  rw [minusEmb_val, minusEmb_val] at hv
  omega

/-! ### The folded value table -/

theorem qd_mem (a : Fin 16) :
    qd a = 1 ∨ qd a = 4 ∨ qd a = 9 ∨ qd a = 25 ∨ qd a = 50 := by
  fin_cases a <;> norm_num [qd, plusEmb, dval, bOf, aOf, wvec, wvec']

theorem qc_mem (a : Fin 16) : qc a = 0 ∨ qc a = 7 := by
  fin_cases a <;> norm_num [qc, plusEmb, cval, aOf]

theorem qc_eq_seven_iff (a : Fin 16) : qc a = 7 ↔ a = 0 ∨ a = 8 := by
  fin_cases a <;> norm_num [qc, plusEmb, cval, aOf]

theorem qd_eq_one_iff (a : Fin 16) : qd a = 1 ↔ a = 0 := by
  fin_cases a <;> norm_num [qd, plusEmb, dval, bOf, aOf, wvec, wvec']

theorem qd_eq_fifty_iff (a : Fin 16) : qd a = 50 ↔ a = 8 := by
  fin_cases a <;> norm_num [qd, plusEmb, dval, bOf, aOf, wvec, wvec']

theorem qd_eq_four_iff (a : Fin 16) : qd a = 4 ↔ a.val % 8 = 1 := by
  fin_cases a <;> norm_num [qd, plusEmb, dval, bOf, aOf, wvec, wvec']

theorem qd_eq_nine_iff (a : Fin 16) :
    qd a = 9 ↔ a.val % 8 = 2 ∨ a.val % 8 = 4 ∨ a.val % 8 = 6 := by
  fin_cases a <;> norm_num [qd, plusEmb, dval, bOf, aOf, wvec, wvec']

theorem qd_eq_twentyfive_iff (a : Fin 16) :
    qd a = 25 ↔ a.val % 8 = 3 ∨ a.val % 8 = 5 ∨ a.val % 8 = 7 := by
  fin_cases a <;> norm_num [qd, plusEmb, dval, bOf, aOf, wvec, wvec']

theorem qc_flip8 (a : Fin 16) : qc (flip8 a) = qc a := by
  fin_cases a <;> norm_num [qc, plusEmb, flip8, cval, aOf]

theorem qd_flip8 (a : Fin 16) :
    qd (flip8 a) = if a = 0 then 50 else if a = 8 then 1 else qd a := by
  fin_cases a <;> norm_num [qd, plusEmb, flip8, dval, bOf, aOf, wvec, wvec']

theorem star_qd (a : Fin 16) : star (qd a) = qd a := by
  fin_cases a <;> norm_num [qd, plusEmb, dval, bOf, aOf, wvec, wvec']

theorem star_qc (a : Fin 16) : star (qc a) = qc a := by
  fin_cases a <;> norm_num [qc, plusEmb, cval, aOf]

/-- The class of a folded seat: the coupled pair `{0, 8}`, or one of
    the three diagonal eigenvalues `4`, `9`, `25`. -/
theorem seat_class (a : Fin 16) :
    (a = 0 ∨ a = 8) ∨ qd a = 4 ∨ qd a = 9 ∨ qd a = 25 := by
  rcases qd_mem a with h | h | h | h | h
  · exact Or.inl (Or.inl ((qd_eq_one_iff a).mp h))
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))
  · exact Or.inl (Or.inr ((qd_eq_fifty_iff a).mp h))

theorem qc_eq_zero_of_not_coupled (a : Fin 16) (h : ¬ (a = 0 ∨ a = 8)) :
    qc a = 0 := by
  rcases qc_mem a with h0 | h7
  · exact h0
  · exact absurd ((qc_eq_seven_iff a).mp h7) h

theorem coupled_flip (a : Fin 16) (h : a = 0 ∨ a = 8) :
    qd a + qd (flip8 a) = 51 ∧ qd a * qd (flip8 a) = 50 ∧ qc a = 7 := by
  rcases h with rfl | rfl <;>
    simp only [flip8_zero, flip8_eight, qd_zero, qd_eight, qc_zero, qc_eight] <;>
    norm_num

theorem qd_sq_ne (a : Fin 16) (h : qd a = 4 ∨ qd a = 9 ∨ qd a = 25) :
    qd a ^ 2 - 51 * qd a + 1 ≠ 0 := by
  rcases h with h | h | h <;> rw [h] <;> norm_num

/-! ### The folded seat matrix and its multiplication formulas -/

/-- The folded seat matrix: the plus-sector block of `K0` in folded
    coordinates — and, by the `flip8` twist, also its minus-sector
    block (`Qmat_apply_plus`, `Qmat_apply_minus`). -/
def Qmat : Matrix (Fin 16) (Fin 16) ℂ :=
  fun a b => if b = a then qd a else if b = flip8 a then qc a else 0

theorem Qmat_apply_plus (a b : Fin 16) :
    Qmat a b = K0 (plusEmb a) (plusEmb b) := by
  have e1 : (plusEmb b = plusEmb a) ↔ (b = a) := plusEmb_inj.eq_iff
  have e2 : (plusEmb b = pIdx (plusEmb a)) ↔ (b = flip8 a) := by
    rw [pIdx_plusEmb]; exact plusEmb_inj.eq_iff
  rw [K0_apply, Qmat]
  simp only [e1, e2]
  split_ifs <;> rfl

theorem Qmat_apply_minus (a b : Fin 16) :
    Qmat a b = K0 (minusEmb (flip8 a)) (minusEmb (flip8 b)) := by
  have e1 : (minusEmb (flip8 b) = minusEmb (flip8 a)) ↔ (b = a) :=
    ⟨fun h => (Function.Involutive.injective flip8_flip8) (minusEmb_inj h),
     fun h => by rw [h]⟩
  have e2 : (minusEmb (flip8 b) = pIdx (minusEmb (flip8 a))) ↔ (b = flip8 a) := by
    rw [pIdx_minusEmb_flip8]
    constructor
    · intro h
      have h3 : flip8 b = a := minusEmb_inj h
      have hb : b = flip8 (flip8 b) := (flip8_flip8 b).symm
      rw [hb, h3]
    · intro h
      rw [h, flip8_flip8]
  rw [K0_apply, Qmat]
  simp only [e1, e2]
  split_ifs <;> first
    | rfl
    | exact (dval_minusEmb_flip8 a).symm
    | exact (qc_flip8 a).symm.trans (cval_minusEmb_flip8 a).symm

theorem Qmat_mul_apply (B : Matrix (Fin 16) (Fin 16) ℂ) (a b : Fin 16) :
    (Qmat * B) a b = qd a * B a b + qc a * B (flip8 a) b := by
  have hsum : (Qmat * B) a b = ∑ k : Fin 16, Qmat a k * B k b := by
    rw [Matrix.mul_apply]
  rw [hsum]
  have hsub : (∑ k : Fin 16, Qmat a k * B k b)
      = ∑ k ∈ ({a, flip8 a} : Finset (Fin 16)), Qmat a k * B k b := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro k _ hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rw [not_or] at hk
    show Qmat a k * B k b = 0
    rw [Qmat, ite_eq_right hk.1, ite_eq_right hk.2, zero_mul]
  rw [hsub, Finset.sum_pair (flip8_ne_self a).symm]
  rw [Qmat, Qmat, ite_eq_left rfl, ite_eq_right (flip8_ne_self a),
    ite_eq_left rfl]

theorem mul_Qmat_apply (B : Matrix (Fin 16) (Fin 16) ℂ) (a b : Fin 16) :
    (B * Qmat) a b = B a b * qd b + B a (flip8 b) * qc (flip8 b) := by
  have hsum : (B * Qmat) a b = ∑ k : Fin 16, B a k * Qmat k b := by
    rw [Matrix.mul_apply]
  rw [hsum]
  have hsub : (∑ k : Fin 16, B a k * Qmat k b)
      = ∑ k ∈ ({b, flip8 b} : Finset (Fin 16)), B a k * Qmat k b := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro k _ hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rw [not_or] at hk
    show B a k * Qmat k b = 0
    rw [Qmat, ite_eq_right (fun h => hk.1 h.symm),
      ite_eq_right (fun h => hk.2 (by rw [h, flip8_flip8])), mul_zero]
  rw [hsub, Finset.sum_pair (flip8_ne_self b).symm]
  have e1 : Qmat b b = qd b := by
    rw [Qmat, ite_eq_left rfl]
  have e2 : Qmat (flip8 b) b = qc (flip8 b) := by
    rw [Qmat, ite_eq_right (fun h => flip8_ne_self b h.symm),
      ite_eq_left (flip8_flip8 b).symm]
  rw [e1, e2]

/-! ### Row and column formulas for `K0` -/

theorem K0_mul_apply (X : Matrix I32 I32 ℂ) (i j : I32) :
    (K0 * X) i j = dval i * X i j + cval i * X (pIdx i) j := by
  have hsum : (K0 * X) i j = ∑ k : I32, K0 i k * X k j := by
    rw [Matrix.mul_apply]
  rw [hsum]
  have hsub : (∑ k : I32, K0 i k * X k j)
      = ∑ k ∈ ({i, pIdx i} : Finset I32), K0 i k * X k j := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro k _ hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rw [not_or] at hk
    rw [K0_apply, ite_eq_right hk.1, ite_eq_right hk.2, zero_mul]
  rw [hsub, Finset.sum_pair (pIdx_ne_self i).symm]
  rw [K0_apply, K0_apply, ite_eq_left rfl, ite_eq_right (pIdx_ne_self i),
    ite_eq_left rfl]

theorem mul_K0_apply (X : Matrix I32 I32 ℂ) (i j : I32) :
    (X * K0) i j = X i j * dval j + X i (pIdx j) * cval j := by
  have hsum : (X * K0) i j = ∑ k : I32, X i k * K0 k j := by
    rw [Matrix.mul_apply]
  rw [hsum]
  have hsub : (∑ k : I32, X i k * K0 k j)
      = ∑ k ∈ ({j, pIdx j} : Finset I32), X i k * K0 k j := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro k _ hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rw [not_or] at hk
    have hk1 : j ≠ k := fun h => hk.1 h.symm
    have hk2 : j ≠ pIdx k := by
      intro h
      apply hk.2
      rw [h, pIdx_involutive]
    rw [K0_apply, ite_eq_right hk1, ite_eq_right hk2, mul_zero]
  rw [hsub, Finset.sum_pair (pIdx_ne_self j).symm]
  have e1 : K0 j j = dval j := by
    rw [K0_apply, ite_eq_left rfl]
  have e2 : K0 (pIdx j) j = cval j := by
    rw [K0_apply, ite_eq_right (fun h => pIdx_ne_self j h.symm),
      ite_eq_left (pIdx_involutive j).symm, cval_pIdx]
  rw [e1, e2]


/-! ## §2. Coordinate parametrizations of the diagonal classes

The folded seats with `qd = 4` are `{1, 9}`; with `qd = 9` they are
`{2, 4, 6, 10, 12, 14}`; with `qd = 25`, `{3, 5, 7, 11, 13, 15}`
(the `a9` / `a25` within-block indices of VL-4a, in both halves).
`p4` / `p9` / `p25` parametrize them; `pos4` / `pos9` / `pos25` are
the inverse position maps on the class. -/

/-- Folded seats with `qd = 4`. -/
def p4 : Fin 2 → Fin 16 := ![1, 9]

/-- Folded seats with `qd = 9`. -/
def p9 : Fin 2 × Fin 3 → Fin 16 :=
  fun p => ⟨(a9 p.2).val + 8 * p.1.val, by
    have h1 := (a9 p.2).isLt; have h2 := p.1.isLt; omega⟩

/-- Folded seats with `qd = 25`. -/
def p25 : Fin 2 × Fin 3 → Fin 16 :=
  fun p => ⟨(a25 p.2).val + 8 * p.1.val, by
    have h1 := (a25 p.2).isLt; have h2 := p.1.isLt; omega⟩

/-- Position of a `qd = 4` seat in `p4`. -/
def pos4 (a : Fin 16) : Fin 2 := if a.val < 8 then 0 else 1

/-- Position of a `qd = 9` seat in `p9`. -/
def pos9 (a : Fin 16) : Fin 2 × Fin 3 :=
  (if a.val < 8 then 0 else 1,
   if a.val % 8 = 2 then 0 else if a.val % 8 = 4 then 1 else 2)

/-- Position of a `qd = 25` seat in `p25`. -/
def pos25 (a : Fin 16) : Fin 2 × Fin 3 :=
  (if a.val < 8 then 0 else 1,
   if a.val % 8 = 3 then 0 else if a.val % 8 = 5 then 1 else 2)

theorem p4_inj : Function.Injective p4 := by decide

theorem p9_inj : Function.Injective p9 := by
  rintro ⟨t, s⟩ ⟨t', s'⟩ h
  have hv := congrArg Fin.val h
  have hv1 : (p9 (t, s)).val = (a9 s).val + 8 * t.val := rfl
  have hv2 : (p9 (t', s')).val = (a9 s').val + 8 * t'.val := rfl
  rw [hv1, hv2] at hv
  have h1 := (a9 s).isLt; have h2 := (a9 s').isLt
  have ht : t = t' := by
    apply Fin.ext; have ht2 := t.isLt; have ht2' := t'.isLt; omega
  have hs : s = s' := by
    apply a9_inj; apply Fin.ext; omega
  exact Prod.ext ht hs

theorem p25_inj : Function.Injective p25 := by
  rintro ⟨t, s⟩ ⟨t', s'⟩ h
  have hv := congrArg Fin.val h
  have hv1 : (p25 (t, s)).val = (a25 s).val + 8 * t.val := rfl
  have hv2 : (p25 (t', s')).val = (a25 s').val + 8 * t'.val := rfl
  rw [hv1, hv2] at hv
  have h1 := (a25 s).isLt; have h2 := (a25 s').isLt
  have ht : t = t' := by
    apply Fin.ext; have ht2 := t.isLt; have ht2' := t'.isLt; omega
  have hs : s = s' := by
    apply a25_inj; apply Fin.ext; omega
  exact Prod.ext ht hs

theorem qd_p4 (t : Fin 2) : qd (p4 t) = 4 := by
  fin_cases t <;> norm_num [p4, qd, plusEmb, dval, bOf, aOf, wvec, wvec']

theorem qd_p9 (p : Fin 2 × Fin 3) : qd (p9 p) = 9 := by
  obtain ⟨t, s⟩ := p
  fin_cases t <;> fin_cases s <;>
    norm_num [p9, qd, plusEmb, dval, bOf, aOf, wvec, wvec', a9]

theorem qd_p25 (p : Fin 2 × Fin 3) : qd (p25 p) = 25 := by
  obtain ⟨t, s⟩ := p
  fin_cases t <;> fin_cases s <;>
    norm_num [p25, qd, plusEmb, dval, bOf, aOf, wvec, wvec', a25]

theorem p4_pos4 (a : Fin 16) (h : a.val % 8 = 1) : p4 (pos4 a) = a := by
  fin_cases a <;> simp_all [p4, pos4]

theorem p9_pos9 (a : Fin 16)
    (h : a.val % 8 = 2 ∨ a.val % 8 = 4 ∨ a.val % 8 = 6) : p9 (pos9 a) = a := by
  fin_cases a <;> simp_all [p9, pos9, a9]

theorem p25_pos25 (a : Fin 16)
    (h : a.val % 8 = 3 ∨ a.val % 8 = 5 ∨ a.val % 8 = 7) : p25 (pos25 a) = a := by
  fin_cases a <;> simp_all [p25, pos25, a25]

theorem pos4_p4 (t : Fin 2) : pos4 (p4 t) = t := by
  fin_cases t <;> norm_num [p4, pos4]

theorem pos9_p9 (p : Fin 2 × Fin 3) : pos9 (p9 p) = p := by
  obtain ⟨t, s⟩ := p
  fin_cases t <;> fin_cases s <;> norm_num [p9, pos9, a9]

theorem pos25_p25 (p : Fin 2 × Fin 3) : pos25 (p25 p) = p := by
  obtain ⟨t, s⟩ := p
  fin_cases t <;> fin_cases s <;> norm_num [p25, pos25, a25]


/-! ## §3. Obligation 1: the per-root separation

The two roots of `μ² - 51μ + 1` are REAL, `(51 ± √2597)/2`; named
here as complex numbers via the real embedding.  For each root `μ`,
the eigenspace of `K0` is the span of the two explicit eigenvectors
`vecP μ` (plus sector, supported on the coupled seats
`blkIdx 0 0`, `blkIdx 3 0`, with values `(7, μ - 1)`) and `vecM μ`
(minus sector, supported on `blkIdx 1 0`, `blkIdx 2 0`, with values
`(7, μ - 50)`) — hence finrank 2 with γ-split (1, 1).  This is the
per-root refinement of VL-4a's joint (2, 2) split of
`ker (M² - 51M + 1)`: the joint kernel is the direct sum of the two
per-root eigenspaces, and the commutant preserves each separately. -/

/-- The larger root of `μ² - 51μ + 1`. -/
noncomputable def muP : ℂ := Complex.ofReal ((51 + Real.sqrt 2597) / 2)

/-- The smaller root of `μ² - 51μ + 1`. -/
noncomputable def muM : ℂ := Complex.ofReal ((51 - Real.sqrt 2597) / 2)

theorem sqrt2597_sq : (Real.sqrt 2597) ^ 2 = 2597 :=
  Real.sq_sqrt (by norm_num)

theorem muP_add_muM : muP + muM = 51 := by
  have hr : (51 + Real.sqrt 2597) / 2 + (51 - Real.sqrt 2597) / 2 = (51 : ℝ) := by ring
  rw [muP, muM, ← Complex.ofReal_add, hr]
  simp

theorem muP_mul_muM : muP * muM = 1 := by
  have hr : (51 + Real.sqrt 2597) / 2 * ((51 - Real.sqrt 2597) / 2) = (1 : ℝ) := by
    nlinarith [sqrt2597_sq]
  rw [muP, muM, ← Complex.ofReal_mul, hr]
  simp

theorem muP_ne_muM : muP ≠ muM := by
  have hs : 0 < Real.sqrt 2597 := Real.sqrt_pos.mpr (by norm_num)
  rw [muP, muM, Ne, Complex.ofReal_inj]
  linarith

theorem muP_quad (μ : ℂ) (hμ : μ = muP ∨ μ = muM) : μ ^ 2 - 51 * μ + 1 = 0 := by
  rcases hμ with rfl | rfl
  · have hr : ((51 + Real.sqrt 2597) / 2 : ℝ) ^ 2
        - 51 * ((51 + Real.sqrt 2597) / 2 : ℝ) + 1 = 0 := by
      nlinarith [sqrt2597_sq]
    have h2 := congrArg (fun r : ℝ => (r : ℂ)) hr
    rw [muP]
    simpa using h2
  · have hr : ((51 - Real.sqrt 2597) / 2 : ℝ) ^ 2
        - 51 * ((51 - Real.sqrt 2597) / 2 : ℝ) + 1 = 0 := by
      nlinarith [sqrt2597_sq]
    have h2 := congrArg (fun r : ℝ => (r : ℂ)) hr
    rw [muM]
    simpa using h2

theorem mu_sub_one_ne (μ : ℂ) (hμ : μ ^ 2 - 51 * μ + 1 = 0) : μ - 1 ≠ 0 := by
  intro h
  have h1 : μ = 1 := sub_eq_zero.mp h
  rw [h1] at hμ
  norm_num at hμ

theorem fin8_cases (x : Fin 8) :
    x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 5 ∨ x = 6 ∨ x = 7 := by
  fin_cases x <;> decide

/-- The plus-sector eigenvector of `K0` at a root `μ` of the
    quadratic, supported on the coupled seats `blkIdx 0 0`,
    `blkIdx 3 0` with values `7`, `μ - 1`. -/
def vecP (μ : ℂ) : I32 → ℂ :=
  fun i => if i = blkIdx 0 0 then 7 else if i = blkIdx 3 0 then μ - 1 else 0

/-- The minus-sector eigenvector of `K0` at a root `μ`, supported on
    `blkIdx 1 0`, `blkIdx 2 0` with values `7`, `μ - 50`. -/
def vecM (μ : ℂ) : I32 → ℂ :=
  fun i => if i = blkIdx 1 0 then 7 else if i = blkIdx 2 0 then μ - 50 else 0

theorem vecP_apply_blk (μ : ℂ) (b : Fin 4) (a : Fin 8) :
    vecP μ (blkIdx b a)
      = if (b = 0 ∧ a = 0) then 7 else if (b = 3 ∧ a = 0) then μ - 1 else 0 := by
  rw [vecP]
  by_cases h1 : b = 0 ∧ a = 0
  · obtain ⟨rfl, rfl⟩ := h1
    rw [ite_eq_left rfl, ite_eq_left ⟨rfl, rfl⟩]
  · by_cases h2 : b = 3 ∧ a = 0
    · obtain ⟨rfl, rfl⟩ := h2
      have e1 : (blkIdx (3 : Fin 4) (0 : Fin 8)) ≠ blkIdx 0 0 := by decide
      rw [ite_eq_right e1, ite_eq_left rfl, ite_eq_right h1, ite_eq_left ⟨rfl, rfl⟩]
    · have e1 : blkIdx b a ≠ blkIdx 0 0 := by
        intro h
        exact h1 ⟨(blkIdx_inj h).1, (blkIdx_inj h).2⟩
      have e2 : blkIdx b a ≠ blkIdx 3 0 := by
        intro h
        exact h2 ⟨(blkIdx_inj h).1, (blkIdx_inj h).2⟩
      rw [ite_eq_right e1, ite_eq_right e2, ite_eq_right h1, ite_eq_right h2]

theorem vecM_apply_blk (μ : ℂ) (b : Fin 4) (a : Fin 8) :
    vecM μ (blkIdx b a)
      = if (b = 1 ∧ a = 0) then 7 else if (b = 2 ∧ a = 0) then μ - 50 else 0 := by
  rw [vecM]
  by_cases h1 : b = 1 ∧ a = 0
  · obtain ⟨rfl, rfl⟩ := h1
    rw [ite_eq_left rfl, ite_eq_left ⟨rfl, rfl⟩]
  · by_cases h2 : b = 2 ∧ a = 0
    · obtain ⟨rfl, rfl⟩ := h2
      have e1 : (blkIdx (2 : Fin 4) (0 : Fin 8)) ≠ blkIdx 1 0 := by decide
      rw [ite_eq_right e1, ite_eq_left rfl, ite_eq_right h1, ite_eq_left ⟨rfl, rfl⟩]
    · have e1 : blkIdx b a ≠ blkIdx 1 0 := by
        intro h
        exact h1 ⟨(blkIdx_inj h).1, (blkIdx_inj h).2⟩
      have e2 : blkIdx b a ≠ blkIdx 2 0 := by
        intro h
        exact h2 ⟨(blkIdx_inj h).1, (blkIdx_inj h).2⟩
      rw [ite_eq_right e1, ite_eq_right e2, ite_eq_right h1, ite_eq_right h2]

theorem vecP_mem_eig (μ : ℂ) (hμ : μ ^ 2 - 51 * μ + 1 = 0) :
    vecP μ ∈ eigSub μ := by
  rw [mem_eigSub]
  funext i
  obtain ⟨b, a, rfl⟩ : ∃ b a, i = blkIdx b a := ⟨bOf i, aOf i, (eq_blkIdx i).symm⟩
  rw [K0_mulVec_apply, Pi.smul_apply, smul_eq_mul, pIdx_blk,
    vecP_apply_blk, vecP_apply_blk, dval_blk, cval_blk]
  rcases fin4_cases b with rfl | rfl | rfl | rfl <;>
    rcases fin8_cases a with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [pb_zero, pb_one, pb_two, pb_three, wvec, wvec',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.cons_val_three] <;>
    norm_num <;> ring_nf <;> first
      | linear_combination hμ
      | linear_combination (-hμ)
      | linear_combination (2 * hμ)
      | linear_combination (-2 * hμ)
      | (rw [show μ ^ 2 = 51 * μ - 1 by linear_combination hμ]; ring)

theorem vecM_mem_eig (μ : ℂ) (hμ : μ ^ 2 - 51 * μ + 1 = 0) :
    vecM μ ∈ eigSub μ := by
  rw [mem_eigSub]
  funext i
  obtain ⟨b, a, rfl⟩ : ∃ b a, i = blkIdx b a := ⟨bOf i, aOf i, (eq_blkIdx i).symm⟩
  rw [K0_mulVec_apply, Pi.smul_apply, smul_eq_mul, pIdx_blk,
    vecM_apply_blk, vecM_apply_blk, dval_blk, cval_blk]
  rcases fin4_cases b with rfl | rfl | rfl | rfl <;>
    rcases fin8_cases a with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [pb_zero, pb_one, pb_two, pb_three, wvec, wvec',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.cons_val_three] <;>
    norm_num <;> ring_nf <;> first
      | linear_combination hμ
      | linear_combination (-hμ)
      | linear_combination (2 * hμ)
      | linear_combination (-2 * hμ)
      | (rw [show μ ^ 2 = 51 * μ - 1 by linear_combination hμ]; ring)


/-! ### Values of the eigenvectors on the coupled seats -/

theorem vecP_blk00 (μ : ℂ) : vecP μ (blkIdx (0 : Fin 4) (0 : Fin 8)) = 7 :=
  if_pos rfl

theorem vecP_blk30 (μ : ℂ) : vecP μ (blkIdx (3 : Fin 4) (0 : Fin 8)) = μ - 1 :=
  (if_neg (by decide : blkIdx (3 : Fin 4) (0 : Fin 8) ≠ blkIdx (0 : Fin 4) (0 : Fin 8))).trans
    (if_pos rfl)

theorem vecP_blk10 (μ : ℂ) : vecP μ (blkIdx (1 : Fin 4) (0 : Fin 8)) = 0 :=
  (if_neg (by decide : blkIdx (1 : Fin 4) (0 : Fin 8) ≠ blkIdx (0 : Fin 4) (0 : Fin 8))).trans
    (if_neg (by decide : blkIdx (1 : Fin 4) (0 : Fin 8) ≠ blkIdx (3 : Fin 4) (0 : Fin 8)))

theorem vecP_blk20 (μ : ℂ) : vecP μ (blkIdx (2 : Fin 4) (0 : Fin 8)) = 0 :=
  (if_neg (by decide : blkIdx (2 : Fin 4) (0 : Fin 8) ≠ blkIdx (0 : Fin 4) (0 : Fin 8))).trans
    (if_neg (by decide : blkIdx (2 : Fin 4) (0 : Fin 8) ≠ blkIdx (3 : Fin 4) (0 : Fin 8)))

theorem vecP_of_a_ne (μ : ℂ) (b : Fin 4) (a : Fin 8) (ha : a ≠ 0) :
    vecP μ (blkIdx b a) = 0 :=
  (if_neg (fun h => ha (blkIdx_inj h).2)).trans
    (if_neg (fun h => ha (blkIdx_inj h).2))

theorem vecM_blk10 (μ : ℂ) : vecM μ (blkIdx (1 : Fin 4) (0 : Fin 8)) = 7 :=
  if_pos rfl

theorem vecM_blk20 (μ : ℂ) : vecM μ (blkIdx (2 : Fin 4) (0 : Fin 8)) = μ - 50 :=
  (if_neg (by decide : blkIdx (2 : Fin 4) (0 : Fin 8) ≠ blkIdx (1 : Fin 4) (0 : Fin 8))).trans
    (if_pos rfl)

theorem vecM_blk00 (μ : ℂ) : vecM μ (blkIdx (0 : Fin 4) (0 : Fin 8)) = 0 :=
  (if_neg (by decide : blkIdx (0 : Fin 4) (0 : Fin 8) ≠ blkIdx (1 : Fin 4) (0 : Fin 8))).trans
    (if_neg (by decide : blkIdx (0 : Fin 4) (0 : Fin 8) ≠ blkIdx (2 : Fin 4) (0 : Fin 8)))

theorem vecM_blk30 (μ : ℂ) : vecM μ (blkIdx (3 : Fin 4) (0 : Fin 8)) = 0 :=
  (if_neg (by decide : blkIdx (3 : Fin 4) (0 : Fin 8) ≠ blkIdx (1 : Fin 4) (0 : Fin 8))).trans
    (if_neg (by decide : blkIdx (3 : Fin 4) (0 : Fin 8) ≠ blkIdx (2 : Fin 4) (0 : Fin 8)))

theorem vecM_of_a_ne (μ : ℂ) (b : Fin 4) (a : Fin 8) (ha : a ≠ 0) :
    vecM μ (blkIdx b a) = 0 :=
  (if_neg (fun h => ha (blkIdx_inj h).2)).trans
    (if_neg (fun h => ha (blkIdx_inj h).2))

theorem vecP_ne_zero (μ : ℂ) : vecP μ ≠ 0 := by
  intro h
  have h0 := congrFun h (blkIdx (0 : Fin 4) (0 : Fin 8))
  rw [vecP_blk00, Pi.zero_apply] at h0
  norm_num at h0

theorem vecM_ne_zero (μ : ℂ) : vecM μ ≠ 0 := by
  intro h
  have h0 := congrFun h (blkIdx (1 : Fin 4) (0 : Fin 8))
  rw [vecM_blk10, Pi.zero_apply] at h0
  norm_num at h0

theorem vecP_ne_vecM (μ : ℂ) : vecP μ ≠ vecM μ := by
  intro h
  have h0 := congrFun h (blkIdx (0 : Fin 4) (0 : Fin 8))
  rw [vecP_blk00, vecM_blk00] at h0
  norm_num at h0

theorem vecP_mem_gammaPlus (μ : ℂ) : vecP μ ∈ gammaPlusSub := by
  refine (mem_coordEmb_range fPlus_inj (vecP μ)).mpr ?_
  intro i hi
  rw [range_fPlus_bOf] at hi
  obtain ⟨b, a, rfl⟩ : ∃ b a, i = blkIdx b a := ⟨bOf i, aOf i, (eq_blkIdx i).symm⟩
  rw [blkIdx_bOf] at hi
  by_cases ha : a = 0
  · subst ha
    rcases fin4_cases b with rfl | rfl | rfl | rfl
    · exact absurd (Or.inl rfl) hi
    · exact vecP_blk10 μ
    · exact vecP_blk20 μ
    · exact absurd (Or.inr rfl) hi
  · exact vecP_of_a_ne μ b a ha

theorem vecM_mem_gammaMinus (μ : ℂ) : vecM μ ∈ gammaMinusSub := by
  refine (mem_coordEmb_range fMinus_inj (vecM μ)).mpr ?_
  intro i hi
  rw [range_fMinus_bOf] at hi
  obtain ⟨b, a, rfl⟩ : ∃ b a, i = blkIdx b a := ⟨bOf i, aOf i, (eq_blkIdx i).symm⟩
  rw [blkIdx_bOf] at hi
  by_cases ha : a = 0
  · subst ha
    rcases fin4_cases b with rfl | rfl | rfl | rfl
    · exact vecM_blk00 μ
    · exact absurd (Or.inl rfl) hi
    · exact absurd (Or.inr rfl) hi
    · exact vecM_blk30 μ
  · exact vecM_of_a_ne μ b a ha

/-! ### The eigenspace is the span of the two eigenvectors -/

theorem eigSub_factor_zero (μ : ℂ) {v : I32 → ℂ} (hv : v ∈ eigSub μ) :
    (K0 - μ • (1 : Matrix I32 I32 ℂ)) *ᵥ v = 0 := by
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, mem_eigSub.mp hv,
    sub_self]

theorem eigSub_quad_of_mem (μ : ℂ) (hμ : μ = muP ∨ μ = muM) {v : I32 → ℂ}
    (hv : v ∈ eigSub μ) : v ∈ quadKer := by
  have hquad : μ ^ 2 - 51 * μ + 1 = 0 := muP_quad μ hμ
  have he : K0 *ᵥ v = μ • v := mem_eigSub.mp hv
  have hcalc : (K0 ^ 2 - 51 • K0 + 1) *ᵥ v = (μ ^ 2 - 51 * μ + 1) • v := by
    simp only [pow_two, Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec, ← Matrix.mulVec_mulVec, he, Matrix.mulVec_smul, smul_smul]
    module
  rw [mem_quadKer, hcalc, hquad, zero_smul]

theorem eig_eq_span (μ : ℂ) (hμ : μ = muP ∨ μ = muM) :
    eigSub μ = Submodule.span ℂ {vecP μ, vecM μ} := by
  have hquad : μ ^ 2 - 51 * μ + 1 = 0 := muP_quad μ hμ
  have h49 : (μ - 1) * (μ - 50) = 49 := by linear_combination hquad
  apply le_antisymm
  · intro v hv
    have hvq : v ∈ quadKer := eigSub_quad_of_mem μ hμ hv
    rw [quadKer_eq_range] at hvq
    obtain ⟨w, hw⟩ := hvq
    have hva : ∀ b : Fin 4, v (blkIdx b 0) = w b := by
      intro b
      rw [← hw]
      exact coordEmb_apply_at fQ_inj w b
    have hv0 : ∀ (b : Fin 4) (a : Fin 8), a ≠ 0 → v (blkIdx b a) = 0 := by
      intro b a ha
      rw [← hw]
      refine coordEmb_apply_of_not_mem w ?_
      rw [range_fQ_aOf, blkIdx_aOf]
      exact fun h => ha (Fin.ext h)
    have heig := eigSub_factor_zero μ hv
    have hd0 : dval (blkIdx (0 : Fin 4) (0 : Fin 8)) = 1 := by
      rw [dval_blk0]; norm_num [wvec]
    have hd2 : dval (blkIdx (2 : Fin 4) (0 : Fin 8)) = 1 := by
      rw [dval_blk2]; norm_num [wvec]
    have hc0 : cval (blkIdx (0 : Fin 4) (0 : Fin 8)) = 7 := by
      rw [cval_blk]; norm_num
    have hc2 : cval (blkIdx (2 : Fin 4) (0 : Fin 8)) = 7 := by
      rw [cval_blk]; norm_num
    have hp0 : pIdx (blkIdx (0 : Fin 4) (0 : Fin 8)) = blkIdx 3 0 := rfl
    have hp2 : pIdx (blkIdx (2 : Fin 4) (0 : Fin 8)) = blkIdx 1 0 := rfl
    have e0 : (1 - μ) * w 0 + 7 * w 3 = 0 := by
      have h := congrFun heig (blkIdx (0 : Fin 4) (0 : Fin 8))
      rw [factor_mulVec_apply, Pi.zero_apply, hd0, hc0, hp0, hva, hva] at h
      exact h
    have e2 : (1 - μ) * w 2 + 7 * w 1 = 0 := by
      have h := congrFun heig (blkIdx (2 : Fin 4) (0 : Fin 8))
      rw [factor_mulVec_apply, Pi.zero_apply, hd2, hc2, hp2, hva, hva] at h
      exact h
    rw [Submodule.mem_span_pair]
    refine ⟨w 0 / 7, w 1 / 7, ?_⟩
    funext i
    obtain ⟨b, a, rfl⟩ : ∃ b a, i = blkIdx b a := ⟨bOf i, aOf i, (eq_blkIdx i).symm⟩
    rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
    by_cases ha : a = 0
    · subst ha
      rw [hva]
      rcases fin4_cases b with rfl | rfl | rfl | rfl
      · rw [vecP_blk00, vecM_blk00]
        linear_combination (0 : ℂ) * e0
      · rw [vecP_blk10, vecM_blk10]
        linear_combination (0 : ℂ) * e0
      · rw [vecP_blk20, vecM_blk20]
        linear_combination ((μ - 50) / 49) * e2 + (w 2 / 49) * h49
      · rw [vecP_blk30, vecM_blk30]
        linear_combination (-e0 / 7)
    · rw [hv0 b a ha, vecP_of_a_ne μ b a ha, vecM_of_a_ne μ b a ha]
      norm_num
  · intro v hv
    obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp hv
    rw [← hab]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (vecP_mem_eig μ hquad))
      (Submodule.smul_mem _ _ (vecM_mem_eig μ hquad))

theorem finrank_eig_mu (μ : ℂ) (hμ : μ = muP ∨ μ = muM) :
    Module.finrank ℂ ↥(eigSub μ) = 2 := by
  rw [eig_eq_span μ hμ]
  have hli : LinearIndepOn ℂ id {vecP μ, vecM μ} := by
    rw [LinearIndepOn.pair_iff id (vecP_ne_vecM μ)]
    intro a b hab
    have h0 := congrFun hab (blkIdx (0 : Fin 4) (0 : Fin 8))
    have h1 := congrFun hab (blkIdx (1 : Fin 4) (0 : Fin 8))
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, id_eq, vecP_blk00,
      vecM_blk00, Pi.zero_apply] at h0
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, id_eq, vecP_blk10,
      vecM_blk10, Pi.zero_apply] at h1
    constructor
    · have h7 : a * 7 = 0 := by linear_combination h0
      exact (mul_eq_zero.mp h7).resolve_right (by norm_num)
    · have h7 : b * 7 = 0 := by linear_combination h1
      exact (mul_eq_zero.mp h7).resolve_right (by norm_num)
  rw [finrank_span_set_eq_card hli, Set.toFinset_card, Fintype.card_eq_nat_card,
    Nat.card_coe_set_eq, Set.ncard_pair (vecP_ne_vecM μ)]

/-! ### The per-root γ-splits are (1, 1) -/

theorem finrank_eig_split_plus (μ : ℂ) (hμ : μ = muP ∨ μ = muM) :
    Module.finrank ℂ ↥(eigSub μ ⊓ gammaPlusSub) = 1 := by
  have hquad : μ ^ 2 - 51 * μ + 1 = 0 := muP_quad μ hμ
  have hEq : eigSub μ ⊓ gammaPlusSub = Submodule.span ℂ {vecP μ} := by
    apply le_antisymm
    · intro v hv
      obtain ⟨hve, hvp⟩ := hv
      obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp (eig_eq_span μ hμ ▸ hve)
      have hv0 : v (blkIdx (1 : Fin 4) (0 : Fin 8)) = 0 := by
        have hmem := (mem_coordEmb_range fPlus_inj v).mp hvp
        apply hmem
        rw [range_fPlus_bOf, blkIdx_bOf]
        norm_num
      have hb0 : b = 0 := by
        have h := congrFun hab (blkIdx (1 : Fin 4) (0 : Fin 8))
        rw [hv0, Pi.add_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul,
          smul_eq_mul, vecP_blk10, vecM_blk10] at h
        have h7 : b * 7 = 0 := by linear_combination h
        exact (mul_eq_zero.mp h7).resolve_right (by norm_num)
      rw [hb0, zero_smul, add_zero] at hab
      rw [← hab]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))
    · rw [Submodule.span_le]
      simp only [Set.singleton_subset_iff]
      exact ⟨vecP_mem_eig μ hquad, vecP_mem_gammaPlus μ⟩
  rw [hEq]
  exact finrank_span_singleton (vecP_ne_zero μ)

theorem finrank_eig_split_minus (μ : ℂ) (hμ : μ = muP ∨ μ = muM) :
    Module.finrank ℂ ↥(eigSub μ ⊓ gammaMinusSub) = 1 := by
  have hquad : μ ^ 2 - 51 * μ + 1 = 0 := muP_quad μ hμ
  have hEq : eigSub μ ⊓ gammaMinusSub = Submodule.span ℂ {vecM μ} := by
    apply le_antisymm
    · intro v hv
      obtain ⟨hve, hvm⟩ := hv
      obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp (eig_eq_span μ hμ ▸ hve)
      have hv0 : v (blkIdx (0 : Fin 4) (0 : Fin 8)) = 0 := by
        have hmem := (mem_coordEmb_range fMinus_inj v).mp hvm
        apply hmem
        rw [range_fMinus_bOf, blkIdx_bOf]
        norm_num
      have ha0 : a = 0 := by
        have h := congrFun hab (blkIdx (0 : Fin 4) (0 : Fin 8))
        rw [hv0, Pi.add_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul,
          smul_eq_mul, vecP_blk00, vecM_blk00] at h
        have h7 : a * 7 = 0 := by linear_combination h
        exact (mul_eq_zero.mp h7).resolve_right (by norm_num)
      rw [ha0, zero_smul, zero_add] at hab
      rw [← hab]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))
    · rw [Submodule.span_le]
      simp only [Set.singleton_subset_iff]
      exact ⟨vecM_mem_eig μ hquad, vecM_mem_gammaMinus μ⟩
  rw [hEq]
  exact finrank_span_singleton (vecM_ne_zero μ)

/-- **Obligation 1, assembled (the per-root separation).**  The two
    roots are distinct with sum 51 and product 1; each root's
    eigenspace has finrank 2 with γ-split (1, 1) — NOT the joint
    (2, 2) of VL-4a read per root. -/
theorem per_root_separation :
    muP + muM = 51 ∧ muP * muM = 1 ∧ muP ≠ muM ∧
    Module.finrank ℂ ↥(eigSub muP) = 2 ∧ Module.finrank ℂ ↥(eigSub muM) = 2 ∧
    Module.finrank ℂ ↥(eigSub muP ⊓ gammaPlusSub) = 1 ∧
    Module.finrank ℂ ↥(eigSub muP ⊓ gammaMinusSub) = 1 ∧
    Module.finrank ℂ ↥(eigSub muM ⊓ gammaPlusSub) = 1 ∧
    Module.finrank ℂ ↥(eigSub muM ⊓ gammaMinusSub) = 1 :=
  ⟨muP_add_muM, muP_mul_muM, muP_ne_muM,
   finrank_eig_mu muP (Or.inl rfl), finrank_eig_mu muM (Or.inr rfl),
   finrank_eig_split_plus muP (Or.inl rfl), finrank_eig_split_minus muP (Or.inl rfl),
   finrank_eig_split_plus muM (Or.inr rfl), finrank_eig_split_minus muM (Or.inr rfl)⟩


/-! ## §4. The centralizer of the folded seat matrix

`centQ` is the complex centralizer of `Qmat`.  Its elements are
parametrized by `CentParams`: an arbitrary `2 × 2` block on the
`qd = 4` seats, arbitrary `6 × 6` blocks on the `qd = 9` and
`qd = 25` seats, and a 2-dimensional coupled block `(w, x)` on the
pair `{0, 8}` (the folded shadow of §3's per-root (1, 1) splits:
on the coupled block, commuting with `[[1, 7], [7, 50]]` forces
`B 8 0 = B 0 8` and `B 8 8 = B 0 0 + 7 * B 0 8`, one complex degree
of freedom per root `μ±`).  Complex dimension: `4 + 36 + 36 + 2 = 78`. -/

/-- The complex centralizer of the folded seat matrix. -/
def centQ : Submodule ℂ (Matrix (Fin 16) (Fin 16) ℂ) where
  carrier := {B | Qmat * B = B * Qmat}
  add_mem' := by
    intro A B hA hB
    simp only [Set.mem_setOf_eq] at *
    rw [Matrix.mul_add, Matrix.add_mul, hA, hB]
  zero_mem' := by simp
  smul_mem' := by
    intro c B hB
    simp only [Set.mem_setOf_eq] at *
    rw [Matrix.mul_smul, Matrix.smul_mul, hB]

theorem mem_centQ {B : Matrix (Fin 16) (Fin 16) ℂ} :
    B ∈ centQ ↔ Qmat * B = B * Qmat := Iff.rfl

/-- The parameter space of the centralizer. -/
abbrev CentParams : Type :=
  (Fin 2 → Fin 2 → ℂ) ×
  ((Fin 2 × Fin 3) → (Fin 2 × Fin 3) → ℂ) ×
  ((Fin 2 × Fin 3) → (Fin 2 × Fin 3) → ℂ) × ℂ × ℂ

/-- The `qd = 4` block term. -/
noncomputable def t4 (A : Fin 2 → Fin 2 → ℂ) : Matrix (Fin 16) (Fin 16) ℂ :=
  fun a b => if qd a = 4 ∧ qd b = 4 then A (pos4 a) (pos4 b) else 0

/-- The `qd = 9` block term. -/
noncomputable def t9 (A : (Fin 2 × Fin 3) → (Fin 2 × Fin 3) → ℂ) : Matrix (Fin 16) (Fin 16) ℂ :=
  fun a b => if qd a = 9 ∧ qd b = 9 then A (pos9 a) (pos9 b) else 0

/-- The `qd = 25` block term. -/
noncomputable def t25 (A : (Fin 2 × Fin 3) → (Fin 2 × Fin 3) → ℂ) : Matrix (Fin 16) (Fin 16) ℂ :=
  fun a b => if qd a = 25 ∧ qd b = 25 then A (pos25 a) (pos25 b) else 0

/-- Entries of the coupled block: the general matrix commuting with
    `[[1, 7], [7, 50]]`, with diagonal parameters `(w, x)`. -/
noncomputable def quadEntry (w x : ℂ) (a b : Fin 16) : ℂ :=
  if a = 0 then (if b = 0 then w else x)
  else (if b = 0 then x else w + 7 * x)

/-- The coupled block term. -/
noncomputable def tQ (w x : ℂ) : Matrix (Fin 16) (Fin 16) ℂ :=
  fun a b => if (a = 0 ∨ a = 8) ∧ (b = 0 ∨ b = 8) then quadEntry w x a b else 0

theorem t4_apply (A : Fin 2 → Fin 2 → ℂ) (a b : Fin 16) :
    t4 A a b = if qd a = 4 ∧ qd b = 4 then A (pos4 a) (pos4 b) else 0 := rfl

theorem t9_apply (A : (Fin 2 × Fin 3) → (Fin 2 × Fin 3) → ℂ) (a b : Fin 16) :
    t9 A a b = if qd a = 9 ∧ qd b = 9 then A (pos9 a) (pos9 b) else 0 := rfl

theorem t25_apply (A : (Fin 2 × Fin 3) → (Fin 2 × Fin 3) → ℂ) (a b : Fin 16) :
    t25 A a b = if qd a = 25 ∧ qd b = 25 then A (pos25 a) (pos25 b) else 0 := rfl

theorem tQ_apply (w x : ℂ) (a b : Fin 16) :
    tQ w x a b
      = if (a = 0 ∨ a = 8) ∧ (b = 0 ∨ b = 8) then quadEntry w x a b else 0 := rfl

theorem t4_p4 (A : Fin 2 → Fin 2 → ℂ) (s t : Fin 2) :
    t4 A (p4 s) (p4 t) = A s t := by
  rw [t4_apply, ite_eq_left ⟨qd_p4 s, qd_p4 t⟩, pos4_p4, pos4_p4]

theorem t9_p9 (A : (Fin 2 × Fin 3) → (Fin 2 × Fin 3) → ℂ)
    (s t : Fin 2 × Fin 3) : t9 A (p9 s) (p9 t) = A s t := by
  rw [t9_apply, ite_eq_left ⟨qd_p9 s, qd_p9 t⟩, pos9_p9, pos9_p9]

theorem t25_p25 (A : (Fin 2 × Fin 3) → (Fin 2 × Fin 3) → ℂ)
    (s t : Fin 2 × Fin 3) : t25 A (p25 s) (p25 t) = A s t := by
  rw [t25_apply, ite_eq_left ⟨qd_p25 s, qd_p25 t⟩, pos25_p25, pos25_p25]

theorem t4_eq_zero_of_qd_ne_left (A : Fin 2 → Fin 2 → ℂ) {a b : Fin 16}
    (h : qd a ≠ 4) : t4 A a b = 0 := by
  rw [t4_apply]; exact ite_eq_right (fun hh => h hh.1)

theorem t4_eq_zero_of_qd_ne_right (A : Fin 2 → Fin 2 → ℂ) {a b : Fin 16}
    (h : qd b ≠ 4) : t4 A a b = 0 := by
  rw [t4_apply]; exact ite_eq_right (fun hh => h hh.2)

theorem t9_eq_zero_of_qd_ne_left
    (A : (Fin 2 × Fin 3) → (Fin 2 × Fin 3) → ℂ) {a b : Fin 16}
    (h : qd a ≠ 9) : t9 A a b = 0 := by
  rw [t9_apply]; exact ite_eq_right (fun hh => h hh.1)

theorem t9_eq_zero_of_qd_ne_right
    (A : (Fin 2 × Fin 3) → (Fin 2 × Fin 3) → ℂ) {a b : Fin 16}
    (h : qd b ≠ 9) : t9 A a b = 0 := by
  rw [t9_apply]; exact ite_eq_right (fun hh => h hh.2)

theorem t25_eq_zero_of_qd_ne_left
    (A : (Fin 2 × Fin 3) → (Fin 2 × Fin 3) → ℂ) {a b : Fin 16}
    (h : qd a ≠ 25) : t25 A a b = 0 := by
  rw [t25_apply]; exact ite_eq_right (fun hh => h hh.1)

theorem t25_eq_zero_of_qd_ne_right
    (A : (Fin 2 × Fin 3) → (Fin 2 × Fin 3) → ℂ) {a b : Fin 16}
    (h : qd b ≠ 25) : t25 A a b = 0 := by
  rw [t25_apply]; exact ite_eq_right (fun hh => h hh.2)

theorem tQ_eq_zero_of_not_coupled_left (w x : ℂ) {a b : Fin 16}
    (h : ¬ (a = 0 ∨ a = 8)) : tQ w x a b = 0 := by
  rw [tQ_apply]; exact ite_eq_right (fun hh => h hh.1)

theorem tQ_eq_zero_of_not_coupled_right (w x : ℂ) {a b : Fin 16}
    (h : ¬ (b = 0 ∨ b = 8)) : tQ w x a b = 0 := by
  rw [tQ_apply]; exact ite_eq_right (fun hh => h hh.2)

theorem quadEntry_zero_zero (w x : ℂ) : quadEntry w x 0 0 = w :=
  (ite_eq_left rfl).trans (ite_eq_left rfl)

theorem quadEntry_zero_eight (w x : ℂ) : quadEntry w x 0 8 = x :=
  (ite_eq_left rfl).trans (ite_eq_right (by decide : (8 : Fin 16) ≠ 0))

theorem quadEntry_eight_zero (w x : ℂ) : quadEntry w x 8 0 = x :=
  (ite_eq_right (by decide : (8 : Fin 16) ≠ 0)).trans (ite_eq_left rfl)

theorem quadEntry_eight_eight (w x : ℂ) : quadEntry w x 8 8 = w + 7 * x :=
  (ite_eq_right (by decide : (8 : Fin 16) ≠ 0)).trans
    (ite_eq_right (by decide : (8 : Fin 16) ≠ 0))

theorem tQ_zero_zero (w x : ℂ) : tQ w x 0 0 = w :=
  (ite_eq_left ⟨Or.inl rfl, Or.inl rfl⟩).trans (quadEntry_zero_zero w x)

theorem tQ_zero_eight (w x : ℂ) : tQ w x 0 8 = x :=
  (ite_eq_left ⟨Or.inl rfl, Or.inr rfl⟩).trans (quadEntry_zero_eight w x)

theorem tQ_eight_zero (w x : ℂ) : tQ w x 8 0 = x :=
  (ite_eq_left ⟨Or.inr rfl, Or.inl rfl⟩).trans (quadEntry_eight_zero w x)

theorem tQ_eight_eight (w x : ℂ) : tQ w x 8 8 = w + 7 * x :=
  (ite_eq_left ⟨Or.inr rfl, Or.inr rfl⟩).trans (quadEntry_eight_eight w x)

/-- Assembling a centralizer element from its parameters. -/
noncomputable def basm (P : CentParams) : Matrix (Fin 16) (Fin 16) ℂ :=
  fun a b => t4 P.1 a b + t9 P.2.1 a b + t25 P.2.2.1 a b
    + tQ P.2.2.2.1 P.2.2.2.2 a b

theorem basm_apply (P : CentParams) (a b : Fin 16) :
    basm P a b = t4 P.1 a b + t9 P.2.1 a b + t25 P.2.2.1 a b
      + tQ P.2.2.2.1 P.2.2.2.2 a b := rfl

/-- Reading the parameters off a matrix. -/
def paramsOf (B : Matrix (Fin 16) (Fin 16) ℂ) : CentParams :=
  (fun s t => B (p4 s) (p4 t),
   fun s t => B (p9 s) (p9 t),
   fun s t => B (p25 s) (p25 t),
   B 0 0, B 0 8)

/-! ### The entry equation and its vanishing consequences -/

theorem not_coupled_flip8 {a : Fin 16} (h : ¬ (a = 0 ∨ a = 8)) :
    ¬ (flip8 a = 0 ∨ flip8 a = 8) := by
  intro hh
  rcases hh with hh | hh
  · apply h
    have h2 : flip8 (flip8 a) = flip8 0 := by rw [hh]
    rw [flip8_flip8, flip8_zero] at h2
    exact Or.inr h2
  · apply h
    have h2 : flip8 (flip8 a) = flip8 8 := by rw [hh]
    rw [flip8_flip8, flip8_eight] at h2
    exact Or.inl h2

theorem centQ_entry_eq {B : Matrix (Fin 16) (Fin 16) ℂ} (hB : B ∈ centQ)
    (a b : Fin 16) :
    qd a * B a b + qc a * B (flip8 a) b
      = B a b * qd b + B a (flip8 b) * qc (flip8 b) := by
  have h : Qmat * B = B * Qmat := hB
  have h2 : (Qmat * B) a b = (B * Qmat) a b := congrFun (congrFun h a) b
  rwa [Qmat_mul_apply, mul_Qmat_apply] at h2

theorem centQ_entry_eq_zero_of_ne {B : Matrix (Fin 16) (Fin 16) ℂ}
    (hB : B ∈ centQ) {a b : Fin 16} (ha : ¬ (a = 0 ∨ a = 8))
    (hb : ¬ (b = 0 ∨ b = 8)) (h : qd a ≠ qd b) : B a b = 0 := by
  have e := centQ_entry_eq hB a b
  rw [qc_eq_zero_of_not_coupled a ha,
    qc_eq_zero_of_not_coupled (flip8 b) (not_coupled_flip8 hb)] at e
  have e2 : (qd a - qd b) * B a b = 0 := by linear_combination e
  rcases mul_eq_zero.mp e2 with h0 | h0
  · exact absurd (sub_eq_zero.mp h0) h
  · exact h0

theorem centQ_entry_eq_zero_coupled_left {B : Matrix (Fin 16) (Fin 16) ℂ}
    (hB : B ∈ centQ) {a b : Fin 16} (ha : a = 0 ∨ a = 8)
    (hb : ¬ (b = 0 ∨ b = 8)) : B a b = 0 := by
  have e1 := centQ_entry_eq hB a b
  have e2 := centQ_entry_eq hB (flip8 a) b
  obtain ⟨hsum, hprod, hqc⟩ := coupled_flip a ha
  have hqc' : qc (flip8 a) = 7 := (qc_flip8 a).trans hqc
  have hqcb : qc (flip8 b) = 0 :=
    qc_eq_zero_of_not_coupled (flip8 b) (not_coupled_flip8 hb)
  rw [hqc, hqcb] at e1
  rw [hqc', hqcb] at e2
  rw [flip8_flip8] at e2
  have key : (qd b ^ 2 - 51 * qd b + 1) * B a b = 0 := by
    linear_combination (qd (flip8 a) - qd b) * e1 - 7 * e2
      - (B a b) * hprod + (qd b * B a b) * hsum
  have hqb : qd b = 4 ∨ qd b = 9 ∨ qd b = 25 := by
    rcases seat_class b with hc | h4 | h9 | h25
    · exact absurd hc hb
    · exact Or.inl h4
    · exact Or.inr (Or.inl h9)
    · exact Or.inr (Or.inr h25)
  rcases mul_eq_zero.mp key with h0 | h0
  · exact absurd h0 (qd_sq_ne b hqb)
  · exact h0

theorem centQ_entry_eq_zero_coupled_right {B : Matrix (Fin 16) (Fin 16) ℂ}
    (hB : B ∈ centQ) {a b : Fin 16} (ha : ¬ (a = 0 ∨ a = 8))
    (hb : b = 0 ∨ b = 8) : B a b = 0 := by
  have e1 := centQ_entry_eq hB a b
  have e2 := centQ_entry_eq hB a (flip8 b)
  obtain ⟨hsum, hprod, hqc⟩ := coupled_flip b hb
  have hqa0 : qc a = 0 := qc_eq_zero_of_not_coupled a ha
  have hqfb7 : qc (flip8 b) = 7 := (qc_flip8 b).trans hqc
  rw [flip8_flip8] at e2
  rw [hqa0, hqfb7] at e1
  rw [hqa0, hqc] at e2
  have key : (qd a ^ 2 - 51 * qd a + 1) * B a b = 0 := by
    linear_combination (qd a - qd (flip8 b)) * e1 + 7 * e2
      + (qd a * B a b) * hsum - (B a b) * hprod
  have hqa : qd a = 4 ∨ qd a = 9 ∨ qd a = 25 := by
    rcases seat_class a with hc | h4 | h9 | h25
    · exact absurd hc ha
    · exact Or.inl h4
    · exact Or.inr (Or.inl h9)
    · exact Or.inr (Or.inr h25)
  rcases mul_eq_zero.mp key with h0 | h0
  · exact absurd h0 (qd_sq_ne a hqa)
  · exact h0

theorem centQ_eight_zero {B : Matrix (Fin 16) (Fin 16) ℂ} (hB : B ∈ centQ) :
    B 8 0 = B 0 8 := by
  have e := centQ_entry_eq hB 0 0
  rw [flip8_zero, qd_zero, qc_zero, qc_eight] at e
  linear_combination e / 7

theorem centQ_eight_eight {B : Matrix (Fin 16) (Fin 16) ℂ} (hB : B ∈ centQ) :
    B 8 8 = B 0 0 + 7 * B 0 8 := by
  have e := centQ_entry_eq hB 0 8
  rw [flip8_zero, flip8_eight, qd_zero, qd_eight, qc_zero] at e
  linear_combination e / 7


/-! ### Each block term commutes with `Qmat` pointwise -/

theorem t4_id (A : Fin 2 → Fin 2 → ℂ) (a b : Fin 16) :
    qd a * t4 A a b + qc a * t4 A (flip8 a) b
      = t4 A a b * qd b + t4 A a (flip8 b) * qc (flip8 b) := by
  by_cases ha : (a = 0 ∨ a = 8)
  · have hqa : qd a ≠ 4 := by
      rcases ha with rfl | rfl
      · rw [qd_zero]; norm_num
      · rw [qd_eight]; norm_num
    have hqfa : qd (flip8 a) ≠ 4 := by
      rcases ha with rfl | rfl
      · rw [flip8_zero, qd_eight]; norm_num
      · rw [flip8_eight, qd_zero]; norm_num
    rw [t4_eq_zero_of_qd_ne_left A hqa, t4_eq_zero_of_qd_ne_left A hqfa,
      t4_eq_zero_of_qd_ne_left A hqa]
    simp
  · by_cases hb : (b = 0 ∨ b = 8)
    · have hqb : qd b ≠ 4 := by
        rcases hb with rfl | rfl
        · rw [qd_zero]; norm_num
        · rw [qd_eight]; norm_num
      have hqfb : qd (flip8 b) ≠ 4 := by
        rcases hb with rfl | rfl
        · rw [flip8_zero, qd_eight]; norm_num
        · rw [flip8_eight, qd_zero]; norm_num
      have hqa0 : qc a = 0 := qc_eq_zero_of_not_coupled a ha
      rw [t4_eq_zero_of_qd_ne_right A hqb, t4_eq_zero_of_qd_ne_right A hqfb, hqa0]
      simp
    · have hqa0 : qc a = 0 := qc_eq_zero_of_not_coupled a ha
      have hqfb0 : qc (flip8 b) = 0 :=
        qc_eq_zero_of_not_coupled (flip8 b) (not_coupled_flip8 hb)
      rw [hqa0, hqfb0]
      by_cases h44 : qd a = 4 ∧ qd b = 4
      · rw [t4_apply, ite_eq_left h44, h44.1, h44.2]; ring
      · rcases not_and_or.mp h44 with h | h
        · rw [t4_eq_zero_of_qd_ne_left A h]; ring
        · rw [t4_eq_zero_of_qd_ne_right A h]; ring

theorem t9_id (A : (Fin 2 × Fin 3) → (Fin 2 × Fin 3) → ℂ) (a b : Fin 16) :
    qd a * t9 A a b + qc a * t9 A (flip8 a) b
      = t9 A a b * qd b + t9 A a (flip8 b) * qc (flip8 b) := by
  by_cases ha : (a = 0 ∨ a = 8)
  · have hqa : qd a ≠ 9 := by
      rcases ha with rfl | rfl
      · rw [qd_zero]; norm_num
      · rw [qd_eight]; norm_num
    have hqfa : qd (flip8 a) ≠ 9 := by
      rcases ha with rfl | rfl
      · rw [flip8_zero, qd_eight]; norm_num
      · rw [flip8_eight, qd_zero]; norm_num
    rw [t9_eq_zero_of_qd_ne_left A hqa, t9_eq_zero_of_qd_ne_left A hqfa,
      t9_eq_zero_of_qd_ne_left A hqa]
    simp
  · by_cases hb : (b = 0 ∨ b = 8)
    · have hqb : qd b ≠ 9 := by
        rcases hb with rfl | rfl
        · rw [qd_zero]; norm_num
        · rw [qd_eight]; norm_num
      have hqfb : qd (flip8 b) ≠ 9 := by
        rcases hb with rfl | rfl
        · rw [flip8_zero, qd_eight]; norm_num
        · rw [flip8_eight, qd_zero]; norm_num
      have hqa0 : qc a = 0 := qc_eq_zero_of_not_coupled a ha
      rw [t9_eq_zero_of_qd_ne_right A hqb, t9_eq_zero_of_qd_ne_right A hqfb, hqa0]
      simp
    · have hqa0 : qc a = 0 := qc_eq_zero_of_not_coupled a ha
      have hqfb0 : qc (flip8 b) = 0 :=
        qc_eq_zero_of_not_coupled (flip8 b) (not_coupled_flip8 hb)
      rw [hqa0, hqfb0]
      by_cases h99 : qd a = 9 ∧ qd b = 9
      · rw [t9_apply, ite_eq_left h99, h99.1, h99.2]; ring
      · rcases not_and_or.mp h99 with h | h
        · rw [t9_eq_zero_of_qd_ne_left A h]; ring
        · rw [t9_eq_zero_of_qd_ne_right A h]; ring

theorem t25_id (A : (Fin 2 × Fin 3) → (Fin 2 × Fin 3) → ℂ) (a b : Fin 16) :
    qd a * t25 A a b + qc a * t25 A (flip8 a) b
      = t25 A a b * qd b + t25 A a (flip8 b) * qc (flip8 b) := by
  by_cases ha : (a = 0 ∨ a = 8)
  · have hqa : qd a ≠ 25 := by
      rcases ha with rfl | rfl
      · rw [qd_zero]; norm_num
      · rw [qd_eight]; norm_num
    have hqfa : qd (flip8 a) ≠ 25 := by
      rcases ha with rfl | rfl
      · rw [flip8_zero, qd_eight]; norm_num
      · rw [flip8_eight, qd_zero]; norm_num
    rw [t25_eq_zero_of_qd_ne_left A hqa, t25_eq_zero_of_qd_ne_left A hqfa,
      t25_eq_zero_of_qd_ne_left A hqa]
    simp
  · by_cases hb : (b = 0 ∨ b = 8)
    · have hqb : qd b ≠ 25 := by
        rcases hb with rfl | rfl
        · rw [qd_zero]; norm_num
        · rw [qd_eight]; norm_num
      have hqfb : qd (flip8 b) ≠ 25 := by
        rcases hb with rfl | rfl
        · rw [flip8_zero, qd_eight]; norm_num
        · rw [flip8_eight, qd_zero]; norm_num
      have hqa0 : qc a = 0 := qc_eq_zero_of_not_coupled a ha
      rw [t25_eq_zero_of_qd_ne_right A hqb, t25_eq_zero_of_qd_ne_right A hqfb, hqa0]
      simp
    · have hqa0 : qc a = 0 := qc_eq_zero_of_not_coupled a ha
      have hqfb0 : qc (flip8 b) = 0 :=
        qc_eq_zero_of_not_coupled (flip8 b) (not_coupled_flip8 hb)
      rw [hqa0, hqfb0]
      by_cases h22 : qd a = 25 ∧ qd b = 25
      · rw [t25_apply, ite_eq_left h22, h22.1, h22.2]; ring
      · rcases not_and_or.mp h22 with h | h
        · rw [t25_eq_zero_of_qd_ne_left A h]; ring
        · rw [t25_eq_zero_of_qd_ne_right A h]; ring

theorem tQ_id (w x : ℂ) (a b : Fin 16) :
    qd a * tQ w x a b + qc a * tQ w x (flip8 a) b
      = tQ w x a b * qd b + tQ w x a (flip8 b) * qc (flip8 b) := by
  by_cases ha : (a = 0 ∨ a = 8)
  · by_cases hb : (b = 0 ∨ b = 8)
    · rcases ha with rfl | rfl
      · rcases hb with rfl | rfl
        · rw [flip8_zero, qd_zero, qc_zero, qc_eight, tQ_zero_zero, tQ_eight_zero,
            tQ_zero_eight]
          ring
        · rw [flip8_zero, flip8_eight, qd_zero, qd_eight, qc_zero, tQ_zero_eight,
            tQ_eight_eight, tQ_zero_zero]
          ring
      · rcases hb with rfl | rfl
        · rw [flip8_eight, flip8_zero, qd_eight, qd_zero, qc_eight,
            tQ_eight_zero, tQ_zero_zero, tQ_eight_eight]
          ring
        · rw [flip8_eight, qd_eight, qc_eight, qc_zero, tQ_eight_eight,
            tQ_zero_eight, tQ_eight_zero]
          ring
    · rw [tQ_eq_zero_of_not_coupled_right w x hb,
        tQ_eq_zero_of_not_coupled_right w x hb,
        tQ_eq_zero_of_not_coupled_right w x (not_coupled_flip8 hb)]
      simp
  · by_cases hb : (b = 0 ∨ b = 8)
    · rw [tQ_eq_zero_of_not_coupled_left w x ha,
        tQ_eq_zero_of_not_coupled_left w x (not_coupled_flip8 ha),
        tQ_eq_zero_of_not_coupled_left w x ha]
      simp
    · rw [tQ_eq_zero_of_not_coupled_left w x ha,
        tQ_eq_zero_of_not_coupled_left w x (not_coupled_flip8 ha),
        tQ_eq_zero_of_not_coupled_left w x ha]
      simp

theorem basm_mem (P : CentParams) : basm P ∈ centQ := by
  rw [mem_centQ]
  funext a b
  have h4 := t4_id P.1 a b
  have h9 := t9_id P.2.1 a b
  have h25 := t25_id P.2.2.1 a b
  have hQ := tQ_id P.2.2.2.1 P.2.2.2.2 a b
  rw [Qmat_mul_apply, mul_Qmat_apply, basm_apply, basm_apply, basm_apply]
  linear_combination h4 + h9 + h25 + hQ

/-! ### The parametrization is a bijection -/

theorem paramsOf_basm (P : CentParams) : paramsOf (basm P) = P := by
  have h4nc : ∀ s : Fin 2, ¬ (p4 s = 0 ∨ p4 s = 8) := by
    intro s h
    rcases h with h | h
    · have hq := qd_p4 s; rw [h, qd_zero] at hq; norm_num at hq
    · have hq := qd_p4 s; rw [h, qd_eight] at hq; norm_num at hq
  have h9nc : ∀ s : Fin 2 × Fin 3, ¬ (p9 s = 0 ∨ p9 s = 8) := by
    intro s h
    rcases h with h | h
    · have hq := qd_p9 s; rw [h, qd_zero] at hq; norm_num at hq
    · have hq := qd_p9 s; rw [h, qd_eight] at hq; norm_num at hq
  have h25nc : ∀ s : Fin 2 × Fin 3, ¬ (p25 s = 0 ∨ p25 s = 8) := by
    intro s h
    rcases h with h | h
    · have hq := qd_p25 s; rw [h, qd_zero] at hq; norm_num at hq
    · have hq := qd_p25 s; rw [h, qd_eight] at hq; norm_num at hq
  obtain ⟨A4, A9, A25, w, x⟩ := P
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)))
  · funext s t
    show basm (A4, A9, A25, w, x) (p4 s) (p4 t) = A4 s t
    rw [basm_apply, t4_p4,
      t9_eq_zero_of_qd_ne_left _ (show qd (p4 s) ≠ 9 by rw [qd_p4]; norm_num),
      t25_eq_zero_of_qd_ne_left _ (show qd (p4 s) ≠ 25 by rw [qd_p4]; norm_num),
      tQ_eq_zero_of_not_coupled_left _ _ (h4nc s)]
    simp
  · funext s t
    show basm (A4, A9, A25, w, x) (p9 s) (p9 t) = A9 s t
    rw [basm_apply,
      t4_eq_zero_of_qd_ne_left _ (show qd (p9 s) ≠ 4 by rw [qd_p9]; norm_num),
      t9_p9,
      t25_eq_zero_of_qd_ne_left _ (show qd (p9 s) ≠ 25 by rw [qd_p9]; norm_num),
      tQ_eq_zero_of_not_coupled_left _ _ (h9nc s)]
    simp
  · funext s t
    show basm (A4, A9, A25, w, x) (p25 s) (p25 t) = A25 s t
    rw [basm_apply,
      t4_eq_zero_of_qd_ne_left _ (show qd (p25 s) ≠ 4 by rw [qd_p25]; norm_num),
      t9_eq_zero_of_qd_ne_left _ (show qd (p25 s) ≠ 9 by rw [qd_p25]; norm_num),
      t25_p25,
      tQ_eq_zero_of_not_coupled_left _ _ (h25nc s)]
    simp
  · show basm (A4, A9, A25, w, x) 0 0 = w
    rw [basm_apply,
      t4_eq_zero_of_qd_ne_left _ (show qd (0 : Fin 16) ≠ 4 by rw [qd_zero]; norm_num),
      t9_eq_zero_of_qd_ne_left _ (show qd (0 : Fin 16) ≠ 9 by rw [qd_zero]; norm_num),
      t25_eq_zero_of_qd_ne_left _ (show qd (0 : Fin 16) ≠ 25 by rw [qd_zero]; norm_num),
      tQ_zero_zero]
    simp
  · show basm (A4, A9, A25, w, x) 0 8 = x
    rw [basm_apply,
      t4_eq_zero_of_qd_ne_left _ (show qd (0 : Fin 16) ≠ 4 by rw [qd_zero]; norm_num),
      t9_eq_zero_of_qd_ne_left _ (show qd (0 : Fin 16) ≠ 9 by rw [qd_zero]; norm_num),
      t25_eq_zero_of_qd_ne_left _ (show qd (0 : Fin 16) ≠ 25 by rw [qd_zero]; norm_num),
      tQ_zero_eight]
    simp

theorem basm_paramsOf {B : Matrix (Fin 16) (Fin 16) ℂ} (hB : B ∈ centQ) :
    basm (paramsOf B) = B := by
  have hw : (paramsOf B).2.2.2.1 = B 0 0 := rfl
  have hx : (paramsOf B).2.2.2.2 = B 0 8 := rfl
  funext a b
  rw [basm_apply]
  rcases seat_class a with ha | ha | ha | ha
  · have hqa4 : qd a ≠ 4 := by
      rcases ha with rfl | rfl
      · rw [qd_zero]; norm_num
      · rw [qd_eight]; norm_num
    have hqa9 : qd a ≠ 9 := by
      rcases ha with rfl | rfl
      · rw [qd_zero]; norm_num
      · rw [qd_eight]; norm_num
    have hqa25 : qd a ≠ 25 := by
      rcases ha with rfl | rfl
      · rw [qd_zero]; norm_num
      · rw [qd_eight]; norm_num
    rw [t4_eq_zero_of_qd_ne_left _ hqa4, t9_eq_zero_of_qd_ne_left _ hqa9,
      t25_eq_zero_of_qd_ne_left _ hqa25]
    by_cases hb : (b = 0 ∨ b = 8)
    · rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · rw [tQ_zero_zero, hw]; simp
      · rw [tQ_zero_eight, hx]; simp
      · rw [tQ_eight_zero, hx, ← centQ_eight_zero hB]; simp
      · rw [tQ_eight_eight, hw, hx, ← centQ_eight_eight hB]; simp
    · rw [tQ_eq_zero_of_not_coupled_right _ _ hb,
        centQ_entry_eq_zero_coupled_left hB ha hb]
      simp
  · have ha4 : qd a = 4 := ha
    have hanc : ¬ (a = 0 ∨ a = 8) := by
      intro h
      rcases h with rfl | rfl
      · rw [qd_zero] at ha4; norm_num at ha4
      · rw [qd_eight] at ha4; norm_num at ha4
    rw [t9_eq_zero_of_qd_ne_left _ (show qd a ≠ 9 by rw [ha4]; norm_num),
      t25_eq_zero_of_qd_ne_left _ (show qd a ≠ 25 by rw [ha4]; norm_num),
      tQ_eq_zero_of_not_coupled_left _ _ hanc]
    by_cases hb4 : qd b = 4
    · rw [t4_apply, ite_eq_left ⟨ha4, hb4⟩]
      show (paramsOf B).1 (pos4 a) (pos4 b) + 0 + 0 + 0 = B a b
      show B (p4 (pos4 a)) (p4 (pos4 b)) + 0 + 0 + 0 = B a b
      rw [p4_pos4 a ((qd_eq_four_iff a).mp ha4), p4_pos4 b ((qd_eq_four_iff b).mp hb4)]
      simp
    · rw [t4_eq_zero_of_qd_ne_right _ hb4]
      by_cases hbc : (b = 0 ∨ b = 8)
      · rw [centQ_entry_eq_zero_coupled_right hB hanc hbc]; simp
      · rw [centQ_entry_eq_zero_of_ne hB hanc hbc (fun h => hb4 (h ▸ ha4))]; simp
  · have ha9 : qd a = 9 := ha
    have hanc : ¬ (a = 0 ∨ a = 8) := by
      intro h
      rcases h with rfl | rfl
      · rw [qd_zero] at ha9; norm_num at ha9
      · rw [qd_eight] at ha9; norm_num at ha9
    rw [t4_eq_zero_of_qd_ne_left _ (show qd a ≠ 4 by rw [ha9]; norm_num),
      t25_eq_zero_of_qd_ne_left _ (show qd a ≠ 25 by rw [ha9]; norm_num),
      tQ_eq_zero_of_not_coupled_left _ _ hanc]
    by_cases hb9 : qd b = 9
    · rw [t9_apply, ite_eq_left ⟨ha9, hb9⟩]
      show 0 + (paramsOf B).2.1 (pos9 a) (pos9 b) + 0 + 0 = B a b
      show 0 + B (p9 (pos9 a)) (p9 (pos9 b)) + 0 + 0 = B a b
      rw [p9_pos9 a ((qd_eq_nine_iff a).mp ha9), p9_pos9 b ((qd_eq_nine_iff b).mp hb9)]
      simp
    · rw [t9_eq_zero_of_qd_ne_right _ hb9]
      by_cases hbc : (b = 0 ∨ b = 8)
      · rw [centQ_entry_eq_zero_coupled_right hB hanc hbc]; simp
      · rw [centQ_entry_eq_zero_of_ne hB hanc hbc (fun h => hb9 (h ▸ ha9))]; simp
  · have ha25 : qd a = 25 := ha
    have hanc : ¬ (a = 0 ∨ a = 8) := by
      intro h
      rcases h with rfl | rfl
      · rw [qd_zero] at ha25; norm_num at ha25
      · rw [qd_eight] at ha25; norm_num at ha25
    rw [t4_eq_zero_of_qd_ne_left _ (show qd a ≠ 4 by rw [ha25]; norm_num),
      t9_eq_zero_of_qd_ne_left _ (show qd a ≠ 9 by rw [ha25]; norm_num),
      tQ_eq_zero_of_not_coupled_left _ _ hanc]
    by_cases hb25 : qd b = 25
    · rw [t25_apply, ite_eq_left ⟨ha25, hb25⟩]
      show 0 + 0 + (paramsOf B).2.2.1 (pos25 a) (pos25 b) + 0 = B a b
      show 0 + 0 + B (p25 (pos25 a)) (p25 (pos25 b)) + 0 = B a b
      rw [p25_pos25 a ((qd_eq_twentyfive_iff a).mp ha25),
        p25_pos25 b ((qd_eq_twentyfive_iff b).mp hb25)]
      simp
    · rw [t25_eq_zero_of_qd_ne_right _ hb25]
      by_cases hbc : (b = 0 ∨ b = 8)
      · rw [centQ_entry_eq_zero_coupled_right hB hanc hbc]; simp
      · rw [centQ_entry_eq_zero_of_ne hB hanc hbc (fun h => hb25 (h ▸ ha25))]; simp

/-- The centralizer of `Qmat` is complex-linearly equivalent to its
    parameter space. -/
noncomputable def centQEquiv : ↥centQ ≃ₗ[ℂ] CentParams where
  toFun B := paramsOf B.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun P := ⟨basm P, basm_mem P⟩
  left_inv B := Subtype.ext (basm_paramsOf B.2)
  right_inv P := paramsOf_basm P

theorem finrank_centQ : Module.finrank ℂ ↥centQ = 78 := by
  rw [centQEquiv.finrank_eq]
  simp only [Module.finrank_prod, Module.finrank_pi_fintype,
    Module.finrank_self, Fintype.card_prod, Fintype.card_fin, Finset.sum_const,
    Finset.card_univ, smul_eq_mul]


/-! ## §5. The locus and the count 156

`locusB` is the real locus of the pack: Hermitian, γ-odd matrices
commuting with `K0`, as a real submodule.  The folded cross-block
map `X ↦ crossCoordOf X` (of `Census96Decoupling`) sends it into
`centQ` — both sector blocks of `K0` read as `Qmat` in folded
coordinates, the plus block directly (`Qmat_apply_plus`) and the
minus block through the `flip8` twist (`Qmat_apply_minus`), with
`qc` flip8-invariant closing the equation.  The inverse is `matOf`,
assembling a Hermitian odd matrix from a folded block.  Hence
`finrank ℝ ↥locusB = 2 * 78 = 156`, the block sum
`8 + 72 + 72 + 2 + 2` of BR1-027 read through the parametrization:
`2·(2·2) + 2·(6·6) + 2·(6·6) + 2·(1·1) + 2·(1·1)`. -/

/-- **The locus at Seat B** (the pack's carrier): Hermitian,
    grading-odd matrices on `I32` commuting with `K0`, as a real
    submodule. -/
def locusB : Submodule ℝ (Matrix I32 I32 ℂ) where
  carrier := {X | Xᴴ = X ∧ gammaF * X + X * gammaF = 0 ∧ X * K0 = K0 * X}
  add_mem' := by
    rintro X Y ⟨hX1, hX2, hX3⟩ ⟨hY1, hY2, hY3⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [Matrix.conjTranspose_add, hX1, hY1]
    · have h3 : (gammaF * X + gammaF * Y) + (X * gammaF + Y * gammaF)
          = (gammaF * X + X * gammaF) + (gammaF * Y + Y * gammaF) := by
        ac_rfl
      show gammaF * (X + Y) + (X + Y) * gammaF = 0
      rw [Matrix.mul_add, Matrix.add_mul, h3, hX2, hY2, add_zero]
    · show (X + Y) * K0 = K0 * (X + Y)
      rw [Matrix.add_mul, Matrix.mul_add, hX3, hY3]
  zero_mem' := by
    refine ⟨?_, ?_, ?_⟩
    · show (0 : Matrix I32 I32 ℂ)ᴴ = 0; simp
    · show gammaF * (0 : Matrix I32 I32 ℂ) + (0 : Matrix I32 I32 ℂ)
        * gammaF = 0; simp
    · show (0 : Matrix I32 I32 ℂ) * K0 = K0 * (0 : Matrix I32 I32 ℂ); simp
  smul_mem' := by
    intro c X hX
    obtain ⟨hX1, hX2, hX3⟩ := hX
    refine ⟨?_, ?_, ?_⟩
    · have hS : (c • X)ᴴ = c • Xᴴ := by
        ext i j
        have e1 : ((c • X) j i) = c • (X j i) := rfl
        have e2 : ((c • Xᴴ) i j) = c • (Xᴴ i j) := rfl
        rw [Matrix.conjTranspose_apply, e1, census96_star_real_smul, e2,
          Matrix.conjTranspose_apply]
      show (c • X)ᴴ = c • X
      rw [hS, hX1]
    · have hG : gammaF * (c • X) + (c • X) * gammaF
          = c • (gammaF * X + X * gammaF) := by
        rw [Matrix.mul_smul, Matrix.smul_mul, ← smul_add]
      show gammaF * (c • X) + (c • X) * gammaF = 0
      rw [hG, hX2, smul_zero]
    · show (c • X) * K0 = K0 * (c • X)
      rw [Matrix.smul_mul, Matrix.mul_smul, hX3]

theorem cross_apply (X : Matrix I32 I32 ℂ) (u v : Fin 16) :
    crossCoordOf X u v = X (plusEmb u) (minusEmb (flip8 v)) := rfl

/-- The folded cross-block of `X`, as a folded matrix. -/
def foldedOf (X : Matrix I32 I32 ℂ) : Matrix (Fin 16) (Fin 16) ℂ :=
  fun a b => crossCoordOf X a b

theorem foldedOf_apply (X : Matrix I32 I32 ℂ) (a b : Fin 16) :
    foldedOf X a b = crossCoordOf X a b := rfl

/-- The folded cross-block of a locus element commutes with `Qmat`. -/
theorem cross_mem_centQ {X : Matrix I32 I32 ℂ} (hX : X ∈ locusB) :
    foldedOf X ∈ centQ := by
  obtain ⟨h1, h2, h3⟩ := hX
  rw [mem_centQ]
  funext a b
  rw [Qmat_mul_apply, mul_Qmat_apply]
  have e1 : (K0 * X) (plusEmb a) (minusEmb (flip8 b))
      = (X * K0) (plusEmb a) (minusEmb (flip8 b)) := by rw [h3]
  rw [K0_mul_apply, mul_K0_apply, pIdx_plusEmb, pIdx_minusEmb_flip8,
    dval_minusEmb_flip8, cval_minusEmb_flip8] at e1
  rw [foldedOf_apply, foldedOf_apply, foldedOf_apply, cross_apply, cross_apply,
    cross_apply, flip8_flip8]
  exact e1

/-- Assembling a Hermitian odd matrix from a folded block: the
    (+, −) block is `B` in folded coordinates, the (−, +) block its
    conjugate transpose, the diagonal blocks zero. -/
noncomputable def matOf (B : Matrix (Fin 16) (Fin 16) ℂ) : Matrix I32 I32 ℂ :=
  fun i j => if gSign i = 1 then
    (if gSign j = 1 then 0 else B (acoord i) (acoord j))
  else
    (if gSign j = 1 then star (B (acoord j) (acoord i)) else 0)

theorem matOf_apply (B : Matrix (Fin 16) (Fin 16) ℂ) (i j : I32) :
    matOf B i j = if gSign i = 1 then
      (if gSign j = 1 then 0 else B (acoord i) (acoord j))
    else
      (if gSign j = 1 then star (B (acoord j) (acoord i)) else 0) := rfl

theorem matOf_pp (B : Matrix (Fin 16) (Fin 16) ℂ) {i j : I32}
    (hi : gSign i = 1) (hj : gSign j = 1) : matOf B i j = 0 := by
  rw [matOf_apply, ite_eq_left hi, ite_eq_left hj]

theorem matOf_pm (B : Matrix (Fin 16) (Fin 16) ℂ) {i j : I32}
    (hi : gSign i = 1) (hj : gSign j = -1) :
    matOf B i j = B (acoord i) (acoord j) := by
  rw [matOf_apply, ite_eq_left hi,
    ite_eq_right (show ¬ gSign j = 1 by rw [hj]; norm_num)]

theorem matOf_mp (B : Matrix (Fin 16) (Fin 16) ℂ) {i j : I32}
    (hi : gSign i = -1) (hj : gSign j = 1) :
    matOf B i j = star (B (acoord j) (acoord i)) := by
  rw [matOf_apply, ite_eq_right (show ¬ gSign i = 1 by rw [hi]; norm_num),
    ite_eq_left hj]

theorem matOf_mm (B : Matrix (Fin 16) (Fin 16) ℂ) {i j : I32}
    (hi : gSign i = -1) (hj : gSign j = -1) : matOf B i j = 0 := by
  rw [matOf_apply, ite_eq_right (show ¬ gSign i = 1 by rw [hi]; norm_num),
    ite_eq_right (show ¬ gSign j = 1 by rw [hj]; norm_num)]

theorem matOf_hermitian (B : Matrix (Fin 16) (Fin 16) ℂ) :
    (matOf B)ᴴ = matOf B := by
  funext i j
  rw [Matrix.conjTranspose_apply]
  rcases gSign_eq_one_or_neg_one i with hi | hi <;>
    rcases gSign_eq_one_or_neg_one j with hj | hj
  · rw [matOf_pp B hj hi, matOf_pp B hi hj, star_zero]
  · rw [matOf_mp B hj hi, star_star, matOf_pm B hi hj]
  · rw [matOf_pm B hj hi, matOf_mp B hi hj]
  · rw [matOf_mm B hj hi, matOf_mm B hi hj, star_zero]

theorem matOf_odd (B : Matrix (Fin 16) (Fin 16) ℂ) :
    gammaF * matOf B + matOf B * gammaF = 0 := by
  funext i j
  rw [Matrix.add_apply, Matrix.zero_apply, gammaF_mul_apply, mul_gammaF_apply,
    show gammaF i i = gSign i from rfl, show gammaF j j = gSign j from rfl]
  rcases gSign_eq_one_or_neg_one i with hi | hi <;>
    rcases gSign_eq_one_or_neg_one j with hj | hj
  · rw [hi, hj, matOf_pp B hi hj]; simp
  · rw [hi, hj, matOf_pm B hi hj]; ring
  · rw [hi, hj, matOf_mp B hi hj]; ring
  · rw [hi, hj, matOf_mm B hi hj]; simp


/-! ### `matOf B` commutes with `K0` -/

theorem matOf_comm_pm {B : Matrix (Fin 16) (Fin 16) ℂ} (hB : B ∈ centQ)
    (a v : Fin 16) :
    (K0 * matOf B) (plusEmb a) (minusEmb (flip8 v))
      = (matOf B * K0) (plusEmb a) (minusEmb (flip8 v)) := by
  rw [K0_mul_apply, mul_K0_apply, pIdx_plusEmb, pIdx_minusEmb_flip8,
    matOf_pm B (gSign_plusEmb a) (gSign_minusEmb (flip8 v)),
    matOf_pm B (gSign_plusEmb (flip8 a)) (gSign_minusEmb (flip8 v)),
    matOf_pm B (gSign_plusEmb a) (gSign_minusEmb v),
    acoord_plusEmb a, acoord_plusEmb (flip8 a), acoord_minusEmb (flip8 v),
    acoord_minusEmb v, flip8_flip8,
    show dval (plusEmb a) = qd a from rfl, show cval (plusEmb a) = qc a from rfl,
    dval_minusEmb_flip8, cval_minusEmb_flip8]
  exact centQ_entry_eq hB a v

theorem matOf_comm_mp {B : Matrix (Fin 16) (Fin 16) ℂ} (hB : B ∈ centQ)
    (a v : Fin 16) :
    (K0 * matOf B) (minusEmb (flip8 v)) (plusEmb a)
      = (matOf B * K0) (minusEmb (flip8 v)) (plusEmb a) := by
  rw [K0_mul_apply, mul_K0_apply, pIdx_plusEmb, pIdx_minusEmb_flip8,
    matOf_mp B (gSign_minusEmb (flip8 v)) (gSign_plusEmb a),
    matOf_mp B (gSign_minusEmb v) (gSign_plusEmb a),
    matOf_mp B (gSign_minusEmb (flip8 v)) (gSign_plusEmb (flip8 a)),
    acoord_plusEmb a, acoord_plusEmb (flip8 a), acoord_minusEmb (flip8 v),
    acoord_minusEmb v, flip8_flip8,
    show dval (plusEmb a) = qd a from rfl, show cval (plusEmb a) = qc a from rfl,
    show dval (minusEmb (flip8 v)) = qd v from dval_minusEmb_flip8 v,
    show cval (minusEmb (flip8 v)) = qc (flip8 v) from cval_minusEmb_flip8 v]
  have e := congrArg star (centQ_entry_eq hB a v)
  rw [star_add, star_mul, star_mul, star_add, star_mul, star_mul,
    star_qd, star_qc, star_qd, star_qc] at e
  exact e.symm

theorem matOf_comm {B : Matrix (Fin 16) (Fin 16) ℂ} (hB : B ∈ centQ) :
    matOf B * K0 = K0 * matOf B := by
  funext i j
  rcases gSign_eq_one_or_neg_one i with hi | hi <;>
    rcases gSign_eq_one_or_neg_one j with hj | hj
  · have hpi : gSign (pIdx i) = 1 := by rw [gSign_pIdx]; exact hi
    have hpj : gSign (pIdx j) = 1 := by rw [gSign_pIdx]; exact hj
    rw [mul_K0_apply, K0_mul_apply, matOf_pp B hi hj, matOf_pp B hi hpj,
      matOf_pp B hpi hj]
    simp
  · have ei : plusEmb (acoord i) = i := plusEmb_acoord_of_gSign_eq_one hi
    have ej : minusEmb (flip8 (acoord j)) = j :=
      minusEmb_flip8_acoord_of_gSign_eq_neg_one hj
    rw [← ei, ← ej]
    exact (matOf_comm_pm hB (acoord i) (acoord j)).symm
  · have ei : minusEmb (flip8 (acoord i)) = i :=
      minusEmb_flip8_acoord_of_gSign_eq_neg_one hi
    have ej : plusEmb (acoord j) = j := plusEmb_acoord_of_gSign_eq_one hj
    rw [← ei, ← ej]
    exact (matOf_comm_mp hB (acoord j) (acoord i)).symm
  · have hpi : gSign (pIdx i) = -1 := by rw [gSign_pIdx]; exact hi
    have hpj : gSign (pIdx j) = -1 := by rw [gSign_pIdx]; exact hj
    rw [mul_K0_apply, K0_mul_apply, matOf_mm B hi hj, matOf_mm B hi hpj,
      matOf_mm B hpi hj]
    simp

theorem matOf_mem {B : Matrix (Fin 16) (Fin 16) ℂ} (hB : B ∈ centQ) :
    matOf B ∈ locusB :=
  ⟨matOf_hermitian B, matOf_odd B, matOf_comm hB⟩

/-! ### The two maps are mutually inverse -/

theorem cross_matOf (B : Matrix (Fin 16) (Fin 16) ℂ) :
    foldedOf (matOf B) = B := by
  funext a b
  rw [foldedOf_apply, cross_apply,
    matOf_pm B (gSign_plusEmb a) (gSign_minusEmb (flip8 b)),
    acoord_plusEmb, acoord_minusEmb, flip8_flip8]

theorem matOf_cross {X : Matrix I32 I32 ℂ} (hX : X ∈ locusB) :
    matOf (foldedOf X) = X := by
  obtain ⟨h1, h2, h3⟩ := hX
  funext i j
  rcases gSign_eq_one_or_neg_one i with hi | hi <;>
    rcases gSign_eq_one_or_neg_one j with hj | hj
  · rw [matOf_pp _ hi hj]
    exact (gammaOdd_entry_eq_zero_of_gSign_eq X h2 (hi.trans hj.symm)).symm
  · rw [matOf_pm _ hi hj, foldedOf_apply, cross_apply,
      plusEmb_acoord_of_gSign_eq_one hi,
      minusEmb_flip8_acoord_of_gSign_eq_neg_one hj]
  · rw [matOf_mp _ hi hj, foldedOf_apply, cross_apply,
      plusEmb_acoord_of_gSign_eq_one hj,
      minusEmb_flip8_acoord_of_gSign_eq_neg_one hi]
    exact (selfAdjoint_entry X h1 i j).symm
  · rw [matOf_mm _ hi hj]
    exact (gammaOdd_entry_eq_zero_of_gSign_eq X h2 (hi.trans hj.symm)).symm

/-- The locus is real-linearly equivalent to the centralizer of
    `Qmat` with scalars restricted to ℝ. -/
noncomputable def locusEquiv :
    ↥locusB ≃ₗ[ℝ] ↥(centQ.restrictScalars ℝ) where
  toFun X := ⟨foldedOf X.val, cross_mem_centQ X.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun B := ⟨matOf B.val, matOf_mem B.2⟩
  left_inv X := Subtype.ext (matOf_cross X.2)
  right_inv B := Subtype.ext (cross_matOf B.val)

/-- **VL-4b headline count.**  The full-space locus at Seat B has
    real dimension `156 = 2 * 78`. -/
theorem finrank_locusB : Module.finrank ℝ ↥locusB = 156 := by
  rw [locusEquiv.finrank_eq]
  show Module.finrank ℝ ↥centQ = 156
  rw [finrank_real_of_complex, finrank_centQ]

/-- **VL-4b, assembled.**  The per-root separation (Obligation 1),
    the folded centralizer count, and the locus count, in one
    statement. -/
theorem vl4b_headline :
    (muP + muM = 51 ∧ muP * muM = 1 ∧ muP ≠ muM) ∧
    (∀ μ : ℂ, μ = muP ∨ μ = muM →
      Module.finrank ℂ ↥(eigSub μ) = 2 ∧
      Module.finrank ℂ ↥(eigSub μ ⊓ gammaPlusSub) = 1 ∧
      Module.finrank ℂ ↥(eigSub μ ⊓ gammaMinusSub) = 1) ∧
    Module.finrank ℂ ↥centQ = 78 ∧
    Module.finrank ℝ ↥locusB = 156 :=
  ⟨⟨muP_add_muM, muP_mul_muM, muP_ne_muM⟩,
   fun μ hμ => ⟨finrank_eig_mu μ hμ, finrank_eig_split_plus μ hμ,
     finrank_eig_split_minus μ hμ⟩,
   finrank_centQ, finrank_locusB⟩

#print axioms per_root_separation
#print axioms finrank_centQ
#print axioms finrank_locusB
#print axioms vl4b_headline

end ThetLogos
