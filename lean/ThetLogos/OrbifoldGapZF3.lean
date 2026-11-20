/-
# OrbifoldGapZF3 — ZF-3: the variational gap map at (2, 1)

**Scope: ~/workspace/your_files/gravity-orb-z3-fold-scope-2026-11-18.md,
§2 Leg A, brick ZF-3. Commissioned by Zero, 2026-11-18 18:07 EST
("Fire all three legs"). NO CLAIM. Dials 0/4. Dial-ineligible.**

At the diagonal-free seat the fibres agree (ZF-2: every fibre has
card `3`), so ZF-1's totals identity makes the averaged quotient
weights symmetric, and the full variational package transports:
BridgeCompletion's attainment makes the quotient's Fiedler value
an eigenvalue carried by a mean-zero, nonconstant eigenvector, and
the base pin's banked comparison then gives

  `fiedler (sliceW) ≤ fiedler (quotW)`   at `(2, 1)`,

with the equality criterion transported to variational form:
equality holds iff the slice has a cyc-invariant Fiedler
eigenvector at this seat. (The criterion itself is not decided
here — that was Leg C's question at the headline seat, decided
negatively in ZF-9; at `(2, 1)` it is stated in variational form,
open.)

Kills watched: K-ORB-GAPMAP-VAR — the transport could have bitten
on the intra-orbit self-weights at this seat (`quotW o o > 0`
occurs: the axis orbit's nodes are pairwise neighbours). It does
not: attainment and the eigenvector characterization apply to
`quotW` as they stand, self-weights included — they cancel in the
operator exactly as the scope's route predicted. The kill does
not fire.
-/

import ThetLogos.OrbifoldGapZF2
import ThetLogos.OrbifoldGapZF1

namespace ThetLogos
namespace OrbifoldGapPin

/-- At `(2, 1)` the averaged quotient weights are symmetric: the
fibres all have card `3` (ZF-2), so ZF-1's criterion applies at
every pair. -/
theorem quotW_symm_two_one (o o' : SliceQuot 2 1) :
    quotW o o' = quotW o' o :=
  quotW_symm_of_card_eq (by rw [fiber_card_two_one o, fiber_card_two_one o'])

/-- Attainment at `(2, 1)`: the quotient's Fiedler value is an
eigenvalue of `laplacianOp quotW`, carried by a mean-zero
eigenvector that is nonconstant (unit norm over the two-point
quotient forces it apart from every constant). -/
theorem quotient_fiedler_eigen_two_one :
    ∃ G : SliceQuot 2 1 → ℝ, (∑ o, G o = 0) ∧ (∃ o o', G o ≠ G o')
      ∧ ∀ o, laplacianOp quotW G o
        = fiedler (quotW (R := 2) (h := 1)) * G o := by
  obtain ⟨G, hGmem, hGeig⟩ := laplacianOp_fiedler_minimizer quotW
    quotW_symm_two_one (fun o o' => quotW_nonneg o o')
    quot_distinct_two_one
  obtain ⟨hG0, hG1⟩ := hGmem
  refine ⟨G, hG0, ?_, hGeig⟩
  by_contra hcon
  push_neg at hcon
  have hsum0 : G (Quotient.mk (orbitSetoid 2 1) fullNode21)
      + G (Quotient.mk (orbitSetoid 2 1) axisNode21) = 0 := by
    have h := hG0
    rw [univ_quot_two_one,
      Finset.sum_insert (Finset.notMem_singleton.mpr quot_distinct_two_one),
      Finset.sum_singleton] at h
    exact h
  have hsum1 : G (Quotient.mk (orbitSetoid 2 1) fullNode21) ^ 2
      + G (Quotient.mk (orbitSetoid 2 1) axisNode21) ^ 2 = 1 := by
    have h := hG1
    rw [univ_quot_two_one,
      Finset.sum_insert (Finset.notMem_singleton.mpr quot_distinct_two_one),
      Finset.sum_singleton] at h
    exact h
  have e := hcon (Quotient.mk (orbitSetoid 2 1) fullNode21)
    (Quotient.mk (orbitSetoid 2 1) axisNode21)
  have h0 : G (Quotient.mk (orbitSetoid 2 1) axisNode21) = 0 := by
    linarith [hsum0, e]
  rw [e, h0] at hsum1
  norm_num at hsum1

/-- **The variational gap map at `(2, 1)`**: folding does not
decrease the gap — the slice's Fiedler value is at most the
quotient's. -/
theorem fiedler_le_fiedler_quot_two_one :
    fiedler (sliceW (R := 2) (h := 1)) ≤ fiedler (quotW (R := 2) (h := 1)) := by
  obtain ⟨G, -, hnc, hGeig⟩ := quotient_fiedler_eigen_two_one
  have hcard : (Fintype.card (Slice 2 1) : ℝ) ≠ 0 :=
    ne_of_gt (by exact_mod_cast Fintype.card_pos_iff.mpr ⟨fullNode21⟩)
  exact fiedler_slice_le_of_eigen_quotient hGeig hnc hcard

/-- The equality criterion at `(2, 1)`, in variational form:
the slice and quotient Fiedler values agree iff the slice has a
cyc-invariant Fiedler eigenvector at this seat. -/
theorem fiedler_eq_iff_invariant_eigen_two_one :
    fiedler (sliceW (R := 2) (h := 1)) = fiedler (quotW (R := 2) (h := 1))
    ↔ ∃ F : Slice 2 1 → ℝ, (∀ p, F (cycSlice 2 1 p) = F p) ∧ F ≠ 0
      ∧ (∑ p, F p = 0)
      ∧ ∀ p, laplacianOp sliceW F p
        = fiedler (sliceW (R := 2) (h := 1)) * F p := by
  have hcard : (Fintype.card (Slice 2 1) : ℝ) ≠ 0 :=
    ne_of_gt (by exact_mod_cast Fintype.card_pos_iff.mpr ⟨fullNode21⟩)
  constructor
  · intro heq
    obtain ⟨G, -, hnc, hGeig⟩ := quotient_fiedler_eigen_two_one
    rw [← heq] at hGeig
    exact (fiedler_eq_iff_invariant_eigen hcard).mp ⟨G, hnc, hGeig⟩
  · intro hF
    obtain ⟨F, hinv, hFne, hFsum, hFeig⟩ := hF
    -- The descended eigenvector is mean-zero over the quotient:
    -- the slice sum of `F` is `3` times the quotient sum of its
    -- descent, because every fibre has card `3`.
    have hid : ∀ G : SliceQuot 2 1 → ℝ,
        ∑ p, pullback G p = ∑ o, ((fiber o).card : ℝ) * G o := by
      intro G
      rw [← Finset.sum_fiberwise_of_maps_to
        (s := Finset.univ) (t := Finset.univ)
        (g := fun p : Slice 2 1 => Quotient.mk (orbitSetoid 2 1) p)
        (f := fun p : Slice 2 1 => pullback G p)
        (fun p _ => Finset.mem_univ _)]
      apply Finset.sum_congr rfl
      intro o _
      show (∑ p ∈ fiber o, pullback G p) = ((fiber o).card : ℝ) * G o
      have hterm : ∀ p ∈ fiber o, pullback G p = G o := by
        intro p hp
        have hmk : Quotient.mk (orbitSetoid 2 1) p = o :=
          (Finset.mem_filter.mp hp).2
        exact congrArg G hmk
      rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul]
    have hG0 : ∑ o, descend F hinv o = 0 := by
      have h1 := hid (descend F hinv)
      rw [pullback_descend F hinv, hFsum] at h1
      have h2 : (∑ o, ((fiber o).card : ℝ) * descend F hinv o)
          = 3 * ∑ o, descend F hinv o := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun o _ => by
          simp [fiber_card_two_one o])
      rw [h2] at h1
      linarith [h1]
    have hGne : descend F hinv ≠ 0 := by
      intro h0
      apply hFne
      have h := pullback_descend F hinv
      rw [h0] at h
      rw [← h]
      funext p
      rfl
    have hle : fiedler (quotW (R := 2) (h := 1))
        ≤ fiedler (sliceW (R := 2) (h := 1)) :=
      fiedler_le_of_eigenvector quotW quotW_symm_two_one
        (fun o o' => quotW_nonneg o o') (descend F hinv)
        (fiedler (sliceW (R := 2) (h := 1))) hG0 hGne
        (fun o => descend_eigen hinv hFeig o)
    exact le_antisymm fiedler_le_fiedler_quot_two_one hle

end OrbifoldGapPin
end ThetLogos
