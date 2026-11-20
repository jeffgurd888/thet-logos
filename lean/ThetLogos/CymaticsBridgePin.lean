/-
# Cymatics Bridge Pin (working label — the public name is Zero's to coin)

**Scope: ~/workspace/your_files/cymatics-bridge-pin-scope-2026-11-18.md.
Commissioned by Zero, 2026-11-18 23:10 EST ("can you build the bridge"),
fired 2026-11-18 23:18 EST ("Fire the bridge plus the CB-7 stretch").
NO CLAIM. Dials 0/4. Dial-ineligible.**

The bridge in finite form: a finite spherical seat — the integer sphere
shell at `R = 1` in `ℤ³`, which the census (CB-1/CB-2) proves *is* the
6-vertex octahedral seat — whose Laplacian eigenmodes are its standing
waves (cymatics on a sphere, seat grade), with each mode assigned an
energy `E = h·√λ` where `h` is a **bare parameter, exactly as `G` is a
bare parameter in the gravity seats** (CB-5), and whose fundamental
mode's nodal split is counted exactly (CB-6, CB-7).

Fences, on the face: the pin tests the finite FORM of the coupling
`spectrum → √λ → E = h√λ → nodal reading` only. It states nothing about
the Earth: no crustal feature is identified, no terrestrial mode is
named, no value of `h` is ever chosen, no frequency in Hz exists in the
seat. The gap between the Planck scale and the seismic scale (~46
orders of magnitude) is FRONTIER — named in the scope, unpriced,
untouched, and not narrowed by anything here.

Precision note (scope §1): the seat's fundamental mode is the *dipole*
two-lobe split — one positive lobe, one negative lobe. Earth's gravest
football mode `₀S₂` is the quadrupole relative (three zonal sign
bands). The honest echo is two-lobedness as such, not `₀S₂`'s pattern.

Kills armed (scope §3): K-CYM-SEAT, K-CYM-NODAL (two-sided),
K-CYM-LADDER, K-CYM-COSTUME (grade guard).
-/

import ThetLogos.OrbifoldGapPin

namespace ThetLogos
namespace CymaticsBridgePin

open OrbifoldGapPin (normSq ballFinset)

/-! ## CB-1 — The shell seat and its census -/

/-- The integer sphere shell of radius `R` in `ℤ³`: the points of the
ball's box with `normSq p = R²` exactly (the ball filters `≤`; the
shell is its boundary filter `=`). -/
def shellFinset (R : ℕ) : Finset (ℤ × ℤ × ℤ) :=
  (ballFinset R).filter (fun p => normSq p = (R : ℤ) ^ 2)

/-- The shell as a finite type. -/
abbrev Shell (R : ℕ) : Type := ↥(shellFinset R)

/-- The shell graph's weights: `1` on nearest neighbours (squared
distance `2` — the orb's own adjacency convention, mirroring
`sliceW` verbatim), else `0`. -/
def shellW {R : ℕ} (p q : Shell R) : ℝ :=
  if (p.1.1 - q.1.1) ^ 2 + (p.1.2.1 - q.1.2.1) ^ 2
      + (p.1.2.2 - q.1.2.2) ^ 2 = 2
    then 1 else 0

/-- The shell weights are symmetric. -/
theorem shellW_symm {R : ℕ} (p q : Shell R) : shellW p q = shellW q p := by
  have hsq : (p.1.1 - q.1.1) ^ 2 + (p.1.2.1 - q.1.2.1) ^ 2
      + (p.1.2.2 - q.1.2.2) ^ 2
      = (q.1.1 - p.1.1) ^ 2 + (q.1.2.1 - p.1.2.1) ^ 2
      + (q.1.2.2 - p.1.2.2) ^ 2 := by ring
  unfold shellW
  rw [hsq]

/-- The shell weights are nonnegative. -/
theorem shellW_nonneg {R : ℕ} (p q : Shell R) : 0 ≤ shellW p q := by
  unfold shellW
  split_ifs <;> norm_num

/-- **The R = 1 census.** The shell at radius 1 is exactly the six
axis points `(±1, 0, 0), (0, ±1, 0), (0, 0, ±1)` — by ℤ-tuple
enumeration over the box. (K-CYM-SEAT is armed against this census:
any other output fires it. It does not fire.) -/
theorem shellFinset_one :
    shellFinset 1 = {(1, 0, 0), (-1, 0, 0), (0, 1, 0), (0, -1, 0),
      (0, 0, 1), (0, 0, -1)} := by
  decide

/-- The R = 1 shell has exactly six points. -/
theorem shellFinset_one_card : (shellFinset 1).card = 6 := by
  decide

/-- The R = 1 shell, as a type, has exactly six elements. -/
theorem shell_one_card : Fintype.card (Shell 1) = 6 := by
  rw [Fintype.card_coe]
  exact shellFinset_one_card

/-! ## CB-2 — The seat is the octahedron -/

/-- Every point of `Shell 1` is one of the six axis points
(the CB-1 census, as a case split). -/
theorem shell_one_cases (p : Shell 1) :
    p.1 = (1, 0, 0) ∨ p.1 = (-1, 0, 0) ∨ p.1 = (0, 1, 0) ∨
    p.1 = (0, -1, 0) ∨ p.1 = (0, 0, 1) ∨ p.1 = (0, 0, -1) := by
  have hp : p.1 ∈ shellFinset 1 := p.2
  have hp' : p.1 ∈ ({(1, 0, 0), (-1, 0, 0), (0, 1, 0), (0, -1, 0),
      (0, 0, 1), (0, 0, -1)} : Finset (ℤ × ℤ × ℤ)) := by
    rw [← shellFinset_one]
    exact hp
  simpa only [Finset.mem_insert, Finset.mem_singleton] using hp'

/-- Every shell point has squared norm exactly `1`. -/
theorem normSq_shell (p : Shell 1) : normSq p.1 = 1 := by
  have h := (Finset.mem_filter.mp p.2).2
  simpa using h

/-- The antipode of a shell point: `p ↦ -p`, shell-preserving
(the census is symmetric under negation). -/
def antipode (p : Shell 1) : Shell 1 :=
  ⟨-p.1, by
    have hp' : p.1 ∈ ({(1, 0, 0), (-1, 0, 0), (0, 1, 0), (0, -1, 0),
        (0, 0, 1), (0, 0, -1)} : Finset (ℤ × ℤ × ℤ)) := by
      rw [← shellFinset_one]
      exact p.2
    have hgoal : -p.1 ∈ ({(1, 0, 0), (-1, 0, 0), (0, 1, 0), (0, -1, 0),
        (0, 0, 1), (0, 0, -1)} : Finset (ℤ × ℤ × ℤ)) := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp' ⊢
      rcases hp' with h | h | h | h | h | h <;> rw [h] <;> decide
    rwa [← shellFinset_one] at hgoal⟩

/-- The antipode's underlying point is the negation. -/
theorem antipode_val (p : Shell 1) : (antipode p).1 = -p.1 := rfl

/-- The antipode is an involution. -/
theorem antipode_antipode (p : Shell 1) : antipode (antipode p) = p := by
  apply Subtype.ext
  rw [antipode_val, antipode_val, neg_neg]

/-- The antipode has no fixed point on the shell (no axis point
is its own negation). -/
theorem antipode_ne_self (p : Shell 1) : antipode p ≠ p := by
  intro h
  have hv : (antipode p).1 = p.1 := congrArg Subtype.val h
  rw [antipode_val] at hv
  rcases shell_one_cases p with h1 | h1 | h1 | h1 | h1 | h1 <;>
    rw [h1] at hv <;> revert hv <;> decide

/-- No self-loop: the weight from a point to itself is `0`. -/
theorem shellW_self (p : Shell 1) : shellW p p = 0 := by
  unfold shellW
  norm_num

/-- Antipodal points are not adjacent: their squared distance
is `4 · normSq = 4 ≠ 2`. -/
theorem shellW_antipode (p : Shell 1) : shellW p (antipode p) = 0 := by
  have hnorm : normSq p.1 = 1 := normSq_shell p
  have h4 : (p.1.1 - (antipode p).1.1) ^ 2 + (p.1.2.1 - (antipode p).1.2.1) ^ 2
      + (p.1.2.2 - (antipode p).1.2.2) ^ 2 = 4 := by
    obtain ⟨⟨x, y, z⟩, hp⟩ := p
    have hnorm' : x ^ 2 + y ^ 2 + z ^ 2 = 1 := hnorm
    rw [antipode_val]
    change (x - -x) ^ 2 + (y - -y) ^ 2 + (z - -z) ^ 2 = 4
    linear_combination 4 * hnorm'
  unfold shellW
  rw [h4]
  norm_num

/-- **The adjacency characterisation.** For distinct shell points,
the weight is `1` exactly when the second is not the antipode of
the first — the octahedral graph `K_{2,2,2}`: every vertex is
adjacent to all but itself and its antipode. -/
theorem shellW_eq_one_iff {p q : Shell 1} (hpq : p ≠ q) :
    shellW p q = 1 ↔ q ≠ antipode p := by
  have hanti : ∀ a b : Shell 1, (a ≠ antipode b) ↔ a.1 ≠ -b.1 := by
    intro a b
    constructor
    · intro h hab
      exact h (Subtype.ext (by rw [antipode_val]; exact hab))
    · intro h hab
      have hv : a.1 = (antipode b).1 := congrArg Subtype.val hab
      rw [antipode_val] at hv
      exact h hv
  rw [hanti q p]
  rcases shell_one_cases p with hp1 | hp1 | hp1 | hp1 | hp1 | hp1 <;>
    rcases shell_one_cases q with hq1 | hq1 | hq1 | hq1 | hq1 | hq1 <;>
    first
      | exact absurd (Subtype.ext (hp1.trans hq1.symm)) hpq
      | norm_num [shellW, hp1, hq1]

/-- Regularity: every vertex row of the shell weights sums to `4`
(the octahedral graph is 4-regular) — read off the adjacency
characterisation: the weight is `1` off the pair `{p, antipode p}`
and `0` on it, and the pair has card `2` in a 6-point seat. -/
theorem shellW_row_sum (p : Shell 1) : ∑ q : Shell 1, shellW p q = 4 := by
  classical
  set s : Finset (Shell 1) := {p, antipode p} with hs
  have hchar : ∀ q : Shell 1, shellW p q
      = if q ∈ s then (0 : ℝ) else 1 := by
    intro q
    by_cases hq : q ∈ s
    · rw [if_pos hq]
      simp only [hs, Finset.mem_insert, Finset.mem_singleton] at hq
      rcases hq with rfl | rfl
      · exact shellW_self _
      · exact shellW_antipode _
    · rw [if_neg hq]
      simp only [hs, Finset.mem_insert, Finset.mem_singleton, not_or] at hq
      exact (shellW_eq_one_iff (Ne.symm hq.1)).mpr hq.2
  have hcard : s.card = 2 := by
    rw [hs, Finset.card_insert_of_notMem, Finset.card_singleton]
    simp only [Finset.mem_singleton]
    exact fun h => antipode_ne_self p h.symm
  calc (∑ q : Shell 1, shellW p q)
      = ∑ q : Shell 1, (if q ∈ s then (0 : ℝ) else 1) :=
        Finset.sum_congr rfl (fun q _ => hchar q)
    _ = ∑ q ∈ sᶜ, (1 : ℝ) := by
        have h1 : ∑ q ∈ s, (if q ∈ s then (0 : ℝ) else 1) = 0 :=
          Finset.sum_eq_zero (fun q hq => if_pos hq)
        have h2 : ∑ q ∈ sᶜ, (if q ∈ s then (0 : ℝ) else 1)
            = ∑ q ∈ sᶜ, (1 : ℝ) :=
          Finset.sum_congr rfl (fun q hq =>
            if_neg (Finset.mem_compl.mp hq))
        have h3 := Finset.sum_add_sum_compl s
          (fun q : Shell 1 => if q ∈ s then (0 : ℝ) else 1)
        rw [h1, h2] at h3
        rw [← h3, zero_add]
    _ = (sᶜ).card • (1 : ℝ) := Finset.sum_const _
    _ = 4 := by
        rw [Finset.card_compl, shell_one_card, hcard]
        norm_num [nsmul_eq_mul]

/-! ## CB-3 — Exhibition: the coordinate modes -/

/-- The first coordinate function on the shell. -/
def coordX (p : Shell 1) : ℝ := (p.1.1 : ℝ)

/-- The second coordinate function on the shell. -/
def coordY (p : Shell 1) : ℝ := (p.1.2.1 : ℝ)

/-- The third coordinate function on the shell. -/
def coordZ (p : Shell 1) : ℝ := (p.1.2.2 : ℝ)

/-- **The pointwise shell Laplacian.** For every potential `φ` and
every shell point `p`,
`L φ p = 5 φ p + φ (antipode p) − ∑ q, φ q`:
the neighbours of `p` are all points but `p` and its antipode
(CB-2), so the weighted drop sum is `4 φ p − (Σφ − φ p − φ (antipode p))`. -/
theorem laplacianOp_shellW_apply (φ : Shell 1 → ℝ) (p : Shell 1) :
    laplacianOp shellW φ p
      = 5 * φ p + φ (antipode p) - ∑ q, φ q := by
  classical
  set s : Finset (Shell 1) := {p, antipode p} with hs
  have hcard : s.card = 2 := by
    rw [hs, Finset.card_insert_of_notMem, Finset.card_singleton]
    simp only [Finset.mem_singleton]
    exact fun h => antipode_ne_self p h.symm
  have hsum_s : ∑ q ∈ s, φ q = φ p + φ (antipode p) := by
    rw [hs, Finset.sum_insert (by
      simp only [Finset.mem_singleton]
      exact fun h => antipode_ne_self p h.symm), Finset.sum_singleton]
  have h1 : (∑ q, shellW p q * (φ p - φ q))
      = ∑ q ∈ sᶜ, shellW p q * (φ p - φ q) := by
    apply (Finset.sum_subset (Finset.subset_univ sᶜ) _).symm
    intro q _ hq
    have hqs : q ∈ s := by
      by_contra hc
      exact hq (Finset.mem_compl.mpr hc)
    simp only [hs, Finset.mem_insert, Finset.mem_singleton] at hqs
    rcases hqs with rfl | rfl
    · simp
    · rw [shellW_antipode, zero_mul]
  have h2 : (∑ q ∈ sᶜ, shellW p q * (φ p - φ q))
      = ∑ q ∈ sᶜ, (φ p - φ q) := by
    apply Finset.sum_congr rfl
    intro q hq
    rw [Finset.mem_compl] at hq
    simp only [hs, Finset.mem_insert, Finset.mem_singleton, not_or] at hq
    rw [(shellW_eq_one_iff (Ne.symm hq.1)).mpr hq.2, one_mul]
  have h3 : (∑ q ∈ sᶜ, (φ p - φ q))
      = 4 * φ p - (∑ q, φ q - (φ p + φ (antipode p))) := by
    have hcompl : ∑ q ∈ sᶜ, φ q
        = ∑ q, φ q - (φ p + φ (antipode p)) := by
      have h := Finset.sum_add_sum_compl s φ
      rw [hsum_s] at h
      linarith [h]
    have hcardc : (sᶜ).card = 4 := by
      rw [Finset.card_compl, shell_one_card, hcard]
    rw [Finset.sum_sub_distrib, hcompl, Finset.sum_const, hcardc,
      nsmul_eq_mul]
    norm_num
  rw [laplacianOp_apply, h1, h2, h3]
  ring

/-- The coordinate functions are antipode-odd: each flips sign
at the antipodal point. -/
theorem coord_antipode (p : Shell 1) :
    coordX (antipode p) = -coordX p ∧ coordY (antipode p) = -coordY p ∧
    coordZ (antipode p) = -coordZ p := by
  obtain ⟨⟨x, y, z⟩, hp⟩ := p
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [coordX, coordY, coordZ, antipode_val, Prod.fst_neg,
      Prod.snd_neg, Int.cast_neg]

/-- The coordinate functions are mean-zero on the shell
(the census values are `1, -1, 0, 0, 0, 0` in some order). -/
theorem coord_sum_zero :
    (∑ q, coordX q = 0) ∧ (∑ q, coordY q = 0) ∧ (∑ q, coordZ q = 0) := by
  have hX : ∑ q, coordX q = 0 := by
    have h1 : (∑ q : Shell 1, coordX q)
        = ∑ q ∈ shellFinset 1, ((q.1 : ℤ) : ℝ) :=
      Finset.sum_coe_sort (shellFinset 1) (fun t : ℤ × ℤ × ℤ => ((t.1 : ℤ) : ℝ))
    rw [h1, shellFinset_one]
    norm_num [Finset.sum_insert, Finset.sum_singleton]
  have hY : ∑ q, coordY q = 0 := by
    have h1 : (∑ q : Shell 1, coordY q)
        = ∑ q ∈ shellFinset 1, ((q.2.1 : ℤ) : ℝ) :=
      Finset.sum_coe_sort (shellFinset 1)
        (fun t : ℤ × ℤ × ℤ => ((t.2.1 : ℤ) : ℝ))
    rw [h1, shellFinset_one]
    norm_num [Finset.sum_insert, Finset.sum_singleton]
  have hZ : ∑ q, coordZ q = 0 := by
    have h1 : (∑ q : Shell 1, coordZ q)
        = ∑ q ∈ shellFinset 1, ((q.2.2 : ℤ) : ℝ) :=
      Finset.sum_coe_sort (shellFinset 1)
        (fun t : ℤ × ℤ × ℤ => ((t.2.2 : ℤ) : ℝ))
    rw [h1, shellFinset_one]
    norm_num [Finset.sum_insert, Finset.sum_singleton]
  exact ⟨hX, hY, hZ⟩

/-- The first coordinate is a shell eigenfunction at `λ = 4`. -/
theorem coordX_eigen (p : Shell 1) :
    laplacianOp shellW coordX p = 4 * coordX p := by
  rw [laplacianOp_shellW_apply, (coord_antipode p).1, coord_sum_zero.1]
  ring

/-- The second coordinate is a shell eigenfunction at `λ = 4`. -/
theorem coordY_eigen (p : Shell 1) :
    laplacianOp shellW coordY p = 4 * coordY p := by
  rw [laplacianOp_shellW_apply, (coord_antipode p).2.1, coord_sum_zero.2.1]
  ring

/-- The third coordinate is a shell eigenfunction at `λ = 4`. -/
theorem coordZ_eigen (p : Shell 1) :
    laplacianOp shellW coordZ p = 4 * coordZ p := by
  rw [laplacianOp_shellW_apply, (coord_antipode p).2.2, coord_sum_zero.2.2]
  ring

/-- **CB-3 headline.** The shell's Fiedler value is at most `4`,
by exhibition of the first coordinate mode (banked
`fiedler_le_of_eigenvector`). -/
theorem fiedler_shellW_le_four : fiedler (shellW (R := 1)) ≤ 4 := by
  refine fiedler_le_of_eigenvector _ shellW_symm shellW_nonneg _ _
    coord_sum_zero.1 ?_ coordX_eigen
  intro h
  have h1 := congrFun h ⟨(1, 0, 0), by decide⟩
  simp only [Pi.zero_apply] at h1
  norm_num [coordX] at h1

/-! ## CB-4 — Full resolution -/

/-- **The energy identity (SOS form).** For every potential `φ` on
the shell,
`energy φ = 4 ‖φ‖² + ½ ∑ p, (φ p + φ (antipode p))² − (∑ φ)²`:
the pointwise formula gives `5‖φ‖² + ∑ φ·φ∘antipode − (∑φ)²`, and
the pair-square sum is `2‖φ‖² + 2∑ φ·φ∘antipode` (the antipode
reindexing is an involution). The two correction terms are a sum of
squares and a square — the floor at `4` is read off in the next
theorem. This is the memo's sanctioned SOS route. -/
theorem energy_shellW (φ : Shell 1 → ℝ) :
    energy shellW φ = 4 * (∑ p, φ p ^ 2)
      + (∑ p, (φ p + φ (antipode p)) ^ 2) / 2 - (∑ p, φ p) ^ 2 := by
  have hanti : ∑ p, φ (antipode p) ^ 2 = ∑ p, φ p ^ 2 :=
    Equiv.sum_comp (Function.Involutive.toPerm antipode antipode_antipode)
      (fun p => φ p ^ 2)
  have hB : (∑ p, (φ p + φ (antipode p)) ^ 2)
      = (∑ p, φ p ^ 2) + (∑ p, φ (antipode p) ^ 2)
        + 2 * (∑ p, φ p * φ (antipode p)) := by
    have h : (∑ p, (φ p + φ (antipode p)) ^ 2)
        = ∑ p, (φ p ^ 2 + φ (antipode p) ^ 2
            + 2 * (φ p * φ (antipode p))) := by
      apply Finset.sum_congr rfl
      intro p _
      ring
    rw [h, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hE : energy shellW φ = 5 * (∑ p, φ p ^ 2)
      + (∑ p, φ p * φ (antipode p)) - (∑ p, φ p) ^ 2 := by
    rw [energy_def]
    have hpt : ∀ p : Shell 1, φ p * laplacianOp shellW φ p
        = φ p * (5 * φ p) + φ p * φ (antipode p) - φ p * (∑ q, φ q) := by
      intro p
      rw [laplacianOp_shellW_apply]
      ring
    simp only [hpt]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    have hS1 : (∑ p, φ p * (5 * φ p)) = 5 * (∑ p, φ p ^ 2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      ring
    have hS3 : (∑ p, φ p * (∑ q, φ q)) = (∑ p, φ p) ^ 2 := by
      rw [← Finset.sum_mul, pow_two]
    rw [hS1, hS3]
  rw [hE]
  linarith [hB, hanti]

/-- **The floor.** A mean-zero potential has energy at least
`4 ‖φ‖²`: in the SOS identity the mean term vanishes and the
pair-square term is a sum of squares. -/
theorem four_le_energy_of_mean_zero (φ : Shell 1 → ℝ)
    (hφ : ∑ p, φ p = 0) :
    4 * (∑ p, φ p ^ 2) ≤ energy shellW φ := by
  rw [energy_shellW, hφ]
  have hB : 0 ≤ (∑ p, (φ p + φ (antipode p)) ^ 2) / 2 := by
    apply div_nonneg _ (by norm_num)
    apply Finset.sum_nonneg
    intro p _
    exact sq_nonneg _
  linarith [hB]

/-- The squared coordinate sums: each coordinate is `±1` on exactly
one antipodal pair. -/
theorem sqCoord_sum :
    (∑ p, coordX p ^ 2 = 2) ∧ (∑ p, coordY p ^ 2 = 2) ∧
    (∑ p, coordZ p ^ 2 = 2) := by
  have hX : ∑ p, coordX p ^ 2 = 2 := by
    have h1 : (∑ p : Shell 1, coordX p ^ 2)
        = ∑ t ∈ shellFinset 1, ((t.1 : ℤ) : ℝ) ^ 2 :=
      Finset.sum_coe_sort (shellFinset 1)
        (fun t : ℤ × ℤ × ℤ => ((t.1 : ℤ) : ℝ) ^ 2)
    rw [h1, shellFinset_one]
    norm_num [Finset.sum_insert, Finset.sum_singleton]
  have hY : ∑ p, coordY p ^ 2 = 2 := by
    have h1 : (∑ p : Shell 1, coordY p ^ 2)
        = ∑ t ∈ shellFinset 1, ((t.2.1 : ℤ) : ℝ) ^ 2 :=
      Finset.sum_coe_sort (shellFinset 1)
        (fun t : ℤ × ℤ × ℤ => ((t.2.1 : ℤ) : ℝ) ^ 2)
    rw [h1, shellFinset_one]
    norm_num [Finset.sum_insert, Finset.sum_singleton]
  have hZ : ∑ p, coordZ p ^ 2 = 2 := by
    have h1 : (∑ p : Shell 1, coordZ p ^ 2)
        = ∑ t ∈ shellFinset 1, ((t.2.2 : ℤ) : ℝ) ^ 2 :=
      Finset.sum_coe_sort (shellFinset 1)
        (fun t : ℤ × ℤ × ℤ => ((t.2.2 : ℤ) : ℝ) ^ 2)
    rw [h1, shellFinset_one]
    norm_num [Finset.sum_insert, Finset.sum_singleton]
  exact ⟨hX, hY, hZ⟩

/-- The first pair mode: `+1` on the first antipodal pair, `-1` on
the second, `0` on the third (as a difference of pair indicators
`coordX² − coordY²`). -/
def modeXY (p : Shell 1) : ℝ := coordX p ^ 2 - coordY p ^ 2

/-- The second pair mode: `coordX² − coordZ²`. -/
def modeXZ (p : Shell 1) : ℝ := coordX p ^ 2 - coordZ p ^ 2

/-- The first pair mode is a shell eigenfunction at `λ = 6`:
it is antipode-even with mean zero, so the pointwise formula gives
`5φ + φ − 0 = 6φ`. -/
theorem modeXY_eigen (p : Shell 1) :
    laplacianOp shellW modeXY p = 6 * modeXY p := by
  have hsum : ∑ q, modeXY q = 0 := by
    have h : (∑ q, modeXY q)
        = (∑ q, coordX q ^ 2) - (∑ q, coordY q ^ 2) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro q _
      rfl
    rw [h, sqCoord_sum.1, sqCoord_sum.2.1]
    norm_num
  have hanti : modeXY (antipode p) = modeXY p := by
    simp only [modeXY, (coord_antipode p).1, (coord_antipode p).2.1, neg_sq]
  rw [laplacianOp_shellW_apply, hsum, hanti]
  ring

/-- The second pair mode is a shell eigenfunction at `λ = 6`. -/
theorem modeXZ_eigen (p : Shell 1) :
    laplacianOp shellW modeXZ p = 6 * modeXZ p := by
  have hsum : ∑ q, modeXZ q = 0 := by
    have h : (∑ q, modeXZ q)
        = (∑ q, coordX q ^ 2) - (∑ q, coordZ q ^ 2) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro q _
      rfl
    rw [h, sqCoord_sum.1, sqCoord_sum.2.2]
    norm_num
  have hanti : modeXZ (antipode p) = modeXZ p := by
    simp only [modeXZ, (coord_antipode p).1, (coord_antipode p).2.2, neg_sq]
  rw [laplacianOp_shellW_apply, hsum, hanti]
  ring

/-- **The value `6` is attained** as a shell eigenvalue, by the
first pair mode. -/
theorem eigen_six :
    ∃ φ : Shell 1 → ℝ, φ ≠ 0 ∧
      ∀ p, laplacianOp shellW φ p = 6 * φ p := by
  refine ⟨modeXY, ?_, modeXY_eigen⟩
  intro h
  have h1 := congrFun h ⟨(1, 0, 0), by decide⟩
  simp only [Pi.zero_apply] at h1
  norm_num [modeXY, coordX, coordY] at h1

/-- **The floor, variationally.** The shell's Fiedler value is at
least `4`: every admissible potential has energy `≥ 4 · 1`. -/
theorem fiedler_shellW_ge_four : 4 ≤ fiedler (shellW (R := 1)) := by
  rw [fiedler_def]
  apply le_csInf
  · exact fiedlerSet_nonempty_of_exists_ne _
      (a := ⟨(1, 0, 0), by decide⟩) (b := ⟨(-1, 0, 0), by decide⟩)
      (by decide)
  · intro μ hμ
    rcases hμ with ⟨F, hF0, hF2, rfl⟩
    rw [← energy_def]
    have h := four_le_energy_of_mean_zero F hF0
    rw [hF2] at h
    linarith [h]

/-- **CB-4 headline — the shell's Fiedler value is exactly `4`.**
The resolution of the seat: `fiedler shellW = 4`, the upper bound
by exhibition (CB-3), the lower bound by the SOS floor. The rung
`K-CYM-LADDER` does not fire. -/
theorem fiedler_shellW : fiedler (shellW (R := 1)) = 4 :=
  le_antisymm fiedler_shellW_le_four fiedler_shellW_ge_four

/-! ## CB-4b — Pairwise orthogonality of the exhibited families -/

/-- The banked bilinear form on an eigenfunction: `bilin w F G`
is the eigenvalue times the inner product `∑ G·F`. -/
theorem bilin_eigen_left (F G : Shell 1 → ℝ) (μ : ℝ)
    (hF : ∀ p, laplacianOp shellW F p = μ * F p) :
    bilin shellW F G = μ * (∑ p, G p * F p) := by
  rw [bilin_def, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  rw [hF p]
  ring

/-- **The cross inner products vanish.** Between the coordinate
family (`λ = 4`) and the pair-mode family (`λ = 6`), and inside
the coordinate family, every exhibited cross inner product is `0`
(census computations). Deliberately NOT claimed: the two pair
modes against each other — `∑ modeXZ·modeXY = 2 ≠ 0`; they span
the two-dimensional `λ = 6` eigenspace at inner product `2`
(norms² `4` each), so the exhibited pair basis is not orthogonal.
Orthogonality is a between-family statement here. -/
theorem cross_inner_zero :
    (∑ p, coordY p * coordX p = 0) ∧ (∑ p, coordZ p * coordX p = 0) ∧
    (∑ p, coordZ p * coordY p = 0) ∧
    (∑ p, modeXY p * coordX p = 0) ∧ (∑ p, modeXY p * coordY p = 0) ∧
    (∑ p, modeXY p * coordZ p = 0) ∧
    (∑ p, modeXZ p * coordX p = 0) ∧ (∑ p, modeXZ p * coordY p = 0) ∧
    (∑ p, modeXZ p * coordZ p = 0) := by
  have c1 : ∑ p, coordY p * coordX p = 0 := by
    have h1 : (∑ p : Shell 1, coordY p * coordX p)
        = ∑ t ∈ shellFinset 1, ((t.2.1 : ℤ) : ℝ) * ((t.1 : ℤ) : ℝ) :=
      Finset.sum_coe_sort (shellFinset 1)
        (fun t : ℤ × ℤ × ℤ => ((t.2.1 : ℤ) : ℝ) * ((t.1 : ℤ) : ℝ))
    rw [h1, shellFinset_one]
    norm_num [Finset.sum_insert, Finset.sum_singleton]
  have c2 : ∑ p, coordZ p * coordX p = 0 := by
    have h1 : (∑ p : Shell 1, coordZ p * coordX p)
        = ∑ t ∈ shellFinset 1, ((t.2.2 : ℤ) : ℝ) * ((t.1 : ℤ) : ℝ) :=
      Finset.sum_coe_sort (shellFinset 1)
        (fun t : ℤ × ℤ × ℤ => ((t.2.2 : ℤ) : ℝ) * ((t.1 : ℤ) : ℝ))
    rw [h1, shellFinset_one]
    norm_num [Finset.sum_insert, Finset.sum_singleton]
  have c3 : ∑ p, coordZ p * coordY p = 0 := by
    have h1 : (∑ p : Shell 1, coordZ p * coordY p)
        = ∑ t ∈ shellFinset 1, ((t.2.2 : ℤ) : ℝ) * ((t.2.1 : ℤ) : ℝ) :=
      Finset.sum_coe_sort (shellFinset 1)
        (fun t : ℤ × ℤ × ℤ => ((t.2.2 : ℤ) : ℝ) * ((t.2.1 : ℤ) : ℝ))
    rw [h1, shellFinset_one]
    norm_num [Finset.sum_insert, Finset.sum_singleton]
  have c4 : ∑ p, modeXY p * coordX p = 0 := by
    have h1 : (∑ p : Shell 1, modeXY p * coordX p)
        = ∑ t ∈ shellFinset 1,
            (((t.1 : ℤ) : ℝ) ^ 2 - ((t.2.1 : ℤ) : ℝ) ^ 2)
              * ((t.1 : ℤ) : ℝ) :=
      Finset.sum_coe_sort (shellFinset 1)
        (fun t : ℤ × ℤ × ℤ =>
          (((t.1 : ℤ) : ℝ) ^ 2 - ((t.2.1 : ℤ) : ℝ) ^ 2)
            * ((t.1 : ℤ) : ℝ))
    rw [h1, shellFinset_one]
    norm_num [Finset.sum_insert, Finset.sum_singleton]
  have c5 : ∑ p, modeXY p * coordY p = 0 := by
    have h1 : (∑ p : Shell 1, modeXY p * coordY p)
        = ∑ t ∈ shellFinset 1,
            (((t.1 : ℤ) : ℝ) ^ 2 - ((t.2.1 : ℤ) : ℝ) ^ 2)
              * ((t.2.1 : ℤ) : ℝ) :=
      Finset.sum_coe_sort (shellFinset 1)
        (fun t : ℤ × ℤ × ℤ =>
          (((t.1 : ℤ) : ℝ) ^ 2 - ((t.2.1 : ℤ) : ℝ) ^ 2)
            * ((t.2.1 : ℤ) : ℝ))
    rw [h1, shellFinset_one]
    norm_num [Finset.sum_insert, Finset.sum_singleton]
  have c6 : ∑ p, modeXY p * coordZ p = 0 := by
    have h1 : (∑ p : Shell 1, modeXY p * coordZ p)
        = ∑ t ∈ shellFinset 1,
            (((t.1 : ℤ) : ℝ) ^ 2 - ((t.2.1 : ℤ) : ℝ) ^ 2)
              * ((t.2.2 : ℤ) : ℝ) :=
      Finset.sum_coe_sort (shellFinset 1)
        (fun t : ℤ × ℤ × ℤ =>
          (((t.1 : ℤ) : ℝ) ^ 2 - ((t.2.1 : ℤ) : ℝ) ^ 2)
            * ((t.2.2 : ℤ) : ℝ))
    rw [h1, shellFinset_one]
    norm_num [Finset.sum_insert, Finset.sum_singleton]
  have c7 : ∑ p, modeXZ p * coordX p = 0 := by
    have h1 : (∑ p : Shell 1, modeXZ p * coordX p)
        = ∑ t ∈ shellFinset 1,
            (((t.1 : ℤ) : ℝ) ^ 2 - ((t.2.2 : ℤ) : ℝ) ^ 2)
              * ((t.1 : ℤ) : ℝ) :=
      Finset.sum_coe_sort (shellFinset 1)
        (fun t : ℤ × ℤ × ℤ =>
          (((t.1 : ℤ) : ℝ) ^ 2 - ((t.2.2 : ℤ) : ℝ) ^ 2)
            * ((t.1 : ℤ) : ℝ))
    rw [h1, shellFinset_one]
    norm_num [Finset.sum_insert, Finset.sum_singleton]
  have c8 : ∑ p, modeXZ p * coordY p = 0 := by
    have h1 : (∑ p : Shell 1, modeXZ p * coordY p)
        = ∑ t ∈ shellFinset 1,
            (((t.1 : ℤ) : ℝ) ^ 2 - ((t.2.2 : ℤ) : ℝ) ^ 2)
              * ((t.2.1 : ℤ) : ℝ) :=
      Finset.sum_coe_sort (shellFinset 1)
        (fun t : ℤ × ℤ × ℤ =>
          (((t.1 : ℤ) : ℝ) ^ 2 - ((t.2.2 : ℤ) : ℝ) ^ 2)
            * ((t.2.1 : ℤ) : ℝ))
    rw [h1, shellFinset_one]
    norm_num [Finset.sum_insert, Finset.sum_singleton]
  have c9 : ∑ p, modeXZ p * coordZ p = 0 := by
    have h1 : (∑ p : Shell 1, modeXZ p * coordZ p)
        = ∑ t ∈ shellFinset 1,
            (((t.1 : ℤ) : ℝ) ^ 2 - ((t.2.2 : ℤ) : ℝ) ^ 2)
              * ((t.2.2 : ℤ) : ℝ) :=
      Finset.sum_coe_sort (shellFinset 1)
        (fun t : ℤ × ℤ × ℤ =>
          (((t.1 : ℤ) : ℝ) ^ 2 - ((t.2.2 : ℤ) : ℝ) ^ 2)
            * ((t.2.2 : ℤ) : ℝ))
    rw [h1, shellFinset_one]
    norm_num [Finset.sum_insert, Finset.sum_singleton]
  exact ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9⟩

/-- **CB-4b headline.** The banked bilinear form vanishes on every
exhibited cross-family pair (and inside the coordinate family):
the `λ = 4` and `λ = 6` exhibited families are pairwise orthogonal
in the form of the memo. -/
theorem exhibited_orthogonal :
    bilin shellW coordX coordY = 0 ∧ bilin shellW coordX coordZ = 0 ∧
    bilin shellW coordY coordZ = 0 ∧
    bilin shellW coordX modeXY = 0 ∧ bilin shellW coordY modeXY = 0 ∧
    bilin shellW coordZ modeXY = 0 ∧
    bilin shellW coordX modeXZ = 0 ∧ bilin shellW coordY modeXZ = 0 ∧
    bilin shellW coordZ modeXZ = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [bilin_eigen_left coordX coordY 4 coordX_eigen,
      cross_inner_zero.1, mul_zero]
  · rw [bilin_eigen_left coordX coordZ 4 coordX_eigen,
      cross_inner_zero.2.1, mul_zero]
  · rw [bilin_eigen_left coordY coordZ 4 coordY_eigen,
      cross_inner_zero.2.2.1, mul_zero]
  · rw [bilin_eigen_left coordX modeXY 4 coordX_eigen,
      cross_inner_zero.2.2.2.1, mul_zero]
  · rw [bilin_eigen_left coordY modeXY 4 coordY_eigen,
      cross_inner_zero.2.2.2.2.1, mul_zero]
  · rw [bilin_eigen_left coordZ modeXY 4 coordZ_eigen,
      cross_inner_zero.2.2.2.2.2.1, mul_zero]
  · rw [bilin_eigen_left coordX modeXZ 4 coordX_eigen,
      cross_inner_zero.2.2.2.2.2.2.1, mul_zero]
  · rw [bilin_eigen_left coordY modeXZ 4 coordY_eigen,
      cross_inner_zero.2.2.2.2.2.2.2.1, mul_zero]
  · rw [bilin_eigen_left coordZ modeXZ 4 coordZ_eigen,
      cross_inner_zero.2.2.2.2.2.2.2.2, mul_zero]

/-! ## CB-6 — The nodal split of the fundamental mode -/

/-- The positive sign class of the fundamental mode `coordX` is
the single point `+e₁`. -/
theorem coordX_pos :
    (Finset.univ.filter (fun p => 0 < coordX p))
      = {⟨(1, 0, 0), by decide⟩} := by
  classical
  ext p
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_singleton]
  constructor
  · intro hp
    rcases shell_one_cases p with h | h | h | h | h | h
    · exact Subtype.ext h
    all_goals
      exfalso
      simp only [coordX, h] at hp
      norm_num at hp
  · intro hp
    rw [hp]
    norm_num [coordX]

/-- The negative sign class of the fundamental mode `coordX` is
the single point `-e₁`. -/
theorem coordX_neg :
    (Finset.univ.filter (fun p => coordX p < 0))
      = {⟨(-1, 0, 0), by decide⟩} := by
  classical
  ext p
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_singleton]
  constructor
  · intro hp
    rcases shell_one_cases p with h | h | h | h | h | h
    swap
    · exact Subtype.ext h
    all_goals
      exfalso
      simp only [coordX, h] at hp
      norm_num at hp
  · intro hp
    rw [hp]
    norm_num [coordX]

/-- The zero class (nodal set) of the fundamental mode is the
equatorial four: the two other antipodal pairs. -/
theorem coordX_zero :
    (Finset.univ.filter (fun p => coordX p = 0))
      = {⟨(0, 1, 0), by decide⟩, ⟨(0, -1, 0), by decide⟩,
        ⟨(0, 0, 1), by decide⟩, ⟨(0, 0, -1), by decide⟩} := by
  classical
  ext p
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro hp
    rcases shell_one_cases p with h | h | h | h | h | h
    · exfalso
      simp only [coordX, h] at hp
      norm_num at hp
    · exfalso
      simp only [coordX, h] at hp
      norm_num at hp
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Or.inl (Subtype.ext h))
    · exact Or.inr (Or.inr (Or.inl (Subtype.ext h)))
    · exact Or.inr (Or.inr (Or.inr (Subtype.ext h)))
  · intro hp
    rcases hp with rfl | rfl | rfl | rfl <;> norm_num [coordX]

/-- The nodal set of the fundamental mode has exactly four points. -/
theorem coordX_zero_card :
    (Finset.univ.filter (fun p => coordX p = 0)).card = 4 := by
  rw [coordX_zero]
  decide

/-- Same nodal domain: `p` and `q` are joined by a path whose
steps are shell edges with both endpoints in one strict sign
class of `φ` (both positive or both negative). -/
def SameDomain (φ : Shell 1 → ℝ) (p q : Shell 1) : Prop :=
  Relation.ReflTransGen
    (fun a b => shellW a b ≠ 0 ∧
      (0 < φ a ∧ 0 < φ b ∨ φ a < 0 ∧ φ b < 0)) p q

/-- A same-domain path preserves the strict sign of its start. -/
theorem sameDomain_sign (φ : Shell 1 → ℝ) {p q : Shell 1}
    (h : SameDomain φ p q) (hp : 0 < φ p) : 0 < φ q := by
  induction h with
  | refl => exact hp
  | tail _ hstep ih =>
    rcases hstep.2 with ⟨-, hq⟩ | ⟨hb, -⟩
    · exact hq
    · linarith [ih, hb]

/-- **CB-6 headline — the fundamental mode has exactly two nodal
domains.** The positive class and the negative class of `coordX`
are each a single point (CB-6 census), hence each is trivially
one domain; and no same-domain path crosses from positive to
negative, since a path preserves the sign of its start. The
two-lobe split is a theorem of the seat. **K-CYM-NODAL does not
fire** — the count is `2`. -/
theorem nodal_two_domains :
    (∀ p q : Shell 1, 0 < coordX p → 0 < coordX q →
      SameDomain coordX p q) ∧
    (∀ p q : Shell 1, coordX p < 0 → coordX q < 0 →
      SameDomain coordX p q) ∧
    (∀ p q : Shell 1, 0 < coordX p → coordX q < 0 →
      ¬ SameDomain coordX p q) := by
  have hpos : ∀ p : Shell 1, 0 < coordX p
      → p = ⟨(1, 0, 0), by decide⟩ := by
    intro p hp
    have hmem : p ∈ Finset.univ.filter (fun p => 0 < coordX p) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hp
    rw [coordX_pos] at hmem
    exact Finset.mem_singleton.mp hmem
  have hneg : ∀ p : Shell 1, coordX p < 0
      → p = ⟨(-1, 0, 0), by decide⟩ := by
    intro p hp
    have hmem : p ∈ Finset.univ.filter (fun p => coordX p < 0) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hp
    rw [coordX_neg] at hmem
    exact Finset.mem_singleton.mp hmem
  refine ⟨?_, ?_, ?_⟩
  · intro p q hp hq
    rw [hpos p hp, hpos q hq]
    exact Relation.ReflTransGen.refl
  · intro p q hp hq
    rw [hneg p hp, hneg q hq]
    exact Relation.ReflTransGen.refl
  · intro p q hp hq hpath
    have hsign := sameDomain_sign coordX hpath hp
    linarith [hsign, hq]

/-! ## CB-5 — The Planck rung: `E = h√λ`, `h` bare -/

/-- **Mode energy.** `E = h √λ`, with `h` a BARE PARAMETER —
never assigned a value anywhere in this pin. The seat's Laplacian
eigenvalue `λ` plays the role of (frequency)², so `√λ` is the
mode's tone and `h√λ` its Planck price, in the finite form of
`E = hf`. No real-Earth claim is made or implied; the scale gap
between this seat's tones and any physical frequency stays
FRONTIER, named and untouched. -/
noncomputable def modeEnergy (h lam : ℝ) : ℝ := h * Real.sqrt lam

/-- The zero mode is free: `E(h, 0) = 0`. -/
theorem modeEnergy_zero (h : ℝ) : modeEnergy h 0 = 0 := by
  simp [modeEnergy]

/-- **CB-5 headline.** The seat's fundamental tone — the Fiedler
rung `λ = 4` of CB-4 — carries Planck price exactly `2h`. -/
theorem modeEnergy_fiedler (h : ℝ) :
    modeEnergy h (fiedler (shellW (R := 1))) = 2 * h := by
  have hsqrt4 : Real.sqrt (4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [modeEnergy, fiedler_shellW, hsqrt4]
  ring

/-- The top exhibited rung: `E(h, 6) = h√6`. -/
theorem modeEnergy_six (h : ℝ) : modeEnergy h 6 = h * Real.sqrt 6 :=
  rfl

/-- Mode energy is monotone in the rung for `0 ≤ h`. -/
theorem modeEnergy_mono (h : ℝ) (hh : 0 ≤ h) {a b : ℝ} (hab : a ≤ b) :
    modeEnergy h a ≤ modeEnergy h b :=
  mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hab) hh

/-- **The seat's energy ladder.** Reading the exhibited spectrum
of CB-3/CB-4 through the Planck rung: the constant mode at `0`
(multiplicity 1), the fundamental at `2h` (multiplicity 3 — the
coordinate modes), the pair rung at `h√6` (multiplicity 2 — the
pair modes). The ladder is the finite form of the postulate's
`E = hf` half; the identification of any rung with a physical
tone is not made. -/
theorem energy_ladder (h : ℝ) :
    modeEnergy h 0 = 0 ∧
    modeEnergy h (fiedler (shellW (R := 1))) = 2 * h ∧
    modeEnergy h 6 = h * Real.sqrt 6 :=
  ⟨modeEnergy_zero h, modeEnergy_fiedler h, modeEnergy_six h⟩

/-! ## CB-7 (STRETCH) — Every Fiedler mode has exactly two nodal domains -/

/-- The total of a potential is the sum of its six vertex values,
in census order. -/
theorem sum_shell (φ : Shell 1 → ℝ) :
    ∑ q, φ q = φ ⟨(1, 0, 0), by decide⟩
      + (φ ⟨(-1, 0, 0), by decide⟩
      + (φ ⟨(0, 1, 0), by decide⟩
      + (φ ⟨(0, -1, 0), by decide⟩
      + (φ ⟨(0, 0, 1), by decide⟩
      + φ ⟨(0, 0, -1), by decide⟩)))) := by
  have huniv : (Finset.univ : Finset (Shell 1))
      = {⟨(1, 0, 0), by decide⟩, ⟨(-1, 0, 0), by decide⟩,
        ⟨(0, 1, 0), by decide⟩, ⟨(0, -1, 0), by decide⟩,
        ⟨(0, 0, 1), by decide⟩, ⟨(0, 0, -1), by decide⟩} := by
    ext q
    simp only [Finset.mem_univ, true_iff, Finset.mem_insert,
      Finset.mem_singleton]
    rcases shell_one_cases q with h | h | h | h | h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Or.inl (Subtype.ext h))
    · exact Or.inr (Or.inr (Or.inl (Subtype.ext h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (Subtype.ext h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Subtype.ext h)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Subtype.ext h)))))
  rw [huniv, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]

/-- **The Fiedler eigenspace is the coordinate span.** A
`λ = 4` eigenfunction is determined by its three positive-pole
values: the eigen-equation at each positive pole forces the
antipodal value to be `(∑φ) − (pole value)`, and summing the
three forces `∑φ = 0` — so the mode is antipode-odd and equals
`a·coordX + b·coordY + c·coordZ` with `a, b, c` its pole values. -/
theorem fiedler_mode_form (φ : Shell 1 → ℝ)
    (hφ : ∀ p, laplacianOp shellW φ p = 4 * φ p) (p : Shell 1) :
    φ p = φ ⟨(1, 0, 0), by decide⟩ * coordX p
      + φ ⟨(0, 1, 0), by decide⟩ * coordY p
      + φ ⟨(0, 0, 1), by decide⟩ * coordZ p := by
  have hanti1 : antipode ⟨(1, 0, 0), by decide⟩
      = ⟨(-1, 0, 0), by decide⟩ := by
    apply Subtype.ext
    rw [antipode_val]
    rfl
  have hanti2 : antipode ⟨(0, 1, 0), by decide⟩
      = ⟨(0, -1, 0), by decide⟩ := by
    apply Subtype.ext
    rw [antipode_val]
    rfl
  have hanti3 : antipode ⟨(0, 0, 1), by decide⟩
      = ⟨(0, 0, -1), by decide⟩ := by
    apply Subtype.ext
    rw [antipode_val]
    rfl
  have e1 := hφ ⟨(1, 0, 0), by decide⟩
  rw [laplacianOp_shellW_apply, hanti1] at e1
  have e2 := hφ ⟨(0, 1, 0), by decide⟩
  rw [laplacianOp_shellW_apply, hanti2] at e2
  have e3 := hφ ⟨(0, 0, 1), by decide⟩
  rw [laplacianOp_shellW_apply, hanti3] at e3
  have hS := sum_shell φ
  have hS0 : (∑ q, φ q) = 0 := by linarith [e1, e2, e3, hS]
  have hn1 : φ ⟨(-1, 0, 0), by decide⟩
      = -φ ⟨(1, 0, 0), by decide⟩ := by linarith [e1, hS0]
  have hn2 : φ ⟨(0, -1, 0), by decide⟩
      = -φ ⟨(0, 1, 0), by decide⟩ := by linarith [e2, hS0]
  have hn3 : φ ⟨(0, 0, -1), by decide⟩
      = -φ ⟨(0, 0, 1), by decide⟩ := by linarith [e3, hS0]
  rcases shell_one_cases p with h | h | h | h | h | h
  · have hpp : p = ⟨(1, 0, 0), by decide⟩ := Subtype.ext h
    rw [hpp]
    norm_num [coordX, coordY, coordZ]
  · have hpp : p = ⟨(-1, 0, 0), by decide⟩ := Subtype.ext h
    rw [hpp, hn1]
    norm_num [coordX, coordY, coordZ]
  · have hpp : p = ⟨(0, 1, 0), by decide⟩ := Subtype.ext h
    rw [hpp]
    norm_num [coordX, coordY, coordZ]
  · have hpp : p = ⟨(0, -1, 0), by decide⟩ := Subtype.ext h
    rw [hpp, hn2]
    norm_num [coordX, coordY, coordZ]
  · have hpp : p = ⟨(0, 0, 1), by decide⟩ := Subtype.ext h
    rw [hpp]
    norm_num [coordX, coordY, coordZ]
  · have hpp : p = ⟨(0, 0, -1), by decide⟩ := Subtype.ext h
    rw [hpp, hn3]
    norm_num [coordX, coordY, coordZ]

/-- Every Fiedler mode is antipode-odd. -/
theorem fiedler_mode_antipode_odd (φ : Shell 1 → ℝ)
    (hφ : ∀ p, laplacianOp shellW φ p = 4 * φ p) (p : Shell 1) :
    φ (antipode p) = -φ p := by
  rw [fiedler_mode_form φ hφ p, fiedler_mode_form φ hφ (antipode p),
    (coord_antipode p).1, (coord_antipode p).2.1, (coord_antipode p).2.2]
  ring

/-- The domain structure of a Fiedler mode: each strict sign
class is one `SameDomain` class, and no path crosses. (Positive
vertices are pairwise non-antipodal — antipodes flip the sign —
hence adjacent by CB-2, hence joined by a single step.) -/
theorem fiedler_mode_domains (φ : Shell 1 → ℝ)
    (hφ : ∀ p, laplacianOp shellW φ p = 4 * φ p) :
    (∀ p q : Shell 1, 0 < φ p → 0 < φ q → SameDomain φ p q) ∧
    (∀ p q : Shell 1, φ p < 0 → φ q < 0 → SameDomain φ p q) ∧
    (∀ p q : Shell 1, 0 < φ p → φ q < 0 → ¬ SameDomain φ p q) := by
  have hstep : ∀ p q : Shell 1, q ≠ antipode p →
      ((0 < φ p ∧ 0 < φ q) ∨ (φ p < 0 ∧ φ q < 0)) →
      SameDomain φ p q := by
    intro p q hqa hdisj
    by_cases hpq : p = q
    · subst hpq
      exact Relation.ReflTransGen.refl
    · have hw1 : shellW p q = 1 := (shellW_eq_one_iff hpq).mpr hqa
      have hw : shellW p q ≠ 0 := by
        rw [hw1]
        exact one_ne_zero
      exact Relation.ReflTransGen.head ⟨hw, hdisj⟩
        Relation.ReflTransGen.refl
  refine ⟨?_, ?_, ?_⟩
  · intro p q hp hq
    apply hstep p q _ (Or.inl ⟨hp, hq⟩)
    intro h
    have hodd := fiedler_mode_antipode_odd φ hφ p
    rw [← h] at hodd
    linarith [hp, hq, hodd]
  · intro p q hp hq
    apply hstep p q _ (Or.inr ⟨hp, hq⟩)
    intro h
    have hodd := fiedler_mode_antipode_odd φ hφ p
    rw [← h] at hodd
    linarith [hp, hq, hodd]
  · intro p q hp hq hpath
    have hsign := sameDomain_sign φ hpath hp
    linarith [hsign, hq]

/-- A nonzero Fiedler mode takes both signs: some vertex is
positive, and its antipode is negative. -/
theorem fiedler_mode_signs_nonempty (φ : Shell 1 → ℝ)
    (hφ : ∀ p, laplacianOp shellW φ p = 4 * φ p) (hφne : φ ≠ 0) :
    (∃ p, 0 < φ p) ∧ (∃ p, φ p < 0) := by
  obtain ⟨p, hp⟩ : ∃ p, φ p ≠ 0 := by
    by_contra h
    push_neg at h
    exact hφne (funext h)
  have hodd := fiedler_mode_antipode_odd φ hφ p
  rcases lt_or_gt_of_ne hp with hlt | hgt
  · refine ⟨⟨antipode p, ?_⟩, ⟨p, hlt⟩⟩
    rw [hodd]
    linarith [hlt]
  · refine ⟨⟨p, hgt⟩, ⟨antipode p, ?_⟩⟩
    rw [hodd]
    linarith [hgt]

/-- **CB-7 headline (the stretch).** EVERY Fiedler mode of the
seat — every eigenfunction at `λ = fiedler shellW = 4`, not only
the exhibited `coordX` of CB-6 — has exactly two nodal domains:
each strict sign class is a single domain, no same-domain path
crosses between them, and a nonzero mode inhabits both sides.
The dipole two-lobe form of CB-6 is thus a property of the whole
Fiedler eigenspace. -/
theorem every_fiedler_mode_two_domains (φ : Shell 1 → ℝ)
    (hφ : ∀ p, laplacianOp shellW φ p
      = fiedler (shellW (R := 1)) * φ p)
    (hφne : φ ≠ 0) :
    (∀ p q : Shell 1, 0 < φ p → 0 < φ q → SameDomain φ p q) ∧
    (∀ p q : Shell 1, φ p < 0 → φ q < 0 → SameDomain φ p q) ∧
    (∀ p q : Shell 1, 0 < φ p → φ q < 0 → ¬ SameDomain φ p q) ∧
    (∃ p, 0 < φ p) ∧ (∃ p, φ p < 0) := by
  rw [fiedler_shellW] at hφ
  obtain ⟨h1, h2, h3⟩ := fiedler_mode_domains φ hφ
  obtain ⟨h4, h5⟩ := fiedler_mode_signs_nonempty φ hφ hφne
  exact ⟨h1, h2, h3, h4, h5⟩

end CymaticsBridgePin
end ThetLogos
