import Mathlib.Tactic
import ThetLogos.DialOneShapeBCoordinates
import ThetLogos.DialOneSwapOrbitBase

open Matrix Complex
open ThetLogos.Track1RouteB
open ThetLogos.PreOptionARepresentation
open ThetLogos.HyperchargeForcing
open ThetLogos.DialOneSeatTiePin
open ThetLogos.DialOneGammaTracePin
open ThetLogos.DialOneGammaTraceChecks
open ThetLogos.DialOneGammaFamilyChecks
open ThetLogos.DialOneDoubleFlipPin
open ThetLogos.DialOneClassificationPin
open ThetLogos.DialOneSwapOrbit
open ThetLogos.DialOneSwapOrbitBase
open ThetLogos.DialOneLeptonChapter
open ThetLogos.DialOneSwapColourChapter
open ThetLogos.DialOneShapeBCoordinates

namespace ThetLogos.DialOneShapeBIdentification

/-!
# ThetLogos.DialOneShapeBIdentification — CLS-B-ID: the Shape B identification on the toggle family

Governing texts: the CLS-B pin
(`DialOneShapeBCoordinates`: `ShapeBIdentification`,
`shapeBCoord`, `sectorPoly`, frozen) and the CLS-B-ID
pack (next-rotation scoping Lane 1 + SS1.5). This brick
was commissioned to PROVE the frozen identification on
the toggle family. **It does not hold. The verdict of
this module is a REFUTATION, at full rank: the frozen
`ShapeBIdentification` is FALSE, and every one of its
four clauses fails on a landed fiber point.** NO CLAIM;
Dial 1 = 0; all dials 0/4. Parts of any official
statement closed by this module: 0.

## The verdict, per member

For every toggle-family member `π` the `weightAt` fiber
is determined exactly in this module: it is a two-point
set `{E_π, -E_π}`, where `E_π` is the member's lifted
weight vector at its unique surviving primitive
determinant-one direction (the direction is pinned by
the member's determinant along the two-parameter family
plus `gcd = 1`, and the two points are the two signs of
that direction). The sector polynomials and the trace
coordinates are then computed on the nose:

* `pi1` (direction `(3, -1)`, `E = commonWeightVector`):
  `sectorPoly E = ![0, 0, 0, 0]` (the four sector
  polynomials vanish — the anomaly-shaped sums cancel),
  but `shapeBCoord pi1 = ![0, 0, 0, 4i]`. The clause
  fails at index 3 only: the cubic moment
  `Tr (pi1 (u1Gen 1 0))^3 = 4i` is a trace of `π` alone,
  while `sectorA111` reads the LIFTED (π ⊗ π°)
  weights; the two instruments disagree there by `4i`.
* `piFlip` (direction `(-2, 1)`): fiber
  `{flipWeight, -flipWeight}`,
  `sectorPoly flipWeight = ![0, -2, -4, -40]`,
  `shapeBCoord piFlip = ![0, 0, 2i, 6i]`. Clause fails
  at indices 1, 2, 3.
* `piEFlip` (direction `(-6, 1)`): fiber
  `{eflipWeight, -eflipWeight}`,
  `sectorPoly eflipWeight = ![0, 6, 12, 1080]`,
  `shapeBCoord piEFlip = ![0, 0, -2i, 2i]`. Clause
  fails at indices 1, 2, 3.
* `orbitRep b` for every `b : Fin 4 → Bool` (direction
  `(3, -1)`; covers `pi1`, `piDouble`, every `piSwap c`,
  and the all-swap point): fiber
  `{orbWeight b, -orbWeight b}`,
  `sectorPoly (orbWeight b) = ![0, 0, 0, 0]`, and
  `shapeBCoord (orbitRep b) = ![0, 0, 0, 4i]`. Clause
  fails at index 3 only, at every orbit point.

Index 0 (the SU(3)²U(1)-shaped coordinate) is the only
index at which the two sides agree on every member:
both are `0` everywhere.

## K-CLS-B resolution table (registered in the pin)

`shapeBCoord` across the realized toggle family:

| point | coordinates |
|---|---|
| `pi1` and ALL 16 orbit points `orbitRep b` (incl. `piDouble`, `piSwap c`, all-swap) | `![0, 0, 0, 4i]` |
| `piFlip` | `![0, 0, 2i, 6i]` |
| `piEFlip` | `![0, 0, -2i, 2i]` |

The instrument's resolution is therefore exactly:
the whole swap orbit (17 named points: `pi1` plus the
16 orbit representatives) COLLIDES at one value, and
the two lepton toggles are separated from the orbit
blob and from each other. This is coarser than the
pin's registered expectation ("at best up to swap
orbits"): the coordinates do not merely fail to
separate points within an orbit — they fail to
separate the orbit's points from `pi1` at all, because
every correction in the orbit family is a sign flip at
a seat pair whose γ-weighted and cubic contributions
cancel in pairs. Reported at exactly this coarseness,
never upgraded (K-CLS-B).

## The pin-shape finding

The colour-0 representative read in `sectorPoly` is
NOT the obstruction: on the swap family the sector
polynomials are provably insensitive to which colour
is swapped (they see only the symmetric sums
`x_uR + x_dR` and `x_uR^3 + x_dR^3`, and the colour-0
read of `orbWeight b` already gives `0`). The
obstruction is the moment shapes themselves: the
frozen coordinates are traces of the representation
`π` at Lie-algebra elements, whereas `sectorPoly`
evaluates the anomaly polynomials at the LIFTED
weights of `π ⊗ π°`. At the linear and quadratic
indices the two happen to agree on `pi1` and on the
orbit (both sides `0`); at the cubic index they
provably do not (`4i` against `0`). Any future
repaired instrument must change the coordinate side
(e.g. lifted traces) or the polynomial side — the
frozen Prop cannot be repaired by a different choice
of fiber vector, because the fiber is exactly
`{E_π, -E_π}` and `sectorPoly` is odd, so both fiber
points give the same sector values up to sign, and on
the orbit both give `0 ≠ 4i` at index 3.

## What is proved here (T1 inventory)

1. Character rigidity for integral characters
   (`char_eq_of_forall`) and the determinant-one
   direction pins for the three determinant shapes
   (`dir_pi1`, `dir_flip`, `dir_eflip`).
2. `pi1` at the U(1) generator is diagonal with the
   landed `pi1AVal`/`pi1BVal` tables
   (`pi1_u1Gen_diagonal`, via an `afAdd` decomposition
   through the landed `pi1_eq_diagonal`); the diagonal
   entries of `pi1` at `genHdiag`/`genCdiag`
   (`pi1_genHdiag_diag`, `pi1_genCdiag_diag`).
3. Per member: the diagonal form along the
   two-parameter family, the lifted-exponent formula,
   the determinant formula, the exact fiber
   (`fiber_pi1`, `fiber_piFlip`, `fiber_piEFlip`,
   `fiber_orbitRep`), and both fiber points realized.
4. Per member: the four coordinates computed
   (`shapeBCoord_pi1`, `shapeBCoord_piFlip`,
   `shapeBCoord_piEFlip`, `shapeBCoord_orbitRep`) and
   the sector polynomials on the fiber vectors
   (ℤ shadows, `decide`).
5. The refutation: `not_shapeBIdentification`, with
   the `pi1` clause as the primary kill (index 3) and
   per-clause kills for `piFlip` (index 1), `piEFlip`
   (index 1), and the orbit clause (index 3 at every
   `b`, via `orbWeight b`).
-/

/-! ## §1. Seat tables for the two non-U(1) generators -/

/-- The ℤ shadow of `pi1 genHdiag`'s diagonal:
`pi1 genHdiag i i = i * (sbHVal i)`, with `sbHVal`
the `+1`/`-1` alternation on the `H_L` seats and `0`
elsewhere (the ℍ-summand generator `!![i, 0; 0, -i]`
reads the isospin sign). -/
def sbHVal (v : ℕ) : ℤ := if v < 8 then (if v % 2 = 0 then 1 else -1) else 0

/-- The ℤ shadow of `pi1 genCdiag`'s diagonal:
`pi1 genCdiag i i = i * (sbCVal i)`, nonzero only on
the antiquark seats, where the M₃ diagonal
`!![i, 0, 0; 0, -i, 0; 0, 0, 0]` is read through
`star`: colour 0 gives `-i`, colour 1 gives `+i`,
colour 2 gives `0`. -/
def sbCVal (v : ℕ) : ℤ :=
  if v = 18 ∨ v = 19 ∨ v = 26 ∨ v = 27 then -1
  else if v = 20 ∨ v = 21 ∨ v = 28 ∨ v = 29 then 1
  else 0

/-! ## §2. The toggle sign tables and fiber vectors -/

/-- The seat set toggled by the orbit pattern `b`:
bit 0 toggles the two right-handed lepton seats
`s8, s9`; bit `c + 1` toggles the colour-`c`
right-handed quark seats `uSeat c, dSeat c`. -/
def sbToggled (b : Fin 4 → Bool) (s : Fin 32) : Prop :=
  (b 0 = true ∧ (s = s8 ∨ s = s9))
    ∨ ∃ c : Fin 3, b (swapIdx c) = true ∧ (s = uSeat c ∨ s = dSeat c)

instance (b : Fin 4 → Bool) (s : Fin 32) : Decidable (sbToggled b s) := by
  unfold sbToggled
  infer_instance

/-- The orbit sign table: `-1` exactly on the toggled
seats, `+1` elsewhere. Every orbit correction is a
sign flip of the `pi1AVal` exponent at its seats. -/
def sbOrbSign (b : Fin 4 → Bool) (s : Fin 32) : ℤ :=
  if sbToggled b s then -1 else 1

/-- The orbit A-table: `pi1AVal` sign-flipped at the
toggled seats. This is the diagonal exponent table of
`orbitRep b` along the two-parameter family (the
B-table is `pi1BVal`, untouched: every toggled seat
has `pi1BVal = 0`). -/
def sbOrbA (b : Fin 4 → Bool) (s : Fin 32) : ℤ :=
  sbOrbSign b s * pi1AVal s.val

/-- The orbit fiber vector at the surviving direction
`(3, -1)`: the lifted exponent of `orbitRep b`. For
`b = fun _ => false` it is `commonWeightVector`; for
the single-swap patterns it is CLS-3b's
`swappedWeightVector c`. -/
def sbOrbWeight (b : Fin 4 → Bool) (s : Fin 32) : ℤ :=
  (sbOrbA b s + sbOrbA b (partner s)) * 3
    + (pi1BVal s.val + pi1BVal (partner s).val) * (-1)

/-- The piFlip sign table: `-1` at `s8` only. -/
def sbFlipSign (s : Fin 32) : ℤ := if s = s8 then -1 else 1

/-- The piFlip A-table. -/
def sbFlipA (s : Fin 32) : ℤ := sbFlipSign s * pi1AVal s.val

/-- The piFlip fiber vector at its surviving direction
`(-2, 1)`. -/
def sbFlipWeight (s : Fin 32) : ℤ :=
  (sbFlipA s + sbFlipA (partner s)) * (-2)
    + (pi1BVal s.val + pi1BVal (partner s).val) * 1

/-- The piEFlip sign table: `-1` at `s9` only. -/
def sbEFlipSign (s : Fin 32) : ℤ := if s = s9 then -1 else 1

/-- The piEFlip A-table. -/
def sbEFlipA (s : Fin 32) : ℤ := sbEFlipSign s * pi1AVal s.val

/-- The piEFlip fiber vector at its surviving direction
`(-6, 1)`. -/
def sbEFlipWeight (s : Fin 32) : ℤ :=
  (sbEFlipA s + sbEFlipA (partner s)) * (-6)
    + (pi1BVal s.val + pi1BVal (partner s).val) * 1

/-! ## §3. ℤ shadows (all discharged by `decide`) -/

/-- The sector polynomials on the common vector are
all `0` — the anomaly-shaped sums cancel at the table
weights `(-3, -3, 1, 1, 0, -6, 4, -2)`. -/
theorem sector_common_zero :
    sectorA3 commonWeightVector = 0 ∧ sectorA2 commonWeightVector = 0
      ∧ sectorAgrav commonWeightVector = 0
      ∧ sectorA111 commonWeightVector = 0 := by decide

/-- The sector polynomials on the piFlip fiber vector:
`(0, -2, -4, -40)`. -/
theorem sector_flipWeight :
    sectorA3 sbFlipWeight = 0 ∧ sectorA2 sbFlipWeight = -2
      ∧ sectorAgrav sbFlipWeight = -4
      ∧ sectorA111 sbFlipWeight = -40 := by decide

/-- The sector polynomials on the piEFlip fiber vector:
`(0, 6, 12, 1080)`. -/
theorem sector_eflipWeight :
    sectorA3 sbEFlipWeight = 0 ∧ sectorA2 sbEFlipWeight = 6
      ∧ sectorAgrav sbEFlipWeight = 12
      ∧ sectorA111 sbEFlipWeight = 1080 := by decide

/-- The sector polynomials on every orbit fiber vector
are all `0`: the colour-0 read is swap-insensitive
(only the symmetric sums `x_uR + x_dR`,
`x_uR^3 + x_dR^3` and the lepton sums enter, and the
double flip exchanges the `ν_R`/`e_R` pair). -/
theorem sector_orbWeight (b : Fin 4 → Bool) :
    sectorA3 (sbOrbWeight b) = 0 ∧ sectorA2 (sbOrbWeight b) = 0
      ∧ sectorAgrav (sbOrbWeight b) = 0
      ∧ sectorA111 (sbOrbWeight b) = 0 := by
  revert b
  decide

/-- Determinant shadow for the orbit: the sign-flipped
A-table still sums to `-4` (each toggled pair
`{s8, s9}`, `{uSeat c, dSeat c}` has A-sum `0`). -/
theorem sum_orbA (b : Fin 4 → Bool) :
    ∑ s : Fin 32, sbOrbA b s = -4 := by
  revert b
  decide

/-- Determinant shadow for piFlip: the flipped A-table
sums to `-6`. -/
theorem sum_flipA : ∑ s : Fin 32, sbFlipA s = -6 := by decide

/-- Determinant shadow for piEFlip: the flipped A-table
sums to `-2`. -/
theorem sum_eflipA : ∑ s : Fin 32, sbEFlipA s = -2 := by decide

/-- Cubic shadow for pi1: `∑ A^3 = -4` (the A-table
takes values in `{-1, 0, 1}`, so `A^3 = A` seatwise
in the signed sum `(sbOrbSign * A)^3` form). -/
theorem sum_A3 : ∑ s : Fin 32, (pi1AVal s.val) ^ 3 = -4 := by decide

/-- Cubic shadow for the orbit: the signed cubes still
sum to `-4` at every pattern (each toggled pair has
cube-sum `0`). -/
theorem sum_orbA3 (b : Fin 4 → Bool) :
    ∑ s : Fin 32, (sbOrbSign b s * pi1AVal s.val) ^ 3 = -4 := by
  revert b
  decide

/-- Cubic shadow for piFlip. -/
theorem sum_flipA3 : ∑ s : Fin 32, (sbFlipSign s * pi1AVal s.val) ^ 3 = -6 := by
  decide

/-- Cubic shadow for piEFlip. -/
theorem sum_eflipA3 :
    ∑ s : Fin 32, (sbEFlipSign s * pi1AVal s.val) ^ 3 = -2 := by decide

/-- γ-weighted shadow for the orbit: the γ-weighted
signed A-sum vanishes at every pattern (each toggled
pair is γ-flat with A-sum `0`). -/
theorem gamma_sum_orbA (b : Fin 4 → Bool) :
    ∑ s : Fin 32, gammaVal s.val * sbOrbSign b s * pi1AVal s.val = 0 := by
  revert b
  decide

/-- The coord-0 shadow: `∑ sbCVal * B = 0`. -/
theorem sum_cB : ∑ i : Fin 32, sbCVal i.val * pi1BVal i.val = 0 := by decide

/-- The coord-1 shadow: the H-table and the A-table
have disjoint supports. -/
theorem sum_A_hval : ∀ i : Fin 32, pi1AVal i.val * sbHVal i.val = 0 := by
  decide

/-! ## §4. Character rigidity and direction pins -/

/-- `exp (k * i) = 1` with `k : ℤ` forces `k = 0`
(otherwise `π` would be rational). The landed
`im_int_mul_I` (CLS-2b) does the imaginary-part read. -/
theorem exp_int_mul_I_eq_one {k : ℤ}
    (h : Complex.exp ((k : ℂ) * Complex.I) = 1) : k = 0 := by
  obtain ⟨n, hn⟩ := (Complex.exp_eq_one_iff).mp h
  have him : ((k : ℤ) : ℝ) = (n : ℝ) * (2 * Real.pi) :=
    im_int_mul_I k n hn
  by_cases hn0 : n = 0
  · rw [hn0] at him
    simp at him
    exact_mod_cast him
  · exfalso
    apply irrational_pi.ne_rational k (2 * n)
    rw [eq_div_iff (by simp [hn0] : ((2 * n : ℤ) : ℝ) ≠ 0)]
    push_cast
    push_cast at him
    linarith [him]

/-- **Character rigidity**: two integral characters
agreeing at every `t : ℝ` have the same weight. -/
theorem char_eq_of_forall {m n : ℤ}
    (h : ∀ t : ℝ, Complex.exp ((m : ℂ) * (t : ℂ) * Complex.I)
      = Complex.exp ((n : ℂ) * (t : ℂ) * Complex.I)) : m = n := by
  have h1 : Complex.exp (((m - n : ℤ) : ℂ) * Complex.I) = 1 := by
    have hsub : Complex.exp ((m : ℂ) * ((1 : ℝ) : ℂ) * Complex.I
        - (n : ℂ) * ((1 : ℝ) : ℂ) * Complex.I) = 1 := by
      rw [Complex.exp_sub, h 1, div_self (Complex.exp_ne_zero _)]
    have hform : (((m - n : ℤ) : ℂ)) * Complex.I
        = (m : ℂ) * ((1 : ℝ) : ℂ) * Complex.I
          - (n : ℂ) * ((1 : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [← hform] at hsub
    exact hsub
  have := exp_int_mul_I_eq_one h1
  omega

/-- **Direction pin, `(3, -1)` shape**: a primitive
direction with `-4α - 12β = 0` is `±(3, -1)`. -/
theorem dir_of_det_shape_4312 {α β : ℤ}
    (hgcd : Nat.gcd α.natAbs β.natAbs = 1) (hlin : -4 * α + -12 * β = 0) :
    (α = 3 ∧ β = -1) ∨ (α = -3 ∧ β = 1) := by
  have hαβ : α = -3 * β := by omega
  have hβ : β = 1 ∨ β = -1 := by
    have h1 : β.natAbs = 1 := by
      have hα : α.natAbs = 3 * β.natAbs := by
        rw [hαβ]
        simp [Int.natAbs_mul]
      have hdvd : β.natAbs ∣ 1 := by
        rw [← hgcd, hα]
        exact dvd_gcd (dvd_mul_left _ _) dvd_rfl
      exact Nat.dvd_one.mp hdvd
    exact Int.isUnit_iff.mp (Int.isUnit_iff_natAbs_eq.mpr h1)
  rcases hβ with h | h
  · right
    omega
  · left
    omega

/-- **Direction pin, piFlip shape**: a primitive
direction with `-6α - 12β = 0` is `±(-2, 1)`. -/
theorem dir_of_det_shape_612 {α β : ℤ}
    (hgcd : Nat.gcd α.natAbs β.natAbs = 1) (hlin : -6 * α + -12 * β = 0) :
    (α = -2 ∧ β = 1) ∨ (α = 2 ∧ β = -1) := by
  have hαβ : α = -2 * β := by omega
  have hβ : β = 1 ∨ β = -1 := by
    have h1 : β.natAbs = 1 := by
      have hα : α.natAbs = 2 * β.natAbs := by
        rw [hαβ]
        simp [Int.natAbs_mul]
      have hdvd : β.natAbs ∣ 1 := by
        rw [← hgcd, hα]
        exact dvd_gcd (dvd_mul_left _ _) dvd_rfl
      exact Nat.dvd_one.mp hdvd
    exact Int.isUnit_iff.mp (Int.isUnit_iff_natAbs_eq.mpr h1)
  rcases hβ with h | h
  · left
    omega
  · right
    omega

/-- **Direction pin, piEFlip shape**: a primitive
direction with `-2α - 12β = 0` is `±(-6, 1)`. -/
theorem dir_of_det_shape_212 {α β : ℤ}
    (hgcd : Nat.gcd α.natAbs β.natAbs = 1) (hlin : -2 * α + -12 * β = 0) :
    (α = -6 ∧ β = 1) ∨ (α = 6 ∧ β = -1) := by
  have hαβ : α = -6 * β := by omega
  have hβ : β = 1 ∨ β = -1 := by
    have h1 : β.natAbs = 1 := by
      have hα : α.natAbs = 6 * β.natAbs := by
        rw [hαβ]
        simp [Int.natAbs_mul]
      have hdvd : β.natAbs ∣ 1 := by
        rw [← hgcd, hα]
        exact dvd_gcd (dvd_mul_left _ _) dvd_rfl
      exact Nat.dvd_one.mp hdvd
    exact Int.isUnit_iff.mp (Int.isUnit_iff_natAbs_eq.mpr h1)
  rcases hβ with h | h
  · left
    omega
  · right
    omega

/-! ## §5. Trace helpers -/

/-- Trace of a product with a diagonal right factor,
reduced to diagonal entries. -/
theorem trace_mul_diagonal (M : Matrix (Fin 32) (Fin 32) ℂ)
    (d : Fin 32 → ℂ) :
    Matrix.trace (M * Matrix.diagonal d) = ∑ i, M i i * d i := by
  unfold Matrix.trace Matrix.diag
  apply Finset.sum_congr rfl
  intro i _
  rw [Matrix.mul_apply]
  have hdi : M i i * d i = M i i * Matrix.diagonal d i i := by
    rw [Matrix.diagonal_apply_eq]
  rw [hdi]
  apply Finset.sum_eq_single i
  · intro k _ hk
    rw [Matrix.diagonal_apply_ne _ hk, mul_zero]
  · intro hmem
    exact absurd (Finset.mem_univ _) hmem

/-- Trace of a product with a diagonal left factor,
reduced to diagonal entries. -/
theorem trace_diagonal_mul (d : Fin 32 → ℂ)
    (M : Matrix (Fin 32) (Fin 32) ℂ) :
    Matrix.trace (Matrix.diagonal d * M) = ∑ i, d i * M i i := by
  unfold Matrix.trace Matrix.diag
  apply Finset.sum_congr rfl
  intro i _
  rw [Matrix.mul_apply]
  have hdi : d i * M i i = Matrix.diagonal d i i * M i i := by
    rw [Matrix.diagonal_apply_eq]
  rw [hdi]
  apply Finset.sum_eq_single i
  · intro k _ hk
    rw [Matrix.diagonal_apply_ne _ (Ne.symm hk), zero_mul]
  · intro hmem
    exact absurd (Finset.mem_univ _) hmem

/-! ## §6. The workhorse: `pi1` at the U(1) generator is diagonal -/

/-- The generator decomposes through the landed
`⟨lam, 1, c • 1⟩` form plus a pure-ℍ correction. -/
theorem u1Gen_decomp (α β : ℤ) :
    u1Gen α β = afAdd ⟨(α : ℂ) * Complex.I, 1,
        ((β : ℂ) * Complex.I) • (1 : Matrix I3 I3 ℂ)⟩
      ⟨0, -1, 0⟩ := by
  rw [ThetLogos.PreOptionARepresentation.ext_iff]
  refine ⟨?_, ?_, ?_⟩ <;> simp [u1Gen, afAdd]

/-- `pi1` of the pure-ℍ correction is minus the zero
diagonal (its `⟨0, 1, 0⟩` partner is the landed
diagonal at `(0, 0)`, and the two sum to `afZero`). -/
theorem pi1_qneg : pi1 ⟨0, -1, 0⟩ = - Matrix.diagonal (pi1Diag 0 0) := by
  have h1 : pi1 ⟨(0 : ℂ), 1, (0 : ℂ) • (1 : Matrix I3 I3 ℂ)⟩
      = Matrix.diagonal (pi1Diag 0 0) := pi1_eq_diagonal 0 0
  have h2 : pi1 (afAdd ⟨(0 : ℂ), 1, (0 : ℂ) • (1 : Matrix I3 I3 ℂ)⟩
      ⟨0, -1, 0⟩) = 0 := by
    have hsum : afAdd ⟨(0 : ℂ), 1, (0 : ℂ) • (1 : Matrix I3 I3 ℂ)⟩
        ⟨0, -1, 0⟩ = afZero := by
      rw [ThetLogos.PreOptionARepresentation.ext_iff]
      refine ⟨?_, ?_, ?_⟩ <;> simp [afAdd, afZero]
    rw [hsum]
    exact pi1_zero
  rw [pi1_afAdd, h1] at h2
  exact eq_neg_of_add_eq_zero_right h2

/-- The diagonal-value computation behind the
workhorse: the `pi1Diag` difference at `(α·i, β·i)`
is the `i * (A α + B β)` table. 32-case exhaustion. -/
theorem pi1Diag_sub (α β : ℤ) (s : Fin 32) :
    pi1Diag ((α : ℂ) * Complex.I) ((β : ℂ) * Complex.I) s - pi1Diag 0 0 s
      = Complex.I * ((pi1AVal s.val * α + pi1BVal s.val * β : ℤ) : ℂ) := by
  obtain ⟨v, hv⟩ := s
  interval_cases v <;>
    simp [pi1Diag, pi1DiagVal, pi1AVal, pi1BVal] <;> ring

/-- **The workhorse**: `pi1` at the U(1) generator is
the diagonal matrix of its `A`/`B` tables. -/
theorem pi1_u1Gen_diagonal (α β : ℤ) :
    pi1 (u1Gen α β) = Matrix.diagonal
      (fun i => Complex.I * ((pi1AVal i.val * α + pi1BVal i.val * β : ℤ) : ℂ)) := by
  rw [u1Gen_decomp, pi1_afAdd, pi1_eq_diagonal, pi1_qneg]
  ext i j
  rw [Matrix.add_apply, Matrix.neg_apply]
  by_cases h : i = j
  · subst h
    rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq,
      Matrix.diagonal_apply_eq]
    have hh := pi1Diag_sub α β i
    rw [sub_eq_add_neg] at hh
    exact hh
  · rw [Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ h,
      Matrix.diagonal_apply_ne _ h]
    simp

/-- `pi1 genU1A` in diagonal form. -/
theorem pi1_genU1A_diagonal :
    pi1 genU1A = Matrix.diagonal
      (fun i => Complex.I * ((pi1AVal i.val : ℤ) : ℂ)) := by
  have h := pi1_u1Gen_diagonal 1 0
  refine h.trans ?_
  congr 1
  funext i
  simp

/-- `pi1 genU1B` in diagonal form. -/
theorem pi1_genU1B_diagonal :
    pi1 genU1B = Matrix.diagonal
      (fun i => Complex.I * ((pi1BVal i.val : ℤ) : ℂ)) := by
  have h := pi1_u1Gen_diagonal 0 1
  refine h.trans ?_
  congr 1
  funext i
  simp

/-- The diagonal of `pi1` at the ℍ generator:
32-case exhaustion over the entry definition. -/
theorem pi1_genHdiag_diag (i : Fin 32) :
    pi1 genHdiag i i = Complex.I * ((sbHVal i.val : ℤ) : ℂ) := by
  obtain ⟨v, hv⟩ := i
  interval_cases v <;> simp [pi1, genHdiag, sbHVal]

/-- The diagonal of `pi1` at the M₃ generator:
32-case exhaustion over the entry definition. -/
theorem pi1_genCdiag_diag (i : Fin 32) :
    pi1 genCdiag i i = Complex.I * ((sbCVal i.val : ℤ) : ℂ) := by
  obtain ⟨v, hv⟩ := i
  interval_cases v <;> simp [pi1, genCdiag, sbCVal]

/-! ## §7. The toggles at elements with `a.u1 = 0`

Every toggle correction is a `single` whose coefficient
is built from `a.u1` and `star a.u1` only, so at any
element with `a.u1 = 0` every toggle agrees with `pi1`.
The three non-U(1) Shape B generators (`genU1B`,
`genHdiag`, `genCdiag`) all have `u1`-component `0`. -/

theorem piFlip_of_u1_zero {a : AF} (h : a.u1 = 0) :
    ThetLogos.HyperchargeForcing.piFlip a = pi1 a := by
  have hsingle : Matrix.single s8 s8 (star a.u1 - a.u1) = 0 := by
    rw [h]
    simp only [star_zero, sub_self]
    ext i j
    simp [Matrix.single_apply]
  unfold ThetLogos.HyperchargeForcing.piFlip
  rw [hsingle, add_zero]

theorem piEFlip_of_u1_zero {a : AF} (h : a.u1 = 0) :
    piEFlip a = pi1 a := by
  have hsingle : Matrix.single s9 s9 (a.u1 - star a.u1) = 0 := by
    rw [h]
    simp only [star_zero, sub_self]
    ext i j
    simp [Matrix.single_apply]
  rw [piEFlip_unfold, hsingle, add_zero]

theorem orbitCorrD_of_u1_zero {a : AF} (h : a.u1 = 0) :
    orbitCorrD a = 0 := by
  ext i j
  simp [orbitCorrD, Matrix.single_apply, h]

theorem orbitCorrS_of_u1_zero (c : Fin 3) {a : AF} (h : a.u1 = 0) :
    orbitCorrS c a = 0 := by
  ext i j
  simp [orbitCorrS, Matrix.single_apply, h]

theorem orbitRep_of_u1_zero (b : Fin 4 → Bool) {a : AF} (h : a.u1 = 0) :
    orbitRep b a = pi1 a := by
  rw [orbitRep, orbitCorrD_of_u1_zero h, orbitCorrS_of_u1_zero 0 h,
    orbitCorrS_of_u1_zero 1 h, orbitCorrS_of_u1_zero 2 h]
  simp

theorem genU1B_u1 : (genU1B).u1 = 0 := by simp [genU1B, u1Gen]

theorem genHdiag_u1 : (genHdiag).u1 = 0 := rfl

theorem genCdiag_u1 : (genCdiag).u1 = 0 := rfl

/-! ## §8. The pi1 fiber -/

/-- pi1's lifted entry in exponential form, along a
general direction: the exponent is the sum of the
seat's and its partner's `A α + B β` table values
(from the landed `pi1_lifted_entry` and
`pi1Diag_exp_gen`). -/
theorem pi1_lifted_exp_gen (α β : ℤ) (t : ℝ) (s : Fin 32) :
    (pi1 (u1ParamGen α β t) * piOp (pi1 (u1ParamGen α β t))) s s
      = Complex.exp ((((pi1AVal s.val + pi1AVal (partner s).val) * α
          + (pi1BVal s.val + pi1BVal (partner s).val) * β : ℤ) : ℂ)
        * ((t : ℂ) * Complex.I)) := by
  rw [pi1_lifted_entry, pi1Diag_exp_gen, pi1Diag_exp_gen,
    ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The common weight vector is the `(3, -1)` lifted
exponent of pi1, seat by seat (via the landed
`pi1WVal_eq`: `W = 3A - B` at every slot). -/
theorem common_eq_exp (s : Fin 32) :
    commonWeightVector s
      = (pi1AVal s.val + pi1AVal (partner s).val) * 3
        + (pi1BVal s.val + pi1BVal (partner s).val) * (-1) := by
  show ThetLogos.Track1RouteB.W s
      + ThetLogos.Track1RouteB.W (partner s) = _
  rw [show ThetLogos.Track1RouteB.W s = pi1WVal s.val from rfl,
    show ThetLogos.Track1RouteB.W (partner s)
      = pi1WVal (partner s).val from rfl,
    pi1WVal_eq s, pi1WVal_eq (partner s)]
  ring

/-- Determinant pin for pi1: determinant one along
`(α, β)` forces `-4α - 12β = 0`. -/
theorem det_one_pi1 {α β : ℤ}
    (hdet : ∀ t : ℝ, (pi1 (u1ParamGen α β t)).det = 1) :
    -4 * α + -12 * β = 0 := by
  have h := hdet 1
  rw [pi1_det_gen] at h
  simp only [Complex.ofReal_one, one_mul] at h
  exact exp_int_mul_I_eq_one h

/-- pi1 carries the common weight vector, along
`(3, -1)`. -/
theorem weightAt_pi1_common : weightAt pi1 commonWeightVector := by
  refine ⟨3, -1, by decide, ?_, ?_⟩
  · intro t
    have h0 : (-4 * (3 : ℤ) + -12 * (-1) : ℤ) = 0 := rfl
    rw [pi1_det_gen, h0]
    simp
  · intro t s
    rw [pi1_lifted_exp_gen]
    congr 1
    rw [common_eq_exp]
    push_cast
    ring

/-- pi1 carries the negated common weight vector,
along `(-3, 1)`. -/
theorem weightAt_pi1_neg_common :
    weightAt pi1 (-commonWeightVector) := by
  refine ⟨-3, 1, by decide, ?_, ?_⟩
  · intro t
    have h0 : (-4 * (-3 : ℤ) + -12 * (1 : ℤ) : ℤ) = 0 := rfl
    rw [pi1_det_gen, h0]
    simp
  · intro t s
    rw [pi1_lifted_exp_gen]
    congr 1
    rw [Pi.neg_apply, common_eq_exp]
    push_cast
    ring

/-- **The pi1 fiber is exactly
`{commonWeightVector, -commonWeightVector}`.** -/
theorem fiber_pi1 {v : Fin 32 → ℤ} (hv : weightAt pi1 v) :
    v = commonWeightVector ∨ v = -commonWeightVector := by
  obtain ⟨α, β, hgcd, hdet, hlift⟩ := hv
  have hlin := det_one_pi1 hdet
  rcases dir_of_det_shape_4312 hgcd hlin with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · left
    funext s
    have hchar : ∀ t : ℝ,
        Complex.exp ((v s : ℂ) * (t : ℂ) * Complex.I)
          = Complex.exp ((commonWeightVector s : ℂ) * (t : ℂ)
            * Complex.I) := by
      intro t
      have h_eq : Complex.exp ((v s : ℂ) * (t : ℂ) * Complex.I)
          = Complex.exp ((((pi1AVal s.val
              + pi1AVal (partner s).val) * 3
              + (pi1BVal s.val + pi1BVal (partner s).val) * (-1)
              : ℤ) : ℂ) * ((t : ℂ) * Complex.I)) := by
        rw [← hlift t s]
        exact pi1_lifted_exp_gen 3 (-1) t s
      rw [h_eq]
      congr 1
      rw [common_eq_exp]
      push_cast
      ring
    exact char_eq_of_forall hchar
  · right
    funext s
    have hchar : ∀ t : ℝ,
        Complex.exp ((v s : ℂ) * (t : ℂ) * Complex.I)
          = Complex.exp ((((-commonWeightVector) s : ℤ) : ℂ)
            * (t : ℂ) * Complex.I) := by
      intro t
      have h_eq : Complex.exp ((v s : ℂ) * (t : ℂ) * Complex.I)
          = Complex.exp ((((pi1AVal s.val
              + pi1AVal (partner s).val) * (-3)
              + (pi1BVal s.val + pi1BVal (partner s).val) * 1
              : ℤ) : ℂ) * ((t : ℂ) * Complex.I)) := by
        rw [← hlift t s]
        exact pi1_lifted_exp_gen (-3) 1 t s
      rw [h_eq]
      congr 1
      rw [Pi.neg_apply, common_eq_exp]
      push_cast
      ring
    exact char_eq_of_forall hchar

/-! ## §9. The piFlip fiber -/

/-- piFlip along the family is diagonal: pi1's
diagonal with the `s8` entry conjugated. -/
theorem piFlip_u1ParamGen_diagonal (α β : ℤ) (t : ℝ) :
    ThetLogos.HyperchargeForcing.piFlip (u1ParamGen α β t)
      = Matrix.diagonal (Function.update
          (pi1Diag (Complex.exp ((α : ℂ) * ((t : ℂ) * Complex.I)))
            (Complex.exp ((β : ℂ) * ((t : ℂ) * Complex.I)))) s8
          (star (Complex.exp ((α : ℂ) * ((t : ℂ) * Complex.I))))) := by
  have hU : u1ParamGen α β t
      = ⟨Complex.exp ((α : ℂ) * ((t : ℂ) * Complex.I)), 1,
        Complex.exp ((β : ℂ) * ((t : ℂ) * Complex.I))
          • (1 : Matrix I3 I3 ℂ)⟩ := rfl
  rw [hU]
  unfold ThetLogos.HyperchargeForcing.piFlip
  rw [pi1_eq_diagonal, diagonal_add_single_diag]
  congr 1
  funext i
  by_cases hi : i = s8
  · subst hi
    rw [Function.update_self, Function.update_self]
    have hd : pi1Diag (Complex.exp ((α : ℂ) * ((t : ℂ) * Complex.I)))
        (Complex.exp ((β : ℂ) * ((t : ℂ) * Complex.I))) s8
        = Complex.exp ((α : ℂ) * ((t : ℂ) * Complex.I)) :=
      pi1DiagVal_nuR _ _
    rw [hd]
    show Complex.exp ((α : ℂ) * ((t : ℂ) * Complex.I))
        + (star (Complex.exp ((α : ℂ) * ((t : ℂ) * Complex.I)))
          - Complex.exp ((α : ℂ) * ((t : ℂ) * Complex.I)))
      = star (Complex.exp ((α : ℂ) * ((t : ℂ) * Complex.I)))
    ring
  · rw [Function.update_of_ne hi, Function.update_of_ne hi]

/-- The piFlip diagonal in exponential form. -/
theorem flipDiag_exp (α β : ℤ) (t : ℝ) (s : Fin 32) :
    Function.update
        (pi1Diag (Complex.exp ((α : ℂ) * ((t : ℂ) * Complex.I)))
          (Complex.exp ((β : ℂ) * ((t : ℂ) * Complex.I)))) s8
        (star (Complex.exp ((α : ℂ) * ((t : ℂ) * Complex.I)))) s
      = Complex.exp (((sbFlipA s * α + pi1BVal s.val * β : ℤ) : ℂ)
        * ((t : ℂ) * Complex.I)) := by
  by_cases hs : s = s8
  · subst hs
    rw [Function.update_self, star_exp_int]
    have hA : sbFlipA s8 = -1 := by decide
    have hB : pi1BVal (s8).val = 0 := by decide
    congr 1
    rw [hA, hB]
    push_cast
    ring
  · rw [Function.update_of_ne hs, pi1Diag_exp_gen]
    have hA : sbFlipA s = pi1AVal s.val := by
      simp [sbFlipA, sbFlipSign, hs]
    congr 1
    rw [hA]

/-- piFlip's lifted entry in exponential form. -/
theorem piFlip_lifted_exp (α β : ℤ) (t : ℝ) (s : Fin 32) :
    (ThetLogos.HyperchargeForcing.piFlip (u1ParamGen α β t)
        * piOp (ThetLogos.HyperchargeForcing.piFlip
          (u1ParamGen α β t))) s s
      = Complex.exp ((((sbFlipA s + sbFlipA (partner s)) * α
          + (pi1BVal s.val + pi1BVal (partner s).val) * β : ℤ) : ℂ)
        * ((t : ℂ) * Complex.I)) := by
  rw [piFlip_u1ParamGen_diagonal, diagonal_lifted_entry,
    flipDiag_exp, flipDiag_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- piFlip's determinant along the family:
`exp ((-6α - 12β) · t · i)` — the seat-8 flip moves
the A-sum from `-4` to `-6`. -/
theorem piFlip_det_gen (α β : ℤ) (t : ℝ) :
    (ThetLogos.HyperchargeForcing.piFlip (u1ParamGen α β t)).det
      = Complex.exp (((-6 * α + -12 * β : ℤ) : ℂ)
        * ((t : ℂ) * Complex.I)) := by
  have hsum : ∑ s : Fin 32, (sbFlipA s * α + pi1BVal s.val * β)
      = -6 * α + -12 * β := by
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul,
      sum_flipA, sum_B]
  rw [piFlip_u1ParamGen_diagonal, Matrix.det_diagonal,
    Finset.prod_congr rfl (fun s _ => flipDiag_exp α β t s),
    ← Complex.exp_sum, ← Finset.sum_mul, ← Int.cast_sum, hsum]

/-- Determinant pin for piFlip. -/
theorem det_one_piFlip {α β : ℤ}
    (hdet : ∀ t : ℝ,
      (ThetLogos.HyperchargeForcing.piFlip (u1ParamGen α β t)).det
        = 1) :
    -6 * α + -12 * β = 0 := by
  have h := hdet 1
  rw [piFlip_det_gen] at h
  simp only [Complex.ofReal_one, one_mul] at h
  exact exp_int_mul_I_eq_one h

/-- piFlip carries its flip weight vector, along
`(-2, 1)`. -/
theorem weightAt_piFlip_flipWeight :
    weightAt ThetLogos.HyperchargeForcing.piFlip sbFlipWeight := by
  refine ⟨-2, 1, by decide, ?_, ?_⟩
  · intro t
    have h0 : (-6 * (-2 : ℤ) + -12 * (1 : ℤ) : ℤ) = 0 := rfl
    rw [piFlip_det_gen, h0]
    simp
  · intro t s
    rw [piFlip_lifted_exp]
    congr 1
    have hW : sbFlipWeight s
        = (sbFlipA s + sbFlipA (partner s)) * (-2)
          + (pi1BVal s.val + pi1BVal (partner s).val) * 1 := rfl
    rw [hW]
    push_cast
    ring

/-- piFlip carries the negated flip weight vector,
along `(2, -1)`. -/
theorem weightAt_piFlip_neg_flipWeight :
    weightAt ThetLogos.HyperchargeForcing.piFlip (-sbFlipWeight) := by
  refine ⟨2, -1, by decide, ?_, ?_⟩
  · intro t
    have h0 : (-6 * (2 : ℤ) + -12 * (-1 : ℤ) : ℤ) = 0 := rfl
    rw [piFlip_det_gen, h0]
    simp
  · intro t s
    rw [piFlip_lifted_exp]
    congr 1
    have hW : sbFlipWeight s
        = (sbFlipA s + sbFlipA (partner s)) * (-2)
          + (pi1BVal s.val + pi1BVal (partner s).val) * 1 := rfl
    rw [Pi.neg_apply, hW]
    push_cast
    ring

/-- **The piFlip fiber is exactly
`{sbFlipWeight, -sbFlipWeight}`.** -/
theorem fiber_piFlip {v : Fin 32 → ℤ}
    (hv : weightAt ThetLogos.HyperchargeForcing.piFlip v) :
    v = sbFlipWeight ∨ v = -sbFlipWeight := by
  obtain ⟨α, β, hgcd, hdet, hlift⟩ := hv
  have hlin := det_one_piFlip hdet
  rcases dir_of_det_shape_612 hgcd hlin with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · left
    funext s
    have hchar : ∀ t : ℝ,
        Complex.exp ((v s : ℂ) * (t : ℂ) * Complex.I)
          = Complex.exp ((sbFlipWeight s : ℂ) * (t : ℂ)
            * Complex.I) := by
      intro t
      have h_eq : Complex.exp ((v s : ℂ) * (t : ℂ) * Complex.I)
          = Complex.exp ((((sbFlipA s + sbFlipA (partner s)) * (-2)
              + (pi1BVal s.val + pi1BVal (partner s).val) * 1
              : ℤ) : ℂ) * ((t : ℂ) * Complex.I)) := by
        rw [← hlift t s]
        exact piFlip_lifted_exp (-2) 1 t s
      rw [h_eq]
      congr 1
      have hW : sbFlipWeight s
          = (sbFlipA s + sbFlipA (partner s)) * (-2)
            + (pi1BVal s.val + pi1BVal (partner s).val) * 1 := rfl
      rw [hW]
      push_cast
      ring
    exact char_eq_of_forall hchar
  · right
    funext s
    have hchar : ∀ t : ℝ,
        Complex.exp ((v s : ℂ) * (t : ℂ) * Complex.I)
          = Complex.exp ((((-sbFlipWeight) s : ℤ) : ℂ)
            * (t : ℂ) * Complex.I) := by
      intro t
      have h_eq : Complex.exp ((v s : ℂ) * (t : ℂ) * Complex.I)
          = Complex.exp ((((sbFlipA s + sbFlipA (partner s)) * 2
              + (pi1BVal s.val + pi1BVal (partner s).val) * (-1)
              : ℤ) : ℂ) * ((t : ℂ) * Complex.I)) := by
        rw [← hlift t s]
        exact piFlip_lifted_exp 2 (-1) t s
      rw [h_eq]
      congr 1
      have hW : sbFlipWeight s
          = (sbFlipA s + sbFlipA (partner s)) * (-2)
            + (pi1BVal s.val + pi1BVal (partner s).val) * 1 := rfl
      rw [Pi.neg_apply, hW]
      push_cast
      ring
    exact char_eq_of_forall hchar

/-! ## §10. The piEFlip fiber -/

/-- piEFlip along the family is diagonal: pi1's
diagonal with the `s9` entry un-conjugated. -/
theorem piEFlip_u1ParamGen_diagonal (α β : ℤ) (t : ℝ) :
    piEFlip (u1ParamGen α β t)
      = Matrix.diagonal (Function.update
          (pi1Diag (Complex.exp ((α : ℂ) * ((t : ℂ) * Complex.I)))
            (Complex.exp ((β : ℂ) * ((t : ℂ) * Complex.I)))) s9
          (Complex.exp ((α : ℂ) * ((t : ℂ) * Complex.I)))) := by
  have hU : u1ParamGen α β t
      = ⟨Complex.exp ((α : ℂ) * ((t : ℂ) * Complex.I)), 1,
        Complex.exp ((β : ℂ) * ((t : ℂ) * Complex.I))
          • (1 : Matrix I3 I3 ℂ)⟩ := rfl
  rw [hU]
  rw [piEFlip_unfold, pi1_eq_diagonal, diagonal_add_single_diag]
  congr 1
  funext i
  by_cases hi : i = s9
  · subst hi
    rw [Function.update_self, Function.update_self]
    have hd : pi1Diag (Complex.exp ((α : ℂ) * ((t : ℂ) * Complex.I)))
        (Complex.exp ((β : ℂ) * ((t : ℂ) * Complex.I))) s9
        = star (Complex.exp ((α : ℂ) * ((t : ℂ) * Complex.I))) :=
      pi1DiagVal_eR _ _
    rw [hd]
    show star (Complex.exp ((α : ℂ) * ((t : ℂ) * Complex.I)))
        + (Complex.exp ((α : ℂ) * ((t : ℂ) * Complex.I))
          - star (Complex.exp ((α : ℂ) * ((t : ℂ) * Complex.I))))
      = Complex.exp ((α : ℂ) * ((t : ℂ) * Complex.I))
    ring
  · rw [Function.update_of_ne hi, Function.update_of_ne hi]

/-- The piEFlip diagonal in exponential form. -/
theorem eflipDiag_exp (α β : ℤ) (t : ℝ) (s : Fin 32) :
    Function.update
        (pi1Diag (Complex.exp ((α : ℂ) * ((t : ℂ) * Complex.I)))
          (Complex.exp ((β : ℂ) * ((t : ℂ) * Complex.I)))) s9
        (Complex.exp ((α : ℂ) * ((t : ℂ) * Complex.I))) s
      = Complex.exp (((sbEFlipA s * α + pi1BVal s.val * β : ℤ) : ℂ)
        * ((t : ℂ) * Complex.I)) := by
  by_cases hs : s = s9
  · subst hs
    rw [Function.update_self]
    have hA : sbEFlipA s9 = 1 := by decide
    have hB : pi1BVal (s9).val = 0 := by decide
    congr 1
    rw [hA, hB]
    push_cast
    ring
  · rw [Function.update_of_ne hs, pi1Diag_exp_gen]
    have hA : sbEFlipA s = pi1AVal s.val := by
      simp [sbEFlipA, sbEFlipSign, hs]
    congr 1
    rw [hA]

/-- piEFlip's lifted entry in exponential form. -/
theorem piEFlip_lifted_exp (α β : ℤ) (t : ℝ) (s : Fin 32) :
    (piEFlip (u1ParamGen α β t)
        * piOp (piEFlip (u1ParamGen α β t))) s s
      = Complex.exp ((((sbEFlipA s + sbEFlipA (partner s)) * α
          + (pi1BVal s.val + pi1BVal (partner s).val) * β : ℤ) : ℂ)
        * ((t : ℂ) * Complex.I)) := by
  rw [piEFlip_u1ParamGen_diagonal, diagonal_lifted_entry,
    eflipDiag_exp, eflipDiag_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- piEFlip's determinant along the family:
`exp ((-2α - 12β) · t · i)` — the seat-9 un-flip moves
the A-sum from `-4` to `-2`. -/
theorem piEFlip_det_gen (α β : ℤ) (t : ℝ) :
    (piEFlip (u1ParamGen α β t)).det
      = Complex.exp (((-2 * α + -12 * β : ℤ) : ℂ)
        * ((t : ℂ) * Complex.I)) := by
  have hsum : ∑ s : Fin 32, (sbEFlipA s * α + pi1BVal s.val * β)
      = -2 * α + -12 * β := by
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul,
      sum_eflipA, sum_B]
  rw [piEFlip_u1ParamGen_diagonal, Matrix.det_diagonal,
    Finset.prod_congr rfl (fun s _ => eflipDiag_exp α β t s),
    ← Complex.exp_sum, ← Finset.sum_mul, ← Int.cast_sum, hsum]

/-- Determinant pin for piEFlip. -/
theorem det_one_piEFlip {α β : ℤ}
    (hdet : ∀ t : ℝ, (piEFlip (u1ParamGen α β t)).det = 1) :
    -2 * α + -12 * β = 0 := by
  have h := hdet 1
  rw [piEFlip_det_gen] at h
  simp only [Complex.ofReal_one, one_mul] at h
  exact exp_int_mul_I_eq_one h

/-- piEFlip carries its flip weight vector, along
`(-6, 1)`. -/
theorem weightAt_piEFlip_eflipWeight :
    weightAt piEFlip sbEFlipWeight := by
  refine ⟨-6, 1, by decide, ?_, ?_⟩
  · intro t
    have h0 : (-2 * (-6 : ℤ) + -12 * (1 : ℤ) : ℤ) = 0 := rfl
    rw [piEFlip_det_gen, h0]
    simp
  · intro t s
    rw [piEFlip_lifted_exp]
    congr 1
    have hW : sbEFlipWeight s
        = (sbEFlipA s + sbEFlipA (partner s)) * (-6)
          + (pi1BVal s.val + pi1BVal (partner s).val) * 1 := rfl
    rw [hW]
    push_cast
    ring

/-- piEFlip carries the negated flip weight vector,
along `(6, -1)`. -/
theorem weightAt_piEFlip_neg_eflipWeight :
    weightAt piEFlip (-sbEFlipWeight) := by
  refine ⟨6, -1, by decide, ?_, ?_⟩
  · intro t
    have h0 : (-2 * (6 : ℤ) + -12 * (-1 : ℤ) : ℤ) = 0 := rfl
    rw [piEFlip_det_gen, h0]
    simp
  · intro t s
    rw [piEFlip_lifted_exp]
    congr 1
    have hW : sbEFlipWeight s
        = (sbEFlipA s + sbEFlipA (partner s)) * (-6)
          + (pi1BVal s.val + pi1BVal (partner s).val) * 1 := rfl
    rw [Pi.neg_apply, hW]
    push_cast
    ring

/-- **The piEFlip fiber is exactly
`{sbEFlipWeight, -sbEFlipWeight}`.** -/
theorem fiber_piEFlip {v : Fin 32 → ℤ}
    (hv : weightAt piEFlip v) :
    v = sbEFlipWeight ∨ v = -sbEFlipWeight := by
  obtain ⟨α, β, hgcd, hdet, hlift⟩ := hv
  have hlin := det_one_piEFlip hdet
  rcases dir_of_det_shape_212 hgcd hlin with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · left
    funext s
    have hchar : ∀ t : ℝ,
        Complex.exp ((v s : ℂ) * (t : ℂ) * Complex.I)
          = Complex.exp ((sbEFlipWeight s : ℂ) * (t : ℂ)
            * Complex.I) := by
      intro t
      have h_eq : Complex.exp ((v s : ℂ) * (t : ℂ) * Complex.I)
          = Complex.exp ((((sbEFlipA s + sbEFlipA (partner s)) * (-6)
              + (pi1BVal s.val + pi1BVal (partner s).val) * 1
              : ℤ) : ℂ) * ((t : ℂ) * Complex.I)) := by
        rw [← hlift t s]
        exact piEFlip_lifted_exp (-6) 1 t s
      rw [h_eq]
      congr 1
      have hW : sbEFlipWeight s
          = (sbEFlipA s + sbEFlipA (partner s)) * (-6)
            + (pi1BVal s.val + pi1BVal (partner s).val) * 1 := rfl
      rw [hW]
      push_cast
      ring
    exact char_eq_of_forall hchar
  · right
    funext s
    have hchar : ∀ t : ℝ,
        Complex.exp ((v s : ℂ) * (t : ℂ) * Complex.I)
          = Complex.exp ((((-sbEFlipWeight) s : ℤ) : ℂ)
            * (t : ℂ) * Complex.I) := by
      intro t
      have h_eq : Complex.exp ((v s : ℂ) * (t : ℂ) * Complex.I)
          = Complex.exp ((((sbEFlipA s + sbEFlipA (partner s)) * 6
              + (pi1BVal s.val + pi1BVal (partner s).val) * (-1)
              : ℤ) : ℂ) * ((t : ℂ) * Complex.I)) := by
        rw [← hlift t s]
        exact piEFlip_lifted_exp 6 (-1) t s
      rw [h_eq]
      congr 1
      have hW : sbEFlipWeight s
          = (sbEFlipA s + sbEFlipA (partner s)) * (-6)
            + (pi1BVal s.val + pi1BVal (partner s).val) * 1 := rfl
      rw [Pi.neg_apply, hW]
      push_cast
      ring
    exact char_eq_of_forall hchar

/-! ## §11. The orbit fiber

Seat-distinctness facts (all closed or `Fin 3`-case
facts, discharged by `decide` after `fin_cases`), the
characterization of the toggled seat set at each seat
shape, and the additive-singles normal form of
`orbitRep`. -/

theorem uSeat_ne_s8 (c : Fin 3) : uSeat c ≠ s8 := by
  fin_cases c <;> decide

theorem uSeat_ne_s9 (c : Fin 3) : uSeat c ≠ s9 := by
  fin_cases c <;> decide

theorem dSeat_ne_s8 (c : Fin 3) : dSeat c ≠ s8 := by
  fin_cases c <;> decide

theorem dSeat_ne_s9 (c : Fin 3) : dSeat c ≠ s9 := by
  fin_cases c <;> decide

theorem s8_ne_uSeat (c : Fin 3) : s8 ≠ uSeat c := by
  fin_cases c <;> decide

theorem s8_ne_dSeat (c : Fin 3) : s8 ≠ dSeat c := by
  fin_cases c <;> decide

theorem s9_ne_uSeat (c : Fin 3) : s9 ≠ uSeat c := by
  fin_cases c <;> decide

theorem s9_ne_dSeat (c : Fin 3) : s9 ≠ dSeat c := by
  fin_cases c <;> decide

theorem uSeat_ne_dSeat (c c' : Fin 3) : uSeat c ≠ dSeat c' := by
  fin_cases c <;> fin_cases c' <;> decide

theorem dSeat_ne_uSeat (c c' : Fin 3) : dSeat c ≠ uSeat c' := by
  fin_cases c <;> fin_cases c' <;> decide

theorem uSeat_inj {c c' : Fin 3} (h : uSeat c = uSeat c') : c = c' := by
  fin_cases c <;> fin_cases c' <;> revert h <;> decide

theorem dSeat_inj {c c' : Fin 3} (h : dSeat c = dSeat c') : c = c' := by
  fin_cases c <;> fin_cases c' <;> revert h <;> decide

theorem s8_ne_s9 : s8 ≠ s9 := by decide

/-- At `s8`, the toggled condition is exactly bit 0. -/
theorem sbToggled_s8 (b : Fin 4 → Bool) :
    sbToggled b s8 ↔ b 0 = true := by
  constructor
  · rintro (⟨h, -⟩ | ⟨c, -, h⟩)
    · exact h
    · rcases h with h | h
      · exact absurd h (s8_ne_uSeat c)
      · exact absurd h (s8_ne_dSeat c)
  · intro h
    exact Or.inl ⟨h, Or.inl rfl⟩

/-- At `s9`, the toggled condition is exactly bit 0. -/
theorem sbToggled_s9 (b : Fin 4 → Bool) :
    sbToggled b s9 ↔ b 0 = true := by
  constructor
  · rintro (⟨h, -⟩ | ⟨c, -, h⟩)
    · exact h
    · rcases h with h | h
      · exact absurd h (s9_ne_uSeat c)
      · exact absurd h (s9_ne_dSeat c)
  · intro h
    exact Or.inl ⟨h, Or.inr rfl⟩

/-- At `uSeat c`, the toggled condition is exactly
bit `c + 1`. -/
theorem sbToggled_uSeat (b : Fin 4 → Bool) (c : Fin 3) :
    sbToggled b (uSeat c) ↔ b (swapIdx c) = true := by
  constructor
  · rintro (⟨-, h⟩ | ⟨c', hb, h⟩)
    · rcases h with h | h
      · exact absurd h (uSeat_ne_s8 c)
      · exact absurd h (uSeat_ne_s9 c)
    · rcases h with h | h
      · rwa [← uSeat_inj h] at hb
      · exact absurd h (uSeat_ne_dSeat c c')
  · intro h
    exact Or.inr ⟨c, h, Or.inl rfl⟩

/-- At `dSeat c`, the toggled condition is exactly
bit `c + 1`. -/
theorem sbToggled_dSeat (b : Fin 4 → Bool) (c : Fin 3) :
    sbToggled b (dSeat c) ↔ b (swapIdx c) = true := by
  constructor
  · rintro (⟨-, h⟩ | ⟨c', hb, h⟩)
    · rcases h with h | h
      · exact absurd h (dSeat_ne_s8 c)
      · exact absurd h (dSeat_ne_s9 c)
    · rcases h with h | h
      · exact absurd h (dSeat_ne_uSeat c c')
      · rwa [← dSeat_inj h] at hb
  · intro h
    exact Or.inr ⟨c, h, Or.inr rfl⟩

/-- A `single` with an if-coefficient is the if of the
`single`. -/
theorem single_ite (s : Fin 32) (x : ℂ) (c : Bool) :
    Matrix.single s s (if c then x else 0)
      = if c then Matrix.single s s x else 0 := by
  split_ifs with h
  · rfl
  · ext i j
    simp [Matrix.single_apply]

/-- Two if-matrices with the same condition add
inside the if. -/
theorem ite_add {c : Bool} {P Q : Matrix (Fin 32) (Fin 32) ℂ} :
    (if c then P else 0) + (if c then Q else 0)
      = if c then P + Q else 0 := by
  by_cases hc : c = true <;> simp [hc]

/-- The `orbitCorrD` correction, in ite-single form. -/
theorem ite_orbitCorrD (b : Fin 4 → Bool) (a : AF) :
    (if b 0 then orbitCorrD a else 0)
      = Matrix.single s8 s8 (if b 0 then star a.u1 - a.u1 else 0)
        + Matrix.single s9 s9 (if b 0 then a.u1 - star a.u1 else 0) := by
  simp only [orbitCorrD]
  rw [single_ite, single_ite, ← ite_add]

/-- The `orbitCorrS` corrections, in ite-single form. -/
theorem ite_orbitCorrS (b : Fin 4 → Bool) (k : Fin 4) (c : Fin 3)
    (a : AF) :
    (if b k then orbitCorrS c a else 0)
      = Matrix.single (uSeat c) (uSeat c)
          (if b k then star a.u1 - a.u1 else 0)
        + Matrix.single (dSeat c) (dSeat c)
          (if b k then a.u1 - star a.u1 else 0) := by
  simp only [orbitCorrS]
  rw [single_ite, single_ite, ← ite_add]

/-- **The additive-singles normal form of
`orbitRep`**: pi1 plus eight ite-coefficient singles
at the eight toggle seats. -/
theorem orbitRep_eq_singles (b : Fin 4 → Bool) (a : AF) :
    orbitRep b a = pi1 a
      + Matrix.single s8 s8 (if b 0 then star a.u1 - a.u1 else 0)
      + Matrix.single s9 s9 (if b 0 then a.u1 - star a.u1 else 0)
      + Matrix.single (uSeat 0) (uSeat 0)
          (if b 1 then star a.u1 - a.u1 else 0)
      + Matrix.single (dSeat 0) (dSeat 0)
          (if b 1 then a.u1 - star a.u1 else 0)
      + Matrix.single (uSeat 1) (uSeat 1)
          (if b 2 then star a.u1 - a.u1 else 0)
      + Matrix.single (dSeat 1) (dSeat 1)
          (if b 2 then a.u1 - star a.u1 else 0)
      + Matrix.single (uSeat 2) (uSeat 2)
          (if b 3 then star a.u1 - a.u1 else 0)
      + Matrix.single (dSeat 2) (dSeat 2)
          (if b 3 then a.u1 - star a.u1 else 0) := by
  unfold orbitRep
  rw [ite_orbitCorrD, ite_orbitCorrS b 1 0, ite_orbitCorrS b 2 1,
    ite_orbitCorrS b 3 2]
  abel

/-- **The orbit diagonal**: pi1's diagonal entry,
conjugated at exactly the toggled seats — `lam` at
the seats whose pi1 entry is `star lam` (`s9` and
the `dSeat`s), `star lam` at the rest of the toggled
seats. -/
def sbOrbDiag (b : Fin 4 → Bool) (lam μ : ℂ) : Fin 32 → ℂ :=
  fun s => if sbToggled b s
    then (if s = s9 ∨ (∃ c : Fin 3, s = dSeat c)
      then lam else star lam)
    else pi1Diag lam μ s

/-- The orbit diagonal at `s8`: bit 0 decides
between `star lam` (toggled) and pi1's `lam`. -/
theorem sbOrbDiag_s8 (b : Fin 4 → Bool) (lam μ : ℂ) :
    sbOrbDiag b lam μ s8
      = if b 0 = true then star lam else lam := by
  have hinner : ¬ (s8 = s9 ∨ ∃ c : Fin 3, s8 = dSeat c) := by
    rintro (h | ⟨c, h⟩)
    · exact s8_ne_s9 h
    · exact s8_ne_dSeat c h
  by_cases hb : b 0 = true
  · unfold sbOrbDiag
    rw [if_pos ((sbToggled_s8 b).mpr hb), if_neg hinner, if_pos hb]
  · unfold sbOrbDiag
    rw [if_neg (fun h => hb ((sbToggled_s8 b).mp h)),
      show pi1Diag lam μ s8 = lam from pi1DiagVal_nuR lam μ,
      if_neg hb]

/-- The orbit diagonal at `s9`: bit 0 decides
between `lam` (toggled) and pi1's `star lam`. -/
theorem sbOrbDiag_s9 (b : Fin 4 → Bool) (lam μ : ℂ) :
    sbOrbDiag b lam μ s9
      = if b 0 = true then lam else star lam := by
  by_cases hb : b 0 = true
  · unfold sbOrbDiag
    rw [if_pos ((sbToggled_s9 b).mpr hb),
      if_pos (show (s9 = s9 ∨ ∃ c : Fin 3, s9 = dSeat c)
        from Or.inl rfl), if_pos hb]
  · unfold sbOrbDiag
    rw [if_neg (fun h => hb ((sbToggled_s9 b).mp h)),
      show pi1Diag lam μ s9 = star lam from pi1DiagVal_eR lam μ,
      if_neg hb]

/-- The orbit diagonal at `uSeat c`: bit `c + 1`
decides between `star lam` (toggled) and pi1's
`lam`. -/
theorem sbOrbDiag_uSeat (b : Fin 4 → Bool) (lam μ : ℂ)
    (c : Fin 3) :
    sbOrbDiag b lam μ (uSeat c)
      = if b (swapIdx c) = true then star lam else lam := by
  have hinner : ¬ (uSeat c = s9 ∨ ∃ c' : Fin 3,
      uSeat c = dSeat c') := by
    rintro (h | ⟨c', h⟩)
    · exact uSeat_ne_s9 c h
    · exact uSeat_ne_dSeat c c' h
  by_cases hb : b (swapIdx c) = true
  · unfold sbOrbDiag
    rw [if_pos ((sbToggled_uSeat b c).mpr hb), if_neg hinner,
      if_pos hb]
  · unfold sbOrbDiag
    rw [if_neg (fun h => hb ((sbToggled_uSeat b c).mp h)),
      pi1Diag_uSeat, if_neg hb]

/-- The orbit diagonal at `dSeat c`: bit `c + 1`
decides between `lam` (toggled) and pi1's
`star lam`. -/
theorem sbOrbDiag_dSeat (b : Fin 4 → Bool) (lam μ : ℂ)
    (c : Fin 3) :
    sbOrbDiag b lam μ (dSeat c)
      = if b (swapIdx c) = true then lam else star lam := by
  by_cases hb : b (swapIdx c) = true
  · unfold sbOrbDiag
    rw [if_pos ((sbToggled_dSeat b c).mpr hb),
      if_pos (show (dSeat c = s9 ∨ ∃ c' : Fin 3, dSeat c = dSeat c')
        from Or.inr ⟨c, rfl⟩), if_pos hb]
  · unfold sbOrbDiag
    rw [if_neg (fun h => hb ((sbToggled_dSeat b c).mp h)),
      pi1Diag_dSeat, if_neg hb]

/-- **The diagonal entry of `orbitRep b` along the
family**: pi1's diagonal with exactly the toggled
seats conjugated — read off the singles normal form
seat by seat. -/
theorem orbitRep_diag_u1ParamGen (b : Fin 4 → Bool) (α β : ℤ)
    (t : ℝ) (s : Fin 32) :
    orbitRep b (u1ParamGen α β t) s s
      = sbOrbDiag b (Complex.exp ((α : ℂ) * ((t : ℂ) * Complex.I)))
          (Complex.exp ((β : ℂ) * ((t : ℂ) * Complex.I))) s := by
  have hU : u1ParamGen α β t
      = ⟨Complex.exp ((α : ℂ) * ((t : ℂ) * Complex.I)), 1,
        Complex.exp ((β : ℂ) * ((t : ℂ) * Complex.I))
          • (1 : Matrix I3 I3 ℂ)⟩ := rfl
  have hu1 : (u1ParamGen α β t).u1
      = Complex.exp ((α : ℂ) * ((t : ℂ) * Complex.I)) := rfl
  rw [orbitRep_eq_singles, hu1]
  simp only [Matrix.add_apply, Matrix.single_apply, and_self]
  rw [hU, pi1_eq_diagonal, Matrix.diagonal_apply_eq]
  by_cases hs8 : s = s8
  · subst hs8
    have hinner : ¬ (s8 = s9 ∨ ∃ c : Fin 3, s8 = dSeat c) := by
      rintro (h | ⟨c, h⟩)
      · exact s8_ne_s9 h
      · exact s8_ne_dSeat c h
    by_cases hb : b 0 = true
    · rw [sbOrbDiag_s8]
      simp only [hb, eq_self_iff_true, ite_true, ite_false, Bool.false_eq_true_eq_False,
        add_zero, show ¬ (s9 = s8) from s8_ne_s9.symm,
        uSeat_ne_s8, dSeat_ne_s8]
      rw [show pi1Diag (Complex.exp ((α : ℂ) * ((t : ℂ)
            * Complex.I)))
          (Complex.exp ((β : ℂ) * ((t : ℂ) * Complex.I))) s8
          = Complex.exp ((α : ℂ) * ((t : ℂ) * Complex.I))
        from pi1DiagVal_nuR _ _]
      ring
    · rw [sbOrbDiag_s8]
      simp only [if_neg hb, eq_self_iff_true, ite_true, ite_false, Bool.false_eq_true_eq_False,
        add_zero, show ¬ (s9 = s8) from s8_ne_s9.symm,
        uSeat_ne_s8, dSeat_ne_s8]
      rw [show pi1Diag (Complex.exp ((α : ℂ) * ((t : ℂ)
            * Complex.I)))
          (Complex.exp ((β : ℂ) * ((t : ℂ) * Complex.I))) s8
          = Complex.exp ((α : ℂ) * ((t : ℂ) * Complex.I))
        from pi1DiagVal_nuR _ _]
  by_cases hs9 : s = s9
  · subst hs9
    by_cases hb : b 0 = true
    · rw [sbOrbDiag_s9]
      simp only [hb, eq_self_iff_true, ite_true, ite_false, Bool.false_eq_true_eq_False,
        add_zero, show ¬ (s8 = s9) from s8_ne_s9,
        uSeat_ne_s9, dSeat_ne_s9]
      rw [show pi1Diag (Complex.exp ((α : ℂ) * ((t : ℂ)
            * Complex.I)))
          (Complex.exp ((β : ℂ) * ((t : ℂ) * Complex.I))) s9
          = star (Complex.exp ((α : ℂ) * ((t : ℂ) * Complex.I)))
        from pi1DiagVal_eR _ _]
      ring
    · rw [sbOrbDiag_s9]
      simp only [if_neg hb, eq_self_iff_true, ite_true, ite_false, Bool.false_eq_true_eq_False,
        add_zero, show ¬ (s8 = s9) from s8_ne_s9,
        uSeat_ne_s9, dSeat_ne_s9]
      rw [show pi1Diag (Complex.exp ((α : ℂ) * ((t : ℂ)
            * Complex.I)))
          (Complex.exp ((β : ℂ) * ((t : ℂ) * Complex.I))) s9
          = star (Complex.exp ((α : ℂ) * ((t : ℂ) * Complex.I)))
        from pi1DiagVal_eR _ _]
  by_cases hsU0 : s = uSeat 0
  · subst hsU0
    have hinner : ¬ (uSeat 0 = s9 ∨ ∃ c : Fin 3,
        uSeat 0 = dSeat c) := by
      rintro (h | ⟨c, h⟩)
      · exact uSeat_ne_s9 0 h
      · exact uSeat_ne_dSeat 0 c h
    by_cases hb : b 1 = true
    · rw [sbOrbDiag_uSeat, show (swapIdx 0 : Fin 4) = 1 by decide]
      simp only [hb, eq_self_iff_true, ite_true, ite_false, Bool.false_eq_true_eq_False,
        add_zero, s8_ne_uSeat, s9_ne_uSeat, dSeat_ne_uSeat,
        show ¬ (uSeat 1 = uSeat 0) by decide,
        show ¬ (uSeat 2 = uSeat 0) by decide]
      rw [pi1Diag_uSeat]
      ring
    · rw [sbOrbDiag_uSeat, show (swapIdx 0 : Fin 4) = 1 by decide]
      simp only [if_neg hb, eq_self_iff_true, ite_true, ite_false, Bool.false_eq_true_eq_False,
        add_zero, s8_ne_uSeat, s9_ne_uSeat, dSeat_ne_uSeat,
        show ¬ (uSeat 1 = uSeat 0) by decide,
        show ¬ (uSeat 2 = uSeat 0) by decide]
      rw [pi1Diag_uSeat]
  by_cases hsD0 : s = dSeat 0
  · subst hsD0
    by_cases hb : b 1 = true
    · rw [sbOrbDiag_dSeat, show (swapIdx 0 : Fin 4) = 1 by decide]
      simp only [hb, eq_self_iff_true, ite_true, ite_false, Bool.false_eq_true_eq_False,
        add_zero, s8_ne_dSeat, s9_ne_dSeat, uSeat_ne_dSeat,
        show ¬ (dSeat 1 = dSeat 0) by decide,
        show ¬ (dSeat 2 = dSeat 0) by decide]
      rw [pi1Diag_dSeat]
      ring
    · rw [sbOrbDiag_dSeat, show (swapIdx 0 : Fin 4) = 1 by decide]
      simp only [if_neg hb, eq_self_iff_true, ite_true, ite_false, Bool.false_eq_true_eq_False,
        add_zero, s8_ne_dSeat, s9_ne_dSeat, uSeat_ne_dSeat,
        show ¬ (dSeat 1 = dSeat 0) by decide,
        show ¬ (dSeat 2 = dSeat 0) by decide]
      rw [pi1Diag_dSeat]
  by_cases hsU1 : s = uSeat 1
  · subst hsU1
    have hinner : ¬ (uSeat 1 = s9 ∨ ∃ c : Fin 3,
        uSeat 1 = dSeat c) := by
      rintro (h | ⟨c, h⟩)
      · exact uSeat_ne_s9 1 h
      · exact uSeat_ne_dSeat 1 c h
    by_cases hb : b 2 = true
    · rw [sbOrbDiag_uSeat, show (swapIdx 1 : Fin 4) = 2 by decide]
      simp only [hb, eq_self_iff_true, ite_true, ite_false, Bool.false_eq_true_eq_False,
        add_zero, s8_ne_uSeat, s9_ne_uSeat, dSeat_ne_uSeat,
        show ¬ (uSeat 0 = uSeat 1) by decide,
        show ¬ (uSeat 2 = uSeat 1) by decide]
      rw [pi1Diag_uSeat]
      ring
    · rw [sbOrbDiag_uSeat, show (swapIdx 1 : Fin 4) = 2 by decide]
      simp only [if_neg hb, eq_self_iff_true, ite_true, ite_false, Bool.false_eq_true_eq_False,
        add_zero, s8_ne_uSeat, s9_ne_uSeat, dSeat_ne_uSeat,
        show ¬ (uSeat 0 = uSeat 1) by decide,
        show ¬ (uSeat 2 = uSeat 1) by decide]
      rw [pi1Diag_uSeat]
  by_cases hsD1 : s = dSeat 1
  · subst hsD1
    by_cases hb : b 2 = true
    · rw [sbOrbDiag_dSeat, show (swapIdx 1 : Fin 4) = 2 by decide]
      simp only [hb, eq_self_iff_true, ite_true, ite_false, Bool.false_eq_true_eq_False,
        add_zero, s8_ne_dSeat, s9_ne_dSeat, uSeat_ne_dSeat,
        show ¬ (dSeat 0 = dSeat 1) by decide,
        show ¬ (dSeat 2 = dSeat 1) by decide]
      rw [pi1Diag_dSeat]
      ring
    · rw [sbOrbDiag_dSeat, show (swapIdx 1 : Fin 4) = 2 by decide]
      simp only [if_neg hb, eq_self_iff_true, ite_true, ite_false, Bool.false_eq_true_eq_False,
        add_zero, s8_ne_dSeat, s9_ne_dSeat, uSeat_ne_dSeat,
        show ¬ (dSeat 0 = dSeat 1) by decide,
        show ¬ (dSeat 2 = dSeat 1) by decide]
      rw [pi1Diag_dSeat]
  by_cases hsU2 : s = uSeat 2
  · subst hsU2
    have hinner : ¬ (uSeat 2 = s9 ∨ ∃ c : Fin 3,
        uSeat 2 = dSeat c) := by
      rintro (h | ⟨c, h⟩)
      · exact uSeat_ne_s9 2 h
      · exact uSeat_ne_dSeat 2 c h
    by_cases hb : b 3 = true
    · rw [sbOrbDiag_uSeat, show (swapIdx 2 : Fin 4) = 3 by decide]
      simp only [hb, eq_self_iff_true, ite_true, ite_false, Bool.false_eq_true_eq_False,
        add_zero, s8_ne_uSeat, s9_ne_uSeat, dSeat_ne_uSeat,
        show ¬ (uSeat 0 = uSeat 2) by decide,
        show ¬ (uSeat 1 = uSeat 2) by decide]
      rw [pi1Diag_uSeat]
      ring
    · rw [sbOrbDiag_uSeat, show (swapIdx 2 : Fin 4) = 3 by decide]
      simp only [if_neg hb, eq_self_iff_true, ite_true, ite_false, Bool.false_eq_true_eq_False,
        add_zero, s8_ne_uSeat, s9_ne_uSeat, dSeat_ne_uSeat,
        show ¬ (uSeat 0 = uSeat 2) by decide,
        show ¬ (uSeat 1 = uSeat 2) by decide]
      rw [pi1Diag_uSeat]
  by_cases hsD2 : s = dSeat 2
  · subst hsD2
    by_cases hb : b 3 = true
    · rw [sbOrbDiag_dSeat, show (swapIdx 2 : Fin 4) = 3 by decide]
      simp only [hb, eq_self_iff_true, ite_true, ite_false, Bool.false_eq_true_eq_False,
        add_zero, s8_ne_dSeat, s9_ne_dSeat, uSeat_ne_dSeat,
        show ¬ (dSeat 0 = dSeat 2) by decide,
        show ¬ (dSeat 1 = dSeat 2) by decide]
      rw [pi1Diag_dSeat]
      ring
    · rw [sbOrbDiag_dSeat, show (swapIdx 2 : Fin 4) = 3 by decide]
      simp only [if_neg hb, eq_self_iff_true, ite_true, ite_false, Bool.false_eq_true_eq_False,
        add_zero, s8_ne_dSeat, s9_ne_dSeat, uSeat_ne_dSeat,
        show ¬ (dSeat 0 = dSeat 2) by decide,
        show ¬ (dSeat 1 = dSeat 2) by decide]
      rw [pi1Diag_dSeat]
  · -- the generic seat: nothing is toggled, no single fires
    have hnotog : ¬ sbToggled b s := by
      rintro (⟨-, h⟩ | ⟨c, -, h⟩)
      · rcases h with h | h
        · exact hs8 h
        · exact hs9 h
      · rcases h with h | h
        · fin_cases c
          · exact hsU0 h
          · exact hsU1 h
          · exact hsU2 h
        · fin_cases c
          · exact hsD0 h
          · exact hsD1 h
          · exact hsD2 h
    simp only [sbOrbDiag, if_neg hnotog, add_zero,
      show ¬ (s8 = s) from fun h => hs8 h.symm,
      show ¬ (s9 = s) from fun h => hs9 h.symm,
      show ¬ (uSeat 0 = s) from fun h => hsU0 h.symm,
      show ¬ (dSeat 0 = s) from fun h => hsD0 h.symm,
      show ¬ (uSeat 1 = s) from fun h => hsU1 h.symm,
      show ¬ (dSeat 1 = s) from fun h => hsD1 h.symm,
      show ¬ (uSeat 2 = s) from fun h => hsU2 h.symm,
      show ¬ (dSeat 2 = s) from fun h => hsD2 h.symm,
      ite_false]

/-- **The orbit representation along the family is
the diagonal** `sbOrbDiag`. -/
theorem orbitRep_u1ParamGen_diagonal (b : Fin 4 → Bool) (α β : ℤ)
    (t : ℝ) :
    orbitRep b (u1ParamGen α β t)
      = Matrix.diagonal (sbOrbDiag b
          (Complex.exp ((α : ℂ) * ((t : ℂ) * Complex.I)))
          (Complex.exp ((β : ℂ) * ((t : ℂ) * Complex.I)))) := by
  ext i j
  by_cases hij : i = j
  · subst hij
    rw [orbitRep_diag_u1ParamGen, Matrix.diagonal_apply_eq]
  · rw [Matrix.diagonal_apply_ne _ hij]
    have hU : u1ParamGen α β t
        = ⟨Complex.exp ((α : ℂ) * ((t : ℂ) * Complex.I)), 1,
          Complex.exp ((β : ℂ) * ((t : ℂ) * Complex.I))
            • (1 : Matrix I3 I3 ℂ)⟩ := rfl
    have hu1 : (u1ParamGen α β t).u1
        = Complex.exp ((α : ℂ) * ((t : ℂ) * Complex.I)) := rfl
    have hne : ∀ s : Fin 32, ¬ (s = i ∧ s = j) :=
      fun s h => hij (h.1.symm.trans h.2)
    rw [orbitRep_eq_singles, hu1]
    simp only [Matrix.add_apply]
    rw [hU, pi1_eq_diagonal, Matrix.diagonal_apply_ne _ hij]
    simp only [Matrix.single_apply, hne, ite_false, add_zero]

/-- The orbit diagonal in exponential form: at a
toggled seat the sign flips (`sbOrbA = -A`), and
the B-table vanishes at every toggled seat. -/
theorem orbDiag_exp (b : Fin 4 → Bool) (α β : ℤ) (t : ℝ)
    (s : Fin 32) :
    sbOrbDiag b (Complex.exp ((α : ℂ) * ((t : ℂ) * Complex.I)))
        (Complex.exp ((β : ℂ) * ((t : ℂ) * Complex.I))) s
      = Complex.exp (((sbOrbA b s * α + pi1BVal s.val * β : ℤ) : ℂ)
        * ((t : ℂ) * Complex.I)) := by
  by_cases htog : sbToggled b s
  · rcases htog with ⟨hb, hs⟩ | ⟨c, hb, hs⟩
    · rcases hs with rfl | rfl
      · rw [sbOrbDiag_s8, if_pos hb, star_exp_int]
        have hA : sbOrbA b s8 = -1 := by
          rw [sbOrbA, sbOrbSign, if_pos ((sbToggled_s8 b).mpr hb)]
          decide
        have hB : pi1BVal (s8).val = 0 := by decide
        congr 1
        rw [hA, hB]
        push_cast
        ring
      · rw [sbOrbDiag_s9, if_pos hb]
        have hA : sbOrbA b s9 = 1 := by
          rw [sbOrbA, sbOrbSign, if_pos ((sbToggled_s9 b).mpr hb)]
          decide
        have hB : pi1BVal (s9).val = 0 := by decide
        congr 1
        rw [hA, hB]
        push_cast
        ring
    · rcases hs with rfl | rfl
      · rw [sbOrbDiag_uSeat, if_pos hb, star_exp_int]
        have hA : sbOrbA b (uSeat c) = -1 := by
          rw [sbOrbA, sbOrbSign, if_pos ((sbToggled_uSeat b c).mpr hb)]
          fin_cases c <;> decide
        have hB : pi1BVal (uSeat c).val = 0 := by
          fin_cases c <;> decide
        congr 1
        rw [hA, hB]
        push_cast
        ring
      · rw [sbOrbDiag_dSeat, if_pos hb]
        have hA : sbOrbA b (dSeat c) = 1 := by
          rw [sbOrbA, sbOrbSign, if_pos ((sbToggled_dSeat b c).mpr hb)]
          fin_cases c <;> decide
        have hB : pi1BVal (dSeat c).val = 0 := by
          fin_cases c <;> decide
        congr 1
        rw [hA, hB]
        push_cast
        ring
  · rw [sbOrbDiag, if_neg htog, pi1Diag_exp_gen]
    have hA : sbOrbA b s = pi1AVal s.val := by
      simp only [sbOrbA, sbOrbSign, if_neg htog, one_mul]
    congr 1
    rw [hA]

/-- The orbit lifted entry in exponential form. -/
theorem orbitRep_lifted_exp (b : Fin 4 → Bool) (α β : ℤ) (t : ℝ)
    (s : Fin 32) :
    (orbitRep b (u1ParamGen α β t)
        * piOp (orbitRep b (u1ParamGen α β t))) s s
      = Complex.exp ((((sbOrbA b s + sbOrbA b (partner s)) * α
          + (pi1BVal s.val + pi1BVal (partner s).val) * β : ℤ) : ℂ)
        * ((t : ℂ) * Complex.I)) := by
  rw [orbitRep_u1ParamGen_diagonal, diagonal_lifted_entry,
    orbDiag_exp, orbDiag_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Determinant of the orbit family: the direction
form is pi1's own, `-4α - 12β` — the toggles do not
move the determinant character. -/
theorem orbitRep_det_gen (b : Fin 4 → Bool) (α β : ℤ) (t : ℝ) :
    (orbitRep b (u1ParamGen α β t)).det
      = Complex.exp (((-4 * α + -12 * β : ℤ) : ℂ)
        * ((t : ℂ) * Complex.I)) := by
  have hsum : ∑ s : Fin 32, (sbOrbA b s * α + pi1BVal s.val * β)
      = -4 * α + -12 * β := by
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul,
      sum_orbA, sum_B]
  rw [orbitRep_u1ParamGen_diagonal, Matrix.det_diagonal,
    Finset.prod_congr rfl (fun s _ => orbDiag_exp b α β t s),
    ← Complex.exp_sum, ← Finset.sum_mul, ← Int.cast_sum, hsum]

/-- Determinant pin for the orbit points. -/
theorem det_one_orbitRep (b : Fin 4 → Bool) {α β : ℤ}
    (hdet : ∀ t : ℝ, (orbitRep b (u1ParamGen α β t)).det = 1) :
    -4 * α + -12 * β = 0 := by
  have h := hdet 1
  rw [orbitRep_det_gen] at h
  simp only [Complex.ofReal_one, one_mul] at h
  exact exp_int_mul_I_eq_one h

/-- **The orbit weight at the primitive direction**
`(3, -1)`: every orbit point's fiber contains its
own orbit weight `sbOrbWeight b`. -/
theorem weightAt_orbitRep_orbWeight (b : Fin 4 → Bool) :
    weightAt (orbitRep b) (sbOrbWeight b) := by
  refine ⟨3, -1, by decide, ?_, ?_⟩
  · intro t
    have h0 : (-4 * (3 : ℤ) + -12 * (-1) : ℤ) = 0 := rfl
    rw [orbitRep_det_gen, h0]
    simp
  · intro t s
    rw [orbitRep_lifted_exp]
    congr 1
    have hW : sbOrbWeight b s
        = (sbOrbA b s + sbOrbA b (partner s)) * 3
          + (pi1BVal s.val + pi1BVal (partner s).val) * -1 := rfl
    rw [hW]
    push_cast
    ring

/-- **The orbit weight at the opposite primitive
direction** `(-3, 1)`: the fiber also contains the
negated weight. -/
theorem weightAt_orbitRep_neg_orbWeight (b : Fin 4 → Bool) :
    weightAt (orbitRep b) (-sbOrbWeight b) := by
  refine ⟨-3, 1, by decide, ?_, ?_⟩
  · intro t
    have h0 : (-4 * (-3 : ℤ) + -12 * (1 : ℤ) : ℤ) = 0 := rfl
    rw [orbitRep_det_gen, h0]
    simp
  · intro t s
    rw [orbitRep_lifted_exp]
    congr 1
    have hW : sbOrbWeight b s
        = (sbOrbA b s + sbOrbA b (partner s)) * 3
          + (pi1BVal s.val + pi1BVal (partner s).val) * -1 := rfl
    rw [Pi.neg_apply, hW]
    push_cast
    ring

/-- **The orbit fiber, exactly**: at every orbit
point `b`, the `weightAt` fiber is precisely
`{sbOrbWeight b, -sbOrbWeight b}` — the determinant
pins the direction to `±(3, -1)` (sum `Σ sbOrbA = -4`,
as for pi1), and character rigidity reads the weight
off the lifted entries. -/
theorem fiber_orbitRep (b : Fin 4 → Bool) (v : Fin 32 → ℤ)
    (hv : weightAt (orbitRep b) v) :
    v = sbOrbWeight b ∨ v = -sbOrbWeight b := by
  obtain ⟨α, β, hgcd, hdet, hlift⟩ := hv
  have hlin : -4 * α + -12 * β = 0 := det_one_orbitRep b hdet
  rcases dir_of_det_shape_4312 hgcd hlin with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · left
    funext s
    have hchar : ∀ t : ℝ,
        Complex.exp ((v s : ℂ) * (t : ℂ) * Complex.I)
          = Complex.exp ((sbOrbWeight b s : ℂ) * (t : ℂ)
            * Complex.I) := by
      intro t
      have h_eq : Complex.exp ((v s : ℂ) * (t : ℂ) * Complex.I)
          = Complex.exp ((((sbOrbA b s + sbOrbA b (partner s)) * 3
              + (pi1BVal s.val + pi1BVal (partner s).val) * -1
              : ℤ) : ℂ) * ((t : ℂ) * Complex.I)) := by
        rw [← hlift t s]
        exact orbitRep_lifted_exp b 3 (-1) t s
      rw [h_eq]
      congr 1
      have hW : sbOrbWeight b s
          = (sbOrbA b s + sbOrbA b (partner s)) * 3
            + (pi1BVal s.val + pi1BVal (partner s).val) * -1 := rfl
      rw [hW]
      push_cast
      ring
    exact char_eq_of_forall hchar
  · right
    funext s
    have hchar : ∀ t : ℝ,
        Complex.exp ((v s : ℂ) * (t : ℂ) * Complex.I)
          = Complex.exp ((((-sbOrbWeight b) s : ℤ) : ℂ)
            * (t : ℂ) * Complex.I) := by
      intro t
      have h_eq : Complex.exp ((v s : ℂ) * (t : ℂ) * Complex.I)
          = Complex.exp ((((sbOrbA b s + sbOrbA b (partner s)) * -3
              + (pi1BVal s.val + pi1BVal (partner s).val) * 1
              : ℤ) : ℂ) * ((t : ℂ) * Complex.I)) := by
        rw [← hlift t s]
        exact orbitRep_lifted_exp b (-3) 1 t s
      rw [h_eq]
      congr 1
      have hW : sbOrbWeight b s
          = (sbOrbA b s + sbOrbA b (partner s)) * 3
            + (pi1BVal s.val + pi1BVal (partner s).val) * -1 := rfl
      rw [Pi.neg_apply, hW]
      push_cast
      ring
    exact char_eq_of_forall hchar

/-! ## §12-prep. The orbit representation at the
generator `genU1A` -/

/-- `star` of the imaginary unit. -/
theorem star_I_eq : star Complex.I = -Complex.I := by simp

/-- **The diagonal entry of `orbitRep b` at the
generator**: `i` times the orbit A-value — the
singles normal form read at `genU1A`, seat by seat,
exactly as for the family diagonal. -/
theorem orbitRep_diag_genU1A (b : Fin 4 → Bool) (s : Fin 32) :
    orbitRep b genU1A s s
      = Complex.I * ((sbOrbA b s : ℤ) : ℂ) := by
  have hu1 : (genU1A).u1 = Complex.I := by simp [genU1A, u1Gen]
  rw [orbitRep_eq_singles, hu1]
  simp only [Matrix.add_apply, Matrix.single_apply, and_self]
  rw [pi1_genU1A_diagonal, Matrix.diagonal_apply_eq]
  by_cases hs8 : s = s8
  · subst hs8
    by_cases hb : b 0 = true
    · simp only [hb, eq_self_iff_true, ite_true, ite_false,
        Bool.false_eq_true_eq_False, add_zero,
        show ¬ (s9 = s8) from s8_ne_s9.symm,
        uSeat_ne_s8, dSeat_ne_s8]
      have hA : sbOrbA b s8 = -1 := by
        rw [sbOrbA, sbOrbSign, if_pos ((sbToggled_s8 b).mpr hb)]
        decide
      rw [hA, star_I_eq]
      have hA1 : pi1AVal (s8).val = 1 := by decide
      rw [hA1]
      push_cast
      ring
    · simp only [if_neg hb, eq_self_iff_true, ite_true, ite_false,
        Bool.false_eq_true_eq_False, add_zero,
        show ¬ (s9 = s8) from s8_ne_s9.symm,
        uSeat_ne_s8, dSeat_ne_s8]
      have hA : sbOrbA b s8 = 1 := by
        rw [sbOrbA, sbOrbSign,
          if_neg (fun h => hb ((sbToggled_s8 b).mp h))]
        decide
      rw [hA]
      have hA1 : pi1AVal (s8).val = 1 := by decide
      rw [hA1]
  by_cases hs9 : s = s9
  · subst hs9
    by_cases hb : b 0 = true
    · simp only [hb, eq_self_iff_true, ite_true, ite_false,
        Bool.false_eq_true_eq_False, add_zero,
        show ¬ (s8 = s9) from s8_ne_s9,
        uSeat_ne_s9, dSeat_ne_s9]
      have hA : sbOrbA b s9 = 1 := by
        rw [sbOrbA, sbOrbSign, if_pos ((sbToggled_s9 b).mpr hb)]
        decide
      rw [hA, star_I_eq]
      have hA1 : pi1AVal (s9).val = -1 := by decide
      rw [hA1]
      push_cast
      ring
    · simp only [if_neg hb, eq_self_iff_true, ite_true, ite_false,
        Bool.false_eq_true_eq_False, add_zero,
        show ¬ (s8 = s9) from s8_ne_s9,
        uSeat_ne_s9, dSeat_ne_s9]
      have hA : sbOrbA b s9 = -1 := by
        rw [sbOrbA, sbOrbSign,
          if_neg (fun h => hb ((sbToggled_s9 b).mp h))]
        decide
      rw [hA]
      have hA1 : pi1AVal (s9).val = -1 := by decide
      rw [hA1]
  by_cases hsU0 : s = uSeat 0
  · subst hsU0
    by_cases hb : b 1 = true
    · simp only [hb, eq_self_iff_true, ite_true, ite_false,
        Bool.false_eq_true_eq_False, add_zero,
        s8_ne_uSeat, s9_ne_uSeat, dSeat_ne_uSeat,
        show ¬ (uSeat 1 = uSeat 0) by decide,
        show ¬ (uSeat 2 = uSeat 0) by decide]
      have hA : sbOrbA b (uSeat 0) = -1 := by
        rw [sbOrbA, sbOrbSign, if_pos ((sbToggled_uSeat b 0).mpr hb)]
        decide
      rw [hA, star_I_eq]
      have hA1 : pi1AVal (uSeat 0).val = 1 := by decide
      rw [hA1]
      push_cast
      ring
    · simp only [if_neg hb, eq_self_iff_true, ite_true, ite_false,
        Bool.false_eq_true_eq_False, add_zero,
        s8_ne_uSeat, s9_ne_uSeat, dSeat_ne_uSeat,
        show ¬ (uSeat 1 = uSeat 0) by decide,
        show ¬ (uSeat 2 = uSeat 0) by decide]
      have hA : sbOrbA b (uSeat 0) = 1 := by
        rw [sbOrbA, sbOrbSign,
          if_neg (fun h => hb ((sbToggled_uSeat b 0).mp h))]
        decide
      rw [hA]
      have hA1 : pi1AVal (uSeat 0).val = 1 := by decide
      rw [hA1]
  by_cases hsD0 : s = dSeat 0
  · subst hsD0
    by_cases hb : b 1 = true
    · simp only [hb, eq_self_iff_true, ite_true, ite_false,
        Bool.false_eq_true_eq_False, add_zero,
        s8_ne_dSeat, s9_ne_dSeat, uSeat_ne_dSeat,
        show ¬ (dSeat 1 = dSeat 0) by decide,
        show ¬ (dSeat 2 = dSeat 0) by decide]
      have hA : sbOrbA b (dSeat 0) = 1 := by
        rw [sbOrbA, sbOrbSign, if_pos ((sbToggled_dSeat b 0).mpr hb)]
        decide
      rw [hA, star_I_eq]
      have hA1 : pi1AVal (dSeat 0).val = -1 := by decide
      rw [hA1]
      push_cast
      ring
    · simp only [if_neg hb, eq_self_iff_true, ite_true, ite_false,
        Bool.false_eq_true_eq_False, add_zero,
        s8_ne_dSeat, s9_ne_dSeat, uSeat_ne_dSeat,
        show ¬ (dSeat 1 = dSeat 0) by decide,
        show ¬ (dSeat 2 = dSeat 0) by decide]
      have hA : sbOrbA b (dSeat 0) = -1 := by
        rw [sbOrbA, sbOrbSign,
          if_neg (fun h => hb ((sbToggled_dSeat b 0).mp h))]
        decide
      rw [hA]
      have hA1 : pi1AVal (dSeat 0).val = -1 := by decide
      rw [hA1]
  by_cases hsU1 : s = uSeat 1
  · subst hsU1
    by_cases hb : b 2 = true
    · simp only [hb, eq_self_iff_true, ite_true, ite_false,
        Bool.false_eq_true_eq_False, add_zero,
        s8_ne_uSeat, s9_ne_uSeat, dSeat_ne_uSeat,
        show ¬ (uSeat 0 = uSeat 1) by decide,
        show ¬ (uSeat 2 = uSeat 1) by decide]
      have hA : sbOrbA b (uSeat 1) = -1 := by
        rw [sbOrbA, sbOrbSign, if_pos ((sbToggled_uSeat b 1).mpr hb)]
        decide
      rw [hA, star_I_eq]
      have hA1 : pi1AVal (uSeat 1).val = 1 := by decide
      rw [hA1]
      push_cast
      ring
    · simp only [if_neg hb, eq_self_iff_true, ite_true, ite_false,
        Bool.false_eq_true_eq_False, add_zero,
        s8_ne_uSeat, s9_ne_uSeat, dSeat_ne_uSeat,
        show ¬ (uSeat 0 = uSeat 1) by decide,
        show ¬ (uSeat 2 = uSeat 1) by decide]
      have hA : sbOrbA b (uSeat 1) = 1 := by
        rw [sbOrbA, sbOrbSign,
          if_neg (fun h => hb ((sbToggled_uSeat b 1).mp h))]
        decide
      rw [hA]
      have hA1 : pi1AVal (uSeat 1).val = 1 := by decide
      rw [hA1]
  by_cases hsD1 : s = dSeat 1
  · subst hsD1
    by_cases hb : b 2 = true
    · simp only [hb, eq_self_iff_true, ite_true, ite_false,
        Bool.false_eq_true_eq_False, add_zero,
        s8_ne_dSeat, s9_ne_dSeat, uSeat_ne_dSeat,
        show ¬ (dSeat 0 = dSeat 1) by decide,
        show ¬ (dSeat 2 = dSeat 1) by decide]
      have hA : sbOrbA b (dSeat 1) = 1 := by
        rw [sbOrbA, sbOrbSign, if_pos ((sbToggled_dSeat b 1).mpr hb)]
        decide
      rw [hA, star_I_eq]
      have hA1 : pi1AVal (dSeat 1).val = -1 := by decide
      rw [hA1]
      push_cast
      ring
    · simp only [if_neg hb, eq_self_iff_true, ite_true, ite_false,
        Bool.false_eq_true_eq_False, add_zero,
        s8_ne_dSeat, s9_ne_dSeat, uSeat_ne_dSeat,
        show ¬ (dSeat 0 = dSeat 1) by decide,
        show ¬ (dSeat 2 = dSeat 1) by decide]
      have hA : sbOrbA b (dSeat 1) = -1 := by
        rw [sbOrbA, sbOrbSign,
          if_neg (fun h => hb ((sbToggled_dSeat b 1).mp h))]
        decide
      rw [hA]
      have hA1 : pi1AVal (dSeat 1).val = -1 := by decide
      rw [hA1]
  by_cases hsU2 : s = uSeat 2
  · subst hsU2
    by_cases hb : b 3 = true
    · simp only [hb, eq_self_iff_true, ite_true, ite_false,
        Bool.false_eq_true_eq_False, add_zero,
        s8_ne_uSeat, s9_ne_uSeat, dSeat_ne_uSeat,
        show ¬ (uSeat 0 = uSeat 2) by decide,
        show ¬ (uSeat 1 = uSeat 2) by decide]
      have hA : sbOrbA b (uSeat 2) = -1 := by
        rw [sbOrbA, sbOrbSign, if_pos ((sbToggled_uSeat b 2).mpr hb)]
        decide
      rw [hA, star_I_eq]
      have hA1 : pi1AVal (uSeat 2).val = 1 := by decide
      rw [hA1]
      push_cast
      ring
    · simp only [if_neg hb, eq_self_iff_true, ite_true, ite_false,
        Bool.false_eq_true_eq_False, add_zero,
        s8_ne_uSeat, s9_ne_uSeat, dSeat_ne_uSeat,
        show ¬ (uSeat 0 = uSeat 2) by decide,
        show ¬ (uSeat 1 = uSeat 2) by decide]
      have hA : sbOrbA b (uSeat 2) = 1 := by
        rw [sbOrbA, sbOrbSign,
          if_neg (fun h => hb ((sbToggled_uSeat b 2).mp h))]
        decide
      rw [hA]
      have hA1 : pi1AVal (uSeat 2).val = 1 := by decide
      rw [hA1]
  by_cases hsD2 : s = dSeat 2
  · subst hsD2
    by_cases hb : b 3 = true
    · simp only [hb, eq_self_iff_true, ite_true, ite_false,
        Bool.false_eq_true_eq_False, add_zero,
        s8_ne_dSeat, s9_ne_dSeat, uSeat_ne_dSeat,
        show ¬ (dSeat 0 = dSeat 2) by decide,
        show ¬ (dSeat 1 = dSeat 2) by decide]
      have hA : sbOrbA b (dSeat 2) = 1 := by
        rw [sbOrbA, sbOrbSign, if_pos ((sbToggled_dSeat b 2).mpr hb)]
        decide
      rw [hA, star_I_eq]
      have hA1 : pi1AVal (dSeat 2).val = -1 := by decide
      rw [hA1]
      push_cast
      ring
    · simp only [if_neg hb, eq_self_iff_true, ite_true, ite_false,
        Bool.false_eq_true_eq_False, add_zero,
        s8_ne_dSeat, s9_ne_dSeat, uSeat_ne_dSeat,
        show ¬ (dSeat 0 = dSeat 2) by decide,
        show ¬ (dSeat 1 = dSeat 2) by decide]
      have hA : sbOrbA b (dSeat 2) = -1 := by
        rw [sbOrbA, sbOrbSign,
          if_neg (fun h => hb ((sbToggled_dSeat b 2).mp h))]
        decide
      rw [hA]
      have hA1 : pi1AVal (dSeat 2).val = -1 := by decide
      rw [hA1]
  · have hnotog : ¬ sbToggled b s := by
      rintro (⟨-, h⟩ | ⟨c, -, h⟩)
      · rcases h with h | h
        · exact hs8 h
        · exact hs9 h
      · rcases h with h | h
        · fin_cases c
          · exact hsU0 h
          · exact hsU1 h
          · exact hsU2 h
        · fin_cases c
          · exact hsD0 h
          · exact hsD1 h
          · exact hsD2 h
    have hA : sbOrbA b s = pi1AVal s.val := by
      simp only [sbOrbA, sbOrbSign, if_neg hnotog, one_mul]
    rw [hA]
    simp only [add_zero,
      show ¬ (s8 = s) from fun h => hs8 h.symm,
      show ¬ (s9 = s) from fun h => hs9 h.symm,
      show ¬ (uSeat 0 = s) from fun h => hsU0 h.symm,
      show ¬ (dSeat 0 = s) from fun h => hsD0 h.symm,
      show ¬ (uSeat 1 = s) from fun h => hsU1 h.symm,
      show ¬ (dSeat 1 = s) from fun h => hsD1 h.symm,
      show ¬ (uSeat 2 = s) from fun h => hsU2 h.symm,
      show ¬ (dSeat 2 = s) from fun h => hsD2 h.symm,
      ite_false]

/-- **The orbit representation at the generator is
the diagonal** of `i • (orbit A-values)`. -/
theorem orbitRep_genU1A_diagonal (b : Fin 4 → Bool) :
    orbitRep b genU1A
      = Matrix.diagonal (fun i => Complex.I * ((sbOrbA b i : ℤ) : ℂ)) := by
  ext i j
  by_cases hij : i = j
  · subst hij
    rw [orbitRep_diag_genU1A, Matrix.diagonal_apply_eq]
  · rw [Matrix.diagonal_apply_ne _ hij]
    have hu1 : (genU1A).u1 = Complex.I := by simp [genU1A, u1Gen]
    have hne : ∀ s : Fin 32, ¬ (s = i ∧ s = j) :=
      fun s h => hij (h.1.symm.trans h.2)
    rw [orbitRep_eq_singles, hu1]
    simp only [Matrix.add_apply]
    rw [pi1_genU1A_diagonal, Matrix.diagonal_apply_ne _ hij]
    simp only [Matrix.single_apply, hne, ite_false, add_zero]

/-! ## §12. The coordinates, per member -/

/-- Product of two `i • table` entries. -/
theorem prod_I_mul (h x : ℤ) :
    (Complex.I * (h : ℂ)) * (Complex.I * (x : ℂ))
      = -((h * x : ℤ) : ℂ) := by
  have hrw : (Complex.I * (h : ℂ)) * (Complex.I * (x : ℂ))
      = (Complex.I * Complex.I) * ((h : ℂ) * (x : ℂ)) := by ring
  rw [hrw, Complex.I_mul_I]
  push_cast
  ring

/-- Cube of an `i • table` entry. -/
theorem cube_I_mul (x : ℤ) :
    (Complex.I * (x : ℂ)) * (Complex.I * (x : ℂ))
        * (Complex.I * (x : ℂ))
      = -Complex.I * ((x ^ 3 : ℤ) : ℂ) := by
  have hI3 : Complex.I * Complex.I * Complex.I = -Complex.I := by
    rw [Complex.I_mul_I]
    simp
  have hrw : (Complex.I * (x : ℂ)) * (Complex.I * (x : ℂ))
        * (Complex.I * (x : ℂ))
      = (Complex.I * Complex.I * Complex.I) * ((x : ℂ) ^ 3) := by
    ring
  push_cast
  rw [hrw, hI3]

/-- Trace of a cubed diagonal. -/
theorem trace_cube_diagonal (d : Fin 32 → ℂ) :
    Matrix.trace (Matrix.diagonal d * Matrix.diagonal d
        * Matrix.diagonal d)
      = ∑ i, d i * d i * d i := by
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal,
    Matrix.trace_diagonal]

/-- `piFlip` at the generator is the diagonal of
`i • (flip A-values)`. -/
theorem piFlip_genU1A_diagonal :
    ThetLogos.HyperchargeForcing.piFlip genU1A
      = Matrix.diagonal (fun i => Complex.I * ((sbFlipA i : ℤ) : ℂ)) := by
  have hu1 : (genU1A).u1 = Complex.I := by simp [genU1A, u1Gen]
  ext i j
  by_cases hij : i = j
  · subst hij
    rw [Matrix.diagonal_apply_eq,
      ThetLogos.HyperchargeForcing.piFlip_apply]
    by_cases hi : i = s8
    · subst hi
      rw [if_pos ⟨rfl, rfl⟩, hu1, star_I_eq]
      have hF : sbFlipA s8 = -1 := by decide
      rw [hF]
      push_cast
      ring
    · rw [if_neg (fun h => hi h.1), pi1_genU1A_diagonal,
        Matrix.diagonal_apply_eq]
      have hF : sbFlipA i = pi1AVal i.val := by
        simp [sbFlipA, sbFlipSign, hi]
      rw [hF]
  · rw [Matrix.diagonal_apply_ne _ hij,
      ThetLogos.HyperchargeForcing.piFlip_apply,
      if_neg (fun h => hij (h.1.trans h.2.symm)),
      pi1_genU1A_diagonal, Matrix.diagonal_apply_ne _ hij]

/-- `piEFlip` at the generator is the diagonal of
`i • (e-flip A-values)`. -/
theorem piEFlip_genU1A_diagonal :
    piEFlip genU1A
      = Matrix.diagonal (fun i => Complex.I * ((sbEFlipA i : ℤ) : ℂ)) := by
  have hu1 : (genU1A).u1 = Complex.I := by simp [genU1A, u1Gen]
  ext i j
  by_cases hij : i = j
  · subst hij
    rw [Matrix.diagonal_apply_eq, piEFlip_unfold, Matrix.add_apply,
      hu1, pi1_genU1A_diagonal, Matrix.diagonal_apply_eq,
      Matrix.single_apply]
    by_cases hi : i = s9
    · subst hi
      rw [if_pos ⟨rfl, rfl⟩, star_I_eq]
      have hA1 : pi1AVal (s9).val = -1 := by decide
      have hF : sbEFlipA s9 = 1 := by decide
      rw [hA1, hF]
      push_cast
      ring
    · rw [if_neg (fun h => hi h.1.symm)]
      have hF : sbEFlipA i = pi1AVal i.val := by
        simp [sbEFlipA, sbEFlipSign, hi]
      rw [hF, add_zero]
  · rw [Matrix.diagonal_apply_ne _ hij, piEFlip_unfold,
      Matrix.add_apply, hu1, pi1_genU1A_diagonal,
      Matrix.diagonal_apply_ne _ hij, Matrix.single_apply]
    have hne : ¬ (s9 = i ∧ s9 = j) :=
      fun h => hij (h.1.symm.trans h.2)
    rw [if_neg hne, add_zero]

/-! ### Coordinate 0: the M₃ × U(1) moment vanishes
at every member (the C-table and the B-table have
disjoint support). -/

theorem coord0_pi1 : prodMoment pi1 genCdiag genU1B = 0 := by
  rw [prodMoment_unfold, pi1_genU1B_diagonal, trace_mul_diagonal]
  have hterm : ∀ i : Fin 32, pi1 genCdiag i i
        * (Complex.I * ((pi1BVal i.val : ℤ) : ℂ))
      = -((sbCVal i.val * pi1BVal i.val : ℤ) : ℂ) := by
    intro i
    rw [pi1_genCdiag_diag, prod_I_mul]
  rw [Finset.sum_congr rfl (fun i _ => hterm i)]
  simp only [← Int.cast_neg, ← Int.cast_sum, Finset.sum_neg_distrib,
    sum_cB, neg_zero, Int.cast_zero]

theorem coord0_piFlip :
    prodMoment ThetLogos.HyperchargeForcing.piFlip genCdiag genU1B
      = 0 := by
  rw [prodMoment_unfold, piFlip_of_u1_zero genCdiag_u1,
    piFlip_of_u1_zero genU1B_u1, ← prodMoment_unfold]
  exact coord0_pi1

theorem coord0_piEFlip :
    prodMoment piEFlip genCdiag genU1B = 0 := by
  rw [prodMoment_unfold, piEFlip_of_u1_zero genCdiag_u1,
    piEFlip_of_u1_zero genU1B_u1, ← prodMoment_unfold]
  exact coord0_pi1

theorem coord0_orbitRep (b : Fin 4 → Bool) :
    prodMoment (orbitRep b) genCdiag genU1B = 0 := by
  rw [prodMoment_unfold, orbitRep_of_u1_zero b genCdiag_u1,
    orbitRep_of_u1_zero b genU1B_u1, ← prodMoment_unfold]
  exact coord0_pi1

/-! ### Coordinate 1: the ℍ × U(1) moment vanishes
at every member (the H-table and every signed
A-table have disjoint support, pointwise). -/

theorem coord1_pi1 : prodMoment pi1 genHdiag genU1A = 0 := by
  rw [prodMoment_unfold, pi1_genU1A_diagonal, trace_mul_diagonal]
  have hterm : ∀ i : Fin 32, pi1 genHdiag i i
        * (Complex.I * ((pi1AVal i.val : ℤ) : ℂ)) = 0 := by
    intro i
    rw [pi1_genHdiag_diag, prod_I_mul,
      show sbHVal i.val * pi1AVal i.val = 0 from by
        rw [mul_comm]; exact sum_A_hval i,
      Int.cast_zero, neg_zero]
  rw [Finset.sum_congr rfl (fun i _ => hterm i),
    Finset.sum_const_zero]

theorem coord1_piFlip :
    prodMoment ThetLogos.HyperchargeForcing.piFlip genHdiag genU1A
      = 0 := by
  rw [prodMoment_unfold,
    piFlip_of_u1_zero genHdiag_u1,
    piFlip_genU1A_diagonal, trace_mul_diagonal]
  have hterm : ∀ i : Fin 32, pi1 genHdiag i i
        * (Complex.I * ((sbFlipA i : ℤ) : ℂ)) = 0 := by
    intro i
    rw [pi1_genHdiag_diag, prod_I_mul,
      show sbHVal i.val * sbFlipA i = 0 from by
        have h0 : sbHVal i.val * pi1AVal i.val = 0 := by
          rw [mul_comm]; exact sum_A_hval i
        rw [sbFlipA,
          show sbHVal i.val * (sbFlipSign i * pi1AVal i.val)
            = sbFlipSign i * (sbHVal i.val * pi1AVal i.val) from by
            ring, h0, mul_zero],
      Int.cast_zero, neg_zero]
  rw [Finset.sum_congr rfl (fun i _ => hterm i),
    Finset.sum_const_zero]

theorem coord1_piEFlip :
    prodMoment piEFlip genHdiag genU1A = 0 := by
  rw [prodMoment_unfold, piEFlip_of_u1_zero genHdiag_u1,
    piEFlip_genU1A_diagonal, trace_mul_diagonal]
  have hterm : ∀ i : Fin 32, pi1 genHdiag i i
        * (Complex.I * ((sbEFlipA i : ℤ) : ℂ)) = 0 := by
    intro i
    rw [pi1_genHdiag_diag, prod_I_mul,
      show sbHVal i.val * sbEFlipA i = 0 from by
        have h0 : sbHVal i.val * pi1AVal i.val = 0 := by
          rw [mul_comm]; exact sum_A_hval i
        rw [sbEFlipA,
          show sbHVal i.val * (sbEFlipSign i * pi1AVal i.val)
            = sbEFlipSign i * (sbHVal i.val * pi1AVal i.val) from by
            ring, h0, mul_zero],
      Int.cast_zero, neg_zero]
  rw [Finset.sum_congr rfl (fun i _ => hterm i),
    Finset.sum_const_zero]

theorem coord1_orbitRep (b : Fin 4 → Bool) :
    prodMoment (orbitRep b) genHdiag genU1A = 0 := by
  rw [prodMoment_unfold, orbitRep_of_u1_zero b genHdiag_u1,
    orbitRep_genU1A_diagonal, trace_mul_diagonal]
  have hterm : ∀ i : Fin 32, pi1 genHdiag i i
        * (Complex.I * ((sbOrbA b i : ℤ) : ℂ)) = 0 := by
    intro i
    rw [pi1_genHdiag_diag, prod_I_mul,
      show sbHVal i.val * sbOrbA b i = 0 from by
        have h0 : sbHVal i.val * pi1AVal i.val = 0 := by
          rw [mul_comm]; exact sum_A_hval i
        rw [sbOrbA,
          show sbHVal i.val * (sbOrbSign b i * pi1AVal i.val)
            = sbOrbSign b i * (sbHVal i.val * pi1AVal i.val) from by
            ring, h0, mul_zero],
      Int.cast_zero, neg_zero]
  rw [Finset.sum_congr rfl (fun i _ => hterm i),
    Finset.sum_const_zero]

/-! ### Coordinate 2: the γ-weighted moment — `0` at
pi1 and at every orbit point, `2i` at piFlip, `-2i`
at piEFlip (landed γ-trace computations). -/

theorem coord2_pi1 : gammaMoment pi1 genU1A = 0 := by
  rw [gammaMoment_unfold]
  exact trace_gammaF_pi1_u1Gen 1 0

theorem coord2_piFlip :
    gammaMoment ThetLogos.HyperchargeForcing.piFlip genU1A
      = 2 * Complex.I := by
  rw [gammaMoment_unfold]
  simpa [genU1A] using trace_gammaF_piFlip_u1Gen 1 0

theorem coord2_piEFlip :
    gammaMoment piEFlip genU1A = -2 * Complex.I := by
  rw [gammaMoment_unfold]
  simpa [genU1A] using trace_gammaF_piEFlip_u1Gen 1 0

theorem coord2_orbitRep (b : Fin 4 → Bool) :
    gammaMoment (orbitRep b) genU1A = 0 := by
  rw [gammaMoment_unfold, trace_gammaF_mul]
  have hterm : ∀ i : Fin 32, gammaF i i * orbitRep b genU1A i i
      = Complex.I * ((gammaVal i.val * sbOrbA b i : ℤ) : ℂ) := by
    intro i
    rw [gammaF_diag_eq, orbitRep_diag_genU1A]
    push_cast
    ring
  rw [Finset.sum_congr rfl (fun i _ => hterm i), ← Finset.mul_sum,
    ← Int.cast_sum]
  have hsum : ∑ i : Fin 32, gammaVal i.val * sbOrbA b i = 0 := by
    have h := gamma_sum_orbA b
    simpa [sbOrbA, mul_assoc] using h
  rw [hsum]
  simp

/-! ### Coordinate 3: the cubic moment — `4i` at pi1
and at every orbit point, `6i` at piFlip, `2i` at
piEFlip (the signed cube sums `-4`, `-6`, `-2`,
`-4`). -/

theorem coord3_pi1 :
    cubicMoment pi1 genU1A = 4 * Complex.I := by
  rw [cubicMoment_unfold, pi1_genU1A_diagonal, trace_cube_diagonal,
    Finset.sum_congr rfl (fun i _ => cube_I_mul (pi1AVal i.val)),
    ← Finset.mul_sum, ← Int.cast_sum, sum_A3]
  push_cast
  ring

theorem coord3_piFlip :
    cubicMoment ThetLogos.HyperchargeForcing.piFlip genU1A
      = 6 * Complex.I := by
  rw [cubicMoment_unfold, piFlip_genU1A_diagonal,
    trace_cube_diagonal,
    Finset.sum_congr rfl (fun i _ => cube_I_mul (sbFlipA i)),
    ← Finset.mul_sum, ← Int.cast_sum]
  have hsum : ∑ i : Fin 32, (sbFlipA i) ^ 3 = -6 := sum_flipA3
  rw [hsum]
  push_cast
  ring

theorem coord3_piEFlip :
    cubicMoment piEFlip genU1A = 2 * Complex.I := by
  rw [cubicMoment_unfold, piEFlip_genU1A_diagonal,
    trace_cube_diagonal,
    Finset.sum_congr rfl (fun i _ => cube_I_mul (sbEFlipA i)),
    ← Finset.mul_sum, ← Int.cast_sum]
  have hsum : ∑ i : Fin 32, (sbEFlipA i) ^ 3 = -2 := sum_eflipA3
  rw [hsum]
  push_cast
  ring

theorem coord3_orbitRep (b : Fin 4 → Bool) :
    cubicMoment (orbitRep b) genU1A = 4 * Complex.I := by
  rw [cubicMoment_unfold, orbitRep_genU1A_diagonal,
    trace_cube_diagonal,
    Finset.sum_congr rfl (fun i _ => cube_I_mul (sbOrbA b i)),
    ← Finset.mul_sum, ← Int.cast_sum]
  have hsum : ∑ i : Fin 32, (sbOrbA b i) ^ 3 = -4 := sum_orbA3 b
  rw [hsum]
  push_cast
  ring

/-! ### The assembled coordinate vectors -/

theorem shapeBCoord_pi1 :
    shapeBCoord pi1 = ![0, 0, 0, 4 * Complex.I] := by
  rw [shapeBCoord_unfold]
  funext i
  fin_cases i <;> simp [coord0_pi1, coord1_pi1, coord2_pi1,
    coord3_pi1]

theorem shapeBCoord_piFlip :
    shapeBCoord ThetLogos.HyperchargeForcing.piFlip
      = ![0, 0, 2 * Complex.I, 6 * Complex.I] := by
  rw [shapeBCoord_unfold]
  funext i
  fin_cases i <;> simp [coord0_piFlip, coord1_piFlip, coord2_piFlip,
    coord3_piFlip]

theorem shapeBCoord_piEFlip :
    shapeBCoord piEFlip = ![0, 0, -2 * Complex.I, 2 * Complex.I] := by
  rw [shapeBCoord_unfold]
  funext i
  fin_cases i <;> simp [coord0_piEFlip, coord1_piEFlip,
    coord2_piEFlip, coord3_piEFlip]

theorem shapeBCoord_orbitRep (b : Fin 4 → Bool) :
    shapeBCoord (orbitRep b) = ![0, 0, 0, 4 * Complex.I] := by
  rw [shapeBCoord_unfold]
  funext i
  fin_cases i <;> simp [coord0_orbitRep, coord1_orbitRep,
    coord2_orbitRep, coord3_orbitRep]

/-! ## §13. The refutation

Every clause of the frozen `ShapeBIdentification`
fails, at a named fiber point and a named index:
the coordinates do not read the sector polynomials
on the fibers. K-CLS-B resolution: pi1 and all
sixteen orbit points collide at `![0, 0, 0, 4i]`;
piFlip and piEFlip are separated from that blob and
from each other. -/

/-- **The pi1 clause is false**: at the fiber point
`commonWeightVector`, index 3 reads `4i` on the
coordinate side against sector value `0`. -/
theorem pi1_clause_false :
    ¬ (∀ v, weightAt pi1 v → shapeBCoord pi1 = sectorPoly v) := by
  intro h
  have h1 := h commonWeightVector weightAt_pi1_common
  rw [shapeBCoord_pi1, sectorPoly_unfold] at h1
  have h3 := congrFun h1 (3 : Fin 4)
  simp only [Matrix.cons_val_three, Matrix.head_cons] at h3
  rw [sector_common_zero.2.2.2] at h3
  norm_num [Complex.ext_iff] at h3

/-- **The piFlip clause is false**: at the fiber
point `sbFlipWeight`, index 1 reads `0` on the
coordinate side against sector value `-2`. -/
theorem piFlip_clause_false :
    ¬ (∀ v, weightAt ThetLogos.HyperchargeForcing.piFlip v
      → shapeBCoord ThetLogos.HyperchargeForcing.piFlip
        = sectorPoly v) := by
  intro h
  have h1 := h sbFlipWeight weightAt_piFlip_flipWeight
  rw [shapeBCoord_piFlip, sectorPoly_unfold] at h1
  have h3 := congrFun h1 (1 : Fin 4)
  simp only [Matrix.cons_val_one, Matrix.head_cons] at h3
  rw [sector_flipWeight.2.1] at h3
  norm_num [Complex.ext_iff] at h3

/-- **The piEFlip clause is false**: at the fiber
point `sbEFlipWeight`, index 1 reads `0` on the
coordinate side against sector value `6`. -/
theorem piEFlip_clause_false :
    ¬ (∀ v, weightAt piEFlip v → shapeBCoord piEFlip
      = sectorPoly v) := by
  intro h
  have h1 := h sbEFlipWeight weightAt_piEFlip_eflipWeight
  rw [shapeBCoord_piEFlip, sectorPoly_unfold] at h1
  have h3 := congrFun h1 (1 : Fin 4)
  simp only [Matrix.cons_val_one, Matrix.head_cons] at h3
  rw [sector_eflipWeight.2.1] at h3
  norm_num [Complex.ext_iff] at h3

/-- **The orbit clause is false at every pattern
`b`**: at the fiber point `sbOrbWeight b`, index 3
reads `4i` on the coordinate side against sector
value `0` — the same collision as pi1. -/
theorem orbit_clause_false (b : Fin 4 → Bool) :
    ¬ (∀ v, weightAt (orbitRep b) v
      → shapeBCoord (orbitRep b) = sectorPoly v) := by
  intro h
  have h1 := h (sbOrbWeight b) (weightAt_orbitRep_orbWeight b)
  rw [shapeBCoord_orbitRep, sectorPoly_unfold] at h1
  have h3 := congrFun h1 (3 : Fin 4)
  simp only [Matrix.cons_val_three, Matrix.head_cons] at h3
  rw [(sector_orbWeight b).2.2.2] at h3
  norm_num [Complex.ext_iff] at h3

/-- **The frozen `ShapeBIdentification` is REFUTED**
(T1): every clause fails at a named fiber point —
the Shape B coordinates do not identify the sector
polynomials on the toggle family. The frozen Prop
is not weakened; it is false as stated. -/
theorem not_shapeBIdentification : ¬ ShapeBIdentification :=
  fun h => pi1_clause_false (shapeBIdentification_unfold.mp h).1

end ThetLogos.DialOneShapeBIdentification
