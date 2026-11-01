import Mathlib.Tactic
import Mathlib.Basic.ENNReal.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import ThetLogos.ConnesDistanceTheory
import ThetLogos.Q7C4R4SecondLeg
import ThetLogos.Q7C4R4LinkC4

open scoped Matrix.Norms.L2Operator ENNReal InnerProductSpace

namespace ThetLogos

/-!
# ThetLogos.ConnesDistanceCycle - GR-DIST-2: the Fin 4 cycle seat

**Working label only.** The module name `ConnesDistanceCycle`
and the line name GR-DIST are working labels; Jeff names.

**Program ceiling, on the face.** This module computes a finite
state-space distance at one named seat - vocabulary. It seats
NO gravity object; Dial 2 = 0. The distance here is a distance
between point states of the Fin 4 diagonal algebra; it is never
a spatial separation and is never spent as a spatial `r`
(K-GR-SMUG instance (i)).

**The seat operator.** `cycleDirac` is the self-adjoint
cyclic-shift combination built from the landed shift kit: the
matrix `shiftMat` of the landed shift action (`z4ShiftOp` of
`Q7C4R4SecondLeg`, the same action as the C-linear `shiftC4C`
of `Q7C4R4LinkC4`, both acting by `x k -> x (k + 1)`), plus its
conjugate transpose:
`cycleDirac = shiftMat + shiftMat.conjTranspose`.
Its entries are the cycle adjacency: `1` on the two cyclic
neighbours of each site, `0` elsewhere. Normalization: the
unrescaled symmetric shift sum - adjacency entries exactly `1`.
The constant in the value theorem below is whatever this
normalization gives; it was not tuned (see the finding).

**What is proved.**
1. Finiteness at the seat: no pair carries a commutant
   obstruction (a diagonal element commuting with the full
   cycle operator is constant), so by DIST-1's criterion
   (`connesDist_lt_top_of_no_obstruction`) the distance is
   finite at every pair. Definiteness at the seat: the
   commutators separate every distinct pair
   (`ConnesCommSeparates cycleDirac`, by explicit witnesses),
   so by DIST-1's conditional discharge
   (`eq_of_connesDist_eq_zero_of_separates`) distance zero
   forces equality of points.
2. **The value theorem - and a FINDING at full rank.** The
   brick's governing pack anticipated the value
   `constant * cyclic graph distance`. That form is FALSE at
   this seat for this operator: the exact value, proved below,
   is the DISCRETE distance - `connesDist cycleDirac i j = 1`
   for every distinct pair `i, j` (adjacent or opposite), `0`
   on the diagonal. The opposite pair `(0, 2)` is the
   counterexample to the anticipated form: its cyclic distance
   is `2`, its Connes distance is `1` (witness
   `a = (0, 1, 1, 0)`, whose commutator is a signed permutation
   matrix of operator norm `1`). The BRIDGE-1 Python
   cross-check (formula grade, seats differ - see the run
   record `grdist2-bridge1-run.txt` in the scratch tree)
   independently reproduces these values. This is reported as
   the seat's true value, not repaired by renormalizing the
   operator: with the DIST-1 scaling law the rescaling remark
   is a labeled corollary below. Two-sided comparability with
   the cyclic distance does hold and is proved:
   `(1/2) * cycDist4 <= connesDist <= 1 * cycDist4` in the
   `ENNReal.ofReal` form, with `0 < 1/2 <= 1` - so the seat is
   vocabulary-grade (finite, definite, comparable), with the
   exact constant in the anticipated proportional form named
   as NOT EXISTING at this seat: no single constant `K` has
   `connesDist = K * cycDist4` on all pairs (adjacent pairs
   force `K = 1`, opposite pairs force `K = 1/2`).
3. Degeneracy discipline (K-DIST-DEG): no pair at this seat
   degenerates - no distinct pair sits at distance `0` or
   infinity. The degeneracy finding of this brick is the
   value-form finding of item 2, stated at full rank.
-/

/-! ## The shift matrix, from the landed shift kit -/

/-- **The matrix of the landed cyclic shift.** `shiftMat i j`
is `1` when `j = i + 1` (indices in `Fin 4`, so `+1` is the
cyclic successor) and `0` otherwise. Its `mulVec` action is
the landed shift action, proved below. -/
def shiftMat : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.of fun i j => if j = i + 1 then 1 else 0

/-- The landed Z4 shift and the C4 shift permutation agree:
both are the cyclic successor on `Fin 4`. -/
theorem c4ShiftPerm_eq_succ (k : Fin 4) : c4ShiftPerm k = k + 1 := by
  fin_cases k <;> rfl

/-- `shiftMat` acts on vectors as the landed `z4ShiftOp`
(`Q7C4R4SecondLeg`): `(shiftMat *ᵥ x) k = x (k + 1)`. -/
theorem shiftMat_mulVec (x : Fin 4 → ℂ) (k : Fin 4) :
    (shiftMat.mulVec x) k = x (k + 1) := by
  rw [Matrix.mulVec_apply_eq_sum]
  rw [Finset.sum_eq_single (k + 1)]
  · simp [shiftMat]
  · intro j _ hj
    simp [shiftMat, hj]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- `shiftMat` acts on vectors as the landed C-linear shift
`shiftC4C` (`Q7C4R4LinkC4`). -/
theorem shiftMat_mulVec_eq_shiftC4C (x : Fin 4 → ℂ) :
    shiftMat.mulVec x = shiftC4C x := by
  funext k
  rw [shiftMat_mulVec]
  show x (k + 1) = shiftC4C x k
  rw [← c4ShiftPerm_eq_succ k]
  rfl

/-! ## The seat operator -/

/-- **The cycle Dirac at the Fin 4 seat (seat operator of
GR-DIST-2).** The self-adjoint cyclic-shift combination
`shiftMat + shiftMatᴴ`, written entrywise: `1` on the two
cyclic neighbours of each site, `0` elsewhere - the adjacency
operator of the 4-cycle, with adjacency entries exactly `1`
(the unrescaled symmetric shift sum). -/
def cycleDirac : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.of fun i j => if (j = i + 1 ∨ i = j + 1) then 1 else 0

/-- Entry formula for the seat operator, read back. -/
theorem cycleDirac_apply (i j : Fin 4) :
    cycleDirac i j = if (j = i + 1 ∨ i = j + 1) then (1 : ℂ) else 0 :=
  rfl

/-- **The seat operator is the symmetric shift sum:**
`cycleDirac = shiftMat + shiftMatᴴ`, the self-adjoint
combination of the landed shift the pack prescribes. -/
theorem cycleDirac_eq_shiftMat_add_conjTranspose :
    cycleDirac = shiftMat + Matrix.conjTranspose shiftMat := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cycleDirac, shiftMat, Matrix.conjTranspose] <;> norm_num

/-- **Self-adjointness of the seat operator**, from the
symmetric entry formula (entries are real `0`/`1` and the
neighbour relation is symmetric). -/
theorem cycleDirac_selfAdjoint : IsSelfAdjoint cycleDirac := by
  rw [isSelfAdjoint_iff, Matrix.star_eq_conjTranspose]
  ext i j
  by_cases h : (i = j + 1 ∨ j = i + 1)
  · have h' : (j = i + 1 ∨ i = j + 1) := h.symm
    simp [Matrix.conjTranspose, cycleDirac, h, h']
  · have h' : ¬ (j = i + 1 ∨ i = j + 1) := fun hh => h hh.symm
    simp [Matrix.conjTranspose, cycleDirac, h, h']

/-- **The Fin 4 cycle seat**, as a registered
`ConnesDistanceSeat`: the seat operator `cycleDirac` with its
self-adjointness. -/
def cycleSeat : ConnesDistanceSeat (Fin 4) :=
  ⟨cycleDirac, cycleDirac_selfAdjoint⟩

/-- The seat's operator is `cycleDirac`, read back. -/
theorem cycleSeat_D : cycleSeat.D = cycleDirac := rfl

/-! ## The Fin 4 cyclic distance (local definition)

The pack permits reusing GEO's `cycDist` at `N = 4`; that
definition lives on `ZMod 4`, not `Fin 4`, so the Fin 4
cyclic distance is defined locally here. On values it is
`min (dist) (4 - dist)`, and it agrees with the `ZMod 4`
formula `min d (4 - d)` under `Fin.val` - a shared arithmetic
helper coincidence, noted per the pack; no GEO theorem is
cited as DIST evidence. -/

/-- **The cyclic graph distance on `Fin 4`** (local): the
shorter of the two arc lengths between the sites. -/
def cycDist4 (i j : Fin 4) : ℕ :=
  min ((j.val + 4 - i.val) % 4) ((i.val + 4 - j.val) % 4)

/-- The local cyclic distance vanishes exactly on the
diagonal. -/
theorem cycDist4_eq_zero_iff (i j : Fin 4) :
    cycDist4 i j = 0 ↔ i = j := by
  fin_cases i <;> fin_cases j <;> decide

/-- At a distinct pair the local cyclic distance is `1` or
`2`: bounded below by `1` and above by `2`. -/
theorem cycDist4_bounds_of_ne {i j : Fin 4} (h : i ≠ j) :
    1 ≤ cycDist4 i j ∧ cycDist4 i j ≤ 2 := by
  fin_cases i <;> fin_cases j <;> simp_all [cycDist4] <;> decide

/-! ## Finiteness at the seat: no commutant obstruction

A diagonal element commuting with the full cycle is constant:
the `(i, i+1)` entry of its commutator is `a (i+1) - a i`, and
the cycle edges cover every successor step. -/

/-- **Successor step from a vanishing commutator.** If
`commDiag cycleDirac a = 0` then `a (i + 1) = a i` for every
site `i`: the `(i, i+1)` commutator entry is the successor
difference, since `cycleDirac i (i+1) = 1`. -/
theorem step_eq_of_commDiag_cycleDirac_eq_zero (a : Fin 4 → ℂ)
    (h : commDiag cycleDirac a = 0) (i : Fin 4) :
    a (i + 1) = a i := by
  have hentry : commDiag cycleDirac a i (i + 1) = 0 := by
    rw [h]
    rfl
  rw [commDiag_apply] at hentry
  have hD : cycleDirac i (i + 1) = 1 := by
    rw [cycleDirac_apply]
    exact if_pos (Or.inl rfl)
  rw [hD, one_mul, mul_one] at hentry
  exact sub_eq_zero.mp hentry

/-- **A commuting diagonal element is constant** at the cycle
seat: every value equals the value at `0`, by the successor
steps `0 -> 1 -> 2 -> 3`. -/
theorem eq_zero_of_commDiag_cycleDirac_eq_zero (a : Fin 4 → ℂ)
    (h : commDiag cycleDirac a = 0) (i : Fin 4) :
    a i = a 0 := by
  have s0 : a 1 = a 0 := step_eq_of_commDiag_cycleDirac_eq_zero a h 0
  have s1 : a 2 = a 1 := step_eq_of_commDiag_cycleDirac_eq_zero a h 1
  have s2 : a 3 = a 2 := step_eq_of_commDiag_cycleDirac_eq_zero a h 2
  fin_cases i
  · rfl
  · exact s0
  · exact s1.trans s0
  · exact s2.trans (s1.trans s0)

/-- **No commutant obstruction at the cycle seat**, at any
pair: a commuting element cannot separate two points, since
it is constant. -/
theorem not_hasCommutantObstruction_cycleDirac (i j : Fin 4) :
    ¬ HasCommutantObstruction cycleDirac i j := by
  rintro ⟨a, h0, hne⟩
  exact hne (by
    rw [eq_zero_of_commDiag_cycleDirac_eq_zero a h0 i,
      eq_zero_of_commDiag_cycleDirac_eq_zero a h0 j])

/-- **Finiteness at the seat (DIST-1 criterion).**
`connesDist cycleDirac i j < ⊤` for every pair, by DIST-1's
hard direction `connesDist_lt_top_of_no_obstruction` applied
to the seat's absence of obstruction. -/
theorem connesDist_cycleDirac_lt_top (i j : Fin 4) :
    connesDist cycleDirac i j < ⊤ :=
  connesDist_lt_top_of_no_obstruction cycleDirac
    (not_hasCommutantObstruction_cycleDirac i j)

/-- **Row 5 at the seat.** The pin's conditional finiteness
Prop holds for `cycleDirac` with its hypothesis discharged by
the seat's no-obstruction fact (the conditional itself is
DIST-1's `connesDistFiniteConditional_proved`). -/
theorem connesDistFiniteConditional_cycleDirac :
    ConnesDistFiniteConditional cycleDirac :=
  connesDistFiniteConditional_proved cycleDirac

/-! ## The two witness elements

Two diagonal elements with values in `{0, 1}` - the indicators
of the two semicircle arcs `{1, 2}` and `{2, 3}` - whose
commutators with `cycleDirac` are signed permutation matrices
(hence of operator norm `1`, proved in the next section).
Between them they separate every distinct pair of sites. -/

/-- **Witness A**: the arc indicator `(0, 1, 1, 0)`. -/
def witA : Fin 4 → ℂ := ![0, 1, 1, 0]

/-- **Witness B**: the arc indicator `(0, 0, 1, 1)`. -/
def witB : Fin 4 → ℂ := ![0, 0, 1, 1]

/-- **The commutator of witness A, as a table.** `commDiag
cycleDirac witA` is the signed permutation matrix with rows
`(0,1,0,0)`, `(-1,0,0,0)`, `(0,0,0,-1)`, `(0,0,1,0)`. -/
theorem commDiag_witA_eq :
    commDiag cycleDirac witA
      = Matrix.of ![![0, 1, 0, 0], ![-1, 0, 0, 0],
          ![0, 0, 0, -1], ![0, 0, 1, 0]] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [commDiag_apply, cycleDirac, witA] <;> norm_num

/-- **The commutator of witness B, as a table.** `commDiag
cycleDirac witB` is the signed permutation matrix with rows
`(0,0,0,1)`, `(0,0,1,0)`, `(0,-1,0,0)`, `(-1,0,0,0)`. -/
theorem commDiag_witB_eq :
    commDiag cycleDirac witB
      = Matrix.of ![![0, 0, 0, 1], ![0, 0, 1, 0],
          ![0, -1, 0, 0], ![-1, 0, 0, 0]] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [commDiag_apply, cycleDirac, witB] <;> norm_num

/-- **Norm at most `1` from a unitary identity.** If
`Mᴴ * M = 1` then `‖M‖ ≤ 1`: the C-star identity for the L2
operator norm gives `‖M‖ * ‖M‖ = ‖Mᴴ * M‖ = ‖1‖ = 1`, and a
nonnegative real whose square is `1` is at most `1`. -/
theorem norm_le_one_of_conjTranspose_mul_self_eq_one
    (M : Matrix (Fin 4) (Fin 4) ℂ)
    (h : Matrix.conjTranspose M * M = 1) : ‖M‖ ≤ 1 := by
  have hprod : ‖M‖ * ‖M‖ = 1 := by
    rw [← Matrix.l2_opNorm_conjTranspose_mul_self, h]
    exact norm_one
  by_contra hlt
  push_neg at hlt
  have hgt : (1 : ℝ) < ‖M‖ * ‖M‖ := by nlinarith [norm_nonneg M]
  rw [hprod] at hgt
  exact lt_irrefl _ hgt

/-- **Witness A's commutator is unitary**: `Mᴴ * M = 1` for
`M = commDiag cycleDirac witA`, by its signed-permutation
table. -/
theorem commDiag_witA_conjTranspose_mul_self :
    Matrix.conjTranspose (commDiag cycleDirac witA)
      * commDiag cycleDirac witA = 1 := by
  rw [commDiag_witA_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four,
      Matrix.conjTranspose] <;> norm_num

/-- **Witness B's commutator is unitary**: `Mᴴ * M = 1` for
`M = commDiag cycleDirac witB`, by its signed-permutation
table. -/
theorem commDiag_witB_conjTranspose_mul_self :
    Matrix.conjTranspose (commDiag cycleDirac witB)
      * commDiag cycleDirac witB = 1 := by
  rw [commDiag_witB_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four,
      Matrix.conjTranspose] <;> norm_num

/-- **Witness A's commutator has operator norm at most `1`**,
from its unitary identity. -/
theorem commDiag_witA_norm_le_one :
    ‖commDiag cycleDirac witA‖ ≤ 1 :=
  norm_le_one_of_conjTranspose_mul_self_eq_one _
    commDiag_witA_conjTranspose_mul_self

/-- **Witness B's commutator has operator norm at most `1`**,
from its unitary identity. -/
theorem commDiag_witB_norm_le_one :
    ‖commDiag cycleDirac witB‖ ≤ 1 :=
  norm_le_one_of_conjTranspose_mul_self_eq_one _
    commDiag_witB_conjTranspose_mul_self

/-- **Every distinct pair is separated by a named witness
with commutator norm at most `1` and point difference of norm
exactly `1`.** The case split is the full `Fin 4` table:
witness A covers the pairs its arc indicator separates,
witness B the rest. -/
theorem exists_wit_of_ne {i j : Fin 4} (h : i ≠ j) :
    ∃ a : Fin 4 → ℂ, ‖commDiag cycleDirac a‖ ≤ 1
      ∧ ‖a i - a j‖ = 1 := by
  fin_cases i <;> fin_cases j
  · exact (h rfl).elim
  · exact ⟨witA, commDiag_witA_norm_le_one, by simp [witA]⟩
  · exact ⟨witA, commDiag_witA_norm_le_one, by simp [witA]⟩
  · exact ⟨witB, commDiag_witB_norm_le_one, by simp [witB]⟩
  · exact ⟨witA, commDiag_witA_norm_le_one, by simp [witA]⟩
  · exact (h rfl).elim
  · exact ⟨witB, commDiag_witB_norm_le_one, by simp [witB]⟩
  · exact ⟨witA, commDiag_witA_norm_le_one, by simp [witA]⟩
  · exact ⟨witA, commDiag_witA_norm_le_one, by simp [witA]⟩
  · exact ⟨witB, commDiag_witB_norm_le_one, by simp [witB]⟩
  · exact (h rfl).elim
  · exact ⟨witA, commDiag_witA_norm_le_one, by simp [witA]⟩
  · exact ⟨witB, commDiag_witB_norm_le_one, by simp [witB]⟩
  · exact ⟨witA, commDiag_witA_norm_le_one, by simp [witA]⟩
  · exact ⟨witA, commDiag_witA_norm_le_one, by simp [witA]⟩
  · exact (h rfl).elim

/-- **Definiteness hypothesis at the seat, discharged:**
`ConnesCommSeparates cycleDirac` - the commutators of the
cycle operator separate every distinct pair of seat points,
by the explicit witnesses. -/
theorem connesCommSeparates_cycleDirac :
    ConnesCommSeparates cycleDirac := by
  intro i j h
  obtain ⟨a, ha1, had⟩ := exists_wit_of_ne h
  refine ⟨a, ha1, ?_⟩
  intro heq
  rw [heq, sub_self, norm_zero] at had
  norm_num at had

/-- **Definiteness at the seat.** `connesDist cycleDirac i j
= 0` forces `i = j`, by DIST-1's conditional discharge
`eq_of_connesDist_eq_zero_of_separates` with the seat's
separating fact. -/
theorem eq_of_connesDist_cycleDirac_eq_zero {i j : Fin 4}
    (h : connesDist cycleDirac i j = 0) : i = j :=
  eq_of_connesDist_eq_zero_of_separates cycleDirac
    connesCommSeparates_cycleDirac i j h

/-- **Row 4 at the seat.** The pin's conditional definiteness
Prop holds for `cycleDirac` with its hypothesis discharged by
the seat's separating fact (the conditional itself is
DIST-1's `connesDistDefiniteConditional_proved`). -/
theorem connesDistDefiniteConditional_cycleDirac :
    ConnesDistDefiniteConditional cycleDirac :=
  connesDistDefiniteConditional_proved cycleDirac

/-! ## The sharp upper bound: every point difference is at most
the commutator norm

For adjacent pairs the difference is a single commutator
entry. For the two opposite pairs it is a unit-vector pairing
`⟨u, [D, a] v⟩` with `u, v` the signed indicators of the even
and odd sites - the pairing extracts twice the difference
from vectors of norm `√2` each. -/

/-- **The pairing bound.** For any matrix `M` and vectors
`u, v`, the modulus of the pairing sum
`∑ k, conj (u k) * (M *ᵥ v) k` is at most
`‖M‖ * ‖u‖₂ * ‖v‖₂` - Cauchy-Schwarz plus the L2 operator
norm bound `Matrix.l2_opNorm_mulVec`. -/
theorem norm_sum_conj_mul_mulVec_le (M : Matrix (Fin 4) (Fin 4) ℂ)
    (u v : Fin 4 → ℂ) :
    ‖∑ k, (starRingEnd ℂ) (u k) * (M.mulVec v) k‖
      ≤ ‖M‖ * ‖WithLp.toLp 2 u‖ * ‖WithLp.toLp 2 v‖ := by
  have hCS := norm_inner_le_norm (𝕜 := ℂ)
    (WithLp.toLp 2 u : EuclideanSpace ℂ (Fin 4))
    ((EuclideanSpace.equiv (Fin 4) ℂ).symm (M.mulVec (WithLp.toLp 2 v)))
  have hOp := Matrix.l2_opNorm_mulVec M (WithLp.toLp 2 v)
  have hinner : ⟪WithLp.toLp 2 u,
        (EuclideanSpace.equiv (Fin 4) ℂ).symm
          (M.mulVec (WithLp.toLp 2 v))⟫_ℂ
      = ∑ k, (starRingEnd ℂ) (u k) * (M.mulVec v) k := by
    rw [PiLp.inner_apply]
    apply Finset.sum_congr rfl
    intro k _
    rw [RCLike.inner_apply]
    exact mul_comm _ _
  rw [hinner] at hCS
  calc ‖∑ k, (starRingEnd ℂ) (u k) * (M.mulVec v) k‖
      ≤ ‖WithLp.toLp 2 u‖
          * ‖(EuclideanSpace.equiv (Fin 4) ℂ).symm
              (M.mulVec (WithLp.toLp 2 v))‖ := hCS
    _ ≤ ‖WithLp.toLp 2 u‖ * (‖M‖ * ‖WithLp.toLp 2 v‖) :=
        mul_le_mul_of_nonneg_left hOp (norm_nonneg _)
    _ = ‖M‖ * ‖WithLp.toLp 2 u‖ * ‖WithLp.toLp 2 v‖ := by ring

/-- The even-site signed indicator `(1, 0, -1, 0)`. -/
def cycleU02 : Fin 4 → ℂ :=
  fun k => if k = 0 then 1 else if k = 2 then -1 else 0

/-- The odd-site indicator `(0, 1, 0, 1)`. -/
def cycleV02 : Fin 4 → ℂ :=
  fun k => if k = 1 then 1 else if k = 3 then 1 else 0

/-- The odd-site signed indicator `(0, 1, 0, -1)`. -/
def cycleU13 : Fin 4 → ℂ :=
  fun k => if k = 1 then 1 else if k = 3 then -1 else 0

/-- The even-site indicator `(1, 0, 1, 0)`. -/
def cycleV13 : Fin 4 → ℂ :=
  fun k => if k = 0 then 1 else if k = 2 then 1 else 0

/-- Each of the four probe vectors has L2 norm `√2` (two unit
coordinates). -/
theorem norm_cycleU02 :
    ‖WithLp.toLp 2 cycleU02‖ = Real.sqrt 2 := by
  rw [PiLp.norm_eq_of_L2]
  norm_num [cycleU02, Fin.sum_univ_four]

/-- See `norm_cycleU02`. -/
theorem norm_cycleV02 :
    ‖WithLp.toLp 2 cycleV02‖ = Real.sqrt 2 := by
  rw [PiLp.norm_eq_of_L2]
  norm_num [cycleV02, Fin.sum_univ_four]

/-- See `norm_cycleU02`. -/
theorem norm_cycleU13 :
    ‖WithLp.toLp 2 cycleU13‖ = Real.sqrt 2 := by
  rw [PiLp.norm_eq_of_L2]
  norm_num [cycleU13, Fin.sum_univ_four]

/-- See `norm_cycleU02`. -/
theorem norm_cycleV13 :
    ‖WithLp.toLp 2 cycleV13‖ = Real.sqrt 2 := by
  rw [PiLp.norm_eq_of_L2]
  norm_num [cycleV13, Fin.sum_univ_four]

/-- The pairing of the cycle commutator against the
even/odd probes extracts twice the opposite difference:
`∑ k, conj (cycleU02 k) * ([D, a] *ᵥ cycleV02) k
= 2 * (a 2 - a 0)`. -/
theorem sum_conj_cycleU02_mulVec_cycleV02 (a : Fin 4 → ℂ) :
    ∑ k, (starRingEnd ℂ) (cycleU02 k)
        * ((commDiag cycleDirac a).mulVec cycleV02) k
      = 2 * (a 2 - a 0) := by
  have hMv : ∀ k, (commDiag cycleDirac a).mulVec cycleV02 k
      = commDiag cycleDirac a k 1 + commDiag cycleDirac a k 3 := by
    intro k
    rw [Matrix.mulVec_apply_eq_sum, Fin.sum_univ_four]
    simp [cycleV02]
  rw [Fin.sum_univ_four, hMv 0, hMv 1, hMv 2, hMv 3]
  simp only [commDiag_apply]
  simp [cycleU02, cycleDirac]
  ring

/-- The pairing for the other opposite pair:
`∑ k, conj (cycleU13 k) * ([D, a] *ᵥ cycleV13) k
= 2 * (a 3 - a 1)`. -/
theorem sum_conj_cycleU13_mulVec_cycleV13 (a : Fin 4 → ℂ) :
    ∑ k, (starRingEnd ℂ) (cycleU13 k)
        * ((commDiag cycleDirac a).mulVec cycleV13) k
      = 2 * (a 3 - a 1) := by
  have hMv : ∀ k, (commDiag cycleDirac a).mulVec cycleV13 k
      = commDiag cycleDirac a k 0 + commDiag cycleDirac a k 2 := by
    intro k
    rw [Matrix.mulVec_apply_eq_sum, Fin.sum_univ_four]
    simp [cycleV13]
  rw [Fin.sum_univ_four, hMv 0, hMv 1, hMv 2, hMv 3]
  simp only [commDiag_apply]
  simp [cycleU13, cycleDirac]
  ring

/-- **Sharp bound, opposite pair `(0, 2)`.**
`‖a 0 - a 2‖ ≤ ‖[cycleDirac, a]‖`: the pairing bound with
the even/odd probes, whose norms contribute `√2 * √2 = 2`,
exactly the factor the pairing extracts. -/
theorem norm_sub_le_norm_commDiag_cycleDirac_zero_two
    (a : Fin 4 → ℂ) :
    ‖a 0 - a 2‖ ≤ ‖commDiag cycleDirac a‖ := by
  have h := norm_sum_conj_mul_mulVec_le (commDiag cycleDirac a)
    cycleU02 cycleV02
  rw [sum_conj_cycleU02_mulVec_cycleV02, norm_cycleU02,
    norm_cycleV02] at h
  rw [norm_mul, Complex.norm_two] at h
  have hsqrt : Real.sqrt 2 * Real.sqrt 2 = (2 : ℝ) :=
    Real.mul_self_sqrt (by norm_num)
  rw [mul_assoc, hsqrt] at h
  rw [norm_sub_rev (a 0) (a 2)]
  linarith

/-- **Sharp bound, opposite pair `(1, 3)`.** -/
theorem norm_sub_le_norm_commDiag_cycleDirac_one_three
    (a : Fin 4 → ℂ) :
    ‖a 1 - a 3‖ ≤ ‖commDiag cycleDirac a‖ := by
  have h := norm_sum_conj_mul_mulVec_le (commDiag cycleDirac a)
    cycleU13 cycleV13
  rw [sum_conj_cycleU13_mulVec_cycleV13, norm_cycleU13,
    norm_cycleV13] at h
  rw [norm_mul, Complex.norm_two] at h
  have hsqrt : Real.sqrt 2 * Real.sqrt 2 = (2 : ℝ) :=
    Real.mul_self_sqrt (by norm_num)
  rw [mul_assoc, hsqrt] at h
  rw [norm_sub_rev (a 1) (a 3)]
  linarith

/-- **Adjacent-pair bound from a single entry.** If the
`(i, j)` commutator entry is the point difference
`a j - a i` (as it is on every cycle edge), the difference is
bounded by the commutator norm (DIST-1's entry bound
`norm_apply_le_opNorm`). -/
theorem norm_sub_le_of_entry_eq (a : Fin 4 → ℂ) {i j : Fin 4}
    (he : commDiag cycleDirac a i j = a j - a i) :
    ‖a i - a j‖ ≤ ‖commDiag cycleDirac a‖ := by
  have hle := norm_apply_le_opNorm (commDiag cycleDirac a) i j
  rw [he] at hle
  rwa [norm_sub_rev] at hle

/-- **The sharp bound at the seat, all pairs.** For every
algebra element `a` and distinct points `i, j`,
`‖a i - a j‖ ≤ ‖[cycleDirac, a]‖`. The full `Fin 4` table:
adjacent pairs by their edge entry, opposite pairs by the
probe pairings. -/
theorem norm_sub_le_norm_commDiag_cycleDirac (a : Fin 4 → ℂ)
    {i j : Fin 4} (h : i ≠ j) :
    ‖a i - a j‖ ≤ ‖commDiag cycleDirac a‖ := by
  fin_cases i <;> fin_cases j
  · exact (h rfl).elim
  · apply norm_sub_le_of_entry_eq
    rw [commDiag_apply]
    simp [cycleDirac]
  · exact norm_sub_le_norm_commDiag_cycleDirac_zero_two a
  · apply norm_sub_le_of_entry_eq
    rw [commDiag_apply]
    simp [cycleDirac]
  · apply norm_sub_le_of_entry_eq
    rw [commDiag_apply]
    simp [cycleDirac]
  · exact (h rfl).elim
  · apply norm_sub_le_of_entry_eq
    rw [commDiag_apply]
    simp [cycleDirac]
  · exact norm_sub_le_norm_commDiag_cycleDirac_one_three a
  · rw [norm_sub_rev]
    exact norm_sub_le_norm_commDiag_cycleDirac_zero_two a
  · apply norm_sub_le_of_entry_eq
    rw [commDiag_apply]
    simp [cycleDirac]
  · exact (h rfl).elim
  · apply norm_sub_le_of_entry_eq
    rw [commDiag_apply]
    simp [cycleDirac]
  · apply norm_sub_le_of_entry_eq
    rw [commDiag_apply]
    simp [cycleDirac]
  · rw [norm_sub_rev]
    exact norm_sub_le_norm_commDiag_cycleDirac_one_three a
  · apply norm_sub_le_of_entry_eq
    rw [commDiag_apply]
    simp [cycleDirac]
  · exact (h rfl).elim

/-! ## The value theorem

The exact value at the seat is the DISCRETE distance: `1`
between any two distinct points. The upper bound is the sharp
bound of the previous section (every admissible element has
point differences at most its commutator norm, hence at most
`1`); the lower bound is the named witnesses (difference of
norm exactly `1` at commutator norm at most `1`). -/

/-- **THE VALUE THEOREM (exact form).** At the Fin 4 cycle
seat, `connesDist cycleDirac i j = 0` if `i = j` and `= 1` if
`i ≠ j` - the discrete distance, at the normalization of
`cycleDirac` (adjacency entries `1`). In particular the
opposite pair `(0, 2)`, whose cyclic distance is `2`, has
Connes distance `1`: the value is NOT a constant multiple of
the cyclic distance (see `not_exists_const_mul_cycDist4`). -/
theorem connesDist_cycleDirac_eq (i j : Fin 4) :
    connesDist cycleDirac i j = if i = j then 0 else 1 := by
  by_cases h : i = j
  · subst h
    rw [if_pos rfl]
    exact connesDist_self cycleDirac i
  · rw [if_neg h]
    apply le_antisymm
    · rw [connesDist_unfold]
      apply iSup_le
      intro a
      apply iSup_le
      intro ha
      rw [← ENNReal.ofReal_one]
      apply ENNReal.ofReal_le_ofReal
      exact (norm_sub_le_norm_commDiag_cycleDirac a h).trans ha
    · obtain ⟨a, ha1, had⟩ := exists_wit_of_ne h
      have hle := ofReal_norm_sub_le_connesDist cycleDirac a ha1 i j
      rw [had, ENNReal.ofReal_one] at hle
      exact hle

/-- **Positivity at distinct pairs** (with finiteness above,
this is the seat's separation in value form; the decision
brick GR-DIST-3 reads `DistSeparates` off these). -/
theorem connesDist_cycleDirac_pos_of_ne {i j : Fin 4}
    (h : i ≠ j) : 0 < connesDist cycleDirac i j := by
  rw [connesDist_cycleDirac_eq, if_neg h]
  exact zero_lt_one

/-- **No single constant makes the value proportional to the
cyclic distance (FINDING, at full rank).** There is no real
`K` with `connesDist cycleDirac i j = ENNReal.ofReal (K *
cycDist4 i j)` for all pairs: the adjacent pair `(0, 1)`
(forcing `K = 1`) and the opposite pair `(0, 2)` (forcing
`K = 1/2`) conflict. The pack's anticipated proportional
form is therefore FALSE at this seat for this operator; the
exact value is the discrete form proved above. -/
theorem not_exists_const_mul_cycDist4 :
    ¬ ∃ K : ℝ, ∀ i j : Fin 4,
      connesDist cycleDirac i j
        = ENNReal.ofReal (K * (cycDist4 i j : ℝ)) := by
  rintro ⟨K, hK⟩
  have hc01 : cycDist4 (0 : Fin 4) (1 : Fin 4) = 1 := by decide
  have hc02 : cycDist4 (0 : Fin 4) (2 : Fin 4) = 2 := by decide
  have h01 := hK 0 1
  have h02 := hK 0 2
  rw [connesDist_cycleDirac_eq, hc01] at h01
  rw [connesDist_cycleDirac_eq, hc02] at h02
  simp only [if_neg (by decide : (0 : Fin 4) ≠ 1),
    if_neg (by decide : (0 : Fin 4) ≠ 2)] at h01 h02
  simp only [Nat.cast_one, Nat.cast_ofNat] at h01 h02
  -- h01 : (1 : ENNReal) = ENNReal.ofReal (K * 1)
  -- h02 : (1 : ENNReal) = ENNReal.ofReal (K * 2)
  have hKpos : 0 < K := by
    have h1 : (0 : ℝ≥0∞) < ENNReal.ofReal (K * 1) := by
      rw [← h01]
      exact zero_lt_one
    rw [ENNReal.ofReal_pos] at h1
    simpa using h1
  have hK1 : ENNReal.ofReal K = 1 := by
    rw [mul_one] at h01
    exact h01.symm
  have hcontra : ENNReal.ofReal (K * 2) = 2 := by
    rw [ENNReal.ofReal_mul hKpos.le]
    rw [hK1]
    norm_num
  rw [hcontra] at h02
  norm_num at h02

/-- **Two-sided comparability with the cyclic distance**
(the pre-named PARTIAL seam's bounds, here proved alongside
the exact value, which is stronger): with `c₁ = 1/2` and
`c₂ = 1`, `0 < c₁ ≤ c₂`,
`ENNReal.ofReal (c₁ * cycDist4 i j) ≤ connesDist cycleDirac i j
≤ ENNReal.ofReal (c₂ * cycDist4 i j)` for every pair. -/
theorem connesDist_cycleDirac_comparability (i j : Fin 4) :
    ENNReal.ofReal ((1 / 2) * (cycDist4 i j : ℝ))
        ≤ connesDist cycleDirac i j
      ∧ connesDist cycleDirac i j
        ≤ ENNReal.ofReal (1 * (cycDist4 i j : ℝ)) := by
  by_cases h : i = j
  · subst h
    rw [connesDist_self]
    simp [(cycDist4_eq_zero_iff i i).mpr rfl]
  · obtain ⟨hb1, hb2⟩ := cycDist4_bounds_of_ne h
    rw [connesDist_cycleDirac_eq, if_neg h]
    constructor
    · rw [← ENNReal.ofReal_one]
      apply ENNReal.ofReal_le_ofReal
      have hc : (cycDist4 i j : ℝ) ≤ 2 := by exact_mod_cast hb2
      have h2 : (1 / 2 : ℝ) * (cycDist4 i j : ℝ)
          ≤ (1 / 2) * 2 :=
        mul_le_mul_of_nonneg_left hc (by norm_num)
      simpa using h2
    · rw [← ENNReal.ofReal_one]
      apply ENNReal.ofReal_le_ofReal
      have hc : (1 : ℝ) ≤ (cycDist4 i j : ℝ) := by
        exact_mod_cast hb1
      simpa using hc

/-- **Rescaling remark (labeled corollary, via DIST-1's
scaling law).** The discrete value is tied to the chosen
normalization exactly as the scaling law dictates: for
`c > 0`, `connesDist (c • cycleDirac) i j
= (ENNReal.ofReal c)⁻¹ * connesDist cycleDirac i j` - so the
rescaled seat's value is `(ENNReal.ofReal c)⁻¹` on distinct
pairs. The operator of this brick is the unrescaled one; no
renormalization was performed to change the value's form. -/
theorem connesDist_smul_cycleDirac (c : ℝ) (hc : 0 < c)
    (i j : Fin 4) :
    connesDist (c • cycleDirac) i j
      = (ENNReal.ofReal c)⁻¹ * connesDist cycleDirac i j :=
  connesDist_smul cycleDirac hc i j

end ThetLogos
