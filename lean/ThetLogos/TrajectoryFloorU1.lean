/-
# MQ3-4: the trajectory floor at the circle seat

Rung 4 of the M-Q3 continuum ladder
(`~/workspace/your_files/m-q3-scope-2026-11-08.md` §1 + §4):
clause (i)'s discharge at the one seat whose full finite
positivity stack stands T1 — the circle seat
`(haarProb Circle, circleRep)`.

**What is proved.** One explicit trajectory and one explicit
constant:

- `trajFloorU1 : ℕ → ℝ := fun N => 1 / ((N : ℝ) + 1) ^ 4`;
- `m = Real.exp (-192) > 0`;

with (4b) `AdmissibleTrajectory trajFloorU1` (the pin's
admissibility clauses, discharged one by one) and
(4c) `TrajectoryGapFloor (haarProb Circle) circleRep
circleRep_continuous zero_lt_one trajFloorU1 (Real.exp (-192))`
— the pin's floor clause **verbatim**, at the circle seat.

**Route (STATUS §1, frozen).** The floor is fed by the
Doeblin explicit per-N bound (`DoeblinGap`:
`transfer_spectrum_le_doeblin`): at every even `N ≥ 2` and
every real `β`, `doeblinDelta β = exp (-6 * actionBound β)`
is a `GapBound`, with `actionBound β = |β| * (32 * N^4)`.
That bound is unconditional — it consumes neither
`GapPackage` nor `TransferFormPos`. Inside it, compactness
of `transferOp` comes from `HDen`, and `HDen` is
**discharged at every `β`** by the landed `hden_all`
(`LatticeHdenSeat`, the explicit bounded density
`hdKernel`). So the package antecedent of
`TrajectoryGapFloor` is routed around by discharge of its
hard core: below, the floor's consequent is proved outright
at every even `N ≥ 2`, and the antecedent is never used.
No weakening of the floor's statement; no narrowing of the
trajectory class.

**Uniformity computation.** Along `trajFloorU1`,
`|βt N| * N^4 = N^4 / (N+1)^4 ≤ 1`, so
`6 * actionBound (βt N) ≤ 192` and
`doeblinDelta (βt N) ≥ exp (-192)` at every `N` — the per-N
Doeblin gaps, which at fixed `β > 0` decay like
`exp (-192 β N^4)` (the DoeblinGap header fence), uniformize
along this trajectory because `βt N ~ N^{-4}` cancels the
volume factor `N^4`. Faced, not hidden: the trajectory runs
to `β = 0`; admissibility fences out eventually-zero curves
only, and `βt` is everywhere strictly positive. The pin's
floor clause asks for exactly this statement; MQ3-5
(convergence along this trajectory) is where the
`βt → 0` shape is judged.

**K-MQ3-FLOOR: does NOT fire** — the U(1) floor holds along
the exhibited admissible trajectory, with rate
`δ_N ≥ exp (-192)`, i.e. `N * δ_N ≥ 2 * exp (-192)` at every
even `N ≥ 2`.

**NO CLAIM** — parts of any Clay statement closed by this
module: 0. Dials: 0/4; Dial 3 = 0 (no dial moves before
MQ3-6).
-/

import ThetLogos.Span3ScalingLimit
import ThetLogos.DoeblinGap
import ThetLogos.LatticeHdenSeat
import Mathlib.MeasureTheory.Measure.SeparableMeasure

namespace ThetLogos

open MeasureTheory

section TrajectoryFloorU1

/-! ## The exhibited trajectory and floor constant (4a) -/

/-- **The exhibited trajectory at the U(1) seat (MQ3-4, 4a):**
`βt N = 1 / (N + 1)^4`. Strictly positive at every `N`,
tending to `0` at the rate that cancels the Doeblin volume
factor `N^4`. -/
noncomputable def trajFloorU1 : ℕ → ℝ :=
  fun N => 1 / ((N : ℝ) + 1) ^ 4

/-- The exhibited floor constant is positive:
`exp (-192) > 0`. -/
theorem exp_neg_192_pos : 0 < Real.exp (-192) :=
  Real.exp_pos _

theorem trajFloorU1_pos (N : ℕ) : 0 < trajFloorU1 N := by
  unfold trajFloorU1
  positivity

/-! ## (4b) Admissibility, clause by clause -/

/-- **(4b) — `AdmissibleTrajectory trajFloorU1`, PROVED.**
Clause (i): `βt N ≥ 0` everywhere (it is strictly positive).
Clause (ii), the nondegeneracy fence: at every bound `M`,
the witness `N = 2 * (M + 1)` is even, `≥ M`, and carries
`βt N > 0`. -/
theorem admissibleTrajectory_trajFloorU1 :
    AdmissibleTrajectory trajFloorU1 := by
  refine ⟨fun N => (trajFloorU1_pos N).le, fun M => ?_⟩
  exact ⟨2 * (M + 1), by omega, ⟨M + 1, by ring⟩,
    trajFloorU1_pos _⟩

/-! ## The uniformity computation -/

/-- **The volume cancellation, per `N`:** along the
trajectory, `|βt N| * (32 * N^4) ≤ 32` — the `N^4` of the
action bound is cancelled by `βt N = 1 / (N+1)^4 ≤ 1 / N^4`
in the only direction needed, `N^4 ≤ (N+1)^4`. -/
theorem trajFloorU1_actionBound_le (N : ℕ) [NeZero N] :
    |trajFloorU1 N| * (32 * (N : ℝ) ^ 4) ≤ 32 := by
  have hβ : |trajFloorU1 N| = 1 / ((N : ℝ) + 1) ^ 4 :=
    abs_of_pos (trajFloorU1_pos N)
  have hN4 : (N : ℝ) ^ 4 ≤ ((N : ℝ) + 1) ^ 4 := by
    apply pow_le_pow_left₀ (Nat.cast_nonneg N)
    linarith [Nat.cast_nonneg (α := ℝ) N]
  rw [hβ]
  have hpos : (0 : ℝ) < ((N : ℝ) + 1) ^ 4 := by positivity
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hpos]
  nlinarith [hN4]

/-- **The Doeblin gap along the trajectory is floored:**
`exp (-192) ≤ doeblinDelta (βt N)` at every `N`. -/
theorem doeblinDelta_trajFloorU1_ge (N : ℕ) [NeZero N] :
    Real.exp (-192) ≤ doeblinDelta (N := N) (trajFloorU1 N) := by
  unfold doeblinDelta
  rw [actionBound_eq_volume]
  apply Real.exp_le_exp.mpr
  have h := trajFloorU1_actionBound_le N
  nlinarith [h]

/-! ## The per-N gap bound at the seat -/

/-- **A countable-indexed Hilbert basis of the OS space at
the circle seat**, at every `(N, β)`: the space is separable
(it is `Lp` over the finite-product circle slice space), so
the orthonormal set of `exists_hilbertBasis` is countable. -/
theorem exists_countable_hilbertBasis_osSpace_circle
    {N : ℕ} [NeZero N] (β : ℝ) :
    ∃ (ι : Type) (_ : Countable ι),
      Nonempty (HilbertBasis ι ℂ
        (osSpace (N := N) (haarProb Circle) circleRep β)) := by
  obtain ⟨w, b, hb⟩ := exists_hilbertBasis ℂ
    (osSpace (N := N) (haarProb Circle) circleRep β)
  refine ⟨w, ?_, ⟨b⟩⟩
  -- The index set of an orthonormal family in a separable
  -- space is countable: distinct basis vectors are at
  -- distance `√2`, so each can be assigned a distinct point
  -- of a fixed countable dense set within distance `1/2`.
  haveI := isProbabilityMeasure_sliceMeasure (N := N)
    (haarProb Circle) circleRep circleRep_continuous zero_lt_one β
  haveI : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  haveI : SecondCountableTopology
      (osSpace (N := N) (haarProb Circle) circleRep β) :=
    Lp.SecondCountableTopology
  haveI : TopologicalSpace.SeparableSpace
      (osSpace (N := N) (haarProb Circle) circleRep β) :=
    inferInstance
  obtain ⟨s, hs_count, hs_dense⟩ :=
    TopologicalSpace.SeparableSpace.exists_countable_dense
      (α := osSpace (N := N) (haarProb Circle) circleRep β)
  haveI : Countable s := hs_count
  have hchoice : ∀ i : w, ∃ y : s,
      dist (b i) (y : osSpace (N := N) (haarProb Circle)
        circleRep β) < 1 / 2 := by
    intro i
    have hmem : b i ∈ closure s := hs_dense (b i)
    rw [Metric.mem_closure_iff] at hmem
    obtain ⟨y, hy, hdist⟩ := hmem (1 / 2) (by norm_num)
    exact ⟨⟨y, hy⟩, hdist⟩
  choose f hf using hchoice
  have hdist_eq : ∀ i j : w, i ≠ j →
      dist (b i) (b j) = Real.sqrt 2 := by
    intro i j hij
    have hsq : ‖b i - b j‖ ^ 2 = 2 := by
      have hnorm_i : ‖b i‖ = 1 := b.orthonormal.1 i
      have hnorm_j : ‖b j‖ = 1 := b.orthonormal.1 j
      have hinner : inner ℂ (b i) (b j) = 0 :=
        b.orthonormal.2 hij
      rw [norm_sub_sq (𝕜 := ℂ), hinner, hnorm_i, hnorm_j]
      norm_num [RCLike.re_to_complex]
    rw [dist_eq_norm, ← Real.sqrt_sq (norm_nonneg _), hsq]
  have hf_inj : Function.Injective f := by
    intro i j hij
    by_contra hne
    have hcoerce : (f i : osSpace (N := N) (haarProb Circle)
        circleRep β) = (f j : osSpace (N := N) (haarProb Circle)
        circleRep β) := congrArg Subtype.val hij
    have hle : dist (b i) (b j)
        ≤ dist (b i) (f i : osSpace (N := N) (haarProb Circle)
            circleRep β)
          + dist (f j : osSpace (N := N) (haarProb Circle)
            circleRep β) (b j) := by
      calc dist (b i) (b j)
          ≤ dist (b i) (f i : osSpace (N := N) (haarProb Circle)
              circleRep β)
            + dist (f i : osSpace (N := N) (haarProb Circle)
              circleRep β) (b j) := dist_triangle _ _ _
        _ = dist (b i) (f i : osSpace (N := N) (haarProb Circle)
              circleRep β)
            + dist (f j : osSpace (N := N) (haarProb Circle)
              circleRep β) (b j) := by rw [hcoerce]
    have h1sqrt : (1 : ℝ) < Real.sqrt 2 := by
      rw [Real.lt_sqrt (by norm_num)]; norm_num
    have hlt : dist (b i) (b j) < 1 := by
      have hfj : dist (f j : osSpace (N := N) (haarProb Circle)
          circleRep β) (b j) < 1 / 2 := by
        rw [dist_comm]; exact hf j
      linarith [hf i, hfj, hle]
    rw [hdist_eq i j hne] at hlt
    linarith
  exact Function.Injective.countable hf_inj

/-- **The per-N gap bound at the seat, with the explicit
Doeblin value** — `transfer_spectrum_le_doeblin` at
`(haarProb Circle, circleRep)`, read through the definition
of `GapBound` (definitional at the seat, cf.
`Span3GapPinsU1.gapBound_iff_gapBoundU1`). Unconditional:
no `GapPackage`, no `TransferFormPos`; `HDen` is discharged
inside by `hden_all`. -/
theorem gapBound_trajFloorU1 {N : ℕ} [NeZero N]
    (hN2 : 2 ≤ N) (hN : Even N) :
    GapBound (haarProb Circle) circleRep circleRep_continuous
      (trajFloorU1 N) hN2
      (doeblinDelta (N := N) (trajFloorU1 N)) := by
  obtain ⟨ι, hι, ⟨b⟩⟩ :=
    exists_countable_hilbertBasis_osSpace_circle (N := N)
      (trajFloorU1 N)
  exact transfer_spectrum_le_doeblin (haarProb Circle)
    circleRep circleRep_continuous zero_lt_one hN2 hN
    (trajFloorU1 N) b

/-! ## (4c) The floor -/

/-- **(4c) — `TrajectoryGapFloor` at the circle seat,
PROVED for the exhibited trajectory and `m = exp (-192)`.**
The statement is the pin's clause verbatim. The proof
discharges the consequent outright at every even `N ≥ 2`
(`δ := doeblinDelta (βt N)`, normalized by
`doeblinDelta_le_one`, floored by
`doeblinDelta_trajFloorU1_ge` and `N ≥ 2`); the
`GapPackage` antecedent is not consumed — its hard core
`HDen` stands discharged at every `β` by `hden_all`, and
the Doeblin bound needs no `TransferFormPos`. -/
theorem trajectoryGapFloor_trajFloorU1 :
    TrajectoryGapFloor (haarProb Circle) circleRep
      circleRep_continuous zero_lt_one trajFloorU1
      (Real.exp (-192)) := by
  intro _hpack N _hN2inst hN2 hN
  refine ⟨doeblinDelta (N := N) (trajFloorU1 N),
    doeblinDelta_le_one _, gapBound_trajFloorU1 hN2 hN, ?_⟩
  have hδ := doeblinDelta_trajFloorU1_ge N
  have hδ0 : (0 : ℝ) ≤ doeblinDelta (N := N) (trajFloorU1 N) :=
    (doeblinDelta_pos _).le
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast (le_trans (by norm_num) hN2)
  calc Real.exp (-192)
      ≤ doeblinDelta (N := N) (trajFloorU1 N) := hδ
    _ ≤ (N : ℝ) * doeblinDelta (N := N) (trajFloorU1 N) := by
        have h := mul_le_mul_of_nonneg_right hN1 hδ0
        simpa using h

end TrajectoryFloorU1

end ThetLogos
