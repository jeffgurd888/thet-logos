/-
# MQ3-6: M-Q3 assembly — the unconditional instance at the circle seat

Rung 6 of the M-Q3 continuum ladder
(`~/workspace/your_files/m-q3-scope-2026-11-08.md` §1 + §4):
the five-part package of §1 assembled at the circle seat
`(haarProb Circle, circleRep, circleRep_continuous,
zero_lt_one)`, along MQ3-4's exhibited trajectory
`trajFloorU1`, with MQ3-4's floor constant
`m = Real.exp (-192)`.

**The five parts.** (1) `AdmissibleTrajectory trajFloorU1`
— LANDED in MQ3-4 (`admissibleTrajectory_trajFloorU1`),
cited. (2) `TrajectoryGapFloor … trajFloorU1 (exp (-192))`
— LANDED in MQ3-4 (`trajectoryGapFloor_trajFloorU1`),
cited, with `exp_neg_192_pos` for `m > 0`. (3) the limit
system `S = limitSystemMQ35` — LANDED in MQ3-5, cited.
(4) `CorrelationsConvergePointwise (haarProb Circle)
circleRep trajFloorU1 limitSystemMQ35` — LANDED in MQ3-5
(`correlationsConvergePointwise_trajFloorU1`), cited.
(5) THIS MODULE: an exhibited `os : OsterwalderSchraderAxioms`
with `LimitSystemIsOSSchwingerData limitSystemMQ35 os`,
and `LimitGapClustering limitSystemMQ35 (exp (-192))`
for MQ3-4's SAME `m` — neither weakened nor narrowed.

**On (5), first half — the pin's opacity, inherited and
LABELED.** As pinned (`Span3ScalingLimit`),
`LimitSystemIsOSSchwingerData S os` is the carrier equality
`os.schwinger.carrier = LimitCorrelationSystem` — a
definition-level, marker/type-level identification: the
bundle's E0–E4 fields are the S-3 pin's opaque `Prop`s and
this identification asserts NO analytic content about `S`.
The bundle exhibited below carries `True` in every opaque
field; the identification is `rfl`. This is the pin's own
shape ("its opacity inherited and labeled", scope §1/§4),
stated here at full rank so no reader mistakes it for more.

**On (5), second half — how the clustering is obtained.**
The scope prices the clustering as "transported from the
uniform finite clustering estimates inside MQ3-5's proof,
not re-proved". Faced honestly: MQ3-5's proof contains no
finite clustering estimate — its content is the β = 0
stabilization and the near/far weight comparison — and
`LimitGapClustering` is a statement about the limit
system's OWN values (`limitConnectedTwoPoint`). The proof
below therefore reads the clustering off the exhibited
system's computed values, which are MQ3-5's theorem
content: `limitSystemMQ35` takes values in `{0, 1} ⊆ ℂ`,
so its connected two-point function has norm `≤ 1` by case
split; and `insertionSeparation a b ≤ 2` (four coordinates,
each contributing `min (|d|, 1 - |d|) ≤ 1/2` for positions
in `[0, 1)`), so the constant `C = exp (2m)` at the SAME
`m = exp (-192)` gives `C * exp (-m * sep) ≥ 1`. The rate
is MQ3-4's `m` exactly; `S` is MQ3-5's exactly.

**Headline.** `unconditionalInstance_trajFloorU1`: the
five-part package as one theorem, in the pin's exact
consequent shape at this seat/trajectory/m.

**Kills.** No kill is armed on this rung (assembly; its
failure modes are MQ3-4's K-MQ3-FLOOR and MQ3-5's
K-MQ3-CONV, both silent). **K-MQ3-PROXY STANDS:** this
module does not present the assembly as Dial-3 motion in
any form; Dial 3's movement is the parent's call on
landing, with the mandatory companion sentence attached:
parts of the official statement closed remain 0 even then.

**NO CLAIM** beyond the stated tier — parts of any Clay
statement closed by this module: 0.

**LANE STATE (2026-11-09, at first commit): UNVERIFIED
DRAFT.** This module has NOT been elaborated: the lane's
targeted build produced no oleans in 20 minutes under a
three-build contention wave and was paused by the lane
guardrail tripwire (two-lane discipline, 2026-11-09);
the lane re-serialized awaiting the parent's clear, with
the DET-1 staged rerun and integration builds holding the
machine. Every proof in this file is a paper draft until a
targeted build + `#print axioms` say otherwise. The
obstruction is scheduling, not mathematics: no statement
in this file has been weakened, and no elaboration error
has been observed (none has been reached). Resume:
gate-check, `lake build
ThetLogos.CircleSeatScalingAssembly`, fix what the kernel
reports, `#print axioms unconditionalInstance_trajFloorU1`.
-/

import ThetLogos.CircleSeatConvergence

namespace ThetLogos

open MeasureTheory

section CircleSeatScalingAssembly

/-! ## §5a. The exhibited OS bundle and the identification -/

/-- **The exhibited OS bundle (MQ3-6, part 5a).** Its
Schwinger marker's carrier IS `LimitCorrelationSystem`;
every opaque E0–E4 field carries `True`. The bundle is
exhibited so that the pin's carrier identification holds
definitionally — see the module header for the labeled
opacity of exactly this step. -/
def osBundleMQ36 : OsterwalderSchraderAxioms where
  schwinger := ⟨LimitCorrelationSystem⟩
  temperedness := True
  euclideanCovariant := True
  reflectionPositivity := True
  symmetry := True
  clustering := True

/-- **Part (5a) — the carrier identification, PROVED.**
`LimitSystemIsOSSchwingerData limitSystemMQ35 osBundleMQ36`
holds by `rfl`: it is the pin's definition-level carrier
equality `os.schwinger.carrier = LimitCorrelationSystem`,
with the S-3 pin's opacity inherited and labeled (module
header). No analytic content about `limitSystemMQ35` is
asserted or obtained here. -/
theorem limitSystemIsOSSchwingerData_limitSystemMQ35 :
    LimitSystemIsOSSchwingerData limitSystemMQ35 osBundleMQ36 :=
  rfl

/-! ## §5b. Clustering of the exhibited limit system -/

/-- Positions lie in `[0, 1)`, so a coordinate difference
has absolute value `< 1` (cast to ℝ). -/
theorem pos_diff_abs_lt_one (a b : LoopInsertion) (μ : Fin 4) :
    |(a.pos μ : ℝ) - (b.pos μ : ℝ)| < 1 := by
  have ha0 : (0 : ℝ) ≤ (a.pos μ : ℝ) := by
    exact_mod_cast a.pos_nonneg μ
  have ha1 : (a.pos μ : ℝ) < 1 := by
    exact_mod_cast a.pos_lt_one μ
  have hb0 : (0 : ℝ) ≤ (b.pos μ : ℝ) := by
    exact_mod_cast b.pos_nonneg μ
  have hb1 : (b.pos μ : ℝ) < 1 := by
    exact_mod_cast b.pos_lt_one μ
  rw [abs_lt]
  constructor <;> linarith

/-- One coordinate's contribution to the separation is at
most `1 / 2`: `min (x, 1 - x) ≤ 1 / 2` for `x = |d|`. -/
theorem insertionSeparation_term_le_half (a b : LoopInsertion)
    (μ : Fin 4) :
    min (|(a.pos μ : ℝ) - (b.pos μ : ℝ)|)
        (1 - |(a.pos μ : ℝ) - (b.pos μ : ℝ)|) ≤ 1 / 2 := by
  rcases le_total (|(a.pos μ : ℝ) - (b.pos μ : ℝ)|)
      (1 - |(a.pos μ : ℝ) - (b.pos μ : ℝ)|) with h | h
  · rw [min_eq_left h]
    have h1 := pos_diff_abs_lt_one a b μ
    have h2 := abs_nonneg ((a.pos μ : ℝ) - (b.pos μ : ℝ))
    linarith
  · rw [min_eq_right h]
    have h2 := abs_nonneg ((a.pos μ : ℝ) - (b.pos μ : ℝ))
    linarith

/-- The separation is nonnegative: each coordinate
contributes `min (|d|, 1 - |d|) ≥ 0`. -/
theorem insertionSeparation_nonneg (a b : LoopInsertion) :
    0 ≤ insertionSeparation a b := by
  unfold insertionSeparation
  apply Finset.sum_nonneg
  intro μ _
  have h1 := pos_diff_abs_lt_one a b μ
  have h2 := abs_nonneg ((a.pos μ : ℝ) - (b.pos μ : ℝ))
  exact le_min h2 (by linarith)

/-- The separation is at most `2`: four coordinates, each
contributing at most `1 / 2`. -/
theorem insertionSeparation_le_two (a b : LoopInsertion) :
    insertionSeparation a b ≤ 2 := by
  unfold insertionSeparation
  refine le_trans (Finset.sum_le_sum
    (fun μ _ => insertionSeparation_term_le_half a b μ)) ?_
  simp [Finset.sum_const, Finset.card_univ]
  norm_num

/-- The exhibited limit system takes values in `{0, 1}`:
by its defining case split (MQ3-5). -/
theorem limitSystemMQ35_eq_zero_or_one (k : ℕ)
    (c : Fin k → LoopInsertion) :
    limitSystemMQ35 k c = 0 ∨ limitSystemMQ35 k c = 1 := by
  unfold limitSystemMQ35
  split_ifs with h
  · exact Or.inr rfl
  · exact Or.inl rfl

/-- The exhibited limit system's connected two-point
function has norm at most `1`: each of its three values
is `0` or `1`, so the difference is in `{-1, 0, 1}`. -/
theorem norm_limitConnectedTwoPoint_limitSystemMQ35_le_one
    (a b : LoopInsertion) :
    ‖limitConnectedTwoPoint limitSystemMQ35 a b‖ ≤ 1 := by
  obtain h2 | h2 := limitSystemMQ35_eq_zero_or_one 2
    (fun i : Fin 2 => if i = 0 then a else b) <;>
  obtain h1a | h1a := limitSystemMQ35_eq_zero_or_one 1
    (fun _ => a) <;>
  obtain h1b | h1b := limitSystemMQ35_eq_zero_or_one 1
    (fun _ => b) <;>
  simp [limitConnectedTwoPoint, h2, h1a, h1b]

/-- **Part (5b) — limit gap clustering at MQ3-4's SAME
`m = exp (-192)`, PROVED.** With `C = exp (2 * m) ≥ 0`:
`C * exp (-m * sep) ≥ exp (2m - m * sep) ≥ exp 0 = 1 ≥
‖limitConnectedTwoPoint limitSystemMQ35 a b‖`, using
`sep ≤ 2` and `m ≥ 0`. The rate is not weakened and the
system is not narrowed: this is MQ3-5's exhibited system
at MQ3-4's exhibited floor constant. -/
theorem limitGapClustering_limitSystemMQ35 :
    LimitGapClustering limitSystemMQ35 (Real.exp (-192)) := by
  refine ⟨Real.exp (2 * Real.exp (-192)), Real.exp_nonneg _, ?_⟩
  intro a b
  have hm : (0 : ℝ) ≤ Real.exp (-192) := (Real.exp_pos _).le
  have hmul : Real.exp (-192) * insertionSeparation a b
      ≤ Real.exp (-192) * 2 :=
    mul_le_mul_of_nonneg_left (insertionSeparation_le_two a b) hm
  have hone : (1 : ℝ) ≤ Real.exp (2 * Real.exp (-192))
      * Real.exp (-(Real.exp (-192)) * insertionSeparation a b) := by
    calc (1 : ℝ) = Real.exp 0 := (Real.exp_zero).symm
      _ ≤ Real.exp (2 * Real.exp (-192)
            + (-(Real.exp (-192))) * insertionSeparation a b) := by
          apply Real.exp_le_exp.mpr
          linarith
      _ = Real.exp (2 * Real.exp (-192))
            * Real.exp (-(Real.exp (-192))
              * insertionSeparation a b) := Real.exp_add _ _
  exact le_trans
    (norm_limitConnectedTwoPoint_limitSystemMQ35_le_one a b) hone

/-! ## The assembly -/

/-- **MQ3-6 HEADLINE — the unconditional instance of the
scaling-limit pin at the circle seat.** The five-part
package of the scope's §1, at the seat `(haarProb Circle,
circleRep)`, the trajectory `trajFloorU1`, and the floor
`m = Real.exp (-192)`, in the pin's exact dialect
(`Span3ScalingLimit.ScalingLimitOfLattice`'s consequent
shape, with clause (i)'s two discharges conjoined):

- (1) `AdmissibleTrajectory trajFloorU1` — MQ3-4, cited;
- (2) `TrajectoryGapFloor … trajFloorU1 (exp (-192))` and
  `0 < exp (-192)` — MQ3-4, cited;
- (3)–(4) the exhibited `S = limitSystemMQ35` with
  `CorrelationsConvergePointwise … trajFloorU1 S` —
  MQ3-5, cited;
- (5) `LimitSystemIsOSSchwingerData S os` for the
  exhibited `osBundleMQ36` (definition-level carrier
  identification, the pin's opacity inherited and labeled)
  and `LimitGapClustering S (exp (-192))` at the SAME `m`
  — this module.

NO CLAIM beyond this tier: parts of any Clay statement
closed by this theorem: 0. -/
theorem unconditionalInstance_trajFloorU1 :
    AdmissibleTrajectory trajFloorU1 ∧
    TrajectoryGapFloor (haarProb Circle) circleRep
        circleRep_continuous zero_lt_one trajFloorU1
        (Real.exp (-192)) ∧
    0 < Real.exp (-192) ∧
    ∃ S : LimitCorrelationSystem, ∃ os : OsterwalderSchraderAxioms,
      CorrelationsConvergePointwise (haarProb Circle) circleRep
          trajFloorU1 S ∧
      LimitSystemIsOSSchwingerData S os ∧
      LimitGapClustering S (Real.exp (-192)) :=
  ⟨admissibleTrajectory_trajFloorU1,
    trajectoryGapFloor_trajFloorU1,
    exp_neg_192_pos,
    limitSystemMQ35, osBundleMQ36,
    correlationsConvergePointwise_trajFloorU1,
    limitSystemIsOSSchwingerData_limitSystemMQ35,
    limitGapClustering_limitSystemMQ35⟩

end CircleSeatScalingAssembly

end ThetLogos
