import ThetLogos.BSDRankPin
import Mathlib.NumberTheory.Height.EllipticCurve
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.Tactic

namespace ThetLogos

open Filter
open scoped Topology

/-!
# ThetLogos.BSDCanonicalHeight — the Néron–Tate canonical height for `E2`, and the regulator object

Source: the BSD rung-2 scoping memo §2, brick **B2-2**
(`scoping-bsd-rung-2-2026-10-29.md`). Design authority: rung 1
(`ThetLogos.BSDRankPin`) and the refined pin (`ThetLogos.BSDRefinedPin`).

**What this file IS.** The Néron–Tate canonical height `canonHeight` on
`E2(ℚ)` (`E2 : y² = x³ - 2`), defined honestly as the limit of
`naiveHeight (2^n • P) / 4^n` from Mathlib's naïve height, with
convergence proved from Mathlib's `approx_parallelogram_law` (the
standard duplication construction). On top of the definition: the
height of `0`, the doubling law, evenness, the exact parallelogram law
for `canonHeight`, and quadraticity on the cyclic subgroup generated
by `P35 = (3, 5)` (natural and integer multiples). From these, the
regulator **object** `regE2 := canonHeight P35` — an exact in-tree
real, class (a) in the scoping memo's ingredient ledger.

**The definition needs no basis.** The limit is taken pointwise, one
point at a time, from the duplication estimate alone; no finite
generation, no Mordell–Weil basis, and no rank hypothesis enters the
definition or any proof in this file. (The memo's kill condition on
this point does not fire.)

**Normalization (probed, exact).** The 2026-10-27 study's height is
`h(x) = log max(|num x|, |den x|)`. Mathlib's `naiveHeight` at an
affine point is `logHeight₁` of its `x`-coordinate, and
`Rat.logHeight₁_eq_log_max` says `logHeight₁ x = log (max x.num.natAbs
x.den)` — the same normalization, exactly, not up to a bounded error.
This is recorded in-tree as `naiveHeight_E2_some`. The memo's
normalization kill condition does not fire.

**What this file is NOT — the board fences, on the face.**
- **Not the official statement.** The Clay prize statement is the rank
  equality (rung 1's `BSDRankEquality`). The refined formula this
  brick serves is Wiles's Remark 1. Parts of the official BSD
  statement closed by this module: **0**. NO CLAIM.
- **Not the regulator's value.** `regE2` is the object; its value
  `1.3496 ± 0.001` is a class-(c) numeric hypothesis owned by the
  refined pin (`E2RegulatorValue`), not proved or quoted here.
- **Not the identification of `regE2` with *the* regulator.** That
  identification is Seam B4, carried below as the labeled hypothesis
  `RegulatorBasisSeam`, proved nowhere in this file.

**Seam B4 (named by the scoping memo).** Identifying `regE2` with
*the* regulator of `E2` presupposes `{P35}` is a Mordell–Weil basis
mod torsion: `algebraicRank E2` is *exactly* `1` and `P35` is not a
proper multiple. In-tree we own only rank `≥ 1` (rung 1, modulo the
shared Nagell–Lutz seam and Mordell–Weil finiteness); the `≤ 1` half
is a **recorded value** — the 2026-10-27 study flags that no pass has
done the `≤` half by hand. `RegulatorBasisSeam` states exactly the
presupposition, in the tree's vocabulary as far as it reaches, and is
carried as the labeled antecedent wherever this line says "Reg".

Honesty tiers in this file:
- **T1 (proved):** everything with a proof term below — the
  definition's convergence, the height laws, the quadraticity on
  `⟨P35⟩`.
- **T5 (statement, unproved by design):** `RegulatorBasisSeam` — a
  `def` stating a `Prop`, deliberately left unproved.

Status: NO CLAIM on BSD. Parts of the official statement closed: 0.
-/

/-! ## The parallelogram constant for `E2` -/

/-- The constant in Mathlib's approximate parallelogram law for `E2`,
chosen once. Any valid constant would do; the proofs below use only
`heightBound_spec` and `heightBound_nonneg`. -/
noncomputable def heightBound : ℝ :=
  Classical.choose (WeierstrassCurve.Affine.approx_parallelogram_law E2.toAffine)

theorem heightBound_spec (P Q : E2.toAffine.Point) :
    |(P + Q).naiveHeight + (P - Q).naiveHeight
      - 2 * (P.naiveHeight + Q.naiveHeight)| ≤ heightBound :=
  Classical.choose_spec
    (WeierstrassCurve.Affine.approx_parallelogram_law E2.toAffine) P Q

/-- The naïve height of the point at infinity is `0` (its
representative is `![1, 0]`, and `logHeight₁ 1 = 0`). -/
theorem naiveHeight_E2_zero : (0 : E2.toAffine.Point).naiveHeight = 0 := by
  rw [WeierstrassCurve.Affine.Point.naiveHeight_eq_logHeight₁,
    WeierstrassCurve.Affine.Point.xRep_zero]
  simp

/-- **The normalization, on the face.** Mathlib's naïve height at an
affine point `(x, y)` of `E2` is `log (max x.num.natAbs x.den)` — the
2026-10-27 study's `h = log max(|num x|, |den x|)`, exactly. -/
theorem naiveHeight_E2_some {x y : ℚ} (h : E2.toAffine.Nonsingular x y) :
    (WeierstrassCurve.Affine.Point.some x y h).naiveHeight
      = Real.log (max x.num.natAbs x.den) := by
  rw [WeierstrassCurve.Affine.Point.naiveHeight_eq_logHeight₁,
    WeierstrassCurve.Affine.Point.xRep_some, Rat.logHeight₁_eq_log_max]
  simp

theorem heightBound_nonneg : 0 ≤ heightBound := by
  have h := heightBound_spec 0 0
  simp only [add_zero, sub_self, naiveHeight_E2_zero, mul_zero,
    abs_zero] at h
  exact h

/-! ## The duplication estimate and the defining sequence -/

/-- The duplication estimate: `|h(2P) − 4h(P)| ≤ C`, the approximate
parallelogram law at `Q = P`. This is the one estimate the whole
construction iterates. -/
theorem abs_naiveHeight_two_nsmul_sub (P : E2.toAffine.Point) :
    |(2 • P).naiveHeight - 4 * P.naiveHeight| ≤ heightBound := by
  have h := heightBound_spec P P
  rw [sub_self, naiveHeight_E2_zero, add_zero, ← two_nsmul] at h
  have heq : (2 • P).naiveHeight - 2 * (P.naiveHeight + P.naiveHeight)
      = (2 • P).naiveHeight - 4 * P.naiveHeight := by ring
  rwa [heq] at h

/-- The duplication sequence whose limit is the canonical height:
`a n = h(2^n • P) / 4^n`. Purely pointwise — no basis, no finite
generation. -/
noncomputable def canonSeq (P : E2.toAffine.Point) (n : ℕ) : ℝ :=
  (2 ^ n • P).naiveHeight / 4 ^ n

/-- The step bound: consecutive terms of the duplication sequence
differ by at most `C / 4^n` (the duplication estimate at `2^n • P`,
rescaled). -/
theorem canonSeq_succ_sub_abs_le (P : E2.toAffine.Point) (n : ℕ) :
    |canonSeq P (n + 1) - canonSeq P n| ≤ heightBound / 4 ^ n := by
  have hstep : 2 ^ (n + 1) • P = 2 • (2 ^ n • P) := by
    rw [pow_succ]
    exact mul_nsmul P (2 ^ n) 2
  have key : canonSeq P (n + 1) - canonSeq P n
      = ((2 • (2 ^ n • P)).naiveHeight - 4 * (2 ^ n • P).naiveHeight)
        / 4 ^ (n + 1) := by
    have h4n : (4 : ℝ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
    have h4 : (4 : ℝ) ^ (n + 1) ≠ 0 := pow_ne_zero _ (by norm_num)
    simp only [canonSeq, hstep]
    rw [pow_succ]
    field_simp
  rw [key, abs_div,
    abs_of_pos (pow_pos (show (0 : ℝ) < 4 by norm_num) (n + 1))]
  calc |(2 • (2 ^ n • P)).naiveHeight - 4 * (2 ^ n • P).naiveHeight|
        / 4 ^ (n + 1)
      ≤ heightBound / 4 ^ (n + 1) :=
        div_le_div_of_nonneg_right (abs_naiveHeight_two_nsmul_sub (2 ^ n • P))
          (pow_nonneg (by norm_num) (n + 1))
    _ ≤ heightBound / 4 ^ n :=
        div_le_div_of_nonneg_left heightBound_nonneg
          (pow_pos (by norm_num) n)
          (pow_le_pow_right₀ (by norm_num) (Nat.le_succ n))

/-- The duplication sequence is Cauchy: its successive differences are
dominated by the summable geometric sequence `C · (1/4)^n`. -/
theorem canonSeq_cauchy (P : E2.toAffine.Point) : CauchySeq (canonSeq P) := by
  apply cauchySeq_of_summable_dist
  refine Summable.of_norm_bounded (g := fun n => heightBound * (1 / 4) ^ n)
    ?_ ?_
  · exact (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  · intro n
    rw [Real.norm_eq_abs, abs_of_nonneg dist_nonneg, Real.dist_eq,
      Nat.succ_eq_add_one, abs_sub_comm]
    calc |canonSeq P (n + 1) - canonSeq P n|
        ≤ heightBound / 4 ^ n := canonSeq_succ_sub_abs_le P n
      _ = heightBound * (1 / 4) ^ n := by
          rw [div_pow, one_pow, mul_one_div]

/-! ## The canonical height -/

/-- **The Néron–Tate canonical height** of a point of `E2(ℚ)`: the
limit of the duplication sequence `canonSeq P`. Defined pointwise
from the naïve height alone; it presupposes no finite generation and
no basis (see the module header). -/
noncomputable def canonHeight (P : E2.toAffine.Point) : ℝ :=
  Classical.choose (cauchySeq_tendsto_of_complete (canonSeq_cauchy P))

theorem canonHeight_tendsto (P : E2.toAffine.Point) :
    Tendsto (canonSeq P) atTop (𝓝 (canonHeight P)) :=
  Classical.choose_spec (cauchySeq_tendsto_of_complete (canonSeq_cauchy P))

theorem canonHeight_zero : canonHeight 0 = 0 := by
  have hseq : canonSeq 0 = fun _ => 0 := by
    funext n
    simp [canonSeq, naiveHeight_E2_zero]
  have h1 : Tendsto (canonSeq 0) atTop (𝓝 0) := by
    rw [hseq]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique (canonHeight_tendsto 0) h1

/-- The doubling law, by reindexing the defining limit:
`ĥ(2P) = 4 ĥ(P)`. -/
theorem canonHeight_two_nsmul (P : E2.toAffine.Point) :
    canonHeight (2 • P) = 4 * canonHeight P := by
  have hseq : ∀ n : ℕ, canonSeq (2 • P) n = 4 * canonSeq P (n + 1) := by
    intro n
    have hsmul : 2 ^ n • (2 • P) = 2 ^ (n + 1) • P := by
      rw [pow_succ, mul_comm (2 ^ n) 2]
      exact (mul_nsmul P 2 (2 ^ n)).symm
    have h4 : (4 : ℝ) ^ (n + 1) ≠ 0 := pow_ne_zero _ (by norm_num)
    have h4n : (4 : ℝ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
    simp only [canonSeq, hsmul]
    rw [pow_succ]
    field_simp
    ring
  have hlim : Tendsto (fun n => 4 * canonSeq P (n + 1)) atTop
      (𝓝 (4 * canonHeight P)) :=
    ((canonHeight_tendsto P).comp (tendsto_add_atTop_nat 1)).const_mul 4
  have hlim2 : Tendsto (canonSeq (2 • P)) atTop (𝓝 (4 * canonHeight P)) := by
    have hfun : canonSeq (2 • P) = fun n => 4 * canonSeq P (n + 1) :=
      funext hseq
    rwa [hfun]
  exact tendsto_nhds_unique (canonHeight_tendsto (2 • P)) hlim2

/-- Evenness: the naïve height sees only the `x`-coordinate
(`xRep_neg`), so the limit does too. -/
theorem canonHeight_neg (P : E2.toAffine.Point) :
    canonHeight (-P) = canonHeight P := by
  have hseq : canonSeq (-P) = canonSeq P := by
    funext n
    have h1 : 2 ^ n • (-P) = (-(2 ^ n • P) : E2.toAffine.Point) :=
      smul_neg (2 ^ n) P
    simp only [canonSeq, h1,
      WeierstrassCurve.Affine.Point.naiveHeight_eq_logHeight,
      WeierstrassCurve.Affine.Point.xRep_neg]
  have h1 := canonHeight_tendsto P
  rw [← hseq] at h1
  exact tendsto_nhds_unique (canonHeight_tendsto (-P)) h1

/-! ## The exact parallelogram law, and quadraticity on `⟨P35⟩` -/

/-- **The exact parallelogram law for `canonHeight`.** At level `n`
the approximate law bounds the defect of the rescaled expression by
`C / 4^n`; the defect tends to `0`, so the limit height satisfies the
law exactly. -/
theorem canonHeight_parallelogram (P Q : E2.toAffine.Point) :
    canonHeight (P + Q) + canonHeight (P - Q)
      = 2 * canonHeight P + 2 * canonHeight Q := by
  have hsum : Tendsto
      (fun n => canonSeq (P + Q) n + canonSeq (P - Q) n) atTop
      (𝓝 (canonHeight (P + Q) + canonHeight (P - Q))) :=
    (canonHeight_tendsto (P + Q)).add (canonHeight_tendsto (P - Q))
  have hmul : Tendsto
      (fun n => 2 * (canonSeq P n + canonSeq Q n)) atTop
      (𝓝 (2 * (canonHeight P + canonHeight Q))) :=
    Tendsto.const_mul 2
      ((canonHeight_tendsto P).add (canonHeight_tendsto Q))
  have hlim : Tendsto
      (fun n => canonSeq (P + Q) n + canonSeq (P - Q) n
        - 2 * (canonSeq P n + canonSeq Q n)) atTop
      (𝓝 (canonHeight (P + Q) + canonHeight (P - Q)
        - 2 * (canonHeight P + canonHeight Q))) :=
    hsum.sub hmul
  have hbound : ∀ n : ℕ, |canonSeq (P + Q) n + canonSeq (P - Q) n
      - 2 * (canonSeq P n + canonSeq Q n)| ≤ heightBound * (1 / 4) ^ n := by
    intro n
    have h := heightBound_spec (2 ^ n • P) (2 ^ n • Q)
    have h2 : (2 ^ n • P) + (2 ^ n • Q) = 2 ^ n • (P + Q) :=
      (smul_add (2 ^ n) P Q).symm
    have h3 : (2 ^ n • P) - (2 ^ n • Q) = 2 ^ n • (P - Q) :=
      (smul_sub (2 ^ n) P Q).symm
    rw [h2, h3] at h
    have heq : canonSeq (P + Q) n + canonSeq (P - Q) n
        - 2 * (canonSeq P n + canonSeq Q n)
        = ((2 ^ n • (P + Q)).naiveHeight + (2 ^ n • (P - Q)).naiveHeight
          - 2 * ((2 ^ n • P).naiveHeight + (2 ^ n • Q).naiveHeight))
          / 4 ^ n := by
      have h4 : (4 : ℝ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
      simp only [canonSeq]
      field_simp
    rw [heq, abs_div,
      abs_of_pos (pow_pos (show (0 : ℝ) < 4 by norm_num) n)]
    calc |(2 ^ n • (P + Q)).naiveHeight + (2 ^ n • (P - Q)).naiveHeight
          - 2 * ((2 ^ n • P).naiveHeight + (2 ^ n • Q).naiveHeight)|
          / 4 ^ n
        ≤ heightBound / 4 ^ n :=
          div_le_div_of_nonneg_right h (pow_nonneg (by norm_num) n)
      _ = heightBound * (1 / 4) ^ n := by
          rw [div_pow, one_pow, mul_one_div]
  have hzero : Tendsto
      (fun n => |canonSeq (P + Q) n + canonSeq (P - Q) n
        - 2 * (canonSeq P n + canonSeq Q n)|) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => abs_nonneg _) hbound
    have hgt := (tendsto_pow_atTop_nhds_zero_of_lt_one
      (show (0 : ℝ) ≤ 1 / 4 by norm_num)
      (show (1 / 4 : ℝ) < 1 by norm_num)).const_mul heightBound
    simpa using hgt
  have habs := hlim.abs
  have hE := tendsto_nhds_unique habs hzero
  rw [abs_eq_zero] at hE
  linarith [hE]

/-- **Quadraticity on the cyclic subgroup generated by `P35`**,
natural multiples: `ĥ(m • P35) = m² ĥ(P35)`. Two-step induction
through the exact parallelogram law — the standard proof, at exactly
the point the refined pin's assembly consumes. -/
theorem canonHeight_nsmul_P35 (m : ℕ) :
    canonHeight (m • P35) = (m : ℝ) ^ 2 * canonHeight P35 := by
  have key : ∀ m : ℕ, canonHeight (m • P35) = (m : ℝ) ^ 2 * canonHeight P35
      ∧ canonHeight ((m + 1) • P35)
        = ((m + 1 : ℕ) : ℝ) ^ 2 * canonHeight P35 := by
    intro m
    induction m with
    | zero =>
      constructor
      · simp [canonHeight_zero]
      · simp
    | succ k ih =>
      obtain ⟨ih0, ih1⟩ := ih
      refine ⟨ih1, ?_⟩
      have hpar := canonHeight_parallelogram ((k + 1) • P35) P35
      have hadd : (k + 1) • P35 + P35 = (k + 1 + 1) • P35 :=
        (succ_nsmul P35 (k + 1)).symm
      have hsub : (k + 1) • P35 - P35 = k • P35 := by
        rw [succ_nsmul P35 k]
        exact add_sub_cancel_right _ _
      rw [hadd, hsub, ih0, ih1] at hpar
      push_cast at hpar ⊢
      linear_combination hpar
  exact (key m).1

/-- **Quadraticity on `⟨P35⟩`, integer multiples** — the `ℤ` form,
which falls out of the `ℕ` form by evenness. -/
theorem canonHeight_zsmul_P35 (m : ℤ) :
    canonHeight (m • P35) = (m : ℝ) ^ 2 * canonHeight P35 := by
  obtain ⟨k, hk | hk⟩ := Int.eq_nat_or_neg m
  · have h1 : m • P35 = k • P35 := by
      rw [hk]
      exact Nat.cast_smul_eq_nsmul ℤ k P35
    have hcast : (m : ℝ) = (k : ℝ) := by
      rw [hk]
      exact Int.cast_natCast k
    rw [h1, canonHeight_nsmul_P35 k, hcast]
  · have h1 : m • P35 = -(k • P35) := by
      rw [hk, neg_zsmul]
      congr 1
    have hcast : (m : ℝ) ^ 2 = (k : ℝ) ^ 2 := by
      rw [hk, Int.cast_neg, Int.cast_natCast]
      ring
    rw [h1, canonHeight_neg, canonHeight_nsmul_P35 k, hcast]

/-! ## The regulator object, and Seam B4 -/

/-- **The regulator object for `E2`**: `regE2 := ĥ(P35)`, an exact
in-tree real (class (a) as an object). Its *value* is the refined
pin's class-(c) hypothesis `E2RegulatorValue`, and its identification
with *the* regulator of `E2` is Seam B4 (`RegulatorBasisSeam`) —
neither is asserted here. -/
noncomputable def regE2 : ℝ :=
  canonHeight P35

/-- **Seam B4 — the regulator basis seam, as a labeled hypothesis.**
Identifying `regE2` with *the* regulator of `E2` presupposes that
`{P35}` is a Mordell–Weil basis mod torsion: the algebraic rank is
exactly `1` and `P35` is not a proper multiple (if `P35 = k • Q` then
`k = ±1`). Provenance (scoping memo §2, B2-2): in-tree we own only
rank `≥ 1` (rung 1, modulo the shared Nagell–Lutz seam and
Mordell–Weil finiteness); the `≤ 1` half is a recorded value from the
2026-10-27 study, whose own text flags that no pass has done it by
hand. This `Prop` is stated in the tree's vocabulary as far as it
reaches and is **proved nowhere**; it is carried as the labeled
antecedent wherever this line says "Reg". -/
def RegulatorBasisSeam : Prop :=
  algebraicRank E2 = 1 ∧
    ∀ (Q : E2.toAffine.Point) (k : ℤ), P35 = k • Q → k = 1 ∨ k = -1

/-! ## Axiom checks (headline results) -/

#print axioms canonHeight_zero
#print axioms canonHeight_two_nsmul
#print axioms canonHeight_neg
#print axioms canonHeight_parallelogram
#print axioms canonHeight_nsmul_P35
#print axioms canonHeight_zsmul_P35

end ThetLogos
