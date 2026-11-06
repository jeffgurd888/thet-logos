/-
# Brick TM-4 — The FACT-analog decision at the ternary seat
(Ternary Magnetism chain, LAST brick; TM-0 gate PASSED, TM-1/TM-2/TM-3
shipped — `layerKernelPos_ternary_seat` stands on the public record)

Commission: Jeff's TM chain commission (2026-11-05, "do it"),
executing TM-4 from the priced menu in
`~/workspace/your_files/ternary-magnetism-scoping-2026-11-05.md`
(§7, with §2.3/§2.4), fired after TM-3 integrated and shipped.

**Scope — exactly this brick.**  The ternary analog of LK-P0's
Item 2 (`seat_not_stratumColumnFactorization` at the binary seat):
decide the stratum-column factorization
`StratumColumnFactorization seatμ₃ seatρ₃ β` at the ZMod 3
character seat, `N = 2`.  Plus the two companions, as LK-P0's
package shipped them: the factorization's survival at `β = 0`,
and the FACT ⇒ `LayerKernelPos` conditional at this seat in its
vacuous form (the general arrow is `fact_implies_layerKernelPos`,
landed in `Span3FactLayerKernelPos`).

**Kill posture: K-TM-FACT is armed and EXPECTED TO FIRE — the
kill IS the landing.**  The TM-0 gate's arithmetic
(`~/workspace/your_files/ternary-magnetism-gate-2026-11-05.md` §3):
`K(1,1) − a₃²⁴ = 1.54e-3 / 4.74e-4 / 4.57e-4` at
`β = 0.3 / 0.7 / 1.3`, strictly above the reverse-pair lower
bound `2·a₃²²b₃²` throughout.  The mechanism is the binary
seat's: at `(1,1)` the trivial character does not exhaust the
column — the single-column average kills both non-vacuum
branches (`seat_colZ₃ = a₃`, `seat_zPolymer₃ = a₃²⁴`), but the
closed form (`layerKernel_ternary_closed`) sums over ALL
divergence-free patterns, and the go/return pair patterns
survive, contributing their weights on top of `a₃²⁴`.  The Lean
kill below spends only the `(1,1)` pair (weight `a₃²²b₃² > 0`
for `β > 0`); the gate's `2·` bound counts its `(2,2)` twin as
well.  `LayerKernelPos` at this seat is untouched by the kill —
it is proved in TM-3 by the Gram route, not through FACT.

NO CLAIM; dials 0/4.  Magnetism grade (scoping §2.2): ternary
magnetism in the clock/Potts sense only.
-/

import ThetLogos.LayerKernelPosTernaryGram
import ThetLogos.Span3FactLayerKernelPos

open MeasureTheory Finset
open scoped ENNReal

namespace ThetLogos

/-! ## The go/return pair pattern at branches `(1, 1)` -/

/-- The **go/return pair pattern** at branches `(1, 1)`: branch
`1` on the chosen column `seatCol0` and on its return partner
`seatCol0'` (the column over the shifted site with the same
direction — at `N = 2` its head is `seatCol0`'s base), branch
`0` elsewhere.  The ternary seat's analog of LK-P0's even pair
`{seatCol0, seatCol0'}`: a 2-cycle of the signed pattern field,
the shortest divergence-free pattern after the empty one
(TM-0 gate §2: among support ≤ 3, the survivors are exactly the
empty pattern and the 24 go/return equal-branch pairs). -/
noncomputable def seatPair₃ : LayerColumn 2 → ZMod 3 :=
  Function.update
    (Function.update (0 : LayerColumn 2 → ZMod 3) seatCol0 1)
    seatCol0' 1

/-- The two columns of the pair differ (their base sites
differ). -/
theorem seatPair₃_ne : seatCol0 ≠ seatCol0' :=
  fun h => seatCol0_ne h.symm

/-- The pair pattern in indicator form: branch `1` exactly on
the two pair columns, `0` elsewhere (the two indicators never
fire together — the columns differ). -/
theorem seatPair₃_apply (P : LayerColumn 2) :
    seatPair₃ P = (if P = seatCol0 then (1 : ZMod 3) else 0)
      + (if P = seatCol0' then (1 : ZMod 3) else 0) := by
  unfold seatPair₃
  by_cases h1 : P = seatCol0 <;> by_cases h2 : P = seatCol0'
  · exact absurd (h1.symm.trans h2) seatPair₃_ne
  · rw [Function.update_of_ne h2, h1, Function.update_self]
    simp [seatPair₃_ne]
  · rw [h2, Function.update_self]
    simp [seatCol0_ne]
  · rw [Function.update_of_ne h2, Function.update_of_ne h1]
    simp [h1, h2]

/-- A fiber sum of the pair pattern over any column predicate
collects exactly the two indicators of the pair columns. -/
theorem seatPair₃_fiber_sum (p : LayerColumn 2 → Prop)
    [DecidablePred p] :
    (∑ P ∈ Finset.univ.filter p, seatPair₃ P)
      = (if p seatCol0 then (1 : ZMod 3) else 0)
        + (if p seatCol0' then (1 : ZMod 3) else 0) := by
  have hsum : (∑ P ∈ Finset.univ.filter p, seatPair₃ P)
      = ∑ P ∈ Finset.univ.filter p,
          ((if P = seatCol0 then (1 : ZMod 3) else 0)
            + (if P = seatCol0' then (1 : ZMod 3) else 0)) :=
    Finset.sum_congr rfl fun P _ => seatPair₃_apply P
  rw [hsum, Finset.sum_add_distrib]
  congr 1
  · rw [Finset.sum_ite_eq']
    simp
  · rw [Finset.sum_ite_eq']
    simp

/-- **The pair pattern survives the filter.**  At every site the
signed divergence cancels: the base fiber sees the two pair
columns at `seatSite0` and at its shift, the head fiber sees
them at the same two sites in the opposite order (the return
column's head is the first column's base, by the involution
`layerShift_shift` at `N = 2`). -/
theorem patternSurvives₃_seatPair₃ : patternSurvives₃ seatPair₃ := by
  intro c
  unfold patternDiv₃
  rw [seatPair₃_fiber_sum, seatPair₃_fiber_sum]
  show ((if seatSite0 = c then (1 : ZMod 3) else 0)
      + (if layerShift seatDir1.1 seatDir1.2 seatSite0 = c
          then (1 : ZMod 3) else 0))
    - ((if layerShift seatDir1.1 seatDir1.2 seatSite0 = c
          then (1 : ZMod 3) else 0)
      + (if layerShift seatDir1.1 seatDir1.2
            (layerShift seatDir1.1 seatDir1.2 seatSite0) = c
          then (1 : ZMod 3) else 0)) = 0
  rw [layerShift_shift]
  rw [add_comm (if seatSite0 = c then (1 : ZMod 3) else 0)
    (if layerShift seatDir1.1 seatDir1.2 seatSite0 = c
      then (1 : ZMod 3) else 0)]
  exact sub_self _

/-- The pair pattern's support is exactly the two pair
columns. -/
theorem patternSupp₃_seatPair₃ :
    patternSupp₃ seatPair₃ = {seatCol0, seatCol0'} := by
  ext P
  simp only [patternSupp₃, Finset.mem_filter, Finset.mem_univ,
    true_and, Finset.mem_insert, Finset.mem_singleton]
  rw [seatPair₃_apply]
  constructor
  · intro h
    by_cases h1 : P = seatCol0
    · exact Or.inl h1
    by_cases h2 : P = seatCol0'
    · exact Or.inr h2
    · simp [h1, h2] at h
  · rintro (rfl | rfl)
    · simp [seatPair₃_ne]
    · simp [seatCol0_ne]

/-- The pair pattern's weight is the excess term itself:
`w = a₃²² b₃²` (support of card `2` in the weight
`a₃^(24−|supp|) b₃^|supp|`). -/
theorem patternWeight₃_seatPair₃ (β : ℝ) :
    patternWeight₃ seatPair₃ β = seatA₃ β ^ 22 * seatB₃ β ^ 2 := by
  unfold patternWeight₃
  rw [patternSupp₃_seatPair₃, Finset.card_pair seatPair₃_ne]

/-- The empty pattern's weight is the polymer value `a₃²⁴`
(empty support). -/
theorem patternWeight₃_zero (β : ℝ) :
    patternWeight₃ (0 : LayerColumn 2 → ZMod 3) β
      = seatA₃ β ^ 24 := by
  have hsupp : patternSupp₃ (0 : LayerColumn 2 → ZMod 3) = ∅ := by
    ext P
    simp [patternSupp₃]
  unfold patternWeight₃
  rw [hsupp]
  simp

/-! ## The split coefficients: values at `β = 0`, positivity -/

/-- `a₃(0) = 1` (at `β = 0` every Boltzmann factor is `1`). -/
theorem seatA₃_zero : seatA₃ 0 = 1 := by
  unfold seatA₃
  norm_num

/-- `b₃(0) = 0` (at `β = 0` the character branches carry no
weight — the factorization's survival at `β = 0` turns on
this). -/
theorem seatB₃_zero : seatB₃ 0 = 0 := by
  unfold seatB₃
  norm_num

/-- `a₃(β) > 0` at every `β` (strengthening TM-1's
`seatA₃_nonneg` to the strict bound the kill spends). -/
theorem seatA₃_pos (β : ℝ) : 0 < seatA₃ β := by
  have h := Real.exp_pos (-(3 / 2) * β)
  unfold seatA₃
  linarith

/-- `b₃(β) > 0` iff `β > 0` — the forward direction, spent by
the kill: the excess weight `a₃²²b₃²` is strictly positive
exactly when `β > 0`. -/
theorem seatB₃_pos {β : ℝ} (hβ : 0 < β) : 0 < seatB₃ β := by
  have h : Real.exp (-(3 / 2) * β) < 1 := by
    rw [Real.exp_lt_one_iff]
    have h2 : (0 : ℝ) < (3 / 2) * β :=
      mul_pos (by norm_num) hβ
    linarith
  unfold seatB₃
  linarith

/-! ## The FACT-analog decision at the ternary seat -/

/-- The configuration character of any pattern at the identity
configuration is `1` (every link character is `χ(1) = 1`) — the
ternary analog of LK-P0's `configProd_one`. -/
theorem patternConfig₃_one (ε : LayerColumn 2 → ZMod 3) :
    patternConfig₃ ε 1 = 1 := by
  unfold patternConfig₃ configChar₃
  simp [seatChar₃_one]

/-- The zero pattern's configuration character is `1` (every
branch exponent is `0`). -/
theorem patternConfig₃_zero
    (u : LayerLink 2 → Multiplicative (ZMod 3)) :
    patternConfig₃ (0 : LayerColumn 2 → ZMod 3) u = 1 := by
  unfold patternConfig₃
  refine Finset.prod_eq_one fun P _ => ?_
  rw [Pi.zero_apply, ZMod.val_zero, pow_zero]

/-- **TM-4 — K-TM-FACT fires.**  FACT (the stratum column
factorization `StratumColumnFactorization`) is **false at the
ternary seat for every `β > 0`**: at the identity configuration,
FACT would force `layerKernel = zPolymer = a₃(β)²⁴`, but the
closed form gives
`∑_{ε surviving} w_ε ≥ a₃²⁴ + a₃²²b₃² > a₃²⁴`, the excess
being the go/return pair pattern's contribution (the `(1,1)`
pair alone; its `(2,2)` twin contributes the same again — the
TM-0 gate's `2·a₃²²b₃²` lower bound counts both).  One
certified mismatch kills FACT at the seat, exactly as
K-FACT-SEAT did at the binary seat.  `LayerKernelPos` at this
seat is untouched by the kill — it is proved in TM-3
(`layerKernelPos_ternary_seat`) by the Gram route, not through
FACT. -/
theorem seat_not_stratumColumnFactorization₃ {β : ℝ} (hβ : 0 < β) :
    ¬ StratumColumnFactorization (N := 2) seatμ₃ seatρ₃ β := by
  intro hfact
  have hK := hfact 1 1
  rw [layerKernel_ternary_closed, seat_zPolymer₃] at hK
  have hsum1 : layerKernel_ternary β 1 1
      = ((∑ ε ∈ Finset.univ.filter patternSurvives₃,
          patternWeight₃ ε β : ℝ) : ℂ) := by
    unfold layerKernel_ternary
    rw [Complex.ofReal_sum]
    exact Finset.sum_congr rfl fun ε _ => by
      rw [patternConfig₃_one]
      simp
  rw [hsum1] at hK
  have hre := congrArg Complex.re hK
  simp only [Complex.ofReal_re] at hre
  have hsub : ({0, seatPair₃} : Finset (LayerColumn 2 → ZMod 3))
      ⊆ Finset.univ.filter patternSurvives₃ := by
    intro ε hε
    simp only [Finset.mem_insert, Finset.mem_singleton] at hε
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rcases hε with rfl | rfl
    · exact patternSurvives₃_zero
    · exact patternSurvives₃_seatPair₃
  have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (f := fun ε => patternWeight₃ ε β)
    (fun ε _ _ => patternWeight₃_nonneg ε hβ.le)
  have hne : (0 : LayerColumn 2 → ZMod 3) ≠ seatPair₃ := by
    intro h
    have h1 : seatPair₃ seatCol0 = 1 := by
      rw [seatPair₃_apply]
      simp [seatPair₃_ne]
    have h2 := congrFun h seatCol0
    rw [Pi.zero_apply, h1] at h2
    exact (by decide : (0 : ZMod 3) ≠ 1) h2
  have hpair : (∑ ε ∈ ({0, seatPair₃}
        : Finset (LayerColumn 2 → ZMod 3)), patternWeight₃ ε β)
      = seatA₃ β ^ 24 + seatA₃ β ^ 22 * seatB₃ β ^ 2 := by
    rw [Finset.sum_pair hne, patternWeight₃_zero,
      patternWeight₃_seatPair₃]
  have hpos : 0 < seatA₃ β ^ 22 * seatB₃ β ^ 2 :=
    mul_pos (pow_pos (seatA₃_pos β) 22) (pow_pos (seatB₃_pos hβ) 2)
  rw [hpair] at hle
  linarith

/-- **Companion — the factorization survives at `β = 0`.**  At
`β = 0` the character branches carry no weight (`b₃(0) = 0`),
every nonempty-support pattern's weight vanishes, and the
closed form collapses to the empty pattern's term: the kernel
is identically `1 = a₃(0)²⁴ = zPolymer`.  The kill above is
exactly a `β > 0` phenomenon, as at the binary seat. -/
theorem seat_stratumColumnFactorization₃_zero :
    StratumColumnFactorization (N := 2) seatμ₃ seatρ₃ 0 := by
  intro u u'
  rw [layerKernel_ternary_closed, seat_zPolymer₃, seatA₃_zero,
    one_pow, Complex.ofReal_one]
  have hterm : ∀ ε ∈ Finset.univ.filter patternSurvives₃,
      (patternWeight₃ ε 0 : ℂ)
        * (patternConfig₃ ε u' * star (patternConfig₃ ε u))
      = (if ε = 0 then 1 else 0) := by
    intro ε _
    by_cases hε : ε = 0
    · subst hε
      simp [patternWeight₃_zero, seatA₃_zero, patternConfig₃_zero]
    · have hcard : (patternSupp₃ ε).card ≠ 0 := by
        rw [Finset.card_ne_zero]
        obtain ⟨P, hP⟩ : ∃ P, ε P ≠ 0 := by
          by_contra hcon
          push Not at hcon
          exact hε (funext hcon)
        refine ⟨P, ?_⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hP⟩
      have hw : patternWeight₃ ε 0 = 0 := by
        unfold patternWeight₃
        rw [seatB₃_zero, zero_pow hcard, mul_zero]
      rw [hw]
      simp [hε]
  unfold layerKernel_ternary
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq']
  simp [patternSurvives₃_zero]

/-- **Companion — the FACT ⇒ `LayerKernelPos` conditional at
the ternary seat, in its vacuous form.**  The general arrow
(`fact_implies_layerKernelPos`, landed) instantiated at this
seat: were the factorization to hold at some `β`, positivity
would follow.  For `β > 0` the antecedent is false by the kill
above, so the conditional's live content is the `β = 0` case —
`LayerKernelPos` at this seat for `β ≥ 0` is proved directly
in TM-3, not through this arrow. -/
theorem fact_implies_layerKernelPos_ternary_seat (β : ℝ)
    (hfact : StratumColumnFactorization (N := 2) seatμ₃ seatρ₃ β) :
    LayerKernelPos (N := 2) seatμ₃ seatρ₃ β :=
  fact_implies_layerKernelPos seatμ₃ seatρ₃ even_two seatρ₃_cont
    β hfact

end ThetLogos
