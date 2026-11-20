import Mathlib.Tactic
import ThetLogos.ThermalLiftFallPin

/-!
# ThetLogos.ThermalLiftCold — THERMAL LIFT, brick LIFT-3

**Cold out of heat.** The β → ∞ face of the Gibbs family,
in this tree's own idiom (`ThermalProfileSeparation`'s
profiled weight at a constant profile): the floor's
weight is monotone in β; every excited weight is at most
the gap factor `e^{−βΔ}` of its height above the floor;
the total off-floor weight dies like `(card V − 1) ·
e^{−βΔ}`; the weight is largest exactly at the floor;
and the limit itself — at any site strictly above the
floor the weight tends to `0` as `β → ∞` (the frozen
`ColdTieForm` of LIFT-0b, proved). The cold face is a
limit of the heat family, not a separate state.

**Citation at grade.** The bound shapes (monotonicity,
the per-mode gap factor, the total off-floor bound) are
proved at the diagonal seat by the lane-grade
`HotColdLimits` (og0 lane, T5 pins batch — not in this
tree's ancestry), in the `coldWeight` idiom of
`ColdHeatDualityPin`, which is likewise not in this
tree's ancestry. Following that module's own GapLine
precedent, the shapes are cited here by name and PROVED
in this tree's idiom — nothing is imported from that
line, and its grade is not borrowed. The limit statement
(`coldTieForm_holds`) is not stated in `HotColdLimits`;
it is this brick's own, obtained from the gap bound by
squeezing.

**The tie to LIFT-2.** The concentration locus is the
energy floor `argmin E` — the sites where the weight is
largest at every `β > 0` (`profWeight_max_at_ground`).
LIFT-2's thermal ground is the fall minimum of the
grounded thermal potential under its sign condition;
this brick's floor is the same physical seat read from
the heat side: what the fall reaches, the cold weight
concentrates on. No identity between the two objects is
asserted — the tie is the shared floor, stated as such.

**Fences.** A statement about a finite Gibbs family's
weights; no state is prepared, no engine is claimed
(K-HOTCOLD-PHYS stands from the cited scope), no
continuum limit is read (K-HOTCOLD-CONT). **Dial 2 = 0
under every outcome. NO CLAIM; dials 0/4.**
-/

namespace ThetLogos

open Filter

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

/-- The constant-profile partition sum, in sum form. -/
private theorem profPartition_const (E : V → ℝ) (β : ℝ) :
    profPartition (fun _ => β) E
      = ∑ i, Real.exp (-(β * E i)) :=
  rfl

/-- **Monotonicity at the floor.** As it gets colder the
floor only gains: the ground site's constant-profile
weight is monotone in `β`. (The `HotColdLimits` H-2
shape, proved here in the profiled idiom: the weight is
the reciprocal of a sum of terms each antitone in `β`.) -/
theorem profWeight_ground_mono {E : V → ℝ} {i₀ : V}
    (hi₀ : ∀ i, E i₀ ≤ E i) {β₁ β₂ : ℝ} (hβ : β₁ ≤ β₂) :
    profWeight (fun _ => β₁) E i₀
      ≤ profWeight (fun _ => β₂) E i₀ := by
  set S : ℝ → ℝ := fun β => ∑ i, Real.exp (-(β * (E i - E i₀)))
    with hS
  have hSpos : ∀ β, 0 < S β :=
    fun β => Finset.sum_pos (fun i _ => Real.exp_pos _)
      Finset.univ_nonempty
  have hSantitone : S β₂ ≤ S β₁ := by
    apply Finset.sum_le_sum
    intro i _
    apply Real.exp_le_exp.mpr
    apply neg_le_neg
    apply mul_le_mul_of_nonneg_right hβ
    exact sub_nonneg.mpr (hi₀ i)
  have hform : ∀ β, profWeight (fun _ => β) E i₀
      = (S β)⁻¹ := by
    intro β
    have hZfact : profPartition (fun _ => β) E
        = Real.exp (-(β * E i₀)) * S β := by
      rw [profPartition_const, hS, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [← Real.exp_add]
      congr 1
      ring
    have he : Real.exp (-(β * E i₀)) ≠ 0 := Real.exp_ne_zero _
    have hS' : S β ≠ 0 := (hSpos β).ne'
    show Real.exp (-(β * E i₀)) / profPartition (fun _ => β) E
      = (S β)⁻¹
    rw [hZfact]
    field_simp
  rw [hform β₁, hform β₂]
  exact (inv_le_inv₀ (hSpos β₁) (hSpos β₂)).mpr hSantitone

/-- **The gap factor (per mode).** Every site's weight is
at most `e^{−β(E i − E i₀)}`, the exponential of its own
height above the floor — no sign condition on `β`: the
partition sum dominates its ground term. (The
`HotColdLimits` H-3a / GAPFLOOR-1 shape, in this tree's
idiom.) -/
theorem profWeight_le_exp_neg_gap {E : V → ℝ} {i₀ : V}
    (β : ℝ) (i : V) :
    profWeight (fun _ => β) E i
      ≤ Real.exp (-(β * (E i - E i₀))) := by
  have hterm : Real.exp (-(β * E i₀))
      ≤ profPartition (fun _ => β) E := by
    rw [profPartition_const]
    exact Finset.single_le_sum
      (f := fun j => Real.exp (-(β * E j)))
      (fun j _ => (Real.exp_pos _).le) (Finset.mem_univ i₀)
  have hcalc : Real.exp (-(β * E i))
        / profPartition (fun _ => β) E
      ≤ Real.exp (-(β * E i)) / Real.exp (-(β * E i₀)) :=
    div_le_div_of_nonneg_left (Real.exp_pos _).le
      (Real.exp_pos _) hterm
  refine le_trans hcalc ?_
  have harg : (-(β * E i)) - (-(β * E i₀))
      = -(β * (E i - E i₀)) := by ring
  rw [← Real.exp_sub, harg]

/-- **The gap factor (total form).** The total off-floor
weight is at most `(card V − 1) · e^{−βΔ}` wherever `Δ`
undercuts every excited height — excited weight dies
like `e^{−βΔ}`. (The `HotColdLimits` H-3b shape, in this
tree's idiom.) -/
theorem offGround_profWeight_le {E : V → ℝ} {i₀ : V}
    (hi₀ : ∀ i, E i₀ ≤ E i) {β Δ : ℝ} (hβ : 0 ≤ β)
    (hΔ : ∀ i, i ≠ i₀ → Δ ≤ E i - E i₀) :
    ∑ i ∈ Finset.univ \ {i₀}, profWeight (fun _ => β) E i
      ≤ ((Fintype.card V : ℝ) - 1) * Real.exp (-(β * Δ)) := by
  have hcard : (Finset.univ \ {i₀} : Finset V).card
      = Fintype.card V - 1 := by
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ,
      Finset.card_singleton]
  have h1card : 1 ≤ Fintype.card V :=
    Fintype.card_pos_iff.mpr inferInstance
  calc ∑ i ∈ Finset.univ \ {i₀}, profWeight (fun _ => β) E i
      ≤ ∑ i ∈ Finset.univ \ {i₀}, Real.exp (-(β * Δ)) := by
        apply Finset.sum_le_sum
        intro i hi
        have hi₀' : i ≠ i₀ :=
          fun h => (Finset.mem_sdiff.mp hi).2
            (Finset.mem_singleton.mpr h)
        exact le_trans (profWeight_le_exp_neg_gap β i)
          (Real.exp_le_exp.mpr (neg_le_neg
            (mul_le_mul_of_nonneg_left (hΔ i hi₀') hβ)))
    _ = ((Fintype.card V : ℝ) - 1) * Real.exp (-(β * Δ)) := by
        rw [Finset.sum_const, hcard, nsmul_eq_mul,
          Nat.cast_sub h1card, Nat.cast_one]

/-- **The weight is largest at the floor.** For
`β > 0`, no site outweighs a minimal-energy site: the
concentration locus of the cold face is exactly the
energy floor. This is the tie-in to LIFT-2's thermal
ground, stated at its exact strength — a shared floor,
not an identity of objects. -/
theorem profWeight_max_at_ground {E : V → ℝ} {i₀ : V}
    (hi₀ : ∀ i, E i₀ ≤ E i) (hβ : 0 < β) (i : V) :
    profWeight (fun _ => β) E i
      ≤ profWeight (fun _ => β) E i₀ := by
  have hZ : 0 < profPartition (fun _ => β) E :=
    profPartition_pos _ _
  have e1 : profWeight (fun _ => β) E i
      = Real.exp (-(β * E i)) / profPartition (fun _ => β) E :=
    rfl
  have e2 : profWeight (fun _ => β) E i₀
      = Real.exp (-(β * E i₀)) / profPartition (fun _ => β) E :=
    rfl
  rw [e1, e2]
  exact (div_le_div_iff_of_pos_right hZ).mpr
    (Real.exp_le_exp.mpr (neg_le_neg
      (mul_le_mul_of_nonneg_left (hi₀ i) hβ.le)))

/-- **LIFT-3, the cold face (frozen target, proved).**
At any site strictly above the floor, the
constant-profile Gibbs weight tends to `0` as
`β → ∞`: squeeze between `0` and the gap factor
`e^{−βΔ}`, which dies exponentially. -/
theorem coldTieForm_holds (E : V → ℝ) (i₀ : V) :
    ColdTieForm E i₀ := by
  intro hi₀ i hi
  have hΔ : 0 < E i - E i₀ := sub_pos.mpr hi
  have hmul' : Tendsto (fun β : ℝ => β * (E i - E i₀))
      atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro b
    refine ⟨b / (E i - E i₀), fun β hβ => ?_⟩
    calc b = b / (E i - E i₀) * (E i - E i₀) := by
            rw [div_mul_cancel₀ b (ne_of_gt hΔ)]
      _ ≤ β * (E i - E i₀) :=
          mul_le_mul_of_nonneg_right hβ hΔ.le
  have hmul : Tendsto (fun β : ℝ => (E i - E i₀) * β)
      atTop atTop :=
    hmul'.congr (fun β => mul_comm _ _)
  have hexp : Tendsto
      (fun β : ℝ => Real.exp (-((E i - E i₀) * β)))
      atTop (nhds 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp hmul
  apply squeeze_zero (fun β => (profWeight_pos _ _ _).le)
    (fun β => profWeight_le_exp_neg_gap (i₀ := i₀) β i)
  have heq : (fun β : ℝ => Real.exp (-(β * (E i - E i₀))))
      = (fun β : ℝ => Real.exp (-((E i - E i₀) * β))) := by
    funext β
    congr 1
    ring
  rw [heq]
  exact hexp

end ThetLogos
