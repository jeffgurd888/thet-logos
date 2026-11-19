/-
# ThermalDensityPin — thermal density at the finite Gibbs seat

**Commissioned by Zero, 2026-11-13 18:43 EST
("build it"), following his seeing of 18:40 EST
(scope:
~/workspace/your_files/thermal-density-pin-scope-2026-11-13.md).
NO CLAIM. T5-seat pin. Dial-ineligible.**

ZERO'S SEEING (verbatim, 2026-11-13 18:40 EST):
"let's set 1 planck space energy = 1 thermal kernal
of action 1 heated space would be thermal density
and the same thermal density of cold is the golden
ratio larger if space hot wants to get bigger while
cold resistance is the geometric shape of thermal
Entropy"

THE SEAT: the diagonal Gibbs seat of `HotColdLimits`
— Gibbs weights (`coldWeight`) on a finite level
list `E`, the heat trace `Z(β) = coldPartition β E`.
The bound stated at commissioning: the build covers
the FINITE SEAT content only.

WHAT THIS PIN DOES NOT BUILD (the scope's fences,
carded): **φ is NOT here** — not as a fact, theorem,
or definition; Zero's φ clause is his setting,
recorded in the scope, unbuilt; `K-PHI-DERIVED` armed
(any density ratio claimed = φ must be DERIVED from a
tree spectrum, never assigned). **No Planck scale as
physics** — no lengths, no cells, no quantum gravity;
`K-PLANCK-SEAT` armed against reading the unit card
as a scale claim. **No gravity** — `K-DENSITY-GRAV`
armed (the density road was killed 2026-11-13 18:34);
the entropy floor is a counting statement at the
seat, not an area law (the Bekenstein–Hawking area
form is Register-2 external authority, cited in the
scope, not built). Continuum forms are FRONTIER.

STATUS: STATUS-DENSITY.md (per brick).
-/

import Mathlib
import ThetLogos.HotColdLimits
import ThetLogos.FiniteEntropy

namespace ThetLogos

variable {N : ℕ} [NeZero N]

/-! ## §1 — the unit card (Zero's setting, Register A) -/

/-- **UNIT CARD (declared, Register A):** Zero's
setting — "1 Planck space energy = 1 thermal kernel
of action." At this seat the thermal kernel of action
is the heat trace, so the seat's unit is declared to
be `Z(β) = coldPartition β E` itself. This is a
DEFINITION carrying its declared status: no theorem
states or uses any Planck-scale physics
(`K-PLANCK-SEAT` armed), and the card names a unit,
never a scale. -/
noncomputable def thermalUnit (β : ℝ) (E : Fin N → ℝ) : ℝ :=
  coldPartition β E

/-! ## §2 — thermal density: the heated space's content -/

/-- **Thermal density at the seat**: the heated
space's energy content — the Gibbs mean energy
`⟨E⟩_β` of the seat's single contained system (the
corpus's `coldMeanEnergy`). No volume exists at the
seat and none is pretended: the density is the
content, in the seat's declared unit. -/
noncomputable def thermalDensity (β : ℝ) (E : Fin N → ℝ) : ℝ :=
  coldMeanEnergy β E

/-- The Gibbs weights are positive and normalized. -/
theorem coldWeight_pos (β : ℝ) (E : Fin N → ℝ) (i : Fin N) :
    0 < coldWeight β E i := by
  rw [coldWeight_eq]
  exact div_pos (Real.exp_pos _) (coldPartition_pos β E)

theorem coldWeight_sum_one (β : ℝ) (E : Fin N → ℝ) :
    ∑ i, coldWeight β E i = 1 := by
  have hZ : coldPartition β E ≠ 0 := (coldPartition_pos β E).ne'
  have h : ∑ i, coldWeight β E i
      = (∑ i, Real.exp (-(β * E i))) / coldPartition β E := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    exact coldWeight_eq β E i
  rw [h]
  exact div_self hZ

/-! ## §3 — hot side: heating raises the content
    (the variance route, in finite comparison form) -/

/-- **The variance-route identity** (finite,
derivative-free): twice the covariance combination of
`E` and `f` under weights `w` is the symmetrized
double sum. Differentiating this identity along the
Gibbs family is `d⟨E⟩/dβ = −Var_β(E)`; at the finite
seat it is proved as an exact identity, and its SIGN
is the content. -/
theorem covar_two_mul (w E f : Fin N → ℝ) :
    2 * ((∑ i, w i * E i * f i) * (∑ i, w i)
        - (∑ i, w i * E i) * (∑ i, w i * f i))
      = ∑ i, ∑ j, w i * w j * (E i - E j) * (f i - f j) := by
  have hA : (∑ i, w i * E i * f i) * (∑ i, w i)
      = ∑ i, ∑ j, (w i * E i * f i) * w j := by
    rw [Finset.sum_mul_sum]
  have hB : (∑ i, w i * E i) * (∑ i, w i * f i)
      = ∑ i, ∑ j, (w i * E i) * (w j * f j) := by
    rw [Finset.sum_mul_sum]
  have hswap : ∀ G : Fin N → Fin N → ℝ,
      (∑ i, ∑ j, G i j) = ∑ i, ∑ j, G j i :=
    fun G => Finset.sum_comm
  calc 2 * ((∑ i, w i * E i * f i) * (∑ i, w i)
          - (∑ i, w i * E i) * (∑ i, w i * f i))
      = ((∑ i, ∑ j, (w i * E i * f i) * w j)
          + (∑ i, ∑ j, (w j * E j * f j) * w i))
        - ((∑ i, ∑ j, (w i * E i) * (w j * f j))
          + (∑ i, ∑ j, (w j * E j) * (w i * f i))) := by
        rw [show (2:ℝ) * ((∑ i, w i * E i * f i) * (∑ i, w i)
              - (∑ i, w i * E i) * (∑ i, w i * f i))
            = ((∑ i, w i * E i * f i) * (∑ i, w i)
              + (∑ i, w i * E i * f i) * (∑ i, w i))
              - ((∑ i, w i * E i) * (∑ i, w i * f i)
              + (∑ i, w i * E i) * (∑ i, w i * f i)) from by ring,
          hA, hB]
        linear_combination
          (hswap (fun i j => (w i * E i * f i) * w j))
          - (hswap (fun i j => (w i * E i) * (w j * f j)))
    _ = ∑ i, ∑ j, w i * w j * (E i - E j) * (f i - f j) := by
        simp_rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring

/-- Each symmetrized summand is nonpositive when `w`
is nonnegative and `f` is antitone in `E`: the two
factors always pull opposite ways. -/
theorem covar_summand_nonpos {w E f : Fin N → ℝ}
    (hw : ∀ i, 0 ≤ w i)
    (hf : ∀ i j, E i ≤ E j → f j ≤ f i) (i j : Fin N) :
    w i * w j * (E i - E j) * (f i - f j) ≤ 0 := by
  rcases le_total (E i) (E j) with h | h
  · exact mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (hw i) (hw j))
        (sub_nonpos.mpr h))
      (sub_nonneg.mpr (hf i j h))
  · exact mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg (mul_nonneg (hw i) (hw j)) (sub_nonneg.mpr h))
      (sub_nonpos.mpr (hf j i h))

/-- The reweighting identity: the colder Gibbs weight
is the hotter weight reweighted by `exp (−δ·E)`,
normalized — the likelihood-ratio form of the Gibbs
family. -/
theorem coldWeight_reweight {E : Fin N → ℝ} {β₁ β₂ : ℝ} :
    ∀ i, coldWeight β₂ E i
      = coldWeight β₁ E i * Real.exp (-((β₂ - β₁) * E i))
        / (∑ j, coldWeight β₁ E j
            * Real.exp (-((β₂ - β₁) * E j))) := by
  have hZ₁ : coldPartition β₁ E ≠ 0 := (coldPartition_pos β₁ E).ne'
  have hZ₂ : coldPartition β₂ E ≠ 0 := (coldPartition_pos β₂ E).ne'
  have hS : (∑ j, coldWeight β₁ E j
        * Real.exp (-((β₂ - β₁) * E j)))
      = coldPartition β₂ E / coldPartition β₁ E := by
    rw [eq_div_iff hZ₁, Finset.sum_mul]
    have hterm : ∀ j : Fin N, coldWeight β₁ E j
        * Real.exp (-((β₂ - β₁) * E j)) * coldPartition β₁ E
        = Real.exp (-(β₂ * E j)) := by
      intro j
      rw [coldWeight_eq]
      field_simp
      rw [← Real.exp_add]
      congr 1
      ring
    rw [Finset.sum_congr rfl (fun j _ => hterm j)]
    rfl
  intro i
  rw [hS, coldWeight_eq β₂, coldWeight_eq β₁]
  field_simp
  rw [← Real.exp_add]
  congr 1
  ring

/-- The mean energy at `β₂` is the `g`-reweighted mean
at `β₁` — the form the association sign consumes. -/
theorem coldMeanEnergy_reweight {E : Fin N → ℝ} {β₁ β₂ : ℝ} :
    coldMeanEnergy β₂ E
      = (∑ i, coldWeight β₁ E i * E i
          * Real.exp (-((β₂ - β₁) * E i)))
        / (∑ j, coldWeight β₁ E j
            * Real.exp (-((β₂ - β₁) * E j))) := by
  have hterm : ∀ i : Fin N, coldWeight β₂ E i * E i
      = (coldWeight β₁ E i * E i
          * Real.exp (-((β₂ - β₁) * E i)))
        / (∑ j, coldWeight β₁ E j
            * Real.exp (-((β₂ - β₁) * E j))) := by
    intro i
    rw [coldWeight_reweight]
    ring
  rw [coldMeanEnergy,
    Finset.sum_congr rfl (fun i _ => hterm i), ← Finset.sum_div]

/-- **D-1 (hot side, weak form):** the thermal density
is antitone in `β` — as the space heats (`β` falls)
the contained energy content rises; as it cools the
content falls. The finite-seat form of the variance
identity's sign. -/
theorem thermalDensity_antitone {E : Fin N → ℝ}
    {β₁ β₂ : ℝ} (hβ : β₁ ≤ β₂) :
    thermalDensity β₂ E ≤ thermalDensity β₁ E := by
  have hδ0 : 0 ≤ β₂ - β₁ := sub_nonneg.mpr hβ
  set g : Fin N → ℝ := fun i => Real.exp (-((β₂ - β₁) * E i))
    with hg
  have hgmean : 0 < ∑ j, coldWeight β₁ E j * g j :=
    Finset.sum_pos (fun i _ => mul_pos (coldWeight_pos β₁ E i)
      (Real.exp_pos _))
      (Finset.univ_nonempty_iff.mpr ⟨⟨0, NeZero.pos N⟩⟩)
  have hassoc : (∑ i, coldWeight β₁ E i * E i * g i)
      ≤ (∑ i, coldWeight β₁ E i * E i)
        * (∑ i, coldWeight β₁ E i * g i) := by
    have h := covar_two_mul (coldWeight β₁ E) E g
    have hsign : ∑ i, ∑ j, coldWeight β₁ E i * coldWeight β₁ E j
        * (E i - E j) * (g i - g j) ≤ 0 := by
      apply Finset.sum_nonpos
      intro i _
      apply Finset.sum_nonpos
      intro j _
      apply covar_summand_nonpos
      · intro k
        exact (coldWeight_pos β₁ E k).le
      · intro a b hab
        show Real.exp (-((β₂ - β₁) * E b))
          ≤ Real.exp (-((β₂ - β₁) * E a))
        apply Real.exp_le_exp.mpr
        apply neg_le_neg
        exact mul_le_mul_of_nonneg_left hab hδ0
    rw [coldWeight_sum_one] at h
    linarith [h, hsign]
  show coldMeanEnergy β₂ E ≤ coldMeanEnergy β₁ E
  rw [coldMeanEnergy_reweight, div_le_iff₀ hgmean]
  exact hassoc

/-- **D-2 (hot side, strict form):** with a genuinely
two-level spectrum and a genuine temperature step,
the density strictly falls as `β` rises — the
variance is strictly positive, so the content
strictly responds. -/
theorem thermalDensity_strictAnti {E : Fin N → ℝ}
    {β₁ β₂ : ℝ} (hβ : β₁ < β₂)
    (hsp : ∃ a b, E a < E b) :
    thermalDensity β₂ E < thermalDensity β₁ E := by
  obtain ⟨a, b, hab⟩ := hsp
  have hδ0 : 0 < β₂ - β₁ := sub_pos.mpr hβ
  set g : Fin N → ℝ := fun i => Real.exp (-((β₂ - β₁) * E i))
    with hg
  have hgmean : 0 < ∑ j, coldWeight β₁ E j * g j :=
    Finset.sum_pos (fun i _ => mul_pos (coldWeight_pos β₁ E i)
      (Real.exp_pos _))
      (Finset.univ_nonempty_iff.mpr ⟨⟨0, NeZero.pos N⟩⟩)
  have hanti : ∀ x y : Fin N, E x ≤ E y → g y ≤ g x := by
    intro x y hxy
    show Real.exp (-((β₂ - β₁) * E y))
      ≤ Real.exp (-((β₂ - β₁) * E x))
    apply Real.exp_le_exp.mpr
    apply neg_le_neg
    exact mul_le_mul_of_nonneg_left hxy hδ0.le
  have hDneg : ∑ i, ∑ j, coldWeight β₁ E i * coldWeight β₁ E j
      * (E i - E j) * (g i - g j) < 0 := by
    apply Finset.sum_neg'
    · intro i _
      apply Finset.sum_nonpos
      intro j _
      exact covar_summand_nonpos
        (fun k => (coldWeight_pos β₁ E k).le) hanti i j
    · refine ⟨a, Finset.mem_univ a, Finset.sum_neg' ?_ ?_⟩
      · intro j _
        exact covar_summand_nonpos
          (fun k => (coldWeight_pos β₁ E k).le) hanti a j
      · refine ⟨b, Finset.mem_univ b, ?_⟩
        have hgab : g b < g a := by
          show Real.exp (-((β₂ - β₁) * E b))
            < Real.exp (-((β₂ - β₁) * E a))
          apply Real.exp_lt_exp.mpr
          apply neg_lt_neg
          exact mul_lt_mul_of_pos_left hab hδ0
        exact mul_neg_of_neg_of_pos
          (mul_neg_of_pos_of_neg
            (mul_pos (coldWeight_pos β₁ E a) (coldWeight_pos β₁ E b))
            (sub_neg.mpr hab))
          (sub_pos.mpr hgab)
  have hassoc : (∑ i, coldWeight β₁ E i * E i * g i)
      < (∑ i, coldWeight β₁ E i * E i)
        * (∑ i, coldWeight β₁ E i * g i) := by
    have h := covar_two_mul (coldWeight β₁ E) E g
    rw [coldWeight_sum_one] at h
    linarith [h, hDneg]
  show coldMeanEnergy β₂ E < coldMeanEnergy β₁ E
  rw [coldMeanEnergy_reweight, div_lt_iff₀ hgmean]
  exact hassoc

/-! ## §4 — cold side: entropy squeezes to its floor
    ("cold resistance" as a theorem shape) -/

/-- The Gibbs entropy in closed form:
`S(β) = β·⟨E⟩_β + log Z(β)`. -/
theorem gibbsEntropy_eq (β : ℝ) (E : Fin N → ℝ) :
    entropyW (coldWeight β E)
      = β * coldMeanEnergy β E + Real.log (coldPartition β E) := by
  have hlog : ∀ i, Real.log (coldWeight β E i)
      = -(β * E i + Real.log (coldPartition β E)) :=
    fun i => GibbsSpan.gibbsWeightsE_log β E _ i
  have h1 : entropyW (coldWeight β E)
      = ∑ i, coldWeight β E i
          * (β * E i + Real.log (coldPartition β E)) := by
    show (-∑ i, coldWeight β E i * Real.log (coldWeight β E i)) = _
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [hlog i]
    ring
  rw [h1]
  have h2 : ∀ i : Fin N, coldWeight β E i
        * (β * E i + Real.log (coldPartition β E))
      = β * (coldWeight β E i * E i)
        + Real.log (coldPartition β E) * coldWeight β E i := by
    intro i
    ring
  rw [Finset.sum_congr rfl (fun i _ => h2 i), Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, coldWeight_sum_one,
    ← coldMeanEnergy]
  ring

/-- The relative entropy of the colder Gibbs state
against the hotter, in closed form. -/
theorem relEnt_gibbs_eq {E : Fin N → ℝ} {β₁ β₂ : ℝ} :
    ∑ i, coldWeight β₂ E i
        * Real.log (coldWeight β₂ E i / coldWeight β₁ E i)
      = (β₁ - β₂) * coldMeanEnergy β₂ E
        + (Real.log (coldPartition β₁ E)
          - Real.log (coldPartition β₂ E)) := by
  have hlog : ∀ (β : ℝ) (i : Fin N), Real.log (coldWeight β E i)
      = -(β * E i + Real.log (coldPartition β E)) :=
    fun β i => GibbsSpan.gibbsWeightsE_log β E _ i
  have hterm : ∀ i : Fin N, coldWeight β₂ E i
        * Real.log (coldWeight β₂ E i / coldWeight β₁ E i)
      = (β₁ - β₂) * (coldWeight β₂ E i * E i)
        + (Real.log (coldPartition β₁ E)
            - Real.log (coldPartition β₂ E))
          * coldWeight β₂ E i := by
    intro i
    rw [Real.log_div (coldWeight_pos β₂ E i).ne'
        (coldWeight_pos β₁ E i).ne', hlog β₂ i, hlog β₁ i]
    ring
  rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, coldWeight_sum_one,
    ← coldMeanEnergy]
  ring

/-- **Gibbs inequality at the seat:** the relative
entropy of one Gibbs state against another is
nonnegative (from `log x ≤ x − 1`). -/
theorem relEnt_gibbs_nonneg {E : Fin N → ℝ} {β₁ β₂ : ℝ} :
    0 ≤ ∑ i, coldWeight β₂ E i
        * Real.log (coldWeight β₂ E i / coldWeight β₁ E i) := by
  have hterm : ∀ i : Fin N, coldWeight β₂ E i - coldWeight β₁ E i
      ≤ coldWeight β₂ E i
        * Real.log (coldWeight β₂ E i / coldWeight β₁ E i) := by
    intro i
    have hw₁ := coldWeight_pos β₁ E i
    have hw₂ := coldWeight_pos β₂ E i
    have hlog : Real.log (coldWeight β₁ E i / coldWeight β₂ E i)
        ≤ coldWeight β₁ E i / coldWeight β₂ E i - 1 :=
      Real.log_le_sub_one_of_pos (div_pos hw₁ hw₂)
    rw [Real.log_div hw₁.ne' hw₂.ne'] at hlog
    have hcan : coldWeight β₂ E i
          * (coldWeight β₁ E i / coldWeight β₂ E i)
        = coldWeight β₁ E i :=
      mul_div_cancel₀ _ hw₂.ne'
    have h2 : coldWeight β₂ E i
          * (Real.log (coldWeight β₁ E i)
            - Real.log (coldWeight β₂ E i))
        ≤ coldWeight β₁ E i - coldWeight β₂ E i := by
      calc coldWeight β₂ E i
            * (Real.log (coldWeight β₁ E i)
              - Real.log (coldWeight β₂ E i))
          ≤ coldWeight β₂ E i
              * (coldWeight β₁ E i / coldWeight β₂ E i - 1) :=
            mul_le_mul_of_nonneg_left hlog hw₂.le
        _ = coldWeight β₁ E i - coldWeight β₂ E i := by
            rw [mul_sub, hcan, mul_one]
    rw [Real.log_div hw₂.ne' hw₁.ne']
    linarith [h2]
  have hsum : ∑ i, (coldWeight β₂ E i - coldWeight β₁ E i) = 0 := by
    rw [Finset.sum_sub_distrib, coldWeight_sum_one,
      coldWeight_sum_one]
    norm_num
  rw [← hsum]
  exact Finset.sum_le_sum (fun i _ => hterm i)

/-- **D-3 (cold side, monotonicity):** on the physical
range `0 ≤ β₁ ≤ β₂` the Gibbs entropy is antitone in
`β` — cooling squeezes the entropy down. (The identity
`S₁ − S₂ = D(w₂‖w₁) + β₁(⟨E⟩₁ − ⟨E⟩₂)` seats it: a
relative entropy plus the hot side's fall, both
nonnegative.) -/
theorem gibbsEntropy_antitone {E : Fin N → ℝ}
    {β₁ β₂ : ℝ} (hβ₁ : 0 ≤ β₁) (hβ : β₁ ≤ β₂) :
    entropyW (coldWeight β₂ E) ≤ entropyW (coldWeight β₁ E) := by
  have hident : entropyW (coldWeight β₁ E)
        - entropyW (coldWeight β₂ E)
      = (∑ i, coldWeight β₂ E i
          * Real.log (coldWeight β₂ E i / coldWeight β₁ E i))
        + β₁ * (coldMeanEnergy β₁ E - coldMeanEnergy β₂ E) := by
    rw [gibbsEntropy_eq β₁, gibbsEntropy_eq β₂, relEnt_gibbs_eq]
    ring
  have hD : 0 ≤ ∑ i, coldWeight β₂ E i
      * Real.log (coldWeight β₂ E i / coldWeight β₁ E i) :=
    relEnt_gibbs_nonneg
  have hE : 0 ≤ coldMeanEnergy β₁ E - coldMeanEnergy β₂ E :=
    sub_nonneg.mpr (thermalDensity_antitone hβ)
  linarith [hident, hD, mul_nonneg hβ₁ hE]

/-- **D-4 (cold side, the floor):** the Gibbs entropy
never falls below `log` of the ground degeneracy —
the count of ground modes. "Cold resistance" at the
seat: entropy is floored by a COUNT (the shape of the
ground space), and the floor resists. -/
theorem gibbsEntropy_floor {E : Fin N → ℝ} {β : ℝ}
    (hβ : 0 ≤ β) :
    Real.log ((coldGround E).card : ℝ)
      ≤ entropyW (coldWeight β E) := by
  obtain ⟨i₀, _, hmin⟩ := Finset.exists_min_image Finset.univ E
    (Finset.univ_nonempty_iff.mpr ⟨⟨0, NeZero.pos N⟩⟩)
  have hi₀min : ∀ i, E i₀ ≤ E i := fun i => hmin i (Finset.mem_univ i)
  have hi₀mem : i₀ ∈ coldGround E :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ i₀, hi₀min⟩
  have hdeg1 : (1:ℝ) ≤ ((coldGround E).card : ℝ) := by
    have h0 : 0 < (coldGround E).card :=
      Finset.card_pos.mpr ⟨i₀, hi₀mem⟩
    exact_mod_cast Nat.succ_le_of_lt h0
  have hEconst : ∀ i ∈ coldGround E, E i = E i₀ :=
    fun i hi => le_antisymm
      ((Finset.mem_filter.mp hi).2 i₀) (hi₀min i)
  -- the partition sum dominates the ground block
  have hZfloor : ((coldGround E).card : ℝ)
        * Real.exp (-(β * E i₀)) ≤ coldPartition β E := by
    have h1 : ∑ i ∈ coldGround E, Real.exp (-(β * E i))
        ≤ coldPartition β E :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset _ _)
        (fun i _ _ => (Real.exp_pos _).le)
    have h2 : ∑ i ∈ coldGround E, Real.exp (-(β * E i))
        = ((coldGround E).card : ℝ) * Real.exp (-(β * E i₀)) := by
      rw [Finset.sum_congr rfl
        (fun i hi => by rw [hEconst i hi]), Finset.sum_const,
        nsmul_eq_mul]
    exact h2 ▸ h1
  -- so the ground weight is at most the reciprocal count
  have hw0 : coldWeight β E i₀ ≤ ((coldGround E).card : ℝ)⁻¹ := by
    have hstep : coldWeight β E i₀
        ≤ Real.exp (-(β * E i₀))
          / (((coldGround E).card : ℝ)
            * Real.exp (-(β * E i₀))) := by
      rw [coldWeight_eq]
      exact div_le_div_of_nonneg_left (Real.exp_pos _).le
        (mul_pos (lt_of_lt_of_le one_pos hdeg1) (Real.exp_pos _))
        hZfloor
    have heq : Real.exp (-(β * E i₀))
          / (((coldGround E).card : ℝ)
            * Real.exp (-(β * E i₀)))
        = ((coldGround E).card : ℝ)⁻¹ := by
      have hcard : ((coldGround E).card : ℝ) ≠ 0 :=
        ne_of_gt (lt_of_lt_of_le one_pos hdeg1)
      field_simp
    exact hstep.trans_eq heq
  -- and the entropy dominates minus the log ground weight
  have hSge : -Real.log (coldWeight β E i₀)
      ≤ entropyW (coldWeight β E) := by
    have hw_le : ∀ i, coldWeight β E i ≤ coldWeight β E i₀ := by
      intro i
      have hZpos := coldPartition_pos β E
      have hexp : Real.exp (-(β * E i))
          ≤ Real.exp (-(β * E i₀)) :=
        Real.exp_le_exp.mpr
          (neg_le_neg (mul_le_mul_of_nonneg_left (hi₀min i) hβ))
      rw [coldWeight_eq, coldWeight_eq]
      gcongr
    have hsum : ∑ i, coldWeight β E i * Real.log (coldWeight β E i)
        ≤ Real.log (coldWeight β E i₀) := by
      have hterm : ∀ i : Fin N, coldWeight β E i
            * Real.log (coldWeight β E i)
          ≤ coldWeight β E i * Real.log (coldWeight β E i₀) :=
        fun i => mul_le_mul_of_nonneg_left
          (Real.log_le_log (coldWeight_pos β E i) (hw_le i))
          (coldWeight_pos β E i).le
      have h2 : ∑ i, coldWeight β E i
            * Real.log (coldWeight β E i₀)
          = Real.log (coldWeight β E i₀) := by
        rw [← Finset.sum_mul, coldWeight_sum_one, one_mul]
      exact le_trans (Finset.sum_le_sum (fun i _ => hterm i))
        (le_of_eq h2)
    show -Real.log (coldWeight β E i₀)
      ≤ -∑ i, coldWeight β E i * Real.log (coldWeight β E i)
    exact neg_le_neg hsum
  -- assemble: `log card = −log (card⁻¹) ≤ −log w_{i₀} ≤ S`
  have hlog : Real.log (coldWeight β E i₀)
      ≤ Real.log (((coldGround E).card : ℝ)⁻¹) :=
    Real.log_le_log (coldWeight_pos β E i₀) hw0
  rw [Real.log_inv] at hlog
  linarith [hSge, hlog]

/-! ## §5 — the pairing card -/

/-- **D-5 (the pairing card):** one dial, two faces.
For `0 ≤ β₁ ≤ β₂`: the same step that lowers the
thermal density (hot side: content falls as it cools)
also lowers the entropy toward — never below — its
count floor (cold side). The density and the entropy
are the two faces of the one `β`. -/
theorem thermal_pairing {E : Fin N → ℝ} {β₁ β₂ : ℝ}
    (hβ₁ : 0 ≤ β₁) (hβ : β₁ ≤ β₂) :
    thermalDensity β₂ E ≤ thermalDensity β₁ E
    ∧ Real.log ((coldGround E).card : ℝ)
        ≤ entropyW (coldWeight β₂ E)
    ∧ entropyW (coldWeight β₂ E)
        ≤ entropyW (coldWeight β₁ E) :=
  ⟨thermalDensity_antitone hβ,
   gibbsEntropy_floor (le_trans hβ₁ hβ),
   gibbsEntropy_antitone hβ₁ hβ⟩

end ThetLogos
