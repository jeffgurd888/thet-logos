/-
# StringSeatPin — the string seat: a finite bendable chain

**Scope: ~/workspace/your_files/string-seat-pin-scope-2026-11-13.md
(Zero's string thread, 2026-11-13 19:04–19:10 EST;
commissioned "scope it" 2026-11-13 19:10 EST).
NO CLAIM. Dial-ineligible.**

THE SEAT: a finite configuration model. A chain of `n`
links; each link carries a bend state from `Fin (k+1)`
(`0` = straight ahead, the rest = bends); a
CONFIGURATION is the tuple of link states; ENERGY is
the total bend content (the count of non-straight
links). Gibbs weights over the finite configuration
set at slope `β`, on the corpus's own finite-Gibbs
machinery — `ModularVariance.gibbsProb` at this
energy, the HotColdLimits / GAPFLOOR seat. The
straight configuration is the unique energy
minimiser, the string's floor.

THE MENU (the scope's): S-1 cold straightens (the
straight configuration's Gibbs probability strictly
increasing in `β`); S-2 heat excites (expected bend
content strictly decreasing in `β`); S-3 hot
uniformity (at `β = 0` all configurations carry equal
weight); S-4 cold concentration (the GAPFLOOR-1
bound on the configuration spectrum, proved at this
seat; the general Hermitian form is `GibbsGapFloor`'s,
cited by name — that module is not in this branch's
ancestry, the GapLine / HotColdLimits precedent);
S-5 the pair card (two Gibbs states of one
configuration set).

FIDELITY FENCES (the scope's, in plain words):
- The pin's "knot" is BEND CONTENT — the countable
  shadow — NOT topological knot type. K-STRING-KNOT
  armed: any statement from this seat about actual
  knots is void.
- The pin is a finite toy. It does NOT model a
  physical string's mechanics. K-STRING-PHYS armed.
  No gravity (K-DENSITY-GRAV governs). No falling,
  drag or packing; no chord geometry; no continuum
  filament.
- Constructed-target exposure: the correspondence
  to the source picture is by CONSTRUCTION of the
  model (configurations, bend cost, floor), and is
  disclosed wherever the pin is cited.

STATUS: STATUS-STRINGSEAT.md.
-/

import Mathlib.Tactic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Data.Fintype.Card
import ThetLogos.ModularVariance

namespace ThetLogos.StringSeatPin

variable {n k : ℕ}

/-! ## §1 — the model -/

/-- **Bend cost of one link state**: `0` at the straight
state, `1` at any bent state. The countable shadow of
bending at one link. -/
noncomputable def bendCost (s : Fin (k + 1)) : ℝ :=
  if s = 0 then 0 else 1

/-- **Bend energy of a configuration**: the total bend
content, `∑ i, bendCost (c i)`. -/
noncomputable def bendEnergy (c : Fin n → Fin (k + 1)) : ℝ :=
  ∑ i, bendCost (c i)

/-- **The straight configuration**: every link straight. -/
def straightConfig : Fin n → Fin (k + 1) :=
  fun _ => 0

theorem bendCost_nonneg (s : Fin (k + 1)) : 0 ≤ bendCost s := by
  unfold bendCost
  split_ifs <;> norm_num

theorem bendCost_eq_zero_iff (s : Fin (k + 1)) :
    bendCost s = 0 ↔ s = 0 := by
  unfold bendCost
  split_ifs with h
  · simp [h]
  · simp [h]

theorem bendEnergy_nonneg (c : Fin n → Fin (k + 1)) :
    0 ≤ bendEnergy c :=
  Finset.sum_nonneg (fun i _ => bendCost_nonneg (c i))

theorem bendEnergy_straightConfig :
    bendEnergy (straightConfig : Fin n → Fin (k + 1)) = 0 := by
  simp [bendEnergy, straightConfig, bendCost]

/-- The straight configuration is the UNIQUE energy
minimiser: energy vanishes exactly there. -/
theorem bendEnergy_eq_zero_iff (c : Fin n → Fin (k + 1)) :
    bendEnergy c = 0 ↔ c = straightConfig := by
  constructor
  · intro h
    have h' : (∑ i, bendCost (c i)) = 0 := h
    have hterm : ∀ i ∈ (Finset.univ : Finset (Fin n)),
        bendCost (c i) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun i _ => bendCost_nonneg (c i))).mp h'
    funext i
    exact (bendCost_eq_zero_iff (c i)).mp (hterm i (Finset.mem_univ i))
  · intro h
    rw [h]
    exact bendEnergy_straightConfig

/-- Every non-straight configuration pays at least the
least bend cost, `1`. -/
theorem one_le_bendEnergy {c : Fin n → Fin (k + 1)}
    (hc : c ≠ straightConfig) : 1 ≤ bendEnergy c := by
  obtain ⟨i, hi⟩ : ∃ i, c i ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hc (funext fun i => hcon i)
  have hcost : bendCost (c i) = 1 := by
    unfold bendCost
    rw [if_neg hi]
  calc (1 : ℝ) = bendCost (c i) := hcost.symm
    _ ≤ ∑ j, bendCost (c j) :=
        Finset.single_le_sum (fun j _ => bendCost_nonneg (c j))
          (Finset.mem_univ i)
    _ = bendEnergy c := rfl

/-! ## §2 — hot uniformity (S-3) and cold straightens (S-1) -/

/-- **General helper**: for nonnegative energies with at
least one positive level, the partition sum is strictly
antitone in `β` — its derivative is a sum of nonnegative
terms, one of them strictly positive. -/
theorem partSum_strictAnti_of_nonneg {ι : Type*} [Fintype ι]
    [Nonempty ι] (E : ι → ℝ) (hE : ∀ i, 0 ≤ E i)
    (hpos : ∃ i, 0 < E i) :
    StrictAnti (ModularVariance.partSum E) := by
  apply strictAnti_of_deriv_neg
  intro β
  rw [(ModularVariance.hasDerivAt_partSum E β).deriv]
  rw [neg_lt_zero]
  apply Finset.sum_pos'
  · intro i _
    exact mul_nonneg (hE i) (Real.exp_pos _).le
  · obtain ⟨i, hi⟩ := hpos
    exact ⟨i, Finset.mem_univ i, mul_pos hi (Real.exp_pos _)⟩

theorem card_config :
    Fintype.card (Fin n → Fin (k + 1)) = (k + 1) ^ n := by
  rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]

/-- **S-3 (hot uniformity)**: at `β = 0` every
configuration carries the same Gibbs weight,
`1 / #configurations` — no selection without a slope. -/
theorem gibbsProb_zero (c : Fin n → Fin (k + 1)) :
    ModularVariance.gibbsProb bendEnergy 0 c
      = (Fintype.card (Fin n → Fin (k + 1)) : ℝ)⁻¹ := by
  have hZ : ModularVariance.partSum
        (bendEnergy : (Fin n → Fin (k + 1)) → ℝ) 0
      = (Fintype.card (Fin n → Fin (k + 1)) : ℝ) := by
    unfold ModularVariance.partSum
    simp
  unfold ModularVariance.gibbsProb
  rw [hZ]
  simp

/-- The straight configuration's Gibbs probability is
the reciprocal partition sum (its Boltzmann factor is
`e⁰ = 1`). -/
theorem gibbsProb_straightConfig_eq (β : ℝ) :
    ModularVariance.gibbsProb bendEnergy β
        (straightConfig : Fin n → Fin (k + 1))
      = (ModularVariance.partSum
          (bendEnergy : (Fin n → Fin (k + 1)) → ℝ) β)⁻¹ := by
  unfold ModularVariance.gibbsProb
  rw [bendEnergy_straightConfig]
  simp

/-- **S-1 (cold straightens)**: the Gibbs probability
of the straight configuration is strictly increasing
in `β` — the colder, the straighter. -/
theorem cold_straightens (hn : 0 < n) (hk : 0 < k) :
    StrictMono (fun β => ModularVariance.gibbsProb bendEnergy β
      (straightConfig : Fin n → Fin (k + 1))) := by
  obtain ⟨s, hs⟩ : ∃ s : Fin (k + 1), s ≠ 0 := by
    have hcard : 1 < Fintype.card (Fin (k + 1)) := by
      rw [Fintype.card_fin]
      omega
    obtain ⟨b, hb⟩ :=
      Fintype.exists_ne_of_one_lt_card hcard (0 : Fin (k + 1))
    exact ⟨b, hb⟩
  have hbend : bendEnergy ((fun _ => s) : Fin n → Fin (k + 1))
      = (n : ℝ) := by
    simp [bendEnergy, bendCost, hs]
  have hanti : StrictAnti (ModularVariance.partSum
        (bendEnergy : (Fin n → Fin (k + 1)) → ℝ)) := by
    apply partSum_strictAnti_of_nonneg
      (ι := Fin n → Fin (k + 1)) bendEnergy bendEnergy_nonneg
    exact ⟨((fun _ => s) : Fin n → Fin (k + 1)), by
      rw [hbend]
      exact_mod_cast hn⟩
  intro a b hab
  show ModularVariance.gibbsProb bendEnergy a
        (straightConfig : Fin n → Fin (k + 1))
      < ModularVariance.gibbsProb bendEnergy b
        (straightConfig : Fin n → Fin (k + 1))
  rw [gibbsProb_straightConfig_eq, gibbsProb_straightConfig_eq]
  rw [inv_eq_one_div, inv_eq_one_div]
  exact one_div_lt_one_div_of_lt
    (ModularVariance.partSum_pos
      (bendEnergy : (Fin n → Fin (k + 1)) → ℝ) b) (hanti hab)

/-! ## §3 — heat excites (S-2) -/

/-- **General helper**: at a nonconstant energy, the
mean energy is strictly antitone in `β` — its
derivative is minus the energy variance, which is
strictly positive exactly at a nonconstant energy
(`ModularVariance.varEnergy_pos_iff`). -/
theorem meanEnergy_strictAnti_of_nonconstant {ι : Type*}
    [Fintype ι] [Nonempty ι] (E : ι → ℝ)
    (h : ∃ i j, E i ≠ E j) :
    StrictAnti (fun β => ModularVariance.meanEnergy E β) := by
  apply strictAnti_of_deriv_neg
  intro β
  rw [(ModularVariance.hasDerivAt_meanEnergy E β).deriv]
  exact neg_lt_zero.mpr
    ((ModularVariance.varEnergy_pos_iff E β).mpr h)

/-- **S-2 (heat excites)**: the Gibbs expected bend
content is strictly decreasing in `β` — the hotter,
the more bent. -/
theorem heat_excites (hn : 0 < n) (hk : 0 < k) :
    StrictAnti (fun β => ModularVariance.meanEnergy
      (bendEnergy : (Fin n → Fin (k + 1)) → ℝ) β) := by
  apply meanEnergy_strictAnti_of_nonconstant
  obtain ⟨s, hs⟩ : ∃ s : Fin (k + 1), s ≠ 0 := by
    have hcard : 1 < Fintype.card (Fin (k + 1)) := by
      rw [Fintype.card_fin]
      omega
    obtain ⟨b, hb⟩ :=
      Fintype.exists_ne_of_one_lt_card hcard (0 : Fin (k + 1))
    exact ⟨b, hb⟩
  have hbend : bendEnergy ((fun _ => s) : Fin n → Fin (k + 1))
      = (n : ℝ) := by
    simp [bendEnergy, bendCost, hs]
  refine ⟨(straightConfig : Fin n → Fin (k + 1)),
    ((fun _ => s) : Fin n → Fin (k + 1)), ?_⟩
  rw [bendEnergy_straightConfig, hbend]
  exact_mod_cast hn.ne

/-! ## §4 — cold concentration (S-4) -/

/-- **S-4 (cold concentration)**: for `β ≥ 0`, the
total Gibbs weight on the non-straight configurations
is at most `(#excited configurations) · e^{−β}` —
GAPFLOOR-1's bound on this seat's configuration
spectrum: every excited configuration pays at least
the least bend cost `1` in its Boltzmann factor, and
the partition sum is at least the ground term `1`.
(The general Hermitian-seat form is `GibbsGapFloor`'s,
cited by name on the module's face.) -/
theorem cold_concentration (hβ : 0 ≤ β) :
    ∑ c ∈ Finset.univ \ {(straightConfig : Fin n → Fin (k + 1))},
        ModularVariance.gibbsProb
          (bendEnergy : (Fin n → Fin (k + 1)) → ℝ) β c
      ≤ ((Fintype.card (Fin n → Fin (k + 1)) : ℝ) - 1)
        * Real.exp (-β) := by
  have hZ1 : (1 : ℝ) ≤ ModularVariance.partSum
      (bendEnergy : (Fin n → Fin (k + 1)) → ℝ) β := by
    have h := Finset.single_le_sum
      (f := fun c : Fin n → Fin (k + 1) =>
        Real.exp (-(β * bendEnergy c)))
      (fun c _ => (Real.exp_pos _).le)
      (Finset.mem_univ (straightConfig : Fin n → Fin (k + 1)))
    rw [bendEnergy_straightConfig, mul_zero, neg_zero,
      Real.exp_zero] at h
    exact h
  have hterm : ∀ c ∈ Finset.univ
        \ {(straightConfig : Fin n → Fin (k + 1))},
      ModularVariance.gibbsProb
          (bendEnergy : (Fin n → Fin (k + 1)) → ℝ) β c
        ≤ Real.exp (-β) := by
    intro c hc
    have hcne : c ≠ (straightConfig : Fin n → Fin (k + 1)) := by
      rw [Finset.mem_sdiff] at hc
      exact fun h => hc.2 (Finset.mem_singleton.mpr h)
    have hEc : (1 : ℝ) ≤ bendEnergy c := one_le_bendEnergy hcne
    unfold ModularVariance.gibbsProb
    rw [div_le_iff₀ (ModularVariance.partSum_pos
      (bendEnergy : (Fin n → Fin (k + 1)) → ℝ) β)]
    calc Real.exp (-(β * bendEnergy c)) ≤ Real.exp (-β) := by
          apply Real.exp_le_exp.mpr
          rw [neg_le_neg_iff]
          calc β = β * 1 := (mul_one β).symm
            _ ≤ β * bendEnergy c :=
                mul_le_mul_of_nonneg_left hEc hβ
      _ ≤ Real.exp (-β) * ModularVariance.partSum
            (bendEnergy : (Fin n → Fin (k + 1)) → ℝ) β :=
          le_mul_of_one_le_right (Real.exp_pos _).le hZ1
  calc ∑ c ∈ Finset.univ \ {(straightConfig : Fin n → Fin (k + 1))},
          ModularVariance.gibbsProb
            (bendEnergy : (Fin n → Fin (k + 1)) → ℝ) β c
      ≤ ∑ c ∈ Finset.univ \ {(straightConfig : Fin n → Fin (k + 1))},
          Real.exp (-β) := Finset.sum_le_sum hterm
    _ = ((Fintype.card (Fin n → Fin (k + 1)) : ℝ) - 1)
          * Real.exp (-β) := by
        rw [Finset.sum_const, Finset.card_sdiff, Finset.inter_univ,
          Finset.card_singleton, Finset.card_univ, nsmul_eq_mul,
          Nat.cast_sub Fintype.card_pos, Nat.cast_one]

/-! ## §5 — the pair card (S-5) -/

/-- **S-5, the selection half of the pair card**: at
every `β > 0` the straight configuration is strictly
more probable than any bent configuration — the same
configuration set that carries no selection at
`β = 0` (S-3) is selected on as soon as a slope
exists. -/
theorem gibbsProb_straightConfig_gt (hβ : 0 < β)
    {c : Fin n → Fin (k + 1)}
    (hc : c ≠ (straightConfig : Fin n → Fin (k + 1))) :
    ModularVariance.gibbsProb
        (bendEnergy : (Fin n → Fin (k + 1)) → ℝ) β c
      < ModularVariance.gibbsProb
          (bendEnergy : (Fin n → Fin (k + 1)) → ℝ) β
          (straightConfig : Fin n → Fin (k + 1)) := by
  have hEc : (1 : ℝ) ≤ bendEnergy c := one_le_bendEnergy hc
  have hexp : Real.exp (-(β * bendEnergy c)) < 1 := by
    rw [Real.exp_lt_one_iff]
    apply neg_lt_zero.mpr
    calc (0 : ℝ) < β := hβ
      _ = β * 1 := (mul_one β).symm
      _ ≤ β * bendEnergy c :=
          mul_le_mul_of_nonneg_left hEc hβ.le
  unfold ModularVariance.gibbsProb
  rw [bendEnergy_straightConfig, mul_zero, neg_zero,
    Real.exp_zero]
  rw [div_lt_iff₀ (ModularVariance.partSum_pos
      (bendEnergy : (Fin n → Fin (k + 1)) → ℝ) β),
    one_div_mul_cancel (ne_of_gt (ModularVariance.partSum_pos
      (bendEnergy : (Fin n → Fin (k + 1)) → ℝ) β))]
  exact hexp

/-- **S-5 (the pair card)**: one chain, one spectrum,
two limits — the hot state (`β = 0`, uniform by S-3)
and any cold state (`β > 0`) are DIFFERENT Gibbs
states of the same configuration set: the
same-but-different pair. They already differ at the
straight configuration, where the cold state
concentrates strictly more than the uniform share
(S-1's mechanism at the value level). -/
theorem gibbsProb_pair_ne (hn : 0 < n) (hk : 0 < k)
    (hβ : 0 < β) :
    ModularVariance.gibbsProb
        (bendEnergy : (Fin n → Fin (k + 1)) → ℝ) 0
      ≠ ModularVariance.gibbsProb
          (bendEnergy : (Fin n → Fin (k + 1)) → ℝ) β := by
  intro hcon
  have hval := congrFun hcon
    (straightConfig : Fin n → Fin (k + 1))
  rw [gibbsProb_zero, gibbsProb_straightConfig_eq] at hval
  have hZlt : ModularVariance.partSum
        (bendEnergy : (Fin n → Fin (k + 1)) → ℝ) β
      < (Fintype.card (Fin n → Fin (k + 1)) : ℝ) := by
    show (∑ c : Fin n → Fin (k + 1),
        Real.exp (-(β * bendEnergy c)))
      < (Fintype.card (Fin n → Fin (k + 1)) : ℝ)
    have hcard : (Fintype.card (Fin n → Fin (k + 1)) : ℝ)
        = ∑ c : Fin n → Fin (k + 1), (1 : ℝ) := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        mul_one]
    rw [hcard]
    apply Finset.sum_lt_sum
    · intro c _
      rw [Real.exp_le_one_iff]
      exact neg_nonpos.mpr
        (mul_nonneg hβ.le (bendEnergy_nonneg c))
    · obtain ⟨s, hs⟩ : ∃ s : Fin (k + 1), s ≠ 0 := by
        have hcard2 : 1 < Fintype.card (Fin (k + 1)) := by
          rw [Fintype.card_fin]
          omega
        obtain ⟨b, hb⟩ := Fintype.exists_ne_of_one_lt_card
          hcard2 (0 : Fin (k + 1))
        exact ⟨b, hb⟩
      have hbend : bendEnergy ((fun _ => s) : Fin n → Fin (k + 1))
          = (n : ℝ) := by
        simp [bendEnergy, bendCost, hs]
      refine ⟨((fun _ => s) : Fin n → Fin (k + 1)),
        Finset.mem_univ _, ?_⟩
      rw [Real.exp_lt_one_iff, hbend]
      exact neg_lt_zero.mpr
        (mul_pos hβ (by exact_mod_cast hn))
  have hlt : (Fintype.card (Fin n → Fin (k + 1)) : ℝ)⁻¹
      < (ModularVariance.partSum
          (bendEnergy : (Fin n → Fin (k + 1)) → ℝ) β)⁻¹ := by
    rw [inv_eq_one_div, inv_eq_one_div]
    exact one_div_lt_one_div_of_lt
      (ModularVariance.partSum_pos
        (bendEnergy : (Fin n → Fin (k + 1)) → ℝ) β) hZlt
  exact (ne_of_lt hlt) hval

end ThetLogos.StringSeatPin
