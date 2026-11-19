/-
# StringChargeDensityPin — the weld: charge density on the thermal string seat

**Scope: ~/workspace/your_files/thermal-string-charge-density-pin-scope-2026-11-16.md
(Zero's seeing of 2026-11-15, "it's really just thermal string
charge density"; fired by his word "wled it", 2026-11-16 21:05 EST).
NO CLAIM. Dial-ineligible.**

WORKING LABEL: the module name `StringChargeDensityPin` is a
working label only — final naming is Zero's. Zero's name for the
combined object ("thermal string charge density") is his; this
module does not coin.

THE SEAT: a finite configuration model, in the exact idiom of
`StringSeatPin`. A chain of `n` links; each link carries a bend
state from `Fin (k+1)` (`0` = straight ahead, the rest = bends);
a CONFIGURATION is the tuple of link states; ENERGY is the total
bend content (the count of non-straight links). Gibbs weights over
the finite configuration set at slope `β`, on the corpus's own
finite-Gibbs machinery — `ModularVariance.gibbsProb` /
`gibbsExpect` at this energy. No parallel apparatus.

DISCLOSURE — SEAT REBUILT IN-MODULE: `StringSeatPin`'s source is
in the main tree and its module is in the census, but it is NOT in
this lane branch's ancestry. Per the scope's fallback, the
configuration shape (bend cost, bend energy, straight
configuration) is rebuilt here identically, on `ModularVariance`
directly — the `StringWindingPin` precedent on this same branch.

THE WELD: a CHARGE ASSIGNMENT `q : Fin n → ℤ` gives each site a
charge in `{−1, 0, +1}` (ternary, the program's grain) — a fixed
assignment per study, not summed over. The charge PRESENT at
site `i` in configuration `c` is the assigned charge when the
link at `i` is in its straight (ground) state, and `0` when the
link is bent: a bent link displaces its site's charge. The
DENSITY at site `i` at slope `β` is the Gibbs expectation of the
charge present at `i`. The straight configuration — the unique
energy minimiser — keeps every site's charge, so its charge
profile is `q` itself.

THE MENU (the scope's): C-1 bookkeeping (the profile sums to the
expected total charge — linearity); C-2 hot uniformity (at
`β = 0` the density is the plain average of the charge present,
over all configurations); C-3 charge-flip symmetry (negating the
assignment negates the profile at every `β`); C-4 cold
concentration (GAPFLOOR shape: for `β ≥ 0` the Gibbs weight on
non-minimal configurations is at most `(card(all) − 1)·e^{−β}`,
and each site's density deviates from its assigned charge by at
most that weight — the profile concentrates on the straight
configuration's charge profile, which is `q`); C-5 spread vs
concentrate (the honest finite form of the seeing's core: C-2 and
C-4 stated together — hot = averaged/spread, cold = concentrated
on the ground configurations — exactly that, no more).

FIDELITY FENCES (the scope's, in plain words):
- This is a finite classical Gibbs seat. No amplitudes, no
  interference, no measurement claim, no wave-particle
  identification. The pin does not discharge the seeing; it
  seats its finite shadow. K-STRING-PHYS armed.
- No Planck scale is declared or needed; no physical units
  anywhere in the module. K-PLANCK-SEAT respected.
- Constructed-target exposure: the charge assignment is CHOSEN,
  the seat is finite, and the density is an expectation over a
  classical ensemble — disclosed wherever the pin is cited.

STATUS: STATUS-STRINGCHARGE.md.
-/

import Mathlib.Tactic
import ThetLogos.ModularVariance

namespace ThetLogos.StringChargeDensityPin

variable {n k : ℕ}

/-! ## §1 — the seat (rebuilt in-module; see the header disclosure) -/

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
least bend cost, `1` — the seat's gap. -/
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

/-! ## §2 — the charge layer; C-1, C-2, C-3 -/

/-- **Charge present at a site**: the charge a configuration
`c` carries at site `i` under the assignment `q` — the
assigned charge `(q i : ℝ)` when the link at `i` is in its
straight (ground) state, and `0` when the link is bent: a
bent link displaces its site's charge. -/
noncomputable def chargeAt (q : Fin n → ℤ) (c : Fin n → Fin (k + 1))
    (i : Fin n) : ℝ :=
  if c i = 0 then (q i : ℝ) else 0

/-- **Total charge present in a configuration**: the sum
over sites of the charge present, `∑ i, chargeAt q c i` —
the configuration-level observable whose Gibbs expectation
C-1 identifies with the summed density profile. (The
assignment's own total is `∑ i, q i`; the two agree on the
straight configuration, by `chargeAt_straightConfig`.) -/
noncomputable def totalCharge (q : Fin n → ℤ)
    (c : Fin n → Fin (k + 1)) : ℝ :=
  ∑ i, chargeAt q c i

/-- **Charge density at a site**: the Gibbs expectation of
the charge present at site `i`, over configurations
weighted by bend energy at slope `β` — the weld's central
object: ThermalDensityPin's "density as a function of
thermal state" seated on StringSeatPin's string. -/
noncomputable def density (k : ℕ) (q : Fin n → ℤ) (β : ℝ) (i : Fin n) : ℝ :=
  ModularVariance.gibbsExpect (bendEnergy : (Fin n → Fin (k + 1)) → ℝ) β
    (fun c => chargeAt q c i)

/-- The straight configuration keeps every site's charge:
its charge profile is the assignment itself. This is the
profile C-4 concentrates on. -/
theorem chargeAt_straightConfig (q : Fin n → ℤ) (i : Fin n) :
    chargeAt q (straightConfig : Fin n → Fin (k + 1)) i = (q i : ℝ) := by
  simp [chargeAt, straightConfig]

/-- **C-1 (bookkeeping)**: the density profile sums to the
Gibbs expectation of the total charge present — linearity
of expectation over the sites; the profile is a genuine
decomposition of the mean total. -/
theorem density_sum (q : Fin n → ℤ) (β : ℝ) :
    ∑ i, density k q β i
      = ModularVariance.gibbsExpect (bendEnergy : (Fin n → Fin (k + 1)) → ℝ) β
          ((totalCharge q) : (Fin n → Fin (k + 1)) → ℝ) := by
  unfold density ModularVariance.gibbsExpect totalCharge
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun c _ =>
    (Finset.mul_sum Finset.univ (fun i => chargeAt q c i)
      (ModularVariance.gibbsProb bendEnergy β c)).symm)

/-- **C-2 (hot uniformity)**: at `β = 0` the density at a
site is the plain average of the charge present at that
site over all configurations — no thermal selection, the
charge reads as its unweighted mean: the spread end of
the profile. -/
theorem density_zero (q : Fin n → ℤ) (i : Fin n) :
    density k q 0 i
      = (∑ c : Fin n → Fin (k + 1), chargeAt q c i)
        / (Fintype.card (Fin n → Fin (k + 1)) : ℝ) := by
  have hZ : ModularVariance.partSum
        (bendEnergy : (Fin n → Fin (k + 1)) → ℝ) 0
      = (Fintype.card (Fin n → Fin (k + 1)) : ℝ) := by
    unfold ModularVariance.partSum
    simp
  have hterm : ∀ c : Fin n → Fin (k + 1),
      ModularVariance.gibbsProb bendEnergy 0 c
        = ((Fintype.card (Fin n → Fin (k + 1)) : ℝ))⁻¹ := by
    intro c
    unfold ModularVariance.gibbsProb
    rw [hZ]
    simp
  have havg : density k q 0 i
      = ((Fintype.card (Fin n → Fin (k + 1)) : ℝ))⁻¹
        * ∑ c : Fin n → Fin (k + 1), chargeAt q c i := by
    unfold density ModularVariance.gibbsExpect
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun c _ => by rw [hterm c])
  rw [havg, div_eq_mul_inv, mul_comm]

/-- **C-3 (charge-flip symmetry)**: negating the assignment
negates the density profile, at every `β` — the ensemble
is blind to the sign convention of the assignment; only
the assignment's own sign flips. -/
theorem density_neg (q : Fin n → ℤ) (β : ℝ) (i : Fin n) :
    density k (fun j => -(q j)) β i = - density k q β i := by
  have hAt : ∀ c : Fin n → Fin (k + 1),
      chargeAt (fun j => -(q j)) c i = - chargeAt q c i := by
    intro c
    unfold chargeAt
    by_cases hc : c i = 0
    · rw [if_pos hc, if_pos hc]
      simp
    · rw [if_neg hc, if_neg hc, neg_zero]
  unfold density
  rw [show (fun c : Fin n → Fin (k + 1) => chargeAt (fun j => -(q j)) c i)
        = (fun c : Fin n → Fin (k + 1) => (-1 : ℝ) * chargeAt q c i) from
      funext fun c => by rw [hAt c]; ring]
  rw [ModularVariance.gibbsExpect_const_mul]
  ring

/-! ## §3 — cold concentration (C-4) and the spread/concentrate pair (C-5) -/

/-- **C-4, the weight half (cold concentration of the
ensemble)**: for `β ≥ 0`, the total Gibbs weight on the
non-straight configurations is at most
`(#configurations − 1) · e^{−β}` — GAPFLOOR-1's bound on
this seat's spectrum, with the seat's gap `1` (every
excited configuration pays at least the least bend cost
in its Boltzmann factor, and the partition sum is at
least the ground term `1`). -/
theorem cold_weight (hβ : 0 ≤ β) :
    ∑ c ∈ Finset.univ \ {(straightConfig : Fin n → Fin (k + 1))},
        ModularVariance.gibbsProb bendEnergy β c
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
      ModularVariance.gibbsProb bendEnergy β c
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
          ModularVariance.gibbsProb bendEnergy β c
      ≤ ∑ c ∈ Finset.univ \ {(straightConfig : Fin n → Fin (k + 1))},
          Real.exp (-β) := Finset.sum_le_sum hterm
    _ = ((Fintype.card (Fin n → Fin (k + 1)) : ℝ) - 1)
          * Real.exp (-β) := by
        rw [Finset.sum_const, Finset.card_sdiff, Finset.inter_univ,
          Finset.card_singleton, Finset.card_univ, nsmul_eq_mul,
          Nat.cast_sub Fintype.card_pos, Nat.cast_one]

/-- Helper for C-4: a site's present charge never deviates
from its assigned charge by more than `1` — the present
charge is either the assigned charge itself (straight
link, deviation `0`) or `0` (bent link, deviation the
assigned charge, of absolute value at most `1` for a
ternary assignment). -/
theorem chargeAt_sub_abs_le (q : Fin n → ℤ) (hq : ∀ j, |q j| ≤ 1)
    (c : Fin n → Fin (k + 1)) (i : Fin n) :
    |chargeAt q c i - (q i : ℝ)| ≤ 1 := by
  unfold chargeAt
  by_cases hc : c i = 0
  · rw [if_pos hc, sub_self, abs_zero]
    exact zero_le_one
  · rw [if_neg hc, zero_sub, abs_neg, ← Int.cast_abs]
    exact_mod_cast hq i

/-- **C-4, the density half (cold concentration of the
profile)**: for a ternary assignment and `β ≥ 0`, each
site's density deviates from its assigned charge by at
most the non-minimal Gibbs weight `(card(all) − 1)·e^{−β}`
— as `β` grows the profile concentrates on the straight
configuration's charge profile, which is the assignment
itself (`chargeAt_straightConfig`). The deviation is the
Gibbs mean of the per-configuration deviation; the
straight term vanishes and every other term is bounded
by its own Gibbs weight times `1`. -/
theorem density_deviation (q : Fin n → ℤ) (hq : ∀ j, |q j| ≤ 1)
    (hβ : 0 ≤ β) (i : Fin n) :
    |density k q β i - (q i : ℝ)|
      ≤ ((Fintype.card (Fin n → Fin (k + 1)) : ℝ) - 1)
        * Real.exp (-β) := by
  have hsum1 : ∑ c : Fin n → Fin (k + 1),
      ModularVariance.gibbsProb bendEnergy β c = 1 :=
    ModularVariance.sum_gibbsProb _ _
  have hqi : (∑ c : Fin n → Fin (k + 1),
      ModularVariance.gibbsProb bendEnergy β c * (q i : ℝ))
      = (q i : ℝ) := by
    rw [← Finset.sum_mul, hsum1, one_mul]
  have hdiff : density k q β i - (q i : ℝ)
      = ∑ c : Fin n → Fin (k + 1),
          ModularVariance.gibbsProb bendEnergy β c
            * (chargeAt q c i - (q i : ℝ)) := by
    unfold density ModularVariance.gibbsExpect
    simp only [mul_sub, Finset.sum_sub_distrib]
    rw [hqi]
  have hsplit : ∀ (f : (Fin n → Fin (k + 1)) → ℝ),
      (∑ c, f c)
        = ∑ c ∈ Finset.univ \ {(straightConfig : Fin n → Fin (k + 1))}, f c
          + f (straightConfig : Fin n → Fin (k + 1)) := by
    intro f
    rw [← Finset.sum_sdiff (Finset.subset_univ _),
      Finset.sum_singleton]
  calc |density k q β i - (q i : ℝ)|
      = |∑ c : Fin n → Fin (k + 1),
          ModularVariance.gibbsProb bendEnergy β c
            * (chargeAt q c i - (q i : ℝ))| := by rw [hdiff]
    _ ≤ ∑ c : Fin n → Fin (k + 1),
          |ModularVariance.gibbsProb bendEnergy β c
            * (chargeAt q c i - (q i : ℝ))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ c ∈ Finset.univ \ {(straightConfig : Fin n → Fin (k + 1))},
          ModularVariance.gibbsProb bendEnergy β c := by
        rw [hsplit]
        simp only [chargeAt_straightConfig, sub_self, mul_zero,
          abs_zero, add_zero]
        apply Finset.sum_le_sum
        intro c _
        rw [abs_mul, abs_of_pos (ModularVariance.gibbsProb_pos _ _ _)]
        calc ModularVariance.gibbsProb bendEnergy β c
              * |chargeAt q c i - (q i : ℝ)|
            ≤ ModularVariance.gibbsProb bendEnergy β c * 1 :=
              mul_le_mul_of_nonneg_left
                (chargeAt_sub_abs_le q hq c i)
                (ModularVariance.gibbsProb_pos _ _ _).le
          _ = ModularVariance.gibbsProb bendEnergy β c := mul_one _
    _ ≤ ((Fintype.card (Fin n → Fin (k + 1)) : ℝ) - 1)
          * Real.exp (-β) := cold_weight hβ

/-- **C-5 (spread vs concentrate — the seeing's core, in
its honest finite form)**: one assignment, one ensemble,
two ends. HOT: at `β = 0` the density at a site is the
plain average of the charge present over all
configurations (C-2) — the charge reads spread over the
whole ensemble. COLD: at every `β ≥ 0` the density
deviates from the assigned charge by at most
`(card(all) − 1)·e^{−β}` (C-4), a bound that dies as
`β → ∞` — the profile concentrates on the straight
configuration's charge profile, the assignment itself.
Temperature sets how the charge spreads or concentrates
— stated as exactly this pair, no more. -/
theorem hot_cold_profile (q : Fin n → ℤ) (hq : ∀ j, |q j| ≤ 1)
    (i : Fin n) :
    (density k q 0 i
      = (∑ c : Fin n → Fin (k + 1), chargeAt q c i)
        / (Fintype.card (Fin n → Fin (k + 1)) : ℝ))
    ∧ (∀ β : ℝ, 0 ≤ β → |density k q β i - (q i : ℝ)|
        ≤ ((Fintype.card (Fin n → Fin (k + 1)) : ℝ) - 1)
          * Real.exp (-β)) :=
  ⟨density_zero q i, fun β hβ => density_deviation q hq hβ i⟩

end ThetLogos.StringChargeDensityPin
