/-
# StringWindingPin — the winding seat: a finite path with endpoint displacement

**Scope: ~/workspace/your_files/string-winding-pin-scope-2026-11-16.md
(Zero's dropped thermal-string formula, 2026-11-16 14:43 EST;
the finite flag fired by his word "fire it", 2026-11-16 14:45 EST).
NO CLAIM. Dial-ineligible.**

WORKING LABEL: the module name `StringWindingPin` is a
working label only — final naming is Zero's. This module
is NOT the continuum object of the dropped formula and
does not name itself after it.

THE SEAT: a finite configuration model, in the exact
idiom of `StringSeatPin`. A chain of `n` links; each link
carries a step state from `Fin 3` (`0` = down, `1` = flat,
`2` = up); a CONFIGURATION is the tuple of link states.
The WINDING of a configuration is its total displacement
`∑ i, stepValue (s i)` in `ℤ` — the endpoint height, the
finite reading of the dropped formula's winding condition
(a path that ends `w` lattice units above where it
started). The ENERGY is the total variation
`∑ i, |stepValue (s i)|` — how much climbing the path
does in total. Gibbs weights over the finite
configuration set at slope `β`, on the corpus's own
finite-Gibbs machinery — `ModularVariance.gibbsProb` /
`partSum` at this energy. No parallel apparatus.

THE MENU (the scope's): W-1 the winding bound
(`|winding| ≤ n`; sectors beyond are empty); W-2 energy
dominates winding; W-3 sharpness (every sector with
`|w| ≤ n` is achieved, by a monotone ramp paying exactly
`|w|`); W-4 reflection (the linkwise up/down flip negates
the winding and preserves the energy); W-5 the sector
decomposition of the partition sum; W-6 sector
reflection symmetry (`Z_{-w}(β) = Z_w(β)`); W-7 the hot
sector card (at `β = 0` a sector's Gibbs probability is
its share of all configurations); W-8 cold unwinds
(nonzero winding carries Gibbs weight at most
`(card(all) − 1) · e^{−β}` for `β ≥ 0` — the GAPFLOOR-1
concentration shape read across sectors).

FIDELITY FENCES (the scope's, in plain words):
- The pin's "winding" is ENDPOINT DISPLACEMENT of a
  finite path — an integer, NOT topological knot type.
  K-STRING-KNOT armed: any statement from this seat
  about actual knots is void.
- The pin is a finite toy seat. It is NOT a physical or
  continuum string: no continuum maps, no Virasoro
  constraints, no GSO projection (no worldsheet fermions
  exist in this corpus), no Hagedorn claim.
  K-STRING-PHYS armed. The established theory's thermal
  winding sectors are the external rhyme (Register 2),
  cited, never built.
- Constructed-target exposure: the correspondence to
  the dropped formula is by CONSTRUCTION of the model
  (steps, displacement, variation energy), and is
  disclosed wherever the pin is cited.

STATUS: STATUS-STRINGWINDING.md.
-/

import Mathlib.Tactic
import ThetLogos.ModularVariance

namespace ThetLogos.StringWindingPin

variable {n : ℕ}

/-! ## §1 — the model -/

/-- **Step value of one link state**: `0 ↦ -1` (down),
`1 ↦ 0` (flat), `2 ↦ +1` (up) — `a.val - 1` in `ℤ`. -/
def stepValue (a : Fin 3) : ℤ :=
  (a.val : ℤ) - 1

/-- **Winding of a configuration**: the total
displacement `∑ i, stepValue (s i)` — the endpoint
height of the finite path. -/
def winding (s : Fin n → Fin 3) : ℤ :=
  ∑ i, stepValue (s i)

/-- **Step energy of a configuration**: the total
variation `∑ i, |stepValue (s i)|`. -/
def stepEnergy (s : Fin n → Fin 3) : ℤ :=
  ∑ i, |stepValue (s i)|

/-- **The linkwise flip**: swaps down (`0`) and up (`2`),
fixes flat (`1`). The finite reflection of one link. -/
def stepFlip (a : Fin 3) : Fin 3 :=
  ⟨2 - a.val, by have h := a.isLt; omega⟩

/-! ## §2 — Brick 1: the sector basics (W-1..W-4) -/

/-- **W-1 (winding bound)**: every configuration's
winding lies in `[-n, n]`; sectors with `|w| > n` are
empty. -/
theorem winding_abs_le (s : Fin n → Fin 3) :
    |winding s| ≤ (n : ℤ) := by
  have habs : ∀ a : Fin 3, |stepValue a| ≤ 1 := by
    intro a
    have h1 : a.val ≤ 2 := by have h := a.isLt; omega
    have h3 : (0 : ℤ) ≤ (a.val : ℤ) := by exact_mod_cast Nat.zero_le _
    have h4 : ((a.val : ℤ)) ≤ 2 := by exact_mod_cast h1
    rw [show stepValue a = (a.val : ℤ) - 1 from rfl, abs_le]
    constructor <;> omega
  calc |winding s| = |∑ i, stepValue (s i)| := rfl
    _ ≤ ∑ i, |stepValue (s i)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin n, (1 : ℤ) :=
        Finset.sum_le_sum (fun i _ => habs (s i))
    _ = (n : ℤ) := by simp

/-- **W-2 (energy dominates winding)**: the total
variation is at least the absolute displacement —
a path cannot end higher than it climbed. -/
theorem winding_abs_le_stepEnergy (s : Fin n → Fin 3) :
    |winding s| ≤ stepEnergy s :=
  Finset.abs_sum_le_sum_abs _ _

/-- **W-3 (sharpness / sector ground)**: every integer
`w` with `|w| ≤ n` is the winding of some configuration,
achieved at step energy exactly `|w|` — the monotone
ramp: `|w|` steps of `sign w`, the rest flat. No sector
inside the bound is empty, and no configuration in a
sector pays less than `|w|` (by W-2). -/
theorem exists_winding (w : ℤ) (hw : |w| ≤ (n : ℤ)) :
    ∃ s : Fin n → Fin 3, winding s = w ∧ stepEnergy s = |w| := by
  have hv1 : stepValue (1 : Fin 3) = 0 := rfl
  set m := w.natAbs with hm
  have hm_cast : (m : ℤ) = |w| := Int.natCast_natAbs w
  have hm_le : m ≤ n := by
    have h : (m : ℤ) ≤ (n : ℤ) := hm_cast ▸ hw
    exact_mod_cast h
  -- The ramp-sum computation, for any chosen step `a` of value `v`.
  have key : ∀ (a : Fin 3) (v : ℤ), stepValue a = v →
      winding (fun i : Fin n => if (i : ℕ) < m then a else 1) = (m : ℤ) * v
      ∧ stepEnergy (fun i : Fin n => if (i : ℕ) < m then a else 1)
        = (m : ℤ) * |v| := by
    intro a v hav
    have hstep : ∀ i : Fin n,
        stepValue ((fun i : Fin n => if (i : ℕ) < m then a else 1) i)
          = if (i : ℕ) < m then v else 0 := by
      intro i
      by_cases hi : (i : ℕ) < m
      · simp only [hi, if_true]
        exact hav
      · simp only [hi, if_false]
        exact hv1
    have habsstep : ∀ i : Fin n,
        |stepValue ((fun i : Fin n => if (i : ℕ) < m then a else 1) i)|
          = if (i : ℕ) < m then |v| else 0 := by
      intro i
      rw [hstep i]
      by_cases hi : (i : ℕ) < m
      · simp only [hi, if_true]
      · simp only [hi, if_false, abs_zero]
    have hrange : ∀ (c : ℤ),
        (∑ j ∈ Finset.range n, (if j < m then c else 0)) = (m : ℤ) * c := by
      intro c
      rw [← Finset.sum_range_add_sum_Ico (fun j => if j < m then c else 0)
        hm_le]
      have h1 : (∑ j ∈ Finset.range m, (if j < m then c else 0))
          = (m : ℤ) * c := by
        rw [Finset.sum_congr rfl
          (fun j (hj : j ∈ Finset.range m) => if_pos (Finset.mem_range.mp hj))]
        simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      have h2 : (∑ j ∈ Finset.Ico m n, (if j < m then c else 0)) = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        rw [Finset.mem_Ico] at hj
        exact if_neg (not_lt.mpr hj.1)
      rw [h1, h2, add_zero]
    constructor
    · show (∑ i, stepValue ((fun i : Fin n => if (i : ℕ) < m then a else 1) i))
          = (m : ℤ) * v
      rw [Finset.sum_congr rfl (fun i _ => hstep i)]
      rw [Fin.sum_univ_eq_sum_range (fun j => if j < m then v else 0) n]
      exact hrange v
    · show (∑ i, |stepValue ((fun i : Fin n => if (i : ℕ) < m then a else 1) i)|)
          = (m : ℤ) * |v|
      rw [Finset.sum_congr rfl (fun i _ => habsstep i)]
      rw [Fin.sum_univ_eq_sum_range (fun j => if j < m then |v| else 0) n]
      exact hrange |v|
  by_cases hw0 : 0 ≤ w
  · have hv2 : stepValue (2 : Fin 3) = 1 := rfl
    obtain ⟨h1, h2⟩ := key 2 1 hv2
    refine ⟨fun i => if (i : ℕ) < m then (2 : Fin 3) else 1, ?_, ?_⟩
    · rw [h1, mul_one, hm_cast, abs_of_nonneg hw0]
    · rw [h2, abs_one, mul_one, hm_cast]
  · have hv0 : stepValue (0 : Fin 3) = -1 := rfl
    obtain ⟨h1, h2⟩ := key 0 (-1) hv0
    refine ⟨fun i => if (i : ℕ) < m then (0 : Fin 3) else 1, ?_, ?_⟩
    · rw [h1]
      have hm2 : (m : ℤ) = -w := by
        rw [hm_cast, abs_of_neg (lt_of_not_ge hw0)]
      rw [hm2]
      ring
    · rw [h2, abs_neg, abs_one, mul_one, hm_cast]

/-- **W-4, winding half (reflection)**: the linkwise
flip negates the winding — the reflected path ends as
far below its start as the original ended above. -/
theorem winding_flip (s : Fin n → Fin 3) :
    winding (fun i => stepFlip (s i)) = -winding s := by
  have hflip : ∀ a : Fin 3, stepValue (stepFlip a) = -stepValue a := by
    intro a
    have h1 : a.val ≤ 2 := by have h := a.isLt; omega
    show ((2 - a.val : ℕ) : ℤ) - 1 = -((a.val : ℤ) - 1)
    rw [Nat.cast_sub h1]
    ring
  show (∑ i, stepValue (stepFlip (s i))) = -∑ i, stepValue (s i)
  rw [Finset.sum_congr rfl (fun i _ => hflip (s i))]
  rw [Finset.sum_neg_distrib]

/-- **W-4, energy half (reflection)**: the linkwise
flip preserves the step energy — reflection costs no
variation. -/
theorem stepEnergy_flip (s : Fin n → Fin 3) :
    stepEnergy (fun i => stepFlip (s i)) = stepEnergy s := by
  have hflip : ∀ a : Fin 3, stepValue (stepFlip a) = -stepValue a := by
    intro a
    have h1 : a.val ≤ 2 := by have h := a.isLt; omega
    show ((2 - a.val : ℕ) : ℤ) - 1 = -((a.val : ℤ) - 1)
    rw [Nat.cast_sub h1]
    ring
  show (∑ i, |stepValue (stepFlip (s i))|)
      = ∑ i, |stepValue (s i)|
  exact Finset.sum_congr rfl (fun i _ => by rw [hflip (s i), abs_neg])

/-! ## §3 — Brick 2: the Gibbs layer (W-5..W-8) -/

/-- **Step energy as a real energy**: the Gibbs-side
reading of `stepEnergy`, cast to `ℝ` for
`ModularVariance`'s finite-Gibbs machinery. -/
noncomputable def stepEnergyR (s : Fin n → Fin 3) : ℝ :=
  (stepEnergy s : ℝ)

/-- **The winding sector at `w`**: the fibre of the
winding map over `w` — the configurations whose endpoint
displacement is exactly `w`. -/
def sector (w : ℤ) : Finset (Fin n → Fin 3) :=
  (Finset.univ : Finset (Fin n → Fin 3)).filter (fun s => winding s = w)

/-- **Sector partition sum**: the Boltzmann sum over one
winding sector at slope `β`. -/
noncomputable def sectorPartSum (w : ℤ) (β : ℝ) : ℝ :=
  ∑ s ∈ sector (n := n) w, Real.exp (-(β * stepEnergyR s))

/-- **W-5 (sector decomposition)**: the total partition
sum splits as the sum over the winding sectors
`w ∈ [-n, n]` of the sector partition sums — the fibre
decomposition of the configuration set under the winding
map (every configuration's winding lies in the range,
by W-1). -/
theorem partSum_sector_decomp (β : ℝ) :
    ModularVariance.partSum (stepEnergyR (n := n)) β
      = ∑ w ∈ Finset.Icc (-(n : ℤ)) (n : ℤ), sectorPartSum (n := n) w β := by
  have hmaps : ∀ s ∈ (Finset.univ : Finset (Fin n → Fin 3)),
      winding s ∈ Finset.Icc (-(n : ℤ)) (n : ℤ) := by
    intro s _
    rw [Finset.mem_Icc]
    have h := winding_abs_le s
    rw [abs_le] at h
    exact h
  calc ModularVariance.partSum (stepEnergyR (n := n)) β
      = ∑ s : Fin n → Fin 3, Real.exp (-(β * stepEnergyR s)) := rfl
    _ = ∑ w ∈ Finset.Icc (-(n : ℤ)) (n : ℤ),
          ∑ s ∈ Finset.univ.filter (fun s => winding s = w),
            Real.exp (-(β * stepEnergyR s)) :=
        (Finset.sum_fiberwise_of_maps_to hmaps _).symm
    _ = ∑ w ∈ Finset.Icc (-(n : ℤ)) (n : ℤ), sectorPartSum (n := n) w β :=
        Finset.sum_congr rfl (fun w _ => rfl)

/-- **W-6 (sector reflection symmetry)**: the sector
partition sums are equal at `±w`, for every `β` — the
linkwise flip is a bijection of the configuration set
that negates the winding (W-4) and preserves the energy,
so the two sectors carry identical Boltzmann sums. -/
theorem sectorPartSum_neg (w : ℤ) (β : ℝ) :
    sectorPartSum (n := n) (-w) β = sectorPartSum (n := n) w β := by
  have hinv : Function.Involutive stepFlip := by
    intro a
    apply Fin.ext
    show 2 - (2 - a.val) = a.val
    have h := a.isLt
    omega
  obtain ⟨e, he⟩ : ∃ e : (Fin n → Fin 3) ≃ (Fin n → Fin 3),
      e = Equiv.piCongrRight
        (fun _ => ⟨stepFlip, stepFlip, hinv, hinv⟩) := ⟨_, rfl⟩
  have hcomp : ∀ (s : Fin n → Fin 3) (i : Fin n),
      e s i = stepFlip (s i) := by
    intro s i
    rw [he]
    exact Equiv.piCongrRight_apply _ s i
  have hwind : ∀ s : Fin n → Fin 3, winding (e s) = -winding s := by
    intro s
    have h : e s = (fun i => stepFlip (s i)) := funext (hcomp s)
    rw [h]
    exact winding_flip s
  have hener : ∀ s : Fin n → Fin 3,
      stepEnergyR (e s) = stepEnergyR s := by
    intro s
    have h : e s = (fun i => stepFlip (s i)) := funext (hcomp s)
    rw [h]
    show ((stepEnergy (fun i => stepFlip (s i)) : ℤ) : ℝ)
        = (stepEnergy s : ℝ)
    rw [stepEnergy_flip s]
  have hterm : ∀ s : Fin n → Fin 3,
      (if winding (e s) = -w
        then Real.exp (-(β * stepEnergyR (e s))) else 0)
      = (if winding s = w
          then Real.exp (-(β * stepEnergyR s)) else 0) := by
    intro s
    rw [hwind s, hener s]
    by_cases hs : winding s = w
    · rw [if_pos (by rw [hs]), if_pos hs]
    · rw [if_neg (fun h => hs (neg_inj.mp h)), if_neg hs]
  have h1 : sectorPartSum (n := n) (-w) β
      = ∑ s : Fin n → Fin 3, (if winding s = -w
          then Real.exp (-(β * stepEnergyR s)) else 0) := by
    show (∑ s ∈ (Finset.univ : Finset (Fin n → Fin 3)).filter (fun s => winding s = -w),
        Real.exp (-(β * stepEnergyR s))) = _
    rw [Finset.sum_filter]
  have h2 : sectorPartSum (n := n) w β
      = ∑ s : Fin n → Fin 3, (if winding s = w
          then Real.exp (-(β * stepEnergyR s)) else 0) := by
    show (∑ s ∈ (Finset.univ : Finset (Fin n → Fin 3)).filter (fun s => winding s = w),
        Real.exp (-(β * stepEnergyR s))) = _
    rw [Finset.sum_filter]
  rw [h1, h2]
  rw [← Equiv.sum_comp e
    (fun s => if winding s = -w
      then Real.exp (-(β * stepEnergyR s)) else 0)]
  exact Finset.sum_congr rfl (fun s _ => hterm s)

/-- **W-7 (hot sector card)**: at `β = 0` the Gibbs
probability of the winding-`w` event is the sector's
share of all configurations, `card(sector) / card(all)`
— hot uniformity (compare StringSeatPin S-3) restated
per sector. -/
theorem gibbsProb_sector_zero (w : ℤ) :
    ∑ s ∈ sector (n := n) w, ModularVariance.gibbsProb stepEnergyR 0 s
      = ((sector (n := n) w).card : ℝ)
        / (Fintype.card (Fin n → Fin 3) : ℝ) := by
  have hZ : ModularVariance.partSum (stepEnergyR (n := n)) 0
      = (Fintype.card (Fin n → Fin 3) : ℝ) := by
    show (∑ s : Fin n → Fin 3,
        Real.exp (-((0 : ℝ) * stepEnergyR s))) = _
    simp
  have hterm : ∀ s : Fin n → Fin 3,
      ModularVariance.gibbsProb stepEnergyR 0 s
        = ((Fintype.card (Fin n → Fin 3) : ℝ))⁻¹ := by
    intro s
    show Real.exp (-((0 : ℝ) * stepEnergyR s))
        / ModularVariance.partSum (stepEnergyR (n := n)) 0 = _
    rw [hZ]
    simp
  rw [Finset.sum_congr rfl (fun s _ => hterm s)]
  rw [Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]

/-- **W-8 (cold unwinds)**: for `β ≥ 0`, the total Gibbs
weight on the nonzero-winding configurations is at most
`(card(all) − 1) · e^{−β}` — every nonzero-winding
configuration has step energy at least `1` (by W-2 and
`|winding| ≥ 1`), so its Boltzmann factor is at most
`e^{−β}`, and the flat configuration witnesses
`partSum ≥ 1`. The GAPFLOOR-1 concentration shape read
across sectors: cold suppresses thermal winding. -/
theorem cold_unwinds (hβ : 0 ≤ β) :
    ∑ s ∈ (Finset.univ : Finset (Fin n → Fin 3)).filter (fun s => winding s ≠ 0),
        ModularVariance.gibbsProb stepEnergyR β s
      ≤ ((Fintype.card (Fin n → Fin 3) : ℝ) - 1)
        * Real.exp (-β) := by
  have hv1 : stepValue (1 : Fin 3) = 0 := rfl
  have hflatE : stepEnergy (fun _ : Fin n => (1 : Fin 3)) = 0 := by
    unfold stepEnergy
    simp [hv1]
  have hflatW : winding (fun _ : Fin n => (1 : Fin 3)) = 0 := by
    unfold winding
    simp [hv1]
  have hflatR : stepEnergyR (fun _ : Fin n => (1 : Fin 3)) = 0 := by
    show ((stepEnergy (fun _ : Fin n => (1 : Fin 3)) : ℤ) : ℝ) = 0
    rw [hflatE]
    exact Int.cast_zero
  have hZ1 : (1 : ℝ) ≤ ModularVariance.partSum (stepEnergyR (n := n)) β := by
    have h := Finset.single_le_sum
      (f := fun s : Fin n → Fin 3 =>
        Real.exp (-(β * stepEnergyR s)))
      (fun s _ => (Real.exp_pos _).le)
      (Finset.mem_univ (fun _ : Fin n => (1 : Fin 3)))
    rw [hflatR, mul_zero, neg_zero, Real.exp_zero] at h
    exact h
  have hterm : ∀ s ∈ (Finset.univ : Finset (Fin n → Fin 3)).filter (fun s => winding s ≠ 0),
      ModularVariance.gibbsProb stepEnergyR β s
        ≤ Real.exp (-β) := by
    intro s hs
    rw [Finset.mem_filter] at hs
    have hE1 : (1 : ℝ) ≤ stepEnergyR s := by
      have h1 : (1 : ℤ) ≤ stepEnergy s :=
        le_trans (Int.one_le_abs hs.2) (winding_abs_le_stepEnergy s)
      show (1 : ℝ) ≤ ((stepEnergy s : ℤ) : ℝ)
      exact_mod_cast h1
    show Real.exp (-(β * stepEnergyR s))
        / ModularVariance.partSum (stepEnergyR (n := n)) β ≤ Real.exp (-β)
    rw [div_le_iff₀ (ModularVariance.partSum_pos (stepEnergyR (n := n)) β)]
    calc Real.exp (-(β * stepEnergyR s)) ≤ Real.exp (-β) := by
          apply Real.exp_le_exp.mpr
          rw [neg_le_neg_iff]
          calc β = β * 1 := (mul_one β).symm
            _ ≤ β * stepEnergyR s :=
                mul_le_mul_of_nonneg_left hE1 hβ
      _ ≤ Real.exp (-β) * ModularVariance.partSum (stepEnergyR (n := n)) β :=
          le_mul_of_one_le_right (Real.exp_pos _).le hZ1
  have hsub : (Finset.univ : Finset (Fin n → Fin 3)).filter (fun s => winding s ≠ 0)
      ⊆ Finset.univ \ {(fun _ : Fin n => (1 : Fin 3))} := by
    intro s hs
    rw [Finset.mem_filter] at hs
    rw [Finset.mem_sdiff]
    refine ⟨Finset.mem_univ s, ?_⟩
    rw [Finset.mem_singleton]
    intro hseq
    apply hs.2
    rw [hseq, hflatW]
  have hcard : ((Finset.univ : Finset (Fin n → Fin 3)).filter (fun s => winding s ≠ 0)).card
      ≤ Fintype.card (Fin n → Fin 3) - 1 := by
    calc ((Finset.univ : Finset (Fin n → Fin 3)).filter (fun s => winding s ≠ 0)).card
        ≤ (Finset.univ \ {(fun _ : Fin n => (1 : Fin 3))}).card :=
          Finset.card_le_card hsub
      _ = Fintype.card (Fin n → Fin 3) - 1 := by
          rw [Finset.card_sdiff, Finset.inter_univ,
            Finset.card_singleton, Finset.card_univ]
  calc ∑ s ∈ (Finset.univ : Finset (Fin n → Fin 3)).filter (fun s => winding s ≠ 0),
          ModularVariance.gibbsProb stepEnergyR β s
      ≤ ∑ s ∈ (Finset.univ : Finset (Fin n → Fin 3)).filter (fun s => winding s ≠ 0),
          Real.exp (-β) := Finset.sum_le_sum hterm
    _ = (((Finset.univ : Finset (Fin n → Fin 3)).filter (fun s => winding s ≠ 0)).card : ℝ)
          * Real.exp (-β) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((Fintype.card (Fin n → Fin 3) : ℝ) - 1)
          * Real.exp (-β) := by
        have hcast : (((Finset.univ : Finset (Fin n → Fin 3)).filter
              (fun s => winding s ≠ 0)).card : ℝ)
            ≤ (Fintype.card (Fin n → Fin 3) : ℝ) - 1 := by
          have h1 : ((Fintype.card (Fin n → Fin 3) - 1 : ℕ) : ℝ)
              = (Fintype.card (Fin n → Fin 3) : ℝ) - 1 := by
            rw [Nat.cast_sub Fintype.card_pos, Nat.cast_one]
          rw [← h1]
          exact_mod_cast hcard
        exact mul_le_mul_of_nonneg_right hcast (Real.exp_pos _).le

end ThetLogos.StringWindingPin
