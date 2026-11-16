/-
# StringResponsePin — the string seat's response function

**Continuation of StringSeatPin (the finite bendable chain),
banked at lane grade on branch `stringseat`. NO CLAIM.
Dial-ineligible.**

THE CONTENT: the response function of the string seat,
derived from StringSeatPin's OWN definitions — the
partition sum of `bendEnergy` under the corpus's
finite-Gibbs machinery (`ModularVariance.partSum` /
`gibbsProb`) factorizes over the chain's links, and the
straight configuration's Gibbs probability (the seat's
ground-state weight; its complement is the seat's
ACTIVITY) is the reciprocal power of a single-site sum.
The hot value is exact, and the cold activity bound is
the GAPFLOOR shape at this seat: at most
`n · k · e^{−β}` — exponential freeze-out at the least
bend cost `1`, the gap of `StringSeatPin.one_le_bendEnergy`.

THE SINGLE-SITE SUM, STATED PLAINLY: the tree's
`bendCost` is `0/1` — a link is straight or bent, and
`bendEnergy` COUNTS bent links; it does not weight a
link by a bend level. The single-site sum is therefore
taken over `bendCost` as defined, and it evaluates
EXACTLY: `z(β) = 1 + k · e^{−β}` — not the geometric
series `Σⱼ e^{−βj}` that a level-weighted energy would
give. Every statement below is about the tree's energy.

FIDELITY FENCES (inherited from StringSeatPin, in plain
words):
- The pin's "knot" is BEND CONTENT — the countable
  shadow — NOT topological knot type. K-STRING-KNOT
  armed.
- The pin is a finite toy. It does NOT model a
  physical string's mechanics. K-STRING-PHYS armed.
  No gravity. No continuum filament.
- NOT BUILT in this brick: the crossover/threshold
  (existence of `β*` by an intermediate-value argument
  — brick 2), and the signed-bend / direction
  observable (bends here carry no sign, so no directed
  current is defined at this seat).

STATUS: STATUS-STRINGRESPONSE.md.
-/

import Mathlib.Tactic
import ThetLogos.StringSeatPin

namespace ThetLogos.StringResponsePin

open ThetLogos.StringSeatPin

variable {n k : ℕ}

/-! ## §1 — the single-site sum and its exact value -/

/-- **The single-site sum**: one link's share of the
partition sum — the sum over one link's bend states of
its Boltzmann factor at the tree's `bendCost`. (The
state count `k` is an explicit argument: nothing in
`β` alone determines it.) -/
noncomputable def siteSum (k : ℕ) (β : ℝ) : ℝ :=
  ∑ s : Fin (k + 1), Real.exp (-(β * bendCost s))

/-- **Exact value of the single-site sum**:
`z(β) = 1 + k · e^{−β}` — the straight state contributes
`e⁰ = 1`; each of the `k` bent states contributes
`e^{−β}` at bend cost `1`. Holds at every `k`,
including `k = 0` (no bent states, `z = 1`). -/
theorem siteSum_eq (β : ℝ) :
    siteSum k β = 1 + (k : ℝ) * Real.exp (-β) := by
  unfold siteSum
  rw [← Finset.add_sum_erase Finset.univ
    (fun s : Fin (k + 1) => Real.exp (-(β * bendCost s)))
    (Finset.mem_univ (0 : Fin (k + 1)))]
  have h0 : Real.exp (-(β * bendCost (0 : Fin (k + 1))))
      = 1 := by
    simp [bendCost]
  have hrest : ∑ s ∈ Finset.univ.erase (0 : Fin (k + 1)),
        Real.exp (-(β * bendCost s))
      = (k : ℝ) * Real.exp (-β) := by
    calc ∑ s ∈ Finset.univ.erase (0 : Fin (k + 1)),
          Real.exp (-(β * bendCost s))
        = ∑ _s ∈ Finset.univ.erase (0 : Fin (k + 1)),
            Real.exp (-β) :=
          Finset.sum_congr rfl (fun s hs => by
            have hs0 : s ≠ 0 := (Finset.mem_erase.mp hs).1
            simp [bendCost, hs0])
      _ = (k : ℝ) * Real.exp (-β) := by
          rw [Finset.sum_const, Finset.card_erase_of_mem
            (Finset.mem_univ (0 : Fin (k + 1))),
            Finset.card_univ, Fintype.card_fin,
            Nat.add_sub_cancel, nsmul_eq_mul]
  rw [h0, hrest]

/-- **Hot value of the single-site sum**: at `β = 0`,
`z = k + 1` — every one of the `k + 1` link states
weighs `1`. -/
theorem siteSum_zero : siteSum k 0 = (k : ℝ) + 1 := by
  rw [siteSum_eq, neg_zero, Real.exp_zero, mul_one, add_comm]

/-! ## §2 — factorization of the partition sum -/

/-- **Factorization**: the string seat's partition sum
is the `n`-th power of the single-site sum,
`Z(β) = z(β)ⁿ` — the links are independent at the
tree's energy, which is a sum over links. Proved by
induction on the chain length, splitting a
configuration into its head link and its tail
(`Fin.consEquiv`). -/
theorem partSum_bendEnergy_eq (β : ℝ) :
    ModularVariance.partSum
        (bendEnergy : (Fin n → Fin (k + 1)) → ℝ) β
      = siteSum k β ^ n := by
  induction n with
  | zero =>
    have hE : ∀ c : Fin 0 → Fin (k + 1), bendEnergy c = 0 :=
      fun c => Finset.sum_eq_zero (fun i _ => i.elim0)
    unfold ModularVariance.partSum
    calc (∑ c : Fin 0 → Fin (k + 1),
          Real.exp (-(β * bendEnergy c)))
        = ∑ _c : Fin 0 → Fin (k + 1), (1 : ℝ) :=
          Finset.sum_congr rfl (fun c _ => by rw [hE c]; simp)
      _ = 1 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun,
            Fintype.card_fin]
          simp
      _ = siteSum k β ^ 0 := (pow_zero _).symm
  | succ n ih =>
    have hcons : ∀ (s : Fin (k + 1)) (t : Fin n → Fin (k + 1)),
        bendEnergy (Fin.cons s t)
          = bendCost s + bendEnergy t := by
      intro s t
      simp only [bendEnergy, Fin.sum_univ_succ, Fin.cons_zero,
        Fin.cons_succ]
    unfold ModularVariance.partSum
    calc (∑ c : Fin (n + 1) → Fin (k + 1),
          Real.exp (-(β * bendEnergy c)))
        = ∑ p : Fin (k + 1) × (Fin n → Fin (k + 1)),
            Real.exp (-(β * bendEnergy (Fin.cons p.1 p.2))) :=
          (Equiv.sum_comp (Fin.consEquiv (fun _ => Fin (k + 1)))
            (fun c : Fin (n + 1) → Fin (k + 1) =>
              Real.exp (-(β * bendEnergy c)))).symm
      _ = ∑ s : Fin (k + 1), ∑ t : Fin n → Fin (k + 1),
            Real.exp (-(β * bendEnergy (Fin.cons s t))) :=
          Fintype.sum_prod_type _
      _ = ∑ s : Fin (k + 1),
            Real.exp (-(β * bendCost s)) * siteSum k β ^ n := by
          apply Finset.sum_congr rfl
          intro s _
          calc (∑ t : Fin n → Fin (k + 1),
                Real.exp (-(β * bendEnergy (Fin.cons s t))))
              = ∑ t : Fin n → Fin (k + 1),
                  Real.exp (-(β * bendCost s))
                    * Real.exp (-(β * bendEnergy t)) := by
                apply Finset.sum_congr rfl
                intro t _
                rw [hcons s t, mul_add, neg_add, Real.exp_add]
            _ = Real.exp (-(β * bendCost s))
                  * ∑ t : Fin n → Fin (k + 1),
                    Real.exp (-(β * bendEnergy t)) :=
                (Finset.mul_sum _ _ _).symm
            _ = Real.exp (-(β * bendCost s)) * siteSum k β ^ n :=
                congrArg _ ih
      _ = siteSum k β ^ (n + 1) := by
          rw [pow_succ']
          exact (Finset.sum_mul _ _ _).symm

/-! ## §3 — the ground probability, hot value, cold bounds -/

/-- **Ground probability**: the straight configuration's
Gibbs probability is the reciprocal partition sum, hence
the reciprocal power of the single-site sum:
`p₀(β) = z(β)^{−n}`. Its complement `1 − p₀(β)` is the
seat's activity — the total weight off the ground
state. -/
theorem gibbsProb_straightConfig_siteSum (β : ℝ) :
    ModularVariance.gibbsProb bendEnergy β
        (straightConfig : Fin n → Fin (k + 1))
      = (siteSum k β ^ n)⁻¹ := by
  rw [gibbsProb_straightConfig_eq, partSum_bendEnergy_eq]

/-- **Hot value of the ground probability**: at
`β = 0`, `p₀ = ((k + 1)ⁿ)⁻¹` — the uniform share of
S-3, `(k + 1)ⁿ` being the number of configurations
(`StringSeatPin.card_config`). -/
theorem gibbsProb_straightConfig_zero :
    ModularVariance.gibbsProb bendEnergy 0
        (straightConfig : Fin n → Fin (k + 1))
      = (((k : ℝ) + 1) ^ n)⁻¹ := by
  rw [gibbsProb_straightConfig_siteSum, siteSum_zero]

/-- The single-site sum is at least `1` at every `β`:
the ground term alone, the rest nonnegative. -/
theorem one_le_siteSum (β : ℝ) :
    1 ≤ siteSum k β := by
  rw [siteSum_eq]
  have h : 0 ≤ (k : ℝ) * Real.exp (-β) :=
    mul_nonneg (Nat.cast_nonneg k) (Real.exp_pos _).le
  linarith

/-- The single-site sum is at most `1 + k` for `β ≥ 0`:
each bent state's factor `e^{−β}` is at most `1`. -/
theorem siteSum_le_one_add {β : ℝ} (hβ : 0 ≤ β) :
    siteSum k β ≤ 1 + (k : ℝ) := by
  rw [siteSum_eq]
  have h1 : Real.exp (-β) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    exact neg_nonpos.mpr hβ
  have h2 : (k : ℝ) * Real.exp (-β) ≤ (k : ℝ) * 1 :=
    mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg k)
  linarith

/-- **Cold activity bound**: the seat's activity — the
total Gibbs weight off the straight configuration — is
at most `n · k · e^{−β}`: exponential freeze-out at the
gap `1`, with the first excited level's degeneracy
`n · k` (one bent link: `n` seats for it, `k` bent
states) as the prefactor. The GAPFLOOR-1 shape at this
seat, in response-function form. (The inequality in
fact holds at every `β` — it is the one-variable bound
`1 − (1 + x)^{−n} ≤ n·x` at `x = k·e^{−β} ≥ 0`; the
cold regime `β ≥ 0` is its physical reading.) -/
theorem activity_le (β : ℝ) :
    1 - ModularVariance.gibbsProb bendEnergy β
          (straightConfig : Fin n → Fin (k + 1))
      ≤ (n : ℝ) * (k : ℝ) * Real.exp (-β) := by
  set z := siteSum k β with hz
  set x := (k : ℝ) * Real.exp (-β) with hx
  have hz_eq : z = 1 + x := siteSum_eq β
  have hx0 : 0 ≤ x := mul_nonneg (Nat.cast_nonneg k)
    (Real.exp_pos _).le
  have hz1 : 1 ≤ z := one_le_siteSum β
  have hzpos : 0 < z := lt_of_lt_of_le one_pos hz1
  rw [gibbsProb_straightConfig_siteSum, ← inv_pow]
  -- the one-variable inequality: for `0 ≤ t ≤ 1`,
  -- `1 − tⁿ ≤ n · (1 − t)` (geometric sum bound)
  have ht0 : 0 ≤ z⁻¹ := inv_nonneg.mpr hzpos.le
  have ht1 : z⁻¹ ≤ 1 := by
    rw [inv_eq_one_div]
    exact div_le_one_of_le₀ hz1 hzpos.le
  have hkey : (1 : ℝ) - z⁻¹ ^ n ≤ (n : ℝ) * (1 - z⁻¹) := by
    have hgeom : (∑ i ∈ Finset.range n, z⁻¹ ^ i) * (1 - z⁻¹)
        = 1 - z⁻¹ ^ n := by
      have h := geom_sum_mul z⁻¹ n
      linarith
    have hsum : (∑ i ∈ Finset.range n, z⁻¹ ^ i) ≤ (n : ℝ) := by
      calc (∑ i ∈ Finset.range n, z⁻¹ ^ i)
          ≤ ∑ _i ∈ Finset.range n, (1 : ℝ) :=
            Finset.sum_le_sum (fun i _ => pow_le_one₀ ht0 ht1)
        _ = (n : ℝ) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
              mul_one]
    calc (1 : ℝ) - z⁻¹ ^ n
        = (∑ i ∈ Finset.range n, z⁻¹ ^ i) * (1 - z⁻¹) :=
          hgeom.symm
      _ ≤ (n : ℝ) * (1 - z⁻¹) :=
          mul_le_mul_of_nonneg_right hsum (sub_nonneg.mpr ht1)
  -- and `1 − z⁻¹ = x / z ≤ x`, since `z = 1 + x ≥ 1`
  have hzne : z ≠ 0 := ne_of_gt hzpos
  have h1t : 1 - z⁻¹ = x / z := by
    rw [eq_div_iff hzne, sub_mul, one_mul, inv_mul_cancel₀ hzne,
      hz_eq, add_sub_cancel_left]
  have hxle : x / z ≤ x := by
    rw [div_le_iff₀ hzpos]
    calc x = x * 1 := (mul_one x).symm
      _ ≤ x * z := mul_le_mul_of_nonneg_left hz1 hx0
  calc (1 : ℝ) - z⁻¹ ^ n ≤ (n : ℝ) * (1 - z⁻¹) := hkey
    _ = (n : ℝ) * (x / z) := by rw [h1t]
    _ ≤ (n : ℝ) * x :=
        mul_le_mul_of_nonneg_left hxle (Nat.cast_nonneg n)
    _ = (n : ℝ) * (k : ℝ) * Real.exp (-β) := by ring

end ThetLogos.StringResponsePin
