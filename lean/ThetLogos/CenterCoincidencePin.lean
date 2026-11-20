import Mathlib.Tactic
import ThetLogos.ModularVariance

/-!
# CenterCoincidencePin — ICDT-2, the center brick

Commissioned by Zero, 2026-11-19 20:28 EST ("build it") over
his seeing, verbatim: *"center of mass is center of thermal
Equilibrium"* (20:26 EST). Scope:
`inertia-coupled-density-tension-scope-2026-11-19.md` §4.
**Grade: T5. NO CLAIM. Pre-registered DIAL-INELIGIBLE — Dial
2 = 0 under every outcome. Dials 0/4.**

## The two centers, with SEPARATE data

The brick's discipline is the scope's: the mass distribution
and the energy landscape are INDEPENDENT inputs. `massCenter`
sees only a mass distribution and positions; `thermalCenter`
sees only an energy landscape, an inverse temperature, and
positions. Neither definition mentions the other's data.
(`thermalCenter` is the Gibbs expectation of the position
observable — `ModularVariance.gibbsExpect` — read as a center; the
identification is stated as its own line below, not hidden.
The ℚ precedent at the rope seat is `CenterBridgePin.wCenter`,
cited, not rebuilt: this brick's centers are the ℝ/Gibbs-seat
forms the coincidence statement needs.)

## K-ICDT-CENTER — the verdict, stated before the theorems

The general claim — for separate data, the two centers
coincide — is **FALSE**, and this brick exhibits the reason:
the two-site countermodel below, where uniform mass on two
sites has center `1/2` and the thermal center sits at
`e⁻¹/(1 + e⁻¹) ≠ 1/2`. **K-ICDT-CENTER FIRES on the general
separate-data coincidence: it is killed, at full rank, by
exhibition.** What survives is exactly the proportional case:
when the mass distribution IS the Gibbs weight up to a
positive scalar, the centers coincide — and that theorem is
labeled here as what it is: the coincidence of a center with
itself under proportional weights. Its proof's content is
real but narrow: the normalization `∑ ModularVariance.gibbsProb = 1` cancels
the scalar. Nothing in this brick engineers around the kill:
no hypothesis was tuned after seeing the countermodel — the
proportional form is the scope's own pre-registered form
(ii), and the countermodel is the scope's pre-registered
form (iii).

## The cold form, in bound form only

(iv) As `β` grows, the thermal center is dragged to the
ground site's position with an explicit off-ground bound:
each off-ground Gibbs weight is at most `exp (−β·gap)`
(`gibbsProb_le_exp_neg_gap` — the diagonal-seat bound;
the landed concentration bounds at the string seat,
`StringSeatPin.cold_concentration`, and the graph seat,
`ThermalLiftCold`, are different weight systems and are
cited as route, not restated). The mass center does not
move with `β` — it is not a function of `β` at all. Cold
coincidence is therefore exactly the mass-on-ground case:
a mass supported on the ground site has its center at the
ground position at every temperature
(`massCenter_eq_of_support_ground`), and the bound drags
the thermal center to that same position. Stated as the
bound plus that corollary — the scope's licensed form.

## Fences

K-ICDT-CENTER (above), K-ICDT-DUP, K-ICDT-COSTUME. No center
in this brick is a gravity object, a response law, or Dial
evidence.
-/

namespace ThetLogos

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- **The mass center** of a mass distribution `m` at
positions `x`: the mass-weighted mean position. Sees mass
data only — no energy, no temperature. -/
noncomputable def massCenter (m x : ι → ℝ) : ℝ :=
  (∑ i, m i * x i) / (∑ i, m i)

/-- **The thermal center** of an energy landscape `E` at
inverse temperature `β`, at positions `x`: the Gibbs-weighted
mean position. Sees thermal data only — no mass. -/
noncomputable def thermalCenter (E : ι → ℝ) (β : ℝ)
    (x : ι → ℝ) : ℝ :=
  ∑ i, ModularVariance.gibbsProb E β i * x i

/-- The thermal center IS the Gibbs expectation of the
position observable — an identification, stated openly
(`rfl`), not a theorem with content. -/
theorem thermalCenter_eq_gibbsExpect (E : ι → ℝ) (β : ℝ)
    (x : ι → ℝ) : thermalCenter E β x = ModularVariance.gibbsExpect E β x :=
  rfl

/-- **The coincidence, in its surviving (proportional) form.**
If the mass distribution is the Gibbs weight up to a
positive scalar, the two centers coincide for every position
observable. Labeled as what it is (see the header): the
coincidence of a center with itself under proportional
weights — the proof's content is the cancellation of the
scalar against the Gibbs normalization. The general
separate-data coincidence is FALSE; the countermodel below
is its exhibited kill (K-ICDT-CENTER). -/
theorem massCenter_eq_thermalCenter_of_proportional
    (m E x : ι → ℝ) (β : ℝ)
    (hc : ∃ c > 0, ∀ i, m i = c * ModularVariance.gibbsProb E β i) :
    massCenter m x = thermalCenter E β x := by
  obtain ⟨c, hc0, hm⟩ := hc
  have hsum : (∑ i, m i) = c := by
    have h1 : (∑ i, m i) = ∑ i, c * ModularVariance.gibbsProb E β i :=
      Finset.sum_congr rfl fun i _ => hm i
    rw [h1, ← Finset.mul_sum, ModularVariance.sum_gibbsProb, mul_one]
  have hnum : (∑ i, m i * x i) = c * thermalCenter E β x := by
    show (∑ i, m i * x i)
      = c * ∑ i, ModularVariance.gibbsProb E β i * x i
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [hm i]
    ring
  rw [massCenter, hnum, hsum, mul_div_cancel_left₀]
  exact ne_of_gt hc0

/-- **The countermodel — the general coincidence is false.**
Two sites, positions `0` and `1`. Uniform mass: center
exactly `1/2`. Landscape `![0, 1]` at `β = 1`: thermal center
`e⁻¹/(1 + e⁻¹) ≈ 0.269`. Mass data and energy data chosen
independently; the centers differ. This is the exhibited
reason K-ICDT-CENTER fires on the general separate-data
coincidence (see the header). -/
theorem centers_differ_countermodel :
    massCenter ![1, 1] ![0, 1]
      ≠ thermalCenter ![0, 1] 1 ![0, 1] := by
  have hmc : massCenter ![1, 1] ![0, 1] = 1 / 2 := by
    rw [massCenter, Fin.sum_univ_two, Fin.sum_univ_two]
    norm_num
  have htc : thermalCenter ![0, 1] 1 ![0, 1]
      = Real.exp (-1) / (1 + Real.exp (-1)) := by
    rw [thermalCenter, Fin.sum_univ_two]
    simp only [ModularVariance.gibbsProb, ModularVariance.partSum, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    norm_num
  rw [hmc, htc]
  intro h
  have he : Real.exp (-1) < 1 := by
    rw [Real.exp_neg]
    apply inv_lt_one_of_one_lt₀
    rw [Real.one_lt_exp_iff]
    norm_num
  have hpos : (0 : ℝ) < 1 + Real.exp (-1) :=
    add_pos (by norm_num) (Real.exp_pos _)
  rw [eq_div_iff (ne_of_gt hpos)] at h
  linarith

/-- **The off-ground Gibbs bound at the diagonal seat.** For
a ground site `g` of the landscape, every site's Gibbs
weight is at most the exponential of its scaled gap:
`ModularVariance.gibbsProb E β i ≤ exp (−β (E i − E g))`. One term of the
partition sum bounds the sum; no sign condition on `β` is
needed. The diagonal-seat form of the concentration family
owned in bound form at the string and graph seats (cited as
route in the header). -/
theorem gibbsProb_le_exp_neg_gap (E : ι → ℝ) (β : ℝ) (g : ι)
    (hg : ∀ i, E g ≤ E i) (i : ι) :
    ModularVariance.gibbsProb E β i ≤ Real.exp (-(β * (E i - E g))) := by
  have hZ : Real.exp (-(β * E g)) ≤ ModularVariance.partSum E β :=
    Finset.single_le_sum
      (f := fun i => Real.exp (-(β * E i)))
      (fun j _ => (Real.exp_pos _).le) (Finset.mem_univ g)
  rw [show ModularVariance.gibbsProb E β i
      = Real.exp (-(β * E i)) / ModularVariance.partSum E β from rfl,
    div_le_iff₀ (ModularVariance.partSum_pos E β)]
  have h1 : Real.exp (-(β * (E i - E g)))
      * Real.exp (-(β * E g)) = Real.exp (-(β * E i)) := by
    rw [← Real.exp_add]
    ring_nf
  calc Real.exp (-(β * E i))
      = Real.exp (-(β * (E i - E g))) * Real.exp (-(β * E g)) :=
        h1.symm
    _ ≤ Real.exp (-(β * (E i - E g))) * ModularVariance.partSum E β :=
        mul_le_mul_of_nonneg_left hZ (Real.exp_pos _).le

/-- **The cold drag, in bound form.** With ground site `g`,
off-ground gap at least `Δ`, positions within `M` of the
ground position, and `0 ≤ β`: the thermal center sits within
`M · (card − 1) · exp (−βΔ)` of the ground site's position.
The `card − 1` is the off-ground count — the ground term of
the center sum vanishes identically. As `β → ∞` the bound
contracts to `0`: cold drags the thermal center home. -/
theorem thermalCenter_sub_abs_le (E x : ι → ℝ) (β : ℝ)
    (hβ : 0 ≤ β) (g : ι) (hg : ∀ i, E g ≤ E i)
    (Δ : ℝ) (hΔ : ∀ i, i ≠ g → Δ ≤ E i - E g)
    (M : ℝ) (hM : ∀ i, |x i - x g| ≤ M) :
    |thermalCenter E β x - x g|
      ≤ M * (((Fintype.card ι : ℝ) - 1) * Real.exp (-(β * Δ))) := by
  have hM0 : 0 ≤ M := le_trans (by simp) (hM g)
  have hdiff : (∑ i, ModularVariance.gibbsProb E β i * (x i - x g))
      = thermalCenter E β x - x g := by
    have h1 : (∑ i, ModularVariance.gibbsProb E β i * (x i - x g))
        = (∑ i, ModularVariance.gibbsProb E β i * x i)
          - ∑ i, ModularVariance.gibbsProb E β i * x g := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [h1, ← Finset.sum_mul, ModularVariance.sum_gibbsProb, one_mul]
    rfl
  have hterm : ∀ i ∈ Finset.univ.erase g,
      |ModularVariance.gibbsProb E β i * (x i - x g)|
        ≤ M * Real.exp (-(β * Δ)) := by
    intro i hi
    have hig : i ≠ g := (Finset.mem_erase.mp hi).1
    rw [abs_mul, abs_of_pos (ModularVariance.gibbsProb_pos E β i)]
    have hgap : ModularVariance.gibbsProb E β i ≤ Real.exp (-(β * Δ)) := by
      refine le_trans (gibbsProb_le_exp_neg_gap E β g hg i) ?_
      apply Real.exp_le_exp.mpr
      have h1 : β * Δ ≤ β * (E i - E g) :=
        mul_le_mul_of_nonneg_left (hΔ i hig) hβ
      linarith
    calc ModularVariance.gibbsProb E β i * |x i - x g|
        ≤ Real.exp (-(β * Δ)) * M :=
          mul_le_mul hgap (hM i) (abs_nonneg _)
            (Real.exp_pos _).le
      _ = M * Real.exp (-(β * Δ)) := by ring
  calc |thermalCenter E β x - x g|
      = |∑ i, ModularVariance.gibbsProb E β i * (x i - x g)| := by rw [hdiff]
    _ ≤ ∑ i, |ModularVariance.gibbsProb E β i * (x i - x g)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i ∈ Finset.univ.erase g,
          |ModularVariance.gibbsProb E β i * (x i - x g)| := by
        rw [← Finset.add_sum_erase Finset.univ _
          (Finset.mem_univ g)]
        simp
    _ ≤ (Finset.univ.erase g).card • (M * Real.exp (-(β * Δ))) :=
        Finset.sum_le_card_nsmul _ _ _ hterm
    _ = M * (((Fintype.card ι : ℝ) - 1) * Real.exp (-(β * Δ))) := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ g),
          Finset.card_univ, nsmul_eq_mul,
          Nat.cast_sub Fintype.card_pos]
        push_cast
        ring

/-- **The mass-on-ground corollary.** A mass supported on
the ground site alone has its center exactly at the ground
position — at every temperature, because the mass center is
not a function of temperature at all. Together with the
cold drag bound, this is the cold form of the coincidence:
cold coincidence holds exactly when the mass already sits
on the ground seat. -/
theorem massCenter_eq_of_support_ground (m x : ι → ℝ) (g : ι)
    (hm : ∀ i, i ≠ g → m i = 0) (hg : 0 < m g) :
    massCenter m x = x g := by
  have hsum : (∑ i, m i) = m g :=
    Finset.sum_eq_single g (fun i _ hi => hm i hi)
      (fun h => absurd (Finset.mem_univ g) h)
  have hnum : (∑ i, m i * x i) = m g * x g :=
    Finset.sum_eq_single g
      (fun i _ hi => by rw [hm i hi, zero_mul])
      (fun h => absurd (Finset.mem_univ g) h)
  rw [massCenter, hnum, hsum, mul_div_cancel_left₀]
  exact ne_of_gt hg

end ThetLogos
