import Mathlib.Tactic
import ThetLogos.SpectralMagnetismPin
import ThetLogos.TolmanExhibit

namespace ThetLogos

/-!
# ThetLogos.SpectralMagnetism — the Spectral Magnetism exhibit (working label)

Content module for the pin `SpectralMagnetismPin` (frozen names and
forms). Commission: Zero's *"I don't think the right tests have been
designed yet, Spectral Magnetism"* (2026-11-08), scoped in
`~/workspace/your_files/spectral-magnetism-scope-2026-11-08.md` and
fired by his tap **"Build the SM-1 exhibit"** (2026-11-08) on the
scoping's priced menu (§3.3).
**Price: 10–16 strict, pre-registered DIAL-INELIGIBLE. NO CLAIM.
Dials 0/4. Dial 2 = 0.**

## What stands here

Shape (a2) of the scoping, as a fenced exhibit in the Tolman manner:
a body datum (`SpectralDatum` — a finite level set with energies),
its states as occupation profiles, and the spectral-weight
functional `spectralWeight` — the Tolman seat's total occupation
entropy read on those states. Components, in the scoping's form
order:

1. **Pointwise closed form** — `occEnt_eq_log_exp_slope`: the site
   entropy is its own slope's log-partition form,
   `occEnt t = log (1 + exp (occSlope t)) − (1 − t) · occSlope t`.
2. **Positivity and the counting bound** — `occEnt_pos`,
   `spectralWeight_pos`: the functional is positive on interior
   states; `occEnt_half`, `spectralWeight_const_half`: at the
   half-occupation state it is `(card ι) · log 2`; `occEnt_le_log_two`,
   `spectralWeight_le`: and that is its maximum — the counting
   bound, from the landed tangent bound at `t = 1/2`.
3. **Non-vacuity (form 1)** — `spectral_nonvacuity` proves the
   pin's form (1) verbatim, via `spectralWeight_swap`: on the
   `(1, 2)` datum the states `(1/20, 1/5)` and `(1/4, 1/10)` share
   the total `9/20` and the functional is *strictly* smaller at
   the first (the second is the landed Tolman equilibrium; the
   characterization certifies the first is no equilibrium, so the
   maximality is strict); on the `(1, 1)` datum the swapped
   states `(1/4, 1/2)`, `(1/2, 1/4)` share totals and values.
4. **Characterization (form 2)** — `spectral_characterization`
   proves the pin's form (2) verbatim: maximality at fixed total
   ⟺ interior + the slope condition at one global `λ`. This is
   the landed `tolman_characterization` transported to the datum
   — cited, not redone, and never postulated.
5. **Equilibrium fence (form 3)** — `spectral_equilibrium_closed_form`
   proves the pin's form (3) verbatim: on an interior
   slope-equalized state the functional is
   `∑ i, log (1 + exp (λ · energy i)) − λ · ((∑ i, energy i) −
   total)`, a function of totals alone; corollary
   `spectralWeight_eq_of_same_totals`: two slope-equalized
   states of one datum with the same witness and the same total
   have the same functional value.

## Faces

- **K-SM-VAC — DOES NOT FIRE.** Form (1) certifies named states
  on both sides: different values at equal totals, and equal
  values on different distributions.
- **K-SM-FIAT — DOES NOT FIRE.** The characterization is the
  landed Tolman derivation (Fermat forward, summed tangent bound
  converse) transported; the closed form is derived from the
  pointwise identity (component 1), never postulated.
- **K-SM-PROXY — DOES NOT FIRE.** The functional is named or
  treated as a gravitational mass, a falling weight, or a
  coupling in no statement, definition, or theorem name here;
  no descent rule consumes it. There is no gravity object and
  no prediction in this module.
- **Pre-registered DIAL-INELIGIBLE; Dial 2 = 0.** Finite
  theorems about a declared functional are Register-A
  mathematics (K-SM-DIAL's fence stands over any other reading).
-/

variable {ι : Type*} [Fintype ι]

/-- **Component 1 (pointwise closed form):** at an interior
occupation, the site entropy is its slope's log-partition form:
`occEnt t = log (1 + exp (occSlope t)) − (1 − t) · occSlope t`.
Pure algebra of `Real.exp_log` at the odds ratio `(1 − t)/t`,
whose exponential is the slope. Tier T1. -/
theorem occEnt_eq_log_exp_slope {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    occEnt t
      = Real.log (1 + Real.exp (occSlope t)) - (1 - t) * occSlope t := by
  have h1t : (0 : ℝ) < 1 - t := by linarith
  have ht0' : t ≠ 0 := ne_of_gt ht0
  have hexp : Real.exp (occSlope t) = (1 - t) / t := by
    show Real.exp (Real.log (1 - t) - Real.log t) = (1 - t) / t
    rw [← Real.log_div (ne_of_gt h1t) ht0']
    exact Real.exp_log (div_pos h1t ht0)
  have hone : (1 : ℝ) + (1 - t) / t = 1 / t := by
    field_simp
    ring
  have hlog : Real.log (1 + Real.exp (occSlope t)) = - Real.log t := by
    rw [hexp, hone, one_div, Real.log_inv]
  rw [hlog]
  show -t * Real.log t - (1 - t) * Real.log (1 - t)
    = - Real.log t - (1 - t) * (Real.log (1 - t) - Real.log t)
  ring

/-- **Component 2 (positivity):** the site entropy is positive at
every interior occupation — both summands are a positive factor
times a negated negative log. Tier T1. -/
theorem occEnt_pos {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    0 < occEnt t := by
  have h1t : (0 : ℝ) < 1 - t := by linarith
  have hlogt : Real.log t < 0 := Real.log_neg ht0 ht1
  have hlog1t : Real.log (1 - t) < 0 := Real.log_neg h1t (by linarith)
  have h1 : (0 : ℝ) < -t * Real.log t := by
    rw [show (-t) * Real.log t = -(t * Real.log t) by ring]
    exact neg_pos.mpr (mul_neg_of_pos_of_neg ht0 hlogt)
  have h2 : (0 : ℝ) < (1 - t) * (- Real.log (1 - t)) :=
    mul_pos h1t (neg_pos.mpr hlog1t)
  have e : occEnt t
      = -t * Real.log t + (1 - t) * (- Real.log (1 - t)) := by
    show -t * Real.log t - (1 - t) * Real.log (1 - t)
      = -t * Real.log t + (1 - t) * (- Real.log (1 - t))
    ring
  rw [e]
  exact add_pos h1 h2

/-- **Component 2 (positivity of the functional):** on a nonempty
level set, the spectral weight of an interior state is positive —
a sum of positive site entropies. Tier T1. -/
theorem spectralWeight_pos [Nonempty ι] (D : SpectralDatum ι)
    {x : ι → ℝ} (hx : IsSpectralState D x) :
    0 < spectralWeight x := by
  show 0 < occEntSum x
  exact Finset.sum_pos (fun i _ => occEnt_pos (hx i).1 (hx i).2)
    Finset.univ_nonempty

/-- **Component 2 (the half-occupation value):** the site entropy
at `1/2` is `log 2`. Tier T1. -/
theorem occEnt_half : occEnt (1 / 2 : ℝ) = Real.log 2 := by
  have h12 : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
  have hlog : Real.log (1 / 2 : ℝ) = - Real.log 2 := by
    rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.log_inv]
  show -(1 / 2 : ℝ) * Real.log (1 / 2)
      - (1 - 1 / 2) * Real.log (1 - 1 / 2) = Real.log 2
  rw [h12, hlog]
  ring

/-- **Component 2 (the constant-state value):** at the
half-occupation state the functional is `(card ι) · log 2`.
Tier T1. -/
theorem spectralWeight_const_half :
    spectralWeight (fun _ : ι => (1 / 2 : ℝ))
      = (Fintype.card ι : ℝ) * Real.log 2 := by
  show (∑ _i : ι, occEnt (1 / 2 : ℝ)) = (Fintype.card ι : ℝ) * Real.log 2
  rw [Finset.sum_const, Finset.card_univ, occEnt_half, nsmul_eq_mul]

/-- **Component 2 (the counting bound, pointwise):** the site
entropy never exceeds `log 2` — the landed tangent bound
(`occEnt_le_tangent`) at the point `1/2`, whose slope vanishes
and whose value is `log 2`. Tier T1. -/
theorem occEnt_le_log_two {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    occEnt t ≤ Real.log 2 := by
  have h := occEnt_le_tangent (x := 1 / 2) (y := t)
    (by norm_num) (by norm_num) ht0 ht1
  have hs : occSlope (1 / 2 : ℝ) = 0 := by
    have h12 : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
    show Real.log (1 - 1 / 2) - Real.log (1 / 2) = 0
    rw [h12, sub_self]
  rw [occEnt_half, hs] at h
  simpa using h

/-- **Component 2 (the counting bound):** the functional is at
most `(card ι) · log 2` on every interior state — the sum of
the pointwise bounds. Tier T1. -/
theorem spectralWeight_le (D : SpectralDatum ι) {x : ι → ℝ}
    (hx : IsSpectralState D x) :
    spectralWeight x ≤ (Fintype.card ι : ℝ) * Real.log 2 := by
  calc spectralWeight x = ∑ i, occEnt (x i) := rfl
    _ ≤ ∑ _i : ι, Real.log 2 :=
        Finset.sum_le_sum
          (fun i _ => occEnt_le_log_two (hx i).1 (hx i).2)
    _ = (Fintype.card ι : ℝ) * Real.log 2 := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- **Component 4 (the characterization, the pin's form (2)
verbatim):** maximality at fixed conserved total ⟺ interior
together with the slope condition at one global `λ`. This is
the landed `tolman_characterization` at the datum's energies —
the Tolman route (Fermat forward, summed tangent bound
converse) cited and transported, never postulated
(K-SM-FIAT's fence). Tier T1. -/
theorem spectral_characterization : SpectralCharForm (ι := ι) := by
  intro D x₀
  exact tolman_characterization (V := ι) D.energy x₀ D.energy_pos

/-- **Component 5 (the equilibrium fence, the pin's form (3)
verbatim):** on an interior slope-equalized state with witness
`λ`, the functional collapses to the closed form
`∑ i, log (1 + exp (λ · energy i)) − λ · ((∑ i, energy i) −
total)` — a function of the state's totals (and the datum)
alone. Derived by summing the pointwise closed form
(`occEnt_eq_log_exp_slope`) along the slope condition; the
correction sum telescopes onto the conserved total.
Tier T1. -/
theorem spectral_equilibrium_closed_form :
    SpectralEquilibriumForm (ι := ι) := by
  intro D x₀ lam hx₀ hlam
  have hpt : ∀ i, occEnt (x₀ i)
      = Real.log (1 + Real.exp (lam * D.energy i))
        - (1 - x₀ i) * (lam * D.energy i) := by
    intro i
    rw [← hlam i]
    exact occEnt_eq_log_exp_slope (hx₀ i).1 (hx₀ i).2
  calc spectralWeight x₀ = ∑ i, occEnt (x₀ i) := rfl
    _ = ∑ i, (Real.log (1 + Real.exp (lam * D.energy i))
          - (1 - x₀ i) * (lam * D.energy i)) :=
        Finset.sum_congr rfl (fun i _ => hpt i)
    _ = (∑ i, Real.log (1 + Real.exp (lam * D.energy i)))
          - ∑ i, (1 - x₀ i) * (lam * D.energy i) := by
        rw [Finset.sum_sub_distrib]
    _ = (∑ i, Real.log (1 + Real.exp (lam * D.energy i)))
          - lam * ((∑ i, D.energy i) - spectralTotal D x₀) := by
        congr 1
        have hterm : ∀ i, (1 - x₀ i) * (lam * D.energy i)
            = lam * (D.energy i - D.energy i * x₀ i) :=
          fun i => by ring
        calc (∑ i, (1 - x₀ i) * (lam * D.energy i))
            = ∑ i, lam * (D.energy i - D.energy i * x₀ i) :=
              Finset.sum_congr rfl (fun i _ => hterm i)
          _ = lam * (∑ i, (D.energy i - D.energy i * x₀ i)) := by
              rw [Finset.mul_sum]
          _ = lam * ((∑ i, D.energy i)
                - ∑ i, D.energy i * x₀ i) := by
              rw [Finset.sum_sub_distrib]
          _ = lam * ((∑ i, D.energy i) - spectralTotal D x₀) := rfl

/-- **Component 5 (corollary — totals determine the value on
equilibrium):** two interior slope-equalized states of one
datum, with the same witness `λ` and the same conserved
total, have the same functional value — both equal the closed
form of `spectral_equilibrium_closed_form`, which sees
nothing else. The finite mirror of the scoping's §2.2 verdict:
on equilibrium states, the functional is a function of
totals. Tier T1. -/
theorem spectralWeight_eq_of_same_totals (D : SpectralDatum ι)
    (x y : ι → ℝ) (lam : ℝ)
    (hx : ∀ i, 0 < x i ∧ x i < 1) (hy : ∀ i, 0 < y i ∧ y i < 1)
    (hxs : ∀ i, occSlope (x i) = lam * D.energy i)
    (hys : ∀ i, occSlope (y i) = lam * D.energy i)
    (htot : spectralTotal D x = spectralTotal D y) :
    spectralWeight x = spectralWeight y := by
  have hx' := spectral_equilibrium_closed_form (ι := ι) D x lam hx hxs
  have hy' := spectral_equilibrium_closed_form (ι := ι) D y lam hy hys
  rw [hx', hy', htot]

/-- **Component 3 (swap symmetry on `Fin 2`):** the functional
of a two-level state is symmetric in the levels — the sum
over the two sites commutes. Tier T1. -/
theorem spectralWeight_swap (p q : ℝ) :
    spectralWeight (![p, q] : Fin 2 → ℝ)
      = spectralWeight (![q, p] : Fin 2 → ℝ) := by
  have e : ∀ u v : ℝ, spectralWeight (![u, v] : Fin 2 → ℝ)
      = occEnt u + occEnt v := by
    intro u v
    show (∑ i : Fin 2, occEnt ((![u, v] : Fin 2 → ℝ) i))
      = occEnt u + occEnt v
    rw [Fin.sum_univ_two]
    simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  rw [e p q, e q p, add_comm]

/-- **Component 3 (non-vacuity, the pin's form (1) verbatim):**
on the `(1, 2)` datum, `(1/20, 1/5)` and `(1/4, 1/10)` share
the total `9/20`, and the functional is strictly smaller at
the first: it is at most the equilibrium's value by maximality,
and equality would make it an equilibrium too — but the
characterization would then force one `λ` to equal both
`log 19` and `(log 4)/2`, and `log 4 < 2 · log 19` since
`4 < 361 = 19²`. On the `(1, 1)` datum, the swapped states
`(1/4, 1/2)` and `(1/2, 1/4)` are different distributions
with equal totals and equal values (`spectralWeight_swap`).
K-SM-VAC does not fire: the functional is certified
distribution-sensitive and distribution-insensitive on named
states, both at fixed totals. Tier T1. -/
theorem spectral_nonvacuity : SpectralNonvacuityForm := by
  have ha2 : ∀ i : Fin 2, 0 < (![1, 2] : Fin 2 → ℝ) i :=
    spectralDatum12.energy_pos
  have hintA : ∀ i : Fin 2, 0 < (![1 / 20, 1 / 5] : Fin 2 → ℝ) i
      ∧ (![1 / 20, 1 / 5] : Fin 2 → ℝ) i < 1 := by
    rw [Fin.forall_fin_two]
    constructor <;>
      simp [Matrix.cons_val_zero, Matrix.cons_val_one] <;> norm_num
  have heqB : IsTolmanEquilibrium (![1, 2] : Fin 2 → ℝ)
      (![1 / 4, 1 / 10] : Fin 2 → ℝ) :=
    tolman_witnesses.2.1
  have htot : spectralTotal spectralDatum12
        (![1 / 20, 1 / 5] : Fin 2 → ℝ)
      = spectralTotal spectralDatum12
        (![1 / 4, 1 / 10] : Fin 2 → ℝ) := by
    show (∑ i : Fin 2, (![1, 2] : Fin 2 → ℝ) i
        * (![1 / 20, 1 / 5] : Fin 2 → ℝ) i)
      = ∑ i : Fin 2, (![1, 2] : Fin 2 → ℝ) i
        * (![1 / 4, 1 / 10] : Fin 2 → ℝ) i
    rw [Fin.sum_univ_two, Fin.sum_univ_two]
    norm_num [Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons]
  refine ⟨⟨htot, ?_⟩, ⟨?_, ?_, ?_⟩⟩
  · -- The strict inequality at equal totals on the `(1, 2)` datum.
    have hle : spectralWeight (![1 / 20, 1 / 5] : Fin 2 → ℝ)
        ≤ spectralWeight (![1 / 4, 1 / 10] : Fin 2 → ℝ) :=
      heqB.2 _ hintA htot
    refine lt_of_le_of_ne hle (fun hEq => ?_)
    -- Equality would make `(1/20, 1/5)` an equilibrium as well.
    have hAeq : IsTolmanEquilibrium (![1, 2] : Fin 2 → ℝ)
        (![1 / 20, 1 / 5] : Fin 2 → ℝ) := by
      refine ⟨hintA, fun y hy hytot => ?_⟩
      have h1 : occEntSum y
          ≤ occEntSum (![1 / 4, 1 / 10] : Fin 2 → ℝ) :=
        heqB.2 y hy (hytot.trans htot)
      have hEq' : occEntSum (![1 / 20, 1 / 5] : Fin 2 → ℝ)
          = occEntSum (![1 / 4, 1 / 10] : Fin 2 → ℝ) := hEq
      linarith [h1, hEq']
    obtain ⟨-, lam, hlam⟩ :=
      (tolman_characterization (V := Fin 2) (![1, 2] : Fin 2 → ℝ)
        (![1 / 20, 1 / 5] : Fin 2 → ℝ) ha2).mp hAeq
    have h0 := hlam 0
    have h1 := hlam 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
    have hs20 : occSlope (1 / 20 : ℝ) = Real.log 19 := by
      have e2 : (1 : ℝ) - 1 / 20 = 19 / 20 := by norm_num
      have e3 : (19 / 20 : ℝ) / (1 / 20) = 19 := by norm_num
      show Real.log (1 - 1 / 20) - Real.log (1 / 20) = Real.log 19
      rw [e2, ← Real.log_div (by norm_num) (by norm_num), e3]
    have hs15 : occSlope (1 / 5 : ℝ) = Real.log 4 := by
      have e2 : (1 : ℝ) - 1 / 5 = 4 / 5 := by norm_num
      have e3 : (4 / 5 : ℝ) / (1 / 5) = 4 := by norm_num
      show Real.log (1 - 1 / 5) - Real.log (1 / 5) = Real.log 4
      rw [e2, ← Real.log_div (by norm_num) (by norm_num), e3]
    rw [hs20, mul_one] at h0
    rw [hs15] at h1
    -- `h0 : log 19 = lam`, `h1 : log 4 = lam * 2`; but `log 4 < 2 log 19`.
    have hbig : Real.log 4 < 2 * Real.log 19 := by
      have hlt : Real.log 4 < Real.log 361 :=
        (Real.log_lt_log_iff (by norm_num) (by norm_num)).mpr
          (by norm_num)
      have h361 : (361 : ℝ) = 19 * 19 := by norm_num
      have hmul : Real.log ((19 : ℝ) * 19)
          = Real.log 19 + Real.log 19 :=
        Real.log_mul (by norm_num) (by norm_num)
      rw [h361, hmul] at hlt
      linarith [hlt]
    rw [← h0] at h1
    linarith [h1, hbig]
  · -- The swapped states on the `(1, 1)` datum differ as distributions.
    intro h
    have h00 := congrFun h 0
    simp only [Matrix.cons_val_zero] at h00
    norm_num at h00
  · -- The swapped states share their total on the `(1, 1)` datum.
    show (∑ i : Fin 2, (![1, 1] : Fin 2 → ℝ) i
        * (![1 / 4, 1 / 2] : Fin 2 → ℝ) i)
      = ∑ i : Fin 2, (![1, 1] : Fin 2 → ℝ) i
        * (![1 / 2, 1 / 4] : Fin 2 → ℝ) i
    rw [Fin.sum_univ_two, Fin.sum_univ_two]
    norm_num [Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons]
  · -- The swapped states share their functional value.
    exact spectralWeight_swap (1 / 4) (1 / 2)

end ThetLogos
