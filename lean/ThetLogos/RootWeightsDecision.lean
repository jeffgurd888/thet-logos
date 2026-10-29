import ThetLogos.RootWeightsPost

/-!
# ThetLogos.RootWeightsDecision — Q-ROOT decided at the owned level (QR-D1)

**The answer is NO at the owned level:** the corpus's three canonical
allocation modes are faithful-only, so the triad (−1, 0, 2) is not
realized as weights by any of them.

Each mode is strictly positive at every seat, by a landed fence:

- a `ThermalClock` carries faithfulness as a structure field, so
  every clock weight is strictly positive;
- Gibbs diagonal weights are exponentials, hence strictly positive
  (`gibbsDiagWeights_pos`, for all real parameters);
- payoff allocations are reciprocals of positive rates, hence
  strictly positive.

The triad's void seat (seat 0) is −1, so every fence kills its mode
already at seat 0.

**Scope fence.** This decides the three owned modes ONLY. It does
not kill the triad as weights in general, and it does not preclude
a future corpus-native signed allocation object — such an object
would be a NEW entry under the relabeling rule, never a retrofit of
the post. Floor 1 (the triad as Jeff's notation) stands; Floors 2
and 3 stay KILLED.

**Status: NO CLAIM; parts of the Clay statement closed: 0;
dials 0/4.**

The post module's question placeholder stays in the tree as the
posted question; this module is the decision record, not an edit
of the post.
-/

namespace ThetLogos

/-- **Fence 1 — clock mode (Tier T1).** No `ThermalClock 3` has
    `rootTriadWeights` as its weights: a clock is faithful, so its
    seat-0 weight is strictly positive, while the triad's seat-0
    weight is −1. -/
theorem rootWeightsRealized_clock_impossible :
    ¬ ∃ C : ThermalClock 3, C.weights = rootTriadWeights := by
  rintro ⟨C, h⟩
  have hpos : 0 < C.weights 0 := C.faithful 0
  have h0 : C.weights 0 = -1 := by
    have hcong := congrFun h 0
    simpa [rootTriadWeights] using hcong
  rw [h0] at hpos
  norm_num at hpos

/-- **Fence 2 — Gibbs mode (Tier T1).** No Gibbs diagonal weights
    equal `rootTriadWeights`: Gibbs weights are strictly positive
    at every seat, for all real parameters, while the triad's
    seat-0 weight is −1. -/
theorem rootWeightsRealized_gibbs_impossible :
    ¬ ∃ (β logZ : ℝ) (lam : Fin 3 → ℝ),
      gibbsDiagWeights β lam logZ = rootTriadWeights := by
  rintro ⟨β, logZ, lam, h⟩
  have hpos : 0 < gibbsDiagWeights β lam logZ 0 :=
    gibbsDiagWeights_pos β lam logZ 0
  have h0 : gibbsDiagWeights β lam logZ 0 = -1 := by
    have hcong := congrFun h 0
    simpa [rootTriadWeights] using hcong
  rw [h0] at hpos
  norm_num at hpos

/-- **Fence 3 — payoff mode (Tier T1).** No payoff allocation of
    a positive rate function equals `rootTriadWeights`: the
    reciprocal of a positive rate is strictly positive, while the
    triad's seat-0 weight is −1. -/
theorem rootWeightsRealized_payoff_impossible :
    ¬ ∃ lam : Fin 3 → ℝ, (∀ s, 0 < lam s) ∧
      (fun s => (lam s)⁻¹) = rootTriadWeights := by
  rintro ⟨lam, hrates, h⟩
  have hpos : 0 < (lam 0)⁻¹ := inv_pos.mpr (hrates 0)
  have h0 : (lam 0)⁻¹ = -1 := by
    have hcong := congrFun h 0
    simpa [rootTriadWeights] using hcong
  rw [h0] at hpos
  norm_num at hpos

/-- **Q-ROOT decided at the owned level (Tier T1).** The triad
    (−1, 0, 2) is not realized as weights by any of the corpus's
    three canonical allocation modes: clock, Gibbs, or payoff.
    This is the assembly of the three fences above through the
    definitional unfolding `rootWeightsRealized_iff`. -/
theorem rootWeights_not_realized :
    ¬ RootWeightsRealized rootTriadWeights := by
  intro h
  rcases (rootWeightsRealized_iff rootTriadWeights).mp h with
    h | h | h
  · exact rootWeightsRealized_clock_impossible h
  · exact rootWeightsRealized_gibbs_impossible h
  · exact rootWeightsRealized_payoff_impossible h

end ThetLogos
