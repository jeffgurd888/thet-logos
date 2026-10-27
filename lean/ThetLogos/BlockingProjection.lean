import ThetLogos.LatticeBlockingFlow
import Mathlib.Tactic

/-!
# ThetLogos.BlockingProjection — RG-2a + RG-2b: plaquette matching as a
projection — vacuity at the RG-1 seat, anchor at the torus seat (T1)

HONESTY LEDGER (read before citing):

- **What this module proves.** Two theorems about the plaquette-matching
  *projection* of the RG-2 scoping memo (§3) — the prescription "define
  `β′(β)` by matching the mean plaquette density between the blocked
  fine ensemble and the coarse Gibbs family":

  * **S1 (vacuity, `plaquetteMatched_flow_vacuous`).** At the RG-1 seat
    (`LatticeBlockingFlow`), for every `β > 0` there is **no** `β′` with
    `PlaquetteMatched flowBlocking β β'`: the coarse side of the
    matching is identically `0` (every coarse plaquette density
    vanishes, `flow_coarse_density`) while the blocked side is strictly
    positive. `β′(β)` fails to exist at that seat — not for lack of
    uniqueness but for lack of a target: the coarse theory is a single
    point and carries no plaquette information at all.
  * **S2 (the anchor, `plaquetteMatched_torus_zero`).** At the torus
    seat (general `(G, ρ)`, `M ≥ 2`), `PlaquetteMatched torusBlocking
    0 0` holds, and the matched value on both sides is exactly
    `1 − (tr (haarIntertwiner μG ρ)).re / d`. This is the projection's
    anchor point `β′(0) = 0` — the one fixed-point-shaped statement
    about the projection the corpus can honestly own today. At `β = 0`
    the projection moreover agrees with the truth:
    `BlockedGibbsIsCoarseGibbs` holds there (`torus_anchor_is_coarse_gibbs`,
    `LatticeBlocking` §7).

- **Standing kill (RG-2 scoping §0, quoted).** "Any presentation of a
  projected `β′(β)` as an RG *flow* — in prose, dossier, or post —
  without a theorem equating the blocked measure with a coarse
  measure, is killed on sight." This module defines **no flow, no
  curve, no β-function, and no fixed point of any dynamical system.**
  A projection is a statistic of a *pair* of measures; iterating a
  projection re-projects at every step and no semigroup property is
  implied, ever. RG-1 is precisely the theorem that the measure
  equality the flow reading would need fails at its seat for `β > 0`.

- **What "blocked side" means here (design resolution, recorded).**
  The blocked side of `PlaquetteMatched` is the fine Gibbs ensemble's
  mean plaquette density — the plaquette content the blocked theory
  inherits. At the RG-1 seat the fine mean plaquette density factors
  through `blockMap` (`flow_plaquetteDensity`), so this equals the
  blocked-measure expectation of the factored observable
  `effAction / 6` — proved, not assumed, as the bridge lemma
  `flow_blocked_meanPlaqDensity`.

- *(finite-lattice discipline)* Everything is a finite lattice at
  fixed spacing and volume. Dial 3's RG-curve absence becomes a
  *measured* absence at these two seats — nothing more. No continuum
  statement is made or implied.

- *(standing charter)* "Parts of the official Clay Yang–Mills
  statement closed by this module: 0." Dials: 0/4. NO CLAIM.
-/

namespace ThetLogos

open MeasureTheory Finset
open scoped Matrix ENNReal NNReal

/-! ## §1. The matched observable: mean plaquette density -/

section MeanDensity

variable {Λ : Type*} [Fintype Λ] {G : Type*} [Group G]
variable (σ : Fin 4 → Equiv.Perm Λ)
variable {d : ℕ} (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ))

/-- The **mean plaquette density** of a configuration: the Wilson
action per plaquette, `⟨S⟩/n_p` at unit coupling — the sum of
`plaquetteDensity` over all sites and unordered direction pairs,
divided by the plaquette count `|Λ| · 6`. This is the observable
matched by the RG-2 projection (scoping §3, design decision). -/
noncomputable def meanPlaqDensity (U : Config Λ G) : ℝ :=
  (∑ x : Λ, ∑ μ : Fin 4, ∑ ν ∈ Finset.Ioi μ, plaquetteDensity σ ρ U x μ ν)
    / ((Fintype.card Λ : ℝ) * 6)

end MeanDensity

/-! ## §2. Plaquette matching, and the β = 0 value of the observable -/

section Matching

variable {Λ Λ' : Type*} [Fintype Λ] [Fintype Λ']
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
variable (σ : Fin 4 → Equiv.Perm Λ) (σ' : Fin 4 → Equiv.Perm Λ')
variable (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
variable {d : ℕ} (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ))

/-- **Plaquette matching** (RG-2 scoping §3): `β′` is plaquette-matched
to `β` across the blocking scheme `B` when the fine ensemble's mean
plaquette density at `β` equals the coarse Gibbs ensemble's mean
plaquette density at `β′`. Where a matched `β′` exists it is a
*statistic of the pair of measures* — bookkeeping, not a flow (see
the module header's standing kill). -/
def PlaquetteMatched (B : BlockingScheme σ σ') (β β' : ℝ) : Prop :=
  gibbsExpectR σ μG ρ β (meanPlaqDensity σ ρ)
    = gibbsExpectR σ' μG ρ β' (meanPlaqDensity σ' ρ)

/-- Integrability of a plaquette trace against the configuration
measure: it is a finite sum of unitary matrix entries, each bounded
by `1` (the entry bound pattern of `integral_trace_plaquette`). -/
theorem integrable_trace_plaquette_config
    (hρcont : Continuous fun g : G => repMatrix ρ g) (x : Λ) (μ ν : Fin 4) :
    Integrable (fun U : Config Λ G =>
        Matrix.trace (repMatrix ρ (plaquette σ U x μ ν)))
      (configMeasure μG) := by
  have entryInt : ∀ a b : Fin d, Integrable
      (fun U : Config Λ G => repMatrix ρ (plaquette σ U x μ ν) a b)
      (configMeasure μG) := by
    intro a b
    refine Integrable.of_bound ?_ 1 (Filter.Eventually.of_forall fun U => ?_)
    · have hm : Measurable fun U : Config Λ G => plaquette σ U x μ ν :=
        measurable_plaquette σ x μ ν
      exact ((measurable_pi_apply b).comp ((measurable_pi_apply a).comp
        (hρcont.measurable.comp hm))).aestronglyMeasurable
    · exact abs_entry_of_mem_unitaryGroup (repMatrix_mem ρ _) a b
  have hfun : (fun U : Config Λ G =>
        Matrix.trace (repMatrix ρ (plaquette σ U x μ ν)))
      = fun U => ∑ i : Fin d, repMatrix ρ (plaquette σ U x μ ν) i i := by
    funext U
    rfl
  rw [hfun]
  exact integrable_finsetSum Finset.univ (fun i _ => entryInt i i)

/-- Integrability of a single plaquette density against the
configuration measure. -/
theorem integrable_plaquetteDensity_config
    (hρcont : Continuous fun g : G => repMatrix ρ g) (x : Λ) (μ ν : Fin 4) :
    Integrable (fun U : Config Λ G => plaquetteDensity σ ρ U x μ ν)
      (configMeasure μG) := by
  have hInt := integrable_trace_plaquette_config σ μG ρ hρcont x μ ν
  have hfun : (fun U : Config Λ G => plaquetteDensity σ ρ U x μ ν)
      = fun U => 1 - (Matrix.trace
          (repMatrix ρ (plaquette σ U x μ ν))).re / (d : ℝ) :=
    funext fun U => rfl
  rw [hfun]
  exact (integrable_const (1 : ℝ)).sub (hInt.re.div_const _)

/-- **The β = 0 value of the matched observable, at any lattice whose
shifts fix no site.** At `β = 0` the Gibbs expectation of the mean
plaquette density is `1 − (tr (haarIntertwiner μG ρ)).re / d`: every
plaquette contributes the Stage-0 Haar intertwiner trace
(`gibbsExpect_zero_plaquette`), and the plaquette count cancels. -/
theorem gibbsExpectR_zero_meanPlaqDensity
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hΛ : (Fintype.card Λ : ℝ) ≠ 0)
    (hfix : ∀ (x : Λ) {μ ν : Fin 4}, μ ≠ ν → σ μ x ≠ x ∧ σ ν x ≠ x) :
    gibbsExpectR σ μG ρ 0 (meanPlaqDensity σ ρ)
      = 1 - (Matrix.trace (haarIntertwiner μG ρ)).re / (d : ℝ) := by
  classical
  have htr : ∀ (x : Λ) (μ ν : Fin 4), μ ≠ ν →
      ∫ U, RCLike.re (Matrix.trace (repMatrix ρ (plaquette σ U x μ ν)))
          ∂(configMeasure μG)
        = (Matrix.trace (haarIntertwiner μG ρ)).re := by
    intro x μ ν hμν
    obtain ⟨hμx, hνx⟩ := hfix x hμν
    have hInt := integrable_trace_plaquette_config σ μG ρ hρcont x μ ν
    calc ∫ U, RCLike.re (Matrix.trace (repMatrix ρ (plaquette σ U x μ ν)))
            ∂(configMeasure μG)
        = RCLike.re (∫ U, Matrix.trace (repMatrix ρ (plaquette σ U x μ ν))
            ∂(configMeasure μG)) := integral_re hInt
      _ = RCLike.re (Matrix.trace (haarIntertwiner μG ρ)) := by
          rw [← gibbsExpect_zero σ μG ρ
            (fun U => Matrix.trace (repMatrix ρ (plaquette σ U x μ ν))),
            gibbsExpect_zero_plaquette σ μG ρ hρcont x hμν hμx hνx]
      _ = (Matrix.trace (haarIntertwiner μG ρ)).re := rfl
  have hdens : ∀ (x : Λ) (μ ν : Fin 4), μ ≠ ν →
      ∫ U, plaquetteDensity σ ρ U x μ ν ∂(configMeasure μG)
        = 1 - (Matrix.trace (haarIntertwiner μG ρ)).re / (d : ℝ) := by
    intro x μ ν hμν
    have hInt := integrable_trace_plaquette_config σ μG ρ hρcont x μ ν
    have hfun : (fun U : Config Λ G => plaquetteDensity σ ρ U x μ ν)
        = fun U => 1 - (Matrix.trace
            (repMatrix ρ (plaquette σ U x μ ν))).re / (d : ℝ) :=
      funext fun U => rfl
    have h2 : ∫ U, RCLike.re (Matrix.trace
            (repMatrix ρ (plaquette σ U x μ ν))) / (d : ℝ)
          ∂(configMeasure μG)
        = (Matrix.trace (haarIntertwiner μG ρ)).re / (d : ℝ) := by
      rw [show (fun U : Config Λ G =>
              RCLike.re (Matrix.trace (repMatrix ρ (plaquette σ U x μ ν)))
                / (d : ℝ))
            = fun U => (d : ℝ)⁻¹ *
              RCLike.re (Matrix.trace
                (repMatrix ρ (plaquette σ U x μ ν))) from
          funext fun U => div_eq_inv_mul _ _,
        integral_const_mul, htr x μ ν hμν, div_eq_inv_mul]
    rw [hfun]
    show ∫ U, (1 - RCLike.re (Matrix.trace
            (repMatrix ρ (plaquette σ U x μ ν))) / (d : ℝ))
          ∂(configMeasure μG)
        = 1 - (Matrix.trace (haarIntertwiner μG ρ)).re / (d : ℝ)
    rw [integral_sub (integrable_const (1 : ℝ)) ((hInt.re).div_const _),
      integral_const, measureReal_def, measure_univ, ENNReal.toReal_one,
      one_smul, h2]
  have hIntD : ∀ (x : Λ) (μ ν : Fin 4),
      Integrable (fun U => plaquetteDensity σ ρ U x μ ν)
        (configMeasure μG) :=
    fun x μ ν => integrable_plaquetteDensity_config σ μG ρ hρcont x μ ν
  have hμ : ∀ (x : Λ) (μ : Fin 4),
      ∫ U, (∑ ν ∈ Finset.Ioi μ, plaquetteDensity σ ρ U x μ ν)
          ∂(configMeasure μG)
        = (Finset.Ioi μ).card
          • (1 - (Matrix.trace (haarIntertwiner μG ρ)).re / (d : ℝ)) := by
    intro x μ
    calc ∫ U, (∑ ν ∈ Finset.Ioi μ, plaquetteDensity σ ρ U x μ ν)
            ∂(configMeasure μG)
        = ∑ ν ∈ Finset.Ioi μ, ∫ U, plaquetteDensity σ ρ U x μ ν
            ∂(configMeasure μG) :=
          integral_finsetSum _ (fun ν _ => hIntD x μ ν)
      _ = ∑ ν ∈ Finset.Ioi μ,
            (1 - (Matrix.trace (haarIntertwiner μG ρ)).re / (d : ℝ)) :=
          Finset.sum_congr rfl fun ν hν =>
            hdens x μ ν (ne_of_lt (Finset.mem_Ioi.mp hν))
      _ = (Finset.Ioi μ).card
            • (1 - (Matrix.trace (haarIntertwiner μG ρ)).re / (d : ℝ)) :=
          Finset.sum_const _
  have hx : ∀ x : Λ,
      ∫ U, (∑ μ : Fin 4, ∑ ν ∈ Finset.Ioi μ, plaquetteDensity σ ρ U x μ ν)
          ∂(configMeasure μG)
        = 6 * (1 - (Matrix.trace (haarIntertwiner μG ρ)).re / (d : ℝ)) := by
    intro x
    rw [integral_finsetSum Finset.univ (fun μ _ =>
      integrable_finsetSum _ (fun ν _ => hIntD x μ ν))]
    have h6 : (∑ μ : Fin 4, (Finset.Ioi μ).card) = 6 := by decide
    calc ∑ μ : Fin 4, ∫ U, (∑ ν ∈ Finset.Ioi μ,
              plaquetteDensity σ ρ U x μ ν) ∂(configMeasure μG)
        = ∑ μ : Fin 4, ((Finset.Ioi μ).card : ℝ)
            * (1 - (Matrix.trace (haarIntertwiner μG ρ)).re / (d : ℝ)) := by
          refine Finset.sum_congr rfl fun μ _ => ?_
          rw [hμ x μ, nsmul_eq_mul]
      _ = 6 * (1 - (Matrix.trace (haarIntertwiner μG ρ)).re / (d : ℝ)) := by
          rw [← Finset.sum_mul, ← Nat.cast_sum, h6, Nat.cast_ofNat]
  have hsum : ∫ U, (∑ x : Λ, ∑ μ : Fin 4, ∑ ν ∈ Finset.Ioi μ,
        plaquetteDensity σ ρ U x μ ν) ∂(configMeasure μG)
      = (Fintype.card Λ : ℝ)
        * (6 * (1 - (Matrix.trace (haarIntertwiner μG ρ)).re / (d : ℝ))) := by
    rw [integral_finsetSum Finset.univ (fun x _ =>
      integrable_finsetSum Finset.univ (fun μ _ =>
        integrable_finsetSum _ (fun ν _ => hIntD x μ ν)))]
    calc ∑ x : Λ, ∫ U, (∑ μ : Fin 4, ∑ ν ∈ Finset.Ioi μ,
              plaquetteDensity σ ρ U x μ ν) ∂(configMeasure μG)
        = ∑ _x : Λ, (6 * (1 - (Matrix.trace (haarIntertwiner μG ρ)).re
            / (d : ℝ))) :=
          Finset.sum_congr rfl fun x _ => hx x
      _ = (Fintype.card Λ : ℝ)
            * (6 * (1 - (Matrix.trace (haarIntertwiner μG ρ)).re
              / (d : ℝ))) := by
          rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
  unfold gibbsExpectR meanPlaqDensity
  rw [gibbsMeasure_zero σ μG ρ,
    show (fun U : Config Λ G => (∑ x : Λ, ∑ μ : Fin 4, ∑ ν ∈ Finset.Ioi μ,
          plaquetteDensity σ ρ U x μ ν) / ((Fintype.card Λ : ℝ) * 6))
        = fun U => ((Fintype.card Λ : ℝ) * 6)⁻¹
          * (∑ x : Λ, ∑ μ : Fin 4, ∑ ν ∈ Finset.Ioi μ,
            plaquetteDensity σ ρ U x μ ν) from
      funext fun U => div_eq_inv_mul _ _,
    integral_const_mul, hsum,
    show (Fintype.card Λ : ℝ)
          * (6 * (1 - (Matrix.trace (haarIntertwiner μG ρ)).re / (d : ℝ)))
        = ((Fintype.card Λ : ℝ) * 6)
          * (1 - (Matrix.trace (haarIntertwiner μG ρ)).re / (d : ℝ)) from by
      ring,
    inv_mul_cancel_left₀ (mul_ne_zero hΛ (by norm_num))]

end Matching

/-! ## §3. RG-2a: vacuity at the RG-1 seat -/

section FlowSeat

/-- The seat's effective action is nonnegative: each of its six terms
is `1 − sgn·sgn ∈ {0, 2}`. -/
theorem effAction_nonneg (V : Config (Fin 1) (Multiplicative (ZMod 2))) :
    0 ≤ effAction V := by
  unfold effAction
  refine Finset.sum_nonneg fun μ _ => Finset.sum_nonneg fun ν _ => ?_
  rcases flow_eq_one_or_seatS (V (0, μ)) with hμ | hμ <;>
    rcases flow_eq_one_or_seatS (V (0, ν)) with hν | hν <;>
    simp only [hμ, hν, sgnR_one, sgnR_seatS] <;> norm_num

/-- The fine mean plaquette density at the RG-1 seat, in blocked
coordinates: it factors through `blockMap` and equals
`effAction / 6`. -/
theorem flow_meanPlaqDensity (U : Config (Fin 2) (Multiplicative (ZMod 2))) :
    meanPlaqDensity flowσ flowSignRep U
      = effAction (blockMap flowσ flowσ' flowBlocking U) / 6 := by
  have hsum : ∀ x : Fin 2, (∑ μ : Fin 4, ∑ ν ∈ Finset.Ioi μ,
        plaquetteDensity flowσ flowSignRep U x μ ν)
      = effAction (blockMap flowσ flowσ' flowBlocking U) := by
    intro x
    show (∑ μ : Fin 4, ∑ ν ∈ Finset.Ioi μ,
        plaquetteDensity flowσ flowSignRep U x μ ν)
      = ∑ μ : Fin 4, ∑ ν ∈ Finset.Ioi μ,
        (1 - sgnR ((blockMap flowσ flowσ' flowBlocking U) (0, μ))
          * sgnR ((blockMap flowσ flowσ' flowBlocking U) (0, ν)))
    exact Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ =>
      flow_plaquetteDensity U x μ ν
  unfold meanPlaqDensity
  rw [Fin.sum_univ_two, hsum 0, hsum 1, Fintype.card_fin]
  ring

/-- The coarse mean plaquette density at the RG-1 seat vanishes
identically: every coarse plaquette density is `0`
(`flow_coarse_density`). -/
theorem flow_coarse_meanPlaqDensity
    (V : Config (Fin 1) (Multiplicative (ZMod 2))) :
    meanPlaqDensity flowσ' flowSignRep V = 0 := by
  unfold meanPlaqDensity
  have h0 : (∑ x : Fin 1, ∑ μ : Fin 4, ∑ ν ∈ Finset.Ioi μ,
      plaquetteDensity flowσ' flowSignRep V x μ ν) = 0 :=
    Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun μ _ =>
      Finset.sum_eq_zero fun ν _ => flow_coarse_density V x μ ν
  rw [h0, zero_div]

/-- The coarse side of the matching at the RG-1 seat is `0` at every
`β′`: the coarse family carries no plaquette information. -/
theorem flow_coarse_meanPlaqDensity_expect (β' : ℝ) :
    gibbsExpectR flowσ' μG₀ flowSignRep β' (meanPlaqDensity flowσ' flowSignRep)
      = 0 := by
  have hfun : meanPlaqDensity flowσ' flowSignRep = fun _ => (0 : ℝ) :=
    funext fun V => flow_coarse_meanPlaqDensity V
  rw [hfun]
  exact integral_zero _ _

/-- **The bridge.** At the RG-1 seat the blocked side of the matching
— defined as the fine ensemble's mean plaquette density — equals the
blocked-measure expectation of the factored observable
`effAction / 6`. The memo's "expectation under the blocked measure"
reading and the definition agree here by proof, because the fine
mean density factors through the blocking. -/
theorem flow_blocked_meanPlaqDensity (β : ℝ) :
    gibbsExpectR flowσ μG₀ flowSignRep β (meanPlaqDensity flowσ flowSignRep)
      = ∫ V, effAction V / 6
          ∂(blockedGibbsMeasure flowσ flowσ' μG₀ flowSignRep flowBlocking
            β) := by
  have hF : AEStronglyMeasurable (fun V => effAction V / 6)
      (blockedGibbsMeasure flowσ flowσ' μG₀ flowSignRep flowBlocking β) :=
    Measurable.of_discrete.aestronglyMeasurable
  rw [integral_blockedGibbsMeasure flowσ flowσ' μG₀ flowSignRep flowBlocking
    β (fun V => effAction V / 6) hF]
  show gibbsExpectR flowσ μG₀ flowSignRep β (meanPlaqDensity flowσ flowSignRep)
      = ∫ U, effAction (blockMap flowσ flowσ' flowBlocking U) / 6
          ∂(gibbsMeasure flowσ μG₀ flowSignRep β)
  unfold gibbsExpectR
  exact integral_congr_ae (Filter.Eventually.of_forall fun U =>
    flow_meanPlaqDensity U)

/-- The blocked side of the matching at the RG-1 seat is **strictly
positive** for `β > 0`: the factored observable `effAction / 6` is
nonnegative everywhere, equals `1` at `flowV₂`, and `flowV₂` carries
blocked mass `exp (−12β) / (16 Z_β) > 0` (RG-1's exact computation). -/
theorem flow_blocked_meanPlaqDensity_pos {β : ℝ} (hβ : 0 < β) :
    0 < gibbsExpectR flowσ μG₀ flowSignRep β
      (meanPlaqDensity flowσ flowSignRep) := by
  rw [flow_blocked_meanPlaqDensity β]
  have hZ : (0 : ℝ) < gibbsPartition flowσ μG₀ flowSignRep β :=
    gibbsPartition_pos flowσ μG₀ flowSignRep flowSignRep_continuous
      (by norm_num) β
  haveI := isProbabilityMeasure_blockedGibbsMeasure flowσ flowσ' μG₀
    flowSignRep flowBlocking flowSignRep_continuous (by norm_num) β
  have hmass : (blockedGibbsMeasure flowσ flowσ' μG₀ flowSignRep
        flowBlocking β).real {flowV₂}
      = Real.exp (-(12 * β))
        / (16 * gibbsPartition flowσ μG₀ flowSignRep β) := by
    rw [← flowObs_integral, rg1_blocked_expect_two]
  have hInt : Integrable (fun V => effAction V / 6)
      (blockedGibbsMeasure flowσ flowσ' μG₀ flowSignRep flowBlocking β) := by
    refine Integrable.of_bound Measurable.of_discrete.aestronglyMeasurable
      (∑ V, ‖effAction V / 6‖) (Filter.Eventually.of_forall fun V => ?_)
    exact Finset.single_le_sum (fun V' _ => norm_nonneg (effAction V' / 6))
      (Finset.mem_univ V)
  rw [integral_fintype hInt]
  simp only [smul_eq_mul]
  have hterm : ∀ V : Config (Fin 1) (Multiplicative (ZMod 2)),
      0 ≤ (blockedGibbsMeasure flowσ flowσ' μG₀ flowSignRep flowBlocking β).real
          {V} * (effAction V / 6) :=
    fun V => mul_nonneg measureReal_nonneg
      (div_nonneg (effAction_nonneg V) (by norm_num))
  have h2 : (blockedGibbsMeasure flowσ flowσ' μG₀ flowSignRep flowBlocking
        β).real {flowV₂} * (effAction flowV₂ / 6)
      = Real.exp (-(12 * β))
        / (16 * gibbsPartition flowσ μG₀ flowSignRep β) := by
    rw [hmass, effAction_flowV₂]
    norm_num
  calc (0 : ℝ) < Real.exp (-(12 * β))
          / (16 * gibbsPartition flowσ μG₀ flowSignRep β) :=
        div_pos (Real.exp_pos _) (mul_pos (by norm_num) hZ)
    _ = (blockedGibbsMeasure flowσ flowσ' μG₀ flowSignRep flowBlocking
          β).real {flowV₂} * (effAction flowV₂ / 6) := h2.symm
    _ ≤ ∑ V, (blockedGibbsMeasure flowσ flowσ' μG₀ flowSignRep flowBlocking
          β).real {V} * (effAction V / 6) :=
        Finset.single_le_sum (fun V _ => hterm V) (Finset.mem_univ flowV₂)

end FlowSeat

section FlowVacuity

variable {Λ Λ' : Type*} [Fintype Λ] [Fintype Λ']

/-- **S1 (RG-2a headline): plaquette matching is vacuous at the RG-1
seat.** For every `β > 0` there is no `β′` plaquette-matched to `β`
across `flowBlocking`: the coarse side of the matching is
identically `0` while the blocked side is strictly positive, so the
matching equation has no solution and `β′(β)` fails to exist at this
seat. A negative theorem about the canonical projection at the
canonical seat — it disciplines the whole RG-2 line. -/
theorem plaquetteMatched_flow_vacuous {β : ℝ} (hβ : 0 < β) (β' : ℝ) :
    ¬ PlaquetteMatched flowσ flowσ' μG₀ flowSignRep flowBlocking β β' := by
  intro h
  unfold PlaquetteMatched at h
  rw [flow_coarse_meanPlaqDensity_expect β'] at h
  exact (flow_blocked_meanPlaqDensity_pos hβ).ne' h

end FlowVacuity

/-! ## §4. RG-2b: the anchor at the torus seat -/

section TorusAnchor

variable {M : ℕ} [NeZero M]
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
variable (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
variable {d : ℕ} (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ))

/-- The coarse side of the torus anchor: at `β = 0` the coarse torus
mean plaquette density expectation is the Haar intertwiner value. -/
theorem torus_meanPlaqDensity_expect_zero_coarse
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hM : 2 ≤ M) :
    gibbsExpectR (torusShift M) μG ρ 0 (meanPlaqDensity (torusShift M) ρ)
      = 1 - (Matrix.trace (haarIntertwiner μG ρ)).re / (d : ℝ) := by
  refine gibbsExpectR_zero_meanPlaqDensity (torusShift M) μG ρ hρcont ?_ ?_
  · have h : 0 < Fintype.card (Fin 4 → ZMod M) :=
      Fintype.card_pos_iff.mpr ⟨fun _ => 0⟩
    exact_mod_cast h.ne'
  · intro x μ ν hμν
    exact ⟨torusShift_ne_self M hM μ x, torusShift_ne_self M hM ν x⟩

/-- The blocked (fine) side of the torus anchor: at `β = 0` the fine
torus mean plaquette density expectation is the same Haar intertwiner
value. -/
theorem torus_meanPlaqDensity_expect_zero_fine
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hM : 2 ≤ M) :
    gibbsExpectR (torusShift (2 * M)) μG ρ 0
        (meanPlaqDensity (torusShift (2 * M)) ρ)
      = 1 - (Matrix.trace (haarIntertwiner μG ρ)).re / (d : ℝ) := by
  haveI : NeZero (2 * M) := ⟨Nat.mul_ne_zero (by norm_num)
    (Nat.pos_iff_ne_zero.mp (Nat.pos_of_neZero M))⟩
  refine gibbsExpectR_zero_meanPlaqDensity (torusShift (2 * M)) μG ρ
    hρcont ?_ ?_
  · have h : 0 < Fintype.card (Fin 4 → ZMod (2 * M)) :=
      Fintype.card_pos_iff.mpr ⟨fun _ => 0⟩
    exact_mod_cast h.ne'
  · intro x μ ν hμν
    exact ⟨torusShift_ne_self (2 * M) (by omega) μ x,
      torusShift_ne_self (2 * M) (by omega) ν x⟩

/-- **S2 (RG-2b headline): the anchor.** At the torus seat (general
`(G, ρ)`, `M ≥ 2`) the projection is anchored at the origin:
`PlaquetteMatched torusBlocking 0 0` — `β′(0) = 0` — with matched
value `1 − (tr (haarIntertwiner μG ρ)).re / d` on both sides (the two
preceding lemmas). This is a statement about the *projection*, not a
flow: see the module header's standing kill. -/
theorem plaquetteMatched_torus_zero
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hM : 2 ≤ M) :
    PlaquetteMatched (torusShift (2 * M)) (torusShift M) μG ρ
      torusBlocking 0 0 := by
  unfold PlaquetteMatched
  rw [torus_meanPlaqDensity_expect_zero_fine μG ρ hρcont hM,
    torus_meanPlaqDensity_expect_zero_coarse μG ρ hρcont hM]

/-- **Anchor consistency.** At `β = 0` the projection's anchor agrees
with the truth: the blocked Gibbs measure at `0` *is* the coarse
Gibbs measure at `0` (`LatticeBlocking` §7, the one point where
matching is a measure equality). For `β > 0` this coincidence is
exactly what RG-1 destroys at its seat. -/
theorem torus_anchor_is_coarse_gibbs :
    BlockedGibbsIsCoarseGibbs (torusShift (2 * M)) (torusShift M) μG ρ
      torusBlocking 0 0 :=
  blockedGibbsIsCoarseGibbs_zero (torusShift (2 * M)) (torusShift M) μG ρ
    torusBlocking

end TorusAnchor

end ThetLogos

