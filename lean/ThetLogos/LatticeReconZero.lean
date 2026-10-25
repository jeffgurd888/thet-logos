import ThetLogos.LatticeBoundaryOp
import ThetLogos.LatticeGramSeries
import ThetLogos.LatticeTransferIdent

/-!
# ThetLogos.LatticeReconZero — Stage 2, brick S2-1: the full
reconstruction at `β = 0`

The first build of the Stage 2 reconstruction ladder (Road Map
Item 2), under the S2-0 paper gate
(`whitepaper/stage2-s20-paper-gate-2026-10-24.md`, Target S2-1):
Picture A (abstract GNS quotient), the algebra fixed as
`𝔸 := 𝔸⁺`, the positive-half algebra of bounded measurable
functions on `(↥halfLinks → G)` read on configurations through
`restrictConfig halfLinks`. The gate's registered prediction
**P-0** was: at `β = 0`, `osForm₀ F F = |ω₀(F)|²` on `𝔸⁺`, the
null space is `ker ω₀`, the quotient is `ℂ·Ω`, `T̂₀ = id`,
`Ĥ₀ = 0`.

**Verdict: PARTIAL — kill K-S2-1(a) FIRES on `𝔸⁺`; the brick
lands whole on the charter's named fallback, `𝔸_slice`.**
What the computation gives, in order:

- **§1 (the kill, exhibited and computed).** On the *closed*
  half, positivity at `β = 0` is **false**. The mechanism is
  visible in the corpus's own definitions: `reflConfig` inverts
  time links, the plane links (time links at base times
  `N/2 − 1` and `N − 1`) are fixed by `reflLink`, and the
  `N/2 − 1` stratum lies *inside* the closed half — so an
  observable supported on a plane link is read by the
  reflected factor at the *same* coordinate, inverted, and
  pairs with itself in `L²`, not through the state. At the
  corpus's own U(1) seat (`G = Circle`, `μG = haarProb`,
  `ρ = circleRep`, `N = 4`), the plane observable
  `f(y) = (y ℓ₀ : ℂ) − ((y ℓ₀)⁻¹ : ℂ)` has `ω₀(f) = 0` and
  `osForm₀ F F = −2`, computed exactly
  (`osForm_planeObs_diag`). A negative diagonal, exhibited:
  **K-S2-1(a) fires; the closed-half algebra choice dies at
  the `β = 0` seat, and P-0 is recorded as REFUTED on `𝔸⁺`.**
- **§2 (where the fence actually runs).** The gate's T1.1
  argument is sound exactly on the *plane-independent*
  observables — the strict-half algebra pulled back along
  `restrictPos`. There the reflected reading is `mirrorP` of
  the negative half (`reflConfig_apply_pos`, landed), the
  split factorization at `Bdry ≡ 1` over the decoupled
  measure separates the halves, and the landed marginal
  identities give the pairing identity
  `osForm₀ = conj(strictState χ) * strictState φ`
  (`osForm_zero_strict_pair`): positivity holds, the null
  space is `ker strictState`, the quotient is `ℂ·Ω`. This is
  also the corpus's own Stage 1b-B support class (`posLinks`)
  — the strict half was the positivity seat all along.
- **§3 (the fallback seat, P-0 confirmed verbatim).** On
  `𝔸_slice` (slice observables `F_φ`), the full package
  lands: the pairing identity
  `osForm₀ F_φ F_χ = conj(coord φ) * coord χ` with
  `coord φ = ∫ φ d(pi slice)` (via S1's polarized identity,
  the landed rank-one `T₀ = ⟪Ω, ·⟫ • Ω`, and
  `sliceMeasure_zero`); the null space is `{coord = 0}`; the
  quotient is `ℂ·Ω₀` with `Ω₀ = [1]`, `coord 1 = 1`, `coord`
  surjective; the reconstructed transfer operator is
  `T̂₀ = id` (its pairing is the landed `T₀`'s pairing, so
  `T₀` descends to it); the Hamiltonian is `Ĥ₀ = 0`, with
  `exp(−Ĥ₀) = T̂₀`. The degenerate seat stands whole.

**Fences.** This is the `β = 0` seat ONLY: no `β > 0`
reconstruction is stated or implied; no continuum, no limit,
no vacuum-uniqueness claim beyond the `β = 0` quotients
computed. `T̂₀`'s identity comes from the OS/S1 pairing,
never from `transferOp` on arbitrary vectors (the R2 fence
stands). The gate's two-step pairing `P₂` is *not* used
here; see the verdict memo for why (it does not descend at
`β = 0`, even on `𝔸_slice` — a repair S2-2 must make).

NO CLAIM. Parts of the official Clay Yang–Mills statement
closed by this module: 0. Stage 1b-B label unchanged
(positivity T1 for U(1) at all `β ≥ 0`; general `(G, ρ)`
OPEN).

- Status: brick S2-1 — built 2026-10-24 under the Stage 2
  reconstruction charter and the S2-0 gate; verdict PARTIAL
  (K-S2-1(a) fired on `𝔸⁺`; fallback `𝔸_slice` STANDS with
  P-0 confirmed); parent-verified 2026-10-24 (targeted build
  exit 0, strict recount, axiom check). Dossier:
  `whitepaper/stage2-s21-partial-plane-kill-2026-10-24.md`.
-/

namespace ThetLogos

open MeasureTheory Finset
open scoped Matrix ENNReal NNReal

section HalfLift

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ))
  {N : ℕ} [NeZero N]

/-! ## §0. The lift of half observables

The gate's reading of `𝔸⁺` on full configurations: a
half-configuration function read through the landed
restriction `restrictConfig halfLinks`. -/

/-- The lift of a closed-half observable to a configuration
observable, through the landed half restriction. -/
def halfLift (f : (↥(halfLinks (N := N)) → G) → ℂ) :
    Config (Fin 4 → ZMod N) G → ℂ :=
  fun U => f (restrictConfig halfLinks U)

theorem halfLift_apply (f : (↥(halfLinks (N := N)) → G) → ℂ)
    (U : Config (Fin 4 → ZMod N) G) :
    halfLift f U = f (restrictConfig halfLinks U) := rfl

end HalfLift

/-! ## §1. The kill: positivity on the closed half fails at
`β = 0`, exhibited

The seat is the corpus's own U(1) seat: `G = Circle`,
`μG = haarProb Circle`, `ρ = circleRep`, at `N = 4`. The
plane link `ℓ₀` is the time link based at time `1 = N/2 − 1`:
it is fixed by `reflLink` and lies in the closed half. The
observable reads that one coordinate as `z − z⁻¹`. -/

section Counterexample

/-- The plane link at `N = 4`: the time link whose base site
has time coordinate `1 = N/2 − 1`, based at the origin in
space. -/
def planeLink : Link (Fin 4 → ZMod 4) :=
  (Function.update (0 : Fin 4 → ZMod 4) 0 1, 0)

theorem planeLink_time : planeLink.1 0 = (1 : ZMod 4) :=
  Function.update_self 0 1 (0 : Fin 4 → ZMod 4)

theorem planeLink_val : (planeLink.1 0).val = 1 := by
  rw [planeLink_time]
  rfl

/-- The plane link lies in the closed positive half
(base time `1 < 4/2`). -/
theorem planeLink_mem_halfLinks :
    planeLink ∈ halfLinks (N := 4) := by
  rw [mem_halfLinks]
  show (planeLink.1 0).val < 4 / 2
  rw [planeLink_val]
  decide

/-- The plane link is fixed by the link reflection:
time links at base time `N/2 − 1` are plane links. -/
theorem reflLink_planeLink :
    reflLink planeLink = planeLink := by
  have h := (reflLink_eq_self_iff (⟨2, rfl⟩ : Even 4)
    planeLink.1 planeLink.2).mpr ⟨rfl, Or.inl ?_⟩
  · exact h
  · show (planeLink.1 0).val = 4 / 2 - 1
    rw [planeLink_val]

/-- The reflection of a configuration at the plane link is
the inversion of the configuration's own value there: the
reflected factor reads the *same* coordinate. -/
theorem planeLink_dir : planeLink.2 = 0 := rfl

theorem reflConfig_planeLink (U : Config (Fin 4 → ZMod 4) Circle) :
    reflConfig U planeLink = (U planeLink)⁻¹ := by
  show (if planeLink.2 = 0
      then (U (reflLink planeLink))⁻¹
      else U (reflLink planeLink)) = (U planeLink)⁻¹
  rw [reflLink_planeLink]
  split
  · rfl
  · exact absurd planeLink_dir ‹¬ planeLink.2 = 0›

set_option maxRecDepth 8192 in
/-- The plane link as an element of the closed half.
(The raised recursion limit is for the concrete `N = 4`
Finset-subtype membership unification only.) -/
def planeHalf : ↥(halfLinks (N := 4) : Finset (Link (Fin 4 → ZMod 4))) :=
  ⟨planeLink, planeLink_mem_halfLinks⟩

/-- The plane coordinate of a closed-half configuration. -/
def planeCoord : (↥(halfLinks (N := 4)) → Circle) → Circle :=
  fun y => y planeHalf

/-- **The exhibited observable**: the plane coordinate read
as `z − z⁻¹` in `ℂ`. Bounded, continuous, supported on the
single plane coordinate inside the closed half. -/
noncomputable def planeObs : (↥(halfLinks (N := 4)) → Circle) → ℂ :=
  fun y => ((planeCoord y : ℂ)) - (((planeCoord y)⁻¹ : Circle) : ℂ)

theorem planeCoord_continuous : Continuous planeCoord :=
  continuous_apply planeHalf

theorem planeObs_continuous : Continuous planeObs := by
  have h1 : Continuous
      fun y : (↥(halfLinks (N := 4)) → Circle) => ((planeCoord y : ℂ)) :=
    continuous_subtype_val.comp planeCoord_continuous
  have h2 : Continuous
      fun y : (↥(halfLinks (N := 4)) → Circle) =>
        (((planeCoord y)⁻¹ : Circle) : ℂ) := by
    have hinv : Continuous fun c : Circle => ((c⁻¹ : Circle) : ℂ) :=
      continuous_subtype_val.comp continuous_inv
    exact hinv.comp planeCoord_continuous
  exact h1.sub h2

theorem planeObs_norm_le (y : ↥(halfLinks (N := 4)) → Circle) :
    ‖planeObs y‖ ≤ 2 := by
  have h1 : ‖((planeCoord y : ℂ))‖ = 1 := by simp
  have h2 : ‖(((planeCoord y)⁻¹ : Circle) : ℂ)‖ = 1 := by simp
  calc ‖planeObs y‖
      ≤ ‖((planeCoord y : ℂ))‖
        + ‖(((planeCoord y)⁻¹ : Circle) : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by rw [h1, h2]; norm_num

/-- The lifted plane observable at a configuration is the
`z − z⁻¹` reading of the configuration's own plane
coordinate. -/
theorem halfLift_planeObs_apply (U : Config (Fin 4 → ZMod 4) Circle) :
    halfLift planeObs U
      = ((U planeLink : ℂ)) - (((U planeLink)⁻¹ : Circle) : ℂ) :=
  rfl

/-- The reflected plane observable reads the same
coordinate, inverted — and the observable negates. -/
theorem halfLift_planeObs_reflConfig
    (U : Config (Fin 4 → ZMod 4) Circle) :
    halfLift planeObs (reflConfig U)
      = - halfLift planeObs U := by
  rw [halfLift_planeObs_apply, halfLift_planeObs_apply,
    reflConfig_planeLink, inv_inv]
  ring

/-- The coercion of a circle element's inverse is the
inverse in `ℂ`. -/
theorem circle_coe_inv (c : Circle) : ((c⁻¹ : Circle) : ℂ) = (c : ℂ)⁻¹ :=
  Circle.coe_inv c

/-- The conjugate of a circle element's coercion is its
inverse (the element has norm `1`). -/
theorem circle_conj_coe (c : Circle) :
    (starRingEnd ℂ) ((c : ℂ)) = (c : ℂ)⁻¹ :=
  (Circle.coe_inv_eq_conj c).symm.trans (Circle.coe_inv c)

/-- **The integrand identity.** At the plane observable,
the OS integrand is a perfect square of one coordinate:
the reflected factor equals the observable itself, so the
integrand is `F(U)²`, the square of `w − w⁻¹` at
`w = (U ℓ₀ : ℂ)` — in character form, `w² + w⁻² − 2`. -/
theorem planeObs_integrand (U : Config (Fin 4 → ZMod 4) Circle) :
    reflObs (halfLift planeObs) U * halfLift planeObs U
      = (((U planeLink ^ (2 : ℤ) : Circle) : ℂ)
        + ((U planeLink ^ (-2 : ℤ) : Circle) : ℂ) - 2) := by
  have hF : halfLift planeObs U
      = ((U planeLink : ℂ)) - (((U planeLink)⁻¹ : Circle) : ℂ) :=
    halfLift_planeObs_apply U
  have hw0 : ((U planeLink : ℂ)) ≠ 0 := by
    have h : ‖((U planeLink : ℂ))‖ = 1 := by simp
    exact norm_ne_zero_iff.mp (by rw [h]; exact one_ne_zero)
  have hconj : (starRingEnd ℂ)
        (halfLift planeObs (reflConfig U)) = halfLift planeObs U := by
    rw [halfLift_planeObs_reflConfig, hF]
    have hci : (starRingEnd ℂ) (((U planeLink : ℂ))⁻¹)
        = ((U planeLink : ℂ)) := by
      rw [← circle_coe_inv, circle_conj_coe, circle_coe_inv, inv_inv]
    simp only [map_sub, circle_conj_coe, circle_coe_inv, neg_sub]
    rw [hci]
  have hsq : (((U planeLink : ℂ)) - ((U planeLink : ℂ))⁻¹) ^ 2
      = ((U planeLink : ℂ)) ^ 2 + (((U planeLink : ℂ))⁻¹) ^ 2 - 2 := by
    have hw1 : ((U planeLink : ℂ)) * ((U planeLink : ℂ))⁻¹ = 1 :=
      mul_inv_cancel₀ hw0
    calc (((U planeLink : ℂ)) - ((U planeLink : ℂ))⁻¹) ^ 2
        = ((U planeLink : ℂ)) ^ 2
          - 2 * (((U planeLink : ℂ)) * ((U planeLink : ℂ))⁻¹)
          + (((U planeLink : ℂ))⁻¹) ^ 2 := by ring
      _ = ((U planeLink : ℂ)) ^ 2 + (((U planeLink : ℂ))⁻¹) ^ 2
          - 2 := by
          rw [hw1]; ring
  calc reflObs (halfLift planeObs) U * halfLift planeObs U
      = ((starRingEnd ℂ) (halfLift planeObs (reflConfig U)))
        * halfLift planeObs U := rfl
    _ = halfLift planeObs U * halfLift planeObs U := by rw [hconj]
    _ = (((U planeLink : ℂ)) - ((U planeLink : ℂ))⁻¹) ^ 2 := by
        rw [hF, circle_coe_inv]; ring
    _ = ((U planeLink : ℂ)) ^ 2 + (((U planeLink : ℂ))⁻¹) ^ 2 - 2 :=
        hsq
    _ = (((U planeLink ^ (2 : ℤ) : Circle) : ℂ)
        + ((U planeLink ^ (-2 : ℤ) : Circle) : ℂ) - 2) := by
        rw [coe_zpow_circle, coe_zpow_circle]
        simp [zpow_ofNat, zpow_neg, inv_pow]

/-- The character integrand of `planeObs_integrand`, as a
function of the plane coordinate alone. -/
noncomputable def planeChar : Circle → ℂ :=
  fun c => ((c ^ (2 : ℤ) : Circle) : ℂ) + ((c ^ (-2 : ℤ) : Circle) : ℂ) - 2

theorem planeChar_continuous : Continuous planeChar := by
  have h2 : Continuous fun c : Circle => ((c ^ (2 : ℤ) : Circle) : ℂ) :=
    continuous_subtype_val.comp (continuous_id.zpow 2)
  have hm2 : Continuous fun c : Circle => ((c ^ (-2 : ℤ) : Circle) : ℂ) :=
    continuous_subtype_val.comp (continuous_id.zpow (-2))
  exact (h2.add hm2).sub continuous_const

/-- The plane coordinate's marginal under the configuration
product measure is the Haar probability itself. -/
theorem configMeasure_map_planeLink :
    (configMeasure (haarProb Circle)).map (Function.eval planeLink)
      = haarProb Circle := by
  show (Measure.pi fun _ : Link (Fin 4 → ZMod 4) => haarProb Circle).map
      (Function.eval planeLink) = haarProb Circle
  rw [Measure.pi_map_eval]
  simp [measure_univ]

/-- **The computation**: the OS diagonal of the plane
observable at `β = 0` is exactly `−2`. The character
integrals vanish (`∫ w^{±2} = 0`) and the constant
contributes `−2`. -/
theorem osForm_planeObs_diag :
    osForm (haarProb Circle) circleRep 0
        (halfLift planeObs) (halfLift planeObs) = -2 := by
  have hd : (0 : ℕ) < 1 := zero_lt_one
  have hint : ∀ e : ℤ, Integrable
      (fun c : Circle => ((c ^ e : Circle) : ℂ)) (haarProb Circle) := by
    intro e
    have hcont : Continuous fun c : Circle => ((c ^ e : Circle) : ℂ) :=
      continuous_subtype_val.comp (continuous_id.zpow e)
    refine Integrable.of_bound hcont.aestronglyMeasurable 1
      (ae_of_all _ fun c => ?_)
    simp
  calc osForm (haarProb Circle) circleRep 0
          (halfLift planeObs) (halfLift planeObs)
      = ∫ U, reflObs (halfLift planeObs) U * halfLift planeObs U
          ∂(gibbsMeasure (torusShift 4) (haarProb Circle)
            circleRep 0) :=
        osForm_eq_integral (haarProb Circle) circleRep
          circleRep_continuous hd 0 _ _
    _ = ∫ U, planeChar (U planeLink)
          ∂(gibbsMeasure (torusShift 4) (haarProb Circle)
            circleRep 0) :=
        integral_congr_ae (ae_of_all _ planeObs_integrand)
    _ = ∫ U, planeChar (U planeLink)
          ∂(configMeasure (haarProb Circle)) := by
        rw [gibbsMeasure_zero]
    _ = ∫ c, planeChar c ∂(haarProb Circle) := by
        have hmap : (configMeasure (haarProb Circle)).map
            (fun U => U planeLink) = haarProb Circle :=
          configMeasure_map_planeLink
        have hf : AEStronglyMeasurable planeChar
            ((configMeasure (haarProb Circle)).map
              (fun U => U planeLink)) := by
          rw [hmap]
          exact planeChar_continuous.aestronglyMeasurable
        have hφ : AEMeasurable
            (fun U : Config (Fin 4 → ZMod 4) Circle => U planeLink)
            (configMeasure (haarProb Circle)) :=
          (measurable_pi_apply planeLink).aemeasurable
        have h := integral_map hφ hf
        rw [hmap] at h
        exact h.symm
    _ = (∫ c, ((c ^ (2 : ℤ) : Circle) : ℂ) ∂(haarProb Circle))
        + (∫ c, ((c ^ (-2 : ℤ) : Circle) : ℂ) ∂(haarProb Circle))
        - 2 := by
        have hconst : ∫ _ : Circle, (2 : ℂ) ∂(haarProb Circle) = 2 := by
          rw [integral_const]
          show (haarProb Circle Set.univ).toReal • (2 : ℂ) = 2
          rw [measure_univ, ENNReal.toReal_one, one_smul]
        have hadd : (∫ c, (((c ^ (2 : ℤ) : Circle) : ℂ)
              + ((c ^ (-2 : ℤ) : Circle) : ℂ)) ∂(haarProb Circle))
            = (∫ c, ((c ^ (2 : ℤ) : Circle) : ℂ) ∂(haarProb Circle))
              + (∫ c, ((c ^ (-2 : ℤ) : Circle) : ℂ)
                  ∂(haarProb Circle)) :=
          integral_add (hint 2) (hint (-2))
        have hsub2 : (∫ c, planeChar c ∂(haarProb Circle))
            = (∫ c, (((c ^ (2 : ℤ) : Circle) : ℂ)
                + ((c ^ (-2 : ℤ) : Circle) : ℂ))
                ∂(haarProb Circle))
              - (∫ _ : Circle, (2 : ℂ) ∂(haarProb Circle)) :=
          integral_sub ((hint 2).add (hint (-2)))
            (integrable_const (2 : ℂ))
        rw [hsub2, hadd, hconst]
    _ = -2 := by
        rw [integral_circle_zpow_haarProb 2,
          integral_circle_zpow_haarProb (-2)]
        norm_num

/-- **Kill K-S2-1(a), fired.** The `β = 0` OS diagonal of
an exhibited bounded measurable closed-half observable is
`−2`: its real part is not nonnegative. Positivity of the
OS form on `𝔸⁺` at `β = 0` is therefore **false** — the
closed-half algebra choice dies at this seat, exactly as
the kill was pre-registered (negative diagonal computed,
not suspected). -/
theorem planeObs_diag_not_nonneg :
    ¬ 0 ≤ (osForm (haarProb Circle) circleRep 0
        (halfLift planeObs) (halfLift planeObs)).re := by
  rw [osForm_planeObs_diag]
  norm_num

/-- The exhibited observable has *state zero* at `β = 0`:
under the gate's T1.1 identity its diagonal would have
been `|ω₀(f)|² = 0`. The computed value is `−2`. The
identity, and with it prediction P-0 on `𝔸⁺`, is refuted
twice over. -/
theorem planeObs_state_zero :
    gibbsExpect (torusShift 4) (haarProb Circle) circleRep 0
        (halfLift planeObs) = 0 := by
  have hd : (0 : ℕ) < 1 := zero_lt_one
  have hint : ∀ e : ℤ, Integrable
      (fun c : Circle => ((c ^ e : Circle) : ℂ)) (haarProb Circle) := by
    intro e
    have hcont : Continuous fun c : Circle => ((c ^ e : Circle) : ℂ) :=
      continuous_subtype_val.comp (continuous_id.zpow e)
    refine Integrable.of_bound hcont.aestronglyMeasurable 1
      (ae_of_all _ fun c => ?_)
    simp
  have hpt : ∀ U : Config (Fin 4 → ZMod 4) Circle,
      halfLift planeObs U
        = (((U planeLink ^ (1 : ℤ) : Circle) : ℂ)
          - ((U planeLink ^ (-1 : ℤ) : Circle) : ℂ)) := by
    intro U
    rw [halfLift_planeObs_apply, coe_zpow_circle, coe_zpow_circle,
      circle_coe_inv]
    simp
  calc gibbsExpect (torusShift 4) (haarProb Circle) circleRep 0
          (halfLift planeObs)
      = ∫ U, halfLift planeObs U
          ∂(gibbsMeasure (torusShift 4) (haarProb Circle)
            circleRep 0) :=
        gibbsExpect_eq_integral (torusShift 4) (haarProb Circle)
          circleRep circleRep_continuous hd 0 _
    _ = ∫ U, (((U planeLink ^ (1 : ℤ) : Circle) : ℂ)
          - ((U planeLink ^ (-1 : ℤ) : Circle) : ℂ))
          ∂(configMeasure (haarProb Circle)) := by
        rw [gibbsMeasure_zero]
        exact integral_congr_ae (ae_of_all _ hpt)
    _ = ∫ c, (((c ^ (1 : ℤ) : Circle) : ℂ)
          - ((c ^ (-1 : ℤ) : Circle) : ℂ)) ∂(haarProb Circle) := by
        have hmap : (configMeasure (haarProb Circle)).map
            (fun U => U planeLink) = haarProb Circle :=
          configMeasure_map_planeLink
        have hf : AEStronglyMeasurable
            (fun c : Circle => (((c ^ (1 : ℤ) : Circle) : ℂ)
              - ((c ^ (-1 : ℤ) : Circle) : ℂ)))
            ((configMeasure (haarProb Circle)).map
              (fun U => U planeLink)) := by
          rw [hmap]
          exact ((hint 1).sub (hint (-1))).aestronglyMeasurable
        have hφ : AEMeasurable
            (fun U : Config (Fin 4 → ZMod 4) Circle => U planeLink)
            (configMeasure (haarProb Circle)) :=
          (measurable_pi_apply planeLink).aemeasurable
        have h := integral_map hφ hf
        rw [hmap] at h
        exact h.symm
    _ = 0 := by
        rw [integral_sub (hint 1) (hint (-1)),
          integral_circle_zpow_haarProb 1,
          integral_circle_zpow_haarProb (-1)]
        norm_num

end Counterexample

/-! ## The reconstructed operators on a one-dimensional
quotient

On any of the `β = 0` seats below whose quotient is
`ℂ·Ω₀`, the reconstructed transfer operator and Hamiltonian
are operators on `ℂ` itself. They are defined here, once:
`T̂₀ = id` (the vacuum line is fixed and the quotient is the
vacuum line) and `Ĥ₀ = 0` (the `−log` of the identity). -/

section ReconOps

/-- The reconstructed transfer operator at `β = 0` on a
one-dimensional quotient: the identity. -/
noncomputable def transferHatZero : ℂ →L[ℂ] ℂ := 1

theorem transferHatZero_apply (z : ℂ) : transferHatZero z = z :=
  one_apply_eq_self z

theorem transferHatZero_vacuum : transferHatZero 1 = 1 :=
  one_apply_eq_self 1

/-- The reconstructed Hamiltonian at `β = 0`: the zero
operator (`−log` of the identity transfer operator). -/
noncomputable def hamZero : ℂ →L[ℂ] ℂ := 0

theorem hamZero_apply (z : ℂ) : hamZero z = 0 :=
  ContinuousLinearMap.zero_apply z

theorem hamZero_vacuum : hamZero 1 = 0 :=
  ContinuousLinearMap.zero_apply 1

/-- The semigroup relation at `β = 0`: `exp(−Ĥ₀) = T̂₀`. -/
theorem exp_neg_hamZero :
    NormedSpace.exp (-hamZero) = transferHatZero := by
  have h0 : (-hamZero) = (0 : ℂ →L[ℂ] ℂ) := by
    ext z
    simp [hamZero]
  rw [h0]
  exact NormedSpace.exp_zero

end ReconOps

/-! ## §2. Where the fence runs: the strict-half seat

The gate's T1.1 argument, carried out where it is sound:
on observables that do not see the plane coordinates —
functions of the strict-half restriction `restrictPos`.
There the reflected reading is the mirror of the negative
half, the two halves separate over the decoupled measure,
and the OS form is the product of two strict-half states. -/

section StrictSeat

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ))
  {N : ℕ} [NeZero N]

/-- The `β = 0` state on the strict half: expectation
under the strict half's own product Haar measure. On
plane-independent observables this is the gate's `ω₀`. -/
noncomputable def strictState (φ : (↥(posLinks (N := N)) → G) → ℂ) : ℂ :=
  ∫ z, φ z ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG)

theorem measurable_restrictPos :
    Measurable (restrictPos (N := N) :
      (↥(halfLinks (N := N)) → G) → (↥(posLinks (N := N)) → G)) := by
  refine measurable_pi_iff.mpr fun ℓ => ?_
  show Measurable fun y : ↥(halfLinks (N := N)) → G =>
    y ⟨ℓ.1, posLinks_subset_halfLinks ℓ.2⟩
  exact measurable_pi_apply _

/-- The strict-half reading of a reflected configuration
is the mirror of its negative half: the landed
`reflConfig_apply_pos`, repackaged as an identity of
restrictions. This is the step that fails on the closed
half (§1): at plane coordinates there is no mirror, only
the coordinate itself, inverted. -/
theorem restrictPos_halfRefl (hN : Even N)
    (U : Config (Fin 4 → ZMod N) G) :
    restrictPos (fun ℓ : ↥(halfLinks (N := N)) => (reflConfig U) ℓ.1)
      = mirrorP hN (fun ℓ : ↥(negLinks (N := N)) => U ℓ.1) := by
  funext ℓ
  exact reflConfig_apply_pos hN U ℓ

/-- Integrating the conjugate of a mirrored observable
over the negative half is conjugating its strict state:
the landed mirror marginal identity, plus the conjugate
integral. -/
theorem integral_conj_mirrorP (hN : Even N)
    (χ : (↥(posLinks (N := N)) → G) → ℂ) :
    ∫ u, (starRingEnd ℂ) (χ (mirrorP hN u))
        ∂(Measure.pi fun _ : ↥(negLinks (N := N)) => μG)
      = (starRingEnd ℂ) (strictState μG χ) := by
  calc ∫ u, (starRingEnd ℂ) (χ (mirrorP hN u))
        ∂(Measure.pi fun _ : ↥(negLinks (N := N)) => μG)
      = ∫ z, (starRingEnd ℂ) (χ z)
          ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG) :=
        integral_mirrorP μG hN (fun z => (starRingEnd ℂ) (χ z))
    _ = (starRingEnd ℂ)
          (∫ z, χ z ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG)) :=
        integral_conj
    _ = (starRingEnd ℂ) (strictState μG χ) := rfl

/-- **The pairing identity at `β = 0` on the strict seat.**
For plane-independent observables the OS form factors
through the strict state: the split factorization at
`Bdry ≡ 1` over the decoupled measure
(`integral_splitEquiv_factor_bdry`, with
`gibbsPartition_zero` and the two half trivializations),
the product integral, and the two landed marginal
identities. In particular the form is positive
semidefinite here, unconditionally. -/
theorem osForm_zero_strict_pair
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hN : Even N)
    (hd : 0 < d)
    (φ χ : (↥(posLinks (N := N)) → G) → ℂ)
    (hφ : Measurable φ) (hχ : Measurable χ) :
    osForm μG ρ 0 (halfLift (χ ∘ restrictPos)) (halfLift (φ ∘ restrictPos))
      = (starRingEnd ℂ) (strictState μG χ) * strictState μG φ := by
  have hΦsm : StronglyMeasurable
      (fun p : ((↥(halfLinks (N := N)) → G)
          × (↥(negLinks (N := N)) → G)) =>
        φ (restrictPos p.1)
          * (starRingEnd ℂ) (χ (mirrorP hN p.2))) := by
    have hm1 : Measurable
        (fun p : ((↥(halfLinks (N := N)) → G)
            × (↥(negLinks (N := N)) → G)) =>
          φ (restrictPos p.1)) :=
      hφ.comp (measurable_restrictPos.comp measurable_fst)
    have hm2 : Measurable
        (fun p : ((↥(halfLinks (N := N)) → G)
            × (↥(negLinks (N := N)) → G)) =>
          (starRingEnd ℂ) (χ (mirrorP hN p.2))) :=
      (RCLike.continuous_conj).measurable.comp
        (hχ.comp ((measurable_mirrorP_lf hN).comp measurable_snd))
    exact (hm1.mul hm2).stronglyMeasurable
  have hpt : ∀ U : Config (Fin 4 → ZMod N) G,
      (fun p : ((↥(halfLinks (N := N)) → G)
          × (↥(negLinks (N := N)) → G)) =>
        φ (restrictPos p.1)
          * (starRingEnd ℂ) (χ (mirrorP hN p.2)))
        ((splitEquiv (halfLinks (N := N))) U)
      = reflObs (halfLift (χ ∘ restrictPos)) U
        * halfLift (φ ∘ restrictPos) U := by
    intro U
    show φ (restrictPos ((splitEquiv (halfLinks (N := N))) U).1)
          * (starRingEnd ℂ)
            (χ (mirrorP hN ((splitEquiv (halfLinks (N := N))) U).2))
        = (starRingEnd ℂ)
            (χ (restrictPos (fun ℓ : ↥(halfLinks (N := N)) =>
              (reflConfig U) ℓ.1)))
          * φ (restrictPos (fun ℓ : ↥(halfLinks (N := N)) => U ℓ.1))
    rw [splitEquiv_fst, splitEquiv_snd, restrictPos_halfRefl hN U]
    exact mul_comm _ _
  calc osForm μG ρ 0 (halfLift (χ ∘ restrictPos)) (halfLift (φ ∘ restrictPos))
      = ∫ U, reflObs (halfLift (χ ∘ restrictPos)) U
          * halfLift (φ ∘ restrictPos) U
          ∂(gibbsMeasure (torusShift N) μG ρ 0) :=
        osForm_eq_integral μG ρ hρcont hd 0 _ _
    _ = ∫ U, (fun p : ((↥(halfLinks (N := N)) → G)
            × (↥(negLinks (N := N)) → G)) =>
          φ (restrictPos p.1)
            * (starRingEnd ℂ) (χ (mirrorP hN p.2)))
          ((splitEquiv (halfLinks (N := N))) U)
          ∂(gibbsMeasure (torusShift N) μG ρ 0) :=
        integral_congr_ae (ae_of_all _ fun U => (hpt U).symm)
    _ = ∫ p, (Bdry ρ 0 p)
          • (φ (restrictPos p.1)
            * (starRingEnd ℂ) (χ (mirrorP hN p.2)))
          ∂((ENNReal.ofReal (gibbsPartition (torusShift N) μG ρ 0))⁻¹
            • ((halfGibbsPlus μG ρ 0).prod (halfGibbsMinus μG ρ hN 0))) :=
        integral_splitEquiv_factor_bdry μG ρ hρcont hN 0 _ hΦsm
    _ = ∫ p, φ (restrictPos p.1)
          * (starRingEnd ℂ) (χ (mirrorP hN p.2))
          ∂((Measure.pi fun _ : ↥(halfLinks (N := N)) => μG).prod
            (Measure.pi fun _ : ↥(negLinks (N := N)) => μG)) := by
        have hmeas : (ENNReal.ofReal
              (gibbsPartition (torusShift N) μG ρ 0))⁻¹
              • ((halfGibbsPlus μG ρ 0).prod (halfGibbsMinus μG ρ hN 0))
            = (Measure.pi fun _ : ↥(halfLinks (N := N)) => μG).prod
              (Measure.pi fun _ : ↥(negLinks (N := N)) => μG) := by
          rw [gibbsPartition_zero, halfGibbsPlus_zero, halfGibbsMinus_zero]
          simp
        rw [hmeas]
        exact integral_congr_ae (ae_of_all _ fun p => by
          simp only [bdry_zero, one_smul])
    _ = (∫ y, φ (restrictPos y)
          ∂(Measure.pi fun _ : ↥(halfLinks (N := N)) => μG))
        * (∫ u, (starRingEnd ℂ) (χ (mirrorP hN u))
          ∂(Measure.pi fun _ : ↥(negLinks (N := N)) => μG)) :=
        integral_prod_mul (fun y => φ (restrictPos y))
          (fun u => (starRingEnd ℂ) (χ (mirrorP hN u)))
    _ = strictState μG φ * (starRingEnd ℂ) (strictState μG χ) := by
        congr 1
        · exact integral_restrictPos μG φ
        · exact integral_conj_mirrorP μG hN χ
    _ = (starRingEnd ℂ) (strictState μG χ) * strictState μG φ :=
        mul_comm _ _

/-- The diagonal on the strict seat: a squared norm —
positivity, in exact form. -/
theorem osForm_zero_strict_diag
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hN : Even N)
    (hd : 0 < d)
    (φ : (↥(posLinks (N := N)) → G) → ℂ) (hφ : Measurable φ) :
    osForm μG ρ 0 (halfLift (φ ∘ restrictPos)) (halfLift (φ ∘ restrictPos))
      = ((‖strictState μG φ‖ : ℂ) ^ 2) := by
  rw [osForm_zero_strict_pair μG ρ hρcont hN hd φ φ hφ hφ]
  exact RCLike.conj_mul (strictState μG φ)

/-- Positivity on the strict seat, as reality and
nonnegativity of the diagonal. -/
theorem osForm_zero_strict_diag_nonneg
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hN : Even N)
    (hd : 0 < d)
    (φ : (↥(posLinks (N := N)) → G) → ℂ) (hφ : Measurable φ) :
    (osForm μG ρ 0 (halfLift (φ ∘ restrictPos))
        (halfLift (φ ∘ restrictPos))).im = 0
      ∧ 0 ≤ (osForm μG ρ 0 (halfLift (φ ∘ restrictPos))
        (halfLift (φ ∘ restrictPos))).re := by
  rw [osForm_zero_strict_diag μG ρ hρcont hN hd φ hφ,
    ← Complex.ofReal_pow]
  constructor
  · rw [Complex.ofReal_im]
  · rw [Complex.ofReal_re]
    exact sq_nonneg _

/-- The null space on the strict seat is the strict
state's kernel — computed, as T1.2 asked, on the seat
where T1.2's conclusion survives. -/
theorem osForm_zero_strict_null
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hN : Even N)
    (hd : 0 < d)
    (φ : (↥(posLinks (N := N)) → G) → ℂ) (hφ : Measurable φ) :
    osForm μG ρ 0 (halfLift (φ ∘ restrictPos)) (halfLift (φ ∘ restrictPos))
        = 0
      ↔ strictState μG φ = 0 := by
  rw [osForm_zero_strict_diag μG ρ hρcont hN hd φ hφ,
    ← Complex.ofReal_pow]
  constructor
  · intro h
    have hre : ((‖strictState μG φ‖ ^ 2 : ℝ) : ℂ).re = 0 := by
      rw [h]
      simp
    rw [Complex.ofReal_re] at hre
    have hnorm : ‖strictState μG φ‖ = 0 :=
      sq_eq_zero_iff.mp hre
    exact norm_eq_zero.mp hnorm
  · intro h
    rw [h]
    simp

/-- The strict coordinate of a constant is the constant:
the vacuum class `[1]` has coordinate `1`. -/
theorem strictState_const (c : ℂ) :
    strictState μG (fun _ : ↥(posLinks (N := N)) → G => c) = c := by
  show (∫ _z, c ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG)) = c
  rw [integral_const]
  show ((Measure.pi fun _ : ↥(posLinks (N := N)) => μG)
    Set.univ).toReal • c = c
  rw [measure_univ, ENNReal.toReal_one, one_smul]

/-- The strict coordinate is surjective: every complex
number is the coordinate of a (constant) observable. With
the pairing identity and the null-space computation, the
strict quotient is `ℂ·Ω₀`. -/
theorem strictState_surjective :
    Function.Surjective (strictState μG (N := N)) := by
  intro c
  exact ⟨fun _ => c, strictState_const μG c⟩

/-- On strict classes the identity operator carries the
OS pairing: at `β = 0` the one-step pairing factors
through the same state as the OS form itself (the
degeneracy of the seat), so the operator characterized
by it on the one-dimensional quotient is `T̂₀ = id`. -/
theorem strict_transferHat_pairing
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hN : Even N)
    (hd : 0 < d)
    (φ χ : (↥(posLinks (N := N)) → G) → ℂ)
    (hφ : Measurable φ) (hχ : Measurable χ) :
    inner ℂ (strictState μG χ) (transferHatZero (strictState μG φ))
      = osForm μG ρ 0 (halfLift (χ ∘ restrictPos))
          (halfLift (φ ∘ restrictPos)) := by
  rw [transferHatZero_apply,
    osForm_zero_strict_pair μG ρ hρcont hN hd φ χ hφ hχ,
    RCLike.inner_apply]
  exact mul_comm _ _

end StrictSeat

/-! ## §3. The fallback seat: full reconstruction on
`𝔸_slice`

The charter's licensed fallback after K-S2-1(a): the
slice-generated algebra, where S1's companion already
fixes the diagonal. Here the gate's prediction P-0 is
confirmed verbatim: the quotient is `ℂ·Ω₀`, the
reconstructed transfer operator is the identity, the
Hamiltonian is zero. -/

section SliceRecon

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ))
  {N : ℕ} [NeZero N]

/-- A slice observable: a function on the time-`0` slice
read on configurations through the landed slice
restriction. The elements of `𝔸_slice`. -/
def sliceObs (φ : (↥(sliceLinks (N := N)) → G) → ℂ) :
    Config (Fin 4 → ZMod N) G → ℂ :=
  fun U => φ (restrictConfig sliceLinks U)

theorem sliceObs_apply (φ : (↥(sliceLinks (N := N)) → G) → ℂ)
    (U : Config (Fin 4 → ZMod N) G) :
    sliceObs φ U = φ (restrictConfig sliceLinks U) := rfl

/-- The `β = 0` coordinate of a slice observable: its
expectation under the decoupled slice marginal, the
product Haar measure on the slice links (identified by
`sliceMeasure_zero`). -/
noncomputable def sliceCoord (φ : (↥(sliceLinks (N := N)) → G) → ℂ) : ℂ :=
  ∫ z, φ z ∂(Measure.pi fun _ : ↥(sliceLinks (N := N)) => μG)

/-- Bounded measurable slice observables are in `MemLp`
at `β = 0` (the slice measure is a probability measure). -/
theorem memLp_slice_zero_of_bounded
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hd : 0 < d)
    {φ : (↥(sliceLinks (N := N)) → G) → ℂ}
    (hφ : Measurable φ) {B : ℝ} (hB : ∀ z, ‖φ z‖ ≤ B) :
    MemLp φ 2 (sliceMeasure (N := N) μG ρ 0) := by
  haveI := isProbabilityMeasure_sliceMeasure (N := N) μG ρ hρcont hd 0
  exact MemLp.of_bound hφ.aestronglyMeasurable B (ae_of_all _ hB)

/-- The coordinate is the vacuum pairing of the prepared
slice state: `coord φ = ⟪Ω, ψ_φ⟫` at `β = 0`. -/
theorem inner_osVacuum_sliceState_zero
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hd : 0 < d)
    (φ : (↥(sliceLinks (N := N)) → G) → ℂ)
    (hφ : MemLp φ 2 (sliceMeasure (N := N) μG ρ 0)) :
    inner ℂ (osVacuum (N := N) μG ρ hρcont hd 0)
        (sliceState μG ρ 0 φ hφ) = sliceCoord μG φ := by
  rw [inner_osVacuum_left μG ρ hρcont hd 0]
  rw [show sliceCoord μG φ = ∫ z, φ z
      ∂(sliceMeasure (N := N) μG ρ 0) by
    show (∫ z, φ z ∂(Measure.pi fun _ : ↥(sliceLinks (N := N)) => μG))
      = ∫ z, φ z ∂(sliceMeasure (N := N) μG ρ 0)
    rw [sliceMeasure_zero]]
  exact integral_congr_ae hφ.coeFn_toLp

/-- **The pairing identity at `β = 0` on `𝔸_slice`** —
the quotient's inner product, computed. S1's polarized
depth-one identity at `β = 0`, where the landed transfer
operator is the vacuum projection `T₀ = ⟪Ω, ·⟫ • Ω`:
the pairing of two slice observables is the product of
the conjugate coordinate and the coordinate. -/
theorem osForm_zero_slice_pair
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hN : Even N)
    (hN2 : 2 ≤ N) (hd : 0 < d)
    (φ χ : (↥(sliceLinks (N := N)) → G) → ℂ)
    (hφ : MemLp φ 2 (sliceMeasure (N := N) μG ρ 0))
    (hχ : MemLp χ 2 (sliceMeasure (N := N) μG ρ 0)) :
    osForm μG ρ 0 (sliceObs φ) (sliceObs χ)
      = (starRingEnd ℂ) (sliceCoord μG φ) * sliceCoord μG χ := by
  calc osForm μG ρ 0 (sliceObs φ) (sliceObs χ)
      = inner ℂ (sliceState μG ρ 0 φ hφ)
          (transferOp μG ρ hN2 hρcont 0 (sliceState μG ρ 0 χ hχ)) :=
        osForm_depthOne_transfer_pair μG ρ hρcont hN hN2 hd 0 φ χ hφ hχ
    _ = inner ℂ (sliceState μG ρ 0 φ hφ)
          ((inner ℂ (osVacuum (N := N) μG ρ hρcont hd 0)
              (sliceState μG ρ 0 χ hχ))
            • osVacuum (N := N) μG ρ hρcont hd 0) := by
        rw [transferOp_zero_apply μG ρ hN2 hρcont hd]
    _ = (inner ℂ (osVacuum (N := N) μG ρ hρcont hd 0)
          (sliceState μG ρ 0 χ hχ))
        * inner ℂ (sliceState μG ρ 0 φ hφ)
          (osVacuum (N := N) μG ρ hρcont hd 0) :=
        inner_smul_right _ _ _
    _ = (starRingEnd ℂ) (sliceCoord μG φ) * sliceCoord μG χ := by
        have h1 : inner ℂ (sliceState μG ρ 0 φ hφ)
            (osVacuum (N := N) μG ρ hρcont hd 0)
            = (starRingEnd ℂ) (inner ℂ
                (osVacuum (N := N) μG ρ hρcont hd 0)
                (sliceState μG ρ 0 φ hφ)) :=
          (inner_conj_symm _ _).symm
        rw [inner_osVacuum_sliceState_zero μG ρ hρcont hd χ hχ, h1,
          inner_osVacuum_sliceState_zero μG ρ hρcont hd φ hφ, mul_comm]

/-- The diagonal on `𝔸_slice`: a squared norm. This is
the exact value behind the landed
`osForm_depthOne_zero` (reality and nonnegativity). -/
theorem osForm_zero_slice_diag
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hN : Even N)
    (hN2 : 2 ≤ N) (hd : 0 < d)
    (φ : (↥(sliceLinks (N := N)) → G) → ℂ)
    (hφ : MemLp φ 2 (sliceMeasure (N := N) μG ρ 0)) :
    osForm μG ρ 0 (sliceObs φ) (sliceObs φ)
      = ((‖sliceCoord μG φ‖ : ℂ) ^ 2) := by
  rw [osForm_zero_slice_pair μG ρ hρcont hN hN2 hd φ φ hφ hφ]
  exact RCLike.conj_mul (sliceCoord μG φ)

/-- The null space on `𝔸_slice` is the coordinate's
kernel — T1.2, on the fallback seat. -/
theorem osForm_zero_slice_null
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hN : Even N)
    (hN2 : 2 ≤ N) (hd : 0 < d)
    (φ : (↥(sliceLinks (N := N)) → G) → ℂ)
    (hφ : MemLp φ 2 (sliceMeasure (N := N) μG ρ 0)) :
    osForm μG ρ 0 (sliceObs φ) (sliceObs φ) = 0
      ↔ sliceCoord μG φ = 0 := by
  rw [osForm_zero_slice_diag μG ρ hρcont hN hN2 hd φ hφ,
    ← Complex.ofReal_pow]
  constructor
  · intro h
    have hre : ((‖sliceCoord μG φ‖ ^ 2 : ℝ) : ℂ).re = 0 := by
      rw [h]
      simp
    rw [Complex.ofReal_re] at hre
    have hnorm : ‖sliceCoord μG φ‖ = 0 :=
      sq_eq_zero_iff.mp hre
    exact norm_eq_zero.mp hnorm
  · intro h
    rw [h]
    simp

/-- The coordinate of a constant observable is the
constant. -/
theorem sliceCoord_const (c : ℂ) :
    sliceCoord μG (fun _ : ↥(sliceLinks (N := N)) → G => c) = c := by
  show (∫ _z, c ∂(Measure.pi fun _ : ↥(sliceLinks (N := N)) => μG)) = c
  rw [integral_const]
  show ((Measure.pi fun _ : ↥(sliceLinks (N := N)) => μG)
    Set.univ).toReal • c = c
  rw [measure_univ, ENNReal.toReal_one, one_smul]

/-- The vacuum's coordinate: `[1]` maps to `1`. -/
theorem sliceCoord_one :
    sliceCoord μG (1 : (↥(sliceLinks (N := N)) → G) → ℂ) = 1 :=
  sliceCoord_const μG (1 : ℂ)

/-- The coordinate is surjective: the quotient of
`𝔸_slice` by its null space is `ℂ·Ω₀`, one-dimensional,
with `Ω₀ = [1]`. -/
theorem sliceCoord_surjective :
    Function.Surjective (sliceCoord μG (N := N)) := by
  intro c
  exact ⟨fun _ => c, sliceCoord_const μG c⟩

/-- **Descent of the landed `T₀`.** The reconstructed
operator `T̂₀ = id` on the quotient has, on slice classes,
exactly the pairing of the landed transfer operator on
slice states: `T₀ = ⟪Ω, ·⟫ • Ω` descends to the identity
of the one-dimensional quotient. This is T1.4 on the
fallback seat — the operator half of P-0. -/
theorem transferHatZero_pairing
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hN : Even N)
    (hN2 : 2 ≤ N) (hd : 0 < d)
    (φ χ : (↥(sliceLinks (N := N)) → G) → ℂ)
    (hφ : MemLp φ 2 (sliceMeasure (N := N) μG ρ 0))
    (hχ : MemLp χ 2 (sliceMeasure (N := N) μG ρ 0)) :
    inner ℂ (sliceCoord μG φ) (transferHatZero (sliceCoord μG χ))
      = osForm μG ρ 0 (sliceObs φ) (sliceObs χ) := by
  rw [transferHatZero_apply,
    osForm_zero_slice_pair μG ρ hρcont hN hN2 hd φ χ hφ hχ,
    RCLike.inner_apply]
  exact mul_comm _ _

/-- **S2-1 on the fallback seat: prediction P-0,
confirmed verbatim.** At `β = 0`, on `𝔸_slice`, at
general `(G, ρ)`: the pairing identity (the quotient is
carried by the coordinate), the null space is the
coordinate's kernel, the vacuum class has coordinate
`1`, the reconstructed transfer operator is the identity
(`T̂₀ = id`, T1.4), and the Hamiltonian vanishes
(`Ĥ₀ = 0`, T1.5) — with `exp(−Ĥ₀) = T̂₀` above. -/
theorem recon_zero_slice_package
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hN : Even N)
    (hN2 : 2 ≤ N) (hd : 0 < d)
    (φ χ : (↥(sliceLinks (N := N)) → G) → ℂ)
    (hφ : MemLp φ 2 (sliceMeasure (N := N) μG ρ 0))
    (hχ : MemLp χ 2 (sliceMeasure (N := N) μG ρ 0)) :
    (osForm μG ρ 0 (sliceObs φ) (sliceObs χ)
        = (starRingEnd ℂ) (sliceCoord μG φ) * sliceCoord μG χ)
      ∧ (osForm μG ρ 0 (sliceObs φ) (sliceObs φ) = 0
          ↔ sliceCoord μG φ = 0)
      ∧ sliceCoord μG (1 : (↥(sliceLinks (N := N)) → G) → ℂ) = 1
      ∧ transferHatZero (sliceCoord μG χ) = sliceCoord μG χ
      ∧ hamZero (sliceCoord μG χ) = 0 := by
  refine ⟨osForm_zero_slice_pair μG ρ hρcont hN hN2 hd φ χ hφ hχ, ?_,
    ?_, ?_, ?_⟩
  · exact osForm_zero_slice_null μG ρ hρcont hN hN2 hd φ hφ
  · exact sliceCoord_one μG
  · exact transferHatZero_apply _
  · exact hamZero_apply _

end SliceRecon

end ThetLogos
