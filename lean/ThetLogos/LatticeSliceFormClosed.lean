/-
# FG-2a — CLOSEDNESS of the landed Hamiltonian form

Brick FG-2a of the frontier gate paper
(`whitepaper/frontier-gate-scoping-2026-10-25.md`, §2.2): the
first brick of the FG-2 hand-built unbounded-operator project.
PLACEMENT LABEL (consumed from the gate, not re-decided here):
this is a **Stage 2 completeness** item — it finishes the
representation-theoretic content of the S2-4(b) form on the
completion. It is NOT frontier progress: Items 3 (uniform
estimates) and 4 (continuum) are untouched, and nothing here
moves any dial. Dials 0/4. NO CLAIM.

## What this brick consumes

* `sliceCompletedForm_package` (LatticeSliceOperator): the
  completed form `sliceHamFormC` on `sliceHilbertSpace`, its
  approximants `q_K = sliceHamFormApproxC`, the domain
  submodule `sliceHamFormDomainC` (carrier = finiteness locus
  of the `ℝ≥0∞`-valued form), term positivity and the
  symmetry of the defect iterates.
* The S2-5 weld's interface clause (LatticeSliceWeld):
  `sliceEnergyForm_one_eq_weldNorm`, i.e. at the quotient
  level `Q₁ = ‖x‖² − ‖W x‖²`, consumed through the completed
  tying identity `sliceEnergyFormC_one_eq` (`Q₁ = q₁`).

## What it delivers

* The polarized form: approximant pairings
  `sliceApproxB K x y = ∑ j∈Icc 1 K, (j:ℝ)⁻¹ · ⟪x, A^j y⟫`
  on the completed space, Cauchy–Schwarz per term and for
  the sums, and the limit pairing `sliceFormB` on the form
  domain (§2, §3).
* The form domain as a **Hilbert space in the form norm**
  `‖x‖²_form = ‖x‖² + form(x)`: the synonym type
  `sliceFormDomain` of `sliceHamFormDomainC` carries the
  form inner product `⟪x, y⟫ + B(x, y)` and is COMPLETE
  (§4, §5). This is exactly `sliceHamFormC` being a CLOSED
  form in the representation theorem's sense: the form
  value of a form-Cauchy sequence's limit is the limit of
  the form values, proved by lower semicontinuity of the
  monotone supremum of the continuous approximants — the
  limit's membership and form bound are *derived* from
  uniform-in-`K` bounds, never assumed.
* The inclusion `sliceFormDomain → sliceHilbertSpace` as a
  continuous linear map with bound `1` (§4).

## What is named, NOT asserted

* **Dense range of the inclusion is NOT proved in general,
  and cannot be from the landed record alone.** §6 proves
  the obstruction: the form domain is always contained in
  `(ker T̂_c)^⊥` — for `w` with `T̂_c w = 0` every
  approximant pairing is `H_K · ⟪x, w⟫` with `H_K` the
  harmonic sum, while Cauchy–Schwarz bounds it by
  `√form(x) · √(H_K · ‖w‖²)`; squaring and cancelling
  `H_K` gives `H_K · |⟪x, w⟫|² ≤ form(x) · ‖w‖²`, and
  `H_K` is unbounded. Hence if
  `ker T̂_c ≠ 0` the inclusion is **not** dense-range.
  Density is asserted only at `β = 0`, where the form is
  identically zero, the domain is the whole space, and the
  inclusion is surjective. Density inside `(ker T̂_c)^⊥`
  at general `β` would need a form-bounded truncation /
  functional calculus for `T̂_c` (the step needs `T̂² ≤ T̂`
  in form order — the spectrum of `T̂_c` in `[0,1]` as a
  form inequality), which is not in the landed record;
  that is the named residue of this brick, exit PARTIAL
  on the density clause only. Completeness and continuity
  land in full.

Fences: no Friedrichs construction (that is FG-2b,
uncommissioned); no `osForm` positivity beyond landed
labels; TM R2 untouched; Stage 1b-B untouched.
NO CLAIM; Clay parts closed: 0.
-/

import ThetLogos.LatticeSliceOperator
import ThetLogos.LatticeSliceWeld

namespace ThetLogos

open MeasureTheory Finset
open scoped Matrix ENNReal NNReal InnerProduct

section SliceFormClosed

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ))
  {N : ℕ} [NeZero N]

/-! ## §1. The real-valued form -/

/-- **The real value of the completed Hamiltonian form**:
`sliceFormVal x = (sliceHamFormC x).toReal` — finite exactly
on the form domain `sliceHamFormDomainC`. -/
noncomputable def sliceFormVal (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (x : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos) : ℝ :=
  (sliceHamFormC μG ρ hN2 hρcont hN β hpos x).toReal

theorem sliceFormVal_nonneg (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (x : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos) :
    0 ≤ sliceFormVal μG ρ hN2 hρcont hN β hpos x :=
  ENNReal.toReal_nonneg

theorem sliceFormVal_zero (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) :
    sliceFormVal μG ρ hN2 hρcont hN β hpos 0 = 0 := by
  unfold sliceFormVal sliceHamFormC
  simp [sliceHamFormApproxC_zero]

/-- Uniform approximant bounds pass to the form value: if
every `q_K x ≤ C` then `sliceFormVal x ≤ C`. -/
theorem sliceFormVal_le_of_forall_approxC_le (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (x : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos)
    {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ K, sliceHamFormApproxC μG ρ hN2 hρcont hN β
      hpos K x ≤ C) :
    sliceFormVal μG ρ hN2 hρcont hN β hpos x ≤ C := by
  have hle : sliceHamFormC μG ρ hN2 hρcont hN β hpos x
      ≤ ENNReal.ofReal C :=
    iSup_le fun K => ENNReal.ofReal_le_ofReal (h K)
  have h2 := (ENNReal.toReal_le_toReal
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle)
    ENNReal.ofReal_ne_top).mpr hle
  rwa [ENNReal.toReal_ofReal hC] at h2

/-- Uniform approximant bounds put a vector in the form
domain (the domain's carrier is the boundedness locus of
the approximants). -/
theorem sliceHam_mem_domainC_of_forall_approxC_le
    (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (x : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos)
    {C : ℝ}
    (h : ∀ K, sliceHamFormApproxC μG ρ hN2 hρcont hN β
      hpos K x ≤ C) :
    x ∈ sliceHamFormDomainC μG ρ hN2 hρcont hN β hpos := by
  rw [sliceHamC_mem_domain_iff, sliceHamFormC_ne_top_iff]
  exact ⟨C, fun z hz => by
    obtain ⟨K, rfl⟩ := hz
    exact h K⟩

/-- On the domain, every approximant sits under the form
value. -/
theorem sliceApproxC_le_formVal (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (x : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos)
    (hx : x ∈ sliceHamFormDomainC μG ρ hN2 hρcont hN β
      hpos) (K : ℕ) :
    sliceHamFormApproxC μG ρ hN2 hρcont hN β hpos K x
      ≤ sliceFormVal μG ρ hN2 hρcont hN β hpos x := by
  have hne : sliceHamFormC μG ρ hN2 hρcont hN β hpos x
      ≠ ⊤ :=
    (sliceHamC_mem_domain_iff μG ρ hN2 hρcont hN β hpos
      x).mp hx
  have h2 := (ENNReal.toReal_le_toReal
    ENNReal.ofReal_ne_top hne).mpr
    (sliceHamFormApproxC_le μG ρ hN2 hρcont hN β hpos K x)
  rwa [ENNReal.toReal_ofReal
    (sliceHamFormApproxC_nonneg μG ρ hN2 hρcont hN β hpos
      K x)] at h2

/-- **Monotone convergence of the approximants to the form
value**, on the domain: `q_K x ↑ sliceFormVal x`. -/
theorem sliceFormVal_tendsto_approxC (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (x : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos)
    (hx : x ∈ sliceHamFormDomainC μG ρ hN2 hρcont hN β
      hpos) :
    Filter.Tendsto
      (fun K => sliceHamFormApproxC μG ρ hN2 hρcont hN β
        hpos K x)
      Filter.atTop
      (nhds (sliceFormVal μG ρ hN2 hρcont hN β hpos x)) := by
  have hne : sliceHamFormC μG ρ hN2 hρcont hN β hpos x
      ≠ ⊤ :=
    (sliceHamC_mem_domain_iff μG ρ hN2 hρcont hN β hpos
      x).mp hx
  have hmono : Monotone (fun K => ENNReal.ofReal
      (sliceHamFormApproxC μG ρ hN2 hρcont hN β hpos K
        x)) :=
    fun a b hab => ENNReal.ofReal_le_ofReal
      ((sliceHamFormApproxC_mono μG ρ hN2 hρcont hN β hpos
        x) hab)
  have h1 : Filter.Tendsto
      (fun K => ENNReal.ofReal (sliceHamFormApproxC μG ρ
        hN2 hρcont hN β hpos K x))
      Filter.atTop
      (nhds (sliceHamFormC μG ρ hN2 hρcont hN β hpos
        x)) := by
    show Filter.Tendsto
      (fun K => ENNReal.ofReal (sliceHamFormApproxC μG ρ
        hN2 hρcont hN β hpos K x))
      Filter.atTop
      (nhds (⨆ K : ℕ, ENNReal.ofReal (sliceHamFormApproxC
        μG ρ hN2 hρcont hN β hpos K x)))
    exact tendsto_atTop_iSup hmono
  have h2 := (ENNReal.tendsto_toReal hne).comp h1
  exact Filter.Tendsto.congr
    (fun K => ENNReal.toReal_ofReal
      (sliceHamFormApproxC_nonneg μG ρ hN2 hρcont hN β hpos
        K x)) h2

/-- The form value is invariant under negation. -/
theorem sliceFormVal_neg (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (x : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos) :
    sliceFormVal μG ρ hN2 hρcont hN β hpos (-x)
      = sliceFormVal μG ρ hN2 hρcont hN β hpos x := by
  have hK : ∀ K, sliceHamFormApproxC μG ρ hN2 hρcont hN β
        hpos K (-x)
      = sliceHamFormApproxC μG ρ hN2 hρcont hN β hpos K
          x := by
    intro K
    simpa using sliceHamFormApproxC_smul μG ρ hN2 hρcont
      hN β hpos K (-1) x
  unfold sliceFormVal sliceHamFormC
  congr 1
  exact iSup_congr fun K => by rw [hK K]

/-! ## §2. Pairings of the defect iterates -/

/-- Pairings are additive in the second argument. -/
theorem slicePair_add_right (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (j : ℕ)
    (x y z : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos) :
    inner ℂ x ((⇑(sliceHamCompletedDefect μG ρ hN2 hρcont
        hN β hpos))^[j] (y + z))
      = inner ℂ x ((⇑(sliceHamCompletedDefect μG ρ hN2
          hρcont hN β hpos))^[j] y)
        + inner ℂ x ((⇑(sliceHamCompletedDefect μG ρ hN2
            hρcont hN β hpos))^[j] z) := by
  rw [sliceHamCompletedDefect_iter_add, inner_add_right]

/-- Pairings are homogeneous in the second argument. -/
theorem slicePair_smul_right (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (j : ℕ)
    (c : ℂ)
    (x y : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos) :
    inner ℂ x ((⇑(sliceHamCompletedDefect μG ρ hN2 hρcont
        hN β hpos))^[j] (c • y))
      = c * inner ℂ x ((⇑(sliceHamCompletedDefect μG ρ
          hN2 hρcont hN β hpos))^[j] y) := by
  rw [sliceHamCompletedDefect_iter_smul, inner_smul_right]

/-- Pairings are additive in the first argument. -/
theorem slicePair_add_left (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (j : ℕ)
    (x y z : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos) :
    inner ℂ (x + y) ((⇑(sliceHamCompletedDefect μG ρ hN2
        hρcont hN β hpos))^[j] z)
      = inner ℂ x ((⇑(sliceHamCompletedDefect μG ρ hN2
          hρcont hN β hpos))^[j] z)
        + inner ℂ y ((⇑(sliceHamCompletedDefect μG ρ hN2
            hρcont hN β hpos))^[j] z) := by
  rw [inner_add_left]

/-- Pairings are conjugate-homogeneous in the first
    argument. -/
theorem slicePair_smul_left (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (j : ℕ)
    (c : ℂ)
    (x y : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos) :
    inner ℂ (c • x) ((⇑(sliceHamCompletedDefect μG ρ hN2
        hρcont hN β hpos))^[j] y)
      = (starRingEnd ℂ) c * inner ℂ x
          ((⇑(sliceHamCompletedDefect μG ρ hN2 hρcont hN
            β hpos))^[j] y) := by
  rw [inner_smul_left]

/-- Pairings are Hermitian: conjugate-symmetry through the
    defect symmetry. -/
theorem slicePair_conj_symm (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (j : ℕ)
    (x y : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos) :
    (starRingEnd ℂ) (inner ℂ x
        ((⇑(sliceHamCompletedDefect μG ρ hN2 hρcont hN β
          hpos))^[j] y))
      = inner ℂ y ((⇑(sliceHamCompletedDefect μG ρ hN2
          hρcont hN β hpos))^[j] x) := by
  rw [inner_conj_symm]
  exact (sliceHamCompletedDefect_iter_inner μG ρ hN2
    hρcont hN β hpos j y x).symm

/-- Diagonal pairings are real: the pairing equals the
    cast of its real part. -/
theorem slicePair_diag_ofReal (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (j : ℕ)
    (x : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos) :
    inner ℂ x ((⇑(sliceHamCompletedDefect μG ρ hN2 hρcont
        hN β hpos))^[j] x)
      = ((inner ℂ x ((⇑(sliceHamCompletedDefect μG ρ hN2
          hρcont hN β hpos))^[j] x)).re : ℂ) := by
  apply Complex.ext
  · rw [Complex.ofReal_re]
  · rw [Complex.ofReal_im]
    exact (sliceHamCompletedDefect_iter_diag μG ρ hN2
      hρcont hN β hpos j x).1

/-- Diagonal pairings have nonnegative real part (term
    positivity, restated for the pair notation). -/
theorem slicePair_diag_nonneg (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (j : ℕ)
    (x : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos) :
    0 ≤ (inner ℂ x ((⇑(sliceHamCompletedDefect μG ρ hN2
        hρcont hN β hpos))^[j] x)).re :=
  (sliceHamCompletedDefect_iter_diag μG ρ hN2 hρcont hN β
    hpos j x).2

/-- Conjugation fixes real casts: the `RCLike` conjugation
    is `starRingEnd` application, and it fixes the real
    axis. -/
theorem sliceStar_ofReal (t : ℝ) :
    (starRingEnd ℂ) ((t : ℂ)) = (t : ℂ) :=
  RCLike.conj_ofReal t

/-- **Cauchy–Schwarz for one defect pairing.** Each
`b_j(x, y) = ⟪x, A^j y⟫` is a positive semidefinite
Hermitian sesquilinear form (symmetry: defect symmetry;
positivity: term positivity), hence satisfies CS. The
proof is the discriminant argument: rotate `y` by a unit
scalar so the pairing is a nonnegative real, then the
real quadratic `t ↦ b_j(x + t•y', x + t•y')` is everywhere
nonnegative. -/
theorem slicePair_cs (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (j : ℕ)
    (x y : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos) :
    ‖inner ℂ x ((⇑(sliceHamCompletedDefect μG ρ hN2
        hρcont hN β hpos))^[j] y)‖ ^ 2
      ≤ (inner ℂ x ((⇑(sliceHamCompletedDefect μG ρ hN2
          hρcont hN β hpos))^[j] x)).re
        * (inner ℂ y ((⇑(sliceHamCompletedDefect μG ρ hN2
            hρcont hN β hpos))^[j] y)).re := by
  have hXnn : 0 ≤ (inner ℂ x ((⇑(sliceHamCompletedDefect
      μG ρ hN2 hρcont hN β hpos))^[j] x)).re :=
    slicePair_diag_nonneg μG ρ hN2 hρcont hN β hpos j x
  have hYnn : 0 ≤ (inner ℂ y ((⇑(sliceHamCompletedDefect
      μG ρ hN2 hρcont hN β hpos))^[j] y)).re :=
    slicePair_diag_nonneg μG ρ hN2 hρcont hN β hpos j y
  set X : ℝ := (inner ℂ x ((⇑(sliceHamCompletedDefect μG
    ρ hN2 hρcont hN β hpos))^[j] x)).re with hX_def
  set Y : ℝ := (inner ℂ y ((⇑(sliceHamCompletedDefect μG
    ρ hN2 hρcont hN β hpos))^[j] y)).re with hY_def
  set b : ℂ := inner ℂ x ((⇑(sliceHamCompletedDefect μG ρ
    hN2 hρcont hN β hpos))^[j] y) with hb_def
  by_cases hb0 : b = 0
  · have h0 : ‖b‖ ^ 2 = 0 := by rw [hb0]; simp
    rw [h0]
    exact mul_nonneg hXnn hYnn
  · set r : ℝ := ‖b‖ with hr_def
    have hr : 0 < r := by
      rw [hr_def]
      exact norm_pos_iff.mpr hb0
    have hrne : r ≠ 0 := hr.ne'
    set u : ℂ := (r : ℂ) / b with hu_def
    have hu_norm : ‖u‖ = 1 := by
      have hn : ‖((r : ℂ))‖ = |r| := RCLike.norm_ofReal r
      have hn2 : ‖((r : ℂ))‖ = r := by
        rwa [abs_of_nonneg hr.le] at hn
      rw [hu_def, norm_div, hn2, ← hr_def]
      exact div_self hrne
    have hcu : (starRingEnd ℂ) u * u = 1 := by
      have hh := RCLike.conj_mul (K := ℂ) u
      rw [hu_norm] at hh
      simpa using hh
    set y' : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos
      := u • y with hy'_def
    have hb' : inner ℂ x ((⇑(sliceHamCompletedDefect μG ρ
          hN2 hρcont hN β hpos))^[j] y') = (r : ℂ) := by
      have h1 : inner ℂ x ((⇑(sliceHamCompletedDefect μG
            ρ hN2 hρcont hN β hpos))^[j] y')
          = u * inner ℂ x ((⇑(sliceHamCompletedDefect μG
              ρ hN2 hρcont hN β hpos))^[j] y) := by
        rw [hy'_def]
        exact slicePair_smul_right μG ρ hN2 hρcont hN β
          hpos j u x y
      rw [h1, ← hb_def, hu_def]
      exact div_mul_cancel₀ _ hb0
    have hy'diag : inner ℂ y' ((⇑(sliceHamCompletedDefect
          μG ρ hN2 hρcont hN β hpos))^[j] y')
        = inner ℂ y ((⇑(sliceHamCompletedDefect μG ρ hN2
            hρcont hN β hpos))^[j] y) := by
      have h1 : inner ℂ y' ((⇑(sliceHamCompletedDefect μG
              ρ hN2 hρcont hN β hpos))^[j] y')
          = (starRingEnd ℂ) u * (u * inner ℂ y
              ((⇑(sliceHamCompletedDefect μG ρ hN2 hρcont
                hN β hpos))^[j] y)) := by
        rw [hy'_def, sliceHamCompletedDefect_iter_smul,
          inner_smul_left, inner_smul_right]
      rw [h1, ← mul_assoc, hcu, one_mul]
    have hcross : inner ℂ y' ((⇑(sliceHamCompletedDefect
          μG ρ hN2 hρcont hN β hpos))^[j] x) = (r : ℂ) := by
      have h := slicePair_conj_symm μG ρ hN2 hρcont hN β
        hpos j x y'
      rw [hb', sliceStar_ofReal] at h
      exact h.symm
    have key : ∀ t : ℝ, 0 ≤ X + 2 * t * r + t ^ 2 * Y := by
      intro t
      have hdiag := (sliceHamCompletedDefect_iter_diag
        μG ρ hN2 hρcont hN β hpos j
        (x + (t : ℂ) • y')).2
      have hexp : inner ℂ (x + (t : ℂ) • y')
          ((⇑(sliceHamCompletedDefect μG ρ hN2 hρcont hN
            β hpos))^[j] (x + (t : ℂ) • y'))
          = ((X + 2 * t * r + t ^ 2 * Y : ℝ) : ℂ) := by
        have e1 : (⇑(sliceHamCompletedDefect μG ρ hN2
              hρcont hN β hpos))^[j] (x + (t : ℂ) • y')
            = (⇑(sliceHamCompletedDefect μG ρ hN2 hρcont
                hN β hpos))^[j] x
              + (t : ℂ) • (⇑(sliceHamCompletedDefect μG ρ
                  hN2 hρcont hN β hpos))^[j] y' := by
          rw [sliceHamCompletedDefect_iter_add,
            sliceHamCompletedDefect_iter_smul]
        have step1 : inner ℂ (x + (t : ℂ) • y')
            ((⇑(sliceHamCompletedDefect μG ρ hN2 hρcont
              hN β hpos))^[j] (x + (t : ℂ) • y'))
            = inner ℂ (x + (t : ℂ) • y')
                ((⇑(sliceHamCompletedDefect μG ρ hN2
                  hρcont hN β hpos))^[j] x)
              + (t : ℂ) * inner ℂ (x + (t : ℂ) • y')
                  ((⇑(sliceHamCompletedDefect μG ρ hN2
                    hρcont hN β hpos))^[j] y') := by
          conv_lhs => rw [e1, inner_add_right,
            inner_smul_right]
        have step2 : inner ℂ (x + (t : ℂ) • y')
            ((⇑(sliceHamCompletedDefect μG ρ hN2 hρcont
              hN β hpos))^[j] x)
            = inner ℂ x ((⇑(sliceHamCompletedDefect μG ρ
                hN2 hρcont hN β hpos))^[j] x)
              + (starRingEnd ℂ) (t : ℂ) * inner ℂ y'
                  ((⇑(sliceHamCompletedDefect μG ρ hN2
                    hρcont hN β hpos))^[j] x) := by
          conv_lhs => rw [inner_add_left, inner_smul_left]
        have step3 : inner ℂ (x + (t : ℂ) • y')
            ((⇑(sliceHamCompletedDefect μG ρ hN2 hρcont
              hN β hpos))^[j] y')
            = inner ℂ x ((⇑(sliceHamCompletedDefect μG ρ
                hN2 hρcont hN β hpos))^[j] y')
              + (starRingEnd ℂ) (t : ℂ) * inner ℂ y'
                  ((⇑(sliceHamCompletedDefect μG ρ hN2
                    hρcont hN β hpos))^[j] y') := by
          conv_lhs => rw [inner_add_left, inner_smul_left]
        rw [step1, step2, step3,
          slicePair_diag_ofReal μG ρ hN2 hρcont hN β hpos
          j x, ← hX_def, hb', hcross, hy'diag,
          slicePair_diag_ofReal μG ρ hN2 hρcont hN β hpos
          j y, ← hY_def, sliceStar_ofReal t]
        push_cast
        ring
      rw [hexp, Complex.ofReal_re] at hdiag
      exact hdiag
    by_cases hY0 : Y = 0
    · have hcontra := key (-(X + 1) / (2 * r))
      rw [hY0] at hcontra
      simp only [mul_zero, add_zero] at hcontra
      have hmid : 2 * (-(X + 1) / (2 * r)) * r
          = -(X + 1) := by
        field_simp
      rw [hmid] at hcontra
      linarith
    · have hYpos : 0 < Y := lt_of_le_of_ne hYnn
        (Ne.symm hY0)
      have hYne : Y ≠ 0 := hY0
      have hkey := key (-r / Y)
      have e1 : 2 * (-r / Y) * r = -(2 * r ^ 2 / Y) := by
        field_simp
      have e2 : (-r / Y) ^ 2 * Y = r ^ 2 / Y := by
        field_simp
      rw [e1, e2] at hkey
      have hle : r ^ 2 / Y ≤ X := by
        linear_combination hkey
      rw [div_le_iff₀ hYpos] at hle
      exact hle

/-! ## §3. The polarized approximants and their limit -/

/-- **The polarized approximants**: the sesquilinear
pairings whose diagonal is `q_K`. -/
noncomputable def sliceApproxB (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (K : ℕ)
    (x y : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos) :
    ℂ :=
  ∑ j ∈ Finset.Icc 1 K, (↑((j : ℝ)⁻¹) : ℂ)
    * inner ℂ x ((⇑(sliceHamCompletedDefect μG ρ hN2 hρcont
        hN β hpos))^[j] y)

/-- The diagonal of the polarized approximant is the
approximant form. -/
theorem sliceApproxB_diag (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (K : ℕ)
    (x : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos) :
    sliceApproxB μG ρ hN2 hρcont hN β hpos K x x
      = ((sliceHamFormApproxC μG ρ hN2 hρcont hN β hpos K
          x : ℝ) : ℂ) := by
  unfold sliceApproxB sliceHamFormApproxC
  rw [Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  conv_lhs => rw [slicePair_diag_ofReal μG ρ hN2 hρcont
    hN β hpos j x]
  rw [← Complex.ofReal_mul]

/-- Polarized approximants are additive in the second
    argument. -/
theorem sliceApproxB_add_right (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (K : ℕ)
    (x y z : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos) :
    sliceApproxB μG ρ hN2 hρcont hN β hpos K x (y + z)
      = sliceApproxB μG ρ hN2 hρcont hN β hpos K x y
        + sliceApproxB μG ρ hN2 hρcont hN β hpos K x
            z := by
  unfold sliceApproxB
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [slicePair_add_right μG ρ hN2 hρcont hN β hpos j x y
    z]
  ring

/-- Polarized approximants are homogeneous in the second
    argument. -/
theorem sliceApproxB_smul_right (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (K : ℕ)
    (c : ℂ)
    (x y : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos) :
    sliceApproxB μG ρ hN2 hρcont hN β hpos K x (c • y)
      = c * sliceApproxB μG ρ hN2 hρcont hN β hpos K x
          y := by
  unfold sliceApproxB
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [slicePair_smul_right μG ρ hN2 hρcont hN β hpos j c x
    y]
  ring

/-- Polarized approximants are additive in the first
    argument. -/
theorem sliceApproxB_add_left (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (K : ℕ)
    (x y z : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos) :
    sliceApproxB μG ρ hN2 hρcont hN β hpos K (x + y) z
      = sliceApproxB μG ρ hN2 hρcont hN β hpos K x z
        + sliceApproxB μG ρ hN2 hρcont hN β hpos K y
            z := by
  unfold sliceApproxB
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [slicePair_add_left μG ρ hN2 hρcont hN β hpos j x y
    z]
  ring

/-- Polarized approximants are conjugate-homogeneous in
    the first argument. -/
theorem sliceApproxB_smul_left (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (K : ℕ)
    (c : ℂ)
    (x y : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos) :
    sliceApproxB μG ρ hN2 hρcont hN β hpos K (c • x) y
      = (starRingEnd ℂ) c * sliceApproxB μG ρ hN2 hρcont
          hN β hpos K x y := by
  unfold sliceApproxB
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [slicePair_smul_left μG ρ hN2 hρcont hN β hpos j c x
    y]
  ring

/-- Polarized approximants are Hermitian. -/
theorem sliceApproxB_conj_symm (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (K : ℕ)
    (x y : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos) :
    (starRingEnd ℂ) (sliceApproxB μG ρ hN2 hρcont hN β
        hpos K x y)
      = sliceApproxB μG ρ hN2 hρcont hN β hpos K y
          x := by
  unfold sliceApproxB
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, sliceStar_ofReal, slicePair_conj_symm μG ρ
    hN2 hρcont hN β hpos j x y]

/-- **Cauchy–Schwarz for a finite block of pairings**:
the norm of a finite sum of polarized terms is bounded
by the square roots of the corresponding diagonal sums.
This is the finite-sum CS of the per-term CS. -/
theorem sliceApproxB_sum_norm_le (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (s : Finset ℕ)
    (x y : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos) :
    ‖∑ j ∈ s, (↑((j : ℝ)⁻¹) : ℂ)
        * inner ℂ x ((⇑(sliceHamCompletedDefect μG ρ hN2
            hρcont hN β hpos))^[j] y)‖
      ≤ Real.sqrt (∑ j ∈ s, (j : ℝ)⁻¹
          * (inner ℂ x ((⇑(sliceHamCompletedDefect μG ρ
              hN2 hρcont hN β hpos))^[j] x)).re)
        * Real.sqrt (∑ j ∈ s, (j : ℝ)⁻¹
            * (inner ℂ y ((⇑(sliceHamCompletedDefect μG
                ρ hN2 hρcont hN β hpos))^[j] y)).re) := by
  have hterm : ∀ j ∈ s, ‖(↑((j : ℝ)⁻¹) : ℂ)
        * inner ℂ x ((⇑(sliceHamCompletedDefect μG ρ hN2
            hρcont hN β hpos))^[j] y)‖
      ≤ Real.sqrt ((j : ℝ)⁻¹
          * (inner ℂ x ((⇑(sliceHamCompletedDefect μG ρ
              hN2 hρcont hN β hpos))^[j] x)).re)
        * Real.sqrt ((j : ℝ)⁻¹
            * (inner ℂ y ((⇑(sliceHamCompletedDefect μG
                ρ hN2 hρcont hN β hpos))^[j] y)).re) := by
    intro j _
    have hjn : (0 : ℝ) ≤ (j : ℝ)⁻¹ := by positivity
    have hax : (0 : ℝ) ≤ (inner ℂ x
        ((⇑(sliceHamCompletedDefect μG ρ hN2 hρcont hN β
          hpos))^[j] x)).re :=
      slicePair_diag_nonneg μG ρ hN2 hρcont hN β hpos j x
    have hay : (0 : ℝ) ≤ (inner ℂ y
        ((⇑(sliceHamCompletedDefect μG ρ hN2 hρcont hN β
          hpos))^[j] y)).re :=
      slicePair_diag_nonneg μG ρ hN2 hρcont hN β hpos j y
    have hcast : ‖((↑((j : ℝ)⁻¹) : ℂ))‖ = (j : ℝ)⁻¹ := by
      have h : ‖((↑((j : ℝ)⁻¹) : ℂ))‖ = |(j : ℝ)⁻¹| :=
        RCLike.norm_ofReal ((j : ℝ)⁻¹)
      rwa [abs_of_nonneg hjn] at h
    have hsq : ((j : ℝ)⁻¹
        * ‖inner ℂ x ((⇑(sliceHamCompletedDefect μG ρ hN2
            hρcont hN β hpos))^[j] y)‖) ^ 2
        ≤ ((j : ℝ)⁻¹ * (inner ℂ x
            ((⇑(sliceHamCompletedDefect μG ρ hN2 hρcont
              hN β hpos))^[j] x)).re)
          * ((j : ℝ)⁻¹ * (inner ℂ y
              ((⇑(sliceHamCompletedDefect μG ρ hN2
                hρcont hN β hpos))^[j] y)).re) := by
      have hcs := slicePair_cs μG ρ hN2 hρcont hN β hpos
        j x y
      have hmul := mul_le_mul_of_nonneg_left hcs
        (sq_nonneg ((j : ℝ)⁻¹))
      have e1 : ((j : ℝ)⁻¹
          * ‖inner ℂ x ((⇑(sliceHamCompletedDefect μG ρ
              hN2 hρcont hN β hpos))^[j] y)‖) ^ 2
          = ((j : ℝ)⁻¹) ^ 2
            * ‖inner ℂ x ((⇑(sliceHamCompletedDefect μG
                ρ hN2 hρcont hN β hpos))^[j] y)‖ ^ 2 := by
        ring
      have e2 : ((j : ℝ)⁻¹ * (inner ℂ x
            ((⇑(sliceHamCompletedDefect μG ρ hN2 hρcont
              hN β hpos))^[j] x)).re)
          * ((j : ℝ)⁻¹ * (inner ℂ y
              ((⇑(sliceHamCompletedDefect μG ρ hN2
                hρcont hN β hpos))^[j] y)).re)
          = ((j : ℝ)⁻¹) ^ 2
            * ((inner ℂ x ((⇑(sliceHamCompletedDefect μG
                ρ hN2 hρcont hN β hpos))^[j] x)).re
              * (inner ℂ y ((⇑(sliceHamCompletedDefect
                  μG ρ hN2 hρcont hN β hpos))^[j]
                  y)).re) := by
        ring
      rw [e1, e2]
      exact hmul
    calc ‖(↑((j : ℝ)⁻¹) : ℂ)
          * inner ℂ x ((⇑(sliceHamCompletedDefect μG ρ
              hN2 hρcont hN β hpos))^[j] y)‖
        = (j : ℝ)⁻¹
            * ‖inner ℂ x ((⇑(sliceHamCompletedDefect μG
                ρ hN2 hρcont hN β hpos))^[j] y)‖ := by
          rw [norm_mul, hcast]
      _ = Real.sqrt (((j : ℝ)⁻¹
            * ‖inner ℂ x ((⇑(sliceHamCompletedDefect μG
                ρ hN2 hρcont hN β hpos))^[j] y)‖) ^ 2) :=
          (Real.sqrt_sq (mul_nonneg hjn
            (norm_nonneg _))).symm
      _ ≤ Real.sqrt (((j : ℝ)⁻¹ * (inner ℂ x
              ((⇑(sliceHamCompletedDefect μG ρ hN2
                hρcont hN β hpos))^[j] x)).re)
            * ((j : ℝ)⁻¹ * (inner ℂ y
                ((⇑(sliceHamCompletedDefect μG ρ hN2
                  hρcont hN β hpos))^[j] y)).re)) :=
          Real.sqrt_le_sqrt hsq
      _ = Real.sqrt ((j : ℝ)⁻¹ * (inner ℂ x
              ((⇑(sliceHamCompletedDefect μG ρ hN2
                hρcont hN β hpos))^[j] x)).re)
            * Real.sqrt ((j : ℝ)⁻¹ * (inner ℂ y
                ((⇑(sliceHamCompletedDefect μG ρ hN2
                  hρcont hN β hpos))^[j] y)).re) :=
          Real.sqrt_mul (mul_nonneg hjn hax) _
  calc ‖∑ j ∈ s, (↑((j : ℝ)⁻¹) : ℂ)
          * inner ℂ x ((⇑(sliceHamCompletedDefect μG ρ
              hN2 hρcont hN β hpos))^[j] y)‖
      ≤ ∑ j ∈ s, ‖(↑((j : ℝ)⁻¹) : ℂ)
          * inner ℂ x ((⇑(sliceHamCompletedDefect μG ρ
              hN2 hρcont hN β hpos))^[j] y)‖ :=
        norm_sum_le s _
    _ ≤ ∑ j ∈ s, Real.sqrt ((j : ℝ)⁻¹
            * (inner ℂ x ((⇑(sliceHamCompletedDefect μG
                ρ hN2 hρcont hN β hpos))^[j] x)).re)
          * Real.sqrt ((j : ℝ)⁻¹
              * (inner ℂ y ((⇑(sliceHamCompletedDefect
                  μG ρ hN2 hρcont hN β hpos))^[j]
                  y)).re) :=
        Finset.sum_le_sum hterm
    _ ≤ Real.sqrt (∑ j ∈ s, (j : ℝ)⁻¹
            * (inner ℂ x ((⇑(sliceHamCompletedDefect μG
                ρ hN2 hρcont hN β hpos))^[j] x)).re)
          * Real.sqrt (∑ j ∈ s, (j : ℝ)⁻¹
              * (inner ℂ y ((⇑(sliceHamCompletedDefect
                  μG ρ hN2 hρcont hN β hpos))^[j]
                  y)).re) := by
        have key := Finset.sum_mul_sq_le_sq_mul_sq s
          (fun j => Real.sqrt ((j : ℝ)⁻¹ * (inner ℂ x
            ((⇑(sliceHamCompletedDefect μG ρ hN2 hρcont
              hN β hpos))^[j] x)).re))
          (fun j => Real.sqrt ((j : ℝ)⁻¹ * (inner ℂ y
            ((⇑(sliceHamCompletedDefect μG ρ hN2 hρcont
              hN β hpos))^[j] y)).re))
        have e1 : (∑ j ∈ s, (Real.sqrt ((j : ℝ)⁻¹
              * (inner ℂ x ((⇑(sliceHamCompletedDefect
                  μG ρ hN2 hρcont hN β hpos))^[j]
                  x)).re)) ^ 2)
            = ∑ j ∈ s, (j : ℝ)⁻¹ * (inner ℂ x
                ((⇑(sliceHamCompletedDefect μG ρ hN2
                  hρcont hN β hpos))^[j] x)).re :=
          Finset.sum_congr rfl fun j _ => Real.sq_sqrt
            (mul_nonneg (by positivity)
              (slicePair_diag_nonneg μG ρ hN2 hρcont hN β
                hpos j x))
        have e2 : (∑ j ∈ s, (Real.sqrt ((j : ℝ)⁻¹
              * (inner ℂ y ((⇑(sliceHamCompletedDefect
                  μG ρ hN2 hρcont hN β hpos))^[j]
                  y)).re)) ^ 2)
            = ∑ j ∈ s, (j : ℝ)⁻¹ * (inner ℂ y
                ((⇑(sliceHamCompletedDefect μG ρ hN2
                  hρcont hN β hpos))^[j] y)).re :=
          Finset.sum_congr rfl fun j _ => Real.sq_sqrt
            (mul_nonneg (by positivity)
              (slicePair_diag_nonneg μG ρ hN2 hρcont hN β
                hpos j y))
        rw [e1, e2] at key
        have hsq2 : (∑ j ∈ s, Real.sqrt ((j : ℝ)⁻¹
              * (inner ℂ x ((⇑(sliceHamCompletedDefect
                  μG ρ hN2 hρcont hN β hpos))^[j] x)).re)
              * Real.sqrt ((j : ℝ)⁻¹ * (inner ℂ y
                  ((⇑(sliceHamCompletedDefect μG ρ hN2
                    hρcont hN β hpos))^[j] y)).re)) ^ 2
            ≤ (Real.sqrt (∑ j ∈ s, (j : ℝ)⁻¹ * (inner ℂ
                  x ((⇑(sliceHamCompletedDefect μG ρ hN2
                    hρcont hN β hpos))^[j] x)).re)
                * Real.sqrt (∑ j ∈ s, (j : ℝ)⁻¹
                    * (inner ℂ y
                      ((⇑(sliceHamCompletedDefect μG ρ
                        hN2 hρcont hN β hpos))^[j]
                        y)).re)) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt
              (Finset.sum_nonneg fun j _ => mul_nonneg
                (by positivity) (slicePair_diag_nonneg μG
                  ρ hN2 hρcont hN β hpos j x)),
            Real.sq_sqrt (Finset.sum_nonneg fun j _ =>
              mul_nonneg (by positivity)
                (slicePair_diag_nonneg μG ρ hN2 hρcont hN
                  β hpos j y))]
          exact key
        have habs := sq_le_sq.mp hsq2
        rwa [abs_of_nonneg (Finset.sum_nonneg fun j _ =>
            mul_nonneg (Real.sqrt_nonneg _)
              (Real.sqrt_nonneg _)),
          abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _)
            (Real.sqrt_nonneg _))] at habs

/-- **Cauchy–Schwarz for the polarized approximants.** -/
theorem sliceApproxB_norm_le (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (K : ℕ)
    (x y : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos) :
    ‖sliceApproxB μG ρ hN2 hρcont hN β hpos K x y‖
      ≤ Real.sqrt (sliceHamFormApproxC μG ρ hN2 hρcont hN
          β hpos K x)
        * Real.sqrt (sliceHamFormApproxC μG ρ hN2 hρcont
            hN β hpos K y) :=
  sliceApproxB_sum_norm_le μG ρ hN2 hρcont hN β hpos
    (Finset.Icc 1 K) x y

/-- `Icc a K` as an `Ico` (interval bookkeeping for tail
    splits). -/
theorem sliceIcc_eq_Ico (a K : ℕ) :
    Finset.Icc a K = Finset.Ico a (K + 1) := by
  ext j
  simp only [Finset.mem_Icc, Finset.mem_Ico]
  omega

/-- Tail split of the polarized approximants. -/
theorem sliceApproxB_sub_eq_sum_Ico (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) {K K' : ℕ}
    (hKK' : K ≤ K')
    (x y : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos) :
    sliceApproxB μG ρ hN2 hρcont hN β hpos K' x y
        - sliceApproxB μG ρ hN2 hρcont hN β hpos K x y
      = ∑ j ∈ Finset.Ico (K + 1) (K' + 1), (↑((j : ℝ)⁻¹) : ℂ)
          * inner ℂ x ((⇑(sliceHamCompletedDefect μG ρ
              hN2 hρcont hN β hpos))^[j] y) := by
  have e : ∀ K : ℕ, sliceApproxB μG ρ hN2 hρcont hN β
        hpos K x y
      = ∑ j ∈ Finset.Ico 1 (K + 1), (↑((j : ℝ)⁻¹) : ℂ)
          * inner ℂ x ((⇑(sliceHamCompletedDefect μG ρ
              hN2 hρcont hN β hpos))^[j] y) := by
    intro K
    unfold sliceApproxB
    rw [sliceIcc_eq_Ico]
  rw [e, e, ← Finset.sum_Ico_consecutive _
    (by omega : 1 ≤ K + 1) (by omega : K + 1 ≤ K' + 1)]
  exact add_sub_cancel_left _ _

/-- Tail split of the approximant forms. -/
theorem sliceHamFormApproxC_sub_eq_sum_Ico (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) {K K' : ℕ}
    (hKK' : K ≤ K')
    (x : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos) :
    sliceHamFormApproxC μG ρ hN2 hρcont hN β hpos K' x
        - sliceHamFormApproxC μG ρ hN2 hρcont hN β hpos K
            x
      = ∑ j ∈ Finset.Ico (K + 1) (K' + 1), (j : ℝ)⁻¹
          * (inner ℂ x ((⇑(sliceHamCompletedDefect μG ρ
              hN2 hρcont hN β hpos))^[j] x)).re := by
  have e : ∀ K : ℕ, sliceHamFormApproxC μG ρ hN2 hρcont
        hN β hpos K x
      = ∑ j ∈ Finset.Ico 1 (K + 1), (j : ℝ)⁻¹
          * (inner ℂ x ((⇑(sliceHamCompletedDefect μG ρ
              hN2 hρcont hN β hpos))^[j] x)).re := by
    intro K
    unfold sliceHamFormApproxC
    rw [sliceIcc_eq_Ico]
  rw [e, e, ← Finset.sum_Ico_consecutive _
    (by omega : 1 ≤ K + 1) (by omega : K + 1 ≤ K' + 1)]
  exact add_sub_cancel_left _ _

/-- **Tail bound**: the difference of two polarized
approximants is controlled by the form tails — the
engine of the Cauchy property on the domain. -/
theorem sliceApproxB_sub_norm_le (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) {K K' : ℕ}
    (hKK' : K ≤ K')
    (x y : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos) :
    ‖sliceApproxB μG ρ hN2 hρcont hN β hpos K' x y
        - sliceApproxB μG ρ hN2 hρcont hN β hpos K x y‖
      ≤ Real.sqrt (sliceHamFormApproxC μG ρ hN2 hρcont hN
          β hpos K' x
          - sliceHamFormApproxC μG ρ hN2 hρcont hN β hpos
              K x)
        * Real.sqrt (sliceHamFormApproxC μG ρ hN2 hρcont
            hN β hpos K' y
            - sliceHamFormApproxC μG ρ hN2 hρcont hN β
                hpos K y) := by
  rw [sliceApproxB_sub_eq_sum_Ico μG ρ hN2 hρcont hN β
      hpos hKK' x y,
    sliceHamFormApproxC_sub_eq_sum_Ico μG ρ hN2 hρcont hN
      β hpos hKK' x,
    sliceHamFormApproxC_sub_eq_sum_Ico μG ρ hN2 hρcont hN
      β hpos hKK' y]
  exact sliceApproxB_sum_norm_le μG ρ hN2 hρcont hN β hpos
    (Finset.Ico (K + 1) (K' + 1)) x y

/-- **The polarized approximants are Cauchy on the
domain**: the form tails vanish by monotone convergence
of `q_K x` to the finite form value. -/
theorem sliceApproxB_cauchySeq (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (x y : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos)
    (hx : x ∈ sliceHamFormDomainC μG ρ hN2 hρcont hN β
      hpos)
    (hy : y ∈ sliceHamFormDomainC μG ρ hN2 hρcont hN β
      hpos) :
    CauchySeq (fun K => sliceApproxB μG ρ hN2 hρcont hN β
      hpos K x y) := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  have hfvy : 0 ≤ sliceFormVal μG ρ hN2 hρcont hN β hpos
      y :=
    sliceFormVal_nonneg μG ρ hN2 hρcont hN β hpos y
  have hδ : (0 : ℝ) < (ε / 2) ^ 2
      / (sliceFormVal μG ρ hN2 hρcont hN β hpos y + 1) :=
    div_pos (pow_pos (half_pos hε) 2) (by linarith)
  obtain ⟨N, hNb⟩ := (Metric.tendsto_atTop.mp
    (sliceFormVal_tendsto_approxC μG ρ hN2 hρcont hN β
      hpos x hx)) _ hδ
  have hdistN : dist (sliceHamFormApproxC μG ρ hN2 hρcont
        hN β hpos N x)
      (sliceFormVal μG ρ hN2 hρcont hN β hpos x)
      < (ε / 2) ^ 2
        / (sliceFormVal μG ρ hN2 hρcont hN β hpos y
          + 1) :=
    hNb N le_rfl
  rw [Real.dist_eq] at hdistN
  have hqN : sliceHamFormApproxC μG ρ hN2 hρcont hN β hpos
        N x
      ≤ sliceFormVal μG ρ hN2 hρcont hN β hpos x :=
    sliceApproxC_le_formVal μG ρ hN2 hρcont hN β hpos x hx
      N
  have hsub : sliceFormVal μG ρ hN2 hρcont hN β hpos x
        - sliceHamFormApproxC μG ρ hN2 hρcont hN β hpos N
            x
      < (ε / 2) ^ 2
        / (sliceFormVal μG ρ hN2 hρcont hN β hpos y
          + 1) := by
    rwa [abs_of_nonpos (sub_nonpos.mpr hqN), neg_sub] at
      hdistN
  have hone : ∀ m ≥ N, dist (sliceApproxB μG ρ hN2
        hρcont hN β hpos m x y)
      (sliceApproxB μG ρ hN2 hρcont hN β hpos N x y)
      < ε / 2 := by
    intro m hm
    rw [dist_eq_norm]
    refine lt_of_le_of_lt (sliceApproxB_sub_norm_le μG ρ
      hN2 hρcont hN β hpos hm x y) ?_
    have hqx : sliceHamFormApproxC μG ρ hN2 hρcont hN β
          hpos m x
          - sliceHamFormApproxC μG ρ hN2 hρcont hN β hpos
              N x
        ≤ sliceFormVal μG ρ hN2 hρcont hN β hpos x
          - sliceHamFormApproxC μG ρ hN2 hρcont hN β hpos
              N x :=
      sub_le_sub_right (sliceApproxC_le_formVal μG ρ hN2
        hρcont hN β hpos x hx m) _
    have hqy : sliceHamFormApproxC μG ρ hN2 hρcont hN β
          hpos m y
          - sliceHamFormApproxC μG ρ hN2 hρcont hN β hpos
              N y
        ≤ sliceFormVal μG ρ hN2 hρcont hN β hpos y := by
      have h1 := sliceApproxC_le_formVal μG ρ hN2 hρcont
        hN β hpos y hy m
      have h2 := sliceHamFormApproxC_nonneg μG ρ hN2
        hρcont hN β hpos N y
      linarith
    have hprod : Real.sqrt (sliceHamFormApproxC μG ρ hN2
          hρcont hN β hpos m x
          - sliceHamFormApproxC μG ρ hN2 hρcont hN β hpos
              N x)
        * Real.sqrt (sliceHamFormApproxC μG ρ hN2 hρcont
            hN β hpos m y
            - sliceHamFormApproxC μG ρ hN2 hρcont hN β
                hpos N y)
        ≤ Real.sqrt (sliceFormVal μG ρ hN2 hρcont hN β
              hpos x
            - sliceHamFormApproxC μG ρ hN2 hρcont hN β
                hpos N x)
          * Real.sqrt (sliceFormVal μG ρ hN2 hρcont hN β
              hpos y) :=
      mul_le_mul (Real.sqrt_le_sqrt hqx)
        (Real.sqrt_le_sqrt hqy) (Real.sqrt_nonneg _)
        (Real.sqrt_nonneg _)
    refine lt_of_le_of_lt hprod ?_
    have hstep : Real.sqrt (sliceFormVal μG ρ hN2 hρcont
          hN β hpos x
          - sliceHamFormApproxC μG ρ hN2 hρcont hN β hpos
              N x)
        * Real.sqrt (sliceFormVal μG ρ hN2 hρcont hN β
            hpos y)
        ≤ Real.sqrt ((ε / 2) ^ 2
            / (sliceFormVal μG ρ hN2 hρcont hN β hpos y
              + 1))
          * Real.sqrt (sliceFormVal μG ρ hN2 hρcont hN β
              hpos y) :=
      mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt
        hsub.le) (Real.sqrt_nonneg _)
    refine lt_of_le_of_lt hstep ?_
    have hlt : (ε / 2) ^ 2
          / (sliceFormVal μG ρ hN2 hρcont hN β hpos y + 1)
          * sliceFormVal μG ρ hN2 hρcont hN β hpos y
        < (ε / 2) ^ 2 := by
      rw [div_mul_eq_mul_div,
        div_lt_iff₀ (by linarith : (0 : ℝ)
          < sliceFormVal μG ρ hN2 hρcont hN β hpos y + 1)]
      calc (ε / 2) ^ 2
            * sliceFormVal μG ρ hN2 hρcont hN β hpos y
          < (ε / 2) ^ 2
              * sliceFormVal μG ρ hN2 hρcont hN β hpos y
            + (ε / 2) ^ 2 := by
            linarith [pow_pos (half_pos hε) 2]
        _ = (ε / 2) ^ 2
            * (sliceFormVal μG ρ hN2 hρcont hN β hpos y
              + 1) := by ring
    calc Real.sqrt ((ε / 2) ^ 2
            / (sliceFormVal μG ρ hN2 hρcont hN β hpos y
              + 1))
          * Real.sqrt (sliceFormVal μG ρ hN2 hρcont hN β
              hpos y)
        = Real.sqrt ((ε / 2) ^ 2
            / (sliceFormVal μG ρ hN2 hρcont hN β hpos y
              + 1)
            * sliceFormVal μG ρ hN2 hρcont hN β hpos
                y) := by
          rw [Real.sqrt_mul (by positivity)]
      _ < Real.sqrt ((ε / 2) ^ 2) :=
          Real.sqrt_lt_sqrt (by positivity) hlt
      _ = ε / 2 := Real.sqrt_sq (half_pos hε).le
  refine ⟨N, fun m hm n hn => ?_⟩
  calc dist (sliceApproxB μG ρ hN2 hρcont hN β hpos m x y)
        (sliceApproxB μG ρ hN2 hρcont hN β hpos n x y)
      ≤ dist (sliceApproxB μG ρ hN2 hρcont hN β hpos m x
            y) (sliceApproxB μG ρ hN2 hρcont hN β hpos N x
              y)
          + dist (sliceApproxB μG ρ hN2 hρcont hN β hpos
              N x y) (sliceApproxB μG ρ hN2 hρcont hN β
                hpos n x y) :=
        dist_triangle _ _ _
    _ = dist (sliceApproxB μG ρ hN2 hρcont hN β hpos m x
            y) (sliceApproxB μG ρ hN2 hρcont hN β hpos N x
              y)
          + dist (sliceApproxB μG ρ hN2 hρcont hN β hpos
              n x y) (sliceApproxB μG ρ hN2 hρcont hN β
                hpos N x y) := by
          rw [dist_comm (sliceApproxB μG ρ hN2 hρcont hN
            β hpos N x y) (sliceApproxB μG ρ hN2 hρcont hN
              β hpos n x y)]
    _ < ε / 2 + ε / 2 := add_lt_add (hone m hm) (hone n hn)
    _ = ε := add_halves ε

/-- The polarized approximants converge on the domain. -/
theorem sliceFormB_exists (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (x y : ↥(sliceHamFormDomainC μG ρ hN2 hρcont hN β
      hpos)) :
    ∃ L : ℂ, Filter.Tendsto
      (fun K => sliceApproxB μG ρ hN2 hρcont hN β hpos K
        x.1 y.1) Filter.atTop (nhds L) :=
  cauchySeq_tendsto_of_complete (sliceApproxB_cauchySeq
    μG ρ hN2 hρcont hN β hpos x.1 y.1 x.2 y.2)

/-- **The polarized Hamiltonian form on the domain**: the
limit of the polarized approximants; the form's off-diagonal
values. -/
noncomputable def sliceFormB (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (x y : ↥(sliceHamFormDomainC μG ρ hN2 hρcont hN β
      hpos)) : ℂ :=
  Classical.choose (sliceFormB_exists μG ρ hN2 hρcont hN β
    hpos x y)

theorem sliceFormB_tendsto (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (x y : ↥(sliceHamFormDomainC μG ρ hN2 hρcont hN β
      hpos)) :
    Filter.Tendsto
      (fun K => sliceApproxB μG ρ hN2 hρcont hN β hpos K
        x.1 y.1) Filter.atTop
      (nhds (sliceFormB μG ρ hN2 hρcont hN β hpos x y)) :=
  Classical.choose_spec (sliceFormB_exists μG ρ hN2 hρcont
    hN β hpos x y)

/-- The limit pairing is additive in the second
    argument. -/
theorem sliceFormB_add_right (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (x y z : ↥(sliceHamFormDomainC μG ρ hN2 hρcont hN β
      hpos)) :
    sliceFormB μG ρ hN2 hρcont hN β hpos x (y + z)
      = sliceFormB μG ρ hN2 hρcont hN β hpos x y
        + sliceFormB μG ρ hN2 hρcont hN β hpos x z := by
  refine tendsto_nhds_unique (sliceFormB_tendsto μG ρ hN2
    hρcont hN β hpos x (y + z)) ?_
  show Filter.Tendsto
    (fun K => sliceApproxB μG ρ hN2 hρcont hN β hpos K
      x.1 (y.1 + z.1)) Filter.atTop
    (nhds (sliceFormB μG ρ hN2 hρcont hN β hpos x y
      + sliceFormB μG ρ hN2 hρcont hN β hpos x z))
  refine Filter.Tendsto.congr
    (fun K => (sliceApproxB_add_right μG ρ hN2 hρcont hN
      β hpos K x.1 y.1 z.1).symm) ?_
  exact (sliceFormB_tendsto μG ρ hN2 hρcont hN β hpos x
    y).add (sliceFormB_tendsto μG ρ hN2 hρcont hN β hpos x
      z)

/-- The limit pairing is homogeneous in the second
    argument. -/
theorem sliceFormB_smul_right (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (c : ℂ)
    (x y : ↥(sliceHamFormDomainC μG ρ hN2 hρcont hN β
      hpos)) :
    sliceFormB μG ρ hN2 hρcont hN β hpos x (c • y)
      = c * sliceFormB μG ρ hN2 hρcont hN β hpos x y := by
  refine tendsto_nhds_unique (sliceFormB_tendsto μG ρ hN2
    hρcont hN β hpos x (c • y)) ?_
  show Filter.Tendsto
    (fun K => sliceApproxB μG ρ hN2 hρcont hN β hpos K
      x.1 (c • y.1)) Filter.atTop
    (nhds (c * sliceFormB μG ρ hN2 hρcont hN β hpos x y))
  refine Filter.Tendsto.congr
    (fun K => (sliceApproxB_smul_right μG ρ hN2 hρcont hN
      β hpos K c x.1 y.1).symm) ?_
  exact Filter.Tendsto.const_mul c (sliceFormB_tendsto μG
    ρ hN2 hρcont hN β hpos x y)

/-- The limit pairing is additive in the first
    argument. -/
theorem sliceFormB_add_left (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (x y z : ↥(sliceHamFormDomainC μG ρ hN2 hρcont hN β
      hpos)) :
    sliceFormB μG ρ hN2 hρcont hN β hpos (x + y) z
      = sliceFormB μG ρ hN2 hρcont hN β hpos x z
        + sliceFormB μG ρ hN2 hρcont hN β hpos y z := by
  refine tendsto_nhds_unique (sliceFormB_tendsto μG ρ hN2
    hρcont hN β hpos (x + y) z) ?_
  show Filter.Tendsto
    (fun K => sliceApproxB μG ρ hN2 hρcont hN β hpos K
      (x.1 + y.1) z.1) Filter.atTop
    (nhds (sliceFormB μG ρ hN2 hρcont hN β hpos x z
      + sliceFormB μG ρ hN2 hρcont hN β hpos y z))
  refine Filter.Tendsto.congr
    (fun K => (sliceApproxB_add_left μG ρ hN2 hρcont hN β
      hpos K x.1 y.1 z.1).symm) ?_
  exact (sliceFormB_tendsto μG ρ hN2 hρcont hN β hpos x
    z).add (sliceFormB_tendsto μG ρ hN2 hρcont hN β hpos y
      z)

/-- The limit pairing is conjugate-homogeneous in the
    first argument. -/
theorem sliceFormB_smul_left (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (c : ℂ)
    (x y : ↥(sliceHamFormDomainC μG ρ hN2 hρcont hN β
      hpos)) :
    sliceFormB μG ρ hN2 hρcont hN β hpos (c • x) y
      = (starRingEnd ℂ) c * sliceFormB μG ρ hN2 hρcont hN
          β hpos x y := by
  refine tendsto_nhds_unique (sliceFormB_tendsto μG ρ hN2
    hρcont hN β hpos (c • x) y) ?_
  show Filter.Tendsto
    (fun K => sliceApproxB μG ρ hN2 hρcont hN β hpos K
      (c • x.1) y.1) Filter.atTop
    (nhds ((starRingEnd ℂ) c * sliceFormB μG ρ hN2 hρcont
      hN β hpos x y))
  refine Filter.Tendsto.congr
    (fun K => (sliceApproxB_smul_left μG ρ hN2 hρcont hN
      β hpos K c x.1 y.1).symm) ?_
  exact Filter.Tendsto.const_mul ((starRingEnd ℂ) c)
    (sliceFormB_tendsto μG ρ hN2 hρcont hN β hpos x y)

/-- The limit pairing is Hermitian. -/
theorem sliceFormB_conj_symm (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (x y : ↥(sliceHamFormDomainC μG ρ hN2 hρcont hN β
      hpos)) :
    (starRingEnd ℂ) (sliceFormB μG ρ hN2 hρcont hN β hpos
        x y)
      = sliceFormB μG ρ hN2 hρcont hN β hpos y x := by
  have hc : Continuous ((starRingEnd ℂ) : ℂ → ℂ) := by
    have he : ((starRingEnd ℂ) : ℂ → ℂ)
        = (star : ℂ → ℂ) :=
      funext fun z => starRingEnd_apply z
    rw [he]
    exact continuous_star
  have hlim := (hc.tendsto _).comp (sliceFormB_tendsto
    μG ρ hN2 hρcont hN β hpos x y)
  have hlim2 : Filter.Tendsto
      (fun K => sliceApproxB μG ρ hN2 hρcont hN β hpos K
        y.1 x.1) Filter.atTop
      (nhds ((starRingEnd ℂ) (sliceFormB μG ρ hN2 hρcont
        hN β hpos x y))) :=
    Filter.Tendsto.congr
      (fun K => sliceApproxB_conj_symm μG ρ hN2 hρcont hN
        β hpos K x.1 y.1) hlim
  exact tendsto_nhds_unique hlim2 (sliceFormB_tendsto μG
    ρ hN2 hρcont hN β hpos y x)

/-- The diagonal of the limit pairing is the form
    value. -/
theorem sliceFormB_self (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (x : ↥(sliceHamFormDomainC μG ρ hN2 hρcont hN β
      hpos)) :
    sliceFormB μG ρ hN2 hρcont hN β hpos x x
      = ((sliceFormVal μG ρ hN2 hρcont hN β hpos x.1 : ℝ)
        : ℂ) := by
  refine tendsto_nhds_unique (sliceFormB_tendsto μG ρ hN2
    hρcont hN β hpos x x) ?_
  have hreal := (Complex.continuous_ofReal.tendsto _).comp
    (sliceFormVal_tendsto_approxC μG ρ hN2 hρcont hN β
      hpos x.1 x.2)
  exact Filter.Tendsto.congr
    (fun K => (sliceApproxB_diag μG ρ hN2 hρcont hN β hpos
      K x.1).symm) hreal

/-! ## §4. The form domain as a Hilbert space -/

/-- **The form domain, as a type in its own right**: the
synonym of `sliceHamFormDomainC` that will carry the form
inner product. (A synonym, not the subtype itself: the
S2-4(b) design note's warning — structures ascribed over
packaged types pick the wrong topology. The synonym's
algebra is transported from the subtype, and every
transport below is `rfl`.) -/
def sliceFormDomain (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) : Type _ :=
  ↥(sliceHamFormDomainC μG ρ hN2 hρcont hN β hpos)

/-- The domain element underlying a form-domain point. -/
def sliceFormDomain.toSub (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (x : sliceFormDomain μG ρ hN2 hρcont hN β hpos) :
    ↥(sliceHamFormDomainC μG ρ hN2 hρcont hN β hpos) :=
  x

/-- A domain element, viewed in the form domain. -/
def sliceFormDomain.ofSub (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (w : ↥(sliceHamFormDomainC μG ρ hN2 hρcont hN β
      hpos)) :
    sliceFormDomain μG ρ hN2 hρcont hN β hpos :=
  w

/-- The ambient vector of a form-domain point. -/
def sliceFormDomain.val (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (x : sliceFormDomain μG ρ hN2 hρcont hN β hpos) :
    sliceHilbertSpace μG ρ hN2 hρcont hN β hpos :=
  (sliceFormDomain.toSub μG ρ hN2 hρcont hN β hpos x).1

noncomputable instance sliceFormDomainAddCommGroup
    (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) :
    AddCommGroup (sliceFormDomain μG ρ hN2 hρcont hN β
      hpos) :=
  inferInstanceAs (AddCommGroup
    ↥(sliceHamFormDomainC μG ρ hN2 hρcont hN β hpos))

noncomputable instance sliceFormDomainModule (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) :
    Module ℂ (sliceFormDomain μG ρ hN2 hρcont hN β
      hpos) :=
  inferInstanceAs (Module ℂ
    ↥(sliceHamFormDomainC μG ρ hN2 hρcont hN β hpos))

theorem sliceFormDomain.toSub_ofSub (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (w : ↥(sliceHamFormDomainC μG ρ hN2 hρcont hN β
      hpos)) :
    (sliceFormDomain.ofSub μG ρ hN2 hρcont hN β hpos
        w).toSub = w :=
  rfl

theorem sliceFormDomain.ofSub_toSub (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (x : sliceFormDomain μG ρ hN2 hρcont hN β hpos) :
    sliceFormDomain.ofSub μG ρ hN2 hρcont hN β hpos
        x.toSub = x :=
  rfl

theorem sliceFormDomain.val_ofSub (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (w : ↥(sliceHamFormDomainC μG ρ hN2 hρcont hN β
      hpos)) :
    (sliceFormDomain.ofSub μG ρ hN2 hρcont hN β hpos
        w).val = w.1 :=
  rfl

theorem sliceFormDomain.val_eq (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (x : sliceFormDomain μG ρ hN2 hρcont hN β hpos) :
    x.val = x.toSub.1 :=
  rfl

theorem sliceFormDomain.toSub_inj (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    {x y : sliceFormDomain μG ρ hN2 hρcont hN β hpos} :
    x.toSub = y.toSub → x = y :=
  fun h => h

theorem sliceFormDomain.toSub_zero (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) :
    (0 : sliceFormDomain μG ρ hN2 hρcont hN β hpos).toSub
      = 0 :=
  rfl

theorem sliceFormDomain.toSub_add (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (x y : sliceFormDomain μG ρ hN2 hρcont hN β hpos) :
    (x + y).toSub = x.toSub + y.toSub :=
  rfl

theorem sliceFormDomain.toSub_smul (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (c : ℂ)
    (x : sliceFormDomain μG ρ hN2 hρcont hN β hpos) :
    (c • x).toSub = c • x.toSub :=
  rfl

theorem sliceFormDomain.val_zero (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) :
    (0 : sliceFormDomain μG ρ hN2 hρcont hN β hpos).val
      = 0 :=
  rfl

theorem sliceFormDomain.val_add (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (x y : sliceFormDomain μG ρ hN2 hρcont hN β hpos) :
    (x + y).val = x.val + y.val :=
  rfl

theorem sliceFormDomain.val_sub (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (x y : sliceFormDomain μG ρ hN2 hρcont hN β hpos) :
    (x - y).val = x.val - y.val :=
  rfl

theorem sliceFormDomain.val_smul (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (c : ℂ)
    (x : sliceFormDomain μG ρ hN2 hρcont hN β hpos) :
    (c • x).val = c • x.val :=
  rfl

/-- **The form inner product** on the domain: the ambient
pairing plus the polarized form. -/
noncomputable def sliceFormInner (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (x y : sliceFormDomain μG ρ hN2 hρcont hN β hpos) :
    ℂ :=
  inner ℂ x.val y.val + sliceFormB μG ρ hN2 hρcont hN β
    hpos x.toSub y.toSub

theorem sliceFormInner_conj_symm (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (x y : sliceFormDomain μG ρ hN2 hρcont hN β hpos) :
    (starRingEnd ℂ) (sliceFormInner μG ρ hN2 hρcont hN β
        hpos y x)
      = sliceFormInner μG ρ hN2 hρcont hN β hpos x y := by
  unfold sliceFormInner
  rw [map_add, inner_conj_symm, sliceFormB_conj_symm]

theorem sliceFormInner_add_left (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (x y z : sliceFormDomain μG ρ hN2 hρcont hN β hpos) :
    sliceFormInner μG ρ hN2 hρcont hN β hpos (x + y) z
      = sliceFormInner μG ρ hN2 hρcont hN β hpos x z
        + sliceFormInner μG ρ hN2 hρcont hN β hpos y
            z := by
  unfold sliceFormInner
  rw [sliceFormDomain.val_add, sliceFormDomain.toSub_add,
    inner_add_left, sliceFormB_add_left]
  ring

theorem sliceFormInner_smul_left (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (c : ℂ)
    (x y : sliceFormDomain μG ρ hN2 hρcont hN β hpos) :
    sliceFormInner μG ρ hN2 hρcont hN β hpos (c • x) y
      = (starRingEnd ℂ) c * sliceFormInner μG ρ hN2
          hρcont hN β hpos x y := by
  unfold sliceFormInner
  rw [sliceFormDomain.val_smul, sliceFormDomain.toSub_smul,
    inner_smul_left, sliceFormB_smul_left]
  ring

/-- The form inner product's diagonal real part is the
form norm's square: ambient norm² plus form value. -/
theorem sliceFormInner_self_re (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (x : sliceFormDomain μG ρ hN2 hρcont hN β hpos) :
    (sliceFormInner μG ρ hN2 hρcont hN β hpos x x).re
      = ‖x.val‖ ^ 2 + sliceFormVal μG ρ hN2 hρcont hN β
          hpos x.val := by
  unfold sliceFormInner
  rw [sliceFormDomain.val_eq, Complex.add_re,
    sliceCompleted_inner_self_re, sliceFormB_self,
    Complex.ofReal_re]

theorem sliceFormInner_re_nonneg (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (x : sliceFormDomain μG ρ hN2 hρcont hN β hpos) :
    0 ≤ (sliceFormInner μG ρ hN2 hρcont hN β hpos x
        x).re := by
  rw [sliceFormInner_self_re]
  exact add_nonneg (sq_nonneg ‖x.val‖)
    (sliceFormVal_nonneg μG ρ hN2 hρcont hN β hpos x.val)

theorem sliceFormInner_self_eq_zero (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (x : sliceFormDomain μG ρ hN2 hρcont hN β hpos) :
    sliceFormInner μG ρ hN2 hρcont hN β hpos x x = 0
      → x = 0 := by
  intro h
  have hre : (sliceFormInner μG ρ hN2 hρcont hN β hpos x
      x).re = 0 := by
    rw [h]
    simp
  rw [sliceFormInner_self_re] at hre
  have hsq : ‖x.val‖ ^ 2 = 0 :=
    (add_eq_zero_iff_of_nonneg (sq_nonneg ‖x.val‖)
      (sliceFormVal_nonneg μG ρ hN2 hρcont hN β hpos
        x.val)).mp hre |>.1
  have hval : x.val = 0 :=
    norm_eq_zero.mp (sq_eq_zero_iff.mp hsq)
  have hsub : x.toSub = 0 := Subtype.ext hval
  have h0 : (0 : sliceFormDomain μG ρ hN2 hρcont hN β
      hpos).toSub = 0 :=
    sliceFormDomain.toSub_zero μG ρ hN2 hρcont hN β hpos
  exact sliceFormDomain.toSub_inj μG ρ hN2 hρcont hN β
    hpos (by rwa [← h0] at hsub)

/-- **The form Core**: the form inner product as an
`InnerProductSpace.Core` on the domain synonym. -/
noncomputable def sliceFormCore (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) :
    InnerProductSpace.Core ℂ (sliceFormDomain μG ρ hN2
      hρcont hN β hpos) where
  inner := sliceFormInner μG ρ hN2 hρcont hN β hpos
  conj_inner_symm := sliceFormInner_conj_symm μG ρ hN2
    hρcont hN β hpos
  re_inner_nonneg := sliceFormInner_re_nonneg μG ρ hN2
    hρcont hN β hpos
  add_left := sliceFormInner_add_left μG ρ hN2 hρcont hN
    β hpos
  smul_left := fun x y r => sliceFormInner_smul_left μG
    ρ hN2 hρcont hN β hpos r x y
  definite := sliceFormInner_self_eq_zero μG ρ hN2
    hρcont hN β hpos

noncomputable instance sliceFormDomainNormedAddCommGroup
    (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) :
    NormedAddCommGroup (sliceFormDomain μG ρ hN2 hρcont
      hN β hpos) :=
  (sliceFormCore μG ρ hN2 hρcont hN β
    hpos).toNormedAddCommGroup

noncomputable instance sliceFormDomainInnerProductSpace
    (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) :
    InnerProductSpace ℂ (sliceFormDomain μG ρ hN2 hρcont
      hN β hpos) :=
  InnerProductSpace.ofCore (sliceFormCore μG ρ hN2
    hρcont hN β hpos).toCore

/-- **The form norm, squared**: `‖x‖²_form = ‖x‖² + form(x)`. -/
theorem sliceFormDomain_norm_sq (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (x : sliceFormDomain μG ρ hN2 hρcont hN β hpos) :
    ‖x‖ ^ 2 = ‖x.val‖ ^ 2 + sliceFormVal μG ρ hN2 hρcont
        hN β hpos x.val := by
  have h1 : ‖x‖ ^ 2 = (sliceFormInner μG ρ hN2 hρcont hN
      β hpos x x).re :=
    InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ) x
  rwa [sliceFormInner_self_re] at h1

/-- **The form norm**: `‖x‖_form = √(‖x‖² + form(x))`. -/
theorem sliceFormDomain_norm (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (x : sliceFormDomain μG ρ hN2 hρcont hN β hpos) :
    ‖x‖ = Real.sqrt (‖x.val‖ ^ 2 + sliceFormVal μG ρ hN2
        hρcont hN β hpos x.val) := by
  rw [← Real.sqrt_sq (norm_nonneg x),
    sliceFormDomain_norm_sq]

/-- The ambient norm is dominated by the form norm (the
inclusion bound). -/
theorem sliceFormDomain_val_norm_le (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (x : sliceFormDomain μG ρ hN2 hρcont hN β hpos) :
    ‖x.val‖ ≤ ‖x‖ := by
  have h : ‖x.val‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [sliceFormDomain_norm_sq]
    exact le_add_of_nonneg_right
      (sliceFormVal_nonneg μG ρ hN2 hρcont hN β hpos
        x.val)
  have h2 := sq_le_sq.mp h
  simpa using h2

/-- The inclusion of the form domain into the completed
space, as a linear map: the `val` projection. -/
noncomputable def sliceFormInclusionLin (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) :
    sliceFormDomain μG ρ hN2 hρcont hN β hpos →ₗ[ℂ]
      sliceHilbertSpace μG ρ hN2 hρcont hN β hpos where
  toFun := sliceFormDomain.val μG ρ hN2 hρcont hN β hpos
  map_add' := fun x y => sliceFormDomain.val_add μG ρ
    hN2 hρcont hN β hpos x y
  map_smul' := fun c x => sliceFormDomain.val_smul μG ρ
    hN2 hρcont hN β hpos c x

/-- **The continuous inclusion** of the form domain into
the completed space, with bound `1`. -/
noncomputable def sliceFormInclusion (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) :
    sliceFormDomain μG ρ hN2 hρcont hN β hpos →L[ℂ]
      sliceHilbertSpace μG ρ hN2 hρcont hN β hpos :=
  (sliceFormInclusionLin μG ρ hN2 hρcont hN β
    hpos).mkContinuous 1 (fun x => by
      rw [one_mul]
      show ‖(sliceFormInclusionLin μG ρ hN2 hρcont hN β
          hpos) x‖ ≤ ‖x‖
      exact sliceFormDomain_val_norm_le μG ρ hN2 hρcont
        hN β hpos x)

theorem sliceFormInclusion_apply (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (x : sliceFormDomain μG ρ hN2 hρcont hN β hpos) :
    sliceFormInclusion μG ρ hN2 hρcont hN β hpos x = x.val :=
  rfl

theorem sliceFormInclusion_norm_le (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (x : sliceFormDomain μG ρ hN2 hρcont hN β hpos) :
    ‖sliceFormInclusion μG ρ hN2 hρcont hN β hpos x‖
      ≤ ‖x‖ := by
  rw [sliceFormInclusion_apply]
  exact sliceFormDomain_val_norm_le μG ρ hN2 hρcont hN β
    hpos x

/-! ## §5. Closedness: completeness of the form domain -/

/-- The completed defect, as a continuous linear map:
`1 - T̂_c`. -/
noncomputable def sliceDefectCLM (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) :
    sliceHilbertSpace μG ρ hN2 hρcont hN β hpos →L[ℂ]
      sliceHilbertSpace μG ρ hN2 hρcont hN β hpos :=
  1 - sliceHatCompleted μG ρ hN2 hρcont hN β hpos

theorem sliceDefectCLM_apply (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (z : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos) :
    sliceDefectCLM μG ρ hN2 hρcont hN β hpos z
      = sliceHamCompletedDefect μG ρ hN2 hρcont hN β hpos
          z := by
  unfold sliceDefectCLM
  rw [ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.one_apply, sliceHatCompleted_apply,
    sliceHamCompletedDefect_apply]

/-- The CLM defect's iterates are the defect iterates. -/
theorem sliceDefectCLM_iterate (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (j : ℕ)
    (z : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos) :
    (⇑(sliceDefectCLM μG ρ hN2 hρcont hN β hpos))^[j] z
      = (⇑(sliceHamCompletedDefect μG ρ hN2 hρcont hN β
          hpos))^[j] z := by
  induction j generalizing z with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih,
      sliceDefectCLM_apply]
    exact Eq.symm (Function.iterate_succ_apply' _ _ _)

/-- **Each approximant form is continuous** on the
completed space: a finite sum of continuous pairings of
defect iterates. This is the continuity input of the
lower-semicontinuity argument. -/
theorem sliceHamFormApproxC_continuous (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (K : ℕ) :
    Continuous (fun z => sliceHamFormApproxC μG ρ hN2
      hρcont hN β hpos K z) := by
  unfold sliceHamFormApproxC
  refine continuous_finsetSum _ fun j _ => ?_
  refine Continuous.mul continuous_const ?_
  have heq : (fun z => inner ℂ z
        ((⇑(sliceHamCompletedDefect μG ρ hN2 hρcont hN β
          hpos))^[j] z))
      = (fun z => inner ℂ z ((⇑(sliceDefectCLM μG ρ hN2
          hρcont hN β hpos))^[j] z)) :=
    funext fun z => by rw [sliceDefectCLM_iterate]
  have hinner : Continuous (fun z => inner ℂ z
      ((⇑(sliceHamCompletedDefect μG ρ hN2 hρcont hN β
        hpos))^[j] z)) := by
    rw [heq]
    exact continuous_id.inner
      ((sliceDefectCLM μG ρ hN2 hρcont hN β
        hpos).continuous.iterate j)
  exact Complex.continuous_re.comp hinner

/-- **Lower semicontinuity of the form, in the form the
closedness proof consumes.** If a sequence in the domain
converges ambiently to `y` with uniformly small form
tails beyond `N₀`, then every `y - u n` (`n ≥ N₀`) is in
the domain with form value `≤ ε`. The membership is
*derived*: each approximant `q_K(y - u n)` is a limit of
approximants along the sequence, bounded by `ε` for
*every* `K`, and the domain is the boundedness locus.
Nothing about `form(y)` is assumed. -/
theorem sliceFormClosed_lim (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (u : ℕ → sliceHilbertSpace μG ρ hN2 hρcont hN β hpos)
    (huD : ∀ n, u n ∈ sliceHamFormDomainC μG ρ hN2 hρcont
      hN β hpos)
    (y : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos)
    (hy : Filter.Tendsto u Filter.atTop (nhds y))
    {ε : ℝ} (hε : 0 ≤ ε) (N₀ : ℕ)
    (htail : ∀ m ≥ N₀, ∀ n ≥ N₀, sliceFormVal μG ρ hN2
      hρcont hN β hpos (u m - u n) ≤ ε) :
    ∀ n ≥ N₀, y - u n ∈ sliceHamFormDomainC μG ρ hN2
        hρcont hN β hpos
      ∧ sliceFormVal μG ρ hN2 hρcont hN β hpos (y - u n)
        ≤ ε := by
  intro n hn
  have hbound : ∀ K, sliceHamFormApproxC μG ρ hN2 hρcont
        hN β hpos K (y - u n) ≤ ε := by
    intro K
    have hlim : Filter.Tendsto
        (fun m => sliceHamFormApproxC μG ρ hN2 hρcont hN
          β hpos K (u m - u n)) Filter.atTop
        (nhds (sliceHamFormApproxC μG ρ hN2 hρcont hN β
          hpos K (y - u n))) := by
      have hsub : Filter.Tendsto (fun m => u m - u n)
          Filter.atTop (nhds (y - u n)) :=
        hy.sub tendsto_const_nhds
      exact ((sliceHamFormApproxC_continuous μG ρ hN2
        hρcont hN β hpos K).tendsto _).comp hsub
    refine le_of_tendsto hlim ?_
    rw [Filter.eventually_atTop]
    refine ⟨N₀, fun m hm => ?_⟩
    exact le_trans (sliceApproxC_le_formVal μG ρ hN2
      hρcont hN β hpos (u m - u n)
      (sub_mem (huD m) (huD n)) K) (htail m hm n hn)
  exact ⟨sliceHam_mem_domainC_of_forall_approxC_le μG ρ
      hN2 hρcont hN β hpos (y - u n) hbound,
    sliceFormVal_le_of_forall_approxC_le μG ρ hN2 hρcont
      hN β hpos (y - u n) hε hbound⟩

/-- **CLOSEDNESS.** The form domain, with the form inner
product, is a Hilbert space: it is complete in the form
norm. A form-Cauchy sequence is ambient-Cauchy (the
inclusion bound), its ambient limit lies in the domain
by the lower-semicontinuity lemma, and the sequence
converges to it in the form norm by the same lemma —
the two clauses (membership, form bound) are exactly
the lemma's two conclusions. -/
noncomputable instance sliceFormDomainCompleteSpace
    (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) :
    CompleteSpace (sliceFormDomain μG ρ hN2 hρcont hN β
      hpos) :=
  Metric.complete_of_cauchySeq_tendsto fun u hu => by
    have hvC : CauchySeq (fun n => (u n).val) := by
      rw [Metric.cauchySeq_iff] at hu ⊢
      intro ε hε
      obtain ⟨N, hNb⟩ := hu ε hε
      refine ⟨N, fun m hm n hn => lt_of_le_of_lt ?_
        (hNb m hm n hn)⟩
      have h1 : dist (u m).val (u n).val
          = ‖(u m - u n).val‖ := by
        rw [dist_eq_norm, sliceFormDomain.val_sub]
      rw [h1]
      exact le_trans (sliceFormDomain_val_norm_le μG ρ
        hN2 hρcont hN β hpos (u m - u n))
        (le_of_eq (dist_eq_norm (u m) (u n)).symm)
    obtain ⟨y, hy⟩ := cauchySeq_tendsto_of_complete hvC
    have huD : ∀ n, (u n).val ∈ sliceHamFormDomainC μG ρ
        hN2 hρcont hN β hpos :=
      fun n => (u n).toSub.2
    have htail : ∀ ε : ℝ, 0 < ε → ∃ N₀, ∀ m ≥ N₀,
        ∀ n ≥ N₀, sliceFormVal μG ρ hN2 hρcont hN β hpos
          ((u m).val - (u n).val) ≤ ε := by
      intro ε hε
      obtain ⟨N₀, hN₀⟩ := (Metric.cauchySeq_iff.mp hu)
        (Real.sqrt ε) (Real.sqrt_pos.mpr hε)
      refine ⟨N₀, fun m hm n hn => ?_⟩
      have hd := hN₀ m hm n hn
      have hfv : sliceFormVal μG ρ hN2 hρcont hN β hpos
            ((u m).val - (u n).val)
          ≤ dist (u m) (u n) ^ 2 := by
        have hnorm := sliceFormDomain_norm_sq μG ρ hN2
          hρcont hN β hpos (u m - u n)
        rw [sliceFormDomain.val_sub] at hnorm
        rw [← dist_eq_norm] at hnorm
        have hnn : (0 : ℝ) ≤ ‖(u m).val - (u n).val‖ ^ 2 :=
          sq_nonneg _
        linarith
      refine le_trans hfv ?_
      have hlt : dist (u m) (u n) ^ 2 < ε := by
        have h := sq_lt_sq.mpr (by
          rwa [abs_of_nonneg dist_nonneg,
            abs_of_nonneg (Real.sqrt_nonneg ε)] :
          |dist (u m) (u n)| < |Real.sqrt ε|)
        rwa [Real.sq_sqrt hε.le] at h
      exact hlt.le
    obtain ⟨N₀, hN₀⟩ := htail 1 one_pos
    have hlim0 := sliceFormClosed_lim μG ρ hN2 hρcont hN
      β hpos (fun n => (u n).val) huD y hy zero_le_one N₀
      hN₀
    have hyD : y ∈ sliceHamFormDomainC μG ρ hN2 hρcont
        hN β hpos := by
      have h := add_mem (hlim0 N₀ le_rfl).1 (huD N₀)
      rwa [sub_add_cancel] at h
    refine ⟨sliceFormDomain.ofSub μG ρ hN2 hρcont hN β
      hpos ⟨y, hyD⟩, ?_⟩
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N₁, hN₁⟩ := (Metric.tendsto_atTop.mp hy)
      (ε / 2) (half_pos hε)
    obtain ⟨N₂, hN₂⟩ := htail (ε ^ 2 / 2) (by positivity)
    have hlim := sliceFormClosed_lim μG ρ hN2 hρcont hN β
      hpos (fun n => (u n).val) huD y hy
      (by positivity : (0 : ℝ) ≤ ε ^ 2 / 2) N₂ hN₂
    refine ⟨max N₁ N₂, fun n hn => ?_⟩
    have hn₁ : n ≥ N₁ := le_trans (le_max_left N₁ N₂) hn
    have hn₂ : n ≥ N₂ := le_trans (le_max_right N₁ N₂) hn
    have hnorm_lt : ‖(u n).val - y‖ < ε / 2 := by
      have h := hN₁ n hn₁
      rwa [dist_eq_norm] at h
    have hfv : sliceFormVal μG ρ hN2 hρcont hN β hpos
        ((u n).val - y) ≤ ε ^ 2 / 2 := by
      have h := (hlim n hn₂).2
      have hneg : (u n).val - y = -(y - (u n).val) := by
        abel
      rw [hneg, sliceFormVal_neg]
      exact h
    have hε2 : (0 : ℝ) ≤ ε / 2 := by positivity
    have hsq1 : ‖(u n).val - y‖ ^ 2 < (ε / 2) ^ 2 :=
      sq_lt_sq.mpr (by
        rwa [abs_of_nonneg (norm_nonneg _),
          abs_of_nonneg hε2] :
        |‖(u n).val - y‖| < |ε / 2|)
    have hsq2 : (ε / 2) ^ 2 + ε ^ 2 / 2 < ε ^ 2 := by
      nlinarith [mul_pos hε hε]
    have hsq : ‖u n - sliceFormDomain.ofSub μG ρ hN2
          hρcont hN β hpos ⟨y, hyD⟩‖ ^ 2 < ε ^ 2 := by
      rw [sliceFormDomain_norm_sq, sliceFormDomain.val_sub,
        sliceFormDomain.val_ofSub]
      exact lt_of_lt_of_le
        (add_lt_add_of_lt_of_le hsq1 hfv) hsq2.le
    rw [dist_eq_norm, ← Real.sqrt_sq (norm_nonneg _)]
    exact (Real.sqrt_lt' hε).mpr hsq

/-! ## §6. The density obstruction, the β = 0 density
case, the weld clause, and the packages -/

/-- On the fixed space of the completed transfer
operator, the completed defect acts as the identity on
every iterate. -/
theorem sliceHamCompletedDefect_iterate_of_hat_eq_zero
    (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    {w : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos}
    (hw : sliceHatCompleted μG ρ hN2 hρcont hN β hpos w
      = 0) (j : ℕ) :
    (⇑(sliceHamCompletedDefect μG ρ hN2 hρcont hN β
        hpos))^[j] w = w := by
  have hw' : sliceHatCompletedFun μG ρ hN2 hρcont hN β
      hpos w = 0 := by
    have h := hw
    rwa [sliceHatCompleted_apply] at h
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih,
      sliceHamCompletedDefect_apply, hw', sub_zero]

/-- The polarized approximant against a fixed vector of
the completed transfer operator is the harmonic scalar
times the ambient pairing. -/
theorem sliceApproxB_apply_ker (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (K : ℕ)
    (x w : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos)
    (hw : sliceHatCompleted μG ρ hN2 hρcont hN β hpos w
      = 0) :
    sliceApproxB μG ρ hN2 hρcont hN β hpos K x w
      = ((∑ j ∈ Finset.Icc 1 K, (j : ℝ)⁻¹ : ℝ) : ℂ)
        * inner ℂ x w := by
  calc sliceApproxB μG ρ hN2 hρcont hN β hpos K x w
      = ∑ j ∈ Finset.Icc 1 K, (↑((j : ℝ)⁻¹) : ℂ)
          * inner ℂ x w := by
        unfold sliceApproxB
        exact Finset.sum_congr rfl fun j _ => by
          rw [sliceHamCompletedDefect_iterate_of_hat_eq_zero
            μG ρ hN2 hρcont hN β hpos hw j]
    _ = (∑ j ∈ Finset.Icc 1 K, (↑((j : ℝ)⁻¹) : ℂ))
          * inner ℂ x w := by
        rw [Finset.sum_mul]
    _ = ((∑ j ∈ Finset.Icc 1 K, (j : ℝ)⁻¹ : ℝ) : ℂ)
          * inner ℂ x w := by
        rw [Complex.ofReal_sum]

/-- The approximant form at a fixed vector of the
completed transfer operator is the harmonic scalar
times the squared norm. -/
theorem sliceHamFormApproxC_apply_ker (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (K : ℕ)
    {w : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos}
    (hw : sliceHatCompleted μG ρ hN2 hρcont hN β hpos w
      = 0) :
    sliceHamFormApproxC μG ρ hN2 hρcont hN β hpos K w
      = (∑ j ∈ Finset.Icc 1 K, (j : ℝ)⁻¹) * ‖w‖ ^ 2 := by
  calc sliceHamFormApproxC μG ρ hN2 hρcont hN β hpos K w
      = ∑ j ∈ Finset.Icc 1 K, (j : ℝ)⁻¹ * ‖w‖ ^ 2 := by
        unfold sliceHamFormApproxC
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [sliceHamCompletedDefect_iterate_of_hat_eq_zero
          μG ρ hN2 hρcont hN β hpos hw j,
          sliceCompleted_inner_self_re]
    _ = (∑ j ∈ Finset.Icc 1 K, (j : ℝ)⁻¹) * ‖w‖ ^ 2 :=
        (Finset.sum_mul ..).symm

/-- The harmonic sums grow at least linearly under
doubling: `H_{2^k} ≥ k / 2`. -/
theorem sliceHarmonicSum_ge (k : ℕ) :
    (k : ℝ) / 2
      ≤ ∑ j ∈ Finset.Icc 1 (2 ^ k), ((j : ℕ) : ℝ)⁻¹ := by
  rw [sliceIcc_eq_Ico]
  induction k with
  | zero => norm_num
  | succ k ih =>
    have h2k : (2 : ℕ) ^ (k + 1) = 2 ^ k + 2 ^ k := by
      rw [pow_succ]; ring
    have hsplit := Finset.sum_Ico_consecutive
      (fun j : ℕ => (j : ℝ)⁻¹)
      (show (1 : ℕ) ≤ 2 ^ k + 1 by
        have h := Nat.one_le_two_pow (n := k); omega)
      (show (2 : ℕ) ^ k + 1 ≤ 2 ^ (k + 1) + 1 by
        rw [h2k]; have h := Nat.one_le_two_pow (n := k);
        omega)
    rw [← hsplit]
    have hcard : (Finset.Ico (2 ^ k + 1)
        (2 ^ (k + 1) + 1) : Finset ℕ).card = 2 ^ k := by
      rw [Nat.card_Ico, h2k]
      have h := Nat.one_le_two_pow (n := k); omega
    have hterm : ∀ j : ℕ, j ∈ Finset.Ico (2 ^ k + 1)
        (2 ^ (k + 1) + 1) →
        ((2 : ℝ) ^ (k + 1))⁻¹ ≤ (j : ℝ)⁻¹ := by
      intro j hj
      rw [Finset.mem_Ico] at hj
      have h1 : j ≤ 2 ^ (k + 1) := by omega
      have h2 : (j : ℝ) ≤ ((2 ^ (k + 1) : ℕ) : ℝ) := by
        exact_mod_cast h1
      rw [Nat.cast_pow, Nat.cast_ofNat] at h2
      exact inv_anti₀
        (by exact_mod_cast (show 0 < j by omega)) h2
    have hval : (2 ^ k : ℝ) * ((2 : ℝ) ^ (k + 1))⁻¹
        = 1 / 2 := by
      rw [pow_succ, mul_inv, ← mul_assoc,
        mul_inv_cancel₀ (pow_ne_zero k
          (by norm_num : (2 : ℝ) ≠ 0)), one_mul]
      norm_num
    have hsum2 : (1 : ℝ) / 2
        ≤ ∑ j ∈ Finset.Ico (2 ^ k + 1) (2 ^ (k + 1) + 1),
          ((j : ℕ) : ℝ)⁻¹ := by
      calc (1 : ℝ) / 2
          = (2 ^ k : ℝ) * ((2 : ℝ) ^ (k + 1))⁻¹ := hval.symm
        _ = ∑ j ∈ Finset.Ico (2 ^ k + 1) (2 ^ (k + 1) + 1),
              ((2 : ℝ) ^ (k + 1))⁻¹ := by
            rw [Finset.sum_const, hcard, nsmul_eq_mul,
              Nat.cast_pow, Nat.cast_ofNat]
        _ ≤ ∑ j ∈ Finset.Ico (2 ^ k + 1) (2 ^ (k + 1) + 1),
              ((j : ℕ) : ℝ)⁻¹ :=
            Finset.sum_le_sum fun j hj => hterm j hj
    have hk : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by simp
    rw [hk]
    linarith [ih, hsum2]

/-- The norm of a real harmonic scalar, as a complex
number, is the scalar itself. -/
theorem sliceHarmonicSum_norm (K : ℕ) :
    ‖((∑ j ∈ Finset.Icc 1 K, (j : ℝ)⁻¹ : ℝ) : ℂ)‖
      = ∑ j ∈ Finset.Icc 1 K, (j : ℝ)⁻¹ := by
  have h1 : ‖((∑ j ∈ Finset.Icc 1 K, (j : ℝ)⁻¹ : ℝ) : ℂ)‖
      = |∑ j ∈ Finset.Icc 1 K, (j : ℝ)⁻¹| :=
    RCLike.norm_ofReal _
  rw [h1, abs_of_nonneg (Finset.sum_nonneg fun j _ =>
    inv_nonneg.mpr (Nat.cast_nonneg j))]

/-- Pure real-analysis core of the density obstruction:
a pairing bounded through every harmonic window by
`√(fv) · √(H_K · d)` with `c, d > 0` is impossible,
because `H_K` is unbounded. -/
theorem sliceHarmonic_contradiction_aux {c d fv : ℝ}
    (hc : 0 < c) (hd : 0 < d) (hfv : 0 ≤ fv)
    (hIneq : ∀ K : ℕ, (∑ j ∈ Finset.Icc 1 K, (j : ℝ)⁻¹) * c
      ≤ Real.sqrt fv
        * Real.sqrt ((∑ j ∈ Finset.Icc 1 K, (j : ℝ)⁻¹)
          * d)) :
    False := by
  obtain ⟨k, hk⟩ := exists_nat_gt ((fv * d) / c ^ 2 * 2)
  have hI := hIneq (2 ^ k)
  have hH := sliceHarmonicSum_ge k
  have hnn : (0 : ℝ) ≤ (fv * d) / c ^ 2 * 2 := by
    positivity
  have hkpos : (0 : ℝ) < (k : ℝ) := lt_of_le_of_lt hnn hk
  have hHpos : (0 : ℝ) < ∑ j ∈ Finset.Icc 1 (2 ^ k),
      ((j : ℕ) : ℝ)⁻¹ :=
    lt_of_lt_of_le (by linarith) hH
  have hsq : ((∑ j ∈ Finset.Icc 1 (2 ^ k), ((j : ℕ) : ℝ)⁻¹) * c)
        * ((∑ j ∈ Finset.Icc 1 (2 ^ k), ((j : ℕ) : ℝ)⁻¹) * c)
      ≤ (Real.sqrt fv * Real.sqrt
          ((∑ j ∈ Finset.Icc 1 (2 ^ k), ((j : ℕ) : ℝ)⁻¹) * d))
        * (Real.sqrt fv * Real.sqrt
          ((∑ j ∈ Finset.Icc 1 (2 ^ k), ((j : ℕ) : ℝ)⁻¹)
            * d)) :=
    mul_self_le_mul_self (mul_nonneg hHpos.le hc.le) hI
  have hsq2 : (Real.sqrt fv * Real.sqrt
        ((∑ j ∈ Finset.Icc 1 (2 ^ k), ((j : ℕ) : ℝ)⁻¹) * d))
      * (Real.sqrt fv * Real.sqrt
        ((∑ j ∈ Finset.Icc 1 (2 ^ k), ((j : ℕ) : ℝ)⁻¹) * d))
      = fv * ((∑ j ∈ Finset.Icc 1 (2 ^ k), ((j : ℕ) : ℝ)⁻¹)
        * d) := by
    calc (Real.sqrt fv * Real.sqrt
          ((∑ j ∈ Finset.Icc 1 (2 ^ k), ((j : ℕ) : ℝ)⁻¹) * d))
        * (Real.sqrt fv * Real.sqrt
          ((∑ j ∈ Finset.Icc 1 (2 ^ k), ((j : ℕ) : ℝ)⁻¹) * d))
        = (Real.sqrt fv * Real.sqrt fv)
          * (Real.sqrt ((∑ j ∈ Finset.Icc 1 (2 ^ k),
              ((j : ℕ) : ℝ)⁻¹) * d)
            * Real.sqrt ((∑ j ∈ Finset.Icc 1 (2 ^ k),
              ((j : ℕ) : ℝ)⁻¹) * d)) := by ring
      _ = fv * ((∑ j ∈ Finset.Icc 1 (2 ^ k), ((j : ℕ) : ℝ)⁻¹)
          * d) := by
          rw [Real.mul_self_sqrt hfv,
            Real.mul_self_sqrt
              (mul_nonneg hHpos.le hd.le)]
  have hcan : (∑ j ∈ Finset.Icc 1 (2 ^ k), ((j : ℕ) : ℝ)⁻¹)
        * c ^ 2 ≤ fv * d := by
    have h := le_trans hsq (le_of_eq hsq2)
    have h' : (∑ j ∈ Finset.Icc 1 (2 ^ k), ((j : ℕ) : ℝ)⁻¹)
          * ((∑ j ∈ Finset.Icc 1 (2 ^ k), ((j : ℕ) : ℝ)⁻¹)
            * c ^ 2)
        ≤ (∑ j ∈ Finset.Icc 1 (2 ^ k), ((j : ℕ) : ℝ)⁻¹)
          * (fv * d) := by
      rwa [show ((∑ j ∈ Finset.Icc 1 (2 ^ k), ((j : ℕ) : ℝ)⁻¹)
            * c) * ((∑ j ∈ Finset.Icc 1 (2 ^ k), ((j : ℕ) : ℝ)⁻¹)
            * c)
          = (∑ j ∈ Finset.Icc 1 (2 ^ k), ((j : ℕ) : ℝ)⁻¹)
            * ((∑ j ∈ Finset.Icc 1 (2 ^ k), ((j : ℕ) : ℝ)⁻¹)
              * c ^ 2) from by ring,
        show fv * ((∑ j ∈ Finset.Icc 1 (2 ^ k), ((j : ℕ) : ℝ)⁻¹)
            * d)
          = (∑ j ∈ Finset.Icc 1 (2 ^ k), ((j : ℕ) : ℝ)⁻¹)
            * (fv * d) from by ring] at h
    exact le_of_mul_le_mul_left h' hHpos
  have hfin : fv * d
      < (∑ j ∈ Finset.Icc 1 (2 ^ k), ((j : ℕ) : ℝ)⁻¹) * c ^ 2 := by
    have hc2 : c ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hc)
    have e1 : fv * d = ((fv * d) / c ^ 2 * 2) / 2
        * c ^ 2 := by
      field_simp
    rw [e1]
    have e2 : ((fv * d) / c ^ 2 * 2) / 2 < (k : ℝ) / 2 := by
      linarith [hk]
    have e3 : ((fv * d) / c ^ 2 * 2) / 2 * c ^ 2
        < (k : ℝ) / 2 * c ^ 2 :=
      mul_lt_mul_of_pos_right e2 (by positivity)
    exact lt_of_lt_of_le e3
      (mul_le_mul_of_nonneg_right hH (by positivity))
  exact absurd hcan (not_le.mpr hfin)

/-- **THE DENSITY OBSTRUCTION (proved).** Every vector
of the form domain is ambient-orthogonal to the fixed
space of the completed transfer operator: the polarized
approximant against a fixed vector grows like the
harmonic sums, while Cauchy–Schwarz bounds it by
`√(form value) · √(H_K · ‖w‖²)` — forcing the pairing
to vanish. In particular the form domain is contained
in `(ker T̂_c)⊥`, so dense range in the ambient space
*fails* wherever `ker T̂_c ≠ 0` with the vacuum line
outside the domain. Density is therefore NOT asserted
in general; it is proved at `β = 0` below, where the
kernel is everything and the domain is the whole
space. -/
theorem sliceFormDomain_orthogonal_ker (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    {x : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos}
    (hx : x ∈ sliceHamFormDomainC μG ρ hN2 hρcont hN β
      hpos)
    {w : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos}
    (hw : sliceHatCompleted μG ρ hN2 hρcont hN β hpos w
      = 0) :
    inner ℂ x w = 0 := by
  by_contra hne
  have hc : 0 < ‖inner ℂ x w‖ := norm_pos_iff.mpr hne
  have hd : 0 < ‖w‖ ^ 2 := by
    rcases eq_or_ne w 0 with rfl | hw0
    · simp at hne
    · exact pow_pos (norm_pos_iff.mpr hw0) 2
  have hIneq : ∀ K : ℕ,
      (∑ j ∈ Finset.Icc 1 K, (j : ℝ)⁻¹) * ‖inner ℂ x w‖
        ≤ Real.sqrt (sliceFormVal μG ρ hN2 hρcont hN β
            hpos x)
          * Real.sqrt ((∑ j ∈ Finset.Icc 1 K, (j : ℝ)⁻¹)
            * ‖w‖ ^ 2) := by
    intro K
    calc (∑ j ∈ Finset.Icc 1 K, (j : ℝ)⁻¹)
          * ‖inner ℂ x w‖
        = ‖sliceApproxB μG ρ hN2 hρcont hN β hpos K
            x w‖ := by
          rw [sliceApproxB_apply_ker μG ρ hN2 hρcont hN
            β hpos K x w hw, norm_mul, sliceHarmonicSum_norm]
      _ ≤ Real.sqrt (sliceHamFormApproxC μG ρ hN2
            hρcont hN β hpos K x)
          * Real.sqrt (sliceHamFormApproxC μG ρ hN2
            hρcont hN β hpos K w) :=
          sliceApproxB_norm_le μG ρ hN2 hρcont hN β hpos
            K x w
      _ ≤ Real.sqrt (sliceFormVal μG ρ hN2 hρcont hN β
            hpos x)
          * Real.sqrt ((∑ j ∈ Finset.Icc 1 K, (j : ℝ)⁻¹)
            * ‖w‖ ^ 2) := by
          rw [sliceHamFormApproxC_apply_ker μG ρ hN2
            hρcont hN β hpos K hw]
          exact mul_le_mul
            (Real.sqrt_le_sqrt (sliceApproxC_le_formVal
              μG ρ hN2 hρcont hN β hpos x hx K)) le_rfl
            (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  exact sliceHarmonic_contradiction_aux hc hd
    (sliceFormVal_nonneg μG ρ hN2 hρcont hN β hpos x)
    hIneq

/-- **The weld interface clause, on the completion:**
the first approximant at an embedded quotient vector is
the weld's norm defect `‖x‖² − ‖W x‖²`. -/
theorem sliceHamFormApproxC_one_embed_weld (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (x : sliceQuotient μG ρ hN2 hρcont hN β hpos) :
    sliceHamFormApproxC μG ρ hN2 hρcont hN β hpos 1
        (sliceEmbed μG ρ hN2 hρcont hN β hpos x)
      = ‖x‖ ^ 2 - ‖sliceWeldMap μG ρ hN2 hρcont hN β hpos
          x‖ ^ 2 := by
  rw [sliceHamFormApproxC_embed, ← sliceEnergyForm_one_eq,
    sliceEnergyForm_one_eq_weldNorm]

/-- **At `β = 0` the form domain is the whole space:**
the form vanishes identically there (the landed
`sliceHamFormC_beta_zero`), so the boundedness locus
is everything. -/
theorem sliceFormDomain_beta_zero_top (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (hd : 0 < d)
    (x : sliceHilbertSpace μG ρ hN2 hρcont hN 0
      (sliceHPosOne_zero μG ρ hN2 hρcont hN hd)) :
    x ∈ sliceHamFormDomainC μG ρ hN2 hρcont hN 0
      (sliceHPosOne_zero μG ρ hN2 hρcont hN hd) := by
  rw [sliceHamC_mem_domain_iff,
    sliceHamFormC_beta_zero μG ρ hN2 hρcont hN hd x]
  exact ENNReal.zero_ne_top

/-- **Density at `β = 0`:** the inclusion of the form
domain is surjective — hence of dense range — because
the domain is the whole space. This is the one density
clause the record supports. -/
theorem sliceFormInclusion_beta_zero_surjective
    (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (hd : 0 < d) :
    Function.Surjective
      (fun x : ↥(sliceHamFormDomainC μG ρ hN2 hρcont hN 0
          (sliceHPosOne_zero μG ρ hN2 hρcont hN hd)) =>
        (x : sliceHilbertSpace μG ρ hN2 hρcont hN 0
          (sliceHPosOne_zero μG ρ hN2 hρcont hN hd))) :=
  fun y => ⟨⟨y, sliceFormDomain_beta_zero_top μG ρ hN2
    hρcont hN hd y⟩, rfl⟩

theorem sliceFormInclusion_beta_zero_denseRange
    (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (hd : 0 < d) :
    DenseRange
      (fun x : ↥(sliceHamFormDomainC μG ρ hN2 hρcont hN 0
          (sliceHPosOne_zero μG ρ hN2 hρcont hN hd)) =>
        (x : sliceHilbertSpace μG ρ hN2 hρcont hN 0
          (sliceHPosOne_zero μG ρ hN2 hρcont hN hd))) :=
  (sliceFormInclusion_beta_zero_surjective μG ρ hN2
    hρcont hN hd).denseRange

/-- **FG-2a CLOSEDNESS PACKAGE.** What this brick
proves, bundled at the standing generality (general
`(G, ρ)`, every real `β`, under exactly
`SliceHPosOne`): (1) the form domain with the form
inner product is complete — `sliceHamFormC` is a
closed form; (2) the inclusion into the completed
space is continuous with bound `1`; (3) the density
obstruction: the domain lies inside `(ker T̂_c)⊥`;
(4) the weld clause `Q₁ = ‖x‖² − ‖W x‖²` on embedded
quotient vectors. Dense range in the ambient space is
*not* a clause of this package: clause (3) is its
proved obstruction. -/
def sliceFormClosedPackage (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (hd : 0 < d) :
    Prop :=
  CompleteSpace (sliceFormDomain μG ρ hN2 hρcont hN β
      hpos)
    ∧ (∀ x : sliceFormDomain μG ρ hN2 hρcont hN β hpos,
        ‖x.val‖ ≤ ‖x‖)
    ∧ (∀ (x : sliceHilbertSpace μG ρ hN2 hρcont hN β
        hpos), x ∈ sliceHamFormDomainC μG ρ hN2 hρcont
          hN β hpos →
        ∀ (w : sliceHilbertSpace μG ρ hN2 hρcont hN β
          hpos), sliceHatCompleted μG ρ hN2 hρcont hN β
            hpos w = 0 → inner ℂ x w = 0)
    ∧ (∀ x : sliceQuotient μG ρ hN2 hρcont hN β hpos,
        sliceHamFormApproxC μG ρ hN2 hρcont hN β hpos 1
            (sliceEmbed μG ρ hN2 hρcont hN β hpos x)
          = ‖x‖ ^ 2 - ‖sliceWeldMap μG ρ hN2 hρcont hN β
              hpos x‖ ^ 2)

theorem sliceFormClosed_package (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (hd : 0 < d) :
    sliceFormClosedPackage μG ρ hN2 hρcont hN β hpos
      hd :=
  ⟨sliceFormDomainCompleteSpace μG ρ hN2 hρcont hN β
      hpos,
    sliceFormDomain_val_norm_le μG ρ hN2 hρcont hN β
      hpos,
    fun x hx w hw => sliceFormDomain_orthogonal_ker μG ρ
      hN2 hρcont hN β hpos hx hw,
    fun x => sliceHamFormApproxC_one_embed_weld μG ρ hN2
      hρcont hN β hpos x⟩

/-- The package at the U(1) seat: hypothesis-free in
`β ≥ 0`. -/
theorem sliceFormClosed_circle_package (hN2 : 2 ≤ N)
    (hN : Even N) (β : ℝ) (hβ : 0 ≤ β) :
    sliceFormClosedPackage (haarProb Circle) circleRep
      hN2 circleRep_continuous hN β
      (sliceHPosOne_circle hN2 hN β hβ) zero_lt_one :=
  sliceFormClosed_package (haarProb Circle) circleRep
    hN2 circleRep_continuous hN β
    (sliceHPosOne_circle hN2 hN β hβ) zero_lt_one

/-- **The `β = 0` package:** domain = whole space and
the inclusion of the *carrier subtype* is surjective
(dense range). Note the subtype here is `↥D` itself,
not the form-norm synonym: at `β = 0` the form is
zero, so the two inclusions agree as sets of vectors;
the form-norm statement is the general package at
`β = 0`, `hpos = sliceHPosOne_zero`. -/
def sliceFormClosedBetaZeroPackage (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (hd : 0 < d) : Prop :=
  (∀ x : sliceHilbertSpace μG ρ hN2 hρcont hN 0
      (sliceHPosOne_zero μG ρ hN2 hρcont hN hd),
    x ∈ sliceHamFormDomainC μG ρ hN2 hρcont hN 0
      (sliceHPosOne_zero μG ρ hN2 hρcont hN hd))
    ∧ Function.Surjective
      (fun x : ↥(sliceHamFormDomainC μG ρ hN2 hρcont hN
          0 (sliceHPosOne_zero μG ρ hN2 hρcont hN hd)) =>
        (x : sliceHilbertSpace μG ρ hN2 hρcont hN 0
          (sliceHPosOne_zero μG ρ hN2 hρcont hN hd)))

theorem sliceFormClosed_beta_zero_package (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (hd : 0 < d) :
    sliceFormClosedBetaZeroPackage μG ρ hN2 hρcont hN
      hd :=
  ⟨fun x => sliceFormDomain_beta_zero_top μG ρ hN2
      hρcont hN hd x,
    sliceFormInclusion_beta_zero_surjective μG ρ hN2
      hρcont hN hd⟩

end SliceFormClosed

end ThetLogos
