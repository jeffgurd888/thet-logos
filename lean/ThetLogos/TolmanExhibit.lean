import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import ThetLogos.TolmanExhibitPin

namespace ThetLogos

/-!
# ThetLogos.TolmanExhibit — the finite Tolman exhibit (working label)

Content module for the pin `TolmanExhibitPin` (frozen names and forms).
Commission: Jeff, *"fire that exactly as stated"* (2026-11-07 13:01
EST) and *"Fire the Tolman exhibit"* (2026-11-07 13:09 EST), on the
priced menu of
`~/workspace/your_files/tolman-exhibit-scoping-2026-11-07.md`.
**Price: 14–19 strict, pre-registered DIAL-INELIGIBLE. NO CLAIM.
Dials 0/4. Dial 2 = 0.**

## What stands here

The entropy-maximization form of the finite Tolman argument (the
pin's §What this seat is). Equilibrium is *defined* as entropy
maximality at fixed site-weighted occupation sum; the theorems derive
its characterization. Components, in the scoping's order:

1. **Slope package** — `occEnt` differentiates to `occSlope`
   (`hasDerivAt_occEnt`); the slope's sign is the half-occupation
   comparison (`occSlope_pos_iff`, `occSlope_neg_iff`,
   `occSlope_eq_zero_iff`).
2. **Tangent bound** — the KL tangent bound and its strict form
   (`occEnt_tangent_identity`, `occEnt_le_tangent`,
   `occEnt_lt_tangent`): the graph of `occEnt` lies strictly below
   its tangents. Technique: `FiniteEntropy`'s deficit route
   (`Real.log_le_sub_one_of_pos`), citation-grade method reuse,
   named here per the pin's K-TOL-DUP assessment.
3. **Transfer derivative** — `hasDerivAt_occEnt_transfer`: the
   derivative of a two-site conserved-quantity-preserving transfer.
4. **Forward** — `exists_slope_condition_of_equilibrium`: at an
   equilibrium the transfer derivative vanishes at every pair of
   sites (Fermat), giving the slope condition with one global `λ`.
5. **Converse** — `equilibrium_of_slope_condition`: the slope
   condition implies maximality, by the summed tangent bound.
6. **Packaged characterization** — `tolman_characterization` proves
   the pin's form (1) verbatim.
7. **Product, λ = 0 fence, regimes** — `tolman_product`,
   `tolman_lambda_zero`, `tolman_regimes` prove forms (2), (3), (4)
   verbatim.
8. **Non-vacuity witnesses** — `tolman_witnesses` proves form (5):
   on `Fin 2` with site factor `(1, 2)`, `(1/4, 1/4)` is certified
   NOT an equilibrium and `(1/4, 1/10)` IS one, with both products
   equal to `(log 3)⁻¹`.
9. **The TE fence** — `tolman_te_fence` proves form (6): `θ ≡ 1` is
   a TE equilibrium whose `θ · a` products for `a = (1, 2)` are the
   distinct values `1` and `2` — the literal TE reading of the
   Tolman shape is false at the corpus's own landed seat, and the
   negative stands proved beside the exhibit.

## Faces

- **K-TOL-PROXY — DOES NOT FIRE.** The site factor `a` is a bare
  positive site weight inside a conserved sum in every statement;
  it is never named or treated as a metric, a metric component, or
  a redshift factor; those tokens occur in no statement, definition,
  or theorem name in this package.
- **K-TOL-FIAT — DOES NOT FIRE.** Equilibrium is entropy maximality
  by definition; the slope condition and the product are derived
  (components 4–7), never postulated.
- **K-TOL-VAC — DOES NOT FIRE.** The characterization is an iff, and
  form (5) certifies a named configuration NOT an equilibrium and a
  named one an equilibrium, with the products computed.
- The weight `a` decreases nowhere and is derived from nothing: it
  is the exhibit's fixed datum, and `localTemp` is a reciprocal
  slope. There is no metric, no gravity object, and no prediction
  in this module. **Pre-registered DIAL-INELIGIBLE; Dial 2 = 0.**
-/

variable {V : Type*} [Fintype V]

/-- **Component 1 (derivative):** the site entropy `occEnt`
differentiates to the slope `occSlope` at every interior point.
Assembly of Mathlib's `Real.hasDerivAt_mul_log` under the two
reflections `t ↦ t` and `t ↦ 1 − t`. Tier T1. -/
theorem hasDerivAt_occEnt {t : ℝ} (ht0 : t ≠ 0) (ht1 : (1 - t) ≠ 0) :
    HasDerivAt occEnt (occSlope t) t := by
  have h1 : HasDerivAt (fun u : ℝ => u * Real.log u) (Real.log t + 1) t :=
    Real.hasDerivAt_mul_log ht0
  have h2 : HasDerivAt (fun u : ℝ => (1 - u) * Real.log (1 - u))
      (-(Real.log (1 - t) + 1)) t := by
    have hcomp := (Real.hasDerivAt_mul_log ht1).comp t
      ((hasDerivAt_id t).const_sub (1 : ℝ))
    convert hcomp using 1
    · ext u
      rfl
    · ring
  have h := h1.neg.sub h2
  convert h using 1
  · ext u
    simp only [occEnt, Pi.sub_apply, Pi.neg_apply]
    ring
  · simp only [occSlope]
    ring

/-- **Component 1 (sign package):** at an interior occupation, the
slope vanishes iff the occupation is exactly `1/2` — the
infinite-temperature configuration of the pin's form (3). Tier T1. -/
theorem occSlope_eq_zero_iff {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    occSlope t = 0 ↔ t = 1 / 2 := by
  have h1t : (0 : ℝ) < 1 - t := by linarith
  constructor
  · intro h
    have hlog : Real.log (1 - t) = Real.log t :=
      sub_eq_zero.mp (show Real.log (1 - t) - Real.log t = 0 from h)
    have harg := Real.log_injOn_pos (Set.mem_Ioi.mpr h1t)
      (Set.mem_Ioi.mpr ht0) hlog
    linarith
  · intro h
    have e : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
    rw [h]
    show Real.log (1 - 1 / 2) - Real.log (1 / 2) = 0
    rw [e, sub_self]

/-- **Component 1 (sign package):** at an interior occupation, the
slope is positive iff the occupation is below `1/2` — the positive
local temperature side of the pin's form (4). Tier T1. -/
theorem occSlope_pos_iff {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    0 < occSlope t ↔ t < 1 / 2 := by
  have h1t : (0 : ℝ) < 1 - t := by linarith
  have hlog : (Real.log t < Real.log (1 - t)) ↔ t < 1 - t :=
    Real.log_lt_log_iff ht0 h1t
  show (0 : ℝ) < Real.log (1 - t) - Real.log t ↔ t < 1 / 2
  constructor
  · intro h
    have h' : Real.log t < Real.log (1 - t) := by linarith
    have := hlog.mp h'
    linarith
  · intro h
    have h' : t < 1 - t := by linarith
    have := hlog.mpr h'
    linarith

/-- **Component 1 (sign package):** at an interior occupation, the
slope is negative iff the occupation is past `1/2` — the signed
local temperature side of the pin's form (4). Tier T1. -/
theorem occSlope_neg_iff {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    occSlope t < 0 ↔ 1 / 2 < t := by
  have h1t : (0 : ℝ) < 1 - t := by linarith
  have hlog : (Real.log (1 - t) < Real.log t) ↔ 1 - t < t :=
    Real.log_lt_log_iff h1t ht0
  show Real.log (1 - t) - Real.log t < 0 ↔ 1 / 2 < t
  constructor
  · intro h
    have h' : Real.log (1 - t) < Real.log t := by linarith
    have := hlog.mp h'
    linarith
  · intro h
    have h' : 1 - t < t := by linarith
    have := hlog.mpr h'
    linarith

/-- **Component 2 (the KL identity):** the tangent deficit of
`occEnt` at `x`, evaluated at `y`, is exactly the two-term
Kullback–Leibler form `y·log(y/x) + (1−y)·log((1−y)/(1−x))`. Pure
algebra of `Real.log_div` at interior points. Tier T1. -/
theorem occEnt_tangent_identity {x y : ℝ} (hx0 : 0 < x) (hx1 : x < 1)
    (hy0 : 0 < y) (hy1 : y < 1) :
    occEnt x + occSlope x * (y - x) - occEnt y
      = y * Real.log (y / x) + (1 - y) * Real.log ((1 - y) / (1 - x)) := by
  have hx1' : (0 : ℝ) < 1 - x := by linarith
  have hy1' : (0 : ℝ) < 1 - y := by linarith
  rw [Real.log_div (ne_of_gt hy0) (ne_of_gt hx0),
    Real.log_div (ne_of_gt hy1') (ne_of_gt hx1')]
  simp only [occEnt, occSlope]
  ring

/-- **Component 2 (tangent bound):** the graph of `occEnt` lies
below its tangent at every interior point — the one-variable heart
of the converse (component 5). Proved from the KL identity by
`FiniteEntropy`'s deficit route: `Real.log_le_sub_one_of_pos`
applied at the ratios `x/y` and `(1−x)/(1−y)`. Tier T1. -/
theorem occEnt_le_tangent {x y : ℝ} (hx0 : 0 < x) (hx1 : x < 1)
    (hy0 : 0 < y) (hy1 : y < 1) :
    occEnt y ≤ occEnt x + occSlope x * (y - x) := by
  have hx1' : (0 : ℝ) < 1 - x := by linarith
  have hy1' : (0 : ℝ) < 1 - y := by linarith
  have hy0' : y ≠ 0 := ne_of_gt hy0
  have hy1'' : (1 - y) ≠ 0 := ne_of_gt hy1'
  have hid := occEnt_tangent_identity hx0 hx1 hy0 hy1
  rw [Real.log_div (ne_of_gt hy0) (ne_of_gt hx0),
    Real.log_div (ne_of_gt hy1') (ne_of_gt hx1')] at hid
  have hlog1 : Real.log x - Real.log y ≤ x / y - 1 := by
    have h := Real.log_le_sub_one_of_pos (div_pos hx0 hy0)
    rwa [Real.log_div (ne_of_gt hx0) (ne_of_gt hy0)] at h
  have hlog2 : Real.log (1 - x) - Real.log (1 - y)
      ≤ (1 - x) / (1 - y) - 1 := by
    have h := Real.log_le_sub_one_of_pos (div_pos hx1' hy1')
    rwa [Real.log_div (ne_of_gt hx1') (ne_of_gt hy1')] at h
  have b1 : y - x ≤ y * (Real.log y - Real.log x) := by
    have hmul := mul_le_mul_of_nonneg_left hlog1 hy0.le
    have hval : y * (x / y - 1) = x - y := by
      field_simp
    linarith
  have b2 : x - y ≤ (1 - y) * (Real.log (1 - y) - Real.log (1 - x)) := by
    have hmul := mul_le_mul_of_nonneg_left hlog2 hy1'.le
    have hval : (1 - y) * ((1 - x) / (1 - y) - 1) = y - x := by
      field_simp
      ring
    linarith
  linarith [hid, b1, b2]

/-- **Component 2 (strict tangent bound):** off the point of
tangency the bound is strict — the deficit route's strict form
(`Real.log_lt_sub_one_of_pos`) fires on whichever ratio differs
from `1`. Tier T1. -/
theorem occEnt_lt_tangent {x y : ℝ} (hx0 : 0 < x) (hx1 : x < 1)
    (hy0 : 0 < y) (hy1 : y < 1) (hxy : y ≠ x) :
    occEnt y < occEnt x + occSlope x * (y - x) := by
  have hx1' : (0 : ℝ) < 1 - x := by linarith
  have hy1' : (0 : ℝ) < 1 - y := by linarith
  have hy0' : y ≠ 0 := ne_of_gt hy0
  have hy1'' : (1 - y) ≠ 0 := ne_of_gt hy1'
  have hid := occEnt_tangent_identity hx0 hx1 hy0 hy1
  rw [Real.log_div (ne_of_gt hy0) (ne_of_gt hx0),
    Real.log_div (ne_of_gt hy1') (ne_of_gt hx1')] at hid
  have hlog1 : Real.log x - Real.log y ≤ x / y - 1 := by
    have h := Real.log_le_sub_one_of_pos (div_pos hx0 hy0)
    rwa [Real.log_div (ne_of_gt hx0) (ne_of_gt hy0)] at h
  have hlog2 : Real.log (1 - x) - Real.log (1 - y)
      ≤ (1 - x) / (1 - y) - 1 := by
    have h := Real.log_le_sub_one_of_pos (div_pos hx1' hy1')
    rwa [Real.log_div (ne_of_gt hx1') (ne_of_gt hy1')] at h
  have b1 : y - x ≤ y * (Real.log y - Real.log x) := by
    have hmul := mul_le_mul_of_nonneg_left hlog1 hy0.le
    have hval : y * (x / y - 1) = x - y := by
      field_simp
    linarith
  have b2 : x - y ≤ (1 - y) * (Real.log (1 - y) - Real.log (1 - x)) := by
    have hmul := mul_le_mul_of_nonneg_left hlog2 hy1'.le
    have hval : (1 - y) * ((1 - x) / (1 - y) - 1) = y - x := by
      field_simp
      ring
    linarith
  rcases lt_or_gt_of_ne hxy with hlt | hgt
  · -- `y < x`: the ratio `(1−x)/(1−y)` is `< 1`, so its log bound is strict.
    have hlog2s : Real.log (1 - x) - Real.log (1 - y)
        < (1 - x) / (1 - y) - 1 := by
      have hlt1 : (1 - x) / (1 - y) < 1 :=
        (div_lt_one hy1').mpr (by linarith)
      have h := Real.log_lt_sub_one_of_pos (div_pos hx1' hy1')
        (ne_of_lt hlt1)
      rwa [Real.log_div (ne_of_gt hx1') (ne_of_gt hy1')] at h
    have b2s : x - y < (1 - y) * (Real.log (1 - y) - Real.log (1 - x)) := by
      have hmul := mul_lt_mul_of_pos_left hlog2s hy1'
      have hval : (1 - y) * ((1 - x) / (1 - y) - 1) = y - x := by
        field_simp
        ring
      linarith
    linarith [hid, b1, b2s]
  · -- `x < y`: the ratio `x/y` is `< 1`, so its log bound is strict.
    have hlog1s : Real.log x - Real.log y < x / y - 1 := by
      have hlt1 : x / y < 1 := (div_lt_one hy0).mpr hgt
      have h := Real.log_lt_sub_one_of_pos (div_pos hx0 hy0)
        (ne_of_lt hlt1)
      rwa [Real.log_div (ne_of_gt hx0) (ne_of_gt hy0)] at h
    have b1s : y - x < y * (Real.log y - Real.log x) := by
      have hmul := mul_lt_mul_of_pos_left hlog1s hy0
      have hval : y * (x / y - 1) = x - y := by
        field_simp
      linarith
    linarith [hid, b1s, b2]

/-- **Component 3 (transfer derivative):** the two-site transfer
`t ↦ (x₀ j − t/a j, x₀ k + t/a k)` — which preserves the conserved
quantity `occWeightedSum a` exactly — has entropy derivative
`occSlope (x₀ k)/a k − occSlope (x₀ j)/a j` at `t = 0`. Tier T1. -/
theorem hasDerivAt_occEnt_transfer {x₀ a : V → ℝ} {j k : V}
    (hxj0 : 0 < x₀ j) (hxj1 : x₀ j < 1) (hxk0 : 0 < x₀ k)
    (hxk1 : x₀ k < 1) (haj : a j ≠ 0) (hak : a k ≠ 0) :
    HasDerivAt (fun t : ℝ => occEnt (x₀ j - t / a j)
        + occEnt (x₀ k + t / a k))
      (occSlope (x₀ k) / a k - occSlope (x₀ j) / a j) 0 := by
  have hg1 : HasDerivAt (fun t : ℝ => x₀ j - t / a j) (-(1 / a j)) 0 :=
    ((hasDerivAt_id (0 : ℝ)).div_const (a j)).const_sub (x₀ j)
  have hg2 : HasDerivAt (fun t : ℝ => x₀ k + t / a k) (1 / a k) 0 :=
    ((hasDerivAt_id (0 : ℝ)).div_const (a k)).const_add (x₀ k)
  have hne_j1 : (x₀ j - 0 / a j) ≠ 0 := by simpa using ne_of_gt hxj0
  have hne_j2 : (1 - (x₀ j - 0 / a j)) ≠ 0 := by
    have h : (0 : ℝ) < 1 - x₀ j := by linarith
    simpa using ne_of_gt h
  have hne_k1 : (x₀ k + 0 / a k) ≠ 0 := by simpa using ne_of_gt hxk0
  have hne_k2 : (1 - (x₀ k + 0 / a k)) ≠ 0 := by
    have h : (0 : ℝ) < 1 - x₀ k := by linarith
    simpa using ne_of_gt h
  have h1 := (hasDerivAt_occEnt hne_j1 hne_j2).comp (0 : ℝ) hg1
  have h2 := (hasDerivAt_occEnt hne_k1 hne_k2).comp (0 : ℝ) hg2
  have hadd := h1.add h2
  convert hadd using 1
  · ext t
    rfl
  · simp only [zero_div, sub_zero, add_zero, div_eq_mul_inv]
    ring

/-- **Component 4 (forward):** at an equilibrium for a positive site
factor, the slope condition holds with one global `λ`. Proof: at any
two sites the conserved-quantity-preserving transfer has a local
maximum at `t = 0` (the perturbed configuration is interior for
small `|t|`, keeps the same weighted sum, and so cannot beat the
equilibrium), so Fermat's theorem
(`IsLocalMax.hasDerivAt_eq_zero`) kills its derivative; the pairwise
ratio equalities assemble into one `λ` from any base site. Tier T1. -/
theorem exists_slope_condition_of_equilibrium {a x₀ : V → ℝ}
    (ha : ∀ i, 0 < a i) (hx₀ : IsTolmanEquilibrium a x₀) :
    ∃ lam : ℝ, ∀ i, occSlope (x₀ i) = lam * a i := by
  classical
  have key : ∀ j k : V, j ≠ k →
      occSlope (x₀ k) / a k - occSlope (x₀ j) / a j = 0 := by
    intro j k hjk
    have hj := hx₀.1 j
    have hk := hx₀.1 k
    have haj : a j ≠ 0 := ne_of_gt (ha j)
    have hak : a k ≠ 0 := ne_of_gt (ha k)
    have hsplit : ∀ (F G : V → ℝ), (∀ i, i ≠ j → i ≠ k → F i = G i) →
        (∑ i, F i) = (∑ i, G i) + (F j - G j) + (F k - G k) := by
      intro F G hFG
      have hcompl : (∑ i ∈ ({j, k} : Finset V)ᶜ, F i)
          = ∑ i ∈ ({j, k} : Finset V)ᶜ, G i := by
        refine Finset.sum_congr rfl fun i hi => ?_
        have hni := Finset.mem_compl.mp hi
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          at hni
        exact hFG i hni.1 hni.2
      have hsum : ∀ H : V → ℝ, (∑ i, H i)
          = (∑ i ∈ ({j, k} : Finset V), H i)
            + ∑ i ∈ ({j, k} : Finset V)ᶜ, H i :=
        fun H => (Finset.sum_add_sum_compl ({j, k} : Finset V)
          (fun i => H i)).symm
      rw [hsum F, hsum G, hcompl, Finset.sum_pair hjk,
        Finset.sum_pair hjk]
      ring
    have hderiv := hasDerivAt_occEnt_transfer (x₀ := x₀) (a := a)
      (j := j) (k := k) hj.1 hj.2 hk.1 hk.2 haj hak
    have hmax : IsLocalMax
        (fun t : ℝ => occEnt (x₀ j - t / a j)
          + occEnt (x₀ k + t / a k)) 0 := by
      refine Metric.eventually_nhds_iff.mpr
        ⟨min (min (x₀ j * a j) ((1 - x₀ j) * a j))
            (min (x₀ k * a k) ((1 - x₀ k) * a k)),
          lt_min (lt_min (mul_pos hj.1 (ha j))
              (mul_pos (by linarith) (ha j)))
            (lt_min (mul_pos hk.1 (ha k))
              (mul_pos (by linarith) (ha k))), ?_⟩
      intro t ht
      rw [Real.dist_eq, sub_zero] at ht
      have hbj1 : |t| / a j < x₀ j := (div_lt_iff₀ (ha j)).mpr
        (lt_of_lt_of_le ht (le_trans (min_le_left _ _) (min_le_left _ _)))
      have hbj2 : |t| / a j < 1 - x₀ j := (div_lt_iff₀ (ha j)).mpr
        (lt_of_lt_of_le ht
          (le_trans (min_le_left _ _) (min_le_right _ _)))
      have hbk1 : |t| / a k < x₀ k := (div_lt_iff₀ (ha k)).mpr
        (lt_of_lt_of_le ht
          (le_trans (min_le_right _ _) (min_le_left _ _)))
      have hbk2 : |t| / a k < 1 - x₀ k := (div_lt_iff₀ (ha k)).mpr
        (lt_of_lt_of_le ht
          (le_trans (min_le_right _ _) (min_le_right _ _)))
      have hle_j : t / a j ≤ |t| / a j :=
        (div_le_div_iff_of_pos_right (ha j)).mpr (le_abs_self t)
      have hge_j : -(t / a j) ≤ |t| / a j := by
        rw [← neg_div]
        exact (div_le_div_iff_of_pos_right (ha j)).mpr (neg_le_abs t)
      have hle_k : t / a k ≤ |t| / a k :=
        (div_le_div_iff_of_pos_right (ha k)).mpr (le_abs_self t)
      have hge_k : -(t / a k) ≤ |t| / a k := by
        rw [← neg_div]
        exact (div_le_div_iff_of_pos_right (ha k)).mpr (neg_le_abs t)
      set x' : V → ℝ := Function.update
        (Function.update x₀ j (x₀ j - t / a j)) k (x₀ k + t / a k)
        with hx'def
      have hx'j : x' j = x₀ j - t / a j := by
        simp only [hx'def, Function.update_of_ne hjk,
          Function.update_self]
      have hx'k : x' k = x₀ k + t / a k := by
        simp only [hx'def, Function.update_self]
      have hx'oth : ∀ i, i ≠ j → i ≠ k → x' i = x₀ i := by
        intro i hij hik
        simp only [hx'def, Function.update_of_ne hik,
          Function.update_of_ne hij]
      have hx'int : ∀ i, 0 < x' i ∧ x' i < 1 := by
        intro i
        by_cases hij : i = j
        · subst hij
          rw [hx'j]
          constructor <;> linarith [hbj1, hbj2, hle_j, hge_j]
        · by_cases hik : i = k
          · subst hik
            rw [hx'k]
            constructor <;> linarith [hbk1, hbk2, hle_k, hge_k]
          · rw [hx'oth i hij hik]
            exact hx₀.1 i
      have hspA : (∑ i, a i * x' i) = (∑ i, a i * x₀ i)
          + (a j * x' j - a j * x₀ j) + (a k * x' k - a k * x₀ k) :=
        hsplit (fun i => a i * x' i) (fun i => a i * x₀ i)
          (fun i hij hik => by
            show a i * x' i = a i * x₀ i
            rw [hx'oth i hij hik])
      have hA : occWeightedSum a x' = occWeightedSum a x₀ := by
        have e1 : a j * (x₀ j - t / a j) - a j * x₀ j = -t := by
          field_simp
          ring
        have e2 : a k * (x₀ k + t / a k) - a k * x₀ k = t := by
          field_simp
          ring
        rw [hx'j, hx'k, e1, e2] at hspA
        show (∑ i, a i * x' i) = ∑ i, a i * x₀ i
        linarith [hspA]
      have hle : (∑ i, occEnt (x' i)) ≤ ∑ i, occEnt (x₀ i) :=
        hx₀.2 x' hx'int hA
      have hsp : (∑ i, occEnt (x' i)) = (∑ i, occEnt (x₀ i))
          + (occEnt (x' j) - occEnt (x₀ j))
          + (occEnt (x' k) - occEnt (x₀ k)) :=
        hsplit (fun i => occEnt (x' i)) (fun i => occEnt (x₀ i))
          (fun i hij hik => by
            show occEnt (x' i) = occEnt (x₀ i)
            rw [hx'oth i hij hik])
      rw [hx'j, hx'k] at hsp
      show occEnt (x₀ j - t / a j) + occEnt (x₀ k + t / a k)
        ≤ occEnt (x₀ j - 0 / a j) + occEnt (x₀ k + 0 / a k)
      simp only [zero_div, sub_zero, add_zero]
      linarith [hsp, hle]
    exact IsLocalMax.hasDerivAt_eq_zero hmax hderiv
  rcases isEmpty_or_nonempty V with hE | hNE
  · refine ⟨0, fun i => ?_⟩
    haveI := hE
    exact (IsEmpty.false i).elim
  · obtain ⟨j₀⟩ := hNE
    refine ⟨occSlope (x₀ j₀) / a j₀, fun i => ?_⟩
    by_cases hi : i = j₀
    · subst hi
      exact (div_mul_cancel₀ _ (ne_of_gt (ha i))).symm
    · have hratio : occSlope (x₀ i) / a i
          = occSlope (x₀ j₀) / a j₀ :=
        sub_eq_zero.mp (key j₀ i (Ne.symm hi))
      calc occSlope (x₀ i)
          = occSlope (x₀ i) / a i * a i :=
            (div_mul_cancel₀ _ (ne_of_gt (ha i))).symm
        _ = occSlope (x₀ j₀) / a j₀ * a i := by rw [hratio]

/-- **Component 5 (converse):** the slope condition implies
equilibrium. Proof: sum the tangent bound
(`occEnt_le_tangent`) over all sites; the summed correction term
is `λ` times the difference of the conserved quantities, which
vanishes at fixed `occWeightedSum a`. Tier T1. -/
theorem equilibrium_of_slope_condition {a x₀ : V → ℝ}
    (ha : ∀ i, 0 < a i) (hx₀ : ∀ i, 0 < x₀ i ∧ x₀ i < 1) (lam : ℝ)
    (hlam : ∀ i, occSlope (x₀ i) = lam * a i) :
    IsTolmanEquilibrium a x₀ := by
  refine ⟨hx₀, fun x hx hA => ?_⟩
  have h1 : occEntSum x
      ≤ occEntSum x₀ + ∑ i, occSlope (x₀ i) * (x i - x₀ i) := by
    have h := Finset.sum_le_sum (s := Finset.univ)
      (f := fun i => occEnt (x i))
      (g := fun i => occEnt (x₀ i) + occSlope (x₀ i) * (x i - x₀ i))
      (fun i _ => occEnt_le_tangent (hx₀ i).1 (hx₀ i).2 (hx i).1
        (hx i).2)
    rwa [Finset.sum_add_distrib] at h
  have hzero : (∑ i, occSlope (x₀ i) * (x i - x₀ i)) = 0 := by
    have hterm : ∀ i, occSlope (x₀ i) * (x i - x₀ i)
        = lam * (a i * x i - a i * x₀ i) := by
      intro i
      rw [hlam i]
      ring
    calc (∑ i, occSlope (x₀ i) * (x i - x₀ i))
        = ∑ i, lam * (a i * x i - a i * x₀ i) :=
          Finset.sum_congr rfl (fun i _ => hterm i)
      _ = lam * ((∑ i, a i * x i) - ∑ i, a i * x₀ i) := by
          rw [← Finset.sum_sub_distrib, ← Finset.mul_sum]
      _ = 0 := by
          have hA' : (∑ i, a i * x i) = ∑ i, a i * x₀ i := hA
          rw [hA', sub_self, mul_zero]
  linarith [h1, hzero]

/-- **Component 6 (the characterization, the pin's form (1)
verbatim):** for a positive site factor, equilibrium ⟺ interior
together with the slope condition at one global `λ`. Forward is
component 4; converse is component 5. Tier T1. -/
theorem tolman_characterization : TolmanCharForm (V := V) := by
  intro a x₀ ha
  constructor
  · intro h
    exact ⟨h.1, exists_slope_condition_of_equilibrium ha h⟩
  · rintro ⟨hint, lam, hlam⟩
    exact equilibrium_of_slope_condition ha hint lam hlam

/-- **Component 7 (the product, the pin's form (2) verbatim):** at
an equilibrium with slope witness `λ ≠ 0`, the local temperature
factor times the site factor is the one global constant `λ⁻¹` at
every site — the Tolman-shaped product, as the characterization's
output. Pure algebra from the slope condition. Tier T1. -/
theorem tolman_product : TolmanProductForm (V := V) := by
  intro a x₀ lam ha hx₀ hlam hlam0 i
  have hai : a i ≠ 0 := ne_of_gt (ha i)
  show (occSlope (x₀ i))⁻¹ * a i = lam⁻¹
  calc (occSlope (x₀ i))⁻¹ * a i = (lam * a i)⁻¹ * a i := by
        rw [hlam i]
    _ = (a i)⁻¹ * lam⁻¹ * a i := by rw [mul_inv_rev]
    _ = lam⁻¹ * ((a i)⁻¹ * a i) := by ring
    _ = lam⁻¹ := by rw [inv_mul_cancel₀ hai, mul_one]

/-- **Component 7 (the λ = 0 fence, the pin's form (3) verbatim):**
slope zero at every site of an interior configuration forces
`x₀ ≡ 1/2` — the infinite-temperature configuration, at which the
product form is fenced off by its `λ ≠ 0` hypothesis. Tier T1. -/
theorem tolman_lambda_zero : TolmanLambdaZeroForm (V := V) := by
  intro a x₀ hint hslope i
  exact (occSlope_eq_zero_iff (hint i).1 (hint i).2).mp (hslope i)

/-- **Component 7 (the λ regimes, the pin's form (4) verbatim):**
a positive witness puts every equilibrium occupation below `1/2`
with positive local temperature; a negative witness puts every one
past `1/2` with signed (negative) local temperature — the
population-inversion side of the slope, stated as the mathematics'
own case split. Tier T1. -/
theorem tolman_regimes : TolmanRegimeForm (V := V) := by
  constructor
  · intro a x₀ lam ha hint hlam hlampos i
    have hsp : 0 < occSlope (x₀ i) := by
      rw [hlam i]
      exact mul_pos hlampos (ha i)
    refine ⟨(occSlope_pos_iff (hint i).1 (hint i).2).mp hsp, ?_⟩
    show 0 < (occSlope (x₀ i))⁻¹
    exact inv_pos.mpr hsp
  · intro a x₀ lam ha hint hlam hlamneg i
    have hsn : occSlope (x₀ i) < 0 := by
      rw [hlam i]
      exact mul_neg_of_neg_of_pos hlamneg (ha i)
    refine ⟨(occSlope_neg_iff (hint i).1 (hint i).2).mp hsn, ?_⟩
    show (occSlope (x₀ i))⁻¹ < 0
    exact inv_lt_zero'.mpr hsn

/-- **Component 8 (non-vacuity witnesses, the pin's form (5)
verbatim):** on `Fin 2` with site factor `(1, 2)`: `(1/4, 1/4)` is
NOT an equilibrium — the characterization would force one `λ` to
equal both `log 3` and `(log 3)/2` — while `(1/4, 1/10)` IS an
equilibrium (slope witness `λ = log 3`: the slopes are `log 3` and
`log 9 = 2·log 3`), with both products equal to `(log 3)⁻¹`.
K-TOL-VAC does not fire: the characterization is an iff with named
configurations certified on both sides. Tier T1. -/
theorem tolman_witnesses : TolmanWitnessForm := by
  have hs14 : occSlope (1 / 4 : ℝ) = Real.log 3 := by
    have e2 : (1 : ℝ) - 1 / 4 = 3 / 4 := by norm_num
    have e3 : (3 / 4 : ℝ) / (1 / 4) = 3 := by norm_num
    show Real.log (1 - 1 / 4) - Real.log (1 / 4) = Real.log 3
    rw [e2, ← Real.log_div (by norm_num) (by norm_num), e3]
  have hs110 : occSlope (1 / 10 : ℝ) = 2 * Real.log 3 := by
    have e2 : (1 : ℝ) - 1 / 10 = 9 / 10 := by norm_num
    have e3 : (9 / 10 : ℝ) / (1 / 10) = 9 := by norm_num
    have e4 : Real.log (9 : ℝ) = 2 * Real.log 3 := by
      have h9 : (9 : ℝ) = 3 ^ 2 := by norm_num
      rw [h9, Real.log_pow]
      norm_num
    show Real.log (1 - 1 / 10) - Real.log (1 / 10) = 2 * Real.log 3
    rw [e2, ← Real.log_div (by norm_num) (by norm_num), e3, e4]
  have ha2 : ∀ i : Fin 2, 0 < (![1, 2] : Fin 2 → ℝ) i := by
    rw [Fin.forall_fin_two]
    constructor <;>
      simp [Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons] <;> norm_num
  have hint : ∀ i : Fin 2, 0 < (![1 / 4, 1 / 10] : Fin 2 → ℝ) i
      ∧ (![1 / 4, 1 / 10] : Fin 2 → ℝ) i < 1 := by
    rw [Fin.forall_fin_two]
    constructor <;>
      simp [Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons] <;> norm_num
  have hslope : ∀ i : Fin 2,
      occSlope ((![1 / 4, 1 / 10] : Fin 2 → ℝ) i)
        = Real.log 3 * (![1, 2] : Fin 2 → ℝ) i := by
    rw [Fin.forall_fin_two]
    constructor
    · simp only [Matrix.cons_val_zero]
      rw [hs14, mul_one]
    · simp only [Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_zero]
      rw [hs110]
      ring
  have heq : IsTolmanEquilibrium (![1, 2] : Fin 2 → ℝ)
      (![1 / 4, 1 / 10] : Fin 2 → ℝ) :=
    equilibrium_of_slope_condition ha2 hint (Real.log 3) hslope
  refine ⟨?_, heq, ?_⟩
  · intro h
    have hchar := (tolman_characterization (V := Fin 2)
      (![1, 2] : Fin 2 → ℝ) (![1 / 4, 1 / 4] : Fin 2 → ℝ) ha2).mp h
    obtain ⟨-, lam, hlam⟩ := hchar
    have h0 := hlam 0
    have h1 := hlam 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons] at h0 h1
    rw [hs14, mul_one] at h0
    rw [hs14] at h1
    rw [← h0] at h1
    have hlog3 : (0 : ℝ) < Real.log 3 :=
      Real.log_pos (by norm_num)
    linarith [h1, hlog3]
  · exact tolman_product _ _ _ ha2 heq hslope
      (ne_of_gt (Real.log_pos (by norm_num)))

/-- **Component 9 (the TE fence, the pin's form (6) verbatim):** on
`Fin 2` with unit conductance, the constant field `θ ≡ 1` is a TE
equilibrium — its separated charge vanishes identically by the
landed `teCharge_eq_zero_of_forall_eq` — while its products
against the site factor `(1, 2)` are the distinct values `1` and
`2`. The literal TE reading of the Tolman shape is therefore
false at the corpus's own seat, and the negative stands proved
beside the exhibit (the scoping's §2 refutation, carried as a
corpus fact). Tier T1. -/
theorem tolman_te_fence : TolmanTEFenceForm := by
  constructor
  · funext i
    apply teCharge_eq_zero_of_forall_eq
    intro p q _
    rfl
  · norm_num [Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons]

end ThetLogos
