import Mathlib.Tactic
import ThetLogos.FiniteEntropy

/-!
# ThetLogos.SiteEntropyMap — the site-wise entropy map of a finite weight (T1)

HONESTY LEDGER (read before citing):

- Everything in this file is **T1 finite information bookkeeping**:
  a finite index type `κ`, finite local state types `X i`, a weight
  `w : (∀ i, X i) → ℝ` on the configuration space `(∀ i, X i)`, and
  the site-wise marginals `margWeight w i : X i → ℝ`. The entropy
  functional is consumed at its exact landed shape from
  `FiniteEntropy`: `entropyW w = -∑ i, w i * Real.log (w i)`. Zero
  sorrys, no new axioms (headline theorems checked against the
  standard three: `propext`, `Classical.choice`, `Quot.sound`).
- THE MAP. `siteEntropy w i = entropyW (margWeight w i)`: push the
  weight down to one site, take the entropy there. The map lives on
  whatever finite index type the weight lives on — `κ` is arbitrary.
  Jeff's "3D" in the originating assertion (thermal charge separation
  scoping dossier, 2026-11-04) is the seat's index shape: the lattice
  case `κ = Fin 3` — or a three-dimensional grid flattened to a
  finite `κ` — is a special case of what is stated. **No geometry is
  claimed**: no adjacency, no metric, no embedding of `κ` anywhere.
- WHAT IS PROVED. (i) Marginals of a probability weight are
  probability weights (`isProbWeight_margWeight`), so the map's
  basic bounds are exact consumptions of FiniteEntropy's:
  `0 ≤ siteEntropy w i` and
  `siteEntropy w i ≤ Real.log (Fintype.card (X i))`.
  (ii) **Additivity for product weights**: if the weight factors as
  a product of site weights, total entropy is the sum of the site
  entropies — at the weight level (`entropyW_siteProdWeight`), at
  the marginal level (`margWeight_siteProdWeight`: the marginal of a
  product weight is its own factor), and as the map identity
  (`entropyW_siteProdWeight_eq_sum_siteEntropy`).
  (iii) **Subadditivity in general**
  (`entropyW_le_sum_siteEntropy`): total entropy never exceeds the
  sum of the site entropies, proved by the pointwise Gibbs
  inequality `Real.log_le_sub_one_of_pos` against the product of the
  marginals (itself a product weight, by (ii)'s machinery).
- THE K-TCS-ENT GUARD, ON THE FACE. Additivity WITHOUT the product
  hypothesis is FALSE — pre-registered kill **K-TCS-ENT**. Witness
  (the scoping dossier's counterexample): two perfectly correlated
  sites, `w(0,0) = w(1,1) = 1/2`, `w(0,1) = w(1,0) = 0`. Each
  marginal is the fair bit, so each site entropy is `log 2` and the
  sum is `2 log 2`, but the total entropy is `log 2`. That is why
  this file states additivity only under the product hypothesis and
  subadditivity in general; the strictness gap in the correlated
  case is the mutual information, which is not named or measured
  here. K-TCS-ENT did not fire: the false form was never attempted.
- DETERMINATION LANGUAGE ONLY. This brick is T3 of the
  thermal-charge-separation scoping dossier (2026-11-04). The map is
  a *function of given data* (a weight); it is not a dynamics,
  nothing builds itself, and no equivalence between an entropy map
  and any geometric or spectral structure is stated — the
  assertion's equivalence and division components are NOT addressed
  here and appear only as this fence.
- SEP FENCES, STANDING (Jeff's SEP-0 ruling, 2026-10-31). β appears
  nowhere in this file: β is data elsewhere in the corpus and moves
  nothing by itself. No charge operator and no electromagnetic
  field object is claimed at any seat. NOT CLAIMED: thermodynamic
  entropy of any physical system, continuum information theory,
  self-organization. NO CLAIM; dials 0/4.
-/

namespace ThetLogos

variable {κ : Type*} [Fintype κ] [DecidableEq κ] {X : κ → Type*}
  [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]

/-! ## §1. Marginals -/

/-- The marginal weight of `w` at site `i`: the total weight of all
configurations whose `i`-th coordinate is `x`. -/
def margWeight (w : (∀ i, X i) → ℝ) (i : κ) : X i → ℝ :=
  fun x => ∑ y ∈ Finset.univ.filter (fun y => y i = x), w y

theorem margWeight_apply (w : (∀ i, X i) → ℝ) (i : κ) (x : X i) :
    margWeight w i x
      = ∑ y ∈ Finset.univ.filter (fun y => y i = x), w y := rfl

/-- The site entropy map: the entropy of the marginal at each site,
with `entropyW` consumed from `FiniteEntropy` at its exact shape. -/
noncomputable def siteEntropy (w : (∀ i, X i) → ℝ) (i : κ) : ℝ :=
  entropyW (margWeight w i)

/-- Marginals of a nonnegative weight are nonnegative. -/
theorem margWeight_nonneg (w : (∀ i, X i) → ℝ) (hw : ∀ y, 0 ≤ w y)
    (i : κ) (x : X i) : 0 ≤ margWeight w i x :=
  Finset.sum_nonneg (fun y _ => hw y)

/-- The total mass of a marginal is the total mass of the weight:
fibering the configuration sum over the `i`-th coordinate. -/
theorem sum_margWeight (w : (∀ i, X i) → ℝ) (i : κ) :
    ∑ x, margWeight w i x = ∑ y, w y := by
  have h := Finset.sum_fiberwise_of_maps_to
    (s := (Finset.univ : Finset (∀ i, X i)))
    (t := (Finset.univ : Finset (X i))) (g := fun y : (∀ i, X i) => y i)
    (f := w) (fun y _ => Finset.mem_univ _)
  exact h

/-- Marginals of a probability weight are probability weights. -/
theorem isProbWeight_margWeight (w : (∀ i, X i) → ℝ)
    (hw : IsProbWeight w) (i : κ) : IsProbWeight (margWeight w i) :=
  ⟨fun x => margWeight_nonneg w hw.1 i x, by
    rw [sum_margWeight]; exact hw.2⟩

/-- A configuration's own weight is at most its marginal at any
site: the fiber over `y i` contains `y` itself. -/
theorem le_margWeight_self (w : (∀ i, X i) → ℝ) (hw : ∀ y, 0 ≤ w y)
    (y : ∀ i, X i) (i : κ) : w y ≤ margWeight w i (y i) := by
  rw [margWeight_apply]
  apply Finset.single_le_sum (fun z _ => hw z)
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ y, rfl⟩

/-- The marginal's entropy sum, refibered over configurations: on
each fiber the marginal factor is constant. -/
theorem sum_margWeight_mul_log (w : (∀ i, X i) → ℝ) (i : κ) :
    ∑ x, margWeight w i x * Real.log (margWeight w i x)
      = ∑ y, w y * Real.log (margWeight w i (y i)) := by
  have h := Finset.sum_fiberwise_of_maps_to
    (s := (Finset.univ : Finset (∀ i, X i)))
    (t := (Finset.univ : Finset (X i))) (g := fun y : (∀ i, X i) => y i)
    (f := fun y => w y * Real.log (margWeight w i (y i)))
    (fun y _ => Finset.mem_univ _)
  rw [← h]
  apply Finset.sum_congr rfl
  intro x _
  have step : ∀ y ∈ Finset.univ.filter (fun y => y i = x),
      w y * Real.log (margWeight w i (y i))
        = w y * Real.log (margWeight w i x) := by
    intro y hy
    rw [Finset.mem_filter] at hy
    rw [hy.2]
  rw [Finset.sum_congr rfl step, ← Finset.sum_mul, ← margWeight_apply]

/-! ## §2. The map's basic bounds (consumed from FiniteEntropy) -/

/-- Site entropy is nonnegative. -/
theorem siteEntropy_nonneg (w : (∀ i, X i) → ℝ) (hw : IsProbWeight w)
    (i : κ) : 0 ≤ siteEntropy w i :=
  entropyW_nonneg (isProbWeight_margWeight w hw i)

/-- Site entropy is at most the log of the local state count. -/
theorem siteEntropy_le_log_card (w : (∀ i, X i) → ℝ)
    (hw : IsProbWeight w) (i : κ) :
    siteEntropy w i ≤ Real.log (Fintype.card (X i) : ℝ) :=
  entropyW_le_log_card (isProbWeight_margWeight w hw i)

/-! ## §3. Product weights: factorization and additivity -/

/-- The product weight of a family of site weights. -/
def siteProdWeight (u : ∀ i, X i → ℝ) : (∀ i, X i) → ℝ :=
  fun y => ∏ i, u i (y i)

omit [DecidableEq κ] [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)] in
theorem siteProdWeight_apply (u : ∀ i, X i → ℝ) (y : ∀ i, X i) :
    siteProdWeight u y = ∏ i, u i (y i) := rfl

omit [∀ i, DecidableEq (X i)] in
/-- A product of probability weights is a probability weight:
nonnegativity factorwise, and the total mass factors as a product
of ones (`Finset.prod_univ_sum`). -/
theorem isProbWeight_siteProdWeight (u : ∀ i, X i → ℝ)
    (hu : ∀ i, IsProbWeight (u i)) : IsProbWeight (siteProdWeight u) := by
  refine ⟨fun y => Finset.prod_nonneg (fun i _ => (hu i).1 (y i)), ?_⟩
  have h := Finset.prod_univ_sum (fun j => (Finset.univ : Finset (X j)))
    (fun j x => u j x)
  rw [Fintype.piFinset_univ] at h
  calc (∑ y, siteProdWeight u y)
      = ∑ y, ∏ j, u j (y j) :=
        Finset.sum_congr rfl (fun y _ => siteProdWeight_apply u y)
    _ = ∏ j, ∑ x, u j x := h.symm
    _ = ∏ _j : κ, (1 : ℝ) :=
        Finset.prod_congr rfl (fun j _ => (hu j).2)
    _ = 1 := Finset.prod_const_one

omit [∀ i, DecidableEq (X i)] in
/-- **Factorization.** Twisting a product weight by a function of
the `i`-th coordinate alone splits the total into the twisted
`i`-factor times the masses of all other factors. The twisted
family is `Function.update u i (fun x => u i x * φ x)` — the
dependent-safe way to change one factor of a dependent family. -/
theorem sum_siteProdWeight_mul (u : ∀ i, X i → ℝ) (i : κ)
    (φ : X i → ℝ) :
    ∑ y, siteProdWeight u y * φ (y i)
      = (∑ x, u i x * φ x)
        * ∏ j ∈ Finset.univ.erase i, ∑ x, u j x := by
  have hFi : Function.update u i (fun x => u i x * φ x) i
      = fun x => u i x * φ x :=
    Function.update_self i _ u
  have hFj : ∀ j, j ≠ i →
      Function.update u i (fun x => u i x * φ x) j = u j :=
    fun j hj => Function.update_of_ne hj _ _
  have hpt : ∀ y : (∀ i, X i), siteProdWeight u y * φ (y i)
      = ∏ j, Function.update u i (fun x => u i x * φ x) j (y j) := by
    intro y
    have e1 : ∏ j, Function.update u i (fun x => u i x * φ x) j (y j)
        = (u i (y i) * φ (y i))
          * ∏ j ∈ Finset.univ.erase i, u j (y j) := by
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
      congr 1
      · exact congrFun hFi (y i)
      · apply Finset.prod_congr rfl
        intro j hj
        rw [Finset.mem_erase] at hj
        exact congrFun (hFj j hj.1) (y j)
    rw [e1, siteProdWeight_apply,
      ← Finset.mul_prod_erase Finset.univ (fun j => u j (y j))
        (Finset.mem_univ i)]
    ring
  rw [Finset.sum_congr rfl (fun y _ => hpt y)]
  have h := Finset.prod_univ_sum
    (fun j => (Finset.univ : Finset (X j)))
    (Function.update u i (fun x => u i x * φ x))
  rw [Fintype.piFinset_univ] at h
  rw [← h, ← Finset.mul_prod_erase Finset.univ
    (fun j => ∑ x, Function.update u i (fun x => u i x * φ x) j x)
    (Finset.mem_univ i)]
  congr 1
  · exact Finset.sum_congr rfl (fun x _ => congrFun hFi x)
  · apply Finset.prod_congr rfl
    intro j hj
    rw [Finset.mem_erase] at hj
    exact Finset.sum_congr rfl (fun x _ => congrFun (hFj j hj.1) x)

omit [∀ i, DecidableEq (X i)] in
/-- Factorization when every factor is a probability weight: the
other factors' masses are all `1`. -/
theorem sum_siteProdWeight_mul_of_isProb (u : ∀ i, X i → ℝ)
    (hu : ∀ i, IsProbWeight (u i)) (i : κ) (φ : X i → ℝ) :
    ∑ y, siteProdWeight u y * φ (y i) = ∑ x, u i x * φ x := by
  rw [sum_siteProdWeight_mul]
  have h1 : ∏ j ∈ Finset.univ.erase i, ∑ x, u j x = 1 := by
    have h2 : ∏ j ∈ Finset.univ.erase i, ∑ x, u j x
        = ∏ _j ∈ Finset.univ.erase i, (1 : ℝ) :=
      Finset.prod_congr rfl (fun j _ => (hu j).2)
    rw [h2, Finset.prod_const_one]
  rw [h1, mul_one]

/-- The marginal of a product weight at site `i` is its own factor
at `i`. -/
theorem margWeight_siteProdWeight (u : ∀ i, X i → ℝ)
    (hu : ∀ i, IsProbWeight (u i)) (i : κ) :
    margWeight (siteProdWeight u) i = u i := by
  funext x
  rw [margWeight_apply, Finset.sum_filter]
  have h : (∑ y, if y i = x then siteProdWeight u y else 0)
      = ∑ y, siteProdWeight u y * (if y i = x then (1 : ℝ) else 0) := by
    apply Finset.sum_congr rfl
    intro y _
    by_cases hy : y i = x <;> simp [hy]
  rw [h, sum_siteProdWeight_mul_of_isProb u hu i
    (fun z => if z = x then (1 : ℝ) else 0)]
  have h2 : (∑ z, u i z * (if z = x then (1 : ℝ) else 0))
      = ∑ z, (if z = x then u i z else 0) := by
    apply Finset.sum_congr rfl
    intro z _
    by_cases hz : z = x <;> simp [hz]
  rw [h2, Finset.sum_ite_eq']
  simp

omit [DecidableEq κ] [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)] in
/-- A product weight times its own log splits as the sum of its
factors' contributions. -/
theorem siteProdWeight_mul_log (u : ∀ i, X i → ℝ) (y : ∀ i, X i) :
    siteProdWeight u y * Real.log (siteProdWeight u y)
      = ∑ i, siteProdWeight u y * Real.log (u i (y i)) := by
  by_cases h0 : ∃ j, u j (y j) = 0
  · obtain ⟨j, hj⟩ := h0
    have hP : siteProdWeight u y = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ j) hj
    rw [hP]
    simp
  · push Not at h0
    have hne : ∀ i ∈ (Finset.univ : Finset κ), u i (y i) ≠ 0 :=
      fun i _ => h0 i
    rw [siteProdWeight_apply, Real.log_prod hne, Finset.mul_sum]

omit [∀ i, DecidableEq (X i)] in
/-- **Additivity for product weights.** The entropy of a product
weight is the sum of the factor entropies. Stated ONLY under the
product hypothesis — see the K-TCS-ENT guard in the header. -/
theorem entropyW_siteProdWeight (u : ∀ i, X i → ℝ)
    (hu : ∀ i, IsProbWeight (u i)) :
    entropyW (siteProdWeight u) = ∑ i, entropyW (u i) := by
  have E : ∑ y, siteProdWeight u y * Real.log (siteProdWeight u y)
      = ∑ i, ∑ x, u i x * Real.log (u i x) := by
    rw [Finset.sum_congr rfl (fun y _ => siteProdWeight_mul_log u y),
      Finset.sum_comm]
    exact Finset.sum_congr rfl
      (fun i _ => sum_siteProdWeight_mul_of_isProb u hu i
        (fun z => Real.log (u i z)))
  show -∑ y, siteProdWeight u y * Real.log (siteProdWeight u y)
    = ∑ i, -∑ x, u i x * Real.log (u i x)
  rw [E, Finset.sum_neg_distrib]

/-- The site entropy of a product weight at site `i` is the entropy
of its own factor. -/
theorem siteEntropy_siteProdWeight (u : ∀ i, X i → ℝ)
    (hu : ∀ i, IsProbWeight (u i)) (i : κ) :
    siteEntropy (siteProdWeight u) i = entropyW (u i) := by
  have h : siteEntropy (siteProdWeight u) i
      = entropyW (margWeight (siteProdWeight u) i) := rfl
  rw [h, margWeight_siteProdWeight u hu i]

/-- Additivity in map form: for a product weight, the total entropy
is the sum of the site entropies of the weight itself. -/
theorem entropyW_siteProdWeight_eq_sum_siteEntropy
    (u : ∀ i, X i → ℝ) (hu : ∀ i, IsProbWeight (u i)) :
    entropyW (siteProdWeight u)
      = ∑ i, siteEntropy (siteProdWeight u) i := by
  rw [entropyW_siteProdWeight u hu]
  exact Finset.sum_congr rfl
    (fun i _ => (siteEntropy_siteProdWeight u hu i).symm)

/-! ## §4. Subadditivity in general -/

/-- The sum of the site entropies, refibered: it is the negative
log-moment of the product of the marginals. -/
theorem sum_siteEntropy_eq (w : (∀ i, X i) → ℝ) (hw : IsProbWeight w) :
    ∑ i, siteEntropy w i
      = -∑ y, w y * Real.log (∏ i, margWeight w i (y i)) := by
  have step1 : ∑ i, siteEntropy w i
      = -∑ i, ∑ y, w y * Real.log (margWeight w i (y i)) := by
    have hterm : ∀ i, siteEntropy w i
        = -∑ y, w y * Real.log (margWeight w i (y i)) := by
      intro i
      have h : siteEntropy w i = entropyW (margWeight w i) := rfl
      rw [h]
      show entropyW (margWeight w i)
        = -∑ y, w y * Real.log (margWeight w i (y i))
      unfold entropyW
      rw [sum_margWeight_mul_log]
    rw [Finset.sum_congr rfl (fun i _ => hterm i),
      Finset.sum_neg_distrib]
  rw [step1, Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro y _
  by_cases hy : w y = 0
  · rw [hy]
    simp
  · have hwy : 0 < w y := lt_of_le_of_ne' (hw.1 y) hy
    have hne : ∀ i ∈ (Finset.univ : Finset κ),
        margWeight w i (y i) ≠ 0 := by
      intro i _
      exact (lt_of_lt_of_le hwy (le_margWeight_self w hw.1 y i)).ne'
    rw [Real.log_prod hne, Finset.mul_sum]

/-- **Subadditivity.** The entropy of a weight never exceeds the
sum of its site entropies. Route: the pointwise Gibbs inequality
`Real.log_le_sub_one_of_pos` applied to the ratio of the product of
the marginals (a probability weight, by §3's machinery) to the
weight itself; summing, both total masses are `1` and cancel. The
general theorem — additivity without the product hypothesis is
false (K-TCS-ENT, header). -/
theorem entropyW_le_sum_siteEntropy (w : (∀ i, X i) → ℝ)
    (hw : IsProbWeight w) :
    entropyW w ≤ ∑ i, siteEntropy w i := by
  have hPprob : IsProbWeight
      (fun y : (∀ i, X i) => ∏ i, margWeight w i (y i)) :=
    isProbWeight_siteProdWeight (margWeight w)
      (fun i => isProbWeight_margWeight w hw i)
  have hP2 : (∑ (y : (∀ i, X i)), ∏ i, margWeight w i (y i)) = 1 :=
    hPprob.2
  have hpoint : ∀ y, w y - ∏ i, margWeight w i (y i)
      ≤ w y * Real.log (w y)
        - w y * Real.log (∏ i, margWeight w i (y i)) := by
    intro y
    by_cases hy : w y = 0
    · rw [hy]
      have hnn : 0 ≤ ∏ i, margWeight w i (y i) := hPprob.1 y
      simp only [zero_mul, sub_zero, zero_sub]
      exact neg_nonpos.mpr hnn
    · have hwy : 0 < w y := lt_of_le_of_ne' (hw.1 y) hy
      have hPpos : 0 < ∏ i, margWeight w i (y i) :=
        Finset.prod_pos (fun i _ =>
          lt_of_lt_of_le hwy (le_margWeight_self w hw.1 y i))
      have hGibbs := Real.log_le_sub_one_of_pos
        (x := (∏ i, margWeight w i (y i)) / w y) (div_pos hPpos hwy)
      rw [Real.log_div hPpos.ne' hy] at hGibbs
      have hmul := mul_le_mul_of_nonneg_left hGibbs hwy.le
      have e1 : w y * ((∏ i, margWeight w i (y i)) / w y - 1)
          = (∏ i, margWeight w i (y i)) - w y := by
        rw [mul_sub, mul_one, mul_div_cancel₀ _ hy]
      rw [e1] at hmul
      have e2 : w y * (Real.log (∏ i, margWeight w i (y i))
            - Real.log (w y))
          = w y * Real.log (∏ i, margWeight w i (y i))
            - w y * Real.log (w y) := by ring
      rw [e2] at hmul
      linarith
  have hsum : ∑ y, (w y - ∏ i, margWeight w i (y i))
      ≤ ∑ y, (w y * Real.log (w y)
        - w y * Real.log (∏ i, margWeight w i (y i))) :=
    Finset.sum_le_sum (fun y _ => hpoint y)
  have hL : ∑ y, (w y - ∏ i, margWeight w i (y i)) = 0 := by
    rw [Finset.sum_sub_distrib, hw.2, hP2, sub_self]
  have hR : (∑ i, siteEntropy w i) - entropyW w
      = ∑ y, (w y * Real.log (w y)
          - w y * Real.log (∏ i, margWeight w i (y i))) := by
    have h1 : entropyW w = -∑ y, w y * Real.log (w y) := rfl
    have h2 : ∑ i, siteEntropy w i
        = -∑ y, w y * Real.log (∏ i, margWeight w i (y i)) :=
      sum_siteEntropy_eq w hw
    rw [h1, h2, Finset.sum_sub_distrib]
    ring
  rw [hL, ← hR] at hsum
  exact sub_nonneg.mp hsum

end ThetLogos
