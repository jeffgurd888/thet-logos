import Mathlib

/-!
# ThetLogos.SurfaceTensionSeat — the surface-tension analog seat (finite, one ring)

Charter: `surface-tension-seat-charter-2026-11-05.md`. Jeff's seeing
(2026-11-05 00:42–00:44 EST): "gravity should be landing soon" → "why can't
gravity be the same thing as surface tension" → "build it".

The literal identity gravity = surface tension is NO-GO (pinned before the
build): surface tension is interface-only, material-dependent (it breaks
free-fall universality), scalar and short-range; gravity is bulk, universal,
tensor, long-range. What is built here is the honest finite analog seat: one
ring of `n` sites, two phases (`f : Fin n → Bool`), and the tension functional
`T(f)` = the number of phase boundaries (edges `i ~ i + 1` where the label
changes), with tension energy `E = γ · T`.

What the seat proves (T1, this module):
1. Complement symmetry `T(¬f) = T(f)` — the two phases are interchangeable.
2. Evenness: `T(f)` is always even — transitions around a closed ring pair up.
3. Isoperimetric floor (the finite Young–Laplace content): a nonconstant
   labeling pays `T(f) ≥ 2` — a droplet on a ring has at least two boundary
   edges.
4. Sharpness: single-site and single-arc labelings attain `T = 2`.
5. Bulk-blindness (the seat's proved limitation, in the spirit of K-SR-4):
   the single-site and two-adjacent-sites labelings have the *same* tension
   `T = 2` but *different* masses `1 ≠ 2` — the functional provably cannot
   see bulk mass.

NO CLAIM. Dial 2 = 0: a finite analog exhibit is not a gravity object, and
item 5 is the pre-registered D2 failure of this seat (no bulk coupling),
proved rather than asserted. Working label only; public naming is Jeff's.
-/

namespace ThetLogos

/-- The tension functional of the seat: the number of phase boundaries of a
    labeling `f : Fin n → Bool` on the ring — the sites `i` whose label
    differs from the next site's label `f (i + 1)`. -/
def tensionCount {n : ℕ} [NeZero n] (f : Fin n → Bool) : ℕ :=
  (Finset.univ.filter fun i => f i ≠ f (i + 1)).card

/-- The mass of a labeling: the number of sites labeled `true`. -/
def labelMass {n : ℕ} (f : Fin n → Bool) : ℕ :=
  (Finset.univ.filter fun i => f i = true).card

/-- The tension energy `E = γ · T`, for a surface-tension coefficient `γ`. -/
def tensionEnergy {n : ℕ} [NeZero n] (γ : ℝ) (f : Fin n → Bool) : ℝ :=
  γ * (tensionCount f : ℝ)

/-- The single-site ("droplet of one site") labeling: `true` exactly at `0`. -/
def singleSiteLabel {n : ℕ} [NeZero n] : Fin n → Bool :=
  fun i => decide (i = 0)

/-- The two-adjacent-sites ("single arc of length two") labeling:
    `true` exactly at `0` and `1`. -/
def twoSiteLabel {n : ℕ} [NeZero n] : Fin n → Bool :=
  fun i => decide (i = 0 ∨ i = 1)

/-- Complement symmetry: swapping the two phases does not change the tension. -/
theorem tensionCount_comp {n : ℕ} [NeZero n] (f : Fin n → Bool) :
    tensionCount (fun i => !(f i)) = tensionCount f := by
  unfold tensionCount
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  cases h₁ : f i <;> cases h₂ : f (i + 1) <;> decide

/-- Evenness: the number of phase boundaries around a closed ring is even.
    Proved in `ZMod 2`: the transition indicator at `i` is `x (i+1) - x i`
    for the `ZMod 2`-valued label `x`, and the sum over the ring telescopes
    to `0` because the shift by `1` permutes `Fin n`. -/
theorem tensionCount_even {n : ℕ} [NeZero n] (f : Fin n → Bool) :
    Even (tensionCount f) := by
  set x : Fin n → ZMod 2 := fun i => if f i then 1 else 0 with hx
  have hind : ∀ i : Fin n,
      (if f i ≠ f (i + 1) then (1 : ZMod 2) else 0) = x (i + 1) - x i := by
    intro i
    cases h₁ : f i <;> cases h₂ : f (i + 1) <;> simp only [hx, h₁, h₂] <;> decide
  have hshift : (∑ i : Fin n, x (i + 1)) = ∑ i : Fin n, x i := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · exact (NeZero.ne n hn).elim
    · exact Equiv.sum_comp (Equiv.addRight (1 : Fin n)) x
  have hcast : (tensionCount f : ZMod 2) = 0 := by
    have h1 : (tensionCount f : ZMod 2)
        = ∑ i : Fin n, (if f i ≠ f (i + 1) then (1 : ZMod 2) else 0) := by
      rw [Finset.sum_boole]
      rfl
    calc (tensionCount f : ZMod 2)
        = ∑ i : Fin n, (if f i ≠ f (i + 1) then (1 : ZMod 2) else 0) := h1
      _ = ∑ i : Fin n, (x (i + 1) - x i) :=
          Finset.sum_congr rfl (fun i _ => hind i)
      _ = (∑ i : Fin n, x (i + 1)) - ∑ i : Fin n, x i :=
          Finset.sum_sub_distrib (fun i => x (i + 1)) x
      _ = 0 := by rw [hshift, sub_self]
  have hdvd : 2 ∣ tensionCount f :=
    (CharP.cast_eq_zero_iff (ZMod 2) 2 (tensionCount f)).mp hcast
  exact even_iff_two_dvd.mpr hdvd

/-- If the tension vanishes, adjacent labels agree everywhere, so the
    labeling is constant. The walk goes once around the ring from site `0`. -/
theorem const_of_tensionCount_eq_zero {n : ℕ} [NeZero n] (f : Fin n → Bool)
    (h : tensionCount f = 0) (a b : Fin n) : f a = f b := by
  have hadj : ∀ i : Fin n, f i = f (i + 1) := by
    intro i
    by_contra hne
    have hmem : i ∈ Finset.univ.filter (fun j => f j ≠ f (j + 1)) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ i, hne⟩
    have hpos : 0 < tensionCount f := Finset.card_pos.mpr ⟨i, hmem⟩
    omega
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    exact (Nat.not_lt_zero _ a.isLt).elim
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have step : ∀ j : ℕ, ∀ hj : j + 1 < m + 1,
        f ⟨j, by omega⟩ = f ⟨j + 1, hj⟩ := by
      cases m with
      | zero =>
        intro j hj
        exact ((by omega : ¬ (j + 1 < 1)) hj).elim
      | succ k =>
        intro j hj
        have h1 : (⟨j, by omega⟩ : Fin (k + 1 + 1)) + 1 = ⟨j + 1, hj⟩ := by
          apply Fin.ext
          rw [Fin.val_add, Fin.val_one, Nat.mod_eq_of_lt hj]
        rw [← h1]
        exact hadj _
    have key : ∀ j : ℕ, ∀ hj : j < m + 1, f ⟨j, hj⟩ = f ⟨0, by omega⟩ := by
      intro j
      induction j with
      | zero => intro _; rfl
      | succ j ih =>
        intro hj
        rw [← step j hj]
        exact ih (by omega)
    have ea : f a = f ⟨0, by omega⟩ := by
      have ha : a = ⟨a.val, a.isLt⟩ := Fin.ext rfl
      rw [ha]
      exact key a.val a.isLt
    have eb : f b = f ⟨0, by omega⟩ := by
      have hb : b = ⟨b.val, b.isLt⟩ := Fin.ext rfl
      rw [hb]
      exact key b.val b.isLt
    rw [ea, eb]

/-- The isoperimetric floor of the seat (finite Young–Laplace content):
    a nonconstant labeling pays at least two boundary edges. -/
theorem two_le_tensionCount_of_nonconstant {n : ℕ} [NeZero n] (f : Fin n → Bool)
    (h : ∃ a b, f a ≠ f b) : 2 ≤ tensionCount f := by
  obtain ⟨a, b, hab⟩ := h
  have hne : tensionCount f ≠ 0 := by
    intro h0
    exact hab (const_of_tensionCount_eq_zero f h0 a b)
  obtain ⟨k, hk⟩ := tensionCount_even f
  omega

/-- Successor of a named site in `Fin (m + 3)`, computed on values. -/
theorem fin_succ_mk {m j : ℕ} (hj : j + 1 < m + 3) :
    (⟨j, by omega⟩ : Fin (m + 3)) + 1 = ⟨j + 1, hj⟩ := by
  apply Fin.ext
  rw [Fin.val_add, Fin.val_one, Nat.mod_eq_of_lt hj]

/-- In `Fin (m + 3)`: the successor of `0` is `1`. -/
theorem zero_add_one {m : ℕ} : (0 : Fin (m + 3)) + 1 = 1 := by
  have e0 : (0 : Fin (m + 3)) = ⟨0, by omega⟩ := Fin.ext rfl
  have e1 : (⟨1, by omega⟩ : Fin (m + 3)) = 1 := by
    apply Fin.ext
    show (1 : ℕ) = ((1 : Fin (m + 3)) : ℕ)
    exact (Fin.val_one _).symm
  rw [e0, fin_succ_mk (by omega : 0 + 1 < m + 3), e1]

/-- In `Fin (m + 3)`: `1 ≠ 0`. -/
theorem one_ne_zero_fin {m : ℕ} : (1 : Fin (m + 3)) ≠ 0 := by
  intro hcon
  have hv := congrArg Fin.val hcon
  rw [Fin.val_one] at hv
  exact one_ne_zero hv

/-- In `Fin (m + 3)`, the only site whose successor is `0` is the last
    site `⟨m + 2, _⟩`: since `(i.val + 1) % (m + 3) = 0` and
    `1 ≤ i.val + 1 ≤ m + 3`, divisibility forces `i.val + 1 = m + 3`. -/
theorem eq_last_of_add_one_eq_zero {m : ℕ} (i : Fin (m + 3))
    (h : i + 1 = 0) : i = ⟨m + 2, by omega⟩ := by
  have hval : (i + 1).val = 0 := by rw [h]; rfl
  rw [Fin.val_add, Fin.val_one] at hval
  have hdvd : (m + 3) ∣ (i.val + 1) := Nat.dvd_of_mod_eq_zero hval
  obtain ⟨q, hq⟩ := hdvd
  have hq1 : q = 1 := by
    have hle : i.val + 1 ≤ m + 3 := by have := i.isLt; omega
    have hpos : 0 < i.val + 1 := by omega
    rw [hq] at hle hpos
    have hqle : q ≤ 1 := by
      by_contra hq2
      push Not at hq2
      have hmul : (m + 3) * 2 ≤ (m + 3) * q := Nat.mul_le_mul_left _ hq2
      omega
    have hqpos : 0 < q := by
      by_contra hq0
      push Not at hq0
      interval_cases q
      simp at hpos
    omega
  rw [hq1, Nat.mul_one] at hq
  apply Fin.ext
  show i.val = m + 2
  omega

/-- In `Fin (m + 3)`, the only site whose successor is `1` is `0`:
    `(i.val + 1) % (m + 3) = 1` with `1 ≤ i.val + 1 ≤ m + 3` forces
    `i.val + 1 = 1` (the quotient in the division is `0`). -/
theorem eq_zero_of_add_one_eq_one {m : ℕ} (i : Fin (m + 3))
    (h : i + 1 = 1) : i = 0 := by
  have hval : (i + 1).val = 1 := by
    rw [h]
    exact Fin.val_one _
  rw [Fin.val_add, Fin.val_one] at hval
  have hdiv := Nat.mod_add_div (i.val + 1) (m + 3)
  rw [hval] at hdiv
  have hle : i.val + 1 ≤ m + 3 := by have := i.isLt; omega
  have hq0 : (i.val + 1) / (m + 3) = 0 := by
    by_contra hq
    have hge : 1 ≤ (i.val + 1) / (m + 3) := Nat.pos_of_ne_zero hq
    have hmul : (m + 3) * 1 ≤ (m + 3) * ((i.val + 1) / (m + 3)) :=
      Nat.mul_le_mul_left _ hge
    omega
  rw [hq0, Nat.mul_zero, add_zero] at hdiv
  apply Fin.ext
  show i.val = 0
  omega

/-- The successor of the last site of `Fin (m + 3)` wraps around to `0`. -/
theorem last_add_one {m : ℕ} :
    (⟨m + 2, by omega⟩ : Fin (m + 3)) + 1 = 0 := by
  apply Fin.ext
  have hv : (⟨m + 2, by omega⟩ : Fin (m + 3)).val = m + 2 := rfl
  rw [Fin.val_add, Fin.val_one, hv]
  exact Nat.mod_self _

/-- Sharpness, single site: for `n ≥ 3` the single-site labeling attains
    the floor, `T = 2` — its two boundary edges are at `0` and at the
    last site (whose successor wraps to `0`). -/
theorem tensionCount_singleSite {n : ℕ} [NeZero n] (hn : 3 ≤ n) :
    tensionCount (singleSiteLabel : Fin n → Bool) = 2 := by
  obtain ⟨m, hm⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  subst hm
  unfold tensionCount
  have hset : Finset.univ.filter (fun i => singleSiteLabel i ≠ singleSiteLabel (i + 1))
      = ({0, ⟨m + 2, by omega⟩} : Finset (Fin (m + 3))) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · intro hi
      by_cases hi0 : i = 0
      · exact Or.inl hi0
      · right
        have hfi : singleSiteLabel i = false := by
          simp only [singleSiteLabel, decide_eq_false_iff_not]
          exact hi0
        have hfi1 : singleSiteLabel (i + 1) = true := by
          rw [hfi] at hi
          exact Bool.ne_false_iff.mp (Ne.symm hi)
        have hsucc : i + 1 = 0 := by
          have htmp := hfi1
          simp only [singleSiteLabel, decide_eq_true_eq] at htmp
          exact htmp
        exact eq_last_of_add_one_eq_zero i hsucc
    · intro hi
      rcases hi with rfl | rfl
      · rw [zero_add_one]
        have e0 : singleSiteLabel (0 : Fin (m + 3)) = true := by
          simp [singleSiteLabel]
        have e1 : singleSiteLabel (1 : Fin (m + 3)) = false := by
          simp only [singleSiteLabel, decide_eq_false_iff_not]
          exact one_ne_zero_fin
        rw [e0, e1]
        decide
      · rw [last_add_one]
        have e0 : singleSiteLabel (0 : Fin (m + 3)) = true := by
          simp [singleSiteLabel]
        have eL : singleSiteLabel (⟨m + 2, by omega⟩ : Fin (m + 3)) = false := by
          simp only [singleSiteLabel, decide_eq_false_iff_not]
          apply Fin.ne_of_val_ne
          show (m + 2 : ℕ) ≠ 0
          omega
        rw [eL, e0]
        exact Bool.false_ne_true
  rw [hset, Finset.card_pair]
  apply Fin.ne_of_val_ne
  show (0 : ℕ) ≠ m + 2
  omega

/-- Sharpness, single arc of length two: for `n ≥ 3` the two-adjacent-sites
    labeling also attains the floor, `T = 2` — its boundary edges are at `1`
    and at the last site. -/
theorem tensionCount_twoSite {n : ℕ} [NeZero n] (hn : 3 ≤ n) :
    tensionCount (twoSiteLabel : Fin n → Bool) = 2 := by
  obtain ⟨m, hm⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  subst hm
  unfold tensionCount
  have hset : Finset.univ.filter (fun i => twoSiteLabel i ≠ twoSiteLabel (i + 1))
      = ({1, ⟨m + 2, by omega⟩} : Finset (Fin (m + 3))) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · intro hi
      by_cases hi0 : i = 0
      · -- at `0` both labels are `true`: no transition — contradiction.
        subst hi0
        rw [zero_add_one] at hi
        have e0 : twoSiteLabel (0 : Fin (m + 3)) = true := by
          simp [twoSiteLabel]
        have e1 : twoSiteLabel (1 : Fin (m + 3)) = true := by
          simp [twoSiteLabel]
        rw [e0, e1] at hi
        exact absurd rfl hi
      · by_cases hi1 : i = 1
        · exact Or.inl hi1
        · right
          have hfi : twoSiteLabel i = false := by
            simp only [twoSiteLabel, decide_eq_false_iff_not, not_or]
            exact ⟨hi0, hi1⟩
          have hfi1 : twoSiteLabel (i + 1) = true := by
            rw [hfi] at hi
            exact Bool.ne_false_iff.mp (Ne.symm hi)
          have hcases : i + 1 = 0 ∨ i + 1 = 1 := by
            have htmp := hfi1
            simp only [twoSiteLabel, decide_eq_true_eq] at htmp
            exact htmp
          rcases hcases with hc | hc
          · exact eq_last_of_add_one_eq_zero i hc
          · exact absurd (eq_zero_of_add_one_eq_one i hc) hi0
    · intro hi
      rcases hi with rfl | rfl
      · -- at `1`: `true` vs `f 2 = false`, where `2 = ⟨2, _⟩` via `1 + 1`.
        have e1m : (1 : Fin (m + 3)) = ⟨1, by omega⟩ := by
          apply Fin.ext
          show ((1 : Fin (m + 3)) : ℕ) = 1
          exact Fin.val_one _
        have h2 : (1 : Fin (m + 3)) + 1 = ⟨2, by omega⟩ := by
          rw [e1m]
          exact fin_succ_mk (by omega : 1 + 1 < m + 3)
        rw [h2]
        have e1 : twoSiteLabel (1 : Fin (m + 3)) = true := by
          simp [twoSiteLabel]
        have e2 : twoSiteLabel (⟨2, by omega⟩ : Fin (m + 3)) = false := by
          simp only [twoSiteLabel, decide_eq_false_iff_not, not_or]
          constructor
          · apply Fin.ne_of_val_ne
            show (2 : ℕ) ≠ 0
            omega
          · apply Fin.ne_of_val_ne
            rw [Fin.val_one]
            show (2 : ℕ) ≠ 1
            omega
        rw [e1, e2]
        decide
      · rw [last_add_one]
        have e0 : twoSiteLabel (0 : Fin (m + 3)) = true := by
          simp [twoSiteLabel]
        have eL : twoSiteLabel (⟨m + 2, by omega⟩ : Fin (m + 3)) = false := by
          simp only [twoSiteLabel, decide_eq_false_iff_not, not_or]
          constructor
          · apply Fin.ne_of_val_ne
            show (m + 2 : ℕ) ≠ 0
            omega
          · apply Fin.ne_of_val_ne
            rw [Fin.val_one]
            show (m + 2 : ℕ) ≠ 1
            omega
        rw [eL, e0]
        exact Bool.false_ne_true
  rw [hset, Finset.card_pair]
  apply Fin.ne_of_val_ne
  rw [Fin.val_one]
  show (1 : ℕ) ≠ m + 2
  omega

/-- The single-site labeling has mass `1`. -/
theorem labelMass_singleSite {n : ℕ} [NeZero n] (_hn : 1 ≤ n) :
    labelMass (singleSiteLabel : Fin n → Bool) = 1 := by
  unfold labelMass
  have hset : Finset.univ.filter (fun i => singleSiteLabel i = true)
      = ({0} : Finset (Fin n)) := by
    ext i
    simp [singleSiteLabel]
  exact Finset.card_eq_one.mpr ⟨0, hset⟩

/-- The two-adjacent-sites labeling has mass `2` (for `n ≥ 2`, so that
    `0 ≠ 1` in `Fin n`). -/
theorem labelMass_twoSite {n : ℕ} [NeZero n] (hn : 2 ≤ n) :
    labelMass (twoSiteLabel : Fin n → Bool) = 2 := by
  obtain ⟨m, hm⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  subst hm
  unfold labelMass
  have hset : Finset.univ.filter (fun i => twoSiteLabel i = true)
      = ({0, 1} : Finset (Fin (m + 2))) := by
    ext i
    simp [twoSiteLabel]
  rw [hset, Finset.card_pair]
  apply Fin.ne_of_val_ne
  rw [Fin.val_one]
  show (0 : ℕ) ≠ 1
  omega

/-- Bulk-blindness — the seat's proved limitation. For `n ≥ 4`, the
    single-site and two-adjacent-sites labelings have the *same* tension
    `T = 2` but *different* masses `1 ≠ 2`: the tension functional does not
    determine the bulk mass. A boundary-tension functional cannot couple to
    the bulk; this is the D2 failure of the seat, proved at the seat. -/
theorem tensionCount_does_not_determine_mass {n : ℕ} [NeZero n] (hn : 4 ≤ n) :
    tensionCount (singleSiteLabel : Fin n → Bool)
      = tensionCount (twoSiteLabel : Fin n → Bool)
    ∧ labelMass (singleSiteLabel : Fin n → Bool)
      ≠ labelMass (twoSiteLabel : Fin n → Bool) := by
  have ht1 := tensionCount_singleSite (n := n) (by omega : 3 ≤ n)
  have ht2 := tensionCount_twoSite (n := n) (by omega : 3 ≤ n)
  have hm1 := labelMass_singleSite (n := n) (by omega : 1 ≤ n)
  have hm2 := labelMass_twoSite (n := n) (by omega : 2 ≤ n)
  have h12 : (1 : ℕ) ≠ 2 := by decide
  exact ⟨ht1.trans ht2.symm,
    fun heq => h12 (hm1.symm.trans (heq.trans hm2))⟩

/-- The tension energy inherits the complement symmetry. -/
theorem tensionEnergy_comp {n : ℕ} [NeZero n] (γ : ℝ) (f : Fin n → Bool) :
    tensionEnergy γ (fun i => !(f i)) = tensionEnergy γ f := by
  unfold tensionEnergy
  rw [tensionCount_comp]

/-- For `γ ≥ 0` the tension energy is nonnegative. -/
theorem tensionEnergy_nonneg {n : ℕ} [NeZero n] {γ : ℝ} (hγ : 0 ≤ γ)
    (f : Fin n → Bool) :
    0 ≤ tensionEnergy γ f := by
  unfold tensionEnergy
  exact mul_nonneg hγ (Nat.cast_nonneg _)

end ThetLogos
