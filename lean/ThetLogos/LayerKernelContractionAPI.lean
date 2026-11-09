/-
# Brick (ii), Module 1 — the finite-group contraction API
# (δ-coefficient / regular coefficient system)

Brick (ii) of the Q3 closable set (item 6;
`q3-closable-scope-2026-11-08.md` §2): the G-1 finite
`d ≥ 2` sector.  This module is the contraction API at the
generality the assembly (`LayerKernelGramCertFinite`)
consumes, no wider — per the frozen shape's own clause for
sub-brick 1c.

**The coefficient system.**  The assembly expands the
one-column Boltzmann factor in the δ-basis of functions on
the finite group `G` (the matrix coefficients of the left
regular coefficient system): `deltaFn t g = if g = t then 1
else 0`, with coefficients `exp (-β • gramDens ρ t) > 0`.
This is a design decision logged at full rank in the lane's
STATUS.md: the ρ-tensor-character expansion route needs an
infinite `tsum` plus irreducible decomposition (the
Peter–Weyl wall of the scoping's §1, T3/T4, not closable),
while the δ-basis is finite, exact, and FACT-free.  The
headline and its generality are unchanged.

Contents:
* (1a) single-coefficient orthogonality / sifting, and the
  translation invariance of finite sums over `G` — the
  concrete finite form of the pin's averaging engine
  (`average` / `averageMap` project by exactly this
  invariance for the counting measure).
* (1b) product contractions: products of δ-coefficients
  over a finite index, and the column-word contraction —
  a product of column δ's is the consistency indicator of
  the induced link configuration times the δ of that
  configuration.
* (1c) the channel form as the assembly consumes it: the
  configuration δ splits over an intermediate configuration
  `s` as `feat • star feat`.

NO CLAIM; dials 0/4.
-/

import ThetLogos.LayerKernelGramCert

open MeasureTheory Finset
open scoped Matrix ENNReal NNReal

namespace ThetLogos

section DeltaAPI

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

/-- The δ-coefficient of the regular coefficient system on a
finite group: `deltaFn t g = 1` iff `g = t`. -/
def deltaFn (t g : G) : ℂ := if g = t then 1 else 0

theorem deltaFn_self (t : G) : deltaFn t t = 1 := if_pos rfl

theorem deltaFn_of_ne {t g : G} (h : g ≠ t) : deltaFn t g = 0 :=
  if_neg h

theorem deltaFn_star (t g : G) : star (deltaFn t g) = deltaFn t g := by
  by_cases h : g = t <;> simp [deltaFn, h]

/-- (1a) Sifting: pairing a function against a δ-coefficient
extracts its value — the projection content of the averaging
engine at a point mass. -/
theorem deltaFn_sift (F : G → ℂ) (t : G) :
    ∑ a : G, deltaFn t a * F a = F t := by
  have h1 : ∀ a : G, deltaFn t a * F a = if a = t then F t else 0 := by
    intro a
    by_cases ha : a = t
    · subst ha
      rw [if_pos rfl, deltaFn_self, one_mul]
    · rw [if_neg ha, deltaFn_of_ne ha, zero_mul]
  rw [Finset.sum_congr rfl fun a _ => h1 a]
  simp

/-- (1a) Expansion sift, coefficient form: a function is the
sum of its values against the δ-basis. -/
theorem sum_deltaFn_mul (F : G → ℂ) (g : G) :
    ∑ t : G, F t * deltaFn t g = F g := by
  have h1 : ∀ t : G, F t * deltaFn t g = if t = g then F g else 0 := by
    intro t
    by_cases ht : t = g
    · subst ht
      rw [if_pos rfl, deltaFn_self, mul_one]
    · rw [if_neg ht, deltaFn_of_ne (Ne.symm ht), mul_zero]
  rw [Finset.sum_congr rfl fun t _ => h1 t]
  simp

/-- (1a) Single-coefficient orthogonality of the
δ-coefficients in `L²(G)` (counting pairing). -/
theorem deltaFn_orthonormal (s t : G) :
    ∑ a : G, deltaFn s a * star (deltaFn t a)
      = if s = t then 1 else 0 := by
  simp only [deltaFn_star]
  by_cases h : s = t
  · subst h
    rw [if_pos rfl]
    have : ∀ a : G, deltaFn s a * deltaFn s a = deltaFn s a := by
      intro a
      by_cases ha : a = s <;> simp [deltaFn, ha]
    rw [Finset.sum_congr rfl fun a _ => this a]
    have hs := deltaFn_sift (fun _ : G => (1 : ℂ)) s
    simpa using hs
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro a _
    by_cases ha : a = s
    · have hta : deltaFn t a = 0 :=
        deltaFn_of_ne (by rw [ha]; exact h)
      rw [hta, mul_zero]
    · rw [deltaFn_of_ne ha, zero_mul]

/-- (1a) Translation invariance of the finite sum over `G`:
the counting-measure content of `average`/`averageMap`
invariance. -/
theorem sum_translate (F : G → ℂ) (g : G) :
    ∑ a : G, F (g * a) = ∑ a : G, F a :=
  Equiv.sum_comp (Equiv.mulLeft g) F

/-- (1b) A product of δ-coefficients over a finite index is
the δ of the two configurations. -/
theorem prod_deltaFn_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (t w : ι → G) :
    ∏ i, deltaFn (t i) (w i) = if w = t then 1 else 0 := by
  by_cases h : w = t
  · subst h
    rw [if_pos rfl]
    exact Finset.prod_eq_one fun i _ => deltaFn_self _
  · rw [if_neg h]
    have hex : ∃ i, w i ≠ t i := by
      by_contra hc
      push_neg at hc
      exact h (funext hc)
    obtain ⟨i, hi⟩ := hex
    exact Finset.prod_eq_zero (Finset.mem_univ i) (deltaFn_of_ne hi)

/-- (1b) A product of indicators is the indicator of the
conjunction. -/
theorem prod_indicator_eq {ι : Type*} [Fintype ι]
    (p : ι → Prop) [DecidablePred p] :
    ∏ i, (if p i then (1 : ℂ) else 0)
      = if (∀ i, p i) then 1 else 0 := by
  by_cases h : ∀ i, p i
  · rw [if_pos h]
    exact Finset.prod_eq_one fun i _ => if_pos (h i)
  · rw [if_neg h]
    push_neg at h
    obtain ⟨i, hi⟩ := h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

end DeltaAPI

section WordContraction

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]
  {N : ℕ} [NeZero N] [DecidableEq (LayerLink N)]

/-- The column word read at a column index.  (The word itself
carries no representation: `colWord` mentions no `ρ`.) -/
def colWordOf (u u' : LayerLink N → G) (P : LayerColumn N)
    (α : LayerSite N → G) : G :=
  colWord u u' P.1 P.2.1 P.2.2 α

/-- The link of a column. -/
def colLink (P : LayerColumn N) : LayerLink N :=
  layerLinkOf P.1 P.2.1 P.2.2

/-- Every link is the link of some column (the column over
its own base site in its own direction). -/
theorem colLink_surjective :
    Function.Surjective (colLink : LayerColumn N → LayerLink N) := by
  intro ℓ
  exact ⟨(⟨ℓ.1.1, ℓ.2.1⟩, ⟨ℓ.1.2, ℓ.2.2⟩), rfl⟩

/-- A chosen column over each link. -/
noncomputable def wordColumn (ℓ : LayerLink N) : LayerColumn N :=
  Classical.choose (colLink_surjective (N := N) ℓ)

theorem colLink_wordColumn (ℓ : LayerLink N) :
    colLink (wordColumn (N := N) ℓ) = ℓ :=
  Classical.choose_spec (colLink_surjective (N := N) ℓ)

/-- The link value forced by a column equation
`colWordOf u u' P α = t P`: solving the word
`α c * u' ℓ * (α (σ c))⁻¹ * (u ℓ)⁻¹ = t P` for `u' ℓ` gives
`u' ℓ = (α c)⁻¹ * t P * u ℓ * α (σ c)`. -/
def wordVal (α : LayerSite N → G) (t : LayerColumn N → G)
    (u : LayerLink N → G) (P : LayerColumn N) : G :=
  (α P.1)⁻¹ * t P * u (colLink P) * α (layerShift P.2.1 P.2.2 P.1)

/-- The one-column contraction, algebraic form: the column
word equals its type iff the link value is the forced one. -/
theorem colWordOf_eq_iff (u u' : LayerLink N → G)
    (P : LayerColumn N) (α : LayerSite N → G)
    (t : LayerColumn N → G) :
    colWordOf u u' P α = t P
      ↔ u' (colLink P) = wordVal α t u P := by
  constructor
  · intro h
    have h2 : u' (colLink P)
        = (α P.1)⁻¹ * colWordOf u u' P α * u (colLink P)
          * α (layerShift P.2.1 P.2.2 P.1) := by
      simp only [colWordOf, colLink, colWord]
      group
    rw [h] at h2
    exact h2
  · intro h
    have hunfold : colWordOf u u' P α
        = α P.1 * u' (colLink P)
          * (α (layerShift P.2.1 P.2.2 P.1))⁻¹
          * (u (colLink P))⁻¹ := rfl
    rw [hunfold, h]
    simp only [wordVal]
    group

/-- Consistency of the forced link values: columns sharing
a link force the same value. -/
def linkConsistent (α : LayerSite N → G) (t : LayerColumn N → G)
    (u : LayerLink N → G) : Prop :=
  ∀ P Q : LayerColumn N, colLink P = colLink Q
    → wordVal α t u P = wordVal α t u Q

/-- The configuration forced by a consistent column-type
pattern: the forced value at the chosen column over each
link. -/
noncomputable def wordConfig (α : LayerSite N → G)
    (t : LayerColumn N → G) (u : LayerLink N → G) :
    LayerLink N → G :=
  fun ℓ => wordVal α t u (wordColumn (N := N) ℓ)

theorem wordVal_eq_wordConfig {α : LayerSite N → G}
    {t : LayerColumn N → G} {u : LayerLink N → G}
    (hcons : linkConsistent α t u) (P : LayerColumn N) :
    wordVal α t u P = wordConfig α t u (colLink P) :=
  hcons P (wordColumn (N := N) (colLink P))
    (colLink_wordColumn (N := N) (colLink P)).symm

open Classical in
/-- (1b) **The word contraction.**  The product over all
columns of the δ-coefficient of the column word is the
consistency indicator times the δ of the forced
configuration: the α-word system contracts to a condition
on `u` alone and a determined `u'`. -/
theorem prod_deltaFn_colWordOf (u u' : LayerLink N → G)
    (α : LayerSite N → G) (t : LayerColumn N → G) :
    ∏ P, deltaFn (t P) (colWordOf u u' P α)
      = (if linkConsistent α t u then (1 : ℂ) else 0)
        * (if u' = wordConfig α t u then 1 else 0) := by
  classical
  have hprod : ∏ P, deltaFn (t P) (colWordOf u u' P α)
      = if (∀ P, colWordOf u u' P α = t P) then (1 : ℂ) else 0 := by
    have h1 : (∏ P, deltaFn (t P) (colWordOf u u' P α))
        = ∏ P, (if colWordOf u u' P α = t P then (1 : ℂ) else 0) :=
      Finset.prod_congr rfl fun P _ => rfl
    rw [h1, prod_indicator_eq]
  have hequiv : (∀ P, colWordOf u u' P α = t P)
      ↔ linkConsistent α t u ∧ u' = wordConfig α t u := by
    constructor
    · intro h
      have hval : ∀ P, u' (colLink P) = wordVal α t u P :=
        fun P => (colWordOf_eq_iff u u' P α t).mp (h P)
      constructor
      · intro P Q hPQ
        rw [← hval P, ← hval Q, hPQ]
      · funext ℓ
        have h1 : u' ℓ = u' (colLink (wordColumn (N := N) ℓ)) := by
          rw [colLink_wordColumn]
        rw [h1, hval]
        rfl
    · intro h P
      have h1 : u' (colLink P) = wordVal α t u P := by
        have h2 : u' (colLink P) = wordConfig α t u (colLink P) := by
          rw [h.2]
        rw [h2, ← wordVal_eq_wordConfig h.1 P]
      exact (colWordOf_eq_iff u u' P α t).mpr h1
  rw [hprod]
  by_cases hA : ∀ P, colWordOf u u' P α = t P
  · have hB : linkConsistent α t u ∧ u' = wordConfig α t u :=
      hequiv.mp hA
    rw [if_pos hA, if_pos hB.1, if_pos hB.2, mul_one]
  · have hB : ¬ (linkConsistent α t u ∧ u' = wordConfig α t u) :=
      fun hh => hA (hequiv.mpr hh)
    rw [if_neg hA]
    by_cases hc : linkConsistent α t u
    · have hu : u' ≠ wordConfig α t u := fun hh => hB ⟨hc, hh⟩
      rw [if_pos hc, if_neg hu, mul_zero]
    · rw [if_neg hc, zero_mul]

/-- (1c) **The channel form.**  The δ of a configuration
against a forced configuration splits over an intermediate
configuration `s`, exactly as the assembly's features
consume it. -/
theorem channel_split (W u' : LayerLink N → G) :
    ∏ ℓ, deltaFn (W ℓ) (u' ℓ)
      = ∑ s : LayerLink N → G,
          (∏ ℓ, deltaFn (s ℓ) (W ℓ))
            * star (∏ ℓ, deltaFn (s ℓ) (u' ℓ)) := by
  have hterm : ∀ s : LayerLink N → G,
      (∏ ℓ, deltaFn (s ℓ) (W ℓ))
          * star (∏ ℓ, deltaFn (s ℓ) (u' ℓ))
        = (if W = s then (1 : ℂ) else 0) * (if u' = s then 1 else 0) := by
    intro s
    rw [star_prod]
    rw [Finset.prod_congr rfl (fun ℓ _ => deltaFn_star (s ℓ) (u' ℓ))]
    rw [prod_deltaFn_eq, prod_deltaFn_eq]
  calc ∏ ℓ, deltaFn (W ℓ) (u' ℓ)
      = if u' = W then (1 : ℂ) else 0 := prod_deltaFn_eq W u'
    _ = ∑ s : LayerLink N → G,
          (if W = s then (1 : ℂ) else 0) * (if u' = s then 1 else 0) := by
        rw [Finset.sum_eq_single W]
        · by_cases hu : u' = W <;> simp [hu]
        · intro s _ hs
          rw [if_neg (Ne.symm hs), zero_mul]
        · simp
    _ = ∑ s : LayerLink N → G,
          (∏ ℓ, deltaFn (s ℓ) (W ℓ))
            * star (∏ ℓ, deltaFn (s ℓ) (u' ℓ)) :=
        Finset.sum_congr rfl fun s _ => (hterm s).symm

end WordContraction

end ThetLogos
