/-
# G-1 (one-dimensional sector) — finite-group certificates for
representations of dimension one

Menu item **G-1** of the Gram/SOS scoping
(`~/workspace/your_files/gram-sos-lkp-scoping-2026-11-05.md`, §4):
finite-group certificates for `LayerKernelPos`.  This module
lands the **one-dimensional sector** of G-1, and names the rest
of G-1 open on its face (see the scope split below).

## What is proved here

For **every finite group `G`** (no commutativity hypothesis),
every **one-dimensional** unitary representation
`ρ : G →* unitaryGroup (Fin 1) ℂ`, every **even `N`**, and every
`β ≥ 0`: `LayerKernelPos μG ρ β` at any Haar probability measure
`μG` on `G` — discharged through the G-0 certificate
infrastructure (`LayerKernelSOSCert.layerKernelPos`,
`LayerKernelGramCert.lean`), so the certificate vocabulary of
§2 of the scoping covers this whole sector:

* the column expansion (§2) is the character's own exponential
  series regrouped modulo `k = |G|` (the character's values are
  roots of unity because `g^|G| = 1`): with
  `A_j(β) = ∑'_{m ≡ j (mod k)} (β/2)^m / m! ≥ 0` for `β ≥ 0`,
  `exp(−β·dens) = e^{−β} · (∑_j A_j ψ^j)(∑_l A_l ψ^{−l})`, a
  finite nonnegative combination of the homomorphisms `ψ^{j−l}`;
* the separation identities (§2) for one-dimensional types are
  the **character filter**: a pattern of character powers
  separates iff at every site the total character is trivial,
  because `∑_{a ∈ G} χ(a) = 0` for every nontrivial
  `χ : G → ℂˣ` (translation invariance) — the same mechanism as
  the landed parity filter (binary seat / abelian family) and
  the mod-3 filter (ternary seat), here proved once for all
  finite groups and all one-dimensional characters.  In
  particular this sector's `LayerKernelPos` conclusions subsume
  those of all three G-0b instances (binary seat, abelian
  family, ternary seat are all `d = 1`); no landed brick is
  re-pointed — the registrations in `LayerKernelGramCertInstances`
  stand untouched, per the commission.

## The scope split — what is NOT in this module

G-1 as scoped also covers **higher-dimensional** `ρ`.  That
sector is **NOT built here and stays open**, named exactly:

* The column expansion generalizes (the probe at `(N=2, D₄,
  std)` computed all five coefficients `≥ 0` exactly; no
  negative coefficient exists there).  **K-GRAM-SECTOR does
  NOT fire**: no seat, character, or coefficient failure was
  found — at D₄ or anywhere the probe reached.
* What is missing is proof, not sign: the separation identities
  for types of dimension `≥ 2` are tensor-contraction
  (Weingarten-type) identities for products of matrix
  coefficients over the column graph.  Neither the pinned
  Mathlib (finite-group character theory stops at character
  orthogonality) nor this module formalizes them.  The first
  seat of that sector is D₄ with its 2-dimensional standard
  representation — G-1's D₄ instance, and with it the stronger
  all-`F` form of R2's PSD question, remains open with the
  sector.  R2 itself is not fired, subsumed, or repriced by
  this module.
* Odd `N` is out of scope exactly as scoped (the column form
  `layerDensSum_eq_sum_columns` is an even-`N` identity).
* The certificate and the headline carry a
  `[DecidableEq (LayerLink N)]` instance hypothesis (the same
  side condition `famSOSCert` ships with in G-0b); it is used
  only to form the finite configuration type
  `LayerLink N → G`.

**K-GRAM-DEGEN does not fire on this sector**: at `β > 0` with
`ψ` nontrivial the features below are genuinely
configuration-dependent (the filter's survivors include
patterns whose features are nonconstant character products);
the trivial-character case has constant kernel because the
density vanishes identically, which is the `β = 0` shape at a
trivial representation, not a FACT-shaped degeneracy.

NO CLAIM; dials 0/4.  `LayerKernelPos` in general at `β > 0`
remains OPEN.
-/

import ThetLogos.LayerKernelGramCert

open MeasureTheory Finset
open scoped Matrix ENNReal NNReal

namespace ThetLogos

section FiniteHaar

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]
  [MeasurableSpace G] [MeasurableSingletonClass G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] [DiscreteTopology G]
  (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]

/-- On a finite type with singleton-class measurable space,
every complex-valued function is integrable against a finite
measure: it is measurable (countable discrete domain) and
bounded by the finite sum of its norms. -/
theorem integrable_of_fintype {X : Type*} [Fintype X]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    {μ : Measure X} [IsFiniteMeasure μ] (f : X → ℂ) :
    Integrable f μ := by
  refine Integrable.of_bound (μ := μ) (f := f)
    (measurable_of_countable f).aestronglyMeasurable
    (∑ x, ‖f x‖) ?_
  filter_upwards with a
  exact Finset.single_le_sum (fun x _ => norm_nonneg _)
    (Finset.mem_univ a)

/-- A Haar probability measure on a finite group gives every
singleton the same mass: left invariance moves any singleton
to any other. -/
theorem measure_singleton_eq (a b : G) : μG {a} = μG {b} := by
  have h := Measure.IsMulLeftInvariant.map_mul_left_eq_self
    (μ := μG) (b * a⁻¹)
  have h2 : μG {b}
      = (Measure.map (fun x => (b * a⁻¹) * x) μG) {b} := by rw [h]
  rw [h2, Measure.map_apply (by measurability)
    (MeasurableSet.singleton b)]
  congr 1
  ext x
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  constructor
  · intro hx
    rw [hx]; group
  · intro hx
    have h3 := congrArg (fun y : G => (a * b⁻¹) * y) hx
    have e1 : (a * b⁻¹) * ((b * a⁻¹) * x) = x := by group
    have e2 : (a * b⁻¹) * b = a := by group
    rwa [e1, e2] at h3

/-- Hence every singleton has real mass `(card G)⁻¹`: a Haar
probability measure on a finite group is the uniform
probability measure. -/
theorem measureReal_singleton_eq (a : G) :
    μG.real {a} = (Fintype.card G : ℝ)⁻¹ := by
  have heq : ∀ b : G, μG.real {b} = μG.real {1} := by
    intro b
    rw [measureReal_def, measureReal_def,
      measure_singleton_eq μG b 1]
  have hsum : ∑ b : G, μG.real {b} = 1 := by
    have h := integral_fintype (μ := μG) (f := fun _ : G => (1 : ℂ))
      (integrable_of_fintype _)
    have hru : μG.real Set.univ = 1 := by
      rw [measureReal_def, measure_univ, ENNReal.toReal_one]
    rw [integral_const, hru, one_smul] at h
    have h2 : ∑ b : G, μG.real {b} • (1 : ℂ)
        = ((∑ b : G, μG.real {b} : ℝ) : ℂ) := by
      rw [Complex.ofReal_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [Complex.real_smul, mul_one]
    rw [h2] at h
    have h3 : ((∑ b : G, μG.real {b} : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := by
      rw [Complex.ofReal_one]; exact h.symm
    exact Complex.ofReal_injective h3
  have hmul : (Fintype.card G : ℝ) * μG.real {a} = 1 := by
    have e : (∑ b : G, μG.real {b})
        = ∑ _b : G, μG.real {a} :=
      Finset.sum_congr rfl fun b _ => by rw [heq b, heq a]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at e
    exact e.symm.trans hsum
  have hcard : (Fintype.card G : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_pos.ne'
  calc μG.real {a}
      = (Fintype.card G : ℝ)⁻¹
          * ((Fintype.card G : ℝ) * μG.real {a}) := by
        rw [inv_mul_cancel_left₀ hcard]
    _ = (Fintype.card G : ℝ)⁻¹ := by rw [hmul, mul_one]

/-- Integrals against a Haar probability measure on a finite
group are uniform finite averages. -/
theorem integral_eq_card_inv_sum (f : G → ℂ) :
    ∫ a, f a ∂μG
      = ((Fintype.card G : ℝ)⁻¹) • ∑ a, f a := by
  rw [integral_fintype (integrable_of_fintype f)]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [measureReal_singleton_eq μG a]

/-- The product-measure version over a finite index type:
integrals over the configuration/stratum type are uniform
finite averages with the configuration count. -/
theorem integral_pi_eq_card_inv_sum {ι : Type*} [Fintype ι]
    [DecidableEq ι] (f : (ι → G) → ℂ) :
    ∫ u, f u ∂(Measure.pi fun _ : ι => μG)
      = ((Fintype.card (ι → G) : ℝ)⁻¹) • ∑ u, f u := by
  rw [integral_fintype (integrable_of_fintype f)]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  have hpi : (Measure.pi fun _ : ι => μG) {u}
      = ∏ i, μG {u i} := by
    have hset : ({u} : Set (ι → G))
        = Set.pi Set.univ (fun i => {u i}) := by
      ext v
      simp only [Set.mem_singleton_iff, Set.mem_pi]
      constructor
      · intro hv i _
        rw [hv]
      · intro hv
        funext i
        exact hv i (Set.mem_univ i)
    rw [hset, MeasureTheory.Measure.pi_pi]
  have hreal : (Measure.pi fun _ : ι => μG).real {u}
      = ∏ i, μG.real {u i} := by
    rw [measureReal_def, hpi, ENNReal.toReal_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [measureReal_def]
  rw [hreal]
  rw [Finset.prod_congr rfl
    (fun i _ => measureReal_singleton_eq μG (u i))]
  rw [Finset.prod_const, Finset.card_univ, inv_pow, ← Nat.cast_pow,
    ← Fintype.card_fun]

/-- **The character filter, sum form.**  For a homomorphism
`θ : G → ℂˣ` (given by its multiplication law), the sum of its
values over a finite group is the cardinality if `θ` is
trivial and `0` otherwise — translation by an element where
`θ ≠ 1` negates the sum. -/
theorem sum_coe_units_hom_eq (θ : G → ℂˣ)
    (hθ : ∀ a b, θ (a * b) = θ a * θ b) :
    (∑ a, ((θ a : ℂˣ) : ℂ))
      = if (∀ a, θ a = 1) then (Fintype.card G : ℂ) else 0 := by
  by_cases h : ∀ a, θ a = 1
  · rw [if_pos h]
    have h1 : ∀ a : G, ((θ a : ℂˣ) : ℂ) = 1 := fun a => by
      rw [h a]; rfl
    trans ∑ _a : G, (1 : ℂ)
    · exact Finset.sum_congr rfl fun a _ => h1 a
    · rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  · rw [if_neg h]
    push_neg at h
    obtain ⟨a₀, ha₀⟩ := h
    have hS : ((θ a₀ : ℂˣ) : ℂ) * ∑ a, ((θ a : ℂˣ) : ℂ)
        = ∑ a, ((θ a : ℂˣ) : ℂ) := by
      calc ((θ a₀ : ℂˣ) : ℂ) * ∑ a, ((θ a : ℂˣ) : ℂ)
          = ∑ a, ((θ a₀ : ℂˣ) : ℂ) * ((θ a : ℂˣ) : ℂ) :=
            Finset.mul_sum (s := Finset.univ)
              (f := fun a : G => ((θ a : ℂˣ) : ℂ))
              (a := ((θ a₀ : ℂˣ) : ℂ))
        _ = ∑ a, ((θ (a₀ * a) : ℂˣ) : ℂ) :=
            Finset.sum_congr rfl fun a _ => by
              rw [hθ, Units.val_mul]
        _ = ∑ a, ((θ a : ℂˣ) : ℂ) :=
            Equiv.sum_comp (Equiv.mulLeft a₀)
              (fun a : G => ((θ a : ℂˣ) : ℂ))
    have hne : ((θ a₀ : ℂˣ) : ℂ) ≠ 1 := by
      intro hh
      apply ha₀
      ext
      rw [hh]
      rfl
    have hzero : (((θ a₀ : ℂˣ) : ℂ) - 1)
        * ∑ a, ((θ a : ℂˣ) : ℂ) = 0 := by
      rw [sub_mul, hS, one_mul, sub_self]
    rcases mul_eq_zero.mp hzero with h1 | h2
    · exact absurd (sub_eq_zero.mp h1) hne
    · exact h2

end FiniteHaar

section ExpCoeff

/-- The mod-`k` regrouped exponential coefficients
`A_j(β) = ∑'_{m ≡ j (mod k)} (β/2)^m / m!`.  For `β ≥ 0` every
`A_j(β) ≥ 0` — these are the nonnegative column-expansion
coefficients of §2 of the scoping at one-dimensional types. -/
noncomputable def gramCoeffA (β : ℝ) (k : ℕ) (j : Fin k) : ℝ :=
  ∑' m : {m : ℕ // m % k = j.val}, (β / 2) ^ m.val / (Nat.factorial m.val : ℝ)

theorem summable_gramCoeffA (β : ℝ) (k : ℕ) (j : Fin k) :
    Summable (fun m : {m : ℕ // m % k = j.val} =>
      (β / 2) ^ m.val / (Nat.factorial m.val : ℝ)) :=
  (Real.summable_pow_div_factorial (β / 2)).comp_injective
    Subtype.val_injective

theorem gramCoeffA_nonneg {β : ℝ} (hβ : 0 ≤ β) (k : ℕ)
    (j : Fin k) : 0 ≤ gramCoeffA β k j :=
  tsum_nonneg fun m =>
    div_nonneg (pow_nonneg (by linarith) _) (Nat.cast_nonneg _)

/-- The exponential of a root of unity, regrouped: if
`z ^ k = 1`, then `exp(βz/2) = ∑_{j<k} A_j(β) z^j`.  The full
exponential series is the fiberwise sum over residue classes
modulo `k`, and on each fiber `z ^ m = z ^ (m % k)`. -/
theorem exp_half_eq {β : ℝ} (k : ℕ) (hk : 0 < k) (z : ℂ)
    (hz : z ^ k = 1) :
    Complex.exp ((β : ℂ) / 2 * z)
      = ∑ j : Fin k, (gramCoeffA β k j : ℂ) * z ^ j.val := by
  have hexp : Complex.exp ((β : ℂ) / 2 * z)
      = ∑' m : ℕ, (((β : ℂ) / 2) ^ m / (Nat.factorial m : ℂ)) * z ^ m := by
    conv_lhs => rw [Complex.exp_eq_exp_ℂ, NormedSpace.exp_eq_tsum ℂ]
    refine tsum_congr fun m => ?_
    simp only [smul_eq_mul]
    rw [mul_pow, div_eq_mul_inv]
    ring
  have hnorm : ‖z‖ = 1 := by
    have h1 : ‖z‖ ^ k = 1 := by
      rw [← norm_pow, hz, norm_one]
    have h2 : 0 ≤ ‖z‖ := norm_nonneg z
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hlt1 := pow_lt_one₀ h2 hlt hk.ne'
      linarith
    · have hgt1 := one_lt_pow₀ hgt hk.ne'
      linarith
  have hsumm : Summable
      (fun m : ℕ => (((β : ℂ) / 2) ^ m / (Nat.factorial m : ℂ)) * z ^ m) := by
    refine Summable.of_norm_bounded
      (g := fun m : ℕ => (|β| / 2) ^ m / (Nat.factorial m : ℝ))
      (Real.summable_pow_div_factorial _) fun m => ?_
    rw [norm_mul, norm_div, norm_pow, norm_pow, hnorm, one_pow,
      mul_one]
    have hβ2 : ‖((β : ℂ) / 2)‖ = |β| / 2 := by
      rw [show ((β : ℂ) / 2) = ((β / 2 : ℝ) : ℂ) by
            push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs, abs_div, abs_two]
    have hm : ‖((Nat.factorial m : ℂ))‖ = (Nat.factorial m : ℝ) :=
      norm_natCast (Nat.factorial m)
    rw [hm, hβ2]
  have hhas : HasSum
      (fun m : ℕ => (((β : ℂ) / 2) ^ m / (Nat.factorial m : ℂ)) * z ^ m)
      (Complex.exp ((β : ℂ) / 2 * z)) := hexp ▸ hsumm.hasSum
  have hfib := hhas.tsum_fiberwise
    (fun m : ℕ => (⟨m % k, Nat.mod_lt m hk⟩ : Fin k))
  rw [← hfib.tsum_eq, tsum_fintype]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hfibeq : ∑' m : ↥((fun m : ℕ =>
        (⟨m % k, Nat.mod_lt m hk⟩ : Fin k)) ⁻¹' {j}),
        (((β : ℂ) / 2) ^ m.val / (Nat.factorial m.val : ℂ)) * z ^ m.val
      = ∑' m : {m : ℕ // m % k = j.val},
        (((β : ℂ) / 2) ^ m.val / (Nat.factorial m.val : ℂ)) * z ^ m.val := by
    set e : ↥((fun m : ℕ =>
          (⟨m % k, Nat.mod_lt m hk⟩ : Fin k)) ⁻¹' {j})
        ≃ {m : ℕ // m % k = j.val} :=
      Equiv.subtypeEquivRight fun m => by
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Fin.ext_iff]
      with he
    calc ∑' m : ↥((fun m : ℕ =>
            (⟨m % k, Nat.mod_lt m hk⟩ : Fin k)) ⁻¹' {j}),
          (((β : ℂ) / 2) ^ m.val / (Nat.factorial m.val : ℂ)) * z ^ m.val
        = ∑' m : ↥((fun m : ℕ =>
            (⟨m % k, Nat.mod_lt m hk⟩ : Fin k)) ⁻¹' {j}),
          (((β : ℂ) / 2) ^ (e m).val / (Nat.factorial (e m).val : ℂ))
            * z ^ (e m).val := by
          refine tsum_congr fun c => ?_
          have hc : (e c).val = c.val := by rw [he]; rfl
          rw [hc]
      _ = ∑' m : {m : ℕ // m % k = j.val},
          (((β : ℂ) / 2) ^ m.val / (Nat.factorial m.val : ℂ))
            * z ^ m.val :=
          e.tsum_eq (fun m : {m : ℕ // m % k = j.val} =>
            (((β : ℂ) / 2) ^ m.val / (Nat.factorial m.val : ℂ))
              * z ^ m.val)
  rw [hfibeq]
  calc ∑' m : {m : ℕ // m % k = j.val},
        (((β : ℂ) / 2) ^ m.val / (Nat.factorial m.val : ℂ)) * z ^ m.val
      = ∑' m : {m : ℕ // m % k = j.val},
        (((β : ℂ) / 2) ^ m.val / (Nat.factorial m.val : ℂ)) * z ^ j.val := by
        refine tsum_congr fun m => ?_
        have hzm : z ^ m.val = z ^ j.val := by
          have hm : m.val = k * (m.val / k) + m.val % k :=
            (Nat.div_add_mod m.val k).symm
          conv_lhs => rw [hm, m.prop, pow_add, pow_mul, hz, one_pow,
            one_mul]
        rw [hzm]
    _ = (∑' m : {m : ℕ // m % k = j.val},
        ((β : ℂ) / 2) ^ m.val / (Nat.factorial m.val : ℂ)) * z ^ j.val :=
        tsum_mul_right
    _ = (gramCoeffA β k j : ℂ) * z ^ j.val := by
        congr 1
        rw [gramCoeffA, Complex.ofReal_tsum]
        refine tsum_congr fun m => ?_
        push_cast
        ring

end ExpCoeff

section OneDimChar

variable {G : Type*} [Group G] [Fintype G]
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin 1) ℂ))

/-- The character of a one-dimensional representation, as a
unit of `ℂ`: the `(0, 0)` entry of the unitary matrix.  The
inverse component is its conjugate, by the `(0, 0)` entry of
the unitarity identity `star A * A = 1` at size one. -/
noncomputable def gramCharUnit (g : G) : ℂˣ where
  val := repMatrix ρ g 0 0
  inv := star (repMatrix ρ g 0 0)
  val_inv := by
    have h00 : (star (repMatrix ρ g) * repMatrix ρ g) 0 0 = 1 := by
      rw [Matrix.mem_unitaryGroup_iff'.mp (repMatrix_mem ρ g)]
      exact Matrix.one_apply_eq 0
    rw [Matrix.mul_apply, Fin.sum_univ_one, Matrix.star_apply] at h00
    rw [mul_comm]
    exact h00
  inv_val := by
    have h00 : (star (repMatrix ρ g) * repMatrix ρ g) 0 0 = 1 := by
      rw [Matrix.mem_unitaryGroup_iff'.mp (repMatrix_mem ρ g)]
      exact Matrix.one_apply_eq 0
    rw [Matrix.mul_apply, Fin.sum_univ_one, Matrix.star_apply] at h00
    exact h00

/-- The character as a group homomorphism `G →* ℂˣ`: matrix
multiplication at size one is entry multiplication. -/
noncomputable def gramChar : G →* ℂˣ where
  toFun := gramCharUnit ρ
  map_one' := by
    ext
    show repMatrix ρ 1 0 0 = 1
    rw [repMatrix_one]
    exact Matrix.one_apply_eq 0
  map_mul' := by
    intro a b
    ext
    show repMatrix ρ (a * b) 0 0
        = repMatrix ρ a 0 0 * repMatrix ρ b 0 0
    rw [repMatrix_mul, Matrix.mul_apply, Fin.sum_univ_one]

theorem gramChar_coe (g : G) :
    ((gramChar ρ g : ℂˣ) : ℂ) = repMatrix ρ g 0 0 := rfl

/-- The `(0, 0)` entry of the unitarity identity, in scalar
form: `conj ψ * ψ = 1` for the character value `ψ`. -/
theorem gramChar_star_mul (g : G) :
    star (((gramChar ρ g : ℂˣ) : ℂ)) * ((gramChar ρ g : ℂˣ) : ℂ)
      = 1 := by
  rw [gramChar_coe]
  have h := congrFun (congrFun
    (Matrix.mem_unitaryGroup_iff'.mp (repMatrix_mem ρ g)) 0) 0
  rwa [Matrix.mul_apply, Fin.sum_univ_one, Matrix.star_apply,
    Matrix.one_apply_eq] at h

theorem gramChar_norm (g : G) :
    ‖((gramChar ρ g : ℂˣ) : ℂ)‖ = 1 := by
  have h2 := Complex.conj_mul' (((gramChar ρ g : ℂˣ) : ℂ))
  rw [starRingEnd_apply, gramChar_star_mul] at h2
  have h1 : ‖((gramChar ρ g : ℂˣ) : ℂ)‖ ^ 2 = 1 := by
    have h3 : ((‖((gramChar ρ g : ℂˣ) : ℂ)‖ ^ 2 : ℝ) : ℂ)
        = ((1 : ℝ) : ℂ) := by
      push_cast
      exact h2.symm
    exact Complex.ofReal_injective h3
  rcases sq_eq_one_iff.mp h1 with h | h
  · exact h
  · have hnn := norm_nonneg (((gramChar ρ g : ℂˣ) : ℂ))
    linarith

/-- At dimension one the corpus character function is the
unit's value: the trace over `Fin 1` is the single entry. -/
theorem charFn_gramChar (g : G) :
    charFn ρ g = ((gramChar ρ g : ℂˣ) : ℂ) := by
  rw [charFn, Matrix.trace, gramChar_coe]
  simp [Matrix.diag]

/-- At dimension one the G-0 density is `1 - Re ψ`: the
dimension cast is `1`. -/
theorem gramDens_gramChar (g : G) :
    gramDens ρ g = 1 - (((gramChar ρ g : ℂˣ) : ℂ)).re := by
  rw [gramDens, charFn_gramChar]
  simp

/-- The character's values are roots of unity of order
dividing `|G|`: `g ^ |G| = 1` in any finite group. -/
theorem gramChar_pow_card (g : G) :
    ((gramChar ρ g) ^ (Fintype.card G) : ℂˣ) = 1 := by
  rw [← map_pow, pow_card_eq_one, map_one]

theorem gramChar_coe_pow_card (g : G) :
    (((gramChar ρ g : ℂˣ) : ℂ)) ^ (Fintype.card G) = 1 := by
  have h := congrArg (fun u : ℂˣ => (u : ℂ)) (gramChar_pow_card ρ g)
  rwa [Units.val_pow_eq_pow_val, Units.val_one] at h

/-- The conjugate of the character value is its inverse:
`star ψ * ψ = 1` and the field inverse is unique. -/
theorem gramChar_star_coe (g : G) :
    star ((gramChar ρ g : ℂˣ) : ℂ)
      = (((gramChar ρ g : ℂˣ) : ℂ))⁻¹ := by
  have h2 := inv_eq_of_mul_eq_one_right (gramChar_star_mul ρ g)
  have h3 := congrArg Inv.inv h2
  rw [inv_inv] at h3
  exact h3

end OneDimChar

section Expansion

variable {G : Type*} [Group G] [Fintype G]
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin 1) ℂ))

/-- The certificate coefficients at a one-dimensional type:
`e^{-β} · A_j(β) · A_l(β)` on the index type
`Fin |G| × Fin |G|` of character powers. -/
noncomputable def gramCoeff (β : ℝ)
    (t : Fin (Fintype.card G) × Fin (Fintype.card G)) : ℝ :=
  Real.exp (-β) * gramCoeffA β (Fintype.card G) t.1
    * gramCoeffA β (Fintype.card G) t.2

/-- The certificate characters at a one-dimensional type: the
values of `ψ ^ (j - l)`, the difference of the two regrouped
exponential halves. -/
noncomputable def gramCharFn
    (t : Fin (Fintype.card G) × Fin (Fintype.card G)) (g : G) :
    ℂ :=
  ((gramChar ρ g) ^ ((t.1.val : ℤ) - (t.2.val : ℤ)) : ℂ)

theorem gramCoeff_nonneg {β : ℝ} (hβ : 0 ≤ β)
    (t : Fin (Fintype.card G) × Fin (Fintype.card G)) :
    0 ≤ gramCoeff β t :=
  mul_nonneg
    (mul_nonneg (Real.exp_nonneg _)
      (gramCoeffA_nonneg hβ _ _))
    (gramCoeffA_nonneg hβ _ _)

/-- **The column expansion at a one-dimensional type** (the
expansion identity of §2 of the scoping): the Boltzmann factor
of the density `1 - Re ψ` is a finite nonnegative combination
of the character powers `ψ ^ (j - l)`.  The two halves of
`exp(β·Re ψ)` are `exp(βψ/2)` and `exp(βψ⁻¹/2)`, each
regrouped modulo `|G|` by `exp_half_eq`. -/
theorem gram_expansion {β : ℝ} (g : G) :
    ((Real.exp (-β * gramDens ρ g) : ℝ) : ℂ)
      = ∑ t : Fin (Fintype.card G) × Fin (Fintype.card G),
        ((gramCoeff β t : ℝ) : ℂ) * gramCharFn ρ t g := by
  set k := Fintype.card G with hk
  have hkpos : 0 < k := Fintype.card_pos
  have hψk : ((gramChar ρ g : ℂˣ) : ℂ) ^ k = 1 :=
    gramChar_coe_pow_card ρ g
  have hψinv : (((gramChar ρ g : ℂˣ) : ℂ)⁻¹) ^ k = 1 := by
    rw [inv_pow, hψk, inv_one]
  have hre : ((((gramChar ρ g : ℂˣ) : ℂ).re : ℝ) : ℂ)
      = (((gramChar ρ g : ℂˣ) : ℂ)
          + ((gramChar ρ g : ℂˣ) : ℂ)⁻¹) / 2 := by
    have h := Complex.add_conj (((gramChar ρ g : ℂˣ) : ℂ))
    rw [starRingEnd_apply, gramChar_star_coe] at h
    rw [h]
    push_cast
    ring
  have harg : ((Real.exp (-β * gramDens ρ g) : ℝ) : ℂ)
      = Complex.exp (-(β : ℂ))
          * Complex.exp ((β : ℂ) / 2 * ((gramChar ρ g : ℂˣ) : ℂ))
          * Complex.exp
            ((β : ℂ) / 2 * ((gramChar ρ g : ℂˣ) : ℂ)⁻¹) := by
    have e1 : (-β * gramDens ρ g : ℝ)
        = -β + β * ((gramChar ρ g : ℂˣ) : ℂ).re := by
      rw [gramDens_gramChar]; ring
    rw [e1, Complex.ofReal_exp]
    have e2 : ((-β + β * ((gramChar ρ g : ℂˣ) : ℂ).re : ℝ) : ℂ)
        = -(β : ℂ) + (β : ℂ) / 2 * ((gramChar ρ g : ℂˣ) : ℂ)
          + (β : ℂ) / 2 * ((gramChar ρ g : ℂˣ) : ℂ)⁻¹ := by
      push_cast
      rw [hre]
      ring
    rw [e2, Complex.exp_add, Complex.exp_add]
  rw [harg, exp_half_eq k hkpos _ hψk, exp_half_eq k hkpos _ hψinv,
    Fintype.sum_prod_type]
  have hterm : ∀ j l : Fin k,
      ((gramCoeff β (j, l) : ℝ) : ℂ) * gramCharFn ρ (j, l) g
        = (Complex.exp (-(β : ℂ))
            * ((gramCoeffA β k j : ℂ)
              * ((gramChar ρ g : ℂˣ) : ℂ) ^ j.val))
          * ((gramCoeffA β k l : ℂ)
            * (((gramChar ρ g : ℂˣ) : ℂ)⁻¹) ^ l.val) := by
    intro j l
    have hc : ((gramChar ρ g : ℂˣ) : ℂ) ^ ((j.val : ℤ) - (l.val : ℤ))
        = ((gramChar ρ g : ℂˣ) : ℂ) ^ j.val
          * (((gramChar ρ g : ℂˣ) : ℂ)⁻¹) ^ l.val := by
      have hne : ((gramChar ρ g : ℂˣ) : ℂ) ≠ 0 := by
        intro h
        have hn := gramChar_norm ρ g
        rw [h, norm_zero] at hn
        exact zero_ne_one hn
      rw [zpow_sub₀ hne, zpow_natCast, zpow_natCast, div_eq_mul_inv,
        inv_pow]
    show ((gramCoeff β (j, l) : ℝ) : ℂ) * gramCharFn ρ (j, l) g = _
    rw [gramCoeff, gramCharFn]
    show ((Real.exp (-β) * gramCoeffA β (Fintype.card G) j
          * gramCoeffA β (Fintype.card G) l : ℝ) : ℂ)
        * (((gramChar ρ g : ℂˣ) : ℂ) ^ ((j.val : ℤ) - (l.val : ℤ)))
        = _
    rw [hc]
    push_cast
    ring
  rw [Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun l _ => hterm j l]
  rw [← Finset.sum_mul_sum, Finset.mul_sum Finset.univ
    (fun j : Fin k => (gramCoeffA β k j : ℂ)
      * ((gramChar ρ g : ℂˣ) : ℂ) ^ j.val)
    (Complex.exp (-(β : ℂ)))]

end Expansion

section Separation

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]
  [MeasurableSpace G] [MeasurableSingletonClass G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] [DiscreteTopology G]
  (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin 1) ℂ))
  {N : ℕ} [NeZero N]

/-- The character-power exponent a pattern assigns to one
column: `j - l` for the character index `(j, l)`. -/
noncomputable def gramPatExp
    (ε : LayerColumn N → Fin (Fintype.card G) × Fin (Fintype.card G))
    (P : LayerColumn N) : ℤ :=
  (ε P).1.val - (ε P).2.val

open Classical in
/-- The total character exponent a pattern leaves at the site
`c` after all columns are expanded: columns based at `c`
contribute positively, columns whose shifted link lands at
`c` negatively (the plaquette word's `α c` and
`(α (σ c))⁻¹` parts). -/
noncomputable def gramSiteExp
    (ε : LayerColumn N → Fin (Fintype.card G) × Fin (Fintype.card G))
    (c : LayerSite N) : ℤ :=
  (∑ P ∈ Finset.univ.filter (fun P => P.1 = c), gramPatExp ε P)
    - ∑ P ∈ Finset.univ.filter
        (fun P => layerShift P.2.1 P.2.2 P.1 = c), gramPatExp ε P

/-- A pattern survives the character filter iff at every site
its total character is trivial: then (and only then) the
stratum integral of its character product is nonzero. -/
def gramSurvives
    (ε : LayerColumn N → Fin (Fintype.card G) × Fin (Fintype.card G)) :
    Prop :=
  ∀ c, ∀ a : G, (gramChar ρ a) ^ (gramSiteExp ε c) = 1

/-- The pattern's feature as a unit: the product of the link
characters at the negative pattern exponents — the `u`-side
of the separation identity. -/
noncomputable def gramFeatUnit
    (ε : LayerColumn N → Fin (Fintype.card G) × Fin (Fintype.card G))
    (u : LayerLink N → G) : ℂˣ :=
  ∏ P, (gramChar ρ (u (layerLinkOf P.1 P.2.1 P.2.2)))
    ^ (-(gramPatExp ε P))

open Classical in
/-- The certificate feature: the feature unit's value on
surviving patterns, `0` on filtered-out patterns — the same
filter-inside-feature shape as the landed binary/ternary
seats. -/
noncomputable def gramFeat
    (ε : LayerColumn N → Fin (Fintype.card G) × Fin (Fintype.card G))
    (u : LayerLink N → G) : ℂ :=
  if gramSurvives ρ ε then ((gramFeatUnit ρ ε u : ℂˣ) : ℂ) else 0

/-- Powers distribute over finite products in `ℂˣ` as sums in
the exponent. -/
theorem prod_zpow_eq_zpow_sum {ι : Type*} [DecidableEq ι]
    (a : ℂˣ) (s : Finset ι) (e : ι → ℤ) :
    ∏ i ∈ s, a ^ e i = a ^ (∑ i ∈ s, e i) := by
  induction s using Finset.induction with
  | empty => simp
  | insert i s hi ih =>
      rw [Finset.prod_insert hi, ih, Finset.sum_insert hi, zpow_add]

/-- **The separation identity at a one-dimensional type** (the
separation identities of §2 of the scoping): over a column
pattern, the product of the plaquette-word characters splits
as the `u'`-characters, the `u`-feature unit, and one
character per site at the site exponent.  Each column word
`α c · u' ℓ · (α (σ c))⁻¹ · (u ℓ)⁻¹` contributes its four
character factors; the `α` factors regroup site by site. -/
theorem prod_gramChar_colWord
    (ε : LayerColumn N → Fin (Fintype.card G) × Fin (Fintype.card G))
    (α : LayerSite N → G) (u u' : LayerLink N → G) :
    ∏ P, (gramChar ρ (colWord u u' P.1 P.2.1 P.2.2 α))
        ^ (gramPatExp ε P)
      = (∏ P, (gramChar ρ (u' (layerLinkOf P.1 P.2.1 P.2.2)))
            ^ (gramPatExp ε P))
        * gramFeatUnit ρ ε u
        * ∏ c, (gramChar ρ (α c)) ^ (gramSiteExp ε c) := by
  have hP : ∀ P : LayerColumn N,
      (gramChar ρ (colWord u u' P.1 P.2.1 P.2.2 α)) ^ (gramPatExp ε P)
        = (gramChar ρ (α P.1)) ^ (gramPatExp ε P)
          * (gramChar ρ (u' (layerLinkOf P.1 P.2.1 P.2.2)))
              ^ (gramPatExp ε P)
          * (gramChar ρ (α (layerShift P.2.1 P.2.2 P.1)))
              ^ (-(gramPatExp ε P))
          * (gramChar ρ (u (layerLinkOf P.1 P.2.1 P.2.2)))
              ^ (-(gramPatExp ε P)) := by
    intro P
    rw [colWord, map_mul, map_mul, map_mul, map_inv, map_inv,
      mul_zpow, mul_zpow, mul_zpow, inv_zpow, inv_zpow,
      ← zpow_neg, ← zpow_neg]
  have hsplit :
      ∏ P, (gramChar ρ (colWord u u' P.1 P.2.1 P.2.2 α))
          ^ (gramPatExp ε P)
        = (∏ P, (gramChar ρ (α P.1)) ^ (gramPatExp ε P))
          * (∏ P, (gramChar ρ (u' (layerLinkOf P.1 P.2.1 P.2.2)))
              ^ (gramPatExp ε P))
          * (∏ P, (gramChar ρ (α (layerShift P.2.1 P.2.2 P.1)))
              ^ (-(gramPatExp ε P)))
          * (∏ P, (gramChar ρ (u (layerLinkOf P.1 P.2.1 P.2.2)))
              ^ (-(gramPatExp ε P))) := by
    calc ∏ P, (gramChar ρ (colWord u u' P.1 P.2.1 P.2.2 α))
            ^ (gramPatExp ε P)
        = ∏ P, ((gramChar ρ (α P.1)) ^ (gramPatExp ε P)
            * (gramChar ρ (u' (layerLinkOf P.1 P.2.1 P.2.2)))
                ^ (gramPatExp ε P)
            * (gramChar ρ (α (layerShift P.2.1 P.2.2 P.1)))
                ^ (-(gramPatExp ε P))
            * (gramChar ρ (u (layerLinkOf P.1 P.2.1 P.2.2)))
                ^ (-(gramPatExp ε P))) :=
          Finset.prod_congr rfl fun P _ => hP P
      _ = (∏ P, (gramChar ρ (α P.1)) ^ (gramPatExp ε P))
            * (∏ P, (gramChar ρ (u' (layerLinkOf P.1 P.2.1 P.2.2)))
                ^ (gramPatExp ε P))
            * (∏ P, (gramChar ρ (α (layerShift P.2.1 P.2.2 P.1)))
                ^ (-(gramPatExp ε P)))
            * (∏ P, (gramChar ρ (u (layerLinkOf P.1 P.2.1 P.2.2)))
                ^ (-(gramPatExp ε P))) := by
          rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib,
            ← Finset.prod_mul_distrib]
  have hα1 : ∏ P, (gramChar ρ (α P.1)) ^ (gramPatExp ε P)
      = ∏ c, (gramChar ρ (α c))
          ^ (∑ P ∈ Finset.univ.filter (fun P => P.1 = c),
              gramPatExp ε P) := by
    rw [← Finset.prod_fiberwise_of_maps_to (s := Finset.univ)
      (t := Finset.univ) (g := fun P : LayerColumn N => P.1)
      (f := fun P : LayerColumn N =>
        (gramChar ρ (α P.1)) ^ (gramPatExp ε P))
      (fun P _ => Finset.mem_univ P.1)]
    refine Finset.prod_congr rfl fun c _ => ?_
    trans ∏ P ∈ Finset.univ.filter (fun P => P.1 = c),
        (gramChar ρ (α c)) ^ (gramPatExp ε P)
    · refine Finset.prod_congr rfl fun P hP => ?_
      rw [(Finset.mem_filter.mp hP).2]
    · exact prod_zpow_eq_zpow_sum _ _ _
  have hα2 : ∏ P, (gramChar ρ (α (layerShift P.2.1 P.2.2 P.1)))
        ^ (-(gramPatExp ε P))
      = ∏ c, (gramChar ρ (α c))
          ^ (-(∑ P ∈ Finset.univ.filter
              (fun P => layerShift P.2.1 P.2.2 P.1 = c),
              gramPatExp ε P)) := by
    rw [← Finset.prod_fiberwise_of_maps_to (s := Finset.univ)
      (t := Finset.univ)
      (g := fun P : LayerColumn N => layerShift P.2.1 P.2.2 P.1)
      (f := fun P : LayerColumn N =>
        (gramChar ρ (α (layerShift P.2.1 P.2.2 P.1)))
          ^ (-(gramPatExp ε P)))
      (fun P _ => Finset.mem_univ _)]
    refine Finset.prod_congr rfl fun c _ => ?_
    trans ∏ P ∈ Finset.univ.filter
          (fun P => layerShift P.2.1 P.2.2 P.1 = c),
        (gramChar ρ (α c)) ^ (-(gramPatExp ε P))
    · refine Finset.prod_congr rfl fun P hP => ?_
      rw [(Finset.mem_filter.mp hP).2]
    · calc ∏ P ∈ Finset.univ.filter
              (fun P => layerShift P.2.1 P.2.2 P.1 = c),
            (gramChar ρ (α c)) ^ (-(gramPatExp ε P))
          = (gramChar ρ (α c))
              ^ (∑ P ∈ Finset.univ.filter
                  (fun P => layerShift P.2.1 P.2.2 P.1 = c),
                  -(gramPatExp ε P)) :=
            prod_zpow_eq_zpow_sum _ _ _
        _ = (gramChar ρ (α c))
              ^ (-(∑ P ∈ Finset.univ.filter
                  (fun P => layerShift P.2.1 P.2.2 P.1 = c),
                  gramPatExp ε P)) := by
            rw [Finset.sum_neg_distrib]
  have hα : (∏ c, (gramChar ρ (α c))
        ^ (∑ P ∈ Finset.univ.filter (fun P => P.1 = c),
            gramPatExp ε P))
      * (∏ c, (gramChar ρ (α c))
        ^ (-(∑ P ∈ Finset.univ.filter
            (fun P => layerShift P.2.1 P.2.2 P.1 = c),
            gramPatExp ε P)))
      = ∏ c, (gramChar ρ (α c)) ^ (gramSiteExp ε c) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun c _ => ?_
    rw [← zpow_add, gramSiteExp, sub_eq_add_neg]
  rw [hsplit, hα1, hα2]
  calc (∏ c, (gramChar ρ (α c))
        ^ (∑ P ∈ Finset.univ.filter (fun P => P.1 = c),
            gramPatExp ε P))
      * (∏ P, (gramChar ρ (u' (layerLinkOf P.1 P.2.1 P.2.2)))
          ^ (gramPatExp ε P))
      * (∏ c, (gramChar ρ (α c))
        ^ (-(∑ P ∈ Finset.univ.filter
            (fun P => layerShift P.2.1 P.2.2 P.1 = c),
            gramPatExp ε P)))
      * (∏ P, (gramChar ρ (u (layerLinkOf P.1 P.2.1 P.2.2)))
          ^ (-(gramPatExp ε P)))
      = ((∏ c, (gramChar ρ (α c))
          ^ (∑ P ∈ Finset.univ.filter (fun P => P.1 = c),
              gramPatExp ε P))
        * (∏ c, (gramChar ρ (α c))
          ^ (-(∑ P ∈ Finset.univ.filter
              (fun P => layerShift P.2.1 P.2.2 P.1 = c),
              gramPatExp ε P))))
        * ((∏ P, (gramChar ρ (u' (layerLinkOf P.1 P.2.1 P.2.2)))
            ^ (gramPatExp ε P))
          * (∏ P, (gramChar ρ (u (layerLinkOf P.1 P.2.1 P.2.2)))
            ^ (-(gramPatExp ε P)))) := by
        ac_rfl
    _ = (∏ c, (gramChar ρ (α c)) ^ (gramSiteExp ε c))
        * ((∏ P, (gramChar ρ (u' (layerLinkOf P.1 P.2.1 P.2.2)))
            ^ (gramPatExp ε P))
          * (∏ P, (gramChar ρ (u (layerLinkOf P.1 P.2.1 P.2.2)))
            ^ (-(gramPatExp ε P)))) := by
        rw [hα]
    _ = (∏ P, (gramChar ρ (u' (layerLinkOf P.1 P.2.1 P.2.2)))
          ^ (gramPatExp ε P))
        * (∏ P, (gramChar ρ (u (layerLinkOf P.1 P.2.1 P.2.2)))
            ^ (-(gramPatExp ε P)))
        * ∏ c, (gramChar ρ (α c)) ^ (gramSiteExp ε c) := by
        ac_rfl

/-- The feature unit's values lie on the unit circle, so
conjugate = inverse for their coercion to `ℂ`. -/
theorem star_coe_gramFeatUnit
    (ε : LayerColumn N → Fin (Fintype.card G) × Fin (Fintype.card G))
    (u : LayerLink N → G) :
    star ((gramFeatUnit ρ ε u : ℂˣ) : ℂ)
      = (((gramFeatUnit ρ ε u : ℂˣ) : ℂ))⁻¹ := by
  have hnorm : ‖((gramFeatUnit ρ ε u : ℂˣ) : ℂ)‖ = 1 := by
    have hprod : ((gramFeatUnit ρ ε u : ℂˣ) : ℂ)
        = ∏ P, (((gramChar ρ (u (layerLinkOf P.1 P.2.1 P.2.2))
            ^ (-(gramPatExp ε P)) : ℂˣ)) : ℂ) := by
      rw [gramFeatUnit]
      exact map_prod (Units.coeHom ℂ) _ _
    have hnp : ∀ s : Finset (LayerColumn N),
        ∀ f : LayerColumn N → ℂ,
        ‖∏ P ∈ s, f P‖ = ∏ P ∈ s, ‖f P‖ := by
      intro s f
      induction s using Finset.induction with
      | empty => simp
      | insert P s hP ih =>
          rw [Finset.prod_insert hP, Finset.prod_insert hP, ← ih,
            norm_mul]
    rw [hprod, hnp]
    trans ∏ P : LayerColumn N, (1 : ℝ)
    · refine Finset.prod_congr rfl fun P _ => ?_
      rw [Units.val_zpow_eq_zpow_val, norm_zpow, gramChar_norm,
        one_zpow]
    · exact Finset.prod_const_one
  have h2 := Complex.conj_mul' ((gramFeatUnit ρ ε u : ℂˣ) : ℂ)
  rw [starRingEnd_apply] at h2
  simp only [hnorm, one_pow, Complex.ofReal_one] at h2
  have h4 := inv_eq_of_mul_eq_one_right h2
  have h5 := congrArg Inv.inv h4
  rw [inv_inv] at h5
  exact h5

/-- The `u'`-feature unit is the inverse of the pattern's
`u'`-product: exponents negate under inversion. -/
theorem coe_inv_gramFeatUnit
    (ε : LayerColumn N → Fin (Fintype.card G) × Fin (Fintype.card G))
    (u' : LayerLink N → G) :
    (((gramFeatUnit ρ ε u' : ℂˣ) : ℂ))⁻¹
      = ((∏ P, (gramChar ρ (u' (layerLinkOf P.1 P.2.1 P.2.2)))
          ^ (gramPatExp ε P) : ℂˣ) : ℂ) := by
  have hU : (gramFeatUnit ρ ε u')⁻¹
      = ∏ P, (gramChar ρ (u' (layerLinkOf P.1 P.2.1 P.2.2)))
          ^ (gramPatExp ε P) := by
    rw [gramFeatUnit, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun P _ => ?_
    rw [zpow_neg, inv_inv]
  rw [← Units.val_inv_eq_inv_val, hU]

/-- The per-site character factor of a column pattern, as a
plain function of the site variable (the shape the product-
measure factorization lemma consumes). -/
noncomputable def gramSiteChar
    (ε : LayerColumn N → Fin (Fintype.card G) × Fin (Fintype.card G))
    (c : LayerSite N) (a : G) : ℂ :=
  (((gramChar ρ a) : ℂˣ) : ℂ) ^ (gramSiteExp ε c)

/-- **The character filter, integral form.**  A pattern's
stratum integral is its feature times the conjugate feature
of `u'`: the filter `gramSurvives` decides — surviving
patterns integrate to the separated product over every site,
and one failing site annihilates the whole integral. -/
theorem integral_gramPat
    (ε : LayerColumn N → Fin (Fintype.card G) × Fin (Fintype.card G))
    (u u' : LayerLink N → G) :
    ∫ α : LayerSite N → G,
        ∏ P, (((gramChar ρ (colWord u u' P.1 P.2.1 P.2.2 α)) : ℂˣ)
            : ℂ) ^ (gramPatExp ε P)
        ∂(Measure.pi fun _ : LayerSite N => μG)
      = gramFeat ρ ε u * star (gramFeat ρ ε u') := by
  have hfact : ∀ α : LayerSite N → G,
      ∏ P, (((gramChar ρ (colWord u u' P.1 P.2.1 P.2.2 α)) : ℂˣ)
            : ℂ) ^ (gramPatExp ε P)
        = ((∏ P, (gramChar ρ (u' (layerLinkOf P.1 P.2.1 P.2.2)))
              ^ (gramPatExp ε P) : ℂˣ) : ℂ)
          * ((gramFeatUnit ρ ε u : ℂˣ) : ℂ)
          * ∏ c, (((gramChar ρ (α c)) : ℂˣ) : ℂ)
              ^ (gramSiteExp ε c) := by
    intro α
    have h1 : ∏ P, (((gramChar ρ (colWord u u' P.1 P.2.1 P.2.2 α))
              : ℂˣ) : ℂ) ^ (gramPatExp ε P)
        = ((∏ P, (gramChar ρ (colWord u u' P.1 P.2.1 P.2.2 α))
            ^ (gramPatExp ε P) : ℂˣ) : ℂ) := by
      calc ∏ P, (((gramChar ρ (colWord u u' P.1 P.2.1 P.2.2 α))
                : ℂˣ) : ℂ) ^ (gramPatExp ε P)
          = ∏ P, (((gramChar ρ (colWord u u' P.1 P.2.1 P.2.2 α))
                ^ (gramPatExp ε P) : ℂˣ) : ℂ) :=
            Finset.prod_congr rfl fun P _ =>
              (Units.val_zpow_eq_zpow_val _ _).symm
        _ = ((∏ P, (gramChar ρ (colWord u u' P.1 P.2.1 P.2.2 α))
              ^ (gramPatExp ε P) : ℂˣ) : ℂ) :=
            (map_prod (Units.coeHom ℂ) _ _).symm
    have hsite2 : ((∏ c, (gramChar ρ (α c)) ^ (gramSiteExp ε c)
          : ℂˣ) : ℂ)
        = ∏ c, (((gramChar ρ (α c)) : ℂˣ) : ℂ)
            ^ (gramSiteExp ε c) := by
      calc ((∏ c, (gramChar ρ (α c)) ^ (gramSiteExp ε c) : ℂˣ) : ℂ)
          = ∏ c, (((gramChar ρ (α c)) ^ (gramSiteExp ε c) : ℂˣ)
              : ℂ) :=
            map_prod (Units.coeHom ℂ) _ _
        _ = ∏ c, (((gramChar ρ (α c)) : ℂˣ) : ℂ)
              ^ (gramSiteExp ε c) :=
            Finset.prod_congr rfl fun c _ =>
              Units.val_zpow_eq_zpow_val _ _
    rw [h1, prod_gramChar_colWord, Units.val_mul, Units.val_mul,
      hsite2]
  have hsite : ∀ c : LayerSite N,
      ∫ a : G, gramSiteChar ρ ε c a ∂μG
        = if (∀ a : G, (gramChar ρ a) ^ (gramSiteExp ε c) = 1)
          then (1 : ℂ) else 0 := by
    intro c
    show ∫ a : G, (((gramChar ρ a) : ℂˣ) : ℂ) ^ (gramSiteExp ε c)
        ∂μG = _
    have hθ : ∀ a b : G,
        ((gramChar ρ (a * b)) ^ (gramSiteExp ε c) : ℂˣ)
          = ((gramChar ρ a) ^ (gramSiteExp ε c) : ℂˣ)
            * ((gramChar ρ b) ^ (gramSiteExp ε c) : ℂˣ) := by
      intro a b
      rw [map_mul, mul_zpow]
    have hconv : ∀ a : G, (((gramChar ρ a) : ℂˣ) : ℂ)
          ^ (gramSiteExp ε c)
        = ((gramChar ρ a) ^ (gramSiteExp ε c) : ℂˣ) :=
      fun a => (Units.val_zpow_eq_zpow_val _ _).symm
    rw [integral_congr_ae (Filter.Eventually.of_forall hconv),
      integral_eq_card_inv_sum μG,
      sum_coe_units_hom_eq (fun a => (gramChar ρ a) ^ (gramSiteExp ε c))
        hθ]
    by_cases ht : ∀ a : G, (gramChar ρ a) ^ (gramSiteExp ε c) = 1
    · rw [if_pos ht, if_pos ht]
      have hcard : (Fintype.card G : ℝ) ≠ 0 :=
        Nat.cast_ne_zero.mpr Fintype.card_pos.ne'
      rw [Complex.real_smul]
      have e : ((Fintype.card G : ℂ)) = ((Fintype.card G : ℝ) : ℂ) := by
        norm_cast
      rw [e, ← Complex.ofReal_mul, inv_mul_cancel₀ hcard,
        Complex.ofReal_one]
    · rw [if_neg ht, if_neg ht, smul_zero]
  have hθ : ∀ α : LayerSite N → G,
      ∏ c, (((gramChar ρ (α c)) : ℂˣ) : ℂ) ^ (gramSiteExp ε c)
        = ∏ c, gramSiteChar ρ ε c (α c) :=
    fun α => Finset.prod_congr rfl fun c _ => rfl
  have hInt : ∫ α : LayerSite N → G,
        ∏ P, (((gramChar ρ (colWord u u' P.1 P.2.1 P.2.2 α)) : ℂˣ)
            : ℂ) ^ (gramPatExp ε P)
        ∂(Measure.pi fun _ : LayerSite N => μG)
      = ((∏ P, (gramChar ρ (u' (layerLinkOf P.1 P.2.1 P.2.2)))
            ^ (gramPatExp ε P) : ℂˣ) : ℂ)
        * ((gramFeatUnit ρ ε u : ℂˣ) : ℂ)
        * ∏ c, (if (∀ a : G, (gramChar ρ a) ^ (gramSiteExp ε c) = 1)
            then (1 : ℂ) else 0) := by
    rw [integral_congr_ae (Filter.Eventually.of_forall hfact),
      integral_const_mul,
      integral_congr_ae (Filter.Eventually.of_forall hθ),
      integral_fintype_prod_eq_prod]
    simp only [hsite]
  rw [hInt]
  by_cases hs : gramSurvives ρ ε
  · have hone : ∏ c : LayerSite N,
        (if (∀ a : G, (gramChar ρ a) ^ (gramSiteExp ε c) = 1)
          then (1 : ℂ) else 0) = 1 := by
      refine (Finset.prod_congr rfl fun c _ => if_pos (hs c)).trans
        Finset.prod_const_one
    have hfu : gramFeat ρ ε u = ((gramFeatUnit ρ ε u : ℂˣ) : ℂ) :=
      if_pos hs
    have hfu' : gramFeat ρ ε u' = ((gramFeatUnit ρ ε u' : ℂˣ) : ℂ) :=
      if_pos hs
    rw [hone, mul_one, hfu, hfu', star_coe_gramFeatUnit,
      coe_inv_gramFeatUnit]
    exact mul_comm _ _
  · obtain ⟨c₀, hc₀⟩ := not_forall.mp hs
    have hzero : ∏ c : LayerSite N,
        (if (∀ a : G, (gramChar ρ a) ^ (gramSiteExp ε c) = 1)
          then (1 : ℂ) else 0) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ c₀) (if_neg hc₀)
    have hfu' : gramFeat ρ ε u' = 0 := if_neg hs
    rw [hzero, mul_zero, hfu', star_zero, mul_zero]

/-- The kernel itself, in certificate form: the even-`N`
column expansion of the layer kernel at a one-dimensional
type, summed over all character patterns with the
certificate weights. -/
theorem gram_kernel_eq (hN : Even N) (β : ℝ) (u u' : LayerLink N → G) :
    layerKernel μG ρ β u u'
      = ∑ ε : LayerColumn N
          → Fin (Fintype.card G) × Fin (Fintype.card G),
        ((gramColWeight (gramCoeff β) (fun ε P => ε P) ε : ℝ) : ℂ)
          * gramFeat ρ ε u * star (gramFeat ρ ε u') := by
  have hreal : ∀ α : LayerSite N → G, -(layerAction ρ β α u u')
      = ∑ P : LayerColumn N, (-β * gramDens ρ
          (colWord u u' P.1 P.2.1 P.2.2 α)) := by
    intro α
    rw [layerAction_eq, layerDensSum_eq_sum_columns ρ hN,
      Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun P _ => ?_
    have hcd : colDensC ρ u u' P α
        = gramDens ρ (colWord u u' P.1 P.2.1 P.2.2 α) := rfl
    rw [hcd, neg_mul]
  have hcol : ∀ α : LayerSite N → G,
      ((Real.exp (-(layerAction ρ β α u u')) : ℝ) : ℂ)
        = ∏ P : LayerColumn N, ((Real.exp (-β * gramDens ρ
            (colWord u u' P.1 P.2.1 P.2.2 α)) : ℝ) : ℂ) := by
    intro α
    rw [hreal α, Real.exp_sum, Complex.ofReal_prod]
  calc layerKernel μG ρ β u u'
      = ∫ α : LayerSite N → G, ∏ P : LayerColumn N,
          ((Real.exp (-β * gramDens ρ
            (colWord u u' P.1 P.2.1 P.2.2 α)) : ℝ) : ℂ)
          ∂(Measure.pi fun _ : LayerSite N => μG) := by
        unfold layerKernel
        exact integral_congr_ae (Filter.Eventually.of_forall hcol)
    _ = ∫ α : LayerSite N → G,
          ∑ ε : LayerColumn N
              → Fin (Fintype.card G) × Fin (Fintype.card G),
            ∏ P : LayerColumn N, ((gramCoeff β (ε P) : ℝ) : ℂ)
              * (((gramChar ρ (colWord u u' P.1 P.2.1 P.2.2 α))
                  : ℂˣ) : ℂ) ^ (gramPatExp ε P)
          ∂(Measure.pi fun _ : LayerSite N => μG) := by
        refine integral_congr_ae (Filter.Eventually.of_forall
          fun α => ?_)
        calc ∏ P : LayerColumn N, ((Real.exp (-β * gramDens ρ
                (colWord u u' P.1 P.2.1 P.2.2 α)) : ℝ) : ℂ)
            = ∏ P : LayerColumn N, ∑ t : Fin (Fintype.card G) × Fin (Fintype.card G),
                ((gramCoeff β t : ℝ) : ℂ) * gramCharFn ρ t
                  (colWord u u' P.1 P.2.1 P.2.2 α) :=
              Finset.prod_congr rfl fun P _ =>
                gram_expansion ρ (colWord u u' P.1 P.2.1 P.2.2 α)
          _ = ∑ ε : LayerColumn N
                → Fin (Fintype.card G) × Fin (Fintype.card G),
                ∏ P : LayerColumn N, ((gramCoeff β (ε P) : ℝ) : ℂ) * gramCharFn ρ
                  (ε P) (colWord u u' P.1 P.2.1 P.2.2 α) :=
              Fintype.prod_sum (fun (P : LayerColumn N)
                (t : Fin (Fintype.card G) × Fin (Fintype.card G)) =>
                ((gramCoeff β t : ℝ) : ℂ)
                * gramCharFn ρ t (colWord u u' P.1 P.2.1 P.2.2 α))
          _ = ∑ ε : LayerColumn N
                → Fin (Fintype.card G) × Fin (Fintype.card G),
                ∏ P : LayerColumn N, ((gramCoeff β (ε P) : ℝ) : ℂ)
                  * (((gramChar ρ (colWord u u' P.1 P.2.1 P.2.2 α))
                      : ℂˣ) : ℂ) ^ (gramPatExp ε P) :=
              Finset.sum_congr rfl fun ε _ =>
                Finset.prod_congr rfl fun P _ => rfl
    _ = ∑ ε : LayerColumn N
          → Fin (Fintype.card G) × Fin (Fintype.card G),
          ∫ α : LayerSite N → G,
            ∏ P : LayerColumn N, ((gramCoeff β (ε P) : ℝ) : ℂ)
              * (((gramChar ρ (colWord u u' P.1 P.2.1 P.2.2 α))
                  : ℂˣ) : ℂ) ^ (gramPatExp ε P)
            ∂(Measure.pi fun _ : LayerSite N => μG) :=
        integral_finset_sum Finset.univ
          fun ε _ => integrable_of_fintype
            (fun α : LayerSite N → G =>
              ∏ P : LayerColumn N, ((gramCoeff β (ε P) : ℝ) : ℂ)
                * (((gramChar ρ (colWord u u' P.1 P.2.1 P.2.2 α))
                    : ℂˣ) : ℂ) ^ (gramPatExp ε P))
    _ = ∑ ε : LayerColumn N
          → Fin (Fintype.card G) × Fin (Fintype.card G),
          ((gramColWeight (gramCoeff β) (fun ε P => ε P) ε : ℝ) : ℂ)
            * gramFeat ρ ε u * star (gramFeat ρ ε u') := by
        refine Finset.sum_congr rfl fun ε _ => ?_
        have hsplit : ∀ α : LayerSite N → G,
            ∏ P : LayerColumn N, ((gramCoeff β (ε P) : ℝ) : ℂ)
                * (((gramChar ρ (colWord u u' P.1 P.2.1 P.2.2 α))
                    : ℂˣ) : ℂ) ^ (gramPatExp ε P)
              = ((gramColWeight (gramCoeff β) (fun ε P => ε P) ε
                    : ℝ) : ℂ)
                * ∏ P : LayerColumn N, (((gramChar ρ
                    (colWord u u' P.1 P.2.1 P.2.2 α)) : ℂˣ) : ℂ)
                    ^ (gramPatExp ε P) := by
          intro α
          rw [Finset.prod_mul_distrib]
          congr 1
          exact (Complex.ofReal_prod _ _).symm
        rw [integral_congr_ae (Filter.Eventually.of_forall hsplit),
          integral_const_mul, integral_gramPat, mul_assoc]

end Separation

section Cert

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]
  [MeasurableSpace G] [MeasurableSingletonClass G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] [DiscreteTopology G]
  (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin 1) ℂ))
  {N : ℕ} [NeZero N] [DecidableEq (LayerLink N)]

/-- **The G-1 certificate at one-dimensional types**: the
`LayerKernelSOSCert` whose index type is the character-power
pairs, whose coefficients are the regrouped exponential
coefficients, and whose features are the character-filter
features.  It is a certificate for EVERY finite group and
every one-dimensional representation, at every even `N`. -/
noncomputable def gramOneDimCert (hN : Even N) (hβ : 0 ≤ β) :
    LayerKernelSOSCert (N := N)
      (τ := Fin (Fintype.card G) × Fin (Fintype.card G))
      (ι := LayerColumn N → Fin (Fintype.card G) × Fin (Fintype.card G))
      μG ρ β where
  coeff := gramCoeff β
  coeff_nonneg := fun t => gramCoeff_nonneg hβ t
  char := gramCharFn ρ
  expansion := fun g => gram_expansion ρ g
  τof := fun ε P => ε P
  feat := gramFeat ρ
  pairScale := ((Fintype.card (LayerLink N → G) : ℝ)⁻¹)
    * ((Fintype.card (LayerLink N → G) : ℝ)⁻¹)
  pairScale_nonneg := mul_nonneg
    (inv_nonneg.mpr (Nat.cast_nonneg _))
    (inv_nonneg.mpr (Nat.cast_nonneg _))
  pairing_eq := by
    intro F
    have step1 : ∀ u : LayerLink N → G,
        ∫ u', (starRingEnd ℂ) (F u) * layerKernel μG ρ β u u' * F u'
            ∂(Measure.pi fun _ : LayerLink N => μG)
          = ((Fintype.card (LayerLink N → G) : ℝ)⁻¹)
            • ∑ u', (starRingEnd ℂ) (F u) * layerKernel μG ρ β u u'
              * F u' :=
      fun u => integral_pi_eq_card_inv_sum μG _
    rw [integral_congr_ae (Filter.Eventually.of_forall step1),
      integral_pi_eq_card_inv_sum μG, ← Finset.smul_sum, smul_smul,
      Complex.real_smul]
  kernel_eq := fun u u' => gram_kernel_eq μG ρ hN β u u'

/-- **G-1, one-dimensional sector (headline).**  For every
finite group `G`, every one-dimensional unitary
representation `ρ`, every even `N`, and every `β ≥ 0`,
`LayerKernelPos` holds at `(μG, ρ, β)` — by the explicit
Gram/SOS certificate of `gramOneDimCert`, discharged once by
the G-0 theorem. -/
theorem layerKernelPos_gram_oneDim (hN : Even N) (hβ : 0 ≤ β) :
    LayerKernelPos (N := N) μG ρ β :=
  (gramOneDimCert μG ρ hN hβ).layerKernelPos

end Cert


end ThetLogos
