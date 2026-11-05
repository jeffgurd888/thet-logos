/-
# Brick TM-1 — the ternary seat data + character engine
(Ternary Magnetism chain, brick 2; TM-0 gate PASSED 2026-11-05)

Commission: Jeff's TM chain commission (2026-11-05, "do it"), executing
TM-1 from the priced menu in
`~/workspace/your_files/ternary-magnetism-scoping-2026-11-05.md` (§7),
fired after R1's integration shipped and freed the single core lane
(gauntlet order R1 → TM chain → RL-P1).

**Scope — exactly this brick.**  The ZMod 3 CHARACTER seat's data
package and character engine, mirroring LK-P0's front half
(`LayerKernelPosSeatProbe.lean`) with the group swapped:

* the discrete instance package for `Multiplicative (ZMod 3)` and the
  uniform probability measure `seatμ₃ = (3)⁻¹ • Measure.count` with its
  invariance instances;
* the cube-root character `seatChar₃ g = chiC3 (toAdd g)`
  (`chiC3`/`zetaC3` are landed in `PlaneCrossingKappa4Probe`), its
  homomorphism / inversion / conjugation algebra, its real-part and
  one-site orthogonality sums;
* the seat representation `seatρ₃` (the character as a `1 × 1`
  unitary), `charFn_seat₃`, and the column-density evaluation
  `colDensC_seat₃` (`1 − Re χ(word) ∈ {0, 3/2}`);
* the three-term Boltzmann split
  `exp(−β·dens) = a₃(β) + b₃(β)·χ(word) + b₃(β)·χ̄(word)` with
  `a₃(β) = (1 + 2e^{−3β/2})/3`, `b₃(β) = (1 − e^{−3β/2})/3`
  (TM-0 gate ground truth: split max err `3.6e-14`, `b₃ ≥ 0` iff
  `β ≥ 0`);
* the finite-seat integral `seatIntegralPi₃`, the single-column
  partition function `colZ₃ = a₃(β)`, and the polymer partition
  function `zPolymer₃ = a₃(β)^24` at the priced torus side `N = 2`.

**NOT in this brick** (later bricks, fired separately): TM-2 (pattern
machinery, the mod-3 signed-divergence filter, the closed form),
TM-3 (Gram assembly + `LayerKernelPos` at this seat), TM-4 (the
FACT-analog decision — the gate already shows the excess
`K(1,1) − a₃²⁴ > 0`, T2).

**Kill armed: K-TM-SPLIT** — fires if the density evaluation or the
split fails in the corpus's own terms (e.g. `charFn seatρ₃ ≠ χ` as
computed, or a coefficient sign failure).  Paper- and probe-verified
at TM-0, so this kill guards Lean-side surprises in how
`repMatrix`/`charFn` unfold at `Fin 1`.

NO CLAIM; dials 0/4.  Magnetism grade (scoping §2.2): this seat is
ternary magnetism in the clock/Potts sense only — its values are the
phases `{1, ω, ω²}`; no `0` state and no signs appear.
-/

import ThetLogos.LayerKernelPosSeatProbe
import ThetLogos.PolymerPartition
import ThetLogos.PlaneCrossingKappa4Probe

open MeasureTheory Finset
open scoped ENNReal

namespace ThetLogos

/-! ## The seat: `G = Multiplicative (ZMod 3)`, discrete, uniform -/

/-- The ternary seat topology: discrete (`⊥`). -/
instance ternarySeatInstTopologicalSpace :
    TopologicalSpace (Multiplicative (ZMod 3)) := ⊥

/-- The ternary seat σ-algebra: everything measurable (`⊤`). -/
instance ternarySeatInstMeasurableSpace :
    MeasurableSpace (Multiplicative (ZMod 3)) := ⊤

/-- The ternary seat topology is discrete. -/
instance ternarySeatInstDiscreteTopology :
    DiscreteTopology (Multiplicative (ZMod 3)) := ⟨rfl⟩

/-- The ternary seat Borel σ-algebra agrees with `⊤`. -/
instance ternarySeatInstBorelSpace : BorelSpace (Multiplicative (ZMod 3)) :=
  ⟨borel_eq_top_of_discrete.symm⟩

/-- The ternary seat measure: the uniform probability measure on the
three-element group, `(3)⁻¹ • Measure.count`. -/
noncomputable def seatμ₃ : Measure (Multiplicative (ZMod 3)) :=
  (3 : ℝ≥0∞)⁻¹ • Measure.count

/-- The ternary seat measure is a probability measure. -/
instance : IsProbabilityMeasure seatμ₃ := by
  constructor
  have hc : Nat.card (Multiplicative (ZMod 3)) = 3 := by
    rw [Nat.card_eq_fintype_card]
    decide
  rw [seatμ₃, Measure.smul_apply, smul_eq_mul, Measure.count_univ,
    ENat.card_eq_coe_natCard, hc, Nat.cast_ofNat]
  exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)

/-- The ternary seat measure is inversion-invariant. -/
instance : Measure.IsInvInvariant seatμ₃ := by
  constructor
  show Measure.map Inv.inv ((3 : ℝ≥0∞)⁻¹ • Measure.count)
    = (3 : ℝ≥0∞)⁻¹ • Measure.count
  rw [Measure.map_smul _ measurable_inv.aemeasurable,
    Measure.map_inv_eq_self]

/-- The ternary seat measure is left-invariant. -/
instance : Measure.IsMulLeftInvariant seatμ₃ := by
  constructor
  intro g
  show Measure.map (g * ·) ((3 : ℝ≥0∞)⁻¹ • Measure.count)
    = (3 : ℝ≥0∞)⁻¹ • Measure.count
  rw [Measure.map_smul _ (measurable_const_mul g).aemeasurable]
  congr 1
  exact MeasureTheory.Measure.IsMulLeftInvariant.map_mul_left_eq_self
    (μ := (Measure.count : Measure (Multiplicative (ZMod 3)))) g

/-- The ternary seat measure is right-invariant. -/
instance : Measure.IsMulRightInvariant seatμ₃ := by
  constructor
  intro g
  show Measure.map (· * g) ((3 : ℝ≥0∞)⁻¹ • Measure.count)
    = (3 : ℝ≥0∞)⁻¹ • Measure.count
  rw [Measure.map_smul _ (measurable_mul_const g).aemeasurable]
  congr 1
  exact MeasureTheory.Measure.IsMulRightInvariant.map_mul_right_eq_self
    (μ := (Measure.count : Measure (Multiplicative (ZMod 3)))) g

/-- A singleton under the ternary seat measure has mass `(3)⁻¹`. -/
theorem seatμ₃_singleton (g : Multiplicative (ZMod 3)) :
    seatμ₃ {g} = (3 : ℝ≥0∞)⁻¹ := by
  rw [seatμ₃, Measure.smul_apply, smul_eq_mul, Measure.count_singleton,
    mul_one]

/-- The ternary seat group has three elements. -/
theorem ternarySeat_card : Fintype.card (Multiplicative (ZMod 3)) = 3 := by
  decide

/-- The three-element universe of the ternary seat group. -/
theorem ternarySeat_univ :
    (Finset.univ : Finset (Multiplicative (ZMod 3)))
      = {1, Multiplicative.ofAdd 1, Multiplicative.ofAdd 2} := by decide

/-! ## The cube-root character of the seat group -/

/-- The cube-root character of `Multiplicative (ZMod 3)`:
`seatChar₃ g = χ(toAdd g) = ω^(toAdd g)` with `ω = zetaC3 = e^{2πi/3}`
(the landed `chiC3` of `PlaneCrossingKappa4Probe`). -/
noncomputable def seatChar₃ (g : Multiplicative (ZMod 3)) : ℂ :=
  chiC3 (Multiplicative.toAdd g)

/-- The character at the identity. -/
theorem seatChar₃_one : seatChar₃ (1 : Multiplicative (ZMod 3)) = 1 := by
  simp [seatChar₃, chiC3_zero]

/-- The character at the first generator: `ω`. -/
theorem seatChar₃_ofAdd_one :
    seatChar₃ (Multiplicative.ofAdd 1) = zetaC3 := by
  simp [seatChar₃, chiC3_one]

/-- The character at the second generator: `ω²`. -/
theorem seatChar₃_ofAdd_two :
    seatChar₃ (Multiplicative.ofAdd 2) = zetaC3 ^ 2 := by
  simp [seatChar₃, chiC3_two]

/-- The character is a group homomorphism to `(ℂ, *)`:
`χ(gh) = χ(g)χ(h)` (via `toAdd` and `chiC3_add`). -/
theorem seatChar₃_mul (g h : Multiplicative (ZMod 3)) :
    seatChar₃ (g * h) = seatChar₃ g * seatChar₃ h := by
  unfold seatChar₃
  rw [toAdd_mul, chiC3_add]

/-- The character takes exactly the three values `1, ω, ω²`. -/
theorem seatChar₃_cases (g : Multiplicative (ZMod 3)) :
    seatChar₃ g = 1 ∨ seatChar₃ g = zetaC3 ∨ seatChar₃ g = zetaC3 ^ 2 := by
  rcases zmod3_cases (Multiplicative.toAdd g) with h | h | h
  · left
    simp [seatChar₃, h, chiC3_zero]
  · right; left
    simp [seatChar₃, h, chiC3_one]
  · right; right
    simp [seatChar₃, h, chiC3_two]

/-- Conjugation of the primitive root: `ω̄ = ω²`. -/
theorem zetaC3_star : star zetaC3 = zetaC3 ^ 2 := by
  rw [zetaC3_sq]
  simp only [Complex.ext_iff, Complex.conj_re, Complex.conj_im,
    Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
    Complex.one_re, Complex.one_im, zetaC3]
  constructor <;> norm_num

/-- The primitive root is nonzero (its cube is `1`). -/
theorem zetaC3_ne_zero : zetaC3 ≠ 0 := by
  intro h
  have h3 := zetaC3_cube
  rw [h] at h3
  simp at h3

/-- The character never vanishes. -/
theorem seatChar₃_ne_zero (g : Multiplicative (ZMod 3)) :
    seatChar₃ g ≠ 0 := by
  rcases seatChar₃_cases g with h | h | h
  · rw [h]; exact one_ne_zero
  · rw [h]; exact zetaC3_ne_zero
  · rw [h]; exact pow_ne_zero 2 zetaC3_ne_zero

/-- Inversion of the character is inversion in `ℂ`:
`χ(g⁻¹) = (χ g)⁻¹` (from `χ(g⁻¹)χ(g) = χ(1) = 1`). -/
theorem seatChar₃_inv (g : Multiplicative (ZMod 3)) :
    seatChar₃ g⁻¹ = (seatChar₃ g)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← seatChar₃_mul, inv_mul_cancel, seatChar₃_one]

/-- Conjugation of the character is inversion in the group:
`χ̄(g) = χ(g⁻¹)` — the ternary seat's visible inversion
(at the binary seat this was invisible, `χ(g⁻¹) = χ(g)`). -/
theorem seatChar₃_star (g : Multiplicative (ZMod 3)) :
    star (seatChar₃ g) = seatChar₃ g⁻¹ := by
  rcases zmod3_cases (Multiplicative.toAdd g) with h | h | h
  · have hg : g = 1 := by
      apply Multiplicative.toAdd.injective
      rw [h]; rfl
    rw [hg, seatChar₃_one, inv_one, seatChar₃_one]
    simp
  · have e1 : seatChar₃ g = zetaC3 := by simp [seatChar₃, h, chiC3_one]
    have e2 : seatChar₃ g⁻¹ = zetaC3 ^ 2 := by
      have hinv : Multiplicative.toAdd g⁻¹ = 2 := by
        rw [toAdd_inv, h]
        decide
      simp [seatChar₃, hinv, chiC3_two]
    rw [e1, e2, zetaC3_star]
  · have e1 : seatChar₃ g = zetaC3 ^ 2 := by simp [seatChar₃, h, chiC3_two]
    have e2 : seatChar₃ g⁻¹ = zetaC3 := by
      have hinv : Multiplicative.toAdd g⁻¹ = 1 := by
        rw [toAdd_inv, h]
        decide
      simp [seatChar₃, hinv, chiC3_one]
    rw [e1, e2]
    have h4 : (zetaC3 ^ 2) ^ 2 = zetaC3 := by
      calc (zetaC3 ^ 2) ^ 2 = zetaC3 ^ 3 * zetaC3 := by ring
        _ = zetaC3 := by rw [zetaC3_cube, one_mul]
    calc star (zetaC3 ^ 2) = (star zetaC3) ^ 2 := by rw [star_pow]
      _ = (zetaC3 ^ 2) ^ 2 := by rw [zetaC3_star]
      _ = zetaC3 := h4

/-- The character is unitary pointwise: `χ̄(g)·χ(g) = 1`. -/
theorem seatChar₃_star_mul_self (g : Multiplicative (ZMod 3)) :
    star (seatChar₃ g) * seatChar₃ g = 1 := by
  rw [seatChar₃_star, seatChar₃_inv,
    inv_mul_cancel₀ (seatChar₃_ne_zero g)]

/-- The character is unitary pointwise, in the `starRingEnd` form
the matrix lemmas produce: `χ(g)·χ̄(g) = 1`. -/
theorem seatChar₃_mul_starRingEnd_self (g : Multiplicative (ZMod 3)) :
    seatChar₃ g * (starRingEnd ℂ) (seatChar₃ g) = 1 := by
  rw [show (starRingEnd ℂ) (seatChar₃ g) = star (seatChar₃ g) from
    (congrFun RCLike.star_def (seatChar₃ g)).symm, mul_comm]
  exact seatChar₃_star_mul_self g

/-- The real part of the character: `1` at the identity, `-1/2`
at the two nontrivial elements. -/
theorem seatChar₃_re (g : Multiplicative (ZMod 3)) :
    (seatChar₃ g).re
      = if Multiplicative.toAdd g = 0 then 1 else -1 / 2 := by
  rcases zmod3_cases (Multiplicative.toAdd g) with h | h | h
  · rw [if_pos h]
    simp [seatChar₃, h, chiC3_zero]
  · rw [if_neg (show ¬ (Multiplicative.toAdd g = 0) by rw [h]; decide)]
    have e1 : seatChar₃ g = zetaC3 := by simp [seatChar₃, h, chiC3_one]
    rw [e1]
    rfl
  · rw [if_neg (show ¬ (Multiplicative.toAdd g = 0) by rw [h]; decide)]
    have e1 : seatChar₃ g = zetaC3 ^ 2 := by simp [seatChar₃, h, chiC3_two]
    rw [e1, zetaC3_sq]
    norm_num [zetaC3, Complex.sub_re, Complex.neg_re, Complex.one_re]

/-- The character plus its conjugate: `χ + χ̄ = 2` at the identity,
`-1` elsewhere (this is `2·Re χ`; the load-bearing identity of the
three-term split). -/
theorem seatChar₃_add_star (g : Multiplicative (ZMod 3)) :
    seatChar₃ g + star (seatChar₃ g)
      = if Multiplicative.toAdd g = 0 then 2 else -1 := by
  rcases zmod3_cases (Multiplicative.toAdd g) with h | h | h
  · rw [if_pos h]
    have hg : g = 1 := by
      apply Multiplicative.toAdd.injective
      rw [h]; rfl
    rw [hg, seatChar₃_one, star_one]
    norm_num
  · rw [if_neg (show ¬ (Multiplicative.toAdd g = 0) by rw [h]; decide)]
    have e1 : seatChar₃ g = zetaC3 := by simp [seatChar₃, h, chiC3_one]
    rw [e1, zetaC3_star]
    linear_combination zetaC3_sq_add
  · rw [if_neg (show ¬ (Multiplicative.toAdd g = 0) by rw [h]; decide)]
    have e1 : seatChar₃ g = zetaC3 ^ 2 := by simp [seatChar₃, h, chiC3_two]
    rw [e1]
    have hstar : star (zetaC3 ^ 2) = zetaC3 := by
      calc star (zetaC3 ^ 2) = (star zetaC3) ^ 2 := by rw [star_pow]
        _ = (zetaC3 ^ 2) ^ 2 := by rw [zetaC3_star]
        _ = zetaC3 := by
            calc (zetaC3 ^ 2) ^ 2 = zetaC3 ^ 3 * zetaC3 := by ring
              _ = zetaC3 := by rw [zetaC3_cube, one_mul]
    rw [hstar]
    linear_combination zetaC3_sq_add

/-- One-site orthogonality, degree one: `∑_g χ(g) = 0`. -/
theorem seatChar₃_sum :
    ∑ g : Multiplicative (ZMod 3), seatChar₃ g = 0 := by
  rw [ternarySeat_univ, Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton,
    seatChar₃_one, seatChar₃_ofAdd_one, seatChar₃_ofAdd_two]
  linear_combination zetaC3_sq_add

/-- One-site orthogonality at every power: `∑_g χ(g)^k = 3` if
`3 ∣ k`, else `0` (the character-sum engine the filter bricks
consume). -/
theorem seatChar₃_pow_sum (k : ℕ) :
    ∑ g : Multiplicative (ZMod 3), (seatChar₃ g) ^ k
      = if 3 ∣ k then 3 else 0 := by
  rw [ternarySeat_univ, Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton,
    seatChar₃_one, seatChar₃_ofAdd_one, seatChar₃_ofAdd_two, one_pow]
  have hmod : zetaC3 ^ k = zetaC3 ^ (k % 3) := (zetaC3_pow_mod k).symm
  have hmod2 : (zetaC3 ^ 2) ^ k = zetaC3 ^ ((2 * k) % 3) := by
    rw [← pow_mul, ← zetaC3_pow_mod]
  have hk3 : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by
    have hlt : k % 3 < 3 := Nat.mod_lt _ (by norm_num)
    omega
  have h2k : (2 * k) % 3 = (2 * (k % 3)) % 3 := by rw [Nat.mul_mod]
  rcases hk3 with h0 | h1 | h2
  · have hdvd : 3 ∣ k := ⟨k / 3, by
      conv_lhs => rw [← Nat.div_add_mod k 3]
      rw [h0, add_zero]⟩
    have e2k : (2 * k) % 3 = 0 := by rw [h2k, h0]
    rw [if_pos hdvd, hmod, h0, hmod2, e2k]
    norm_num
  · have hndvd : ¬ 3 ∣ k := by
      intro hd
      have := Nat.mod_eq_zero_of_dvd hd
      rw [h1] at this
      norm_num at this
    have e2k : (2 * k) % 3 = 2 := by rw [h2k, h1]
    rw [if_neg hndvd, hmod, h1, hmod2, e2k]
    simp only [pow_one]
    linear_combination zetaC3_sq_add
  · have hndvd : ¬ 3 ∣ k := by
      intro hd
      have := Nat.mod_eq_zero_of_dvd hd
      rw [h2] at this
      norm_num at this
    have e2k : (2 * k) % 3 = 1 := by rw [h2k, h2]
    rw [if_neg hndvd, hmod, h2, hmod2, e2k]
    simp only [pow_one]
    linear_combination zetaC3_sq_add

/-! ## The seat representation: the character as a `1 × 1` unitary -/

/-- The ternary seat matrix: the `1 × 1` matrix with entry
`seatChar₃ g`. -/
noncomputable def seatMat₃ (g : Multiplicative (ZMod 3)) :
    Matrix (Fin 1) (Fin 1) ℂ :=
  fun _ _ => seatChar₃ g

/-- The ternary seat matrix is unitary (its entry is a cube-root
phase). -/
theorem seatMat₃_mem (g : Multiplicative (ZMod 3)) :
    seatMat₃ g ∈ Matrix.unitaryGroup (Fin 1) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext i j
  fin_cases i
  fin_cases j
  simp [seatMat₃, Matrix.mul_apply, Matrix.star_apply,
    seatChar₃_mul_starRingEnd_self]

/-- The ternary seat representation: the cube-root character, as a
homomorphism into the `1 × 1` unitary group. -/
noncomputable def seatρ₃ : Multiplicative (ZMod 3)
    →* ↥(Matrix.unitaryGroup (Fin 1) ℂ) where
  toFun g := ⟨seatMat₃ g, seatMat₃_mem g⟩
  map_one' := by
    apply Subtype.ext
    ext i j
    fin_cases i
    fin_cases j
    simp [seatMat₃, seatChar₃_one]
  map_mul' := by
    intro g h
    apply Subtype.ext
    show seatMat₃ (g * h) = _
    rw [Submonoid.coe_mul]
    ext i j
    fin_cases i
    fin_cases j
    simp [seatMat₃, seatChar₃_mul, Matrix.mul_apply]

/-- The ternary seat representation's matrix is `seatMat₃`
(by definition). -/
theorem repMatrix_seatρ₃ (g : Multiplicative (ZMod 3)) :
    repMatrix seatρ₃ g = seatMat₃ g := rfl

/-- The ternary seat character: `charFn seatρ₃ g = seatChar₃ g`.
(**K-TM-SPLIT guard**: the corpus's own `charFn` of the built
representation computes to the pinned character.) -/
theorem charFn_seat₃ (g : Multiplicative (ZMod 3)) :
    charFn seatρ₃ g = seatChar₃ g := by
  rw [charFn, repMatrix_seatρ₃, Matrix.trace_fin_one]
  rfl

/-- The ternary seat column density is `1 − Re χ(word)`. -/
theorem colDensC_seat₃ (u u' : LayerLink 2 → Multiplicative (ZMod 3))
    (P : LayerColumn 2) (α : LayerSite 2 → Multiplicative (ZMod 3)) :
    colDensC seatρ₃ u u' P α
      = 1 - (seatChar₃ (colWord u u' P.1 P.2.1 P.2.2 α)).re := by
  rw [colDensC, colDens_eq, charFn_seat₃]
  simp

/-- The ternary seat representation is continuous (discrete
domain), the `hρcont` side condition of the polymer lemmas. -/
theorem seatρ₃_cont : Continuous fun g => repMatrix seatρ₃ g :=
  continuous_of_discreteTopology

/-! ## The split coefficients `a₃, b₃` -/

/-- The ternary split's constant coefficient:
`a₃(β) = (1 + 2e^{−3β/2})/3`. -/
noncomputable def seatA₃ (β : ℝ) : ℝ :=
  (1 + 2 * Real.exp (-(3 / 2) * β)) / 3

/-- The ternary split's character coefficient:
`b₃(β) = (1 − e^{−3β/2})/3` (the same coefficient on `χ` and `χ̄`,
because the density sees only `Re χ` — ACC-TM-4). -/
noncomputable def seatB₃ (β : ℝ) : ℝ :=
  (1 - Real.exp (-(3 / 2) * β)) / 3

/-- The split coefficients sum to the vacuum value:
`a₃ + 2b₃ = 1`. -/
theorem seatA₃_add_two_mul_seatB₃ (β : ℝ) :
    seatA₃ β + 2 * seatB₃ β = 1 := by
  unfold seatA₃ seatB₃
  ring

/-- The split coefficients differ by the nontrivial Boltzmann
factor: `a₃ − b₃ = e^{−3β/2}`. -/
theorem seatA₃_sub_seatB₃ (β : ℝ) :
    seatA₃ β - seatB₃ β = Real.exp (-(3 / 2) * β) := by
  unfold seatA₃ seatB₃
  ring

/-- `a₃(β) > 0` at every `β`. -/
theorem seatA₃_nonneg (β : ℝ) : 0 ≤ seatA₃ β := by
  have h := Real.exp_pos (-(3 / 2) * β)
  unfold seatA₃
  apply div_nonneg _ (by norm_num)
  linarith

/-- `b₃(β) ≥ 0` iff `β ≥ 0` — the forward direction is the Gram
route's fence (ACC-TM-3): `b₃` changes sign at `β < 0`. -/
theorem seatB₃_nonneg {β : ℝ} (hβ : 0 ≤ β) : 0 ≤ seatB₃ β := by
  have h1 : Real.exp (-(3 / 2) * β) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have h2 : (0 : ℝ) ≤ (3 / 2) * β := mul_nonneg (by norm_num) hβ
    linarith
  unfold seatB₃
  apply div_nonneg _ (by norm_num)
  linarith

/-! ## The three-term split -/

/-- The ternary seat column density takes the two values
`{0, 3/2}` (as the binary seat's took `{0, 2}`). -/
theorem colDensC_seat₃_values (u u' : LayerLink 2 → Multiplicative (ZMod 3))
    (P : LayerColumn 2) (α : LayerSite 2 → Multiplicative (ZMod 3)) :
    colDensC seatρ₃ u u' P α = 0 ∨ colDensC seatρ₃ u u' P α = 3 / 2 := by
  rw [colDensC_seat₃, seatChar₃_re]
  by_cases h : Multiplicative.toAdd (colWord u u' P.1 P.2.1 P.2.2 α) = 0
  · rw [if_pos h]
    left
    norm_num
  · rw [if_neg h]
    right
    norm_num

/-- **The three-term Boltzmann split** (TM-0 gate §1: verified to
`3.6e-14` over the β grid; **K-TM-SPLIT guard**):
`exp(−β·dens) = a₃(β) + b₃(β)·χ(word) + b₃(β)·χ̄(word)`, exactly,
because a function on the three-point set `{1, ω, ω²}` interpolates
uniquely and the density sees only `Re χ`. -/
theorem exp_colDensC₃ (β : ℝ) (P : LayerColumn 2)
    (α : LayerSite 2 → Multiplicative (ZMod 3))
    (u u' : LayerLink 2 → Multiplicative (ZMod 3)) :
    ((Real.exp (-β * colDensC seatρ₃ u u' P α) : ℂ))
      = (seatA₃ β : ℂ)
        + (seatB₃ β : ℂ) * seatChar₃ (colWord u u' P.1 P.2.1 P.2.2 α)
        + (seatB₃ β : ℂ)
          * star (seatChar₃ (colWord u u' P.1 P.2.1 P.2.2 α)) := by
  set w := colWord u u' P.1 P.2.1 P.2.2 α with hw
  have hdens : colDensC seatρ₃ u u' P α = 1 - (seatChar₃ w).re :=
    colDensC_seat₃ u u' P α
  by_cases h : Multiplicative.toAdd w = 0
  · have hw1 : seatChar₃ w = 1 := by simp [seatChar₃, h, chiC3_zero]
    have hre : (seatChar₃ w).re = 1 := by rw [seatChar₃_re, if_pos h]
    have hexp : Real.exp (-β * colDensC seatρ₃ u u' P α) = 1 := by
      rw [hdens, hre]
      simp
    rw [hexp, hw1]
    simp only [Complex.ofReal_one, star_one, mul_one]
    calc (1 : ℂ) = ((seatA₃ β + 2 * seatB₃ β : ℝ) : ℂ) := by
          rw [seatA₃_add_two_mul_seatB₃]
          simp
      _ = (seatA₃ β : ℂ) + (seatB₃ β : ℂ) + (seatB₃ β : ℂ) := by
          push_cast
          ring
  · have hre : (seatChar₃ w).re = -1 / 2 := by
      rw [seatChar₃_re, if_neg h]
    have hsum : seatChar₃ w + star (seatChar₃ w) = -1 := by
      have h2 := seatChar₃_add_star w
      rw [if_neg h] at h2
      exact h2
    have hexp : Real.exp (-β * colDensC seatρ₃ u u' P α)
        = Real.exp (-(3 / 2) * β) := by
      rw [hdens, hre]
      congr 1
      ring
    rw [hexp]
    calc ((Real.exp (-(3 / 2) * β) : ℂ))
        = ((seatA₃ β - seatB₃ β : ℝ) : ℂ) := by
          rw [seatA₃_sub_seatB₃]
      _ = (seatA₃ β : ℂ)
          + (seatB₃ β : ℂ) * seatChar₃ w
          + (seatB₃ β : ℂ) * star (seatChar₃ w) := by
          have h3 : (seatA₃ β : ℂ) + (seatB₃ β : ℂ) * seatChar₃ w
              + (seatB₃ β : ℂ) * star (seatChar₃ w)
              = (seatA₃ β : ℂ)
                + (seatB₃ β : ℂ) * (seatChar₃ w + star (seatChar₃ w)) := by
            ring
          rw [h3, hsum]
          push_cast
          ring

/-- The three-term split in real form (the form `colZ₃` consumes):
`exp(−β·dens) = a₃(β) + b₃(β)·(2·Re χ(word))`. -/
theorem exp_colDensC₃_re (β : ℝ) (P : LayerColumn 2)
    (α : LayerSite 2 → Multiplicative (ZMod 3))
    (u u' : LayerLink 2 → Multiplicative (ZMod 3)) :
    Real.exp (-β * colDensC seatρ₃ u u' P α)
      = seatA₃ β + seatB₃ β
        * (2 * (seatChar₃ (colWord u u' P.1 P.2.1 P.2.2 α)).re) := by
  set w := colWord u u' P.1 P.2.1 P.2.2 α with hw
  have hdens : colDensC seatρ₃ u u' P α = 1 - (seatChar₃ w).re :=
    colDensC_seat₃ u u' P α
  by_cases h : Multiplicative.toAdd w = 0
  · have hre : (seatChar₃ w).re = 1 := by rw [seatChar₃_re, if_pos h]
    rw [hdens, hre]
    simp only [sub_self, mul_zero, Real.exp_zero]
    rw [show seatB₃ β * (2 * (1 : ℝ)) = 2 * seatB₃ β by ring,
      seatA₃_add_two_mul_seatB₃ β]
  · have hre : (seatChar₃ w).re = -1 / 2 := by
      rw [seatChar₃_re, if_neg h]
    rw [hdens, hre]
    have e1 : -β * (1 - (-1 / 2 : ℝ)) = -(3 / 2) * β := by ring
    rw [e1, show seatB₃ β * (2 * (-1 / 2 : ℝ)) = -seatB₃ β by ring,
      show seatA₃ β + -seatB₃ β = seatA₃ β - seatB₃ β from
        (sub_eq_add_neg _ _).symm,
      seatA₃_sub_seatB₃ β]

/-! ## Integration over the finite ternary seat -/

/-- **The finite-seat integral at the ternary seat.**  For a finite
index type `ι`, the integral over the product seat measure is the
sum over all configurations scaled by the inverse configuration
count (the card-3 twin of LK-P0's `seatIntegralPi`). -/
theorem seatIntegralPi₃ {ι : Type*} [Fintype ι] [DecidableEq ι]
    {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : (ι → Multiplicative (ZMod 3)) → E) :
    (∫ a, f a ∂(Measure.pi fun _ : ι => seatμ₃))
      = (Fintype.card (ι → Multiplicative (ZMod 3)) : ℝ)⁻¹
        • ∑ a, f a := by
  have hInt : Integrable f (Measure.pi fun _ : ι => seatμ₃) := by
    rw [← Measure.sum_smul_dirac (Measure.pi fun _ : ι => seatμ₃)]
    refine integrable_sum_dirac (fun a => measure_ne_top _ _) ?_
    exact Summable.of_finite
  rw [integral_fintype hInt, Finset.smul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  have hsing : ∀ g : Multiplicative (ZMod 3), seatμ₃ {g} = (3 : ℝ≥0∞)⁻¹ :=
    seatμ₃_singleton
  have hc3 : Fintype.card (Multiplicative (ZMod 3)) = 3 := ternarySeat_card
  rw [measureReal_def, Measure.pi_singleton]
  simp only [hsing]
  rw [Finset.prod_const, ← ENNReal.inv_pow, ENNReal.toReal_inv,
    Fintype.card_fun, hc3]
  simp [Finset.card_univ, ENNReal.toReal_pow]

/-- The stratum configuration space at the ternary seat has
`3^8 = 6561` points. -/
theorem ternary_stratum_card :
    Fintype.card (LayerSite 2 → Multiplicative (ZMod 3)) = 6561 := by
  norm_num [Fintype.card_fun, ternarySeat_card, layerSite_card]

/-! ## Column character factorization and the single-column average -/

/-- The stratum part of a column character: the two `α`-factors. -/
noncomputable def stratumChar₃ (P : LayerColumn 2)
    (α : LayerSite 2 → Multiplicative (ZMod 3)) : ℂ :=
  seatChar₃ (α P.1)
    * (seatChar₃ (α (layerShift P.2.1 P.2.2 P.1)))⁻¹

/-- The layer-configuration part of a column character. -/
noncomputable def configChar₃ (P : LayerColumn 2)
    (u : LayerLink 2 → Multiplicative (ZMod 3)) : ℂ :=
  seatChar₃ (u (layerLinkOf P.1 P.2.1 P.2.2))

/-- **Character factorization.**  The column character splits as
the stratum character times the two configuration characters —
with inversion VISIBLE (`χ(g⁻¹) = χ̄(g) ≠ χ(g)`), the ternary
seat's structural difference from the binary seat's sign
factorization. -/
theorem colChar₃_factor (P : LayerColumn 2)
    (α : LayerSite 2 → Multiplicative (ZMod 3))
    (u u' : LayerLink 2 → Multiplicative (ZMod 3)) :
    seatChar₃ (colWord u u' P.1 P.2.1 P.2.2 α)
      = stratumChar₃ P α * (configChar₃ P u' * (configChar₃ P u)⁻¹) := by
  unfold stratumChar₃ configChar₃ colWord
  simp only [seatChar₃_mul, seatChar₃_inv]
  ring

/-- The per-site factor of a column character: `χ(g)` at the
column's base site, `χ(g)⁻¹` at its head site, `1` elsewhere. -/
noncomputable def colSiteFactor₃ (P : LayerColumn 2) (s : LayerSite 2)
    (g : Multiplicative (ZMod 3)) : ℂ :=
  if s = P.1 then seatChar₃ g
  else if s = layerShift P.2.1 P.2.2 P.1 then (seatChar₃ g)⁻¹
  else 1

/-- The stratum character is the product of its per-site factors
(the head site differs from the base site, `layerShift_ne`). -/
theorem prod_colSiteFactor₃ (P : LayerColumn 2)
    (α : LayerSite 2 → Multiplicative (ZMod 3)) :
    ∏ s, colSiteFactor₃ P s (α s) = stratumChar₃ P α := by
  classical
  have hne : layerShift P.2.1 P.2.2 P.1 ≠ P.1 :=
    layerShift_ne P.2.1 P.2.2 P.1
  have hfac1 : colSiteFactor₃ P P.1 (α P.1) = seatChar₃ (α P.1) := by
    simp [colSiteFactor₃]
  have hfac2 : colSiteFactor₃ P (layerShift P.2.1 P.2.2 P.1)
        (α (layerShift P.2.1 P.2.2 P.1))
      = (seatChar₃ (α (layerShift P.2.1 P.2.2 P.1)))⁻¹ := by
    simp [colSiteFactor₃, hne]
  have hrest : ∏ s ∈ (Finset.univ.erase P.1).erase
        (layerShift P.2.1 P.2.2 P.1), colSiteFactor₃ P s (α s) = 1 := by
    apply Finset.prod_eq_one
    intro s hs
    simp only [Finset.mem_erase, Finset.mem_univ, true_and] at hs
    simp [colSiteFactor₃, hs.2, hs.1]
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ P.1), hfac1,
    ← Finset.mul_prod_erase (Finset.univ.erase P.1) _
      (Finset.mem_erase.mpr ⟨hne, Finset.mem_univ _⟩), hfac2, hrest,
    mul_one]
  rfl

/-- The stratum average of a single column's character vanishes
(one-site orthogonality at the base site: the column never
survives alone — the singleton case of TM-2's filter). -/
theorem sum_seatChar₃_colWord (u u' : LayerLink 2 → Multiplicative (ZMod 3))
    (P : LayerColumn 2) :
    ∑ α : LayerSite 2 → Multiplicative (ZMod 3),
      seatChar₃ (colWord u u' P.1 P.2.1 P.2.2 α) = 0 := by
  classical
  have hsum : (∑ α : LayerSite 2 → Multiplicative (ZMod 3),
        ∏ s, colSiteFactor₃ P s (α s))
      = ∏ s, ∑ g, colSiteFactor₃ P s g := by
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  have hzero : ∏ s, ∑ g, colSiteFactor₃ P s g = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ P.1)
    have hbase : (∑ g, colSiteFactor₃ P P.1 g) = ∑ g, seatChar₃ g := by
      apply Finset.sum_congr rfl
      intro g _
      simp [colSiteFactor₃]
    rw [hbase, seatChar₃_sum]
  calc ∑ α : LayerSite 2 → Multiplicative (ZMod 3),
        seatChar₃ (colWord u u' P.1 P.2.1 P.2.2 α)
      = ∑ α : LayerSite 2 → Multiplicative (ZMod 3),
          (∏ s, colSiteFactor₃ P s (α s))
            * (configChar₃ P u' * (configChar₃ P u)⁻¹) := by
        apply Finset.sum_congr rfl
        intro α _
        rw [colChar₃_factor, prod_colSiteFactor₃]
    _ = (∑ α : LayerSite 2 → Multiplicative (ZMod 3),
          ∏ s, colSiteFactor₃ P s (α s))
        * (configChar₃ P u' * (configChar₃ P u)⁻¹) := by
        rw [Finset.sum_mul]
    _ = 0 * (configChar₃ P u' * (configChar₃ P u)⁻¹) := by
        rw [hsum, hzero]
    _ = 0 := zero_mul _

/-- Real parts commute with finite sums (the form `seat_colZ₃`
consumes). -/
theorem ternary_sum_re {ι : Type*} (s : Finset ι) (f : ι → ℂ) :
    (∑ i ∈ s, f i).re = ∑ i ∈ s, (f i).re := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Complex.add_re, ih]

/-! ## The column and polymer partition functions at the seat -/

/-- **The column partition function at the ternary seat is
exactly `a₃(β)`.**  The stratum average of the column's Boltzmann
factor kills the `b₃(β)` term (a single column never survives),
leaving the constant term. -/
theorem seat_colZ₃ (β : ℝ) (u u' : LayerLink 2 → Multiplicative (ZMod 3))
    (P : LayerColumn 2) :
    colZ seatρ₃ seatμ₃ β u u' P = seatA₃ β := by
  rw [colZ_eq_integral_exp (ρ := seatρ₃) (μG := seatμ₃) seatρ₃_cont
      β u u' P,
    seatIntegralPi₃,
    show ((Fintype.card (LayerSite 2 → Multiplicative (ZMod 3)) : ℝ)⁻¹)
      = (6561 : ℝ)⁻¹ by rw [ternary_stratum_card]; norm_num]
  have hsum : (∑ α : LayerSite 2 → Multiplicative (ZMod 3),
        Real.exp (-β * colDensC seatρ₃ u u' P α))
      = 6561 * seatA₃ β := by
    calc (∑ α : LayerSite 2 → Multiplicative (ZMod 3),
          Real.exp (-β * colDensC seatρ₃ u u' P α))
        = ∑ α : LayerSite 2 → Multiplicative (ZMod 3),
            (seatA₃ β + seatB₃ β
              * (2 * (seatChar₃ (colWord u u' P.1 P.2.1 P.2.2 α)).re)) :=
          Finset.sum_congr rfl fun α _ => exp_colDensC₃_re β P α u u'
      _ = (∑ α : LayerSite 2 → Multiplicative (ZMod 3), seatA₃ β)
          + ∑ α : LayerSite 2 → Multiplicative (ZMod 3),
            seatB₃ β
              * (2 * (seatChar₃ (colWord u u' P.1 P.2.1 P.2.2 α)).re) :=
          Finset.sum_add_distrib
      _ = 6561 * seatA₃ β + 0 := by
          congr 1
          · rw [Finset.sum_const, Finset.card_univ, ternary_stratum_card]
            simp [nsmul_eq_mul]
          · have hnorm : ∀ α : LayerSite 2 → Multiplicative (ZMod 3),
                seatB₃ β
                    * (2 * (seatChar₃ (colWord u u' P.1 P.2.1 P.2.2 α)).re)
                  = (seatB₃ β * 2)
                    * (seatChar₃ (colWord u u' P.1 P.2.1 P.2.2 α)).re :=
              fun α => by ring
            rw [Finset.sum_congr rfl fun α _ => hnorm α, ← Finset.mul_sum,
              ← ternary_sum_re, sum_seatChar₃_colWord]
            simp
      _ = 6561 * seatA₃ β := by rw [add_zero]
  rw [hsum, smul_eq_mul]
  rw [show (6561 : ℝ)⁻¹ * (6561 * seatA₃ β) = seatA₃ β by field_simp]

/-- **The polymer partition function at the ternary seat is
`a₃(β)^24`.**  (TM-4 will decide the FACT-analog against this:
the gate's excess `K(1,1) − a₃²⁴ > 0` says the layer kernel is
NOT this product — the factorization kill is priced there, not
here.) -/
theorem seat_zPolymer₃ (β : ℝ)
    (u u' : LayerLink 2 → Multiplicative (ZMod 3)) :
    zPolymer seatρ₃ seatμ₃ β u u' = (seatA₃ β) ^ 24 := by
  show ∏ P : LayerColumn 2, colZ seatρ₃ seatμ₃ β u u' P = _
  rw [Finset.prod_congr rfl (fun P _ => seat_colZ₃ β u u' P),
    Finset.prod_const, Finset.card_univ, layerColumn_card]

end ThetLogos
