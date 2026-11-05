/-
# Brick LK-P0 — the fused seat probe (LayerKernelPos front)

Commission: Jeff's "fire all" (2026-11-04), front 1 of 5.  Contract:
`whitepaper`-side scoping note
`layerkernelpos-attack-scoping-2026-11-04.md`.  Three decisions:

1. **`LayerKernelPos` at `β = 0`, at general `(G, ρ)`** — the scoping
   found no β = 0 case in the tree (its UNVERIFIED flag); grep at
   build time confirms the only β = 0 kernel fact in the tree is
   `layerKernel_zero` (`Span3SeatSchurGateProbe`), whose module
   explicitly asserts nothing about `LayerKernelPos`.  Item 1 is
   `layerKernelPos_zero` below: the constant kernel `1` separates the
   pairing as `conj (∫ F) * (∫ F)`, whose real part is `‖∫ F‖² ≥ 0`.
   Gauge invariance is not consumed (the F2 separation at `c = 1`).
2. **FACT at the smallest non-vacuous seat** — see
   `seat_not_stratumColumnFactorization`: at the seat below, FACT is
   **false** for every `β > 0` (**K-FACT-SEAT fires**).  The column
   partition function is exactly `a(β) = (1 + e^{-2β})/2` per column,
   so `zPolymer = a(β)^24`; but the diagonal kernel value at the
   identity configuration is `∑_{S even} a^{24-|S|} b^{|S|}` with
   `b(β) = (1 - e^{-2β})/2`, which exceeds `a(β)^24` by the positive
   amount `a(β)^22 b(β)^2` contributed by one even reverse pair of
   columns.  One certified mismatch kills FACT generally
   (contrapositive of the general statement); `LayerKernelPos`
   itself is untouched by this kill and survives for other routes.
3. **PSD at the same seat** — `layerKernelPos_seat`: at the seat,
   `LayerKernelPos` holds for all `β ≥ 0` (**K-LKP-SEAT does not
   fire**): the closed form writes the kernel as a sum over even
   column families of nonnegative weights times `Φ_S(u) Φ_S(u')`,
   so the pairing is a nonnegative sum of `‖Z_S‖²` terms.

## The seat

`N = 2`, `G = Multiplicative (ZMod 2)` (written multiplicatively),
`d = 1`, `ρ` the sign representation (the `1 × 1` unitary with entry
`seatSign g = ±1`), `μG` the uniform probability measure
`(2)⁻¹ • Measure.count`.  Sizes: `LayerSite 2` has `8` sites,
`LayerColumn 2` has `8 × 3 = 24` columns, the stratum configuration
space `LayerSite 2 → G` has `2^8 = 256` points, the layer
configuration space `LayerLink 2 → G` has `2^24` points.  The
pairing is manipulated symbolically (Gram separation), never by
enumerating `2^24` configurations, so the seat does not breach the
brick's S–M band.  At the seat every column density takes values in
`{0, 2}` only, `exp (-β · dens) = a(β) + b(β) · χ(word)`, and the
shared-stratum average of a character monomial is `1` on even
column families and `0` otherwise — that parity filter is the whole
engine.

## Honesty

A seat decision is a seat decision: it kills generally if negative,
but a positive seat result is evidence at ONE seat, not the general
statement.  FACT is dead generally (item 2); `LayerKernelPos` in
general remains open — this brick proves it at `β = 0` for all
`(G, ρ)` (item 1) and at one finite seat for `β ≥ 0` (item 3), and
nothing more.  NO CLAIM; dials 0/4; a general discharge would move
no dial.
-/

import ThetLogos.Span3SeatSchurGateProbe
import ThetLogos.Span3MarginPin
import ThetLogos.LayerKernelPos

open MeasureTheory Finset
open scoped ENNReal

namespace ThetLogos

/-! ## Item 1 — `LayerKernelPos` at `β = 0`, general `(G, ρ)` -/

/-- **Item 1 (β = 0 closed).**  At `β = 0` the layer kernel is the
constant `1` (`layerKernel_zero`), the pairing separates, and its
real part is a norm square.  Hence `LayerKernelPos` holds at
`β = 0` at the full generality of its definition, for every
observable `F` (gauge invariance not consumed). -/
theorem layerKernelPos_zero {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableInv G] [TopologicalSpace G] [IsTopologicalGroup G]
    [BorelSpace G] [SecondCountableTopology G] {d : ℕ}
    (μG : Measure G) [IsProbabilityMeasure μG]
    [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
    [Measure.IsInvInvariant μG]
    (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ)) {N : ℕ} [NeZero N] :
    LayerKernelPos (N := N) μG ρ 0 := by
  intro F _hF
  have step1 : (∫ u, ∫ u', (starRingEnd ℂ) (F u) * layerKernel μG ρ 0 u u' * F u'
        ∂(Measure.pi fun _ : LayerLink N => μG)
        ∂(Measure.pi fun _ : LayerLink N => μG))
      = (∫ u, (starRingEnd ℂ) (F u)
          * (∫ u', F u' ∂(Measure.pi fun _ : LayerLink N => μG))
          ∂(Measure.pi fun _ : LayerLink N => μG)) := by
    apply integral_congr_ae (ae_of_all _ _)
    intro u
    have hinner : (∫ u', (starRingEnd ℂ) (F u) * layerKernel μG ρ 0 u u' * F u'
          ∂(Measure.pi fun _ : LayerLink N => μG))
        = ∫ u', (starRingEnd ℂ) (F u) * F u'
            ∂(Measure.pi fun _ : LayerLink N => μG) := by
      apply integral_congr_ae (ae_of_all _ _)
      intro u'
      rw [layerKernel_zero μG ρ u u', mul_one]
    rw [hinner, integral_const_mul]
  rw [step1, integral_mul_const]
  have hconj : (∫ u, (starRingEnd ℂ) (F u)
        ∂(Measure.pi fun _ : LayerLink N => μG))
      = (starRingEnd ℂ) (∫ u, F u
        ∂(Measure.pi fun _ : LayerLink N => μG)) :=
    integral_conj
  rw [hconj]
  have hJ : ((starRingEnd ℂ) (∫ u, F u ∂(Measure.pi fun _ : LayerLink N => μG))
        * (∫ u, F u ∂(Measure.pi fun _ : LayerLink N => μG)))
      = ((‖∫ u, F u ∂(Measure.pi fun _ : LayerLink N => μG)‖ : ℂ)) ^ 2 :=
    (mul_comm _ _).trans (RCLike.mul_conj _)
  rw [hJ, ← Complex.ofReal_pow, Complex.ofReal_re]
  positivity

/-! ## The seat: `G = Multiplicative (ZMod 2)`, discrete, uniform -/

/-- The seat topology: discrete (`⊥`). -/
instance seatInstTopologicalSpace : TopologicalSpace (Multiplicative (ZMod 2)) := ⊥

/-- The seat σ-algebra: everything measurable (`⊤`). -/
instance seatInstMeasurableSpace : MeasurableSpace (Multiplicative (ZMod 2)) := ⊤

/-- The seat topology is discrete. -/
instance seatInstDiscreteTopology : DiscreteTopology (Multiplicative (ZMod 2)) := ⟨rfl⟩

/-- The seat Borel σ-algebra agrees with `⊤`. -/
instance seatInstBorelSpace : BorelSpace (Multiplicative (ZMod 2)) :=
  ⟨borel_eq_top_of_discrete.symm⟩

/-- The seat measure: the uniform probability measure on the
two-element group, `(2)⁻¹ • Measure.count`. -/
noncomputable def seatμ : Measure (Multiplicative (ZMod 2)) :=
  (2 : ℝ≥0∞)⁻¹ • Measure.count

/-- The seat measure is a probability measure. -/
instance : IsProbabilityMeasure seatμ := by
  constructor
  have hc : Nat.card (Multiplicative (ZMod 2)) = 2 := by
    rw [Nat.card_eq_fintype_card]
    decide
  rw [seatμ, Measure.smul_apply, smul_eq_mul, Measure.count_univ,
    ENat.card_eq_coe_natCard, hc, Nat.cast_ofNat]
  exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)

/-- The seat measure is inversion-invariant. -/
instance : Measure.IsInvInvariant seatμ := by
  constructor
  show Measure.map Inv.inv ((2 : ℝ≥0∞)⁻¹ • Measure.count)
    = (2 : ℝ≥0∞)⁻¹ • Measure.count
  rw [Measure.map_smul _ measurable_inv.aemeasurable,
    Measure.map_inv_eq_self]

/-- The seat measure is left-invariant. -/
instance : Measure.IsMulLeftInvariant seatμ := by
  constructor
  intro g
  show Measure.map (g * ·) ((2 : ℝ≥0∞)⁻¹ • Measure.count)
    = (2 : ℝ≥0∞)⁻¹ • Measure.count
  rw [Measure.map_smul _ (measurable_const_mul g).aemeasurable]
  congr 1
  exact MeasureTheory.Measure.IsMulLeftInvariant.map_mul_left_eq_self
    (μ := (Measure.count : Measure (Multiplicative (ZMod 2)))) g

/-- The seat measure is right-invariant. -/
instance : Measure.IsMulRightInvariant seatμ := by
  constructor
  intro g
  show Measure.map (· * g) ((2 : ℝ≥0∞)⁻¹ • Measure.count)
    = (2 : ℝ≥0∞)⁻¹ • Measure.count
  rw [Measure.map_smul _ (measurable_mul_const g).aemeasurable]
  congr 1
  exact MeasureTheory.Measure.IsMulRightInvariant.map_mul_right_eq_self
    (μ := (Measure.count : Measure (Multiplicative (ZMod 2)))) g

/-- A singleton under the seat measure has mass `(2)⁻¹`. -/
theorem seatμ_singleton (g : Multiplicative (ZMod 2)) :
    seatμ {g} = (2 : ℝ≥0∞)⁻¹ := by
  rw [seatμ, Measure.smul_apply, smul_eq_mul, Measure.count_singleton,
    mul_one]

/-! ## The sign character of the seat group -/

/-- The sign character of `Multiplicative (ZMod 2)`: `1` at the
identity, `-1` at the other element. -/
def seatSign (g : Multiplicative (ZMod 2)) : ℝ :=
  if Multiplicative.toAdd g = 0 then 1 else -1

/-- The sign is `±1`. -/
theorem seatSign_eq (g : Multiplicative (ZMod 2)) :
    seatSign g = 1 ∨ seatSign g = -1 := by
  unfold seatSign
  split_ifs <;> simp

/-- The sign at the identity. -/
theorem seatSign_one : seatSign (1 : Multiplicative (ZMod 2)) = 1 := by
  simp [seatSign]

/-- The sign in value form: `1 - 2·(toAdd g).val`. -/
theorem seatSign_form (g : Multiplicative (ZMod 2)) :
    seatSign g = 1 - 2 * ((Multiplicative.toAdd g).val : ℝ) := by
  unfold seatSign
  split_ifs with h
  · rw [h]
    simp
  · have hval : (Multiplicative.toAdd g).val = 1 := by
      have hlt := ZMod.val_lt (Multiplicative.toAdd g)
      have hne : (Multiplicative.toAdd g).val ≠ 0 :=
        fun hv => h ((ZMod.val_eq_zero _).mp hv)
      omega
    rw [hval]
    norm_num

/-- The sign is a group homomorphism to `(ℝ, *)`. -/
theorem seatSign_mul (g h : Multiplicative (ZMod 2)) :
    seatSign (g * h) = seatSign g * seatSign h := by
  rw [seatSign_form, seatSign_form, seatSign_form,
    toAdd_mul]
  have hx : (Multiplicative.toAdd g).val ≤ 1 :=
    Nat.le_of_lt_succ (ZMod.val_lt _)
  have hy : (Multiplicative.toAdd h).val ≤ 1 :=
    Nat.le_of_lt_succ (ZMod.val_lt _)
  rw [ZMod.val_add]
  interval_cases (Multiplicative.toAdd g).val <;>
    interval_cases (Multiplicative.toAdd h).val <;> norm_num

/-- Inversion does not change the sign (the group is `2`-torsion). -/
theorem seatSign_inv (g : Multiplicative (ZMod 2)) :
    seatSign g⁻¹ = seatSign g := by
  have hneg : ∀ a : ZMod 2, -a = a := by decide
  have h : Multiplicative.toAdd g⁻¹ = Multiplicative.toAdd g :=
    hneg _
  unfold seatSign
  rw [h]

/-- The sign squares to `1`. -/
theorem seatSign_sq (g : Multiplicative (ZMod 2)) :
    seatSign g * seatSign g = 1 := by
  rcases seatSign_eq g with h | h <;> rw [h] <;> norm_num

/-- The two-element universe of the seat group. -/
theorem seat_univ :
    (Finset.univ : Finset (Multiplicative (ZMod 2)))
      = {1, Multiplicative.ofAdd 1} := by decide

/-- The sign sums to `0` over the seat group. -/
theorem sum_seatSign : ∑ g : Multiplicative (ZMod 2), seatSign g = 0 := by
  rw [seat_univ, Finset.sum_pair (by decide : (1 : Multiplicative (ZMod 2))
    ≠ Multiplicative.ofAdd 1), seatSign_one]
  have h : seatSign (Multiplicative.ofAdd 1) = -1 := by
    unfold seatSign
    split_ifs with h'
    · exact absurd h' (by decide)
    · rfl
  rw [h]
  norm_num

/-! ## The seat representation: the sign character as a `1 × 1` unitary -/

/-- The seat matrix: the `1 × 1` matrix with entry `seatSign g`. -/
def seatMat (g : Multiplicative (ZMod 2)) : Matrix (Fin 1) (Fin 1) ℂ :=
  fun _ _ => (seatSign g : ℂ)

/-- The seat matrix is unitary (its entry is a real sign). -/
theorem seatMat_mem (g : Multiplicative (ZMod 2)) :
    seatMat g ∈ Matrix.unitaryGroup (Fin 1) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext i j
  fin_cases i
  fin_cases j
  simp [seatMat, Matrix.mul_apply, Matrix.star_apply,
    Complex.conj_ofReal, ← Complex.ofReal_mul, seatSign_sq]

/-- The seat representation: the sign character, as a homomorphism
into the `1 × 1` unitary group. -/
def seatρ : Multiplicative (ZMod 2)
    →* ↥(Matrix.unitaryGroup (Fin 1) ℂ) where
  toFun g := ⟨seatMat g, seatMat_mem g⟩
  map_one' := by
    apply Subtype.ext
    ext i j
    fin_cases i
    fin_cases j
    simp [seatMat, seatSign_one]
  map_mul' := by
    intro g h
    apply Subtype.ext
    show seatMat (g * h) = _
    rw [Submonoid.coe_mul]
    ext i j
    fin_cases i
    fin_cases j
    simp [seatMat, seatSign_mul, Matrix.mul_apply,
      Complex.ofReal_mul]

/-- The seat representation's matrix is `seatMat` (by definition). -/
theorem repMatrix_seatρ (g : Multiplicative (ZMod 2)) :
    repMatrix seatρ g = seatMat g := rfl

/-- The seat character: `charFn seatρ g = seatSign g`. -/
theorem charFn_seat (g : Multiplicative (ZMod 2)) :
    charFn seatρ g = (seatSign g : ℂ) := by
  rw [charFn, repMatrix_seatρ, Matrix.trace_fin_one]
  rfl

/-- The seat column density is `1 - χ(word) ∈ {0, 2}`. -/
theorem colDensC_seat (u u' : LayerLink 2 → Multiplicative (ZMod 2))
    (P : LayerColumn 2) (α : LayerSite 2 → Multiplicative (ZMod 2)) :
    colDensC seatρ u u' P α
      = 1 - seatSign (colWord u u' P.1 P.2.1 P.2.2 α) := by
  rw [colDensC, colDens_eq, charFn_seat]
  simp

/-- The seat representation is continuous (discrete domain), the
`hρcont` side condition of the polymer lemmas. -/
theorem seatρ_cont : Continuous fun g => repMatrix seatρ g :=
  continuous_of_discreteTopology

/-! ## Integration over a finite seat is a scaled finite sum -/

/-- **The finite-seat integral.**  For a finite index type `ι`, the
integral over the product seat measure is the sum over all
configurations scaled by the inverse configuration count.  Proved
by writing the product measure as a sum of Dirac measures
(`Measure.sum_smul_dirac`), where every function is integrable,
then reading off the singleton masses. -/
theorem seatIntegralPi {ι : Type*} [Fintype ι] [DecidableEq ι]
    {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : (ι → Multiplicative (ZMod 2)) → E) :
    (∫ a, f a ∂(Measure.pi fun _ : ι => seatμ))
      = (Fintype.card (ι → Multiplicative (ZMod 2)) : ℝ)⁻¹
        • ∑ a, f a := by
  have hInt : Integrable f (Measure.pi fun _ : ι => seatμ) := by
    rw [← Measure.sum_smul_dirac (Measure.pi fun _ : ι => seatμ)]
    refine integrable_sum_dirac (fun a => measure_ne_top _ _) ?_
    exact Summable.of_finite
  rw [integral_fintype hInt, Finset.smul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  have hsing : ∀ g : Multiplicative (ZMod 2), seatμ {g} = (2 : ℝ≥0∞)⁻¹ :=
    seatμ_singleton
  have hc2 : Fintype.card (Multiplicative (ZMod 2)) = 2 := by decide
  rw [measureReal_def, Measure.pi_singleton]
  simp only [hsing]
  rw [Finset.prod_const, ← ENNReal.inv_pow, ENNReal.toReal_inv,
    Fintype.card_fun, hc2]
  simp [Finset.card_univ, ENNReal.toReal_pow]

/-! ## Seat cardinalities -/

/-- The seat group has two elements. -/
theorem seat_card : Fintype.card (Multiplicative (ZMod 2)) = 2 := by
  decide

/-- `LayerSite 2` has `2^3 = 8` sites (the time coordinate is frozen). -/
theorem layerSite_card : Fintype.card (LayerSite 2) = 8 := by decide

/-- `LayerColumn 2` has `8 × 3 = 24` columns. -/
theorem layerColumn_card : Fintype.card (LayerColumn 2) = 24 := by
  decide

/-- The stratum configuration space at the seat has `2^8 = 256`
points. -/
theorem stratum_card :
    Fintype.card (LayerSite 2 → Multiplicative (ZMod 2)) = 256 := by
  norm_num [Fintype.card_fun, seat_card, layerSite_card]

/-! ## Column signs and their factorization -/

/-- The sign of a column word: `χ` of the column's word in the
shared stratum configuration `α` between layer configurations
`u, u'`. -/
def colSign (P : LayerColumn 2)
    (α : LayerSite 2 → Multiplicative (ZMod 2))
    (u u' : LayerLink 2 → Multiplicative (ZMod 2)) : ℝ :=
  seatSign (colWord u u' P.1 P.2.1 P.2.2 α)

/-- The stratum part of a column sign: the two `α`-factors. -/
def stratumSign (P : LayerColumn 2)
    (α : LayerSite 2 → Multiplicative (ZMod 2)) : ℝ :=
  seatSign (α P.1) * seatSign (α (layerShift P.2.1 P.2.2 P.1))

/-- The layer-configuration part of a column sign: the link factor
(the two inverse link factors have the same sign, inversion being
invisible to `χ`). -/
def configSign (P : LayerColumn 2)
    (u : LayerLink 2 → Multiplicative (ZMod 2)) : ℝ :=
  seatSign (u (layerLinkOf P.1 P.2.1 P.2.2))

/-- The configuration character of a column family. -/
def configProd (S : Finset (LayerColumn 2))
    (u : LayerLink 2 → Multiplicative (ZMod 2)) : ℝ :=
  ∏ P ∈ S, configSign P u

/-- **Sign factorization.**  The column sign splits as the stratum
sign times the two configuration signs: the shared stratum sees
only `stratumSign`, the layer configurations only `configSign`. -/
theorem colSign_factor (P : LayerColumn 2)
    (α : LayerSite 2 → Multiplicative (ZMod 2))
    (u u' : LayerLink 2 → Multiplicative (ZMod 2)) :
    colSign P α u u'
      = stratumSign P α * (configSign P u' * configSign P u) := by
  unfold colSign stratumSign configSign colWord
  simp only [seatSign_mul, seatSign_inv]
  ring

/-- The Boltzmann factor of one seat column:
`exp (-β · dens) = a(β) + b(β) · χ(word)` with
`a(β) = (1 + e^{-2β})/2`, `b(β) = (1 - e^{-2β})/2`. -/
theorem exp_colDensC (β : ℝ) (P : LayerColumn 2)
    (α : LayerSite 2 → Multiplicative (ZMod 2))
    (u u' : LayerLink 2 → Multiplicative (ZMod 2)) :
    Real.exp (-β * colDensC seatρ u u' P α)
      = (1 + Real.exp (-2 * β)) / 2
        + (1 - Real.exp (-2 * β)) / 2 * colSign P α u u' := by
  rw [colDensC_seat]
  unfold colSign
  rcases seatSign_eq (colWord u u' P.1 P.2.1 P.2.2 α) with h | h
  · rw [h]
    simp only [sub_self, mul_zero, Real.exp_zero]
    ring
  · rw [h]
    have harg : -β * (1 - (-1 : ℝ)) = -2 * β := by ring
    rw [harg]
    ring

/-! ## The layer shift at `N = 2` -/

/-- The shifted site's coordinates: `σ_ν c = single ν 1 + c`. -/
theorem layerShift_apply (ν : Fin 4) (hν : ν ≠ 0) (c : LayerSite 2) :
    (layerShift ν hν c).1 = Pi.single ν 1 + c.1 := rfl

/-- A layer shift by a nonzero direction moves every site. -/
theorem layerShift_ne (ν : Fin 4) (hν : ν ≠ 0) (c : LayerSite 2) :
    layerShift ν hν c ≠ c := by
  intro hcon
  have h1 : (layerShift ν hν c).1 ν = c.1 ν := by rw [hcon]
  rw [layerShift_apply, Pi.add_apply, Pi.single_eq_same] at h1
  have h3 : (1 : ZMod 2) = 0 := by
    have h4 : c.1 ν + 1 = c.1 ν + 0 := by
      rw [add_zero, add_comm]
      exact h1
    exact add_left_cancel h4
  exact (by decide : (1 : ZMod 2) ≠ 0) h3

/-- At `N = 2` the layer shift is an involution (`1 + 1 = 0` in
`ZMod 2`). -/
theorem layerShift_shift (ν : Fin 4) (hν : ν ≠ 0) (c : LayerSite 2) :
    layerShift ν hν (layerShift ν hν c) = c := by
  apply Subtype.ext
  rw [layerShift_apply, layerShift_apply, ← add_assoc,
    ← Pi.single_add]
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  rw [h11]
  simp

/-! ## Column multiplicity and the parity filter -/

/-- The multiplicity of a site `c` in a column family `S`: how many
columns of `S` are based at `c`, plus how many are based at a site
shifted to `c`.  This is the exponent of `χ(α c)` in the family's
stratum character. -/
noncomputable def colMult (S : Finset (LayerColumn 2)) (c : LayerSite 2) : ℕ :=
  (S.filter (fun P => P.1 = c)).card
    + (S.filter (fun P => layerShift P.2.1 P.2.2 P.1 = c)).card

/-- A column family is **even** when every site has even
multiplicity. -/
noncomputable def seatEven (S : Finset (LayerColumn 2)) : Prop :=
  ∀ c, colMult S c % 2 = 0

/-- Evenness of a finite column family is decidable. -/
noncomputable instance (S : Finset (LayerColumn 2)) :
    Decidable (seatEven S) :=
  Fintype.decidableForallFintype

/-- The family's stratum character as a character monomial in the
site values: `∏_{P ∈ S} stratumSign P α = ∏_c χ(α c)^{mult_S(c)}`
(fiberwise over base sites and over shifted sites). -/
theorem stratumSign_prod (S : Finset (LayerColumn 2))
    (α : LayerSite 2 → Multiplicative (ZMod 2)) :
    ∏ P ∈ S, stratumSign P α
      = ∏ c : LayerSite 2, seatSign (α c) ^ colMult S c := by
  have hsplit : ∏ c : LayerSite 2, seatSign (α c) ^ colMult S c
      = (∏ c : LayerSite 2,
          seatSign (α c) ^ (S.filter (fun P => P.1 = c)).card)
        * ∏ c : LayerSite 2, seatSign (α c)
            ^ (S.filter (fun P => layerShift P.2.1 P.2.2 P.1 = c)).card := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun c _ => ?_
    simp only [colMult, pow_add]
  rw [hsplit]
  unfold stratumSign
  rw [Finset.prod_mul_distrib]
  congr 1
  · rw [← Finset.prod_fiberwise_of_maps_to' (s := S) (t := Finset.univ)
      (g := fun P : LayerColumn 2 => P.1)
      (f := fun c => seatSign (α c)) (fun P _ => Finset.mem_univ _)]
    refine Finset.prod_congr rfl fun c _ => ?_
    rw [Finset.prod_const]
  · rw [← Finset.prod_fiberwise_of_maps_to' (s := S) (t := Finset.univ)
      (g := fun P : LayerColumn 2 => layerShift P.2.1 P.2.2 P.1)
      (f := fun c => seatSign (α c)) (fun P _ => Finset.mem_univ _)]
    refine Finset.prod_congr rfl fun c _ => ?_
    rw [Finset.prod_const]

/-- **The parity filter.**  The shared-stratum average of a column
family's stratum character is `1` when the family is even and `0`
otherwise: at each site, `∑_g χ(g)^{mult}` is `2` for even
multiplicity and `0` for odd, and `2^8 = 256` cancels the seat
factor. -/
theorem stratum_average (S : Finset (LayerColumn 2)) :
    (256 : ℝ)⁻¹ * ∑ α : LayerSite 2 → Multiplicative (ZMod 2),
        ∏ P ∈ S, stratumSign P α
      = if seatEven S then 1 else 0 := by
  have hsum : (∑ α : LayerSite 2 → Multiplicative (ZMod 2),
        ∏ P ∈ S, stratumSign P α)
      = ∏ c : LayerSite 2, ∑ g : Multiplicative (ZMod 2),
          seatSign g ^ colMult S c := by
    have hpi : Fintype.piFinset
        (fun _ : LayerSite 2 =>
          (Finset.univ : Finset (Multiplicative (ZMod 2))))
        = Finset.univ := by
      ext α
      simp
    calc (∑ α : LayerSite 2 → Multiplicative (ZMod 2),
          ∏ P ∈ S, stratumSign P α)
        = ∑ α : LayerSite 2 → Multiplicative (ZMod 2),
            ∏ c : LayerSite 2, seatSign (α c) ^ colMult S c :=
          Finset.sum_congr rfl fun α _ => stratumSign_prod S α
      _ = ∏ c : LayerSite 2, ∑ g : Multiplicative (ZMod 2),
            seatSign g ^ colMult S c := by
          rw [Finset.prod_univ_sum, hpi]
  rw [hsum]
  have hinner : ∀ c : LayerSite 2,
      (∑ g : Multiplicative (ZMod 2), seatSign g ^ colMult S c)
        = if colMult S c % 2 = 0 then 2 else 0 := by
    intro c
    split_ifs with hev
    · calc (∑ g : Multiplicative (ZMod 2), seatSign g ^ colMult S c)
          = ∑ g : Multiplicative (ZMod 2), (1 : ℝ) := by
            refine Finset.sum_congr rfl fun g _ => ?_
            rcases seatSign_eq g with h | h
            · rw [h, one_pow]
            · rw [h]
              exact Even.neg_one_pow (Nat.even_iff.mpr hev)
        _ = 2 := by
            rw [Finset.sum_const, Finset.card_univ, seat_card]
            simp
    · have hodd : colMult S c % 2 = 1 := by
        have := Nat.mod_lt (colMult S c) (show 0 < 2 by norm_num)
        omega
      calc (∑ g : Multiplicative (ZMod 2), seatSign g ^ colMult S c)
          = ∑ g : Multiplicative (ZMod 2), seatSign g := by
            refine Finset.sum_congr rfl fun g _ => ?_
            rcases seatSign_eq g with h | h
            · rw [h, one_pow]
            · rw [h]
              exact Odd.neg_one_pow (Nat.odd_iff.mpr hodd)
        _ = 0 := sum_seatSign
  rw [Finset.prod_congr rfl fun c _ => hinner c]
  split_ifs with hsev
  · have hprod : ∏ c : LayerSite 2,
        (if colMult S c % 2 = 0 then (2 : ℝ) else 0)
        = ∏ c : LayerSite 2, (2 : ℝ) := by
      refine Finset.prod_congr rfl fun c _ => ?_
      split_ifs with hc
      · rfl
      · exact absurd (hsev c) hc
    rw [hprod, Finset.prod_const, Finset.card_univ, layerSite_card]
    norm_num
  · obtain ⟨c₀, hc₀⟩ := not_forall.mp hsev
    have hzero : ∏ c : LayerSite 2,
        (if colMult S c % 2 = 0 then (2 : ℝ) else 0) = 0 := by
      refine Finset.prod_eq_zero (Finset.mem_univ c₀) ?_
      exact ite_eq_right hc₀
    rw [hzero, mul_zero]

/-! ## The closed form of the seat kernel -/

/-- The seat Boltzmann weight of a layer action, column by column:
`exp (-action) = ∏_P (a + b · colSign P)`. -/
theorem exp_neg_layerAction (β : ℝ)
    (α : LayerSite 2 → Multiplicative (ZMod 2))
    (u u' : LayerLink 2 → Multiplicative (ZMod 2)) :
    (Real.exp (-(layerAction seatρ β α u u')) : ℂ)
      = ((∏ P : LayerColumn 2, ((1 + Real.exp (-2 * β)) / 2
          + (1 - Real.exp (-2 * β)) / 2 * colSign P α u u') : ℝ)
          : ℂ) := by
  have h1 : layerAction seatρ β α u u'
      = β * ∑ P : LayerColumn 2, colDensC seatρ u u' P α := by
    rw [layerAction_eq, layerDensSum_eq_sum_columns seatρ (by decide)
      α u u']
  rw [h1]
  have h2 : Real.exp (-(β * ∑ P : LayerColumn 2,
        colDensC seatρ u u' P α))
      = ∏ P : LayerColumn 2, ((1 + Real.exp (-2 * β)) / 2
          + (1 - Real.exp (-2 * β)) / 2 * colSign P α u u') := by
    have h3 : -(β * ∑ P : LayerColumn 2, colDensC seatρ u u' P α)
        = ∑ P : LayerColumn 2, (-β * colDensC seatρ u u' P α) := by
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun P _ => ?_
      ring
    rw [h3, Real.exp_sum]
    refine Finset.prod_congr rfl fun P _ => ?_
    exact exp_colDensC β P α u u'
  rw [h2]

/-- **Expansion over even families.**  The stratum sum of the
seat Boltzmann weight, scaled by the seat factor `(256)⁻¹`, is the
sum over even column families of `a^(24-|S|) b^|S| Φ_S(u) Φ_S(u')`:
expand the product over columns (`Finset.prod_add`), swap the
finite sums, and apply the parity filter (`stratum_average`). -/
theorem seat_kernel_expand (β : ℝ)
    (u u' : LayerLink 2 → Multiplicative (ZMod 2)) :
    (256 : ℝ)⁻¹ * ∑ α : LayerSite 2 → Multiplicative (ZMod 2),
        ∏ P : LayerColumn 2, ((1 + Real.exp (-2 * β)) / 2
          + (1 - Real.exp (-2 * β)) / 2 * colSign P α u u')
      = ∑ S ∈ Finset.univ.filter seatEven,
          ((1 + Real.exp (-2 * β)) / 2) ^ (24 - S.card)
            * ((1 - Real.exp (-2 * β)) / 2) ^ S.card
            * configProd S u * configProd S u' := by
  set a := (1 + Real.exp (-2 * β)) / 2 with ha
  set b := (1 - Real.exp (-2 * β)) / 2 with hb
  have hexp : ∀ α : LayerSite 2 → Multiplicative (ZMod 2),
      ∏ P : LayerColumn 2, (a + b * colSign P α u u')
        = ∑ S ∈ Finset.univ.powerset,
            a ^ (24 - S.card) * b ^ S.card
              * (∏ P ∈ S, stratumSign P α)
              * configProd S u * configProd S u' := by
    intro α
    calc ∏ P : LayerColumn 2, (a + b * colSign P α u u')
        = ∏ P : LayerColumn 2, (b * colSign P α u u' + a) :=
          Finset.prod_congr rfl fun P _ => add_comm _ _
      _ = ∑ S ∈ Finset.univ.powerset,
            (∏ P ∈ S, b * colSign P α u u')
              * ∏ P ∈ Finset.univ \ S, a := Finset.prod_add _ _ _
      _ = ∑ S ∈ Finset.univ.powerset,
            a ^ (24 - S.card) * b ^ S.card
              * (∏ P ∈ S, stratumSign P α)
              * configProd S u * configProd S u' := by
          refine Finset.sum_congr rfl fun S _ => ?_
          have hsign : ∏ P ∈ S, b * colSign P α u u'
              = b ^ S.card * ((∏ P ∈ S, stratumSign P α)
                  * (configProd S u' * configProd S u)) := by
            rw [Finset.prod_mul_distrib, Finset.prod_const]
            congr 1
            calc ∏ P ∈ S, colSign P α u u'
                = ∏ P ∈ S, (stratumSign P α
                    * (configSign P u' * configSign P u)) :=
                  Finset.prod_congr rfl fun P _ =>
                    colSign_factor P α u u'
              _ = (∏ P ∈ S, stratumSign P α)
                    * ((∏ P ∈ S, configSign P u')
                      * ∏ P ∈ S, configSign P u) := by
                  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
              _ = (∏ P ∈ S, stratumSign P α)
                    * (configProd S u' * configProd S u) := rfl
          have hpow : ∏ P ∈ Finset.univ \ S, a = a ^ (24 - S.card) := by
            rw [Finset.prod_const, Finset.card_sdiff, Finset.inter_univ,
              Finset.card_univ, layerColumn_card]
          rw [hsign, hpow]
          ring
  calc (256 : ℝ)⁻¹ * ∑ α : LayerSite 2 → Multiplicative (ZMod 2),
        ∏ P : LayerColumn 2, (a + b * colSign P α u u')
      = (256 : ℝ)⁻¹ * ∑ S ∈ Finset.univ.powerset,
          ∑ α : LayerSite 2 → Multiplicative (ZMod 2),
            a ^ (24 - S.card) * b ^ S.card
              * (∏ P ∈ S, stratumSign P α)
              * configProd S u * configProd S u' := by
        rw [Finset.sum_congr rfl fun α _ => hexp α, Finset.sum_comm]
    _ = ∑ S ∈ Finset.univ.powerset,
          a ^ (24 - S.card) * b ^ S.card
            * configProd S u * configProd S u'
            * ((256 : ℝ)⁻¹ * ∑ α : LayerSite 2
                → Multiplicative (ZMod 2),
                ∏ P ∈ S, stratumSign P α) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun S _ => ?_
        have hnorm : ∀ α : LayerSite 2 → Multiplicative (ZMod 2),
            a ^ (24 - S.card) * b ^ S.card
                * (∏ P ∈ S, stratumSign P α)
                * configProd S u * configProd S u'
              = (a ^ (24 - S.card) * b ^ S.card * configProd S u
                  * configProd S u')
                * ∏ P ∈ S, stratumSign P α := fun α => by ring
        rw [Finset.sum_congr rfl fun α _ => hnorm α, ← Finset.mul_sum]
        ring
    _ = ∑ S ∈ Finset.univ.powerset,
          a ^ (24 - S.card) * b ^ S.card
            * configProd S u * configProd S u'
            * (if seatEven S then 1 else 0) := by
        refine Finset.sum_congr rfl fun S _ => ?_
        rw [stratum_average]
    _ = ∑ S ∈ Finset.univ.filter seatEven,
          a ^ (24 - S.card) * b ^ S.card
            * configProd S u * configProd S u' := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun S _ => ?_
        split_ifs with hS
        · rw [mul_one]
        · rw [mul_zero]

/-- **The seat kernel in closed form.**  At the seat, the layer
kernel is the cast of a real sum over even column families. -/
theorem layerKernel_seat (β : ℝ)
    (u u' : LayerLink 2 → Multiplicative (ZMod 2)) :
    layerKernel seatμ seatρ β u u'
      = ((∑ S ∈ Finset.univ.filter seatEven,
          ((1 + Real.exp (-2 * β)) / 2) ^ (24 - S.card)
            * ((1 - Real.exp (-2 * β)) / 2) ^ S.card
            * configProd S u * configProd S u' : ℝ) : ℂ) := by
  have h1 : layerKernel seatμ seatρ β u u'
      = (∫ α : LayerSite 2 → Multiplicative (ZMod 2),
          (Real.exp (-(layerAction seatρ β α u u')) : ℂ)
          ∂(Measure.pi fun _ : LayerSite 2 => seatμ)) := rfl
  rw [h1, seatIntegralPi,
    show ((Fintype.card (LayerSite 2 → Multiplicative (ZMod 2)) : ℝ)⁻¹)
      = (256 : ℝ)⁻¹ by rw [stratum_card]; norm_num,
    Finset.sum_congr rfl fun α _ => exp_neg_layerAction β α u u',
    ← Complex.ofReal_sum, Complex.real_smul, ← Complex.ofReal_mul,
    seat_kernel_expand]

/-! ## Item 2 — the FACT decision at the seat -/

/-- A single column is never an even family: its base site has
multiplicity `1` (the shifted site differs from the base by
`layerShift_ne`). -/
theorem seatEven_singleton_false (P : LayerColumn 2) :
    ¬ seatEven {P} := by
  intro h
  have h1 : colMult {P} P.1 % 2 = 0 := h P.1
  have h2 : colMult {P} P.1 = 1 := by
    unfold colMult
    have hf1 : ({P} : Finset (LayerColumn 2)).filter
        (fun Q => Q.1 = P.1) = {P} := by
      rw [Finset.filter_singleton]
      exact ite_eq_left rfl
    have hf2 : ({P} : Finset (LayerColumn 2)).filter
        (fun Q => layerShift Q.2.1 Q.2.2 Q.1 = P.1) = ∅ := by
      rw [Finset.filter_singleton]
      exact ite_eq_right (layerShift_ne P.2.1 P.2.2 P.1)
    rw [hf1, hf2, Finset.card_singleton, Finset.card_empty]
  rw [h2] at h1
  norm_num at h1

/-- The stratum average of a single column's sign vanishes. -/
theorem stratumSign_singleton_average (P : LayerColumn 2) :
    (∑ α : LayerSite 2 → Multiplicative (ZMod 2), stratumSign P α)
      = 0 := by
  have h := stratum_average {P}
  rw [ite_eq_right (seatEven_singleton_false P)] at h
  have hprod : ∀ α : LayerSite 2 → Multiplicative (ZMod 2),
      ∏ Q ∈ ({P} : Finset (LayerColumn 2)), stratumSign Q α
        = stratumSign P α :=
    fun α => Finset.prod_singleton _ _
  rw [Finset.sum_congr rfl fun α _ => hprod α] at h
  have h256 : (256 : ℝ)⁻¹ ≠ 0 := by norm_num
  exact (mul_eq_zero.mp h).resolve_left h256

/-- **The column partition function at the seat is exactly
`a(β)`.**  The stratum average of the column's Boltzmann factor
kills the `b(β)` term (a single column is odd), leaving the
constant term. -/
theorem seat_colZ (β : ℝ) (u u' : LayerLink 2 → Multiplicative (ZMod 2))
    (P : LayerColumn 2) :
    colZ seatρ seatμ β u u' P = (1 + Real.exp (-2 * β)) / 2 := by
  rw [colZ_eq_integral_exp (ρ := seatρ) (μG := seatμ) seatρ_cont β u u' P,
    seatIntegralPi,
    show ((Fintype.card (LayerSite 2 → Multiplicative (ZMod 2)) : ℝ)⁻¹)
      = (256 : ℝ)⁻¹ by rw [stratum_card]; norm_num]
  have hsum : (∑ α : LayerSite 2 → Multiplicative (ZMod 2),
        Real.exp (-β * colDensC seatρ u u' P α))
      = 256 * ((1 + Real.exp (-2 * β)) / 2) := by
    calc (∑ α : LayerSite 2 → Multiplicative (ZMod 2),
          Real.exp (-β * colDensC seatρ u u' P α))
        = ∑ α : LayerSite 2 → Multiplicative (ZMod 2),
            ((1 + Real.exp (-2 * β)) / 2 + (1 - Real.exp (-2 * β)) / 2
              * (stratumSign P α
                * (configSign P u' * configSign P u))) := by
          refine Finset.sum_congr rfl fun α _ => ?_
          rw [exp_colDensC, colSign_factor]
      _ = (∑ α : LayerSite 2 → Multiplicative (ZMod 2),
            (1 + Real.exp (-2 * β)) / 2)
          + (∑ α : LayerSite 2 → Multiplicative (ZMod 2),
            (1 - Real.exp (-2 * β)) / 2
              * (stratumSign P α
                * (configSign P u' * configSign P u))) :=
          Finset.sum_add_distrib
      _ = 256 * ((1 + Real.exp (-2 * β)) / 2) + 0 := by
          congr 1
          · rw [Finset.sum_const, Finset.card_univ, stratum_card]
            simp [nsmul_eq_mul]
          · have hnorm : ∀ α : LayerSite 2 → Multiplicative (ZMod 2),
                (1 - Real.exp (-2 * β)) / 2
                    * (stratumSign P α
                      * (configSign P u' * configSign P u))
                  = ((1 - Real.exp (-2 * β)) / 2
                    * (configSign P u' * configSign P u))
                    * stratumSign P α := fun α => by ring
            rw [Finset.sum_congr rfl fun α _ => hnorm α, ← Finset.mul_sum,
              stratumSign_singleton_average, mul_zero]
      _ = 256 * ((1 + Real.exp (-2 * β)) / 2) := by rw [add_zero]
  rw [hsum, smul_eq_mul]
  rw [show (256 : ℝ)⁻¹ * (256 * ((1 + Real.exp (-2 * β)) / 2))
      = ((1 + Real.exp (-2 * β)) / 2) by field_simp]

/-- **The polymer partition function at the seat is `a(β)^24`.** -/
theorem seat_zPolymer (β : ℝ)
    (u u' : LayerLink 2 → Multiplicative (ZMod 2)) :
    zPolymer seatρ seatμ β u u' = ((1 + Real.exp (-2 * β)) / 2) ^ 24 := by
  show ∏ P : LayerColumn 2, colZ seatρ seatμ β u u' P = _
  rw [Finset.prod_congr rfl (fun P _ => seat_colZ β u u' P),
    Finset.prod_const, Finset.card_univ, layerColumn_card]

/-- The configuration character at the identity configuration is
`1` (every link sign is `seatSign 1 = 1`). -/
theorem configProd_one (S : Finset (LayerColumn 2)) :
    configProd S (1 : LayerLink 2 → Multiplicative (ZMod 2)) = 1 := by
  calc configProd S (1 : LayerLink 2 → Multiplicative (ZMod 2))
      = ∏ P ∈ S, (1 : ℝ) :=
        Finset.prod_congr rfl fun P _ => seatSign_one
    _ = 1 := Finset.prod_const_one

/-- The zero site of `LayerSite 2`. -/
def seatSite0 : LayerSite 2 := ⟨fun _ => 0, rfl⟩

/-- The first spatial direction, as a nonzero `Fin 4` element. -/
def seatDir1 : {ν : Fin 4 // ν ≠ 0} := ⟨1, by decide⟩

/-- A chosen column at the seat: base `seatSite0`, direction
`seatDir1`. -/
def seatCol0 : LayerColumn 2 := (seatSite0, seatDir1)

/-- The reverse partner of `seatCol0`: the column over the shifted
site with the same direction.  At `N = 2` shifting twice is the
identity, so the pair `{seatCol0, seatCol0'}` has every site at
multiplicity `0` or `2`. -/
def seatCol0' : LayerColumn 2 :=
  (layerShift seatDir1.1 seatDir1.2 seatSite0, seatDir1)

/-- The two columns of the pair differ (their base sites differ). -/
theorem seatCol0_ne : seatCol0' ≠ seatCol0 :=
  fun h => layerShift_ne seatDir1.1 seatDir1.2 seatSite0
    (congrArg Prod.fst h)

/-- **The reverse pair is even.**  Every site has multiplicity
`2·(1[c = base] + 1[c = shifted base])` in `{seatCol0, seatCol0'}`:
the bases are `base, σ base` and the shifts are `σ base, σ² base =
base`. -/
theorem seatEven_pair : seatEven {seatCol0, seatCol0'} := by
  intro c
  have hne : seatCol0 ≠ seatCol0' := fun h => seatCol0_ne h.symm
  have hfin : ∀ (p : LayerColumn 2 → Prop) [DecidablePred p],
      (({seatCol0, seatCol0'} : Finset (LayerColumn 2)).filter p).card
        = (if p seatCol0 then 1 else 0)
          + (if p seatCol0' then 1 else 0) := by
    intro p _
    rw [Finset.card_filter, Finset.sum_pair hne]
  unfold colMult
  rw [hfin, hfin]
  have e1 : seatCol0.1 = seatSite0 := rfl
  have e2 : seatCol0'.1
      = layerShift seatDir1.1 seatDir1.2 seatSite0 := rfl
  have e3 : layerShift seatCol0.2.1 seatCol0.2.2 seatCol0.1
      = layerShift seatDir1.1 seatDir1.2 seatSite0 := rfl
  have e4 : layerShift seatCol0'.2.1 seatCol0'.2.2 seatCol0'.1
      = seatSite0 :=
    layerShift_shift seatDir1.1 seatDir1.2 seatSite0
  rw [e3, e4, e1, e2]
  obtain ⟨k, hk⟩ : ∃ k : ℕ,
      ((if seatSite0 = c then (1 : ℕ) else 0)
        + (if layerShift seatDir1.1 seatDir1.2 seatSite0 = c
            then 1 else 0))
        + ((if layerShift seatDir1.1 seatDir1.2 seatSite0 = c
            then 1 else 0)
          + (if seatSite0 = c then 1 else 0)) = 2 * k :=
    ⟨(if seatSite0 = c then 1 else 0)
      + (if layerShift seatDir1.1 seatDir1.2 seatSite0 = c
          then 1 else 0), by ring⟩
  rw [hk]
  omega

/-- **Item 2 — K-FACT-SEAT fires.**  FACT (the stratum column
factorization `StratumColumnFactorization`) is **false at the
seat for every `β > 0`**: at the identity configuration, FACT
would force `layerKernel = zPolymer = a(β)^24`, but the closed
form gives `∑_{S even} a^{24-|S|} b^{|S|} ≥ a^24 + a^22 b^2 >
a^24`, the excess being the reverse pair's contribution.  One
certified mismatch kills FACT generally (the seat is a
specialization of the general statement).  `LayerKernelPos` is
untouched by this kill — it is proved at the same seat in
`layerKernelPos_seat` below, by the Gram route, not through FACT. -/
theorem seat_not_stratumColumnFactorization {β : ℝ} (hβ : 0 < β) :
    ¬ StratumColumnFactorization (N := 2) seatμ seatρ β := by
  intro hfact
  have hK := hfact 1 1
  rw [layerKernel_seat β 1 1, seat_zPolymer β 1 1] at hK
  have hsum1 : (∑ S ∈ Finset.univ.filter seatEven,
        ((1 + Real.exp (-2 * β)) / 2) ^ (24 - S.card)
          * ((1 - Real.exp (-2 * β)) / 2) ^ S.card
          * configProd S 1 * configProd S 1)
      = ∑ S ∈ Finset.univ.filter seatEven,
          ((1 + Real.exp (-2 * β)) / 2) ^ (24 - S.card)
            * ((1 - Real.exp (-2 * β)) / 2) ^ S.card := by
    refine Finset.sum_congr rfl fun S _ => ?_
    rw [configProd_one, mul_one, mul_one]
  rw [hsum1] at hK
  have hre := congrArg Complex.re hK
  simp only [Complex.ofReal_re] at hre
  have ha0 : 0 < (1 + Real.exp (-2 * β)) / 2 := by
    have h := Real.exp_pos (-2 * β)
    linarith
  have hb0 : 0 < (1 - Real.exp (-2 * β)) / 2 := by
    have h : Real.exp (-2 * β) < 1 := by
      rw [Real.exp_lt_one_iff]
      linarith
    linarith
  have hsub : ({∅, {seatCol0, seatCol0'}}
        : Finset (Finset (LayerColumn 2)))
      ⊆ Finset.univ.filter seatEven := by
    intro S hS
    simp only [Finset.mem_insert, Finset.mem_singleton] at hS
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rcases hS with rfl | rfl
    · intro c
      simp [colMult]
    · exact seatEven_pair
  have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (f := fun S => ((1 + Real.exp (-2 * β)) / 2) ^ (24 - S.card)
      * ((1 - Real.exp (-2 * β)) / 2) ^ S.card)
    (fun S _ _ => mul_nonneg (pow_nonneg ha0.le _) (pow_nonneg hb0.le _))
  have hne_pair : (∅ : Finset (LayerColumn 2))
      ≠ {seatCol0, seatCol0'} := by
    intro h
    have hc := congrArg Finset.card h
    rw [Finset.card_empty,
      Finset.card_pair (fun hh => seatCol0_ne hh.symm)] at hc
    norm_num at hc
  have hpair : (∑ S ∈ ({∅, {seatCol0, seatCol0'}}
        : Finset (Finset (LayerColumn 2))),
        ((1 + Real.exp (-2 * β)) / 2) ^ (24 - S.card)
          * ((1 - Real.exp (-2 * β)) / 2) ^ S.card)
      = ((1 + Real.exp (-2 * β)) / 2) ^ 24
        + ((1 + Real.exp (-2 * β)) / 2) ^ 22
          * ((1 - Real.exp (-2 * β)) / 2) ^ 2 := by
    rw [Finset.sum_pair hne_pair, Finset.card_empty,
      Finset.card_pair (fun hh => seatCol0_ne hh.symm)]
    norm_num
  have hpos : 0 < ((1 + Real.exp (-2 * β)) / 2) ^ 22
      * ((1 - Real.exp (-2 * β)) / 2) ^ 2 :=
    mul_pos (pow_pos ha0 22) (pow_pos hb0 2)
  linarith

/-- The corpus installs a classical `DecidableEq` for `LayerSite`
(`PlaneCrossingBeta2`) but not for `LayerLink`; the finite-seat
integral over layer configurations needs one.  Installed here in
the same style. -/
noncomputable instance : DecidableEq (LayerLink 2) :=
  Classical.decEq _

/-- **Item 3 — PSD at the seat; K-LKP-SEAT does not fire.**  At
the seat, `LayerKernelPos` holds for all `β ≥ 0`: with the closed
form of `layerKernel_seat`, the pairing is (a positive scalar
times) a sum over even column families of nonnegative weights
`a^(24-|S|) b^(|S|)` (both `a, b ≥ 0` when `β ≥ 0`) times
`‖Z_S‖²`, where `Z_S = ∑_u Φ_S(u) F(u)` — a Gram sum.  Gauge
invariance is not consumed.  This is a seat result: it proves
`LayerKernelPos` at this one finite seat, not in general. -/
theorem layerKernelPos_seat {β : ℝ} (hβ : 0 ≤ β) :
    LayerKernelPos (N := 2) seatμ seatρ β := by
  intro F _hF
  have ha0 : 0 ≤ (1 + Real.exp (-2 * β)) / 2 := by
    have h := Real.exp_pos (-2 * β)
    linarith
  have hb0 : 0 ≤ (1 - Real.exp (-2 * β)) / 2 := by
    have h : Real.exp (-2 * β) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      linarith
    linarith
  have hsmul : ∀ (r : ℝ) (x : ℂ), r • x = (r : ℂ) * x := by
    intro r x
    rw [Complex.real_smul]
  have hP1 : (∫ u, ∫ u', (starRingEnd ℂ) (F u)
        * layerKernel seatμ seatρ β u u' * F u'
        ∂(Measure.pi fun _ : LayerLink 2 => seatμ)
        ∂(Measure.pi fun _ : LayerLink 2 => seatμ))
      = ((Fintype.card (LayerLink 2 → Multiplicative (ZMod 2))
          : ℝ)⁻¹)
        • ∑ u, (((Fintype.card (LayerLink 2
            → Multiplicative (ZMod 2)) : ℝ)⁻¹)
          • ∑ u', (starRingEnd ℂ) (F u)
              * layerKernel seatμ seatρ β u u' * F u') := by
    rw [seatIntegralPi]
    congr 1
    refine Finset.sum_congr rfl fun u _ => ?_
    exact seatIntegralPi _
  have hterm : ∀ u u' : LayerLink 2 → Multiplicative (ZMod 2),
      (starRingEnd ℂ) (F u)
        * ((∑ S ∈ Finset.univ.filter seatEven,
            ((1 + Real.exp (-2 * β)) / 2) ^ (24 - S.card)
              * ((1 - Real.exp (-2 * β)) / 2) ^ S.card
              * configProd S u * configProd S u' : ℝ) : ℂ) * F u'
      = ∑ S ∈ Finset.univ.filter seatEven,
          ((((1 + Real.exp (-2 * β)) / 2) ^ (24 - S.card)
            * ((1 - Real.exp (-2 * β)) / 2) ^ S.card : ℝ) : ℂ)
          * ((starRingEnd ℂ) (F u)
            * ((configProd S u : ℝ) : ℂ))
          * (((configProd S u' : ℝ) : ℂ) * F u') := by
    intro u u'
    rw [Complex.ofReal_sum, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun S _ => ?_
    push_cast
    ring
  have hswap : ∀ g : (LayerLink 2 → Multiplicative (ZMod 2))
      → (LayerLink 2 → Multiplicative (ZMod 2))
      → Finset (LayerColumn 2) → ℂ,
      (∑ u, ∑ u', ∑ S ∈ Finset.univ.filter seatEven, g u u' S)
        = ∑ S ∈ Finset.univ.filter seatEven, ∑ u, ∑ u', g u u' S := by
    intro g
    calc (∑ u, ∑ u', ∑ S ∈ Finset.univ.filter seatEven, g u u' S)
        = ∑ u, ∑ S ∈ Finset.univ.filter seatEven, ∑ u', g u u' S :=
          Finset.sum_congr rfl fun u _ => Finset.sum_comm
      _ = ∑ S ∈ Finset.univ.filter seatEven, ∑ u, ∑ u', g u u' S :=
          Finset.sum_comm
  have hfac : ∀ S : Finset (LayerColumn 2),
      (∑ u, ∑ u',
          ((((1 + Real.exp (-2 * β)) / 2) ^ (24 - S.card)
            * ((1 - Real.exp (-2 * β)) / 2) ^ S.card : ℝ) : ℂ)
          * ((starRingEnd ℂ) (F u)
            * ((configProd S u : ℝ) : ℂ))
          * (((configProd S u' : ℝ) : ℂ) * F u'))
        = ((((1 + Real.exp (-2 * β)) / 2) ^ (24 - S.card)
            * ((1 - Real.exp (-2 * β)) / 2) ^ S.card : ℝ) : ℂ)
          * ((∑ u, (starRingEnd ℂ) (F u)
              * ((configProd S u : ℝ) : ℂ))
            * (∑ u', ((configProd S u' : ℝ) : ℂ) * F u')) := by
    intro S
    calc (∑ u, ∑ u',
          ((((1 + Real.exp (-2 * β)) / 2) ^ (24 - S.card)
            * ((1 - Real.exp (-2 * β)) / 2) ^ S.card : ℝ) : ℂ)
          * ((starRingEnd ℂ) (F u)
            * ((configProd S u : ℝ) : ℂ))
          * (((configProd S u' : ℝ) : ℂ) * F u'))
        = ∑ u, ((((1 + Real.exp (-2 * β)) / 2) ^ (24 - S.card)
            * ((1 - Real.exp (-2 * β)) / 2) ^ S.card : ℝ) : ℂ)
            * ((starRingEnd ℂ) (F u)
              * ((configProd S u : ℝ) : ℂ))
            * (∑ u', ((configProd S u' : ℝ) : ℂ) * F u') := by
          refine Finset.sum_congr rfl fun u _ => ?_
          rw [← Finset.mul_sum]
      _ = ((((1 + Real.exp (-2 * β)) / 2) ^ (24 - S.card)
            * ((1 - Real.exp (-2 * β)) / 2) ^ S.card : ℝ) : ℂ)
          * ((∑ u, (starRingEnd ℂ) (F u)
              * ((configProd S u : ℝ) : ℂ))
            * (∑ u', ((configProd S u' : ℝ) : ℂ) * F u')) := by
          rw [← Finset.sum_mul, ← Finset.mul_sum, mul_assoc]
  have hZ : ∀ S : Finset (LayerColumn 2),
      (∑ u, (starRingEnd ℂ) (F u) * ((configProd S u : ℝ) : ℂ))
        = (starRingEnd ℂ)
          (∑ u, ((configProd S u : ℝ) : ℂ) * F u) := by
    intro S
    rw [map_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [map_mul, Complex.conj_ofReal]
    exact mul_comm _ _
  have hKrw : ∀ u u' : LayerLink 2 → Multiplicative (ZMod 2),
      (starRingEnd ℂ) (F u) * layerKernel seatμ seatρ β u u' * F u'
        = (starRingEnd ℂ) (F u)
          * ((∑ S ∈ Finset.univ.filter seatEven,
              ((1 + Real.exp (-2 * β)) / 2) ^ (24 - S.card)
                * ((1 - Real.exp (-2 * β)) / 2) ^ S.card
                * configProd S u * configProd S u' : ℝ) : ℂ)
          * F u' := by
    intro u u'
    rw [layerKernel_seat]
  have hP : (∫ u, ∫ u', (starRingEnd ℂ) (F u)
        * layerKernel seatμ seatρ β u u' * F u'
        ∂(Measure.pi fun _ : LayerLink 2 => seatμ)
        ∂(Measure.pi fun _ : LayerLink 2 => seatμ))
      = (((Fintype.card (LayerLink 2 → Multiplicative (ZMod 2))
            : ℝ)⁻¹
          * ((Fintype.card (LayerLink 2 → Multiplicative (ZMod 2))
              : ℝ)⁻¹
            * ∑ S ∈ Finset.univ.filter seatEven,
                ((1 + Real.exp (-2 * β)) / 2) ^ (24 - S.card)
                  * ((1 - Real.exp (-2 * β)) / 2) ^ S.card
                  * ‖∑ u, ((configProd S u : ℝ) : ℂ) * F u‖ ^ 2)
          : ℝ) : ℂ) := by
    calc (∫ u, ∫ u', (starRingEnd ℂ) (F u)
          * layerKernel seatμ seatρ β u u' * F u'
          ∂(Measure.pi fun _ : LayerLink 2 => seatμ)
          ∂(Measure.pi fun _ : LayerLink 2 => seatμ))
        = ((Fintype.card (LayerLink 2 → Multiplicative (ZMod 2))
            : ℝ)⁻¹)
          • ∑ u, (((Fintype.card (LayerLink 2
              → Multiplicative (ZMod 2)) : ℝ)⁻¹)
            • ∑ u', (starRingEnd ℂ) (F u)
                * layerKernel seatμ seatρ β u u' * F u') := hP1
      _ = (((Fintype.card (LayerLink 2 → Multiplicative (ZMod 2))
              : ℝ)⁻¹ : ℂ))
          * ((((Fintype.card (LayerLink 2
              → Multiplicative (ZMod 2)) : ℝ)⁻¹ : ℂ))
            * ∑ u, ∑ u', (starRingEnd ℂ) (F u)
                * layerKernel seatμ seatρ β u u' * F u') := by
          have e1 : ∀ x : ℂ,
              ((Fintype.card (LayerLink 2 → Multiplicative (ZMod 2))
                : ℝ)⁻¹) • x
              = (((Fintype.card (LayerLink 2
                  → Multiplicative (ZMod 2)) : ℝ)⁻¹ : ℂ)) * x := by
            intro x
            rw [Complex.real_smul, Complex.ofReal_inv]
          rw [e1]
          congr 1
          rw [← Finset.smul_sum, e1]
      _ = (((Fintype.card (LayerLink 2 → Multiplicative (ZMod 2))
              : ℝ)⁻¹ : ℂ))
          * ((((Fintype.card (LayerLink 2
              → Multiplicative (ZMod 2)) : ℝ)⁻¹ : ℂ))
            * ∑ S ∈ Finset.univ.filter seatEven,
                ((((1 + Real.exp (-2 * β)) / 2) ^ (24 - S.card)
                  * ((1 - Real.exp (-2 * β)) / 2) ^ S.card : ℝ)
                  : ℂ)
                * ((starRingEnd ℂ)
                    (∑ u, ((configProd S u : ℝ) : ℂ) * F u)
                  * (∑ u, ((configProd S u : ℝ) : ℂ) * F u))) := by
          congr 1
          congr 1
          rw [Finset.sum_congr rfl fun u _ =>
            Finset.sum_congr rfl fun u' _ => hKrw u u']
          rw [Finset.sum_congr rfl fun u _ =>
            Finset.sum_congr rfl fun u' _ => hterm u u', hswap]
          refine Finset.sum_congr rfl fun S _ => ?_
          rw [hfac, hZ]
      _ = (((Fintype.card (LayerLink 2 → Multiplicative (ZMod 2))
            : ℝ)⁻¹
          * ((Fintype.card (LayerLink 2 → Multiplicative (ZMod 2))
              : ℝ)⁻¹
            * ∑ S ∈ Finset.univ.filter seatEven,
                ((1 + Real.exp (-2 * β)) / 2) ^ (24 - S.card)
                  * ((1 - Real.exp (-2 * β)) / 2) ^ S.card
                  * ‖∑ u, ((configProd S u : ℝ) : ℂ) * F u‖ ^ 2)
          : ℝ) : ℂ) := by
          have hper : ∀ S ∈ Finset.univ.filter seatEven,
              ((((1 + Real.exp (-2 * β)) / 2) ^ (24 - S.card)
                  * ((1 - Real.exp (-2 * β)) / 2) ^ S.card : ℝ)
                  : ℂ)
                * ((starRingEnd ℂ)
                    (∑ u, ((configProd S u : ℝ) : ℂ) * F u)
                  * (∑ u, ((configProd S u : ℝ) : ℂ) * F u))
              = ((((1 + Real.exp (-2 * β)) / 2) ^ (24 - S.card)
                    * ((1 - Real.exp (-2 * β)) / 2) ^ S.card
                    * ‖∑ u, ((configProd S u : ℝ) : ℂ) * F u‖ ^ 2
                  : ℝ) : ℂ) := by
            intro S _
            have hcc : (starRingEnd ℂ)
                  (∑ u, ((configProd S u : ℝ) : ℂ) * F u)
                * (∑ u, ((configProd S u : ℝ) : ℂ) * F u)
              = ((‖∑ u, ((configProd S u : ℝ) : ℂ) * F u‖ ^ 2
                  : ℝ) : ℂ) :=
              (mul_comm _ _).trans
                ((RCLike.mul_conj _).trans (Complex.ofReal_pow _ _).symm)
            rw [hcc, ← Complex.ofReal_mul]
          rw [Finset.sum_congr rfl hper, ← Complex.ofReal_inv,
            ← Complex.ofReal_sum, ← Complex.ofReal_mul,
            ← Complex.ofReal_mul]
  rw [hP, Complex.ofReal_re]
  have hMnn : (0 : ℝ)
      ≤ ((Fintype.card (LayerLink 2 → Multiplicative (ZMod 2))
        : ℝ))⁻¹ :=
    inv_nonneg.mpr (by positivity)
  refine mul_nonneg hMnn (mul_nonneg hMnn ?_)
  refine Finset.sum_nonneg fun S _ => ?_
  refine mul_nonneg (mul_nonneg (pow_nonneg ha0 _) (pow_nonneg hb0 _)) ?_
  exact pow_nonneg (norm_nonneg _) _

end ThetLogos
