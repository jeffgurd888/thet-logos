/-
# ThetLogos.PlaqBlockContraction — Brick A2-2c: the one-corner
contraction (the telescoping step), Route B

**Fences, up front.** NO CLAIM. Parts of the Clay Yang–Mills
statement closed by this module: **0**. Dials **0/4**, unmoved.
Route B scope on the face: one-plaquette mechanism + leading
square only — this brick is **NOT** `𝒜 ⪰ 0`, **NOT** clause
(a), and the block is not a factor of `layerKernel`. The
literal quotient form R1 is CERTIFIED DEAD (probe BR1-005)
and is not touched.

## What this brick is

The telescoping step of A2-2, at the level of `ρ`'s matrix
coefficients: for one shared corner variable `x`, the Haar
integral over `x` of a product of two column-factor
*polynomial approximants* — the finite partial sums of
A2-1's exponential series in `Re tr ρ` (see
`PlaquetteFactorPD`: `f_β = e^{−β} · exp ((β/d) · Re tr ρ)`,
whose order-`K` partial sum in the density variable is
`colApprox` below) — contracted via the owned twirl
evaluations. Two corner types, separately reported (the
pack's two sub-deliverables):

1. **Mixed corner** (the shared variable sits in the
   `b`-slot of one column and the `a`-slot of the other;
   plaquette corners `c₁₀`, `c₀₁`): the owned mixed sewing
   `integral_charFn_mul_charFn_inv` (PW-1, in
   `QuadReMomentTelescope`) applies to the primary pairing.
2. **Source/sink corners** (the shared variable sits in the
   `a`-slot of both columns — source, corner `c₀₀` — or in
   the `b`-slot of both — sink, corner `c₁₁`): the primary
   pairing is the same-orientation twirl, evaluated by the
   owned Frobenius–Schur sewing `charFn_sewing` (PW-3, in
   `RepTensorTwirl`), through the named `J`-contraction
   `jSew` against the canonical invariant form.

**Conjugate-pair assembly (binding probe caveat).** Because
the approximants are polynomials in `Re tr ρ`, each factor
contributes both a character and its inverse character; the
contraction is assembled on conjugate PAIRS — the mixed
terms pair as `χ(C₁C₂)` with `χ(C₁⁻¹C₂⁻¹)`, and the
same-orientation terms pair as the `J`-contraction at
`(C₁, C₂⁻¹)` with the one at `(C₁⁻¹, C₂)` (mixed corner) —
never term-by-term at a non-self-dual label. A term-by-term
failure at such a label would not be a counterexample; the
paired formulas below are the statement.

**Hypothesis fences (inherited from the owned twirls, not
papered over).** The evaluated pair twirls are
irreducible-only (PW-1/PW-3 honesty ledgers: every consumer
carries `RepIrreducible ρ`); the same-orientation evaluation
carries `0 < d`; the vanishing of the single (one-factor)
corner integrals is owned only at `2 ≤ d`
(`integral_repMatrix_entry_eq_zero`; at `d = 1` the trivial
character has mean `1`, so no such vanishing is asserted
there). The plaquette statements (T)/(P) of A2-2a carry no
irreducibility hypothesis; this brick's contraction
formulas do, and the gap is a named seam for A2-2d, not an
assumption smuggled into (T)/(P).

**Approximant-order scope actually landed.** Order `K = 1`
in each factor (and the total-degree-≤2 boundary orders
`(2,0)`, `(0,2)`), for both corner types. **SEAM
(A2-2c-HIGHER-ORDERS):** approximant orders with total
degree `≥ 3` in the two factors contain corner integrals of
three or more matrix coefficients of the shared variable —
triple-and-higher tensor twirls, which the corpus does not
own (the β-line's triple twirls are likewise unevaluated).
Per the pack's unowned-twirl stop, those orders are NOT
landed here and are named for separate pricing; nothing
below silently restricts to the landed orders — every
headline states its order on its face. A2-2d assembles
uniformly in `K` only over the orders this brick (or a
successor pricing the higher twirls) supplies.

**K-A2 status:** no polynomial-stage counterexample was
found at the landed orders: at every landed order the
contraction depends on the remaining data only through the
two frozen words `frozenB` / `frozenA` (the corner-rotated
column words), i.e. only through holonomy-type data of the
two columns — K-A2 does not fire at these orders. Orders
`≥ 3` total are untested by this brick (the seam above),
not certified either way.
-/

import ThetLogos.PlaqBlockReductions
import ThetLogos.QuadReMomentTelescope
import ThetLogos.RepTensorTwirl

namespace ThetLogos

open Finset MeasureTheory

section Setup

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ))

/-! ## §1. The contracted objects -/

/-- **The real character, in `ℂ`**: `((tr ρ w).re : ℂ)` — the
quantity A2-1's exponential series is a series in. -/
noncomputable def reTrC (w : G) : ℂ :=
  ((Matrix.trace (repMatrix ρ w)).re : ℂ)

/-- **The `J`-contraction** of two frozen words: the
same-orientation (Frobenius–Schur) sewing of `charFn_sewing`
(PW-3), named: the frozen matrix coefficients of `A` and `B`
contracted against `star (J i k) * J j l` for the canonical
invariant form `J = canonicalForm ρ`. -/
noncomputable def jSew (A B : G) : ℂ :=
  ∑ p : Fin d × Fin d, ∑ q : Fin d × Fin d,
    repMatrix ρ A p.2 p.1 * repMatrix ρ B q.2 q.1
      * (star ((canonicalForm ρ) p.1 q.1) * (canonicalForm ρ) p.2 q.2)

/-- **The same-orientation corner factor**: the value of the
`(2,0)` twirl contraction of two frozen words — zero when
the Frobenius–Schur indicator vanishes, else `(d)⁻¹` times
the `J`-contraction. -/
noncomputable def jForm (A B : G) : ℂ :=
  if fsIndicator ρ μG = 0 then 0 else (d : ℂ)⁻¹ * jSew ρ A B

/-- **The polynomial approximant of a column factor**, of
order `K`: the finite partial sum of the exponential series
of `columnKernel ρ β a b u u' = exp (−β · wordDensity ρ w)`
in the density variable, at the column word
`w = a * u' * b⁻¹ * u⁻¹`. (A2-1's series form: the factor is
the `K → ∞` limit of these partial sums, through
`wordDensity = 1 − (Re tr ρ)/d`.) -/
noncomputable def colApprox (β : ℝ) (K : ℕ) (a b u u' : G) : ℝ :=
  ∑ k ∈ Finset.range (K + 1), (-β) ^ k / (Nat.factorial k : ℝ)
    * (wordDensity ρ (a * u' * b⁻¹ * u⁻¹)) ^ k

/-- **The frozen word of an `a`-slot column**: when the
shared corner variable `x` sits in the `a`-slot, the column
word is `x * frozenA b u u'` on the nose. -/
def frozenA (b u u' : G) : G := u' * b⁻¹ * u⁻¹

/-- **The frozen word of a `b`-slot column**: when the shared
corner variable `x` sits in the `b`-slot, the column word
`a * u' * x⁻¹ * u⁻¹` has the same character (and the same
`reTrC`) as `x⁻¹ * frozenB a u u'`, by cyclic rotation of the
word (the re-basing A2-2b landed as `wordDensity_rotate4`). -/
def frozenB (a u u' : G) : G := u⁻¹ * a * u'

/-! ## §2. Character expansions of `reTrC` -/

/-- `reTrC` is the average of a character and its inverse
character (A2-1's `reTr_eq`, restated for `charFn`). -/
theorem reTrC_eq (w : G) :
    reTrC ρ w = (charFn ρ w + charFn ρ w⁻¹) / 2 := by
  have h := reTr_eq ρ w
  show ((Matrix.trace (repMatrix ρ w)).re : ℂ) = _
  rw [h]
  rfl

/-- Characters are invariant under swapping a two-letter
word (trace cyclicity). -/
theorem charFn_rotate (a b : G) :
    charFn ρ (a * b) = charFn ρ (b * a) := by
  show Matrix.trace (repMatrix ρ (a * b))
    = Matrix.trace (repMatrix ρ (b * a))
  rw [repMatrix_mul, repMatrix_mul, Matrix.trace_mul_comm]

/-- `reTrC` is invariant under swapping a two-letter word. -/
theorem reTrC_rotate (a b : G) :
    reTrC ρ (a * b) = reTrC ρ (b * a) := by
  rw [reTrC_eq, reTrC_eq, mul_inv_rev, mul_inv_rev,
    charFn_rotate ρ a b, charFn_rotate ρ b⁻¹ a⁻¹]

/-- Expansion of `reTrC` at an `a`-slot word `x * C`: the
inverse character is the one at `x⁻¹ * C⁻¹`. -/
theorem reTrC_expand_mul (x C : G) :
    reTrC ρ (x * C)
      = (charFn ρ (x * C) + charFn ρ (x⁻¹ * C⁻¹)) / 2 := by
  rw [reTrC_eq, mul_inv_rev, charFn_rotate ρ C⁻¹ x⁻¹]

/-- Expansion of `reTrC` at a `b`-slot word `x⁻¹ * C`: the
inverse character is the one at `x * C⁻¹`. -/
theorem reTrC_expand_inv_mul (x C : G) :
    reTrC ρ (x⁻¹ * C)
      = (charFn ρ (x⁻¹ * C) + charFn ρ (x * C⁻¹)) / 2 := by
  rw [reTrC_eq, mul_inv_rev, inv_inv, charFn_rotate ρ C⁻¹ x]

/-! ## §3. Integrability helpers (characters of words in `x`) -/

/-- A character of a measurable word in `x` is integrable:
measurable (character of a continuous representation) and
bounded by `d` (`norm_charFn_le`) on a probability space. -/
theorem integrable_charFn_comp (hρcont : Continuous fun g => repMatrix ρ g)
    {w : G → G} (hw : Measurable w) :
    Integrable (fun x => charFn ρ (w x)) μG :=
  Integrable.of_bound
    ((measurable_charFn ρ hρcont).comp hw).aestronglyMeasurable
    (d : ℝ) (Filter.Eventually.of_forall fun x => norm_charFn_le ρ (w x))

/-- A product of two characters of measurable words in `x`
is integrable: bounded by `d * d`. -/
theorem integrable_charFn_comp_mul
    (hρcont : Continuous fun g => repMatrix ρ g)
    {w₁ w₂ : G → G} (hw₁ : Measurable w₁) (hw₂ : Measurable w₂) :
    Integrable (fun x => charFn ρ (w₁ x) * charFn ρ (w₂ x)) μG := by
  refine Integrable.of_bound
    (((measurable_charFn ρ hρcont).comp hw₁).mul
      ((measurable_charFn ρ hρcont).comp hw₂)).aestronglyMeasurable
    ((d : ℝ) * d) (Filter.Eventually.of_forall fun x => ?_)
  calc ‖charFn ρ (w₁ x) * charFn ρ (w₂ x)‖
      = ‖charFn ρ (w₁ x)‖ * ‖charFn ρ (w₂ x)‖ := norm_mul _ _
    _ ≤ (d : ℝ) * d :=
        mul_le_mul (norm_charFn_le ρ (w₁ x)) (norm_charFn_le ρ (w₂ x))
          (norm_nonneg _) (Nat.cast_nonneg d)

/-! ## §4. The owned pair twirls, in corner form

The four character sewings of two words in the shared corner
variable `x`, with all remaining data frozen into the words
`A`, `B`. The mixed sewings are PW-1
(`integral_charFn_mul_charFn_inv`, the mixed-pair sewing of
`QuadReMomentTelescope`); the same-orientation sewing is
PW-3 (`charFn_sewing`, the Frobenius–Schur evaluation of
`RepTensorTwirl`). -/

/-- **Mixed sewing, `(x·, x⁻¹·)`**: integrating two characters
whose corner letters have opposite orientations sews them
into one character of the product of the frozen words, at
the pair-twirl price `(d)⁻¹`. -/
theorem sew_mixed (hρcont : Continuous fun g => repMatrix ρ g)
    (hρirr : RepIrreducible ρ) (A B : G) :
    ∫ x, charFn ρ (x * A) * charFn ρ (x⁻¹ * B) ∂μG
      = (d : ℂ)⁻¹ * charFn ρ (A * B) := by
  have h := integral_charFn_mul_charFn_inv ρ μG hρcont hρirr 1 A 1 B
  simp only [one_mul, mul_one] at h
  exact h

/-- **Mixed sewing, `(x⁻¹·, x·)`**: the other mixed
orientation; the sewn word is the same product, by trace
cyclicity of the character. -/
theorem sew_mixed' (hρcont : Continuous fun g => repMatrix ρ g)
    (hρirr : RepIrreducible ρ) (A B : G) :
    ∫ x, charFn ρ (x⁻¹ * A) * charFn ρ (x * B) ∂μG
      = (d : ℂ)⁻¹ * charFn ρ (A * B) := by
  have hpt : (∫ x, charFn ρ (x⁻¹ * A) * charFn ρ (x * B) ∂μG)
      = ∫ x, charFn ρ (x * B) * charFn ρ (x⁻¹ * A) ∂μG :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => mul_comm _ _)
  rw [hpt, sew_mixed μG ρ hρcont hρirr B A, charFn_rotate ρ B A]

/-- **Same-orientation sewing, `(x·, x·)`** (the
Frobenius–Schur case): the contraction is the named
`J`-factor `jForm` of the two frozen words. -/
theorem sew_same (hd : 0 < d)
    (hρcont : Continuous fun g => repMatrix ρ g)
    (hρirr : RepIrreducible ρ) (A B : G) :
    ∫ x, charFn ρ (x * A) * charFn ρ (x * B) ∂μG
      = jForm μG ρ A B := by
  have h := charFn_sewing μG ρ hd hρirr hρcont 1 A 1 B
  simp only [one_mul, mul_one] at h
  rw [h]
  rfl

/-- **Same-orientation sewing, `(x⁻¹·, x⁻¹·)`**: equal to
the `(x·, x·)` sewing by the inversion substitution
(Haar invariance under `x ↦ x⁻¹`). -/
theorem sew_same_inv (hd : 0 < d)
    (hρcont : Continuous fun g => repMatrix ρ g)
    (hρirr : RepIrreducible ρ) (A B : G) :
    ∫ x, charFn ρ (x⁻¹ * A) * charFn ρ (x⁻¹ * B) ∂μG
      = jForm μG ρ A B := by
  have h := integral_inv_eq_self
    (fun x => charFn ρ (x * A) * charFn ρ (x * B)) μG
  rw [h]
  exact sew_same μG ρ hd hρcont hρirr A B

/-! ## §5. The single corner integrals vanish at `2 ≤ d`

One factor alone, integrated over the shared corner: every
matrix coefficient of an irreducible `ρ` with `2 ≤ d` has
mean zero (PW-1's one-factor twirl), so the character and
`reTrC` of any word in `x` integrate to zero. This is the
input that kills the constant×linear cross terms of the
order-1 approximant contraction. -/

/-- The character of an `a`-slot word integrates to zero. -/
theorem integral_charFn_mul_C (hρcont : Continuous fun g => repMatrix ρ g)
    (hρirr : RepIrreducible ρ) (hd : 2 ≤ d) (C : G) :
    ∫ x, charFn ρ (x * C) ∂μG = 0 := by
  obtain ⟨hMmul, hMone, hMinv, hMcont⟩ := repMatrix_isOrientationMat ρ hρcont
  have hpt : ∀ x : G, charFn ρ (x * C)
      = ∑ p, ∑ q, repMatrix ρ C q p * repMatrix ρ x p q := by
    intro x
    show Matrix.trace (repMatrix ρ (x * C)) = _
    rw [repMatrix_mul]
    show (∑ p, (repMatrix ρ x * repMatrix ρ C) p p) = _
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Matrix.mul_apply]
    exact Finset.sum_congr rfl fun q _ => mul_comm _ _
  have hInt : ∀ p q : Fin d,
      Integrable (fun x => repMatrix ρ C q p * repMatrix ρ x p q) μG :=
    fun p q => (matFn_integrable_entry μG (repMatrix ρ)
      hMmul hMone hMinv hMcont p q).const_mul _
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
    integral_finsetSum _ fun p _ =>
      MeasureTheory.integrable_finsetSum _ fun q _ => hInt p q]
  refine Finset.sum_eq_zero fun p _ => ?_
  rw [integral_finsetSum _ fun q _ => hInt p q]
  refine Finset.sum_eq_zero fun q _ => ?_
  rw [integral_const_mul,
    integral_repMatrix_entry_eq_zero μG ρ hρirr hd hρcont p q, mul_zero]

/-- The character of a `b`-slot word integrates to zero (by
the inversion substitution, from the `a`-slot case). -/
theorem integral_charFn_inv_mul_C
    (hρcont : Continuous fun g => repMatrix ρ g)
    (hρirr : RepIrreducible ρ) (hd : 2 ≤ d) (C : G) :
    ∫ x, charFn ρ (x⁻¹ * C) ∂μG = 0 := by
  have h := integral_inv_eq_self (fun x => charFn ρ (x * C)) μG
  rw [h]
  exact integral_charFn_mul_C μG ρ hρcont hρirr hd C

/-- `reTrC` of an `a`-slot word integrates to zero. -/
theorem integral_reTrC_mul_C (hρcont : Continuous fun g => repMatrix ρ g)
    (hρirr : RepIrreducible ρ) (hd : 2 ≤ d) (C : G) :
    ∫ x, reTrC ρ (x * C) ∂μG = 0 := by
  have hpt : ∀ x : G, reTrC ρ (x * C)
      = (charFn ρ (x * C) + charFn ρ (x⁻¹ * C⁻¹)) / 2 :=
    fun x => reTrC_expand_mul ρ x C
  have hI₁ : Integrable (fun x => charFn ρ (x * C)) μG :=
    integrable_charFn_comp μG ρ hρcont
      (w := fun x => x * C) (continuous_id.mul continuous_const).measurable
  have hI₂ : Integrable (fun x => charFn ρ (x⁻¹ * C⁻¹)) μG :=
    integrable_charFn_comp μG ρ hρcont
      (w := fun x => x⁻¹ * C⁻¹)
      (continuous_inv.mul continuous_const).measurable
  have hscale : (∫ x, (charFn ρ (x * C) + charFn ρ (x⁻¹ * C⁻¹)) / 2 ∂μG)
      = (2 : ℂ)⁻¹ * (∫ x, charFn ρ (x * C) + charFn ρ (x⁻¹ * C⁻¹) ∂μG) := by
    rw [← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), hscale,
    integral_add hI₁ hI₂,
    integral_charFn_mul_C μG ρ hρcont hρirr hd C,
    integral_charFn_inv_mul_C μG ρ hρcont hρirr hd C⁻¹,
    add_zero, mul_zero]

/-- `reTrC` of a `b`-slot word integrates to zero. -/
theorem integral_reTrC_inv_mul_C
    (hρcont : Continuous fun g => repMatrix ρ g)
    (hρirr : RepIrreducible ρ) (hd : 2 ≤ d) (C : G) :
    ∫ x, reTrC ρ (x⁻¹ * C) ∂μG = 0 := by
  have h := integral_inv_eq_self (fun x => reTrC ρ (x * C)) μG
  rw [h]
  exact integral_reTrC_mul_C μG ρ hρcont hρirr hd C

/-! ## §6. Integrability of `reTrC` and of its corner products -/

/-- `reTrC` of an `a`-slot word is integrable (it is the
average of two word characters). -/
theorem integrable_reTrC_mul_C
    (hρcont : Continuous fun g => repMatrix ρ g) (C : G) :
    Integrable (fun x => reTrC ρ (x * C)) μG := by
  have hI : Integrable
      (fun x => (charFn ρ (x * C) + charFn ρ (x⁻¹ * C⁻¹)) / 2) μG :=
    ((integrable_charFn_comp μG ρ hρcont
        (w := fun x => x * C) (continuous_id.mul continuous_const).measurable).add
      (integrable_charFn_comp μG ρ hρcont
        (w := fun x => x⁻¹ * C⁻¹)
        (continuous_inv.mul continuous_const).measurable)).div_const 2
  exact hI.congr (Filter.Eventually.of_forall fun x =>
    (reTrC_expand_mul ρ x C).symm)

/-- `reTrC` of a `b`-slot word is integrable. -/
theorem integrable_reTrC_inv_mul_C
    (hρcont : Continuous fun g => repMatrix ρ g) (C : G) :
    Integrable (fun x => reTrC ρ (x⁻¹ * C)) μG := by
  have hI : Integrable
      (fun x => (charFn ρ (x⁻¹ * C) + charFn ρ (x * C⁻¹)) / 2) μG :=
    ((integrable_charFn_comp μG ρ hρcont
        (w := fun x => x⁻¹ * C)
        (continuous_inv.mul continuous_const).measurable).add
      (integrable_charFn_comp μG ρ hρcont
        (w := fun x => x * C⁻¹)
        (continuous_id.mul continuous_const).measurable)).div_const 2
  exact hI.congr (Filter.Eventually.of_forall fun x =>
    (reTrC_expand_inv_mul ρ x C).symm)

/-! ## §7. The pair contractions (the two sub-deliverables)

The product of two `reTrC` corner factors expands, via §2,
into four character products. Each is contracted by §4's
sewings. The assembly is on conjugate pairs: in every
formula below the first and fourth terms are a conjugate
pair (frozen words inverted), and the two middle terms are
the other conjugate pair — at a non-self-dual label the
contraction exists only in this paired form. -/

/-- Pointwise expansion of the mixed-corner product. -/
theorem reTrC_mixed_mul_expand (x C₁ C₂ : G) :
    reTrC ρ (x⁻¹ * C₁) * reTrC ρ (x * C₂)
      = (1 / 4 : ℂ) * (charFn ρ (x⁻¹ * C₁) * charFn ρ (x * C₂)
        + charFn ρ (x⁻¹ * C₁) * charFn ρ (x⁻¹ * C₂⁻¹)
        + charFn ρ (x * C₁⁻¹) * charFn ρ (x * C₂)
        + charFn ρ (x * C₁⁻¹) * charFn ρ (x⁻¹ * C₂⁻¹)) := by
  rw [reTrC_expand_inv_mul ρ x C₁, reTrC_expand_mul ρ x C₂]
  ring

/-- Pointwise expansion of the source-corner product. -/
theorem reTrC_source_mul_expand (x C₁ C₂ : G) :
    reTrC ρ (x * C₁) * reTrC ρ (x * C₂)
      = (1 / 4 : ℂ) * (charFn ρ (x * C₁) * charFn ρ (x * C₂)
        + charFn ρ (x * C₁) * charFn ρ (x⁻¹ * C₂⁻¹)
        + charFn ρ (x⁻¹ * C₁⁻¹) * charFn ρ (x * C₂)
        + charFn ρ (x⁻¹ * C₁⁻¹) * charFn ρ (x⁻¹ * C₂⁻¹)) := by
  rw [reTrC_expand_mul ρ x C₁, reTrC_expand_mul ρ x C₂]
  ring

/-- Pointwise expansion of the sink-corner product. -/
theorem reTrC_sink_mul_expand (x C₁ C₂ : G) :
    reTrC ρ (x⁻¹ * C₁) * reTrC ρ (x⁻¹ * C₂)
      = (1 / 4 : ℂ) * (charFn ρ (x⁻¹ * C₁) * charFn ρ (x⁻¹ * C₂)
        + charFn ρ (x⁻¹ * C₁) * charFn ρ (x * C₂⁻¹)
        + charFn ρ (x * C₁⁻¹) * charFn ρ (x⁻¹ * C₂)
        + charFn ρ (x * C₁⁻¹) * charFn ρ (x * C₂⁻¹)) := by
  rw [reTrC_expand_inv_mul ρ x C₁, reTrC_expand_inv_mul ρ x C₂]
  ring

/-- **SUB-DELIVERABLE 1 — the mixed corner contraction.**
The Haar integral over the shared corner variable `x` of
the product of the `b`-slot factor's and the `a`-slot
factor's `Re tr` parts, at frozen words `C₁` (the `b`-slot
column's `frozenB`) and `C₂` (the `a`-slot column's
`frozenA`), is the named contracted expression: the
conjugate pair of mixed sewings
`(d)⁻¹ (χ(C₁C₂) + χ(C₁⁻¹C₂⁻¹))` plus the conjugate pair of
same-orientation `J`-factors at `(C₁, C₂⁻¹)` and
`(C₁⁻¹, C₂)`, all over `4`. It depends on the remaining
data only through the frozen words — no other edge data
survives the corner integral (K-A2 does not fire here). -/
theorem integral_reTrC_mixed (hd : 0 < d)
    (hρcont : Continuous fun g => repMatrix ρ g)
    (hρirr : RepIrreducible ρ) (C₁ C₂ : G) :
    ∫ x, reTrC ρ (x⁻¹ * C₁) * reTrC ρ (x * C₂) ∂μG
      = (1 / 4 : ℂ) * ((d : ℂ)⁻¹ * charFn ρ (C₁ * C₂)
        + jForm μG ρ C₁ C₂⁻¹ + jForm μG ρ C₁⁻¹ C₂
        + (d : ℂ)⁻¹ * charFn ρ (C₁⁻¹ * C₂⁻¹)) := by
  have hm₁ : Measurable (fun x : G => x⁻¹ * C₁) :=
    (continuous_inv.mul continuous_const).measurable
  have hm₂ : Measurable (fun x : G => x * C₂) :=
    (continuous_id.mul continuous_const).measurable
  have hm₃ : Measurable (fun x : G => x⁻¹ * C₂⁻¹) :=
    (continuous_inv.mul continuous_const).measurable
  have hm₄ : Measurable (fun x : G => x * C₁⁻¹) :=
    (continuous_id.mul continuous_const).measurable
  have hI₁ : Integrable (fun x => charFn ρ (x⁻¹ * C₁) * charFn ρ (x * C₂)) μG :=
    integrable_charFn_comp_mul μG ρ hρcont hm₁ hm₂
  have hI₂ : Integrable
      (fun x => charFn ρ (x⁻¹ * C₁) * charFn ρ (x⁻¹ * C₂⁻¹)) μG :=
    integrable_charFn_comp_mul μG ρ hρcont hm₁ hm₃
  have hI₃ : Integrable (fun x => charFn ρ (x * C₁⁻¹) * charFn ρ (x * C₂)) μG :=
    integrable_charFn_comp_mul μG ρ hρcont hm₄ hm₂
  have hI₄ : Integrable
      (fun x => charFn ρ (x * C₁⁻¹) * charFn ρ (x⁻¹ * C₂⁻¹)) μG :=
    integrable_charFn_comp_mul μG ρ hρcont hm₄ hm₃
  have sA : (∫ x, charFn ρ (x⁻¹ * C₁) * charFn ρ (x * C₂)
        + charFn ρ (x⁻¹ * C₁) * charFn ρ (x⁻¹ * C₂⁻¹)
        + charFn ρ (x * C₁⁻¹) * charFn ρ (x * C₂)
        + charFn ρ (x * C₁⁻¹) * charFn ρ (x⁻¹ * C₂⁻¹) ∂μG)
      = (∫ x, charFn ρ (x⁻¹ * C₁) * charFn ρ (x * C₂)
          + charFn ρ (x⁻¹ * C₁) * charFn ρ (x⁻¹ * C₂⁻¹)
          + charFn ρ (x * C₁⁻¹) * charFn ρ (x * C₂) ∂μG)
        + ∫ x, charFn ρ (x * C₁⁻¹) * charFn ρ (x⁻¹ * C₂⁻¹) ∂μG :=
    integral_add ((hI₁.add hI₂).add hI₃) hI₄
  have sB : (∫ x, charFn ρ (x⁻¹ * C₁) * charFn ρ (x * C₂)
        + charFn ρ (x⁻¹ * C₁) * charFn ρ (x⁻¹ * C₂⁻¹)
        + charFn ρ (x * C₁⁻¹) * charFn ρ (x * C₂) ∂μG)
      = (∫ x, charFn ρ (x⁻¹ * C₁) * charFn ρ (x * C₂)
          + charFn ρ (x⁻¹ * C₁) * charFn ρ (x⁻¹ * C₂⁻¹) ∂μG)
        + ∫ x, charFn ρ (x * C₁⁻¹) * charFn ρ (x * C₂) ∂μG :=
    integral_add (hI₁.add hI₂) hI₃
  have sC : (∫ x, charFn ρ (x⁻¹ * C₁) * charFn ρ (x * C₂)
        + charFn ρ (x⁻¹ * C₁) * charFn ρ (x⁻¹ * C₂⁻¹) ∂μG)
      = (∫ x, charFn ρ (x⁻¹ * C₁) * charFn ρ (x * C₂) ∂μG)
        + ∫ x, charFn ρ (x⁻¹ * C₁) * charFn ρ (x⁻¹ * C₂⁻¹) ∂μG :=
    integral_add hI₁ hI₂
  rw [integral_congr_ae (Filter.Eventually.of_forall fun x =>
      reTrC_mixed_mul_expand ρ x C₁ C₂), integral_const_mul,
    sA, sB, sC,
    sew_mixed' μG ρ hρcont hρirr C₁ C₂,
    sew_same_inv μG ρ hd hρcont hρirr C₁ C₂⁻¹,
    sew_same μG ρ hd hρcont hρirr C₁⁻¹ C₂,
    sew_mixed μG ρ hρcont hρirr C₁⁻¹ C₂⁻¹]

/-- **SUB-DELIVERABLE 2a — the source corner contraction.**
Both factors carry the shared variable in the `a`-slot
(corner `c₀₀`). The primary pairing is now the
same-orientation `J`-factor at `(C₁, C₂)`; the mixed
sewings pair the cross terms as
`(d)⁻¹ (χ(C₁C₂⁻¹) + χ(C₁⁻¹C₂))`, and the conjugate
`J`-factor at `(C₁⁻¹, C₂⁻¹)` closes the second pair. -/
theorem integral_reTrC_source (hd : 0 < d)
    (hρcont : Continuous fun g => repMatrix ρ g)
    (hρirr : RepIrreducible ρ) (C₁ C₂ : G) :
    ∫ x, reTrC ρ (x * C₁) * reTrC ρ (x * C₂) ∂μG
      = (1 / 4 : ℂ) * (jForm μG ρ C₁ C₂
        + (d : ℂ)⁻¹ * charFn ρ (C₁ * C₂⁻¹)
        + (d : ℂ)⁻¹ * charFn ρ (C₁⁻¹ * C₂)
        + jForm μG ρ C₁⁻¹ C₂⁻¹) := by
  have hm₁ : Measurable (fun x : G => x * C₁) :=
    (continuous_id.mul continuous_const).measurable
  have hm₂ : Measurable (fun x : G => x * C₂) :=
    (continuous_id.mul continuous_const).measurable
  have hm₃ : Measurable (fun x : G => x⁻¹ * C₂⁻¹) :=
    (continuous_inv.mul continuous_const).measurable
  have hm₄ : Measurable (fun x : G => x⁻¹ * C₁⁻¹) :=
    (continuous_inv.mul continuous_const).measurable
  have hI₁ : Integrable (fun x => charFn ρ (x * C₁) * charFn ρ (x * C₂)) μG :=
    integrable_charFn_comp_mul μG ρ hρcont hm₁ hm₂
  have hI₂ : Integrable
      (fun x => charFn ρ (x * C₁) * charFn ρ (x⁻¹ * C₂⁻¹)) μG :=
    integrable_charFn_comp_mul μG ρ hρcont hm₁ hm₃
  have hI₃ : Integrable
      (fun x => charFn ρ (x⁻¹ * C₁⁻¹) * charFn ρ (x * C₂)) μG :=
    integrable_charFn_comp_mul μG ρ hρcont hm₄ hm₂
  have hI₄ : Integrable
      (fun x => charFn ρ (x⁻¹ * C₁⁻¹) * charFn ρ (x⁻¹ * C₂⁻¹)) μG :=
    integrable_charFn_comp_mul μG ρ hρcont hm₄ hm₃
  have sA : (∫ x, charFn ρ (x * C₁) * charFn ρ (x * C₂)
        + charFn ρ (x * C₁) * charFn ρ (x⁻¹ * C₂⁻¹)
        + charFn ρ (x⁻¹ * C₁⁻¹) * charFn ρ (x * C₂)
        + charFn ρ (x⁻¹ * C₁⁻¹) * charFn ρ (x⁻¹ * C₂⁻¹) ∂μG)
      = (∫ x, charFn ρ (x * C₁) * charFn ρ (x * C₂)
          + charFn ρ (x * C₁) * charFn ρ (x⁻¹ * C₂⁻¹)
          + charFn ρ (x⁻¹ * C₁⁻¹) * charFn ρ (x * C₂) ∂μG)
        + ∫ x, charFn ρ (x⁻¹ * C₁⁻¹) * charFn ρ (x⁻¹ * C₂⁻¹) ∂μG :=
    integral_add ((hI₁.add hI₂).add hI₃) hI₄
  have sB : (∫ x, charFn ρ (x * C₁) * charFn ρ (x * C₂)
        + charFn ρ (x * C₁) * charFn ρ (x⁻¹ * C₂⁻¹)
        + charFn ρ (x⁻¹ * C₁⁻¹) * charFn ρ (x * C₂) ∂μG)
      = (∫ x, charFn ρ (x * C₁) * charFn ρ (x * C₂)
          + charFn ρ (x * C₁) * charFn ρ (x⁻¹ * C₂⁻¹) ∂μG)
        + ∫ x, charFn ρ (x⁻¹ * C₁⁻¹) * charFn ρ (x * C₂) ∂μG :=
    integral_add (hI₁.add hI₂) hI₃
  have sC : (∫ x, charFn ρ (x * C₁) * charFn ρ (x * C₂)
        + charFn ρ (x * C₁) * charFn ρ (x⁻¹ * C₂⁻¹) ∂μG)
      = (∫ x, charFn ρ (x * C₁) * charFn ρ (x * C₂) ∂μG)
        + ∫ x, charFn ρ (x * C₁) * charFn ρ (x⁻¹ * C₂⁻¹) ∂μG :=
    integral_add hI₁ hI₂
  rw [integral_congr_ae (Filter.Eventually.of_forall fun x =>
      reTrC_source_mul_expand ρ x C₁ C₂), integral_const_mul,
    sA, sB, sC,
    sew_same μG ρ hd hρcont hρirr C₁ C₂,
    sew_mixed μG ρ hρcont hρirr C₁ C₂⁻¹,
    sew_mixed' μG ρ hρcont hρirr C₁⁻¹ C₂,
    sew_same_inv μG ρ hd hρcont hρirr C₁⁻¹ C₂⁻¹]

/-- **SUB-DELIVERABLE 2b — the sink corner contraction.**
Both factors carry the shared variable in the `b`-slot
(corner `c₁₁`). By the inversion substitution the sink
contraction equals the source contraction at the same
frozen words, and its contracted expression is the same
named one. (Direct expansion confirms it: the
same-orientation terms of `reTrC_sink_mul_expand` are the
`J`-factors at `(C₁, C₂)` and `(C₁⁻¹, C₂⁻¹)` — the
`J`-contraction is invariant under simultaneous inversion
of the corner variable, since `jSew`'s two orientations
agree.) -/
theorem integral_reTrC_sink (hd : 0 < d)
    (hρcont : Continuous fun g => repMatrix ρ g)
    (hρirr : RepIrreducible ρ) (C₁ C₂ : G) :
    ∫ x, reTrC ρ (x⁻¹ * C₁) * reTrC ρ (x⁻¹ * C₂) ∂μG
      = (1 / 4 : ℂ) * (jForm μG ρ C₁ C₂
        + (d : ℂ)⁻¹ * charFn ρ (C₁ * C₂⁻¹)
        + (d : ℂ)⁻¹ * charFn ρ (C₁⁻¹ * C₂)
        + jForm μG ρ C₁⁻¹ C₂⁻¹) := by
  have h := integral_inv_eq_self
    (fun x => reTrC ρ (x * C₁) * reTrC ρ (x * C₂)) μG
  rw [h]
  exact integral_reTrC_source μG ρ hd hρcont hρirr C₁ C₂

/-- The mixed-corner product of `reTrC` factors is
integrable (its expansion is a sum of character products). -/
theorem integrable_reTrC_mixed_mul
    (hρcont : Continuous fun g => repMatrix ρ g) (C₁ C₂ : G) :
    Integrable (fun x => reTrC ρ (x⁻¹ * C₁) * reTrC ρ (x * C₂)) μG := by
  have hm₁ : Measurable (fun x : G => x⁻¹ * C₁) :=
    (continuous_inv.mul continuous_const).measurable
  have hm₂ : Measurable (fun x : G => x * C₂) :=
    (continuous_id.mul continuous_const).measurable
  have hm₃ : Measurable (fun x : G => x⁻¹ * C₂⁻¹) :=
    (continuous_inv.mul continuous_const).measurable
  have hm₄ : Measurable (fun x : G => x * C₁⁻¹) :=
    (continuous_id.mul continuous_const).measurable
  have hI : Integrable (fun x => (1 / 4 : ℂ)
      * (charFn ρ (x⁻¹ * C₁) * charFn ρ (x * C₂)
        + charFn ρ (x⁻¹ * C₁) * charFn ρ (x⁻¹ * C₂⁻¹)
        + charFn ρ (x * C₁⁻¹) * charFn ρ (x * C₂)
        + charFn ρ (x * C₁⁻¹) * charFn ρ (x⁻¹ * C₂⁻¹))) μG :=
    (((integrable_charFn_comp_mul μG ρ hρcont hm₁ hm₂).add
      (integrable_charFn_comp_mul μG ρ hρcont hm₁ hm₃)).add
      (integrable_charFn_comp_mul μG ρ hρcont hm₄ hm₂)).add
      (integrable_charFn_comp_mul μG ρ hρcont hm₄ hm₃) |>.const_mul _
  exact hI.congr (Filter.Eventually.of_forall fun x =>
    (reTrC_mixed_mul_expand ρ x C₁ C₂).symm)

/-- The source-corner product of `reTrC` factors is
integrable. -/
theorem integrable_reTrC_source_mul
    (hρcont : Continuous fun g => repMatrix ρ g) (C₁ C₂ : G) :
    Integrable (fun x => reTrC ρ (x * C₁) * reTrC ρ (x * C₂)) μG := by
  have hm₁ : Measurable (fun x : G => x * C₁) :=
    (continuous_id.mul continuous_const).measurable
  have hm₂ : Measurable (fun x : G => x * C₂) :=
    (continuous_id.mul continuous_const).measurable
  have hm₃ : Measurable (fun x : G => x⁻¹ * C₂⁻¹) :=
    (continuous_inv.mul continuous_const).measurable
  have hm₄ : Measurable (fun x : G => x⁻¹ * C₁⁻¹) :=
    (continuous_inv.mul continuous_const).measurable
  have hI : Integrable (fun x => (1 / 4 : ℂ)
      * (charFn ρ (x * C₁) * charFn ρ (x * C₂)
        + charFn ρ (x * C₁) * charFn ρ (x⁻¹ * C₂⁻¹)
        + charFn ρ (x⁻¹ * C₁⁻¹) * charFn ρ (x * C₂)
        + charFn ρ (x⁻¹ * C₁⁻¹) * charFn ρ (x⁻¹ * C₂⁻¹))) μG :=
    (((integrable_charFn_comp_mul μG ρ hρcont hm₁ hm₂).add
      (integrable_charFn_comp_mul μG ρ hρcont hm₁ hm₃)).add
      (integrable_charFn_comp_mul μG ρ hρcont hm₄ hm₂)).add
      (integrable_charFn_comp_mul μG ρ hρcont hm₄ hm₃) |>.const_mul _
  exact hI.congr (Filter.Eventually.of_forall fun x =>
    (reTrC_source_mul_expand ρ x C₁ C₂).symm)

/-- The sink-corner product of `reTrC` factors is
integrable. -/
theorem integrable_reTrC_sink_mul
    (hρcont : Continuous fun g => repMatrix ρ g) (C₁ C₂ : G) :
    Integrable (fun x => reTrC ρ (x⁻¹ * C₁) * reTrC ρ (x⁻¹ * C₂)) μG := by
  have hm₁ : Measurable (fun x : G => x⁻¹ * C₁) :=
    (continuous_inv.mul continuous_const).measurable
  have hm₂ : Measurable (fun x : G => x⁻¹ * C₂) :=
    (continuous_inv.mul continuous_const).measurable
  have hm₃ : Measurable (fun x : G => x * C₂⁻¹) :=
    (continuous_id.mul continuous_const).measurable
  have hm₄ : Measurable (fun x : G => x * C₁⁻¹) :=
    (continuous_id.mul continuous_const).measurable
  have hI : Integrable (fun x => (1 / 4 : ℂ)
      * (charFn ρ (x⁻¹ * C₁) * charFn ρ (x⁻¹ * C₂)
        + charFn ρ (x⁻¹ * C₁) * charFn ρ (x * C₂⁻¹)
        + charFn ρ (x * C₁⁻¹) * charFn ρ (x⁻¹ * C₂)
        + charFn ρ (x * C₁⁻¹) * charFn ρ (x * C₂⁻¹))) μG :=
    (((integrable_charFn_comp_mul μG ρ hρcont hm₁ hm₂).add
      (integrable_charFn_comp_mul μG ρ hρcont hm₁ hm₃)).add
      (integrable_charFn_comp_mul μG ρ hρcont hm₄ hm₂)).add
      (integrable_charFn_comp_mul μG ρ hρcont hm₄ hm₃) |>.const_mul _
  exact hI.congr (Filter.Eventually.of_forall fun x =>
    (reTrC_sink_mul_expand ρ x C₁ C₂).symm)

/-! ## §8. The approximant at orders `0` and `1` -/

/-- The order-`0` approximant is the constant `1`. -/
theorem colApprox_zero (β : ℝ) (a b u u' : G) :
    colApprox ρ β 0 a b u u' = 1 := by
  simp [colApprox]

/-- The order-`1` approximant is `1 − β · wordDensity`. -/
theorem colApprox_one (β : ℝ) (a b u u' : G) :
    colApprox ρ β 1 a b u u'
      = 1 - β * wordDensity ρ (a * u' * b⁻¹ * u⁻¹) := by
  unfold colApprox
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
  simp only [Nat.factorial_zero, Nat.factorial_one, Nat.cast_one,
    pow_zero, pow_one, div_one, mul_one, zero_add]
  ring

/-- The order-`1` approximant, affine in `Re tr ρ`:
`1 − β · wordDensity w = (1 − β) + (β/d) · Re tr ρ (w)`
(the field identity of A2-1's headline, at the approximant
level; no hypothesis on `d`). -/
theorem colApprox_one_affine (β : ℝ) (a b u u' : G) :
    colApprox ρ β 1 a b u u' = (1 - β) + (β / (d : ℝ))
      * (Matrix.trace (repMatrix ρ (a * u' * b⁻¹ * u⁻¹))).re := by
  rw [colApprox_one]
  unfold wordDensity
  ring

/-- The order-`1` approximant, cast to `ℂ`, affine in
`reTrC`. -/
theorem colApprox_one_cast (β : ℝ) (a b u u' : G) :
    ((colApprox ρ β 1 a b u u' : ℝ) : ℂ)
      = (1 - (β : ℂ)) + ((β : ℂ) / (d : ℂ))
        * reTrC ρ (a * u' * b⁻¹ * u⁻¹) := by
  rw [colApprox_one_affine]
  simp only [Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_one,
    Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_natCast, reTrC]

/-- At an `a`-slot column, `reTrC` of the column word is
`reTrC` of `x * frozenA` (associativity only). -/
theorem reTrC_aSlot (x b u u' : G) :
    reTrC ρ (x * u' * b⁻¹ * u⁻¹) = reTrC ρ (x * frozenA b u u') := by
  simp only [frozenA, mul_assoc]

/-- At a `b`-slot column, `reTrC` of the column word is
`reTrC` of `x⁻¹ * frozenB` (cyclic rotation of the word by
two letters — A2-2b's re-basing, at the `reTrC` level). -/
theorem reTrC_bSlot (x a u u' : G) :
    reTrC ρ (a * u' * x⁻¹ * u⁻¹) = reTrC ρ (x⁻¹ * frozenB a u u') := by
  calc reTrC ρ (a * u' * x⁻¹ * u⁻¹)
      = reTrC ρ ((a * u') * (x⁻¹ * u⁻¹)) := by simp only [mul_assoc]
    _ = reTrC ρ ((x⁻¹ * u⁻¹) * (a * u')) := reTrC_rotate ρ (a * u') (x⁻¹ * u⁻¹)
    _ = reTrC ρ (x⁻¹ * frozenB a u u') := by simp only [frozenB, mul_assoc]

/-! ## §9. The approximant contractions at order `(1, 1)`

The pack's deliverable, assembled: the Haar integral over
the shared corner variable of a product of two order-`1`
column-factor approximants. The constant×linear cross terms
vanish by §5 (this is where `2 ≤ d` enters); the
linear×linear term is §7's pair contraction at the frozen
words. The contracted expression depends on the remaining
data only through the two frozen words. -/

/-- **HEADLINE, mixed corner (sub-deliverable 1).** At a
mixed corner — first column carrying the shared variable
`x` in its `b`-slot (data `a₁, u₁, u₁'`), second in its
`a`-slot (data `b₂, u₂, u₂'`) — the integral over `x` of
the product of the two order-`1` approximants is
`(1 − β)² + (β/d)² ·` (the mixed pair contraction at the
frozen words `frozenB a₁ u₁ u₁'`, `frozenA b₂ u₂ u₂'`). -/
theorem integral_colApprox_one_mixed (hd2 : 2 ≤ d)
    (hρcont : Continuous fun g => repMatrix ρ g)
    (hρirr : RepIrreducible ρ) (β : ℝ)
    (a₁ u₁ u₁' b₂ u₂ u₂' : G) :
    ∫ x, ((colApprox ρ β 1 a₁ x u₁ u₁' : ℝ) : ℂ)
        * ((colApprox ρ β 1 x b₂ u₂ u₂' : ℝ) : ℂ) ∂μG
      = (1 - (β : ℂ)) ^ 2 + ((β : ℂ) / (d : ℂ)) ^ 2
        * ((1 / 4 : ℂ) * ((d : ℂ)⁻¹
            * charFn ρ (frozenB a₁ u₁ u₁' * frozenA b₂ u₂ u₂')
          + jForm μG ρ (frozenB a₁ u₁ u₁') (frozenA b₂ u₂ u₂')⁻¹
          + jForm μG ρ (frozenB a₁ u₁ u₁')⁻¹ (frozenA b₂ u₂ u₂')
          + (d : ℂ)⁻¹
            * charFn ρ ((frozenB a₁ u₁ u₁')⁻¹ * (frozenA b₂ u₂ u₂')⁻¹))) := by
  have hpt : ∀ x : G, ((colApprox ρ β 1 a₁ x u₁ u₁' : ℝ) : ℂ)
        * ((colApprox ρ β 1 x b₂ u₂ u₂' : ℝ) : ℂ)
      = (1 - (β : ℂ)) ^ 2
        + ((1 - (β : ℂ)) * ((β : ℂ) / (d : ℂ)))
          * (reTrC ρ (x⁻¹ * frozenB a₁ u₁ u₁')
            + reTrC ρ (x * frozenA b₂ u₂ u₂'))
        + (((β : ℂ) / (d : ℂ)) ^ 2)
          * (reTrC ρ (x⁻¹ * frozenB a₁ u₁ u₁')
            * reTrC ρ (x * frozenA b₂ u₂ u₂')) := by
    intro x
    rw [colApprox_one_cast ρ β a₁ x u₁ u₁',
      colApprox_one_cast ρ β x b₂ u₂ u₂',
      reTrC_bSlot ρ x a₁ u₁ u₁', reTrC_aSlot ρ x b₂ u₂ u₂']
    ring
  have hIc : Integrable (fun _ : G => (1 - (β : ℂ)) ^ 2) μG :=
    integrable_const _
  have hIcross : Integrable (fun x => ((1 - (β : ℂ)) * ((β : ℂ) / (d : ℂ)))
      * (reTrC ρ (x⁻¹ * frozenB a₁ u₁ u₁')
        + reTrC ρ (x * frozenA b₂ u₂ u₂'))) μG :=
    ((integrable_reTrC_inv_mul_C μG ρ hρcont _).add
      (integrable_reTrC_mul_C μG ρ hρcont _)).const_mul _
  have hIprod : Integrable (fun x => (((β : ℂ) / (d : ℂ)) ^ 2)
      * (reTrC ρ (x⁻¹ * frozenB a₁ u₁ u₁')
        * reTrC ρ (x * frozenA b₂ u₂ u₂'))) μG :=
    (integrable_reTrC_mixed_mul μG ρ hρcont _ _).const_mul _
  have sA : (∫ x, (1 - (β : ℂ)) ^ 2
        + ((1 - (β : ℂ)) * ((β : ℂ) / (d : ℂ)))
          * (reTrC ρ (x⁻¹ * frozenB a₁ u₁ u₁')
            + reTrC ρ (x * frozenA b₂ u₂ u₂'))
        + (((β : ℂ) / (d : ℂ)) ^ 2)
          * (reTrC ρ (x⁻¹ * frozenB a₁ u₁ u₁')
            * reTrC ρ (x * frozenA b₂ u₂ u₂')) ∂μG)
      = (∫ x, (1 - (β : ℂ)) ^ 2
          + ((1 - (β : ℂ)) * ((β : ℂ) / (d : ℂ)))
            * (reTrC ρ (x⁻¹ * frozenB a₁ u₁ u₁')
              + reTrC ρ (x * frozenA b₂ u₂ u₂')) ∂μG)
        + ∫ x, (((β : ℂ) / (d : ℂ)) ^ 2)
          * (reTrC ρ (x⁻¹ * frozenB a₁ u₁ u₁')
            * reTrC ρ (x * frozenA b₂ u₂ u₂')) ∂μG :=
    integral_add (hIc.add hIcross) hIprod
  have sB : (∫ x, (1 - (β : ℂ)) ^ 2
        + ((1 - (β : ℂ)) * ((β : ℂ) / (d : ℂ)))
          * (reTrC ρ (x⁻¹ * frozenB a₁ u₁ u₁')
            + reTrC ρ (x * frozenA b₂ u₂ u₂')) ∂μG)
      = (∫ _x : G, (1 - (β : ℂ)) ^ 2 ∂μG)
        + ∫ x, ((1 - (β : ℂ)) * ((β : ℂ) / (d : ℂ)))
          * (reTrC ρ (x⁻¹ * frozenB a₁ u₁ u₁')
            + reTrC ρ (x * frozenA b₂ u₂ u₂')) ∂μG :=
    integral_add hIc hIcross
  have hconst : (∫ _x : G, (1 - (β : ℂ)) ^ 2 ∂μG) = (1 - (β : ℂ)) ^ 2 := by
    simp
  have hcross0 : (∫ x, ((1 - (β : ℂ)) * ((β : ℂ) / (d : ℂ)))
        * (reTrC ρ (x⁻¹ * frozenB a₁ u₁ u₁')
          + reTrC ρ (x * frozenA b₂ u₂ u₂')) ∂μG) = 0 := by
    rw [integral_const_mul,
      integral_add (integrable_reTrC_inv_mul_C μG ρ hρcont _)
        (integrable_reTrC_mul_C μG ρ hρcont _),
      integral_reTrC_inv_mul_C μG ρ hρcont hρirr hd2 _,
      integral_reTrC_mul_C μG ρ hρcont hρirr hd2 _, add_zero, mul_zero]
  have hprod : (∫ x, (((β : ℂ) / (d : ℂ)) ^ 2)
        * (reTrC ρ (x⁻¹ * frozenB a₁ u₁ u₁')
          * reTrC ρ (x * frozenA b₂ u₂ u₂')) ∂μG)
      = ((β : ℂ) / (d : ℂ)) ^ 2
        * ((1 / 4 : ℂ) * ((d : ℂ)⁻¹
            * charFn ρ (frozenB a₁ u₁ u₁' * frozenA b₂ u₂ u₂')
          + jForm μG ρ (frozenB a₁ u₁ u₁') (frozenA b₂ u₂ u₂')⁻¹
          + jForm μG ρ (frozenB a₁ u₁ u₁')⁻¹ (frozenA b₂ u₂ u₂')
          + (d : ℂ)⁻¹
            * charFn ρ ((frozenB a₁ u₁ u₁')⁻¹ * (frozenA b₂ u₂ u₂')⁻¹))) := by
    rw [integral_const_mul,
      integral_reTrC_mixed μG ρ (by omega) hρcont hρirr _ _]
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), sA, sB,
    hconst, hcross0, hprod, add_zero]

/-- **HEADLINE, source corner (sub-deliverable 2).** At a
source corner — both columns carrying the shared variable
`x` in their `a`-slots (data `b₁, u₁, u₁'` and
`b₂, u₂, u₂'`) — the integral over `x` of the product of
the two order-`1` approximants is `(1 − β)² + (β/d)² ·`
(the source pair contraction at the frozen words
`frozenA b₁ u₁ u₁'`, `frozenA b₂ u₂ u₂'`). The primary
pairing is the same-orientation `J`-factor: this is where
§1.1's source/sink asymmetry lives, and it is carried by
the Frobenius–Schur twirl, separately from the mixed
corner. -/
theorem integral_colApprox_one_source (hd2 : 2 ≤ d)
    (hρcont : Continuous fun g => repMatrix ρ g)
    (hρirr : RepIrreducible ρ) (β : ℝ)
    (b₁ u₁ u₁' b₂ u₂ u₂' : G) :
    ∫ x, ((colApprox ρ β 1 x b₁ u₁ u₁' : ℝ) : ℂ)
        * ((colApprox ρ β 1 x b₂ u₂ u₂' : ℝ) : ℂ) ∂μG
      = (1 - (β : ℂ)) ^ 2 + ((β : ℂ) / (d : ℂ)) ^ 2
        * ((1 / 4 : ℂ) * (jForm μG ρ (frozenA b₁ u₁ u₁') (frozenA b₂ u₂ u₂')
          + (d : ℂ)⁻¹
            * charFn ρ (frozenA b₁ u₁ u₁' * (frozenA b₂ u₂ u₂')⁻¹)
          + (d : ℂ)⁻¹
            * charFn ρ ((frozenA b₁ u₁ u₁')⁻¹ * frozenA b₂ u₂ u₂')
          + jForm μG ρ (frozenA b₁ u₁ u₁')⁻¹ (frozenA b₂ u₂ u₂')⁻¹)) := by
  have hpt : ∀ x : G, ((colApprox ρ β 1 x b₁ u₁ u₁' : ℝ) : ℂ)
        * ((colApprox ρ β 1 x b₂ u₂ u₂' : ℝ) : ℂ)
      = (1 - (β : ℂ)) ^ 2
        + ((1 - (β : ℂ)) * ((β : ℂ) / (d : ℂ)))
          * (reTrC ρ (x * frozenA b₁ u₁ u₁')
            + reTrC ρ (x * frozenA b₂ u₂ u₂'))
        + (((β : ℂ) / (d : ℂ)) ^ 2)
          * (reTrC ρ (x * frozenA b₁ u₁ u₁')
            * reTrC ρ (x * frozenA b₂ u₂ u₂')) := by
    intro x
    rw [colApprox_one_cast ρ β x b₁ u₁ u₁',
      colApprox_one_cast ρ β x b₂ u₂ u₂',
      reTrC_aSlot ρ x b₁ u₁ u₁', reTrC_aSlot ρ x b₂ u₂ u₂']
    ring
  have hIc : Integrable (fun _ : G => (1 - (β : ℂ)) ^ 2) μG :=
    integrable_const _
  have hIcross : Integrable (fun x => ((1 - (β : ℂ)) * ((β : ℂ) / (d : ℂ)))
      * (reTrC ρ (x * frozenA b₁ u₁ u₁')
        + reTrC ρ (x * frozenA b₂ u₂ u₂'))) μG :=
    ((integrable_reTrC_mul_C μG ρ hρcont _).add
      (integrable_reTrC_mul_C μG ρ hρcont _)).const_mul _
  have hIprod : Integrable (fun x => (((β : ℂ) / (d : ℂ)) ^ 2)
      * (reTrC ρ (x * frozenA b₁ u₁ u₁')
        * reTrC ρ (x * frozenA b₂ u₂ u₂'))) μG :=
    (integrable_reTrC_source_mul μG ρ hρcont _ _).const_mul _
  have sA : (∫ x, (1 - (β : ℂ)) ^ 2
        + ((1 - (β : ℂ)) * ((β : ℂ) / (d : ℂ)))
          * (reTrC ρ (x * frozenA b₁ u₁ u₁')
            + reTrC ρ (x * frozenA b₂ u₂ u₂'))
        + (((β : ℂ) / (d : ℂ)) ^ 2)
          * (reTrC ρ (x * frozenA b₁ u₁ u₁')
            * reTrC ρ (x * frozenA b₂ u₂ u₂')) ∂μG)
      = (∫ x, (1 - (β : ℂ)) ^ 2
          + ((1 - (β : ℂ)) * ((β : ℂ) / (d : ℂ)))
            * (reTrC ρ (x * frozenA b₁ u₁ u₁')
              + reTrC ρ (x * frozenA b₂ u₂ u₂')) ∂μG)
        + ∫ x, (((β : ℂ) / (d : ℂ)) ^ 2)
          * (reTrC ρ (x * frozenA b₁ u₁ u₁')
            * reTrC ρ (x * frozenA b₂ u₂ u₂')) ∂μG :=
    integral_add (hIc.add hIcross) hIprod
  have sB : (∫ x, (1 - (β : ℂ)) ^ 2
        + ((1 - (β : ℂ)) * ((β : ℂ) / (d : ℂ)))
          * (reTrC ρ (x * frozenA b₁ u₁ u₁')
            + reTrC ρ (x * frozenA b₂ u₂ u₂')) ∂μG)
      = (∫ _x : G, (1 - (β : ℂ)) ^ 2 ∂μG)
        + ∫ x, ((1 - (β : ℂ)) * ((β : ℂ) / (d : ℂ)))
          * (reTrC ρ (x * frozenA b₁ u₁ u₁')
            + reTrC ρ (x * frozenA b₂ u₂ u₂')) ∂μG :=
    integral_add hIc hIcross
  have hconst : (∫ _x : G, (1 - (β : ℂ)) ^ 2 ∂μG) = (1 - (β : ℂ)) ^ 2 := by
    simp
  have hcross0 : (∫ x, ((1 - (β : ℂ)) * ((β : ℂ) / (d : ℂ)))
        * (reTrC ρ (x * frozenA b₁ u₁ u₁')
          + reTrC ρ (x * frozenA b₂ u₂ u₂')) ∂μG) = 0 := by
    rw [integral_const_mul,
      integral_add (integrable_reTrC_mul_C μG ρ hρcont _)
        (integrable_reTrC_mul_C μG ρ hρcont _),
      integral_reTrC_mul_C μG ρ hρcont hρirr hd2 _,
      integral_reTrC_mul_C μG ρ hρcont hρirr hd2 _, add_zero, mul_zero]
  have hprod : (∫ x, (((β : ℂ) / (d : ℂ)) ^ 2)
        * (reTrC ρ (x * frozenA b₁ u₁ u₁')
          * reTrC ρ (x * frozenA b₂ u₂ u₂')) ∂μG)
      = ((β : ℂ) / (d : ℂ)) ^ 2
        * ((1 / 4 : ℂ) * (jForm μG ρ (frozenA b₁ u₁ u₁') (frozenA b₂ u₂ u₂')
          + (d : ℂ)⁻¹
            * charFn ρ (frozenA b₁ u₁ u₁' * (frozenA b₂ u₂ u₂')⁻¹)
          + (d : ℂ)⁻¹
            * charFn ρ ((frozenA b₁ u₁ u₁')⁻¹ * frozenA b₂ u₂ u₂')
          + jForm μG ρ (frozenA b₁ u₁ u₁')⁻¹ (frozenA b₂ u₂ u₂')⁻¹)) := by
    rw [integral_const_mul,
      integral_reTrC_source μG ρ (by omega) hρcont hρirr _ _]
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), sA, sB,
    hconst, hcross0, hprod, add_zero]

/-- **HEADLINE, sink corner (sub-deliverable 2).** At a
sink corner — both columns carrying the shared variable
`x` in their `b`-slots (data `a₁, u₁, u₁'` and
`a₂, u₂, u₂'`) — the integral over `x` of the product of
the two order-`1` approximants is `(1 − β)² + (β/d)² ·`
(the sink pair contraction at the frozen words
`frozenB a₁ u₁ u₁'`, `frozenB a₂ u₂ u₂'`), whose contracted
expression is the source corner's expression at those
frozen words (inversion substitution). -/
theorem integral_colApprox_one_sink (hd2 : 2 ≤ d)
    (hρcont : Continuous fun g => repMatrix ρ g)
    (hρirr : RepIrreducible ρ) (β : ℝ)
    (a₁ u₁ u₁' a₂ u₂ u₂' : G) :
    ∫ x, ((colApprox ρ β 1 a₁ x u₁ u₁' : ℝ) : ℂ)
        * ((colApprox ρ β 1 a₂ x u₂ u₂' : ℝ) : ℂ) ∂μG
      = (1 - (β : ℂ)) ^ 2 + ((β : ℂ) / (d : ℂ)) ^ 2
        * ((1 / 4 : ℂ) * (jForm μG ρ (frozenB a₁ u₁ u₁') (frozenB a₂ u₂ u₂')
          + (d : ℂ)⁻¹
            * charFn ρ (frozenB a₁ u₁ u₁' * (frozenB a₂ u₂ u₂')⁻¹)
          + (d : ℂ)⁻¹
            * charFn ρ ((frozenB a₁ u₁ u₁')⁻¹ * frozenB a₂ u₂ u₂')
          + jForm μG ρ (frozenB a₁ u₁ u₁')⁻¹ (frozenB a₂ u₂ u₂')⁻¹)) := by
  have hpt : ∀ x : G, ((colApprox ρ β 1 a₁ x u₁ u₁' : ℝ) : ℂ)
        * ((colApprox ρ β 1 a₂ x u₂ u₂' : ℝ) : ℂ)
      = (1 - (β : ℂ)) ^ 2
        + ((1 - (β : ℂ)) * ((β : ℂ) / (d : ℂ)))
          * (reTrC ρ (x⁻¹ * frozenB a₁ u₁ u₁')
            + reTrC ρ (x⁻¹ * frozenB a₂ u₂ u₂'))
        + (((β : ℂ) / (d : ℂ)) ^ 2)
          * (reTrC ρ (x⁻¹ * frozenB a₁ u₁ u₁')
            * reTrC ρ (x⁻¹ * frozenB a₂ u₂ u₂')) := by
    intro x
    rw [colApprox_one_cast ρ β a₁ x u₁ u₁',
      colApprox_one_cast ρ β a₂ x u₂ u₂',
      reTrC_bSlot ρ x a₁ u₁ u₁', reTrC_bSlot ρ x a₂ u₂ u₂']
    ring
  have hIc : Integrable (fun _ : G => (1 - (β : ℂ)) ^ 2) μG :=
    integrable_const _
  have hIcross : Integrable (fun x => ((1 - (β : ℂ)) * ((β : ℂ) / (d : ℂ)))
      * (reTrC ρ (x⁻¹ * frozenB a₁ u₁ u₁')
        + reTrC ρ (x⁻¹ * frozenB a₂ u₂ u₂'))) μG :=
    ((integrable_reTrC_inv_mul_C μG ρ hρcont _).add
      (integrable_reTrC_inv_mul_C μG ρ hρcont _)).const_mul _
  have hIprod : Integrable (fun x => (((β : ℂ) / (d : ℂ)) ^ 2)
      * (reTrC ρ (x⁻¹ * frozenB a₁ u₁ u₁')
        * reTrC ρ (x⁻¹ * frozenB a₂ u₂ u₂'))) μG :=
    (integrable_reTrC_sink_mul μG ρ hρcont _ _).const_mul _
  have sA : (∫ x, (1 - (β : ℂ)) ^ 2
        + ((1 - (β : ℂ)) * ((β : ℂ) / (d : ℂ)))
          * (reTrC ρ (x⁻¹ * frozenB a₁ u₁ u₁')
            + reTrC ρ (x⁻¹ * frozenB a₂ u₂ u₂'))
        + (((β : ℂ) / (d : ℂ)) ^ 2)
          * (reTrC ρ (x⁻¹ * frozenB a₁ u₁ u₁')
            * reTrC ρ (x⁻¹ * frozenB a₂ u₂ u₂')) ∂μG)
      = (∫ x, (1 - (β : ℂ)) ^ 2
          + ((1 - (β : ℂ)) * ((β : ℂ) / (d : ℂ)))
            * (reTrC ρ (x⁻¹ * frozenB a₁ u₁ u₁')
              + reTrC ρ (x⁻¹ * frozenB a₂ u₂ u₂')) ∂μG)
        + ∫ x, (((β : ℂ) / (d : ℂ)) ^ 2)
          * (reTrC ρ (x⁻¹ * frozenB a₁ u₁ u₁')
            * reTrC ρ (x⁻¹ * frozenB a₂ u₂ u₂')) ∂μG :=
    integral_add (hIc.add hIcross) hIprod
  have sB : (∫ x, (1 - (β : ℂ)) ^ 2
        + ((1 - (β : ℂ)) * ((β : ℂ) / (d : ℂ)))
          * (reTrC ρ (x⁻¹ * frozenB a₁ u₁ u₁')
            + reTrC ρ (x⁻¹ * frozenB a₂ u₂ u₂')) ∂μG)
      = (∫ _x : G, (1 - (β : ℂ)) ^ 2 ∂μG)
        + ∫ x, ((1 - (β : ℂ)) * ((β : ℂ) / (d : ℂ)))
          * (reTrC ρ (x⁻¹ * frozenB a₁ u₁ u₁')
            + reTrC ρ (x⁻¹ * frozenB a₂ u₂ u₂')) ∂μG :=
    integral_add hIc hIcross
  have hconst : (∫ _x : G, (1 - (β : ℂ)) ^ 2 ∂μG) = (1 - (β : ℂ)) ^ 2 := by
    simp
  have hcross0 : (∫ x, ((1 - (β : ℂ)) * ((β : ℂ) / (d : ℂ)))
        * (reTrC ρ (x⁻¹ * frozenB a₁ u₁ u₁')
          + reTrC ρ (x⁻¹ * frozenB a₂ u₂ u₂')) ∂μG) = 0 := by
    rw [integral_const_mul,
      integral_add (integrable_reTrC_inv_mul_C μG ρ hρcont _)
        (integrable_reTrC_inv_mul_C μG ρ hρcont _),
      integral_reTrC_inv_mul_C μG ρ hρcont hρirr hd2 _,
      integral_reTrC_inv_mul_C μG ρ hρcont hρirr hd2 _, add_zero, mul_zero]
  have hprod : (∫ x, (((β : ℂ) / (d : ℂ)) ^ 2)
        * (reTrC ρ (x⁻¹ * frozenB a₁ u₁ u₁')
          * reTrC ρ (x⁻¹ * frozenB a₂ u₂ u₂')) ∂μG)
      = ((β : ℂ) / (d : ℂ)) ^ 2
        * ((1 / 4 : ℂ) * (jForm μG ρ (frozenB a₁ u₁ u₁') (frozenB a₂ u₂ u₂')
          + (d : ℂ)⁻¹
            * charFn ρ (frozenB a₁ u₁ u₁' * (frozenB a₂ u₂ u₂')⁻¹)
          + (d : ℂ)⁻¹
            * charFn ρ ((frozenB a₁ u₁ u₁')⁻¹ * frozenB a₂ u₂ u₂')
          + jForm μG ρ (frozenB a₁ u₁ u₁')⁻¹ (frozenB a₂ u₂ u₂')⁻¹)) := by
    rw [integral_const_mul,
      integral_reTrC_sink μG ρ (by omega) hρcont hρirr _ _]
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), sA, sB,
    hconst, hcross0, hprod, add_zero]

/-! ## §10. The total-degree-2 boundary: orders `(2, 0)` and `(0, 2)`

An order-`2` approximant against an order-`0` one (the
constant `1`, in either slot — the order-`0` factor is `1`
whatever its data) still closes with owned pair twirls:
its `(Re tr)²` term is a pair contraction of the frozen
word with itself. These are the last orders that close:
total degree `≥ 3` is the seam named in the header. -/

/-- The order-`2` approximant:
`1 − β · wordDensity + (β²/2) · wordDensity²`. -/
theorem colApprox_two (β : ℝ) (a b u u' : G) :
    colApprox ρ β 2 a b u u'
      = 1 - β * wordDensity ρ (a * u' * b⁻¹ * u⁻¹)
        + (β ^ 2 / 2) * (wordDensity ρ (a * u' * b⁻¹ * u⁻¹)) ^ 2 := by
  unfold colApprox
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_zero]
  simp only [Nat.factorial_zero, Nat.factorial_one, Nat.factorial_two,
    Nat.cast_one, Nat.cast_ofNat, pow_zero, pow_one, div_one, mul_one,
    zero_add]
  ring

/-- The order-`2` approximant, quadratic-affine in
`Re tr ρ`: constant `1 − β + β²/2`, linear coefficient
`(β − β²)/d`, quadratic coefficient `(β²/2)/d²`. -/
theorem colApprox_two_affine (β : ℝ) (a b u u' : G) :
    colApprox ρ β 2 a b u u' = (1 - β + β ^ 2 / 2)
      + ((β - β ^ 2) / (d : ℝ))
        * (Matrix.trace (repMatrix ρ (a * u' * b⁻¹ * u⁻¹))).re
      + ((β ^ 2 / 2) / (d : ℝ) ^ 2)
        * ((Matrix.trace (repMatrix ρ (a * u' * b⁻¹ * u⁻¹))).re) ^ 2 := by
  rw [colApprox_two]
  unfold wordDensity
  ring

/-- The order-`2` approximant, cast to `ℂ`, in `reTrC`. -/
theorem colApprox_two_cast (β : ℝ) (a b u u' : G) :
    ((colApprox ρ β 2 a b u u' : ℝ) : ℂ)
      = (1 - (β : ℂ) + (β : ℂ) ^ 2 / 2)
        + (((β : ℂ) - (β : ℂ) ^ 2) / (d : ℂ))
          * reTrC ρ (a * u' * b⁻¹ * u⁻¹)
        + (((β : ℂ) ^ 2 / 2) / (d : ℂ) ^ 2)
          * (reTrC ρ (a * u' * b⁻¹ * u⁻¹)) ^ 2 := by
  rw [colApprox_two_affine]
  simp only [Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_one,
    Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_pow,
    Complex.ofReal_natCast, Complex.ofReal_ofNat, reTrC]

/-- **HEADLINE, order `(2, 0)` at a `b`-slot factor.** The
integral over the shared corner `x` of an order-`2`
`b`-slot approximant times an order-`0` approximant (the
constant `1`, shown in the `a`-slot placement; any
placement is the same integral) is the constant
`1 − β + β²/2` plus the quadratic coefficient times the
self-pair contraction of the frozen word
`C₁ = frozenB a₁ u₁ u₁'` — the sink self-contraction
`(1/4) (J(C₁,C₁) + (d)⁻¹χ(C₁C₁⁻¹) + (d)⁻¹χ(C₁⁻¹C₁)
+ J(C₁⁻¹,C₁⁻¹))`. The linear term integrates to zero by
§5. -/
theorem integral_colApprox_two_bSlot (hd2 : 2 ≤ d)
    (hρcont : Continuous fun g => repMatrix ρ g)
    (hρirr : RepIrreducible ρ) (β : ℝ)
    (a₁ u₁ u₁' b₂ u₂ u₂' : G) :
    ∫ x, ((colApprox ρ β 2 a₁ x u₁ u₁' : ℝ) : ℂ)
        * ((colApprox ρ β 0 x b₂ u₂ u₂' : ℝ) : ℂ) ∂μG
      = (1 - (β : ℂ) + (β : ℂ) ^ 2 / 2)
        + (((β : ℂ) ^ 2 / 2) / (d : ℂ) ^ 2)
          * ((1 / 4 : ℂ) * (jForm μG ρ (frozenB a₁ u₁ u₁') (frozenB a₁ u₁ u₁')
            + (d : ℂ)⁻¹
              * charFn ρ (frozenB a₁ u₁ u₁' * (frozenB a₁ u₁ u₁')⁻¹)
            + (d : ℂ)⁻¹
              * charFn ρ ((frozenB a₁ u₁ u₁')⁻¹ * frozenB a₁ u₁ u₁')
            + jForm μG ρ (frozenB a₁ u₁ u₁')⁻¹ (frozenB a₁ u₁ u₁')⁻¹)) := by
  have hpt : ∀ x : G, ((colApprox ρ β 2 a₁ x u₁ u₁' : ℝ) : ℂ)
        * ((colApprox ρ β 0 x b₂ u₂ u₂' : ℝ) : ℂ)
      = (1 - (β : ℂ) + (β : ℂ) ^ 2 / 2)
        + (((β : ℂ) - (β : ℂ) ^ 2) / (d : ℂ))
          * reTrC ρ (x⁻¹ * frozenB a₁ u₁ u₁')
        + (((β : ℂ) ^ 2 / 2) / (d : ℂ) ^ 2)
          * (reTrC ρ (x⁻¹ * frozenB a₁ u₁ u₁')) ^ 2 := by
    intro x
    rw [colApprox_two_cast ρ β a₁ x u₁ u₁', colApprox_zero ρ β x b₂ u₂ u₂',
      reTrC_bSlot ρ x a₁ u₁ u₁']
    simp
  have hIc : Integrable
      (fun _ : G => (1 - (β : ℂ) + (β : ℂ) ^ 2 / 2)) μG := integrable_const _
  have hIlin : Integrable (fun x => (((β : ℂ) - (β : ℂ) ^ 2) / (d : ℂ))
      * reTrC ρ (x⁻¹ * frozenB a₁ u₁ u₁')) μG :=
    (integrable_reTrC_inv_mul_C μG ρ hρcont _).const_mul _
  have hIsq : Integrable (fun x => (((β : ℂ) ^ 2 / 2) / (d : ℂ) ^ 2)
      * (reTrC ρ (x⁻¹ * frozenB a₁ u₁ u₁')) ^ 2) μG := by
    have h := (integrable_reTrC_sink_mul μG ρ hρcont
      (frozenB a₁ u₁ u₁') (frozenB a₁ u₁ u₁')).const_mul
      (((β : ℂ) ^ 2 / 2) / (d : ℂ) ^ 2)
    refine h.congr (Filter.Eventually.of_forall fun x => ?_)
    ring
  have sA : (∫ x, (1 - (β : ℂ) + (β : ℂ) ^ 2 / 2)
        + (((β : ℂ) - (β : ℂ) ^ 2) / (d : ℂ))
          * reTrC ρ (x⁻¹ * frozenB a₁ u₁ u₁')
        + (((β : ℂ) ^ 2 / 2) / (d : ℂ) ^ 2)
          * (reTrC ρ (x⁻¹ * frozenB a₁ u₁ u₁')) ^ 2 ∂μG)
      = (∫ x, (1 - (β : ℂ) + (β : ℂ) ^ 2 / 2)
          + (((β : ℂ) - (β : ℂ) ^ 2) / (d : ℂ))
            * reTrC ρ (x⁻¹ * frozenB a₁ u₁ u₁') ∂μG)
        + ∫ x, (((β : ℂ) ^ 2 / 2) / (d : ℂ) ^ 2)
          * (reTrC ρ (x⁻¹ * frozenB a₁ u₁ u₁')) ^ 2 ∂μG :=
    integral_add (hIc.add hIlin) hIsq
  have sB : (∫ x, (1 - (β : ℂ) + (β : ℂ) ^ 2 / 2)
        + (((β : ℂ) - (β : ℂ) ^ 2) / (d : ℂ))
          * reTrC ρ (x⁻¹ * frozenB a₁ u₁ u₁') ∂μG)
      = (∫ _x : G, (1 - (β : ℂ) + (β : ℂ) ^ 2 / 2) ∂μG)
        + ∫ x, (((β : ℂ) - (β : ℂ) ^ 2) / (d : ℂ))
          * reTrC ρ (x⁻¹ * frozenB a₁ u₁ u₁') ∂μG :=
    integral_add hIc hIlin
  have hconst : (∫ _x : G, (1 - (β : ℂ) + (β : ℂ) ^ 2 / 2) ∂μG)
      = (1 - (β : ℂ) + (β : ℂ) ^ 2 / 2) := by simp
  have hlin0 : (∫ x, (((β : ℂ) - (β : ℂ) ^ 2) / (d : ℂ))
        * reTrC ρ (x⁻¹ * frozenB a₁ u₁ u₁') ∂μG) = 0 := by
    rw [integral_const_mul,
      integral_reTrC_inv_mul_C μG ρ hρcont hρirr hd2 _, mul_zero]
  have hsq : (∫ x, (((β : ℂ) ^ 2 / 2) / (d : ℂ) ^ 2)
        * (reTrC ρ (x⁻¹ * frozenB a₁ u₁ u₁')) ^ 2 ∂μG)
      = (((β : ℂ) ^ 2 / 2) / (d : ℂ) ^ 2)
        * ((1 / 4 : ℂ) * (jForm μG ρ (frozenB a₁ u₁ u₁') (frozenB a₁ u₁ u₁')
          + (d : ℂ)⁻¹
            * charFn ρ (frozenB a₁ u₁ u₁' * (frozenB a₁ u₁ u₁')⁻¹)
          + (d : ℂ)⁻¹
            * charFn ρ ((frozenB a₁ u₁ u₁')⁻¹ * frozenB a₁ u₁ u₁')
          + jForm μG ρ (frozenB a₁ u₁ u₁')⁻¹ (frozenB a₁ u₁ u₁')⁻¹)) := by
    have hcong : (∫ x, (((β : ℂ) ^ 2 / 2) / (d : ℂ) ^ 2)
          * (reTrC ρ (x⁻¹ * frozenB a₁ u₁ u₁')) ^ 2 ∂μG)
        = ∫ x, (((β : ℂ) ^ 2 / 2) / (d : ℂ) ^ 2)
          * (reTrC ρ (x⁻¹ * frozenB a₁ u₁ u₁')
            * reTrC ρ (x⁻¹ * frozenB a₁ u₁ u₁')) ∂μG :=
      integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
    rw [hcong, integral_const_mul,
      integral_reTrC_sink μG ρ (by omega) hρcont hρirr _ _]
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), sA, sB,
    hconst, hlin0, hsq, add_zero]

/-- **HEADLINE, order `(2, 0)` at an `a`-slot factor.**
The same boundary order with the order-`2` factor in the
`a`-slot (and the order-`0` factor in the `b`-slot
placement): the self-pair contraction is the source
self-contraction at `C₁ = frozenA b₁ u₁ u₁'`, of the same
named shape. Together with the `b`-slot headline this
covers orders `(2, 0)` and `(0, 2)` at every corner type:
the order-`0` factor is `1` in any slot, so only the
order-`2` factor's slot matters. -/
theorem integral_colApprox_two_aSlot (hd2 : 2 ≤ d)
    (hρcont : Continuous fun g => repMatrix ρ g)
    (hρirr : RepIrreducible ρ) (β : ℝ)
    (b₁ u₁ u₁' a₂ u₂ u₂' : G) :
    ∫ x, ((colApprox ρ β 2 x b₁ u₁ u₁' : ℝ) : ℂ)
        * ((colApprox ρ β 0 a₂ x u₂ u₂' : ℝ) : ℂ) ∂μG
      = (1 - (β : ℂ) + (β : ℂ) ^ 2 / 2)
        + (((β : ℂ) ^ 2 / 2) / (d : ℂ) ^ 2)
          * ((1 / 4 : ℂ) * (jForm μG ρ (frozenA b₁ u₁ u₁') (frozenA b₁ u₁ u₁')
            + (d : ℂ)⁻¹
              * charFn ρ (frozenA b₁ u₁ u₁' * (frozenA b₁ u₁ u₁')⁻¹)
            + (d : ℂ)⁻¹
              * charFn ρ ((frozenA b₁ u₁ u₁')⁻¹ * frozenA b₁ u₁ u₁')
            + jForm μG ρ (frozenA b₁ u₁ u₁')⁻¹ (frozenA b₁ u₁ u₁')⁻¹)) := by
  have hpt : ∀ x : G, ((colApprox ρ β 2 x b₁ u₁ u₁' : ℝ) : ℂ)
        * ((colApprox ρ β 0 a₂ x u₂ u₂' : ℝ) : ℂ)
      = (1 - (β : ℂ) + (β : ℂ) ^ 2 / 2)
        + (((β : ℂ) - (β : ℂ) ^ 2) / (d : ℂ))
          * reTrC ρ (x * frozenA b₁ u₁ u₁')
        + (((β : ℂ) ^ 2 / 2) / (d : ℂ) ^ 2)
          * (reTrC ρ (x * frozenA b₁ u₁ u₁')) ^ 2 := by
    intro x
    rw [colApprox_two_cast ρ β x b₁ u₁ u₁', colApprox_zero ρ β a₂ x u₂ u₂',
      reTrC_aSlot ρ x b₁ u₁ u₁']
    simp
  have hIc : Integrable
      (fun _ : G => (1 - (β : ℂ) + (β : ℂ) ^ 2 / 2)) μG := integrable_const _
  have hIlin : Integrable (fun x => (((β : ℂ) - (β : ℂ) ^ 2) / (d : ℂ))
      * reTrC ρ (x * frozenA b₁ u₁ u₁')) μG :=
    (integrable_reTrC_mul_C μG ρ hρcont _).const_mul _
  have hIsq : Integrable (fun x => (((β : ℂ) ^ 2 / 2) / (d : ℂ) ^ 2)
      * (reTrC ρ (x * frozenA b₁ u₁ u₁')) ^ 2) μG := by
    have h := (integrable_reTrC_source_mul μG ρ hρcont
      (frozenA b₁ u₁ u₁') (frozenA b₁ u₁ u₁')).const_mul
      (((β : ℂ) ^ 2 / 2) / (d : ℂ) ^ 2)
    refine h.congr (Filter.Eventually.of_forall fun x => ?_)
    ring
  have sA : (∫ x, (1 - (β : ℂ) + (β : ℂ) ^ 2 / 2)
        + (((β : ℂ) - (β : ℂ) ^ 2) / (d : ℂ))
          * reTrC ρ (x * frozenA b₁ u₁ u₁')
        + (((β : ℂ) ^ 2 / 2) / (d : ℂ) ^ 2)
          * (reTrC ρ (x * frozenA b₁ u₁ u₁')) ^ 2 ∂μG)
      = (∫ x, (1 - (β : ℂ) + (β : ℂ) ^ 2 / 2)
          + (((β : ℂ) - (β : ℂ) ^ 2) / (d : ℂ))
            * reTrC ρ (x * frozenA b₁ u₁ u₁') ∂μG)
        + ∫ x, (((β : ℂ) ^ 2 / 2) / (d : ℂ) ^ 2)
          * (reTrC ρ (x * frozenA b₁ u₁ u₁')) ^ 2 ∂μG :=
    integral_add (hIc.add hIlin) hIsq
  have sB : (∫ x, (1 - (β : ℂ) + (β : ℂ) ^ 2 / 2)
        + (((β : ℂ) - (β : ℂ) ^ 2) / (d : ℂ))
          * reTrC ρ (x * frozenA b₁ u₁ u₁') ∂μG)
      = (∫ _x : G, (1 - (β : ℂ) + (β : ℂ) ^ 2 / 2) ∂μG)
        + ∫ x, (((β : ℂ) - (β : ℂ) ^ 2) / (d : ℂ))
          * reTrC ρ (x * frozenA b₁ u₁ u₁') ∂μG :=
    integral_add hIc hIlin
  have hconst : (∫ _x : G, (1 - (β : ℂ) + (β : ℂ) ^ 2 / 2) ∂μG)
      = (1 - (β : ℂ) + (β : ℂ) ^ 2 / 2) := by simp
  have hlin0 : (∫ x, (((β : ℂ) - (β : ℂ) ^ 2) / (d : ℂ))
        * reTrC ρ (x * frozenA b₁ u₁ u₁') ∂μG) = 0 := by
    rw [integral_const_mul,
      integral_reTrC_mul_C μG ρ hρcont hρirr hd2 _, mul_zero]
  have hsq : (∫ x, (((β : ℂ) ^ 2 / 2) / (d : ℂ) ^ 2)
        * (reTrC ρ (x * frozenA b₁ u₁ u₁')) ^ 2 ∂μG)
      = (((β : ℂ) ^ 2 / 2) / (d : ℂ) ^ 2)
        * ((1 / 4 : ℂ) * (jForm μG ρ (frozenA b₁ u₁ u₁') (frozenA b₁ u₁ u₁')
          + (d : ℂ)⁻¹
            * charFn ρ (frozenA b₁ u₁ u₁' * (frozenA b₁ u₁ u₁')⁻¹)
          + (d : ℂ)⁻¹
            * charFn ρ ((frozenA b₁ u₁ u₁')⁻¹ * frozenA b₁ u₁ u₁')
          + jForm μG ρ (frozenA b₁ u₁ u₁')⁻¹ (frozenA b₁ u₁ u₁')⁻¹)) := by
    have hcong : (∫ x, (((β : ℂ) ^ 2 / 2) / (d : ℂ) ^ 2)
          * (reTrC ρ (x * frozenA b₁ u₁ u₁')) ^ 2 ∂μG)
        = ∫ x, (((β : ℂ) ^ 2 / 2) / (d : ℂ) ^ 2)
          * (reTrC ρ (x * frozenA b₁ u₁ u₁')
            * reTrC ρ (x * frozenA b₁ u₁ u₁')) ∂μG :=
      integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
    rw [hcong, integral_const_mul,
      integral_reTrC_source μG ρ (by omega) hρcont hρirr _ _]
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), sA, sB,
    hconst, hlin0, hsq, add_zero]

end Setup

end ThetLogos
