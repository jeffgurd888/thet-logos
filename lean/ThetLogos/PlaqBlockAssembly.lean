/-
# ThetLogos.PlaqBlockAssembly — Brick A2-2d: polynomial-stage
assembly of the plaquette block (Route B)

**Fences, up front.** NO CLAIM. Parts of the Clay Yang–Mills
statement closed by this module: **0**. Dials **0/4**, unmoved.
Route B scope on the face: one-plaquette mechanism + leading
square only — this brick is **NOT** `𝒜 ⪰ 0`, **NOT** clause
(a), and the block is not a factor of `layerKernel`. The
literal quotient form R1 is CERTIFIED DEAD (probe BR1-005)
and is not touched.

## What this brick is, and the verdict shape (read first)

A2-2d assembles A2-2c's one-corner contractions into the
block-level statements (T) and (P) of A2-2a
(`PlaquetteTelescoping`) with every column factor replaced
by its order-`K` polynomial approximant `colApprox`
(`PlaqBlockContraction`). The pack's deliverable was
uniform-in-`K` (all `K` simultaneously), because A2-2e's
limit consumes exactly that. **That uniform form is NOT
landed, and the reason is the pre-registered one:**
**SEAM A2-2c-HIGHER-ORDERS** — total degree `≥ 3` in the
corner factors needs triple-and-higher tensor twirls, which
the corpus does not own (they are TW-1's brick in the GD
line). A2-2c landed order `1` in each factor and the
total-degree-`2` boundary orders `(2,0)`/`(0,2)`; nothing
beyond that scope is asserted anywhere below, and every
headline states its order scope on its face. Per the pack's
pre-registered PARTIAL stop, this brick lands **PARTIAL**
with the leading-order (R4) statements as headlines,
recorded, not edited:

- **(T) at `K = 0`: FULL** (`plaqTelescopingApprox_zero`):
  the order-`0` block is the constant `1`, so it factors
  through the holonomy pair trivially.
- **Contracted form at `K = 1`** (the R4 headline,
  `plaqBlockApprox_one` / `plaqKernelApprox_one`): the
  order-`1` block is `(1 − β)⁴ + (β/d)⁴ · CycleIntegral`,
  where `CycleIntegral` is the four-corner integral of the
  product of the four `Re tr ρ` corner factors. Every
  lower-order corner contraction is composed here and
  vanishes or is constant: in the expansion of the product
  of the four affine factors, every monomial except the
  constant and the full four-factor monomial has a corner
  occurring in exactly one selected factor, and its corner
  integral is zero by A2-2c's §5 single-corner vanishing
  (this is where `2 ≤ d` and `RepIrreducible ρ` enter).
- **(P) at `K = 0`: FULL** (`plaqKernelPosApprox_zero`):
  PSD and separate class invariance of the constant kernel.
- **(P) at `K = 1`: class invariance FULL**
  (`plaqKernelApprox_one_class_left` / `_right`, from the
  contracted form and the cycle integral's own corner
  change of variables, mirroring A2-2b); **PSD at `K = 1`
  NOT landed** — see SEAM A2-2d-J-PATTERNS below.

## The hypothesis gap, carried explicitly (never assumed)

A2-2a's registered (T)/(P) carry **no** irreducibility
hypothesis and no `d` hypothesis. A2-2c's contraction
formulas carry `RepIrreducible ρ`, `0 < d`, `2 ≤ d`
(inherited from the PW-1/PW-3 twirl ledgers). The gap is
**carried, not closed**: every assembly headline below that
consumes a contraction states `RepIrreducible ρ`,
`2 ≤ d` (which gives `0 < d`), and the continuity
hypothesis `hρcont` on its face, and the stage propositions
`PlaqTelescopingApprox` / `PlaqKernelPosApprox` are new
entries in the sense of the house relabeling rule — they
are the registered propositions' approximant-stage forms,
not the registered propositions. Closing the gap (e.g. by
decomposing `ρ` into irreducibles at the block level) is
not attempted here and is not silently assumed.

Registered-(T)/(P) also carry `Even N` and `4 ≤ N` (for the
campaign's identification of the factors with
`layerAction`'s columns). The stage statements below are
about the corner-integral form itself and are datum-general
(no `Even N` / `4 ≤ N`) except where a section computation
needs corner distinctness, which is then stated on the
face. This is a scope difference, recorded here, not a
generalization of (T)/(P).

## The seams (all named, none edited away)

- **SEAM A2-2c-HIGHER-ORDERS** (inherited, binding):
  approximant orders with total degree `≥ 3` in a corner's
  two factors need triple-and-higher twirls — not owned.
  Hence no uniform-in-`K` statement is landed; `K ≥ 2`
  assembly is open. K-A2 remains armed at those orders.
- **SEAM A2-2d-J-PATTERNS**: at `K = 1`, `CycleIntegral`'s
  character expansion (each `Re tr ρ = (χ + χ⁻¹)/2`) has
  sixteen sign patterns. The two alternating patterns are
  the Gram/character diagonal (their contraction is a chain
  of owned mixed sewings plus the owned conjugation twirl);
  the fourteen non-alternating patterns pair some corner
  in the same orientation — the Frobenius–Schur / `J`
  pairings of A2-2c's `jForm`. Their closed cycle evaluation
  needs the `J`-invariance collapse (`C J Cᵀ = J` for word
  matrices `C`) at entry level around the whole cycle,
  which the corpus does not own as a cycle lemma. Until it
  is owned: the closed form of `CycleIntegral`, PSD of
  `Ψ₁` at `K = 1`, and (T) at `K = 1` (factorization of
  `CycleIntegral` through the holonomy pair) are all open
  at this seam, and K-A2 remains armed there — a
  non-alternating pattern carrying edge data beyond the
  holonomies would fire it.
- **A2-2b's deferrals, inherited**: (i) both-arguments
  inversion `Ψ x⁻¹ y⁻¹ = Ψ x y` — at the approximant stage
  it is landed here **conditionally**: modulo
  `PlaqTelescopingApprox 1` it is equivalent to the
  kernel-level datum rotation, and the block-level datum
  rotation lands unconditionally (below). Unconditionally
  it stays DEFERRED at SEAM A2-2d-J-PATTERNS /
  A2-2c-HIGHER-ORDERS, with the obstruction updated: at
  `K = 1` it is exactly the statement that the cycle
  integral is invariant under the simultaneous inversion,
  an integrated (character-level) identity, not a
  factorwise one — A2-2b's obstruction, one level down.
  (ii) Datum rotation: **block level FULL**
  (`plaqBlockApprox_transpose`, all `K`): transposing the
  datum (`μ ↔ ν`) leaves the approximant block unchanged
  and inverts the holonomy
  (`plaqHol_transpose`). Kernel level: conditional form
  only, as in (i).

## Conventions

Corners of `a : Fin 4 → G` are read as in `PlaqBlock`:
`a 0 = α₀₀`, `a 1 = α₁₀`, `a 2 = α₀₁`, `a 3 = α₁₁`. Edges
are indexed `e : Fin 4` as `0 =` bottom, `1 =` right,
`2 =` top, `3 =` left, with corner pairs `(0,1)`, `(1,3)`,
`(2,3)`, `(0,2)` — the assignment of `PlaqBlock`'s four
factors, in order.
-/

import ThetLogos.PlaqBlockContraction
import ThetLogos.PlaqBlockReductions

namespace ThetLogos

open Finset MeasureTheory

section EdgeIndexing

variable {N : ℕ} [NeZero N]

/-- The plaquette edge of index `e`: `0 =` bottom,
`1 =` right, `2 =` top, `3 =` left. -/
def plaqEdgeOf (P : PlaqDatum N) : Fin 4 → LayerLink N :=
  ![plaqEdgeB P, plaqEdgeR P, plaqEdgeT P, plaqEdgeL P]

/-- The first (`a`-slot) corner of edge `e`. -/
def plaqCornerA : Fin 4 → Fin 4 := ![0, 1, 2, 0]

/-- The second (`b`-slot) corner of edge `e`. -/
def plaqCornerB : Fin 4 → Fin 4 := ![1, 3, 3, 2]

/-- The corner pair of edge `e`, as a two-element finset. -/
def plaqEdgePair (e : Fin 4) : Finset (Fin 4) :=
  {plaqCornerA e, plaqCornerB e}

@[simp] theorem plaqEdgeOf_zero (P : PlaqDatum N) :
    plaqEdgeOf P 0 = plaqEdgeB P := rfl

@[simp] theorem plaqEdgeOf_one (P : PlaqDatum N) :
    plaqEdgeOf P 1 = plaqEdgeR P := rfl

@[simp] theorem plaqEdgeOf_two (P : PlaqDatum N) :
    plaqEdgeOf P 2 = plaqEdgeT P := rfl

@[simp] theorem plaqEdgeOf_three (P : PlaqDatum N) :
    plaqEdgeOf P 3 = plaqEdgeL P := rfl

end EdgeIndexing

section ApproxBlockDef

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ)) {N : ℕ} [NeZero N]

/-- **The column word of edge `e`** at corner tuple `a` and
edge data `(u, u')`: `a_A · u' ℓ · (a_B)⁻¹ · (u ℓ)⁻¹`, the
word whose `wordDensity` is the column's density (the word
form of `columnKernel` / `colApprox`). -/
def plaqWord (P : PlaqDatum N) (u u' : LayerLink N → G)
    (a : Fin 4 → G) (e : Fin 4) : G :=
  a (plaqCornerA e) * u' (plaqEdgeOf P e)
    * (a (plaqCornerB e))⁻¹ * (u (plaqEdgeOf P e))⁻¹

/-- **The order-`K` approximant integrand** of the
plaquette block: the product over the four edges of the
order-`K` column-factor approximants `colApprox`, cast to
`ℂ`. At the level of the integrand this is `PlaqBlock`'s
fourfold product with each `columnKernel` factor replaced
by its approximant. -/
noncomputable def plaqApproxIntegrand (P : PlaqDatum N) (K : ℕ)
    (β : ℝ) (u u' : LayerLink N → G) (a : Fin 4 → G) : ℂ :=
  ∏ e : Fin 4, ((colApprox ρ β K (a (plaqCornerA e))
      (a (plaqCornerB e)) (u (plaqEdgeOf P e))
      (u' (plaqEdgeOf P e)) : ℝ) : ℂ)

/-- **The order-`K` approximant block**: the corner
integral of the approximant integrand, against the product
Haar probability — `PlaqBlock` with every column factor
replaced by its order-`K` approximant. ℂ-valued (the
factors are real; the cast is the one (P)'s kernel language
consumes). -/
noncomputable def PlaqBlockApprox (P : PlaqDatum N) (K : ℕ)
    (β : ℝ) (u u' : LayerLink N → G) : ℂ :=
  ∫ a : Fin 4 → G, plaqApproxIntegrand ρ P K β u u' a
    ∂(Measure.pi fun _ : Fin 4 => μG)

/-- **The order-`K` approximant kernel** `Ψ_K`: the
approximant block on the section configurations — the
approximant-stage form of `PlaqKernel`. -/
noncomputable def PlaqKernelApprox (P : PlaqDatum N) (K : ℕ)
    (β : ℝ) (x y : G) : ℂ :=
  PlaqBlockApprox μG ρ P K β (plaqSection P x) (plaqSection P y)

/-- **(T) at the approximant stage** (new entry; see the
header's hypothesis-gap paragraph): the order-`K`
approximant block factors through the pair of plaquette
holonomies. -/
def PlaqTelescopingApprox (P : PlaqDatum N) (K : ℕ) (β : ℝ) :
    Prop :=
  ∀ u u' : LayerLink N → G,
    PlaqBlockApprox μG ρ P K β u u'
      = PlaqKernelApprox μG ρ P K β (PlaqHol P u) (PlaqHol P u')

/-- **(P) at the approximant stage** (new entry): the
order-`K` approximant kernel is a positive-semidefinite
kernel on `G` and separately a class function in each
argument. -/
def PlaqKernelPosApprox (P : PlaqDatum N) (K : ℕ) (β : ℝ) :
    Prop :=
  PosDefKernel (fun x y => PlaqKernelApprox μG ρ P K β x y) ∧
  (∀ g x y : G, PlaqKernelApprox μG ρ P K β (g * x * g⁻¹) y
      = PlaqKernelApprox μG ρ P K β x y) ∧
  (∀ g x y : G, PlaqKernelApprox μG ρ P K β x (g * y * g⁻¹)
      = PlaqKernelApprox μG ρ P K β x y)

/-! ## §2. Order `K = 0`: (T) and (P) in full

The order-`0` approximant is the constant `1`
(`colApprox_zero`), so the order-`0` block and kernel are
the constant `1`, and both stage propositions hold with no
analytic hypothesis at all — in particular no
irreducibility and no `d` hypothesis. This is the base case
of the (absent) uniform-in-`K` statement. -/

/-- The order-`0` approximant integrand is `1`. -/
theorem plaqApproxIntegrand_zero (P : PlaqDatum N) (β : ℝ)
    (u u' : LayerLink N → G) (a : Fin 4 → G) :
    plaqApproxIntegrand ρ P 0 β u u' a = 1 := by
  unfold plaqApproxIntegrand
  refine Finset.prod_eq_one fun e _ => ?_
  rw [colApprox_zero]
  simp

/-- The order-`0` approximant block is `1`. -/
theorem plaqBlockApprox_zero (P : PlaqDatum N) (β : ℝ)
    (u u' : LayerLink N → G) :
    PlaqBlockApprox μG ρ P 0 β u u' = 1 := by
  unfold PlaqBlockApprox
  rw [integral_congr_ae
    (Filter.Eventually.of_forall fun a =>
      plaqApproxIntegrand_zero ρ P β u u' a)]
  simp

/-- The order-`0` approximant kernel is `1`. -/
theorem plaqKernelApprox_zero (P : PlaqDatum N) (β : ℝ)
    (x y : G) :
    PlaqKernelApprox μG ρ P 0 β x y = 1 :=
  plaqBlockApprox_zero μG ρ P β _ _

/-- **(T) at `K = 0`, FULL.** The order-`0` approximant
block factors through the holonomy pair: both sides are
`1`. No hypothesis on `ρ` or `d`. -/
theorem plaqTelescopingApprox_zero (P : PlaqDatum N) (β : ℝ) :
    PlaqTelescopingApprox μG ρ P 0 β :=
  fun u u' => by
    rw [plaqBlockApprox_zero, plaqKernelApprox_zero]

/-- **(P) at `K = 0`, FULL.** The constant kernel `1` is
positive semidefinite — its quadratic form is
`‖∑ j, c j‖²` — and separately a class function (it is
constant). No hypothesis on `ρ`, `d`, or the sign of `β`. -/
theorem plaqKernelPosApprox_zero (P : PlaqDatum N) (β : ℝ) :
    PlaqKernelPosApprox μG ρ P 0 β := by
  refine ⟨?_, ?_, ?_⟩
  · intro n x c
    simp only [plaqKernelApprox_zero μG ρ P β, mul_one]
    rw [← Finset.sum_mul_sum, ← map_sum]
    have h : ((starRingEnd ℂ) (∑ j, c j) * (∑ j, c j)).re
        = Complex.normSq (∑ j, c j) := by
      rw [starRingEnd_apply, Complex.star_def, mul_comm, Complex.mul_conj]
      simp
    rw [h]
    exact Complex.normSq_nonneg _
  · intro g x y
    rw [plaqKernelApprox_zero, plaqKernelApprox_zero]
  · intro g x y
    rw [plaqKernelApprox_zero, plaqKernelApprox_zero]

end ApproxBlockDef

section CycleIntegral

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ)) {N : ℕ} [NeZero N]

/-- **The cycle integral**: the four-corner integral of the
product of the four `Re tr ρ` corner factors — the fully
contracted cycle that survives the order-`1` expansion
(§4 below). Its closed evaluation is SEAM
A2-2d-J-PATTERNS (see the header). -/
noncomputable def plaqCycleIntegral (P : PlaqDatum N)
    (u u' : LayerLink N → G) : ℂ :=
  ∫ a : Fin 4 → G, ∏ e : Fin 4, reTrC ρ (plaqWord P u u' a e)
    ∂(Measure.pi fun _ : Fin 4 => μG)

/-- `reTrC` of a plaquette word is measurable in the corner
tuple (the word is continuous in the tuple, and `charFn` is
measurable for a continuous representation). -/
theorem measurable_reTrC_plaqWord
    (hρcont : Continuous fun g => repMatrix ρ g) (P : PlaqDatum N)
    (u u' : LayerLink N → G) (e : Fin 4) :
    Measurable fun a : Fin 4 → G => reTrC ρ (plaqWord P u u' a e) := by
  have hw : Continuous fun a : Fin 4 → G => plaqWord P u u' a e := by
    unfold plaqWord
    exact (((continuous_apply (plaqCornerA e)).mul
      continuous_const).mul
      (continuous_apply (plaqCornerB e)).inv).mul continuous_const
  have h1 : Measurable fun a : Fin 4 → G =>
      charFn ρ (plaqWord P u u' a e) :=
    (measurable_charFn ρ hρcont).comp hw.measurable
  have h2 : Measurable fun a : Fin 4 → G =>
      charFn ρ (plaqWord P u u' a e)⁻¹ :=
    (measurable_charFn ρ hρcont).comp
      (hw.inv.measurable)
  have hfun : (fun a : Fin 4 → G => reTrC ρ (plaqWord P u u' a e))
      = fun a => (charFn ρ (plaqWord P u u' a e)
        + charFn ρ (plaqWord P u u' a e)⁻¹) / 2 :=
    funext fun a => reTrC_eq ρ _
  rw [hfun]
  exact (h1.add h2).div_const 2

/-- `‖reTrC ρ w‖ ≤ d`: `reTrC` is the real part of the
character, cast to `ℂ`. -/
theorem norm_reTrC_le (w : G) : ‖reTrC ρ w‖ ≤ (d : ℝ) := by
  unfold reTrC
  rw [Complex.norm_real]
  exact le_trans (Complex.abs_re_le_norm _) (norm_charFn_le ρ w)

/-- A corner monomial (product of `reTrC` plaquette words
over a finset of edges) is measurable in the tuple. -/
theorem measurable_monomial
    (hρcont : Continuous fun g => repMatrix ρ g) (P : PlaqDatum N)
    (u u' : LayerLink N → G) (t : Finset (Fin 4)) :
    Measurable fun a : Fin 4 → G =>
      ∏ e ∈ t, reTrC ρ (plaqWord P u u' a e) :=
  Finset.measurable_prod t fun e _ =>
    measurable_reTrC_plaqWord ρ hρcont P u u' e

/-- A corner monomial is bounded by `d ^ (card t)`. -/
theorem norm_monomial_le (P : PlaqDatum N)
    (u u' : LayerLink N → G) (t : Finset (Fin 4)) (a : Fin 4 → G) :
    ‖∏ e ∈ t, reTrC ρ (plaqWord P u u' a e)‖ ≤ (d : ℝ) ^ t.card := by
  calc ‖∏ e ∈ t, reTrC ρ (plaqWord P u u' a e)‖
      ≤ ∏ e ∈ t, ‖reTrC ρ (plaqWord P u u' a e)‖ := norm_prod_le _ _
    _ ≤ ∏ _e ∈ t, (d : ℝ) := by
        gcongr with e _
        exact norm_reTrC_le ρ _
    _ = (d : ℝ) ^ t.card := by rw [Finset.prod_const]

/-- A corner monomial is integrable against the product
Haar probability. -/
theorem integrable_monomial
    (hρcont : Continuous fun g => repMatrix ρ g) (P : PlaqDatum N)
    (u u' : LayerLink N → G) (t : Finset (Fin 4)) :
    Integrable (fun a : Fin 4 → G =>
      ∏ e ∈ t, reTrC ρ (plaqWord P u u' a e))
      (Measure.pi fun _ : Fin 4 => μG) :=
  Integrable.of_bound
    (measurable_monomial ρ hρcont P u u' t).aestronglyMeasurable
    ((d : ℝ) ^ t.card)
    (Filter.Eventually.of_forall fun a =>
      norm_monomial_le ρ P u u' t a)

/-! ## §3. The peel: one corner at a time (Fubini)

The four-corner integral is an iterated integral: peeling
corner `c` writes it as an outer integral over the remaining
three corners of the inner Haar integral over `c`
(`MeasurableEquiv.piFinSuccAbove`, measure-preserving, plus
Fubini on the product measure). -/

/-- The corner tuple with value `x` inserted at corner `c`
and the remaining corners read from `b : Fin 3 → G` (in
`Fin.succAbove c` order): `Fin.insertNth` with its family
pinned to the constant family `fun _ : Fin 4 => G`. -/
def cornerInsert (c : Fin 4) (x : G) (b : Fin 3 → G) :
    Fin 4 → G :=
  Fin.insertNth (α := fun _ : Fin 4 => G) c x b

/-- **Peel lemma.** For a bounded measurable integrand on
the corner space, the integral over `Fin 4 → G` equals the
iterated integral with corner `c` innermost, the remaining
corners assembled by `cornerInsert`. -/
theorem integral_pi_peel (c : Fin 4) {F : (Fin 4 → G) → ℂ}
    (hFm : Measurable F) (C : ℝ) (hFb : ∀ a, ‖F a‖ ≤ C) :
    ∫ a, F a ∂(Measure.pi fun _ : Fin 4 => μG)
      = ∫ b : Fin 3 → G, ∫ x : G, F (cornerInsert c x b)
          ∂μG ∂(Measure.pi fun _ : Fin 3 => μG) := by
  have hFi : Integrable F (Measure.pi fun _ : Fin 4 => μG) :=
    Integrable.of_bound hFm.aestronglyMeasurable C
      (Filter.Eventually.of_forall hFb)
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin 4 => G) c with he
  have hMP : MeasurePreserving e (Measure.pi fun _ : Fin 4 => μG)
      (μG.prod (Measure.pi fun _ : Fin 3 => μG)) :=
    measurePreserving_piFinSuccAbove (fun _ : Fin 4 => μG) c
  have hInt : Integrable (Function.uncurry fun x b =>
      F (cornerInsert c x b))
      (μG.prod (Measure.pi fun _ : Fin 3 => μG)) := by
    refine Integrable.of_bound ?_ C (Filter.Eventually.of_forall fun z => ?_)
    · have hm : Measurable fun z : G × (Fin 3 → G) =>
          cornerInsert c z.1 z.2 :=
        e.symm.measurable
      exact (hFm.comp hm).aestronglyMeasurable
    · exact hFb _
  calc ∫ a, F a ∂(Measure.pi fun _ : Fin 4 => μG)
      = ∫ z : G × (Fin 3 → G), F (cornerInsert c z.1 z.2)
          ∂(μG.prod (Measure.pi fun _ : Fin 3 => μG)) := by
        rw [← hMP.symm.integral_comp e.symm.measurableEmbedding]
        refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
        rfl
    _ = ∫ x : G, ∫ b : Fin 3 → G, F (cornerInsert c x b)
          ∂(Measure.pi fun _ : Fin 3 => μG) ∂μG :=
        (integral_integral hInt).symm
    _ = ∫ b : Fin 3 → G, ∫ x : G, F (cornerInsert c x b)
          ∂μG ∂(Measure.pi fun _ : Fin 3 => μG) :=
        integral_integral_swap hInt

/-- The inserted tuple's value at the peel corner is the
peeled value. -/
theorem cornerInsert_apply_same (c : Fin 4) (x : G) (b : Fin 3 → G) :
    cornerInsert c x b c = x :=
  Fin.insertNth_apply_same _ _ _

/-- At a corner other than the peel corner, the inserted
tuple's value does not depend on the peeled value. -/
theorem cornerInsert_apply_of_ne {c k : Fin 4} (hk : k ≠ c)
    (x x' : G) (b : Fin 3 → G) :
    cornerInsert c x b k = cornerInsert c x' b k := by
  obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq hk
  unfold cornerInsert
  rw [← hj, Fin.insertNth_apply_succAbove,
    Fin.insertNth_apply_succAbove]

/-- A plaquette word at an edge not containing the peel
corner does not depend on the peeled value. -/
theorem plaqWord_cornerInsert_of_ne (P : PlaqDatum N)
    (u u' : LayerLink N → G) {e : Fin 4} {c : Fin 4}
    (hA : plaqCornerA e ≠ c) (hB : plaqCornerB e ≠ c)
    (x x' : G) (b : Fin 3 → G) :
    plaqWord P u u' (cornerInsert c x b) e
      = plaqWord P u u' (cornerInsert c x' b) e := by
  unfold plaqWord
  rw [cornerInsert_apply_of_ne hA, cornerInsert_apply_of_ne hB]

/-- The two corners of an edge are distinct (finite check). -/
theorem plaqCornerA_ne_cornerB (e : Fin 4) :
    plaqCornerA e ≠ plaqCornerB e := by
  revert e
  decide

/-- **Combinatorial core of the vanishing**: every proper
nonempty set of edges has a corner occurring in exactly one
of its edges (finite check over the sixteen subsets). -/
theorem exists_unique_corner (t : Finset (Fin 4)) (ht0 : t.Nonempty)
    (ht1 : t ≠ Finset.univ) :
    ∃ c : Fin 4, ∃ e₀ ∈ t, (c = plaqCornerA e₀ ∨ c = plaqCornerB e₀) ∧
      ∀ e ∈ t, (c = plaqCornerA e ∨ c = plaqCornerB e) → e = e₀ := by
  revert t
  decide

/-! ## §4. The monomial vanishing and the contracted form

Every monomial of the order-`1` expansion except the
constant and the full cycle has a corner occurring in
exactly one selected factor; peeling that corner, the inner
integral is a single `reTrC` word integral, which vanishes
by A2-2c's §5 (this is where `RepIrreducible ρ` and `2 ≤ d`
enter the assembly). -/

/-- **Monomial vanishing.** The corner integral of a
product of `reTrC` plaquette words over a proper nonempty
set of edges is zero. -/
theorem integral_monomial_eq_zero
    (hρcont : Continuous fun g => repMatrix ρ g)
    (hρirr : RepIrreducible ρ) (hd2 : 2 ≤ d) (P : PlaqDatum N)
    (u u' : LayerLink N → G) {t : Finset (Fin 4)}
    (ht0 : t.Nonempty) (ht1 : t ≠ Finset.univ) :
    (∫ a : Fin 4 → G, ∏ e ∈ t, reTrC ρ (plaqWord P u u' a e)
      ∂(Measure.pi fun _ : Fin 4 => μG)) = 0 := by
  obtain ⟨c, e₀, he₀, hc, huniq⟩ :=
    exists_unique_corner t ht0 ht1
  have hcorner : ∀ e ∈ t, e ≠ e₀ →
      plaqCornerA e ≠ c ∧ plaqCornerB e ≠ c := by
    intro e heT he0
    constructor
    · intro hA
      exact he0 (huniq e heT (Or.inl hA.symm))
    · intro hB
      exact he0 (huniq e heT (Or.inr hB.symm))
  rw [integral_pi_peel μG c (measurable_monomial ρ hρcont P u u' t)
    ((d : ℝ) ^ t.card) (norm_monomial_le ρ P u u' t)]
  have hinner : ∀ b : Fin 3 → G, (∫ x : G,
      ∏ e ∈ t, reTrC ρ (plaqWord P u u' (cornerInsert c x b) e)
      ∂μG) = 0 := by
    intro b
    have hsplit : ∀ x : G, (∏ e ∈ t, reTrC ρ
          (plaqWord P u u' (cornerInsert c x b) e))
        = reTrC ρ (plaqWord P u u' (cornerInsert c x b) e₀)
          * ∏ e ∈ t.erase e₀, reTrC ρ
            (plaqWord P u u' (cornerInsert c 1 b) e) := by
      intro x
      rw [← Finset.mul_prod_erase _ _ he₀]
      congr 1
      refine Finset.prod_congr rfl fun e he => ?_
      rw [Finset.mem_erase] at he
      obtain ⟨he0, heT⟩ := he
      obtain ⟨hA, hB⟩ := hcorner e heT he0
      exact congrArg _ (plaqWord_cornerInsert_of_ne P u u' hA hB x 1 b)
    rw [integral_congr_ae (Filter.Eventually.of_forall hsplit)]
    rcases hc with hcA | hcB
    · -- `c` is the `a`-slot corner of `e₀`
      have hword : ∀ x : G, reTrC ρ
            (plaqWord P u u' (cornerInsert c x b) e₀)
          = reTrC ρ (x * (u' (plaqEdgeOf P e₀)
              * (cornerInsert c 1 b (plaqCornerB e₀))⁻¹
              * (u (plaqEdgeOf P e₀))⁻¹)) := by
        intro x
        have h1 : cornerInsert c x b (plaqCornerA e₀) = x := by
          rw [← hcA]; exact cornerInsert_apply_same _ _ _
        have h2 : cornerInsert c x b (plaqCornerB e₀)
            = cornerInsert c 1 b (plaqCornerB e₀) :=
          cornerInsert_apply_of_ne (fun h : plaqCornerB e₀ = c =>
            plaqCornerA_ne_cornerB e₀ (hcA.symm.trans h.symm)) x 1 b
        unfold plaqWord
        rw [h1, h2]
        simp only [mul_assoc]
      rw [integral_congr_ae (Filter.Eventually.of_forall fun x => by
        rw [hword x]), integral_mul_const,
        integral_reTrC_mul_C μG ρ hρcont hρirr hd2 _, zero_mul]
    · -- `c` is the `b`-slot corner of `e₀`
      have hword : ∀ x : G, reTrC ρ
            (plaqWord P u u' (cornerInsert c x b) e₀)
          = reTrC ρ (x⁻¹ * frozenB
              (cornerInsert c 1 b (plaqCornerA e₀))
              (u (plaqEdgeOf P e₀)) (u' (plaqEdgeOf P e₀))) := by
        intro x
        have h1 : cornerInsert c x b (plaqCornerB e₀) = x := by
          rw [← hcB]; exact cornerInsert_apply_same _ _ _
        have h2 : cornerInsert c x b (plaqCornerA e₀)
            = cornerInsert c 1 b (plaqCornerA e₀) :=
          cornerInsert_apply_of_ne (fun h : plaqCornerA e₀ = c =>
            plaqCornerA_ne_cornerB e₀ (h.trans hcB)) x 1 b
        have hform : plaqWord P u u' (cornerInsert c x b) e₀
            = cornerInsert c 1 b (plaqCornerA e₀)
              * u' (plaqEdgeOf P e₀) * x⁻¹
              * (u (plaqEdgeOf P e₀))⁻¹ := by
          unfold plaqWord
          rw [h1, h2]
        rw [hform]
        exact reTrC_bSlot ρ x _ _ _
      rw [integral_congr_ae (Filter.Eventually.of_forall fun x => by
        rw [hword x]), integral_mul_const,
        integral_reTrC_inv_mul_C μG ρ hρcont hρirr hd2 _, zero_mul]
  rw [integral_congr_ae (Filter.Eventually.of_forall hinner)]
  simp

/-! ## §5. The contracted form at `K = 1` (the R4 headline)

The order-`1` expansion of the block, with every lower-order
corner contraction composed: the subset expansion of the
product of the four affine factors has sixteen terms; the
constant term and the full cycle survive, and every other
term vanishes by §4. -/

/-- The order-`1` approximant integrand, expanded over the
sixteen subsets of edges. -/
theorem plaqApproxIntegrand_one (P : PlaqDatum N) (β : ℝ)
    (u u' : LayerLink N → G) (a : Fin 4 → G) :
    plaqApproxIntegrand ρ P 1 β u u' a
      = ∑ t ∈ (Finset.univ : Finset (Fin 4)).powerset,
        (((β : ℂ) / (d : ℂ)) ^ t.card * (1 - (β : ℂ)) ^ (4 - t.card))
          * ∏ e ∈ t, reTrC ρ (plaqWord P u u' a e) := by
  have h1 : ∀ e : Fin 4, ((colApprox ρ β 1 (a (plaqCornerA e))
        (a (plaqCornerB e)) (u (plaqEdgeOf P e))
        (u' (plaqEdgeOf P e)) : ℝ) : ℂ)
      = (1 - (β : ℂ)) + ((β : ℂ) / (d : ℂ))
          * reTrC ρ (plaqWord P u u' a e) :=
    fun e => colApprox_one_cast ρ β _ _ _ _
  calc plaqApproxIntegrand ρ P 1 β u u' a
      = ∏ e : Fin 4, ((1 - (β : ℂ)) + ((β : ℂ) / (d : ℂ))
          * reTrC ρ (plaqWord P u u' a e)) :=
        Finset.prod_congr rfl fun e _ => h1 e
    _ = ∏ e : Fin 4, (((β : ℂ) / (d : ℂ))
          * reTrC ρ (plaqWord P u u' a e) + (1 - (β : ℂ))) :=
        Finset.prod_congr rfl fun e _ => add_comm _ _
    _ = ∑ t ∈ (Finset.univ : Finset (Fin 4)).powerset,
          (∏ e ∈ t, ((β : ℂ) / (d : ℂ))
            * reTrC ρ (plaqWord P u u' a e))
          * ∏ e ∈ Finset.univ \ t, (1 - (β : ℂ)) :=
        Finset.prod_add _ _ _
    _ = ∑ t ∈ (Finset.univ : Finset (Fin 4)).powerset,
          (((β : ℂ) / (d : ℂ)) ^ t.card
            * (1 - (β : ℂ)) ^ (4 - t.card))
          * ∏ e ∈ t, reTrC ρ (plaqWord P u u' a e) := by
        refine Finset.sum_congr rfl fun t _ => ?_
        have hcard : (Finset.univ \ t).card = 4 - t.card := by
          rw [Finset.card_sdiff, Finset.inter_univ,
            Finset.card_univ, Fintype.card_fin]
        rw [Finset.prod_mul_distrib, Finset.prod_const,
          Finset.prod_const, hcard]
        ring

/-- **HEADLINE (d-i), contracted form of the order-`1`
block.** The order-`1` approximant block is
`(1 − β)⁴ + (β/d)⁴ · CycleIntegral`: every lower-order
corner contraction is composed and vanishes (§4); the
surviving nonconstant term is the full four-corner cycle.
Hypotheses on the face: `RepIrreducible ρ`, `2 ≤ d`,
continuity of `ρ` — the hypothesis gap of the header,
carried explicitly. Order scope: `K = 1` exactly. -/
theorem plaqBlockApprox_one
    (hρcont : Continuous fun g => repMatrix ρ g)
    (hρirr : RepIrreducible ρ) (hd2 : 2 ≤ d) (P : PlaqDatum N)
    (β : ℝ) (u u' : LayerLink N → G) :
    PlaqBlockApprox μG ρ P 1 β u u'
      = (1 - (β : ℂ)) ^ 4 + ((β : ℂ) / (d : ℂ)) ^ 4
        * plaqCycleIntegral μG ρ P u u' := by
  have hterm : ∀ t : Finset (Fin 4),
      (∫ a : Fin 4 → G, (((β : ℂ) / (d : ℂ)) ^ t.card
          * (1 - (β : ℂ)) ^ (4 - t.card))
          * ∏ e ∈ t, reTrC ρ (plaqWord P u u' a e)
        ∂(Measure.pi fun _ : Fin 4 => μG))
      = ((β : ℂ) / (d : ℂ)) ^ t.card * (1 - (β : ℂ)) ^ (4 - t.card)
        * ∫ a : Fin 4 → G, ∏ e ∈ t, reTrC ρ (plaqWord P u u' a e)
          ∂(Measure.pi fun _ : Fin 4 => μG) :=
    fun t => integral_const_mul _ _
  have hsum : PlaqBlockApprox μG ρ P 1 β u u'
      = ∑ t ∈ (Finset.univ : Finset (Fin 4)).powerset,
        ((β : ℂ) / (d : ℂ)) ^ t.card * (1 - (β : ℂ)) ^ (4 - t.card)
        * ∫ a : Fin 4 → G, ∏ e ∈ t, reTrC ρ (plaqWord P u u' a e)
          ∂(Measure.pi fun _ : Fin 4 => μG) := by
    unfold PlaqBlockApprox
    rw [integral_congr_ae (Filter.Eventually.of_forall fun a =>
      plaqApproxIntegrand_one ρ P β u u' a), integral_finsetSum]
    · exact Finset.sum_congr rfl fun t _ => hterm t
    · intro t _
      exact (integrable_monomial μG ρ hρcont P u u' t).const_mul _
  rw [hsum]
  have hF : ∀ t ∈ (Finset.univ : Finset (Fin 4)).powerset,
      ((β : ℂ) / (d : ℂ)) ^ t.card * (1 - (β : ℂ)) ^ (4 - t.card)
        * ∫ a : Fin 4 → G, ∏ e ∈ t, reTrC ρ (plaqWord P u u' a e)
          ∂(Measure.pi fun _ : Fin 4 => μG)
      = if t = Finset.univ then ((β : ℂ) / (d : ℂ)) ^ 4
          * plaqCycleIntegral μG ρ P u u'
        else if t = ∅ then (1 - (β : ℂ)) ^ 4 else 0 := by
    intro t ht
    rw [Finset.mem_powerset] at ht
    by_cases huniv : t = Finset.univ
    · rw [if_pos huniv, huniv]
      simp [plaqCycleIntegral]
    · rw [if_neg huniv]
      by_cases hempty : t = ∅
      · rw [if_pos hempty, hempty]
        simp
      · rw [if_neg hempty]
        have hne : t.Nonempty :=
          Finset.nonempty_iff_ne_empty.mpr hempty
        rw [integral_monomial_eq_zero μG ρ hρcont hρirr hd2 P u u' hne
          huniv, mul_zero]
  rw [Finset.sum_congr rfl hF]
  have huniv : (Finset.univ : Finset (Fin 4))
      ∈ (Finset.univ : Finset (Fin 4)).powerset :=
    Finset.mem_powerset.mpr (Finset.subset_univ _)
  rw [← Finset.add_sum_erase _ _ huniv, if_pos rfl]
  have hempty : (∅ : Finset (Fin 4))
      ∈ (Finset.univ : Finset (Fin 4)).powerset.erase Finset.univ :=
    Finset.mem_erase.mpr ⟨by decide,
      Finset.mem_powerset.mpr (Finset.empty_subset _)⟩
  rw [← Finset.add_sum_erase _ _ hempty,
    if_neg (by decide : (∅ : Finset (Fin 4)) ≠ Finset.univ),
    if_pos rfl]
  have hrest : ∑ t ∈ ((Finset.univ : Finset (Fin 4)).powerset.erase
        Finset.univ).erase ∅,
      (if t = Finset.univ then ((β : ℂ) / (d : ℂ)) ^ 4
          * plaqCycleIntegral μG ρ P u u'
        else if t = ∅ then (1 - (β : ℂ)) ^ 4 else 0) = 0 := by
    refine Finset.sum_eq_zero fun t ht => ?_
    rw [Finset.mem_erase, Finset.mem_erase] at ht
    obtain ⟨ht0, ht1, -⟩ := ht
    rw [if_neg ht1, if_neg ht0]
  rw [hrest]
  ring

/-- **HEADLINE (d-i), contracted form of `Ψ₁`.** The
order-`1` approximant kernel in contracted form: the
section evaluation of `plaqBlockApprox_one`. -/
theorem plaqKernelApprox_one
    (hρcont : Continuous fun g => repMatrix ρ g)
    (hρirr : RepIrreducible ρ) (hd2 : 2 ≤ d) (P : PlaqDatum N)
    (β : ℝ) (x y : G) :
    PlaqKernelApprox μG ρ P 1 β x y
      = (1 - (β : ℂ)) ^ 4 + ((β : ℂ) / (d : ℂ)) ^ 4
        * plaqCycleIntegral μG ρ P (plaqSection P x)
          (plaqSection P y) :=
  plaqBlockApprox_one μG ρ hρcont hρirr hd2 P β _ _

end CycleIntegral

section StageSymmetries

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ)) {N : ℕ} [NeZero N]

/-! ## §6. Class invariance of `Ψ₁` (d-ii, first item)

The contracted form of §5 reduces class invariance of the
order-`1` kernel to conjugation invariance of the cycle
integral, which is a corner change of variables exactly as
in A2-2b: at left-translated corners with conjugated
`u`-data, each cycle word is the conjugate of the original
word, and `reTrC` is conjugation-invariant. -/

/-- `reTrC` is invariant under conjugation of its argument
(character cyclicity, both orientations). -/
theorem reTrC_conj (g w : G) : reTrC ρ (g * w * g⁻¹) = reTrC ρ w := by
  rw [reTrC_eq, reTrC_eq]
  have h1 : charFn ρ (g * w * g⁻¹) = charFn ρ w :=
    trace_repMatrix_conj ρ g w
  have h2 : charFn ρ (g * w * g⁻¹)⁻¹ = charFn ρ w⁻¹ := by
    have e : (g * w * g⁻¹)⁻¹ = g * w⁻¹ * g⁻¹ := by group
    rw [e]
    exact trace_repMatrix_conj ρ g w⁻¹
  rw [h1, h2]

/-- The cycle word at left-translated corners, with the
`u`-data conjugated, is the conjugate of the original
cycle word. -/
theorem plaqWord_leftMul_conj (P : PlaqDatum N) (g : G)
    (u u' : LayerLink N → G) (a : Fin 4 → G) (e : Fin 4) :
    plaqWord P (fun ℓ => g * u ℓ * g⁻¹) u' (cornerLeftMulEquiv g a) e
      = g * plaqWord P u u' a e * g⁻¹ := by
  unfold plaqWord
  rw [cornerLeftMulEquiv_apply, cornerLeftMulEquiv_apply]
  dsimp only
  group

/-- The cycle word at right-translated corners, with the
`u'`-data conjugated by `h⁻¹`, is the original cycle word
on the nose. -/
theorem plaqWord_rightMul_conj (P : PlaqDatum N) (h : G)
    (u u' : LayerLink N → G) (a : Fin 4 → G) (e : Fin 4) :
    plaqWord P u (fun ℓ => h⁻¹ * u' ℓ * h)
        (cornerRightMulEquiv h a) e
      = plaqWord P u u' a e := by
  unfold plaqWord
  rw [cornerRightMulEquiv_apply, cornerRightMulEquiv_apply]
  dsimp only
  group

/-- The cycle integral is invariant under conjugation of
the `u`-data (corner left translation). -/
theorem plaqCycleIntegral_conj_u (P : PlaqDatum N) (g : G)
    (u u' : LayerLink N → G) :
    plaqCycleIntegral μG ρ P (fun ℓ => g * u ℓ * g⁻¹) u'
      = plaqCycleIntegral μG ρ P u u' := by
  unfold plaqCycleIntegral
  rw [← (measurePreserving_cornerLeftMulEquiv μG g).integral_comp
    (cornerLeftMulEquiv g).measurableEmbedding
    (fun a => ∏ e : Fin 4, reTrC ρ
      (plaqWord P (fun ℓ => g * u ℓ * g⁻¹) u' a e))]
  refine integral_congr_ae (ae_of_all _ fun a => ?_)
  refine Finset.prod_congr rfl fun e _ => ?_
  rw [plaqWord_leftMul_conj, reTrC_conj]

/-- The cycle integral is invariant under conjugation of
the `u'`-data (corner right translation). -/
theorem plaqCycleIntegral_conj_u' (P : PlaqDatum N) (g : G)
    (u u' : LayerLink N → G) :
    plaqCycleIntegral μG ρ P u (fun ℓ => g * u' ℓ * g⁻¹)
      = plaqCycleIntegral μG ρ P u u' := by
  have hform : (fun ℓ => g * u' ℓ * g⁻¹)
      = (fun ℓ => (g⁻¹)⁻¹ * u' ℓ * g⁻¹) := by
    funext ℓ
    simp
  rw [hform]
  unfold plaqCycleIntegral
  rw [← (measurePreserving_cornerRightMulEquiv μG g⁻¹).integral_comp
    (cornerRightMulEquiv g⁻¹).measurableEmbedding
    (fun a => ∏ e : Fin 4, reTrC ρ
      (plaqWord P u (fun ℓ => (g⁻¹)⁻¹ * u' ℓ * g⁻¹) a e))]
  refine integral_congr_ae (ae_of_all _ fun a => ?_)
  refine Finset.prod_congr rfl fun e _ => ?_
  rw [plaqWord_rightMul_conj]

/-- **Separate class invariance of `Ψ₁`, first argument**
(d-ii): conjugation invariance transported through the
contracted form of §5. -/
theorem plaqKernelApprox_one_class_left
    (hρcont : Continuous fun g => repMatrix ρ g)
    (hρirr : RepIrreducible ρ) (hd2 : 2 ≤ d) (P : PlaqDatum N)
    (β : ℝ) (g x y : G) :
    PlaqKernelApprox μG ρ P 1 β (g * x * g⁻¹) y
      = PlaqKernelApprox μG ρ P 1 β x y := by
  rw [plaqKernelApprox_one μG ρ hρcont hρirr hd2 P β (g * x * g⁻¹) y,
    plaqKernelApprox_one μG ρ hρcont hρirr hd2 P β x y,
    plaqSection_map_conj, plaqCycleIntegral_conj_u]

/-- **Separate class invariance of `Ψ₁`, second argument**
(d-ii). -/
theorem plaqKernelApprox_one_class_right
    (hρcont : Continuous fun g => repMatrix ρ g)
    (hρirr : RepIrreducible ρ) (hd2 : 2 ≤ d) (P : PlaqDatum N)
    (β : ℝ) (g x y : G) :
    PlaqKernelApprox μG ρ P 1 β x (g * y * g⁻¹)
      = PlaqKernelApprox μG ρ P 1 β x y := by
  rw [plaqKernelApprox_one μG ρ hρcont hρirr hd2 P β x (g * y * g⁻¹),
    plaqKernelApprox_one μG ρ hρcont hρirr hd2 P β x y,
    plaqSection_map_conj, plaqCycleIntegral_conj_u']

/-- **Separate class invariance of `Ψ₁`, bundled** in the
shape of the class conjuncts of the stage proposition
`PlaqKernelPosApprox` at `K = 1`. -/
theorem plaqKernelApprox_one_separately_classFn
    (hρcont : Continuous fun g => repMatrix ρ g)
    (hρirr : RepIrreducible ρ) (hd2 : 2 ≤ d) (P : PlaqDatum N)
    (β : ℝ) :
    (∀ g x y : G, PlaqKernelApprox μG ρ P 1 β (g * x * g⁻¹) y
      = PlaqKernelApprox μG ρ P 1 β x y)
    ∧ (∀ g x y : G, PlaqKernelApprox μG ρ P 1 β x (g * y * g⁻¹)
      = PlaqKernelApprox μG ρ P 1 β x y) :=
  ⟨fun g x y => plaqKernelApprox_one_class_left μG ρ hρcont hρirr
      hd2 P β g x y,
   fun g x y => plaqKernelApprox_one_class_right μG ρ hρcont hρirr
      hd2 P β g x y⟩

end StageSymmetries

section DatumRotation

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ)) {N : ℕ} [NeZero N]

/-! ## §7. The datum-rotation deferral (A2-2b, item (ii))

The transposed datum `Pᵀ` exchanges the two spatial
directions. At block level the rotation is an identity at
every order `K`: the corner swap `1 ↔ 2` relabels the
four factors. The holonomy inverts. At kernel level the
sections are datum-dependent, so the rotated kernel reads
the original kernel at the inverted arguments,
CONDITIONALLY on the stage telescoping identity
`PlaqTelescopingApprox 1` at `P` (with the standing
`Even N`, `4 ≤ N` edge-distinctness hypotheses). This is
also the precise progress on A2-2b's deferral (i)
(both-arguments inversion): at `K = 1` inversion is
exactly this rotation identity; unconditionally it stays
open (see the header). -/

/-- The transpose datum: the two spatial directions
exchanged. -/
def plaqDatumTranspose (P : PlaqDatum N) : PlaqDatum N :=
  ⟨P.base, P.nu, P.mu, P.hnu, P.hmu, Ne.symm P.hne⟩

theorem plaqEdgeB_transpose (P : PlaqDatum N) :
    plaqEdgeB (plaqDatumTranspose P) = plaqEdgeL P := rfl

theorem plaqEdgeR_transpose (P : PlaqDatum N) :
    plaqEdgeR (plaqDatumTranspose P) = plaqEdgeT P := rfl

theorem plaqEdgeT_transpose (P : PlaqDatum N) :
    plaqEdgeT (plaqDatumTranspose P) = plaqEdgeR P := rfl

theorem plaqEdgeL_transpose (P : PlaqDatum N) :
    plaqEdgeL (plaqDatumTranspose P) = plaqEdgeB P := rfl

/-- The holonomy of the transposed datum is the inverse
holonomy. -/
theorem plaqHol_transpose (P : PlaqDatum N)
    (u : LayerLink N → G) :
    PlaqHol (plaqDatumTranspose P) u = (PlaqHol P u)⁻¹ := by
  unfold PlaqHol
  rw [plaqEdgeB_transpose, plaqEdgeR_transpose,
    plaqEdgeT_transpose, plaqEdgeL_transpose]
  group

/-- The corner swap `1 ↔ 2`, as a measurable equivalence
of the corner tuples. -/
def cornerSwapEquiv : (Fin 4 → G) ≃ᵐ (Fin 4 → G) :=
  MeasurableEquiv.piCongrLeft (fun _ : Fin 4 => G) (Equiv.swap 1 2)

theorem cornerSwapEquiv_apply (a : Fin 4 → G) (i : Fin 4) :
    cornerSwapEquiv a i = a (Equiv.swap 1 2 i) := by
  unfold cornerSwapEquiv
  have h := MeasurableEquiv.piCongrLeft_apply_apply
    (β := fun _ : Fin 4 => G) (Equiv.swap 1 2) a (Equiv.swap 1 2 i)
  rwa [Equiv.swap_apply_self] at h

theorem measurePreserving_cornerSwapEquiv :
    MeasurePreserving cornerSwapEquiv
      (Measure.pi fun _ : Fin 4 => μG)
      (Measure.pi fun _ : Fin 4 => μG) :=
  measurePreserving_piCongrLeft (fun _ : Fin 4 => μG)
    (Equiv.swap 1 2)

/-- Corner-integral substitution: the corner swap `1 ↔ 2`. -/
theorem cornerIntegral_swap12 (F : (Fin 4 → G) → ℂ) :
    (∫ a : Fin 4 → G, F (cornerSwapEquiv a)
      ∂(Measure.pi fun _ : Fin 4 => μG))
      = ∫ a : Fin 4 → G, F a
        ∂(Measure.pi fun _ : Fin 4 => μG) :=
  (measurePreserving_cornerSwapEquiv μG).integral_comp
    cornerSwapEquiv.measurableEmbedding F

/-- The edge reversal on the four plaquette edges: under
the datum transpose, edge `e` of `Pᵀ` is edge `3 − e`
of `P`. -/
def plaqEdgeRev : Fin 4 → Fin 4 := ![3, 2, 1, 0]

theorem plaqEdgeRev_involutive :
    ∀ e : Fin 4, plaqEdgeRev (plaqEdgeRev e) = e := by decide

theorem plaqCornerA_swap :
    ∀ e : Fin 4, plaqCornerA (plaqEdgeRev e)
      = Equiv.swap 1 2 (plaqCornerA e) := by decide

theorem plaqCornerB_swap :
    ∀ e : Fin 4, plaqCornerB (plaqEdgeRev e)
      = Equiv.swap 1 2 (plaqCornerB e) := by decide

/-- The edges of the transposed datum are the reversed
edges of the original datum. -/
theorem plaqEdgeOf_transpose (P : PlaqDatum N) :
    ∀ e : Fin 4, plaqEdgeOf (plaqDatumTranspose P) e
      = plaqEdgeOf P (plaqEdgeRev e) := by
  intro e
  fin_cases e
  · exact plaqEdgeB_transpose P
  · exact plaqEdgeR_transpose P
  · exact plaqEdgeT_transpose P
  · exact plaqEdgeL_transpose P

/-- The approximant integrand at the transposed datum and
swapped corners is the original integrand (factor
relabeling by the edge reversal). -/
theorem plaqApproxIntegrand_transpose (P : PlaqDatum N)
    (K : ℕ) (β : ℝ) (u u' : LayerLink N → G) (a : Fin 4 → G) :
    plaqApproxIntegrand ρ (plaqDatumTranspose P) K β u u'
        (cornerSwapEquiv a)
      = plaqApproxIntegrand ρ P K β u u' a := by
  unfold plaqApproxIntegrand
  refine Finset.prod_bij (fun e _ => plaqEdgeRev e)
    (fun e _ => Finset.mem_univ _) ?_ ?_ ?_
  · intro e₁ _ e₂ _ h
    have h2 := congrArg plaqEdgeRev h
    rwa [plaqEdgeRev_involutive, plaqEdgeRev_involutive] at h2
  · intro e _
    exact ⟨plaqEdgeRev e, Finset.mem_univ _,
      plaqEdgeRev_involutive e⟩
  · intro e _
    simp only [cornerSwapEquiv_apply, ← plaqCornerA_swap,
      ← plaqCornerB_swap, plaqEdgeOf_transpose]

/-- **Block-level datum rotation (all orders `K`)**: the
approximant block is unchanged by transposing the datum. -/
theorem plaqBlockApprox_transpose (P : PlaqDatum N) (K : ℕ)
    (β : ℝ) (u u' : LayerLink N → G) :
    PlaqBlockApprox μG ρ (plaqDatumTranspose P) K β u u'
      = PlaqBlockApprox μG ρ P K β u u' := by
  unfold PlaqBlockApprox
  rw [← cornerIntegral_swap12 μG
    (fun a => plaqApproxIntegrand ρ (plaqDatumTranspose P)
      K β u u' a)]
  exact integral_congr_ae (ae_of_all _ fun a =>
    plaqApproxIntegrand_transpose ρ P K β u u' a)

/-- The right edge is not the left edge (`Even N`,
`4 ≤ N`: same direction `ν`, bases `c₁₀ ≠ c₀₀`). -/
theorem plaqEdgeR_ne_L (hN : Even N) (h4N : 4 ≤ N)
    (P : PlaqDatum N) : plaqEdgeR P ≠ plaqEdgeL P := by
  intro h
  have h2 := congrArg (fun ℓ : LayerLink N => ℓ.1.1) h
  have h3 : plaqCorner10 P = plaqCorner00 P := Subtype.ext h2
  exact plaqCorner10_ne_00 hN h4N P h3

/-- The top edge is not the left edge (directions `μ`
and `ν` differ). -/
theorem plaqEdgeT_ne_L (P : PlaqDatum N) :
    plaqEdgeT P ≠ plaqEdgeL P := by
  intro h
  have h2 := congrArg (fun ℓ : LayerLink N => ℓ.1.2) h
  exact P.hne (show P.mu = P.nu from h2)

/-- The holonomy of the transposed section is the
inverse: the transposed section sits on the left edge,
so the loop reads `x` only there, inverted. -/
theorem PlaqHol_plaqSection_transpose (hN : Even N)
    (h4N : 4 ≤ N) (P : PlaqDatum N) (x : G) :
    PlaqHol P (plaqSection (plaqDatumTranspose P) x)
      = x⁻¹ := by
  have hB : plaqEdgeB P ≠ plaqEdgeB (plaqDatumTranspose P) := by
    rw [plaqEdgeB_transpose]
    exact Ne.symm (plaqEdgeL_ne_B P)
  have hR : plaqEdgeR P ≠ plaqEdgeB (plaqDatumTranspose P) := by
    rw [plaqEdgeB_transpose]
    exact plaqEdgeR_ne_L hN h4N P
  have hT : plaqEdgeT P ≠ plaqEdgeB (plaqDatumTranspose P) := by
    rw [plaqEdgeB_transpose]
    exact plaqEdgeT_ne_L P
  have hL : plaqSection (plaqDatumTranspose P) x (plaqEdgeL P)
      = x := by
    rw [← plaqEdgeB_transpose]
    exact plaqSection_at_B _ x
  unfold PlaqHol
  rw [plaqSection_at_of_ne _ _ hB, plaqSection_at_of_ne _ _ hR,
    plaqSection_at_of_ne _ _ hT, hL]
  simp

/-- **Kernel-level datum rotation at `K = 1`, conditional
form** (A2-2b deferral (ii) in datum-rotation form; this
identity is also the `K = 1` content of deferral (i),
both-arguments inversion): IF the stage telescoping
identity `PlaqTelescopingApprox 1` holds at `P`, then the
rotated kernel is the original kernel at the inverted
arguments. Hypotheses on the face: the conditional `hT`,
and `Even N`, `4 ≤ N` for edge distinctness, exactly as
in A2-2a's registration sanity lemma `PlaqHol_plaqSection`. -/
theorem plaqKernelApprox_one_transpose (hN : Even N)
    (h4N : 4 ≤ N) (P : PlaqDatum N) (β : ℝ)
    (hT : PlaqTelescopingApprox μG ρ P 1 β) (x y : G) :
    PlaqKernelApprox μG ρ (plaqDatumTranspose P) 1 β x y
      = PlaqKernelApprox μG ρ P 1 β x⁻¹ y⁻¹ := by
  show PlaqBlockApprox μG ρ (plaqDatumTranspose P) 1 β
      (plaqSection (plaqDatumTranspose P) x)
      (plaqSection (plaqDatumTranspose P) y)
    = PlaqKernelApprox μG ρ P 1 β x⁻¹ y⁻¹
  rw [plaqBlockApprox_transpose,
    hT (plaqSection (plaqDatumTranspose P) x)
      (plaqSection (plaqDatumTranspose P) y),
    PlaqHol_plaqSection_transpose hN h4N,
    PlaqHol_plaqSection_transpose hN h4N]

end DatumRotation

end ThetLogos
