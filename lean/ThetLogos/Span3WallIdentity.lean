/-
# S3-1-F1: FACT ⇔ BRIDGE, formalized

Brick S3-1-F1 of the Span-3 first pier, formalizing §§1–2.1
and §7 (F1 spec) of the S3-1 wall-identity gate dossier
(`whitepaper/s31-wall-identity-gate-2026-10-29.md`) and DP-1's
verdict for the factorization/bridge pair: the stratum column
factorization (i) FACT and the LOC-3 bridge (iii) BRIDGE are
one proposition in two dialects — the identity dialect and
the log-density dialect.

Consumed, landed: S3-0's `StratumColumnFactorization`
(`ThetLogos.Span3MarginPin`), `log_zpolymer_eq`,
`zpolymer_pos`, `colZ_pos` (whose positivity argument
`layerKernelReal_pos` below follows one level up),
`layerDensSum_nonneg`, `layerDensSum_le`
(`ThetLogos.PolymerPartition`, `ThetLogos.PlaneCrossingBeta2`).

This module lives on the MarginPin / PolymerPartition side
of the tree seam recorded in `Span3MarginPin`'s header (the
duplicate declaration `ThetLogos.reflSite_eq_torusShift_zero`
makes the `LatticeUniformGap` chain and the
`PolymerPartition` chain co-importable nowhere); it does not
import the `LatticeUniformGap` chain.

**What is proved here is an equivalence of two STATEMENTS.**
Neither statement is proved: no factorization, no bridge, no
positivity of any kernel is asserted for `layerKernel`
itself. Arrows A4/A5/A6 of the gate (to and from uniformity)
are untouched, statable-and-open; this brick changes nothing
about the second wall. Proof-grade distance toward the
continuum remains ZERO. NO CLAIM, parts 0, dials 0/4. The
fenced Span-3 vocabulary stays unspent.
-/

import ThetLogos.Span3MarginPin

namespace ThetLogos

open MeasureTheory

section Span3WallIdentity

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ)) {N : ℕ} [NeZero N]

/-- **The real layer kernel** — the gate's §1(iii) paper
definition, in owned vocabulary: the stratum integral of the
real Boltzmann factor `exp (-(layerAction ρ β α u u'))` over
the product Haar probability `πμG`. `layerKernel` is this
number cast to `ℂ` (see `layerKernel_eq_ofReal_layerKernelReal`
below). -/
noncomputable def layerKernelReal (β : ℝ) (u u' : LayerLink N → G) :
    ℝ :=
  ∫ α, Real.exp (-(layerAction ρ β α u u'))
    ∂(Measure.pi fun _ : LayerSite N => μG)

/-- The real Boltzmann integrand of `layerKernelReal` is
integrable: it is bounded by the constant
`exp (|β| * (2 * colCount N))` on the probability stratum,
since `0 ≤ layerDensSum ≤ 2 * colCount N`
(`layerDensSum_nonneg`, `layerDensSum_le`, Even `N`) and
`layerAction = β * layerDensSum`. -/
theorem integrable_exp_neg_layerAction (hN : Even N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (β : ℝ) (u u' : LayerLink N → G) :
    Integrable (fun α => Real.exp (-(layerAction ρ β α u u')))
      (Measure.pi fun _ : LayerSite N => μG) := by
  have hmeas : Measurable
      fun α : LayerSite N → G => layerDensSum ρ α u u' :=
    measurable_layerDensSum ρ hN hρcont u u'
  have hfun : (fun α => Real.exp (-(layerAction ρ β α u u')))
      = fun α => Real.exp (-(β * layerDensSum ρ α u u')) :=
    funext fun α => by rw [layerAction_eq]
  rw [hfun]
  refine Integrable.of_bound
    ((Real.continuous_exp.measurable.comp
      ((hmeas.const_mul β).neg)).aestronglyMeasurable)
    (Real.exp (|β| * (2 * colCount N)))
    (Filter.Eventually.of_forall fun α => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  have hS0 : 0 ≤ layerDensSum ρ α u u' :=
    layerDensSum_nonneg ρ hN α u u'
  have hS2 : layerDensSum ρ α u u' ≤ 2 * colCount N :=
    layerDensSum_le ρ hN α u u'
  have habs : |β * layerDensSum ρ α u u'|
      ≤ |β| * (2 * colCount N) := by
    rw [abs_mul, abs_of_nonneg hS0]
    exact mul_le_mul_of_nonneg_left hS2 (abs_nonneg β)
  linarith [neg_le_abs (β * layerDensSum ρ α u u')]

/-- **(B-real)** — the gate's §2.1 bookkeeping lemma:
`layerKernel` is the complex cast of `layerKernelReal`. The
integrand of `layerKernel` is by definition the cast of the
real integrand, and the integral commutes with the cast. -/
theorem layerKernel_eq_ofReal_layerKernelReal
    (β : ℝ) (u u' : LayerLink N → G) :
    layerKernel μG ρ β u u'
      = ((layerKernelReal μG ρ β u u' : ℝ) : ℂ) := by
  unfold layerKernel layerKernelReal
  exact integral_ofReal

/-- **(B-pos)** — the gate's §2.1 bookkeeping lemma:
`0 < layerKernelReal β u u'`. The integrand is
`exp (-β * layerDensSum)` with
`0 ≤ layerDensSum ≤ 2 * colCount N`
(`layerDensSum_nonneg`, `layerDensSum_le`, Even `N`), so it
is bounded below by the positive constant
`exp (-(|β| * (2 * colCount N)))` on a probability space —
the landed `colZ_pos` argument, one level up. -/
theorem layerKernelReal_pos (hN : Even N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (β : ℝ) (u u' : LayerLink N → G) :
    0 < layerKernelReal μG ρ β u u' := by
  have hInt := integrable_exp_neg_layerAction μG ρ hN hρcont β u u'
  have hge : Real.exp (-(|β| * (2 * colCount N)))
      ≤ layerKernelReal μG ρ β u u' := by
    have hle : ∀ α : LayerSite N → G,
        Real.exp (-(|β| * (2 * colCount N)))
          ≤ Real.exp (-(layerAction ρ β α u u')) := by
      intro α
      apply Real.exp_le_exp.mpr
      have hS0 : 0 ≤ layerDensSum ρ α u u' :=
        layerDensSum_nonneg ρ hN α u u'
      have hS2 : layerDensSum ρ α u u' ≤ 2 * colCount N :=
        layerDensSum_le ρ hN α u u'
      have habs : |β * layerDensSum ρ α u u'|
          ≤ |β| * (2 * colCount N) := by
        rw [abs_mul, abs_of_nonneg hS0]
        exact mul_le_mul_of_nonneg_left hS2 (abs_nonneg β)
      rw [layerAction_eq]
      linarith [le_abs_self (β * layerDensSum ρ α u u')]
    have hconst : ∫ _α : LayerSite N → G,
          Real.exp (-(|β| * (2 * colCount N)))
          ∂(Measure.pi fun _ : LayerSite N => μG)
        = Real.exp (-(|β| * (2 * colCount N))) := by simp
    rw [layerKernelReal, ← hconst]
    exact integral_mono_ae (integrable_const _) hInt
      (Filter.Eventually.of_forall hle)
  exact lt_of_lt_of_le (Real.exp_pos _) hge

/-- **The LOC-3 bridge for `𝒜` — BRIDGE** (the gate's §1(iii)):
the per-volume log-density of `𝒜` equals the polymer
density,

  `Real.log (layerKernelReal β u u')
    = colCount N * Real.log (colZ ρ μG β u u' P)`

for every pair of layer data `u u'` and every column `P`.

**Reconciliation, on the face:** the gate's §1(iii) form
quantifies `β` universally, inside the Prop
(`∀ β u u' P, …`); this is the per-`β` form, reconciled with
S3-0's per-`β` `StratumColumnFactorization` exactly as that
pin reconciled its own per-`β` form with the gate's §1(i) —
the universal form is the conjunction of these over `β`, and
the equivalence below is stated and proved per `β`. This is
a TARGET statement: it is not proved anywhere in this
module, and the landed LOC-3 bridge (`log_zpolymer_eq`) is
not this statement — its left-hand side is `zPolymer`, an
object that is a product over columns by definition, not
`𝒜`. -/
def BridgeLOC3 (β : ℝ) : Prop :=
  ∀ u u' : LayerLink N → G, ∀ P : LayerColumn N,
    Real.log (layerKernelReal μG ρ β u u')
      = colCount N * Real.log (colZ ρ μG β u u' P)

/-- **FACT ⇔ BRIDGE** — the headline equivalence of the
S3-1 gate, §2.1 (arrows A1–A2): at fixed `(β, N)` with
`hN : Even N` and `hρcont`, the stratum column factorization
and the LOC-3 bridge for `𝒜` are the same proposition in two
dialects.

A1 (forward): FACT identifies `𝒜`'s real density with
`zPolymer` by (B-real)
(`layerKernel_eq_ofReal_layerKernelReal`); applying
`Real.log`, the landed `log_zpolymer_eq` gives exactly
BRIDGE's right-hand side.

A2 (backward): both densities are positive — (B-pos)
(`layerKernelReal_pos`) and the landed `zpolymer_pos` — and
`Real.log` is injective on positive reals
(`Real.log_injOn_pos`), so BRIDGE's log-equality is an
equality of the densities themselves, which by (B-real) is
FACT.

**DP-1 consequence, in the gate's exact terms:** (i) and
(iii) are the same proposition in two dialects; any future
result about one is a result about the other. Arrows
A4/A5/A6 (to and from uniformity) are untouched,
statable-and-open; this equivalence changes nothing about
the second wall. Neither side is proved here. -/
theorem stratumColumnFactorization_iff_bridgeLOC3 (hN : Even N)
    (hρcont : Continuous fun g : G => repMatrix ρ g) (β : ℝ) :
    StratumColumnFactorization (N := N) μG ρ β
      ↔ BridgeLOC3 (N := N) μG ρ β := by
  constructor
  · intro hfact u u' P
    have hreal : layerKernelReal μG ρ β u u'
        = zPolymer ρ μG β u u' := by
      have h := hfact u u'
      rw [layerKernel_eq_ofReal_layerKernelReal μG ρ β u u'] at h
      exact Complex.ofReal_injective h
    rw [hreal]
    exact log_zpolymer_eq ρ μG hN hρcont β u u' P
  · intro hbridge u u'
    have hP : Nonempty (LayerColumn N) :=
      ⟨⟨(⟨fun _ => (0 : ZMod N), by simp⟩ : LayerSite N),
        ⟨1, by simp⟩⟩⟩
    obtain ⟨P⟩ := hP
    have hpos1 : 0 < layerKernelReal μG ρ β u u' :=
      layerKernelReal_pos μG ρ hN hρcont β u u'
    have hpos2 : 0 < zPolymer ρ μG β u u' :=
      zpolymer_pos ρ μG hρcont β u u'
    have hlog : Real.log (layerKernelReal μG ρ β u u')
        = Real.log (zPolymer ρ μG β u u') := by
      rw [hbridge u u' P]
      exact (log_zpolymer_eq ρ μG hN hρcont β u u' P).symm
    have hreal : layerKernelReal μG ρ β u u'
        = zPolymer ρ μG β u u' :=
      Real.log_injOn_pos (Set.mem_Ioi.mpr hpos1)
        (Set.mem_Ioi.mpr hpos2) hlog
    rw [layerKernel_eq_ofReal_layerKernelReal μG ρ β u u', hreal]

end Span3WallIdentity

end ThetLogos
