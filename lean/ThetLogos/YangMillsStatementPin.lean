/-
# YangMillsStatementPin — YM-0: the Yang–Mills mass-gap statement, pinned

**Commissioned by Zero, 2026-11-21 00:09 EST ("fire").
Lane-grade pin. NO CLAIM. Pre-registered DIAL-INELIGIBLE; dials 0/4
under every outcome.**

Spec of record: ~/workspace/your_files/ym0-statement-pin-spec-2026-11-21.md
(rung YM-0 of millennium-ladders-ym-and-riemann-2026-11-21.md).

A statement pin earns NO progress. Its only job is to fix the target
exactly, so no later rung can drift and no external claim can be graded
against a moving statement. Dial 3 (continuum limit) stays 0; this pin
constructs nothing, assumes nothing, and proves nothing about
Yang–Mills theory.

STRIKE-CHECK (2026-11-21, against Mathlib): CLEAR — no duplicate.
`MassGap` / `mass gap` / `massGap` return zero hits in all of Mathlib;
there is no Yang–Mills object to collide with.

HONEST SCOPE, on the face: the gap predicate below is stated over
BOUNDED self-adjoint operators (`E →L[ℂ] E`), because that is the
carrier Mathlib's `spectrum` supports. A physical Yang–Mills
Hamiltonian is unbounded; Mathlib's unbounded carrier (`LinearPMap`)
has self-adjointness but no spectrum API. `YangMillsHasMassGap` states what a
mass gap IS, in the bounded shape — it is not the Clay Hamiltonian,
and no rung may cite it as one without the YM-3 bridge. The
OS/Wightman axioms are carried as a NAMED, UNFILLED `Prop` field in
the checklist: the pin refuses to define an axioms predicate, since
any such definition today would be a definition wearing the axioms'
name (the Hecke failure mode).

STATUS: STATUS-YANGMILLSSTATEMENT.md.
-/

import Mathlib.Tactic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.GroupTheory.Subgroup.Simple

namespace ThetLogos

/-- The pure spectral shape of a mass gap: the real set `σ` has no points in
the open interval `(E₀, E₀ + Δ)`, with `Δ > 0`. No operator, no physics —
the shape every gap statement below is built from. -/
def SpectrumHasGapAbove (σ : Set ℝ) (E₀ Δ : ℝ) : Prop :=
  0 < Δ ∧ σ ∩ Set.Ioo E₀ (E₀ + Δ) = ∅

/-- A smaller spectrum keeps the gap. (Pin-level working lemma.) -/
theorem SpectrumHasGapAbove.mono_set {σ σ' : Set ℝ} (hσ : σ ⊆ σ') {E₀ Δ : ℝ}
    (h : SpectrumHasGapAbove σ' E₀ Δ) : SpectrumHasGapAbove σ E₀ Δ :=
  ⟨h.1, by
    have hsub : σ ∩ Set.Ioo E₀ (E₀ + Δ) ⊆ σ' ∩ Set.Ioo E₀ (E₀ + Δ) :=
      fun x hx => ⟨hσ hx.1, hx.2⟩
    rw [h.2] at hsub
    exact Set.eq_empty_of_subset_empty hsub⟩

/-- A narrower claimed gap is easier to have: if `σ` has a gap of width `Δ`
above `E₀` and `0 < Δ' ≤ Δ`, it has a gap of width `Δ'`. -/
theorem SpectrumHasGapAbove.anti_delta {σ : Set ℝ} {E₀ Δ Δ' : ℝ} (hΔ : Δ' ≤ Δ)
    (hΔ' : 0 < Δ') (h : SpectrumHasGapAbove σ E₀ Δ) :
    SpectrumHasGapAbove σ E₀ Δ' :=
  ⟨hΔ', by
    have hIoo : Set.Ioo E₀ (E₀ + Δ') ⊆ Set.Ioo E₀ (E₀ + Δ) :=
      Set.Ioo_subset_Ioo le_rfl (by linarith)
    have hsub : σ ∩ Set.Ioo E₀ (E₀ + Δ') ⊆ σ ∩ Set.Ioo E₀ (E₀ + Δ) :=
      fun x hx => ⟨hx.1, hIoo hx.2⟩
    rw [h.2] at hsub
    exact Set.eq_empty_of_subset_empty hsub⟩

/-- `T` has a mass gap of width `Δ`: `T` is self-adjoint, `0` lies in its
real spectrum, its real spectrum lies in `[0, ∞)` (so `0` is the BOTTOM of
the spectrum — the vacuum energy, normalized to `0`), and the spectrum has
a gap of width `Δ` above `0`.

HONEST SCOPE, on the face: `T` here is a BOUNDED operator
(`E →L[ℂ] E`), because that is the carrier Mathlib's `spectrum` supports.
A physical Yang–Mills Hamiltonian is unbounded; Mathlib's unbounded carrier
(`LinearPMap`) has self-adjointness but no spectrum API, so the unbounded
form of this predicate cannot yet be stated with Mathlib spectrum. This
definition states what a mass gap IS, in the bounded shape. It is not the
Clay Hamiltonian, and no rung may cite it as one without the YM-3 bridge.

T10 INTEGRATION NOTE (2026-11-22): at lane grade this predicate was named
`HasMassGap`, colliding with `ClayStatement`'s theory-based
`ThetLogos.HasMassGap` (a predicate on a `QuantumYangMillsTheory`, not on
an operator). It is renamed `YangMillsHasMassGap` in this in-tree form;
the statement content is byte-identical, and the rename is disclosed in
the T10 ledger record. The unfolding lemma `hasMassGap_iff` keeps its
name (collision-free: the tree carries only `hasMassGap_iff_isolated`). -/
def YangMillsHasMassGap {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (T : E →L[ℂ] E) (Δ : ℝ) : Prop :=
  IsSelfAdjoint T ∧ (0 : ℝ) ∈ spectrum ℝ T ∧ spectrum ℝ T ⊆ Set.Ici 0 ∧
    SpectrumHasGapAbove (spectrum ℝ T) 0 Δ

/-- The unfolding of `YangMillsHasMassGap`, for later rungs to rewrite with. -/
theorem hasMassGap_iff {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (T : E →L[ℂ] E) (Δ : ℝ) :
    YangMillsHasMassGap T Δ ↔ IsSelfAdjoint T ∧ (0 : ℝ) ∈ spectrum ℝ T ∧
      spectrum ℝ T ⊆ Set.Ici 0 ∧ SpectrumHasGapAbove (spectrum ℝ T) 0 Δ :=
  Iff.rfl

/-- The SPECTRAL half of the Clay Yang–Mills statement, for the compact
simple gauge group `G` as a parameter: there exist a Hilbert space `E`, a
Hamiltonian `H` on it, and a gap width `Δ` with `YangMillsHasMassGap H Δ`.

This is a STATEMENT, not a construction: it is the proposition a YM-2/YM-3
construction would have to inhabit. `G` enters as the statement's
parameter; tying `H` to `G` (a theory OF the group `G`) is part of what
those rungs must supply — the pin does not pretend the parameter is
already coupled to the operator. -/
def YangMillsSpectralPrize (G : Type*) [Group G] [TopologicalSpace G]
    [CompactSpace G] [IsSimpleGroup G] : Prop :=
  ∃ (E : Type*) (_ : NormedAddCommGroup E) (_ : InnerProductSpace ℂ E)
    (_ : CompleteSpace E) (H : E →L[ℂ] E) (Δ : ℝ), YangMillsHasMassGap H Δ

/-- The FULL Clay checklist for Yang–Mills existence and mass gap, as one
proposition — every item the prize demands, as a named component.

- `E`, `H`, `Δ`: the theory's Hilbert space, Hamiltonian, and gap width.
- `gap`: the mass gap, in the pin's exact sense (`YangMillsHasMassGap`). This
  component has content TODAY because the pin defines it.
- `os_axioms`: the Osterwalder–Schrader / Wightman content of the prize —
  reflection positivity, Euclidean covariance, the field axioms. This is a
  NAMED, UNFILLED hypothesis: a component of type `Prop` that a claimant
  must SUPPLY. The pin does not define it, does not assume it, and
  inhabiting this checklist with `os_axioms := True` (or any stand-in) is
  NOT the prize — the prize is an inhabitant whose `os_axioms` component
  is the genuine axiom predicate, which does not exist in Mathlib yet. Any
  future rung that defines that predicate owes a definition-vs-named-object
  bridge (the RH-2 lesson) before this checklist may be read as Clay's.

LANE FALLBACK, used and disclosed (spec §Build notes): the spec's draft
stated this checklist as a `structure … : Prop`, but a Prop-valued
structure cannot carry data fields (`E : Type*`) with projections —
elaboration refuses it. Per the spec's own prescribed fallback, the
checklist ships in ∃-form (instances ∃-bound, as in
`YangMillsSpectralPrize`, plus the `os_axioms` component ∃-bound):
same frozen meaning, different binder plumbing. -/
def YangMillsStatement (G : Type*) [Group G] [TopologicalSpace G]
    [CompactSpace G] [IsSimpleGroup G] : Prop :=
  ∃ (E : Type*) (_ : NormedAddCommGroup E) (_ : InnerProductSpace ℂ E)
    (_ : CompleteSpace E) (H : E →L[ℂ] E) (Δ : ℝ) (os_axioms : Prop),
    YangMillsHasMassGap H Δ

/-- A checklist witness really does carry a positive gap width — the
checklist's teeth are connected. Nothing about Yang–Mills is proved here.
(∃-form, per the fallback disclosed at `YangMillsStatement`: the
witness's gap width exists and is positive.) -/
theorem YangMillsStatement.gap_pos {G : Type*} [Group G] [TopologicalSpace G]
    [CompactSpace G] [IsSimpleGroup G] (w : YangMillsStatement G) :
    ∃ Δ : ℝ, 0 < Δ := by
  obtain ⟨E, _, _, _, H, Δ, _os, gap⟩ := w
  exact ⟨Δ, gap.2.2.2.1⟩

end ThetLogos
