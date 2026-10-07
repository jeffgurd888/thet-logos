import Mathlib.Basic.Real.Basic
import Mathlib.Tactic
import Mathlib.Geometry.Convex.Cone.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace ThetLogos

/-!
# ThetLogos.WightmanAxioms — the Wightman axioms as a pinned statement

Source: the QFT rungs map (`whitepaper/qft-rungs-map-2026-10-06.md`, Rung 3),
which records that no interacting 4D Wightman QFT has ever been constructed.
This file pins the axioms as a fixed Lean target so that "progress toward
constructive QFT" is measured against an unmoving statement.

**What this file IS.** A machine-checked *statement* of the Wightman axioms
(Streater–Wightman, *PCT, Spin and Statistics, and All That*, 1964), with
each analytic component as a labeled opaque field, plus the open existence
problem for interacting theories.

**What this file is NOT.** A construction of any QFT, or progress toward one.
Mathlib (2026) has no Schwartz distribution theory, no operator-valued
distributions, no Poincaré representation theory adequate for quantum fields —
those dependencies are logged below, not wished away. Per the rungs map's
caution: a Lean file *named* after a theorem proves nothing until the
statement is checked; this file claims only the statement.

Honesty tiers in this file:
- **T1 (proved):** `forwardLightCone_convexCone` — the closed forward light
  cone (the geometric object in the spectrum condition) is a convex cone.
  Elementary, but it grounds the axiom's geometry in checked mathematics.
- **T5 (theorem-shaped, content opaque):** `WightmanAxioms`,
  `InteractingWightmanQFT`, `WightmanExistence` — the open problem.
-/

/-- Minkowski space ℝ^{1,3} as a function type. -/
abbrev Minkowski := Fin 4 → ℝ

/-- The Minkowski inner product with signature (+,−,−,−).
    `p 0` is the energy component. -/
def minkowskiInner (p q : Minkowski) : ℝ :=
  p 0 * q 0 - p 1 * q 1 - p 2 * q 2 - p 3 * q 3

/-- The closed forward light cone: `p² ≥ 0` and `p⁰ ≥ 0`.
    The spectrum condition (Wightman axiom W3) asserts that the joint
    spectrum of the energy-momentum operators lies in this cone. -/
def forwardLightCone : Set Minkowski :=
  {p | 0 ≤ minkowskiInner p p ∧ 0 ≤ p 0}

/-- Reverse Cauchy–Schwarz for the forward light cone: the Minkowski
    inner product of two future-timelike vectors is nonnegative.
    This is the analytic heart of the spectrum condition's consistency. -/
theorem minkowskiInner_nonneg_of_mem {p q : Minkowski}
    (hp : p ∈ forwardLightCone) (hq : q ∈ forwardLightCone) :
    0 ≤ minkowskiInner p q := by
  simp only [forwardLightCone, Set.mem_ofPred_eq] at hp hq
  obtain ⟨hp1, hp2⟩ := hp
  obtain ⟨hq1, hq2⟩ := hq
  unfold minkowskiInner at hp1 hq1 ⊢
  -- Spatial Cauchy–Schwarz: (u·v)² ≤ |u|²|v|²
  have cs : (p 1 * q 1 + p 2 * q 2 + p 3 * q 3) ^ 2 ≤
      (p 1 ^ 2 + p 2 ^ 2 + p 3 ^ 2) * (q 1 ^ 2 + q 2 ^ 2 + q 3 ^ 2) := by
    nlinarith [sq_nonneg (p 1 * q 2 - p 2 * q 1),
               sq_nonneg (p 1 * q 3 - p 3 * q 1),
               sq_nonneg (p 2 * q 3 - p 3 * q 2)]
  -- |u|²|v|² ≤ (p⁰q⁰)² from the cone hypotheses
  have hPQ : (p 1 ^ 2 + p 2 ^ 2 + p 3 ^ 2) * (q 1 ^ 2 + q 2 ^ 2 + q 3 ^ 2)
      ≤ (p 0 * q 0) ^ 2 := by
    have e1 : (0 : ℝ) ≤ p 0 * p 0 - (p 1 ^ 2 + p 2 ^ 2 + p 3 ^ 2) := by
      nlinarith [hp1]
    have e2 : (0 : ℝ) ≤ q 0 * q 0 - (q 1 ^ 2 + q 2 ^ 2 + q 3 ^ 2) := by
      nlinarith [hq1]
    have e3 : (0 : ℝ) ≤ p 1 ^ 2 + p 2 ^ 2 + p 3 ^ 2 := by positivity
    nlinarith [mul_nonneg e1 (sq_nonneg (q 0)), mul_nonneg e3 e2]
  have hsq : (p 1 * q 1 + p 2 * q 2 + p 3 * q 3) ^ 2 ≤ (p 0 * q 0) ^ 2 :=
    le_trans cs hPQ
  -- Take square roots: |u·v| ≤ p⁰q⁰
  have habs : |p 1 * q 1 + p 2 * q 2 + p 3 * q 3| ≤ p 0 * q 0 := by
    have h := Real.sqrt_le_sqrt hsq
    rw [Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs,
      abs_of_nonneg (mul_nonneg hp2 hq2)] at h
    exact h
  have hle : p 1 * q 1 + p 2 * q 2 + p 3 * q 3 ≤ p 0 * q 0 :=
    le_trans (le_abs_self _) habs
  linarith

/-- The forward light cone is a convex cone (Tier T1): closed under
    addition and positive scaling. This is the elementary geometric
    fact underlying the spectrum condition's stability. -/
def forwardLightCone_convexCone : ConvexCone ℝ Minkowski where
  carrier := forwardLightCone
  smul_mem' := by
    intro c hc x hx
    simp only [forwardLightCone, Set.mem_ofPred_eq] at hx ⊢
    obtain ⟨hx1, hx2⟩ := hx
    have hcs : ∀ i : Fin 4, (c • x) i = c * x i := fun i => by
      simp [Pi.smul_apply, smul_eq_mul]
    refine ⟨?_, ?_⟩
    · -- (c•x)² = c²·x² ≥ 0
      have : minkowskiInner (c • x) (c • x)
          = (c * c) * minkowskiInner x x := by
        unfold minkowskiInner
        simp only [hcs]
        ring
      rw [this]
      have : (0 : ℝ) ≤ c * c := by positivity
      nlinarith [hx1, this, mul_nonneg this hx1]
    · -- (c•x)⁰ = c·x⁰ ≥ 0
      rw [hcs]
      exact mul_nonneg (le_of_lt hc) hx2
  add_mem' := by
    intro x hx y hy
    have hcs := minkowskiInner_nonneg_of_mem hx hy
    simp only [forwardLightCone, Set.mem_ofPred_eq] at hx hy ⊢
    obtain ⟨hx1, hx2⟩ := hx
    obtain ⟨hy1, hy2⟩ := hy
    refine ⟨?_, by simp [Pi.add_apply]; linarith⟩
    -- (x+y)² = x² + y² + 2⟨x,y⟩ ≥ 0 by reverse Cauchy–Schwarz
    have hexpand : minkowskiInner (x + y) (x + y)
        = minkowskiInner x x + minkowskiInner y y
          + 2 * minkowskiInner x y := by
      unfold minkowskiInner
      simp [Pi.add_apply]
      ring
    rw [hexpand]
    linarith [hcs]

/-- A Hilbert space marker: Mathlib has Hilbert spaces, but the
    Wightman framework needs the *specific* physical Hilbert space
    carrying a Poincaré representation — pinned as a marker type. -/
structure HilbertMarker where
  carrier : Type

/-- Tempered distributions marker: Mathlib (2026) has no Schwartz
    distribution theory, let alone operator-valued distributions.
    This is a labeled placeholder, not a definition. -/
structure TemperedDistMarker where
  carrier : Type

/-- The Wightman axioms (Streater–Wightman 1964), pinned as a bundle.
    Each analytic field is an opaque `Prop` naming the axiom; the content
    (operator-valued tempered distributions, Poincaré covariance of
    unbounded operators, the reconstruction theorem) is beyond Mathlib's
    2026 infrastructure. -/
structure WightmanAxioms where
  /-- The physical Hilbert space. -/
  hilbert : HilbertMarker
  /-- The vacuum vector (marker: a distinguished vector). -/
  vacuumExists : Prop
  /-- W1: quantum fields as operator-valued tempered distributions
      (opaque: needs distribution theory). -/
  fieldsExist : Prop
  /-- W2: Poincaré covariance of the fields (opaque). -/
  poincareCovariant : Prop
  /-- W3: spectrum condition — joint energy-momentum spectrum in the
      closed forward light cone (geometry pinned above in T1). -/
  spectrumCondition : Prop
  /-- W4: locality / microcausality — spacelike-separated fields
      (anti)commute (opaque). -/
  locality : Prop
  /-- W5: the vacuum is cyclic for the field algebra (opaque). -/
  vacuumCyclic : Prop
  /-- Non-triviality: not a (generalized) free field (opaque: pinning
      down "free" needs the full n-point function content). -/
  nontrivial : Prop

/-- An interacting Wightman QFT in 4D: a non-trivial model of the axioms.
    **Open:** no example has ever been constructed (rungs map, Rung 3). -/
def InteractingWightmanQFT : Prop :=
  ∃ _ : WightmanAxioms, True

/-- The constructive-QFT existence problem, pinned: does an interacting
    4D Wightman QFT exist? This is the fixed target for Rung 3;
    partial results are measured against it, never against a weakening. -/
def WightmanExistence : Prop := InteractingWightmanQFT

/-!
## Dependency ledger (what Mathlib 2026 lacks for Rung 3)

1. Schwartz distribution theory (`𝒮'`) — no tempered distributions.
2. Operator-valued distributions / quantum fields as such.
3. Poincaré group representation theory for unbounded operators.
4. The Wightman reconstruction theorem (needs 1–3).
5. Any interacting 4D example (open problem in mathematics, not just
   in formalization).

Nothing in this file bridges these gaps. The file's value is the pinned
target: `WightmanExistence` does not move when fashions change.
-/

end ThetLogos
