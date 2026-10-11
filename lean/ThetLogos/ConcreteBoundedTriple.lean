import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import ThetLogos.BoundedTriple
import ThetLogos.ConcreteFiniteModel

namespace ThetLogos

/-!
# ThetLogos.ConcreteBoundedTriple — Rung 4 Track 1: bounded-triple instance for the Pauli model (2026-10-11)

Rung 4 Track 1 (Jeff's "Build the house", 2026-10-11): form the
`BoundedAnalyticTriple` instance for the concrete 2-dim Pauli model of
`ConcreteFiniteModel.lean` — honestly.

## The blocker and the honest route (route (a))
`hcompactRes : HasCompactResolvent D` is an OPAQUE def (`BoundedTriple.lean`
§1): it cannot be proved, only assumed. The mathematical content it packages
IS provable for this finite model, and is proved here as T1:
- `pauliD_resolvent`: the resolvent `(pauliD - lam • 1)⁻¹` exists as a
  two-sided inverse for `lam ∉ {1, -1}` (the spectrum of Pauli X),
  transported from the 2×2 matrix inverse via `endAlgEquiv`
  (helpers `pauliD_sub_smul_matrix`, `pauliD_sub_det`);
- `pauliD_resolvent_compact`: every such resolvent is a compact operator —
  finite-dimensionality is the whole proof (`end_compact`).

The instance is therefore formed with `hcompactRes` discharged by ONE
explicit, model-specific, labeled T2 axiom —
`pauli_compactResolvent : HasCompactResolvent pauliD` — a NAMED WINDOW whose
content is proved by the T1s above. `hbddComm` / `hbddRep` are the proved
T1s `bddComm` / `bddRep` from `ConcreteFiniteModel.lean`.

## What remains a window
- `pauli_compactResolvent` (T2): the bridge from the opaque Prop
  `HasCompactResolvent pauliD` to the proved mathematics. It cannot be
  eliminated without changing `HasCompactResolvent` from `opaque` to a
  transparent def stated in Mathlib's compact-operator API — a
  `BoundedTriple.lean` design decision, out of scope here (route (b) in
  the task; not taken).
- The model itself stays analytically trivial: scalar `π` makes all
  commutators vanish (`bddComm` with `C = 0`); this discharges the analytic
  DEBT, not interesting gauge content (see the HONESTY NOTE in
  `ConcreteFiniteModel.lean`). `satisfiesDestruction` (the 32×32 model) is
  untouched — out of scope.

## Tier ledger
T2 (axiom/instance): `pauli_compactResolvent`, `pauliBounded`.
T1 (proved, zero sorrys): `pauliD_sub_smul_matrix`, `pauliD_sub_det`,
  `pauliD_resolvent`, `pauliD_resolvent_compact`.
-/

-- ============================================================================
-- §1. The resolvent of `pauliD` off its spectrum (T1)
-- ============================================================================

/-- The matrix of `pauliD - lam • 1` (Tier T1 — proved): `endAlgEquiv`
    sends `pauliD` to Pauli X. -/
theorem pauliD_sub_smul_matrix (lam : ℂ) :
    endAlgEquiv (pauliD - lam • 1) = pauliX - lam • 1 := by
  have e1 : endAlgEquiv pauliD = pauliX := AlgEquiv.apply_symm_apply _ _
  rw [map_sub, e1, map_smul, map_one]

/-- The determinant (Tier T1 — proved): `det (X - lam • 1) = lam² - 1`,
    by direct 2×2 computation. -/
theorem pauliD_sub_det (lam : ℂ) :
    Matrix.det (pauliX - lam • 1) = lam ^ 2 - 1 := by
  have hmat : pauliX - lam • 1 = !![-lam, 1; 1, -lam] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pauliX, Matrix.sub_apply, smul_eq_mul]
  rw [hmat, Matrix.det_fin_two_of]
  ring

/-- The resolvent exists off the spectrum `{1, -1}` (Tier T1 — proved):
    for `lam ≠ ±1`, `pauliD - lam • 1` has a two-sided inverse, transported
    from the matrix inverse via `endAlgEquiv` (determinant `lam² - 1 ≠ 0`,
    since `ℂ` is a domain). -/
theorem pauliD_resolvent (lam : ℂ) (h1 : lam ≠ 1) (h2 : lam ≠ -1) :
    ∃ R : Module.End ℂ (EuclideanSpace ℂ (Fin 2)),
      R * (pauliD - lam • 1) = 1 ∧ (pauliD - lam • 1) * R = 1 := by
  have hM : endAlgEquiv (pauliD - lam • 1) = pauliX - lam • 1 :=
    pauliD_sub_smul_matrix lam
  have hne : Matrix.det (pauliX - lam • 1) ≠ 0 := by
    rw [pauliD_sub_det lam, show lam ^ 2 - 1 = (lam - 1) * (lam + 1) by ring]
    exact mul_ne_zero (sub_ne_zero.mpr h1) (fun h => h2 (eq_neg_of_add_eq_zero_left h))
  have hunit : IsUnit (pauliX - lam • 1) :=
    -- NB: `Matrix.isUnit_iff_isUnit_det.mpr` (projection on the namespaced
    -- constant, no explicit args) fails to resolve once `Mathlib.Tactic` is
    -- imported (transitively via `ThetLogos.ProductTriple`) — "unknown
    -- constant". Term projection `(… _).mpr` works fine.
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hne)
  obtain ⟨u, hu⟩ := hunit
  refine ⟨endAlgEquiv.symm ((u⁻¹ : (Matrix (Fin 2) (Fin 2) ℂ)ˣ) : Matrix (Fin 2) (Fin 2) ℂ), ?_, ?_⟩
  · apply endAlgEquiv.injective
    rw [map_mul, hM, map_one, AlgEquiv.apply_symm_apply, ← hu]
    exact Units.inv_mul u
  · apply endAlgEquiv.injective
    rw [map_mul, hM, map_one, AlgEquiv.apply_symm_apply, ← hu]
    exact Units.mul_inv u

-- ============================================================================
-- §2. The resolvent is compact (T1)
-- ============================================================================

/-- The resolvent is a compact operator (Tier T1 — proved):
    finite-dimensionality is the whole proof — every endomorphism of `S`
    is compact (`end_compact`). Together with `pauliD_resolvent` this is the
    full mathematical content of `HasCompactResolvent pauliD`. -/
theorem pauliD_resolvent_compact (lam : ℂ) (h1 : lam ≠ 1) (h2 : lam ≠ -1) :
    ∃ R : Module.End ℂ (EuclideanSpace ℂ (Fin 2)),
      R * (pauliD - lam • 1) = 1 ∧ (pauliD - lam • 1) * R = 1 ∧
        IsCompactOperator (⇑(Module.End.toContinuousLinearMap _ R)) := by
  obtain ⟨R, hR1, hR2⟩ := pauliD_resolvent lam h1 h2
  exact ⟨R, hR1, hR2, end_compact _⟩

-- ============================================================================
-- §3. The named T2 window (axiom)
-- ============================================================================

/-- Compact resolvent for the Pauli Dirac (Tier T2 — model-specific axiom).

    `HasCompactResolvent` is an opaque def (`BoundedTriple.lean` §1): it
    cannot be proved, only assumed. Its mathematical content for this model
    IS proved as T1 above — `pauliD_resolvent` (the resolvent exists
    off-spectrum) and `pauliD_resolvent_compact` (it is a compact operator,
    via `end_compact`). This axiom is therefore a NAMED WINDOW whose content
    is proved: it exists solely to discharge the `hcompactRes` field of
    `BoundedAnalyticTriple` for the Pauli model. Eliminating it would
    require redefining `HasCompactResolvent` transparently in Mathlib's
    compact-operator API — a `BoundedTriple.lean` design decision, priced
    and out of scope. -/
axiom pauli_compactResolvent : HasCompactResolvent pauliD

-- ============================================================================
-- §4. The BoundedAnalyticTriple instance (T2)
-- ============================================================================

/-- The bounded analytic triple instance for the Pauli model (Tier T2 —
    instance): `hbddComm` / `hbddRep` are the proved T1s `bddComm` /
    `bddRep` from `ConcreteFiniteModel.lean`; `hcompactRes` is the named T2
    window `pauli_compactResolvent`, whose mathematical content is proved in
    `pauliD_resolvent` / `pauliD_resolvent_compact`. -/
noncomputable instance pauliBounded : BoundedAnalyticTriple where
  toAnalyticTripleData := pauliAnalytic
  hbddComm := bddComm
  hbddRep := bddRep
  hcompactRes := pauli_compactResolvent

-- ============================================================================
-- §5. Tier ledger check
-- ============================================================================

#print axioms pauliD_sub_smul_matrix
#print axioms pauliD_sub_det
#print axioms pauliD_resolvent
#print axioms pauliD_resolvent_compact
#print axioms pauli_compactResolvent
#print axioms pauliBounded

end ThetLogos
