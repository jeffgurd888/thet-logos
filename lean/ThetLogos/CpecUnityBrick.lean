import Mathlib.Tactic
import ThetLogos.DiracTorsionMap
import ThetLogos.ThreeGen
import ThetLogos.CpecJSeatTorsion

open Matrix Finset
open scoped Kronecker

namespace ThetLogos

/-!
# ThetLogos.CpecUnityBrick - CPEC-CC-2: the triplication seat

**Working label only.** The module name `CpecUnityBrick` and
the brick name CPEC-CC-2 are working labels; Jeff names.
Jeff's name for this brick, recorded on the dossier, is
"the unity brick" (Jeff, 2026-11-01). That name is his
coinage for the brick; it is not a claim about what the
brick proves, and no sentence below spends it as one.

**Status: BUILT for parent landing - the triplicated seats
are DECIDED below. NO CLAIM. No gravity object is defined,
constructed, or asserted to exist. Dial 2 = 0, dials 0/4.**

Governing texts: the pack
`routeb-general-scratch/pack-cpec-cc-2.md`, the frozen pin
`CpecBridgePost` (CPEC-0, commit 35d5d6e; its registered
remainder `cc2TriplicationFired` is the fired remainder this
brick discharges, and its names are cited, never renamed),
the governing scoping
`routeb-general-scratch/scoping-cpec-bridge-2026-10-31.md`
sections 3 and 8 (the R3 remainder), and the home module
`DiracTorsionMap`, whose seat discipline this module
transports. Gates, all cleared on the record before this
build: the CPEC-0 pin landed, CC-1 (CpecJSeatTorsion)
landed its seat verdict, and the `DiracTorsionMap` direct
axiom sweep completed BAD = 0.

## What this brick is

`DiracTorsionMap` built the torsion map at two seats of
EdgeSignature's defect law and named triplication as its
remainder R3: the torsion map carried to
`smDirac3diag = D1 ⊗ I3` (ThreeGen). This module builds it.

- **The triplicated defect law.** The defect at the
  96-dimensional seat is the same formula,
  `defect3 eta T = eta * T + T * eta + T * T`, and the
  triplication `trip` (the explicit `⊗ I3` leg, entrywise
  `M i j * (if g = gp then 1 else 0)`) is a ring
  homomorphism (`trip_add`, `trip_mul`, `trip_one`), so the
  defect transports exactly: `defect3 (trip eta) (trip T)
  = trip (defect eta T)` (`defect3_trip`), entrywise the
  Kronecker form `defect3_trip_apply`.

- **Seat verdicts transported.** Grading seat: the defect
  of the zero correction at `gamma3` vanishes and
  grading-oddness inherits under triplication
  (`grading_seat_survival3`, by ThreeGen's
  `smDirac3diag_grading_odd`). Sign seat: the triplicated
  Majorana obstruction entry is computed entrywise at
  C96 (`defect3_majorana_entry`): at generation-diagonal
  entries `((0, g), (24, g))` it is `(y)^-1 * star s`, and
  off the generation diagonal it is `0`; survival at the
  triplicated seat holds exactly at `s = 0`
  (`majorana_survival3_iff`), the landed
  `majorana_survival_iff` read through the triplication.
  The J seat of CC-1 conforms the same way
  (`j_seat_defect3_entry`): its entry is the CC-1 closed
  form on the generation diagonal, zero off it.

## THE FENCE (on the face, verbatim-grade)

This brick concerns the torsion map's behavior ON the
triplicated space. It does NOT derive triplication. The
three-generation factor is IMPOSED data - the explicit
`⊗ I3` leg carried in every definition below, in
ThreeGen's own fence - not a theorem: no statement here
derives why three generations exist, no flavour quantity
is derived, **Q3 stays OPEN**, flavour stays an input, no
dial moves, NO CLAIM. The factor `3` enters as the index
type `Fin 3` of `I96 = I32 × Fin 3`, given, never proved.
-/

-- ============================================================================
-- Section 0. Triplication as explicit data: the ⊗ I3 leg
-- ============================================================================

/-- **Triplication** (Tier T2 definition): the
    flavour-diagonal triplication of a one-generation
    matrix, `M ↦ M ⊗ I3` in entry form. The generation
    factor `Fin 3` is carried here as explicit index data
    of `I96 = I32 × Fin 3`; nothing in this definition
    selects or derives it. This is `smDirac3diag` in
    general form: `smDirac3diag_eq_trip` identifies the
    two. -/
def trip (M : Matrix I32 I32 ℂ) : Matrix I96 I96 ℂ :=
  fun (i, g) (j, gp) => M i j * if g = gp then (1 : ℂ) else 0

/-- Triplication is the Kronecker product with the
    generation identity (T1 target): the explicit `⊗ I3`
    leg, in the exact form ThreeGen registers. -/
theorem trip_eq_kronecker (M : Matrix I32 I32 ℂ) :
    trip M = M ⊗ₖ (1 : Matrix (Fin 3) (Fin 3) ℂ) := by
  ext ⟨i, g⟩ ⟨j, gp⟩
  unfold trip
  rw [Matrix.kronecker_apply, Matrix.one_apply]

/-- Triplication preserves addition (T1 target). -/
theorem trip_add (M N : Matrix I32 I32 ℂ) :
    trip (M + N) = trip M + trip N := by
  simp only [trip_eq_kronecker, Matrix.add_kronecker]

/-- Triplication preserves multiplication (T1 target). -/
theorem trip_mul (M N : Matrix I32 I32 ℂ) :
    trip (M * N) = trip M * trip N := by
  rw [trip_eq_kronecker, trip_eq_kronecker, trip_eq_kronecker,
    ← Matrix.mul_kronecker_mul, mul_one]

/-- Triplication preserves the identity (T1 target). -/
theorem trip_one : trip (1 : Matrix I32 I32 ℂ) = 1 := by
  rw [trip_eq_kronecker, Matrix.one_kronecker_one]

/-- Triplication is injective at zero (T1 target): a
    triplicated matrix vanishes exactly when the base
    matrix does, read off at generation `0`. -/
theorem trip_eq_zero (M : Matrix I32 I32 ℂ) :
    trip M = 0 ↔ M = 0 := by
  constructor
  · intro h
    ext i j
    have h2 := congrArg
      (fun X : Matrix I96 I96 ℂ =>
        X (i, ⟨0, by norm_num⟩) (j, ⟨0, by norm_num⟩)) h
    simpa [trip] using h2
  · intro h
    rw [h]
    ext ⟨i, g⟩ ⟨j, gp⟩
    simp [trip]

/-- The triplicated Dirac is the triplication of the
    one-generation Dirac (T1 target): `smDirac3diag` is
    `trip` at a Dirac operator, by definition. -/
theorem smDirac3diag_eq_trip (D1 : Matrix I32 I32 ℂ) :
    smDirac3diag D1 = trip D1 :=
  rfl

-- ============================================================================
-- Section 1. The triplicated defect, and its transport law
-- ============================================================================

/-- **The defect at the triplicated seat** (Tier T2
    definition): EdgeSignature's defect formula
    `eta * T + T * eta + T * T`, at `Matrix I96 I96 ℂ`.
    The same law, the larger arena; no connection is
    involved, in the home module's fenced sense. -/
def defect3 (η T : Matrix I96 I96 ℂ) : Matrix I96 I96 ℂ :=
  η * T + T * η + T * T

/-- **The defect-transport identity** (T1 target): the
    defect of triplicated data is the triplication of the
    defect. The defect law is entrywise and tensorial, so
    it passes through the `⊗ I3` leg unchanged. -/
theorem defect3_trip (η T : Matrix I32 I32 ℂ) :
    defect3 (trip η) (trip T) = trip (defect η T) := by
  unfold defect3 defect
  rw [← trip_mul, ← trip_mul, ← trip_mul, ← trip_add, ← trip_add]

/-- **The defect-transport identity, entrywise** (T1
    target): the Kronecker form of the defect at the
    triplicated seat - the base defect entry on the
    generation diagonal, zero off it. -/
theorem defect3_trip_apply (η T : Matrix I32 I32 ℂ)
    (i : I32) (g : Fin 3) (j : I32) (gp : Fin 3) :
    defect3 (trip η) (trip T) (i, g) (j, gp)
      = defect η T i j * (if g = gp then (1 : ℂ) else 0) := by
  rw [defect3_trip]
  rfl

-- ============================================================================
-- Section 2. The triplicated sign seat
-- ============================================================================

/-- **The triplicated sign** (Tier T2 definition): the
    sign seat's operator carried to the triplicated space
    by the explicit `⊗ I3` leg. -/
noncomputable def etaSign3 (y : ℝ) : Matrix I96 I96 ℂ :=
  trip (etaSign y)

/-- **The triplicated Majorana correction** (Tier T2
    definition): the sign seat's Majorana correction
    carried to the triplicated space by the same leg. -/
noncomputable def torsionMajorana3 (y : ℝ) (s : ℂ) : Matrix I96 I96 ℂ :=
  trip (torsionMajorana y s)

/-- The triplicated sign is an involution (T1 target),
    from the base involution through the triplication. -/
theorem etaSign3_sq (y : ℝ) (hy : y ≠ 0) :
    etaSign3 y * etaSign3 y = 1 := by
  unfold etaSign3
  rw [← trip_mul, etaSign_sq y hy, trip_one]

/-- **R2 - the triplicated sign-seat defect entry,
    computed entrywise** (T1 target): at the triplicated
    witness entry `((0, g), (24, g))` - the (ν_L, ν̄_R)
    corner of generation `g` - the defect is the landed
    base value `(↑y)⁻¹ * star s`; at off-diagonal
    generation pairs `g ≠ gp` it is `0`. This is
    `defect_entry` read through the Kronecker form
    `defect3_trip_apply`, computed, not assumed. -/
theorem defect3_majorana_entry (y : ℝ) (hy : y ≠ 0) (s : ℂ)
    (g gp : Fin 3) :
    defect3 (etaSign3 y) (torsionMajorana3 y s)
        (⟨0, by norm_num⟩, g) (⟨24, by norm_num⟩, gp)
      = if g = gp then (↑y)⁻¹ * star s else 0 := by
  have h := defect3_trip_apply (etaSign y) (torsionMajorana y s)
    ⟨0, by norm_num⟩ g ⟨24, by norm_num⟩ gp
  rw [defect_entry y hy s] at h
  by_cases hgg : g = gp
  · rw [if_pos hgg]
    rw [if_pos hgg, mul_one] at h
    exact h
  · rw [if_neg hgg]
    rw [if_neg hgg, mul_zero] at h
    exact h

/-- **R3 - the triplicated survival read-back** (T1
    target): the triplicated deformed sign
    `etaSign3 y + torsionMajorana3 y s` is a fundamental
    symmetry if and only if `s = 0` - the landed
    `majorana_survival_iff` transported through the
    triplication, with the same verdict and the same
    witness. The triplication adds generations; it adds
    no new flat point. -/
theorem majorana_survival3_iff (y : ℝ) (hy : y ≠ 0) (s : ℂ) :
    (etaSign3 y + torsionMajorana3 y s)
        * (etaSign3 y + torsionMajorana3 y s) = 1
      ↔ s = 0 := by
  have hflat : (etaSign3 y + torsionMajorana3 y s)
        * (etaSign3 y + torsionMajorana3 y s) = 1
      ↔ defect3 (etaSign3 y) (torsionMajorana3 y s) = 0 :=
    torsion_flat_iff _ _ (etaSign3_sq y hy)
  rw [hflat]
  show defect3 (trip (etaSign y)) (trip (torsionMajorana y s)) = 0
    ↔ s = 0
  rw [defect3_trip, trip_eq_zero]
  exact (dirac_torsion_flat_iff _ _ (etaSign_sq y hy)).symm.trans
    (majorana_survival_iff y hy s)

-- ============================================================================
-- Section 3. The triplicated grading seat, and CC-1 conformance
-- ============================================================================

/-- **The grading seat, transported** (T1 target):
    SURVIVAL. The defect of the zero correction at the
    triplicated grading `gamma3` vanishes, and every
    γ-odd one-generation Dirac operator triplicates to a
    γ₃-odd operator - the grading seat's invariance,
    carried through the `⊗ I3` leg by ThreeGen's
    `smDirac3diag_grading_odd`. -/
theorem grading_seat_survival3 :
    defect3 gamma3 0 = 0 ∧ ∀ D : Matrix I32 I32 ℂ,
      gammaF * D + D * gammaF = 0 →
      gamma3 * smDirac3diag D + smDirac3diag D * gamma3 = 0 :=
  ⟨by simp [defect3], fun D hD => smDirac3diag_grading_odd D hD⟩

/-- **CC-1 conformance at the triplicated seat** (T1
    target): the J seat's imported Majorana defect, read
    through the triplication - the CC-1 closed form
    `(↑y)⁻¹ * (s + star s)
      + (↑y)⁻¹ * (↑y)⁻¹ * (s * star s)` at the
    generation-diagonal partner-pair entry `((8, g),
    (8, g))`, zero off the generation diagonal. The J
    seat's verdict is a property of the seat, not of the
    generation count. -/
theorem j_seat_defect3_entry (y : ℝ) (s : ℂ) (g gp : Fin 3) :
    defect3 UJ3 (torsionMajorana3 y s)
        (⟨8, by norm_num⟩, g) (⟨8, by norm_num⟩, gp)
      = if g = gp then (↑y)⁻¹ * (s + star s)
          + (↑y)⁻¹ * (↑y)⁻¹ * (s * star s)
        else 0 := by
  have h := defect3_trip_apply UJ (torsionMajorana y s)
    ⟨8, by norm_num⟩ g ⟨8, by norm_num⟩ gp
  have hj := j_majorana_defect_apply y s
    ⟨8, by norm_num⟩ ⟨8, by norm_num⟩
  rw [if_pos (Or.inl ⟨rfl, rfl⟩)] at hj
  rw [hj] at h
  by_cases hgg : g = gp
  · rw [if_pos hgg]
    rw [if_pos hgg, mul_one] at h
    exact h
  · rw [if_neg hgg]
    rw [if_neg hgg, mul_zero] at h
    exact h

end ThetLogos
