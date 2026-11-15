import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

/-!
# ThetIdentity — T01–T05: Thet identity and operator foundations

External draft ("ACMD Lean 4 — Thet Identity Development", dropped
2026-11-12) formalized in-tree at Zero's commission ("review scope
and build", 2026-11-12). Scope of record:
`your_files/thet-identity-development-scope-2026-11-12.md`.

What this module is, at its true grade:

* T01–T02 are DEFINITIONAL. `ThetIdentity x t` is `x = t ∧ t = x` —
  `Eq` restated under a name (a Register-A definition; the name is
  Zero's to give). Its theorems are Eq's own reflexivity, symmetry
  and transitivity wearing the label. Recorded trivial: no content
  is claimed for them beyond the definition itself. Tet is the name
  of the equality, never the value.
* T03–T05 are STANDARD partial-isometry algebra for complex
  matrices: from `θ * star θ * θ = θ`, the second Moore–Penrose
  identity and the idempotence and self-adjointness of the initial
  and final projections follow. First-page partial-isometry theory;
  not new mathematics.
* NO physical interpretation is asserted for any of it. NO CLAIM.
* T06 (finite spectral realization) is NOT addressed by this
  module: the draft's §4 integration targets were audited and found
  absent from this tree (scope §3); a real T06 is a separate seat.
-/

namespace ThetLogos
namespace ThetIdentity

/-! ## T01: Symbolic identity -/

/-- Thet-centered two-sided identity: `x = t ∧ t = x`.
`Eq` restated under a name — a definition, not a result. -/
def ThetIdentity {α : Type*} (x t : α) : Prop :=
  x = t ∧ t = x

theorem identity_reflexive {α : Type*} (x : α) :
    ThetIdentity x x := by
  constructor <;> rfl

theorem identity_iff {α : Type*} (x t : α) :
    ThetIdentity x t ↔ x = t := by
  constructor
  · intro h
    exact h.1
  · intro h
    exact ⟨h, h.symm⟩

theorem identity_symmetric {α : Type*}
    (x t : α) (h : ThetIdentity x t) :
    ThetIdentity t x := by
  exact ⟨h.2, h.1⟩

/-! ## T02: Equality as an equivalence relation -/

theorem equality_equivalence (α : Type*) :
    Equivalence (@Eq α) := by
  constructor
  · intro x
    rfl
  · intro x y h
    exact h.symm
  · intro x y z h₁ h₂
    exact h₁.trans h₂

/-! ## T03: Partial-isometry realization -/

/-- Partial-isometry defining relation for complex matrices, using
the Hilbert-space adjoint (`star` on matrices is the conjugate
transpose). -/
def IsPartialIsometry {n : Type*}
    [Fintype n] [DecidableEq n]
    (θ : Matrix n n ℂ) : Prop :=
  θ * star θ * θ = θ

/-! ## T04: Moore–Penrose identities -/

/-- The second Moore–Penrose identity, obtained from the defining
relation by applying `star` to both sides. -/
theorem mp_second {n : Type*}
    [Fintype n] [DecidableEq n]
    (θ : Matrix n n ℂ)
    (h : IsPartialIsometry θ) :
    star θ * θ * star θ = star θ := by
  simpa only [star_mul, star_star, mul_assoc] using
    congrArg star h

/-- The first two Moore–Penrose identities for a pair `(θ, δ)`. -/
def MoorePenrosePair {n : Type*}
    [Fintype n] [DecidableEq n]
    (θ δ : Matrix n n ℂ) : Prop :=
  θ * δ * θ = θ ∧
  δ * θ * δ = δ

theorem partial_isometry_moore_penrose
    {n : Type*} [Fintype n] [DecidableEq n]
    (θ : Matrix n n ℂ)
    (h : IsPartialIsometry θ) :
    MoorePenrosePair θ (star θ) := by
  exact ⟨h, mp_second θ h⟩

/-! ## T05: Initial and final projections -/

/-- The final projection `θ θ*`. -/
def finalProjection {n : Type*}
    [Fintype n] [DecidableEq n]
    (θ : Matrix n n ℂ) :=
  θ * star θ

/-- The initial projection `θ* θ`. -/
def initialProjection {n : Type*}
    [Fintype n] [DecidableEq n]
    (θ : Matrix n n ℂ) :=
  star θ * θ

theorem final_projection_idempotent
    {n : Type*} [Fintype n] [DecidableEq n]
    (θ : Matrix n n ℂ)
    (h : IsPartialIsometry θ) :
    finalProjection θ * finalProjection θ =
      finalProjection θ := by
  unfold finalProjection
  calc
    (θ * star θ) * (θ * star θ) =
        (θ * star θ * θ) * star θ := by
          simp only [mul_assoc]
    _ = θ * star θ := by rw [h]

theorem initial_projection_idempotent
    {n : Type*} [Fintype n] [DecidableEq n]
    (θ : Matrix n n ℂ)
    (h : IsPartialIsometry θ) :
    initialProjection θ * initialProjection θ =
      initialProjection θ := by
  unfold initialProjection
  calc
    (star θ * θ) * (star θ * θ) =
        star θ * (θ * star θ * θ) := by
          simp only [mul_assoc]
    _ = star θ * θ := by rw [h]

theorem final_projection_self_adjoint
    {n : Type*} [Fintype n] [DecidableEq n]
    (θ : Matrix n n ℂ) :
    star (finalProjection θ) =
      finalProjection θ := by
  simp [finalProjection, star_mul]

theorem initial_projection_self_adjoint
    {n : Type*} [Fintype n] [DecidableEq n]
    (θ : Matrix n n ℂ) :
    star (initialProjection θ) =
      initialProjection θ := by
  simp [initialProjection, star_mul]

end ThetIdentity
end ThetLogos
