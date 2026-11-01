import Mathlib.Tactic
import Mathlib.LinearAlgebra.Dimension.Finrank
import ThetLogos.MaxwellQuadPost

namespace ThetLogos

open Finset

/-!
# ThetLogos.MaxwellQuadWeld - MAX-1: the weld + the atom

**Status: MAX-1 landing brick. NO CLAIM. No Millennium
statement, no ladder rung, no dial (dials stay 0/4).**
Governing texts: the MAX-0 pin `MaxwellQuadPost.lean` (its
registered names and its registered M4 form govern) and the
scoping memo `scoping-maxwell-finite-2026-10-31.md` sections
3 and 5.

Two contents, both discharged here:

1. **The weld.** At `G = Circle`, the additive plaquette
angle `plaqAngle` is the additive shadow of the owned
multiplicative holonomy `PlaqHol`: for every plaquette datum
`P` and every link angle `theta`,
`PlaqHol P (fun l => Circle.exp (theta l))
  = Circle.exp (plaqAngle P theta)`.
The exponential map used is Mathlib's `Circle.exp`
(the landed Circle vocabulary; home:
`Mathlib/Analysis/Complex/Circle.lean`, with
`Circle.exp_add` and `Circle.exp_neg`).

2. **The atom (M4), discharged exactly as registered in the
pin.** The single-plaquette operator `maxwellAtomOp` on the
four edge values in (B, R, T, L) order is rank one with
spectrum exactly {4, 0, 0, 0}: eigenvalue 4 with named
eigenvector `atomVec = (1, 1, -1, -1)`, eigenvalue 0, no
other eigenvalue, kernel `{x | x 0 + x 1 = x 2 + x 3}` of
finrank 3, and Rayleigh form
`sum i, x i * (maxwellAtomOp x) i = (plaqPattern x)^2`.

## Fences (memo section 5, K-MAX-2)

Finite in every statement: the atom is a property of a
chosen finite operator at spacing 1; not a derived measured
number, not a gravity object, not a continuum statement.
FENCE SENTENCE: the words "Lorentzian" and "bridge" are not
earned terms in this line and appear in this module only
inside fence text. Disjoint from OP-1's photon (the massless
Higgs-sector direction) - no trading between the two senses.
Not `magLin` (vertex potentials, matter side): this operator
lives on the connection's own tangent space (link angles),
the gauge-field side, and the atom lives on the four edge
values of one plaquette.

## K-MAX-1 re-check (on the face)

`maxwellAtomOp` is defined in the pin by its own component
formula `(maxwellAtomOp x) i = plaqPattern x * atomVec i` on
`Fin 4 -> R`; it is not definitionally the transfer
operator, the plaquette block/factor, `magLin`, or the
vertex `lapLin`, none of which has this type or this
component formula.
-/

section Weld

/-- **The weld (MAX-1, content 1).** At `G = Circle`, the
plaquette holonomy of the exponential of a link angle is
the exponential of the plaquette angle:
`PlaqHol P (fun l => Circle.exp (theta l))
  = Circle.exp (plaqAngle P theta)`. -/
theorem plaqHol_circle_exp_weld {N : ℕ} [NeZero N]
    (P : PlaqDatum N) (θ : linkAngle N) :
    PlaqHol P (fun ℓ => Circle.exp (θ ℓ))
      = Circle.exp (plaqAngle P θ) := by
  unfold PlaqHol plaqAngle
  rw [← Circle.exp_neg, ← Circle.exp_neg,
    ← Circle.exp_add, ← Circle.exp_add, ← Circle.exp_add]
  simp only [sub_eq_add_neg]

end Weld

section Atom

/-- The plaquette pattern of the atom vector:
`plaqPattern atomVec = 4`. -/
theorem plaqPattern_atomVec : plaqPattern atomVec = 4 := by
  norm_num [plaqPattern, atomVec]

/-- The atom vector is nonzero (its B-coordinate is 1). -/
theorem atomVec_ne_zero : atomVec ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  simp [atomVec] at h0

/-- Component formula for the atom operator (the rank-one
form of M4, pointwise form):
`(maxwellAtomOp x) i = plaqPattern x * atomVec i`. -/
theorem maxwellAtomOp_apply (x : Fin 4 → ℝ) (i : Fin 4) :
    (maxwellAtomOp x) i = plaqPattern x * atomVec i := rfl

/-- **(M4, rank-one form).** `maxwellAtomOp x
= plaqPattern x • atomVec` for every `x`. -/
theorem maxwellAtomOp_eq_smul (x : Fin 4 → ℝ) :
    maxwellAtomOp x = plaqPattern x • atomVec := by
  funext i
  rw [maxwellAtomOp_apply]
  simp [Pi.smul_apply, smul_eq_mul]

/-- **(M4, eigenvalue 4).** `atomVec` is an eigenvector of
`maxwellAtomOp` with eigenvalue `4`. -/
theorem maxwellAtomOp_atomVec :
    maxwellAtomOp atomVec = (4 : ℝ) • atomVec := by
  funext i
  rw [maxwellAtomOp_apply, plaqPattern_atomVec]
  simp [Pi.smul_apply]

/-- **(M4) `HasEigenvalue maxwellAtomOp 4`.** -/
theorem maxwellAtomOp_hasEigenvalue_four :
    Module.End.HasEigenvalue maxwellAtomOp 4 :=
  Module.End.hasEigenvalue_of_hasEigenvector
    (f := maxwellAtomOp) (μ := 4) (x := atomVec)
    ⟨Module.End.mem_eigenspace_iff.mpr maxwellAtomOp_atomVec,
      atomVec_ne_zero⟩

/-- A kernel witness for eigenvalue 0: the edge values
`(1, 0, 1, 0)` have plaquette pattern `0`. -/
theorem plaqPattern_kernel_witness :
    plaqPattern ![1, 0, 1, 0] = 0 := by
  norm_num [plaqPattern]

/-- **(M4) `HasEigenvalue maxwellAtomOp 0`.** -/
theorem maxwellAtomOp_hasEigenvalue_zero :
    Module.End.HasEigenvalue maxwellAtomOp 0 := by
  apply Module.End.hasEigenvalue_of_hasEigenvector
    (f := maxwellAtomOp) (μ := 0) (x := ![1, 0, 1, 0])
  constructor
  · rw [Module.End.mem_eigenspace_iff]
    funext i
    rw [maxwellAtomOp_apply, plaqPattern_kernel_witness]
    simp
  · intro h
    have h0 := congrFun h 0
    simp at h0

/-- **(M4, kernel characterization).**
`maxwellAtomOp x = 0` iff `x 0 + x 1 = x 2 + x 3`. -/
theorem maxwellAtomOp_eq_zero_iff (x : Fin 4 → ℝ) :
    maxwellAtomOp x = 0 ↔ x 0 + x 1 = x 2 + x 3 := by
  constructor
  · intro h
    have h0 := congrFun h 0
    rw [maxwellAtomOp_apply] at h0
    have hpat : plaqPattern x = 0 := by
      have hv : atomVec 0 = 1 := rfl
      rw [hv, mul_one] at h0
      exact h0
    unfold plaqPattern at hpat
    linarith
  · intro h
    have hpat : plaqPattern x = 0 := by
      unfold plaqPattern
      linarith
    funext i
    rw [maxwellAtomOp_apply, hpat]
    simp

/-- **(M4, no other eigenvalue).** Every eigenvalue of
`maxwellAtomOp` is `4` or `0`. -/
theorem maxwellAtomOp_eigenvalue_eq (μ : ℝ)
    (hμ : Module.End.HasEigenvalue maxwellAtomOp μ) :
    μ = 4 ∨ μ = 0 := by
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  have happly : maxwellAtomOp v = μ • v := hv.apply_eq_smul
  have ei : ∀ i : Fin 4,
      plaqPattern v * atomVec i = μ * v i := by
    intro i
    have hi := congrFun happly i
    rw [maxwellAtomOp_apply] at hi
    simpa [Pi.smul_apply, smul_eq_mul] using hi
  have e0 := ei 0
  have e1 := ei 1
  have e2 := ei 2
  have e3 := ei 3
  have hv0 : atomVec 0 = 1 := rfl
  have hv1 : atomVec 1 = 1 := rfl
  have hv2 : atomVec 2 = -1 := rfl
  have hv3 : atomVec 3 = -1 := rfl
  rw [hv0] at e0
  rw [hv1] at e1
  rw [hv2] at e2
  rw [hv3] at e3
  have hμp : μ * plaqPattern v = 4 * plaqPattern v := by
    have key : μ * plaqPattern v
        = μ * v 0 + μ * v 1 - μ * v 2 - μ * v 3 := by
      unfold plaqPattern
      ring
    rw [key]
    linarith
  by_cases hp : plaqPattern v = 0
  · right
    obtain ⟨i, hi⟩ : ∃ i : Fin 4, v i ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hv.2 (funext hc)
    have hμi : μ * v i = 0 := by
      have h2 := ei i
      rw [hp] at h2
      simpa using h2.symm
    exact (mul_eq_zero.mp hμi).resolve_right hi
  · left
    have hfac : (μ - 4) * plaqPattern v = 0 := by
      rw [sub_mul, sub_eq_zero]
      exact hμp
    rcases mul_eq_zero.mp hfac with h | h
    · linarith
    · exact absurd h hp

/-- **(M4, Rayleigh form).**
`sum i, x i * (maxwellAtomOp x) i = (plaqPattern x)^2`. -/
theorem maxwellAtomOp_rayleigh (x : Fin 4 → ℝ) :
    (∑ i, x i * (maxwellAtomOp x) i) = (plaqPattern x) ^ 2 := by
  rw [Fin.sum_univ_four]
  rw [maxwellAtomOp_apply, maxwellAtomOp_apply,
    maxwellAtomOp_apply, maxwellAtomOp_apply]
  have hv0 : atomVec 0 = 1 := rfl
  have hv1 : atomVec 1 = 1 := rfl
  have hv2 : atomVec 2 = -1 := rfl
  have hv3 : atomVec 3 = -1 := rfl
  rw [hv0, hv1, hv2, hv3]
  unfold plaqPattern
  ring

/-- The range of the atom operator is the span of
`atomVec` (rank one, in submodule form). -/
theorem maxwellAtomOp_range :
    LinearMap.range maxwellAtomOp = ℝ ∙ atomVec := by
  apply le_antisymm
  · rintro y ⟨x, rfl⟩
    rw [maxwellAtomOp_eq_smul]
    exact Submodule.smul_mem _ _
      (Submodule.mem_span_singleton_self atomVec)
  · rw [Submodule.span_le]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    refine ⟨![1, 0, 0, 0], ?_⟩
    funext i
    rw [maxwellAtomOp_apply]
    have hp : plaqPattern ![1, 0, 0, 0] = 1 := by
      norm_num [plaqPattern]
    rw [hp, one_mul]

/-- **(M4, kernel finrank).**
`Module.finrank R (LinearMap.ker maxwellAtomOp) = 3`. -/
theorem maxwellAtomOp_finrank_ker :
    Module.finrank ℝ (LinearMap.ker maxwellAtomOp) = 3 := by
  have hrn := LinearMap.finrank_range_add_finrank_ker
    maxwellAtomOp
  rw [maxwellAtomOp_range,
    finrank_span_singleton atomVec_ne_zero] at hrn
  rw [Module.finrank_pi] at hrn
  simp only [Fintype.card_fin] at hrn
  omega

/-- **(M4) The single-plaquette atom, discharged exactly as
registered in the MAX-0 pin (`maxwellM4`).** -/
theorem maxwellM4_proved : maxwellM4 :=
  ⟨maxwellAtomOp_eq_smul,
    maxwellAtomOp_hasEigenvalue_four,
    maxwellAtomOp_hasEigenvalue_zero,
    maxwellAtomOp_eigenvalue_eq,
    maxwellAtomOp_eq_zero_iff,
    maxwellAtomOp_finrank_ker,
    maxwellAtomOp_rayleigh⟩

end Atom

end ThetLogos
