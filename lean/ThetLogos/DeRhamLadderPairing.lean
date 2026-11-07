/-
# ThetLogos.DeRhamLadderPairing — LAD-4: spectral pairing

**WORKING LABEL — naming is Jeff's.** The SP-5 analog at each
adjacent pair of the ladder, in SP-5's two forms, landing
independently as SP-5's did:

(i) **Algebraic half — PRICED OBSTRUCTION, not landed.**
The charpoly identities for the up/down parts (at pair
(0,1), `X^60 * charpoly(Δ₀) = X^30 * charpoly(d₁ᵀ d₁)`; at
pair (1,2), `X^32 * charpoly(d₂ d₂ᵀ) = X^60 * charpoly(Δ₂)`)
should each be ONE application of Mathlib's
`Matrix.charpoly_mul_comm'` (the rectangular identity SP-5
used). At this seat they are NOT proved in this module:
every route tried in the lane (bare `exact` against the
card form, `rw`/`simp only` conversion of `Fintype.card`
in the hypothesis, goal reshaping by `unfold`/show-`rw`,
generalize-to-a-variable then apply, and
`maxRecDepth`/`maxHeartbeats` raised to 100000/4000000)
terminates in elaborator/kernel deep recursion or a `whnf`
timeout on the final definitional-equality check at index
sizes Fin 60 / Fin 32 in this Mathlib pin — while the
identical proof closes instantly at small index sizes
(Fin 2 / Fin 3 control). The identities are therefore
recorded as a priced obstruction, open: untried routes
include the `Matrix.charpoly_toLin'` operator transport
and a future Mathlib pin. NO claim is made for them here;
the geometric half below is the landed content, and it
does not depend on them.

(ii) **Geometric half** — eigenspace multiplicity matching at
every `λ ≠ 0`, per pair, by SP-5's intertwining route: `d`
maps the λ-eigenspace of the down-part across the adjacency,
`d*` maps back, inverse `λ⁻¹ • d(*)` — an explicit linear
equivalence of eigenspaces, no diagonalization anywhere.

Scoping: `derham-ladder-scoping-2026-11-06.md` §4 (LAD-4).
NO CLAIM; dials 0/4; Dial 2 = 0.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Tactic.NormNum
import ThetLogos.DeRhamLadderHodgeSeat

namespace ThetLogos
namespace DeRhamLadder

open Polynomial

/-! ## (ii) Geometric half: eigenspace intertwining

The Laplacians as endomorphisms (`Module.End`), the
intertwining identities, and the eigenspace equivalences.
An eigenspace is a kernel of `Δ − λ • 1`; the intertwining
`d ∘ (part) = (other part) ∘ d` moves eigenspaces across the
adjacency, and `λ ≠ 0` makes the round trip the identity. -/

/-- LAD-4: Δ₀ as an endomorphism of C⁰. -/
noncomputable def ladEnd0 : Module.End ℝ (Fin 30 → ℝ) := ladLap0

/-- LAD-4: the down part of Δ₁ (`d₁* d₁`) as an endomorphism
    of C¹. -/
noncomputable def ladDown1 : Module.End ℝ (Fin 60 → ℝ) :=
  ladD1Adj ∘ₗ ladD1

/-- LAD-4: the up part of Δ₁ (`d₂ d₂*`) as an endomorphism
    of C¹. -/
noncomputable def ladUp1 : Module.End ℝ (Fin 60 → ℝ) :=
  ladD2 ∘ₗ ladD2Adj

/-- LAD-4: Δ₂ as an endomorphism of C². -/
noncomputable def ladEnd2 : Module.End ℝ (Fin 32 → ℝ) := ladLap2

/-- LAD-4 (intertwining, pair (0,1)): `d₁ ∘ Δ₀ = (d₁* d₁) ∘ d₁`
    — i.e. `d₁` intertwines Δ₀ with the down part of Δ₁.
    Pure associativity of the composition. -/
theorem lad_intertwine01 : ladD1Adj ∘ₗ ladEnd0 = ladDown1 ∘ₗ ladD1Adj := by
  simp only [ladEnd0, ladDown1, ladLap0_eq]
  rw [LinearMap.comp_assoc]

/-- LAD-4 (intertwining, pair (1,2)): `d₂* ∘ (d₂ d₂*) = Δ₂ ∘ d₂*`
    — `d₂*` intertwines the up part of Δ₁ with Δ₂. -/
theorem lad_intertwine12 : ladD2Adj ∘ₗ ladUp1 = ladEnd2 ∘ₗ ladD2Adj := by
  simp only [ladEnd2, ladUp1, ladLap2_eq]
  rw [LinearMap.comp_assoc]

/-- LAD-4 (intertwining, pair (1,2), forward form):
    `(d₂ d₂*) ∘ d₂ = d₂ ∘ Δ₂` — the same associativity read
    in the direction the eigenspace helper consumes. -/
theorem lad_intertwine12' : ladUp1 ∘ₗ ladD2 = ladD2 ∘ₗ ladEnd2 := by
  simp only [ladEnd2, ladUp1, ladLap2_eq]
  rw [LinearMap.comp_assoc]

/-- LAD-4 helper: `d₁` maps the λ-eigenspace of Δ₀ into the
    λ-eigenspace of the down part of Δ₁. -/
theorem ladD1Adj_mem_eigenspace_image {lam : ℝ}
    {x : Fin 30 → ℝ} (hx : x ∈ Module.End.eigenspace ladEnd0 lam) :
    ladD1Adj x ∈ Module.End.eigenspace ladDown1 lam := by
  rw [Module.End.mem_eigenspace_iff] at hx ⊢
  have hcomp : ladDown1 (ladD1Adj x) = ladD1Adj (ladEnd0 x) := by
    have hi := LinearMap.congr_fun lad_intertwine01 x
    simpa only [LinearMap.comp_apply] using hi.symm
  rw [hcomp, hx, map_smul]

/-- LAD-4 helper: `d₁*` maps the λ-eigenspace of the down part
    of Δ₁ into the λ-eigenspace of Δ₀. -/
theorem ladD1_mem_eigenspace_image {lam : ℝ}
    {y : Fin 60 → ℝ} (hy : y ∈ Module.End.eigenspace ladDown1 lam) :
    ladD1 y ∈ Module.End.eigenspace ladEnd0 lam := by
  rw [Module.End.mem_eigenspace_iff] at hy ⊢
  have hcomp : ladEnd0 (ladD1 y) = ladD1 (ladDown1 y) := by
    show ladLap0 (ladD1 y) = ladD1 (ladDown1 y)
    rw [ladLap0_eq]
    rfl
  rw [hcomp, hy, map_smul]

/-- LAD-4 helper: `d₂` maps the λ-eigenspace of Δ₂ into the
    λ-eigenspace of the up part of Δ₁. -/
theorem ladD2_mem_eigenspace_image {lam : ℝ}
    {z : Fin 32 → ℝ} (hz : z ∈ Module.End.eigenspace ladEnd2 lam) :
    ladD2 z ∈ Module.End.eigenspace ladUp1 lam := by
  rw [Module.End.mem_eigenspace_iff] at hz ⊢
  have hcomp : ladUp1 (ladD2 z) = ladD2 (ladEnd2 z) := by
    have hi := LinearMap.congr_fun lad_intertwine12' z
    simpa only [LinearMap.comp_apply] using hi
  rw [hcomp, hz, map_smul]

/-- LAD-4 helper: `d₂*` maps the λ-eigenspace of the up part
    of Δ₁ into the λ-eigenspace of Δ₂. -/
theorem ladD2Adj_mem_eigenspace_image {lam : ℝ}
    {y : Fin 60 → ℝ} (hy : y ∈ Module.End.eigenspace ladUp1 lam) :
    ladD2Adj y ∈ Module.End.eigenspace ladEnd2 lam := by
  rw [Module.End.mem_eigenspace_iff] at hy ⊢
  have hcomp : ladEnd2 (ladD2Adj y) = ladD2Adj (ladUp1 y) := by
    have hi := LinearMap.congr_fun lad_intertwine12 y
    simpa only [LinearMap.comp_apply] using hi.symm
  rw [hcomp, hy, map_smul]

/-- LAD-4 (geometric, pair (0,1)): the eigenspace equivalence
    at every λ — `d₁` and `λ⁻¹ • d₁*` are inverse between the
    λ-eigenspaces of Δ₀ and of the down part of Δ₁. -/
noncomputable def ladEigenspaceEquiv01 (lam : ℝ) (hlam : lam ≠ 0) :
    ↥(Module.End.eigenspace ladEnd0 lam)
      ≃ₗ[ℝ] ↥(Module.End.eigenspace ladDown1 lam) where
  toFun f := ⟨ladD1Adj f.1, ladD1Adj_mem_eigenspace_image f.2⟩
  map_add' f g := by
    apply Subtype.ext
    show ladD1Adj (f.1 + g.1) = ladD1Adj f.1 + ladD1Adj g.1
    exact map_add _ _ _
  map_smul' r f := by
    apply Subtype.ext
    show ladD1Adj (r • f.1) = r • ladD1Adj f.1
    exact map_smul _ _ _
  invFun g := ⟨lam⁻¹ • ladD1 g.1,
    Submodule.smul_mem _ _ (ladD1_mem_eigenspace_image g.2)⟩
  left_inv f := by
    apply Subtype.ext
    have hf : ladEnd0 f.1 = lam • f.1 :=
      Module.End.mem_eigenspace_iff.mp f.2
    show lam⁻¹ • ladD1 (ladD1Adj f.1) = f.1
    have h2 : ladD1 (ladD1Adj f.1) = ladEnd0 f.1 := by
      show ladD1 (ladD1Adj f.1) = ladLap0 f.1
      rw [ladLap0_eq]
      rfl
    rw [h2, hf, smul_smul, inv_mul_cancel₀ hlam, one_smul]
  right_inv g := by
    apply Subtype.ext
    have hg : ladDown1 g.1 = lam • g.1 :=
      Module.End.mem_eigenspace_iff.mp g.2
    show ladD1Adj (lam⁻¹ • ladD1 g.1) = g.1
    rw [map_smul]
    have h2 : ladD1Adj (ladD1 g.1) = ladDown1 g.1 := by
      show ladD1Adj (ladD1 g.1) = (ladD1Adj ∘ₗ ladD1) g.1
      rfl
    rw [h2, hg, smul_smul, inv_mul_cancel₀ hlam, one_smul]

/-- LAD-4 (geometric, pair (1,2)): the eigenspace equivalence
    at every λ — `d₂` and `λ⁻¹ • d₂*` are inverse between the
    λ-eigenspaces of Δ₂ and of the up part of Δ₁. -/
noncomputable def ladEigenspaceEquiv12 (lam : ℝ) (hlam : lam ≠ 0) :
    ↥(Module.End.eigenspace ladEnd2 lam)
      ≃ₗ[ℝ] ↥(Module.End.eigenspace ladUp1 lam) where
  toFun f := ⟨ladD2 f.1, ladD2_mem_eigenspace_image f.2⟩
  map_add' f g := by
    apply Subtype.ext
    show ladD2 (f.1 + g.1) = ladD2 f.1 + ladD2 g.1
    exact map_add _ _ _
  map_smul' r f := by
    apply Subtype.ext
    show ladD2 (r • f.1) = r • ladD2 f.1
    exact map_smul _ _ _
  invFun g := ⟨lam⁻¹ • ladD2Adj g.1,
    Submodule.smul_mem _ _ (ladD2Adj_mem_eigenspace_image g.2)⟩
  left_inv f := by
    apply Subtype.ext
    have hf : ladEnd2 f.1 = lam • f.1 :=
      Module.End.mem_eigenspace_iff.mp f.2
    show lam⁻¹ • ladD2Adj (ladD2 f.1) = f.1
    have h2 : ladD2Adj (ladD2 f.1) = ladEnd2 f.1 := by
      show ladD2Adj (ladD2 f.1) = ladLap2 f.1
      rw [ladLap2_eq]
      rfl
    rw [h2, hf, smul_smul, inv_mul_cancel₀ hlam, one_smul]
  right_inv g := by
    apply Subtype.ext
    have hg : ladUp1 g.1 = lam • g.1 :=
      Module.End.mem_eigenspace_iff.mp g.2
    show ladD2 (lam⁻¹ • ladD2Adj g.1) = g.1
    rw [map_smul]
    have h2 : ladD2 (ladD2Adj g.1) = ladUp1 g.1 := by
      show ladD2 (ladD2Adj g.1) = (ladD2 ∘ₗ ladD2Adj) g.1
      rfl
    rw [h2, hg, smul_smul, inv_mul_cancel₀ hlam, one_smul]

/-- LAD-4 (geometric, pair (0,1)): **geometric multiplicities
    agree at every λ ≠ 0** — the nonzero spectra of Δ₀ and of
    the down part of Δ₁ coincide with multiplicities. -/
theorem lad_finrank_eigenspace01 {lam : ℝ} (hlam : lam ≠ 0) :
    Module.finrank ℝ ↥(Module.End.eigenspace ladEnd0 lam)
      = Module.finrank ℝ ↥(Module.End.eigenspace ladDown1 lam) :=
  LinearEquiv.finrank_eq (ladEigenspaceEquiv01 lam hlam)

/-- LAD-4 (geometric, pair (1,2)): **geometric multiplicities
    agree at every λ ≠ 0** — the nonzero spectra of Δ₂ and of
    the up part of Δ₁ coincide with multiplicities. -/
theorem lad_finrank_eigenspace12 {lam : ℝ} (hlam : lam ≠ 0) :
    Module.finrank ℝ ↥(Module.End.eigenspace ladEnd2 lam)
      = Module.finrank ℝ ↥(Module.End.eigenspace ladUp1 lam) :=
  LinearEquiv.finrank_eq (ladEigenspaceEquiv12 lam hlam)

end DeRhamLadder
end ThetLogos
