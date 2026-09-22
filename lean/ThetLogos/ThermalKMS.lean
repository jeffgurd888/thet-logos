import Mathlib.Data.Matrix.Mul
import Mathlib.Basic.Complex.Basic
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Tactic
import ThetLogos.Scaffold32

/-!
# ThetLogos.ThermalKMS — modular flow and partition trace (Tiers T2/T3)

After: Gurd, *The Ontological Thet–LOGOS Framework* (Revised Draft, Nexus
Research, Sept 2026), §2.1.4.

Definitions are Tier T2; flow properties are Tier T3 (numerically checked
in `python/thet_logos/modular_flow.py`; `spectralGap_pos` proven in Lean,
remaining Lean proofs pending).

The relation K = −log ρ is documented in `spectral/modular-flow.md`; here
the flow is carried as an abstract one-parameter group satisfying the
group law, which is all the statements below need.
-/

open Matrix

namespace ThetLogos

/-- Modular data: a Hermitian modular Hamiltonian K (K = −log ρ in the
    finite-dimensional model) and its flow σ_s, satisfying the one-parameter
    group law. Tier T2. -/
structure ModularData where
  K : Matrix I32 I32 ℂ
  K_hermitian : K.conjTranspose = K
  flow : ℝ → Matrix I32 I32 ℂ → Matrix I32 I32 ℂ
  flow_add : ∀ (s t : ℝ) (A : Matrix I32 I32 ℂ),
    flow (s + t) A = flow s (flow t A)

/-- Spectral gap Δ = min positive eigenvalue of a Hermitian D.
    Tier T2 (definition); numerical evaluation is Tier T3. -/
noncomputable def spectralGap {n : ℕ} (D : Matrix (Fin n) (Fin n) ℂ)
    (hD : D.IsHermitian) : ℝ :=
  sInf { r : ℝ | 0 < r ∧ ∃ i, hD.eigenvalues i = r }

/-- The gap is positive when D is invertible on its support.
    Tier T3 — proven in Lean; depends only on the standard axioms
    (propext, Classical.choice, Quot.sound). -/
theorem spectralGap_pos {n : ℕ} (D : Matrix (Fin n) (Fin n) ℂ)
    (hD : D.IsHermitian) (hpos : ∃ i, 0 < hD.eigenvalues i) :
    0 < spectralGap D hD := by
  unfold spectralGap
  -- The finset of positive eigenvalues.
  set F : Finset ℝ :=
    (Finset.univ.filter (fun i : Fin n => 0 < hD.eigenvalues i)).image
      hD.eigenvalues with hF
  have hFmem : ∀ x ∈ F, 0 < x := by
    intro x hx
    simp only [hF, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
      true_and] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    exact hi
  have hFne : F.Nonempty := by
    obtain ⟨i, hi⟩ := hpos
    refine ⟨hD.eigenvalues i, ?_⟩
    simp only [hF, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
      true_and]
    exact ⟨i, hi, rfl⟩
  -- The set in the definition is exactly the coercion of F.
  have hSeq : { r : ℝ | 0 < r ∧ ∃ i, hD.eigenvalues i = r } = ↑F := by
    ext r
    simp only [Set.mem_ofPred_eq, Finset.mem_coe, hF, Finset.mem_image,
      Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hr, i, rfl⟩
      exact ⟨i, hr, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨hi, i, rfl⟩
  rw [hSeq]
  -- sInf ↑F = F.min', which is a member of F, hence positive.
  have hmin_mem : F.min' hFne ∈ F := Finset.min'_mem F hFne
  have hpos_min : 0 < F.min' hFne := hFmem _ hmin_mem
  have hbb : BddBelow (↑F : Set ℝ) := (Finset.finite_toSet F).bddBelow
  have hne' : (↑F : Set ℝ).Nonempty := Finset.coe_nonempty.mpr hFne
  have heq : sInf (↑F : Set ℝ) = F.min' hFne := by
    apply le_antisymm
    · exact csInf_le hbb (Finset.mem_coe.mpr hmin_mem)
    · apply le_csInf hne'
      intro x hx
      rw [Finset.mem_coe] at hx
      exact Finset.min'_le F x hx
  rw [heq]
  exact hpos_min

end ThetLogos
