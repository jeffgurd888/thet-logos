import ThetLogos.OneModeFermion
import ThetLogos.WightmanTargets
import ThetLogos.WightmanAxioms

namespace ThetLogos

open scoped InnerProductSpace

/-!
# ThetLogos.Rung5W3 — W3 spectrum condition, trivial translation representation

Source: Rung 5 (2026-10-11), axiom W3 (spectrum condition).

**What this file IS.** A machine-checked discharge of the sharpened W3 target
`W3_spectrumCondition_sharp` for the *trivial* translation representation:
constant identity unitaries, zero energy-momentum generators
(`P^μ = liftTop 0`), joint spectrum `{0}`. The four conjuncts are proved:
the representation law, weak symmetry, weak commutation, and
`{0} ⊆ forwardLightCone` (the cone membership is `0 ≤ 0 ∧ 0 ≤ 0`).

**What this file is NOT.** The physical spectrum condition. The real content
— positive energy for a genuine translation representation, via Stone's
theorem and the joint spectral calculus for commuting unbounded self-adjoint
operators — is priced, not proved: unbounded spectral theory is absent from
Mathlib (2026). See the docstring of `w3_trivial` for the honest label.

Honesty tiers in this file:
- **T1 (proved):** `w3_trivial` — zero `sorry`s, clean axiom footprint.
- **T5 (priced, not proved):** positive energy for a genuine translation
  representation (Stone's theorem + unbounded joint spectral theory).
-/

/-- **W3 trivial (T1):** the spectrum condition for the trivial translation
    representation. `transRep a = 1` constantly, `energyMom μ = liftTop 0`
    (the zero operator on `D = ⊤`), joint spectrum `{0}`.

    HONEST LABEL: spectrum condition discharged only for the trivial
    representation — zero energy-momentum, spec = {0}. This is a consistency
    check of the sharpened frame, not physics. The physical content —
    positive energy for a genuine translation representation via Stone's
    theorem — remains priced (unbounded spectral theory absent from Mathlib). -/
theorem w3_trivial :
    W3_spectrumCondition_sharp Fock1 (⊤ : Submodule ℂ Fock1)
      (fun _ => LinearIsometryEquiv.refl ℂ Fock1)
      (fun _ => liftTop 0)
      {0} := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- Representation law: refl = refl.trans refl
    intro a b
    simp
  · -- Weak symmetry of the zero operator: both inner products are 0
    intro _ ψ χ
    simp [liftTop]
  · -- Weak commutation: 0 = 0, definitionally
    intro _ _ ψ
    rfl
  · -- {0} ⊆ forwardLightCone: 0 ≤ minkowskiInner 0 0 ∧ 0 ≤ (0 : Minkowski) 0
    intro p hp
    rw [Set.mem_singleton_iff] at hp
    subst hp
    show (0 : Minkowski) ∈ forwardLightCone
    refine ⟨?_, ?_⟩ <;> simp [minkowskiInner]

#print axioms w3_trivial

end ThetLogos
