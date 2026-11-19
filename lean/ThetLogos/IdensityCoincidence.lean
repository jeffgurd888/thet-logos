import Mathlib.Tactic
import ThetLogos.FiniteEntropy
import ThetLogos.ModularTime
import ThetLogos.ModularVariance

/-!
# ID-1 — the Idensity coincidence, assembled (statement + proof brick)

## The discussion that brought this about

**The term (Zero's coinage, 2026-11-09).** "Idensity" (Identity
Density) is the third term of Zero's symmetry-breaking ternary —
containment / identity / **Idensity** — and is defined by Zero,
verbatim: *"The concentration of invariant state information and
modular energy confined per unit boundary volume."* It is a
Register-A definition by declaration: defining it asserts no
theorem and moves no dial.

**The scoping (2026-11-09, `idensity-scope-2026-11-09.md`).** The
definition's numerator conjoins two quantities — invariant state
information AND modular energy — and the audit's structural finding
(§2.2) governs everything below: for a state's **own** modular
Hamiltonian, the two quantities are *the same number*. On the
diagonal seat it is definitional (`⟨K⟩ = ∑ wⱼ(−log wⱼ) = entropyW w`);
on the Gibbs seat, `S(ρ_β) = β⟨E⟩_β + log Z = ⟨K⟩_β` follows from
`ModularVariance.gibbsExpect_modEigen` — but the assembled identity
was *not* a named in-tree theorem. Every component existed; the
assembly is this brick (ID-1 of the scoping's §6 residue table).

**Zero's ruling on the open joint (2026-11-09, after the scoping):**
the numerator is the ordered **PAIR** (invariant state information,
reference-modular energy) — pair form, never a sum. The two terms
are genuinely two only against a *reference* Hamiltonian; at an
own-modular seat they coincide, which is exactly what this brick
proves. The guard is **K-IDENSITY-DOUBLE**: presenting an
own-modular sum as "information plus energy" (two independent
contributions) is a kill — the honest own-modular statements are
"the pair is (x, x)" or "the sum is 2S", said as such.

**What this brick is not.** No Idensity definition is stated here
(that is ID-3, gated on Zero's pins: the primary boundary form and
the empty-boundary convention; the boundary vocabulary itself is
ID-2, ungated under Zero's ruling C of 2026-11-10 — both boundary
forms built). No boundary, no ratio, no gravity reading:
**K-IDENSITY-PROXY / K-IDENSITY-DIAL / K-IDENSITY-LAUNDER stand on
the parent scoping's face. Dial-ineligible; Dial 2 = 0; NO CLAIM.**
-/

namespace ThetLogos

section GibbsSeat

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- **ID-1, the coincidence at the Gibbs seat (Tier T1 — proved):**
    the entropy of the Gibbs weights IS the expectation of the
    modular eigenvalues — `S(ρ_β) = ⟨K⟩_β`. This is the assembled
    identity the ID scoping (§2.2) found unbuilt: information and
    own-modular energy are one number at this seat. -/
theorem entropyW_gibbsProb_eq (E : ι → ℝ) (β : ℝ) :
    entropyW (ModularVariance.gibbsProb E β)
      = ModularVariance.gibbsExpect E β
          (ModularVariance.modEigen E β) := by
  have hZ : ModularVariance.partSum E β ≠ 0 :=
    ne_of_gt (ModularVariance.partSum_pos E β)
  have hlog : ∀ i, Real.log (ModularVariance.gibbsProb E β i)
      = -(β * E i) - Real.log (ModularVariance.partSum E β) := by
    intro i
    rw [ModularVariance.gibbsProb,
      Real.log_div (Real.exp_ne_zero _) hZ, Real.log_exp]
  unfold entropyW ModularVariance.gibbsExpect
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [hlog i, ModularVariance.modEigen]
  ring

/-- **The β-form of the coincidence (Tier T1 — proved):**
    `S(ρ_β) = β⟨E⟩_β + log Z` — the entropy read off the energy
    side, via `gibbsExpect_modEigen`. -/
theorem entropyW_gibbsProb_eq_beta_form (E : ι → ℝ) (β : ℝ) :
    entropyW (ModularVariance.gibbsProb E β)
      = β * ModularVariance.meanEnergy E β
        + Real.log (ModularVariance.partSum E β) := by
  rw [entropyW_gibbsProb_eq, ModularVariance.gibbsExpect_modEigen]

end GibbsSeat

/-- **ID-1, the coincidence at the diagonal seat (Tier T1 —
    proved):** the weight-expectation of the diagonal modular
    Hamiltonian's entries is the weight entropy, definitionally —
    `∑ⱼ wⱼ · (−log wⱼ) = entropyW w`, with the entries read off
    `diagModularK` itself. -/
theorem diagModularK_expectation_eq_entropyW {N : ℕ} (w : Fin N → ℝ) :
    (∑ j, w j * (diagModularK w j j).re) = entropyW w := by
  unfold entropyW
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  simp only [diagModularK, Matrix.diagonal_apply_eq, Complex.ofReal_re]
  rw [mul_neg]

end ThetLogos
