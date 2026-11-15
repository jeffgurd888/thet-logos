/-
# ResonanceTransport — TAB-2: the resonance / frequency
law beyond the diagonal seat

**TAB-2 of the thermal-acoustic bridge line
(~/workspace/your_files/thermal-acoustic-bridge-scope-2026-11-11.md
§3/§5). NO CLAIM. Dial-ineligible. NO physics claim.**

The bridge's Part III (the resonance/frequency law) is
landed at the DIAGONAL seat (`ResonanceSpectrum`:
`gibbs_resonance_phase`, `gibbs_stationary_iff`), the
thermal clock runs at the diagonal seat (`ThermalClock`),
and `HermitianReduction` transports the generator side —
exp, trace, stationarity in the eigenbasis
(`genFlow_stationary_iff`, eigenbasis form). What was
NOT in the tree (scope §3, row "exp of a general scalar
multiple of a Hermitian generator, spectral form"):

1. the exp of a scalar multiple of a Hermitian generator
   in spectral form, at a general complex scalar (§1 —
   `HermitianReduction.heatKernelGen_eq_conj` is the
   heat specialization `-(t:ℂ)`);
2. the dictionary between the two flow dialects at a
   general Hermitian generator: `ThermalClock.modularFlow`
   (the modular side) and `HermitianReduction.genFlow`
   (the phase/eigenbasis side) — they differ by time
   orientation, and the identity is stated and proved
   here (§2);
3. the stationarity criterion in the ORIGINAL basis —
   commutation with the generator — closing
   `HermitianReduction`'s named remainder R1 in its
   original-basis form (§3; the eigenbasis form is
   already landed there);
4. the GibbsClock reading of the transported flow, and
   the resonance spectrum of a Gibbs generator as a
   rescaling of the Hamiltonian's gap set (§4).

Everything is transport of landed material; the section
adds no new physics and no new claim. The word
"acoustic" has no referent in the tree (scope Finding
1); nothing here creates one. **K-TAB-DIAL stands: no
theorem here moves any dial, and none is stated so it
could. K-TAB-RENAME fired on this line in 2026-11; this
module does not re-open it.**

Build note (disclosed, 2026-11-13): brick 2's first
build failed on three proof-level defects, all
repaired without touching any statement — (i) the
diagonal entry lemmas are entry-form, so they must
rewrite the entry equation directly (expanding with
`mul_apply` first leaves no product pattern for
them); (ii) `hspec`'s spectral rewrite abstracts
`K` inside `hK`-dependent terms (motive not type
correct), replaced by an explicit `congrArg` calc;
(iii) the cited `genFlow_stationary_iff` carries
the Clock section's `[Nonempty ι]` instance, so
`genFlow_stationary_iff_commute` case-splits on
`Nonempty ι` — at an empty index both sides are
matrix equalities over an empty type and close by
entry elimination. The statement stands at full
generality, as scoped.

STATUS: STATUS-TAB2.md.
-/

import Mathlib
import ThetLogos.ResonanceSpectrum
import ThetLogos.ThermalClock
import ThetLogos.HermitianReduction

namespace ThetLogos

open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## §1 — exp of a scalar multiple, spectral form -/

/-- **Exp of a scalar multiple of a Hermitian generator,
in spectral form:** for `K` Hermitian with spectral data
`(U, λ)` (`hermitian_spectral_form`), the exponential of
`z • K` at ANY complex scalar `z` is the conjugated
diagonal exponential. `HermitianReduction.heatKernelGen_eq_conj`
is the specialization `z = -(t:ℂ)`. The proof mirrors
that specialization's: scalar transport through the
spectral form, `exp_conj_star`, `Matrix.exp_diagonal`. -/
theorem exp_smul_conj_diag {K : Matrix ι ι ℂ} (hK : K.IsHermitian)
    (z : ℂ) :
    NormedSpace.exp (z • K)
      = (hK.eigenvectorUnitary : Matrix ι ι ℂ)
        * diagonal (fun i => Complex.exp (z * (hK.eigenvalues i : ℂ)))
        * star (hK.eigenvectorUnitary : Matrix ι ι ℂ) := by
  classical
  have hsmul : z • K
      = (hK.eigenvectorUnitary : Matrix ι ι ℂ)
        * (z • diagonal (fun i => ((hK.eigenvalues i : ℂ))))
        * star (hK.eigenvectorUnitary : Matrix ι ι ℂ) := by
    conv_lhs => rw [hermitian_spectral_form hK]
    rw [mul_smul_comm, smul_mul_assoc]
  have hdiag : z • diagonal (fun i => ((hK.eigenvalues i : ℂ)))
      = diagonal (fun i => z * ((hK.eigenvalues i : ℂ))) := by
    ext i j
    by_cases h : i = j
    · subst h
      simp [Matrix.diagonal_apply_eq, Matrix.smul_apply, smul_eq_mul]
    · simp [Matrix.diagonal_apply, h, Matrix.smul_apply, smul_eq_mul]
  have hfun : NormedSpace.exp (fun i => z * ((hK.eigenvalues i : ℂ)))
      = (fun i => Complex.exp (z * ((hK.eigenvalues i : ℂ)))) := by
    funext i
    rw [Pi.coe_exp]
    exact congrFun Complex.exp_eq_exp_ℂ.symm _
  rw [hsmul, exp_conj_star _ _ (Unitary.coe_star_mul_self _)
    (Unitary.coe_mul_star_self _), hdiag, Matrix.exp_diagonal, hfun]

/-! ## §2 — the two flow dialects -/

/-- **The flow dictionary:** the modular flow of a
Hermitian generator `K` is its eigenbasis phase flow
(`genFlow`) run with reversed time. The two landed
dialects of the same one-parameter group —
`ThermalClock.modularFlow` (built from `exp (±I·s•K)`)
and `HermitianReduction.genFlow` (built from
`phaseFlow` on the eigenvalues) — agree up to the time
orientation: after the spectral transport of §1, both
sides are the same seven-factor product
`U · diag · starU · A · U · diag · starU`, differing
only in the diagonal entries, which agree by the
orientation arithmetic. -/
theorem modularFlow_eq_genFlow_neg {N : ℕ}
    {K : Matrix (Fin N) (Fin N) ℂ}
    (hK : K.IsHermitian) (t : ℝ) (A : Matrix (Fin N) (Fin N) ℂ) :
    modularFlow K t A = genFlow hK (-t) A := by
  classical
  have hdiagL : diagonal (fun i => Complex.exp
        ((Complex.I * (t:ℂ)) * (hK.eigenvalues i : ℂ)))
      = diagonal (fun i => Complex.exp
        (-(Complex.I * ((-t:ℝ):ℂ) * (hK.eigenvalues i : ℂ)))) := by
    rw [Matrix.diagonal_eq_diagonal_iff]
    intro i
    congr 1
    push_cast
    ring
  have hdiagR : diagonal (fun i => Complex.exp
        ((-(Complex.I * (t:ℂ))) * (hK.eigenvalues i : ℂ)))
      = diagonal (fun i => Complex.exp
        (Complex.I * ((-t:ℝ):ℂ) * (hK.eigenvalues i : ℂ))) := by
    rw [Matrix.diagonal_eq_diagonal_iff]
    intro i
    congr 1
    push_cast
    ring
  unfold genFlow phaseFlow modularFlow
  rw [exp_smul_conj_diag hK, exp_smul_conj_diag hK]
  rw [hdiagL, hdiagR]
  simp only [Matrix.mul_assoc]

/-! ## §3 — stationarity in the original basis (R1) -/

/-- A matrix commutes with a real diagonal matrix iff
its entries between distinct diagonal levels vanish. -/
theorem diagonal_commute_iff {d : ι → ℝ} {A : Matrix ι ι ℂ} :
    (A * diagonal (fun i => (d i : ℂ)) = diagonal (fun i => (d i : ℂ)) * A)
      ↔ ∀ i j, A i j ≠ 0 → d i = d j := by
  classical
  constructor
  · intro h i j hij
    have hentry := congrFun (congrFun h i) j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at hentry
    by_contra hne
    apply hij
    have h0 : A i j * (d j : ℂ) - (d i : ℂ) * A i j = 0 := by
      rw [← hentry]; ring
    have hfactor : A i j * ((d j : ℂ) - (d i : ℂ)) = 0 := by
      rw [mul_sub]; rw [← h0]; ring
    rcases mul_eq_zero.mp hfactor with h1 | h2
    · exact h1
    · exfalso; apply hne
      have hcast : (d j : ℂ) = (d i : ℂ) := sub_eq_zero.mp h2
      exact_mod_cast hcast.symm
  · intro h
    ext i j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    by_cases hij : A i j = 0
    · rw [hij]; ring
    · have hd : d i = d j := h i j hij
      rw [hd]; ring

/-- **Stationarity in the original basis** — the
original-basis form of `HermitianReduction`'s remainder
R1: `A` is stationary under the generator flow
(`genFlow`, at the generator's own seat) iff `A`
commutes with the generator `K` itself. The transport
is the unitary conjugation (`Unitary.conjStarAlgAut`):
it carries `K` to its eigenvalue diagonal
(`hK.spectral_theorem`) and the eigenbasis stationarity
form to `diagonal_commute_iff`. -/
theorem genFlow_stationary_iff_commute {K : Matrix ι ι ℂ}
    (hK : K.IsHermitian) (A : Matrix ι ι ℂ) :
    (∀ t : ℝ, genFlow hK t A = A) ↔ A * K = K * A := by
  classical
  by_cases hι : Nonempty ι
  · haveI := hι
    have hφA : (Unitary.conjStarAlgAut ℂ _ hK.eigenvectorUnitary).symm A
        = star (hK.eigenvectorUnitary : Matrix ι ι ℂ) * A
          * (hK.eigenvectorUnitary : Matrix ι ι ℂ) :=
      Unitary.conjStarAlgAut_symm_apply _ _
    have hspec : (Unitary.conjStarAlgAut ℂ _ hK.eigenvectorUnitary).symm K
        = diagonal (fun i => ((hK.eigenvalues i : ℂ))) := by
      rw [Unitary.conjStarAlgAut_symm_apply]
      calc star (hK.eigenvectorUnitary : Matrix ι ι ℂ) * K
            * (hK.eigenvectorUnitary : Matrix ι ι ℂ)
          = star (hK.eigenvectorUnitary : Matrix ι ι ℂ)
              * ((hK.eigenvectorUnitary : Matrix ι ι ℂ)
                * diagonal (fun i => ((hK.eigenvalues i : ℂ)))
                * star (hK.eigenvectorUnitary : Matrix ι ι ℂ))
              * (hK.eigenvectorUnitary : Matrix ι ι ℂ) :=
            congrArg (fun X => star (hK.eigenvectorUnitary : Matrix ι ι ℂ)
              * X * (hK.eigenvectorUnitary : Matrix ι ι ℂ))
              (hermitian_spectral_form hK)
        _ = (star (hK.eigenvectorUnitary : Matrix ι ι ℂ)
              * (hK.eigenvectorUnitary : Matrix ι ι ℂ))
            * diagonal (fun i => ((hK.eigenvalues i : ℂ)))
            * (star (hK.eigenvectorUnitary : Matrix ι ι ℂ)
              * (hK.eigenvectorUnitary : Matrix ι ι ℂ)) := by
            simp only [Matrix.mul_assoc]
        _ = diagonal (fun i => ((hK.eigenvalues i : ℂ))) := by
            rw [Unitary.coe_star_mul_self, Matrix.one_mul, Matrix.mul_one]
    constructor
    · intro h
      have hcomm : (star (hK.eigenvectorUnitary : Matrix ι ι ℂ) * A
            * (hK.eigenvectorUnitary : Matrix ι ι ℂ))
          * diagonal (fun i => ((hK.eigenvalues i : ℂ)))
          = diagonal (fun i => ((hK.eigenvalues i : ℂ)))
            * (star (hK.eigenvectorUnitary : Matrix ι ι ℂ) * A
              * (hK.eigenvectorUnitary : Matrix ι ι ℂ)) := by
        rw [diagonal_commute_iff]
        intro i j hij
        by_contra hne
        exact hij ((genFlow_stationary_iff hK A).mp h i j hne)
      have hconj : (Unitary.conjStarAlgAut ℂ _ hK.eigenvectorUnitary).symm
            (A * K)
          = (Unitary.conjStarAlgAut ℂ _ hK.eigenvectorUnitary).symm
            (K * A) := by
        rw [map_mul, map_mul, hφA, hspec]
        exact hcomm
      exact (Unitary.conjStarAlgAut ℂ _ hK.eigenvectorUnitary).symm.injective
        hconj
    · intro h
      rw [genFlow_stationary_iff]
      intro i j hne
      have hcomm : (star (hK.eigenvectorUnitary : Matrix ι ι ℂ) * A
            * (hK.eigenvectorUnitary : Matrix ι ι ℂ))
          * diagonal (fun i => ((hK.eigenvalues i : ℂ)))
          = diagonal (fun i => ((hK.eigenvalues i : ℂ)))
            * (star (hK.eigenvectorUnitary : Matrix ι ι ℂ) * A
              * (hK.eigenvectorUnitary : Matrix ι ι ℂ)) := by
        have hconj : (Unitary.conjStarAlgAut ℂ _
              hK.eigenvectorUnitary).symm (A * K)
            = (Unitary.conjStarAlgAut ℂ _
              hK.eigenvectorUnitary).symm (K * A) := by
          rw [h]
        rw [map_mul, map_mul, hφA, hspec] at hconj
        exact hconj
      have hform := (diagonal_commute_iff).mp hcomm i j
      by_contra hnz
      exact hne (hform hnz)
  · constructor
    · intro _
      exact Matrix.ext fun i j => (hι ⟨i⟩).elim
    · intro _ _
      exact Matrix.ext fun i j => (hι ⟨i⟩).elim

/-! ## §4 — the GibbsClock reading and the Gibbs spectrum -/

/-- **The GibbsClock flow in the generator dialect:** a
Gibbs clock's own flow is the `genFlow` of its
Hamiltonian at the rescaled, time-reversed parameter
`-(β·s)`. Assembled from `GibbsClock.conversion` (the
clock's flow is `modularFlow` of `K` at `β·s`) and §2. -/
theorem gibbsClock_flow_genFlow {N : ℕ} (G : GibbsClock N)
    (s : ℝ) (B : Matrix (Fin N) (Fin N) ℂ) :
    G.flow s B = genFlow G.K_hermitian (-(G.beta * s)) B := by
  rw [GibbsClock.conversion, modularFlow_eq_genFlow_neg]

/-- The gap set of a rescaled-and-shifted spectrum is
the rescaled image of the gap set: gaps are differences,
so the shift cancels and the scale factors out. -/
theorem resonanceSpectrum_rescale {lam : ι → ℝ} (β : ℝ) (c : ℝ) :
    resonanceSpectrum (fun i => β * lam i + c)
      = (fun x => β * x) '' resonanceSpectrum lam := by
  unfold resonanceSpectrum
  ext x
  constructor
  · rintro ⟨⟨i, j⟩, rfl⟩
    exact ⟨lam i - lam j, ⟨⟨i, j⟩, rfl⟩, by ring⟩
  · rintro ⟨y, ⟨⟨i, j⟩, rfl⟩, rfl⟩
    exact ⟨⟨i, j⟩, by
      show (β * lam i + c) - (β * lam j + c) = β * (lam i - lam j)
      ring⟩

/-- **Part III at a general Hermitian seat (Gibbs
form):** the resonance spectrum of the Gibbs generator
`β • K` (spectral values `β·λᵢ`) is the β-rescaling of
the Hamiltonian's own gap set. The diagonal-seat version
is `ResonanceSpectrum.gibbs_resonance_phase`; this is
the same law read off the generator's eigenvalues. -/
theorem gibbs_resonance_spectrum {K : Matrix ι ι ℂ}
    (hK : K.IsHermitian) (β : ℝ) :
    resonanceSpectrum (fun i => β * hK.eigenvalues i)
      = (fun x => β * x) '' resonanceSpectrum hK.eigenvalues := by
  have h := resonanceSpectrum_rescale (lam := hK.eigenvalues) β 0
  simpa using h

end ThetLogos
