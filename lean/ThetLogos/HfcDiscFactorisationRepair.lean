import ThetLogos.HfcDiscSpectralMapping

/-!
# B4-REPAIR — the conditional `DiscFactorisationHyp'` (SHELF-7b-disc chain)

Repair entry for GATE-B4 (scoping
`routeb-general-scratch/scoping-gate-b4-2026-11-02.md` §0).
The landed B3′ module `HfcDiscSpectralMapping.lean` is NOT
edited; this module is a NEW entry under the relabeling rule.

## Header record

* **K-B4-LITERAL fired** — the frozen `DiscFactorisationHyp`
  (B3′, `HfcDiscSpectralMapping.lean`) omits the
  `DiscHolomorphic f R` and `(spectralRadius ℂ a).toReal < R`
  antecedents and is FALSE as stated. This module is its
  in-tree receipt: `discFactorisationHyp_not` refutes it at
  GATE-B1's boundary witness, `a = 0`, `R = 2`, `R₀ = 1`,
  `mu = 1`, from landed parts only (B1's boundary coefficient
  `discCoeff_boundary_counterexample`, `hfcDisc_at_zero`,
  and B3′'s own unit lemmas).
* The frozen hyp is **never consumed downstream**: B3′'s
  theorems stand, but no later GATE-B brick targets the
  frozen form.
* The live target is the NEW conditional entry
  `DiscFactorisationHyp'` below, whose antecedents are
  exactly what `Shelf7bDiscInterior` itself supplies:
  `DiscHolomorphic f R` and
  `(spectralRadius ℂ a).toReal < R`, then the frozen body.
  Every later GATE-B brick targets the primed form.
* The adapter `shelf7bDiscInterior_proved_of_factorisation'`
  feeds B3′'s landed assembly
  (`shelf7bDiscInterior_proved_of_factorisation`) from the
  primed form: inside the interior's own antecedents the
  conditional hyp yields the frozen hyp, and B3′'s assembly
  closes.

Face fence: 7b-disc is NOT 7b-in-full. NO CLAIM; dials 0/4.
-/

namespace ThetLogos

open Filter
open scoped NNReal ENNReal

noncomputable section

variable {A : Type*} [NormedRing A] [NormOneClass A]
  [NormedAlgebra ℂ A] [CompleteSpace A] [Nontrivial A]

/-! ## 1. The refutation (receipt of K-B4-LITERAL) -/

omit [Nontrivial A] in
/-- The boundary witness's values on the spectrum of `0`:
every spectral value of `0` is `0` itself (its norm is at
most the spectral radius, which is `0`), and the witness
vanishes at `0`, so `1` is not in the image. -/
theorem one_notMem_image_spectrum_zero :
    (1 : ℂ) ∉ (fun z : ℂ => if ‖z‖ = 1 then (1 : ℂ) else 0)
      '' spectrum ℂ (0 : A) := by
  rintro ⟨lam, hlam, hflam⟩
  have hle : ‖lam‖ ≤ (spectralRadius ℂ (0 : A)).toReal :=
    norm_le_spectralRadius_toReal hlam
  have hsr0 : (spectralRadius ℂ (0 : A)).toReal = 0 := by
    simp [spectrum.spectralRadius_zero]
  rw [hsr0] at hle
  have hlam0 : lam = 0 := by
    simpa using le_antisymm hle (norm_nonneg lam)
  rw [hlam0] at hflam
  have hf0 : (fun z : ℂ => if ‖z‖ = 1 then (1 : ℂ) else 0) 0 = 0 := by
    simp
  rw [hf0] at hflam
  exact one_ne_zero hflam.symm

/-- K-B4-LITERAL, in-tree receipt: the frozen
`DiscFactorisationHyp` is false as stated. At GATE-B1's
boundary witness `f`, `a = 0`, `R = 2`, presented at
`R₀ = 1` with `mu = 1 ∉ f '' spectrum ℂ 0`, the
factorisation's left side is
`hfcDisc 0 (discCoeff f 1) - 1 • 1 = 1 - 1 = 0`
(`hfcDisc_at_zero` + `discCoeff_boundary_counterexample`),
while its right side is a product of units (B3′'s
`isUnit_list_prod` and
`isUnit_a_sub_smul_one_of_notMem_spectrum`) times a unit,
hence a unit — and `0` is not a unit in a nontrivial
algebra. -/
theorem discFactorisationHyp_not :
    ¬ DiscFactorisationHyp (0 : A)
      (fun z : ℂ => if ‖z‖ = 1 then (1 : ℂ) else 0) 2 := by
  intro h
  obtain ⟨lam, hc, hlam, -, hunit, hfact⟩ :=
    h 1 spectralRadius_zero_toReal_lt_one (by norm_num) 1
      one_notMem_image_spectrum_zero
  have hLHS : hfcDisc (0 : A)
        (discCoeff (fun z : ℂ => if ‖z‖ = 1 then (1 : ℂ) else 0) 1)
        - (1 : ℂ) • (1 : A) = 0 := by
    rw [hfcDisc_at_zero, discCoeff_boundary_counterexample]
    simp
  have hprod : IsUnit (lam.map fun l => (0 : A) - l • (1 : A)).prod := by
    apply isUnit_list_prod
    intro x hx
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hx
    exact isUnit_a_sub_smul_one_of_notMem_spectrum (hlam l hl)
  have hunitRHS : IsUnit (hfcDisc (0 : A)
      (discCoeff (fun z : ℂ => if ‖z‖ = 1 then (1 : ℂ) else 0) 1)
      - (1 : ℂ) • (1 : A)) := by
    rw [hfact]
    exact hprod.mul hunit
  rw [hLHS] at hunitRHS
  exact hunitRHS.ne_zero rfl

/-! ## 2. The corrected conditional form (new entry) -/

/-- The corrected factorisation hypothesis, NEW entry:
the frozen body `DiscFactorisationHyp a f R` WITH the
antecedents the interior supplies, in the GATE-B4
scoping's exact form — `DiscHolomorphic f R` and
`(spectralRadius ℂ a).toReal < R`. Later GATE-B discharge
bricks target this primed form verbatim; the frozen form
is never consumed downstream. -/
def DiscFactorisationHyp' (a : A) (f : ℂ → ℂ) (R : ℝ) : Prop :=
  DiscHolomorphic f R → (spectralRadius ℂ a).toReal < R →
    DiscFactorisationHyp a f R

/-! ## 3. The adapter to B3′'s landed assembly -/

/-- The adapter: `Shelf7bDiscInterior` from the primed
factorisation hypothesis, feeding B3′'s landed assembly
`shelf7bDiscInterior_proved_of_factorisation`. The primed
hyp is applied after the interior's own antecedents
`hf`/`hsr` are introduced, yielding the frozen hyp in
exactly the context where B3′'s assembly consumes it. -/
theorem shelf7bDiscInterior_proved_of_factorisation'
    (a : A) (f : ℂ → ℂ) (R : ℝ)
    (hfact' : DiscFactorisationHyp' a f R) :
    Shelf7bDiscInterior a f R := by
  intro hf hsr R₀ hsr₀ hR₀R
  exact shelf7bDiscInterior_proved_of_factorisation a f R
    (hfact' hf hsr) hf hsr R₀ hsr₀ hR₀R

end

end ThetLogos
