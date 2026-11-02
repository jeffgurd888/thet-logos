import ThetLogos.BSDRefinedE3Repin
import ThetLogos.BSDTorsionE3Sweep
import Mathlib.Tactic

namespace ThetLogos

/-!
# ThetLogos.BSDRefinedE3Assembly — the E3 re-pin's assembly at its own seams

Source: BSD rung 3, brick **BSD3-2R** (assembly), mirroring
`ThetLogos.BSDRefinedE1Assembly` statement-for-statement with E3's
seams and values, in B2-6's discipline (`ThetLogos.BSDRefinedAssembly`).

**What this file IS.** At the E3 re-pin's seams — the rank-zero
seam, the torsion-card seam (discharged in
`ThetLogos.BSDTorsionE3Sweep`, conditional on the corrected
Nagell–Lutz seam `NagellLutzCriterionE3R`), the Sha seam, the
in-pass L-value, the in-pass period value, and the Tamagawa seam
instance `∏c_p = 5` — the proved core of the re-pin
`BSDRefinedE3R`: for an arbitrary `sha : ℕ`,

  `|Lval − refinedRHS sha ΩE3 1 tam 5| ≤ 5e-3 ↔ sha = 1`,

with `sha` **derived by interval arithmetic, never input**: at the
seams `refinedRHS` reduces to `sha · ΩE3 / 5` (with `Reg = 1` the
rank-0 empty-determinant convention, `tam = 5`, `#tors = 5`);
`sha = 0` is excluded by the Sha seam's positivity; and every
`sha ≥ 2` puts the right side at `≥ 2 · 1.2692092 / 5 =
0.50768368`, against `Lval ≤ 0.2538518609` — a gap of `≈ 0.2538`,
far outside the `5e-3` tolerance — while `sha = 1` agrees within
`≈ 1.1e-5` (`ΩE3 / 5 ∈ [0.25384184, 0.25384188]` against `Lval`
within `1e-5` of `0.2538418609`). A conjunction corollary recovers
the re-pin's conjoined conclusion form for any `sha` for which the
tolerance is given, exactly as the E1 assembly did for E1.

**Shape fence (B2-6 / E1 discipline, on the face).** The re-pin
`BSDRefinedE3R` as a bare `∀`-proposition — tolerance in the
conclusion for **all** `sha` — is **NOT asserted as a theorem**
here: for `sha ≥ 2` its first conjunct is false. The equivalence
proved here is the pin's provable core, exactly as for E1.

**Charter kill K-BSD3-2R-a — disposition: does not fire.** The
assembly quantifies over the seam's `sha : ℕ`; the only Sha
hypothesis consumed is `E3ShaFiniteSeam sha`, whose statable
residue is `0 < sha` for the *denoted* finite order. No use is
made of the analytic Sha as the algebraic group's order beyond
the B1 region licence, and no identification of analytic with
algebraic Sha is asserted anywhere.

**What this file is NOT — the board fences, on the face.**
- **Not the official statement.** The Clay prize statement is the
  rank equality (rung 1's `BSDRankEquality`). The refined formula
  assembled here is Wiles's Remark 1, for one regression curve.
  Parts of the official BSD statement closed by this module:
  **0**. NO CLAIM; dials 0/4.
- **No laundered exactness.** The bars are the seams': `1e-5` on
  the in-pass L-value, the period interval
  `[1.2692092, 1.2692094]`, `5e-3` the pin's tolerance.

Honesty tiers in this file:
- **T1 (proved):** the `refinedRHS` reduction, both directions of
  the tolerance equivalence, the assembly theorem, and the
  pin-conclusion corollary — all conditional on the named seams.
- **T5 (statement, unproved by design):** the seams themselves,
  carried as antecedents.

Status: NO CLAIM on BSD. Parts of the official statement closed: 0.
-/

/-! ## The interval arithmetic core -/

/-- The right-hand side at the seam values: with `tam = 5` (the
Tamagawa seam instance), the literal regulator `1` (rank-0
empty-determinant convention) and the literal torsion `5`,
`refinedRHS sha ΩE3 1 tam 5 = sha · ΩE3 / 5`. -/
theorem refinedRHS_E3_tam_five (sha : ℕ) (ΩE3 tam : ℝ)
    (hTam : E3TamagawaValue tam) :
    refinedRHS sha ΩE3 1 tam 5 = (sha : ℝ) * ΩE3 / 5 := by
  have ht : tam = 5 := hTam
  rw [ht]
  unfold refinedRHS
  ring

/-- **The uniqueness direction.** Under the re-pin's named
hypotheses, if the tolerance identity holds then `sha = 1`:
`sha = 0` is excluded by the Sha seam (`E3ShaFiniteSeam`,
positivity of the denoted order), and every `sha ≥ 2` makes the
right-hand side at least `2 · 1.2692092 / 5 = 0.50768368`,
overshooting `Lval ≤ 0.2538518609` by `≈ 0.2538 > 5e-3`. `sha` is
derived here, never input. -/
theorem E3_sha_eq_one_of_tolerance (Lval ΩE3 : ℝ) (sha : ℕ) (tam : ℝ)
    (hSha : E3ShaFiniteSeam sha) (hL : E3LValue Lval)
    (hPer : E3PeriodValue ΩE3) (hTam : E3TamagawaValue tam)
    (htol : |Lval - refinedRHS sha ΩE3 1 tam 5| ≤ 5e-3) : sha = 1 := by
  have hL' : |Lval - 0.2538418609| ≤ 1e-5 := hL
  obtain ⟨hΩlo, hΩhi⟩ := Set.mem_Icc.mp hPer
  rw [abs_le] at hL'
  rw [refinedRHS_E3_tam_five sha ΩE3 tam hTam, abs_le] at htol
  have hpos : 0 < sha := hSha
  by_contra hne
  have hge : 2 ≤ sha := by omega
  have hcast : (2 : ℝ) ≤ (sha : ℝ) := by exact_mod_cast hge
  have hbig : (2 : ℝ) * 1.2692092 ≤ (sha : ℝ) * ΩE3 :=
    mul_le_mul hcast hΩlo (by norm_num) (Nat.cast_nonneg sha)
  linarith

/-- **The agreement direction.** At `sha = 1`, under the re-pin's
named hypotheses, the tolerance identity holds: `ΩE3 / 5` lies in
`[0.25384184, 0.25384188]` and `Lval` in
`[0.2538318609, 0.2538518609]`, so the two differ by at most
`≈ 1.1e-5 < 5e-3`. -/
theorem E3_tolerance_of_sha_eq_one (Lval ΩE3 tam : ℝ)
    (hL : E3LValue Lval) (hPer : E3PeriodValue ΩE3)
    (hTam : E3TamagawaValue tam) :
    |Lval - refinedRHS 1 ΩE3 1 tam 5| ≤ 5e-3 := by
  have hL' : |Lval - 0.2538418609| ≤ 1e-5 := hL
  obtain ⟨hΩlo, hΩhi⟩ := Set.mem_Icc.mp hPer
  rw [abs_le] at hL'
  have ht : tam = 5 := hTam
  rw [ht]
  have hRHS : refinedRHS (1 : ℝ) ΩE3 1 5 5 = ΩE3 / 5 := by
    unfold refinedRHS
    ring
  rw [hRHS, abs_le]
  constructor <;> linarith

/-- **The tolerance equivalence (the re-pin's provable core).**
Under the named hypotheses only — the Sha seam, the in-pass
L-value, the in-pass period value, and the Tamagawa seam
instance — the tolerance identity in the re-pin's exact stated
form holds **iff `sha = 1`**, with `sha` derived by interval
arithmetic, never input. -/
theorem E3_tolerance_iff_sha_eq_one (Lval ΩE3 : ℝ) (sha : ℕ) (tam : ℝ)
    (hSha : E3ShaFiniteSeam sha) (hL : E3LValue Lval)
    (hPer : E3PeriodValue ΩE3) (hTam : E3TamagawaValue tam) :
    (|Lval - refinedRHS sha ΩE3 1 tam 5| ≤ 5e-3 ↔ sha = 1) := by
  constructor
  · intro htol
    exact E3_sha_eq_one_of_tolerance Lval ΩE3 sha tam hSha hL hPer
      hTam htol
  · intro h1
    subst h1
    simpa using E3_tolerance_of_sha_eq_one Lval ΩE3 tam hL hPer hTam

/-! ## The assembly -/

/-- **The E3 assembly theorem (brick BSD3-2R).** From the named
hypotheses only — the corrected Nagell–Lutz seam
`NagellLutzCriterionE3R` as an antecedent (the sweep brick's
discharge of the torsion factor), and, inside, the re-pin's own
seams in their stated forms (`E3RankZeroSeam`, carried as an
antecedent and not consumed by the arithmetic, exactly as the E1
assembly carried its rank seam; `E3ShaFiniteSeam sha`;
`E3LValue Lval`; `E3PeriodValue ΩE3`; `E3TamagawaValue tam`) —
the torsion cardinality is `5`, and the tolerance identity holds
**iff `sha = 1`**, with `sha` derived by interval arithmetic,
never input. K-BSD3-2R-a does not fire: the assembly quantifies
over the seam's `sha : ℕ` and asserts no identification of
analytic with algebraic Sha beyond the B1 licence. This closes
zero parts of the official BSD statement. NO CLAIM. -/
theorem BSDRefinedE3R_assembly (hNL : NagellLutzCriterionE3R) :
    E3TorsionCardSeam ∧
    ∀ (Lval ΩE3 : ℝ) (sha : ℕ) (tam : ℝ),
      E3RankZeroSeam → E3ShaFiniteSeam sha →
      E3LValue Lval → E3PeriodValue ΩE3 → E3TamagawaValue tam →
      (|Lval - refinedRHS sha ΩE3 1 tam 5| ≤ 5e-3 ↔ sha = 1) := by
  refine ⟨e3TorsionCard_of_nagellLutzR hNL, ?_⟩
  intro Lval ΩE3 sha tam _hRank hSha hL hPer hTam
  exact E3_tolerance_iff_sha_eq_one Lval ΩE3 sha tam hSha hL hPer hTam

/-- **The re-pin's conjoined conclusion, in its stated form,**
recovered from the assembly: for any `sha` satisfying the
re-pin's named hypotheses *and* the tolerance identity, the
conclusion `|Lval − refinedRHS sha ΩE3 1 tam 5| ≤ 5e-3 ∧ sha = 1`
holds — the first conjunct is the given tolerance, the second is
derived by `E3_sha_eq_one_of_tolerance`. -/
theorem BSDRefinedE3R_conclusion_of_tolerance (Lval ΩE3 : ℝ) (sha : ℕ)
    (tam : ℝ) (hSha : E3ShaFiniteSeam sha) (hL : E3LValue Lval)
    (hPer : E3PeriodValue ΩE3) (hTam : E3TamagawaValue tam)
    (htol : |Lval - refinedRHS sha ΩE3 1 tam 5| ≤ 5e-3) :
    |Lval - refinedRHS sha ΩE3 1 tam 5| ≤ 5e-3 ∧ sha = 1 :=
  ⟨htol, E3_sha_eq_one_of_tolerance Lval ΩE3 sha tam hSha hL hPer
    hTam htol⟩

/-! ## Axiom checks (headline results) -/

#print axioms refinedRHS_E3_tam_five
#print axioms E3_sha_eq_one_of_tolerance
#print axioms E3_tolerance_of_sha_eq_one
#print axioms E3_tolerance_iff_sha_eq_one
#print axioms BSDRefinedE3R_assembly
#print axioms BSDRefinedE3R_conclusion_of_tolerance

end ThetLogos
