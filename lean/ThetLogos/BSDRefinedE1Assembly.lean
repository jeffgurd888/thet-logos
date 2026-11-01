import ThetLogos.BSDTorsionE1Sweep
import ThetLogos.BSDRefinedAssembly
import Mathlib.Tactic

namespace ThetLogos

/-!
# ThetLogos.BSDRefinedE1Assembly — the E1 sibling's assembly at its own seams

Source: BSD rung 3, brick **BSD3-1** (module 2), in B2-6's discipline
(`ThetLogos.BSDRefinedAssembly`): the E1 sibling statement that B2-6
stated and proved nothing about, assembled here from its named
seams only.

**What this file IS.** At the E1 seams — the rank-zero seam, the
torsion seam (discharged in module 1, `ThetLogos.BSDTorsionE1Sweep`,
conditional on the shared Nagell–Lutz seam), the Sha seam, the
T4 L-value, the T4 period value introduced below, and the Tamagawa
seam instance `∏c_p = 2` — the proved core of the sibling pin:
for an arbitrary `sha : ℕ`,

  `|Lval − refinedRHS sha ΩE1 1 tam 4| ≤ 5e-3 ↔ sha = 1`,

with `sha` **derived by interval arithmetic, never input**: at the
seams `refinedRHS` reduces to `sha · ΩE1 / 8` (the rung-2 memo's
verified reduced form `L(E1,1) = ΩE1/8`, with `Reg = 1` the rank-0
empty-determinant convention, `tam = 2`, `#tors = 4`); `sha = 0`
is excluded by the Sha seam's positivity; and every `sha ≥ 2`
puts the right side at `≥ 2 · 5.244115012 / 8 = 1.311028753`,
against `Lval ≤ 0.655514390` — a gap of `≈ 0.6555`, far outside
the `5e-3` tolerance — while `sha = 1` agrees within `≈ 1.4e-5`.
A conjunction corollary recovers the pin's conjoined conclusion
form for any `sha` for which the tolerance is given, exactly as
B2-6 did for E2. (The pin `BSDRefinedE1` itself, stated for all
`sha` with the tolerance in its *conclusion* and no period
hypothesis, is not provable as stated — for `sha ≥ 2` its first
conjunct is false — and it is not edited; the equivalence here is
its provable content, in B2-6's exact discipline.)

**The period input, honestly tiered (on the face).** B2-6 recorded
NO period value for E1 (`ΩE1` is a bare parameter in
`BSDRefinedE1`), and E2's period is an in-tree computed object —
E1's is NOT. `E1PeriodValueT4` below records the value
`5.244115112` at tier **T4**: it is `8 ×` the LMFDB-recorded
`L(E1,1)` per the study's verified reduced form `L = Ω/8`
(equivalently the full-locus real period of 32.a3). It is a
recorded input — NOT an in-tree object, NOT computed in this
pass. Its bar `1e-7` covers the rounding of the quoted digits
and is not tightened anywhere in this module.

**Charter kill K-BSD3-1a — disposition.** The assembly quantifies
over the seam's `sha : ℕ` exactly as B2-6 did; the only Sha
hypothesis consumed is `E1ShaFiniteSeam sha`, whose statable
residue is `0 < sha` for the *denoted* finite order. No use is
made of the analytic Sha as the algebraic group's order beyond
the B1 region licence, and no identification is asserted
anywhere. The kill does not fire.

**What this file is NOT — the board fences, on the face.**
- **Not the official statement.** The Clay prize statement is the
  rank equality (rung 1's `BSDRankEquality`). The refined formula
  assembled here is Wiles's Remark 1, for one regression curve.
  Parts of the official BSD statement closed by this module:
  **0**. NO CLAIM.
- **No laundered exactness.** The bars are the seams': `1e-9` on
  the T4 L-value, `1e-7` on the T4 period, `5e-3` the pin's
  tolerance.

Honesty tiers in this file:
- **T1 (proved):** the `refinedRHS` reduction, both directions of
  the tolerance equivalence, the assembly theorem, and the
  pin-conclusion corollary — all conditional on the named seams.
- **T4 (recorded input):** `E1PeriodValueT4`, and (from B2-6)
  `E1LValueT4`.
- **T5 (statement, unproved by design):** the seams themselves,
  carried as antecedents.

Status: NO CLAIM on BSD. Parts of the official statement closed: 0.
-/

/-! ## The period input (T4) -/

/-- **E1's period value, T4-recorded.** `ΩE1 ≈ 5.244115112`, where
the value is `8 ×` the LMFDB-recorded `L(E1,1)` per the study's
verified reduced form `L(E1,1) = ΩE1/8` (equivalently the
full-locus real period of 32.a3). Tier **T4**, a recorded input:
NOT an in-tree object (contrast E2's `periodE2`, computed in-tree
in B2-3), NOT computed in this pass. The bar `1e-7` covers the
rounding of the quoted digits; it is the pin family's period bar
and is not tightened here. -/
def E1PeriodValueT4 (ΩE1 : ℝ) : Prop :=
  |ΩE1 - 5.244115112| ≤ 1e-7

/-! ## The interval arithmetic core -/

/-- The right-hand side at the seam values: with `tam = 2` (the
Tamagawa seam instance), the literal regulator `1` (rank-0
empty-determinant convention) and the literal torsion `4`,
`refinedRHS sha ΩE1 1 tam 4 = sha · ΩE1 / 8` — the memo's verified
reduced form. -/
theorem refinedRHS_E1_tam_two (sha : ℕ) (ΩE1 tam : ℝ)
    (hTam : E1TamagawaValue tam) :
    refinedRHS sha ΩE1 1 tam 4 = (sha : ℝ) * ΩE1 / 8 := by
  have ht : tam = 2 := hTam
  rw [ht]
  unfold refinedRHS
  ring

/-- **The uniqueness direction.** Under the sibling's named
hypotheses, if the tolerance identity holds then `sha = 1`:
`sha = 0` is excluded by the Sha seam (`E1ShaFiniteSeam`,
positivity of the denoted order), and every `sha ≥ 2` makes the
right-hand side at least `2 · 5.244115012 / 8 = 1.311028753`,
overshooting `Lval ≤ 0.655514390` by `≈ 0.6555 > 5e-3`. `sha` is
derived here, never input. -/
theorem E1_sha_eq_one_of_tolerance (Lval ΩE1 : ℝ) (sha : ℕ)
    (tam : ℝ) (hSha : E1ShaFiniteSeam sha) (hL : E1LValueT4 Lval)
    (hPer : E1PeriodValueT4 ΩE1) (hTam : E1TamagawaValue tam)
    (htol : |Lval - refinedRHS sha ΩE1 1 tam 4| ≤ 5e-3) :
    sha = 1 := by
  have hPer' : |ΩE1 - 5.244115112| ≤ 1e-7 := hPer
  have hL' : |Lval - 0.655514389| ≤ 1e-9 := hL
  rw [abs_le] at hPer' hL'
  rw [refinedRHS_E1_tam_two sha ΩE1 tam hTam, abs_le] at htol
  have hpos : 0 < sha := hSha
  by_contra hne
  have hge : 2 ≤ sha := by omega
  have hcast : (2 : ℝ) ≤ (sha : ℝ) := by exact_mod_cast hge
  have hΩlo : (5.244115012 : ℝ) ≤ ΩE1 := by linarith
  have hbig : (2 : ℝ) * 5.244115012 ≤ (sha : ℝ) * ΩE1 :=
    mul_le_mul hcast hΩlo (by norm_num) (Nat.cast_nonneg sha)
  linarith

/-- **The agreement direction.** At `sha = 1`, under the sibling's
named hypotheses, the tolerance identity holds: `ΩE1 / 8` lies in
`[0.6555143765, 0.6555144015]` and `Lval` in
`[0.655514388, 0.655514390]`, so the two differ by at most
`≈ 1.4e-5 < 5e-3`. -/
theorem E1_tolerance_of_sha_eq_one (Lval ΩE1 tam : ℝ)
    (hL : E1LValueT4 Lval) (hPer : E1PeriodValueT4 ΩE1)
    (hTam : E1TamagawaValue tam) :
    |Lval - refinedRHS 1 ΩE1 1 tam 4| ≤ 5e-3 := by
  have hPer' : |ΩE1 - 5.244115112| ≤ 1e-7 := hPer
  have hL' : |Lval - 0.655514389| ≤ 1e-9 := hL
  rw [abs_le] at hPer' hL'
  have ht : tam = 2 := hTam
  rw [ht]
  have hRHS : refinedRHS (1 : ℝ) ΩE1 1 2 4 = ΩE1 / 8 := by
    unfold refinedRHS
    ring
  rw [hRHS, abs_le]
  constructor <;> linarith

/-- **The tolerance equivalence (the sibling's provable core).**
Under the named hypotheses only — the Sha seam, the T4 L-value,
the T4 period value, and the Tamagawa seam instance — the
tolerance identity in the pin's exact stated form holds **iff
`sha = 1`**, with `sha` derived by interval arithmetic, never
input. -/
theorem E1_tolerance_iff_sha_eq_one (Lval ΩE1 : ℝ) (sha : ℕ)
    (tam : ℝ) (hSha : E1ShaFiniteSeam sha) (hL : E1LValueT4 Lval)
    (hPer : E1PeriodValueT4 ΩE1) (hTam : E1TamagawaValue tam) :
    (|Lval - refinedRHS sha ΩE1 1 tam 4| ≤ 5e-3 ↔ sha = 1) := by
  constructor
  · intro htol
    exact E1_sha_eq_one_of_tolerance Lval ΩE1 sha tam hSha hL hPer
      hTam htol
  · intro h1
    subst h1
    simpa using E1_tolerance_of_sha_eq_one Lval ΩE1 tam hL hPer hTam

/-! ## The assembly -/

/-- **The E1 assembly theorem (brick BSD3-1).** From the named
hypotheses only — the shared Nagell–Lutz seam
`NagellLutzCriterionE1` as an antecedent (module 1's discharge of
the torsion factor), and, inside, the sibling pin's own seams in
their stated forms (`E1RankZeroSeam`, carried as an antecedent
and not consumed by the arithmetic, exactly as B2-6 carried
Seam B4; `E1ShaFiniteSeam sha`; `E1LValueT4 Lval`;
`E1PeriodValueT4 ΩE1`, the T4 period input B2-6 did not record;
`E1TamagawaValue tam`) — the torsion cardinality is `4`, and the
tolerance identity holds **iff `sha = 1`**, with `sha` derived by
interval arithmetic, never input. K-BSD3-1a does not fire: the
assembly quantifies over the seam's `sha : ℕ` and asserts no
identification of analytic with algebraic Sha beyond the B1
licence. This closes zero parts of the official BSD statement.
NO CLAIM. -/
theorem BSDRefinedE1_assembly (hNL : NagellLutzCriterionE1) :
    E1TorsionCardSeam ∧
    ∀ (Lval ΩE1 : ℝ) (sha : ℕ) (tam : ℝ),
      E1RankZeroSeam → E1ShaFiniteSeam sha →
      E1LValueT4 Lval → E1PeriodValueT4 ΩE1 → E1TamagawaValue tam →
      (|Lval - refinedRHS sha ΩE1 1 tam 4| ≤ 5e-3 ↔ sha = 1) := by
  refine ⟨e1TorsionCard_of_nagellLutz hNL, ?_⟩
  intro Lval ΩE1 sha tam _hRank hSha hL hPer hTam
  exact E1_tolerance_iff_sha_eq_one Lval ΩE1 sha tam hSha hL hPer hTam

/-- **The pin's conjoined conclusion, in its stated form,**
recovered from the assembly: for any `sha` satisfying the
sibling's named hypotheses *and* the tolerance identity, the
conclusion `|Lval − refinedRHS sha ΩE1 1 tam 4| ≤ 5e-3 ∧ sha = 1`
holds — the first conjunct is the given tolerance, the second is
derived by `E1_sha_eq_one_of_tolerance`. -/
theorem BSDRefinedE1_conclusion_of_tolerance
    (Lval ΩE1 : ℝ) (sha : ℕ) (tam : ℝ)
    (hSha : E1ShaFiniteSeam sha) (hL : E1LValueT4 Lval)
    (hPer : E1PeriodValueT4 ΩE1) (hTam : E1TamagawaValue tam)
    (htol : |Lval - refinedRHS sha ΩE1 1 tam 4| ≤ 5e-3) :
    |Lval - refinedRHS sha ΩE1 1 tam 4| ≤ 5e-3 ∧ sha = 1 :=
  ⟨htol, E1_sha_eq_one_of_tolerance Lval ΩE1 sha tam hSha hL hPer
    hTam htol⟩

/-! ## Axiom checks (headline results) -/

#print axioms refinedRHS_E1_tam_two
#print axioms E1_sha_eq_one_of_tolerance
#print axioms E1_tolerance_of_sha_eq_one
#print axioms E1_tolerance_iff_sha_eq_one
#print axioms BSDRefinedE1_assembly
#print axioms BSDRefinedE1_conclusion_of_tolerance

end ThetLogos
