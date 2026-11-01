import ThetLogos.BSDRefinedPin
import ThetLogos.BSDCanonicalHeight
import ThetLogos.BSDPeriod
import ThetLogos.BSDLeadingCoeff
import ThetLogos.BSDIntervalPack

namespace ThetLogos

/-!
# ThetLogos.BSDRefinedAssembly — the assembly: the proved core, plus the E1 sibling statement

Source: the BSD rung-2 scoping memo §1.2, §1.4, §2 brick **B2-6**
(`scoping-bsd-rung-2-2026-10-29.md`). Design authority: the refined pin
(`ThetLogos.BSDRefinedPin`, brick B2-0, whose landed `BSDRefinedE2`
statement governs this brick), the torsion sweep (B2-1, in the pin),
the regulator object `regE2` and Seam B4 (B2-2,
`ThetLogos.BSDCanonicalHeight`), the period object `periodE2` (B2-3,
`ThetLogos.BSDPeriod`), the leading-coefficient readout `leadingCoeff`
(B2-4, `ThetLogos.BSDLeadingCoeff`), and the numeric interval pack
(B2-5, `ThetLogos.BSDIntervalPack`).

**What this file IS.** The pin's one genuinely provable content,
proved: at the landed objects `periodE2` and `regE2`, under exactly
the pin's named hypotheses, the tolerance identity

  `|(deriv D.L 1).re − refinedRHS sha periodE2 regE2 tam 1| ≤ 5e-3`

holds **iff `sha = 1`** — by real interval arithmetic over the three
(c) intervals and the Tamagawa seam. `sha` is a bound variable
throughout and its value is **derived, never input** (the circularity
fence, memo §1.2): `sha = 0` is excluded by Seam B1's positivity
(`ShaFiniteE2`), and every `sha ≥ 2` overshoots by
`≥ 2 · 2.91794114062 − 2.9200647683 ≈ 2.9158 > 5e-3`, while `sha = 1`
agrees within `0.0023 < 5e-3` (the product `periodE2 · regE2` lies in
`[2.91794114062, 2.92226863908]`, against
`L′ ∈ [2.9200447683, 2.9200647683]`). The torsion factor is the pin's
literal `1`: the assembly's first conjunct discharges it at the
landed objects as B2-1's conditional theorem
`E2_torsion_card_eq_one_of_nagellLutz`, with the shared seam
`NagellLutzCriterionE2` as an explicit antecedent of the assembly.

**The pin's exact form, and what is proved of it (on the face).** The
landed pin `BSDRefinedE2 periodE2 regE2` conjoins the tolerance and
`sha = 1` in its conclusion, universally over `sha`. The provable
content of that shape — and the memo §1.2 shape ("the identity holds
iff sha = 1") — is the **equivalence** proved here: for an arbitrary
`sha` the tolerance can fail (it does fail for `sha ≥ 2`), so no
honest proof can conjoin it for all `sha` from these hypotheses
alone. Two corollaries of the equivalence recover the pin's
conjoined conclusion in its exact stated form: at `sha = 1`
(`tolerance_of_sha_eq_one` gives the tolerance, and `sha = 1` is
then trivially the second conjunct), and for any `sha` for which the
tolerance is given (`BSDRefinedE2_conclusion_of_tolerance`). Nothing
stronger is claimed for the pin, and the pin itself is not edited.

**Seam B4 — the choice, reported (per the brick's instruction).**
The pin `BSDRefinedE2` is parameterized over bare reals
`(periodE2 regE2 : ℝ)`; its only mention of the regulator is the
antecedent `E2RegulatorValue regE2`, a statement about the
*parameter*. Seam B4 (`RegulatorBasisSeam`) is about the *landed
object* `regE2 = canonHeight P35` — its identification with *the*
regulator of `E2`. B4 is therefore carried exactly here, as an
antecedent of the assembly theorem (the brick that instantiates the
pin at the landed `regE2`), and **not** added to the pin's own
antecedents, where the pin speaks only of the parameter. It is not
dropped, and it is not consumed by the arithmetic: the interval
arithmetic needs only the (c) value of `regE2`, never its
identification — B4 is the licence for reading that value as "Reg"
in this statement, carried on the face.

**The three (c) intervals — forms.** The assembly speaks in the
pin's parameterized forms (`E2LPrimeValue D` on `(deriv D.L 1).re`,
`E2RegulatorValue regE2`, `E2PeriodValue periodE2`), as
`BSDRefinedE2` does. The B2-5 pack's concrete forms
(`ThetLogos.BSDIntervalPack.*`, stated on `leadingCoeff` and on the
landed objects with no parameter) are the *same* Props at the landed
objects; the three `intervalPack_*_iff` lemmas below record the
equivalence (each is `Iff.rfl`: `leadingCoeff D` is defined as
`deriv D.L 1`).

**Charter kill — disposition.** The assembly never uses the analytic
order of Sha as the algebraic group's order beyond the B1 region
licence. The only Sha hypothesis consumed is `ShaFiniteE2 sha`,
whose statable residue is `0 < sha` for the *denoted* finite order;
nothing about `Ш(E2)` as a group is stated or needed. The licence is
cited (Seam B1, in the pin), never extended. The kill does not fire.

**What this file is NOT — the board fences, on the face.**
- **Not the official statement.** The Clay prize statement is the
  rank equality (rung 1's `BSDRankEquality`, Wiles's chapter text).
  The refined formula assembled here is Wiles's Remark 1. Parts of
  the official BSD statement closed by this module: **0**. NO CLAIM.
- **Not existence of the package.** `BSDAnalyticData E2` existing is
  modularity — settled mathematics, formalization debt inherited
  from rung 1; the assembly is vacuous at any package-free reading,
  exactly as the pin is.
- **No laundered exactness.** The bars are the pin's: `±0.001` on
  Reg (hence on the sha conclusion), `1e-5` on `L′`, `1e-7` on `Ω`.
  The product bounds quoted above are exact products of the
  intervals' endpoints, not new precision.

**The E1 sibling (statement only).** The last section states — and
proves *nothing* about — the same Prop shape for
`E1 : y² = x³ − x`, per memo §1.4, with E1's own distinctly labeled
seams. The provenance difference is on its face: E1's L-value is
**T4-recorded** (LMFDB 32.a3), whereas E2's is the in-pass AFE
computation. **Scope kill — disposition:** stating the sibling
dragged in no rank-0 *proof* obligation: E1's finiteness enters only
as the labeled `E1RankZeroSeam` Prop (a definition stating a `Prop`,
proved nowhere), so the sibling lands as a Prop, not as a header
comment. (Rung 1's `algebraicRank_eq_zero_of_finite` reads rank 0
*from* finiteness; finiteness itself is never proved in this tree.)

Honesty tiers in this file:
- **T1 (proved):** the interval-pack equivalences, the product
  bounds, the two directions of the tolerance equivalence, the
  assembly theorem, and the pin-conclusion corollary.
- **T5 (statement, unproved by design):** the E1 sibling — `E1`,
  its seam Props, and `BSDRefinedE1`. Nothing about E1 is proved.

Status: NO CLAIM on BSD. Parts of the official statement closed: 0.
-/

/-! ## The (c) intervals: the pack's concrete forms are the pin's forms -/

/-- The B2-5 pack's regulator Prop is the pin's parameterized
`E2RegulatorValue` at the landed object `regE2` — the same `Prop`
(the intervals are identical), recorded as an `Iff`. -/
theorem intervalPack_regulator_iff :
    BSDIntervalPack.E2RegulatorValue ↔ E2RegulatorValue regE2 :=
  Iff.rfl

/-- The B2-5 pack's period Prop is the pin's parameterized
`E2PeriodValue` at the landed object `periodE2` — the same `Prop`. -/
theorem intervalPack_period_iff :
    BSDIntervalPack.E2PeriodValue ↔ E2PeriodValue periodE2 :=
  Iff.rfl

/-- The B2-5 pack's `L′` Prop (stated on the B2-4 readout
`leadingCoeff D`) is the pin's `E2LPrimeValue D` (stated on
`(deriv D.L 1).re`) — the same `Prop`, since `leadingCoeff D` is
defined as `deriv D.L 1`. -/
theorem intervalPack_lPrime_iff (D : BSDAnalyticData E2) :
    BSDIntervalPack.E2LPrimeValue D ↔ E2LPrimeValue D :=
  Iff.rfl

/-! ## The interval arithmetic core -/

/-- The product bounds: under the (c) hypotheses,
`periodE2 · regE2 ∈ [2.91794114062, 2.92226863908]` — the exact
products of the interval endpoints
(`2.1636817 · 1.3486` and `2.1636818 · 1.3506`). -/
theorem periodE2_mul_regE2_bounds
    (hReg : E2RegulatorValue regE2) (hPer : E2PeriodValue periodE2) :
    2.91794114062 ≤ periodE2 * regE2 ∧
      periodE2 * regE2 ≤ 2.92226863908 := by
  have hReg' : regE2 ∈ Set.Icc 1.3486 1.3506 := hReg
  have hPer' : periodE2 ∈ Set.Icc 2.1636817 2.1636818 := hPer
  obtain ⟨hrlo, hrhi⟩ := Set.mem_Icc.mp hReg'
  obtain ⟨hplo, hphi⟩ := Set.mem_Icc.mp hPer'
  have h1 : (2.1636817 : ℝ) * 1.3486 ≤ periodE2 * regE2 :=
    mul_le_mul hplo hrlo (by norm_num) (by linarith)
  have h2 : periodE2 * regE2 ≤ (2.1636818 : ℝ) * 1.3506 :=
    mul_le_mul hphi hrhi (by linarith) (by norm_num)
  norm_num at h1 h2
  exact ⟨by linarith, by linarith⟩

/-- The right-hand side at the seam values: with `tam = 1` (the
Tamagawa seam) and the pin's literal torsion `1`,
`refinedRHS sha periodE2 regE2 tam 1 = sha · periodE2 · regE2`. -/
theorem refinedRHS_tam_one (sha : ℕ) (tam : ℝ)
    (hTam : E2TamagawaValue tam) :
    refinedRHS sha periodE2 regE2 tam 1
      = (sha : ℝ) * periodE2 * regE2 := by
  have ht : tam = 1 := hTam
  rw [ht]
  unfold refinedRHS
  ring

/-- **The uniqueness direction.** Under the pin's named hypotheses,
if the tolerance identity holds then `sha = 1`: `sha = 0` is
excluded by Seam B1 (`ShaFiniteE2`, positivity of the denoted
order), and every `sha ≥ 2` makes the right-hand side at least
`2 · 2.91794114062`, overshooting `L′ ≤ 2.9200647683` by more than
the `5e-3` tolerance. `sha` is derived here, never input. -/
theorem sha_eq_one_of_tolerance (D : BSDAnalyticData E2) (sha : ℕ)
    (tam : ℝ) (hSha : ShaFiniteE2 sha) (hL : E2LPrimeValue D)
    (hTam : E2TamagawaValue tam) (hReg : E2RegulatorValue regE2)
    (hPer : E2PeriodValue periodE2)
    (htol : |(deriv D.L 1).re - refinedRHS sha periodE2 regE2 tam 1|
      ≤ 5e-3) :
    sha = 1 := by
  obtain ⟨hplo, -⟩ := periodE2_mul_regE2_bounds hReg hPer
  have hL' : |(deriv D.L 1).re - 2.9200547683| ≤ 1e-5 := hL
  rw [abs_le] at hL'
  rw [refinedRHS_tam_one sha tam hTam, abs_le] at htol
  have hpos : 0 < sha := hSha
  by_contra hne
  have hge : 2 ≤ sha := by omega
  have hcast : (2 : ℝ) ≤ (sha : ℝ) := by exact_mod_cast hge
  have hbig : (2 : ℝ) * 2.91794114062
      ≤ (sha : ℝ) * (periodE2 * regE2) :=
    mul_le_mul hcast hplo (by linarith) (by norm_num)
  linarith

/-- **The agreement direction.** At `sha = 1`, under the pin's named
hypotheses, the tolerance identity holds: `periodE2 · regE2` lies in
`[2.91794114062, 2.92226863908]` and `L′` in
`[2.9200447683, 2.9200647683]`, so the two differ by at most
`0.0023 < 5e-3`. -/
theorem tolerance_of_sha_eq_one (D : BSDAnalyticData E2) (tam : ℝ)
    (hL : E2LPrimeValue D) (hTam : E2TamagawaValue tam)
    (hReg : E2RegulatorValue regE2) (hPer : E2PeriodValue periodE2) :
    |(deriv D.L 1).re - refinedRHS 1 periodE2 regE2 tam 1| ≤ 5e-3 := by
  obtain ⟨hplo, hphi⟩ := periodE2_mul_regE2_bounds hReg hPer
  have hL' : |(deriv D.L 1).re - 2.9200547683| ≤ 1e-5 := hL
  rw [abs_le] at hL'
  have ht : tam = 1 := hTam
  rw [ht]
  have hRHS : refinedRHS (1 : ℝ) periodE2 regE2 1 1
      = periodE2 * regE2 := by
    unfold refinedRHS
    ring
  rw [hRHS, abs_le]
  constructor <;> linarith

/-! ## The assembly -/

/-- **The assembly theorem (brick B2-6).** At the landed objects
`(periodE2, regE2)`, from the named hypotheses only — each visible
as an antecedent: the shared Nagell–Lutz seam
`NagellLutzCriterionE2` (B2-1's discharge of the torsion factor),
Seam B4 `RegulatorBasisSeam` (carried at the landed `regE2`, where
the pin's parameter becomes the regulator object — see the module
header for the reported choice), and, inside, the pin's own
antecedents in its exact stated forms (`ShaFiniteE2`,
`analyticRank D = 1`, `E2LPrimeValue D`, `E2TamagawaValue tam`,
`E2RegulatorValue regE2`, `E2PeriodValue periodE2`) — the proved
core of the pin: the torsion cardinality is `1`, and the tolerance
identity in the pin's exact stated form holds **iff `sha = 1`**,
with `sha` derived by interval arithmetic, never input. This
closes zero parts of the official BSD statement. NO CLAIM. -/
theorem BSDRefinedE2_assembly
    (hNL : NagellLutzCriterionE2) (hB4 : RegulatorBasisSeam) :
    Nat.card (AddCommGroup.torsion E2.toAffine.Point) = 1 ∧
    ∀ (D : BSDAnalyticData E2) (sha : ℕ) (tam : ℝ),
      ShaFiniteE2 sha → analyticRank D = 1 →
      E2LPrimeValue D → E2TamagawaValue tam →
      E2RegulatorValue regE2 → E2PeriodValue periodE2 →
      (|(deriv D.L 1).re - refinedRHS sha periodE2 regE2 tam 1|
        ≤ 5e-3 ↔ sha = 1) := by
  have _hB4 := hB4
  refine ⟨E2_torsion_card_eq_one_of_nagellLutz hNL, ?_⟩
  intro D sha tam hSha _hRank hL hTam hReg hPer
  constructor
  · intro htol
    exact sha_eq_one_of_tolerance D sha tam hSha hL hTam hReg hPer htol
  · intro h1
    subst h1
    simpa using tolerance_of_sha_eq_one D tam hL hTam hReg hPer

/-- **The pin's conjoined conclusion, in its exact stated form,**
recovered from the assembly: for any `sha` satisfying the pin's
named hypotheses *and* the tolerance identity, the pin's conclusion
`|L′ − refinedRHS sha periodE2 regE2 tam 1| ≤ 5e-3 ∧ sha = 1`
holds — the first conjunct is the given tolerance, the second is
derived by `sha_eq_one_of_tolerance`. -/
theorem BSDRefinedE2_conclusion_of_tolerance
    (D : BSDAnalyticData E2) (sha : ℕ) (tam : ℝ)
    (hSha : ShaFiniteE2 sha) (hL : E2LPrimeValue D)
    (hTam : E2TamagawaValue tam) (hReg : E2RegulatorValue regE2)
    (hPer : E2PeriodValue periodE2)
    (htol : |(deriv D.L 1).re - refinedRHS sha periodE2 regE2 tam 1|
      ≤ 5e-3) :
    |(deriv D.L 1).re - refinedRHS sha periodE2 regE2 tam 1|
      ≤ 5e-3 ∧ sha = 1 :=
  ⟨htol, sha_eq_one_of_tolerance D sha tam hSha hL hTam hReg hPer htol⟩

/-! ## The E1 sibling — statement only; nothing about E1 is proved -/

/-- The sibling curve `E1 : y² = x³ − x` over `ℚ`. Statement only:
no theorem about `E1` appears in this module. -/
def E1 : WeierstrassCurve ℚ := ⟨0, 0, 0, -1, 0⟩

/-- **E1's `rankZero_seam`, distinctly labeled.** `E1(ℚ)` is finite.
This is recorded / Kolyvagin-region knowledge, **not** in-tree: rung
1's `algebraicRank_eq_zero_of_finite` reads the rank `0` *from*
finiteness, and finiteness itself is proved nowhere in this tree.
Stated here as a `Prop`, proved nowhere. -/
def E1RankZeroSeam : Prop :=
  Finite E1.toAffine.Point

/-- **E1's torsion seam.** `#E1(ℚ)_tors = 4` (the torsion is
`ℤ/2 × ℤ/2`; the sweep *finds* points here, unlike E2). Carried
modulo the same shared Nagell–Lutz seam method as E2's discharge —
the criterion for E1 is not in-tree — and stated here as a `Prop`,
proved nowhere. -/
def E1TorsionCardSeam : Prop :=
  Nat.card (AddCommGroup.torsion E1.toAffine.Point) = 4

/-- **E1's Sha seam (the B1 analogue, distinctly labeled).** The
sibling's `sha` denotes a finite order; its statable residue is
positivity, as in `ShaFiniteE2`. The identification with `#Ш(E1)`
rides on the same region licence as E2's, cited on the pin's face,
never extended. Stated as a `Prop`, proved nowhere. -/
def E1ShaFiniteSeam (sha : ℕ) : Prop :=
  0 < sha

/-- **E1's Tamagawa seam instance.** `∏c_p = 2` for E1, as a named
hypothesis `Prop` in the same form as E2's `E2TamagawaValue` (the
Tamagawa object does not exist in Mathlib). Proved nowhere. -/
def E1TamagawaValue (tam : ℝ) : Prop :=
  tam = 2

/-- **E1's L-value, T4-recorded.** `L(E1, 1) ≈ 0.655514389`, recorded
from LMFDB 32.a3 — tier **T4**, in contrast to E2's in-pass AFE
computation (the provenance difference is the point of the label).
The bar `1e-9` is the rounding bar of the nine quoted decimal
digits, nothing tighter. Stated as a `Prop`, proved nowhere. -/
def E1LValueT4 (Lval : ℝ) : Prop :=
  |Lval - 0.655514389| ≤ 1e-9

/-- **The E1 sibling pin (statement only, brick B2-6).** The same
Prop shape as `BSDRefinedE2`, for `E1 : y² = x³ − x`, with E1's own
labeled seams as antecedents: the rank-0 seam, the torsion seam
(`#tors = 4`, hence the literal `4` in `refinedRHS`), the Sha seam,
the T4 L-value, and the Tamagawa seam instance (`∏c_p = 2`, hence
`tam`); the regulator is the literal `1` (rank-0 empty-determinant
convention, memo §1.4) and `ΩE1` is a bare real parameter — no
period value for E1 is recorded in the memo, and none is invented
here. With the seams discharged at their recorded values the
right-hand side reduces to `ΩE1 / 8`, the memo's verified reduced
form `L(E1, 1) = Ω_E1 / 8`. **No assembly theorem is stated or
proved for E1 in this rung** — its L-value's provenance (T4,
LMFDB-recorded) differs from E2's (in-pass computed), and mixing
the two in one proved core would blur exactly that line. -/
def BSDRefinedE1 : Prop :=
  ∀ (Lval ΩE1 : ℝ) (sha : ℕ) (tam : ℝ),
    E1RankZeroSeam → E1TorsionCardSeam → E1ShaFiniteSeam sha →
    E1LValueT4 Lval → E1TamagawaValue tam →
    |Lval - refinedRHS sha ΩE1 1 tam 4| ≤ 5e-3 ∧ sha = 1

/-! ## Axiom checks (headline results) -/

#print axioms intervalPack_regulator_iff
#print axioms intervalPack_period_iff
#print axioms intervalPack_lPrime_iff
#print axioms periodE2_mul_regE2_bounds
#print axioms refinedRHS_tam_one
#print axioms sha_eq_one_of_tolerance
#print axioms tolerance_of_sha_eq_one
#print axioms BSDRefinedE2_assembly
#print axioms BSDRefinedE2_conclusion_of_tolerance

end ThetLogos
