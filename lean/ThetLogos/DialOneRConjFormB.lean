import Mathlib.Tactic
import ThetLogos.DialOneGradeRConjAmend
import ThetLogos.DialOneAntiparticleBase
import ThetLogos.DialOnePiAntiPackage
import ThetLogos.DialOneSwapOrbitBase
import ThetLogos.DialOneShapeBIdentification
import ThetLogos.DialOneExtraction

open Matrix Complex
open ThetLogos.Track1RouteB
open ThetLogos.PreOptionARepresentation
open ThetLogos.HyperchargeForcing
open ThetLogos.DialOneSeatTiePin
open ThetLogos.DialOneGammaTracePin
open ThetLogos.DialOneGammaFamilyPin
open ThetLogos.DialOneGradeRConjPin
open ThetLogos.DialOneGradeRConjAmend
open ThetLogos.DialOneConjugationCounterexample
open ThetLogos.DialOneAntiparticleChapter
open ThetLogos.DialOneAntiparticleBase
open ThetLogos.DialOneSwapOrbit
open ThetLogos.DialOneSwapOrbitBase

/-!
# R-CONJ FORM B (Q1) — exhibited-points twisted uniqueness

NO CLAIM; Dial 1 = 0. Zero's chosen Form B (extraction re-scope
§3.3) with the pinned twist set Φ = {id, colourTwist}: for each
exhibited strengthened point π, ∃ φ ∈ Φ and ∃ U ∈
RealCentralizingClass with π = conjRep U (pi1 ∘ φ).

Verdicts per point: pi1, piU, piAnti, conjRep conjU piAnti PLACE
(witnesses below). `orbitRep allSwapBits` does NOT place, for
either twist, for any amended-class U — obstruction proved at
full rank in §5 (twist half: the plain trace, the O-A genus;
id half: a seat-⟨10⟩ row argument spending γ_F-commutation, the
u1-only diagonal pattern, and DF_oneGen-commutation).
K-RCONJ-TWIST-VAC does not fire: colourTwist's credential is
proved from its definition (§1), never from reaching piAnti.
-/

namespace ThetLogos.DialOneRConjFormB

/-- The pinned twist set's membership predicate (Form B, Φ =
{id, colourTwist}, both as functions `AF → AF`). -/
def TwistMem (φ : AF → AF) : Prop := φ = id ∨ φ = colourTwist

/-- The Form B placement statement for a single point. -/
def FormBPlaced (π : AF → Matrix (Fin 32) (Fin 32) ℂ) : Prop :=
  ∃ φ : AF → AF, TwistMem φ ∧
    ∃ U, RealCentralizingClass U ∧ π = conjRep U (pi1 ∘ φ)

/-! ## §1 The twist credential (K-RCONJ-TWIST-VAC hygiene)

`colourTwist` is defined (DialOneAntiparticleBase:90) from
seated structure alone — `⟨a.u1, a.q, a.color.map (starRingEnd
ℂ)⟩`: the ℂ and ℍ summands untouched, entrywise conjugation on
the colour summand. The homomorphism properties below are the
landed proofs from that definition; none mentions `piAnti`. -/

/-- **Automorphism credential for `colourTwist`**, from its
definition: it fixes the u1 and q summands, acts entrywise by
`star` on colour, and preserves `afMul`, `afAdd`, `afStar`,
`afOne`, `afZero`; it is involutive, hence bijective. -/
theorem colourTwist_credential :
    (∀ a : AF, (colourTwist a).u1 = a.u1 ∧ (colourTwist a).q = a.q)
    ∧ (∀ (a : AF) (k l : Fin 3), (colourTwist a).color k l = star (a.color k l))
    ∧ (∀ a b : AF, colourTwist (afMul a b)
        = afMul (colourTwist a) (colourTwist b))
    ∧ (∀ a b : AF, colourTwist (afAdd a b)
        = afAdd (colourTwist a) (colourTwist b))
    ∧ (∀ a : AF, colourTwist (afStar a) = afStar (colourTwist a))
    ∧ colourTwist afOne = afOne
    ∧ colourTwist afZero = afZero
    ∧ Function.Involutive colourTwist
    ∧ Function.Bijective colourTwist :=
  ⟨fun _a => ⟨rfl, rfl⟩,
   fun a k l => colourTwist_color_apply a k l,
   colourTwist_afMul, colourTwist_afAdd, colourTwist_afStar,
   colourTwist_afOne, colourTwist_afZero,
   colourTwist_involutive, colourTwist_bijective⟩

/-! ## §2 The identity matrix is an amended-class member -/

/-- **`1 ∈ RealCentralizingClass`** (read-level in the
class-level scoping §0; landed here): unitarity and the
Dirac/grading commutations are trivial at `1`, `piOp 1 = 1`
is landed (`DialOneExtraction.piOp_one`), and `1` is real. -/
theorem one_realCentralizing :
    RealCentralizingClass (1 : Matrix (Fin 32) (Fin 32) ℂ) :=
  ⟨⟨by simp, by simp, by simp, by
      rw [ThetLogos.DialOneExtraction.piOp_one, Matrix.transpose_one],
    fun Ynu Ye Yu Yd => by simp⟩,
   by simp [IsRealMat, Matrix.conjTranspose_one, Matrix.transpose_one]⟩

/-- Conjugation by `1` is the identity on representations. -/
theorem conjRep_one (π : AF → Matrix (Fin 32) (Fin 32) ℂ) :
    conjRep 1 π = π := by
  funext _a
  simp [conjRep, Matrix.transpose_one]

/-! ## §3 Preservation under the twist, at the exhibited points

The twisted base point `pi1 ∘ colourTwist` IS `piAnti`
(landed, ∀ a), and its strengthened status is landed — the
twist of a strengthened rep used anywhere below is proved
strengthened, not assumed. Its `conjU`-conjugate's status is
likewise landed (DialOnePiAntiPackage). -/

theorem pi1_comp_colourTwist_eq_piAnti : pi1 ∘ colourTwist = piAnti := by
  funext a
  exact (piAnti_eq_pi1_colourTwist a).symm

/-- **Preservation under twist (exhibited clauses)**: the
twisted point and its exhibited class conjugate are both in
the strengthened family. -/
theorem twist_preservation_exhibited :
    DialOneStrengthenedFam (pi1 ∘ colourTwist)
    ∧ DialOneStrengthenedFam (conjRep conjU (pi1 ∘ colourTwist)) := by
  rw [pi1_comp_colourTwist_eq_piAnti]
  exact ⟨strengthenedFam_piAnti,
    ThetLogos.DialOnePiAntiPackage.strengthened_conjRep_piAnti⟩

/-! ## §4 The four placements -/

/-- **pi1 places**: φ = id, U = 1. -/
theorem placed_pi1 : FormBPlaced pi1 :=
  ⟨id, Or.inl rfl, 1, one_realCentralizing, by
    rw [Function.comp_id, conjRep_one]⟩

/-- **piU places**: φ = id, U = conjU (landed orbit fact). -/
theorem placed_piU : FormBPlaced piU :=
  ⟨id, Or.inl rfl, conjU, conjU_realCentralizing, by
    rw [Function.comp_id]; exact piU_eq_conjRep⟩

/-- **piAnti places**: φ = colourTwist, U = 1. The twist, not
a conjugation, carries the trace change (cf. §5). -/
theorem placed_piAnti : FormBPlaced piAnti :=
  ⟨colourTwist, Or.inr rfl, 1, one_realCentralizing, by
    rw [pi1_comp_colourTwist_eq_piAnti, conjRep_one]⟩

/-- **`conjRep conjU piAnti` places**: φ = colourTwist,
U = conjU — transport of the piAnti placement. -/
theorem placed_conjRep_piAnti : FormBPlaced (conjRep conjU piAnti) :=
  ⟨colourTwist, Or.inr rfl, conjU, conjU_realCentralizing, by
    rw [pi1_comp_colourTwist_eq_piAnti]⟩

/-! ## §5 The all-swap point does NOT place

`orbitRep allSwapBits` is a strengthened point (landed:
`DialOneSwapOrbitBase.allSwap_mem_strengthened`), but it is
in neither exhibited twist-orbit of `pi1`:

* φ = colourTwist is killed by the plain trace (the O-A
  genus): the swap corrections are u1-data, so at a colour
  witness `allSwap` has `pi1`'s trace, while the twist flips
  the colour term's star — the two traces are `-4i` and `4i`.
  The trace is invariant under `conjRep U` for every
  transpose-unitary `U`, a fortiori every class member.
* φ = id is killed by a seat-⟨10⟩ row argument: intertwining
  `U * pi1 = allSwap * U` at the u1-only witness `a0` (where
  `pi1 a0` is diagonal and `allSwap a0` has diagonal `-i` at
  seat 10) forces row 10 of `U` into the seats where the two
  diagonals agree; γ_F-commutation removes the seats outside
  8–23, and DF_oneGen-commutation at the six remaining seats
  removes those. Row 10 is zero, contradicting `U * Uᵀ = 1`.
  (Numerically the class-intertwiner space `pi1 → allSwap`
  is 1-dimensional, spanned by a rank-8 matrix; the argument
  below is the entrywise form of that fact at one row.) -/

/-- Trace invariance under sandwich conjugation. -/
theorem trace_conjRep_eq (U X : Matrix (Fin 32) (Fin 32) ℂ)
    (h : Uᵀ * U = 1) : Matrix.trace (U * X * Uᵀ) = Matrix.trace X := by
  have h1 : U * X * Uᵀ = U * (X * Uᵀ) := by simp [Matrix.mul_assoc]
  have h2 : (X * Uᵀ) * U = X := by
    calc (X * Uᵀ) * U = X * (Uᵀ * U) := Matrix.mul_assoc _ _ _
    _ = X := by rw [h, Matrix.mul_one]
  rw [h1, Matrix.trace_mul_comm U (X * Uᵀ), h2]

/-- The colour witness for the trace half: `tr(color) = i`,
all other data zero. -/
noncomputable def colourWitness : AF :=
  { u1 := 0, q := 0,
    color := Matrix.diagonal (fun k : Fin 3 => if k = 0 then Complex.I else 0) }

/-- Diagonal value profile of a representation at a point,
supported on the four colour-diagonal seats. -/
def diagProfile (z : ℂ) : Fin 32 → ℂ := fun i =>
  if i = ⟨18, by norm_num⟩ ∨ i = ⟨19, by norm_num⟩
      ∨ i = ⟨26, by norm_num⟩ ∨ i = ⟨27, by norm_num⟩ then z else 0

theorem pi1_diag_colourWitness : ∀ i : Fin 32,
    pi1 colourWitness i i = diagProfile (-Complex.I) i := by
  intro i
  fin_cases i <;> simp [pi1, colourWitness, diagProfile, Complex.conj_I]

theorem pi1_diag_colourWitness_twist : ∀ i : Fin 32,
    pi1 (colourTwist colourWitness) i i = diagProfile (Complex.I) i := by
  intro i
  fin_cases i <;> simp only [pi1, colourTwist, colourWitness, diagProfile,
    Matrix.map_apply, starRingEnd_apply, Matrix.diagonal_apply] <;> norm_num

theorem sum_diagProfile : ∀ z : ℂ, ∑ i : Fin 32, diagProfile z i = 4 * z := by
  intro z
  set S : Finset (Fin 32) := {⟨18, by norm_num⟩, ⟨19, by norm_num⟩,
    ⟨26, by norm_num⟩, ⟨27, by norm_num⟩} with hS
  have hsub : ∑ i : Fin 32, diagProfile z i = ∑ i ∈ S, diagProfile z i := by
    refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
    intro i _ hi
    simp only [hS, Finset.mem_insert, Finset.mem_singleton, not_or] at hi
    rw [diagProfile]
    split_ifs with h
    · exfalso
      rcases h with rfl | rfl | rfl | rfl
      · exact hi.1 rfl
      · exact hi.2.1 rfl
      · exact hi.2.2.1 rfl
      · exact hi.2.2.2 rfl
    · rfl
  rw [hsub, hS, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [diagProfile, ite_true, or_true, true_or]
  ring

theorem trace_pi1_colourWitness :
    Matrix.trace (pi1 colourWitness) = -4 * Complex.I := by
  rw [Matrix.trace]
  simp only [Matrix.diag_apply]
  rw [Finset.sum_congr rfl (fun i _ => pi1_diag_colourWitness i), sum_diagProfile]
  ring

theorem trace_pi1_colourWitness_twist :
    Matrix.trace (pi1 (colourTwist colourWitness)) = 4 * Complex.I := by
  rw [Matrix.trace]
  simp only [Matrix.diag_apply]
  rw [Finset.sum_congr rfl (fun i _ => pi1_diag_colourWitness_twist i),
    sum_diagProfile]

/-- **All-swap, twist half**: no amended-class `U` conjugates
`pi1 ∘ colourTwist` to `orbitRep allSwapBits`. -/
theorem allSwap_twist_obstruction (U : Matrix (Fin 32) (Fin 32) ℂ)
    (hU : RealCentralizingClass U)
    (heq : orbitRep allSwapBits = conjRep U (pi1 ∘ colourTwist)) : False := by
  have htr := congrArg Matrix.trace (congrFun heq colourWitness)
  have h1 : orbitRep allSwapBits colourWitness = pi1 colourWitness :=
    ThetLogos.DialOneShapeBIdentification.orbitRep_of_u1_zero allSwapBits rfl
  have h2 : conjRep U (pi1 ∘ colourTwist) colourWitness
      = U * pi1 (colourTwist colourWitness) * Uᵀ := rfl
  rw [h1, h2, trace_conjRep_eq U _ hU.1.2.1,
    trace_pi1_colourWitness, trace_pi1_colourWitness_twist] at htr
  have h3 := congrArg Complex.im htr
  simp at h3
  norm_num at h3

/-- The u1-only witness for the id half: `u1 = i`, all other
data zero. At this point `pi1` is diagonal. -/
noncomputable def u1Witness : AF := { u1 := Complex.I, q := 0, color := 0 }

theorem pi1_u1Witness_offDiag : ∀ k j : Fin 32, k ≠ j → pi1 u1Witness k j = 0 := by
  intro k j hkj
  fin_cases k <;> fin_cases j <;> first
    | exact absurd rfl hkj
    | simp [pi1, u1Witness]

theorem pi1_u1Witness_diag8 :
    pi1 u1Witness ⟨8, by norm_num⟩ ⟨8, by norm_num⟩ = Complex.I := by
  simpa [u1Witness] using pi1_entry_nuR u1Witness

theorem pi1_u1Witness_diag10 :
    pi1 u1Witness ⟨10, by norm_num⟩ ⟨10, by norm_num⟩ = Complex.I := by
  simpa [u1Witness] using pi1_entry_quarkR u1Witness 0 0 0 0

theorem pi1_u1Witness_diag12 :
    pi1 u1Witness ⟨12, by norm_num⟩ ⟨12, by norm_num⟩ = Complex.I := by
  simpa [u1Witness] using pi1_entry_quarkR u1Witness 1 1 0 0

theorem pi1_u1Witness_diag14 :
    pi1 u1Witness ⟨14, by norm_num⟩ ⟨14, by norm_num⟩ = Complex.I := by
  simpa [u1Witness] using pi1_entry_quarkR u1Witness 2 2 0 0

theorem pi1_u1Witness_diag18 :
    pi1 u1Witness ⟨18, by norm_num⟩ ⟨18, by norm_num⟩ = 0 := by
  simpa [u1Witness] using pi1_entry_quarkLc u1Witness 0 0 0 0

theorem pi1_u1Witness_diag19 :
    pi1 u1Witness ⟨19, by norm_num⟩ ⟨19, by norm_num⟩ = 0 := by
  simpa [u1Witness] using pi1_entry_quarkLc u1Witness 0 0 1 1

theorem pi1_u1Witness_diag20 :
    pi1 u1Witness ⟨20, by norm_num⟩ ⟨20, by norm_num⟩ = 0 := by
  simpa [u1Witness] using pi1_entry_quarkLc u1Witness 1 1 0 0

theorem pi1_u1Witness_diag21 :
    pi1 u1Witness ⟨21, by norm_num⟩ ⟨21, by norm_num⟩ = 0 := by
  simpa [u1Witness] using pi1_entry_quarkLc u1Witness 1 1 1 1

theorem pi1_u1Witness_diag22 :
    pi1 u1Witness ⟨22, by norm_num⟩ ⟨22, by norm_num⟩ = 0 := by
  simpa [u1Witness] using pi1_entry_quarkLc u1Witness 2 2 0 0

theorem pi1_u1Witness_diag23 :
    pi1 u1Witness ⟨23, by norm_num⟩ ⟨23, by norm_num⟩ = 0 := by
  simpa [u1Witness] using pi1_entry_quarkLc u1Witness 2 2 1 1

/-- `gammaF` at seat 10 is `-1`. -/
theorem gammaF_ten_ten :
    gammaF ⟨10, by norm_num⟩ ⟨10, by norm_num⟩ = -1 := by simp [gammaF]

/-- `gammaF` is `+1` on the outer blocks. -/
theorem gammaF_diag_one (j : Fin 32) (hj : j.val < 8 ∨ 24 ≤ j.val) :
    gammaF j j = 1 := by
  have hk : gammaF j j = (if j.val < 8 then (1 : ℂ)
      else if j.val < 16 then -1 else if j.val < 24 then -1 else 1) := by
    simp [gammaF]
  rw [hk]
  split_ifs <;> simp_all <;> omega

/-- Row-10 kill by γ_F-commutation: seats outside 8–23. -/
theorem row10_zero_of_gamma (U : Matrix (Fin 32) (Fin 32) ℂ)
    (hU : RealCentralizingClass U) (j : Fin 32)
    (hj : j.val < 8 ∨ 24 ≤ j.val) : U ⟨10, by norm_num⟩ j = 0 := by
  have e := congrFun (congrFun hU.1.2.2.1 ⟨10, by norm_num⟩) j
  rw [gammaF_mul_apply, mul_gammaF_apply, gammaF_ten_ten,
    gammaF_diag_one j hj] at e
  have e2 : (-1 : ℂ) * U ⟨10, by norm_num⟩ j = U ⟨10, by norm_num⟩ j := by
    simpa using e
  rw [neg_one_mul] at e2
  have h2x : (2 : ℂ) * U ⟨10, by norm_num⟩ j = 0 := by linear_combination -e2
  exact (mul_eq_zero.mp h2x).resolve_left (by norm_num)

/-- Row-10 kill by the diagonal pattern at the u1 witness:
any seat where `pi1 u1Witness`'s diagonal differs from the
all-swap diagonal `-i` at seat 10. -/
theorem row10_zero_of_pattern (U : Matrix (Fin 32) (Fin 32) ℂ)
    (hconj : ∀ a, U * pi1 a = orbitRep allSwapBits a * U) (j : Fin 32)
    (hj : pi1 u1Witness j j ≠ -Complex.I) : U ⟨10, by norm_num⟩ j = 0 := by
  have e := congrFun (congrFun (hconj u1Witness) ⟨10, by norm_num⟩) j
  have eL : (U * pi1 u1Witness) ⟨10, by norm_num⟩ j
      = U ⟨10, by norm_num⟩ j * pi1 u1Witness j j := by
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_single (a := j)
      (f := fun k => U ⟨10, by norm_num⟩ k * pi1 u1Witness k j)
    · intro k _ hk
      rw [pi1_u1Witness_offDiag k j hk, mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hdiagS : orbitRep allSwapBits u1Witness ⟨10, by norm_num⟩ ⟨10, by norm_num⟩
      = -Complex.I := by
    have hswap : swapCorr u1Witness ⟨10, by norm_num⟩ ⟨10, by norm_num⟩
        = star (u1Witness.u1) - u1Witness.u1 :=
      ThetLogos.DialOneSwapOrbitBase.swapCorr_uSeat_diag 0 u1Witness
    rw [ThetLogos.DialOneSwapOrbitBase.allSwap_eq, Matrix.add_apply,
      pi1_u1Witness_diag10, hswap,
      show u1Witness.u1 = Complex.I from rfl]
    have hstar : star (Complex.I) = -Complex.I := by simp
    rw [hstar]
    ring
  have eR : (orbitRep allSwapBits u1Witness * U) ⟨10, by norm_num⟩ j
      = (-Complex.I) * U ⟨10, by norm_num⟩ j := by
    have hmain : orbitRep allSwapBits u1Witness ⟨10, by norm_num⟩ ⟨10, by norm_num⟩
          * U ⟨10, by norm_num⟩ j
        = (-Complex.I) * U ⟨10, by norm_num⟩ j := by
      rw [hdiagS]
    rw [Matrix.mul_apply, ← hmain]
    apply Finset.sum_eq_single (a := ⟨10, by norm_num⟩)
      (f := fun k => orbitRep allSwapBits u1Witness ⟨10, by norm_num⟩ k * U k j)
    · intro k _ hk
      rw [ThetLogos.DialOneSwapOrbitBase.allSwap_eq, Matrix.add_apply,
        pi1_u1Witness_offDiag ⟨10, by norm_num⟩ k (Ne.symm hk),
        ThetLogos.DialOneSwapOrbitBase.swapCorr_apply_of_ne (Ne.symm hk),
        add_zero, zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [eL, eR] at e
  have h2 : U ⟨10, by norm_num⟩ j * (pi1 u1Witness j j + Complex.I) = 0 := by
    have hrw : U ⟨10, by norm_num⟩ j * (pi1 u1Witness j j + Complex.I)
        = U ⟨10, by norm_num⟩ j * pi1 u1Witness j j
          + Complex.I * U ⟨10, by norm_num⟩ j := by ring
    rw [hrw, e]
    ring
  rcases mul_eq_zero.mp h2 with h | h
  · exact h
  · exact absurd (eq_neg_of_add_eq_zero_left h) hj

/-- Entry of `DF_oneGen * U` at row 10: only the `dparSeat`
partner seat 2 contributes, with coefficient `Yu`. -/
theorem dfU_entry (U : Matrix (Fin 32) (Fin 32) ℂ) (Ynu Ye Yu Yd : ℝ)
    (j : Fin 32) :
    (DF_oneGen Ynu Ye Yu Yd * U) ⟨10, by norm_num⟩ j
      = (Yu : ℂ) * U ⟨2, by norm_num⟩ j := by
  have hmain : DF_oneGen Ynu Ye Yu Yd ⟨10, by norm_num⟩ ⟨2, by norm_num⟩
        * U ⟨2, by norm_num⟩ j
      = (Yu : ℂ) * U ⟨2, by norm_num⟩ j := by
    rw [df_entry]
    simp only [show dparSeat ⟨10, by norm_num⟩ = ⟨2, by norm_num⟩ from rfl,
      if_pos rfl,
      show dcoef Ynu Ye Yu Yd ⟨10, by norm_num⟩ = (Yu : ℂ) from by simp [dcoef],
      if_true]
  rw [Matrix.mul_apply, ← hmain]
  apply Finset.sum_eq_single (a := ⟨2, by norm_num⟩)
    (f := fun k => DF_oneGen Ynu Ye Yu Yd ⟨10, by norm_num⟩ k * U k j)
  · intro k _ hk
    rw [df_entry]
    simp only [show dparSeat ⟨10, by norm_num⟩ = ⟨2, by norm_num⟩ from rfl]
    rw [if_neg hk, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- Entry of `U * DF_oneGen` at row 10: only the `dparSeat`
partner of the column contributes. -/
theorem Udf_entry (U : Matrix (Fin 32) (Fin 32) ℂ) (Ynu Ye Yu Yd : ℝ)
    (j : Fin 32) :
    (U * DF_oneGen Ynu Ye Yu Yd) ⟨10, by norm_num⟩ j
      = U ⟨10, by norm_num⟩ (dparSeat j) * dcoef Ynu Ye Yu Yd (dparSeat j) := by
  have hmain : U ⟨10, by norm_num⟩ (dparSeat j)
        * DF_oneGen Ynu Ye Yu Yd (dparSeat j) j
      = U ⟨10, by norm_num⟩ (dparSeat j)
        * dcoef Ynu Ye Yu Yd (dparSeat j) := by
    rw [df_entry, dparSeat_involutive, if_pos rfl]
  rw [Matrix.mul_apply, ← hmain]
  apply Finset.sum_eq_single (a := dparSeat j)
    (f := fun k => U ⟨10, by norm_num⟩ k * DF_oneGen Ynu Ye Yu Yd k j)
  · intro k _ hk
    rw [df_entry, if_neg, mul_zero]
    intro hjk
    apply hk
    have h2 : dparSeat j = dparSeat (dparSeat k) := by rw [hjk]
    rw [dparSeat_involutive] at h2
    exact h2.symm
  · intro h; exact absurd (Finset.mem_univ _) h

/-- Row-10 kill by DF_oneGen-commutation at one seat. -/
theorem row10_zero_of_df (U : Matrix (Fin 32) (Fin 32) ℂ)
    (hU : RealCentralizingClass U) (j k : Fin 32) (Ynu Ye Yu Yd : ℝ)
    (hjk : dparSeat j = k) (hc : dcoef Ynu Ye Yu Yd k = 1) (hYu : Yu = 0) :
    U ⟨10, by norm_num⟩ k = 0 := by
  have e := congrFun (congrFun (hU.1.2.2.2.2 Ynu Ye Yu Yd) ⟨10, by norm_num⟩) j
  rw [dfU_entry, Udf_entry, hjk, hc, hYu] at e
  simpa using e.symm

/-- `Complex.I ≠ -Complex.I`. -/
theorem I_ne_negI : Complex.I ≠ -Complex.I := by
  intro h
  have h2 := congrArg Complex.im h
  simp at h2
  norm_num at h2

/-- **Row 10 of any would-be conjugator is zero.** -/
theorem row10_zero (U : Matrix (Fin 32) (Fin 32) ℂ)
    (hU : RealCentralizingClass U)
    (hconj : ∀ a, U * pi1 a = orbitRep allSwapBits a * U) :
    ∀ j, U ⟨10, by norm_num⟩ j = 0 := by
  intro j
  fin_cases j
  · exact row10_zero_of_gamma U hU _ (Or.inl (by norm_num))
  · exact row10_zero_of_gamma U hU _ (Or.inl (by norm_num))
  · exact row10_zero_of_gamma U hU _ (Or.inl (by norm_num))
  · exact row10_zero_of_gamma U hU _ (Or.inl (by norm_num))
  · exact row10_zero_of_gamma U hU _ (Or.inl (by norm_num))
  · exact row10_zero_of_gamma U hU _ (Or.inl (by norm_num))
  · exact row10_zero_of_gamma U hU _ (Or.inl (by norm_num))
  · exact row10_zero_of_gamma U hU _ (Or.inl (by norm_num))
  · exact row10_zero_of_pattern U hconj _
      (by intro hh; exact I_ne_negI (pi1_u1Witness_diag8.symm.trans hh))
  · exact row10_zero_of_df U hU ⟨1, by norm_num⟩ ⟨9, by norm_num⟩ 0 1 0 0
      rfl (by simp [dcoef]) rfl
  · exact row10_zero_of_pattern U hconj _
      (by intro hh; exact I_ne_negI (pi1_u1Witness_diag10.symm.trans hh))
  · exact row10_zero_of_df U hU ⟨3, by norm_num⟩ ⟨11, by norm_num⟩ 0 0 0 1
      rfl (by simp [dcoef]) rfl
  · exact row10_zero_of_pattern U hconj _
      (by intro hh; exact I_ne_negI (pi1_u1Witness_diag12.symm.trans hh))
  · exact row10_zero_of_df U hU ⟨5, by norm_num⟩ ⟨13, by norm_num⟩ 0 0 0 1
      rfl (by simp [dcoef]) rfl
  · exact row10_zero_of_pattern U hconj _
      (by intro hh; exact I_ne_negI (pi1_u1Witness_diag14.symm.trans hh))
  · exact row10_zero_of_df U hU ⟨7, by norm_num⟩ ⟨15, by norm_num⟩ 0 0 0 1
      rfl (by simp [dcoef]) rfl
  · exact row10_zero_of_df U hU ⟨24, by norm_num⟩ ⟨16, by norm_num⟩ 1 0 0 0
      rfl (by simp [dcoef]) rfl
  · exact row10_zero_of_df U hU ⟨25, by norm_num⟩ ⟨17, by norm_num⟩ 0 1 0 0
      rfl (by simp [dcoef]) rfl
  · exact row10_zero_of_pattern U hconj _
      (by intro hh; have h2 := congrArg Complex.im (pi1_u1Witness_diag18.symm.trans hh); simp at h2)
  · exact row10_zero_of_pattern U hconj _
      (by intro hh; have h2 := congrArg Complex.im (pi1_u1Witness_diag19.symm.trans hh); simp at h2)
  · exact row10_zero_of_pattern U hconj _
      (by intro hh; have h2 := congrArg Complex.im (pi1_u1Witness_diag20.symm.trans hh); simp at h2)
  · exact row10_zero_of_pattern U hconj _
      (by intro hh; have h2 := congrArg Complex.im (pi1_u1Witness_diag21.symm.trans hh); simp at h2)
  · exact row10_zero_of_pattern U hconj _
      (by intro hh; have h2 := congrArg Complex.im (pi1_u1Witness_diag22.symm.trans hh); simp at h2)
  · exact row10_zero_of_pattern U hconj _
      (by intro hh; have h2 := congrArg Complex.im (pi1_u1Witness_diag23.symm.trans hh); simp at h2)
  · exact row10_zero_of_gamma U hU _ (Or.inr (by norm_num))
  · exact row10_zero_of_gamma U hU _ (Or.inr (by norm_num))
  · exact row10_zero_of_gamma U hU _ (Or.inr (by norm_num))
  · exact row10_zero_of_gamma U hU _ (Or.inr (by norm_num))
  · exact row10_zero_of_gamma U hU _ (Or.inr (by norm_num))
  · exact row10_zero_of_gamma U hU _ (Or.inr (by norm_num))
  · exact row10_zero_of_gamma U hU _ (Or.inr (by norm_num))
  · exact row10_zero_of_gamma U hU _ (Or.inr (by norm_num))

/-- **All-swap, id half**: no amended-class `U` conjugates
`pi1` to `orbitRep allSwapBits`. -/
theorem allSwap_id_obstruction (U : Matrix (Fin 32) (Fin 32) ℂ)
    (hU : RealCentralizingClass U)
    (heq : orbitRep allSwapBits = conjRep U pi1) : False := by
  have hconj : ∀ a, U * pi1 a = orbitRep allSwapBits a * U := by
    intro a
    have h1 : orbitRep allSwapBits a = U * pi1 a * Uᵀ := congrFun heq a
    have h2 : orbitRep allSwapBits a * U = U * pi1 a := by
      rw [h1]
      calc (U * pi1 a * Uᵀ) * U = (U * pi1 a) * (Uᵀ * U) := Matrix.mul_assoc _ _ _
      _ = U * pi1 a := by rw [hU.1.2.1, Matrix.mul_one]
    exact h2.symm
  have hrow := row10_zero U hU hconj
  have h10 : (U * Uᵀ) ⟨10, by norm_num⟩ ⟨10, by norm_num⟩ = 0 := by
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro j _
    rw [Matrix.transpose_apply, hrow j, zero_mul]
  have h11 : (U * Uᵀ) ⟨10, by norm_num⟩ ⟨10, by norm_num⟩ = 1 := by
    rw [hU.1.1]
    exact Matrix.one_apply_eq _
  exact one_ne_zero (h11.symm.trans h10)

/-- **The all-swap point does not place** — for either pinned
twist, for any amended-class conjugator. This is the brick's
decision on the one point whose twisted orbit was not on the
record: PARTIAL for the five-point target, with the
obstruction proved here at full rank. -/
theorem allSwap_not_placed : ¬ FormBPlaced (orbitRep allSwapBits) := by
  rintro ⟨φ, hφ, U, hU, heq⟩
  rcases hφ with rfl | rfl
  · rw [Function.comp_id] at heq
    exact allSwap_id_obstruction U hU heq
  · exact allSwap_twist_obstruction U hU heq

/-! ## §6 Headline -/

/-- **R-CONJ FORM B, exhibited points — headline.** The
twist credential (§1), preservation under twist at the
exhibited clauses (§3), the four placements (§4), the
all-swap point's strengthened membership (landed), and its
non-placement (§5). -/
theorem formB_headline :
    (∀ a b : AF, colourTwist (afMul a b)
        = afMul (colourTwist a) (colourTwist b))
    ∧ (∀ a : AF, colourTwist (afStar a) = afStar (colourTwist a))
    ∧ Function.Bijective colourTwist
    ∧ DialOneStrengthenedFam (pi1 ∘ colourTwist)
    ∧ DialOneStrengthenedFam (conjRep conjU (pi1 ∘ colourTwist))
    ∧ DialOneStrengthenedFam (orbitRep allSwapBits)
    ∧ FormBPlaced pi1
    ∧ FormBPlaced piU
    ∧ FormBPlaced piAnti
    ∧ FormBPlaced (conjRep conjU piAnti)
    ∧ ¬ FormBPlaced (orbitRep allSwapBits) :=
  ⟨colourTwist_credential.2.2.1, colourTwist_credential.2.2.2.2.1,
   colourTwist_credential.2.2.2.2.2.2.2.2,
   twist_preservation_exhibited.1, twist_preservation_exhibited.2,
   ThetLogos.DialOneSwapOrbitBase.allSwap_mem_strengthened,
   placed_pi1, placed_piU, placed_piAnti, placed_conjRep_piAnti,
   allSwap_not_placed⟩

#print axioms formB_headline

end ThetLogos.DialOneRConjFormB
