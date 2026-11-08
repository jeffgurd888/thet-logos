import Mathlib.Tactic
import ThetLogos.DialOneGradeRConjPin
import ThetLogos.DialOneExtraction

open Matrix Complex
open ThetLogos.Track1RouteB
open ThetLogos.PreOptionARepresentation
open ThetLogos.HyperchargeForcing
open ThetLogos.DialOneSeatTiePin
open ThetLogos.DialOneGammaTracePin
open ThetLogos.DialOneGammaFamilyPin
open ThetLogos.DialOneGradeRConjPin

namespace ThetLogos.DialOneGradeRConj

/-!
# ThetLogos.DialOneGradeRConj — GRADE R, R-CONJ road: transport, clause by clause

Governing texts: the pin `DialOneGradeRConjPin` and the
re-scope note `grade-r-conj-rescope-2026-11-07.md` §4.
This module attacks the pin's `PreservationQ` honestly,
clause by clause, for a GENERAL member `U` of the
centralizing class — not for `conjU` alone:

* `C3` is preserved in full (`c3_preserved`): only
  condition (a) and `Uᵀ * U = 1` are used.
* `DialOneBase` is preserved under (a)/(b)/(c) PLUS the
  explicitly carried reality hypothesis `IsRealMat U`
  (`dialOneBase_preserved`): nine of its ten clause
  groups transport by the sandwich algebra, the
  `piOp` transport identity (`piOp_conjRep`, the
  general-`U` form of the landed `piOp_conj`), and the
  Dirac commutator transport
  (`df_commutator_conjRep`). The star clause is the
  exception — it transports iff `Uᴴ = Uᵀ`, which is
  gap **(α)**: reality is carried here as a hypothesis
  on the face, never smuggled into the class.
* The projection clauses `C3lep` / `C3col` / `FeR` are
  NOT transported: each is proved EQUIVALENT to its
  pulled form at the original point
  (`c3lep_conjRep_iff`, `c3col_conjRep_iff`,
  `feR_conjRep_iff`, via `trace_gammaF_pulled`) — the
  clause at the conjugate holds iff the trace against
  the pulled projection `Uᵀ * P * U` vanishes at `π`.
  That is gap **(β)**, stated as an iff, not papered
  over: the pulled projections differ from the
  projections already for `conjU`.
* The capstone (`strengthened_preserved_of_reality_pulled`)
  assembles exactly what is proved: preservation holds
  for any class member that is real AND whose three
  pulled clauses hold at the point. `PreservationQ`
  itself — all class members, no extra hypotheses —
  remains OPEN, obstructed at precisely (α) and (β).

**No counterexample is exhibited in this module, and
none is claimed**: the road's kill condition (pin
header) has not fired. NO CLAIM. Dial 1 = 0.
-/

/-! ## Transport identities for a general class member -/

/-- The transpose companion of condition (a):
`gammaF * Uᵀ = Uᵀ * gammaF`, by transposing (a)
against the landed `gammaF_transpose_eq`. -/
theorem gammaF_transpose_comm_of_class {U : Matrix (Fin 32) (Fin 32) ℂ}
    (hU : CentralizingClass U) :
    gammaF * Uᵀ = Uᵀ * gammaF := by
  have h := congrArg Matrix.transpose hU.2.2.1
  rw [Matrix.transpose_mul, Matrix.transpose_mul,
    ThetLogos.DialOneConjugationCounterexample.gammaF_transpose_eq] at h
  exact h.symm

/-- The grading is fixed by the sandwich: from (a) and
`Uᵀ * U = 1`, `Uᵀ * gammaF * U = gammaF`. -/
theorem transpose_gammaF_sandwich {U : Matrix (Fin 32) (Fin 32) ℂ}
    (hU : CentralizingClass U) :
    Uᵀ * gammaF * U = gammaF := by
  calc Uᵀ * gammaF * U = Uᵀ * (gammaF * U) := by simp only [Matrix.mul_assoc]
    _ = Uᵀ * (U * gammaF) := by rw [hU.2.2.1]
    _ = (Uᵀ * U) * gammaF := by simp only [Matrix.mul_assoc]
    _ = gammaF := by rw [hU.2.1, Matrix.one_mul]

/-- The γ-trace is invariant under the sandwich, for
every class member and every matrix `X`. -/
theorem trace_gammaF_conjRep {U : Matrix (Fin 32) (Fin 32) ℂ}
    (hU : CentralizingClass U) (X : Matrix (Fin 32) (Fin 32) ℂ) :
    Matrix.trace (gammaF * (U * X * Uᵀ)) = Matrix.trace (gammaF * X) := by
  calc Matrix.trace (gammaF * (U * X * Uᵀ))
      = Matrix.trace ((gammaF * U * X) * Uᵀ) := by simp only [Matrix.mul_assoc]
    _ = Matrix.trace (Uᵀ * (gammaF * U * X)) := Matrix.trace_mul_comm _ _
    _ = Matrix.trace ((Uᵀ * gammaF * U) * X) := by simp only [Matrix.mul_assoc]
    _ = Matrix.trace (gammaF * X) := by rw [transpose_gammaF_sandwich hU]

/-- **C3 is preserved under the whole class**, in
full: for every class member `U` and every `π`
satisfying `C3`, the conjugate satisfies `C3`. Only
(a) and unitarity enter. -/
theorem c3_preserved {U : Matrix (Fin 32) (Fin 32) ℂ}
    (hU : CentralizingClass U)
    (π : AF → Matrix (Fin 32) (Fin 32) ℂ) (h : C3 π) :
    C3 (conjRep U π) := by
  intro α β
  show Matrix.trace (gammaF * (U * π (u1Gen α β) * Uᵀ)) = 0
  rw [trace_gammaF_conjRep hU]
  exact h α β

/-- The `piOp` transport identity for a general class
member — the general-`U` form of the landed
`piOp_conj`, from `piOp_mul_rev`, condition (b), and
`piOp` involutivity. -/
theorem piOp_conjRep {U : Matrix (Fin 32) (Fin 32) ℂ}
    (hU : CentralizingClass U) (M : Matrix (Fin 32) (Fin 32) ℂ) :
    piOp (U * M * Uᵀ) = U * piOp M * Uᵀ := by
  have hUT : piOp Uᵀ = U := by
    have h := ThetLogos.DialOneConjugationCounterexample.piOp_piOp U
    rw [hU.2.2.2.1] at h
    exact h
  rw [ThetLogos.DialOneExtraction.piOp_mul_rev,
    ThetLogos.DialOneExtraction.piOp_mul_rev, hUT, hU.2.2.2.1]
  simp only [Matrix.mul_assoc]

/-- The transpose companion of condition (c):
`DF_oneGen` commutes with `Uᵀ` at every Yukawa tuple,
by transposing (c) against the landed
`df_transpose_eq`. -/
theorem df_comm_transpose_of_class {U : Matrix (Fin 32) (Fin 32) ℂ}
    (hU : CentralizingClass U) (Ynu Ye Yu Yd : ℝ) :
    DF_oneGen Ynu Ye Yu Yd * Uᵀ = Uᵀ * DF_oneGen Ynu Ye Yu Yd := by
  have h := congrArg Matrix.transpose (hU.2.2.2.2 Ynu Ye Yu Yd)
  rw [Matrix.transpose_mul, Matrix.transpose_mul,
    ThetLogos.DialOneConjugationCounterexample.df_transpose_eq] at h
  exact h.symm

/-- The Dirac commutator transports through the
sandwich: `[DF, U X Uᵀ] = U [DF, X] Uᵀ` for every
class member, at every Yukawa tuple. -/
theorem df_commutator_conjRep {U : Matrix (Fin 32) (Fin 32) ℂ}
    (hU : CentralizingClass U) (Ynu Ye Yu Yd : ℝ)
    (X : Matrix (Fin 32) (Fin 32) ℂ) :
    DF_oneGen Ynu Ye Yu Yd * (U * X * Uᵀ)
        - (U * X * Uᵀ) * DF_oneGen Ynu Ye Yu Yd
      = U * (DF_oneGen Ynu Ye Yu Yd * X
        - X * DF_oneGen Ynu Ye Yu Yd) * Uᵀ := by
  have hDFU : DF_oneGen Ynu Ye Yu Yd * U
      = U * DF_oneGen Ynu Ye Yu Yd := hU.2.2.2.2 Ynu Ye Yu Yd
  have hDFUT : DF_oneGen Ynu Ye Yu Yd * Uᵀ
      = Uᵀ * DF_oneGen Ynu Ye Yu Yd :=
    df_comm_transpose_of_class hU Ynu Ye Yu Yd
  calc DF_oneGen Ynu Ye Yu Yd * (U * X * Uᵀ)
        - (U * X * Uᵀ) * DF_oneGen Ynu Ye Yu Yd
      = U * (DF_oneGen Ynu Ye Yu Yd * X) * Uᵀ
        - U * (X * DF_oneGen Ynu Ye Yu Yd) * Uᵀ := by
        congr 1
        · calc DF_oneGen Ynu Ye Yu Yd * (U * X * Uᵀ)
              = (DF_oneGen Ynu Ye Yu Yd * U) * X * Uᵀ := by
                simp only [Matrix.mul_assoc]
            _ = U * (DF_oneGen Ynu Ye Yu Yd * X) * Uᵀ := by
                rw [hDFU]; simp only [Matrix.mul_assoc]
        · calc (U * X * Uᵀ) * DF_oneGen Ynu Ye Yu Yd
              = U * X * (Uᵀ * DF_oneGen Ynu Ye Yu Yd) := by
                simp only [Matrix.mul_assoc]
            _ = U * X * (DF_oneGen Ynu Ye Yu Yd * Uᵀ) := by
                rw [← hDFUT]
            _ = U * (X * DF_oneGen Ynu Ye Yu Yd) * Uᵀ := by
                simp only [Matrix.mul_assoc]
    _ = U * (DF_oneGen Ynu Ye Yu Yd * X
        - X * DF_oneGen Ynu Ye Yu Yd) * Uᵀ := by
        rw [Matrix.mul_sub, Matrix.sub_mul]


/-! ## The base: sandwich algebra and preservation modulo gap (α) -/

/-- The sandwich is multiplicative for every class
member — the general-`U` form of the landed
`conj_mul`. -/
theorem conjRep_mul {U : Matrix (Fin 32) (Fin 32) ℂ}
    (hU : CentralizingClass U) (X Y : Matrix (Fin 32) (Fin 32) ℂ) :
    (U * X * Uᵀ) * (U * Y * Uᵀ) = U * (X * Y) * Uᵀ := by
  have h : (U * X * Uᵀ) * (U * Y * Uᵀ)
      = U * X * (Uᵀ * U) * Y * Uᵀ := by
    simp only [Matrix.mul_assoc]
  rw [h, hU.2.1]
  simp [Matrix.mul_assoc]

/-- Reality in the transposed form: if `Uᴴ = Uᵀ` then
also `(Uᵀ)ᴴ = U` (entrywise: reality says every entry
equals its own conjugate). -/
theorem conjTranspose_transpose_of_real {U : Matrix (Fin 32) (Fin 32) ℂ}
    (hreal : IsRealMat U) : (Uᵀ)ᴴ = U := by
  have hreal' : Uᴴ = Uᵀ := hreal
  ext i j
  have h3 := congrArg (fun M : Matrix (Fin 32) (Fin 32) ℂ => M j i) hreal'
  simp only [Matrix.conjTranspose_apply, Matrix.transpose_apply] at h3 ⊢
  exact h3

/-- **The base is preserved under (a)/(b)/(c) plus
reality** — `DialOneBase` transports through the
sandwich for every real class member. Nine clause
groups are the sandwich algebra, `piOp_conjRep`, and
`df_commutator_conjRep`; the star clause is exactly
where the reality hypothesis `hreal` (gap (α)) is
spent, and it is spent nowhere else. -/
theorem dialOneBase_preserved {U : Matrix (Fin 32) (Fin 32) ℂ}
    (hU : CentralizingClass U) (hreal : IsRealMat U)
    (π : AF → Matrix (Fin 32) (Fin 32) ℂ) (h : DialOneBase π) :
    DialOneBase (conjRep U π) := by
  obtain ⟨hmul, hadd, hstar, hone, hzero, hinj, hgamma, hord, hfirst, hdet⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- multiplicativity: the sandwich algebra
    intro a b
    show U * π (afMul a b) * Uᵀ = (U * π a * Uᵀ) * (U * π b * Uᵀ)
    rw [hmul]
    exact (conjRep_mul hU (π a) (π b)).symm
  · -- additivity: distributivity
    intro a b
    show U * π (afAdd a b) * Uᵀ = (U * π a * Uᵀ) + (U * π b * Uᵀ)
    rw [hadd, Matrix.mul_add, Matrix.add_mul]
  · -- the star clause: exactly gap (α), spent here
    intro a
    have hreal' : Uᴴ = Uᵀ := hreal
    show U * π (afStar a) * Uᵀ = (U * π a * Uᵀ)ᴴ
    rw [hstar a, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      hreal', conjTranspose_transpose_of_real hreal]
    simp only [Matrix.mul_assoc]
  · -- unitality
    show U * π afOne * Uᵀ = 1
    rw [hone, Matrix.mul_one, hU.1]
  · -- zero
    show U * π afZero * Uᵀ = 0
    rw [hzero]
    simp
  · -- injectivity: the sandwich is invertible
    intro a b hab
    apply hinj
    have h3 : U * π a * Uᵀ = U * π b * Uᵀ := hab
    have key : ∀ X : Matrix (Fin 32) (Fin 32) ℂ,
        Uᵀ * (U * X * Uᵀ) * U = X := by
      intro X
      calc Uᵀ * (U * X * Uᵀ) * U = (Uᵀ * U) * X * (Uᵀ * U) := by
            simp only [Matrix.mul_assoc]
        _ = X := by rw [hU.2.1]; simp
    have h4 := congrArg (fun M : Matrix (Fin 32) (Fin 32) ℂ => Uᵀ * M * U) h3
    rwa [key (π a), key (π b)] at h4
  · -- γ-commutation: (a) and its transpose companion
    intro a
    show gammaF * (U * π a * Uᵀ) = (U * π a * Uᵀ) * gammaF
    have e1 : gammaF * (U * π a * Uᵀ) = U * (gammaF * π a) * Uᵀ := by
      calc gammaF * (U * π a * Uᵀ) = (gammaF * U) * π a * Uᵀ := by
            simp only [Matrix.mul_assoc]
        _ = (U * gammaF) * π a * Uᵀ := by rw [hU.2.2.1]
        _ = U * (gammaF * π a) * Uᵀ := by simp only [Matrix.mul_assoc]
    have e2 : (U * π a * Uᵀ) * gammaF = U * (π a * gammaF) * Uᵀ := by
      calc (U * π a * Uᵀ) * gammaF = U * π a * (Uᵀ * gammaF) := by
            simp only [Matrix.mul_assoc]
        _ = U * π a * (gammaF * Uᵀ) := by
            rw [← gammaF_transpose_comm_of_class hU]
        _ = U * (π a * gammaF) * Uᵀ := by simp only [Matrix.mul_assoc]
    rw [e1, e2, hgamma a]
  · -- order-zero: the piOp transport identity
    intro a b
    show (U * π a * Uᵀ) * piOp (U * π b * Uᵀ)
      = piOp (U * π b * Uᵀ) * (U * π a * Uᵀ)
    rw [piOp_conjRep hU, conjRep_mul hU, conjRep_mul hU, hord a b]
  · -- first-order: the Dirac commutator transport
    intro Ynu Ye Yu Yd a b i j
    show ((DF_oneGen Ynu Ye Yu Yd * (U * π a * Uᵀ)
        - (U * π a * Uᵀ) * DF_oneGen Ynu Ye Yu Yd)
        * piOp (U * π b * Uᵀ)
      - piOp (U * π b * Uᵀ)
        * (DF_oneGen Ynu Ye Yu Yd * (U * π a * Uᵀ)
          - (U * π a * Uᵀ) * DF_oneGen Ynu Ye Yu Yd)) i j = 0
    rw [piOp_conjRep hU, df_commutator_conjRep hU,
      conjRep_mul hU, conjRep_mul hU,
      ← Matrix.sub_mul, ← Matrix.mul_sub]
    have hE : (DF_oneGen Ynu Ye Yu Yd * π a
          - π a * DF_oneGen Ynu Ye Yu Yd) * piOp (π b)
        - piOp (π b) * (DF_oneGen Ynu Ye Yu Yd * π a
          - π a * DF_oneGen Ynu Ye Yu Yd) = 0 := by
      ext i j
      exact hfirst Ynu Ye Yu Yd a b i j
    rw [hE]
    simp
  · -- the determinant clause: det is sandwich-invariant
    obtain ⟨α, β, hgcd, hdet1⟩ := hdet
    refine ⟨α, β, hgcd, fun t => ?_⟩
    show (U * π (u1ParamGen α β t) * Uᵀ).det = 1
    have hdetU : U.det * Uᵀ.det = 1 := by
      have hh := congrArg Matrix.det hU.1
      rwa [Matrix.det_mul, Matrix.det_one] at hh
    rw [Matrix.det_mul, Matrix.det_mul, hdet1 t]
    calc U.det * 1 * Uᵀ.det = U.det * Uᵀ.det := by rw [mul_one]
      _ = 1 := hdetU


/-! ## The projection clauses: the pulled reduction (gap (β)) -/

/-- The γ-trace against a projection `P`, at the
conjugate, equals the γ-trace against the PULLED
projection `Uᵀ * P * U` at the original matrix. Cyclicity
plus condition (a) only — this identity is the whole
content of gap (β): the pulled projection is not the
projection. -/
theorem trace_gammaF_pulled {U : Matrix (Fin 32) (Fin 32) ℂ}
    (hU : CentralizingClass U) (P X : Matrix (Fin 32) (Fin 32) ℂ) :
    Matrix.trace (gammaF * P * (U * X * Uᵀ))
      = Matrix.trace (gammaF * (Uᵀ * P * U) * X) := by
  calc Matrix.trace (gammaF * P * (U * X * Uᵀ))
      = Matrix.trace (Uᵀ * (gammaF * P * (U * X))) := by
        rw [show gammaF * P * (U * X * Uᵀ)
            = (gammaF * P * (U * X)) * Uᵀ from by
          simp only [Matrix.mul_assoc], Matrix.trace_mul_comm]
    _ = Matrix.trace ((Uᵀ * gammaF) * (P * (U * X))) := by
        simp only [Matrix.mul_assoc]
    _ = Matrix.trace ((gammaF * Uᵀ) * (P * (U * X))) := by
        rw [← gammaF_transpose_comm_of_class hU]
    _ = Matrix.trace (gammaF * (Uᵀ * P * U) * X) := by
        simp only [Matrix.mul_assoc]

/-- The pulled reduction, at the level of clauses: a
projection clause at the conjugate holds iff the pulled
clause holds at the original point, for every
projection `P` and every class member `U`. -/
theorem pulled_clause_transport {U : Matrix (Fin 32) (Fin 32) ℂ}
    (hU : CentralizingClass U) (P : Matrix (Fin 32) (Fin 32) ℂ)
    (π : AF → Matrix (Fin 32) (Fin 32) ℂ) :
    (∀ α β : ℤ, Matrix.trace (gammaF * P * (conjRep U π) (u1Gen α β)) = 0)
      ↔ ∀ α β : ℤ,
        Matrix.trace (gammaF * (Uᵀ * P * U) * π (u1Gen α β)) = 0 := by
  constructor
  · intro h α β
    have hαβ := h α β
    rw [show (conjRep U π) (u1Gen α β) = U * π (u1Gen α β) * Uᵀ from rfl]
      at hαβ
    rwa [trace_gammaF_pulled hU P (π (u1Gen α β))] at hαβ
  · intro h α β
    have hαβ := h α β
    rw [show (conjRep U π) (u1Gen α β) = U * π (u1Gen α β) * Uᵀ from rfl]
    rwa [trace_gammaF_pulled hU P (π (u1Gen α β))]

/-- **C3lep at the conjugate ⟺ the pulled lepton
clause at the point.** Not a transport: the right side
is a new trace condition, gap (β). -/
theorem c3lep_conjRep_iff {U : Matrix (Fin 32) (Fin 32) ℂ}
    (hU : CentralizingClass U) (π : AF → Matrix (Fin 32) (Fin 32) ℂ) :
    C3lep (conjRep U π)
      ↔ ∀ α β : ℤ,
        Matrix.trace (gammaF * (Uᵀ * lepProj * U) * π (u1Gen α β)) = 0 :=
  (ThetLogos.DialOneGammaFamilyPin.c3lep_unfold _).trans
    (pulled_clause_transport hU lepProj π)

/-- **C3col `c` at the conjugate ⟺ the pulled colour
clause at the point.** Not a transport: gap (β). -/
theorem c3col_conjRep_iff {U : Matrix (Fin 32) (Fin 32) ℂ}
    (hU : CentralizingClass U) (c : Fin 3)
    (π : AF → Matrix (Fin 32) (Fin 32) ℂ) :
    C3col c (conjRep U π)
      ↔ ∀ α β : ℤ,
        Matrix.trace (gammaF * (Uᵀ * colProj c * U) * π (u1Gen α β)) = 0 :=
  (ThetLogos.DialOneGammaFamilyPin.c3col_unfold c _).trans
    (pulled_clause_transport hU (colProj c) π)

/-- **FeR at the conjugate ⟺ the pulled e_R clause at
the point.** Not a transport: gap (β). -/
theorem feR_conjRep_iff {U : Matrix (Fin 32) (Fin 32) ℂ}
    (hU : CentralizingClass U) (π : AF → Matrix (Fin 32) (Fin 32) ℂ) :
    FeR (conjRep U π)
      ↔ ∀ α β : ℤ,
        Matrix.trace (gammaF * (Uᵀ * eRProj * U) * π (u1Gen α β)) = 0 :=
  (ThetLogos.DialOneGammaFamilyPin.feR_unfold _).trans
    (pulled_clause_transport hU eRProj π)

/-! ## The capstone: preservation modulo exactly the two gaps -/

/-- **Preservation, modulo exactly gaps (α) and (β).**
For a REAL class member whose three pulled clauses
hold at `π`, the conjugate of a strengthened `π` is
strengthened — assembled from `dialOneBase_preserved`
(base, reality spent), `c3_preserved` (C3, in full),
and the three pulled iffs. The hypotheses of this
theorem ARE the obstruction to the pin's
`PreservationQ`: nothing here discharges them for a
general class member, and `PreservationQ` itself
remains open. -/
theorem strengthened_preserved_of_reality_pulled
    {U : Matrix (Fin 32) (Fin 32) ℂ}
    (hU : CentralizingClass U) (hreal : IsRealMat U)
    (π : AF → Matrix (Fin 32) (Fin 32) ℂ)
    (h : DialOneStrengthenedFam π)
    (hlep : ∀ α β : ℤ,
      Matrix.trace (gammaF * (Uᵀ * lepProj * U) * π (u1Gen α β)) = 0)
    (hcol : ∀ (c : Fin 3) (α β : ℤ),
      Matrix.trace (gammaF * (Uᵀ * colProj c * U) * π (u1Gen α β)) = 0)
    (heR : ∀ α β : ℤ,
      Matrix.trace (gammaF * (Uᵀ * eRProj * U) * π (u1Gen α β)) = 0) :
    DialOneStrengthenedFam (conjRep U π) := by
  obtain ⟨hbase, hC3, hfam⟩ := h
  obtain ⟨-, -, -⟩ := hfam
  refine ⟨dialOneBase_preserved hU hreal π hbase, c3_preserved hU π hC3,
    (c3lep_conjRep_iff hU π).mpr hlep,
    fun c => (c3col_conjRep_iff hU c π).mpr (hcol c),
    (feR_conjRep_iff hU π).mpr heR⟩

end ThetLogos.DialOneGradeRConj
