/-
# AqftKmsGibbs — AQFT-1: finite KMS ⟺ Gibbs, with a statement correction

**Scope: the AQFT adjacency map
(~/workspace/your_files/aqft-adjacency-scope-2026-11-09.md
§8), fired by Zero. NO CLAIM. Dial-ineligible.**

THE CAMPAIGN: prove `FlowKernel.kms_iff_gibbs` — the
finite-dimensional KMS ⟺ Gibbs statement pinned at
T5 in `FlowKernel` — retiring it to proved status.

**STATEMENT FINDING (full rank, recorded before any
proof): the pin as literally stated is FALSE.** Its
right side (ρ = the Gibbs expression in H) carries
no Hermiticity hypothesis on H. At `Fin 2`, with
`β = 1` and `H = diag((π/2)i, −(π/2)i)`, the heat
trace `Tr exp(−βH) = (−i) + (i) = 0`, so the Gibbs
expression is `(0)⁻¹ • exp(−βH) = 0`; the equation
then holds for `ρ = 0`, while `IsKMSFlow 0 H 1`
fails (a density matrix has trace 1). The ⟸
direction therefore cannot be proved as stated —
`kms_iff_gibbs_fin2_false` below is the refutation
(Brick 4). What IS true, and what this module proves:
(i) the uniqueness direction ⟹, exactly as stated
(`IsKMSFlow` itself supplies Hermiticity and the
density axioms); (ii) the corrected ⟸ with
`H.IsHermitian` adjoined, hence the corrected iff
(`kms_iff_gibbs_corrected`); (iii) the
`phiActFlowKMSQuestion` corollary, whose generator
is Hermitian by `modularFlux_selfAdjoint`, so it
falls to the corrected direction. **K-AQFT1-STATEMENT
fired on the literal pin; the corrected statement is
the theorem.** (The classic Bratteli–Robinson
statement always understood the generator
self-adjoint — the pin's quantifier was wider than
its theorem.)

FENCES (the adjacency map's): finite full-matrix
seat only; this says nothing about algebraic KMS in
infinite systems, where equilibrium needs no density
matrix. K-AQFT-UPGRADE stays FIRED (this is finite
bookkeeping, not an ACMD upgrade);
K-AQFT-TYPEIII-FINITE armed (no Type III structure
exists or is claimed at finite seats).

STATUS: STATUS-AQFT1.md (per brick).
-/

import Mathlib
import ThetLogos.PartnerThermal
import ThetLogos.KMSBridge
import ThetLogos.ModularTime

namespace ThetLogos

variable {m : Type*} [Fintype m] [DecidableEq m]

/-! ## §1 — instruments: matrix units, trace faithfulness,
    the center of the full matrix algebra -/

/-- The matrix unit: `1` at `(i, j)`, `0` elsewhere
(defined in-module; this Mathlib pin has no
`stdBasisMatrix`). -/
def matUnitCoeff (i j : m) (c : ℂ) : Matrix m m ℂ :=
  fun a b => if a = i ∧ b = j then c else 0

/-- The trace against a matrix unit reads off the
transposed entry: `Tr (X · E_{ji}) = X i j`. -/
theorem trace_mul_matUnit (X : Matrix m m ℂ) (i j : m) :
    Matrix.trace (X * matUnitCoeff j i (1 : ℂ)) = X i j := by
  have h1 : ∀ k : m, (X * matUnitCoeff j i (1 : ℂ)) k k
      = if k = i then X i j else 0 := by
    intro k
    rw [Matrix.mul_apply]
    by_cases hk : k = i
    · subst hk
      rw [if_pos rfl, Finset.sum_eq_single j]
      · simp [matUnitCoeff]
      · intro l _ hlj
        simp only [matUnitCoeff]
        rw [if_neg (fun hh => hlj hh.1), mul_zero]
      · simp
    · rw [if_neg hk]
      apply Finset.sum_eq_zero
      intro l _
      simp only [matUnitCoeff]
      rw [if_neg (fun hh => hk hh.2), mul_zero]
  rw [Matrix.trace]
  simp only [Matrix.diag_apply, h1]
  simp

/-- **Faithfulness of the trace:** a matrix is
determined by its trace pairings — if
`Tr (P·A) = Tr (Q·A)` for every `A`, then `P = Q`. -/
theorem eq_of_forall_trace_mul_eq {P Q : Matrix m m ℂ}
    (h : ∀ A : Matrix m m ℂ,
      Matrix.trace (P * A) = Matrix.trace (Q * A)) :
    P = Q := by
  ext i j
  have hA := h (matUnitCoeff j i (1 : ℂ))
  rwa [trace_mul_matUnit, trace_mul_matUnit] at hA

/-- **The center of the full matrix algebra is the
scalars:** a matrix commuting with every matrix is a
scalar multiple of `1`. (Entry proof: commutation
with diagonal matrices kills the off-diagonal;
commutation with a matrix unit equates the diagonal
entries.) -/
theorem eq_smul_one_of_forall_commute [Nonempty m]
    {X : Matrix m m ℂ}
    (hX : ∀ B : Matrix m m ℂ, X * B = B * X) :
    ∃ c : ℂ, X = c • (1 : Matrix m m ℂ) := by
  obtain ⟨i₀⟩ := ‹Nonempty m›
  have hdiag : ∀ i j : m, i ≠ j → X i j = 0 := by
    intro i j hij
    have key := hX (Matrix.diagonal
      (fun k => if k = i then (1 : ℂ) else 0))
    have e1 : (X * Matrix.diagonal
          (fun k => if k = i then (1 : ℂ) else 0)) i j = 0 := by
      rw [Matrix.mul_diagonal]
      show X i j * (if j = i then (1 : ℂ) else 0) = 0
      rw [if_neg hij.symm, mul_zero]
    have e2 : (Matrix.diagonal
          (fun k => if k = i then (1 : ℂ) else 0) * X) i j
        = X i j := by
      rw [Matrix.diagonal_mul]
      show (if i = i then (1 : ℂ) else 0) * X i j = X i j
      rw [if_pos rfl, one_mul]
    have h := congrArg (fun M : Matrix m m ℂ => M i j) key
    rw [e1, e2] at h
    exact h.symm
  have hconst : ∀ i : m, X i i = X i₀ i₀ := by
    intro i
    have h := congrArg (fun M : Matrix m m ℂ => M i₀ i)
      (hX (matUnitCoeff i₀ i (1 : ℂ)))
    have hL : (X * matUnitCoeff i₀ i (1 : ℂ)) i₀ i = X i₀ i₀ := by
      rw [Matrix.mul_apply, Finset.sum_eq_single i₀]
      · simp [matUnitCoeff]
      · intro k _ hk0
        simp only [matUnitCoeff]
        rw [if_neg (fun hh => hk0 hh.1), mul_zero]
      · simp
    have hR : (matUnitCoeff i₀ i (1 : ℂ) * X) i₀ i = X i i := by
      rw [Matrix.mul_apply, Finset.sum_eq_single i]
      · simp [matUnitCoeff]
      · intro k _ hki
        simp only [matUnitCoeff]
        rw [if_neg (fun hh => hki hh.2), zero_mul]
      · simp
    rw [hL, hR] at h
    exact h.symm
  refine ⟨X i₀ i₀, ?_⟩
  ext i j
  by_cases h : i = j
  · subst h
    rw [hconst i]
    simp
  · rw [hdiag i j h]
    simp [Matrix.one_apply_ne h]

/-! ## §2 — exponential and flow instruments (general seat;
    `KMSBridge`'s are the `Fin N` special cases) -/

/-- Scalar multiples of one generator commute. -/
theorem commute_smul_gen (H : Matrix m m ℂ) (c d : ℂ) :
    Commute (c • H) (d • H) := by
  show (c • H) * (d • H) = (d • H) * (c • H)
  rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm,
    Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_comm]

/-- Gibbs exponentials at opposite scalars are mutual
inverses: `exp (cH) · exp (−cH) = 1`. -/
theorem exp_smul_mul_exp_neg_smul_gen (H : Matrix m m ℂ)
    (c : ℂ) :
    NormedSpace.exp (c • H) * NormedSpace.exp ((-c) • H) = 1 := by
  rw [neg_smul c H, Matrix.exp_neg,
    Matrix.nonsing_inv_eq_ringInverse,
    Ring.mul_inverse_cancel _ (Matrix.isUnit_exp _)]

/-- The exponential of a sum of scalar multiples splits:
`exp ((c+d)H) = exp (cH) · exp (dH)`. -/
theorem exp_add_smul_gen (H : Matrix m m ℂ) (c d : ℂ) :
    NormedSpace.exp ((c + d) • H)
      = NormedSpace.exp (c • H) * NormedSpace.exp (d • H) := by
  rw [add_smul]
  exact Matrix.exp_add_of_commute _ _ (commute_smul_gen H c d)

/-- The flow at the KMS point `z = β·i`: 
`α_{iβ}(B) = e^{−βH} B e^{+βH}` — the imaginary-time
form the KMS identity consumes. -/
theorem flowAction_iβ (H B : Matrix m m ℂ) (β : ℝ) :
    flowAction H ((β : ℂ) * Complex.I) B
      = NormedSpace.exp ((-(β : ℂ)) • H) * B
        * NormedSpace.exp ((β : ℂ) • H) := by
  have h1 : Complex.I * ((β : ℂ) * Complex.I) = (-(β : ℂ)) := by
    calc Complex.I * ((β : ℂ) * Complex.I)
        = (Complex.I * Complex.I) * (β : ℂ) := by ring
      _ = -(β : ℂ) := by rw [Complex.I_mul_I]; ring
  have h2 : -Complex.I * ((β : ℂ) * Complex.I) = (β : ℂ) := by
    calc -Complex.I * ((β : ℂ) * Complex.I)
        = -((Complex.I * Complex.I) * (β : ℂ)) := by ring
      _ = (β : ℂ) := by rw [Complex.I_mul_I]; ring
  unfold flowAction
  rw [h1, h2]

/-! ## §3 — the uniqueness direction: a KMS state is
    the Gibbs state of its generator -/

/-- The KMS identity at `t = 0`, read through trace
faithfulness: conjugating `ρ` by the Gibbs exponential
returns `A·ρ` — `e^{βH} ρ A e^{−βH} = A ρ` for every `A`. -/
theorem conj_eq_of_isKMSFlow {ρ H : Matrix m m ℂ} {β : ℝ}
    (hKMS : IsKMSFlow ρ H β) (A : Matrix m m ℂ) :
    NormedSpace.exp ((β : ℂ) • H) * ρ * A
      * NormedSpace.exp ((-(β : ℂ)) • H) = A * ρ := by
  apply eq_of_forall_trace_mul_eq
  intro B
  have h0 := hKMS.2.2 A B 0
  simp only [Complex.ofReal_zero, zero_add] at h0
  rw [flowAction_iβ, flowAction_zero] at h0
  calc Matrix.trace (NormedSpace.exp ((β : ℂ) • H) * ρ * A
        * NormedSpace.exp ((-(β : ℂ)) • H) * B)
      = Matrix.trace (NormedSpace.exp ((β : ℂ) • H)
          * (ρ * A * NormedSpace.exp ((-(β : ℂ)) • H) * B)) := by
        simp only [Matrix.mul_assoc]
    _ = Matrix.trace (ρ * A * NormedSpace.exp ((-(β : ℂ)) • H) * B
          * NormedSpace.exp ((β : ℂ) • H)) :=
        Matrix.trace_mul_comm _ _
    _ = Matrix.trace (ρ * A
          * (NormedSpace.exp ((-(β : ℂ)) • H) * B
            * NormedSpace.exp ((β : ℂ) • H))) := by
        simp only [Matrix.mul_assoc]
    _ = Matrix.trace (ρ * B * A) := h0
    _ = Matrix.trace (A * (ρ * B)) := Matrix.trace_mul_comm _ _
    _ = Matrix.trace (A * ρ * B) := by simp only [Matrix.mul_assoc]

/-- A KMS state commutes with the Gibbs exponential of
its generator: `e^{βH} ρ = ρ e^{βH}` (the conjugation
identity at `A = 1`, with `e^{−βH}` cancelled). -/
theorem exp_smul_comm_of_isKMSFlow {ρ H : Matrix m m ℂ} {β : ℝ}
    (hKMS : IsKMSFlow ρ H β) :
    NormedSpace.exp ((β : ℂ) • H) * ρ
      = ρ * NormedSpace.exp ((β : ℂ) • H) := by
  have key : NormedSpace.exp ((-(β : ℂ)) • H)
      * NormedSpace.exp ((β : ℂ) • H) = 1 := by
    have h := exp_smul_mul_exp_neg_smul_gen H (-(β : ℂ))
    rwa [neg_neg] at h
  have h := conj_eq_of_isKMSFlow hKMS (1 : Matrix m m ℂ)
  simp only [Matrix.mul_one, Matrix.one_mul] at h
  calc NormedSpace.exp ((β : ℂ) • H) * ρ
      = NormedSpace.exp ((β : ℂ) • H) * ρ
          * (NormedSpace.exp ((-(β : ℂ)) • H)
            * NormedSpace.exp ((β : ℂ) • H)) := by
        rw [key, Matrix.mul_one]
    _ = (NormedSpace.exp ((β : ℂ) • H) * ρ
          * NormedSpace.exp ((-(β : ℂ)) • H))
          * NormedSpace.exp ((β : ℂ) • H) := by
        simp only [Matrix.mul_assoc]
    _ = ρ * NormedSpace.exp ((β : ℂ) • H) := by rw [h]

/-- **Uniqueness (⟹, exactly as pinned):** a KMS state
for `H` at `β` is the Gibbs state in `H`. The forward
direction of `FlowKernel.kms_iff_gibbs` is true as
stated, because `IsKMSFlow` itself supplies the
Hermiticity and density hypotheses. -/
theorem eq_gibbsForm_of_isKMSFlow [Nonempty m]
    {ρ H : Matrix m m ℂ} {β : ℝ} (hKMS : IsKMSFlow ρ H β) :
    ρ = gibbsForm H β := by
  have key : NormedSpace.exp ((-(β : ℂ)) • H)
      * NormedSpace.exp ((β : ℂ) • H) = 1 := by
    have h := exp_smul_mul_exp_neg_smul_gen H (-(β : ℂ))
    rwa [neg_neg] at h
  have step : ∀ X : Matrix m m ℂ,
      X * NormedSpace.exp ((-(β : ℂ)) • H)
        * NormedSpace.exp ((β : ℂ) • H) = X := by
    intro X
    rw [Matrix.mul_assoc, key, Matrix.mul_one]
  have hB := exp_smul_comm_of_isKMSFlow hKMS
  have hT : ∀ A : Matrix m m ℂ,
      (ρ * NormedSpace.exp ((β : ℂ) • H)) * A
        = A * (ρ * NormedSpace.exp ((β : ℂ) • H)) := by
    intro A
    have hA := conj_eq_of_isKMSFlow hKMS A
    calc (ρ * NormedSpace.exp ((β : ℂ) • H)) * A
        = (NormedSpace.exp ((β : ℂ) • H) * ρ) * A := by rw [hB]
      _ = (NormedSpace.exp ((β : ℂ) • H) * ρ * A
            * NormedSpace.exp ((-(β : ℂ)) • H))
            * NormedSpace.exp ((β : ℂ) • H) :=
          (step (NormedSpace.exp ((β : ℂ) • H) * ρ * A)).symm
      _ = (A * ρ) * NormedSpace.exp ((β : ℂ) • H) := by rw [hA]
      _ = A * (ρ * NormedSpace.exp ((β : ℂ) • H)) := by
          simp only [Matrix.mul_assoc]
  obtain ⟨c, hc⟩ := eq_smul_one_of_forall_commute hT
  have hρ : ρ = c • NormedSpace.exp ((-(β : ℂ)) • H) := by
    calc ρ = ρ * (NormedSpace.exp ((β : ℂ) • H)
            * NormedSpace.exp ((-(β : ℂ)) • H)) := by
          rw [exp_smul_mul_exp_neg_smul_gen, Matrix.mul_one]
      _ = (ρ * NormedSpace.exp ((β : ℂ) • H))
            * NormedSpace.exp ((-(β : ℂ)) • H) := by
          simp only [Matrix.mul_assoc]
      _ = c • NormedSpace.exp ((-(β : ℂ)) • H) := by
          rw [hc, Algebra.smul_mul_assoc, Matrix.one_mul]
  have htr : Matrix.trace ρ = 1 := hKMS.1.2.2
  rw [hρ, Matrix.trace_smul, smul_eq_mul] at htr
  by_cases hE : Matrix.trace
      (NormedSpace.exp ((-(β : ℂ)) • H)) = 0
  · rw [hE, mul_zero] at htr
    exact (one_ne_zero htr.symm).elim
  · have hc_eq : c = (Matrix.trace
        (NormedSpace.exp ((-(β : ℂ)) • H)))⁻¹ :=
      eq_inv_of_mul_eq_one_left htr
    rw [hρ, hc_eq, gibbsForm]

/-! ## §4 — the corrected iff and the flux corollary -/

/-- **The corrected iff:** with `H.IsHermitian`
adjoined — the correction the STATEMENT FINDING
priced — KMS ⟺ Gibbs holds exactly. The ⟹ half is
§3's uniqueness; the ⟸ half is
`PartnerThermal.gibbsForm_isKMSFlow`, cited, not
re-proved. This is the true form of the
`FlowKernel.kms_iff_gibbs` pin: the bare pin, which
quantifies over non-Hermitian `H` as well, is false
(its refutation is Brick 4, separate and still
open). -/
theorem kms_iff_gibbs_corrected [Nonempty m]
    {ρ H : Matrix m m ℂ} {β : ℝ} (hH : H.IsHermitian) :
    IsKMSFlow ρ H β ↔ ρ = gibbsForm H β := by
  constructor
  · exact eq_gibbsForm_of_isKMSFlow
  · intro h
    rw [h]
    exact gibbsForm_isKMSFlow hH β

/-- **The flux corollary:** the pinned
`phiActFlowKMSQuestion` holds — for Hermitian
`G, D` (at the `Fin 32` seat), the Gibbs state of
the modular flux `φ_act = i[G, D]` is a KMS state
for the flux's own flow. The generator is
Hermitian by `modularFlux_selfAdjoint`, so the
question falls to the corrected ⟸ direction.
(The question's further content — a continuum /
twisted-triple limit in which the flow becomes
spacetime — is not touched by this finite
corollary.) -/
theorem phiActFlowKMSQuestion_gibbsForm :
    phiActFlowKMSQuestion := by
  intro G D β hG hD
  exact gibbsForm_isKMSFlow (modularFlux_selfAdjoint hG hD) β


/-! ## §5 — Brick 4: the literal pin is false at `Fin 2` -/

/-- **Brick 4 — the refutation (K-AQFT1-STATEMENT,
proved):** the literal pin `FlowKernel.kms_iff_gibbs`
at the `Fin 2` seat is FALSE. The counterexample is
exactly the one the header cards: `β = 1`,
`H = diag((π/2)·i, −(π/2)·i)`. Its heat trace
vanishes — `Tr exp(−H) = (−i) + (i) = 0` — so the
pin's Gibbs expression is `(0)⁻¹ • exp(−H) = 0`, and
the pin's right side therefore holds for `ρ = 0`;
but `IsKMSFlow 0 H 1` would make `0` a density
matrix, forcing `Tr 0 = 1`. The bare pin's `⟸`
direction fails at `Fin 2`. What survives is §4's
corrected iff, where `H.IsHermitian` is adjoined. -/
theorem kms_iff_gibbs_fin2_false :
    ¬ @kms_iff_gibbs (Fin 2) _ _ := by
  intro h
  have h' : ∀ (ρ H : Matrix (Fin 2) (Fin 2) ℂ) (β : ℝ),
      IsKMSFlow ρ H β ↔
        ρ = (Matrix.trace (NormedSpace.exp ((-(β : ℂ)) • H)))⁻¹
          • NormedSpace.exp ((-(β : ℂ)) • H) := h
  -- the counterexample generator: `H = diag (c, −c)` with `c = (π/2)·i`
  set c : ℂ := ((Real.pi / 2 : ℝ) : ℂ) * Complex.I with hc
  set H : Matrix (Fin 2) (Fin 2) ℂ := Matrix.diagonal ![c, -c] with hH
  -- the bridge between `NormedSpace.exp` on `ℂ` and `Complex.exp`
  have hb : ∀ z : ℂ, NormedSpace.exp z = Complex.exp z :=
    fun z => congrFun Complex.exp_eq_exp_ℂ.symm z
  -- the two scalar exponentials at the seat
  have e0 : NormedSpace.exp (-c) = -Complex.I := by
    have harg : -c = ((-(Real.pi / 2) : ℝ) : ℂ) * Complex.I := by
      rw [hc]; push_cast; ring
    rw [harg, hb, Complex.exp_ofReal_mul_I]
    simp [Real.cos_pi_div_two, Real.sin_pi_div_two]
  have e1 : NormedSpace.exp c = Complex.I := by
    have harg : c = ((Real.pi / 2 : ℝ) : ℂ) * Complex.I := by
      rw [hc]
    rw [harg, hb, Complex.exp_ofReal_mul_I]
    simp [Real.cos_pi_div_two, Real.sin_pi_div_two]
  -- at `β = 1` the Gibbs exponent is the flipped diagonal
  have hsmul : (-((1 : ℝ) : ℂ)) • H = Matrix.diagonal ![-c, c] := by
    rw [hH, ← Matrix.diagonal_smul]
    congr 1
    funext i
    fin_cases i <;>
      simp [Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero,
        Matrix.cons_val_one]
  -- the entrywise exponential of the flipped diagonal
  have hfun : NormedSpace.exp ![-c, c]
      = ![(-Complex.I), Complex.I] := by
    funext i
    rw [Pi.coe_exp]
    fin_cases i
    · simpa using e0
    · simpa using e1
  -- its exponential is `diag (−i, i)`
  have hexp : NormedSpace.exp ((-((1 : ℝ) : ℂ)) • H)
      = Matrix.diagonal ![(-Complex.I), Complex.I] := by
    rw [hsmul, Matrix.exp_diagonal, hfun]
  -- so the heat trace vanishes
  have htrace : Matrix.trace
      (NormedSpace.exp ((-((1 : ℝ) : ℂ)) • H)) = 0 := by
    rw [hexp, Matrix.trace_diagonal, Fin.sum_univ_two]
    simp [Matrix.cons_val_zero, Matrix.cons_val_one]
  -- the pin's right side then holds for `ρ = 0` …
  have hKMS : IsKMSFlow (0 : Matrix (Fin 2) (Fin 2) ℂ) H 1 := by
    apply (h' 0 H 1).mpr
    rw [htrace, inv_zero, zero_smul]
  -- … but `0` is no density matrix: `Tr 0 = 1` is false
  have htr : Matrix.trace (0 : Matrix (Fin 2) (Fin 2) ℂ) = 1 :=
    hKMS.1.2.2
  rw [Matrix.trace_zero] at htr
  exact zero_ne_one htr

end ThetLogos
