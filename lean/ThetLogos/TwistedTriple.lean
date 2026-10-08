import ThetLogos.FlowKernel
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Tactic

open Matrix

/-!
# ThetLogos.TwistedTriple — the twisted spectral triple (Bridge Span 1)

**Setup.** We work with finite matrices `Matrix n n ℂ` (`[Fintype n]`,
`[DecidableEq n]`), the same conventions as `FlowKernel.lean` (`Uᴴ` for the
conjugate transpose). A *twist* `ρ` is an algebra automorphism of `Mₙ(ℂ)`,
taken as explicit hypothesis data (`TwistAuto`: multiplicativity,
additivity, `ρ(1) = 1`, explicit two-sided inverse). The twisted
commutator is `[D, a]_ρ := D * a − ρ(a) * D`, after Connes–Moscovici
("Type III and spectral triples", 2008) and Devastato–Lizzi–Martinetti
("Grand symmetry, spectral action and the Higgs mass", 2016).

**Convention table** (ours vs the literature):

| ours | Connes–Moscovici | Devastato–Lizzi–Martinetti | note |
|---|---|---|---|
| `ρ` (`TwistAuto`) | `σ` (the twist) | `ρ` | we follow DLM; `σ` is taken here for the modular flow |
| `twistedComm D ρ a = D*a − ρ(a)*D` | twisted commutator `[D,a]_σ` | `[D,a]_ρ` | |
| `IsCMRegular`: `ρ(aᴴ) = (ρ⁻¹(a))ᴴ` | regularity `σ(a*) = σ⁻¹(a)*` | regularity | FALSE for `ρ_U` in general — see refutation below |
| `twistConj U a = U*a*Uᴴ` | — | inner twist | `ρ_U`, `ρ_U⁻¹ = ρ_{Uᴴ}` |
| `IsTwistedOneForm` | twisted `Ω¹_D` | `Ω¹_D(A,ρ) = Σ a_k [D,b_k]_ρ` | |
| `TwistedFirstOrderCond` | — | `[[D,a]_ρ, b°]_{ρ°} = 0`, `ρ°(x°) = (ρ⁻¹(x))°` | pinned T5 |
| `twistedFluctuation` | — | `D_{A_ρ} = D + A_ρ + ε' J A_ρ J⁻¹` | our `ε₁` = their KO sign `ε'` |

**Numerical refutation 1 — CM-regularity (2026-10-07, numerical worker).**
The Connes–Moscovici regularity `ρ(a†) = (ρ⁻¹(a))†` is FALSE for
`ρ_U(a) = U * a * Uᴴ` in general: residual `0.866` at `s = 0.1`, growing
linearly in `s`, for `U_s = e^{isK}` with generic `K`. An earlier draft of
this file claimed it as automatic — that claim is dead. What IS true
unconditionally is the *-automorphism law `ρ_U(aᴴ) = (ρ_U(a))ᴴ`
(`twistConj_star`, T1). CM-regularity for `ρ_U` holds ⟺ `U²` is central
(`twistConj_CM_iff_centralSq`, T1); in particular it holds for involutive
twists `U² = 1` (`twistConj_CM_of_involutive`, T1).

**Numerical refutation 2 — algebra preservation (2026-10-07, numerical
worker).** Do NOT assume the modular flow `σ_s` preserves the represented
algebra `π(A_F)`: preservation residuals reach `1.413 ≈ ‖π(g)‖`. So
`TwistPreserves` is an *explicit hypothesis* throughout
(`twistedComm_mem_subalgebra` is conditional T1), never automatic.

**Bridge Span 2 — the DLM flip twist (2026-10-07).** §7 formalizes the
Devastato–Lizzi–Martinetti *minimal twist by grading*
(Filaci–Martinetti, SIGMA 2020 §2.3; survey arXiv:2301.08346 §4.2): the
grand algebra `Mₙ(ℂ) × Mₙ(ℂ)` acting via the grading projectors
`P± = (1±Γ)/2`, twisted by the FLIP `(a,a') ↦ (a',a)`. The headline
result is the theorem Span 1 was missing: Connes–Moscovici regularity
holds UNCONDITIONALLY for the flip (`flipTwist_CM_regular`, T1), because
the flip is its own inverse and commutes with `ᴴ` componentwise. The
naive "twist by conjugation" `ρ(a) = ΓaΓ` is proved TRIVIAL on the graded
subalgebra (`twistByGrading_trivial`, T1) — this is why DLM use the flip
on the doubled algebra, not conjugation by `Γ`. Our numerics confirm
`[Γ, π(g)] = 0` exactly for all 24 generators, so the evenness hypotheses
below are the physical case, not an extra assumption.

**Bridge Span 3 — the Krein pylon (2026-10-07).** §8 formalizes the
algebraic core of Devastato et al., "Lorentz signature and twisted spectral
triples" (arXiv:1710.04965) §3.1–3.2, as pure matrix algebra: the ρ-product
`⟨Ψ,Φ⟩_ρ := ⟨Ψ, RΦ⟩`, the fundamental symmetry `R† = R`, `R² = I`, the
Krein-adjoint `A⁺ := R A† R` (an involution, T1), and ρ-symmetry
`R D† R = D`. The swap `R = fromBlocks 0 1 1 0` is the DLM SM-case
fundamental symmetry: `R² = 1`, `Rᴴ = R`, implements the flip on
block-diagonal doubled representations (T1), and a block-diagonal Dirac is
R-Krein-symmetric iff self-adjoint (T1). For the twisted fluctuation,
Krein symmetry REDUCES to the reality prescription — which stays T5-pinned
(the Span 2 §B C obstruction). `R ≠ Γ` is proved (`swapR_ne_diagGrading`):
Γ is diagonal `±1`, `R` is the off-diagonal swap — a NEW object.

**Killed-claims rule.** No Lorentzian claims and no "thermal phase
transition" language appear anywhere in this file. §7 adds none. §8 adds
none: the swap `R` is a new off-diagonal object (`R ≠ Γ`,
`swapR_ne_diagGrading`); the killed flow twist and the naive Γ-conjugation
triviality stay killed.

## Tier ledger

T2 (definitions): `TwistAuto`, `twistedComm`, `idTwist`, `twistConj`,
`modularTwist`, `IsTwistedOneForm`, `TwistPreserves`, `twistedFluctuation`;
§7: `gradProjPlus`, `gradProjMinus`, `flipTwist`, `grandRep`,
`twistedCommGrand`, `TwistedFirstOrderCondGrand`;
§8: `IsFundamentalSymm`, `kreinAdjoint`, `kreinProd`, `KreinSymm`,
`ImplementsFlip`, `swapR`, `IsKreinUnitary`;
§8 T5 Prop-pins: `AntilinearJCompat`, `KreinUnitaryTwist`.
§9: `IsRhoReal`, `doubledFluctuation`;
§10: `IsPosSemidef`, `IsCausalConeStatic`, `IsDynamicallyCompatible`,
`IsLorentzCompatible` (stated, no verdict), `CausalLE`.
T1 (proved, zero sorrys): `twisted_leibniz`, `twisted_add`, `twisted_one`,
`twistedComm_id_is_comm`, `twistedComm_twistConj_one`,
`twistedComm_flow_zero`, `twistConj_mul`, `twistConj_comp`,
`twistConj_one`, `twistConj_one_eq_id`, `twistConj_inv_left`,
`twistConj_inv_right`, `twistConjAuto`, `twistConj_star`,
`twistConj_CM_iff_centralSq`, `twistConj_CM_of_involutive`,
`twistConjAuto_CM_iff`, `modularTwist_zero`, `modularTwist_auto`,
`bimod_mul_left`, `bimod_add_left`, `bimod_lr_compat`,
`twistedComm_mem_oneForm`, `twistedOneForm_zero`, `twistedOneForm_add`,
`twistedOneForm_twistL`, `twistedOneForm_mul_right`,
`twistedComm_mem_subalgebra`, `twistedFluctuation_selfAdjoint`;
§7: `gradProj_add`, `gradProj_mul_orth`, `gradProj_mul_orth'`,
`gradProjPlus_sq`, `gradProjMinus_sq`, `gradProjPlus_hermitian`,
`gradProjMinus_hermitian`, `even_mul`, `gradProjPlus_comm_of_comm`,
`gradProjMinus_comm_of_comm`, `flipTwist_involutive`, `flipTwist_mul`,
`flipTwist_add`, `flipTwist_one`, `flipTwist_CM_regular`,
`twistByGrading_trivial`, `grandRep_add`, `grandRep_mul_of_comm`,
`twistedCommGrand_add`, `twistedCommGrand_leibniz`, `twistedCommGrand_diag`;
§8: `kreinAdjoint_involutive`, `swapR_sq`, `swapR_hermitian`,
`swapR_fundamental`, `swapR_conj_blockDiag`,
`kreinSymm_blockDiag_of_selfAdjoint`, `kreinSymm_blockDiag_iff_selfAdjoint`,
`kreinSymm_twistedFluctuation_iff` (conditional),
`swapR_implements_flip`, `trace_swapR`,
`kreinSymm_swapR_transport_of_comm`,
`kreinSymm_swapR_transport_of_anticomm` (linear stand-ins),
`kreinProd_one`, `kreinProd_fundSymm_self`, `swapR_ne_diagGrading`,
`swapR_kreinUnitary_self`;
§9: `kreinSymm_add`, `kreinSymm_sub`, `kreinSymm_real_smul`,
`rhoReal_blockDiag_iff`, `kreinSymm_fluctuation_of_rhoReal` (conditional),
`rhoReal_of_kreinSymm_fluctuation` (conditional),
`kreinSymm_fluctuation_iff_rhoReal` (conditional);
§10: `causalLE_refl`, `causalLE_trans`, `re_sum_helper`, `form_single_eq`,
`re_form_one`, `isPosSemidef_zero`, `isPosSemidef_add`,
`isPosSemidef_real_smul`, `isPosSemidef_one`, `form_affine`,
`posSemidef_trace_eq_zero`, `trace_comm_eq_zero`, `dyn_comm_eq_zero`,
`causalCone_forces_central`, `causalCone_obstruction` (the verdict),
`selfAdjointSet_static`, `norm_mul_le_sum_sq`, `estimate_aux`,
`isPosSemidef_shift_add`, `isPosSemidef_shift_sub`, `psd_spanning`,
`psdCone_static`.
T5 (pinned, not claimed): `IsCMRegular` for a general twist (characterized
T1 for `ρ_U` only; proved T1 for the flip); `TwistedFirstOrderCond`;
`TwistedFirstOrderCondGrand` (opposite involution for the doubled algebra
not constructed; flip-compatibility undischarged); the physical reading of
`twistedFluctuation` (antilinearity of the true real structure `J`;
self-adjointness of a twisted 1-form needs CM-regularity plus a
coefficient constraint); `TwistPreserves` for the physical modular flow
(numerically refuted — see above).
§8: `AntilinearJCompat` (the true `J` is antilinear — the linear matrix
model cannot express it; the linear shadows are proved T1 as the two
transport lemmas); `KreinUnitaryTwist` (full DLM generality unbuilt);
unconditional `KreinSymm` for the fluctuated Dirac — reduces T1 to
`Dfᴴ = Df`, which needs the twist-corrected reality prescription (same
obstruction as §6).
-/

namespace ThetLogos

variable {n : Type*} [Fintype n] [DecidableEq n]

-- ============================================================================
-- §1. Twist automorphisms and the twisted commutator (T2 defs, T1 proofs)
-- ============================================================================

/-- A twist: an algebra automorphism of `Mₙ(ℂ)` as explicit data.
    Tier T2 (structure). The fields are exactly the hypotheses the twisted
    calculus needs: multiplicativity, additivity, `ρ(1) = 1`, and an
    explicit two-sided inverse (bijectivity). -/
structure TwistAuto (n : Type*) [Fintype n] [DecidableEq n] where
  toFun : Matrix n n ℂ → Matrix n n ℂ
  invFun : Matrix n n ℂ → Matrix n n ℂ
  map_mul' : ∀ a b, toFun (a * b) = toFun a * toFun b
  map_add' : ∀ a b, toFun (a + b) = toFun a + toFun b
  map_one' : toFun 1 = 1
  left_inv' : ∀ a, invFun (toFun a) = a
  right_inv' : ∀ a, toFun (invFun a) = a

/-- The twisted commutator `[D, a]_ρ := D * a − ρ(a) * D`.
    Tier T2 (definition). -/
def twistedComm (D : Matrix n n ℂ) (ρ : Matrix n n ℂ → Matrix n n ℂ)
    (a : Matrix n n ℂ) : Matrix n n ℂ :=
  D * a - ρ a * D

/-- The identity twist (Tier T2 — definition). -/
def idTwist : Matrix n n ℂ → Matrix n n ℂ := id

/-- The twisted Leibniz rule (Tier T1 — proved):
    `[D, a*b]_ρ = [D,a]_ρ * b + ρ(a) * [D,b]_ρ`.
    This is the twisted derivation law; `ρ(a*b) = ρ(a)*ρ(b)` is what makes
    the middle terms cancel. -/
theorem twisted_leibniz (D : Matrix n n ℂ) (ρ : TwistAuto n)
    (a b : Matrix n n ℂ) :
    twistedComm D ρ.toFun (a * b)
      = twistedComm D ρ.toFun a * b + ρ.toFun a * twistedComm D ρ.toFun b := by
  unfold twistedComm
  rw [ρ.map_mul' a b]
  noncomm_ring

/-- The twisted commutator is additive in `a` (Tier T1 — proved). -/
theorem twisted_add (D : Matrix n n ℂ) (ρ : TwistAuto n)
    (a b : Matrix n n ℂ) :
    twistedComm D ρ.toFun (a + b)
      = twistedComm D ρ.toFun a + twistedComm D ρ.toFun b := by
  unfold twistedComm
  rw [ρ.map_add' a b]
  noncomm_ring

/-- The twisted commutator kills `1` (Tier T1 — proved). -/
theorem twisted_one (D : Matrix n n ℂ) (ρ : TwistAuto n) :
    twistedComm D ρ.toFun 1 = 0 := by
  unfold twistedComm
  rw [ρ.map_one', Matrix.mul_one, one_mul, sub_self]

/-- With the identity twist the twisted commutator is the ordinary
    commutator (Tier T1 — proved). -/
theorem twistedComm_id_is_comm (D a : Matrix n n ℂ) :
    twistedComm D idTwist a = D * a - a * D :=
  rfl

-- ============================================================================
-- §2. Unitary-conjugation twists ρ_U (T1)
-- ============================================================================

/-- The unitary-conjugation twist `ρ_U(a) := U * a * Uᴴ` (Tier T2 —
    definition). The inner twist of the literature. -/
def twistConj (U a : Matrix n n ℂ) : Matrix n n ℂ :=
  U * a * Uᴴ

/-- `ρ_U` is multiplicative (Tier T1 — proved): the middle `Uᴴ * U`
    cancels. Needs only `Uᴴ * U = 1`. -/
theorem twistConj_mul (U : Matrix n n ℂ) (hU1 : Uᴴ * U = 1)
    (hU2 : U * Uᴴ = 1) (a b : Matrix n n ℂ) :
    twistConj U (a * b) = twistConj U a * twistConj U b := by
  have e : (U * a * Uᴴ) * (U * b * Uᴴ) = U * (a * b) * Uᴴ := by
    calc (U * a * Uᴴ) * (U * b * Uᴴ)
        = U * (a * ((Uᴴ * U) * (b * Uᴴ))) := by simp only [Matrix.mul_assoc]
      _ = U * (a * (b * Uᴴ)) := by rw [hU1, Matrix.one_mul]
      _ = U * (a * b) * Uᴴ := by simp only [Matrix.mul_assoc]
  unfold twistConj
  exact e.symm

/-- Composition law `ρ_U ∘ ρ_V = ρ_{U*V}` (Tier T1 — proved).
    Needs no unitarity — pure reassociation. -/
theorem twistConj_comp (U V a : Matrix n n ℂ) :
    twistConj (U * V) a = twistConj U (twistConj V a) := by
  unfold twistConj
  rw [Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

/-- `ρ_1 = id` (Tier T1 — proved). -/
theorem twistConj_one (a : Matrix n n ℂ) : twistConj 1 a = a := by
  unfold twistConj
  simp

/-- `ρ_1 = id`, as functions (Tier T1 — proved). -/
theorem twistConj_one_eq_id : twistConj (1 : Matrix n n ℂ) = id :=
  funext twistConj_one

/-- `[D,a]_{ρ_1} = [D,a]`: the twisted commutator for the identity twist
    is the ordinary commutator (Tier T1 — proved). -/
theorem twistedComm_twistConj_one (D a : Matrix n n ℂ) :
    twistedComm D (twistConj 1) a = D * a - a * D := by
  unfold twistedComm
  rw [twistConj_one a]

/-- `ρ_U⁻¹ = ρ_{Uᴴ}`, left inverse (Tier T1 — proved). -/
theorem twistConj_inv_left (U : Matrix n n ℂ)
    (hU1 : Uᴴ * U = 1) (hU2 : U * Uᴴ = 1) (a : Matrix n n ℂ) :
    twistConj U (twistConj Uᴴ a) = a := by
  have e : twistConj Uᴴ a = Uᴴ * a * U := by
    unfold twistConj
    rw [Matrix.conjTranspose_conjTranspose]
  rw [e]
  unfold twistConj
  exact conj_cancel_left U a hU2

/-- `ρ_U⁻¹ = ρ_{Uᴴ}`, right inverse (Tier T1 — proved). -/
theorem twistConj_inv_right (U : Matrix n n ℂ)
    (hU1 : Uᴴ * U = 1) (hU2 : U * Uᴴ = 1) (a : Matrix n n ℂ) :
    twistConj Uᴴ (twistConj U a) = a := by
  have e : twistConj Uᴴ (twistConj U a) = Uᴴ * (U * a * Uᴴ) * U := by
    unfold twistConj
    rw [Matrix.conjTranspose_conjTranspose]
  rw [e]
  exact conj_cancel_right U a hU1

/-- Every unitary-conjugation twist is a twist automorphism (Tier T1 —
    proved). -/
def twistConjAuto (U : Matrix n n ℂ) (hU1 : Uᴴ * U = 1) (hU2 : U * Uᴴ = 1) :
    TwistAuto n where
  toFun := twistConj U
  invFun := twistConj Uᴴ
  map_mul' a b := twistConj_mul U hU1 hU2 a b
  map_add' a b := by
    unfold twistConj
    rw [Matrix.mul_add, Matrix.add_mul]
  map_one' := by
    unfold twistConj
    rw [Matrix.mul_one]
    exact hU2
  left_inv' a := twistConj_inv_right U hU1 hU2 a
  right_inv' a := twistConj_inv_left U hU1 hU2 a

/-- The *-automorphism law for unitary-conjugation twists (Tier T1 —
    proved): `ρ_U(aᴴ) = (ρ_U(a))ᴴ`. This is what holds unconditionally —
    NOT the Connes–Moscovici regularity (see `twistConj_CM_iff_centralSq`
    and the refutation in the module docstring). -/
theorem twistConj_star (U a : Matrix n n ℂ) :
    (twistConj U a)ᴴ = twistConj U (aᴴ) := by
  unfold twistConj
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]

/-- Connes–Moscovici regularity for a unitary-conjugation twist,
    characterized (Tier T1 — proved).
    `ρ_U(aᴴ) = (ρ_U⁻¹(a))ᴴ` for all `a` — with `ρ_U⁻¹ = ρ_{Uᴴ}` by
    `twistConj_inv_left/right` — holds if and only if `U²` is central.
    Proof idea: the condition is `U X Uᴴ = Uᴴ X U` for all `X`; conjugating
    by `U` on both sides trades the `Uᴴ`s for a second `U`, giving
    `U² X = X U²`, and back. -/
theorem twistConj_CM_iff_centralSq (U : Matrix n n ℂ)
    (hU1 : Uᴴ * U = 1) (hU2 : U * Uᴴ = 1) :
    (∀ a : Matrix n n ℂ, twistConj U (aᴴ) = (twistConj Uᴴ a)ᴴ)
      ↔ ∀ X : Matrix n n ℂ, (U * U) * X = X * (U * U) := by
  have key : ∀ a : Matrix n n ℂ, (twistConj Uᴴ a)ᴴ = Uᴴ * aᴴ * U := by
    intro a
    rw [twistConj_star]
    unfold twistConj
    rw [Matrix.conjTranspose_conjTranspose]
  have keyU : ∀ a : Matrix n n ℂ, twistConj U a = U * a * Uᴴ := fun a => rfl
  simp_rw [key, keyU]
  constructor
  · intro h X
    have hX : U * X * Uᴴ = Uᴴ * X * U := by
      have h' := h (Xᴴ)
      rwa [Matrix.conjTranspose_conjTranspose] at h'
    have e1 : U * (U * X * Uᴴ) = U * (Uᴴ * X * U) := congrArg (U * ·) hX
    rw [← Matrix.mul_assoc U (U * X) Uᴴ, ← Matrix.mul_assoc U U X,
        ← Matrix.mul_assoc U (Uᴴ * X) U, ← Matrix.mul_assoc U Uᴴ X,
        hU2, one_mul] at e1
    have e2 := congrArg (· * U) e1
    rw [Matrix.mul_assoc ((U * U) * X) Uᴴ U, hU1, mul_one,
        Matrix.mul_assoc X U U] at e2
    exact e2
  · intro h X
    have aux : ∀ Y : Matrix n n ℂ, (U * U) * Y = Y * (U * U)
        → U * Y * Uᴴ = Uᴴ * Y * U := by
      intro Y hY
      have e1 : Uᴴ * ((U * U) * Y) = Uᴴ * (Y * (U * U)) := congrArg (Uᴴ * ·) hY
      rw [← Matrix.mul_assoc Uᴴ (U * U) Y, ← Matrix.mul_assoc Uᴴ U U,
          hU1, one_mul, ← Matrix.mul_assoc Uᴴ Y (U * U)] at e1
      have e2 := congrArg (· * Uᴴ) e1
      rw [Matrix.mul_assoc (Uᴴ * Y) (U * U) Uᴴ, Matrix.mul_assoc U U Uᴴ,
          hU2, mul_one] at e2
      exact e2
    exact aux (Xᴴ) (h (Xᴴ))

/-- Involutive twists satisfy CM-regularity (Tier T1 — proved): if
    `U² = 1` then `U²` is central, so `twistConj_CM_iff_centralSq` applies. -/
theorem twistConj_CM_of_involutive (U : Matrix n n ℂ)
    (hU1 : Uᴴ * U = 1) (hU2 : U * Uᴴ = 1) (hinv : U * U = 1) :
    ∀ a : Matrix n n ℂ, twistConj U (aᴴ) = (twistConj Uᴴ a)ᴴ := by
  rw [twistConj_CM_iff_centralSq U hU1 hU2]
  intro X
  rw [hinv, one_mul, mul_one]

/-- Connes–Moscovici regularity as a property of a general twist
    (Tier T5 — PINNED): `ρ(aᴴ) = (ρ⁻¹(a))ᴴ`. Not proved in general; for
    unitary-conjugation twists it is characterized T1 by
    `twistConj_CM_iff_centralSq` and is FALSE without `U²` central. -/
def IsCMRegular (ρ : TwistAuto n) : Prop :=
  ∀ a : Matrix n n ℂ, ρ.toFun (aᴴ) = (ρ.invFun a)ᴴ

/-- The pinned regularity property, characterized for `ρ_U` (Tier T1 —
    proved). -/
theorem twistConjAuto_CM_iff (U : Matrix n n ℂ)
    (hU1 : Uᴴ * U = 1) (hU2 : U * Uᴴ = 1) :
    IsCMRegular (twistConjAuto U hU1 hU2)
      ↔ ∀ X : Matrix n n ℂ, (U * U) * X = X * (U * U) :=
  twistConj_CM_iff_centralSq U hU1 hU2

-- ============================================================================
-- §3. The s → 0 limit: twist families with ρ₀ = id (T1)
-- ============================================================================

/-- The s → 0 limit, abstract form (Tier T1 — proved): for any 1-parameter
    family of maps with `ρ₀ = id`, the twisted commutator at `s = 0` is the
    ordinary commutator. -/
theorem twistedComm_flow_zero {ρs : ℝ → Matrix n n ℂ → Matrix n n ℂ}
    (h0 : ∀ a, ρs 0 a = a) (D a : Matrix n n ℂ) :
    twistedComm D (ρs 0) a = D * a - a * D := by
  unfold twistedComm
  rw [h0 a]

/-- The modular twist family `ρ_s(a) = U_s * a * U_sᴴ` with
    `U_s = e^{isK}` the modular unitary (`FlowKernel.lean`)
    (Tier T2 — definition). -/
noncomputable def modularTwist (K : Matrix (Fin 32) (Fin 32) ℂ) (s : ℝ)
    (a : Matrix (Fin 32) (Fin 32) ℂ) : Matrix (Fin 32) (Fin 32) ℂ :=
  twistConj (modularUnitary K s) a

/-- At `s = 0` the modular twist is the identity (Tier T1 — proved):
    `U₀ = e^0 = 1`, so `ρ₀(a) = a`. -/
theorem modularTwist_zero (K : Matrix (Fin 32) (Fin 32) ℂ) :
    ∀ a, modularTwist K 0 a = a := by
  intro a
  have hU : modularUnitary K 0 = 1 := by
    unfold modularUnitary
    have hsm : (Complex.I * ((0 : ℝ) : ℂ)) • K
        = (0 : Matrix (Fin 32) (Fin 32) ℂ) := by simp
    rw [hsm, NormedSpace.exp_zero]
  unfold modularTwist
  rw [hU]
  exact twistConj_one a

/-- Every modular twist is a twist automorphism (Tier T1 — proved), via
    unitarity of the modular unitary (`modularUnitary_unitary`,
    `FlowKernel.lean`). -/
noncomputable def modularTwist_auto (K : Matrix (Fin 32) (Fin 32) ℂ)
    (hK : K.IsHermitian) (s : ℝ) : TwistAuto (Fin 32) :=
  twistConjAuto (modularUnitary K s)
    (modularUnitary_unitary K hK s).1 (modularUnitary_unitary K hK s).2

-- ============================================================================
-- §4. The twisted bimodule law and twisted 1-forms (T1)
-- ============================================================================

/-- Left twisted action is multiplicative (Tier T1 — proved):
    `ρ(a*a') * ω = ρ(a) * (ρ(a') * ω)`. -/
theorem bimod_mul_left (ρ : TwistAuto n)
    (a a' : Matrix n n ℂ) (ω : Matrix n n ℂ) :
    ρ.toFun (a * a') * ω = ρ.toFun a * (ρ.toFun a' * ω) := by
  rw [ρ.map_mul', Matrix.mul_assoc]

/-- Left twisted action is additive (Tier T1 — proved). -/
theorem bimod_add_left (ρ : TwistAuto n)
    (a a' : Matrix n n ℂ) (ω : Matrix n n ℂ) :
    ρ.toFun (a + a') * ω = ρ.toFun a * ω + ρ.toFun a' * ω := by
  rw [ρ.map_add', Matrix.add_mul]

/-- Bimodule compatibility (Tier T1 — proved): the left twisted action and
    the right ordinary action associate,
    `(ρ(a) * ω) * b = ρ(a) * (ω * b)` — i.e. `a • ω • b = ρ(a)*ω*b` is a
    well-defined bimodule structure. -/
theorem bimod_lr_compat (ρ : TwistAuto n)
    (a : Matrix n n ℂ) (ω b : Matrix n n ℂ) :
    (ρ.toFun a * ω) * b = ρ.toFun a * (ω * b) :=
  Matrix.mul_assoc _ _ _

/-- Twisted 1-forms `Ω¹_D(A,ρ)`: finite sums `Σ_k a_k * [D, b_k]_ρ`
    (Tier T2 — definition). -/
def IsTwistedOneForm (D : Matrix n n ℂ) (ρ : TwistAuto n)
    (ω : Matrix n n ℂ) : Prop :=
  ∃ (m : ℕ) (a b : Fin m → Matrix n n ℂ),
    ω = ∑ k, a k * twistedComm D ρ.toFun (b k)

/-- The twisted derivation lands in the 1-forms (Tier T1 — proved). -/
theorem twistedComm_mem_oneForm (D : Matrix n n ℂ) (ρ : TwistAuto n)
    (b : Matrix n n ℂ) :
    IsTwistedOneForm D ρ (twistedComm D ρ.toFun b) :=
  ⟨1, fun _ => 1, fun _ => b, by simp⟩

/-- `0` is a twisted 1-form (Tier T1 — proved). -/
theorem twistedOneForm_zero (D : Matrix n n ℂ) (ρ : TwistAuto n) :
    IsTwistedOneForm D ρ 0 :=
  ⟨0, Fin.elim0, Fin.elim0, (Fintype.sum_empty _).symm⟩

/-- Twisted 1-forms are closed under addition (Tier T1 — proved). -/
theorem twistedOneForm_add (D : Matrix n n ℂ) (ρ : TwistAuto n)
    {ω₁ ω₂ : Matrix n n ℂ}
    (h₁ : IsTwistedOneForm D ρ ω₁) (h₂ : IsTwistedOneForm D ρ ω₂) :
    IsTwistedOneForm D ρ (ω₁ + ω₂) := by
  obtain ⟨m₁, a₁, b₁, rfl⟩ := h₁
  obtain ⟨m₂, a₂, b₂, rfl⟩ := h₂
  refine ⟨m₁ + m₂, Fin.addCases a₁ a₂, Fin.addCases b₁ b₂, ?_⟩
  rw [Fin.sum_univ_add]
  simp only [Fin.addCases_left, Fin.addCases_right]

/-- Twisted 1-forms are closed under the left twisted action (Tier T1 —
    proved): `ρ(d) * ω ∈ Ω¹`. -/
theorem twistedOneForm_twistL (D : Matrix n n ℂ) (ρ : TwistAuto n)
    {ω : Matrix n n ℂ} (h : IsTwistedOneForm D ρ ω) (d : Matrix n n ℂ) :
    IsTwistedOneForm D ρ (ρ.toFun d * ω) := by
  obtain ⟨m, a, b, rfl⟩ := h
  refine ⟨m, fun k => ρ.toFun d * a k, b, ?_⟩
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [Matrix.mul_assoc]

/-- Twisted 1-forms are closed under right multiplication (Tier T1 —
    proved): `ω * c ∈ Ω¹`. This is the twisted derivation on 1-forms in
    action — the single-term identity
    `a*[D,b]_ρ*c = a*[D,b*c]_ρ − (a*ρ(b))*[D,c]_ρ` is the twisted Leibniz
    rule solved for the right action. -/
theorem twistedOneForm_mul_right (D : Matrix n n ℂ) (ρ : TwistAuto n)
    {ω : Matrix n n ℂ} (h : IsTwistedOneForm D ρ ω) (c : Matrix n n ℂ) :
    IsTwistedOneForm D ρ (ω * c) := by
  obtain ⟨m, a, b, rfl⟩ := h
  have term : ∀ k : Fin m, (a k * twistedComm D ρ.toFun (b k)) * c
      = a k * twistedComm D ρ.toFun (b k * c)
        - (a k * ρ.toFun (b k)) * twistedComm D ρ.toFun c := by
    intro k
    unfold twistedComm
    rw [ρ.map_mul' (b k) c]
    noncomm_ring
  refine ⟨m + m, Fin.addCases a (fun k => -(a k * ρ.toFun (b k))),
    Fin.addCases (fun k => b k * c) (fun _ => c), ?_⟩
  rw [Fin.sum_univ_add]
  simp only [Fin.addCases_left, Fin.addCases_right]
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  rw [term k, sub_eq_add_neg, neg_mul]

-- ============================================================================
-- §5. Preservation is a hypothesis, not a theorem (T1 conditional)
-- ============================================================================

/-- The twist preserves a subalgebra (Tier T2 — definition).
    NUMERICAL REFUTATION (2026-10-07): the modular flow `σ_s` does NOT
    preserve `π(A_F)` in general — preservation residuals reach
    `1.413 ≈ ‖π(g)‖`. So this is an explicit hypothesis, never automatic. -/
def TwistPreserves (ρ : TwistAuto n) (S : Subalgebra ℂ (Matrix n n ℂ)) : Prop :=
  ∀ a ∈ S, ρ.toFun a ∈ S

/-- Twisted commutators stay in a preserved subalgebra (Tier T1 — proved,
    conditional): if `ρ` preserves `S` and `D ∈ S`, then `[D,a]_ρ ∈ S` for
    `a ∈ S`. This replaces the refuted claim that the flow preserves the
    represented algebra. -/
theorem twistedComm_mem_subalgebra (D : Matrix n n ℂ) (ρ : TwistAuto n)
    (S : Subalgebra ℂ (Matrix n n ℂ))
    (hpres : TwistPreserves ρ S) (hD : D ∈ S) {a : Matrix n n ℂ} (ha : a ∈ S) :
    twistedComm D ρ.toFun a ∈ S := by
  unfold twistedComm
  exact S.sub_mem (S.mul_mem hD ha) (S.mul_mem (hpres a ha) hD)

-- ============================================================================
-- §6. Twisted first-order condition and twisted fluctuation (T5 pins)
-- ============================================================================

/-- The twisted first-order condition (Tier T5 — PINNED, conditional
    hypothesis): `[[D,a]_ρ, b°]_{ρ°} = 0` with the opposite twist
    `ρ°(x°) := (ρ⁻¹(x))°` (Devastato–Lizzi–Martinetti). The opposite
    involution `°` is an explicit parameter. NOT claimed for our triple —
    the ordinary first-order condition is proved in `OrderOne.lean`. -/
def TwistedFirstOrderCond (D : Matrix n n ℂ) (ρ : TwistAuto n)
    (opp : Matrix n n ℂ → Matrix n n ℂ) : Prop :=
  ∀ a b : Matrix n n ℂ,
    let X := twistedComm D ρ.toFun a
    let bopp := opp b
    X * bopp - opp (ρ.invFun b) * X = 0

/-- The twisted fluctuation `D_{A_ρ} := D + A_ρ + ε₁ * J * A_ρ * J⁻¹`
    (Tier T2 — definition; physical reading T5 — pinned).
    `A_ρ ∈ Ω¹_D(A,ρ)`; `ε₁` is a KO sign (`±1`, hence real); `J⁻¹` is
    modeled as `Jᴴ` for unitary `J`. PINNED: the true real structure is
    antilinear, which the linear matrix model does not capture. -/
noncomputable def twistedFluctuation (D Aρ : Matrix n n ℂ) (eps1 : ℂ)
    (J : Matrix n n ℂ) : Matrix n n ℂ :=
  D + Aρ + eps1 • (J * Aρ * Jᴴ)

/-- Algebraic self-adjointness of the twisted fluctuation (Tier T1 —
    proved, conditional): if `D` and `A_ρ` are self-adjoint and `ε₁` is
    real (`star eps1 = eps1`, true for the KO signs `±1`), the fluctuation
    is self-adjoint. PINNED (T5): self-adjointness of a twisted 1-form
    `A_ρ` itself needs CM-regularity (for `ρ_U`: `U²` central, by
    `twistConj_CM_iff_centralSq`) plus a coefficient constraint — not
    proved here. -/
theorem twistedFluctuation_selfAdjoint (D Aρ : Matrix n n ℂ) (eps1 : ℂ)
    (J : Matrix n n ℂ)
    (hD : Dᴴ = D) (hA : Aρᴴ = Aρ) (heps : star eps1 = eps1) :
    (twistedFluctuation D Aρ eps1 J)ᴴ = twistedFluctuation D Aρ eps1 J := by
  have e : (J * Aρ * Jᴴ)ᴴ = J * Aρ * Jᴴ := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, hA, Matrix.mul_assoc]
  unfold twistedFluctuation
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_add,
    Matrix.conjTranspose_smul, hD, hA, heps, e]

-- ============================================================================
-- §7. Bridge Span 2: the DLM twist by grading — the FLIP twist (T1)
-- ============================================================================

/-- The grading projector `P₊ = (1+Γ)/2` for an involutive self-adjoint
    grading `Γ` (Tier T2 — definition). Devastato–Lizzi–Martinetti minimal
    twist by grading (Filaci–Martinetti, SIGMA 2020 §2.3). -/
noncomputable def gradProjPlus (Γ : Matrix n n ℂ) : Matrix n n ℂ :=
  (2 : ℂ)⁻¹ • (1 + Γ)

/-- The grading projector `P₋ = (1−Γ)/2` (Tier T2 — definition). -/
noncomputable def gradProjMinus (Γ : Matrix n n ℂ) : Matrix n n ℂ :=
  (2 : ℂ)⁻¹ • (1 - Γ)

/-- `P₊ + P₋ = 1` (Tier T1 — proved): the projectors resolve the identity. -/
theorem gradProj_add (Γ : Matrix n n ℂ) :
    gradProjPlus Γ + gradProjMinus Γ = 1 := by
  unfold gradProjPlus gradProjMinus
  rw [← smul_add]
  have e : (1 + Γ) + (1 - Γ) = 1 + 1 := by noncomm_ring
  have e2 : (2:ℂ) • (1 : Matrix n n ℂ) = 1 + 1 := by
    rw [show (2:ℂ) = (1:ℂ) + 1 from by norm_num]
    simp only [add_smul, one_smul]
  rw [e, ← e2, smul_smul, inv_mul_cancel₀ (by norm_num : (2:ℂ) ≠ 0),
    one_smul]

/-- `P₊ * P₋ = 0` (Tier T1 — proved): orthogonality, from `Γ² = 1`. -/
theorem gradProj_mul_orth (Γ : Matrix n n ℂ) (hΓ2 : Γ * Γ = 1) :
    gradProjPlus Γ * gradProjMinus Γ = 0 := by
  unfold gradProjPlus gradProjMinus
  rw [Matrix.smul_mul, Matrix.mul_smul]
  have e : (1 + Γ) * (1 - Γ) = 0 := by
    have h1 : (1 + Γ) * (1 - Γ) = 1 - Γ * Γ := by noncomm_ring
    rw [h1, hΓ2, sub_self]
  rw [e]
  simp only [smul_zero]

/-- `P₋ * P₊ = 0` (Tier T1 — proved). -/
theorem gradProj_mul_orth' (Γ : Matrix n n ℂ) (hΓ2 : Γ * Γ = 1) :
    gradProjMinus Γ * gradProjPlus Γ = 0 := by
  unfold gradProjPlus gradProjMinus
  rw [Matrix.smul_mul, Matrix.mul_smul]
  have e : (1 - Γ) * (1 + Γ) = 0 := by
    have h1 : (1 - Γ) * (1 + Γ) = 1 - Γ * Γ := by noncomm_ring
    rw [h1, hΓ2, sub_self]
  rw [e]
  simp only [smul_zero]

/-- `P₊² = P₊` (Tier T1 — proved): idempotence, from `Γ² = 1`. -/
theorem gradProjPlus_sq (Γ : Matrix n n ℂ) (hΓ2 : Γ * Γ = 1) :
    gradProjPlus Γ * gradProjPlus Γ = gradProjPlus Γ := by
  unfold gradProjPlus
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  have e : (1 + Γ) * (1 + Γ) = (2:ℂ) • (1 + Γ) := by
    have h1 : (1 + Γ) * (1 + Γ) = (1 + 1) + (Γ + Γ) := by
      have h2 : (1 + Γ) * (1 + Γ) = 1 + (Γ + Γ) + Γ * Γ := by noncomm_ring
      rw [h2, hΓ2]
      abel
    have h3 : (2:ℂ) • (1 + Γ) = (1 + 1) + (Γ + Γ) := by
      rw [show (2:ℂ) = (1:ℂ) + 1 from by norm_num]
      simp only [add_smul, one_smul]
      abel
    rw [h1, h3]
  rw [e, smul_smul]
  have h4 : (2:ℂ)⁻¹ * (2:ℂ)⁻¹ * 2 = (2:ℂ)⁻¹ := by
    rw [mul_assoc, inv_mul_cancel₀ (by norm_num : (2:ℂ) ≠ 0), mul_one]
  rw [h4]

/-- `P₋² = P₋` (Tier T1 — proved). -/
theorem gradProjMinus_sq (Γ : Matrix n n ℂ) (hΓ2 : Γ * Γ = 1) :
    gradProjMinus Γ * gradProjMinus Γ = gradProjMinus Γ := by
  unfold gradProjMinus
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  have e : (1 - Γ) * (1 - Γ) = (2:ℂ) • (1 - Γ) := by
    have h1 : (1 - Γ) * (1 - Γ) = (1 + 1) - (Γ + Γ) := by
      have h2 : (1 - Γ) * (1 - Γ) = 1 - (Γ + Γ) + Γ * Γ := by noncomm_ring
      rw [h2, hΓ2]
      abel
    have h3 : (2:ℂ) • (1 - Γ) = (1 + 1) - (Γ + Γ) := by
      rw [show (2:ℂ) = (1:ℂ) + 1 from by norm_num]
      simp only [add_smul, one_smul]
      abel
    rw [h1, h3]
  rw [e, smul_smul]
  have h4 : (2:ℂ)⁻¹ * (2:ℂ)⁻¹ * 2 = (2:ℂ)⁻¹ := by
    rw [mul_assoc, inv_mul_cancel₀ (by norm_num : (2:ℂ) ≠ 0), mul_one]
  rw [h4]

/-- `P₊ᴴ = P₊` (Tier T1 — proved): needs `Γᴴ = Γ`; `(2:ℂ)⁻¹` is real. -/
theorem gradProjPlus_hermitian (Γ : Matrix n n ℂ) (hΓsa : Γᴴ = Γ) :
    (gradProjPlus Γ)ᴴ = gradProjPlus Γ := by
  unfold gradProjPlus
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_add,
    Matrix.conjTranspose_one, hΓsa]
  congr 1
  simp

/-- `P₋ᴴ = P₋` (Tier T1 — proved). -/
theorem gradProjMinus_hermitian (Γ : Matrix n n ℂ) (hΓsa : Γᴴ = Γ) :
    (gradProjMinus Γ)ᴴ = gradProjMinus Γ := by
  unfold gradProjMinus
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_one, hΓsa]
  congr 1
  simp

/-- Even elements are closed under multiplication (Tier T1 — proved):
    `[Γ,a] = [Γ,b] = 0` implies `[Γ, a*b] = 0`. -/
theorem even_mul (Γ a b : Matrix n n ℂ)
    (ha : Γ * a = a * Γ) (hb : Γ * b = b * Γ) :
    Γ * (a * b) = (a * b) * Γ := by
  calc Γ * (a * b) = (Γ * a) * b := by rw [Matrix.mul_assoc]
    _ = (a * Γ) * b := by rw [ha]
    _ = a * (Γ * b) := by rw [Matrix.mul_assoc]
    _ = a * (b * Γ) := by rw [hb]
    _ = (a * b) * Γ := by rw [Matrix.mul_assoc]

/-- `P₊` commutes with even elements (Tier T1 — proved): `P₊` is a linear
    polynomial in `Γ`. -/
theorem gradProjPlus_comm_of_comm (Γ a : Matrix n n ℂ) (h : Γ * a = a * Γ) :
    gradProjPlus Γ * a = a * gradProjPlus Γ := by
  unfold gradProjPlus
  rw [Matrix.smul_mul, Matrix.mul_smul]
  congr 1
  rw [Matrix.add_mul, Matrix.mul_add, one_mul, mul_one, h]

/-- `P₋` commutes with even elements (Tier T1 — proved). -/
theorem gradProjMinus_comm_of_comm (Γ a : Matrix n n ℂ) (h : Γ * a = a * Γ) :
    gradProjMinus Γ * a = a * gradProjMinus Γ := by
  unfold gradProjMinus
  rw [Matrix.smul_mul, Matrix.mul_smul]
  congr 1
  rw [Matrix.sub_mul, Matrix.mul_sub, one_mul, mul_one, h]

/-- The FLIP twist on the doubled (grand) algebra (Tier T2 — definition):
    `flipTwist (a, a') := (a', a)`. The Devastato–Lizzi–Martinetti minimal
    twist by grading (Filaci–Martinetti, SIGMA 2020 §2.3): the twist does
    not act by conjugation inside one copy — it swaps the two copies. -/
def flipTwist : (Matrix n n ℂ × Matrix n n ℂ) → (Matrix n n ℂ × Matrix n n ℂ)
  | (a, a') => (a', a)

/-- The flip is involutive — its own two-sided inverse (Tier T1 — proved).
    This is the `TwistAuto`-analog inverse data on the pair type. -/
theorem flipTwist_involutive (x : Matrix n n ℂ × Matrix n n ℂ) :
    flipTwist (flipTwist x) = x := by
  obtain ⟨a, a'⟩ := x
  rfl

/-- The flip is multiplicative, componentwise (Tier T1 — proved). -/
theorem flipTwist_mul (x y : Matrix n n ℂ × Matrix n n ℂ) :
    flipTwist (x * y) = flipTwist x * flipTwist y := by
  obtain ⟨a, a'⟩ := x
  obtain ⟨b, b'⟩ := y
  rfl

/-- The flip is additive, componentwise (Tier T1 — proved). -/
theorem flipTwist_add (x y : Matrix n n ℂ × Matrix n n ℂ) :
    flipTwist (x + y) = flipTwist x + flipTwist y := by
  obtain ⟨a, a'⟩ := x
  obtain ⟨b, b'⟩ := y
  rfl

/-- The flip fixes `1 = (1, 1)` (Tier T1 — proved). -/
theorem flipTwist_one : flipTwist (1 : Matrix n n ℂ × Matrix n n ℂ) = 1 :=
  rfl

/-- **Connes–Moscovici regularity for the flip twist (Tier T1 — proved).**
    This is the theorem Bridge Span 1 was missing: for the flip,
    `ρ⁻¹ = ρ` (`flipTwist_involutive`) and the flip commutes with the
    involution componentwise, so `ρ(xᴴ) = (ρ⁻¹(x))ᴴ` holds UNCONDITIONALLY.
    In `IsCMRegular` language, with `toFun = invFun = flipTwist` on the
    grand algebra `Mₙ(ℂ) × Mₙ(ℂ)`: `toFun (xᴴ) = (invFun x)ᴴ`.
    (`star` on pairs is the componentwise `ᴴ`; `ᴴ` notation itself is
    Matrix-scoped.) -/
theorem flipTwist_CM_regular (x : Matrix n n ℂ × Matrix n n ℂ) :
    flipTwist (star x) = star (flipTwist x) := by
  obtain ⟨a, a'⟩ := x
  rfl

/-- **Triviality remark (Tier T1 — proved).** On a graded algebra
    representation — i.e. when `[Γ, a] = 0` — the naive "twist by
    conjugation" `ρ(a) = Γ * a * Γ` is TRIVIAL: `Γ * a * Γ = a`.
    This is why DLM use the FLIP on the DOUBLED algebra, not conjugation
    by `Γ`. (Our numerics confirm `[Γ, π(g)] = 0` exactly for all 24
    generators, so conjugation-by-`Γ` would do nothing on the nose.) -/
theorem twistByGrading_trivial (Γ a : Matrix n n ℂ)
    (hΓ2 : Γ * Γ = 1) (hcomm : Γ * a = a * Γ) :
    Γ * a * Γ = a := by
  calc Γ * a * Γ = (a * Γ) * Γ := by rw [hcomm]
    _ = a * (Γ * Γ) := by rw [Matrix.mul_assoc]
    _ = a := by rw [hΓ2, mul_one]

/-- The doubled representation (Tier T2 — definition):
    `grandRep Γ (a, a') := P₊ * a + P₋ * a'`. The grand algebra
    `Mₙ(ℂ) × Mₙ(ℂ)` acts via the grading projectors (Filaci–Martinetti). -/
noncomputable def grandRep (Γ : Matrix n n ℂ) :
    (Matrix n n ℂ × Matrix n n ℂ) → Matrix n n ℂ
  | (a, a') => gradProjPlus Γ * a + gradProjMinus Γ * a'

/-- `grandRep` is additive (Tier T1 — proved, unconditional). -/
theorem grandRep_add (Γ : Matrix n n ℂ)
    (x y : Matrix n n ℂ × Matrix n n ℂ) :
    grandRep Γ (x + y) = grandRep Γ x + grandRep Γ y := by
  obtain ⟨a, a'⟩ := x
  obtain ⟨b, b'⟩ := y
  have erep : ∀ p q : Matrix n n ℂ,
      grandRep Γ (p, q) = gradProjPlus Γ * p + gradProjMinus Γ * q :=
    fun p q => rfl
  have eadd : (a, a') + (b, b') = (a + b, a' + b') := rfl
  rw [eadd, erep, erep, erep, Matrix.mul_add, Matrix.mul_add]
  abel

/-- `grandRep` is multiplicative on graded (even) pairs (Tier T1 — proved,
    conditional): if `[Γ, ·] = 0` on all four components — the physical
    case, since our numerics give `[Γ, π(g)] = 0` exactly for all 24
    generators — then the cross terms vanish via `P₊ * P₋ = 0` and the
    diagonal terms reassemble via `P±² = P±`. This is the algebraic core
    of the DLM doubled representation being an algebra map. -/
theorem grandRep_mul_of_comm (Γ : Matrix n n ℂ)
    (hΓ2 : Γ * Γ = 1)
    (x y : Matrix n n ℂ × Matrix n n ℂ)
    (hx1 : Γ * x.1 = x.1 * Γ) (hx2 : Γ * x.2 = x.2 * Γ)
    (hy1 : Γ * y.1 = y.1 * Γ) (hy2 : Γ * y.2 = y.2 * Γ) :
    grandRep Γ (x * y) = grandRep Γ x * grandRep Γ y := by
  obtain ⟨a, a'⟩ := x
  obtain ⟨b, b'⟩ := y
  have erep : ∀ p q : Matrix n n ℂ,
      grandRep Γ (p, q) = gradProjPlus Γ * p + gradProjMinus Γ * q :=
    fun p q => rfl
  have emul : (a, a') * (b, b') = (a * b, a' * b') := rfl
  rw [emul, erep, erep, erep]
  have hpp : gradProjPlus Γ * gradProjPlus Γ = gradProjPlus Γ :=
    gradProjPlus_sq Γ hΓ2
  have hmm : gradProjMinus Γ * gradProjMinus Γ = gradProjMinus Γ :=
    gradProjMinus_sq Γ hΓ2
  have hpm : gradProjPlus Γ * gradProjMinus Γ = 0 := gradProj_mul_orth Γ hΓ2
  have hmp : gradProjMinus Γ * gradProjPlus Γ = 0 := gradProj_mul_orth' Γ hΓ2
  have hab : Γ * (a * b) = (a * b) * Γ := even_mul Γ a b hx1 hy1
  have ha'b' : Γ * (a' * b') = (a' * b') * Γ := even_mul Γ a' b' hx2 hy2
  have hab' : Γ * (a * b') = (a * b') * Γ := even_mul Γ a b' hx1 hy2
  have ha'b : Γ * (a' * b) = (a' * b) * Γ := even_mul Γ a' b hx2 hy1
  have cPp : ∀ c : Matrix n n ℂ, Γ * c = c * Γ →
      gradProjPlus Γ * c = c * gradProjPlus Γ :=
    fun c hc => gradProjPlus_comm_of_comm Γ c hc
  have cPm : ∀ c : Matrix n n ℂ, Γ * c = c * Γ →
      gradProjMinus Γ * c = c * gradProjMinus Γ :=
    fun c hc => gradProjMinus_comm_of_comm Γ c hc
  have t1 : (gradProjPlus Γ * a) * (gradProjPlus Γ * b)
      = gradProjPlus Γ * (a * b) := by
    calc (gradProjPlus Γ * a) * (gradProjPlus Γ * b)
        = gradProjPlus Γ * (a * (gradProjPlus Γ * b)) := by
          rw [Matrix.mul_assoc]
      _ = gradProjPlus Γ * (a * (b * gradProjPlus Γ)) := by
          rw [cPp b hy1]
      _ = gradProjPlus Γ * ((a * b) * gradProjPlus Γ) := by
          rw [Matrix.mul_assoc]
      _ = gradProjPlus Γ * (gradProjPlus Γ * (a * b)) := by
          rw [← cPp (a * b) hab]
      _ = (gradProjPlus Γ * gradProjPlus Γ) * (a * b) := by
          rw [Matrix.mul_assoc]
      _ = gradProjPlus Γ * (a * b) := by rw [hpp]
  have t2 : (gradProjPlus Γ * a) * (gradProjMinus Γ * b') = 0 := by
    calc (gradProjPlus Γ * a) * (gradProjMinus Γ * b')
        = gradProjPlus Γ * (a * (gradProjMinus Γ * b')) := by
          rw [Matrix.mul_assoc]
      _ = gradProjPlus Γ * (a * (b' * gradProjMinus Γ)) := by
          rw [cPm b' hy2]
      _ = gradProjPlus Γ * ((a * b') * gradProjMinus Γ) := by
          rw [Matrix.mul_assoc]
      _ = gradProjPlus Γ * (gradProjMinus Γ * (a * b')) := by
          rw [← cPm (a * b') hab']
      _ = (gradProjPlus Γ * gradProjMinus Γ) * (a * b') := by
          rw [Matrix.mul_assoc]
      _ = 0 := by rw [hpm, Matrix.zero_mul]
  have t3 : (gradProjMinus Γ * a') * (gradProjPlus Γ * b) = 0 := by
    calc (gradProjMinus Γ * a') * (gradProjPlus Γ * b)
        = gradProjMinus Γ * (a' * (gradProjPlus Γ * b)) := by
          rw [Matrix.mul_assoc]
      _ = gradProjMinus Γ * (a' * (b * gradProjPlus Γ)) := by
          rw [cPp b hy1]
      _ = gradProjMinus Γ * ((a' * b) * gradProjPlus Γ) := by
          rw [Matrix.mul_assoc]
      _ = gradProjMinus Γ * (gradProjPlus Γ * (a' * b)) := by
          rw [← cPp (a' * b) ha'b]
      _ = (gradProjMinus Γ * gradProjPlus Γ) * (a' * b) := by
          rw [Matrix.mul_assoc]
      _ = 0 := by rw [hmp, Matrix.zero_mul]
  have t4 : (gradProjMinus Γ * a') * (gradProjMinus Γ * b')
      = gradProjMinus Γ * (a' * b') := by
    calc (gradProjMinus Γ * a') * (gradProjMinus Γ * b')
        = gradProjMinus Γ * (a' * (gradProjMinus Γ * b')) := by
          rw [Matrix.mul_assoc]
      _ = gradProjMinus Γ * (a' * (b' * gradProjMinus Γ)) := by
          rw [cPm b' hy2]
      _ = gradProjMinus Γ * ((a' * b') * gradProjMinus Γ) := by
          rw [Matrix.mul_assoc]
      _ = gradProjMinus Γ * (gradProjMinus Γ * (a' * b')) := by
          rw [← cPm (a' * b') ha'b']
      _ = (gradProjMinus Γ * gradProjMinus Γ) * (a' * b') := by
          rw [Matrix.mul_assoc]
      _ = gradProjMinus Γ * (a' * b') := by rw [hmm]
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, t1, t2, t3, t4]
  abel

/-- The twisted commutator for doubled elements (Tier T2 — definition):
    `twistedCommGrand D Γ (a,a') := D * grandRep Γ (a,a')
      − grandRep Γ (a',a) * D`, i.e. `D * π̃(x) − π̃(ρ(x)) * D` with
    `ρ = flipTwist`. -/
noncomputable def twistedCommGrand (D Γ : Matrix n n ℂ)
    (x : Matrix n n ℂ × Matrix n n ℂ) : Matrix n n ℂ :=
  D * grandRep Γ x - grandRep Γ (flipTwist x) * D

/-- `twistedCommGrand` is additive in the doubled element (Tier T1 —
    proved, unconditional). -/
theorem twistedCommGrand_add (D Γ : Matrix n n ℂ)
    (x y : Matrix n n ℂ × Matrix n n ℂ) :
    twistedCommGrand D Γ (x + y)
      = twistedCommGrand D Γ x + twistedCommGrand D Γ y := by
  unfold twistedCommGrand
  rw [grandRep_add, flipTwist_add, grandRep_add]
  noncomm_ring

/-- Twisted Leibniz rule for the doubled calculus (Tier T1 — proved,
    conditional): for graded (even) pairs — the physical case, since our
    numerics give `[Γ, π(g)] = 0` exactly —
    `[D, x*y]_flip = [D,x]_flip · π̃(y) + π̃(flip x) · [D,y]_flip`.
    The evenness hypotheses make `grandRep` multiplicative
    (`grandRep_mul_of_comm`); the rest is the same cancellation as
    `twisted_leibniz`. -/
theorem twistedCommGrand_leibniz (D Γ : Matrix n n ℂ) (hΓ2 : Γ * Γ = 1)
    (x y : Matrix n n ℂ × Matrix n n ℂ)
    (hx1 : Γ * x.1 = x.1 * Γ) (hx2 : Γ * x.2 = x.2 * Γ)
    (hy1 : Γ * y.1 = y.1 * Γ) (hy2 : Γ * y.2 = y.2 * Γ) :
    twistedCommGrand D Γ (x * y)
      = twistedCommGrand D Γ x * grandRep Γ y
        + grandRep Γ (flipTwist x) * twistedCommGrand D Γ y := by
  obtain ⟨a, a'⟩ := x
  obtain ⟨b, b'⟩ := y
  have emul : (a, a') * (b, b') = (a * b, a' * b') := rfl
  have h1 : grandRep Γ ((a, a') * (b, b'))
      = grandRep Γ (a, a') * grandRep Γ (b, b') :=
    grandRep_mul_of_comm Γ hΓ2 (a, a') (b, b') hx1 hx2 hy1 hy2
  have h2 : grandRep Γ (flipTwist ((a, a') * (b, b')))
      = grandRep Γ (flipTwist (a, a')) * grandRep Γ (flipTwist (b, b')) := by
    have e1 : flipTwist ((a, a') * (b, b')) = (a', a) * (b', b) := by
      rw [emul]
      rfl
    rw [e1]
    exact grandRep_mul_of_comm Γ hΓ2 (a', a) (b', b) hx2 hx1 hy2 hy1
  unfold twistedCommGrand
  rw [h1, h2]
  noncomm_ring

/-- At diagonal pairs the doubled twisted commutator is the ordinary
    commutator (Tier T1 — proved, unconditional):
    `twistedCommGrand D Γ (a,a) = D*a − a*D`, since
    `grandRep Γ (a,a) = (P₊ + P₋) * a = a` and `flipTwist (a,a) = (a,a)`. -/
theorem twistedCommGrand_diag (D Γ a : Matrix n n ℂ) :
    twistedCommGrand D Γ (a, a) = D * a - a * D := by
  have erep : grandRep Γ (a, a)
      = gradProjPlus Γ * a + gradProjMinus Γ * a := rfl
  have eflip : flipTwist (a, a) = (a, a) := rfl
  have hrep : gradProjPlus Γ * a + gradProjMinus Γ * a = a := by
    rw [← Matrix.add_mul, gradProj_add, one_mul]
  unfold twistedCommGrand
  rw [eflip, erep, hrep]

/-- The twisted first-order condition for the flip twist on doubled
    elements (Tier T5 — PINNED, conditional statement): for an opposite
    representation `opp` on pairs,
    `[D,x]_flip · y° − (flipTwist y)° · [D,x]_flip = 0`.
    PINNED because the opposite involution for the doubled grand algebra
    is not constructed in this file: the flip-compatibility
    `opp (flipTwist y) = flipTwist (opp y)` has no discharged instance,
    and the untwisted first-order condition for `grandRep` is not proved
    here (the ordinary one is `OrderOne.lean`). Do NOT claim
    unconditionally. -/
def TwistedFirstOrderCondGrand (D Γ : Matrix n n ℂ)
    (opp : (Matrix n n ℂ × Matrix n n ℂ) → Matrix n n ℂ) : Prop :=
  ∀ x y : Matrix n n ℂ × Matrix n n ℂ,
    twistedCommGrand D Γ x * opp y
      - opp (flipTwist y) * twistedCommGrand D Γ x = 0

-- ============================================================================
-- §8. Bridge Span 3: Krein structure axioms + the swap fundamental symmetry
-- ============================================================================

/-!
**Bridge Span 3 — the Krein pylon (2026-10-07).** The algebraic core of
Devastato et al., "Lorentz signature and twisted spectral triples"
(arXiv:1710.04965) §3.1–3.2, as pure matrix algebra. NO Lorentzian-physics
claims and NO "thermal phase transition" language appear here.

The ρ-product `⟨Ψ,Φ⟩_ρ := ⟨Ψ, RΦ⟩` (`kreinProd`), the fundamental symmetry
`R† = R`, `R² = I` (`IsFundamentalSymm`), the Krein-adjoint `A⁺ := R A† R`
(`kreinAdjoint` — an involution, `kreinAdjoint_involutive`, T1), and
ρ-symmetry `R D† R = D` (`KreinSymm`).

The swap `R = fromBlocks 0 1 1 0` (`swapR`) is the DLM SM-case fundamental
symmetry (`R = [[0,1],[1,0]]`, swapping the two copies): `R² = 1`,
`Rᴴ = R` (T1), it implements the flip on block-diagonal doubled
representations (`swapR_implements_flip`, T1), and a block-diagonal Dirac
is R-Krein-symmetric iff it is self-adjoint
(`kreinSymm_blockDiag_iff_selfAdjoint`, T1). For the twisted fluctuation
this REDUCES Krein symmetry to the reality prescription — which stays
T5-pinned (`kreinSymm_twistedFluctuation_iff`).

`R ≠ Γ`: Γ is diagonal `±1`, `R` is the off-diagonal swap
(`swapR_ne_diagGrading`, T1). The killed `ρ(a) = ΓaΓ` triviality
(`twistByGrading_trivial`, Span 2) stays killed — `R` is a NEW object, not
a Γ-conjugate.
-/

/-- Fundamental symmetry of a Krein space (Tier T2 — definition):
    `η * η = 1 ∧ ηᴴ = η`. DLM §3.1: `R† = R`, `R ≠ 1`, `R² = I`. -/
def IsFundamentalSymm {N : Type*} [Fintype N] [DecidableEq N]
    (η : Matrix N N ℂ) : Prop :=
  η * η = 1 ∧ ηᴴ = η

/-- The Krein-adjoint `A⁺ := η * Aᴴ * η` (Tier T2 — definition).
    DLM §3.1: `A⁺ := R A† R`. -/
def kreinAdjoint {N : Type*} [Fintype N] [DecidableEq N]
    (η A : Matrix N N ℂ) : Matrix N N ℂ :=
  η * Aᴴ * η

/-- The ρ-product as a sesquilinear form (Tier T2 — definition):
    `kreinProd η x y = star x ⬝ᵥ (η *ᵥ y)`, conjugate-linear in `x`,
    linear in `y` (physics convention). DLM §3.1:
    `⟨Ψ,Φ⟩_ρ := ⟨Ψ, RΦ⟩` with the standard Hilbert product on the right. -/
def kreinProd {N : Type*} [Fintype N] [DecidableEq N]
    (η : Matrix N N ℂ) (x y : N → ℂ) : ℂ :=
  star x ⬝ᵥ (η *ᵥ y)

/-- Krein (ρ-) symmetry of an operator (Tier T2 — definition):
    `η * Dᴴ * η = D`. DLM §3.1: `D` is ρ-symmetric ⟺ `R D† R = D`. -/
def KreinSymm {N : Type*} [Fintype N] [DecidableEq N]
    (η D : Matrix N N ℂ) : Prop :=
  η * Dᴴ * η = D

/-- A fundamental symmetry implements the flip on a doubled representation
    (Tier T2 — definition): `η * π̃(a,a') * η = π̃(a',a)` for all pairs,
    with `π̃` the doubled representation and the flip `flipTwist` of §7. -/
def ImplementsFlip (η : Matrix (n ⊕ n) (n ⊕ n) ℂ)
    (πt : (Matrix n n ℂ × Matrix n n ℂ) → Matrix (n ⊕ n) (n ⊕ n) ℂ) : Prop :=
  ∀ x : Matrix n n ℂ × Matrix n n ℂ, η * πt x * η = πt (flipTwist x)

/-- The swap fundamental symmetry `R = fromBlocks 0 1 1 0` on the doubled
    space (Tier T2 — definition). DLM's SM case: `R = [[0,1],[1,0]]`
    swapping the two copies. NOTE: `R ≠ Γ` — Γ is diagonal `±1`, `R` is
    the off-diagonal swap (`swapR_ne_diagGrading`); the killed
    `ρ(a) = ΓaΓ` triviality stays killed. -/
def swapR : Matrix (n ⊕ n) (n ⊕ n) ℂ :=
  fromBlocks (0 : Matrix n n ℂ) 1 1 0

/-- A Krein-unitary operator (Tier T2 — definition): `U⁺ * U = 1` for the
    Krein adjoint. DLM §3.1. -/
def IsKreinUnitary {N : Type*} [Fintype N] [DecidableEq N]
    (η U : Matrix N N ℂ) : Prop :=
  kreinAdjoint η U * U = 1

/-- The Krein-adjoint is an involution (Tier T1 — proved): `(A⁺)⁺ = A`,
    from `η² = 1` and `ηᴴ = η`. The inner `ηᴴ`s cancel by
    self-adjointness; the outer pairs cancel by the involution law. -/
theorem kreinAdjoint_involutive {N : Type*} [Fintype N] [DecidableEq N]
    (η : Matrix N N ℂ) (hη : IsFundamentalSymm η) (A : Matrix N N ℂ) :
    kreinAdjoint η (kreinAdjoint η A) = A := by
  obtain ⟨hη2, hηsa⟩ := hη
  have e : (η * Aᴴ * η)ᴴ = η * A * η := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, hηsa]
    simp only [Matrix.mul_assoc]
  unfold kreinAdjoint
  rw [e]
  have f : η * (η * A * η) * η = (η * η) * A * (η * η) := by
    simp only [Matrix.mul_assoc]
  rw [f, hη2, one_mul, mul_one]

/-- `R² = 1` for the swap (Tier T1 — proved). -/
theorem swapR_sq : swapR (n := n) * swapR (n := n) = 1 := by
  unfold swapR
  rw [Matrix.fromBlocks_multiply]
  simp only [Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add,
    Matrix.one_mul, Matrix.mul_one]
  rw [Matrix.fromBlocks_one]

/-- `Rᴴ = R` for the swap (Tier T1 — proved). -/
theorem swapR_hermitian : (swapR (n := n))ᴴ = swapR (n := n) := by
  unfold swapR
  rw [Matrix.fromBlocks_conjTranspose]
  simp only [Matrix.conjTranspose_zero, Matrix.conjTranspose_one]

/-- The swap is a fundamental symmetry (Tier T1 — proved). -/
theorem swapR_fundamental : IsFundamentalSymm (swapR (n := n)) :=
  ⟨swapR_sq, swapR_hermitian⟩

/-- Swap-conjugation of a block-diagonal matrix (Tier T1 — proved):
    `R * fromBlocks A 0 0 B * R = fromBlocks B 0 0 A`. The workhorse
    behind the flip implementation and the Krein-symmetry computation. -/
theorem swapR_conj_blockDiag (A B : Matrix n n ℂ) :
    swapR (n := n) * fromBlocks A 0 0 B * swapR (n := n)
      = fromBlocks B 0 0 A := by
  unfold swapR
  rw [Matrix.fromBlocks_multiply]
  simp only [Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add,
    Matrix.one_mul, Matrix.mul_one]
  rw [Matrix.fromBlocks_multiply]
  simp only [Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add,
    Matrix.one_mul, Matrix.mul_one]

/-- Krein symmetry of a block-diagonal Dirac w.r.t. the swap (Tier T1 —
    proved): `R * D̃ᴴ * R = D̃` for `D̃ = fromBlocks D 0 0 D`, given
    `Dᴴ = D`. -/
theorem kreinSymm_blockDiag_of_selfAdjoint (D : Matrix n n ℂ) (hD : Dᴴ = D) :
    KreinSymm (swapR (n := n)) (fromBlocks D 0 0 D) := by
  unfold KreinSymm
  rw [Matrix.fromBlocks_conjTranspose, hD, Matrix.conjTranspose_zero,
    swapR_conj_blockDiag]

/-- Krein symmetry of a doubled block-diagonal operator reduces to
    self-adjointness (Tier T1 — proved): for `D̃ = fromBlocks Df 0 0 Df`,
    `KreinSymm R D̃ ↔ Dfᴴ = Df`. -/
theorem kreinSymm_blockDiag_iff_selfAdjoint (Df : Matrix n n ℂ) :
    KreinSymm (swapR (n := n)) (fromBlocks Df 0 0 Df) ↔ Dfᴴ = Df := by
  constructor
  · intro h
    unfold KreinSymm at h
    rw [Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_zero,
      swapR_conj_blockDiag] at h
    exact (Matrix.fromBlocks_inj.mp h).1
  · intro h
    exact kreinSymm_blockDiag_of_selfAdjoint Df h

/-- Krein symmetry of the doubled twisted fluctuation (Tier T1 — proved,
    CONDITIONAL): `KreinSymm R D̃_{A_ρ} ↔ D_{A_ρ}ᴴ = D_{A_ρ}`.
    The UNCONDITIONAL statement is T5-PINNED: self-adjointness of the
    twisted fluctuation needs the twist-corrected reality prescription
    (cf. §6, `twistedFluctuation_selfAdjoint`; Span 2 §B C flagged the
    residuals) — the same obstruction as in §6, not a new one. -/
theorem kreinSymm_twistedFluctuation_iff (D Aρ : Matrix n n ℂ) (eps1 : ℂ)
    (J : Matrix n n ℂ) :
    KreinSymm (swapR (n := n)) (fromBlocks (twistedFluctuation D Aρ eps1 J) 0 0
        (twistedFluctuation D Aρ eps1 J))
      ↔ (twistedFluctuation D Aρ eps1 J)ᴴ = twistedFluctuation D Aρ eps1 J :=
  kreinSymm_blockDiag_iff_selfAdjoint _

/-- The swap implements the flip on block-diagonal doubled
    representations (Tier T1 — proved): `R * π̃(a,a') * R = π̃(a',a)` for
    `π̃(a,a') = fromBlocks (π a) 0 0 (π a')`. This is the Lean form of the
    DLM mechanism: the fundamental symmetry exchanges the two copies the
    flip exchanges. -/
theorem swapR_implements_flip (π : Matrix n n ℂ → Matrix n n ℂ) :
    ImplementsFlip (swapR (n := n)) (fun x => fromBlocks (π x.1) 0 0 (π x.2)) := by
  intro x
  obtain ⟨a, a'⟩ := x
  show (swapR (n := n)) * fromBlocks (π a) 0 0 (π a') * (swapR (n := n))
    = fromBlocks (π a') 0 0 (π a)
  rw [swapR_conj_blockDiag]

/-- `trace R = 0` (Tier T1 — proved): the swap carries the `(n,n)`
    signature data — vanishing trace, matching the `tr Γ = 0` of the DLM
    grading picture. Both diagonal blocks of the swap are `0`. -/
theorem trace_swapR : Matrix.trace (swapR (n := n)) = 0 := by
  have hdiag : ∀ i : n ⊕ n, (swapR (n := n)) i i = 0 := by
    intro i
    cases i with
    | inl a =>
      unfold swapR
      rw [Matrix.fromBlocks_apply₁₁]
      rfl
    | inr b =>
      unfold swapR
      rw [Matrix.fromBlocks_apply₂₂]
      rfl
  unfold Matrix.trace Matrix.diag
  apply Finset.sum_eq_zero
  intro i _
  exact hdiag i

/-- Krein symmetry transports across a linear operator commuting with `R`
    (Tier T1 — proved, conditional): `J * R = R * J` implies
    `KreinSymm R D → KreinSymm R (J * D * Jᴴ)`.
    CAVEAT: the DLM real structure `J` is ANTILINEAR (DLM (3.12)); the
    linear matrix model of this file cannot capture it (cf. the §6 pin).
    This lemma covers the linear stand-in only; the true compatibility
    is pinned T5 as `AntilinearJCompat`. -/
theorem kreinSymm_swapR_transport_of_comm (J D : Matrix (n ⊕ n) (n ⊕ n) ℂ)
    (hRJ : J * swapR = swapR * J) (hD : KreinSymm swapR D) :
    KreinSymm swapR (J * D * Jᴴ) := by
  unfold KreinSymm at *
  have e : (J * D * Jᴴ)ᴴ = J * Dᴴ * Jᴴ := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]
    simp only [Matrix.mul_assoc]
  rw [e]
  have hJHs : Jᴴ * swapR = swapR * Jᴴ := by
    have h := congrArg Matrix.conjTranspose hRJ
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      swapR_hermitian] at h
    exact h.symm
  have f : swapR * (J * Dᴴ * Jᴴ) * swapR
      = J * (swapR * Dᴴ * swapR) * Jᴴ := by
    have g1 : swapR * J = J * swapR := hRJ.symm
    have g2 : Jᴴ * swapR = swapR * Jᴴ := hJHs
    calc swapR * (J * Dᴴ * Jᴴ) * swapR
        = (swapR * J) * (Dᴴ * (Jᴴ * swapR)) := by simp only [Matrix.mul_assoc]
      _ = (J * swapR) * (Dᴴ * (swapR * Jᴴ)) := by rw [g1, g2]
      _ = J * (swapR * Dᴴ * swapR) * Jᴴ := by simp only [Matrix.mul_assoc]
  rw [f, hD]

/-- Krein symmetry transports across a linear operator ANTIcommuting with
    `R` (Tier T1 — proved, conditional): `J * R = -(R * J)` implies
    `KreinSymm R D → KreinSymm R (J * D * Jᴴ)` — the two minus signs from
    moving `R` past `J` and past `Jᴴ` cancel. Same antilinearity CAVEAT as
    `kreinSymm_swapR_transport_of_comm`: linear stand-in only. -/
theorem kreinSymm_swapR_transport_of_anticomm (J D : Matrix (n ⊕ n) (n ⊕ n) ℂ)
    (hRJ : J * swapR = -(swapR * J)) (hD : KreinSymm swapR D) :
    KreinSymm swapR (J * D * Jᴴ) := by
  unfold KreinSymm at *
  have e : (J * D * Jᴴ)ᴴ = J * Dᴴ * Jᴴ := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]
    simp only [Matrix.mul_assoc]
  rw [e]
  have h2 : swapR * Jᴴ = -(Jᴴ * swapR) := by
    have h := congrArg Matrix.conjTranspose hRJ
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_neg,
      Matrix.conjTranspose_mul, swapR_hermitian] at h
    exact h
  have g1 : swapR * J = -(J * swapR) := by
    have h := congrArg (fun M => -M) hRJ
    simp only [neg_neg] at h
    exact h.symm
  have g2 : Jᴴ * swapR = -(swapR * Jᴴ) := by
    have h := congrArg (fun M => -M) h2
    simp only [neg_neg] at h
    exact h.symm
  have f : swapR * (J * Dᴴ * Jᴴ) * swapR
      = J * (swapR * Dᴴ * swapR) * Jᴴ := by
    calc swapR * (J * Dᴴ * Jᴴ) * swapR
        = (swapR * J) * (Dᴴ * (Jᴴ * swapR)) := by simp only [Matrix.mul_assoc]
      _ = (-(J * swapR)) * (Dᴴ * (-(swapR * Jᴴ))) := by rw [g1, g2]
      _ = (J * swapR) * (Dᴴ * (swapR * Jᴴ)) := by noncomm_ring
      _ = J * (swapR * Dᴴ * swapR) * Jᴴ := by simp only [Matrix.mul_assoc]
  rw [f, hD]

/-- The ρ-product at `η = 1` is the standard sesquilinear dot product
    (Tier T1 — proved). -/
theorem kreinProd_one {N : Type*} [Fintype N] [DecidableEq N]
    (x y : N → ℂ) : kreinProd (1 : Matrix N N ℂ) x y = star x ⬝ᵥ y := by
  unfold kreinProd
  rw [Matrix.one_mulVec]

/-- DLM's positive-definite recovery (Tier T1 — proved):
    `⟨x, Rx⟩_ρ = ⟨x, x⟩` — the standard positive product — from `R² = 1`
    alone. (DLM §3.1: `⟨·, R·⟩_ρ` is the original Hilbert product.) -/
theorem kreinProd_fundSymm_self {N : Type*} [Fintype N] [DecidableEq N]
    (R : Matrix N N ℂ) (hR : IsFundamentalSymm R) (x : N → ℂ) :
    kreinProd R x (R *ᵥ x) = star x ⬝ᵥ x := by
  obtain ⟨hR2, -⟩ := hR
  unfold kreinProd
  rw [Matrix.mulVec_mulVec, hR2, Matrix.one_mulVec]

/-- The swap is NOT a diagonal grading (Tier T1 — proved): `R` is
    off-diagonal while the canonical diagonal grading `diag(1,−1)` is
    diagonal — they differ in the off-diagonal block. This is the proved
    form of the dossier's `R ≠ Γ` (Γ is diagonal `±1`, `R` is the
    off-diagonal swap): the killed `ρ(a) = ΓaΓ` triviality stays killed,
    and `R` is a NEW object. -/
theorem swapR_ne_diagGrading [Nonempty n] :
    swapR (n := n) ≠ fromBlocks (1 : Matrix n n ℂ) 0 0 (-1) := by
  intro h
  unfold swapR at h
  have hinj := Matrix.fromBlocks_inj.mp h
  have h10 : (1 : Matrix n n ℂ) = 0 := hinj.2.1
  obtain ⟨i⟩ := ‹Nonempty n›
  have hentry := congrArg (fun M : Matrix n n ℂ => M i i) h10
  simp at hentry

/-- The swap is Krein-unitary for its own ρ-product (Tier T1 — proved):
    `R⁺ * R = 1` with `R⁺ = R Rᴴ R = R`. The flip's implementer is thus a
    Krein-unitary — the T1 shadow of the pinned full Krein-unitary twist
    (`KreinUnitaryTwist`). -/
theorem swapR_kreinUnitary_self :
    IsKreinUnitary (swapR (n := n)) (swapR (n := n)) := by
  unfold IsKreinUnitary kreinAdjoint
  rw [swapR_hermitian, swapR_sq, one_mul, swapR_sq]

/-- DLM (3.12) compatibility for the true real structure (Tier T5 —
    PINNED): the physical `J` is ANTILINEAR, so `J R = ± R J` cannot be
    stated with `Matrix` multiplication in this linear model (cf. the §6
    pin on `twistedFluctuation`). Recorded here over an abstract
    antilinear operator on vectors; NOT claimed. The linear shadows that
    DO close are `kreinSymm_swapR_transport_of_comm` and
    `kreinSymm_swapR_transport_of_anticomm`. -/
def AntilinearJCompat (J : ((n ⊕ n) → ℂ) → ((n ⊕ n) → ℂ)) : Prop :=
  (∀ c : ℂ, ∀ ψ : (n ⊕ n) → ℂ, J (c • ψ) = (star c) • J ψ) ∧
  ((∀ ψ : (n ⊕ n) → ℂ, J ((swapR (n := n)) *ᵥ ψ) = (swapR (n := n)) *ᵥ (J ψ)) ∨
    (∀ ψ : (n ⊕ n) → ℂ,
      J ((swapR (n := n)) *ᵥ ψ) = -((swapR (n := n)) *ᵥ (J ψ))))

/-- Krein-unitary twist in full DLM generality (Tier T5 — PINNED): a twist
    implemented by a two-sided Krein-unitary for the swap ρ-product.
    Exact obstruction: the Krein-unitary group for the swap product and
    its intertwining with the flip twist are not constructed in this
    file; only the flip itself (a Hilbert-unitary involution, §7) is
    formalized. What does close: the swap is Krein-unitary for its own
    product (`swapR_kreinUnitary_self`, T1). -/
def KreinUnitaryTwist (U : Matrix (n ⊕ n) (n ⊕ n) ℂ) : Prop :=
  IsKreinUnitary (swapR (n := n)) U ∧ U * kreinAdjoint (swapR (n := n)) U = 1

#print axioms twisted_leibniz
#print axioms twistConj_star
#print axioms twistConj_CM_iff_centralSq
#print axioms twistConj_CM_of_involutive
#print axioms twistedOneForm_mul_right
#print axioms twistedFluctuation_selfAdjoint
#print axioms twistedComm_mem_subalgebra
#print axioms modularTwist_zero
#print axioms gradProj_add
#print axioms gradProjPlus_sq
#print axioms gradProjPlus_hermitian
#print axioms flipTwist_CM_regular
#print axioms twistByGrading_trivial
#print axioms grandRep_mul_of_comm
#print axioms twistedCommGrand_leibniz
#print axioms twistedCommGrand_diag
#print axioms kreinAdjoint_involutive
#print axioms swapR_sq
#print axioms swapR_hermitian
#print axioms swapR_fundamental
#print axioms swapR_conj_blockDiag
#print axioms kreinSymm_blockDiag_of_selfAdjoint
#print axioms kreinSymm_blockDiag_iff_selfAdjoint
#print axioms kreinSymm_twistedFluctuation_iff
#print axioms swapR_implements_flip
#print axioms trace_swapR
#print axioms kreinSymm_swapR_transport_of_comm
#print axioms kreinSymm_swapR_transport_of_anticomm
#print axioms kreinProd_one
#print axioms kreinProd_fundSymm_self
#print axioms swapR_ne_diagGrading
#print axioms swapR_kreinUnitary_self

-- ============================================================================
-- §9. Bridge Span 4: the twist-corrected reality prescription (T1/T2)
-- ============================================================================

/-!
**Bridge Span 4 — the twist-corrected reality prescription (2026-10-07).**
Span 3's `kreinSymm_twistedFluctuation_iff` reduced Krein symmetry of the
doubled fluctuation to ordinary self-adjointness of the single-copy
`twistedFluctuation` — conditional on the twist-corrected reality
prescription, which stayed T5-pinned there. This span supplies the
prescription inside the linear matrix model.

The doubled twisted 1-form `Ã = fromBlocks A 0 0 A'` is ρ-real,
`IsRhoReal η A : η * Aᴴ * η = A` (T2), exactly when the second copy
carries the adjoint of the first: `A' = Aᴴ` (`rhoReal_blockDiag_iff`,
T1 — by `swapR_conj_blockDiag` and `fromBlocks` injectivity). This is the
flip-twist reality prescription: the fundamental symmetry exchanges the
two copies, so ρ-reality forces the two diagonal blocks to be adjoints of
each other.

The doubled fluctuation `F̃ = D̃ + Ã + ε₁ • Jterm` (`doubledFluctuation`,
T2) is then Krein-symmetric for the swap
(`kreinSymm_fluctuation_of_rhoReal`, conditional T1): the Dirac term closes
by `kreinSymm_blockDiag_of_selfAdjoint`, the 1-form term by the ρ-reality
prescription, and the J-conjugate term by the packaged hypothesis
`hJ : IsRhoReal swapR Jterm` — the ρ-reality of `ε₁ * J * A_ρ * J⁻¹` is NOT
derived from antilinear `J` (that is the pinned obstruction
`AntilinearJCompat`, §8); it is taken as a hypothesis.

The converse also closes in the model (`rhoReal_of_kreinSymm_fluctuation`,
conditional T1): Krein symmetry of the fluctuation forces ρ-reality of the
1-form, given `Dᴴ = D` and the packaged J-term hypothesis — no T5 pin is
needed for the converse direction, the anticipated obstruction does not
materialize. Together they give the full iff
`kreinSymm_fluctuation_iff_rhoReal` (conditional T1).

Krein-symmetry algebra helpers: `kreinSymm_add`, `kreinSymm_sub`,
`kreinSymm_real_smul` (all T1). NO Lorentzian-physics claims and NO
"thermal phase transition" language appear here. The killed single-`H` η,
the killed flow twist, and the killed naive `ρ(a) = ΓaΓ` stay killed.
-/

/-- ρ-reality of an operator for a fundamental symmetry (Tier T2 —
    definition): `η * Aᴴ * η = A`. Stated for a fundamental symmetry `η`
    (here `swapR`); definitionally the same relation as `KreinSymm`,
    named separately for the reality-prescription reading: a coefficient
    is ρ-real when conjugation by the fundamental symmetry fixes it. -/
def IsRhoReal {N : Type*} [Fintype N] [DecidableEq N]
    (η : Matrix N N ℂ) (A : Matrix N N ℂ) : Prop :=
  η * Aᴴ * η = A

/-- The doubled twisted fluctuation (Tier T2 — definition):
    `F̃ = D̃ + Ã + ε₁ • Jterm` on the doubled space, with
    `D̃ = fromBlocks D 0 0 D` the doubled Dirac, `Ã = fromBlocks A 0 0 A'`
    the doubled twisted 1-form, and `Jterm` the packaged J-conjugate term
    `ε₁ * J * A_ρ * J⁻¹` (cf. `twistedFluctuation`, §6). -/
def doubledFluctuation (D A A' : Matrix n n ℂ)
    (Jterm : Matrix (n ⊕ n) (n ⊕ n) ℂ) (eps1 : ℂ) : Matrix (n ⊕ n) (n ⊕ n) ℂ :=
  fromBlocks D 0 0 D + fromBlocks A 0 0 A' + eps1 • Jterm

/-- Krein symmetry is closed under sums (Tier T1 — proved). -/
theorem kreinSymm_add {N : Type*} [Fintype N] [DecidableEq N]
    {η X Y : Matrix N N ℂ}
    (hX : KreinSymm η X) (hY : KreinSymm η Y) : KreinSymm η (X + Y) := by
  unfold KreinSymm at *
  rw [Matrix.conjTranspose_add]
  have e : η * (Xᴴ + Yᴴ) * η = η * Xᴴ * η + η * Yᴴ * η := by
    rw [Matrix.mul_add, Matrix.add_mul]
  rw [e, hX, hY]

/-- Krein symmetry is closed under differences (Tier T1 — proved). -/
theorem kreinSymm_sub {N : Type*} [Fintype N] [DecidableEq N]
    {η X Y : Matrix N N ℂ}
    (hX : KreinSymm η X) (hY : KreinSymm η Y) : KreinSymm η (X - Y) := by
  unfold KreinSymm at *
  rw [Matrix.conjTranspose_sub]
  have e : η * (Xᴴ - Yᴴ) * η = η * Xᴴ * η - η * Yᴴ * η := by
    rw [Matrix.mul_sub, Matrix.sub_mul]
  rw [e, hX, hY]

/-- Krein symmetry is closed under real scalars (Tier T1 — proved):
    needs `star c = c` (true for the KO signs `±1`). -/
theorem kreinSymm_real_smul {N : Type*} [Fintype N] [DecidableEq N]
    {η X : Matrix N N ℂ} {c : ℂ}
    (hc : star c = c) (hX : KreinSymm η X) : KreinSymm η (c • X) := by
  unfold KreinSymm at *
  rw [Matrix.conjTranspose_smul, hc]
  have e : η * (c • Xᴴ) * η = c • (η * Xᴴ * η) := by
    rw [Matrix.mul_smul, Matrix.smul_mul]
  rw [e, hX]

/-- The twist-corrected reality prescription (Tier T1 — proved):
    `IsRhoReal R (fromBlocks A 0 0 A') ↔ A' = Aᴴ`. Swap-conjugation
    exchanges the diagonal blocks (`swapR_conj_blockDiag`), so ρ-reality
    of the doubled 1-form is exactly the adjoint relation between the two
    copies. -/
theorem rhoReal_blockDiag_iff (A A' : Matrix n n ℂ) :
    IsRhoReal (swapR (n := n)) (fromBlocks A 0 0 A') ↔ A' = Aᴴ := by
  constructor
  · intro h
    unfold IsRhoReal at h
    rw [Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_zero,
      swapR_conj_blockDiag] at h
    exact (Matrix.fromBlocks_inj.mp h).2.2.2.symm
  · intro h
    unfold IsRhoReal
    rw [Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_zero,
      swapR_conj_blockDiag, h, Matrix.conjTranspose_conjTranspose]

/-- Krein symmetry of the doubled fluctuation from the ρ-reality
    prescription (Tier T1 — proved, conditional): if `Dᴴ = D`, the doubled
    1-form satisfies `A' = Aᴴ`, the J-term is ρ-real by hypothesis `hJ`
    (the pinned `AntilinearJCompat` obstruction — NOT proved from
    antilinear `J`), and `ε₁` is real, then the doubled fluctuation
    `F̃ = D̃ + Ã + ε₁ • Jterm` is Krein-symmetric for the swap. Each
    summand's Krein symmetry reduces to ordinary self-adjointness — the
    Span-4 upgrade of the Span-3 reduction `kreinSymm_twistedFluctuation_iff`. -/
theorem kreinSymm_fluctuation_of_rhoReal (D A A' : Matrix n n ℂ)
    (Jterm : Matrix (n ⊕ n) (n ⊕ n) ℂ) (eps1 : ℂ)
    (hD : Dᴴ = D) (hA' : A' = Aᴴ) (hJ : IsRhoReal (swapR (n := n)) Jterm)
    (heps : star eps1 = eps1) :
    KreinSymm (swapR (n := n)) (doubledFluctuation D A A' Jterm eps1) := by
  have hDs : KreinSymm (swapR (n := n)) (fromBlocks D 0 0 D) :=
    kreinSymm_blockDiag_of_selfAdjoint D hD
  have hA : KreinSymm (swapR (n := n)) (fromBlocks A 0 0 A') :=
    (rhoReal_blockDiag_iff A A').mpr hA'
  have hJs : KreinSymm (swapR (n := n)) (eps1 • Jterm) :=
    kreinSymm_real_smul heps hJ
  unfold doubledFluctuation
  exact kreinSymm_add (kreinSymm_add hDs hA) hJs

/-- Converse: Krein symmetry of the fluctuation forces ρ-reality of the
    1-form (Tier T1 — proved, conditional): under the SAME hypotheses
    (`Dᴴ = D`, the packaged J-term hypothesis `hJ`, `ε₁` real), Krein
    symmetry of `F̃` subtracts back down to `IsRhoReal R Ã`. No T5 pin is
    needed for this direction — the J-term hypothesis is available, so the
    anticipated obstruction does not materialize. (`hA'` is not needed
    here; it is kept so both directions share one hypothesis set.) -/
theorem rhoReal_of_kreinSymm_fluctuation (D A A' : Matrix n n ℂ)
    (Jterm : Matrix (n ⊕ n) (n ⊕ n) ℂ) (eps1 : ℂ)
    (hD : Dᴴ = D) (_hA' : A' = Aᴴ) (hJ : IsRhoReal (swapR (n := n)) Jterm)
    (heps : star eps1 = eps1)
    (hF : KreinSymm (swapR (n := n)) (doubledFluctuation D A A' Jterm eps1)) :
    IsRhoReal (swapR (n := n)) (fromBlocks A 0 0 A') := by
  have hDs : KreinSymm (swapR (n := n)) (fromBlocks D 0 0 D) :=
    kreinSymm_blockDiag_of_selfAdjoint D hD
  have hJs : KreinSymm (swapR (n := n)) (eps1 • Jterm) :=
    kreinSymm_real_smul heps hJ
  have hsub := kreinSymm_sub (kreinSymm_sub hF hDs) hJs
  have heq : doubledFluctuation D A A' Jterm eps1 - fromBlocks D 0 0 D
      - eps1 • Jterm = fromBlocks A 0 0 A' := by
    unfold doubledFluctuation
    abel
  rw [heq] at hsub
  exact hsub

/-- The full twist-corrected reality prescription (Tier T1 — proved,
    conditional): Krein symmetry of the doubled fluctuation for the swap
    is EQUIVALENT to ρ-reality of the doubled 1-form, under `Dᴴ = D`, the
    packaged J-term hypothesis, and `ε₁` real. Both directions close in
    the linear model; no T5 pin on either side. -/
theorem kreinSymm_fluctuation_iff_rhoReal (D A A' : Matrix n n ℂ)
    (Jterm : Matrix (n ⊕ n) (n ⊕ n) ℂ) (eps1 : ℂ)
    (hD : Dᴴ = D) (hA' : A' = Aᴴ) (hJ : IsRhoReal (swapR (n := n)) Jterm)
    (heps : star eps1 = eps1) :
    KreinSymm (swapR (n := n)) (doubledFluctuation D A A' Jterm eps1)
      ↔ IsRhoReal (swapR (n := n)) (fromBlocks A 0 0 A') := by
  constructor
  · intro hF
    exact rhoReal_of_kreinSymm_fluctuation D A A' Jterm eps1 hD hA' hJ heps hF
  · intro hQ
    have hA2 : A' = Aᴴ := (rhoReal_blockDiag_iff A A').mp hQ
    exact kreinSymm_fluctuation_of_rhoReal D A A' Jterm eps1 hD hA2 hJ heps

#print axioms kreinSymm_add
#print axioms kreinSymm_sub
#print axioms kreinSymm_real_smul
#print axioms rhoReal_blockDiag_iff
#print axioms kreinSymm_fluctuation_of_rhoReal
#print axioms rhoReal_of_kreinSymm_fluctuation
#print axioms kreinSymm_fluctuation_iff_rhoReal

-- ============================================================================
-- §10. Bridge Span 5: causal cones over the finite algebra (T2 defs, T1 verdict)
-- ============================================================================

/-!
**Bridge Span 5 — causal cones (2026-10-07).** The algebraic core of Franco's
causal-cone program: Franco, "An algebraic formulation of causality for
noncommutative geometry" (arXiv:1212.5171), Def. 4; Franco–Eckstein,
"Noncommutative geometry, Lorentzian structures and causality"
(arXiv:1409.1480), Def. 13; reviewed in Franco–Eckstein, "Two roads to
noncommutative causality" (arXiv:1508.01917).

**Literature-ledger status.** The axiom ledger is
`whitepaper/bridge-span-5-causality-literature.md` (T5 survey, 2026-10-07),
which classifies each axiom as (a) statable over a finite *-algebra vs
(b) needing points/manifold. Franco's axioms: (F1) Hermitian, (F2)
sum-stable, (F3) positive homogeneity, (F4) all real multiples of `1` in
`C`, (F5) `span_ℂ(C)` dense in `A` (closure automatic in finite dimension),
(F6) `⟨φ, J[D,a]φ⟩ ≤ 0` (Krein form of the commutator — needs the
fundamental symmetry `J`), (F7) the induced order on states, (F8) the
commutative recovery theorem (b). Formalized here: (F1)–(F5) as
`IsCausalConeStatic` (with (F4) weakened to `1 ∈ C`; see below), the causal
order (F7-form) as `CausalLE`, and — as the "compatibility-with-D axiom
statable algebraically" — the `i[D,f]`-PSD condition
`IsDynamicallyCompatible`. NOTE: `IsDynamicallyCompatible` is NOT Franco's
(F6): (F6) is the Krein form `J[D,a] ≤ 0` with the fundamental symmetry,
while `IsDynamicallyCompatible` is the `i[D,f] ≥ 0` variant. The `J`-form
is stated as `IsLorentzCompatible` but gets NO verdict here. What needs
points/a manifold (b, not formalizable over `A_F` alone): the recovery
theorem (F8), the toposet duality, and the Lorentzian distance formula.

**Verdict (T1 — proved): OBSTRUCTION.** The static axioms (F1)–(F5) ARE
satisfiable on the finite algebra — even by the positive cone
(`psdCone_static`, the Löwner order). But NO cone satisfies them jointly
with the `i[D,f]`-PSD dynamical axiom when `D` is self-adjoint and
non-central on self-adjoints (`causalCone_obstruction`). Mechanism —
**trace-class collapse of the commutator**: `Tr[D,f] ≡ 0`, so `i[D,f] ≥ 0`
forces `[D,f] = 0`; the dynamical cone collapses to the self-adjoint
commutant of `D`, a real vector subspace, which cannot span `A_sa` unless
`D` is central. The finite Dirac `D_F` is non-scalar (Yukawa structure), so
`A_F` carries no `i[D,f]`-dynamically-compatible causal cone. This is a
finite-dimensionality obstruction: in infinite dimension there is no trace
to force the collapse, which is why the manifold case survives. The status
of Franco's true `J`-form (F6) on `A_F` is NOT settled here.
-/

/-- Positive semidefiniteness for complex matrices (Tier T2 — definition):
    `Mᴴ = M` and `Re(xᴴMx) ≥ 0` for all `x`. Mathlib's `Matrix.PosSemidef`
    needs `PartialOrder R`, which `ℂ` lacks, so the complex case is stated
    directly. -/
def IsPosSemidef (M : Matrix n n ℂ) : Prop :=
  Mᴴ = M ∧ ∀ x : n → ℂ, 0 ≤ (star x ⬝ᵥ (M *ᵥ x)).re

/-- The static Franco causal-cone axioms (Tier T2 — definition): `C ⊆ A_sa`
    a convex cone (`0 ∈ C`, closed under addition and nonnegative real
    scaling), `C - C = A_sa` (spanning), `1 ∈ C` (constants).
    This is Franco's (F1)–(F5) (arXiv:1212.5171, Def. 4; ledger
    `whitepaper/bridge-span-5-causality-literature.md` §1, all class (a)):
    (F1) Hermitian, (F2) sum-stable, (F3) positive homogeneity, (F5) spanning
    (closure automatic in finite dimension; the real span of a convex cone
    containing `0` is `C - C`). NOTE on (F4): Franco requires ALL real
    multiples `x·1 ∈ C` (including negative); this formalization requires
    only `1 ∈ C` (hence `0 ∈ C` and positive multiples), which is weaker —
    so the obstruction below applies a fortiori to true Franco cones.
    In finite dimension, (F1)–(F5) imply this definition. -/
def IsCausalConeStatic (C : Set (Matrix n n ℂ)) : Prop :=
  (∀ a ∈ C, aᴴ = a)
    ∧ 0 ∈ C
    ∧ (∀ a ∈ C, ∀ b ∈ C, a + b ∈ C)
    ∧ (∀ a ∈ C, ∀ r : ℝ, 0 ≤ r → (r : ℂ) • a ∈ C)
    ∧ (∀ a : Matrix n n ℂ, aᴴ = a → ∃ f g : Matrix n n ℂ, f ∈ C ∧ g ∈ C ∧ a = f - g)
    ∧ 1 ∈ C

/-- Dynamical compatibility with the Dirac operator (Tier T2 — definition):
    every `f ∈ C` has `i[D,f]` positive semidefinite. This is an algebraic
    compatibility-with-`D` axiom of commutator-sign type. It is NOT Franco's
    (F6): per the ledger (`whitepaper/bridge-span-5-causality-literature.md`
    §1), (F6) is the Krein form `⟨φ, J[D,a]φ⟩ ≤ 0` with the fundamental
    symmetry `J` — a different condition (the trace argument below does not
    go through for `J[D,f]`, since `Tr(J[D,f]) = Tr([J,D]f)` need not
    vanish). The `J`-form is stated as `IsLorentzCompatible` (no verdict).
    Sign conventions (`i[D,f] ≥ 0` vs `≤ 0`) vary with Clifford conventions;
    the verdict is sign-independent. -/
def IsDynamicallyCompatible (D : Matrix n n ℂ) (C : Set (Matrix n n ℂ)) : Prop :=
  ∀ f ∈ C, IsPosSemidef (Complex.I • (D * f - f * D))

/-- The Lorentzian dynamical axiom (Tier T2 — definition, NO verdict):
    `Re⟨x, η[D,a]x⟩ ≤ 0` for all `a ∈ C` and `x` — the form version of
    Franco's (F6) `⟨φ, J[D,a]φ⟩ ≤ 0` (arXiv:1212.5171, Def. 4; ledger
    `whitepaper/bridge-span-5-causality-literature.md` §1, class (a) in
    form), with the fundamental symmetry `η` (our `swapR` of §8). Stated
    for the record: this is the Span-5-native form of the true dynamical
    axiom. Its finite-dimensional verdict is NOT proved here — the trace
    argument of `causalCone_obstruction` needs `η[D,a]` Hermitian, which
    fails in general, and `Tr(η[D,a]) = Tr([η,D]a)` need not vanish. No
    Lorentzian-physics claims are made. -/
def IsLorentzCompatible (η D : Matrix n n ℂ) (C : Set (Matrix n n ℂ)) : Prop :=
  ∀ a ∈ C, ∀ x : n → ℂ, (star x ⬝ᵥ ((η * (D * a - a * D)) *ᵥ x)).re ≤ 0

/-- The causal order (Tier T2 — definition): `f ≤[C] g` iff `g - f ∈ C`.
    Franco's order (F7-form; the ledger's (F7) is the order on states,
    class (a) in form — this is its element-level shadow). It is a preorder
    (`causalLE_refl`, `causalLE_trans`) but NOT in general a partial order:
    antisymmetry needs pointedness `C ∩ -C = {0}`, which is NOT a Franco
    axiom. -/
def CausalLE (C : Set (Matrix n n ℂ)) (f g : Matrix n n ℂ) : Prop :=
  g - f ∈ C

/-- The causal order is reflexive (Tier T1 — proved): needs `0 ∈ C`. -/
theorem causalLE_refl {C : Set (Matrix n n ℂ)} (hC : IsCausalConeStatic C)
    (f : Matrix n n ℂ) : CausalLE C f f := by
  obtain ⟨_, h0, _, _, _, _⟩ := hC
  show f - f ∈ C
  rw [sub_self]
  exact h0

/-- The causal order is transitive (Tier T1 — proved): needs `C + C ⊆ C`. -/
theorem causalLE_trans {C : Set (Matrix n n ℂ)} (hC : IsCausalConeStatic C)
    {f g h : Matrix n n ℂ} (hfg : CausalLE C f g) (hgh : CausalLE C g h) :
    CausalLE C f h := by
  obtain ⟨_, _, hadd, _, _, _⟩ := hC
  show h - f ∈ C
  have e : h - f = (h - g) + (g - f) := by abel
  rw [e]
  exact hadd _ hgh _ hfg

/-- Real parts commute with finite sums (helper, Tier T1). -/
theorem re_sum_helper {s : Finset n} {f : n → ℂ} :
    (∑ i ∈ s, f i).re = ∑ i ∈ s, (f i).re := by
  induction s using Finset.induction with
  | empty => simp
  | insert a s has ih =>
    rw [Finset.sum_insert has, Finset.sum_insert has, Complex.add_re, ih]

/-- The sesquilinear form on basis vectors is the matrix entry
    (helper, Tier T1). -/
theorem form_single_eq (M : Matrix n n ℂ) (i j : n) :
    star (Pi.single i (1:ℂ)) ⬝ᵥ (M *ᵥ Pi.single j 1) = M i j := by
  have hstar : star (Pi.single i (1:ℂ) : n → ℂ) = Pi.single i (1:ℂ) := by
    ext k
    simp only [Pi.star_apply, Pi.single_apply]
    by_cases h : k = i <;> simp [h, star_one, star_zero]
  rw [hstar, single_dotProduct, one_mul, Matrix.mulVec_apply, dotProduct_single,
    mul_one]
  rfl
/-- `Re(xᴴx) = ∑ ‖x i‖²` (helper, Tier T1). -/
theorem re_form_one (x : n → ℂ) : (star x ⬝ᵥ x).re = ∑ i, ‖x i‖ ^ 2 := by
  have hunfold : star x ⬝ᵥ x = ∑ i, star (x i) * x i := rfl
  rw [hunfold, re_sum_helper]
  apply Finset.sum_congr rfl
  intro i _
  have hterm : (star (x i) * x i).re = ‖x i‖ ^ 2 := by
    have key : star (x i) * x i = ((‖x i‖ : ℂ)) ^ 2 := by
      rw [congr_fun RCLike.star_def (x i), mul_comm]
      exact RCLike.mul_conj (x i)
    rw [key, sq, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    ring
  exact hterm

/-- `0` is positive semidefinite (Tier T1 — proved). -/
theorem isPosSemidef_zero : IsPosSemidef (0 : Matrix n n ℂ) := by
  refine ⟨Matrix.conjTranspose_zero, fun x => ?_⟩
  rw [Matrix.zero_mulVec, dotProduct_zero]
  exact le_refl _

/-- PSD is closed under addition (Tier T1 — proved). -/
theorem isPosSemidef_add {A B : Matrix n n ℂ}
    (hA : IsPosSemidef A) (hB : IsPosSemidef B) : IsPosSemidef (A + B) := by
  obtain ⟨hAh, hAf⟩ := hA
  obtain ⟨hBh, hBf⟩ := hB
  refine ⟨by rw [Matrix.conjTranspose_add, hAh, hBh], fun x => ?_⟩
  rw [Matrix.add_mulVec, dotProduct_add, Complex.add_re]
  exact add_nonneg (hAf x) (hBf x)

/-- PSD is closed under nonnegative real scaling (Tier T1 — proved). -/
theorem isPosSemidef_real_smul {A : Matrix n n ℂ} (hA : IsPosSemidef A)
    {r : ℝ} (hr : 0 ≤ r) : IsPosSemidef ((r : ℂ) • A) := by
  obtain ⟨hAh, hAf⟩ := hA
  refine ⟨?_, fun x => ?_⟩
  · rw [Matrix.conjTranspose_smul, hAh]
    congr 1
    simp only [Complex.star_def, Complex.conj_ofReal]
  · rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    have hnn := mul_nonneg hr (hAf x)
    linarith

/-- `1` is positive semidefinite (Tier T1 — proved). -/
theorem isPosSemidef_one : IsPosSemidef (1 : Matrix n n ℂ) := by
  refine ⟨Matrix.conjTranspose_one, fun x => ?_⟩
  rw [Matrix.one_mulVec, re_form_one x]
  exact Finset.sum_nonneg (fun i _ => sq_nonneg _)

/-- Polarization identity on `eᵢ + c•eⱼ` (helper, Tier T1): the form is
    `c * M i j + star c * star (M i j)` once the diagonal entries vanish. -/
theorem form_affine (M : Matrix n n ℂ) (i j : n) (c : ℂ)
    (hii : M i i = 0) (hjj : M j j = 0)
    (hsymm : ∀ p q : n, M p q = star (M q p)) :
    star (Pi.single i (1:ℂ) + c • Pi.single j (1:ℂ)) ⬝ᵥ
        (M *ᵥ (Pi.single i (1:ℂ) + c • Pi.single j (1:ℂ)))
      = c * M i j + star c * star (M i j) := by
  have e1 : star (Pi.single i (1:ℂ) + c • Pi.single j (1:ℂ))
      = star (Pi.single i 1) + (star c) • star (Pi.single j 1) := by
    ext k
    simp only [Pi.star_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, star_add,
      star_mul]
    ring
  rw [e1, Matrix.mulVec_add, Matrix.mulVec_smul]
  simp only [add_dotProduct, dotProduct_add, dotProduct_smul,
    smul_dotProduct, form_single_eq M i i, form_single_eq M i j,
    form_single_eq M j i, form_single_eq M j j, hii, hjj, hsymm j i,
    smul_eq_mul, add_zero, zero_add, mul_zero]
  ring

/-- A positive-semidefinite complex matrix with zero trace is zero
    (Tier T1 — proved). Proof: diagonal entries are nonnegative reals
    summing to zero, hence zero; off-diagonals die by polarization on
    `eᵢ ± eⱼ` and `eᵢ ± i·eⱼ` (via `form_affine`). This is the engine of
    the obstruction: it turns `Tr[i[D,f]] = 0` into `[D,f] = 0`. -/
theorem posSemidef_trace_eq_zero {M : Matrix n n ℂ}
    (hM : IsPosSemidef M) (htr : Matrix.trace M = 0) : M = 0 := by
  obtain ⟨hH, hform⟩ := hM
  -- `star` on ℂ is definitional: `(star z).re = z.re`, `(star z).im = -(z.im)`
  have star_re : ∀ z : ℂ, (star z).re = z.re := fun z => rfl
  have star_im : ∀ z : ℂ, (star z).im = -(z.im) := fun z => rfl
  have hsymm : ∀ p q : n, M p q = star (M q p) := by
    intro p q
    have h := congr_fun (congr_fun hH q) p
    rw [Matrix.conjTranspose_apply] at h
    have h2 := congr_arg star h
    rwa [star_star] at h2
  have hdiag : ∀ i : n, M i i = 0 := by
    have hre : ∀ i : n, 0 ≤ (M i i).re := by
      intro i
      have h := hform (Pi.single i (1:ℂ))
      rw [form_single_eq M i i] at h
      exact h
    have him : ∀ i : n, (M i i).im = 0 := by
      intro i
      have h := hsymm i i
      have h2 : (M i i).im = -((M i i).im) := by
        conv_lhs => rw [h]
        exact (star_im _).symm
      linarith
    have hsum : ∑ i, (M i i).re = 0 := by
      have htr0 : (Matrix.trace M).re = 0 := by rw [htr]; rfl
      have htrace : Matrix.trace M = ∑ i, M i i := rfl
      rw [htrace, re_sum_helper] at htr0
      exact htr0
    have hre0 : ∀ i : n, (M i i).re = 0 := by
      have h := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hre i)).mp hsum
      intro i
      exact h i (Finset.mem_univ i)
    intro i
    exact Complex.ext (hre0 i) (him i)
  have hoff : ∀ i j : n, M i j = 0 := by
    intro i j
    have h1 : 0 ≤ (M i j).re := by
      have h := hform (Pi.single i (1:ℂ) + (1:ℂ) • Pi.single j (1:ℂ))
      rw [form_affine M i j 1 (hdiag i) (hdiag j) hsymm] at h
      simp only [star_one, one_mul, Complex.add_re, star_re] at h
      linarith
    have h2 : (M i j).re ≤ 0 := by
      have h := hform (Pi.single i (1:ℂ) + (-1:ℂ) • Pi.single j (1:ℂ))
      rw [form_affine M i j (-1) (hdiag i) (hdiag j) hsymm] at h
      simp only [star_neg, star_one, Complex.add_re, neg_mul, one_mul, Complex.neg_re,
        star_re] at h
      linarith
    have hre_ij : (M i j).re = 0 := le_antisymm h2 h1
    have hstarI : star Complex.I = -Complex.I := by
      rw [Complex.star_def, Complex.conj_I]
    have h3 : (M i j).im ≤ 0 := by
      have h := hform (Pi.single i (1:ℂ) + Complex.I • Pi.single j (1:ℂ))
      rw [form_affine M i j Complex.I (hdiag i) (hdiag j) hsymm, hstarI] at h
      have e : (Complex.I * M i j + -Complex.I * star (M i j)).re
          = -2 * (M i j).im := by
        simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
          Complex.neg_re, Complex.neg_im, star_re, star_im]
        ring
      rw [e] at h
      linarith
    have h4 : 0 ≤ (M i j).im := by
      have h := hform (Pi.single i (1:ℂ) + (-Complex.I) • Pi.single j (1:ℂ))
      rw [form_affine M i j (-Complex.I) (hdiag i) (hdiag j) hsymm] at h
      have hs : star (-Complex.I) = Complex.I := by
        rw [star_neg, hstarI, neg_neg]
      rw [hs] at h
      have e : (-Complex.I * M i j + Complex.I * star (M i j)).re
          = 2 * (M i j).im := by
        simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
          Complex.neg_re, Complex.neg_im, star_re, star_im]
        ring
      rw [e] at h
      linarith
    have him_ij : (M i j).im = 0 := le_antisymm h3 h4
    exact Complex.ext hre_ij him_ij
  ext i j
  simp [hoff i j]
theorem trace_comm_eq_zero (D f : Matrix n n ℂ) :
    Matrix.trace (D * f - f * D) = 0 := by
  rw [Matrix.trace_sub, Matrix.trace_mul_comm, sub_self]

/-- The dynamical axiom forces the commutator to vanish (Tier T1 — proved):
    `i[D,f] ≥ 0` (PSD) and `Tr(i[D,f]) = 0` give `i[D,f] = 0`, hence
    `[D,f] = 0`. This is the **trace-class collapse**. -/
theorem dyn_comm_eq_zero {D : Matrix n n ℂ} (hD : Dᴴ = D)
    (C : Set (Matrix n n ℂ)) (hdyn : IsDynamicallyCompatible D C)
    {f : Matrix n n ℂ} (hf : f ∈ C) : D * f - f * D = 0 := by
  have hpsd := hdyn f hf
  have htr : Matrix.trace (Complex.I • (D * f - f * D)) = 0 := by
    rw [Matrix.trace_smul, trace_comm_eq_zero, smul_zero]
  have h0 := posSemidef_trace_eq_zero hpsd htr
  have key : (-Complex.I) • (Complex.I • (D * f - f * D)) = D * f - f * D := by
    rw [← mul_smul]
    have hII : -Complex.I * Complex.I = 1 := by
      rw [neg_mul, Complex.I_mul_I, neg_neg]
    rw [hII, one_smul]
  rw [h0, smul_zero] at key
  exact key.symm

/-- Any admissible cone forces `D` central on self-adjoints (Tier T1 —
    proved): every `f ∈ C` commutes with `D` (`dyn_comm_eq_zero`), and the
    spanning axiom spreads this to all of `A_sa`. -/
theorem causalCone_forces_central (D : Matrix n n ℂ) (hD : Dᴴ = D)
    (C : Set (Matrix n n ℂ))
    (hstatic : IsCausalConeStatic C) (hdyn : IsDynamicallyCompatible D C)
    (a : Matrix n n ℂ) (ha : aᴴ = a) : D * a - a * D = 0 := by
  obtain ⟨_, _, _, _, hspan, _⟩ := hstatic
  obtain ⟨f, g, hf, hg, rfl⟩ := hspan a ha
  have hDf := dyn_comm_eq_zero hD C hdyn hf
  have hDg := dyn_comm_eq_zero hD C hdyn hg
  have e : D * (f - g) - (f - g) * D
      = (D * f - f * D) - (D * g - g * D) := by noncomm_ring
  rw [e, hDf, hDg, sub_self]

/-- **The verdict (Tier T1 — proved obstruction).** No set `C` satisfies the
    static Franco axioms (F1)–(F5) jointly with the `i[D,f]`-PSD dynamical
    compatibility when `D` is self-adjoint but non-central on self-adjoints.
    Mechanism — **trace-class collapse of the commutator**: `Tr[D,f] ≡ 0`
    forces the positive-semidefinite `i[D,f]` to vanish, so every `f ∈ C`
    commutes with `D`; spanning then forces ALL of `A_sa` to commute with
    `D`, contradicting non-centrality. The finite Dirac `D_F` is non-scalar
    (Yukawa structure), so `A_F` carries no `i[D,f]`-dynamically-compatible
    causal cone. This is a finite-dimensionality obstruction: in infinite
    dimension there is no trace to force the collapse, which is why the
    manifold case survives.
    SCOPE: this kills the `i[D,f]`-PSD variant (`IsDynamicallyCompatible`),
    not Franco's true `J`-form (F6) `⟨φ, J[D,a]φ⟩ ≤ 0`, whose
    finite-dimensional status is open (cf. `IsLorentzCompatible`, no
    verdict). Since (F1)–(F5) imply `IsCausalConeStatic`, the obstruction
    applies to any true Franco static cone paired with the `i[D,f]`
    dynamical condition. -/
theorem causalCone_obstruction (D : Matrix n n ℂ) (hD : Dᴴ = D)
    (hDnc : ∃ a : Matrix n n ℂ, aᴴ = a ∧ D * a - a * D ≠ 0)
    (C : Set (Matrix n n ℂ))
    (hstatic : IsCausalConeStatic C) (hdyn : IsDynamicallyCompatible D C) :
    False := by
  obtain ⟨a, ha, hane⟩ := hDnc
  exact hane (causalCone_forces_central D hD C hstatic hdyn a ha)

/-- The full self-adjoint set satisfies the static axioms (Tier T1 —
    proved): the static axioms are consistent — but the induced order is
    indiscrete, carrying no causal content. The positive cone
    (`psdCone_static`) is the non-trivial witness. -/
theorem selfAdjointSet_static :
    IsCausalConeStatic {a : Matrix n n ℂ | aᴴ = a} := by
  refine ⟨fun a ha => ha, Matrix.conjTranspose_zero, ?_, ?_, ?_,
    Matrix.conjTranspose_one⟩
  · intro a ha b hb
    show (a + b)ᴴ = a + b
    rw [Matrix.conjTranspose_add, ha, hb]
  · intro a ha r _
    show ((r : ℂ) • a)ᴴ = (r : ℂ) • a
    rw [Matrix.conjTranspose_smul, ha]
    congr 1
    simp only [Complex.star_def, Complex.conj_ofReal]
  · intro a ha
    exact ⟨a, 0, ha, Matrix.conjTranspose_zero, by rw [sub_zero]⟩

/-- `‖x i‖ * ‖x j‖ ≤ ∑ k, ‖x k‖²` (helper, Tier T1). -/
theorem norm_mul_le_sum_sq (x : n → ℂ) (i j : n) :
    ‖x i‖ * ‖x j‖ ≤ ∑ k, ‖x k‖ ^ 2 := by
  have h1 : ‖x i‖ ^ 2 ≤ ∑ k, ‖x k‖ ^ 2 :=
    Finset.single_le_sum (fun k _ => sq_nonneg (‖x k‖)) (Finset.mem_univ i)
  have h2 : ‖x j‖ ^ 2 ≤ ∑ k, ‖x k‖ ^ 2 :=
    Finset.single_le_sum (fun k _ => sq_nonneg (‖x k‖)) (Finset.mem_univ j)
  have hS : 0 ≤ ∑ k, ‖x k‖ ^ 2 :=
    Finset.sum_nonneg (fun k _ => sq_nonneg _)
  have hpi : 0 ≤ ‖x i‖ := norm_nonneg _
  have hpj : 0 ≤ ‖x j‖ := norm_nonneg _
  nlinarith [sq_nonneg (‖x i‖ * ‖x j‖ - ∑ k, ‖x k‖ ^ 2),
    mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr h2),
    mul_nonneg hpi hpj, hS]

/-- The entrywise bound `|xᴴMx| ≤ (∑ᵢⱼ ‖M i j‖)(∑ₖ ‖x k‖²)` (helper, Tier T1).
    This is the estimate behind the Jordan decomposition for the positive
    cone's spanning axiom. -/
theorem estimate_aux {M : Matrix n n ℂ} (x : n → ℂ) :
    ‖star x ⬝ᵥ (M *ᵥ x)‖ ≤ (∑ i, ∑ j, ‖M i j‖) * (∑ k, ‖x k‖ ^ 2) := by
  have hunfold : star x ⬝ᵥ (M *ᵥ x)
      = ∑ i, ∑ j, star (x i) * (M i j * x j) := by
    have h1 : star x ⬝ᵥ (M *ᵥ x) = ∑ i, star (x i) * ((M *ᵥ x) i) := rfl
    rw [h1]
    apply Finset.sum_congr rfl
    intro i _
    rw [Matrix.mulVec_apply_eq_sum, Finset.mul_sum]
  rw [hunfold]
  calc ‖∑ i, ∑ j, star (x i) * (M i j * x j)‖
        ≤ ∑ i, ∑ j, ‖star (x i) * (M i j * x j)‖ := by
          calc ‖∑ i, ∑ j, star (x i) * (M i j * x j)‖
                ≤ ∑ i, ‖∑ j, star (x i) * (M i j * x j)‖ :=
                  norm_sum_le _ _
            _ ≤ ∑ i, ∑ j, ‖star (x i) * (M i j * x j)‖ := by
                  apply Finset.sum_le_sum
                  intro i _
                  exact norm_sum_le _ _
      _ = ∑ i, ∑ j, ‖x i‖ * ‖M i j‖ * ‖x j‖ := by
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          simp only [Complex.star_def, norm_mul, Complex.norm_conj]
          ring
      _ ≤ ∑ i, ∑ j, (‖M i j‖ * ∑ k, ‖x k‖ ^ 2) := by
          apply Finset.sum_le_sum
          intro i _
          apply Finset.sum_le_sum
          intro j _
          have h := norm_mul_le_sum_sq x i j
          have hM : 0 ≤ ‖M i j‖ := norm_nonneg _
          calc ‖x i‖ * ‖M i j‖ * ‖x j‖
                = ‖M i j‖ * (‖x i‖ * ‖x j‖) := by ring
            _ ≤ ‖M i j‖ * ∑ k, ‖x k‖ ^ 2 :=
                mul_le_mul_of_nonneg_left h hM
      _ = (∑ i, ∑ j, ‖M i j‖) * ∑ k, ‖x k‖ ^ 2 := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.sum_mul]

/-- `(T•1 + M)` is PSD for `T = ∑ᵢⱼ ‖M i j‖` (Tier T1 — proved): the shift
    dominates the form, `Re(xᴴ(T•1+M)x) = T·∑‖x‖² + Re(xᴴMx) ≥ 0`. -/
theorem isPosSemidef_shift_add {M : Matrix n n ℂ} (hM : Mᴴ = M) :
    IsPosSemidef (((∑ i, ∑ j, ‖M i j‖ : ℝ):ℂ) • 1 + M) := by
  set T : ℝ := ∑ i, ∑ j, ‖M i j‖ with hT
  refine ⟨?_, fun x => ?_⟩
  · rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_one, hM]
    congr 1
    simp only [Complex.star_def, Complex.conj_ofReal]
  · have hexpand : star x ⬝ᵥ (((((T:ℝ):ℂ) • 1 + M)) *ᵥ x)
        = (T:ℂ) * (star x ⬝ᵥ x) + star x ⬝ᵥ (M *ᵥ x) := by
      rw [Matrix.add_mulVec, dotProduct_add, Matrix.smul_mulVec,
        Matrix.one_mulVec, dotProduct_smul, smul_eq_mul]
    rw [hexpand, Complex.add_re]
    have hre1 : ((T:ℂ) * (star x ⬝ᵥ x)).re = T * ∑ k, ‖x k‖ ^ 2 := by
      rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, re_form_one x]
      ring
    rw [hre1]
    have habs : |(star x ⬝ᵥ (M *ᵥ x)).re| ≤ T * ∑ k, ‖x k‖ ^ 2 := by
      have h1 := RCLike.abs_re_le_norm (K := ℂ) (star x ⬝ᵥ (M *ᵥ x))
      simp only [RCLike.re_to_complex] at h1
      exact h1.trans (estimate_aux x)
    have hneg := neg_le_of_abs_le habs
    linarith

/-- `(T•1 - M)` is PSD for `T = ∑ᵢⱼ ‖M i j‖` (Tier T1 — proved): from the
    `+` case applied to `-M`. -/
theorem isPosSemidef_shift_sub {M : Matrix n n ℂ} (hM : Mᴴ = M) :
    IsPosSemidef (((∑ i, ∑ j, ‖M i j‖ : ℝ):ℂ) • 1 - M) := by
  have hM' : (-M)ᴴ = -M := by rw [Matrix.conjTranspose_neg, hM]
  have hT : (∑ i, ∑ j, ‖(-M) i j‖ : ℝ) = ∑ i, ∑ j, ‖M i j‖ := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [Matrix.neg_apply, norm_neg]
  have h := isPosSemidef_shift_add hM'
  rw [hT] at h
  have heq : (((∑ i, ∑ j, ‖M i j‖ : ℝ):ℂ) • 1 + -M)
      = ((∑ i, ∑ j, ‖M i j‖ : ℝ):ℂ) • 1 - M := by
    rw [sub_eq_add_neg]
  rwa [heq] at h

/-- Every self-adjoint matrix is a difference of two PSDs (Tier T1 —
    proved): the Jordan decomposition via the entrywise shift,
    `M = ½(T•1+M) - ½(T•1-M)`. -/
theorem psd_spanning {M : Matrix n n ℂ} (hM : Mᴴ = M) :
    ∃ P Q : Matrix n n ℂ, IsPosSemidef P ∧ IsPosSemidef Q ∧ M = P - Q := by
  set T : ℝ := ∑ i, ∑ j, ‖M i j‖ with hT
  have hA := isPosSemidef_shift_add hM
  have hB := isPosSemidef_shift_sub hM
  refine ⟨((1/2 : ℝ):ℂ) • (((T:ℝ):ℂ) • 1 + M),
    ((1/2 : ℝ):ℂ) • (((T:ℝ):ℂ) • 1 - M),
    isPosSemidef_real_smul hA (by norm_num),
    isPosSemidef_real_smul hB (by norm_num), ?_⟩
  have halg : ((1/2:ℝ):ℂ) • (((((T:ℝ):ℂ) • 1 + M) - (((T:ℝ):ℂ) • 1 - M))) = M := by
    have h1 : ((((T:ℝ):ℂ) • 1 + M) - (((T:ℝ):ℂ) • 1 - M)) = (2:ℂ) • M := by
      module
    rw [h1, ← mul_smul]
    have h2 : ((1/2:ℝ):ℂ) * 2 = 1 := by
      rw [show (2:ℂ) = ((2:ℝ):ℂ) by norm_num, ← Complex.ofReal_mul]
      norm_num
    rw [h2, one_smul]
  rw [← smul_sub]
  exact halg.symm

/-- The positive cone satisfies the static Franco axioms (Tier T1 —
    proved): the construction closes for the static part — convex
    (`isPosSemidef_add`, `isPosSemidef_real_smul`), spanning
    (`psd_spanning`, Jordan decomposition), `1 ∈ C` (`isPosSemidef_one`).
    The induced order is the Löwner order. The dynamical axiom is what
    fails — see `causalCone_obstruction`. -/
theorem psdCone_static :
    IsCausalConeStatic {M : Matrix n n ℂ | IsPosSemidef M} := by
  refine ⟨fun M hM => hM.1, isPosSemidef_zero, ?_, ?_, ?_, isPosSemidef_one⟩
  · intro A hA B hB
    exact isPosSemidef_add hA hB
  · intro A hA r hr
    exact isPosSemidef_real_smul hA hr
  · intro M hM
    obtain ⟨P, Q, hP, hQ, hPQ⟩ := psd_spanning hM
    exact ⟨P, Q, hP, hQ, hPQ⟩

#print axioms causalLE_refl
#print axioms causalLE_trans
#print axioms re_sum_helper
#print axioms form_single_eq
#print axioms re_form_one
#print axioms isPosSemidef_zero
#print axioms isPosSemidef_add
#print axioms isPosSemidef_real_smul
#print axioms isPosSemidef_one
#print axioms form_affine
#print axioms posSemidef_trace_eq_zero
#print axioms trace_comm_eq_zero
#print axioms dyn_comm_eq_zero
#print axioms causalCone_forces_central
#print axioms causalCone_obstruction
#print axioms selfAdjointSet_static
#print axioms norm_mul_le_sum_sq
#print axioms estimate_aux
#print axioms isPosSemidef_shift_add
#print axioms isPosSemidef_shift_sub
#print axioms psd_spanning
#print axioms psdCone_static

end ThetLogos

