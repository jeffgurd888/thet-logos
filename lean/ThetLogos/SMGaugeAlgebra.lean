import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Algebra.Star.Unitary
import Mathlib.Tactic
import ThetLogos.FiniteSpectralTriple

/-!
# ThetLogos.SMGaugeAlgebra — the finite gauge algebra (SM-Match Track 1)

**Directive:** Jeff, 2026-10-11 ("build it to match"): formalize the SM gauge
group from the finite algebra, honestly.

## Tier honesty

- **T1 (proved, zero sorrys):**
  - §1: `U(AF) = U(1) × SU(2) × U(3)` — `U(ℂ) = U(1)` by definition,
    `U(ℍ) = SU(2)` via the quaternion embedding (`quat_mem_specialUnitary_iff`),
    `U(M₃(ℂ)) = U(3)` by definition.
  - §2: the unimodularity (determinant-one) condition and the reduction to
    the subgroup `U(1) × SU(2) × SU(3)` (`SMUnimodular_mem_iff`).
  - §3: the 6-dim caveat precisely located — `ker π` is EXACTLY the pure-color
    elements (`pi_ker_iff`); `π` is faithful on the `U(1)` summand
    (`pi_u1_injective`), on the quaternion/`SU(2)` summand
    (`pi_quat_injective`), and on the color factor locked to electroweak
    (`pi_color_locked_injective`); the represented `U(1)` acts trivially on
    left-handed fermions (`pi_u1_eL_trivial`).
- **T2 (cited, not proved):** the standard SM hypercharge assignments
  (textbook NCG result; cf. `ThetLogos.SMFermions.hypercharge`, Track 2).
- **T5 (priced, not papered):** §4 — what the represented picture would need
  in order to see color.

## Verdict

**PARTIAL.** Algebraic side: MATCH — `U(AF)` and the unimodular reduction are
T1. Represented side: precisely located T1 (`ker π` = pure color; `π`
injective on unitaries) — but the SM hypercharge `U(1)`, which is nonzero on
left-handed fermions (`Y(e_L) = -1`), is NOT the represented `U(1)` (which
acts only on `H_R`). The represented picture therefore does not yield the SM
gauge couplings; see the priced gap in §4.

`satisfiesDestruction` untouched. Existing files unmodified. Local only.
-/

open Matrix

namespace ThetLogos

/-! ## §1. The unitary group of `AF = ℂ ⊕ ℍ ⊕ M₃(ℂ)` (T1) -/

/-- `U(1)`: the unitary group of `ℂ` (the circle group). T1. -/
abbrev U1 := unitary ℂ

/-- Membership in `U(ℂ)`. T1. -/
theorem mem_U1_iff {u : ℂ} : u ∈ U1 ↔ star u * u = 1 ∧ u * star u = 1 :=
  Iff.rfl

/-- The quaternion condition inside `M₂(ℂ)`:
    `q = [[α, β], [-β̄, ᾱ]]`. T1 (definition). -/
def IsQuat (q : Matrix (Fin 2) (Fin 2) ℂ) : Prop :=
  ∃ α β : ℂ, q = !![α, β; -star β, star α]

/-- `U(ℍ) = SU(2)`: a `2×2` complex matrix is special-unitary iff it is
    unitary and quaternion-form. T1.

    Forward: for `q ∈ SU(2)`, `q⁻¹ = qᴴ` (unitary) and `q⁻¹ = adj(q)` (det 1),
    so `qᴴ = adj(q)`; comparing entries against
    `adj [[a,b],[c,d]] = [[d,-b],[-c,a]]` gives `d = ā`, `c = -β̄`.
    Backward: for quaternion-form unitary `q`, `det q = |α|² + |β|²`,
    which equals `1` by the `(0,0)` entry of `qᴴq = 1`. -/
theorem quat_mem_specialUnitary_iff {q : Matrix (Fin 2) (Fin 2) ℂ} :
    q ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ ↔
      q ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧ IsQuat q := by
  rw [Matrix.mem_specialUnitaryGroup_iff]
  constructor
  · rintro ⟨hU, hdet⟩
    refine ⟨hU, ?_⟩
    have hUU : q * star q = 1 := Matrix.mem_unitaryGroup_iff.mp hU
    have hadjR : q * q.adjugate = 1 := by
      rw [Matrix.mul_adjugate, hdet, one_smul]
    have hadjL : q.adjugate * q = 1 := by
      rw [Matrix.adjugate_mul, hdet, one_smul]
    have hstar_adj : star q = q.adjugate := by
      calc star q = 1 * star q := (one_mul _).symm
        _ = (q.adjugate * q) * star q := by rw [hadjL]
        _ = q.adjugate * (q * star q) := by rw [Matrix.mul_assoc]
        _ = q.adjugate * 1 := by rw [hUU]
        _ = q.adjugate := mul_one _
    have hqmat : q = !![q 0 0, q 0 1; q 1 0, q 1 1] := by
      ext i j
      fin_cases i <;> fin_cases j <;> rfl
    have e10 : q 1 0 = -star (q 0 1) := by
      have h10 := congrFun (congrFun hstar_adj 1) 0
      rw [Matrix.star_apply] at h10
      have hadj10 : q.adjugate 1 0 = -(q 1 0) := by
        conv_lhs => rw [hqmat, Matrix.adjugate_fin_two_of]
        simp
      rw [hadj10] at h10
      calc q 1 0 = -(-(q 1 0)) := (neg_neg _).symm
        _ = -star (q 0 1) := by rw [← h10]
    have e11 : q 1 1 = star (q 0 0) := by
      have h11 := congrFun (congrFun hstar_adj 1) 1
      rw [Matrix.star_apply] at h11
      have hadj11 : q.adjugate 1 1 = q 0 0 := by
        conv_lhs => rw [hqmat, Matrix.adjugate_fin_two_of]
        simp
      rw [hadj11] at h11
      have h11s := congrArg star h11
      simpa using h11s
    refine ⟨q 0 0, q 0 1, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j
    · rfl
    · rfl
    · simpa using e10
    · simpa using e11
  · rintro ⟨hU, hQ⟩
    obtain ⟨α, β, rfl⟩ := hQ
    refine ⟨?_, ?_⟩
    · exact hU
    · have hUU : (!![α, β; -star β, star α] : Matrix (Fin 2) (Fin 2) ℂ) *
          star !![α, β; -star β, star α] = 1 :=
        Matrix.mem_unitaryGroup_iff.mp hU
      have h00 := congrFun (congrFun hUU 0) 0
      rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply, Matrix.star_apply] at h00
      have e00 : (!![α, β; -star β, star α] : Matrix (Fin 2) (Fin 2) ℂ) 0 0 = α := by simp
      have e01 : (!![α, β; -star β, star α] : Matrix (Fin 2) (Fin 2) ℂ) 0 1 = β := by simp
      rw [e00, e01] at h00
      simp only [Matrix.one_apply_eq] at h00
      -- h00 : α * star α + β * star β = 1
      rw [Matrix.det_fin_two, e00, e01]
      have e10 : (!![α, β; -star β, star α] : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = -star β := by simp
      have e11 : (!![α, β; -star β, star α] : Matrix (Fin 2) (Fin 2) ℂ) 1 1 = star α := by simp
      rw [e10, e11]
      have hβ : β * -star β = -(β * star β) := by ring
      rw [hβ, sub_neg_eq_add]
      exact h00

/-- `SU(2)`: `2×2` special unitary matrices. T1. -/
abbrev SU2 := Matrix.specialUnitaryGroup (Fin 2) ℂ

/-- `U(3)`: `3×3` unitary matrices `= U(M₃(ℂ))`. T1. -/
abbrev U3 := Matrix.unitaryGroup (Fin 3) ℂ

/-- `SU(3)`: `3×3` special unitary matrices. T1. -/
abbrev SU3 := Matrix.specialUnitaryGroup (Fin 3) ℂ

/-- `U(AF) = U(1) × SU(2) × U(3)`: the unitary group of the finite algebra
    `AF = ℂ ⊕ ℍ ⊕ M₃(ℂ)`. T1.

    Unitaries of a direct sum are exactly the componentwise unitaries;
    `U(ℍ) = SU(2)` is `quat_mem_specialUnitary_iff` above. -/
abbrev SMUnitaryGroup := U1 × SU2 × U3

/-! ## §2. Unimodularity: `U(1)×SU(2)×U(3) → SU(3)×SU(2)×U(1)` -/

/-- The unimodularity (determinant-one) condition on the color factor.
    Standard NCG: the "unimodularity (determinant equals one) condition takes
    care of the extra `U(1)`" (Lizzi 2018 review, §3.1). T1 (definition). -/
def IsUnimodular (u : SMUnitaryGroup) : Prop :=
  Matrix.det (u.2.2 : Matrix (Fin 3) (Fin 3) ℂ) = 1

/-- The unimodular subgroup of `U(AF)`. T1. -/
def SMUnimodular : Subgroup SMUnitaryGroup where
  carrier := { u | IsUnimodular u }
  one_mem' := by
    simp only [IsUnimodular, Set.mem_ofPred_eq]
    simp
  mul_mem' := by
    intro a b ha hb
    simp only [IsUnimodular, Set.mem_ofPred_eq] at ha hb ⊢
    have h_eq : (a * b).2.2 = a.2.2 * b.2.2 := rfl
    have h1 : ((a * b).2.2 : Matrix (Fin 3) (Fin 3) ℂ)
        = (a.2.2 : Matrix (Fin 3) (Fin 3) ℂ) * (b.2.2 : Matrix (Fin 3) (Fin 3) ℂ) := by
      rw [h_eq]
      rfl
    rw [h1, Matrix.det_mul, ha, hb, mul_one]
  inv_mem' := by
    intro a ha
    simp only [IsUnimodular, Set.mem_ofPred_eq] at ha ⊢
    have h_eq : (a⁻¹).2.2 = (a.2.2)⁻¹ := rfl
    have h3 : a.2.2 * (a⁻¹).2.2 = 1 := by
      rw [h_eq]
      exact mul_inv_cancel _
    have h2 : (a.2.2 : Matrix (Fin 3) (Fin 3) ℂ) *
        ((a⁻¹).2.2 : Matrix (Fin 3) (Fin 3) ℂ) = 1 := by
      have h4 : ((a.2.2 * (a⁻¹).2.2 : ↥U3) : Matrix (Fin 3) (Fin 3) ℂ)
          = ((1 : ↥U3) : Matrix (Fin 3) (Fin 3) ℂ) := by rw [h3]
      exact h4
    have h5 := congrArg Matrix.det h2
    rw [Matrix.det_mul, Matrix.det_one] at h5
    rw [ha, one_mul] at h5
    exact h5

/-- T1: the unimodular subgroup **is** `U(1) × SU(2) × SU(3)`.
    This is the group-theoretic content of the standard NCG reduction
    `U(1)×SU(2)×U(3) → SU(3)×SU(2)×U(1)`: unimodularity cuts the color factor
    `U(3)` down to `SU(3)$, leaving the `U(1)` and `SU(2)` factors untouched. -/
theorem SMUnimodular_mem_iff (u : SMUnitaryGroup) :
    u ∈ SMUnimodular ↔
      ∃ (a : U1) (b : SU2) (c : SU3),
        u = (a, b, ⟨(c : Matrix (Fin 3) (Fin 3) ℂ),
          (Matrix.mem_specialUnitaryGroup_iff.mp c.2).1⟩) := by
  constructor
  · intro h
    simp only [SMUnimodular, IsUnimodular] at h
    refine ⟨u.1, u.2.1, ⟨(u.2.2 : Matrix (Fin 3) (Fin 3) ℂ), ?_⟩, ?_⟩
    · rw [Matrix.mem_specialUnitaryGroup_iff]
      exact ⟨u.2.2.2, h⟩
    · apply Prod.ext
      · rfl
      · apply Prod.ext
        · rfl
        · exact Subtype.ext rfl
  · rintro ⟨a, b, c, rfl⟩
    simp only [SMUnimodular, IsUnimodular]
    exact (Matrix.mem_specialUnitaryGroup_iff.mp c.2).2

/-! ## §2b. Hypercharge assignments (T2, cited)

The standard SM hypercharge assignments — the textbook NCG result
(Chamseddine–Connes–Marcolli; see e.g. Lizzi 2018 review §3.1, Table 1):

| fermion | `u_R` | `d_R` | `Q_L=(u_L,d_L)` | `e_R` | `L_L=(ν_L,e_L)` | `ν_R` |
|---------|-------|-------|----------------|-------|----------------|-------|
| Y       | 4/3   | -2/3  | 1/3            | -2    | -1             | 0     |

**T2 — cited, not proved.** These values are INPUT here (they coincide with
`ThetLogos.SMFermions.hypercharge`, Track 2, also T2). They are not derived
from the representation in this file. In particular, note `Y(e_L) = -1 ≠ 0`:
SM hypercharge is nonzero on left-handed fermions — compare `pi_u1_eL_trivial`
(§3), which shows the represented `U(1)` acts trivially on `H_L`.
-/

/-! ## §3. The 6-dim caveat, precisely located (T1)

The Option-A representation `π` kills the `M₃(ℂ)` summand
(`pi_pure_color_zero`): a pure-color algebra element acts trivially. Here we
pin down exactly what survives and what dies. -/

/-- The `(8,8)` entry of `π` is the `U(1)` parameter (`ν_R` slot). T1. -/
theorem pi_entry_u1 (a : AF) : pi a ⟨8, by omega⟩ ⟨8, by omega⟩ = a.u1 := by
  have h16 : (8:ℕ) < 16 ∧ (8:ℕ) < 16 := by omega
  have hR : (8:ℕ) ≤ 8 ∧ (8:ℕ) < 16 ∧ (8:ℕ) ≤ 8 ∧ (8:ℕ) < 16 := by omega
  have h1 : (8:ℕ) = 8 ∧ (8:ℕ) = 8 := by omega
  have hnL : ¬ ((8:ℕ) < 8 ∧ (8:ℕ) < 8) := by omega
  unfold pi embedSM
  dsimp only
  simp only [h16, hR, hnL, true_and, dite_true, dite_false]

/-- The lepton-doublet block of `π` is the quaternion parameter. T1. -/
theorem pi_entry_quat (a : AF) (i j : Fin 2) :
    pi a ⟨i.val, by omega⟩ ⟨j.val, by omega⟩ = a.q i j := by
  have h1 : (i.val : ℕ) < 16 ∧ (j.val : ℕ) < 16 := by omega
  have h2 : (i.val : ℕ) < 8 ∧ (j.val : ℕ) < 8 := by omega
  have h3 : (i.val : ℕ) < 2 ∧ (j.val : ℕ) < 2 := ⟨i.isLt, j.isLt⟩
  unfold pi embedSM
  dsimp only
  simp only [h1, h2, h3, true_and, dite_true]

/-- **Kernel of `π`: exactly the pure-color elements.** T1.

    Forward: the `(8,8)` entry gives `a.u1 = 0` and the lepton block gives
    `a.q = 0`. Backward: with `u1 = q = 0` every branch of `embedSM` vanishes
    (the quark blocks need `q` or `u1` as a factor). This extends
    `pi_pure_color_zero` to the full kernel characterization. -/
theorem pi_ker_iff (a : AF) : pi a = 0 ↔ a.u1 = 0 ∧ a.q = 0 := by
  constructor
  · intro h
    have h88 := congrFun (congrFun h ⟨8, by omega⟩) ⟨8, by omega⟩
    rw [pi_entry_u1] at h88
    simp only [Matrix.zero_apply] at h88
    have hq : a.q = 0 := by
      ext i j
      have hentry := congrFun (congrFun h ⟨i.val, by omega⟩) ⟨j.val, by omega⟩
      rw [pi_entry_quat] at hentry
      simpa using hentry
    exact ⟨h88, hq⟩
  · rintro ⟨hu1, hq⟩
    ext i j
    unfold pi
    split_ifs with h16
    · unfold embedSM
      dsimp only
      split_ifs <;> simp_all
    · rfl

/-- The `U(1)` summand survives `π` faithfully. T1. -/
theorem pi_u1_injective : Function.Injective (fun lam : ℂ => pi ⟨lam, 1, 1⟩) := by
  intro lam1 lam2 h
  change pi ⟨lam1, 1, 1⟩ = pi ⟨lam2, 1, 1⟩ at h
  have h8 := congrFun (congrFun h ⟨8, by omega⟩) ⟨8, by omega⟩
  rw [pi_entry_u1, pi_entry_u1] at h8
  exact h8

/-- The quaternion/`SU(2)` summand survives `π` faithfully. T1. -/
theorem pi_quat_injective :
    Function.Injective (fun q : Matrix (Fin 2) (Fin 2) ℂ => pi ⟨1, q, 1⟩) := by
  intro q1 q2 h
  change pi ⟨1, q1, 1⟩ = pi ⟨1, q2, 1⟩ at h
  ext i j
  have hentry := congrFun (congrFun h ⟨i.val, by omega⟩) ⟨j.val, by omega⟩
  rw [pi_entry_quat, pi_entry_quat] at hentry
  exact hentry

/-- Quark-block entry: for `iv = 2+2k`, `jv = 2+2l` the entry is
    `q[0,0]·color[k,l]`. T1 (helper). -/
theorem pi_entry_quarkL (a : AF) (k l : Fin 3) :
    pi a ⟨2 + 2*k.val, by omega⟩ ⟨2 + 2*l.val, by omega⟩
      = a.q ⟨0, by omega⟩ ⟨0, by omega⟩ * a.color k l := by
  have h16 : (2 + 2*k.val) < 16 ∧ (2 + 2*l.val) < 16 := by omega
  have hL : (2 + 2*k.val) < 8 ∧ (2 + 2*l.val) < 8 := by omega
  have hnl : ¬ ((2 + 2*k.val) < 2 ∧ (2 + 2*l.val) < 2) := by omega
  have hq : (2:ℕ) ≤ 2 + 2*k.val ∧ (2:ℕ) ≤ 2 + 2*l.val := by omega
  have hmod1 : (2 + 2*k.val - 2) % 2 = 0 := by omega
  have hmod2 : (2 + 2*l.val - 2) % 2 = 0 := by omega
  have hdiv1 : (2 + 2*k.val - 2) / 2 = k.val := by omega
  have hdiv2 : (2 + 2*l.val - 2) / 2 = l.val := by omega
  unfold pi embedSM
  dsimp only
  simp only [h16, hL, hnl, hq, true_and, dite_true, dite_false,
    hmod1, hmod2, hdiv1, hdiv2]

/-- Color locked to electroweak survives: `m ↦ π⟨1,1,m⟩` is injective.
    T1. The `M₃` factor is not lost as a *parameter* — it acts on quarks via
    `q⊗m` / `λm` — but it has no *independent* action (`pi_pure_color_zero`). -/
theorem pi_color_locked_injective :
    Function.Injective (fun m : Matrix (Fin 3) (Fin 3) ℂ => pi ⟨1, 1, m⟩) := by
  intro m1 m2 h
  change pi ⟨1, 1, m1⟩ = pi ⟨1, 1, m2⟩ at h
  ext k l
  have hentry := congrFun (congrFun h ⟨2 + 2*k.val, by omega⟩) ⟨2 + 2*l.val, by omega⟩
  rw [pi_entry_quarkL, pi_entry_quarkL] at hentry
  simpa using hentry

/-- The represented `U(1)` acts trivially on `H_L` (`e_L` slot is the identity,
    independent of `λ`). T1.

    Consequence: the represented `U(1)` cannot be SM hypercharge, since
    `Y(e_L) = -1 ≠ 0` (T2). The `U(1)` charges only right-handed fermions
    (`ν_R ↦ λ`, `e_R ↦ λ̄`); `SU(2)` charges only left-handed ones. -/
theorem pi_u1_eL_trivial (lam : ℂ) :
    pi ⟨lam, 1, 1⟩ ⟨1, by omega⟩ ⟨1, by omega⟩ = 1 := by
  have h16 : (1:ℕ) < 16 ∧ (1:ℕ) < 16 := by omega
  have hL : (1:ℕ) < 8 ∧ (1:ℕ) < 8 := by omega
  have hl : (1:ℕ) < 2 ∧ (1:ℕ) < 2 := by omega
  unfold pi embedSM
  dsimp only
  simp only [h16, hL, hl, true_and, dite_true, Matrix.one_apply_eq]

/-! ## §4. Priced gap (T5, not papered)

**What would be needed for the represented picture to see color.**

`pi_ker_iff` (§3) shows the obstruction is exact: `ker π` is the pure-color
summand, so pure-color gauge parameters — and hence pure-color inner
fluctuations `∑ a[D, b]` with `a, b` in the `M₃(ℂ)` summand — act as zero.
Color survives only *locked* to electroweak (`q⊗m`, `λm`;
`pi_color_locked_injective`): there is no independent represented `SU(3)`
gauge action on quarks.

To close the gap, one would need a representation in which the `M₃(ℂ)`
summand acts independently — e.g. the pre-Option-A representation (whatever
fixed the color action before Option A pinned it to the quark blocks), or a
representation where color enters through the manifold factor of the
almost-commutative product. Within Option A as formalized, the gap does not
close: `ker π` is provably the pure-color subspace, so no redefinition can
recover an independent color action without changing `π` itself.

Related ledger entries: the represented finite gauge algebra is 6-dimensional
real for the Martinetti `smGen` (`ThetLogos.InnerFluctuations`, T4 numerical);
the full `SU(3)×SU(2)×U(1)` symmetry claim needs the manifold factor
(`ThetLogos.UltimateReduction`, `ThetLogos.ProductTriple`).
-/

end ThetLogos
