import Mathlib.Tactic
import ThetLogos.ClassicalYangMills

open Matrix

namespace ThetLogos

/-!
# ThetLogos.SMLagrangian — SM-Match Track 3: Lagrangian sectors (classical level)

Tier header.
- **Scope:** the CLASSICAL Standard-Model Lagrangian's algebraic STRUCTURE —
  the same shape as the SM: three gauge kinetic terms, the fermion
  kinetic + gauge-coupling bilinear via the fluctuated Dirac, the Higgs
  potential, and the Yukawa shape. Coefficients and values stay INPUTS.
  The QUANTUM Lagrangian (path integral, renormalization, anomalies) is
  priced T5 and untouched here.
- **T1 (proved, zero sorrys):** per-factor gauge invariance of the kinetic
  term (extending `ymAction_gauge_invariant`); nonnegativity of
  `ymAction` and the correct (nonpositive-real) sign of each kinetic
  term; the fermion bilinear's free/coupling split
  (`fermionTerm_split`) and its simultaneous-unitary covariance
  (`diracPairing_gauge_invariant`); the Higgs potential's radial
  reduction with the broken-phase circle of minima and the symmetric-phase
  minimum at the origin (pure algebra, no analysis); Yukawa linearity in
  the input matrix and the VEV-reduction to a fermion bilinear.
- **T2 (definitions / structured targets):** `factorKinetic`,
  `smGaugeKinetic`, `diracPairing`, `fermionTerm`, `higgsNormSq`,
  `higgsPotential`, `yukawaTerm`, `yukawaMassMatrix`, `smLagrangian`.
  Gauge couplings `g_s, g, g'`, the Higgs parameters `μ², λ`, and the
  Yukawa matrix `Y` are T2 INPUTS — measured numbers, never derived.
- **T5 (readings, not proved):** the labels "SU(3)", "SU(2)", "U(1)" on the
  three factors; the "Higgs doublet" and "Yukawa coupling" readings.
- **Priced windows (not claimed — see §6):** quantum Lagrangian, continuum
  integral `∫_M`, junk-ideal quotient, any mass/coupling VALUES, the
  inhomogeneous `u[D,u*]` gauge piece, continuum spinors/`i∂̸`.
- **6-dim caveat (carried):** the represented finite gauge algebra is
  6-dimensional real — Option-A kills the `M₃(ℂ)` summand in the
  representation (`InnerFluctuations` header). The three-factor kinetic
  structure below is the SM TARGET SHAPE; which factors the represented
  algebra actually carries is governed by that caveat, not redefined here.
- **Untouched:** `satisfiesDestruction` — Jeff's Yukawa modeling decision is
  open and is not referenced or modified anywhere in this file.

## Fit-test mapping (SM Lagrangian → formalized objects)

- `-¼F²` per gauge factor ↔ `factorKinetic g F` (T2), summing to
  `smGaugeKinetic` (T2); T1 gauge invariance per factor and jointly.
- `ψ̄(i∂̸ + gA̸)ψ` ↔ `fermionTerm D_F A ψ = diracPairing (fluctuatedDirac D_F A) ψ`
  (T2 shape); the finite `D_F` stands in for `i∂̸` (continuum priced), the
  `A + JAJ⁻¹` fluctuation pieces are the gauge couplings (T1 split).
- `V(H) = -μ²|H|² + λ|H|⁴` ↔ `higgsPotential` (T2); T1 minima structure.
- `ψ̄_L Y H ψ_R` ↔ `yukawaTerm` (T2 shape only); T1 linearity + VEV reduction.
  NO values, NO mass predictions.
-/

/-! ## §1. Gauge kinetic sector: the -¼Tr(F²) shape per factor -/

/-- The `-¼Tr(F²)`-shape kinetic term for ONE gauge factor (T2 — structured
    target). `g` is a T2 INPUT (a measured coupling, never derived here);
    `ymAction` is the finite represented shadow of `∫Tr(F∧⋆F)`
    (`ClassicalYangMills`). The labels SU(3)/SU(2)/U(1) on the three
    factors are T5 readings; the 6-dim caveat applies. -/
noncomputable def factorKinetic (g : ℝ) (F : Matrix I32 I32 ℂ) : ℂ :=
  -(1 / 4 : ℂ) * ((g ^ 2 : ℝ) : ℂ) * ymAction F

/-- Gauge invariance per factor (T1): extends `ymAction_gauge_invariant`. -/
theorem factorKinetic_gauge_invariant (g : ℝ) (u F : Matrix I32 I32 ℂ)
    (hu : IsUnitaryMat u) :
    factorKinetic g (gaugeAct u F) = factorKinetic g F := by
  unfold factorKinetic
  rw [ymAction_gauge_invariant _ _ hu]

/-- `ymAction` is a nonnegative real (T1): `Tr(F†F) = ∑ᵢⱼ‖Fⱼᵢ‖²`.
    This is the algebraic reason the `-¼` kinetic term has the physical sign. -/
theorem ymAction_nonneg (F : Matrix I32 I32 ℂ) :
    ∃ r : ℝ, 0 ≤ r ∧ ymAction F = (r : ℂ) := by
  refine ⟨∑ i : I32, ∑ j : I32, ‖F j i‖ ^ 2,
    Finset.sum_nonneg fun i _ =>
      Finset.sum_nonneg fun j _ => by positivity, ?_⟩
  have hexpand : Matrix.trace (F.conjTranspose * F)
      = ∑ i : I32, ∑ j : I32, star (F j i) * F j i := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply]
  unfold ymAction
  rw [hexpand]
  push_cast
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [show star (F j i) = starRingEnd ℂ (F j i) from rfl, Complex.conj_mul']

/-- Each kinetic term is a nonpositive real (T1): the `-¼g²·Tr(F†F)` shape
    carries the correct sign for every input coupling `g`. -/
theorem factorKinetic_nonpos_real (g : ℝ) (F : Matrix I32 I32 ℂ) :
    ∃ r : ℝ, r ≤ 0 ∧ factorKinetic g F = (r : ℂ) := by
  obtain ⟨s, hs, hF⟩ := ymAction_nonneg F
  refine ⟨-(g ^ 2 / 4) * s, ?_, ?_⟩
  · have hg2 : 0 ≤ g ^ 2 / 4 := by positivity
    nlinarith [mul_nonneg hg2 hs]
  · unfold factorKinetic
    rw [hF]
    push_cast
    ring

/-- The three-factor gauge kinetic term (T2 — structured target):
    `-¼g_s²Tr(F₃²) - ¼g²Tr(F₂²) - ¼g′²Tr(F₁²)`, the SM gauge-kinetic shape.
    Couplings are T2 inputs; the factor labels are T5 readings. -/
noncomputable def smGaugeKinetic (gs g gp : ℝ) (F3 F2 F1 : Matrix I32 I32 ℂ) : ℂ :=
  factorKinetic gs F3 + factorKinetic g F2 + factorKinetic gp F1

/-- Joint gauge invariance (T1): independent unitary rotations of the three
    factors leave the kinetic sum invariant. -/
theorem smGaugeKinetic_gauge_invariant (gs g gp : ℝ)
    (u3 u2 u1 : Matrix I32 I32 ℂ) (F3 F2 F1 : Matrix I32 I32 ℂ)
    (h3 : IsUnitaryMat u3) (h2 : IsUnitaryMat u2) (h1 : IsUnitaryMat u1) :
    smGaugeKinetic gs g gp (gaugeAct u3 F3) (gaugeAct u2 F2) (gaugeAct u1 F1)
      = smGaugeKinetic gs g gp F3 F2 F1 := by
  unfold smGaugeKinetic
  rw [factorKinetic_gauge_invariant _ _ _ h3,
    factorKinetic_gauge_invariant _ _ _ h2,
    factorKinetic_gauge_invariant _ _ _ h1]

/-! ## §2. Fermion kinetic + gauge couplings: the ψ̄D_Aψ structure -/

/-- The Dirac pairing `⟨ψ|D|ψ⟩ = ∑ᵢ ψ̄ᵢ(Dψ)ᵢ` (T2 — structured target).
    The finite Dirac `D` stands in for `i∂̸`; the continuum spinor bundle
    and the manifold factor are priced (§6). -/
def diracPairing (D : Matrix I32 I32 ℂ) (ψ : I32 → ℂ) : ℂ :=
  ∑ i : I32, star (ψ i) * (D *ᵥ ψ) i

/-- The fermion kinetic + gauge-coupling term (T2 — structured target):
    `ψ̄D_Aψ` with `D_A = fluctuatedDirac D_F A` — the finite shadow of
    `ψ̄(i∂̸ + gA̸)ψ`. The `D_F` piece is the free kinematics; the
    `A + JAJ⁻¹` fluctuation pieces are the gauge couplings. -/
def fermionTerm (D_F A : Matrix I32 I32 ℂ) (ψ : I32 → ℂ) : ℂ :=
  diracPairing (fluctuatedDirac D_F A) ψ

/-- The pairing is additive in the operator (T1). -/
theorem diracPairing_add (D₁ D₂ : Matrix I32 I32 ℂ) (ψ : I32 → ℂ) :
    diracPairing (D₁ + D₂) ψ = diracPairing D₁ ψ + diracPairing D₂ ψ := by
  unfold diracPairing
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.add_mulVec, Pi.add_apply]
  ring

/-- The free/coupling split (T1): `ψ̄D_Aψ = ψ̄D_Fψ + ψ̄Aψ + ψ̄(JAJ⁻¹)ψ` —
    the algebraic shape of `ψ̄(i∂̸ + gauge)ψ`. -/
theorem fermionTerm_split (D_F A : Matrix I32 I32 ℂ) (ψ : I32 → ℂ) :
    fermionTerm D_F A ψ
      = diracPairing D_F ψ + diracPairing A ψ
        + diracPairing (oppositeOneForm A) ψ := by
  unfold fermionTerm fluctuatedDirac
  rw [diracPairing_add, diracPairing_add]

/-- The pairing as a trace against the rank-one projector (T1 helper):
    `⟨ψ|D|ψ⟩ = Tr(D·ψψ†)`. -/
theorem diracPairing_eq_trace (D : Matrix I32 I32 ℂ) (ψ : I32 → ℂ) :
    diracPairing D ψ
      = Matrix.trace (D * Matrix.vecMulVec ψ (fun i => star (ψ i))) := by
  unfold diracPairing
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.vecMulVec_apply, Matrix.mulVec, dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- Conjugation of a vector entry (T1 helper). -/
theorem star_mulVec_entry (u : Matrix I32 I32 ℂ) (ψ : I32 → ℂ) (b : I32) :
    star ((u *ᵥ ψ) b) = ∑ k : I32, star (u b k) * star (ψ k) := by
  have e1 : (u *ᵥ ψ) b = ∑ k : I32, u b k * ψ k := by
    simp only [Matrix.mulVec, dotProduct]
  have hstar : ∀ x : ℂ, star x = starRingEnd ℂ x := fun _ => rfl
  rw [e1]
  simp only [hstar, map_sum, map_mul]

/-- The rank-one projector transforms by conjugation (T1 helper):
    `(uψ)(uψ)† = u(ψψ†)u†`. -/
theorem vecMulVec_gauge_conj (u : Matrix I32 I32 ℂ) (ψ : I32 → ℂ) :
    Matrix.vecMulVec (u *ᵥ ψ) (fun i => star ((u *ᵥ ψ) i))
      = u * Matrix.vecMulVec ψ (fun i => star (ψ i)) * u.conjTranspose := by
  ext a b
  have ea : (u *ᵥ ψ) a = ∑ j : I32, u a j * ψ j := by
    simp only [Matrix.mulVec, dotProduct]
  have eb := star_mulVec_entry u ψ b
  have erhs : (u * Matrix.vecMulVec ψ (fun i => star (ψ i)) * u.conjTranspose) a b
      = ∑ j : I32, ∑ k : I32, u a j * (ψ j * star (ψ k)) * star (u b k) := by
    have e1 : (u * Matrix.vecMulVec ψ (fun i => star (ψ i)) * u.conjTranspose) a b
        = ∑ k : I32, ∑ j : I32, (u a j * (ψ j * star (ψ k))) * star (u b k) := by
      simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.conjTranspose_apply,
        Finset.sum_mul]
    rw [e1, Finset.sum_comm]
  have elhs : Matrix.vecMulVec (u *ᵥ ψ) (fun i => star ((u *ᵥ ψ) i)) a b
      = ∑ j : I32, ∑ k : I32, (u a j * ψ j) * (star (u b k) * star (ψ k)) := by
    rw [Matrix.vecMulVec_apply, ea, eb, Finset.sum_mul_sum]
  rw [elhs, erhs]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  ring

/-- Simultaneous-unitary covariance of the pairing (T1):
    `⟨uψ|uDu†|uψ⟩ = ⟨ψ|D|ψ⟩` — the bilinear is basis-independent.
    The TRUE gauge transformation law of the fluctuated Dirac (with the
    inhomogeneous `u[D,u*]` piece) is priced — see `ClassicalYangMills`
    header and §6. -/
theorem diracPairing_gauge_invariant (u D : Matrix I32 I32 ℂ) (hu : IsUnitaryMat u)
    (ψ : I32 → ℂ) :
    diracPairing (gaugeAct u D) (u *ᵥ ψ) = diracPairing D ψ := by
  have h1 := hu.1
  rw [diracPairing_eq_trace, diracPairing_eq_trace, vecMulVec_gauge_conj]
  have hDP : gaugeAct u D
        * (u * Matrix.vecMulVec ψ (fun i => star (ψ i)) * u.conjTranspose)
      = gaugeAct u (D * Matrix.vecMulVec ψ (fun i => star (ψ i))) := by
    have key : u.conjTranspose
          * (u * (Matrix.vecMulVec ψ (fun i => star (ψ i)) * u.conjTranspose))
        = Matrix.vecMulVec ψ (fun i => star (ψ i)) * u.conjTranspose := by
      rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
    unfold gaugeAct
    calc (u * D * u.conjTranspose)
          * (u * Matrix.vecMulVec ψ (fun i => star (ψ i)) * u.conjTranspose)
        = (u * D) * (u.conjTranspose
            * (u * (Matrix.vecMulVec ψ (fun i => star (ψ i)) * u.conjTranspose))) := by
          simp only [Matrix.mul_assoc]
      _ = (u * D) * (Matrix.vecMulVec ψ (fun i => star (ψ i)) * u.conjTranspose) := by
          rw [key]
      _ = u * (D * Matrix.vecMulVec ψ (fun i => star (ψ i))) * u.conjTranspose := by
          simp only [Matrix.mul_assoc]
  rw [hDP]
  exact gaugeAct_trace _ _ h1

/-! ## §3. Higgs potential structure -/

/-- `|H|²` for the Higgs doublet `H ∈ ℂ²` (T2). The doublet reading is T5;
    the `ℂ²` shape is the structural content. -/
noncomputable def higgsNormSq (H : Fin 2 → ℂ) : ℝ :=
  ∑ i : Fin 2, ‖H i‖ ^ 2

/-- The Higgs potential `V(H) = -μ²|H|² + λ|H|⁴` (T2 — structured target).
    `μ²` and `λ` are T2 INPUTS (measured parameters, never derived). -/
noncomputable def higgsPotential (μSq lam : ℝ) (H : Fin 2 → ℂ) : ℝ :=
  -μSq * higgsNormSq H + lam * (higgsNormSq H) ^ 2

/-- `|H|² ≥ 0` (T1). -/
theorem higgsNormSq_nonneg (H : Fin 2 → ℂ) : 0 ≤ higgsNormSq H :=
  Finset.sum_nonneg fun i _ => by positivity

/-- The potential vanishes at the origin (T1). -/
theorem higgsPotential_at_zero (μSq lam : ℝ) :
    higgsPotential μSq lam 0 = 0 := by
  unfold higgsPotential higgsNormSq
  simp

/-- Broken phase (`μ² > 0, λ > 0`): the potential is bounded below by
    `-μ⁴/(4λ)` (T1) — pure algebra, no analysis. -/
theorem higgsPotential_broken_lower_bound (μSq lam : ℝ)
    (_hμ : 0 < μSq) (hlam : 0 < lam) (H : Fin 2 → ℂ) :
    -(μSq ^ 2 / (4 * lam)) ≤ higgsPotential μSq lam H := by
  have hlam' : lam ≠ 0 := ne_of_gt hlam
  unfold higgsPotential
  have hr : 0 ≤ higgsNormSq H := higgsNormSq_nonneg H
  have hsq : 0 ≤ lam * (higgsNormSq H - μSq / (2 * lam)) ^ 2 :=
    mul_nonneg (le_of_lt hlam) (sq_nonneg _)
  have hdecomp : -μSq * higgsNormSq H + lam * (higgsNormSq H) ^ 2
      - (-(μSq ^ 2 / (4 * lam)))
      = lam * (higgsNormSq H - μSq / (2 * lam)) ^ 2 := by
    field_simp
    ring
  linarith

/-- Broken phase: the bound is attained on the circle
    `|H|² = μ²/(2λ)` (T1) — the minima form a circle, the VEV shape,
    with NO value claimed for any physical VEV. -/
theorem higgsPotential_broken_attained (μSq lam : ℝ) (hlam : 0 < lam)
    (H : Fin 2 → ℂ) (hr : higgsNormSq H = μSq / (2 * lam)) :
    higgsPotential μSq lam H = -(μSq ^ 2 / (4 * lam)) := by
  have hlam' : lam ≠ 0 := ne_of_gt hlam
  unfold higgsPotential
  rw [hr]
  field_simp
  ring

/-- Symmetric phase (`μ² ≤ 0, λ ≥ 0`): the origin is the global minimum
    with value `0` (T1). -/
theorem higgsPotential_symmetric_lower_bound (μSq lam : ℝ)
    (hμ : μSq ≤ 0) (hlam : 0 ≤ lam) (H : Fin 2 → ℂ) :
    0 ≤ higgsPotential μSq lam H := by
  unfold higgsPotential
  have hr : 0 ≤ higgsNormSq H := higgsNormSq_nonneg H
  have h1 : 0 ≤ -μSq * higgsNormSq H := mul_nonneg (by linarith) hr
  have h2 : 0 ≤ lam * (higgsNormSq H) ^ 2 := mul_nonneg hlam (sq_nonneg _)
  linarith

/-! ## §4. Yukawa structure (shape only) -/

/-- The Yukawa shape `ψ̄_L Y H ψ_R` (T2 — STRUCTURE ONLY).
    `Y` is a T2 INPUT matrix; NO values, NO fermion mass predictions.
    Jeff's Yukawa modeling decision (`satisfiesDestruction`) is open and
    untouched — this file does not reference it. -/
def yukawaTerm (Y : Matrix (Fin 2) (Fin 2) ℂ) (H : Fin 2 → ℂ)
    (ψL ψR : Fin 2 → ℂ) : ℂ :=
  ∑ i : Fin 2, ∑ j : Fin 2, star (ψL i) * (Y i j * H j) * ψR j

/-- A constant Higgs background turns the Yukawa shape into a fermion
    bilinear with mass matrix `M = Y·H₀` (T2 — the structural content of
    "Yukawa generates masses"; no mass VALUES). -/
def yukawaMassMatrix (Y : Matrix (Fin 2) (Fin 2) ℂ) (H₀ : Fin 2 → ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => Y i j * H₀ j

/-- VEV reduction (T1): with `H` frozen to a constant background `H₀`, the
    Yukawa shape IS the fermion bilinear with `yukawaMassMatrix`. -/
theorem yukawaTerm_vev_bilinear (Y : Matrix (Fin 2) (Fin 2) ℂ) (H₀ : Fin 2 → ℂ)
    (ψL ψR : Fin 2 → ℂ) :
    yukawaTerm Y H₀ ψL ψR
      = ∑ i : Fin 2, ∑ j : Fin 2,
          star (ψL i) * yukawaMassMatrix Y H₀ i j * ψR j := by
  rfl

/-- The Yukawa shape is additive in the input matrix (T1). -/
theorem yukawaTerm_add_Y (Y₁ Y₂ : Matrix (Fin 2) (Fin 2) ℂ) (H : Fin 2 → ℂ)
    (ψL ψR : Fin 2 → ℂ) :
    yukawaTerm (Y₁ + Y₂) H ψL ψR
      = yukawaTerm Y₁ H ψL ψR + yukawaTerm Y₂ H ψL ψR := by
  unfold yukawaTerm
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Matrix.add_apply, add_mul]
  ring

/-- The Yukawa shape is homogeneous in the input matrix (T1). -/
theorem yukawaTerm_smul_Y (c : ℂ) (Y : Matrix (Fin 2) (Fin 2) ℂ) (H : Fin 2 → ℂ)
    (ψL ψR : Fin 2 → ℂ) :
    yukawaTerm (c • Y) H ψL ψR = c * yukawaTerm Y H ψL ψR := by
  unfold yukawaTerm
  simp only [Matrix.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- Vanishing Higgs kills the Yukawa term (T1). -/
theorem yukawaTerm_zero_higgs (Y : Matrix (Fin 2) (Fin 2) ℂ)
    (ψL ψR : Fin 2 → ℂ) :
    yukawaTerm Y 0 ψL ψR = 0 := by
  unfold yukawaTerm
  simp

/-! ## §5. The assembled classical SM Lagrangian shape -/

/-- The assembled classical SM Lagrangian shape (T2 — structured target):
    gauge kinetics + fermion bilinear + Higgs potential + Yukawa.
    All couplings/parameters are T2 inputs; the continuum integral,
    the quantum Lagrangian, and all VALUES are priced (§6). -/
noncomputable def smLagrangian (gs g gp μSq lam : ℝ)
    (F3 F2 F1 : Matrix I32 I32 ℂ)
    (D_F A : Matrix I32 I32 ℂ) (ψ : I32 → ℂ)
    (H : Fin 2 → ℂ) (Y : Matrix (Fin 2) (Fin 2) ℂ)
    (ψL ψR : Fin 2 → ℂ) : ℂ :=
  smGaugeKinetic gs g gp F3 F2 F1
    + fermionTerm D_F A ψ
    + (higgsPotential μSq lam H : ℂ)
    + yukawaTerm Y H ψL ψR

/-! ## §6. Explicitly PRICED (not claimed)

- **Quantum Lagrangian:** path integral, renormalization, anomalies —
  quarantined T5, untouched.
- **Continuum integral `∫_M`:** needs the manifold factor constructed
  (currently T2-axiomatized in `ProductTriple`); all action-level
  statements here are finite represented shadows.
- **Junk-ideal quotient:** the curvature is the represented 2-form BEFORE
  junk is quotiented (see `ClassicalYangMills` header).
- **Inhomogeneous gauge piece:** the `u[D,u*]` term of the full fluctuation
  transformation law (see `ClassicalYangMills` header).
- **Continuum spinors / `i∂̸`:** `diracPairing` uses the finite Dirac;
  the spinor bundle over `M` is priced.
- **Mass/coupling VALUES:** `g_s, g, g'`, `μ²`, `λ`, and the Yukawa matrix
  `Y` are inputs; NOTHING here predicts any of them.
- **Jeff's Yukawa modeling decision** (`satisfiesDestruction`) is open and
  untouched by this file.
-/

end ThetLogos
