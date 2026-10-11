import Mathlib.Tactic
import ThetLogos.ClassicalYangMills

open Matrix

namespace ThetLogos

/-!
# ThetLogos.SMHiggsBreaking — SM-MATCH Track 4: electroweak symmetry breaking

**Directive:** Jeff, 2026-10-11 ("build it to match"): formalize the electroweak
breaking pattern SU(2)_L×U(1)_Y → U(1)_em — the same STRUCTURE as the SM.
Mass VALUES stay out: every mass and coupling is an input, never derived.

Tier header.
- **Scope:** the CLASSICAL Higgs mechanism as an algebraic structure:
  the Higgs doublet, the quartic potential and its VEV, the unbroken/broken
  generator pattern, the W/Z mass FORMULAE as formal relations, the photon's
  masslessness from the unbroken generator, and the Yukawa mass SHAPE
  `m_f = y_f v/√2`.
- **Convention (matches the Track-2 fermion table):** Q = T³ + Y/2.
- **T1 (proved, zero sorrys):** the potential's minimum shape and its unique
  minimizer radius; the VEV attains the minimum; Q annihilates the VEV while
  T¹, T², Y/2 do not; the stabilizer of the VEV is EXACTLY span(Q)
  (the precise algebraic form of SU(2)_L×U(1)_Y → U(1)_em); the gauge-boson
  mass decomposition of |D⟨H⟩|² with M_W = gv/2, M_Z = √(g²+g′²)v/2, M_γ = 0;
  the photon direction is the null direction of the neutral mass form BECAUSE
  its generator is unbroken; the fermion mass shape and its linearity.
- **T2 (definitions / inputs):** the Higgs doublet (Y = +1), the potential
  (μ², λ inputs), the VEV (v input), the generators T¹ T² T³ Q, the connection
  matrix, the mass parameters M_W M_Z, the Yukawa shape (y_f inputs).
- **Priced windows (not claimed):** the QUANTUM Higgs mechanism (this file is
  classical structure only); the hierarchy problem; any mass or coupling
  PREDICTION (values are inputs); the continuum covariant derivative (needs
  the manifold factor); satisfiesDestruction is UNTOUCHED — no Yukawa values,
  no modeling decisions.
- **Tier honesty:** this file formalizes the SM's breaking structure as a
  mathematical target (SM-Match). It does NOT derive SU(2)_L×U(1)_Y, the
  doublet, or the potential from the thet-logos corpus. Nothing here claims
  the represented finite gauge algebra (6-dim caveat stands elsewhere).

## Fit-test mapping (SM breaking → formalized objects)

- Higgs doublet, Y = +1 ↔ `HiggsDoublet`, `higgsHypercharge` (T2).
- V = −μ²|H|² + λ|H|⁴ ↔ `higgsPotential` (T2); minimum shape T1
  (`higgs_potential_min_shape`, `higgs_min_shape_unique`).
- ⟨H⟩ = (0, v/√2) ↔ `higgsVEV` (T2); attains the minimum T1
  (`higgsVEV_minimizes`).
- Q = T³ + Y/2 unbroken; T¹, T², Y broken ↔ `higgsQ`, `higgsT1/2/3` (T2);
  `higgsQ_vev`, `higgsT1_broken`, `higgsT2_broken`, `higgsY_broken` (T1);
  the exact stabilizer `higgs_stabilizer_is_Q` (T1) = SU(2)_L×U(1)_Y → U(1)_em.
- |D_μ⟨H⟩|² mass terms ↔ `higgsMassQuad` (T2); decomposition T1
  (`higgsMassQuad_eq`); M_W = gv/2, M_Z = √(g²+g′²)v/2 as formal relations
  (`higgsMW`, `higgsMZ`, `higgsMW_sq`, `higgsMZ_sq`); M_γ = 0 from the
  unbroken generator (`higgs_photon_generator_unbroken`,
  `higgs_photon_direction_massless`).
- m_f = y_f v/√2 ↔ `diracMassShape` (T2 shape, y_f inputs; T1 linearity).
-/

/-! ## §1. The Higgs doublet and its potential (T2) -/

/-- The Higgs doublet: a complex SU(2) doublet. Tier T2. -/
abbrev HiggsDoublet := Fin 2 → ℂ

/-- Hypercharge of the Higgs doublet: Y = +1 (T2 input).
    With the convention Q = T³ + Y/2, the upper component carries Q = +1
    and the lower component Q = 0 (proved in `higgsQ_diag`). -/
def higgsHypercharge : ℝ := 1

/-- The Higgs potential V(H) = −μ²|H|² + λ|H|⁴ (T2).
    μ² and λ are INPUTS; |H|² = ∑ᵢ ‖Hᵢ‖². -/
def higgsPotential (mu2 lam : ℝ) (H : HiggsDoublet) : ℝ :=
  -mu2 * ∑ i, Complex.normSq (H i) + lam * (∑ i, Complex.normSq (H i)) ^ 2

/-- The VEV ⟨H⟩ = (0, v/√2) (T2). v is an INPUT. -/
noncomputable def higgsVEV (v : ℝ) : HiggsDoublet := ![0, ((v / Real.sqrt 2 : ℝ) : ℂ)]

/-! ## §2. The minimum: shape and VEV (T1) -/

/-- Helper: normSq of a real cast. -/
theorem Complex.normSq_ofReal_cast (x : ℝ) : Complex.normSq (x : ℂ) = x ^ 2 := by
  rw [Complex.normSq_apply]
  simp only [Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- Helper: the VEV's neutral component is nonzero when v ≠ 0. -/
theorem higgsW_ne_zero {v : ℝ} (hv : v ≠ 0) :
    ((v / Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
  intro hc
  apply hv
  have hvr : (v / Real.sqrt 2 : ℝ) = 0 := by
    have hre := congrArg Complex.re hc
    simpa using hre
  have hsqrt : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  rcases div_eq_zero_iff.mp hvr with h | h
  · exact h
  · exact absurd h hsqrt

/-- T1: the potential's shape. With μ² = λv² and λ > 0, the function
    r ↦ −μ²r + λr² is minimized at r = v²/2 (formally: it differs from its
    value there by λ(r − v²/2)² ≥ 0). -/
theorem higgs_potential_min_shape {lam v r : ℝ} (hlam : 0 < lam) :
    -(lam * v ^ 2) * (v ^ 2 / 2) + lam * (v ^ 2 / 2) ^ 2
      ≤ -(lam * v ^ 2) * r + lam * r ^ 2 := by
  have h : (-(lam * v ^ 2) * r + lam * r ^ 2)
      - (-(lam * v ^ 2) * (v ^ 2 / 2) + lam * (v ^ 2 / 2) ^ 2)
      = lam * (r - v ^ 2 / 2) ^ 2 := by ring
  have hnn : 0 ≤ lam * (r - v ^ 2 / 2) ^ 2 :=
    mul_nonneg (le_of_lt hlam) (sq_nonneg _)
  linarith

/-- T1: the minimizer radius is unique — the minimum is attained exactly at
    r = v²/2. -/
theorem higgs_min_shape_unique {lam v r : ℝ} (hlam : 0 < lam) :
    (-(lam * v ^ 2) * r + lam * r ^ 2
      = -(lam * v ^ 2) * (v ^ 2 / 2) + lam * (v ^ 2 / 2) ^ 2)
      ↔ r = v ^ 2 / 2 := by
  constructor
  · intro heq
    have h : (-(lam * v ^ 2) * r + lam * r ^ 2)
        - (-(lam * v ^ 2) * (v ^ 2 / 2) + lam * (v ^ 2 / 2) ^ 2)
        = lam * (r - v ^ 2 / 2) ^ 2 := by ring
    have h0 : lam * (r - v ^ 2 / 2) ^ 2 = 0 := by linarith
    have hsq : (r - v ^ 2 / 2) ^ 2 = 0 := by
      rcases mul_eq_zero.mp h0 with h1 | h1
      · exact absurd h1 (ne_of_gt hlam)
      · exact h1
    have hz : r - v ^ 2 / 2 = 0 := pow_eq_zero_iff (by norm_num) |>.mp hsq
    linarith
  · intro hr
    rw [hr]

/-- T1: the VEV has |⟨H⟩|² = v²/2. -/
theorem higgsVEV_normSq (v : ℝ) :
    ∑ i, Complex.normSq (higgsVEV v i) = v ^ 2 / 2 := by
  rw [Fin.sum_univ_two]
  simp only [higgsVEV, Matrix.cons_val_zero, Matrix.cons_val_one,
    Complex.normSq_zero, zero_add]
  rw [Complex.normSq_ofReal_cast, div_pow, Real.sq_sqrt (by norm_num)]

/-- T1: the VEV minimizes the potential (formally, from the shape):
    with μ² = λv², no doublet configuration has lower V than ⟨H⟩. -/
theorem higgsVEV_minimizes {lam v : ℝ} (hlam : 0 < lam) (H : HiggsDoublet) :
    higgsPotential (lam * v ^ 2) lam (higgsVEV v)
      ≤ higgsPotential (lam * v ^ 2) lam H := by
  have h1 : higgsPotential (lam * v ^ 2) lam (higgsVEV v)
      = -(lam * v ^ 2) * (v ^ 2 / 2) + lam * (v ^ 2 / 2) ^ 2 := by
    unfold higgsPotential
    rw [higgsVEV_normSq]
  have h2 : higgsPotential (lam * v ^ 2) lam H
      = -(lam * v ^ 2) * (∑ i, Complex.normSq (H i))
        + lam * (∑ i, Complex.normSq (H i)) ^ 2 := rfl
  rw [h1, h2]
  exact higgs_potential_min_shape hlam

/-! ## §3. The breaking pattern SU(2)_L × U(1)_Y → U(1)_em (T1) -/

/-- Pauli matrices (T2). Prefixed to avoid the corpus-wide `pauli`. -/
def higgsPauli1 : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]
def higgsPauli2 : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]
def higgsPauli3 : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- SU(2)_L generators T^a = σ^a/2 acting on the doublet (T2). -/
noncomputable def higgsT1 : Matrix (Fin 2) (Fin 2) ℂ := (1 / 2 : ℂ) • higgsPauli1
noncomputable def higgsT2 : Matrix (Fin 2) (Fin 2) ℂ := (1 / 2 : ℂ) • higgsPauli2
noncomputable def higgsT3 : Matrix (Fin 2) (Fin 2) ℂ := (1 / 2 : ℂ) • higgsPauli3

/-- The electric-charge generator Q = T³ + Y/2 with Y = +1 on the doublet
    (T2). Convention matches the Track-2 fermion table. -/
noncomputable def higgsQ : Matrix (Fin 2) (Fin 2) ℂ :=
  higgsT3 + (1 / 2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)

/-- T1: Q = diag(1, 0) — the upper component carries charge +1, the lower 0.
    (Deliverable 1's charge assignment, proved.) -/
theorem higgsQ_diag : higgsQ = !![1, 0; 0, 0] := by
  ext i j
  fin_cases i
  · fin_cases j <;> simp [higgsQ, higgsT3, higgsPauli3] <;> ring
  · fin_cases j <;> simp [higgsQ, higgsT3, higgsPauli3] <;> ring

/-- T1: the hypercharge generator on the doublet is the identity (Y = +1). -/
theorem higgs_hypercharge_gen :
    ((higgsHypercharge : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)
      = 1 := by
  simp [higgsHypercharge]

/-- T1: generator actions on the VEV (the raw material of the pattern).
    Entries are evaluated once as standalone lemmas so the `*ᵥ` unfolding
    never sees the `!!` constructors. -/
theorem higgsT1_00 : higgsT1 0 0 = 0 := by simp [higgsT1, higgsPauli1]
theorem higgsT1_01 : higgsT1 0 1 = 1 / 2 := by simp [higgsT1, higgsPauli1]
theorem higgsT1_10 : higgsT1 1 0 = 1 / 2 := by simp [higgsT1, higgsPauli1]
theorem higgsT1_11 : higgsT1 1 1 = 0 := by simp [higgsT1, higgsPauli1]
theorem higgsT2_00 : higgsT2 0 0 = 0 := by simp [higgsT2, higgsPauli2]
theorem higgsT2_01 : higgsT2 0 1 = -Complex.I / 2 := by simp [higgsT2, higgsPauli2]; ring
theorem higgsT2_10 : higgsT2 1 0 = Complex.I / 2 := by simp [higgsT2, higgsPauli2]; ring
theorem higgsT2_11 : higgsT2 1 1 = 0 := by simp [higgsT2, higgsPauli2]
theorem higgsT3_00 : higgsT3 0 0 = 1 / 2 := by simp [higgsT3, higgsPauli3]
theorem higgsT3_01 : higgsT3 0 1 = 0 := by simp [higgsT3, higgsPauli3]
theorem higgsT3_10 : higgsT3 1 0 = 0 := by simp [higgsT3, higgsPauli3]
theorem higgsT3_11 : higgsT3 1 1 = -1 / 2 := by simp [higgsT3, higgsPauli3]; ring

theorem higgsT1_vev (v : ℝ) :
    higgsT1 *ᵥ higgsVEV v = ![((v / Real.sqrt 2 : ℝ) : ℂ) / 2, 0] := by
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    higgsT1_00, higgsT1_01, higgsT1_10, higgsT1_11, higgsVEV] <;> ring

theorem higgsT2_vev (v : ℝ) :
    higgsT2 *ᵥ higgsVEV v
      = ![-Complex.I * (((v / Real.sqrt 2 : ℝ) : ℂ) / 2), 0] := by
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    higgsT2_00, higgsT2_01, higgsT2_10, higgsT2_11, higgsVEV] <;> ring

theorem higgsT3_vev (v : ℝ) :
    higgsT3 *ᵥ higgsVEV v = ![0, -(((v / Real.sqrt 2 : ℝ) : ℂ) / 2)] := by
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    higgsT3_00, higgsT3_01, higgsT3_10, higgsT3_11, higgsVEV] <;> ring

theorem higgsY_vev (v : ℝ) :
    ((1 / 2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) *ᵥ higgsVEV v
      = ![0, ((v / Real.sqrt 2 : ℝ) : ℂ) / 2] := by
  rw [Matrix.smul_mulVec, Matrix.one_mulVec]
  ext i
  fin_cases i <;> simp [higgsVEV, Pi.smul_apply, smul_eq_mul] <;> ring

/-- T1: Q annihilates the VEV — the electric-charge generator is UNBROKEN. -/
theorem higgsQ_vev (v : ℝ) : higgsQ *ᵥ higgsVEV v = 0 := by
  unfold higgsQ
  rw [Matrix.add_mulVec, higgsT3_vev, higgsY_vev]
  ext i
  fin_cases i <;> simp <;> ring

/-- T1: T¹ is BROKEN (moves the VEV). -/
theorem higgsT1_broken {v : ℝ} (hv : v ≠ 0) : higgsT1 *ᵥ higgsVEV v ≠ 0 := by
  rw [higgsT1_vev]
  intro h
  have h0 := congrFun h 0
  simp only [Matrix.cons_val_zero, Pi.zero_apply] at h0
  apply higgsW_ne_zero hv
  rcases div_eq_zero_iff.mp h0 with h1 | h1
  · exact h1
  · norm_num at h1

/-- T1: T² is BROKEN (moves the VEV). -/
theorem higgsT2_broken {v : ℝ} (hv : v ≠ 0) : higgsT2 *ᵥ higgsVEV v ≠ 0 := by
  rw [higgsT2_vev]
  intro h
  have h0 := congrFun h 0
  simp only [Matrix.cons_val_zero, Pi.zero_apply] at h0
  apply higgsW_ne_zero hv
  have hI : (-Complex.I) ≠ 0 := by simp
  rcases mul_eq_zero.mp h0 with h1 | h1
  · exact absurd h1 hI
  · rcases div_eq_zero_iff.mp h1 with h2 | h2
    · exact h2
    · norm_num at h2

/-- T1: the hypercharge generator Y is BROKEN (moves the VEV). -/
theorem higgsY_broken {v : ℝ} (hv : v ≠ 0) :
    ((1 / 2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) *ᵥ higgsVEV v ≠ 0 := by
  rw [higgsY_vev]
  intro h
  have h1 := congrFun h 1
  simp only [Matrix.cons_val_one, Pi.zero_apply] at h1
  apply higgsW_ne_zero hv
  rcases div_eq_zero_iff.mp h1 with h2 | h2
  · exact h2
  · norm_num at h2

/-- T1: the action of a general real generator combination on the VEV.
    The upper component sees a − ib (T¹, T² broken directions); the lower
    sees d − c (the T³ vs Y/2 competition that leaves Q unbroken). -/
theorem higgs_gen_combo_vev (a b c d : ℝ) (v : ℝ) :
    ((a : ℂ) • higgsT1 + (b : ℂ) • higgsT2 + (c : ℂ) • higgsT3
        + (d : ℂ) • ((1 / 2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)))
        *ᵥ higgsVEV v
      = ![((a : ℂ) - (b : ℂ) * Complex.I) * (((v / Real.sqrt 2 : ℝ) : ℂ) / 2),
          ((d : ℂ) - (c : ℂ)) * (((v / Real.sqrt 2 : ℝ) : ℂ) / 2)] := by
  rw [Matrix.add_mulVec, Matrix.add_mulVec, Matrix.add_mulVec,
    Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec,
    Matrix.smul_mulVec, higgsY_vev, higgsT1_vev, higgsT2_vev, higgsT3_vev]
  ext i
  fin_cases i <;> simp <;> ring

/-- T1 (the breaking pattern, precise algebraic form):
    the stabilizer of the VEV inside the real span of {T¹, T², T³, Y/2} is
    EXACTLY the line spanned by Q = T³ + Y/2. Three generators broken, one
    unbroken: SU(2)_L × U(1)_Y → U(1)_em. -/
theorem higgs_stabilizer_is_Q {v : ℝ} (hv : v ≠ 0) {a b c d : ℝ}
    (h : ((a : ℂ) • higgsT1 + (b : ℂ) • higgsT2 + (c : ℂ) • higgsT3
        + (d : ℂ) • ((1 / 2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)))
        *ᵥ higgsVEV v = 0) :
    a = 0 ∧ b = 0 ∧ c = d := by
  rw [higgs_gen_combo_vev] at h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.zero_apply] at h0 h1
  have hw : ((v / Real.sqrt 2 : ℝ) : ℂ) / 2 ≠ 0 := by
    intro hc
    apply higgsW_ne_zero hv
    rcases div_eq_zero_iff.mp hc with h2 | h2
    · exact h2
    · norm_num at h2
  have hab : (a : ℂ) - (b : ℂ) * Complex.I = 0 := by
    rcases mul_eq_zero.mp h0 with h2 | h2
    · exact h2
    · exact absurd h2 hw
  have hdc : (d : ℂ) - (c : ℂ) = 0 := by
    rcases mul_eq_zero.mp h1 with h2 | h2
    · exact h2
    · exact absurd h2 hw
  have ha : a = 0 := by
    have hre := congrArg Complex.re hab
    simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.zero_re] at hre
    linarith
  have hb : b = 0 := by
    have him := congrArg Complex.im hab
    simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.zero_im] at him
    linarith
  have hcd : c = d := by
    have hre := congrArg Complex.re hdc
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.zero_re] at hre
    linarith
  exact ⟨ha, hb, hcd⟩

/-! ## §4. W/Z mass generation — formal relations (T1 structure) -/

/-- T2: the electroweak connection on the doublet,
    D = ∂ − igT^aW^a − ig′(Y/2)B. The mass form comes from |D⟨H⟩|²; the
    factor i drops out of the norm (|i| = 1) and is kept for fidelity.
    g, g′ and the field values (W¹, W², W³, B) are INPUTS. -/
noncomputable def higgsConn (g g' W1 W2 W3 B : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  -Complex.I • ((g : ℂ) • ((W1 : ℂ) • higgsT1 + (W2 : ℂ) • higgsT2
      + (W3 : ℂ) • higgsT3)
    + ((g' * B / 2 : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ))

/-- T2: the Higgs kinetic mass form |D⟨H⟩|², as a function of the gauge
    field values. -/
noncomputable def higgsMassQuad (g g' v W1 W2 W3 B : ℝ) : ℝ :=
  ∑ i, Complex.normSq ((higgsConn g g' W1 W2 W3 B *ᵥ higgsVEV v) i)

/-- T2: W mass parameter (FORMAL relation): M_W = gv/2. -/
noncomputable def higgsMW (g v : ℝ) : ℝ := g * v / 2

/-- T2: Z mass parameter (FORMAL relation): M_Z = √(g²+g′²)v/2. -/
noncomputable def higgsMZ (g g' v : ℝ) : ℝ := Real.sqrt (g ^ 2 + g' ^ 2) * v / 2

/-- T1 helper: a scalar multiple of the VEV, in components. Keeps the
    B-term away from full-`simp` cast mangling. -/
theorem higgsBterm_vev (c : ℂ) (v : ℝ) :
    (c • higgsVEV v) = ![0, c * ((v / Real.sqrt 2 : ℝ) : ℂ)] := by
  ext i
  fin_cases i <;> simp [Pi.smul_apply, smul_eq_mul, higgsVEV] <;> ring

/-- T1: the connection's action on the VEV, in components.
    Upper: the charged combination g(W¹−iW²); lower: g′B − gW³. -/
theorem higgsConn_vev (g g' v W1 W2 W3 B : ℝ) :
    higgsConn g g' W1 W2 W3 B *ᵥ higgsVEV v
      = ![-Complex.I * ((g : ℂ) * (((W1 : ℂ) - (W2 : ℂ) * Complex.I)
            * (((v / Real.sqrt 2 : ℝ) : ℂ) / 2))),
          -Complex.I * ((-(g : ℂ) * (W3 : ℂ) * (((v / Real.sqrt 2 : ℝ) : ℂ) / 2)
            + ((g' * B / 2 : ℝ) : ℂ) * ((v / Real.sqrt 2 : ℝ) : ℂ)))] := by
  unfold higgsConn
  simp only [Matrix.smul_mulVec, Matrix.add_mulVec, Matrix.one_mulVec,
    higgsT1_vev, higgsT2_vev, higgsT3_vev, higgsBterm_vev]
  ext i
  fin_cases i <;> simp <;> (try exact Or.inl (by ring)) <;> ring

/-- T1: the mass decomposition of |D⟨H⟩|² —
    charged sector ∝ (W¹²+W²²), neutral sector ∝ (gW³−g′B)². -/
theorem higgsMassQuad_eq (g g' v W1 W2 W3 B : ℝ) :
    higgsMassQuad g g' v W1 W2 W3 B
      = g ^ 2 * v ^ 2 * (W1 ^ 2 + W2 ^ 2) / 8
        + v ^ 2 * (g * W3 - g' * B) ^ 2 / 8 := by
  unfold higgsMassQuad
  rw [Fin.sum_univ_two, higgsConn_vev]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  have eI : Complex.normSq (-Complex.I) = 1 := by
    rw [Complex.normSq_apply]
    simp
  have nW : Complex.normSq ((W1 : ℂ) - (W2 : ℂ) * Complex.I)
      = W1 ^ 2 + W2 ^ 2 := by
    rw [Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  have e0 : Complex.normSq (-Complex.I * ((g : ℂ)
        * (((W1 : ℂ) - (W2 : ℂ) * Complex.I)
          * ((((v / Real.sqrt 2 : ℝ)) : ℂ) / 2))))
      = g ^ 2 * v ^ 2 * (W1 ^ 2 + W2 ^ 2) / 8 := by
    rw [Complex.normSq_mul, eI, one_mul]
    have hI0 : (g : ℂ) * (((W1 : ℂ) - (W2 : ℂ) * Complex.I)
          * ((((v / Real.sqrt 2 : ℝ)) : ℂ) / 2))
        = (((g * (v / Real.sqrt 2) / 2 : ℝ)) : ℂ)
          * ((W1 : ℂ) - (W2 : ℂ) * Complex.I) := by
      push_cast
      ring
    rw [hI0, Complex.normSq_mul, Complex.normSq_ofReal_cast, nW,
      div_pow, mul_pow, div_pow, Real.sq_sqrt (by norm_num)]
    ring
  have e1 : Complex.normSq (-Complex.I * ((-(g : ℂ) * (W3 : ℂ) * (((v / Real.sqrt 2 : ℝ) : ℂ) / 2) + ((g' * B / 2 : ℝ) : ℂ) * ((v / Real.sqrt 2 : ℝ) : ℂ))))
      = v ^ 2 * (g * W3 - g' * B) ^ 2 / 8 := by
    have hI1 : ((-(g : ℂ) * (W3 : ℂ) * (((v / Real.sqrt 2 : ℝ) : ℂ) / 2) + ((g' * B / 2 : ℝ) : ℂ) * ((v / Real.sqrt 2 : ℝ) : ℂ)))
        = ((((g' * B - g * W3) / 2 * (v / Real.sqrt 2) : ℝ)) : ℂ) := by
      push_cast
      ring
    rw [hI1, Complex.normSq_mul, eI, one_mul, Complex.normSq_ofReal_cast,
      mul_pow, div_pow, div_pow, Real.sq_sqrt (by norm_num)]
    ring
  rw [e0, e1]

/-- T1: M_W² = g²v²/4 (formal). -/
theorem higgsMW_sq (g v : ℝ) : (higgsMW g v) ^ 2 = g ^ 2 * v ^ 2 / 4 := by
  unfold higgsMW
  ring

/-- T1: M_Z² = (g²+g′²)v²/4 (formal). -/
theorem higgsMZ_sq (g g' v : ℝ) :
    (higgsMZ g g' v) ^ 2 = (g ^ 2 + g' ^ 2) * v ^ 2 / 4 := by
  unfold higgsMZ
  rw [div_pow, mul_pow, Real.sq_sqrt (by positivity)]
  ring

/-- T1: the charged mass term is M_W²·((W¹²+W²²)/2) — i.e. M_W = gv/2. -/
theorem higgs_W_mass_term (g g' v W1 W2 : ℝ) :
    higgsMassQuad g g' v W1 W2 0 0
      = (higgsMW g v) ^ 2 * ((W1 ^ 2 + W2 ^ 2) / 2) := by
  rw [higgsMassQuad_eq, higgsMW_sq]
  ring

/-- T1: the Z mass term is ½M_Z²·(g²+g′²)-normalized — i.e. M_Z = √(g²+g′²)v/2. -/
theorem higgs_Z_mass_term (g g' v : ℝ) :
    higgsMassQuad g g' v 0 0 g (-g')
      = (1 / 2) * (higgsMZ g g' v) ^ 2 * (g ^ 2 + g' ^ 2) := by
  rw [higgsMassQuad_eq, higgsMZ_sq]
  ring

/-- T1: the photon stays massless BECAUSE its generator is unbroken —
    any Q-coupled gauge field gets no mass term from |D⟨H⟩|², since
    Q annihilates the VEV (`higgsQ_vev`). -/
theorem higgs_photon_generator_unbroken (c : ℂ) (v : ℝ) :
    (c • higgsQ) *ᵥ higgsVEV v = 0 := by
  rw [Matrix.smul_mulVec, higgsQ_vev, smul_zero]

/-- T1: M_γ = 0 — the neutral mass form has a null direction (the photon
    combination (W³,B) ∝ (g′,g)); the orthogonal combination gets M_Z. -/
theorem higgs_photon_direction_massless (g g' v : ℝ) :
    higgsMassQuad g g' v 0 0 g' g = 0 := by
  rw [higgsMassQuad_eq]
  ring

/-! ## §5. Fermion mass shape (T2 def, T1 structure) -/

/-- T2: the Dirac mass SHAPE from a Yukawa term evaluated at the VEV.
    A Yukawa coupling y_f (INPUT — no values assigned here) multiplies the
    neutral VEV component v/√2; the induced Dirac mass parameter is
    m_f = y_f·v/√2. satisfiesDestruction is UNTOUCHED: no Yukawa values,
    no modeling decisions. -/
noncomputable def diracMassShape (y v : ℝ) : ℝ := y * v / Real.sqrt 2

/-- T1: the shape is y_f times the neutral VEV component. -/
theorem diracMassShape_eq (y v : ℝ) :
    diracMassShape y v = y * (v / Real.sqrt 2) := by
  unfold diracMassShape
  ring

/-- T1: the shape is linear in the Yukawa coupling. -/
theorem diracMassShape_add (y1 y2 v : ℝ) :
    diracMassShape (y1 + y2) v
      = diracMassShape y1 v + diracMassShape y2 v := by
  unfold diracMassShape
  ring

/-- T1: with v > 0, the induced mass vanishes iff the coupling does —
    no mass without a Yukawa input (structure, not a prediction). -/
theorem diracMassShape_zero_iff {v : ℝ} (hv : 0 < v) {y : ℝ} :
    diracMassShape y v = 0 ↔ y = 0 := by
  unfold diracMassShape
  constructor
  · intro h
    rw [div_eq_zero_iff] at h
    rcases h with h1 | h1
    · rcases mul_eq_zero.mp h1 with h2 | h2
      · exact h2
      · linarith
    · have hsqrt : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
      linarith
  · intro h
    rw [h]
    simp

/-! ## §6. Priced windows (not claimed)

- The QUANTUM Higgs mechanism: this file is classical structure only
  (potential, VEV, tree-level mass relations). Loop corrections, the
  effective potential, and vacuum stability are not touched.
- The hierarchy problem: why v ≪ M_Planck is unasked and unanswered here.
- Mass/coupling PREDICTIONS: g, g′, v, λ, μ², and every y_f are inputs.
  This file derives no numerical value — M_W, M_Z, m_f are formal relations.
- The continuum covariant derivative D_μ and ∫_M: priced at the manifold
  factor (T2-axiomatized in `ProductTriple`).
- satisfiesDestruction: untouched (Jeff's Yukawa modeling decision open).
-/

/-! ## Verdict (Track 4)

**MATCH** — the electroweak breaking pattern SU(2)_L×U(1)_Y → U(1)_em and the
gauge-boson mass structure are formalized at T1 with zero sorrys:
Q = T³+Y/2 is proved to be the EXACT unbroken generator
(`higgs_stabilizer_is_Q`); M_W = gv/2, M_Z = √(g²+g′²)v/2, M_γ = 0 as formal
relations with (g, g′, v) inputs; the photon's masslessness is proved from
the unbroken generator; the fermion mass shape m_f = y_f v/√2 is formalized
with y_f inputs. Quantum mechanism, hierarchy, and all mass values: priced.
-/

end ThetLogos
