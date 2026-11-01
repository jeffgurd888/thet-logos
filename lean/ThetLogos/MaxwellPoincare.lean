import Mathlib.Tactic
import ThetLogos.MaxwellQuadSpectrum

namespace ThetLogos

open Finset

/-!
# ThetLogos.MaxwellPoincare - MAX-4: the Poincare brick (MAX-3 clause 4)

**Status: MAX-4 landing brick. NO CLAIM. No Millennium
statement, no ladder rung, no dial (dials stay 0/4).**
Governing texts: the MAX-0 pin `MaxwellQuadPost.lean`
(registered (M5) form, `maxwellM5`), MAX-2
`MaxwellQuadAssembly.lean` (form identity `maxwellOp_form`,
symmetry `maxwellOp_form_symm`, kernel = flat angles
`maxwellM2_proved`, gauge modes in the kernel
`maxwellOp_gaugeAngle`), MAX-3 `MaxwellQuadSpectrum.lean`
(`maxwellM5_spectrum_part`: clauses 1, 2, 3, 5; the
plaquette enumeration expansion `sum_allPlaqData` and
`plaqForm`), under the MAX-4 pack (clause 4 = the discrete
Poincare/Wirtinger bound).

## What is proved here

Clause 4 of (M5): every eigenvalue `lam` of the pin's
`maxwellOp N` at Even `N` satisfies `lam = 0` or
`4 * sin^2 (pi / N) <= lam`; combined with
`maxwellM5_spectrum_part` this asserts `maxwellM5` in FULL
(`maxwellM5_full`).

## Method (Fourier analysis on the finite cube)

For a link angle `theta`, write `g_mu c = linkVal theta c mu`
for its component functions on layer sites. An eigenvector
with nonzero eigenvalue is orthogonal (via the form
symmetry of MAX-2) to every kernel vector; applied to
gauge modes this gives the pointwise divergence-free
condition `maxwellDiv theta = 0`, and applied to the
constant direction fields it gives zero component means.
The quadratic form is then bounded below by Fourier
analysis on the cube `(ZMod N)^3`: Parseval for the
plaquette functions `plaqForm theta c mu nu`, whose Fourier
coefficients are `(u_mu - 1) * A_nu - (u_nu - 1) * A_mu`
(`u_mu` the shift multiplier at momentum `k`, `A` the
component coefficients), the Lagrange identity per
momentum (its defect term is exactly the Fourier
coefficient of the divergence, hence zero - this is the
Weitzenboeck step, carried per momentum), the multiplier
bound `|u_mu - 1|^2 = 4 * sin^2 (pi * (k mu).val / N)`,
and the cycle Wirtinger bound
`sin^2 (pi * v / N) >= sin^2 (pi / N)` for `1 <= v <= N - 1`
(`cycle_sin_sq_ge`). This is the registered route:
discrete Wirtinger on the cycle, tensored over the cube
(the cube Fourier transform), transported through the
curl-curl form identity of MAX-2.

## Count band (registered at first write)

Expected M-L band: strict 40-80, defs 6-14.

## Fences

Finite in every statement: the chosen finite operator on
the finite link-angle space at spacing 1; the gap value is
a property of that finite operator, never a continuum
dispersion. FENCE SENTENCE: the words "Lorentzian" and
"bridge" are not earned terms in this line and appear in
this module only inside this fence sentence.
-/

section FourierSetup

variable {N : ℕ} [NeZero N]

/-- The spatial coordinate of a layer site in direction
`j : Fin 3`. -/
def spatialCoord (c : LayerSite N) (j : Fin 3) : ZMod N :=
  c.1 (Fin.succ j)

/-- The cube Fourier phase of momentum `k` at site `c`:
`sum_j 2 * pi * (k j).val * (spatialCoord c j).val / N`. -/
noncomputable def sitePhase3 (k : Fin 3 → ZMod N) (c : LayerSite N) :
    ℝ :=
  ∑ j, 2 * Real.pi * ((k j).val : ℝ)
    * ((spatialCoord c j).val : ℝ) / (N : ℝ)

/-- The complex Fourier coefficient of a real site function
`f` at momentum `k`:
`sum_c (f c) * exp (-i * sitePhase3 k c)`. -/
noncomputable def fhat (f : LayerSite N → ℝ) (k : Fin 3 → ZMod N) :
    ℂ :=
  ∑ c, (f c : ℂ)
    * Complex.exp ((-(sitePhase3 k c) : ℂ) * Complex.I)

/-- The shift multiplier at direction `mu` and momentum
`k`: `exp (i * phi)` with `phi = 2 * modePhase (Fin.cons 0 k) mu`
(twice the MAX-3 half-angle). At `mu = 0` this is `1`. -/
noncomputable def shiftMult (k : Fin 3 → ZMod N) (μ : Fin 4) : ℂ :=
  Complex.exp (((2 * modePhase (Fin.cons (0 : ZMod N) k) μ : ℝ) : ℂ)
    * Complex.I)

/-- The component function of a link angle in direction
`mu`, as a site function. -/
noncomputable def linkComp (θ : linkAngle N) (μ : Fin 4) :
    LayerSite N → ℝ :=
  fun c => linkVal θ c μ

/-- The plaquette function of a link angle at the ordered
pair `(mu, nu)`, as a site function. -/
noncomputable def plaqSite (θ : linkAngle N) (μ ν : Fin 4) :
    LayerSite N → ℝ :=
  fun c => plaqForm θ c μ ν

/-- The **discrete divergence** of a link angle at a site:
`sum_mu (g_mu c - g_mu (c - e_mu))`, the adjoint of the
gauge gradient read in coordinates. -/
noncomputable def maxwellDiv (θ : linkAngle N) (c : LayerSite N) :
    ℝ :=
  ∑ μ : Fin 4, (if h : μ ≠ 0 then
    linkVal θ c μ - linkVal θ (layerUnshift μ h c) μ else 0)

end FourierSetup

section CycleWirtinger

variable {N : ℕ} [NeZero N]

/-- **Cycle Wirtinger bound**: for `1 <= v <= N - 1`,
`sin^2 (pi / N) <= sin^2 (pi * v / N)` - the first nonzero
Fourier mode of the cycle minimizes `sin^2`. -/
theorem cycle_sin_sq_ge (hN : 2 ≤ N) {v : ℕ} (hv1 : 1 ≤ v)
    (hv2 : v ≤ N - 1) :
    Real.sin (Real.pi / (N : ℝ)) ^ 2
      ≤ Real.sin (Real.pi * (v : ℝ) / (N : ℝ)) ^ 2 := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast (by omega : 0 < N)
  have hN2 : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  set a : ℝ := Real.pi / (N : ℝ) with ha
  set b : ℝ := Real.pi * (v : ℝ) / (N : ℝ) with hb
  have ha0 : 0 < a := div_pos Real.pi_pos hNpos
  have ha2 : a ≤ Real.pi / 2 := by
    rw [ha, div_le_iff₀ hNpos]
    nlinarith [Real.pi_pos]
  have hb_eq : b = a * (v : ℝ) := by
    rw [ha, hb]
    ring
  have hb1 : a ≤ b := by
    rw [hb_eq]
    have hv : (1 : ℝ) ≤ (v : ℝ) := by exact_mod_cast hv1
    nlinarith [ha0]
  have hb2 : b ≤ Real.pi - a := by
    have hvN : (v : ℝ) ≤ (N : ℝ) - 1 := by
      have h1 : (v : ℝ) ≤ ((N - 1 : ℕ) : ℝ) := by
        exact_mod_cast hv2
      rw [Nat.cast_sub (by omega : 1 ≤ N), Nat.cast_one] at h1
      exact h1
    have hN' : (N : ℝ) ≠ 0 := hNpos.ne'
    have haN : a * (N : ℝ) = Real.pi := by
      rw [ha]
      exact div_mul_cancel₀ Real.pi hN'
    have hbN : b * (N : ℝ) = Real.pi * (v : ℝ) := by
      rw [hb]
      exact div_mul_cancel₀ _ hN'
    have hmul : b * (N : ℝ) ≤ (Real.pi - a) * (N : ℝ) := by
      rw [sub_mul, haN, hbN]
      nlinarith [hvN, Real.pi_pos]
    exact le_of_mul_le_mul_right hmul hNpos
  have hsin : Real.sin a ≤ Real.sin b := by
    by_cases hbhalf : b ≤ Real.pi / 2
    · exact Real.sin_le_sin_of_le_of_le_pi_div_two
        (by linarith [ha0, Real.pi_pos]) hbhalf hb1
    · have h1 : Real.sin b = Real.sin (Real.pi - b) :=
        (Real.sin_pi_sub b).symm
      have h2 : a ≤ Real.pi - b := by linarith [hb2]
      have h3 : Real.pi - b ≤ Real.pi / 2 := by linarith [hbhalf]
      rw [h1]
      exact Real.sin_le_sin_of_le_of_le_pi_div_two
        (by linarith [ha0, Real.pi_pos]) h3 h2
  have ha_nn : 0 ≤ Real.sin a :=
    Real.sin_nonneg_of_nonneg_of_le_pi ha0.le
      (by linarith [ha2, Real.pi_pos])
  have hb_nn : 0 ≤ Real.sin b :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hb1, ha0])
      (by linarith [hb2, ha0])
  exact pow_le_pow_left₀ ha_nn hsin 2

end CycleWirtinger

section Orthogonality

variable {N : ℕ} [NeZero N]

/-- The primitive root of unity used by the cube Fourier
transform: `exp (2 * pi * I / N)`. -/
noncomputable def zetaRoot : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I / (N : ℂ))

theorem zetaRoot_prim : IsPrimitiveRoot (zetaRoot (N := N)) N :=
  Complex.isPrimitiveRoot_exp N (NeZero.ne N)

theorem zetaRoot_pow_N : (zetaRoot (N := N)) ^ N = 1 :=
  zetaRoot_prim.pow_eq_one

/-- One exponential factor of the cube phase:
`exp (i * (2 * pi * a * b / N)) = zetaRoot ^ (a * b)`. -/
theorem exp_phase_factor (a b : ℕ) :
    Complex.exp ((↑(2 * Real.pi * (a : ℝ) * (b : ℝ) / (N : ℝ)) : ℂ)
        * Complex.I)
      = (zetaRoot (N := N)) ^ (a * b) := by
  have hNℂ : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  unfold zetaRoot
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  field_simp

/-- The exponential of the cube phase is the product of the
per-direction root-of-unity powers. -/
theorem exp_sitePhase3 (k : Fin 3 → ZMod N) (c : LayerSite N) :
    Complex.exp (((sitePhase3 k c : ℝ) : ℂ) * Complex.I)
      = ∏ j, (zetaRoot (N := N))
          ^ ((k j).val * (spatialCoord c j).val) := by
  rw [sitePhase3, Complex.ofReal_sum, Finset.sum_mul,
    Complex.exp_sum]
  apply Finset.prod_congr rfl
  intro j _
  exact exp_phase_factor (N := N) (k j).val (spatialCoord c j).val

/-- The geometric sum over `ZMod N` read through `val`:
`sum_t omega ^ (t.val) = N` if `omega = 1`, else `0`, for
any `omega` with `omega ^ N = 1`. -/
theorem geom_sum_zmod (ω : ℂ) (hω : ω ^ N = 1) :
    (∑ t : ZMod N, ω ^ t.val) = if ω = 1 then (N : ℂ) else 0 := by
  have hsum : (∑ t : ZMod N, ω ^ t.val)
      = ∑ i : Fin N, ω ^ (i : ℕ) := by
    rw [Fin.sum_univ_eq_sum_range (fun i => ω ^ i) N]
    apply Finset.sum_bij (fun t _ => t.val)
    · intro t _
      exact Finset.mem_range.mpr (ZMod.val_lt t)
    · intro t₁ _ t₂ _ h
      exact ZMod.val_injective N h
    · intro i hi
      refine ⟨(i : ZMod N), Finset.mem_univ _, ?_⟩
      rw [ZMod.val_natCast_of_lt (Finset.mem_range.mp hi)]
    · intro t _
      rfl
  rw [hsum, Fin.sum_univ_eq_sum_range (fun i => ω ^ i) N]
  by_cases h1 : ω = 1
  · rw [if_pos h1, h1]
    simp
  · rw [if_neg h1]
    have hmul : (∑ i ∈ Finset.range N, ω ^ i) * (ω - 1) = 0 := by
      rw [geom_sum_mul, hω, sub_self]
    rcases mul_eq_zero.mp hmul with h | h
    · exact h
    · exfalso
      exact h1 (eq_of_sub_eq_zero h)

/-- The per-direction root factor
`omega_j = zetaRoot ^ (c_j) / zetaRoot ^ (c'_j)` is `1`
iff the `j`-coordinates of `c` and `c'` agree. -/
theorem rootFactor_eq_one_iff (c c' : LayerSite N) (j : Fin 3) :
    (zetaRoot (N := N)) ^ (spatialCoord c j).val
        / (zetaRoot (N := N)) ^ (spatialCoord c' j).val = 1
      ↔ spatialCoord c j = spatialCoord c' j := by
  have hne : (zetaRoot (N := N)) ^ (spatialCoord c' j).val ≠ 0 :=
    pow_ne_zero _ (Complex.exp_ne_zero _)
  rw [div_eq_one_iff_eq hne]
  constructor
  · intro h
    have hval := zetaRoot_prim.pow_inj (ZMod.val_lt _)
      (ZMod.val_lt _) h
    exact ZMod.val_injective N hval
  · intro h
    rw [h]

/-- The root factor is an `N`-th root of unity. -/
theorem rootFactor_pow_N (c c' : LayerSite N) (j : Fin 3) :
    ((zetaRoot (N := N)) ^ (spatialCoord c j).val
      / (zetaRoot (N := N)) ^ (spatialCoord c' j).val) ^ N = 1 := by
  rw [div_pow, ← pow_mul, ← pow_mul,
    Nat.mul_comm (spatialCoord c j).val N,
    Nat.mul_comm (spatialCoord c' j).val N,
    pow_mul, pow_mul, zetaRoot_pow_N, one_pow, one_pow]
  exact div_self (show (1 : ℂ) ≠ 0 from one_ne_zero)

/-- Factorization of the momentum sum of a product over
directions. -/
theorem sum_prod_factor (F : Fin 3 → ZMod N → ℂ) :
    (∑ k : Fin 3 → ZMod N, ∏ j, F j (k j))
      = ∏ j, ∑ t : ZMod N, F j t := by
  have hpi : Fintype.piFinset (fun _ : Fin 3 =>
      (Finset.univ : Finset (ZMod N))) = Finset.univ :=
    Finset.eq_univ_of_forall (fun k =>
      Fintype.mem_piFinset.mpr (fun j => Finset.mem_univ _))
  rw [← hpi, Finset.sum_prod_piFinset]

/-- Two layer sites agreeing in all spatial coordinates are
equal. -/
theorem layerSite_ext_of_coord {c c' : LayerSite N}
    (h : ∀ j : Fin 3, spatialCoord c j = spatialCoord c' j) :
    c = c' := by
  apply Subtype.ext
  funext μ
  rcases Fin.eq_zero_or_eq_succ μ with rfl | ⟨m, rfl⟩
  · apply ZMod.val_injective N
    rw [c.2, c'.2]
  · exact h m

/-- **Orthogonality of the cube characters**: the momentum
sum of `exp (i * (phase_k c - phase_k c'))` is `(N^3 : ℂ)`
if `c = c'`, else `0`. -/
theorem orth_sum (c c' : LayerSite N) :
    (∑ k : Fin 3 → ZMod N,
      Complex.exp (((sitePhase3 k c - sitePhase3 k c' : ℝ) : ℂ)
        * Complex.I))
      = if c = c' then ((N : ℂ)) ^ 3 else 0 := by
  have hfac : ∀ k : Fin 3 → ZMod N,
      Complex.exp (((sitePhase3 k c - sitePhase3 k c' : ℝ) : ℂ)
          * Complex.I)
        = ∏ j, ((zetaRoot (N := N)) ^ (spatialCoord c j).val
            / (zetaRoot (N := N)) ^ (spatialCoord c' j).val)
            ^ (k j).val := by
    intro k
    have hsub : ((sitePhase3 k c - sitePhase3 k c' : ℝ) : ℂ)
          * Complex.I
        = ((sitePhase3 k c : ℝ) : ℂ) * Complex.I
          + -(((sitePhase3 k c' : ℝ) : ℂ) * Complex.I) := by
      push_cast
      ring
    rw [hsub, Complex.exp_add, Complex.exp_neg, exp_sitePhase3,
      exp_sitePhase3, ← Finset.prod_inv_distrib,
      ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro j _
    rw [div_pow, div_eq_mul_inv, ← pow_mul, ← pow_mul,
      Nat.mul_comm (spatialCoord c j).val (k j).val,
      Nat.mul_comm (spatialCoord c' j).val (k j).val]
  rw [Finset.sum_congr rfl (fun k _ => hfac k),
    show (∑ k : Fin 3 → ZMod N, ∏ j,
        ((zetaRoot (N := N)) ^ (spatialCoord c j).val
          / (zetaRoot (N := N)) ^ (spatialCoord c' j).val)
          ^ (k j).val)
      = ∏ j, ∑ t : ZMod N,
          ((zetaRoot (N := N)) ^ (spatialCoord c j).val
            / (zetaRoot (N := N)) ^ (spatialCoord c' j).val)
            ^ t.val from sum_prod_factor
          (fun j t => ((zetaRoot (N := N)) ^ (spatialCoord c j).val
            / (zetaRoot (N := N)) ^ (spatialCoord c' j).val)
            ^ t.val)]
  by_cases hcc : c = c'
  · rw [if_pos hcc]
    subst hcc
    have h1 : ∀ j : Fin 3,
        (∑ t : ZMod N,
          ((zetaRoot (N := N)) ^ (spatialCoord c j).val
            / (zetaRoot (N := N)) ^ (spatialCoord c j).val)
            ^ t.val) = (N : ℂ) := by
      intro j
      have hω1 : (zetaRoot (N := N)) ^ (spatialCoord c j).val
          / (zetaRoot (N := N)) ^ (spatialCoord c j).val = 1 :=
        div_self (pow_ne_zero _ (Complex.exp_ne_zero _))
      rw [geom_sum_zmod _ (rootFactor_pow_N c c j), if_pos hω1]
    calc (∏ j, ∑ t : ZMod N,
          ((zetaRoot (N := N)) ^ (spatialCoord c j).val
            / (zetaRoot (N := N)) ^ (spatialCoord c j).val)
            ^ t.val)
        = ∏ _j : Fin 3, (N : ℂ) := Finset.prod_congr rfl
          (fun j _ => h1 j)
      _ = ((N : ℂ)) ^ 3 := by
          simp [Finset.prod_const, Finset.card_univ]
  · rw [if_neg hcc]
    have hne : ∃ j : Fin 3, spatialCoord c j ≠ spatialCoord c' j := by
      by_contra h
      push_neg at h
      exact hcc (layerSite_ext_of_coord h)
    obtain ⟨j, hj⟩ := hne
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    rw [geom_sum_zmod _ (rootFactor_pow_N c c' j),
      if_neg (fun h1 => hj ((rootFactor_eq_one_iff c c' j).mp h1))]

end Orthogonality

section Parseval

variable {N : ℕ} [NeZero N]

/-- `normSq` of a Fourier coefficient, as a conjugate
product. -/
theorem normSq_fhat (f : LayerSite N → ℝ) (k : Fin 3 → ZMod N) :
    (Complex.normSq (fhat f k) : ℂ)
      = fhat f k * (starRingEnd ℂ) (fhat f k) :=
  (Complex.mul_conj (fhat f k)).symm

/-- The conjugate of a Fourier coefficient is the Fourier
sum with the opposite phase sign. -/
theorem conj_fhat (f : LayerSite N → ℝ) (k : Fin 3 → ZMod N) :
    (starRingEnd ℂ) (fhat f k)
      = ∑ c, (f c : ℂ)
          * Complex.exp (((sitePhase3 k c : ℝ) : ℂ) * Complex.I) := by
  rw [fhat, map_sum]
  apply Finset.sum_congr rfl
  intro c _
  rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
  congr 1
  simp only [map_neg, map_mul, Complex.conj_ofReal,
    Complex.conj_I, neg_mul, mul_neg, neg_neg]

/-- **Parseval on the cube**: for a real site function `f`,
`sum_c (f c)^2 = (1 / (N^3 : R)) * sum_k normSq (fhat f k)`. -/
theorem parseval (f : LayerSite N → ℝ) :
    (∑ c, (f c) ^ 2)
      = (1 / ((N : ℝ) ^ 3)) * ∑ k, Complex.normSq (fhat f k) := by
  have hexp : ∀ k : Fin 3 → ZMod N,
      (fhat f k) * (∑ c', (f c' : ℂ)
          * Complex.exp (((sitePhase3 k c' : ℝ) : ℂ)
            * Complex.I))
        = ∑ c, ∑ c', ((f c * f c' : ℝ) : ℂ)
            * Complex.exp
              (((sitePhase3 k c' - sitePhase3 k c : ℝ) : ℂ)
                * Complex.I) := by
    intro k
    show (∑ c, (f c : ℂ)
        * Complex.exp ((-(sitePhase3 k c) : ℂ) * Complex.I))
        * (∑ c', (f c' : ℂ)
          * Complex.exp (((sitePhase3 k c' : ℝ) : ℂ)
            * Complex.I)) = _
    rw [Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro c _
    apply Finset.sum_congr rfl
    intro c' _
    have harr : ((f c : ℂ)
          * Complex.exp ((-(sitePhase3 k c) : ℂ) * Complex.I))
        * ((f c' : ℂ)
          * Complex.exp (((sitePhase3 k c' : ℝ) : ℂ)
            * Complex.I))
      = ((f c : ℂ) * (f c' : ℂ))
        * (Complex.exp ((-(sitePhase3 k c) : ℂ) * Complex.I)
          * Complex.exp (((sitePhase3 k c' : ℝ) : ℂ)
            * Complex.I)) := by ring
    rw [harr, ← Complex.exp_add]
    congr 1
    · push_cast
      ring
    · congr 1
      push_cast
      ring
  have hstep : ∀ k : Fin 3 → ZMod N,
      (Complex.normSq (fhat f k) : ℂ)
        = ∑ c, ∑ c', ((f c * f c' : ℝ) : ℂ)
            * Complex.exp
              (((sitePhase3 k c' - sitePhase3 k c : ℝ) : ℂ)
                * Complex.I) := by
    intro k
    rw [normSq_fhat, conj_fhat]
    exact hexp k
  have horth : ∀ c c' : LayerSite N,
      (∑ k : Fin 3 → ZMod N, ((f c * f c' : ℝ) : ℂ)
        * Complex.exp (((sitePhase3 k c' - sitePhase3 k c : ℝ) : ℂ)
            * Complex.I))
      = if c' = c then ((N : ℂ)) ^ 3 * ((f c * f c' : ℝ) : ℂ)
        else 0 := by
    intro c c'
    rw [← Finset.mul_sum, orth_sum]
    by_cases h : c' = c
    · rw [if_pos h, if_pos h]
      ring
    · rw [if_neg h, if_neg h, mul_zero]
  have hswap : (∑ k : Fin 3 → ZMod N, ∑ c, ∑ c',
        ((f c * f c' : ℝ) : ℂ)
          * Complex.exp (((sitePhase3 k c' - sitePhase3 k c : ℝ) : ℂ)
              * Complex.I))
      = ∑ c, ∑ c', ∑ k : Fin 3 → ZMod N,
          ((f c * f c' : ℝ) : ℂ)
            * Complex.exp
              (((sitePhase3 k c' - sitePhase3 k c : ℝ) : ℂ)
                * Complex.I) :=
    (Finset.sum_comm (f := fun k c => ∑ c',
      ((f c * f c' : ℝ) : ℂ)
        * Complex.exp (((sitePhase3 k c' - sitePhase3 k c : ℝ) : ℂ)
            * Complex.I))).trans
      (Finset.sum_congr rfl (fun c _ =>
        Finset.sum_comm (f := fun k c' =>
          ((f c * f c' : ℝ) : ℂ)
            * Complex.exp
              (((sitePhase3 k c' - sitePhase3 k c : ℝ) : ℂ)
                * Complex.I))))
  have hkey : (∑ k, (Complex.normSq (fhat f k) : ℂ))
      = ((N : ℂ)) ^ 3 * ∑ c, (((f c) ^ 2 : ℝ) : ℂ) := by
    rw [Finset.sum_congr rfl (fun k _ => hstep k), hswap]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c _
    rw [Finset.sum_congr rfl (fun c' _ => horth c c'),
      Finset.sum_eq_single c]
    · rw [if_pos rfl]
      push_cast
      ring
    · intro c' _ hc'
      rw [if_neg hc']
    · intro h
      exact absurd (Finset.mem_univ c) h
  have hreal : (∑ k, Complex.normSq (fhat f k))
      = ((N : ℝ)) ^ 3 * ∑ c, (f c) ^ 2 := by
    have hcast : (∑ k, (Complex.normSq (fhat f k) : ℂ))
        = ((∑ k, Complex.normSq (fhat f k) : ℝ) : ℂ) := by
      rw [Complex.ofReal_sum]
    have hcast2 : ((N : ℂ)) ^ 3 * ∑ c, (((f c) ^ 2 : ℝ) : ℂ)
        = ((((N : ℝ)) ^ 3 * ∑ c, (f c) ^ 2 : ℝ) : ℂ) := by
      push_cast
      rfl
    rw [hcast, hcast2] at hkey
    exact_mod_cast hkey
  have hNpos : (0 : ℝ) < ((N : ℝ)) ^ 3 := by
    have hN : (0 : ℝ) < (N : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
    positivity
  have hN3 : ((N : ℝ)) ^ 3 ≠ 0 := ne_of_gt hNpos
  have hcan : (1 / ((N : ℝ) ^ 3))
      * (((N : ℝ) ^ 3) * ∑ c, (f c) ^ 2) = ∑ c, (f c) ^ 2 := by
    rw [one_div, ← mul_assoc, inv_mul_cancel₀ hN3, one_mul]
  rw [← hcan, hreal]

end Parseval

section ShiftMultipliers

variable {N : ℕ} [NeZero N]

/-- The cube phase is the MAX-3 site phase of the extended
momentum `Fin.cons 0 k`. -/
theorem sitePhase3_eq (k : Fin 3 → ZMod N) (c : LayerSite N) :
    sitePhase3 k c = sitePhase (Fin.cons (0 : ZMod N) k) c := by
  rw [sitePhase, Fin.sum_univ_succ]
  have h0 : (2 * modePhase (Fin.cons (0 : ZMod N) k) 0)
      * (((c.1 0).val : ℝ)) = 0 := by
    simp [modePhase]
  rw [h0, zero_add, sitePhase3]
  apply Finset.sum_congr rfl
  intro j _
  rw [modePhase_succ]
  unfold spatialCoord
  ring

/-- `exp (-i x)` in real form. -/
theorem exp_neg_phase (x : ℝ) :
    Complex.exp ((-(x : ℂ)) * Complex.I)
      = (Real.cos x : ℂ) - (Real.sin x : ℂ) * Complex.I := by
  have h : (-(x : ℂ)) * Complex.I = ((-(x) : ℝ) : ℂ) * Complex.I := by
    simp
  rw [h, Complex.exp_ofReal_mul_I]
  simp only [Real.cos_neg, Real.sin_neg, Complex.ofReal_neg,
    neg_mul, sub_eq_add_neg]

/-- Cosine of the cube phase after an unshift. -/
theorem cos_phase3_unshift (hN : 2 ≤ N) (k : Fin 3 → ZMod N)
    (μ : Fin 4) (hμ : μ ≠ 0) (c : LayerSite N) :
    Real.cos (sitePhase3 k (layerUnshift μ hμ c))
      = Real.cos (sitePhase3 k c
          - 2 * modePhase (Fin.cons (0 : ZMod N) k) μ) := by
  have h := cos_sitePhase_layerUnshift hN
    (Fin.cons (0 : ZMod N) k) μ hμ c 0
  simp only [add_zero] at h
  rwa [← sitePhase3_eq, ← sitePhase3_eq] at h

/-- Sine of the cube phase after an unshift. -/
theorem sin_phase3_unshift (hN : 2 ≤ N) (k : Fin 3 → ZMod N)
    (μ : Fin 4) (hμ : μ ≠ 0) (c : LayerSite N) :
    Real.sin (sitePhase3 k (layerUnshift μ hμ c))
      = Real.sin (sitePhase3 k c
          - 2 * modePhase (Fin.cons (0 : ZMod N) k) μ) := by
  have h := sin_sitePhase_layerUnshift hN
    (Fin.cons (0 : ZMod N) k) μ hμ c 0
  simp only [add_zero] at h
  rwa [← sitePhase3_eq, ← sitePhase3_eq] at h

/-- Cosine of the cube phase after a shift. -/
theorem cos_phase3_shift (hN : 2 ≤ N) (k : Fin 3 → ZMod N)
    (μ : Fin 4) (hμ : μ ≠ 0) (c : LayerSite N) :
    Real.cos (sitePhase3 k (layerShift μ hμ c))
      = Real.cos (sitePhase3 k c
          + 2 * modePhase (Fin.cons (0 : ZMod N) k) μ) := by
  have h := cos_sitePhase_layerShift hN
    (Fin.cons (0 : ZMod N) k) μ hμ c 0
  simp only [add_zero] at h
  rwa [← sitePhase3_eq, ← sitePhase3_eq] at h

/-- Sine of the cube phase after a shift. -/
theorem sin_phase3_shift (hN : 2 ≤ N) (k : Fin 3 → ZMod N)
    (μ : Fin 4) (hμ : μ ≠ 0) (c : LayerSite N) :
    Real.sin (sitePhase3 k (layerShift μ hμ c))
      = Real.sin (sitePhase3 k c
          + 2 * modePhase (Fin.cons (0 : ZMod N) k) μ) := by
  have h := sin_sitePhase_layerShift hN
    (Fin.cons (0 : ZMod N) k) μ hμ c 0
  simp only [add_zero] at h
  rwa [← sitePhase3_eq, ← sitePhase3_eq] at h

/-- The exponential factor of an unshifted phase:
`exp (-i * phase (c - e_mu)) = u_mu * exp (-i * phase c)`. -/
theorem exp_neg_phase3_unshift (hN : 2 ≤ N) (k : Fin 3 → ZMod N)
    (μ : Fin 4) (hμ : μ ≠ 0) (c : LayerSite N) :
    Complex.exp ((-(sitePhase3 k (layerUnshift μ hμ c)) : ℂ)
        * Complex.I)
      = shiftMult k μ
        * Complex.exp ((-(sitePhase3 k c) : ℂ) * Complex.I) := by
  have hfact : shiftMult k μ
      = (Real.cos (2 * modePhase (Fin.cons (0 : ZMod N) k) μ) : ℂ)
        + (Real.sin (2 * modePhase (Fin.cons (0 : ZMod N) k) μ) : ℂ)
          * Complex.I := by
    rw [shiftMult, Complex.exp_ofReal_mul_I]
  rw [exp_neg_phase, cos_phase3_unshift hN k μ hμ c,
    sin_phase3_unshift hN k μ hμ c, hfact, exp_neg_phase,
    Real.cos_sub, Real.sin_sub]
  apply Complex.ext
  · simp only [Complex.mul_re, Complex.mul_im, Complex.sub_re,
      Complex.sub_im, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im]
    ring
  · simp only [Complex.mul_re, Complex.mul_im, Complex.sub_re,
      Complex.sub_im, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im]
    ring

/-- The conjugate shift multiplier is `exp (-i * phi)`. -/
theorem conj_shiftMult (k : Fin 3 → ZMod N) (μ : Fin 4) :
    (starRingEnd ℂ) (shiftMult k μ)
      = Complex.exp
          (-(((2 * modePhase (Fin.cons (0 : ZMod N) k) μ : ℝ)) : ℂ)
            * Complex.I) := by
  rw [shiftMult, ← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  rw [mul_neg, ← neg_mul]

/-- The exponential factor of a shifted phase:
`exp (-i * phase (c + e_mu)) = conj (u_mu) * exp (-i * phase c)`. -/
theorem exp_neg_phase3_shift (hN : 2 ≤ N) (k : Fin 3 → ZMod N)
    (μ : Fin 4) (hμ : μ ≠ 0) (c : LayerSite N) :
    Complex.exp ((-(sitePhase3 k (layerShift μ hμ c)) : ℂ)
        * Complex.I)
      = (starRingEnd ℂ) (shiftMult k μ)
        * Complex.exp ((-(sitePhase3 k c) : ℂ) * Complex.I) := by
  have hconj : (starRingEnd ℂ) (shiftMult k μ)
      = (Real.cos (2 * modePhase (Fin.cons (0 : ZMod N) k) μ) : ℂ)
        - (Real.sin (2 * modePhase (Fin.cons (0 : ZMod N) k) μ) : ℂ)
          * Complex.I := by
    rw [conj_shiftMult]
    exact exp_neg_phase _
  rw [exp_neg_phase, cos_phase3_shift hN k μ hμ c,
    sin_phase3_shift hN k μ hμ c, hconj, exp_neg_phase,
    Real.cos_add, Real.sin_add]
  apply Complex.ext
  · simp only [Complex.mul_re, Complex.mul_im, Complex.sub_re,
      Complex.sub_im, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im]
    ring
  · simp only [Complex.mul_re, Complex.mul_im, Complex.sub_re,
      Complex.sub_im, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im]
    ring

/-- Sum invariance under a layer shift, for complex-valued
functions (the MAX-3 `sum_layerShift` is real-valued). -/
theorem sum_layerShiftC (μ : Fin 4) (hμ : μ ≠ 0)
    (F : LayerSite N → ℂ) :
    (∑ c, F (layerShift μ hμ c)) = ∑ c, F c :=
  Fintype.sum_bijective _ (bijective_layerShift μ hμ) _ _
    (fun c => rfl)

/-- Sum invariance under a layer unshift, complex-valued. -/
theorem sum_layerUnshiftC (μ : Fin 4) (hμ : μ ≠ 0)
    (F : LayerSite N → ℂ) :
    (∑ c, F (layerUnshift μ hμ c)) = ∑ c, F c :=
  Fintype.sum_bijective _ (bijective_layerUnshift μ hμ) _ _
    (fun c => rfl)

/-- Fourier coefficient of a forward-shifted site function. -/
theorem fhat_shift (hN : 2 ≤ N) (f : LayerSite N → ℝ)
    (k : Fin 3 → ZMod N) (μ : Fin 4) (hμ : μ ≠ 0) :
    fhat (fun c => f (layerShift μ hμ c)) k
      = shiftMult k μ * fhat f k := by
  have hsum : (∑ c, (f (layerShift μ hμ c) : ℂ)
        * Complex.exp ((-(sitePhase3 k c) : ℂ) * Complex.I))
      = ∑ c, (f c : ℂ) * (shiftMult k μ
          * Complex.exp ((-(sitePhase3 k c) : ℂ) * Complex.I)) := by
    calc (∑ c, (f (layerShift μ hμ c) : ℂ)
          * Complex.exp ((-(sitePhase3 k c) : ℂ) * Complex.I))
        = ∑ c, (f (layerShift μ hμ c) : ℂ)
            * Complex.exp
              ((-(sitePhase3 k (layerUnshift μ hμ
                  (layerShift μ hμ c))) : ℂ) * Complex.I) :=
          Finset.sum_congr rfl (fun c _ => by
            rw [layerUnshift_layerShift])
      _ = ∑ c, (f c : ℂ)
            * Complex.exp
              ((-(sitePhase3 k (layerUnshift μ hμ c)) : ℂ)
                * Complex.I) :=
          sum_layerShiftC μ hμ (fun d => (f d : ℂ)
            * Complex.exp
              ((-(sitePhase3 k (layerUnshift μ hμ d)) : ℂ)
                * Complex.I))
      _ = ∑ c, (f c : ℂ) * (shiftMult k μ
            * Complex.exp ((-(sitePhase3 k c) : ℂ)
              * Complex.I)) :=
          Finset.sum_congr rfl (fun c _ => by
            rw [exp_neg_phase3_unshift hN k μ hμ c])
  unfold fhat
  rw [hsum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  ring

/-- Fourier coefficient of a backward-shifted site function. -/
theorem fhat_unshift (hN : 2 ≤ N) (f : LayerSite N → ℝ)
    (k : Fin 3 → ZMod N) (μ : Fin 4) (hμ : μ ≠ 0) :
    fhat (fun c => f (layerUnshift μ hμ c)) k
      = (starRingEnd ℂ) (shiftMult k μ) * fhat f k := by
  have hsum : (∑ c, (f (layerUnshift μ hμ c) : ℂ)
        * Complex.exp ((-(sitePhase3 k c) : ℂ) * Complex.I))
      = ∑ c, (f c : ℂ) * ((starRingEnd ℂ) (shiftMult k μ)
          * Complex.exp ((-(sitePhase3 k c) : ℂ) * Complex.I)) := by
    calc (∑ c, (f (layerUnshift μ hμ c) : ℂ)
          * Complex.exp ((-(sitePhase3 k c) : ℂ) * Complex.I))
        = ∑ c, (f (layerUnshift μ hμ c) : ℂ)
            * Complex.exp
              ((-(sitePhase3 k (layerShift μ hμ
                  (layerUnshift μ hμ c))) : ℂ) * Complex.I) :=
          Finset.sum_congr rfl (fun c _ => by
            rw [layerShift_layerUnshift])
      _ = ∑ c, (f c : ℂ)
            * Complex.exp
              ((-(sitePhase3 k (layerShift μ hμ c)) : ℂ)
                * Complex.I) :=
          sum_layerUnshiftC μ hμ (fun d => (f d : ℂ)
            * Complex.exp
              ((-(sitePhase3 k (layerShift μ hμ d)) : ℂ)
                * Complex.I))
      _ = ∑ c, (f c : ℂ) * ((starRingEnd ℂ) (shiftMult k μ)
            * Complex.exp ((-(sitePhase3 k c) : ℂ)
              * Complex.I)) :=
          Finset.sum_congr rfl (fun c _ => by
            rw [exp_neg_phase3_shift hN k μ hμ c])
  unfold fhat
  rw [hsum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  ring

/-- Fourier coefficients are additive in the function. -/
theorem fhat_add (f g : LayerSite N → ℝ) (k : Fin 3 → ZMod N) :
    fhat (fun c => f c + g c) k = fhat f k + fhat g k := by
  unfold fhat
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro c _
  push_cast
  ring

/-- Fourier coefficients are subtractive in the function. -/
theorem fhat_sub (f g : LayerSite N → ℝ) (k : Fin 3 → ZMod N) :
    fhat (fun c => f c - g c) k = fhat f k - fhat g k := by
  unfold fhat
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro c _
  push_cast
  ring

/-- The Fourier coefficient of the zero function vanishes. -/
theorem fhat_eq_zero {f : LayerSite N → ℝ}
    (hf : ∀ c, f c = 0) (k : Fin 3 → ZMod N) :
    fhat f k = 0 := by
  unfold fhat
  simp [hf]

/-- Fourier coefficients commute with finite sums of site
functions. -/
theorem fhat_sum {ι : Type*} [Fintype ι] (F : ι → LayerSite N → ℝ)
    (k : Fin 3 → ZMod N) :
    fhat (fun c => ∑ i, F i c) k = ∑ i, fhat (F i) k := by
  have hterm : ∀ c : LayerSite N,
      ((∑ i, F i c : ℝ) : ℂ)
        * Complex.exp ((-(sitePhase3 k c) : ℂ) * Complex.I)
      = ∑ i, (F i c : ℂ)
          * Complex.exp ((-(sitePhase3 k c) : ℂ) * Complex.I) := by
    intro c
    rw [Complex.ofReal_sum, Finset.sum_mul]
  show (∑ c, ((∑ i, F i c : ℝ) : ℂ)
      * Complex.exp ((-(sitePhase3 k c) : ℂ) * Complex.I))
    = ∑ i, fhat (F i) k
  rw [Finset.sum_congr rfl (fun c _ => hterm c), Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rfl

/-- The cube phase at zero momentum vanishes. -/
theorem sitePhase3_zero (c : LayerSite N) :
    sitePhase3 (0 : Fin 3 → ZMod N) c = 0 := by
  apply Finset.sum_eq_zero
  intro j _
  simp [sitePhase3]

/-- The Fourier coefficient at zero momentum is the total
mass of the function. -/
theorem fhat_zero_mom (f : LayerSite N → ℝ) :
    fhat f (0 : Fin 3 → ZMod N) = ((∑ c, f c : ℝ) : ℂ) := by
  unfold fhat
  simp only [sitePhase3_zero, neg_zero, Complex.ofReal_zero,
    zero_mul, Complex.exp_zero, mul_one]
  rw [← Complex.ofReal_sum]

/-- The shift multiplier at direction `0` is `1`. -/
theorem shiftMult_zero (k : Fin 3 → ZMod N) :
    shiftMult k 0 = 1 := by
  simp [shiftMult, modePhase]

/-- The multiplier modulus: `|u_mu - 1|^2
= 4 * sin^2 (half-angle_mu)`. -/
theorem normSq_shiftMult_sub_one (k : Fin 3 → ZMod N) (μ : Fin 4) :
    Complex.normSq (shiftMult k μ - 1)
      = 4 * (Real.sin (modePhase (Fin.cons (0 : ZMod N) k) μ)) ^ 2 := by
  have hmp : shiftMult k μ
      = (Real.cos (2 * modePhase (Fin.cons (0 : ZMod N) k) μ) : ℂ)
        + (Real.sin (2 * modePhase (Fin.cons (0 : ZMod N) k) μ) : ℂ)
          * Complex.I := by
    rw [shiftMult, Complex.exp_ofReal_mul_I]
  have h := one_sub_cos_eq (2 * modePhase (Fin.cons (0 : ZMod N) k) μ)
  rw [show (2 * modePhase (Fin.cons (0 : ZMod N) k) μ) / 2
      = modePhase (Fin.cons (0 : ZMod N) k) μ by ring] at h
  rw [hmp]
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, Complex.one_re, Complex.one_im,
    mul_zero, zero_mul, mul_one, sub_zero, add_zero, zero_add]
  nlinarith [Real.cos_sq_add_sin_sq
    (2 * modePhase (Fin.cons (0 : ZMod N) k) μ), h]

/-- The Fourier coefficient of a plaquette function:
`A_{plaq_{mu nu}} = (u_mu - 1) * A_nu - (u_nu - 1) * A_mu`. -/
theorem fhat_plaq (hN : 2 ≤ N) (θ : linkAngle N)
    (k : Fin 3 → ZMod N) (μ ν : Fin 4) (hμ : μ ≠ 0) (hν : ν ≠ 0) :
    fhat (plaqSite θ μ ν) k
      = (shiftMult k μ - 1) * fhat (linkComp θ ν) k
        - (shiftMult k ν - 1) * fhat (linkComp θ μ) k := by
  have hsite : plaqSite θ μ ν
      = fun c => ((linkComp θ ν (layerShift μ hμ c)
          - linkComp θ ν c)
        - (linkComp θ μ (layerShift ν hν c)
          - linkComp θ μ c)) := by
    funext c
    simp only [plaqSite, plaqForm, linkComp,
      shiftLinkVal_of_ne θ c hμ ν, shiftLinkVal_of_ne θ c hν μ]
    ring
  rw [hsite, fhat_sub, fhat_sub, fhat_sub,
    fhat_shift hN _ _ _ hμ, fhat_shift hN _ _ _ hν]
  ring

/-- One direction's contribution to the Fourier coefficient
of the divergence. -/
theorem fhat_div_term (hN : 2 ≤ N) (θ : linkAngle N)
    (k : Fin 3 → ZMod N) (μ : Fin 4) :
    fhat (fun c => if h : μ ≠ 0 then
        linkVal θ c μ - linkVal θ (layerUnshift μ h c) μ
      else 0) k
      = (1 - (starRingEnd ℂ) (shiftMult k μ))
        * fhat (linkComp θ μ) k := by
  by_cases hμ : μ = 0
  · subst hμ
    have hfun : (fun c => if h : (0 : Fin 4) ≠ 0 then
          linkVal θ c 0 - linkVal θ (layerUnshift 0 h c) 0
        else (0 : ℝ)) = fun _ => 0 := by
      funext c
      exact dif_neg (fun h => h rfl)
    have hz : fhat (fun _ : LayerSite N => (0 : ℝ)) k = 0 :=
      fhat_eq_zero (fun c => rfl) k
    rw [hfun, shiftMult_zero, hz]
    simp
  · have hfun : (fun c => if h : μ ≠ 0 then
          linkVal θ c μ - linkVal θ (layerUnshift μ h c) μ
        else (0 : ℝ))
        = fun c => linkComp θ μ c
          - linkComp θ μ (layerUnshift μ hμ c) := by
      funext c
      rw [dif_pos hμ]
      rfl
    rw [hfun, fhat_sub, fhat_unshift hN _ _ _ hμ]
    ring

/-- The Fourier coefficient of the divergence:
`A_{div} = sum_mu (1 - conj (u_mu)) * A_mu`. -/
theorem fhat_maxwellDiv (hN : 2 ≤ N) (θ : linkAngle N)
    (k : Fin 3 → ZMod N) :
    fhat (maxwellDiv θ) k
      = ∑ μ, (1 - (starRingEnd ℂ) (shiftMult k μ))
          * fhat (linkComp θ μ) k := by
  have hfun : maxwellDiv θ
      = fun c => ∑ μ, (if h : μ ≠ 0 then
          linkVal θ c μ - linkVal θ (layerUnshift μ h c) μ
        else (0 : ℝ)) := rfl
  rw [hfun, fhat_sum]
  apply Finset.sum_congr rfl
  intro μ _
  exact fhat_div_term hN θ k μ

end ShiftMultipliers

section LagrangeIdentity

variable {N : ℕ} [NeZero N]

/-- The Lagrange identity on `Fin 4`: the sum of the six squared
plaquette determinants is the product of the norms minus the
squared divergence defect. -/
theorem lagrange_four (x y : Fin 4 → ℂ) :
    (Complex.normSq (x 0 * y 1 - x 1 * y 0)
      + Complex.normSq (x 0 * y 2 - x 2 * y 0)
      + Complex.normSq (x 0 * y 3 - x 3 * y 0)
      + Complex.normSq (x 1 * y 2 - x 2 * y 1)
      + Complex.normSq (x 1 * y 3 - x 3 * y 1)
      + Complex.normSq (x 2 * y 3 - x 3 * y 2))
    = (∑ μ, Complex.normSq (x μ)) * (∑ μ, Complex.normSq (y μ))
      - Complex.normSq (∑ μ, (starRingEnd ℂ) (x μ) * y μ) := by
  apply Complex.ofReal_injective
  rw [Fin.sum_univ_four, Fin.sum_univ_four, Fin.sum_univ_four]
  push_cast
  simp only [← Complex.mul_conj, map_add, map_sub, map_mul,
    Complex.conj_conj, starRingEnd_self_apply]
  ring

/-- The Lagrange identity in the pair-sum form produced by
`sum_allPlaqData`, for vectors vanishing in the `0` component. -/
theorem lagrange_pair_form (x y : Fin 4 → ℂ) (hx : x 0 = 0)
    (hy : y 0 = 0) :
    (∑ μ, ∑ ν, (if μ ≠ 0 ∧ ν ≠ 0 ∧ μ < ν
        then Complex.normSq (x μ * y ν - x ν * y μ) else 0))
    = (∑ μ, Complex.normSq (x μ)) * (∑ μ, Complex.normSq (y μ))
      - Complex.normSq (∑ μ, (starRingEnd ℂ) (x μ) * y μ) := by
  have hA : (∑ μ, ∑ ν, (if μ ≠ 0 ∧ ν ≠ 0 ∧ μ < ν
        then Complex.normSq (x μ * y ν - x ν * y μ) else 0))
      = ∑ μ, ∑ ν, (if μ < ν
        then Complex.normSq (x μ * y ν - x ν * y μ) else 0) := by
    apply Finset.sum_congr rfl
    intro μ _
    apply Finset.sum_congr rfl
    intro ν _
    by_cases hlt : μ < ν
    · by_cases hμ : μ = 0
      · subst hμ
        have hterm : x 0 * y ν - x ν * y 0 = 0 := by
          rw [hx, hy]
          simp
        rw [if_neg (fun h => h.1 rfl), if_pos hlt, hterm]
        exact (map_zero Complex.normSq).symm
      · have hν : ν ≠ 0 := by
          rintro rfl
          rw [Fin.lt_def] at hlt
          exact Nat.not_lt_zero _ hlt
        rw [if_pos ⟨hμ, hν, hlt⟩, if_pos hlt]
    · rw [if_neg (fun h => hlt h.2.2), if_neg hlt]
  rw [hA]
  have hB : (∑ μ, ∑ ν, (if μ < ν
        then Complex.normSq (x μ * y ν - x ν * y μ) else 0))
      = Complex.normSq (x 0 * y 1 - x 1 * y 0)
        + Complex.normSq (x 0 * y 2 - x 2 * y 0)
        + Complex.normSq (x 0 * y 3 - x 3 * y 0)
        + Complex.normSq (x 1 * y 2 - x 2 * y 1)
        + Complex.normSq (x 1 * y 3 - x 3 * y 1)
        + Complex.normSq (x 2 * y 3 - x 3 * y 2) := by
    rw [Fin.sum_univ_succ, Fin.sum_univ_three]
    simp only [Fin.sum_univ_succ, Fin.sum_univ_three]
    simp
    ring
  rw [hB]
  exact lagrange_four x y

end LagrangeIdentity

section Assembly

variable {N : ℕ} [NeZero N]

/-- A sum over the nonzero directions as a subtype equals
the `dite` sum over `Fin 4`. -/
theorem sum_subtype_ne (G : (μ : Fin 4) → μ ≠ 0 → ℝ) :
    (∑ μ : {μ : Fin 4 // μ ≠ 0}, G μ.1 μ.2)
      = ∑ μ : Fin 4, (if h : μ ≠ 0 then G μ h else 0) := by
  classical
  have e1 : (∑ μ : {μ : Fin 4 // μ ≠ 0}, G μ.1 μ.2)
      = ∑ μ : {μ : Fin 4 // μ ≠ 0},
          (if h : μ.1 ≠ 0 then G μ.1 h else 0) := by
    apply Finset.sum_congr rfl
    intro μ _
    exact (dif_pos μ.2).symm
  have e2 : (∑ μ : {μ : Fin 4 // μ ≠ 0},
        (if h : μ.1 ≠ 0 then G μ.1 h else 0))
      = ∑ μ ∈ Finset.univ.filter (· ≠ 0),
        (if h : μ ≠ 0 then G μ h else 0) :=
    (Finset.sum_subtype (Finset.univ.filter (· ≠ 0))
      (by intro x; simp)
      (fun μ => if h : μ ≠ 0 then G μ h else 0)).symm
  rw [e1, e2, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro μ _
  by_cases hμ : μ ≠ 0
  · rw [if_pos hμ]
  · rw [if_neg hμ, dif_neg hμ]

/-- Every layer link is the layer link of its tail in its
own direction. -/
theorem layerLinkOf_linkTail (ℓ : LayerLink N) :
    layerLinkOf (linkTail ℓ) ℓ.1.2 ℓ.2.2 = ℓ :=
  Subtype.ext (Prod.ext rfl rfl)

/-- The tail of an explicit layer link is its base site. -/
theorem linkTail_layerLinkOf (c : LayerSite N) (μ : Fin 4)
    (hμ : μ ≠ 0) :
    linkTail (layerLinkOf c μ hμ) = c :=
  Subtype.ext rfl

/-- The head of an explicit layer link is the shifted base
site. -/
theorem linkHead_layerLinkOf (c : LayerSite N) (μ : Fin 4)
    (hμ : μ ≠ 0) :
    linkHead (layerLinkOf c μ hμ) = layerShift μ hμ c := rfl

/-- Layer links are base sites paired with nonzero
directions. -/
def linkSigmaEquiv :
    LayerLink N ≃ (Σ _c : LayerSite N, {μ : Fin 4 // μ ≠ 0}) where
  toFun ℓ := ⟨linkTail ℓ, ⟨ℓ.1.2, ℓ.2.2⟩⟩
  invFun p := layerLinkOf p.1 p.2.1 p.2.2
  left_inv ℓ := layerLinkOf_linkTail ℓ
  right_inv p := by
    apply Sigma.ext
    · exact linkTail_layerLinkOf p.1 p.2.1 p.2.2
    · exact heq_of_eq (Subtype.ext rfl)

/-- **Link sum decomposition**: a sum over layer links is a
sum over base sites and directions. -/
theorem sum_link (G : LayerLink N → ℝ) :
    (∑ ℓ, G ℓ) = ∑ c, ∑ μ, (if h : μ ≠ 0 then
      G (layerLinkOf c μ h) else 0) := by
  classical
  have step1 : (∑ ℓ, G ℓ)
      = ∑ c, ∑ μ : {μ : Fin 4 // μ ≠ 0},
          G (layerLinkOf c μ.1 μ.2) := by
    rw [← Fintype.sum_sigma']
    exact (Equiv.sum_comp linkSigmaEquiv.symm G).symm
  rw [step1]
  apply Finset.sum_congr rfl
  intro c _
  exact sum_subtype_ne (fun μ h => G (layerLinkOf c μ h))

/-- The norm of a link angle, decomposed over sites and
directions. -/
theorem sum_link_sq (θ : linkAngle N) :
    (∑ ℓ, (θ ℓ) ^ 2) = ∑ c, ∑ μ, (linkVal θ c μ) ^ 2 := by
  rw [sum_link]
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro μ _
  by_cases hμ : μ = 0
  · subst hμ
    rw [dif_neg (fun h : (0 : Fin 4) ≠ 0 => h rfl), linkVal_zero]
    simp
  · rw [dif_pos hμ, linkVal_of_ne _ _ hμ]

/-- The inner product of two link angles, decomposed over
sites and directions. -/
theorem sum_link_inner (η θ : linkAngle N) :
    (∑ ℓ, η ℓ * θ ℓ)
      = ∑ c, ∑ μ, linkVal η c μ * linkVal θ c μ := by
  rw [sum_link (fun ℓ => η ℓ * θ ℓ)]
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro μ _
  by_cases hμ : μ = 0
  · subst hμ
    rw [dif_neg (fun h : (0 : Fin 4) ≠ 0 => h rfl),
      linkVal_zero, linkVal_zero, mul_zero]
  · rw [dif_pos hμ, linkVal_of_ne _ _ hμ, linkVal_of_ne _ _ hμ]

/-- The divergence, as a sum over the three spatial
directions. -/
theorem maxwellDiv_eq_sum_succ (θ : linkAngle N)
    (s : LayerSite N) :
    maxwellDiv θ s = ∑ j : Fin 3,
      (linkVal θ s (Fin.succ j)
        - linkVal θ (layerUnshift (Fin.succ j)
            (Fin.succ_ne_zero j) s) (Fin.succ j)) := by
  unfold maxwellDiv
  rw [Fin.sum_univ_succ,
    dif_neg (fun h : (0 : Fin 4) ≠ 0 => h rfl), zero_add]
  apply Finset.sum_congr rfl
  intro j _
  rw [dif_pos (Fin.succ_ne_zero j)]

/-- **Orthogonality**: an eigenvector of eigenvalue `μ ≠ 0`
is orthogonal to every kernel element. -/
theorem orth_of_kernel {θ η : linkAngle N} {μ : ℝ}
    (hμ : μ ≠ 0) (hη : maxwellOp N η = 0)
    (hθ : maxwellOp N θ = μ • θ) :
    (∑ ℓ, η ℓ * θ ℓ) = 0 := by
  have hsymm := maxwellOp_form_symm η θ
  rw [hθ, hη] at hsymm
  simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply, mul_zero,
    Finset.sum_const_zero] at hsymm
  have hfactor : (∑ ℓ, η ℓ * (μ * θ ℓ)) = μ * ∑ ℓ, η ℓ * θ ℓ := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ℓ _
    ring
  rw [hfactor] at hsymm
  exact (mul_eq_zero.mp hsymm).resolve_left hμ

/-- **Divergence of an eigenvector**: orthogonality against
gauge modes forces `maxwellDiv θ = 0` at every site. -/
theorem maxwellDiv_of_eigen {θ : linkAngle N} {μ : ℝ}
    (hμ : μ ≠ 0) (hθ : maxwellOp N θ = μ • θ) :
    ∀ s, maxwellDiv θ s = 0 := by
  intro s
  classical
  set ψ : LayerSite N → ℝ := fun c => if c = s then 1 else 0
    with hψ
  have horth := orth_of_kernel hμ (maxwellOp_gaugeAngle ψ) hθ
  rw [sum_link_inner] at horth
  have hper : ∀ μ : Fin 4, (∑ c, linkVal (gaugeAngle ψ) c μ
        * linkVal θ c μ)
      = (if h : μ ≠ 0 then linkVal θ (layerUnshift μ h s) μ
          - linkVal θ s μ else 0) := by
    intro μ
    by_cases hμ : μ = 0
    · subst hμ
      rw [dif_neg (fun h : (0 : Fin 4) ≠ 0 => h rfl)]
      apply Finset.sum_eq_zero
      intro c _
      rw [linkVal_zero, zero_mul]
    · have hval : ∀ c, linkVal (gaugeAngle ψ) c μ
          = ψ (layerShift μ hμ c) - ψ c := by
        intro c
        rw [linkVal_of_ne _ _ hμ]
        show ψ (linkHead (layerLinkOf c μ hμ))
            - ψ (linkTail (layerLinkOf c μ hμ)) = _
        rw [linkHead_layerLinkOf, linkTail_layerLinkOf]
      have hsum : (∑ c, linkVal (gaugeAngle ψ) c μ
            * linkVal θ c μ)
          = (∑ c, ψ (layerShift μ hμ c) * linkVal θ c μ)
            - ∑ c, ψ c * linkVal θ c μ := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro c _
        rw [hval c]
        ring
      have e1 : (∑ c, ψ c * linkVal θ c μ)
          = linkVal θ s μ := by
        have hs : ψ s * linkVal θ s μ = linkVal θ s μ := by
          show (if s = s then (1 : ℝ) else 0)
              * linkVal θ s μ = _
          rw [if_pos rfl, one_mul]
        rw [← hs]
        apply Finset.sum_eq_single s
        · intro b _ hb
          show ψ b * linkVal θ b μ = 0
          rw [show ψ b = 0 from if_neg hb]
          exact zero_mul _
        · intro hmem
          exact absurd (Finset.mem_univ s) hmem
      have e2 : (∑ c, ψ (layerShift μ hμ c) * linkVal θ c μ)
          = linkVal θ (layerUnshift μ hμ s) μ := by
        have hshift : (∑ c, ψ (layerShift μ hμ c)
              * linkVal θ c μ)
            = ∑ c, ψ c * linkVal θ (layerUnshift μ hμ c) μ := by
          have h := sum_layerShift μ hμ
            (fun c => ψ c * linkVal θ (layerUnshift μ hμ c) μ)
          rw [← h]
          apply Finset.sum_congr rfl
          intro c _
          rw [layerUnshift_layerShift]
        rw [hshift]
        have hs : ψ s * linkVal θ (layerUnshift μ hμ s) μ
            = linkVal θ (layerUnshift μ hμ s) μ := by
          show (if s = s then (1 : ℝ) else 0)
              * linkVal θ (layerUnshift μ hμ s) μ = _
          rw [if_pos rfl, one_mul]
        rw [← hs]
        apply Finset.sum_eq_single s
        · intro b _ hb
          show ψ b * linkVal θ (layerUnshift μ hμ b) μ = 0
          rw [show ψ b = 0 from if_neg hb]
          exact zero_mul _
        · intro hmem
          exact absurd (Finset.mem_univ s) hmem
      rw [dif_pos hμ, hsum, e2, e1]
  have hsum : (∑ c, ∑ μ, linkVal (gaugeAngle ψ) c μ
        * linkVal θ c μ)
      = ∑ μ, (if h : μ ≠ 0 then
          linkVal θ (layerUnshift μ h s) μ
          - linkVal θ s μ else 0) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun μ _ => hper μ)
  rw [hsum] at horth
  have hneg : maxwellDiv θ s
      = -∑ μ, (if h : μ ≠ 0 then
          linkVal θ (layerUnshift μ h s) μ
          - linkVal θ s μ else 0) := by
    unfold maxwellDiv
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro μ _
    by_cases hμ : μ = 0
    · subst hμ
      rw [dif_neg (fun h : (0 : Fin 4) ≠ 0 => h rfl),
        dif_neg (fun h : (0 : Fin 4) ≠ 0 => h rfl), neg_zero]
    · rw [dif_pos hμ, dif_pos hμ, neg_sub]
  rw [hneg, horth, neg_zero]

/-- **Component means of an eigenvector**: orthogonality
against the constant direction fields forces every spatial
component mean to vanish. -/
theorem mean_of_eigen {θ : linkAngle N} {μ : ℝ}
    (hμ : μ ≠ 0) (hθ : maxwellOp N θ = μ • θ) :
    ∀ j : Fin 3, ∑ c, linkVal θ c (Fin.succ j) = 0 := by
  intro j
  classical
  set η : linkAngle N
    := fun ℓ => if ℓ.1.2 = Fin.succ j then 1 else 0 with hη
  have hker : maxwellOp N η = 0 := by
    apply ((maxwellM2_proved (N := N)) η).mpr
    intro P _
    show η (plaqEdgeB P) + η (plaqEdgeR P)
        - η (plaqEdgeT P) - η (plaqEdgeL P) = 0
    show (if P.mu = Fin.succ j then (1 : ℝ) else 0)
        + (if P.nu = Fin.succ j then (1 : ℝ) else 0)
        - (if P.mu = Fin.succ j then (1 : ℝ) else 0)
        - (if P.nu = Fin.succ j then (1 : ℝ) else 0) = 0
    ring
  have horth := orth_of_kernel hμ hker hθ
  rw [sum_link_inner] at horth
  have hcol : ∀ c, (∑ μ, linkVal η c μ * linkVal θ c μ)
      = linkVal θ c (Fin.succ j) := by
    intro c
    have hmain : linkVal η c (Fin.succ j)
          * linkVal θ c (Fin.succ j)
        = linkVal θ c (Fin.succ j) := by
      rw [linkVal_of_ne _ _ (Fin.succ_ne_zero j)]
      show η (layerLinkOf c (Fin.succ j) (Fin.succ_ne_zero j))
          * linkVal θ c (Fin.succ j) = _
      show (if (Fin.succ j) = Fin.succ j then (1 : ℝ) else 0)
          * linkVal θ c (Fin.succ j) = _
      rw [if_pos rfl, one_mul]
    rw [← hmain]
    apply Finset.sum_eq_single (Fin.succ j)
    · intro μ _ hμj
      by_cases hμ : μ = 0
      · subst hμ
        rw [linkVal_zero, zero_mul]
      · rw [linkVal_of_ne _ _ hμ]
        show η (layerLinkOf c μ hμ) * linkVal θ c μ = 0
        show (if μ = Fin.succ j then (1 : ℝ) else 0)
            * linkVal θ c μ = 0
        rw [if_neg hμj, zero_mul]
    · intro hmem
      exact absurd (Finset.mem_univ _) hmem
  have hsum : (∑ c, ∑ μ, linkVal η c μ * linkVal θ c μ)
      = ∑ c, linkVal θ c (Fin.succ j) :=
    Finset.sum_congr rfl (fun c _ => hcol c)
  rw [hsum] at horth
  exact horth

end Assembly

section RegisteredStatements

variable {N : ℕ} [NeZero N]

/-- **The Poincare bound (registered)**: a link angle with
vanishing divergence and zero component means has its
quadratic form bounded below by the gap times its norm. -/
theorem maxwellQuad_gap_bound (θ : linkAngle N)
    (hdiv : ∀ c, maxwellDiv θ c = 0)
    (hmean : ∀ j : Fin 3,
      ∑ c, linkVal θ c (Fin.succ j) = 0) :
    4 * Real.sin (Real.pi / (N : ℝ)) ^ 2 * (∑ ℓ, (θ ℓ) ^ 2)
      ≤ maxwellQuad N θ := by
  classical
  by_cases hN1 : N = 1
  · -- At `N = 1` the gap value is `4 * sin^2 pi = 0`.
    have hgap0 : (4 : ℝ) * Real.sin (Real.pi / (N : ℝ)) ^ 2
        = 0 := by
      rw [hN1]
      simp [Real.sin_pi]
    rw [hgap0, zero_mul]
    exact maxwellQuad_nonneg θ
  · have hN2 : 2 ≤ N := by
      have hN0 : N ≠ 0 := NeZero.ne N
      omega
    -- The quadratic form in pair (site, direction) form.
    have hquad : maxwellQuad N θ
        = ∑ c, ∑ μ, ∑ ν, (if μ ≠ 0 ∧ ν ≠ 0 ∧ μ < ν
            then (plaqForm θ c μ ν) ^ 2 else 0) := by
      unfold maxwellQuad
      rw [sum_allPlaqData]
      apply Finset.sum_congr rfl
      intro c _
      apply Finset.sum_congr rfl
      intro μ _
      apply Finset.sum_congr rfl
      intro ν _
      by_cases h : μ ≠ 0 ∧ ν ≠ 0 ∧ μ < ν
      · rw [dif_pos h, if_pos h,
          plaqForm_eq θ c μ ν h.1 h.2.1 (ne_of_lt h.2.2)]
      · rw [dif_neg h, if_neg h]
    -- Parseval applied pair by pair.
    have hquad2 : maxwellQuad N θ
        = ∑ μ, ∑ ν, (if μ ≠ 0 ∧ ν ≠ 0 ∧ μ < ν
            then (1 / ((N : ℝ) ^ 3))
              * ∑ k, Complex.normSq (fhat (plaqSite θ μ ν) k)
            else 0) := by
      have hswap : (∑ c, ∑ μ, ∑ ν, (if μ ≠ 0 ∧ ν ≠ 0 ∧ μ < ν
              then (plaqForm θ c μ ν) ^ 2 else 0))
          = ∑ μ, ∑ ν, ∑ c, (if μ ≠ 0 ∧ ν ≠ 0 ∧ μ < ν
              then (plaqForm θ c μ ν) ^ 2 else 0) := by
        trans (∑ μ, ∑ c, ∑ ν, (if μ ≠ 0 ∧ ν ≠ 0 ∧ μ < ν
              then (plaqForm θ c μ ν) ^ 2 else 0))
        · exact Finset.sum_comm
        · apply Finset.sum_congr rfl
          intro μ _
          exact Finset.sum_comm
      rw [hquad, hswap]
      apply Finset.sum_congr rfl
      intro μ _
      apply Finset.sum_congr rfl
      intro ν _
      by_cases h : μ ≠ 0 ∧ ν ≠ 0 ∧ μ < ν
      · have hcc : (∑ c, (if μ ≠ 0 ∧ ν ≠ 0 ∧ μ < ν
                then (plaqForm θ c μ ν) ^ 2 else 0))
            = ∑ c, (plaqForm θ c μ ν) ^ 2 := by
          apply Finset.sum_congr rfl
          intro c _
          rw [if_pos h]
        rw [hcc, if_pos h]
        exact parseval (plaqSite θ μ ν)
      · have hcc : (∑ c, (if μ ≠ 0 ∧ ν ≠ 0 ∧ μ < ν
                then (plaqForm θ c μ ν) ^ 2 else 0)) = 0 := by
          apply Finset.sum_eq_zero
          intro c _
          rw [if_neg h]
        rw [hcc, if_neg h]
    -- Per-momentum Lagrange evaluation.
    have hpair : ∀ k : Fin 3 → ZMod N,
        (∑ μ, ∑ ν, (if μ ≠ 0 ∧ ν ≠ 0 ∧ μ < ν
            then Complex.normSq (fhat (plaqSite θ μ ν) k)
            else 0))
        = (∑ μ, Complex.normSq (shiftMult k μ - 1))
          * (∑ μ, Complex.normSq (fhat (linkComp θ μ) k)) := by
      intro k
      have hdef : (∑ μ, (starRingEnd ℂ) (shiftMult k μ - 1)
          * fhat (linkComp θ μ) k) = 0 := by
        have h1 : (∑ μ, (starRingEnd ℂ) (shiftMult k μ - 1)
            * fhat (linkComp θ μ) k)
            = - ∑ μ, (1 - (starRingEnd ℂ) (shiftMult k μ))
                * fhat (linkComp θ μ) k := by
          rw [← Finset.sum_neg_distrib]
          apply Finset.sum_congr rfl
          intro μ _
          rw [map_sub, map_one]
          ring
        have h2 : fhat (maxwellDiv θ) k = 0 :=
          fhat_eq_zero hdiv k
        rw [h1, ← fhat_maxwellDiv hN2 θ k, h2, neg_zero]
      have hsum : (∑ μ, ∑ ν, (if μ ≠ 0 ∧ ν ≠ 0 ∧ μ < ν
            then Complex.normSq (fhat (plaqSite θ μ ν) k)
            else 0))
          = ∑ μ, ∑ ν, (if μ ≠ 0 ∧ ν ≠ 0 ∧ μ < ν
            then Complex.normSq
              ((shiftMult k μ - 1) * fhat (linkComp θ ν) k
                - (shiftMult k ν - 1)
                  * fhat (linkComp θ μ) k)
            else 0) := by
        apply Finset.sum_congr rfl
        intro μ _
        apply Finset.sum_congr rfl
        intro ν _
        by_cases h : μ ≠ 0 ∧ ν ≠ 0 ∧ μ < ν
        · rw [if_pos h, if_pos h,
            fhat_plaq hN2 θ k μ ν h.1 h.2.1]
        · rw [if_neg h, if_neg h]
      rw [hsum, lagrange_pair_form
        (fun μ => shiftMult k μ - 1)
        (fun μ => fhat (linkComp θ μ) k)
        (by rw [shiftMult_zero, sub_self])
        (fhat_eq_zero (fun c => linkVal_zero θ c) k), hdef]
      simp only [map_zero, sub_zero]
    -- Pull the Parseval factor out and swap momentum outward.
    have h3 : ∀ μ ν : Fin 4, (if μ ≠ 0 ∧ ν ≠ 0 ∧ μ < ν
          then (1 / ((N : ℝ) ^ 3))
            * ∑ k, Complex.normSq (fhat (plaqSite θ μ ν) k)
          else 0)
        = (1 / ((N : ℝ) ^ 3)) * ∑ k,
            (if μ ≠ 0 ∧ ν ≠ 0 ∧ μ < ν
              then Complex.normSq (fhat (plaqSite θ μ ν) k)
              else 0) := by
      intro μ ν
      by_cases h : μ ≠ 0 ∧ ν ≠ 0 ∧ μ < ν
      · rw [if_pos h]
        congr 1
        apply Finset.sum_congr rfl
        intro k _
        rw [if_pos h]
      · rw [if_neg h]
        have hz : (∑ k, (if μ ≠ 0 ∧ ν ≠ 0 ∧ μ < ν
            then Complex.normSq (fhat (plaqSite θ μ ν) k)
            else 0)) = 0 := by
          apply Finset.sum_eq_zero
          intro k _
          rw [if_neg h]
        rw [hz, mul_zero]
    have hquad3 : maxwellQuad N θ
        = (1 / ((N : ℝ) ^ 3)) * ∑ k,
            (∑ μ, Complex.normSq (shiftMult k μ - 1))
            * (∑ μ, Complex.normSq (fhat (linkComp θ μ) k)) := by
      have hq3a : (∑ μ, ∑ ν, (if μ ≠ 0 ∧ ν ≠ 0 ∧ μ < ν
              then (1 / ((N : ℝ) ^ 3))
                * ∑ k, Complex.normSq (fhat (plaqSite θ μ ν) k)
              else 0))
          = ∑ μ, ∑ ν, (1 / ((N : ℝ) ^ 3)) * ∑ k,
              (if μ ≠ 0 ∧ ν ≠ 0 ∧ μ < ν
                then Complex.normSq (fhat (plaqSite θ μ ν) k)
                else 0) :=
        Finset.sum_congr rfl (fun μ _ =>
          Finset.sum_congr rfl (fun ν _ => h3 μ ν))
      have hq3b : (∑ μ, ∑ ν, (1 / ((N : ℝ) ^ 3)) * ∑ k,
              (if μ ≠ 0 ∧ ν ≠ 0 ∧ μ < ν
                then Complex.normSq (fhat (plaqSite θ μ ν) k)
                else 0))
          = (1 / ((N : ℝ) ^ 3)) * ∑ μ, ∑ ν, ∑ k,
              (if μ ≠ 0 ∧ ν ≠ 0 ∧ μ < ν
                then Complex.normSq (fhat (plaqSite θ μ ν) k)
                else 0) :=
        (Finset.sum_congr rfl (fun μ _ =>
          (Finset.mul_sum Finset.univ
            (fun ν => ∑ k, (if μ ≠ 0 ∧ ν ≠ 0 ∧ μ < ν
              then Complex.normSq (fhat (plaqSite θ μ ν) k)
              else 0)) (1 / ((N : ℝ) ^ 3))).symm)).trans
          (Finset.mul_sum Finset.univ
            (fun μ => ∑ ν, ∑ k, (if μ ≠ 0 ∧ ν ≠ 0 ∧ μ < ν
              then Complex.normSq (fhat (plaqSite θ μ ν) k)
              else 0)) (1 / ((N : ℝ) ^ 3))).symm
      have hq3c : (1 / ((N : ℝ) ^ 3)) * ∑ μ, ∑ ν, ∑ k,
              (if μ ≠ 0 ∧ ν ≠ 0 ∧ μ < ν
                then Complex.normSq (fhat (plaqSite θ μ ν) k)
                else 0)
          = (1 / ((N : ℝ) ^ 3)) * ∑ k,
              (∑ μ, Complex.normSq (shiftMult k μ - 1))
              * (∑ μ, Complex.normSq
                  (fhat (linkComp θ μ) k)) := by
        have hswap3 : (∑ μ, ∑ ν, ∑ k,
                (if μ ≠ 0 ∧ ν ≠ 0 ∧ μ < ν
                  then Complex.normSq (fhat (plaqSite θ μ ν) k)
                  else 0))
            = ∑ k, ∑ μ, ∑ ν, (if μ ≠ 0 ∧ ν ≠ 0 ∧ μ < ν
                then Complex.normSq (fhat (plaqSite θ μ ν) k)
                else 0) :=
          (Finset.sum_congr rfl
            (fun μ _ => Finset.sum_comm)).trans
            Finset.sum_comm
        rw [hswap3]
        congr 1
        exact Finset.sum_congr rfl (fun k _ => hpair k)
      exact hquad2.trans (hq3a.trans (hq3b.trans hq3c))
    -- The multiplier sum at momentum `k`.
    have hS1 : ∀ k : Fin 3 → ZMod N,
        (∑ μ, Complex.normSq (shiftMult k μ - 1))
        = ∑ j : Fin 3, 4 * Real.sin
            (Real.pi * ((k j).val : ℝ) / (N : ℝ)) ^ 2 := by
      intro k
      rw [Fin.sum_univ_succ, shiftMult_zero, sub_self]
      simp only [map_zero, zero_add]
      apply Finset.sum_congr rfl
      intro j _
      rw [normSq_shiftMult_sub_one, modePhase_succ]
    have hS2nn : ∀ k : Fin 3 → ZMod N,
        0 ≤ ∑ μ, Complex.normSq (fhat (linkComp θ μ) k) :=
      fun k => Finset.sum_nonneg
        (fun μ _ => Complex.normSq_nonneg _)
    -- The per-momentum bound.
    have hperk : ∀ k : Fin 3 → ZMod N,
        (4 * Real.sin (Real.pi / (N : ℝ)) ^ 2)
          * (∑ μ, Complex.normSq (fhat (linkComp θ μ) k))
        ≤ (∑ μ, Complex.normSq (shiftMult k μ - 1))
          * (∑ μ, Complex.normSq (fhat (linkComp θ μ) k)) := by
      intro k
      by_cases hk : k = 0
      · subst hk
        have hS20 : (∑ μ, Complex.normSq
            (fhat (linkComp θ μ) (0 : Fin 3 → ZMod N))) = 0 := by
          rw [Fin.sum_univ_succ]
          have t0 : Complex.normSq
              (fhat (linkComp θ 0) (0 : Fin 3 → ZMod N)) = 0 := by
            rw [fhat_zero_mom]
            have hzs : (∑ c, linkComp θ 0 c) = 0 :=
              Finset.sum_eq_zero (fun c _ => linkVal_zero θ c)
            rw [hzs, Complex.ofReal_zero]
            exact map_zero _
          rw [t0, zero_add]
          apply Finset.sum_eq_zero
          intro j _
          rw [fhat_zero_mom]
          have hzs : (∑ c, linkComp θ (Fin.succ j) c) = 0 :=
            hmean j
          rw [hzs, Complex.ofReal_zero]
          exact map_zero _
        rw [hS20]
        simp only [mul_zero]
        exact le_rfl
      · obtain ⟨j, hj⟩ : ∃ j, k j ≠ 0 := by
          by_contra h
          push_neg at h
          exact hk (funext h)
        have hv1 : 1 ≤ (k j).val := by
          rcases Nat.eq_zero_or_pos (k j).val with h0 | h0
          · exact absurd ((ZMod.val_eq_zero (k j)).mp h0) hj
          · exact h0
        have hv2 : (k j).val ≤ N - 1 := by
          have hlt := ZMod.val_lt (k j)
          omega
        have hterm : 4 * Real.sin (Real.pi / (N : ℝ)) ^ 2
            ≤ 4 * Real.sin
                (Real.pi * ((k j).val : ℝ) / (N : ℝ)) ^ 2 :=
          mul_le_mul_of_nonneg_left
            (cycle_sin_sq_ge hN2 hv1 hv2) (by norm_num)
        have hS1ge : (4 * Real.sin (Real.pi / (N : ℝ)) ^ 2)
            ≤ ∑ j : Fin 3, 4 * Real.sin
                (Real.pi * ((k j).val : ℝ) / (N : ℝ)) ^ 2 := by
          apply le_trans hterm
          apply Finset.single_le_sum (a := j)
          · intro i _
            positivity
          · exact Finset.mem_univ j
        calc (4 * Real.sin (Real.pi / (N : ℝ)) ^ 2)
              * (∑ μ, Complex.normSq (fhat (linkComp θ μ) k))
            ≤ (∑ j : Fin 3, 4 * Real.sin
                (Real.pi * ((k j).val : ℝ) / (N : ℝ)) ^ 2)
              * (∑ μ, Complex.normSq
                  (fhat (linkComp θ μ) k)) :=
              mul_le_mul_of_nonneg_right hS1ge (hS2nn k)
          _ = (∑ μ, Complex.normSq (shiftMult k μ - 1))
              * (∑ μ, Complex.normSq
                  (fhat (linkComp θ μ) k)) := by
              rw [hS1 k]
    -- The norm, through Parseval per component.
    have hnorm : (∑ ℓ, (θ ℓ) ^ 2)
        = (1 / ((N : ℝ) ^ 3)) * ∑ k,
            ∑ μ, Complex.normSq (fhat (linkComp θ μ) k) := by
      have e1 : (∑ ℓ, (θ ℓ) ^ 2)
          = ∑ μ, (1 / ((N : ℝ) ^ 3))
              * ∑ k, Complex.normSq
                  (fhat (linkComp θ μ) k) := by
        rw [sum_link_sq, Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro μ _
        exact parseval (linkComp θ μ)
      rw [e1, ← Finset.mul_sum]
      congr 1
      exact Finset.sum_comm
    -- Assemble.
    have hA : (0 : ℝ) ≤ 1 / ((N : ℝ) ^ 3) := by
      apply one_div_nonneg.mpr
      apply pow_nonneg
      exact Nat.cast_nonneg N
    calc (4 * Real.sin (Real.pi / (N : ℝ)) ^ 2)
          * (∑ ℓ, (θ ℓ) ^ 2)
        = (1 / ((N : ℝ) ^ 3))
            * ((4 * Real.sin (Real.pi / (N : ℝ)) ^ 2)
              * ∑ k, ∑ μ, Complex.normSq
                  (fhat (linkComp θ μ) k)) := by
          rw [hnorm]
          ring
      _ = (1 / ((N : ℝ) ^ 3)) * ∑ k,
            (4 * Real.sin (Real.pi / (N : ℝ)) ^ 2)
            * (∑ μ, Complex.normSq
                (fhat (linkComp θ μ) k)) := by
          congr 1
          rw [Finset.mul_sum]
      _ ≤ (1 / ((N : ℝ) ^ 3)) * ∑ k,
            (∑ μ, Complex.normSq (shiftMult k μ - 1))
            * (∑ μ, Complex.normSq
                (fhat (linkComp θ μ) k)) :=
          mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum (fun k _ => hperk k)) hA
      _ = maxwellQuad N θ := hquad3.symm

/-- **Clause 4 of (M5) (registered)**: every eigenvalue of
`maxwellOp N` at Even `N` is `0` or at least the gap value
`4 * sin^2 (pi / N)`. -/
theorem clause4 (hN : Even N) :
    ∀ μ : ℝ, Module.End.HasEigenvalue (maxwellOp N) μ →
      μ = 0 ∨ 4 * Real.sin (Real.pi / (N : ℝ)) ^ 2 ≤ μ := by
  intro μ hμ
  by_cases hμ0 : μ = 0
  · exact Or.inl hμ0
  · right
    obtain ⟨θ, hθ⟩ := hμ.exists_hasEigenvector
    have happly : maxwellOp N θ = μ • θ := hθ.apply_eq_smul
    have hθne : θ ≠ 0 :=
      (Module.End.hasEigenvector_iff.mp hθ).2
    have hdiv : ∀ c, maxwellDiv θ c = 0 :=
      maxwellDiv_of_eigen hμ0 happly
    have hmean : ∀ j : Fin 3,
        ∑ c, linkVal θ c (Fin.succ j) = 0 :=
      mean_of_eigen hμ0 happly
    have hbound := maxwellQuad_gap_bound θ hdiv hmean
    have hray : maxwellQuad N θ = μ * ∑ ℓ, (θ ℓ) ^ 2 := by
      rw [← maxwellOp_form_self θ, happly, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ℓ _
      rw [Pi.smul_apply, smul_eq_mul]
      ring
    have hS : 0 < ∑ ℓ, (θ ℓ) ^ 2 := by
      obtain ⟨ℓ, hℓ⟩ : ∃ ℓ, θ ℓ ≠ 0 := by
        by_contra h
        push_neg at h
        exact hθne (funext h)
      calc (0 : ℝ) < (θ ℓ) ^ 2 :=
            (sq_nonneg (θ ℓ)).lt_of_ne
              (Ne.symm (pow_ne_zero 2 hℓ))
        _ ≤ ∑ ℓ, (θ ℓ) ^ 2 :=
            Finset.single_le_sum (fun i _ => sq_nonneg _)
              (Finset.mem_univ ℓ)
    rw [hray] at hbound
    exact le_of_mul_le_mul_right hbound hS

/-- **(M5) in FULL (registered)**: `maxwellM5 N` at Even
`N`, by combining `maxwellM5_spectrum_part` (clauses
1, 2, 3, 5, MAX-3) with `clause4` (this brick). -/
theorem maxwellM5_full (hN : Even N) : maxwellM5 N hN := by
  have p := maxwellM5_spectrum_part hN
  exact ⟨p.1, p.2.1, p.2.2.1, clause4 hN, p.2.2.2⟩

end RegisteredStatements

end ThetLogos
