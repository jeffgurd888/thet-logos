import Mathlib.Tactic
import Mathlib.Analysis.Calculus.MeanValue
import ThetLogos.SolidBody

/-!
# ThetLogos.SolidBodyVarMoments — variable-axis brick 3: honest I(t)

The time-varying-moments model, in the NARROW form scoped in
`varaxis-scoping-2026-10-26.md` §C: the principal axes remain FIXED in
the body, the moments are prescribed differentiable functions
`Iᵢ(t) > 0`, and `Lᵢ = Iᵢ(t)·ωᵢ`. Torque-free motion in the rotating
body frame, `(dL/dt)_body + ω × L = 0`, then forces the CORRECTED
field

  `ω̇ᵢ = ((Iⱼ − Iₖ)/Iᵢ)·ωⱼ·ωₖ − (İᵢ/Iᵢ)·ωᵢ`   ((i, j, k) cyclic),

i.e. the frozen `eulerRHS` at the instantaneous body minus the
correction `(İᵢ/Iᵢ)·ωᵢ`. This brick proves, from that hypothesis
(T1-from-hypothesis, the foundation's pattern):

* **Energy is NOT conserved** along corrected trajectories:
  `d/dt (½ Σᵢ Iᵢωᵢ²) = −½ Σᵢ İᵢωᵢ²`, the correction term exact.
  The missing power is work exchanged with whatever process
  prescribes the changing inertia; rotational energy alone is a
  subsystem quantity.
* **Body-frame `|L|²` IS conserved** in this narrow model — proved
  by the new chain-rule calculation here (the `İ` terms cancel only
  after the corrected equation is used); the foundation's
  `angMomSq_const` does NOT transfer, since its body is constant and
  its chain rule omits every `İ` term.
* **The contrast:** under the MERELY POSTULATED model
  `ω̇ = eulerRHS(I(t), ω)` (frozen field, no correction),
  `dT/dt = +½ Σᵢ İᵢωᵢ²` and `d|L|²/dt = 2 Σᵢ Iᵢİᵢωᵢ²` — neither
  frozen conservation statement transfers.

## Out of this model — on its face

Rotating principal axes, products of inertia, and mass leaving the
body are OUTSIDE this model: if the axes rotate or mass leaves,
`İᵢ` alone does not specify the dynamics (carried angular-momentum
fluxes / channel torques are also needed). Abstract body only;
no statement about any physical body. **NO CLAIM. Parts of the Clay
Yang–Mills statement closed by this module: 0.**
-/

namespace ThetLogos

/-- A body with prescribed time-varying principal moments: the axes
are fixed in the body, the moments `Iᵢ(t)` are functions of time,
each strictly positive at every time. Differentiability is taken as
a hypothesis where needed, as in the foundation. -/
structure VarBody where
  I1 : ℝ → ℝ
  I2 : ℝ → ℝ
  I3 : ℝ → ℝ
  I1_pos : ∀ t, 0 < I1 t
  I2_pos : ∀ t, 0 < I2 t
  I3_pos : ∀ t, 0 < I3 t

/-- The principal moments of a variable body at time `t`, as a
function on axes: `0 ↦ I₁(t)`, `1 ↦ I₂(t)`, `2 ↦ I₃(t)`. -/
def varMomInertia (v : VarBody) (t : ℝ) : Fin 3 → ℝ := ![v.I1 t, v.I2 t, v.I3 t]

/-- The frozen (constant) body obtained by freezing `v` at time `t`.
The instantaneous Euler field of the variable body is the Euler
field of this frozen body. -/
def varBodyAt (v : VarBody) (t : ℝ) : SolidBody :=
  ⟨v.I1 t, v.I2 t, v.I3 t, v.I1_pos t, v.I2_pos t, v.I3_pos t⟩

/-- The moment derivatives `İᵢ(t)`, componentwise: the derivative of
the `i`-th moment function at `t`. -/
noncomputable def varMomDeriv (v : VarBody) (t : ℝ) : Fin 3 → ℝ :=
  fun i => deriv (fun s => varMomInertia v s i) t

/-- Rotational kinetic energy of the variable body along `ω` at
time `t`: the frozen energy of `varBodyAt v t` at `ω t`. -/
noncomputable def varRotEnergy (v : VarBody) (ω : ℝ → Fin 3 → ℝ) (t : ℝ) : ℝ :=
  rotEnergy (varBodyAt v t) (ω t)

/-- Squared body-frame angular momentum of the variable body along
`ω` at time `t`: the frozen `|L|²` of `varBodyAt v t` at `ω t`. -/
def varAngMomSq (v : VarBody) (ω : ℝ → Fin 3 → ℝ) (t : ℝ) : ℝ :=
  angMomSq (varBodyAt v t) (ω t)

/-- The corrected Euler field: the frozen field at body `b` minus
the moment-drift correction `(İᵢ/Iᵢ)·ωᵢ` in each component, where
`dI` records the moment derivatives `İ`. -/
noncomputable def eulerRHSCorr (b : SolidBody) (dI : Fin 3 → ℝ) (ω : Fin 3 → ℝ) :
    Fin 3 → ℝ :=
  fun i => eulerRHS b ω i - (dI i / momInertia b i) * ω i

@[simp] lemma varMomInertia_zero (v : VarBody) (t : ℝ) :
    varMomInertia v t 0 = v.I1 t := rfl
@[simp] lemma varMomInertia_one (v : VarBody) (t : ℝ) :
    varMomInertia v t 1 = v.I2 t := rfl
@[simp] lemma varMomInertia_two (v : VarBody) (t : ℝ) :
    varMomInertia v t 2 = v.I3 t := rfl

@[simp] lemma varBodyAt_I1 (v : VarBody) (t : ℝ) : (varBodyAt v t).I1 = v.I1 t := rfl
@[simp] lemma varBodyAt_I2 (v : VarBody) (t : ℝ) : (varBodyAt v t).I2 = v.I2 t := rfl
@[simp] lemma varBodyAt_I3 (v : VarBody) (t : ℝ) : (varBodyAt v t).I3 = v.I3 t := rfl

@[simp] lemma momInertia_varBodyAt (v : VarBody) (t : ℝ) (i : Fin 3) :
    momInertia (varBodyAt v t) i = varMomInertia v t i := rfl

@[simp] lemma eulerRHSCorr_apply (b : SolidBody) (dI : Fin 3 → ℝ) (ω : Fin 3 → ℝ)
    (i : Fin 3) :
    eulerRHSCorr b dI ω i = eulerRHS b ω i - (dI i / momInertia b i) * ω i := rfl

/-! ## Algebraic core: what the corrected field does to the two sums

These are pointwise identities at a frozen body `b` with drift `dI`.
The frozen vanishing identities of `SolidBody` do the Euler part;
the correction contributes exactly its own term. -/

/-- Pairing the corrected field against `Iᵢωᵢ` (the energy pairing):
the Euler part vanishes (foundation), and the correction leaves
exactly `−Σᵢ İᵢωᵢ²`. -/
theorem eulerRHSCorr_energy_key (b : SolidBody) (dI : Fin 3 → ℝ) (ω : Fin 3 → ℝ) :
    ∑ i, momInertia b i * ω i * eulerRHSCorr b dI ω i
      = - ∑ i, dI i * (ω i) ^ 2 := by
  have h1 : b.I1 ≠ 0 := b.I1_pos.ne'
  have h2 : b.I2 ≠ 0 := b.I2_pos.ne'
  have h3 : b.I3 ≠ 0 := b.I3_pos.ne'
  rw [Fin.sum_univ_three, Fin.sum_univ_three]
  simp only [momInertia_zero, momInertia_one, momInertia_two,
    eulerRHSCorr_apply, eulerRHS_zero, eulerRHS_one, eulerRHS_two]
  field_simp
  ring

/-- Pairing the corrected field against `Lᵢ = Iᵢωᵢ` (the `|L|²`
pairing), with the drift of `Lᵢ` itself included: the drift term
`İᵢωᵢ` and the correction `Iᵢ·(−(İᵢ/Iᵢ)ωᵢ)` cancel exactly, and
what remains is the foundation's vanishing `|L|²` pairing. This
cancellation is the infinitesimal reason `|L|²` survives. -/
theorem eulerRHSCorr_angMom_key (b : SolidBody) (dI : Fin 3 → ℝ) (ω : Fin 3 → ℝ) :
    ∑ i, (momInertia b i * ω i) * (dI i * ω i + momInertia b i * eulerRHSCorr b dI ω i)
      = 0 := by
  have h1 : b.I1 ≠ 0 := b.I1_pos.ne'
  have h2 : b.I2 ≠ 0 := b.I2_pos.ne'
  have h3 : b.I3 ≠ 0 := b.I3_pos.ne'
  rw [Fin.sum_univ_three]
  simp only [momInertia_zero, momInertia_one, momInertia_two,
    eulerRHSCorr_apply, eulerRHS_zero, eulerRHS_one, eulerRHS_two]
  field_simp
  ring

/-- The same pairing for the MERELY POSTULATED field (frozen
`eulerRHS` at the instantaneous body, no correction): the drift of
`Lᵢ` is left uncancelled, and the pairing equals `Σᵢ Iᵢİᵢωᵢ²`
instead of `0`. -/
theorem eulerRHS_post_angMom_key (b : SolidBody) (dI : Fin 3 → ℝ) (ω : Fin 3 → ℝ) :
    ∑ i, (momInertia b i * ω i) * (dI i * ω i + momInertia b i * eulerRHS b ω i)
      = ∑ i, momInertia b i * dI i * (ω i) ^ 2 := by
  have h1 : b.I1 ≠ 0 := b.I1_pos.ne'
  have h2 : b.I2 ≠ 0 := b.I2_pos.ne'
  have h3 : b.I3 ≠ 0 := b.I3_pos.ne'
  rw [Fin.sum_univ_three, Fin.sum_univ_three]
  simp only [momInertia_zero, momInertia_one, momInertia_two,
    eulerRHS_zero, eulerRHS_one, eulerRHS_two]
  field_simp
  ring

/-! ## Chain-rule helpers (the foundation's pattern, with drift) -/

/-- Derivative of one energy component `Iᵢ(s)·ωᵢ(s)²` when both the
moment and the spin move: the product rule leaves the drift term
`İᵢωᵢ²` beside the frozen term `Iᵢ·2ωᵢω̇ᵢ`. -/
lemma hasDerivAt_mom_mul_sq {A w : ℝ → ℝ} {A' w' t : ℝ}
    (hA : HasDerivAt A A' t) (hw : HasDerivAt w w' t) :
    HasDerivAt (fun s => A s * (w s) ^ 2)
      (A' * (w t) ^ 2 + A t * (2 * w t * w')) t := by
  have hw2 : HasDerivAt (fun s => (w s) ^ 2) (2 * w t * w') t := by
    have hmul : HasDerivAt (fun s => w s * w s) (w' * w t + w t * w') t :=
      hw.mul hw
    have hfun : (fun s => (w s) ^ 2) = (fun s => w s * w s) := by
      funext s
      rw [pow_two]
    have h2 : (2 : ℝ) * w t * w' = w' * w t + w t * w' := by ring
    rw [hfun, h2]
    exact hmul
  exact hA.mul hw2

/-- Derivative of one angular-momentum component `(Iᵢ(s)·ωᵢ(s))²`:
`2·Lᵢ·L̇ᵢ` with `L̇ᵢ = İᵢωᵢ + Iᵢω̇ᵢ` — the drift of `Lᵢ` itself is
inside, which is exactly where the corrected/postulated contrast
will be decided. -/
lemma hasDerivAt_angMom_comp {A w : ℝ → ℝ} {A' w' t : ℝ}
    (hA : HasDerivAt A A' t) (hw : HasDerivAt w w' t) :
    HasDerivAt (fun s => (A s * w s) ^ 2)
      (2 * (A t * w t) * (A' * w t + A t * w')) t := by
  have hL : HasDerivAt (fun s => A s * w s) (A' * w t + A t * w') t :=
    hA.mul hw
  have hmul : HasDerivAt (fun s => (A s * w s) * (A s * w s))
      ((A' * w t + A t * w') * (A t * w t)
        + (A t * w t) * (A' * w t + A t * w')) t := hL.mul hL
  have hfun : (fun s => (A s * w s) ^ 2)
      = (fun s => (A s * w s) * (A s * w s)) := by
    funext s
    rw [pow_two]
  have h2 : (2 : ℝ) * (A t * w t) * (A' * w t + A t * w')
      = (A' * w t + A t * w') * (A t * w t)
        + (A t * w t) * (A' * w t + A t * w') := by ring
  rw [hfun, h2]
  exact hmul

/-! ## The corrected model: energy law and `|L|²` survival

Throughout, `hω` says the trajectory obeys the CORRECTED field at
the instantaneous frozen body (the T4 physics input of §C, taken as
hypothesis), and `hωdiff` / `hIdiff` are the regularity the chain
rule needs, stated honestly as hypotheses. -/

/-- **Energy law, corrected model:** rotational energy is NOT
conserved when the moments drift; its derivative is exactly
`−½ Σᵢ İᵢωᵢ²`. -/
theorem hasDerivAt_varRotEnergy_corr (v : VarBody) (ω : ℝ → Fin 3 → ℝ)
    (hω : ∀ t i, deriv (fun s => ω s i) t
      = eulerRHSCorr (varBodyAt v t) (varMomDeriv v t) (ω t) i)
    (hωdiff : ∀ i, Differentiable ℝ (fun s => ω s i))
    (hIdiff : ∀ i, Differentiable ℝ (fun s => varMomInertia v s i)) (t : ℝ) :
    HasDerivAt (fun s => varRotEnergy v ω s)
      (-(1 / 2) * ∑ i, varMomDeriv v t i * (ω t i) ^ 2) t := by
  have hcoord : ∀ i : Fin 3, HasDerivAt (fun s => ω s i)
      (eulerRHSCorr (varBodyAt v t) (varMomDeriv v t) (ω t) i) t := by
    intro i
    have h := (hωdiff i t).hasDerivAt
    rwa [hω t i] at h
  have hIcoord : ∀ i : Fin 3, HasDerivAt (fun s => varMomInertia v s i)
      (varMomDeriv v t i) t := fun i => (hIdiff i t).hasDerivAt
  have hcomp : ∀ i : Fin 3,
      HasDerivAt (fun s => varMomInertia v s i * (ω s i) ^ 2)
        (varMomDeriv v t i * (ω t i) ^ 2
          + varMomInertia v t i * (2 * ω t i
              * eulerRHSCorr (varBodyAt v t) (varMomDeriv v t) (ω t) i)) t :=
    fun i => hasDerivAt_mom_mul_sq (hIcoord i) (hcoord i)
  have hsum : HasDerivAt (fun s => ∑ i, varMomInertia v s i * (ω s i) ^ 2)
      (∑ i, (varMomDeriv v t i * (ω t i) ^ 2
        + varMomInertia v t i * (2 * ω t i
            * eulerRHSCorr (varBodyAt v t) (varMomDeriv v t) (ω t) i))) t :=
    HasDerivAt.fun_sum (fun i _ => hcomp i)
  have htot := hsum.const_mul (1 / 2)
  have hfun2 : (fun s => varRotEnergy v ω s)
      = (fun s => (1 / 2) * ∑ i, varMomInertia v s i * (ω s i) ^ 2) := by
    funext s
    rfl
  rw [hfun2]
  convert htot using 1
  have hval : ∑ i, (varMomDeriv v t i * (ω t i) ^ 2
        + varMomInertia v t i * (2 * ω t i
            * eulerRHSCorr (varBodyAt v t) (varMomDeriv v t) (ω t) i))
      = - ∑ i, varMomDeriv v t i * (ω t i) ^ 2 := by
    have hterm : ∀ i : Fin 3, varMomDeriv v t i * (ω t i) ^ 2
          + varMomInertia v t i * (2 * ω t i
              * eulerRHSCorr (varBodyAt v t) (varMomDeriv v t) (ω t) i)
        = varMomDeriv v t i * (ω t i) ^ 2
          + 2 * (momInertia (varBodyAt v t) i * ω t i
              * eulerRHSCorr (varBodyAt v t) (varMomDeriv v t) (ω t) i) := by
      intro i
      show varMomDeriv v t i * (ω t i) ^ 2
          + varMomInertia v t i * (2 * ω t i
              * eulerRHSCorr (varBodyAt v t) (varMomDeriv v t) (ω t) i)
        = varMomDeriv v t i * (ω t i) ^ 2
          + 2 * (varMomInertia v t i * ω t i
              * eulerRHSCorr (varBodyAt v t) (varMomDeriv v t) (ω t) i)
      ring
    calc ∑ i, (varMomDeriv v t i * (ω t i) ^ 2
            + varMomInertia v t i * (2 * ω t i
                * eulerRHSCorr (varBodyAt v t) (varMomDeriv v t) (ω t) i))
        = ∑ i, (varMomDeriv v t i * (ω t i) ^ 2
            + 2 * (momInertia (varBodyAt v t) i * ω t i
                * eulerRHSCorr (varBodyAt v t) (varMomDeriv v t) (ω t) i)) :=
          Finset.sum_congr rfl (fun i _ => hterm i)
      _ = (∑ i, varMomDeriv v t i * (ω t i) ^ 2)
            + 2 * ∑ i, momInertia (varBodyAt v t) i * ω t i
                * eulerRHSCorr (varBodyAt v t) (varMomDeriv v t) (ω t) i := by
          rw [Finset.sum_add_distrib, Finset.mul_sum]
      _ = - ∑ i, varMomDeriv v t i * (ω t i) ^ 2 := by
          rw [eulerRHSCorr_energy_key]
          ring
  rw [hval]
  ring

/-- **`|L|²` law, corrected model:** body-frame `|L|²` has
derivative `0` along corrected trajectories — the new calculation:
each `Lᵢ` drifts by `İᵢωᵢ`, and the corrected field's correction
cancels that drift exactly (see `eulerRHSCorr_angMom_key`). -/
theorem hasDerivAt_varAngMomSq_corr (v : VarBody) (ω : ℝ → Fin 3 → ℝ)
    (hω : ∀ t i, deriv (fun s => ω s i) t
      = eulerRHSCorr (varBodyAt v t) (varMomDeriv v t) (ω t) i)
    (hωdiff : ∀ i, Differentiable ℝ (fun s => ω s i))
    (hIdiff : ∀ i, Differentiable ℝ (fun s => varMomInertia v s i)) (t : ℝ) :
    HasDerivAt (fun s => varAngMomSq v ω s) 0 t := by
  have hcoord : ∀ i : Fin 3, HasDerivAt (fun s => ω s i)
      (eulerRHSCorr (varBodyAt v t) (varMomDeriv v t) (ω t) i) t := by
    intro i
    have h := (hωdiff i t).hasDerivAt
    rwa [hω t i] at h
  have hIcoord : ∀ i : Fin 3, HasDerivAt (fun s => varMomInertia v s i)
      (varMomDeriv v t i) t := fun i => (hIdiff i t).hasDerivAt
  have hcomp : ∀ i : Fin 3,
      HasDerivAt (fun s => (varMomInertia v s i * ω s i) ^ 2)
        (2 * (varMomInertia v t i * ω t i)
          * (varMomDeriv v t i * ω t i
            + varMomInertia v t i
              * eulerRHSCorr (varBodyAt v t) (varMomDeriv v t) (ω t) i)) t :=
    fun i => hasDerivAt_angMom_comp (hIcoord i) (hcoord i)
  have hsum : HasDerivAt (fun s => ∑ i, (varMomInertia v s i * ω s i) ^ 2)
      (∑ i, 2 * (varMomInertia v t i * ω t i)
        * (varMomDeriv v t i * ω t i
          + varMomInertia v t i
            * eulerRHSCorr (varBodyAt v t) (varMomDeriv v t) (ω t) i)) t :=
    HasDerivAt.fun_sum (fun i _ => hcomp i)
  have hfun2 : (fun s => varAngMomSq v ω s)
      = (fun s => ∑ i, (varMomInertia v s i * ω s i) ^ 2) := by
    funext s
    rfl
  rw [hfun2]
  convert hsum using 1
  have hval : ∑ i, 2 * (varMomInertia v t i * ω t i)
        * (varMomDeriv v t i * ω t i
          + varMomInertia v t i
            * eulerRHSCorr (varBodyAt v t) (varMomDeriv v t) (ω t) i)
      = 2 * ∑ i, (momInertia (varBodyAt v t) i * ω t i)
          * (varMomDeriv v t i * ω t i
            + momInertia (varBodyAt v t) i
              * eulerRHSCorr (varBodyAt v t) (varMomDeriv v t) (ω t) i) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    show 2 * (varMomInertia v t i * ω t i)
        * (varMomDeriv v t i * ω t i
          + varMomInertia v t i
            * eulerRHSCorr (varBodyAt v t) (varMomDeriv v t) (ω t) i)
      = 2 * ((varMomInertia v t i * ω t i)
          * (varMomDeriv v t i * ω t i
            + varMomInertia v t i
              * eulerRHSCorr (varBodyAt v t) (varMomDeriv v t) (ω t) i))
    ring
  rw [hval, eulerRHSCorr_angMom_key, mul_zero]

/-- **Body-frame `|L|²` is constant** along any trajectory obeying
the corrected variable-moment equations — in this narrow model
(fixed principal axes, no mass flux) only. -/
theorem varAngMomSq_const (v : VarBody) (ω : ℝ → Fin 3 → ℝ)
    (hω : ∀ t i, deriv (fun s => ω s i) t
      = eulerRHSCorr (varBodyAt v t) (varMomDeriv v t) (ω t) i)
    (hωdiff : ∀ i, Differentiable ℝ (fun s => ω s i))
    (hIdiff : ∀ i, Differentiable ℝ (fun s => varMomInertia v s i))
    (t₁ t₂ : ℝ) :
    varAngMomSq v ω t₁ = varAngMomSq v ω t₂ :=
  is_const_of_deriv_eq_zero
    (fun t => (hasDerivAt_varAngMomSq_corr v ω hω hωdiff hIdiff t).differentiableAt)
    (fun t => (hasDerivAt_varAngMomSq_corr v ω hω hωdiff hIdiff t).deriv) t₁ t₂

/-! ## The merely postulated model: neither frozen law transfers

Here `hω` postulates `ω̇ = eulerRHS(I(t), ω)` — the frozen field at
the instantaneous body, with NO correction term. Same chain rule;
different outcome, decided by the uncancelled drift. -/

/-- **Energy law, postulated model:** `dT/dt = +½ Σᵢ İᵢωᵢ²` —
the opposite sign from the corrected model. The frozen energy law
does not transfer. -/
theorem hasDerivAt_varRotEnergy_post (v : VarBody) (ω : ℝ → Fin 3 → ℝ)
    (hω : ∀ t i, deriv (fun s => ω s i) t = eulerRHS (varBodyAt v t) (ω t) i)
    (hωdiff : ∀ i, Differentiable ℝ (fun s => ω s i))
    (hIdiff : ∀ i, Differentiable ℝ (fun s => varMomInertia v s i)) (t : ℝ) :
    HasDerivAt (fun s => varRotEnergy v ω s)
      ((1 / 2) * ∑ i, varMomDeriv v t i * (ω t i) ^ 2) t := by
  have hcoord : ∀ i : Fin 3, HasDerivAt (fun s => ω s i)
      (eulerRHS (varBodyAt v t) (ω t) i) t := by
    intro i
    have h := (hωdiff i t).hasDerivAt
    rwa [hω t i] at h
  have hIcoord : ∀ i : Fin 3, HasDerivAt (fun s => varMomInertia v s i)
      (varMomDeriv v t i) t := fun i => (hIdiff i t).hasDerivAt
  have hcomp : ∀ i : Fin 3,
      HasDerivAt (fun s => varMomInertia v s i * (ω s i) ^ 2)
        (varMomDeriv v t i * (ω t i) ^ 2
          + varMomInertia v t i * (2 * ω t i
              * eulerRHS (varBodyAt v t) (ω t) i)) t :=
    fun i => hasDerivAt_mom_mul_sq (hIcoord i) (hcoord i)
  have hsum : HasDerivAt (fun s => ∑ i, varMomInertia v s i * (ω s i) ^ 2)
      (∑ i, (varMomDeriv v t i * (ω t i) ^ 2
        + varMomInertia v t i * (2 * ω t i
            * eulerRHS (varBodyAt v t) (ω t) i))) t :=
    HasDerivAt.fun_sum (fun i _ => hcomp i)
  have htot := hsum.const_mul (1 / 2)
  have hfun2 : (fun s => varRotEnergy v ω s)
      = (fun s => (1 / 2) * ∑ i, varMomInertia v s i * (ω s i) ^ 2) := by
    funext s
    rfl
  rw [hfun2]
  convert htot using 1
  have hval : ∑ i, (varMomDeriv v t i * (ω t i) ^ 2
        + varMomInertia v t i * (2 * ω t i
            * eulerRHS (varBodyAt v t) (ω t) i))
      = ∑ i, varMomDeriv v t i * (ω t i) ^ 2 := by
    have hterm : ∀ i : Fin 3, varMomDeriv v t i * (ω t i) ^ 2
          + varMomInertia v t i * (2 * ω t i
              * eulerRHS (varBodyAt v t) (ω t) i)
        = varMomDeriv v t i * (ω t i) ^ 2
          + 2 * (momInertia (varBodyAt v t) i * ω t i
              * eulerRHS (varBodyAt v t) (ω t) i) := by
      intro i
      show varMomDeriv v t i * (ω t i) ^ 2
          + varMomInertia v t i * (2 * ω t i
              * eulerRHS (varBodyAt v t) (ω t) i)
        = varMomDeriv v t i * (ω t i) ^ 2
          + 2 * (varMomInertia v t i * ω t i
              * eulerRHS (varBodyAt v t) (ω t) i)
      ring
    calc ∑ i, (varMomDeriv v t i * (ω t i) ^ 2
            + varMomInertia v t i * (2 * ω t i
                * eulerRHS (varBodyAt v t) (ω t) i))
        = ∑ i, (varMomDeriv v t i * (ω t i) ^ 2
            + 2 * (momInertia (varBodyAt v t) i * ω t i
                * eulerRHS (varBodyAt v t) (ω t) i)) :=
          Finset.sum_congr rfl (fun i _ => hterm i)
      _ = (∑ i, varMomDeriv v t i * (ω t i) ^ 2)
            + 2 * ∑ i, momInertia (varBodyAt v t) i * ω t i
                * eulerRHS (varBodyAt v t) (ω t) i := by
          rw [Finset.sum_add_distrib, Finset.mul_sum]
      _ = ∑ i, varMomDeriv v t i * (ω t i) ^ 2 := by
          rw [eulerRHS_energy_vanishes]
          ring
  rw [hval]

/-- **`|L|²` law, postulated model:** `d|L|²/dt = 2 Σᵢ Iᵢİᵢωᵢ²`
— the drift of `Lᵢ` is left uncancelled. The frozen `|L|²` law
does not transfer either. -/
theorem hasDerivAt_varAngMomSq_post (v : VarBody) (ω : ℝ → Fin 3 → ℝ)
    (hω : ∀ t i, deriv (fun s => ω s i) t = eulerRHS (varBodyAt v t) (ω t) i)
    (hωdiff : ∀ i, Differentiable ℝ (fun s => ω s i))
    (hIdiff : ∀ i, Differentiable ℝ (fun s => varMomInertia v s i)) (t : ℝ) :
    HasDerivAt (fun s => varAngMomSq v ω s)
      (2 * ∑ i, varMomInertia v t i * varMomDeriv v t i * (ω t i) ^ 2) t := by
  have hcoord : ∀ i : Fin 3, HasDerivAt (fun s => ω s i)
      (eulerRHS (varBodyAt v t) (ω t) i) t := by
    intro i
    have h := (hωdiff i t).hasDerivAt
    rwa [hω t i] at h
  have hIcoord : ∀ i : Fin 3, HasDerivAt (fun s => varMomInertia v s i)
      (varMomDeriv v t i) t := fun i => (hIdiff i t).hasDerivAt
  have hcomp : ∀ i : Fin 3,
      HasDerivAt (fun s => (varMomInertia v s i * ω s i) ^ 2)
        (2 * (varMomInertia v t i * ω t i)
          * (varMomDeriv v t i * ω t i
            + varMomInertia v t i * eulerRHS (varBodyAt v t) (ω t) i)) t :=
    fun i => hasDerivAt_angMom_comp (hIcoord i) (hcoord i)
  have hsum : HasDerivAt (fun s => ∑ i, (varMomInertia v s i * ω s i) ^ 2)
      (∑ i, 2 * (varMomInertia v t i * ω t i)
        * (varMomDeriv v t i * ω t i
          + varMomInertia v t i * eulerRHS (varBodyAt v t) (ω t) i)) t :=
    HasDerivAt.fun_sum (fun i _ => hcomp i)
  have hfun2 : (fun s => varAngMomSq v ω s)
      = (fun s => ∑ i, (varMomInertia v s i * ω s i) ^ 2) := by
    funext s
    rfl
  rw [hfun2]
  convert hsum using 1
  have hval : ∑ i, 2 * (varMomInertia v t i * ω t i)
        * (varMomDeriv v t i * ω t i
          + varMomInertia v t i * eulerRHS (varBodyAt v t) (ω t) i)
      = 2 * ∑ i, (momInertia (varBodyAt v t) i * ω t i)
          * (varMomDeriv v t i * ω t i
            + momInertia (varBodyAt v t) i * eulerRHS (varBodyAt v t) (ω t) i) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    show 2 * (varMomInertia v t i * ω t i)
        * (varMomDeriv v t i * ω t i
          + varMomInertia v t i * eulerRHS (varBodyAt v t) (ω t) i)
      = 2 * ((varMomInertia v t i * ω t i)
          * (varMomDeriv v t i * ω t i
            + varMomInertia v t i * eulerRHS (varBodyAt v t) (ω t) i))
    ring
  rw [hval, eulerRHS_post_angMom_key]
  refine congrArg (2 * ·) (Finset.sum_congr rfl (fun i _ => ?_))
  rw [momInertia_varBodyAt]

end ThetLogos
