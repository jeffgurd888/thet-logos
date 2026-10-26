import Mathlib.Tactic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import ThetLogos.SolidBody

/-!
# ThetLogos.SolidBodyOcean — the composite body: rigid core + locked ocean

Brick 2 of the solid-body foundation, commissioned 2026-10-25
(Jeff: "rigid body with oceans of lunar tidal locked water").
The body is `SolidBody` (brick 1) plus an ocean shell whose TIDAL
component is phase-locked to the Moon, exchanging angular momentum
with the spin through the lag torque.

## Fences, printed plainly

* The ocean here is ONLY its tidal (locked) component. The free
  currents — wind-driven, Coriolis-steered, the "motion term" of
  the melt–precession work — are a DIFFERENT channel; they are
  modeled in the melt-loop exhibit, not in this module.
* `kappa` (tidal coupling) and `lag` (the lag angle δ) are **T4
  model inputs**. The torque's functional form — MacDonald-style,
  `τ = −κ·sin(2δ)` — is a definition taken from the classical
  tidal literature, not a derived result.
* In this model the lock NEVER slips: the ocean's tidal component
  is locked to the lunar phase by construction. That is exactly
  why the braking below is secular (one-signed): a lock that
  slipped would sometimes push back.
* **No claim about the real Earth** beyond the bookkeeping
  identities and the sign theorem: whatever obeys the stated
  channel hypotheses conserves the spin+orbit total, and the spin
  channel then drains affinely. Calibration numbers (below) are
  T4 comments, never theorems.
-/

namespace ThetLogos

/-- The composite body: a rigid `core` (brick 1), an ocean shell
with moment contribution `Ioc`, tidal coupling `kappa`, tidal lag
angle `lag` (δ), and the lunar mean angular rate `nMoon`.
`Ioc` and `kappa` are positive; `kappa`, `lag` and `nMoon` are
T4 model inputs. -/
structure OceanBody where
  core : SolidBody
  Ioc : ℝ
  kappa : ℝ
  lag : ℝ
  nMoon : ℝ
  Ioc_pos : 0 < Ioc
  kappa_pos : 0 < kappa

/-- The tidal torque law (DEFINITION, T4 input — MacDonald-style
lag torque): the tidal bulge, carried by the faster spin, sits
ahead of the Earth–Moon line by the lag angle δ, and the Moon's
pull on the misaligned bulge brakes the spin:
`τ = −κ · sin (2δ)`. The functional form is the classical model
input, not a theorem. -/
noncomputable def tidalTorque (ob : OceanBody) : ℝ := -ob.kappa * Real.sin (2 * ob.lag)

/-- **Sign theorem (T1 from the definition):** for a lag angle in
the physical regime `0 < δ < π/4`, the tidal torque is strictly
negative — the braking has a definite sign in the lock.
(The range is chosen so that `2δ ∈ (0, π/2)`: the first quadrant,
where the MacDonald torque is monotone braking; real lag angles
are arcminutes, deep inside it. `sin` positivity alone would only
need `2δ ∈ (0, π)`.) -/
theorem tidalTorque_neg (ob : OceanBody) (h0 : 0 < ob.lag)
    (h1 : ob.lag < Real.pi / 4) : tidalTorque ob < 0 := by
  have hs : 0 < Real.sin (2 * ob.lag) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · linarith
    · have hpi : 0 < Real.pi := Real.pi_pos
      linarith
  have hprod : 0 < ob.kappa * Real.sin (2 * ob.lag) :=
    mul_pos ob.kappa_pos hs
  have heq : tidalTorque ob = -(ob.kappa * Real.sin (2 * ob.lag)) := by
    unfold tidalTorque
    ring
  rw [heq]
  exact neg_lt_zero.mpr hprod

/-! ## The transfer bookkeeping

Two channels, modeled as scalar functions of time (the spin-axis
channel): `Lspin` obeys `deriv Lspin = τ` (the lock applies the
torque to the spin) and `Lorbit` obeys `deriv Lorbit = −τ`
(the orbit receives exactly what the spin loses). Both equations
are HYPOTHESES — the coupling identity is the model; what is
proved is what follows from it. -/

/-- **Total bookkeeping (T1 from the channel hypotheses):**
spin + orbit angular momentum is constant in time. The lock moves
angular momentum between the channels; it creates none. -/
theorem total_angMom_const (ob : OceanBody) (Lspin Lorbit : ℝ → ℝ)
    (hspin : ∀ t, deriv Lspin t = tidalTorque ob)
    (horbit : ∀ t, deriv Lorbit t = -tidalTorque ob)
    (hspindiff : Differentiable ℝ Lspin) (horbitdiff : Differentiable ℝ Lorbit)
    (t₁ t₂ : ℝ) :
    Lspin t₁ + Lorbit t₁ = Lspin t₂ + Lorbit t₂ := by
  show (Lspin + Lorbit) t₁ = (Lspin + Lorbit) t₂
  refine is_const_of_deriv_eq_zero (f := Lspin + Lorbit) ?_ ?_ t₁ t₂
  · exact hspindiff.add horbitdiff
  · intro t
    rw [deriv_add (hspindiff t) (horbitdiff t), hspin t, horbit t,
      add_neg_cancel]

/-- **Secular drain (T1 from the channel hypothesis):** with the
torque a constant `τ` (the lock holds it fixed), the spin channel
is affine: `Lspin t = Lspin 0 + τ·t`.

Day-length reading (COMMENT, T4 calibration — not a theorem):
the length of day grows as the spin angular momentum falls; the
measured present-day tidal braking is ≈ +2.3 ms per century, and
the orbit's receipt on the same coupling is the lunar recession
≈ 3.8 cm/yr. Those numbers calibrate `kappa` for the real
Earth–Moon pair; nothing in this module derives them. -/
theorem Lspin_affine (ob : OceanBody) (Lspin : ℝ → ℝ)
    (hspin : ∀ t, deriv Lspin t = tidalTorque ob)
    (hspindiff : Differentiable ℝ Lspin) (t : ℝ) :
    Lspin t = Lspin 0 + tidalTorque ob * t := by
  have hτ : ∀ s : ℝ, deriv (fun u => tidalTorque ob * u) s = tidalTorque ob := by
    intro s
    simpa using ((hasDerivAt_id' s).const_mul (tidalTorque ob)).deriv
  have h0 : ∀ s, deriv (Lspin - fun u => tidalTorque ob * u) s = 0 := by
    intro s
    have hg : DifferentiableAt ℝ (fun u => tidalTorque ob * u) s := by fun_prop
    rw [deriv_sub (hspindiff s) hg, hspin s, hτ s, sub_self]
  have hconst := is_const_of_deriv_eq_zero
    (f := Lspin - fun u => tidalTorque ob * u)
    (hspindiff.sub (differentiable_id.const_mul _)) h0 t 0
  simp only [Pi.sub_apply, mul_zero, sub_zero] at hconst
  linarith

/-- **The spin channel strictly decreases** whenever the torque
has the braking sign: `Lspin` is strictly antitone. With
`tidalTorque_neg`, this applies throughout the physical lag
regime `0 < δ < π/4`. -/
theorem Lspin_strictAnti (ob : OceanBody) (Lspin : ℝ → ℝ)
    (hspin : ∀ t, deriv Lspin t = tidalTorque ob)
    (hspindiff : Differentiable ℝ Lspin)
    (hτ : tidalTorque ob < 0) : StrictAnti Lspin := by
  intro t₁ t₂ hlt
  rw [Lspin_affine ob Lspin hspin hspindiff t₁,
    Lspin_affine ob Lspin hspin hspindiff t₂]
  have hmul : tidalTorque ob * t₂ < tidalTorque ob * t₁ :=
    mul_lt_mul_of_neg_left hlt hτ
  linarith

/-! ## The lock itself

"Locked" means: the ocean's tidal component has NO independent
time dependence — it is a function of the lunar phase
`φ(t) = nMoon · t` alone. The formal content is the chain rule:
the time rate of any phase-locked quantity is the phase rate
times its phase derivative. -/

/-- The locked ocean's spin-channel angular momentum: shell moment
times the locked rate. The lock identifies the rate with the
lunar rate `nMoon` — that identification IS the lock. -/
def lockedChannelAM (ob : OceanBody) : ℝ := ob.Ioc * ob.nMoon

/-- **The lock, as a kinematic identity (T1):** for any
differentiable `g`, the phase-locked observable `t ↦ g (nMoon · t)`
has time derivative `nMoon · g'(nMoon · t)` — the phase rate times
the phase derivative, with no other time dependence. -/
theorem locked_phase_rate (ob : OceanBody) (g : ℝ → ℝ)
    (hg : Differentiable ℝ g) (t : ℝ) :
    deriv (fun s => g (ob.nMoon * s)) t
      = ob.nMoon * deriv g (ob.nMoon * t) := by
  have h1 : DifferentiableAt ℝ (fun s => ob.nMoon * s) t :=
    differentiableAt_id.const_mul _
  have h2 : deriv (fun s => g (ob.nMoon * s)) t
      = deriv g (ob.nMoon * t) * deriv (fun s => ob.nMoon * s) t :=
    deriv_comp t (hg _) h1
  have h3 : deriv (fun s => ob.nMoon * s) t = ob.nMoon := by
    simpa using ((hasDerivAt_id' t).const_mul ob.nMoon).deriv
  rw [h3] at h2
  linarith

end ThetLogos
