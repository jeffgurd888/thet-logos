import Mathlib.Tactic
import ThetLogos.ModularVariance

namespace ThetLogos

/-!
# ThetLogos.MassGibbsPin — Brick 1

**Commission:** Zero, 2026-11-18 00:17 EST ("build it"), on his
seeing filed verbatim 2026-11-18 00:15 EST: "Einstein and planck
both set E=mass •c²=hf therefore mass = Gibbs". Scope:
`~/workspace/your_files/mass-gibbs-pin-scope-2026-11-18.md`.

## Face declarations (MG-6)

- **NO CLAIM. T5 charter. PRE-REGISTERED DIAL-INELIGIBLE.** Dials
  0/4 before this brick, 0 after it, 0 under every outcome.
- The pin covers ONLY the finite Gibbs shadow of the seeing: mass
  entering a Gibbs state as an energy scale. It states **no `hf`,
  no `c`, no frequency, no time, no continuum, no relativity, no
  photon**. The Compton reading (`f = mc²/h`) stays a seeing; the
  seats have no time for it to live in. `E = mc²` enters only as the
  seeing's motivation for letting one mass scalar carry an energy
  profile.
- The seat is `ModularVariance`'s, reused wholesale — no seat is
  rebuilt here (the weld's duplication is the standing lesson).
- Kills armed on the face: K-MASSGIBBS-SPLIT (a Gibbs observable
  separating `m` from `β·m` over any landed interface kills the
  identification as a corpus-wide claim) and K-MASSGIBBS-COSTUME
  (if the menu closes at definitional grade with MG-5 dropped or
  failed, the pin re-grades as a record pin, 0 strict).

## Contents (7 declarations)

- `massEnergy` — the energy profile carried by mass `m` over a
  fixed unit profile `u`: `E_m = m • u` (the one new definition).
- `partSum_massEnergy` — **MG-2**: the partition identity.
- `gibbsProb_massEnergy` — **MG-1**: the identification. The Gibbs
  state at `(β, m)` is the unit-mass Gibbs state at `β * m`: mass
  and cold enter the state only through their product.
- `gibbsExpect_massEnergy` — **MG-3**: every observable's
  expectation agrees under the identification.
- `gibbsVar_massEnergy` — MG-3 corollary: variance agrees.
- `meanEnergy_massEnergy` — MG-3 corollary: the mean energy is `m`
  times the unit profile's mean energy at the product cold.
- `mass_eq_of_gibbsProb_eq` — **MG-5** (separation, the converse):
  at `β ≠ 0` over a nonconstant profile, the state determines the
  mass — the state sees exactly the product `β * m`, no more
  (MG-1), no less (MG-5).
-/

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- **The energy carried by a mass** (Tier T2 — definition): the
profile `E_m = m • u`, mass `m : ℝ` scaling a fixed unit profile
`u : ι → ℝ`. This is the only new definition of the brick: the
pin's whole claim is that a Gibbs state can see this `m` only
inside the product `β * m`. -/
noncomputable def massEnergy (u : ι → ℝ) (m : ℝ) : ι → ℝ :=
  fun i => m * u i

/-- **MG-2 — the partition identity** (Tier T1 — proved at build):
`Z(m • u, β) = Z(u, β * m)`. Termwise: the exponent
`-(β * (m * u i))` is `-((β * m) * u i)` by associativity — a ring
identity, not a definitional one — and the sum follows by
congruence. Proved first; MG-1 consumes it. -/
theorem partSum_massEnergy (u : ι → ℝ) (m β : ℝ) :
    ModularVariance.partSum (massEnergy u m) β =
      ModularVariance.partSum u (β * m) := by
  unfold ModularVariance.partSum massEnergy
  apply Finset.sum_congr rfl
  intro i _
  show Real.exp (-(β * (m * u i))) = Real.exp (-((β * m) * u i))
  congr 1
  ring

/-- **MG-1 — the identification** (Tier T1 — proved at build): the
Gibbs state at mass `m` and inverse temperature `β` IS the
unit-mass Gibbs state at inverse temperature `β * m`, site by
site. Mass and cold enter the state only through their product.
Hypothesis-free: it holds at every real `m` and `β` (at `m ≤ 0` it
reads as the cold/hot exchange of the flipped profile). -/
theorem gibbsProb_massEnergy (u : ι → ℝ) (m β : ℝ) (i : ι) :
    ModularVariance.gibbsProb (massEnergy u m) β i =
      ModularVariance.gibbsProb u (β * m) i := by
  unfold ModularVariance.gibbsProb
  rw [partSum_massEnergy]
  congr 1
  show Real.exp (-(β * (m * u i))) = Real.exp (-((β * m) * u i))
  congr 1
  ring

/-- **MG-3 — observables agree** (Tier T1 — proved at build):
every observable has the same expectation in the state at
`(β, m)` as in the unit-mass state at `β * m`. Immediate from
MG-1 by sum congruence — stated because it is the form in which
"no Gibbs observable separates `m` from `β * m`" is used
(K-MASSGIBBS-SPLIT's negative face, over this interface). -/
theorem gibbsExpect_massEnergy (u : ι → ℝ) (m β : ℝ) (X : ι → ℝ) :
    ModularVariance.gibbsExpect (massEnergy u m) β X =
      ModularVariance.gibbsExpect u (β * m) X := by
  unfold ModularVariance.gibbsExpect
  apply Finset.sum_congr rfl
  intro i _
  rw [gibbsProb_massEnergy]

/-- **MG-3, variance corollary** (Tier T1 — proved at build): the
Gibbs variance of any observable also agrees under the
identification — both `gibbsExpect` occurrences (the outer mean
and the centering mean) rewrite by MG-3. -/
theorem gibbsVar_massEnergy (u : ι → ℝ) (m β : ℝ) (X : ι → ℝ) :
    ModularVariance.gibbsVar (massEnergy u m) β X =
      ModularVariance.gibbsVar u (β * m) X := by
  unfold ModularVariance.gibbsVar
  simp only [gibbsExpect_massEnergy]

/-- **MG-3, mean-energy corollary** (Tier T1 — proved at build):
the mean energy of the mass-carried profile is `m` times the unit
profile's mean energy read at the product cold:
`⟨E_m⟩_β = m * ⟨u⟩_{β*m}`. The state's own energy bookkeeping
scales with the mass — at the rescaled cold. -/
theorem meanEnergy_massEnergy (u : ι → ℝ) (m β : ℝ) :
    ModularVariance.meanEnergy (massEnergy u m) β =
      m * ModularVariance.gibbsExpect u (β * m) u := by
  unfold ModularVariance.meanEnergy
  rw [gibbsExpect_massEnergy]
  exact ModularVariance.gibbsExpect_const_mul u (β * m) u m

/-- **MG-5 — separation (the converse)** (Tier T1 — proved at
build): if at some `β ≠ 0` the Gibbs states of masses `m₁` and
`m₂` over a NONCONSTANT profile `u` agree at every site, then
`m₁ = m₂`. Together with MG-1: the state sees exactly the product
`β * m` — no more, no less. The nonconstancy hypothesis is
load-bearing: at a constant profile every mass gives the uniform
state (the genuine countermodel).

Proof: at sites `i, j` with `u i ≠ u j`, divide the state
equation at `i` by the one at `j` for each mass; each state's own
partition sum cancels in its ratio (`gibbsProb_pos` licenses the
divisions), leaving
`exp (-(β * m₁ * (u i - u j))) = exp (-(β * m₂ * (u i - u j)))`;
`Real.exp` injectivity and cancellation of the nonzero factor
`β * (u i - u j)` close. -/
theorem mass_eq_of_gibbsProb_eq {u : ι → ℝ} {m₁ m₂ β : ℝ}
    (hβ : β ≠ 0)
    (h : ∀ i, ModularVariance.gibbsProb (massEnergy u m₁) β i =
      ModularVariance.gibbsProb (massEnergy u m₂) β i)
    {i j : ι} (hij : u i ≠ u j) :
    m₁ = m₂ := by
  have hd : β * (u i - u j) ≠ 0 :=
    mul_ne_zero hβ (sub_ne_zero.mpr hij)
  -- Ratio step: from `h i`, `h j` and positivity of all four
  -- weights, the partition sums cancel in the ratios at (i, j).
  have hratio :
      Real.exp (-(β * m₁ * (u i - u j))) =
        Real.exp (-(β * m₂ * (u i - u j))) := by
    have hZ1 : (0 : ℝ) < ModularVariance.partSum (massEnergy u m₁) β :=
      ModularVariance.partSum_pos _ _
    have hZ2 : (0 : ℝ) < ModularVariance.partSum (massEnergy u m₂) β :=
      ModularVariance.partSum_pos _ _
    have hi := h i
    have hj := h j
    unfold ModularVariance.gibbsProb massEnergy at hi hj
    -- hi : exp (-(β * (m₁ * u i))) / Z₁ = exp (-(β * (m₂ * u i))) / Z₂
    -- hj : exp (-(β * (m₁ * u j))) / Z₁ = exp (-(β * (m₂ * u j))) / Z₂
    have hi' := (div_eq_div_iff hZ1.ne' hZ2.ne').mp hi
    have hj' := (div_eq_div_iff hZ1.ne' hZ2.ne').mp hj
    -- Cross-multiply: both products, times Z₂, equal `(e₂ᵢ * Z₁) * e₂ⱼ`
    -- up to ring rearrangement (via hi' on the left, hj' on the right).
    have key : Real.exp (-(β * (m₁ * u i))) * Real.exp (-(β * (m₂ * u j)))
          * ModularVariance.partSum (massEnergy u m₂) β
        = Real.exp (-(β * (m₁ * u j))) * Real.exp (-(β * (m₂ * u i)))
          * ModularVariance.partSum (massEnergy u m₂) β := by
      calc Real.exp (-(β * (m₁ * u i))) * Real.exp (-(β * (m₂ * u j)))
            * ModularVariance.partSum (massEnergy u m₂) β
          = (Real.exp (-(β * (m₁ * u i)))
              * ModularVariance.partSum (massEnergy u m₂) β)
              * Real.exp (-(β * (m₂ * u j))) := by ring
        _ = (Real.exp (-(β * (m₂ * u i)))
              * ModularVariance.partSum (massEnergy u m₁) β)
              * Real.exp (-(β * (m₂ * u j))) := by rw [hi']
        _ = (Real.exp (-(β * (m₁ * u j)))
              * ModularVariance.partSum (massEnergy u m₂) β)
              * Real.exp (-(β * (m₂ * u i))) := by
            rw [hj']; ring
        _ = Real.exp (-(β * (m₁ * u j))) * Real.exp (-(β * (m₂ * u i)))
            * ModularVariance.partSum (massEnergy u m₂) β := by ring
    have hcross := mul_right_cancel₀ hZ2.ne' key
    -- hcross : e₁ᵢ * e₂ⱼ = e₁ⱼ * e₂ᵢ — restate as a ratio equality.
    have hr : Real.exp (-(β * (m₁ * u i))) / Real.exp (-(β * (m₁ * u j)))
        = Real.exp (-(β * (m₂ * u i))) / Real.exp (-(β * (m₂ * u j))) := by
      rw [div_eq_div_iff (Real.exp_pos _).ne' (Real.exp_pos _).ne']
      linear_combination hcross
    rw [← Real.exp_sub, ← Real.exp_sub] at hr
    have e1 : -(β * (m₁ * u i)) - -(β * (m₁ * u j))
        = -(β * m₁ * (u i - u j)) := by ring
    have e2 : -(β * (m₂ * u i)) - -(β * (m₂ * u j))
        = -(β * m₂ * (u i - u j)) := by ring
    rw [e1, e2] at hr
    exact hr
  have harg := Real.exp_injective hratio
  -- `-(β * m₁ * d) = -(β * m₂ * d)` with `β * d ≠ 0` gives `m₁ = m₂`
  -- after rearranging both sides to `(β * d) * mₖ` form.
  have e1 : β * m₁ * (u i - u j) = (β * (u i - u j)) * m₁ := by ring
  have e2 : β * m₂ * (u i - u j) = (β * (u i - u j)) * m₂ := by ring
  rw [e1, e2] at harg
  have := (mul_left_cancel₀ hd (neg_inj.mp harg))
  exact this

end ThetLogos
