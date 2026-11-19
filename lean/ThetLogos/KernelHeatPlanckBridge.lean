import ThetLogos.PartnerThermal

/-!
# KernelHeatPlanckBridge — the Planck thermal kernal Bridge (KHP-0 pin)

Zero's name for this bridge, verbatim (Register A):
**"Planck thermal kernal Bridge"** (his spelling,
2026-11-13). Scope of record:
`kernel-heat-planck-bridge-scope-2026-11-13.md`.

Three seats the corpus already owns — the finite
operators and their kernels (kernel seat), the
complete finite Gibbs/thermal machinery (heat seat),
and the Planck seat, empty of the factor until now —
and the one span between them: the Planck radiation
factor `1 / (e^{βE} − 1)` is a THEOREM about the
geometric series `Σₙ e^{−βEn}`, not an axiom. This
module derives that factor inside the tree and ties
it to the two owned seats, in the finite seat only.

THIS BRICK (KHP-0) is the record pin, OG-0 genre:
the definitions, with names frozen, and the fence
lines. It carries ZERO theorems by design. The
proved content lands in the bricks behind it:
Brick A — KHP-1 (the mode partition function is the
geometric sum) and KHP-2 (the keystone: the derived
Planck factor); Brick B — KHP-3 (heat trace =
spectral sum) and KHP-4 (the contact: the finite
Gibbs state is the heat-kernel state at `t = β`).

## Fences (armed, on the face)

* **K-KHP-CONTINUUM** — the continuum blackbody law
  (Stefan–Boltzmann `T⁴`, Wien displacement as a
  theorem, the Planck curve over a continuous
  frequency axis) is NOT stateable at finite grade:
  FRONTIER, unpriced. No `T⁴` will ever be quoted
  from this bridge.
* **K-KHP-UNIT** — `ℏ`, `k_B`, and every physical
  unit enter as inputs or not at all. Mode energies
  and `β` are inputs; `ℏ` never appears. Nothing
  here derives a constant of nature.
* **K-KHP-PHYS** — no statement here says the finite
  object IS physical radiation, a physical
  blackbody, or any laboratory system. Finite modes
  only; the Register A design faces (calendar color
  track, the 0.0 thermal metric) gain no grade from
  this bridge.
* **K-KHP-TIME** — `β` is the bridge's only
  time-adjacent variable, and it is thermal time.
  No clause speaks about laboratory time at any
  scale (the "Ottosecond Time" fragment rides the
  scope unexpanded and changes nothing here).
* **K-KHP-SEAT** — this bridge's Planck is the 1900
  radiation factor ONLY. It does not touch, rename,
  or speak to the Planck-scale seat: the CPEC named
  absence (`CpecBridgePost`), its wires, and
  **K-CPEC-PLANCK-RENAME** stand exactly as filed,
  and no statement of this module may be quoted as
  bearing on the Planck scale, length, or mass in
  either direction.

**Zero-point convention (flagged, never silent):**
the `½E` zero-point shift is EXCLUDED by default in
every definition below — a mode's energy is counted
from its ground level, `Eₙ = n·E` before weighting —
and the exclusion is stated here on the face, not
buried in a proof.

**Voices Register:** KHP-2 carries **Max Planck's**
name (1900) on the face at either verdict — if the
keystone lands, Planck is confirmed at finite
grade; if it falls, the kill reports in his name at
the same volume. The continuum law remains his in
full and untested here (K-KHP-CONTINUUM is a fence
on our scope, not a verdict on his law).

Grade of the whole bridge when landed: T1 finite
theorems, NO CLAIM, dial-ineligible; dials 0/4
(mode energies and β are inputs; nothing here
touches Dial 3's spectrum floor — this is
combinatorics of the Gibbs weight, GAPFLOOR-1's
sibling).

STATUS: STATUS-KHP.md.
-/

namespace ThetLogos

section Mode

/-- The Gibbs weight of the `n`-th level of a
single mode of energy `E` at inverse temperature
`β`: `e^{−β·E·n}`. Mode energies are inputs
(K-KHP-UNIT). -/
noncomputable def modeWeight (β E : ℝ) (n : ℕ) : ℝ :=
  Real.exp (-(β * E * (n : ℝ)))

/-- The single-mode partition function: the total
Gibbs weight of the mode's ladder,
`Z(β, E) = Σ_{n≥0} e^{−βEn}` (KHP-1 evaluates it). -/
noncomputable def modePartition (β E : ℝ) : ℝ :=
  ∑' n : ℕ, modeWeight β E n

/-- The mean occupation of the mode: the
Gibbs-weighted mean of the level index `n` under
the weights `e^{−βEn} / Z`. (KHP-2, the keystone,
evaluates this to the Planck factor.) -/
noncomputable def meanOccupation (β E : ℝ) : ℝ :=
  (∑' n : ℕ, (n : ℝ) * modeWeight β E n) / modePartition β E

/-- **The Planck factor** (Max Planck, 1900),
defined here as a bare expression; KHP-2 proves
the mode's mean occupation EQUALS it — the factor
as a theorem, not an axiom:
`n̄ = 1 / (e^{βE} − 1)`. This is the 1900
radiation factor only (K-KHP-SEAT). -/
noncomputable def planckFactor (β E : ℝ) : ℝ :=
  1 / (Real.exp (β * E) - 1)

end Mode

section Spectrum

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- The heat trace of a finite operator `H` at
thermal time `β`: `Re Tr exp(−βH)` — the trace of
the heat kernel at `t = β` (real by Hermiticity
where it matters; KHP-3 evaluates it at a Hermitian
seat). -/
noncomputable def heatTrace (H : Matrix m m ℂ) (β : ℝ) : ℝ :=
  (Matrix.trace (NormedSpace.exp ((-(β:ℂ)) • H))).re

/-- The spectral side of the heat trace: the sum of
`e^{−βλᵢ}` over a finite spectrum `λ` (KHP-3: the
two sides agree at a Hermitian operator). -/
noncomputable def spectralHeatSum (lam : m → ℝ) (β : ℝ) : ℝ :=
  ∑ i, Real.exp (-(β * lam i))

/-- The total mean energy of a finite family of
independent modes with energies `λᵢ` at inverse
temperature `β`: each mode contributes
`λᵢ · n̄(β, λᵢ)`. ZERO-POINT EXCLUDED (flagged on
the module's face): no `½λᵢ` term appears, by
convention, never silently. (KHP-4 evaluates this
to `Σᵢ λᵢ / (e^{βλᵢ} − 1)` over positive modes.) -/
noncomputable def gibbsMeanEnergy (lam : m → ℝ) (β : ℝ) : ℝ :=
  ∑ i, lam i * meanOccupation β (lam i)

end Spectrum

/-! ## Brick A — KHP-1 and KHP-2 (the Planck factor, derived) -/

/-- The mode weight as a geometric term:
`e^{−βEn} = (e^{−βE})ⁿ`. -/
theorem modeWeight_eq_pow (β E : ℝ) (n : ℕ) :
    modeWeight β E n = (Real.exp (-(β * E))) ^ n := by
  unfold modeWeight
  rw [show -(β * E * (n : ℝ)) = (n : ℝ) * (-(β * E)) by ring,
    Real.exp_nat_mul]

/-- **KHP-1 (single-mode partition function).**
For `E > 0`, `β > 0`:
`Σ_{n≥0} e^{−βEn} = 1 / (1 − e^{−βE})` — the
geometric series (Mathlib's
`tsum_geometric_of_lt_one` at `r = e^{−βE} ∈ (0,1)`). -/
theorem modePartition_eq {β E : ℝ} (hE : 0 < E) (hβ : 0 < β) :
    modePartition β E = 1 / (1 - Real.exp (-(β * E))) := by
  have hr1 : Real.exp (-(β * E)) < 1 := by
    rw [Real.exp_lt_one_iff]
    have hpos : 0 < β * E := mul_pos hβ hE
    linarith
  have hcong : (fun n : ℕ => modeWeight β E n)
      = (fun n : ℕ => (Real.exp (-(β * E))) ^ n) := by
    funext n
    rw [modeWeight_eq_pow]
  unfold modePartition
  rw [hcong, tsum_geometric_of_lt_one (Real.exp_pos _).le hr1,
    one_div]

/-- The mode partition function is positive (the
closed form of KHP-1 has positive denominator). -/
theorem modePartition_pos {β E : ℝ} (hE : 0 < E) (hβ : 0 < β) :
    0 < modePartition β E := by
  have hr1 : Real.exp (-(β * E)) < 1 := by
    rw [Real.exp_lt_one_iff]
    have hpos : 0 < β * E := mul_pos hβ hE
    linarith
  rw [modePartition_eq hE hβ]
  exact one_div_pos.mpr (sub_pos.mpr hr1)

/-- The occupation numerator:
`Σ' n, n · e^{−βEn} = e^{−βE} / (1 − e^{−βE})²`
(Mathlib's `tsum_coe_mul_geometric_of_norm_lt_one`). -/
theorem tsum_modeWeight_mul {β E : ℝ} (hE : 0 < E) (hβ : 0 < β) :
    (∑' n : ℕ, (n : ℝ) * modeWeight β E n)
      = Real.exp (-(β * E)) / (1 - Real.exp (-(β * E))) ^ 2 := by
  have hr1 : Real.exp (-(β * E)) < 1 := by
    rw [Real.exp_lt_one_iff]
    have hpos : 0 < β * E := mul_pos hβ hE
    linarith
  have hnorm : ‖Real.exp (-(β * E))‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact hr1
  have hcong : (fun n : ℕ => (n : ℝ) * modeWeight β E n)
      = (fun n : ℕ => (n : ℝ) * (Real.exp (-(β * E))) ^ n) := by
    funext n
    rw [modeWeight_eq_pow]
  rw [hcong, tsum_coe_mul_geometric_of_norm_lt_one hnorm]

/-- **KHP-2 (the Planck factor, derived).** For
`E > 0`, `β > 0`, the Gibbs-weighted mean
occupation of the mode equals the Planck factor:
`n̄ = 1 / (e^{βE} − 1)`.

**Max Planck (1900)** — the factor as a theorem of
the finite seat, in his name (Voices Register): the
numerator series over the partition series, the
quotient simplifying by `e^{βE} − 1 =
(1 − e^{−βE}) / e^{−βE}`. The continuum law remains
his in full and untested here (K-KHP-CONTINUUM). -/
theorem meanOccupation_eq_planck {β E : ℝ}
    (hE : 0 < E) (hβ : 0 < β) :
    meanOccupation β E = planckFactor β E := by
  have hr0 : (0:ℝ) < Real.exp (-(β * E)) := Real.exp_pos _
  have hr1 : Real.exp (-(β * E)) < 1 := by
    rw [Real.exp_lt_one_iff]
    have hpos : 0 < β * E := mul_pos hβ hE
    linarith
  have h1r : (1:ℝ) - Real.exp (-(β * E)) ≠ 0 :=
    sub_ne_zero.mpr hr1.ne'
  have hE' : Real.exp (β * E)
      = (Real.exp (-(β * E)))⁻¹ := by
    rw [Real.exp_neg, inv_inv]
  have hsub : Real.exp (β * E) - 1
      = (1 - Real.exp (-(β * E))) / Real.exp (-(β * E)) := by
    rw [hE', eq_div_iff hr0.ne', sub_mul,
      inv_mul_cancel₀ hr0.ne', one_mul]
  unfold meanOccupation planckFactor
  rw [tsum_modeWeight_mul hE hβ, modePartition_eq hE hβ,
    hsub, one_div_div]
  field_simp [h1r]

/-! ## Brick B — KHP-3 and KHP-4 (heat trace; the contact) -/

section HeatTrace

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- **KHP-3 (heat trace = spectral sum).** For a
finite Hermitian `H`:
`Re Tr exp(−βH) = Σᵢ e^{−βλᵢ}` over its eigenvalues
— TAB-1's banked `gibbsTraceExp_eq` read on the
real side (`Complex.ofReal_re`). -/
theorem heatTrace_eq_spectralHeatSum
    {H : Matrix m m ℂ} (hH : H.IsHermitian) (β : ℝ) :
    heatTrace H β = spectralHeatSum hH.eigenvalues β := by
  unfold heatTrace spectralHeatSum
  rw [gibbsTraceExp_eq hH β]
  exact Complex.ofReal_re _

/-- The heat trace of a Hermitian operator is
positive (a nonempty spectral sum of exponentials). -/
theorem heatTrace_pos {H : Matrix m m ℂ}
    (hH : H.IsHermitian) (β : ℝ) [Nonempty m] :
    0 < heatTrace H β := by
  rw [heatTrace_eq_spectralHeatSum hH β]
  unfold spectralHeatSum
  exact Finset.sum_pos (fun i _ => Real.exp_pos _)
    Finset.univ_nonempty

/-- **KHP-4 (the contact, operator side).** The
corpus's finite Gibbs state IS the heat-kernel
state at `t = β`: its normalizer is the heat
trace — `gibbsForm H β = (heatTrace H β)⁻¹ •
exp(−βH)`, the scalar cast read on the complex
side. -/
theorem gibbsForm_eq_heatTrace {H : Matrix m m ℂ}
    (hH : H.IsHermitian) (β : ℝ) [Nonempty m] :
    gibbsForm H β
      = ((heatTrace H β : ℝ) : ℂ)⁻¹
        • NormedSpace.exp ((-(β:ℂ)) • H) := by
  have htr : Matrix.trace
        (NormedSpace.exp ((-(β:ℂ)) • H))
      = ((heatTrace H β : ℝ) : ℂ) := by
    rw [gibbsTraceExp_eq hH β,
      heatTrace_eq_spectralHeatSum hH β]
    rfl
  unfold gibbsForm
  rw [htr]

/-- **KHP-4 (the contact, energy side).** The total
mean energy of a finite family of independent
modes with energies `lam` at inverse temperature
`β` is the Planck sum: `U(β) = Σᵢ λᵢ ·
planckFactor β (λᵢ)` over positive modes — each
mode's mean occupation is KHP-2's factor.
ZERO-POINT EXCLUDED (the module's standing flag):
no `½λᵢ` term appears. -/
theorem gibbsMeanEnergy_eq {lam : m → ℝ} (β : ℝ)
    (hβ : 0 < β) (hpos : ∀ i, 0 < lam i) :
    gibbsMeanEnergy lam β
      = ∑ i, lam i * planckFactor β (lam i) := by
  unfold gibbsMeanEnergy
  exact Finset.sum_congr rfl
    (fun i _ => by
      rw [meanOccupation_eq_planck (hpos i) hβ])

end HeatTrace

end ThetLogos
