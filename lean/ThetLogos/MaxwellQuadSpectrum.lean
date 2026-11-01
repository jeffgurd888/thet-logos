import Mathlib.Tactic
import ThetLogos.MaxwellQuadAssembly

namespace ThetLogos

open Finset

/-!
# ThetLogos.MaxwellQuadSpectrum - MAX-3: the cube spectrum (FINITE)

**Status: MAX-3 landing brick. NO CLAIM. No Millennium
statement, no ladder rung, no dial (dials stay 0/4).**
Governing texts: the MAX-0 pin `MaxwellQuadPost.lean` (its
registered (M5) form governs exactly, including how the modes
and multiplicities are stated), MAX-2
`MaxwellQuadAssembly.lean` (`maxwellOp_apply`,
`maxwellOp_form`, `maxwellM1/M2/M3_proved`,
`maxwellOp_gaugeAngle`), under the scoping memo
`scoping-maxwell-finite-2026-10-31.md` sections 3-5.

## What is proved here, and the named seam (K-MAX-S)

(M5) as registered in the pin is a five-clause conjunction.
This brick discharges, at general Even `N`:

- clause 1: at every spatial momentum `k`, the FINITE
  transverse value `maxwellTransverseEig N k` is an
  eigenvalue of the pin's `maxwellOp N`, and `0` is an
  eigenvalue (the longitudinal / pure-gauge mode);
- clause 2: at `k ≠ 0`, the transverse eigenvalue carries
  two linearly independent eigenmodes (the registered
  pairwise-independence witness form);
- clause 3: the gap value `4 * sin^2(pi / N)` is an
  eigenvalue;
- clause 5: the momentum `(1, 0, 0)` attains the gap value.

**Named seam (K-MAX-S, reported exactly, not a verdict on
the line):** clause 4 of the registered (M5) - the statement
that *every* eigenvalue of `maxwellOp N` is either `0` or at
least `4 * sin^2(pi / N)` - is NOT discharged in this brick.
It is the global gap lower bound over the whole spectrum;
the Fourier diagonalization below computes the registered
eigenvalues and their modes, but the exclusion of any
further eigenvalue below the gap is a separate
Poincare-type inequality for the curl-curl operator on the
finite cube, overrunning this brick's band. It remains as
the named remaining clause: `maxwellM5` is therefore NOT
asserted here; what is asserted is the conjunction of
clauses 1, 2, 3 and 5, stated as
`maxwellM5_spectrum_part` below in the pin's exact clause
forms. Re-price: the clause-4 remainder is one
Poincare-inequality brick (discrete Wirtinger inequality on
the cycle, tensored over the cube, transported through the
Weitzenboeck identity `curl-curl + div-grad = Hodge`), est.
L band on its own.

## Fences (memo section 5, K-MAX-2)

Finite in every statement: every result here is about the
chosen finite operator on the finite link-angle space at
spacing 1; the transverse value is a property of that finite
operator and is never asserted as a continuum dispersion.
FENCE SENTENCE: the words "Lorentzian" and "bridge" are not
earned terms in this line and appear in this module only
inside this fence sentence. Disjoint from OP-1's photon (the
massless Higgs-sector direction) - no trading between the
two senses.

## K-MAX-1 re-check (on the face)

The diagonalization proved below is of the pin's
`maxwellOp N` itself, as assembled by MAX-2: the eigenvalue
equations are proved for `maxwellOp N` applied to the named
modes, through MAX-2's proved form identity
`maxwellOp_form` for the pin's polarization definition
`maxwellOp` (component formula `maxwellOp_apply`). No
Fourier-side operator is defined or diagonalized anywhere in
this module; the modes are link angles in the pin's own
link-angle space, and the operator acting on them is the
pin's. `maxwellOp` is not the transfer operator, the
plaquette block/factor, `magLin`, or the vertex `lapLin`,
and its form is not `osForm` (MAX-2's face carries the same
re-check).

## Method (all real, no complexification)

For a momentum profile `K : Fin 4 -> ZMod N` (with
`K 0 = 0`) and a real polarization `A : Fin 4 -> R`, the
cosine and sine link modes are
`cosMode K A l = A (dir l) * cos (sitePhase K (tail l) + phase (dir l))`
and the same with `sin`, where `phase mu = pi * (K mu).val / N`
is the half-angle and `sitePhase` is the lattice phase
`sum_mu 2 * phase mu * (coord mu).val`. The plaquette angle
of a mode is a single sine (resp. cosine) of the plaquette
phase, with amplitude `2 * (A mu * s nu - A nu * s mu)`,
`s mu = sin (phase mu)`. Summing the form identity over the
registered plaquette enumeration and reindexing sites by
the layer shifts collects, for each link direction `mu`,
the coefficient `4 * (A mu * s nu - A nu * s mu) * s nu`;
under the transversality condition `sum_nu A nu * s nu = 0`
this is `4 * (sum_nu s nu ^ 2) * A mu`, the registered
transverse eigenvalue times the mode. No mode definition is
adjusted to the registered numbers: the eigenvalue is read
off the computation (K-MAX-3 armed throughout; it does not
fire - the computed value is the registered one).

## Build note

`clause2` carries a scoped
`set_option maxHeartbeats 1600000 in` (eight times the
default): its case-split applications unify large
`Fin.cons` / `Pi.single` polarization terms against the
pin's clause form and exceed the default heartbeat budget
on this machine (verified: the default and 4x both time
out at `whnf`, 8x compiles). The kernel checks the
resulting proof terms as usual; the option changes no
statement.
-/

section FourierModes

variable {N : ℕ} [NeZero N]

/-- The **half-angle phase** of direction `mu` under the
momentum profile `K`: `pi * (K mu).val / N`. The full lattice
frequency in direction `mu` is twice this. -/
noncomputable def modePhase (K : Fin 4 → ZMod N) (μ : Fin 4) : ℝ :=
  Real.pi * ((K μ).val : ℝ) / (N : ℝ)

/-- The **transverse sine** of direction `mu`:
`s mu = sin (pi * (K mu).val / N)`. -/
noncomputable def modeSin (K : Fin 4 → ZMod N) (μ : Fin 4) : ℝ :=
  Real.sin (modePhase K μ)

/-- The **lattice phase** at a layer site: the sum over
directions of the full frequency times the coordinate value,
`sum_mu (2 * phase mu) * (c.1 mu).val`. -/
noncomputable def sitePhase (K : Fin 4 → ZMod N) (c : LayerSite N) : ℝ :=
  ∑ μ, (2 * modePhase K μ) * ((c.1 μ).val : ℝ)

/-- The **cosine Fourier link mode** of momentum profile `K`
and polarization `A`: at a link `l`, the polarization
component of the link's direction times the cosine of the
lattice phase at the link's tail, advanced by the direction's
half-angle (the link midpoint phase). -/
noncomputable def cosMode (K : Fin 4 → ZMod N) (A : Fin 4 → ℝ) :
    linkAngle N :=
  fun ℓ => A ℓ.1.2 * Real.cos (sitePhase K (linkTail ℓ) + modePhase K ℓ.1.2)

/-- The **sine Fourier link mode** of momentum profile `K`
and polarization `A`. -/
noncomputable def sinMode (K : Fin 4 → ZMod N) (A : Fin 4 → ℝ) :
    linkAngle N :=
  fun ℓ => A ℓ.1.2 * Real.sin (sitePhase K (linkTail ℓ) + modePhase K ℓ.1.2)

/-- The value of a link-indexed function read through a base
site and a direction: `linkVal F c mu = F (layerLinkOf c mu)`
when `mu ≠ 0`, and `0` at `mu = 0` (no link has direction
`0`). -/
noncomputable def linkVal (F : LayerLink N → ℝ) (c : LayerSite N)
    (μ : Fin 4) : ℝ :=
  if h : μ ≠ 0 then F (layerLinkOf c μ h) else 0

theorem linkVal_of_ne (F : LayerLink N → ℝ) (c : LayerSite N)
    {μ : Fin 4} (h : μ ≠ 0) :
    linkVal F c μ = F (layerLinkOf c μ h) :=
  dif_pos h

/-- Every link is the layer link of its tail in its own
direction, read through `linkVal`. -/
theorem linkVal_tail (F : LayerLink N → ℝ) (ℓ : LayerLink N) :
    linkVal F (linkTail ℓ) ℓ.1.2 = F ℓ :=
  dif_pos ℓ.2.2

/-- The mode value at an explicit layer link (cosine). -/
theorem cosMode_linkOf (K : Fin 4 → ZMod N) (A : Fin 4 → ℝ)
    (c : LayerSite N) (μ : Fin 4) (hμ : μ ≠ 0) :
    cosMode K A (layerLinkOf c μ hμ)
      = A μ * Real.cos (sitePhase K c + modePhase K μ) := rfl

/-- The mode value at an explicit layer link (sine). -/
theorem sinMode_linkOf (K : Fin 4 → ZMod N) (A : Fin 4 → ℝ)
    (c : LayerSite N) (μ : Fin 4) (hμ : μ ≠ 0) :
    sinMode K A (layerLinkOf c μ hμ)
      = A μ * Real.sin (sitePhase K c + modePhase K μ) := rfl

/-- The zero layer site (all coordinates `0`). -/
def zeroLayerSite : LayerSite N := ⟨0, by simp⟩

theorem sitePhase_zeroLayerSite (K : Fin 4 → ZMod N) :
    sitePhase K (zeroLayerSite (N := N)) = 0 := by
  apply Finset.sum_eq_zero
  intro μ _
  simp [zeroLayerSite]

end FourierModes

section SitePhaseShifts

variable {N : ℕ} [NeZero N]

/-- The unshift of a layer site in a spatial direction: the
coordinate in direction `nu` is decreased by `1`, all other
coordinates unchanged. It is the inverse of `layerShift`. -/
def layerUnshift (ν : Fin 4) (hν : ν ≠ 0) (c : LayerSite N) :
    LayerSite N :=
  ⟨Function.update c.1 ν (c.1 ν - 1), by
    rw [Function.update_of_ne (Ne.symm hν)]
    exact c.2⟩

theorem layerUnshift_coord_self (ν : Fin 4) (hν : ν ≠ 0)
    (c : LayerSite N) :
    (layerUnshift ν hν c).1 ν = c.1 ν - 1 :=
  Function.update_self ν _ _

theorem layerUnshift_coord_of_ne {ν j : Fin 4} (h : j ≠ ν)
    (hν : ν ≠ 0) (c : LayerSite N) :
    (layerUnshift ν hν c).1 j = c.1 j :=
  Function.update_of_ne h _ _

theorem layerShift_layerUnshift (ν : Fin 4) (hν : ν ≠ 0)
    (c : LayerSite N) :
    layerShift ν hν (layerUnshift ν hν c) = c := by
  apply Subtype.ext
  funext j
  show (torusShift N ν (layerUnshift ν hν c).1) j = c.1 j
  rw [torusShift_apply, Pi.add_apply]
  by_cases hj : j = ν
  · rw [hj, Pi.single_eq_same, layerUnshift_coord_self,
      add_comm 1 (c.1 ν - 1)]
    exact sub_add_cancel (c.1 ν) 1
  · rw [Pi.single_eq_of_ne hj, zero_add,
      layerUnshift_coord_of_ne hj hν]

theorem layerUnshift_layerShift (ν : Fin 4) (hν : ν ≠ 0)
    (c : LayerSite N) :
    layerUnshift ν hν (layerShift ν hν c) = c := by
  apply Subtype.ext
  funext j
  show Function.update (layerShift ν hν c).1 ν
      ((layerShift ν hν c).1 ν - 1) j = c.1 j
  by_cases hj : j = ν
  · rw [hj, Function.update_self]
    show (torusShift N ν c.1) ν - 1 = c.1 ν
    rw [torusShift_apply, Pi.add_apply, Pi.single_eq_same]
    exact add_sub_cancel_left 1 (c.1 ν)
  · rw [Function.update_of_ne hj]
    show (torusShift N ν c.1) j = c.1 j
    rw [torusShift_apply, Pi.add_apply, Pi.single_eq_of_ne hj, zero_add]

/-- `layerShift` is a bijection of the layer sites. -/
theorem bijective_layerShift (ν : Fin 4) (hν : ν ≠ 0) :
    Function.Bijective (layerShift ν hν : LayerSite N → LayerSite N) :=
  ⟨Function.LeftInverse.injective (layerUnshift_layerShift ν hν),
    Function.LeftInverse.surjective (layerShift_layerUnshift ν hν)⟩

/-- `layerUnshift` is a bijection of the layer sites. -/
theorem bijective_layerUnshift (ν : Fin 4) (hν : ν ≠ 0) :
    Function.Bijective (layerUnshift ν hν : LayerSite N → LayerSite N) :=
  ⟨Function.LeftInverse.injective (layerShift_layerUnshift ν hν),
    Function.LeftInverse.surjective (layerUnshift_layerShift ν hν)⟩

/-- Sum invariance under a layer shift. -/
theorem sum_layerShift (ν : Fin 4) (hν : ν ≠ 0)
    (F : LayerSite N → ℝ) :
    (∑ c, F (layerShift ν hν c)) = ∑ c, F c :=
  Fintype.sum_bijective _ (bijective_layerShift ν hν)
    (fun c => F (layerShift ν hν c)) F (fun c => rfl)

/-- Sum invariance under a layer unshift. -/
theorem sum_layerUnshift (ν : Fin 4) (hν : ν ≠ 0)
    (F : LayerSite N → ℝ) :
    (∑ c, F (layerUnshift ν hν c)) = ∑ c, F c :=
  Fintype.sum_bijective _ (bijective_layerUnshift ν hν)
    (fun c => F (layerUnshift ν hν c)) F (fun c => rfl)

/-- The coordinate of a shifted site away from the shift
direction is unchanged. -/
theorem layerShift_coord_of_ne {ν j : Fin 4} (h : j ≠ ν)
    (hν : ν ≠ 0) (c : LayerSite N) :
    (layerShift ν hν c).1 j = c.1 j := by
  show (torusShift N ν c.1) j = c.1 j
  rw [torusShift_apply, Pi.add_apply, Pi.single_eq_of_ne h, zero_add]

/-- The coordinate of a shifted site along the shift
direction is one more. -/
theorem layerShift_coord_self (ν : Fin 4) (hν : ν ≠ 0)
    (c : LayerSite N) :
    (layerShift ν hν c).1 ν = c.1 ν + 1 := by
  show (torusShift N ν c.1) ν = c.1 ν + 1
  rw [torusShift_apply, Pi.add_apply, Pi.single_eq_same, add_comm]

end SitePhaseShifts

section PhaseShiftValues

variable {N : ℕ} [NeZero N]

/-- A real-cast form of `Nat.div_add_mod`:
`((a % N : ℕ) : ℝ) = a - N * (a / N)`. -/
theorem nat_mod_real (a N : ℕ) :
    ((a % N : ℕ) : ℝ) = (a : ℝ) - (N : ℝ) * ((a / N : ℕ) : ℝ) := by
  have h2 : (N : ℝ) * ((a / N : ℕ) : ℝ) + ((a % N : ℕ) : ℝ)
      = (a : ℝ) := by
    exact_mod_cast Nat.div_add_mod a N
  linarith

/-- The real value of the coordinate after a `+1` shift in
`ZMod N`: it is `val + 1` minus `N` times the wrap count
`((val + 1) / N) ∈ {0, 1}`. -/
theorem coord_val_add_one (hN : 2 ≤ N) (x : ZMod N) :
    ((x + 1).val : ℝ)
      = (x.val : ℝ) + 1 - (N : ℝ) * (((x.val + 1) / N : ℕ) : ℝ) := by
  have h1 : (1 : ZMod N).val = 1 := by
    rw [ZMod.val_one_eq_one_mod]
    exact Nat.mod_eq_of_lt (by omega)
  have h2 : (x + 1).val = (x.val + 1) % N := by
    rw [ZMod.val_add, h1]
  rw [h2, nat_mod_real]
  push_cast
  ring

/-- The value of `-1` in `ZMod N` is `N - 1`. -/
theorem neg_one_val (hN : 2 ≤ N) : (-1 : ZMod N).val = N - 1 := by
  have h : (-1 : ZMod N) = ((N - 1 : ℕ) : ZMod N) := by
    rw [Nat.cast_sub (by omega : 1 ≤ N), ZMod.natCast_self, Nat.cast_one,
      zero_sub]
  rw [h]
  exact ZMod.val_natCast_of_lt (by omega)

/-- The real value of the coordinate after a `-1` shift in
`ZMod N`. -/
theorem coord_val_sub_one (hN : 2 ≤ N) (x : ZMod N) :
    ((x - 1).val : ℝ)
      = (x.val : ℝ) + ((N : ℝ) - 1)
        - (N : ℝ) * (((x.val + (N - 1)) / N : ℕ) : ℝ) := by
  have h2 : (x - 1).val = (x.val + (N - 1)) % N := by
    have hx : x - 1 = x + (-1) := sub_eq_add_neg x 1
    rw [hx, ZMod.val_add, neg_one_val (N := N) hN]
  have hcast : ((x.val + (N - 1) : ℕ) : ℝ)
      = (x.val : ℝ) + ((N : ℝ) - 1) := by
    rw [Nat.cast_add, Nat.cast_sub (by omega : 1 ≤ N), Nat.cast_one]
  rw [h2, nat_mod_real, hcast]

/-- Splitting a sum over `Fin 4` at one index. -/
theorem sum_split (ν : Fin 4) (F : Fin 4 → ℝ) :
    (∑ μ, F μ) = F ν + ∑ μ ∈ Finset.univ.erase ν, F μ :=
  (Finset.add_sum_erase Finset.univ F (Finset.mem_univ ν)).symm

/-- The wrap count for a `+1` shift of the `nu` coordinate of
the site `c`, times the momentum value: the integer whose
multiple of `2 * pi` the site phase loses on a wrap. -/
def shiftWrap (K : Fin 4 → ZMod N) (ν : Fin 4) (c : LayerSite N) : ℕ :=
  ((c.1 ν).val + 1) / N * (K ν).val

/-- The integer whose multiple of `2 * pi` the site phase
gains on an unshift wrap. -/
def unshiftWrap (K : Fin 4 → ZMod N) (ν : Fin 4) (c : LayerSite N) : ℤ :=
  ((K ν).val : ℤ) * (1 - ((((c.1 ν).val + (N - 1)) / N : ℕ) : ℤ))

/-- The wrap identity for the full frequency:
`2 * phase * (N * d) = (d * (K nu).val) * (2 * pi)`. -/
theorem modePhase_mul (K : Fin 4 → ZMod N) (ν : Fin 4) (d : ℕ) :
    2 * modePhase K ν * ((N : ℝ) * (d : ℝ))
      = ((d * (K ν).val : ℕ) : ℝ) * (2 * Real.pi) := by
  have hN0 : (N : ℝ) ≠ 0 := by
    have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
    positivity
  unfold modePhase
  push_cast
  field_simp

/-- The site phase after a layer shift: it advances by the
full frequency in the shift direction, minus an integer
multiple of `2 * pi` (the wrap term). -/
theorem sitePhase_layerShift (hN : 2 ≤ N) (K : Fin 4 → ZMod N)
    (ν : Fin 4) (hν : ν ≠ 0) (c : LayerSite N) :
    sitePhase K (layerShift ν hν c)
      = sitePhase K c + 2 * modePhase K ν
        - ((shiftWrap K ν c : ℤ) : ℝ) * (2 * Real.pi) := by
  have e1 : sitePhase K (layerShift ν hν c)
      = ∑ μ, (2 * modePhase K μ) * ((layerShift ν hν c).1 μ).val := rfl
  have e2 : sitePhase K c
      = ∑ μ, (2 * modePhase K μ) * ((c.1 μ).val : ℝ) := rfl
  have hterm : (2 * modePhase K ν) * ((layerShift ν hν c).1 ν).val
      = (2 * modePhase K ν) * (c.1 ν).val + 2 * modePhase K ν
        - ((shiftWrap K ν c : ℤ) : ℝ) * (2 * Real.pi) := by
    rw [layerShift_coord_self, coord_val_add_one hN]
    have hm : 2 * modePhase K ν
          * ((N : ℝ) * (((c.1 ν).val + 1) / N : ℕ))
        = ((shiftWrap K ν c : ℤ) : ℝ) * (2 * Real.pi) := by
      have hm2 := modePhase_mul K ν (((c.1 ν).val + 1) / N)
      rw [show ((shiftWrap K ν c : ℤ) : ℝ)
          = ((shiftWrap K ν c : ℕ) : ℝ) from Int.cast_natCast _]
      exact hm2
    linarith [hm]
  have hrest : (∑ μ ∈ Finset.univ.erase ν,
        (2 * modePhase K μ) * ((layerShift ν hν c).1 μ).val)
      = ∑ μ ∈ Finset.univ.erase ν,
        (2 * modePhase K μ) * ((c.1 μ).val) := by
    apply Finset.sum_congr rfl
    intro μ hμ
    have hμν : μ ≠ ν := (Finset.mem_erase.mp hμ).1
    rw [layerShift_coord_of_ne hμν hν]
  rw [e1, e2, sum_split ν, sum_split ν, hterm, hrest]
  ring

/-- The site phase after a layer unshift: it retreats by the
full frequency in the shift direction, plus an integer
multiple of `2 * pi`. -/
theorem sitePhase_layerUnshift (hN : 2 ≤ N) (K : Fin 4 → ZMod N)
    (ν : Fin 4) (hν : ν ≠ 0) (c : LayerSite N) :
    sitePhase K (layerUnshift ν hν c)
      = sitePhase K c - 2 * modePhase K ν
        + ((unshiftWrap K ν c : ℝ)) * (2 * Real.pi) := by
  have e1 : sitePhase K (layerUnshift ν hν c)
      = ∑ μ, (2 * modePhase K μ) * ((layerUnshift ν hν c).1 μ).val := rfl
  have e2 : sitePhase K c
      = ∑ μ, (2 * modePhase K μ) * ((c.1 μ).val : ℝ) := rfl
  have hval : ((layerUnshift ν hν c).1 ν).val
      = (c.1 ν).val + ((N : ℝ) - 1)
        - (N : ℝ) * ((((c.1 ν).val + (N - 1)) / N : ℕ) : ℝ) := by
    rw [layerUnshift_coord_self]
    exact coord_val_sub_one hN (c.1 ν)
  have hterm : (2 * modePhase K ν) * ((layerUnshift ν hν c).1 ν).val
      = (2 * modePhase K ν) * (c.1 ν).val - 2 * modePhase K ν
        + ((unshiftWrap K ν c : ℝ)) * (2 * Real.pi) := by
    rw [hval]
    have hm' : 2 * modePhase K ν * (N : ℝ)
        = ((K ν).val : ℝ) * (2 * Real.pi) := by
      have hm2 := modePhase_mul K ν 1
      push_cast at hm2
      linarith [hm2]
    have hm'e : 2 * modePhase K ν * (N : ℝ)
          * ((((c.1 ν).val + (N - 1)) / N : ℕ) : ℝ)
        = ((K ν).val : ℝ) * (2 * Real.pi)
          * ((((c.1 ν).val + (N - 1)) / N : ℕ) : ℝ) :=
      congrArg (· * ((((c.1 ν).val + (N - 1)) / N : ℕ) : ℝ)) hm'
    have hwrap : ((unshiftWrap K ν c : ℝ)) * (2 * Real.pi)
        = ((K ν).val : ℝ) * (2 * Real.pi)
          - ((K ν).val : ℝ) * (2 * Real.pi)
            * ((((c.1 ν).val + (N - 1)) / N : ℕ) : ℝ) := by
      unfold unshiftWrap
      simp only [Int.cast_mul, Int.cast_sub, Int.cast_one, Int.cast_natCast]
      ring
    linarith [hm', hm'e, hwrap]
  have hrest : (∑ μ ∈ Finset.univ.erase ν,
        (2 * modePhase K μ) * ((layerUnshift ν hν c).1 μ).val)
      = ∑ μ ∈ Finset.univ.erase ν,
        (2 * modePhase K μ) * ((c.1 μ).val) := by
    apply Finset.sum_congr rfl
    intro μ hμ
    have hμν : μ ≠ ν := (Finset.mem_erase.mp hμ).1
    rw [layerUnshift_coord_of_ne hμν hν]
  rw [e1, e2, sum_split ν, sum_split ν, hterm, hrest]
  ring

/-- Cosine of the site phase after a layer shift. -/
theorem cos_sitePhase_layerShift (hN : 2 ≤ N) (K : Fin 4 → ZMod N)
    (ν : Fin 4) (hν : ν ≠ 0) (c : LayerSite N) (t : ℝ) :
    Real.cos (sitePhase K (layerShift ν hν c) + t)
      = Real.cos (sitePhase K c + 2 * modePhase K ν + t) := by
  rw [sitePhase_layerShift hN K ν hν c]
  have harg : sitePhase K c + 2 * modePhase K ν
        - ((shiftWrap K ν c : ℤ) : ℝ) * (2 * Real.pi) + t
      = (sitePhase K c + 2 * modePhase K ν + t)
        - (shiftWrap K ν c : ℤ) * (2 * Real.pi) := by ring
  rw [harg, Real.cos_sub_int_mul_two_pi]

/-- Sine of the site phase after a layer shift. -/
theorem sin_sitePhase_layerShift (hN : 2 ≤ N) (K : Fin 4 → ZMod N)
    (ν : Fin 4) (hν : ν ≠ 0) (c : LayerSite N) (t : ℝ) :
    Real.sin (sitePhase K (layerShift ν hν c) + t)
      = Real.sin (sitePhase K c + 2 * modePhase K ν + t) := by
  rw [sitePhase_layerShift hN K ν hν c]
  have harg : sitePhase K c + 2 * modePhase K ν
        - ((shiftWrap K ν c : ℤ) : ℝ) * (2 * Real.pi) + t
      = (sitePhase K c + 2 * modePhase K ν + t)
        - (shiftWrap K ν c : ℤ) * (2 * Real.pi) := by ring
  rw [harg, Real.sin_sub_int_mul_two_pi]

/-- Cosine of the site phase after a layer unshift. -/
theorem cos_sitePhase_layerUnshift (hN : 2 ≤ N) (K : Fin 4 → ZMod N)
    (ν : Fin 4) (hν : ν ≠ 0) (c : LayerSite N) (t : ℝ) :
    Real.cos (sitePhase K (layerUnshift ν hν c) + t)
      = Real.cos (sitePhase K c - 2 * modePhase K ν + t) := by
  rw [sitePhase_layerUnshift hN K ν hν c]
  have harg : sitePhase K c - 2 * modePhase K ν
        + ((unshiftWrap K ν c : ℝ)) * (2 * Real.pi) + t
      = (sitePhase K c - 2 * modePhase K ν + t)
        + (unshiftWrap K ν c) * (2 * Real.pi) := by ring
  rw [harg, Real.cos_add_int_mul_two_pi]

/-- Sine of the site phase after a layer unshift. -/
theorem sin_sitePhase_layerUnshift (hN : 2 ≤ N) (K : Fin 4 → ZMod N)
    (ν : Fin 4) (hν : ν ≠ 0) (c : LayerSite N) (t : ℝ) :
    Real.sin (sitePhase K (layerUnshift ν hν c) + t)
      = Real.sin (sitePhase K c - 2 * modePhase K ν + t) := by
  rw [sitePhase_layerUnshift hN K ν hν c]
  have harg : sitePhase K c - 2 * modePhase K ν
        + ((unshiftWrap K ν c : ℝ)) * (2 * Real.pi) + t
      = (sitePhase K c - 2 * modePhase K ν + t)
        + (unshiftWrap K ν c) * (2 * Real.pi) := by ring
  rw [harg, Real.sin_add_int_mul_two_pi]

end PhaseShiftValues

section PlaqEnumeration

variable {N : ℕ} [NeZero N]

open Classical in
/-- A plaquette datum in the registered enumeration's
singleton set has the expected base, `mu` and `nu`. -/
theorem mem_plaqSet {c : LayerSite N} {μ ν : Fin 4}
    {P : PlaqDatum N}
    (hP : P ∈ (if h : μ ≠ 0 ∧ ν ≠ 0 ∧ μ < ν
      then ({⟨c, μ, ν, h.1, h.2.1, ne_of_lt h.2.2⟩}
        : Finset (PlaqDatum N)) else ∅)) :
    P.base = c ∧ P.mu = μ ∧ P.nu = ν := by
  by_cases h : μ ≠ 0 ∧ ν ≠ 0 ∧ μ < ν
  · rw [dif_pos h] at hP
    simp only [Finset.mem_singleton] at hP
    subst hP
    exact ⟨rfl, rfl, rfl⟩
  · rw [dif_neg h] at hP
    exact absurd hP (Finset.notMem_empty P)

/-- The registered plaquette enumeration, expanded as a
triple sum over base sites and ordered direction pairs. -/
theorem sum_allPlaqData (F : PlaqDatum N → ℝ) :
    ∑ P ∈ allPlaqData N, F P
      = ∑ c, ∑ μ, ∑ ν, (if h : μ ≠ 0 ∧ ν ≠ 0 ∧ μ < ν
          then F ⟨c, μ, ν, h.1, h.2.1, ne_of_lt h.2.2⟩ else 0) := by
  classical
  have hdν : ∀ (c : LayerSite N) (μ ν ν' : Fin 4), ν ≠ ν' →
      Disjoint
        (if h : μ ≠ 0 ∧ ν ≠ 0 ∧ μ < ν
          then ({⟨c, μ, ν, h.1, h.2.1, ne_of_lt h.2.2⟩}
            : Finset (PlaqDatum N))
          else ∅)
        (if h : μ ≠ 0 ∧ ν' ≠ 0 ∧ μ < ν'
          then ({⟨c, μ, ν', h.1, h.2.1, ne_of_lt h.2.2⟩}
            : Finset (PlaqDatum N))
          else ∅) := by
    intro c μ ν ν' hνν'
    rw [Finset.disjoint_left]
    intro P hP hP'
    have h1 := (mem_plaqSet hP).2.2
    have h2 := (mem_plaqSet hP').2.2
    exact hνν' (h1 ▸ h2)
  have hdμ : ∀ (c : LayerSite N) (μ μ' : Fin 4), μ ≠ μ' →
      Disjoint
        ((Finset.univ.biUnion (fun ν =>
          if h : μ ≠ 0 ∧ ν ≠ 0 ∧ μ < ν
            then ({⟨c, μ, ν, h.1, h.2.1, ne_of_lt h.2.2⟩}
              : Finset (PlaqDatum N))
            else ∅)) : Finset (PlaqDatum N))
        ((Finset.univ.biUnion (fun ν =>
          if h : μ' ≠ 0 ∧ ν ≠ 0 ∧ μ' < ν
            then ({⟨c, μ', ν, h.1, h.2.1, ne_of_lt h.2.2⟩}
              : Finset (PlaqDatum N))
            else ∅)) : Finset (PlaqDatum N)) := by
    intro c μ μ' hμμ'
    rw [Finset.disjoint_left]
    intro P hP hP'
    obtain ⟨ν, _, hP⟩ := Finset.mem_biUnion.mp hP
    obtain ⟨ν', _, hP'⟩ := Finset.mem_biUnion.mp hP'
    have h1 := (mem_plaqSet hP).2.1
    have h2 := (mem_plaqSet hP').2.1
    exact hμμ' (h1 ▸ h2)
  have hdc : ∀ (c c' : LayerSite N), c ≠ c' →
      Disjoint
        ((Finset.univ.biUnion (fun μ => Finset.univ.biUnion (fun ν =>
          if h : μ ≠ 0 ∧ ν ≠ 0 ∧ μ < ν
            then ({⟨c, μ, ν, h.1, h.2.1, ne_of_lt h.2.2⟩}
              : Finset (PlaqDatum N))
            else ∅))) : Finset (PlaqDatum N))
        ((Finset.univ.biUnion (fun μ => Finset.univ.biUnion (fun ν =>
          if h : μ ≠ 0 ∧ ν ≠ 0 ∧ μ < ν
            then ({⟨c', μ, ν, h.1, h.2.1, ne_of_lt h.2.2⟩}
              : Finset (PlaqDatum N))
            else ∅))) : Finset (PlaqDatum N)) := by
    intro c c' hcc'
    rw [Finset.disjoint_left]
    intro P hP hP'
    obtain ⟨μ, _, hP⟩ := Finset.mem_biUnion.mp hP
    obtain ⟨ν, _, hP⟩ := Finset.mem_biUnion.mp hP
    obtain ⟨μ', _, hP'⟩ := Finset.mem_biUnion.mp hP'
    obtain ⟨ν', _, hP'⟩ := Finset.mem_biUnion.mp hP'
    have h1 := (mem_plaqSet hP).1
    have h2 := (mem_plaqSet hP').1
    exact hcc' (h1 ▸ h2)
  unfold allPlaqData
  rw [Finset.sum_biUnion (fun c _ c' _ hcc' => hdc c c' hcc')]
  apply Finset.sum_congr rfl
  intro c _
  rw [Finset.sum_biUnion (fun μ _ μ' _ hμμ' => hdμ c μ μ' hμμ')]
  apply Finset.sum_congr rfl
  intro μ _
  rw [Finset.sum_biUnion (fun ν _ ν' _ hνν' => hdν c μ ν ν' hνν')]
  apply Finset.sum_congr rfl
  intro ν _
  by_cases h : μ ≠ 0 ∧ ν ≠ 0 ∧ μ < ν <;> simp [h]

/-- The link value at a site shifted in direction `mu`,
read in direction `nu` (with the `mu = 0` case set to `0`). -/
noncomputable def shiftLinkVal (F : LayerLink N → ℝ) (c : LayerSite N)
    (μ ν : Fin 4) : ℝ :=
  if h : μ ≠ 0 then linkVal F (layerShift μ h c) ν else 0

theorem shiftLinkVal_of_ne (F : LayerLink N → ℝ) (c : LayerSite N)
    {μ : Fin 4} (hμ : μ ≠ 0) (ν : Fin 4) :
    shiftLinkVal F c μ ν = linkVal F (layerShift μ hμ c) ν :=
  dif_pos hμ

/-- The **plaquette form**: the plaquette angle of `F` at
base site `c` in directions `(mu, nu)`, as a total function
of the ordered pair `(mu, nu)`:
`F(c,mu) + F(c+mu,nu) - F(c+nu,mu) - F(c,nu)`. It agrees with
`plaqAngle` at every registered plaquette datum. -/
noncomputable def plaqForm (F : LayerLink N → ℝ) (c : LayerSite N)
    (μ ν : Fin 4) : ℝ :=
  linkVal F c μ + shiftLinkVal F c μ ν
    - shiftLinkVal F c ν μ - linkVal F c ν

/-- The plaquette angle at a datum, in `linkVal` form. -/
theorem plaqAngle_datum (F : LayerLink N → ℝ) (c : LayerSite N)
    (μ ν : Fin 4) (hμ : μ ≠ 0) (hν : ν ≠ 0) (hne : μ ≠ ν) :
    plaqAngle ⟨c, μ, ν, hμ, hν, hne⟩ F
      = linkVal F c μ + linkVal F (layerShift μ hμ c) ν
        - linkVal F (layerShift ν hν c) μ - linkVal F c ν := by
  have hrw : plaqAngle ⟨c, μ, ν, hμ, hν, hne⟩ F
      = F (layerLinkOf c μ hμ)
        + F (layerLinkOf (layerShift μ hμ c) ν hν)
        - F (layerLinkOf (layerShift ν hν c) μ hμ)
        - F (layerLinkOf c ν hν) := rfl
  rw [hrw, ← linkVal_of_ne F c hμ,
    ← linkVal_of_ne F (layerShift μ hμ c) hν,
    ← linkVal_of_ne F (layerShift ν hν c) hμ,
    ← linkVal_of_ne F c hν]

/-- `plaqForm` agrees with `plaqAngle` at a datum. -/
theorem plaqForm_eq (F : LayerLink N → ℝ) (c : LayerSite N)
    (μ ν : Fin 4) (hμ : μ ≠ 0) (hν : ν ≠ 0) (hne : μ ≠ ν) :
    plaqForm F c μ ν = plaqAngle ⟨c, μ, ν, hμ, hν, hne⟩ F := by
  rw [plaqAngle_datum]
  unfold plaqForm
  rw [shiftLinkVal_of_ne F c hμ, shiftLinkVal_of_ne F c hν]

/-- `plaqForm` is antisymmetric in its two directions. -/
theorem plaqForm_antisymm (F : LayerLink N → ℝ) (c : LayerSite N)
    (μ ν : Fin 4) :
    plaqForm F c ν μ = -plaqForm F c μ ν := by
  unfold plaqForm
  ring

/-- `plaqForm` on a repeated direction vanishes. -/
theorem plaqForm_self (F : LayerLink N → ℝ) (c : LayerSite N)
    (μ : Fin 4) :
    plaqForm F c μ μ = 0 := by
  unfold plaqForm
  ring

end PlaqEnumeration

section ModePlaquettes

variable {N : ℕ} [NeZero N]

/-- The **cosine mode's plaquette form**: the value the
plaquette angle of `cosMode K A` takes at base site `c` in
directions `(mu, nu)`:
`2 * (A mu * s nu - A nu * s mu) * sin (phase + ph mu + ph nu)`. -/
noncomputable def cosModeForm (K : Fin 4 → ZMod N) (A : Fin 4 → ℝ)
    (c : LayerSite N) (μ ν : Fin 4) : ℝ :=
  2 * (A μ * modeSin K ν - A ν * modeSin K μ)
    * Real.sin (sitePhase K c + modePhase K μ + modePhase K ν)

/-- The **sine mode's plaquette form**. -/
noncomputable def sinModeForm (K : Fin 4 → ZMod N) (A : Fin 4 → ℝ)
    (c : LayerSite N) (μ ν : Fin 4) : ℝ :=
  -2 * (A μ * modeSin K ν - A ν * modeSin K μ)
    * Real.cos (sitePhase K c + modePhase K μ + modePhase K ν)

theorem cosModeForm_antisymm (K : Fin 4 → ZMod N) (A : Fin 4 → ℝ)
    (c : LayerSite N) (μ ν : Fin 4) :
    cosModeForm K A c ν μ = -cosModeForm K A c μ ν := by
  unfold cosModeForm
  have harg : sitePhase K c + modePhase K ν + modePhase K μ
      = sitePhase K c + modePhase K μ + modePhase K ν := by ring
  rw [harg]
  ring

theorem sinModeForm_antisymm (K : Fin 4 → ZMod N) (A : Fin 4 → ℝ)
    (c : LayerSite N) (μ ν : Fin 4) :
    sinModeForm K A c ν μ = -sinModeForm K A c μ ν := by
  unfold sinModeForm
  have harg : sitePhase K c + modePhase K ν + modePhase K μ
      = sitePhase K c + modePhase K μ + modePhase K ν := by ring
  rw [harg]
  ring

/-- The plaquette angle of the cosine mode at a datum is its
plaquette form. -/
theorem plaqAngle_cosMode (hN : 2 ≤ N) (K : Fin 4 → ZMod N)
    (A : Fin 4 → ℝ) (P : PlaqDatum N) :
    plaqAngle P (cosMode K A) = cosModeForm K A P.base P.mu P.nu := by
  obtain ⟨c, μ, ν, hμ, hν, hne⟩ := P
  rw [plaqAngle_datum, linkVal_of_ne _ _ hμ, linkVal_of_ne _ _ hν,
    linkVal_of_ne _ _ hμ, linkVal_of_ne _ _ hν,
    cosMode_linkOf, cosMode_linkOf, cosMode_linkOf, cosMode_linkOf,
    cos_sitePhase_layerShift hN K μ hμ c (modePhase K ν),
    cos_sitePhase_layerShift hN K ν hν c (modePhase K μ)]
  have hb1 : Real.cos (sitePhase K c + modePhase K μ)
        - Real.cos (sitePhase K c + 2 * modePhase K ν + modePhase K μ)
      = 2 * modeSin K ν
        * Real.sin (sitePhase K c + modePhase K μ + modePhase K ν) := by
    have h := Real.cos_sub_cos (sitePhase K c + modePhase K μ)
      (sitePhase K c + 2 * modePhase K ν + modePhase K μ)
    rw [show (sitePhase K c + modePhase K μ
          + (sitePhase K c + 2 * modePhase K ν + modePhase K μ)) / 2
        = sitePhase K c + modePhase K μ + modePhase K ν by ring,
      show (sitePhase K c + modePhase K μ
          - (sitePhase K c + 2 * modePhase K ν + modePhase K μ)) / 2
        = -modePhase K ν by ring, Real.sin_neg] at h
    rw [h]
    unfold modeSin
    ring
  have hb2 : Real.cos (sitePhase K c + 2 * modePhase K μ + modePhase K ν)
        - Real.cos (sitePhase K c + modePhase K ν)
      = -2 * modeSin K μ
        * Real.sin (sitePhase K c + modePhase K μ + modePhase K ν) := by
    have h := Real.cos_sub_cos
      (sitePhase K c + 2 * modePhase K μ + modePhase K ν)
      (sitePhase K c + modePhase K ν)
    rw [show (sitePhase K c + 2 * modePhase K μ + modePhase K ν
          + (sitePhase K c + modePhase K ν)) / 2
        = sitePhase K c + modePhase K μ + modePhase K ν by ring,
      show (sitePhase K c + 2 * modePhase K μ + modePhase K ν
          - (sitePhase K c + modePhase K ν)) / 2
        = modePhase K μ by ring] at h
    rw [h]
    unfold modeSin
    ring
  calc A μ * Real.cos (sitePhase K c + modePhase K μ)
        + A ν * Real.cos (sitePhase K c + 2 * modePhase K μ + modePhase K ν)
        - A μ * Real.cos (sitePhase K c + 2 * modePhase K ν + modePhase K μ)
        - A ν * Real.cos (sitePhase K c + modePhase K ν)
      = A μ * (Real.cos (sitePhase K c + modePhase K μ)
          - Real.cos (sitePhase K c + 2 * modePhase K ν + modePhase K μ))
        + A ν * (Real.cos (sitePhase K c + 2 * modePhase K μ + modePhase K ν)
          - Real.cos (sitePhase K c + modePhase K ν)) := by ring
    _ = A μ * (2 * modeSin K ν
          * Real.sin (sitePhase K c + modePhase K μ + modePhase K ν))
        + A ν * (-2 * modeSin K μ
          * Real.sin (sitePhase K c + modePhase K μ + modePhase K ν)) := by
        rw [hb1, hb2]
    _ = cosModeForm K A c μ ν := by
        unfold cosModeForm
        ring

/-- The plaquette angle of the sine mode at a datum is its
plaquette form. -/
theorem plaqAngle_sinMode (hN : 2 ≤ N) (K : Fin 4 → ZMod N)
    (A : Fin 4 → ℝ) (P : PlaqDatum N) :
    plaqAngle P (sinMode K A) = sinModeForm K A P.base P.mu P.nu := by
  obtain ⟨c, μ, ν, hμ, hν, hne⟩ := P
  rw [plaqAngle_datum, linkVal_of_ne _ _ hμ, linkVal_of_ne _ _ hν,
    linkVal_of_ne _ _ hμ, linkVal_of_ne _ _ hν,
    sinMode_linkOf, sinMode_linkOf, sinMode_linkOf, sinMode_linkOf,
    sin_sitePhase_layerShift hN K μ hμ c (modePhase K ν),
    sin_sitePhase_layerShift hN K ν hν c (modePhase K μ)]
  have hb1 : Real.sin (sitePhase K c + modePhase K μ)
        - Real.sin (sitePhase K c + 2 * modePhase K ν + modePhase K μ)
      = -2 * modeSin K ν
        * Real.cos (sitePhase K c + modePhase K μ + modePhase K ν) := by
    have h := Real.sin_sub_sin (sitePhase K c + modePhase K μ)
      (sitePhase K c + 2 * modePhase K ν + modePhase K μ)
    rw [show (sitePhase K c + modePhase K μ
          + (sitePhase K c + 2 * modePhase K ν + modePhase K μ)) / 2
        = sitePhase K c + modePhase K μ + modePhase K ν by ring,
      show (sitePhase K c + modePhase K μ
          - (sitePhase K c + 2 * modePhase K ν + modePhase K μ)) / 2
        = -modePhase K ν by ring, Real.sin_neg] at h
    rw [h]
    unfold modeSin
    ring
  have hb2 : Real.sin (sitePhase K c + 2 * modePhase K μ + modePhase K ν)
        - Real.sin (sitePhase K c + modePhase K ν)
      = 2 * modeSin K μ
        * Real.cos (sitePhase K c + modePhase K μ + modePhase K ν) := by
    have h := Real.sin_sub_sin
      (sitePhase K c + 2 * modePhase K μ + modePhase K ν)
      (sitePhase K c + modePhase K ν)
    rw [show (sitePhase K c + 2 * modePhase K μ + modePhase K ν
          + (sitePhase K c + modePhase K ν)) / 2
        = sitePhase K c + modePhase K μ + modePhase K ν by ring,
      show (sitePhase K c + 2 * modePhase K μ + modePhase K ν
          - (sitePhase K c + modePhase K ν)) / 2
        = modePhase K μ by ring] at h
    rw [h]
    unfold modeSin
    ring
  calc A μ * Real.sin (sitePhase K c + modePhase K μ)
        + A ν * Real.sin (sitePhase K c + 2 * modePhase K μ + modePhase K ν)
        - A μ * Real.sin (sitePhase K c + 2 * modePhase K ν + modePhase K μ)
        - A ν * Real.sin (sitePhase K c + modePhase K ν)
      = A μ * (Real.sin (sitePhase K c + modePhase K μ)
          - Real.sin (sitePhase K c + 2 * modePhase K ν + modePhase K μ))
        + A ν * (Real.sin (sitePhase K c + 2 * modePhase K μ + modePhase K ν)
          - Real.sin (sitePhase K c + modePhase K ν)) := by ring
    _ = A μ * (-2 * modeSin K ν
          * Real.cos (sitePhase K c + modePhase K μ + modePhase K ν))
        + A ν * (2 * modeSin K μ
          * Real.cos (sitePhase K c + modePhase K μ + modePhase K ν)) := by
        rw [hb1, hb2]
    _ = sinModeForm K A c μ ν := by
        unfold sinModeForm
        ring

end ModePlaquettes

section PairCollection

variable {N : ℕ} [NeZero N]

/-- **Pair collection.** For any site function `M` whose
values at a site and at the two unshifts of it differ by the
site functions `Cmu`, `Cnu`, the plaquette-form sum against
`M` collects into link-value terms:
`∑ c, plaqForm η c μ ν * M c
  = ∑ c, (linkVal η c μ * Cμ c + linkVal η c ν * Cν c)`.
This is the discrete integration by parts at one plaquette
orientation: the two shifted link values in `plaqForm` are
reindexed by the layer unshifts. -/
theorem sum_plaqForm_mul (η : linkAngle N) (μ ν : Fin 4)
    (hμ : μ ≠ 0) (hν : ν ≠ 0) (M Cμ Cν : LayerSite N → ℝ)
    (hμid : ∀ c, M c - M (layerUnshift ν hν c) = Cμ c)
    (hνid : ∀ c, M (layerUnshift μ hμ c) - M c = Cν c) :
    (∑ c, plaqForm η c μ ν * M c)
      = ∑ c, (linkVal η c μ * Cμ c + linkVal η c ν * Cν c) := by
  have hre1 : (∑ c, shiftLinkVal η c μ ν * M c)
      = ∑ c, linkVal η c ν * M (layerUnshift μ hμ c) := by
    have h1 : (∑ c, shiftLinkVal η c μ ν * M c)
        = ∑ c, linkVal η (layerShift μ hμ c) ν * M c :=
      Finset.sum_congr rfl (fun c _ => by rw [shiftLinkVal_of_ne])
    have h2 : (∑ c, linkVal η c ν * M (layerUnshift μ hμ c))
        = ∑ c, linkVal η (layerShift μ hμ c) ν * M c := by
      have h := sum_layerUnshift μ hμ
        (fun c => linkVal η (layerShift μ hμ c) ν * M c)
      rw [← h]
      apply Finset.sum_congr rfl
      intro c _
      rw [layerShift_layerUnshift]
    rw [h1, h2]
  have hre2 : (∑ c, shiftLinkVal η c ν μ * M c)
      = ∑ c, linkVal η c μ * M (layerUnshift ν hν c) := by
    have h1 : (∑ c, shiftLinkVal η c ν μ * M c)
        = ∑ c, linkVal η (layerShift ν hν c) μ * M c :=
      Finset.sum_congr rfl (fun c _ => by rw [shiftLinkVal_of_ne])
    have h2 : (∑ c, linkVal η c μ * M (layerUnshift ν hν c))
        = ∑ c, linkVal η (layerShift ν hν c) μ * M c := by
      have h := sum_layerUnshift ν hν
        (fun c => linkVal η (layerShift ν hν c) μ * M c)
      rw [← h]
      apply Finset.sum_congr rfl
      intro c _
      rw [layerShift_layerUnshift]
    rw [h1, h2]
  have hTμ : (∑ c, linkVal η c μ * Cμ c)
      = (∑ c, linkVal η c μ * M c)
        - ∑ c, linkVal η c μ * M (layerUnshift ν hν c) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro c _
    rw [← hμid]
    ring
  have hTν : (∑ c, linkVal η c ν * Cν c)
      = (∑ c, linkVal η c ν * M (layerUnshift μ hμ c))
        - ∑ c, linkVal η c ν * M c := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro c _
    rw [← hνid]
    ring
  have hexp : (∑ c, plaqForm η c μ ν * M c)
      = (∑ c, linkVal η c μ * M c) + (∑ c, shiftLinkVal η c μ ν * M c)
        - (∑ c, shiftLinkVal η c ν μ * M c)
        - ∑ c, linkVal η c ν * M c := by
    have hpt : ∀ c, plaqForm η c μ ν * M c
        = linkVal η c μ * M c + shiftLinkVal η c μ ν * M c
          - shiftLinkVal η c ν μ * M c - linkVal η c ν * M c :=
      fun c => by unfold plaqForm; ring
    rw [Finset.sum_congr rfl (fun c _ => hpt c),
      Finset.sum_sub_distrib, Finset.sum_sub_distrib,
      Finset.sum_add_distrib]
  rw [hexp, hre1, hre2, Finset.sum_add_distrib]
  linarith [hTμ, hTν]

/-- The **cosine link coefficient**: the coefficient of the
link value `linkVal η c μ` produced by the cosine mode's
plaquette form at the ordered pair `(μ, ν)`:
`4 * (A μ * s ν - A ν * s μ) * s ν * cos (phase_c + ph μ)`,
times the link value. -/
noncomputable def cosLinkCoeff (η : linkAngle N)
    (K : Fin 4 → ZMod N) (A : Fin 4 → ℝ) (c : LayerSite N)
    (μ ν : Fin 4) : ℝ :=
  linkVal η c μ * (4 * (A μ * modeSin K ν - A ν * modeSin K μ)
    * modeSin K ν * Real.cos (sitePhase K c + modePhase K μ))

/-- The **sine link coefficient**. -/
noncomputable def sinLinkCoeff (η : linkAngle N)
    (K : Fin 4 → ZMod N) (A : Fin 4 → ℝ) (c : LayerSite N)
    (μ ν : Fin 4) : ℝ :=
  linkVal η c μ * (4 * (A μ * modeSin K ν - A ν * modeSin K μ)
    * modeSin K ν * Real.sin (sitePhase K c + modePhase K μ))

/-- The cosine mode's plaquette-form sum at one ordered
pair, collected into link coefficients. -/
theorem sum_cosModeForm (hN : 2 ≤ N) (η : linkAngle N)
    (K : Fin 4 → ZMod N) (A : Fin 4 → ℝ) (μ ν : Fin 4)
    (hμ : μ ≠ 0) (hν : ν ≠ 0) :
    (∑ c, plaqForm η c μ ν * cosModeForm K A c μ ν)
      = ∑ c, (cosLinkCoeff η K A c μ ν
          + cosLinkCoeff η K A c ν μ) := by
  show (∑ c, plaqForm η c μ ν * cosModeForm K A c μ ν)
      = ∑ c, (linkVal η c μ * (4 * (A μ * modeSin K ν
            - A ν * modeSin K μ) * modeSin K ν
            * Real.cos (sitePhase K c + modePhase K μ))
          + linkVal η c ν * (4 * (A ν * modeSin K μ
            - A μ * modeSin K ν) * modeSin K μ
            * Real.cos (sitePhase K c + modePhase K ν)))
  refine sum_plaqForm_mul η μ ν hμ hν (fun c => cosModeForm K A c μ ν)
    (fun c => 4 * (A μ * modeSin K ν - A ν * modeSin K μ)
      * modeSin K ν * Real.cos (sitePhase K c + modePhase K μ))
    (fun c => 4 * (A ν * modeSin K μ - A μ * modeSin K ν)
      * modeSin K μ * Real.cos (sitePhase K c + modePhase K ν)) ?_ ?_
  · intro c
    have hb : Real.sin (sitePhase K c + modePhase K μ + modePhase K ν)
          - Real.sin (sitePhase K c - 2 * modePhase K ν
            + (modePhase K μ + modePhase K ν))
        = 2 * Real.cos (sitePhase K c + modePhase K μ)
          * modeSin K ν := by
      have h := Real.sin_sub_sin
        (sitePhase K c + modePhase K μ + modePhase K ν)
        (sitePhase K c - 2 * modePhase K ν
          + (modePhase K μ + modePhase K ν))
      rw [show (sitePhase K c + modePhase K μ + modePhase K ν
            + (sitePhase K c - 2 * modePhase K ν
              + (modePhase K μ + modePhase K ν))) / 2
          = sitePhase K c + modePhase K μ by ring,
        show (sitePhase K c + modePhase K μ + modePhase K ν
            - (sitePhase K c - 2 * modePhase K ν
              + (modePhase K μ + modePhase K ν))) / 2
          = modePhase K ν by ring] at h
      rw [h]
      unfold modeSin
      ring
    unfold cosModeForm
    rw [show sitePhase K (layerUnshift ν hν c) + modePhase K μ
          + modePhase K ν
        = sitePhase K (layerUnshift ν hν c)
          + (modePhase K μ + modePhase K ν) by ring,
      sin_sitePhase_layerUnshift hN K ν hν c
        (modePhase K μ + modePhase K ν)]
    have e : (2 * (A μ * modeSin K ν - A ν * modeSin K μ)
          * Real.sin (sitePhase K c + modePhase K μ + modePhase K ν)
        - 2 * (A μ * modeSin K ν - A ν * modeSin K μ)
          * Real.sin (sitePhase K c - 2 * modePhase K ν
            + (modePhase K μ + modePhase K ν)))
        = 2 * (A μ * modeSin K ν - A ν * modeSin K μ)
          * (Real.sin (sitePhase K c + modePhase K μ + modePhase K ν)
            - Real.sin (sitePhase K c - 2 * modePhase K ν
              + (modePhase K μ + modePhase K ν))) := by ring
    rw [e, hb]
    ring
  · intro c
    have hb : Real.sin (sitePhase K c - 2 * modePhase K μ
            + (modePhase K μ + modePhase K ν))
          - Real.sin (sitePhase K c + modePhase K μ + modePhase K ν)
        = -2 * Real.cos (sitePhase K c + modePhase K ν)
          * modeSin K μ := by
      have h := Real.sin_sub_sin
        (sitePhase K c - 2 * modePhase K μ
          + (modePhase K μ + modePhase K ν))
        (sitePhase K c + modePhase K μ + modePhase K ν)
      rw [show (sitePhase K c - 2 * modePhase K μ
            + (modePhase K μ + modePhase K ν)
            + (sitePhase K c + modePhase K μ + modePhase K ν)) / 2
          = sitePhase K c + modePhase K ν by ring,
        show (sitePhase K c - 2 * modePhase K μ
            + (modePhase K μ + modePhase K ν)
            - (sitePhase K c + modePhase K μ + modePhase K ν)) / 2
          = -modePhase K μ by ring, Real.sin_neg] at h
      rw [h]
      unfold modeSin
      ring
    unfold cosModeForm
    rw [show sitePhase K (layerUnshift μ hμ c) + modePhase K μ
          + modePhase K ν
        = sitePhase K (layerUnshift μ hμ c)
          + (modePhase K μ + modePhase K ν) by ring,
      sin_sitePhase_layerUnshift hN K μ hμ c
        (modePhase K μ + modePhase K ν)]
    have e : (2 * (A μ * modeSin K ν - A ν * modeSin K μ)
          * Real.sin (sitePhase K c - 2 * modePhase K μ
            + (modePhase K μ + modePhase K ν))
        - 2 * (A μ * modeSin K ν - A ν * modeSin K μ)
          * Real.sin (sitePhase K c + modePhase K μ + modePhase K ν))
        = 2 * (A μ * modeSin K ν - A ν * modeSin K μ)
          * (Real.sin (sitePhase K c - 2 * modePhase K μ
              + (modePhase K μ + modePhase K ν))
            - Real.sin (sitePhase K c + modePhase K μ
              + modePhase K ν)) := by ring
    rw [e, hb]
    ring

/-- The sine mode's plaquette-form sum at one ordered pair,
collected into link coefficients. -/
theorem sum_sinModeForm (hN : 2 ≤ N) (η : linkAngle N)
    (K : Fin 4 → ZMod N) (A : Fin 4 → ℝ) (μ ν : Fin 4)
    (hμ : μ ≠ 0) (hν : ν ≠ 0) :
    (∑ c, plaqForm η c μ ν * sinModeForm K A c μ ν)
      = ∑ c, (sinLinkCoeff η K A c μ ν
          + sinLinkCoeff η K A c ν μ) := by
  show (∑ c, plaqForm η c μ ν * sinModeForm K A c μ ν)
      = ∑ c, (linkVal η c μ * (4 * (A μ * modeSin K ν
            - A ν * modeSin K μ) * modeSin K ν
            * Real.sin (sitePhase K c + modePhase K μ))
          + linkVal η c ν * (4 * (A ν * modeSin K μ
            - A μ * modeSin K ν) * modeSin K μ
            * Real.sin (sitePhase K c + modePhase K ν)))
  refine sum_plaqForm_mul η μ ν hμ hν (fun c => sinModeForm K A c μ ν)
    (fun c => 4 * (A μ * modeSin K ν - A ν * modeSin K μ)
      * modeSin K ν * Real.sin (sitePhase K c + modePhase K μ))
    (fun c => 4 * (A ν * modeSin K μ - A μ * modeSin K ν)
      * modeSin K μ * Real.sin (sitePhase K c + modePhase K ν)) ?_ ?_
  · intro c
    have hb : Real.cos (sitePhase K c + modePhase K μ + modePhase K ν)
          - Real.cos (sitePhase K c - 2 * modePhase K ν
            + (modePhase K μ + modePhase K ν))
        = -2 * Real.sin (sitePhase K c + modePhase K μ)
          * modeSin K ν := by
      have h := Real.cos_sub_cos
        (sitePhase K c + modePhase K μ + modePhase K ν)
        (sitePhase K c - 2 * modePhase K ν
          + (modePhase K μ + modePhase K ν))
      rw [show (sitePhase K c + modePhase K μ + modePhase K ν
            + (sitePhase K c - 2 * modePhase K ν
              + (modePhase K μ + modePhase K ν))) / 2
          = sitePhase K c + modePhase K μ by ring,
        show (sitePhase K c + modePhase K μ + modePhase K ν
            - (sitePhase K c - 2 * modePhase K ν
              + (modePhase K μ + modePhase K ν))) / 2
          = modePhase K ν by ring] at h
      exact h
    unfold sinModeForm
    rw [show sitePhase K (layerUnshift ν hν c) + modePhase K μ
          + modePhase K ν
        = sitePhase K (layerUnshift ν hν c)
          + (modePhase K μ + modePhase K ν) by ring,
      cos_sitePhase_layerUnshift hN K ν hν c
        (modePhase K μ + modePhase K ν)]
    have e : (-2 * (A μ * modeSin K ν - A ν * modeSin K μ)
          * Real.cos (sitePhase K c + modePhase K μ + modePhase K ν)
        - -2 * (A μ * modeSin K ν - A ν * modeSin K μ)
          * Real.cos (sitePhase K c - 2 * modePhase K ν
            + (modePhase K μ + modePhase K ν)))
        = -2 * (A μ * modeSin K ν - A ν * modeSin K μ)
          * (Real.cos (sitePhase K c + modePhase K μ + modePhase K ν)
            - Real.cos (sitePhase K c - 2 * modePhase K ν
              + (modePhase K μ + modePhase K ν))) := by ring
    rw [e, hb]
    ring
  · intro c
    have hb : Real.cos (sitePhase K c - 2 * modePhase K μ
            + (modePhase K μ + modePhase K ν))
          - Real.cos (sitePhase K c + modePhase K μ + modePhase K ν)
        = 2 * Real.sin (sitePhase K c + modePhase K ν)
          * modeSin K μ := by
      have h := Real.cos_sub_cos
        (sitePhase K c - 2 * modePhase K μ
          + (modePhase K μ + modePhase K ν))
        (sitePhase K c + modePhase K μ + modePhase K ν)
      rw [show (sitePhase K c - 2 * modePhase K μ
            + (modePhase K μ + modePhase K ν)
            + (sitePhase K c + modePhase K μ + modePhase K ν)) / 2
          = sitePhase K c + modePhase K ν by ring,
        show (sitePhase K c - 2 * modePhase K μ
            + (modePhase K μ + modePhase K ν)
            - (sitePhase K c + modePhase K μ + modePhase K ν)) / 2
          = -modePhase K μ by ring, Real.sin_neg] at h
      rw [h]
      unfold modeSin
      ring
    unfold sinModeForm
    rw [show sitePhase K (layerUnshift μ hμ c) + modePhase K μ
          + modePhase K ν
        = sitePhase K (layerUnshift μ hμ c)
          + (modePhase K μ + modePhase K ν) by ring,
      cos_sitePhase_layerUnshift hN K μ hμ c
        (modePhase K μ + modePhase K ν)]
    have e : (-2 * (A μ * modeSin K ν - A ν * modeSin K μ)
          * Real.cos (sitePhase K c - 2 * modePhase K μ
            + (modePhase K μ + modePhase K ν))
        - -2 * (A μ * modeSin K ν - A ν * modeSin K μ)
          * Real.cos (sitePhase K c + modePhase K μ + modePhase K ν))
        = -2 * (A μ * modeSin K ν - A ν * modeSin K μ)
          * (Real.cos (sitePhase K c - 2 * modePhase K μ
              + (modePhase K μ + modePhase K ν))
            - Real.cos (sitePhase K c + modePhase K μ
              + modePhase K ν)) := by ring
    rw [e, hb]
    ring

end PairCollection

section FormIdentity

variable {N : ℕ} [NeZero N]

/-- `linkVal` at direction `0` vanishes. -/
theorem linkVal_zero (F : LayerLink N → ℝ) (c : LayerSite N) :
    linkVal F c 0 = 0 :=
  dif_neg (fun h => h rfl)

/-- The transverse sine at direction `0` vanishes when
`K 0 = 0`. -/
theorem modeSin_zero {K : Fin 4 → ZMod N} (hK0 : K 0 = 0) :
    modeSin K 0 = 0 := by
  unfold modeSin modePhase
  rw [hK0]
  simp

/-- The cosine link coefficient vanishes at `mu = 0`. -/
theorem cosLinkCoeff_apply_zero_left (η : linkAngle N)
    (K : Fin 4 → ZMod N) (A : Fin 4 → ℝ) (c : LayerSite N)
    (ν : Fin 4) :
    cosLinkCoeff η K A c 0 ν = 0 := by
  unfold cosLinkCoeff
  rw [linkVal_zero, zero_mul]

/-- The cosine link coefficient vanishes at `nu = 0` when
`K 0 = 0`. -/
theorem cosLinkCoeff_apply_zero_right {K : Fin 4 → ZMod N}
    (hK0 : K 0 = 0) (η : linkAngle N) (A : Fin 4 → ℝ)
    (c : LayerSite N) (μ : Fin 4) :
    cosLinkCoeff η K A c μ 0 = 0 := by
  unfold cosLinkCoeff
  rw [modeSin_zero hK0]
  ring

/-- The cosine link coefficient vanishes on the diagonal. -/
theorem cosLinkCoeff_diag (η : linkAngle N)
    (K : Fin 4 → ZMod N) (A : Fin 4 → ℝ) (c : LayerSite N)
    (μ : Fin 4) :
    cosLinkCoeff η K A c μ μ = 0 := by
  unfold cosLinkCoeff
  ring

/-- The sine link coefficient vanishes at `mu = 0`. -/
theorem sinLinkCoeff_apply_zero_left (η : linkAngle N)
    (K : Fin 4 → ZMod N) (A : Fin 4 → ℝ) (c : LayerSite N)
    (ν : Fin 4) :
    sinLinkCoeff η K A c 0 ν = 0 := by
  unfold sinLinkCoeff
  rw [linkVal_zero, zero_mul]

/-- The sine link coefficient vanishes at `nu = 0` when
`K 0 = 0`. -/
theorem sinLinkCoeff_apply_zero_right {K : Fin 4 → ZMod N}
    (hK0 : K 0 = 0) (η : linkAngle N) (A : Fin 4 → ℝ)
    (c : LayerSite N) (μ : Fin 4) :
    sinLinkCoeff η K A c μ 0 = 0 := by
  unfold sinLinkCoeff
  rw [modeSin_zero hK0]
  ring

/-- The sine link coefficient vanishes on the diagonal. -/
theorem sinLinkCoeff_diag (η : linkAngle N)
    (K : Fin 4 → ZMod N) (A : Fin 4 → ℝ) (c : LayerSite N)
    (μ : Fin 4) :
    sinLinkCoeff η K A c μ μ = 0 := by
  unfold sinLinkCoeff
  ring

/-- The cosine mode's `G`-symmetry: the plaquette product
`plaqForm * cosModeForm` is symmetric in its directions. -/
theorem cosG_symm (η : linkAngle N) (K : Fin 4 → ZMod N)
    (A : Fin 4 → ℝ) (c : LayerSite N) (μ ν : Fin 4) :
    plaqForm η c μ ν * cosModeForm K A c μ ν
      = plaqForm η c ν μ * cosModeForm K A c ν μ := by
  rw [plaqForm_antisymm, cosModeForm_antisymm]
  ring

/-- The sine mode's `G`-symmetry. -/
theorem sinG_symm (η : linkAngle N) (K : Fin 4 → ZMod N)
    (A : Fin 4 → ℝ) (c : LayerSite N) (μ ν : Fin 4) :
    plaqForm η c μ ν * sinModeForm K A c μ ν
      = plaqForm η c ν μ * sinModeForm K A c ν μ := by
  rw [plaqForm_antisymm, sinModeForm_antisymm]
  ring

/-- Relabeling symmetry of the ordered-pair ite sum, for a
symmetric summand. -/
theorem ite_lt_sum_symm (G : Fin 4 → Fin 4 → ℝ)
    (hG : ∀ μ ν, G μ ν = G ν μ) :
    (∑ μ, ∑ ν, (if μ ≠ 0 ∧ ν ≠ 0 ∧ μ < ν then G μ ν else 0))
      = ∑ μ, ∑ ν, (if ν ≠ 0 ∧ μ ≠ 0 ∧ ν < μ then G μ ν else 0) := by
  conv_lhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  by_cases h : b ≠ 0 ∧ a ≠ 0 ∧ b < a
  · rw [if_pos h, if_pos h]
    exact (hG a b).symm
  · rw [if_neg h, if_neg h]

/-- Merging the two ordered ite sums into the `≠` ite sum. -/
theorem ite_merge (G : Fin 4 → Fin 4 → ℝ) :
    (∑ μ, ∑ ν, (if μ ≠ 0 ∧ ν ≠ 0 ∧ μ < ν then G μ ν else 0))
      + (∑ μ, ∑ ν, (if ν ≠ 0 ∧ μ ≠ 0 ∧ ν < μ then G μ ν else 0))
      = ∑ μ, ∑ ν, (if μ ≠ 0 ∧ ν ≠ 0 ∧ μ ≠ ν then G μ ν else 0) := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro μ _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ν _
  by_cases hμ0 : μ = 0
  · subst hμ0
    rw [if_neg (fun h : (0 : Fin 4) ≠ 0 ∧ ν ≠ 0 ∧ (0 : Fin 4) < ν =>
        h.1 rfl),
      if_neg (fun h : ν ≠ 0 ∧ (0 : Fin 4) ≠ 0 ∧ ν < 0 =>
        (Fin.not_lt_zero ν) h.2.2),
      if_neg (fun h : (0 : Fin 4) ≠ 0 ∧ ν ≠ 0 ∧ (0 : Fin 4) ≠ ν =>
        h.1 rfl), add_zero]
  · by_cases hν0 : ν = 0
    · subst hν0
      rw [if_neg (fun h : μ ≠ 0 ∧ (0 : Fin 4) ≠ 0 ∧ μ < 0 =>
          h.2.1 rfl),
        if_neg (fun h : (0 : Fin 4) ≠ 0 ∧ μ ≠ 0 ∧ (0 : Fin 4) < μ =>
          h.1 rfl),
        if_neg (fun h : μ ≠ 0 ∧ (0 : Fin 4) ≠ 0 ∧ μ ≠ 0 =>
          h.2.1 rfl), add_zero]
    · rcases lt_trichotomy μ ν with h | h | h
      · rw [if_pos ⟨hμ0, hν0, h⟩,
          if_neg (fun hh => not_lt_of_gt h hh.2.2),
          if_pos ⟨hμ0, hν0, ne_of_lt h⟩, add_zero]
      · subst h
        rw [if_neg (fun hh : μ ≠ 0 ∧ μ ≠ 0 ∧ μ < μ =>
            lt_irrefl μ hh.2.2),
          if_neg (fun hh : μ ≠ 0 ∧ μ ≠ 0 ∧ μ ≠ μ =>
            hh.2.2 rfl), add_zero]
      · rw [if_neg (fun hh => not_lt_of_gt h hh.2.2),
          if_pos ⟨hν0, hμ0, h⟩,
          if_pos ⟨hμ0, hν0, (ne_of_lt h).symm⟩, zero_add]

/-- The cosine mode's form identity, at the level of the
expanded plaquette enumeration. -/
theorem cosMode_form_key (hN : 2 ≤ N)
    (η : linkAngle N) (K : Fin 4 → ZMod N) (A : Fin 4 → ℝ)
    (hK0 : K 0 = 0) :
    (∑ c, ∑ μ, ∑ ν, (if μ ≠ 0 ∧ ν ≠ 0 ∧ μ < ν
        then plaqForm η c μ ν * cosModeForm K A c μ ν else 0))
      = ∑ c, ∑ μ, linkVal η c μ * (∑ ν,
          4 * (A μ * modeSin K ν - A ν * modeSin K μ) * modeSin K ν
            * Real.cos (sitePhase K c + modePhase K μ)) := by
  have key2 : 2 * (∑ c, ∑ μ, ∑ ν, (if μ ≠ 0 ∧ ν ≠ 0 ∧ μ < ν
        then plaqForm η c μ ν * cosModeForm K A c μ ν else 0))
      = 2 * (∑ c, ∑ μ, linkVal η c μ * (∑ ν,
          4 * (A μ * modeSin K ν - A ν * modeSin K μ) * modeSin K ν
            * Real.cos (sitePhase K c + modePhase K μ))) := by
    calc 2 * (∑ c, ∑ μ, ∑ ν, (if μ ≠ 0 ∧ ν ≠ 0 ∧ μ < ν
          then plaqForm η c μ ν * cosModeForm K A c μ ν else 0))
        = (∑ c, ∑ μ, ∑ ν, (if μ ≠ 0 ∧ ν ≠ 0 ∧ μ < ν
            then plaqForm η c μ ν * cosModeForm K A c μ ν else 0))
          + ∑ c, ∑ μ, ∑ ν, (if ν ≠ 0 ∧ μ ≠ 0 ∧ ν < μ
            then plaqForm η c μ ν * cosModeForm K A c μ ν else 0) := by
          rw [two_mul, Finset.sum_congr rfl
            (fun c _ => ite_lt_sum_symm _
              (cosG_symm η K A c))]
      _ = ∑ c, ∑ μ, ∑ ν, (if μ ≠ 0 ∧ ν ≠ 0 ∧ μ ≠ ν
            then plaqForm η c μ ν * cosModeForm K A c μ ν else 0) := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro c _
          exact ite_merge _
      _ = ∑ μ, ∑ ν, (if μ ≠ 0 ∧ ν ≠ 0 ∧ μ ≠ ν
            then (∑ c, plaqForm η c μ ν * cosModeForm K A c μ ν)
            else 0) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro μ _
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro ν _
          by_cases h : μ ≠ 0 ∧ ν ≠ 0 ∧ μ ≠ ν <;> simp [h]
      _ = ∑ μ, ∑ ν, (∑ c, (cosLinkCoeff η K A c μ ν
            + cosLinkCoeff η K A c ν μ)) := by
          apply Finset.sum_congr rfl
          intro μ _
          apply Finset.sum_congr rfl
          intro ν _
          by_cases h : μ ≠ 0 ∧ ν ≠ 0 ∧ μ ≠ ν
          · rw [if_pos h]
            exact sum_cosModeForm hN η K A μ ν h.1 h.2.1
          · rw [if_neg h]
            have hz : (∑ c, (cosLinkCoeff η K A c μ ν
                + cosLinkCoeff η K A c ν μ)) = 0 := by
              apply Finset.sum_eq_zero
              intro c _
              by_cases hμ0 : μ = 0
              · rw [hμ0, cosLinkCoeff_apply_zero_left,
                  cosLinkCoeff_apply_zero_right hK0, add_zero]
              · by_cases hν0 : ν = 0
                · rw [hν0, cosLinkCoeff_apply_zero_right hK0,
                    cosLinkCoeff_apply_zero_left, add_zero]
                · have hμν : μ = ν := by
                    by_contra hne
                    exact h ⟨hμ0, hν0, hne⟩
                  rw [hμν, cosLinkCoeff_diag, add_zero]
            rw [hz]
      _ = ∑ c, (∑ μ, ∑ ν, (cosLinkCoeff η K A c μ ν
            + cosLinkCoeff η K A c ν μ)) := by
          symm
          conv_lhs => rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro μ _
          rw [Finset.sum_comm]
      _ = ∑ c, ((∑ μ, ∑ ν, cosLinkCoeff η K A c μ ν)
            + ∑ μ, ∑ ν, cosLinkCoeff η K A c ν μ) := by
          apply Finset.sum_congr rfl
          intro c _
          calc (∑ μ, ∑ ν, (cosLinkCoeff η K A c μ ν
                + cosLinkCoeff η K A c ν μ))
              = ∑ μ, ((∑ ν, cosLinkCoeff η K A c μ ν)
                + ∑ ν, cosLinkCoeff η K A c ν μ) :=
                Finset.sum_congr rfl
                  (fun μ _ => Finset.sum_add_distrib)
            _ = (∑ μ, ∑ ν, cosLinkCoeff η K A c μ ν)
                + ∑ μ, ∑ ν, cosLinkCoeff η K A c ν μ :=
                Finset.sum_add_distrib
      _ = ∑ c, 2 * (∑ μ, linkVal η c μ * (∑ ν,
            4 * (A μ * modeSin K ν - A ν * modeSin K μ)
              * modeSin K ν
              * Real.cos (sitePhase K c + modePhase K μ))) := by
          apply Finset.sum_congr rfl
          intro c _
          have hswapD : (∑ μ, ∑ ν, cosLinkCoeff η K A c ν μ)
              = ∑ μ, ∑ ν, cosLinkCoeff η K A c μ ν :=
            Finset.sum_comm
          have hfac : (∑ μ, ∑ ν, cosLinkCoeff η K A c μ ν)
              = ∑ μ, linkVal η c μ * (∑ ν,
                  4 * (A μ * modeSin K ν - A ν * modeSin K μ)
                    * modeSin K ν
                    * Real.cos (sitePhase K c + modePhase K μ)) := by
            apply Finset.sum_congr rfl
            intro μ _
            show (∑ ν, linkVal η c μ
                * (4 * (A μ * modeSin K ν - A ν * modeSin K μ)
                  * modeSin K ν
                  * Real.cos (sitePhase K c + modePhase K μ)))
              = linkVal η c μ * (∑ ν,
                  4 * (A μ * modeSin K ν - A ν * modeSin K μ)
                    * modeSin K ν
                    * Real.cos (sitePhase K c + modePhase K μ))
            rw [Finset.mul_sum]
          rw [hswapD, hfac]
          ring
      _ = 2 * (∑ c, ∑ μ, linkVal η c μ * (∑ ν,
            4 * (A μ * modeSin K ν - A ν * modeSin K μ)
              * modeSin K ν
              * Real.cos (sitePhase K c + modePhase K μ))) := by
          rw [Finset.mul_sum]
  exact mul_left_cancel₀ (by norm_num : (2 : ℝ) ≠ 0) key2

/-- The sine mode's form identity, at the level of the
expanded plaquette enumeration. -/
theorem sinMode_form_key (hN : 2 ≤ N)
    (η : linkAngle N) (K : Fin 4 → ZMod N) (A : Fin 4 → ℝ)
    (hK0 : K 0 = 0) :
    (∑ c, ∑ μ, ∑ ν, (if μ ≠ 0 ∧ ν ≠ 0 ∧ μ < ν
        then plaqForm η c μ ν * sinModeForm K A c μ ν else 0))
      = ∑ c, ∑ μ, linkVal η c μ * (∑ ν,
          4 * (A μ * modeSin K ν - A ν * modeSin K μ) * modeSin K ν
            * Real.sin (sitePhase K c + modePhase K μ)) := by
  have key2 : 2 * (∑ c, ∑ μ, ∑ ν, (if μ ≠ 0 ∧ ν ≠ 0 ∧ μ < ν
        then plaqForm η c μ ν * sinModeForm K A c μ ν else 0))
      = 2 * (∑ c, ∑ μ, linkVal η c μ * (∑ ν,
          4 * (A μ * modeSin K ν - A ν * modeSin K μ) * modeSin K ν
            * Real.sin (sitePhase K c + modePhase K μ))) := by
    calc 2 * (∑ c, ∑ μ, ∑ ν, (if μ ≠ 0 ∧ ν ≠ 0 ∧ μ < ν
          then plaqForm η c μ ν * sinModeForm K A c μ ν else 0))
        = (∑ c, ∑ μ, ∑ ν, (if μ ≠ 0 ∧ ν ≠ 0 ∧ μ < ν
            then plaqForm η c μ ν * sinModeForm K A c μ ν else 0))
          + ∑ c, ∑ μ, ∑ ν, (if ν ≠ 0 ∧ μ ≠ 0 ∧ ν < μ
            then plaqForm η c μ ν * sinModeForm K A c μ ν else 0) := by
          rw [two_mul, Finset.sum_congr rfl
            (fun c _ => ite_lt_sum_symm _
              (sinG_symm η K A c))]
      _ = ∑ c, ∑ μ, ∑ ν, (if μ ≠ 0 ∧ ν ≠ 0 ∧ μ ≠ ν
            then plaqForm η c μ ν * sinModeForm K A c μ ν else 0) := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro c _
          exact ite_merge _
      _ = ∑ μ, ∑ ν, (if μ ≠ 0 ∧ ν ≠ 0 ∧ μ ≠ ν
            then (∑ c, plaqForm η c μ ν * sinModeForm K A c μ ν)
            else 0) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro μ _
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro ν _
          by_cases h : μ ≠ 0 ∧ ν ≠ 0 ∧ μ ≠ ν <;> simp [h]
      _ = ∑ μ, ∑ ν, (∑ c, (sinLinkCoeff η K A c μ ν
            + sinLinkCoeff η K A c ν μ)) := by
          apply Finset.sum_congr rfl
          intro μ _
          apply Finset.sum_congr rfl
          intro ν _
          by_cases h : μ ≠ 0 ∧ ν ≠ 0 ∧ μ ≠ ν
          · rw [if_pos h]
            exact sum_sinModeForm hN η K A μ ν h.1 h.2.1
          · rw [if_neg h]
            have hz : (∑ c, (sinLinkCoeff η K A c μ ν
                + sinLinkCoeff η K A c ν μ)) = 0 := by
              apply Finset.sum_eq_zero
              intro c _
              by_cases hμ0 : μ = 0
              · rw [hμ0, sinLinkCoeff_apply_zero_left,
                  sinLinkCoeff_apply_zero_right hK0, add_zero]
              · by_cases hν0 : ν = 0
                · rw [hν0, sinLinkCoeff_apply_zero_right hK0,
                    sinLinkCoeff_apply_zero_left, add_zero]
                · have hμν : μ = ν := by
                    by_contra hne
                    exact h ⟨hμ0, hν0, hne⟩
                  rw [hμν, sinLinkCoeff_diag, add_zero]
            rw [hz]
      _ = ∑ c, (∑ μ, ∑ ν, (sinLinkCoeff η K A c μ ν
            + sinLinkCoeff η K A c ν μ)) := by
          symm
          conv_lhs => rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro μ _
          rw [Finset.sum_comm]
      _ = ∑ c, ((∑ μ, ∑ ν, sinLinkCoeff η K A c μ ν)
            + ∑ μ, ∑ ν, sinLinkCoeff η K A c ν μ) := by
          apply Finset.sum_congr rfl
          intro c _
          calc (∑ μ, ∑ ν, (sinLinkCoeff η K A c μ ν
                + sinLinkCoeff η K A c ν μ))
              = ∑ μ, ((∑ ν, sinLinkCoeff η K A c μ ν)
                + ∑ ν, sinLinkCoeff η K A c ν μ) :=
                Finset.sum_congr rfl
                  (fun μ _ => Finset.sum_add_distrib)
            _ = (∑ μ, ∑ ν, sinLinkCoeff η K A c μ ν)
                + ∑ μ, ∑ ν, sinLinkCoeff η K A c ν μ :=
                Finset.sum_add_distrib
      _ = ∑ c, 2 * (∑ μ, linkVal η c μ * (∑ ν,
            4 * (A μ * modeSin K ν - A ν * modeSin K μ)
              * modeSin K ν
              * Real.sin (sitePhase K c + modePhase K μ))) := by
          apply Finset.sum_congr rfl
          intro c _
          have hswapD : (∑ μ, ∑ ν, sinLinkCoeff η K A c ν μ)
              = ∑ μ, ∑ ν, sinLinkCoeff η K A c μ ν :=
            Finset.sum_comm
          have hfac : (∑ μ, ∑ ν, sinLinkCoeff η K A c μ ν)
              = ∑ μ, linkVal η c μ * (∑ ν,
                  4 * (A μ * modeSin K ν - A ν * modeSin K μ)
                    * modeSin K ν
                    * Real.sin (sitePhase K c + modePhase K μ)) := by
            apply Finset.sum_congr rfl
            intro μ _
            show (∑ ν, linkVal η c μ
                * (4 * (A μ * modeSin K ν - A ν * modeSin K μ)
                  * modeSin K ν
                  * Real.sin (sitePhase K c + modePhase K μ)))
              = linkVal η c μ * (∑ ν,
                  4 * (A μ * modeSin K ν - A ν * modeSin K μ)
                    * modeSin K ν
                    * Real.sin (sitePhase K c + modePhase K μ))
            rw [Finset.mul_sum]
          rw [hswapD, hfac]
          ring
      _ = 2 * (∑ c, ∑ μ, linkVal η c μ * (∑ ν,
            4 * (A μ * modeSin K ν - A ν * modeSin K μ)
              * modeSin K ν
              * Real.sin (sitePhase K c + modePhase K μ))) := by
          rw [Finset.mul_sum]
  exact mul_left_cancel₀ (by norm_num : (2 : ℝ) ≠ 0) key2

/-- **The cosine mode's form identity**: the form of the
pin's `maxwellOp N` against the cosine mode, computed:
`∑ P, plaqAngle P η * plaqAngle P (cosMode K A)` equals the
link sum of `η` against the transverse coefficient. -/
theorem cosMode_form (hN : 2 ≤ N)
    (η : linkAngle N) (K : Fin 4 → ZMod N) (A : Fin 4 → ℝ)
    (hK0 : K 0 = 0) :
    (∑ P ∈ allPlaqData N, plaqAngle P η * plaqAngle P (cosMode K A))
      = ∑ c, ∑ μ, linkVal η c μ * (∑ ν,
          4 * (A μ * modeSin K ν - A ν * modeSin K μ) * modeSin K ν
            * Real.cos (sitePhase K c + modePhase K μ)) := by
  have hL : (∑ P ∈ allPlaqData N,
        plaqAngle P η * plaqAngle P (cosMode K A))
      = ∑ c, ∑ μ, ∑ ν, (if μ ≠ 0 ∧ ν ≠ 0 ∧ μ < ν
          then plaqForm η c μ ν * cosModeForm K A c μ ν else 0) := by
    rw [sum_allPlaqData]
    apply Finset.sum_congr rfl
    intro c _
    apply Finset.sum_congr rfl
    intro μ _
    apply Finset.sum_congr rfl
    intro ν _
    by_cases h : μ ≠ 0 ∧ ν ≠ 0 ∧ μ < ν
    · rw [dif_pos h, if_pos h,
        ← plaqForm_eq η c μ ν h.1 h.2.1 (ne_of_lt h.2.2),
        plaqAngle_cosMode hN K A
          ⟨c, μ, ν, h.1, h.2.1, ne_of_lt h.2.2⟩]
    · rw [dif_neg h, if_neg h]
  rw [hL, cosMode_form_key hN η K A hK0]

/-- **The sine mode's form identity**. -/
theorem sinMode_form (hN : 2 ≤ N)
    (η : linkAngle N) (K : Fin 4 → ZMod N) (A : Fin 4 → ℝ)
    (hK0 : K 0 = 0) :
    (∑ P ∈ allPlaqData N, plaqAngle P η * plaqAngle P (sinMode K A))
      = ∑ c, ∑ μ, linkVal η c μ * (∑ ν,
          4 * (A μ * modeSin K ν - A ν * modeSin K μ) * modeSin K ν
            * Real.sin (sitePhase K c + modePhase K μ)) := by
  have hL : (∑ P ∈ allPlaqData N,
        plaqAngle P η * plaqAngle P (sinMode K A))
      = ∑ c, ∑ μ, ∑ ν, (if μ ≠ 0 ∧ ν ≠ 0 ∧ μ < ν
          then plaqForm η c μ ν * sinModeForm K A c μ ν else 0) := by
    rw [sum_allPlaqData]
    apply Finset.sum_congr rfl
    intro c _
    apply Finset.sum_congr rfl
    intro μ _
    apply Finset.sum_congr rfl
    intro ν _
    by_cases h : μ ≠ 0 ∧ ν ≠ 0 ∧ μ < ν
    · rw [dif_pos h, if_pos h,
        ← plaqForm_eq η c μ ν h.1 h.2.1 (ne_of_lt h.2.2),
        plaqAngle_sinMode hN K A
          ⟨c, μ, ν, h.1, h.2.1, ne_of_lt h.2.2⟩]
    · rw [dif_neg h, if_neg h]
  rw [hL, sinMode_form_key hN η K A hK0]

end FormIdentity

section Eigen

variable {N : ℕ} [NeZero N]

/-- **Transversality collapse, cosine**: under the
transversality condition `∑ ν, A ν * s ν = 0`, the collected
coefficient of the cosine mode is the transverse eigenvalue
times the mode's own link factor. -/
theorem cos_coeff_sum (K : Fin 4 → ZMod N) (A : Fin 4 → ℝ)
    (htrans : ∑ ν, A ν * modeSin K ν = 0)
    (c : LayerSite N) (μ : Fin 4) :
    (∑ ν, 4 * (A μ * modeSin K ν - A ν * modeSin K μ)
        * modeSin K ν
        * Real.cos (sitePhase K c + modePhase K μ))
      = (4 * ∑ ν, (modeSin K ν)^2)
        * (A μ * Real.cos (sitePhase K c + modePhase K μ)) := by
  have e1 : ∀ ν, 4 * (A μ * modeSin K ν - A ν * modeSin K μ)
        * modeSin K ν
        * Real.cos (sitePhase K c + modePhase K μ)
      = (A μ * Real.cos (sitePhase K c + modePhase K μ))
          * (4 * (modeSin K ν)^2)
        - (4 * modeSin K μ
            * Real.cos (sitePhase K c + modePhase K μ))
          * (A ν * modeSin K ν) := fun ν => by ring
  rw [Finset.sum_congr rfl (fun ν _ => e1 ν),
    Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    ← Finset.mul_sum, htrans, mul_zero, sub_zero]
  ring

/-- **Transversality collapse, sine**. -/
theorem sin_coeff_sum (K : Fin 4 → ZMod N) (A : Fin 4 → ℝ)
    (htrans : ∑ ν, A ν * modeSin K ν = 0)
    (c : LayerSite N) (μ : Fin 4) :
    (∑ ν, 4 * (A μ * modeSin K ν - A ν * modeSin K μ)
        * modeSin K ν
        * Real.sin (sitePhase K c + modePhase K μ))
      = (4 * ∑ ν, (modeSin K ν)^2)
        * (A μ * Real.sin (sitePhase K c + modePhase K μ)) := by
  have e1 : ∀ ν, 4 * (A μ * modeSin K ν - A ν * modeSin K μ)
        * modeSin K ν
        * Real.sin (sitePhase K c + modePhase K μ)
      = (A μ * Real.sin (sitePhase K c + modePhase K μ))
          * (4 * (modeSin K ν)^2)
        - (4 * modeSin K μ
            * Real.sin (sitePhase K c + modePhase K μ))
          * (A ν * modeSin K ν) := fun ν => by ring
  rw [Finset.sum_congr rfl (fun ν _ => e1 ν),
    Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    ← Finset.mul_sum, htrans, mul_zero, sub_zero]
  ring

/-- The indicator extraction: for the single-link indicator
at `ℓ`, the double link sum of `cosMode_form` collapses to
the coefficient at `(linkTail ℓ, ℓ.1.2)`. -/
theorem cosMode_form_single (hN : 2 ≤ N)
    (K : Fin 4 → ZMod N) (A : Fin 4 → ℝ) (hK0 : K 0 = 0)
    (ℓ : LayerLink N) :
    (maxwellOp N (cosMode K A)) ℓ
      = ∑ ν, 4 * (A ℓ.1.2 * modeSin K ν - A ν * modeSin K ℓ.1.2)
          * modeSin K ν
          * Real.cos (sitePhase K (linkTail ℓ)
            + modePhase K ℓ.1.2) := by
  classical
  have hsingle : ∀ v : linkAngle N,
      (∑ ℓ', ((Pi.single ℓ (1 : ℝ) : linkAngle N)) ℓ' * v ℓ')
        = v ℓ := by
    intro v
    rw [Finset.sum_eq_single ℓ]
    · rw [Pi.single_eq_same, one_mul]
    · intro b _ hb
      rw [Pi.single_eq_of_ne hb, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ ℓ) h
  have hform : (maxwellOp N (cosMode K A)) ℓ
      = ∑ c, ∑ μ, linkVal
          ((Pi.single ℓ (1 : ℝ) : linkAngle N)) c μ
        * (∑ ν, 4 * (A μ * modeSin K ν - A ν * modeSin K μ)
            * modeSin K ν
            * Real.cos (sitePhase K c + modePhase K μ)) := by
    rw [← hsingle (maxwellOp N (cosMode K A)), maxwellOp_form,
      cosMode_form hN ((Pi.single ℓ (1 : ℝ) : linkAngle N)) K A
        hK0]
  rw [hform]
  have hlink : ∀ (c : LayerSite N) (μ : Fin 4) (h : μ ≠ 0),
      layerLinkOf c μ h = ℓ → c = linkTail ℓ ∧ μ = ℓ.1.2 := by
    intro c μ h hℓ
    constructor
    · have ht : linkTail (layerLinkOf c μ h) = c := rfl
      rw [hℓ] at ht
      exact ht.symm
    · have hd : (layerLinkOf c μ h).1.2 = μ := rfl
      rw [hℓ] at hd
      exact hd.symm
  have hval : ∀ (c : LayerSite N) (μ : Fin 4),
      linkVal ((Pi.single ℓ (1 : ℝ) : linkAngle N)) c μ
        * (∑ ν, 4 * (A μ * modeSin K ν - A ν * modeSin K μ)
            * modeSin K ν
            * Real.cos (sitePhase K c + modePhase K μ))
      = (if c = linkTail ℓ ∧ μ = ℓ.1.2
          then ∑ ν, 4 * (A μ * modeSin K ν - A ν * modeSin K μ)
            * modeSin K ν
            * Real.cos (sitePhase K c + modePhase K μ)
          else 0) := by
    intro c μ
    by_cases h : c = linkTail ℓ ∧ μ = ℓ.1.2
    · rw [if_pos h]
      obtain ⟨rfl, rfl⟩ := h
      have h1 : linkVal ((Pi.single ℓ (1 : ℝ) : linkAngle N))
          (linkTail ℓ) ℓ.1.2 = 1 := by
        unfold linkVal
        rw [dif_pos ℓ.2.2]
        have hℓℓ : layerLinkOf (linkTail ℓ) ℓ.1.2 ℓ.2.2 = ℓ :=
          rfl
        rw [hℓℓ, Pi.single_eq_same]
      rw [h1, one_mul]
    · rw [if_neg h]
      have h0 : linkVal ((Pi.single ℓ (1 : ℝ) : linkAngle N))
          c μ = 0 := by
        by_cases hμ : μ = 0
        · rw [hμ]
          exact linkVal_zero _ _
        · unfold linkVal
          have hne : layerLinkOf c μ hμ ≠ ℓ :=
            fun hℓ => h (hlink c μ hμ hℓ)
          rw [dif_pos hμ, Pi.single_eq_of_ne hne]
      rw [h0, zero_mul]
  rw [Finset.sum_congr rfl
    (fun c _ => Finset.sum_congr rfl (fun μ _ => hval c μ))]
  rw [Finset.sum_eq_single (linkTail ℓ)]
  · rw [Finset.sum_eq_single ℓ.1.2]
    · rw [if_pos ⟨rfl, rfl⟩]
    · intro b _ hb
      rw [if_neg]
      intro hh
      exact hb hh.2
    · intro h
      exact absurd (Finset.mem_univ ℓ.1.2) h
  · intro b _ hb
    apply Finset.sum_eq_zero
    intro μ _
    rw [if_neg]
    intro hh
    exact hb hh.1
  · intro h
    exact absurd (Finset.mem_univ (linkTail ℓ)) h

/-- The indicator extraction, sine mode. -/
theorem sinMode_form_single (hN : 2 ≤ N)
    (K : Fin 4 → ZMod N) (A : Fin 4 → ℝ) (hK0 : K 0 = 0)
    (ℓ : LayerLink N) :
    (maxwellOp N (sinMode K A)) ℓ
      = ∑ ν, 4 * (A ℓ.1.2 * modeSin K ν - A ν * modeSin K ℓ.1.2)
          * modeSin K ν
          * Real.sin (sitePhase K (linkTail ℓ)
            + modePhase K ℓ.1.2) := by
  classical
  have hsingle : ∀ v : linkAngle N,
      (∑ ℓ', ((Pi.single ℓ (1 : ℝ) : linkAngle N)) ℓ' * v ℓ')
        = v ℓ := by
    intro v
    rw [Finset.sum_eq_single ℓ]
    · rw [Pi.single_eq_same, one_mul]
    · intro b _ hb
      rw [Pi.single_eq_of_ne hb, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ ℓ) h
  have hform : (maxwellOp N (sinMode K A)) ℓ
      = ∑ c, ∑ μ, linkVal
          ((Pi.single ℓ (1 : ℝ) : linkAngle N)) c μ
        * (∑ ν, 4 * (A μ * modeSin K ν - A ν * modeSin K μ)
            * modeSin K ν
            * Real.sin (sitePhase K c + modePhase K μ)) := by
    rw [← hsingle (maxwellOp N (sinMode K A)), maxwellOp_form,
      sinMode_form hN ((Pi.single ℓ (1 : ℝ) : linkAngle N)) K A
        hK0]
  rw [hform]
  have hlink : ∀ (c : LayerSite N) (μ : Fin 4) (h : μ ≠ 0),
      layerLinkOf c μ h = ℓ → c = linkTail ℓ ∧ μ = ℓ.1.2 := by
    intro c μ h hℓ
    constructor
    · have ht : linkTail (layerLinkOf c μ h) = c := rfl
      rw [hℓ] at ht
      exact ht.symm
    · have hd : (layerLinkOf c μ h).1.2 = μ := rfl
      rw [hℓ] at hd
      exact hd.symm
  have hval : ∀ (c : LayerSite N) (μ : Fin 4),
      linkVal ((Pi.single ℓ (1 : ℝ) : linkAngle N)) c μ
        * (∑ ν, 4 * (A μ * modeSin K ν - A ν * modeSin K μ)
            * modeSin K ν
            * Real.sin (sitePhase K c + modePhase K μ))
      = (if c = linkTail ℓ ∧ μ = ℓ.1.2
          then ∑ ν, 4 * (A μ * modeSin K ν - A ν * modeSin K μ)
            * modeSin K ν
            * Real.sin (sitePhase K c + modePhase K μ)
          else 0) := by
    intro c μ
    by_cases h : c = linkTail ℓ ∧ μ = ℓ.1.2
    · rw [if_pos h]
      obtain ⟨rfl, rfl⟩ := h
      have h1 : linkVal ((Pi.single ℓ (1 : ℝ) : linkAngle N))
          (linkTail ℓ) ℓ.1.2 = 1 := by
        unfold linkVal
        rw [dif_pos ℓ.2.2]
        have hℓℓ : layerLinkOf (linkTail ℓ) ℓ.1.2 ℓ.2.2 = ℓ :=
          rfl
        rw [hℓℓ, Pi.single_eq_same]
      rw [h1, one_mul]
    · rw [if_neg h]
      have h0 : linkVal ((Pi.single ℓ (1 : ℝ) : linkAngle N))
          c μ = 0 := by
        by_cases hμ : μ = 0
        · rw [hμ]
          exact linkVal_zero _ _
        · unfold linkVal
          have hne : layerLinkOf c μ hμ ≠ ℓ :=
            fun hℓ => h (hlink c μ hμ hℓ)
          rw [dif_pos hμ, Pi.single_eq_of_ne hne]
      rw [h0, zero_mul]
  rw [Finset.sum_congr rfl
    (fun c _ => Finset.sum_congr rfl (fun μ _ => hval c μ))]
  rw [Finset.sum_eq_single (linkTail ℓ)]
  · rw [Finset.sum_eq_single ℓ.1.2]
    · rw [if_pos ⟨rfl, rfl⟩]
    · intro b _ hb
      rw [if_neg]
      intro hh
      exact hb hh.2
    · intro h
      exact absurd (Finset.mem_univ ℓ.1.2) h
  · intro b _ hb
    apply Finset.sum_eq_zero
    intro μ _
    rw [if_neg]
    intro hh
    exact hb hh.1
  · intro h
    exact absurd (Finset.mem_univ (linkTail ℓ)) h

/-- **The cosine mode is an eigenvector** of the pin's
`maxwellOp N` (as assembled by MAX-2) with transverse
eigenvalue `4 * ∑ μ, sin^2 (phase μ)`, whenever the
polarization is transverse: `K 0 = 0` and
`∑ ν, A ν * sin (phase ν) = 0`. Finite statement. -/
theorem cosMode_eigen (hN : 2 ≤ N)
    (K : Fin 4 → ZMod N) (A : Fin 4 → ℝ) (hK0 : K 0 = 0)
    (htrans : ∑ ν, A ν * modeSin K ν = 0) :
    maxwellOp N (cosMode K A)
      = (4 * ∑ μ, (modeSin K μ)^2) • cosMode K A := by
  funext ℓ
  rw [cosMode_form_single hN K A hK0 ℓ,
    cos_coeff_sum K A htrans (linkTail ℓ) ℓ.1.2]
  show (4 * ∑ ν, (modeSin K ν)^2)
      * (A ℓ.1.2 * Real.cos (sitePhase K (linkTail ℓ)
        + modePhase K ℓ.1.2))
    = (4 * ∑ μ, (modeSin K μ)^2)
      * (A ℓ.1.2 * Real.cos (sitePhase K (linkTail ℓ)
        + modePhase K ℓ.1.2))
  rfl

/-- **The sine mode is an eigenvector** of the pin's
`maxwellOp N` with the same transverse eigenvalue, under
the same transversality condition. Finite statement. -/
theorem sinMode_eigen (hN : 2 ≤ N)
    (K : Fin 4 → ZMod N) (A : Fin 4 → ℝ) (hK0 : K 0 = 0)
    (htrans : ∑ ν, A ν * modeSin K ν = 0) :
    maxwellOp N (sinMode K A)
      = (4 * ∑ μ, (modeSin K μ)^2) • sinMode K A := by
  funext ℓ
  rw [sinMode_form_single hN K A hK0 ℓ,
    sin_coeff_sum K A htrans (linkTail ℓ) ℓ.1.2]
  show (4 * ∑ ν, (modeSin K ν)^2)
      * (A ℓ.1.2 * Real.sin (sitePhase K (linkTail ℓ)
        + modePhase K ℓ.1.2))
    = (4 * ∑ μ, (modeSin K μ)^2)
      * (A ℓ.1.2 * Real.sin (sitePhase K (linkTail ℓ)
        + modePhase K ℓ.1.2))
  rfl

end Eigen

section Clauses

variable {N : ℕ} [NeZero N]

/-- The spatial sine profile at a spatial index:
`sin (π * (k j).val / N)` — a FINITE quantity. -/
noncomputable def modeSin3 (k : Fin 3 → ZMod N) (j : Fin 3) :
    ℝ :=
  Real.sin (Real.pi * ((k j).val : ℝ) / (N : ℝ))

/-- The phase of the extended momentum at a spatial
direction. -/
theorem modePhase_succ (k : Fin 3 → ZMod N) (j : Fin 3) :
    modePhase (Fin.cons (0 : ZMod N) k) (Fin.succ j)
      = Real.pi * ((k j).val : ℝ) / (N : ℝ) := by
  unfold modePhase
  rw [Fin.cons_succ]

/-- The transverse sine of the extended momentum at a
spatial direction is the spatial sine profile. -/
theorem modeSin_succ (k : Fin 3 → ZMod N) (j : Fin 3) :
    modeSin (Fin.cons (0 : ZMod N) k) (Fin.succ j)
      = modeSin3 k j := by
  unfold modeSin modeSin3
  rw [modePhase_succ]

/-- The `Fin 4` transverse eigenvalue of the extended
momentum `Fin.cons 0 k` is the pin's registered
`maxwellTransverseEig N k`. -/
theorem transverse_eig_eq (k : Fin 3 → ZMod N) :
    (4 * ∑ μ, (modeSin (Fin.cons (0 : ZMod N) k) μ)^2)
      = maxwellTransverseEig N k := by
  have h0 : modeSin (Fin.cons (0 : ZMod N) k) 0 = 0 :=
    modeSin_zero (K := Fin.cons (0 : ZMod N) k) (by rfl)
  unfold maxwellTransverseEig
  rw [Fin.sum_univ_succ, h0,
    zero_pow (show (2 : ℕ) ≠ 0 by norm_num), zero_add]
  congr 1

/-- The spatial sine profile is positive at a nonzero
momentum component: its angle lies in `(0, π)`. -/
theorem modeSin3_pos (hN : 2 ≤ N) (k : Fin 3 → ZMod N)
    (j : Fin 3) (hj : k j ≠ 0) : 0 < modeSin3 k j := by
  have hv : 1 ≤ (k j).val := by
    rcases Nat.eq_zero_or_pos (k j).val with h | h
    · exact False.elim
        (hj ((ZMod.val_eq_zero (k j)).mp h))
    · exact h
  have hlt : (k j).val < N := ZMod.val_lt (k j)
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast (by omega : 0 < N)
  unfold modeSin3
  apply Real.sin_pos_of_pos_of_lt_pi
  · apply div_pos _ hNpos
    have hvℝ : (0 : ℝ) < ((k j).val : ℝ) := by
      exact_mod_cast (by omega : 0 < (k j).val)
    exact mul_pos Real.pi_pos hvℝ
  · rw [div_lt_iff₀ hNpos]
    have hltℝ : ((k j).val : ℝ) < (N : ℝ) := by
      exact_mod_cast hlt
    exact mul_lt_mul_of_pos_left hltℝ Real.pi_pos

/-- **Clause (M5).1, zero half, at every `N ≥ 2`**: `0` is
an eigenvalue of the pin's `maxwellOp N`, witnessed by a
nonzero gauge (longitudinal) mode. -/
theorem hasEigenvalue_zero (hN : 2 ≤ N) :
    Module.End.HasEigenvalue (maxwellOp N) 0 := by
  classical
  refine Module.End.hasEigenvalue_of_hasEigenvector
    (x := gaugeAngle (fun c : LayerSite N =>
      ((c.1 (Fin.succ (0 : Fin 3))).val : ℝ))) ⟨?_, ?_⟩
  · exact Module.End.mem_eigenspace_iff.mpr (by
      rw [maxwellOp_gaugeAngle, zero_smul])
  · intro hzero
    have hval : gaugeAngle (fun c : LayerSite N =>
        ((c.1 (Fin.succ (0 : Fin 3))).val : ℝ))
        (layerLinkOf (zeroLayerSite (N := N)) (Fin.succ (0 : Fin 3))
          (Fin.succ_ne_zero 0)) = 1 := by
      have hshift : ((layerShift (Fin.succ (0 : Fin 3))
          (Fin.succ_ne_zero 0) (zeroLayerSite (N := N))).1
            (Fin.succ (0 : Fin 3))).val = 1 := by
        rw [layerShift_coord_self]
        have hz : (zeroLayerSite (N := N)).1
            (Fin.succ (0 : Fin 3)) = 0 := rfl
        rw [hz, zero_add, ZMod.val_one_eq_one_mod,
          Nat.mod_eq_of_lt (by omega : 1 < N)]
      have htail : ((zeroLayerSite (N := N)).1
          (Fin.succ (0 : Fin 3))).val = 0 := by
        have hz : (zeroLayerSite (N := N)).1
            (Fin.succ (0 : Fin 3)) = 0 := rfl
        rw [hz, ZMod.val_zero]
      show (((layerShift (Fin.succ (0 : Fin 3))
          (Fin.succ_ne_zero 0) (zeroLayerSite (N := N))).1
            (Fin.succ (0 : Fin 3))).val : ℝ)
        - (((zeroLayerSite (N := N)).1
            (Fin.succ (0 : Fin 3))).val : ℝ) = 1
      rw [hshift, htail, Nat.cast_one, Nat.cast_zero, sub_zero]
    have hcon := congrFun hzero (layerLinkOf (zeroLayerSite (N := N))
      (Fin.succ (0 : Fin 3)) (Fin.succ_ne_zero 0))
    simp only [Pi.zero_apply] at hcon
    rw [hval] at hcon
    exact one_ne_zero hcon

/-- The transverse value at zero momentum is `0`. -/
theorem maxwellTransverseEig_zero :
    maxwellTransverseEig N (0 : Fin 3 → ZMod N) = 0 := by
  unfold maxwellTransverseEig
  simp

/-- **Clause (M5).5**: the momentum `k = (1, 0, 0)` attains
the registered gap value `4 * sin^2 (π / N)`. -/
theorem clause5 (hN : 2 ≤ N) :
    ∃ k : Fin 3 → ZMod N,
      k 0 = 1 ∧ k 1 = 0 ∧ k 2 = 0 ∧
      maxwellTransverseEig N k
        = 4 * Real.sin (Real.pi / (N : ℝ)) ^ 2 := by
  refine ⟨Pi.single 0 1, by simp, by simp, by simp, ?_⟩
  have hv1 : ((Pi.single 0 (1 : ZMod N) : Fin 3 → ZMod N)
      0).val = 1 := by
    rw [show (Pi.single 0 (1 : ZMod N) : Fin 3 → ZMod N) 0 = 1
        from by simp,
      ZMod.val_one_eq_one_mod,
      Nat.mod_eq_of_lt (by omega : 1 < N)]
  have hv2 : ∀ i : Fin 3, i ≠ 0 →
      ((Pi.single 0 (1 : ZMod N) : Fin 3 → ZMod N) i).val
        = 0 := by
    intro i hi
    rw [show (Pi.single 0 (1 : ZMod N) : Fin 3 → ZMod N) i = 0
        from by
          rw [Pi.single_apply, if_neg hi],
      ZMod.val_zero]
  unfold maxwellTransverseEig
  rw [Fin.sum_univ_three, hv1, hv2 1 (by decide),
    hv2 2 (by decide)]
  simp

end Clauses

section Polarizations

variable {N : ℕ} [NeZero N]

/-- The two-support spatial polarization for the sine
profile `s`: value `s j0` at `p`, value `- s p` at `j0`,
zero elsewhere. -/
noncomputable def pol3 (s : Fin 3 → ℝ) (j0 p : Fin 3) :
    Fin 3 → ℝ :=
  fun r => if r = p then s j0 else if r = j0 then - s p else 0

/-- The two-support polarization at `p`. -/
theorem pol3_at_p (s : Fin 3 → ℝ) (j0 p : Fin 3) :
    pol3 s j0 p p = s j0 := by
  simp [pol3]

/-- The two-support polarization at `j0`. -/
theorem pol3_at_j0 (s : Fin 3 → ℝ) {j0 p : Fin 3}
    (hp : p ≠ j0) :
    pol3 s j0 p j0 = - s p := by
  unfold pol3
  rw [if_neg (Ne.symm hp), if_pos rfl]

/-- The two-support polarization is transverse for its
own sine profile. -/
theorem pol3_transverse (s : Fin 3 → ℝ) {j0 p : Fin 3}
    (hp : p ≠ j0) :
    ∑ j, pol3 s j0 p j * s j = 0 := by
  rw [Fin.sum_univ_three]
  fin_cases j0 <;> fin_cases p <;> simp_all [pol3] <;> ring

/-- The `Fin 4` polarization extending `pol3` by zero in
the time direction. -/
noncomputable def modePol (k : Fin 3 → ZMod N) (j0 p : Fin 3) :
    Fin 4 → ℝ :=
  Fin.cons 0 (pol3 (modeSin3 k) j0 p)

/-- The extended polarization at a spatial direction. -/
theorem modePol_succ (k : Fin 3 → ZMod N) (j0 p r : Fin 3) :
    modePol k j0 p (Fin.succ r) = pol3 (modeSin3 k) j0 p r := by
  rfl

/-- The extended polarization at `p` is the sine profile
at `j0`. -/
theorem modePol_at_p (k : Fin 3 → ZMod N) (j0 p : Fin 3) :
    modePol k j0 p (Fin.succ p) = modeSin3 k j0 := by
  rw [modePol_succ, pol3_at_p]

/-- The extended two-support polarization is transverse
for the extended momentum. -/
theorem modePol_transverse (k : Fin 3 → ZMod N)
    {j0 p : Fin 3} (hp : p ≠ j0) :
    ∑ ν, modePol k j0 p ν
        * modeSin (Fin.cons (0 : ZMod N) k) ν = 0 := by
  rw [Fin.sum_univ_succ]
  have h0 : modePol k j0 p 0 = 0 := rfl
  rw [h0, modeSin_zero (K := Fin.cons (0 : ZMod N) k) (by rfl),
    zero_mul, zero_add]
  have e : ∀ j : Fin 3, modePol k j0 p (Fin.succ j)
        * modeSin (Fin.cons (0 : ZMod N) k) (Fin.succ j)
      = pol3 (modeSin3 k) j0 p j * modeSin3 k j := by
    intro j
    rw [modePol_succ, modeSin_succ]
  rw [Finset.sum_congr rfl (fun j _ => e j)]
  exact pol3_transverse _ hp

/-- A single-support spatial polarization at a zero
momentum component is transverse. -/
theorem single_transverse (k : Fin 3 → ZMod N) (p : Fin 3)
    (hp : k p = 0) :
    ∑ ν, (Fin.cons 0 (Pi.single p (1 : ℝ)) : Fin 4 → ℝ) ν
        * modeSin (Fin.cons (0 : ZMod N) k) ν = 0 := by
  rw [Fin.sum_univ_succ]
  have h0 : (Fin.cons 0 (Pi.single p (1 : ℝ)) : Fin 4 → ℝ) 0
      = 0 := rfl
  rw [h0, modeSin_zero (K := Fin.cons (0 : ZMod N) k) (by rfl),
    zero_mul, zero_add]
  have e : ∀ j : Fin 3,
      (Fin.cons 0 (Pi.single p (1 : ℝ)) : Fin 4 → ℝ)
          (Fin.succ j)
        * modeSin (Fin.cons (0 : ZMod N) k) (Fin.succ j)
      = (if j = p then modeSin3 k p else 0) := by
    intro j
    rw [Fin.cons_succ, modeSin_succ, Pi.single_apply]
    by_cases h : j = p
    · subst h
      rw [if_pos rfl, if_pos rfl, one_mul]
    · rw [if_neg h, if_neg h, zero_mul]
  rw [Finset.sum_congr rfl (fun j _ => e j), Finset.sum_ite_eq']
  simp [modeSin3, hp]

/-- A difference of two single-support polarizations at
nonzero momentum components (where the sine profile is
`1`) is transverse. -/
theorem diff_transverse (hN : 2 ≤ N) (k : Fin 3 → ZMod N)
    {q q' : Fin 3} (hq : k q ≠ 0) (hq' : k q' ≠ 0)
    (hsin1 : ∀ j : Fin 3, k j ≠ 0 → modeSin3 k j = 1) :
    ∑ ν, (Fin.cons 0 ((Pi.single q (1 : ℝ))
        - (Pi.single q' (1 : ℝ))) : Fin 4 → ℝ) ν
        * modeSin (Fin.cons (0 : ZMod N) k) ν = 0 := by
  rw [Fin.sum_univ_succ]
  have h0 : (Fin.cons 0 ((Pi.single q (1 : ℝ))
      - (Pi.single q' (1 : ℝ))) : Fin 4 → ℝ) 0 = 0 := rfl
  rw [h0, modeSin_zero (K := Fin.cons (0 : ZMod N) k) (by rfl),
    zero_mul, zero_add]
  have e : ∀ j : Fin 3,
      (Fin.cons 0 ((Pi.single q (1 : ℝ))
        - (Pi.single q' (1 : ℝ))) : Fin 4 → ℝ) (Fin.succ j)
        * modeSin (Fin.cons (0 : ZMod N) k) (Fin.succ j)
      = (Pi.single q (1 : ℝ) : Fin 3 → ℝ) j * modeSin3 k j
        - (Pi.single q' (1 : ℝ) : Fin 3 → ℝ) j
          * modeSin3 k j := by
    intro j
    rw [Fin.cons_succ, modeSin_succ, Pi.sub_apply]
    ring
  rw [Finset.sum_congr rfl (fun j _ => e j),
    Finset.sum_sub_distrib]
  have hs : ∀ r : Fin 3,
      (∑ j, (Pi.single r (1 : ℝ) : Fin 3 → ℝ) j * modeSin3 k j)
        = modeSin3 k r := by
    intro r
    have e1 : ∀ j : Fin 3,
        (Pi.single r (1 : ℝ) : Fin 3 → ℝ) j * modeSin3 k j
        = (if j = r then modeSin3 k r else 0) := by
      intro j
      rw [Pi.single_apply]
      by_cases h : j = r
      · subst h
        rw [if_pos rfl, if_pos rfl, one_mul]
      · rw [if_neg h, if_neg h, zero_mul]
    rw [Finset.sum_congr rfl (fun j _ => e1 j),
      Finset.sum_ite_eq']
    simp
  rw [hs q, hs q', hsin1 q hq, hsin1 q' hq', sub_self]

/-- If `sin (2 * angle) = 0` for a momentum component,
then the component's value is `0` or twice it is `N`. -/
theorem val_eq_zero_or_two_mul (hN : 2 ≤ N)
    (k : Fin 3 → ZMod N) (j : Fin 3)
    (h : Real.sin (2 * (Real.pi * ((k j).val : ℝ) / (N : ℝ)))
      = 0) :
    (k j).val = 0 ∨ 2 * (k j).val = N := by
  rw [Real.sin_eq_zero_iff] at h
  obtain ⟨n, hn⟩ := h
  have hNℝ : (N : ℝ) ≠ 0 := by
    exact_mod_cast (NeZero.ne N)
  have keyπ : ((n : ℝ) * (N : ℝ)) * Real.pi
      = (2 * ((k j).val : ℝ)) * Real.pi := by
    have h2 : ((n : ℝ) * Real.pi) * (N : ℝ)
        = (2 * (Real.pi * ((k j).val : ℝ) / (N : ℝ)))
          * (N : ℝ) := by
      rw [hn]
    have e1 : ((n : ℝ) * (N : ℝ)) * Real.pi
        = ((n : ℝ) * Real.pi) * (N : ℝ) := by ring
    have e2 : (2 * (Real.pi * ((k j).val : ℝ) / (N : ℝ)))
        * (N : ℝ) = (2 * ((k j).val : ℝ)) * Real.pi := by
      field_simp
    rw [e1, h2, e2]
  have key : (n : ℝ) * (N : ℝ) = 2 * ((k j).val : ℝ) :=
    mul_right_cancel₀ Real.pi_ne_zero keyπ
  have hn' : (n : ℝ) = 2 * ((k j).val : ℝ) / (N : ℝ) :=
    (eq_div_iff hNℝ).mpr key
  have hlt : (k j).val < N := ZMod.val_lt (k j)
  have hn0 : 0 ≤ n := by
    by_contra hc
    push_neg at hc
    have hcℝ : (n : ℝ) < 0 := by exact_mod_cast hc
    rw [hn'] at hcℝ
    have hnn : (0 : ℝ) ≤ 2 * ((k j).val : ℝ) / (N : ℝ) := by
      apply div_nonneg _ (by exact_mod_cast (by omega : 0 ≤ N))
      have hv0 : (0 : ℝ) ≤ ((k j).val : ℝ) := by
        exact_mod_cast (Nat.zero_le _)
      linarith
    linarith
  have hn2 : n < 2 := by
    by_contra hc
    push_neg at hc
    have hcℝ : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hc
    rw [hn'] at hcℝ
    have hNpos : (0 : ℝ) < (N : ℝ) := by
      exact_mod_cast (by omega : 0 < N)
    have hle : (2 : ℝ) * (N : ℝ) ≤ 2 * ((k j).val : ℝ) :=
      (le_div_iff₀ hNpos).mp hcℝ
    have hleℕ : N ≤ (k j).val := by
      have h2 : (N : ℝ) ≤ ((k j).val : ℝ) := by linarith
      exact_mod_cast h2
    omega
  interval_cases n
  · left
    simp only [Int.cast_zero] at hn'
    have h2 : (2 : ℝ) * ((k j).val : ℝ) = 0 := by
      rcases (div_eq_zero_iff).mp hn'.symm with h | h
      · exact h
      · exact absurd h hNℝ
    have hv0 : ((k j).val : ℝ) = 0 := by
      rcases mul_eq_zero.mp h2 with h | h
      · norm_num at h
      · exact h
    exact_mod_cast hv0
  · right
    simp only [Int.cast_one] at hn'
    have h2 : (2 : ℝ) * ((k j).val : ℝ) = (N : ℝ) := by
      have h3 := (div_eq_iff hNℝ).mp hn'.symm
      linarith
    exact_mod_cast h2

/-- At a nonzero momentum component where `sin (2 * angle)
= 0`, the sine profile is exactly `1` (the angle is
`π / 2`, using `Even`-free input `2 ≤ N` and the value
alternative). -/
theorem modeSin3_eq_one (hN : 2 ≤ N) (k : Fin 3 → ZMod N)
    (j : Fin 3) (hj : k j ≠ 0)
    (h : Real.sin (2 * (Real.pi * ((k j).val : ℝ) / (N : ℝ)))
      = 0) :
    modeSin3 k j = 1 := by
  have h2v : 2 * (k j).val = N := by
    rcases val_eq_zero_or_two_mul hN k j h with h0 | h2
    · exact absurd ((ZMod.val_eq_zero (k j)).mp h0) hj
    · exact h2
  have hNℝ : (N : ℝ) ≠ 0 := by
    exact_mod_cast (NeZero.ne N)
  have h2vℝ : (2 : ℝ) * ((k j).val : ℝ) = (N : ℝ) := by
    exact_mod_cast h2v
  have harg : Real.pi * ((k j).val : ℝ) / (N : ℝ)
      = Real.pi / 2 := by
    rw [div_eq_div_iff hNℝ (by norm_num : (2 : ℝ) ≠ 0)]
    have hπ : Real.pi * (2 * ((k j).val : ℝ))
        = Real.pi * (N : ℝ) := by
      rw [h2vℝ]
    linarith [hπ]
  unfold modeSin3
  rw [harg, Real.sin_pi_div_two]

end Polarizations

section Clause2Cases

variable {N : ℕ} [NeZero N]

/-- **Clause (M5).2, Case I** (`sin (2 * angle_j) ≠ 0` for
some spatial index `j`): the cosine and sine modes at the
two-support polarization are two linearly independent
eigenmodes at the transverse value. -/
theorem clause2_caseI (hN : 2 ≤ N) (k : Fin 3 → ZMod N)
    (hk : k ≠ 0) (j : Fin 3)
    (hj : Real.sin (2 * (Real.pi * ((k j).val : ℝ) / (N : ℝ)))
      ≠ 0) :
    ∃ θ₁ θ₂ : linkAngle N,
      (∀ a b : ℝ, a • θ₁ + b • θ₂ = 0 → a = 0 ∧ b = 0) ∧
      maxwellOp N θ₁ = (maxwellTransverseEig N k) • θ₁ ∧
      maxwellOp N θ₂ = (maxwellTransverseEig N k) • θ₂ := by
  obtain ⟨j0, hj0⟩ : ∃ j, k j ≠ 0 := by
    by_contra h
    push_neg at h
    exact hk (funext h)
  obtain ⟨p, hp⟩ : ∃ p : Fin 3, p ≠ j0 := by
    by_cases h : j0 = 0
    · exact ⟨1, by rw [h]; decide⟩
    · exact ⟨0, Ne.symm h⟩
  have htrans := modePol_transverse k hp
  have heigc : maxwellOp N (cosMode (Fin.cons (0 : ZMod N) k)
        (modePol k j0 p))
      = (maxwellTransverseEig N k)
        • cosMode (Fin.cons (0 : ZMod N) k) (modePol k j0 p) := by
    rw [← transverse_eig_eq]
    exact cosMode_eigen hN (Fin.cons (0 : ZMod N) k)
      (modePol k j0 p) (by rfl) htrans
  have heigs : maxwellOp N (sinMode (Fin.cons (0 : ZMod N) k)
        (modePol k j0 p))
      = (maxwellTransverseEig N k)
        • sinMode (Fin.cons (0 : ZMod N) k) (modePol k j0 p) := by
    rw [← transverse_eig_eq]
    exact sinMode_eigen hN (Fin.cons (0 : ZMod N) k)
      (modePol k j0 p) (by rfl) htrans
  refine ⟨cosMode (Fin.cons (0 : ZMod N) k) (modePol k j0 p),
    sinMode (Fin.cons (0 : ZMod N) k) (modePol k j0 p),
    ?_, heigc, heigs⟩
  intro u v huv
  have hsj0 : modeSin3 k j0 ≠ 0 :=
    ne_of_gt (modeSin3_pos hN k j0 hj0)
  have e0 := congrFun huv (layerLinkOf (zeroLayerSite (N := N))
    (Fin.succ p) (Fin.succ_ne_zero p))
  have e1 := congrFun huv (layerLinkOf
    (layerShift (Fin.succ j) (Fin.succ_ne_zero j)
      (zeroLayerSite (N := N)))
    (Fin.succ p) (Fin.succ_ne_zero p))
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Pi.zero_apply] at e0 e1
  have v0c : cosMode (Fin.cons (0 : ZMod N) k) (modePol k j0 p)
        (layerLinkOf (zeroLayerSite (N := N)) (Fin.succ p)
          (Fin.succ_ne_zero p))
      = modeSin3 k j0
        * Real.cos (Real.pi * ((k p).val : ℝ) / (N : ℝ)) := by
    rw [cosMode_linkOf, modePol_at_p, sitePhase_zeroLayerSite,
      modePhase_succ, zero_add]
  have v0s : sinMode (Fin.cons (0 : ZMod N) k) (modePol k j0 p)
        (layerLinkOf (zeroLayerSite (N := N)) (Fin.succ p)
          (Fin.succ_ne_zero p))
      = modeSin3 k j0
        * Real.sin (Real.pi * ((k p).val : ℝ) / (N : ℝ)) := by
    rw [sinMode_linkOf, modePol_at_p, sitePhase_zeroLayerSite,
      modePhase_succ, zero_add]
  have v1c : cosMode (Fin.cons (0 : ZMod N) k) (modePol k j0 p)
        (layerLinkOf
          (layerShift (Fin.succ j) (Fin.succ_ne_zero j)
            (zeroLayerSite (N := N)))
          (Fin.succ p) (Fin.succ_ne_zero p))
      = modeSin3 k j0
        * Real.cos (2 * (Real.pi * ((k j).val : ℝ) / (N : ℝ))
          + Real.pi * ((k p).val : ℝ) / (N : ℝ)) := by
    rw [cosMode_linkOf, modePol_at_p,
      cos_sitePhase_layerShift hN (Fin.cons (0 : ZMod N) k)
        (Fin.succ j) (Fin.succ_ne_zero j) (zeroLayerSite (N := N))
        (modePhase (Fin.cons (0 : ZMod N) k) (Fin.succ p)),
      sitePhase_zeroLayerSite, modePhase_succ, modePhase_succ,
      zero_add]
  have v1s : sinMode (Fin.cons (0 : ZMod N) k) (modePol k j0 p)
        (layerLinkOf
          (layerShift (Fin.succ j) (Fin.succ_ne_zero j)
            (zeroLayerSite (N := N)))
          (Fin.succ p) (Fin.succ_ne_zero p))
      = modeSin3 k j0
        * Real.sin (2 * (Real.pi * ((k j).val : ℝ) / (N : ℝ))
          + Real.pi * ((k p).val : ℝ) / (N : ℝ)) := by
    rw [sinMode_linkOf, modePol_at_p,
      sin_sitePhase_layerShift hN (Fin.cons (0 : ZMod N) k)
        (Fin.succ j) (Fin.succ_ne_zero j) (zeroLayerSite (N := N))
        (modePhase (Fin.cons (0 : ZMod N) k) (Fin.succ p)),
      sitePhase_zeroLayerSite, modePhase_succ, modePhase_succ,
      zero_add]
  rw [v0c, v0s] at e0
  rw [v1c, v1s] at e1
  have f0 : u * Real.cos (Real.pi * ((k p).val : ℝ) / (N : ℝ))
      + v * Real.sin (Real.pi * ((k p).val : ℝ) / (N : ℝ))
      = 0 := by
    have hfac : modeSin3 k j0
        * (u * Real.cos (Real.pi * ((k p).val : ℝ) / (N : ℝ))
          + v * Real.sin (Real.pi * ((k p).val : ℝ) / (N : ℝ)))
        = 0 := by
      linarith [e0]
    exact (mul_eq_zero.mp hfac).resolve_left hsj0
  have f1 : u * Real.cos
        (2 * (Real.pi * ((k j).val : ℝ) / (N : ℝ))
          + Real.pi * ((k p).val : ℝ) / (N : ℝ))
      + v * Real.sin
        (2 * (Real.pi * ((k j).val : ℝ) / (N : ℝ))
          + Real.pi * ((k p).val : ℝ) / (N : ℝ)) = 0 := by
    have hfac : modeSin3 k j0
        * (u * Real.cos
            (2 * (Real.pi * ((k j).val : ℝ) / (N : ℝ))
              + Real.pi * ((k p).val : ℝ) / (N : ℝ))
          + v * Real.sin
            (2 * (Real.pi * ((k j).val : ℝ) / (N : ℝ))
              + Real.pi * ((k p).val : ℝ) / (N : ℝ))) = 0 := by
      linarith [e1]
    exact (mul_eq_zero.mp hfac).resolve_left hsj0
  have hexp : u * Real.cos
        (2 * (Real.pi * ((k j).val : ℝ) / (N : ℝ))
          + Real.pi * ((k p).val : ℝ) / (N : ℝ))
      + v * Real.sin
        (2 * (Real.pi * ((k j).val : ℝ) / (N : ℝ))
          + Real.pi * ((k p).val : ℝ) / (N : ℝ))
      = Real.cos (2 * (Real.pi * ((k j).val : ℝ) / (N : ℝ)))
          * (u * Real.cos (Real.pi * ((k p).val : ℝ) / (N : ℝ))
            + v * Real.sin (Real.pi * ((k p).val : ℝ)
              / (N : ℝ)))
        + Real.sin (2 * (Real.pi * ((k j).val : ℝ) / (N : ℝ)))
          * (v * Real.cos (Real.pi * ((k p).val : ℝ) / (N : ℝ))
            - u * Real.sin (Real.pi * ((k p).val : ℝ)
              / (N : ℝ))) := by
    rw [Real.cos_add, Real.sin_add]
    ring
  have hW : v * Real.cos (Real.pi * ((k p).val : ℝ) / (N : ℝ))
      - u * Real.sin (Real.pi * ((k p).val : ℝ) / (N : ℝ))
      = 0 := by
    have h3 : Real.cos (2 * (Real.pi * ((k j).val : ℝ)
        / (N : ℝ)))
        * (u * Real.cos (Real.pi * ((k p).val : ℝ) / (N : ℝ))
          + v * Real.sin (Real.pi * ((k p).val : ℝ) / (N : ℝ)))
        = 0 := by
      rw [f0, mul_zero]
    have h2 : Real.sin (2 * (Real.pi * ((k j).val : ℝ)
        / (N : ℝ)))
        * (v * Real.cos (Real.pi * ((k p).val : ℝ) / (N : ℝ))
          - u * Real.sin (Real.pi * ((k p).val : ℝ) / (N : ℝ)))
        = 0 := by
      linarith [f1, hexp, h3]
    exact (mul_eq_zero.mp h2).resolve_left hj
  constructor
  · have hcs := Real.cos_sq_add_sin_sq
      (Real.pi * ((k p).val : ℝ) / (N : ℝ))
    have hu : u * (Real.cos
        (Real.pi * ((k p).val : ℝ) / (N : ℝ)) ^ 2
        + Real.sin (Real.pi * ((k p).val : ℝ) / (N : ℝ)) ^ 2)
        = 0 := by
      have g1 : u * Real.cos
          (Real.pi * ((k p).val : ℝ) / (N : ℝ))
          = - (v * Real.sin
            (Real.pi * ((k p).val : ℝ) / (N : ℝ))) := by
        linarith [f0]
      have g2 : u * Real.sin
          (Real.pi * ((k p).val : ℝ) / (N : ℝ))
          = v * Real.cos
            (Real.pi * ((k p).val : ℝ) / (N : ℝ)) := by
        linarith [hW]
      calc u * (Real.cos
            (Real.pi * ((k p).val : ℝ) / (N : ℝ)) ^ 2
            + Real.sin (Real.pi * ((k p).val : ℝ) / (N : ℝ))
              ^ 2)
          = Real.cos (Real.pi * ((k p).val : ℝ) / (N : ℝ))
              * (u * Real.cos
                (Real.pi * ((k p).val : ℝ) / (N : ℝ)))
            + Real.sin (Real.pi * ((k p).val : ℝ) / (N : ℝ))
              * (u * Real.sin
                (Real.pi * ((k p).val : ℝ) / (N : ℝ))) := by
            ring
        _ = Real.cos (Real.pi * ((k p).val : ℝ) / (N : ℝ))
              * (- (v * Real.sin
                (Real.pi * ((k p).val : ℝ) / (N : ℝ))))
            + Real.sin (Real.pi * ((k p).val : ℝ) / (N : ℝ))
              * (v * Real.cos
                (Real.pi * ((k p).val : ℝ) / (N : ℝ))) := by
            rw [g1, g2]
        _ = 0 := by ring
    rw [hcs, mul_one] at hu
    exact hu
  · have hcs := Real.cos_sq_add_sin_sq
      (Real.pi * ((k p).val : ℝ) / (N : ℝ))
    have hv : v * (Real.cos
        (Real.pi * ((k p).val : ℝ) / (N : ℝ)) ^ 2
        + Real.sin (Real.pi * ((k p).val : ℝ) / (N : ℝ)) ^ 2)
        = 0 := by
      have g1 : v * Real.sin
          (Real.pi * ((k p).val : ℝ) / (N : ℝ))
          = - (u * Real.cos
            (Real.pi * ((k p).val : ℝ) / (N : ℝ))) := by
        linarith [f0]
      have g2 : v * Real.cos
          (Real.pi * ((k p).val : ℝ) / (N : ℝ))
          = u * Real.sin
            (Real.pi * ((k p).val : ℝ) / (N : ℝ)) := by
        linarith [hW]
      calc v * (Real.cos
            (Real.pi * ((k p).val : ℝ) / (N : ℝ)) ^ 2
            + Real.sin (Real.pi * ((k p).val : ℝ) / (N : ℝ))
              ^ 2)
          = Real.cos (Real.pi * ((k p).val : ℝ) / (N : ℝ))
              * (v * Real.cos
                (Real.pi * ((k p).val : ℝ) / (N : ℝ)))
            + Real.sin (Real.pi * ((k p).val : ℝ) / (N : ℝ))
              * (v * Real.sin
                (Real.pi * ((k p).val : ℝ) / (N : ℝ))) := by
            ring
        _ = Real.cos (Real.pi * ((k p).val : ℝ) / (N : ℝ))
              * (u * Real.sin
                (Real.pi * ((k p).val : ℝ) / (N : ℝ)))
            + Real.sin (Real.pi * ((k p).val : ℝ) / (N : ℝ))
              * (- (u * Real.cos
                (Real.pi * ((k p).val : ℝ) / (N : ℝ)))) := by
            rw [g1, g2]
        _ = 0 := by ring
    rw [hcs, mul_one] at hv
    exact hv

/-- **Clause (M5).2, Case IIa**: some component vanishes,
and two distinct components are nonzero (so all angles
are `0` or `π / 2`): a cosine single-support mode at the
vanishing component and a sine difference mode at the
nonzero pair are independent eigenmodes. -/
theorem clause2_caseIIa (hN : 2 ≤ N) (k : Fin 3 → ZMod N)
    (hsin1 : ∀ j : Fin 3, k j ≠ 0 → modeSin3 k j = 1)
    {p q q' : Fin 3} (hp0 : k p = 0) (hq : k q ≠ 0)
    (hq' : k q' ≠ 0) (hqq' : q ≠ q') :
    ∃ θ₁ θ₂ : linkAngle N,
      (∀ a b : ℝ, a • θ₁ + b • θ₂ = 0 → a = 0 ∧ b = 0) ∧
      maxwellOp N θ₁ = (maxwellTransverseEig N k) • θ₁ ∧
      maxwellOp N θ₂ = (maxwellTransverseEig N k) • θ₂ := by
  have hpq : p ≠ q := fun h => hq (h ▸ hp0)
  have hpq' : p ≠ q' := fun h => hq' (h ▸ hp0)
  refine ⟨cosMode (Fin.cons (0 : ZMod N) k)
      (Fin.cons 0 (Pi.single p (1 : ℝ))),
    sinMode (Fin.cons (0 : ZMod N) k)
      (Fin.cons 0 ((Pi.single q (1 : ℝ))
        - (Pi.single q' (1 : ℝ)))), ?_, ?_, ?_⟩
  · intro u v huv
    have e0 := congrFun huv (layerLinkOf
      (zeroLayerSite (N := N)) (Fin.succ p) (Fin.succ_ne_zero p))
    have e1 := congrFun huv (layerLinkOf
      (zeroLayerSite (N := N)) (Fin.succ q) (Fin.succ_ne_zero q))
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Pi.zero_apply] at e0 e1
    have v0c : cosMode (Fin.cons (0 : ZMod N) k)
          (Fin.cons 0 (Pi.single p (1 : ℝ)))
          (layerLinkOf (zeroLayerSite (N := N)) (Fin.succ p)
            (Fin.succ_ne_zero p)) = 1 := by
      rw [cosMode_linkOf, Fin.cons_succ, Pi.single_eq_same,
        sitePhase_zeroLayerSite, modePhase_succ, hp0]
      simp
    have v0s : sinMode (Fin.cons (0 : ZMod N) k)
          (Fin.cons 0 ((Pi.single q (1 : ℝ))
            - (Pi.single q' (1 : ℝ))))
          (layerLinkOf (zeroLayerSite (N := N)) (Fin.succ p)
            (Fin.succ_ne_zero p)) = 0 := by
      rw [sinMode_linkOf, Fin.cons_succ, Pi.sub_apply,
        Pi.single_apply, Pi.single_apply, if_neg hpq,
        if_neg hpq', sub_self, zero_mul]
    have v1c : cosMode (Fin.cons (0 : ZMod N) k)
          (Fin.cons 0 (Pi.single p (1 : ℝ)))
          (layerLinkOf (zeroLayerSite (N := N)) (Fin.succ q)
            (Fin.succ_ne_zero q)) = 0 := by
      rw [cosMode_linkOf, Fin.cons_succ, Pi.single_apply,
        if_neg (Ne.symm hpq), zero_mul]
    have v1s : sinMode (Fin.cons (0 : ZMod N) k)
          (Fin.cons 0 ((Pi.single q (1 : ℝ))
            - (Pi.single q' (1 : ℝ))))
          (layerLinkOf (zeroLayerSite (N := N)) (Fin.succ q)
            (Fin.succ_ne_zero q)) = 1 := by
      rw [sinMode_linkOf, Fin.cons_succ, Pi.sub_apply,
        Pi.single_eq_same, Pi.single_apply, if_neg hqq',
        sitePhase_zeroLayerSite, modePhase_succ, zero_add,
        show Real.sin (Real.pi * ((k q).val : ℝ) / (N : ℝ)) = 1
          from hsin1 q hq,
        sub_zero, one_mul]
    rw [v0c, v0s] at e0
    rw [v1c, v1s] at e1
    constructor <;> linarith [e0, e1]
  · rw [← transverse_eig_eq]
    exact cosMode_eigen hN (Fin.cons (0 : ZMod N) k)
      (Fin.cons 0 (Pi.single p (1 : ℝ))) (by rfl)
      (single_transverse k p hp0)
  · have h := sinMode_eigen hN (Fin.cons (0 : ZMod N) k)
      (Fin.cons 0 ((Pi.single q (1 : ℝ))
        - (Pi.single q' (1 : ℝ)))) (by rfl)
      (diff_transverse hN k hq hq' hsin1)
    rwa [transverse_eig_eq] at h

/-- **Clause (M5).2, Case IIb**: exactly two components
vanish: the cosine single-support modes at those two
components are independent eigenmodes. -/
theorem clause2_caseIIb (hN : 2 ≤ N) (k : Fin 3 → ZMod N)
    {p q : Fin 3} (hpq : p ≠ q) (hp0 : k p = 0)
    (hq0 : k q = 0) :
    ∃ θ₁ θ₂ : linkAngle N,
      (∀ a b : ℝ, a • θ₁ + b • θ₂ = 0 → a = 0 ∧ b = 0) ∧
      maxwellOp N θ₁ = (maxwellTransverseEig N k) • θ₁ ∧
      maxwellOp N θ₂ = (maxwellTransverseEig N k) • θ₂ := by
  refine ⟨cosMode (Fin.cons (0 : ZMod N) k)
      (Fin.cons 0 (Pi.single p (1 : ℝ))),
    cosMode (Fin.cons (0 : ZMod N) k)
      (Fin.cons 0 (Pi.single q (1 : ℝ))), ?_, ?_, ?_⟩
  · intro u v huv
    have e0 := congrFun huv (layerLinkOf
      (zeroLayerSite (N := N)) (Fin.succ p) (Fin.succ_ne_zero p))
    have e1 := congrFun huv (layerLinkOf
      (zeroLayerSite (N := N)) (Fin.succ q) (Fin.succ_ne_zero q))
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Pi.zero_apply] at e0 e1
    have vpp : cosMode (Fin.cons (0 : ZMod N) k)
          (Fin.cons 0 (Pi.single p (1 : ℝ)))
          (layerLinkOf (zeroLayerSite (N := N)) (Fin.succ p)
            (Fin.succ_ne_zero p)) = 1 := by
      rw [cosMode_linkOf, Fin.cons_succ, Pi.single_eq_same,
        sitePhase_zeroLayerSite, modePhase_succ, hp0]
      simp
    have vqp : cosMode (Fin.cons (0 : ZMod N) k)
          (Fin.cons 0 (Pi.single q (1 : ℝ)))
          (layerLinkOf (zeroLayerSite (N := N)) (Fin.succ p)
            (Fin.succ_ne_zero p)) = 0 := by
      rw [cosMode_linkOf, Fin.cons_succ, Pi.single_apply,
        if_neg hpq, zero_mul]
    have vpq : cosMode (Fin.cons (0 : ZMod N) k)
          (Fin.cons 0 (Pi.single p (1 : ℝ)))
          (layerLinkOf (zeroLayerSite (N := N)) (Fin.succ q)
            (Fin.succ_ne_zero q)) = 0 := by
      rw [cosMode_linkOf, Fin.cons_succ, Pi.single_apply,
        if_neg (Ne.symm hpq), zero_mul]
    have vqq : cosMode (Fin.cons (0 : ZMod N) k)
          (Fin.cons 0 (Pi.single q (1 : ℝ)))
          (layerLinkOf (zeroLayerSite (N := N)) (Fin.succ q)
            (Fin.succ_ne_zero q)) = 1 := by
      rw [cosMode_linkOf, Fin.cons_succ, Pi.single_eq_same,
        sitePhase_zeroLayerSite, modePhase_succ, hq0]
      simp
    rw [vpp, vqp] at e0
    rw [vpq, vqq] at e1
    constructor <;> linarith [e0, e1]
  · rw [← transverse_eig_eq]
    exact cosMode_eigen hN (Fin.cons (0 : ZMod N) k)
      (Fin.cons 0 (Pi.single p (1 : ℝ))) (by rfl)
      (single_transverse k p hp0)
  · rw [← transverse_eig_eq]
    exact cosMode_eigen hN (Fin.cons (0 : ZMod N) k)
      (Fin.cons 0 (Pi.single q (1 : ℝ))) (by rfl)
      (single_transverse k q hq0)

end Clause2Cases

section Assembly

variable {N : ℕ} [NeZero N]

/-- **Clause (M5).1**: at every spatial momentum `k`, the
transverse value `maxwellTransverseEig N k` is an
eigenvalue of the pin's `maxwellOp N` (Fourier link modes
diagonalize the operator), and `0` is an eigenvalue
(gauge mode). At general Even `N`; FINITE. -/
theorem clause1 (hN : Even N) :
    ∀ k : Fin 3 → ZMod N,
      Module.End.HasEigenvalue (maxwellOp N)
          (maxwellTransverseEig N k) ∧
      Module.End.HasEigenvalue (maxwellOp N) 0 := by
  obtain ⟨r, hr⟩ := hN
  have h2 : 2 ≤ N := by
    have hN0 : N ≠ 0 := NeZero.ne N
    omega
  intro k
  refine ⟨?_, hasEigenvalue_zero h2⟩
  by_cases hk : k = 0
  · subst hk
    rw [maxwellTransverseEig_zero]
    exact hasEigenvalue_zero h2
  · obtain ⟨j0, hj0⟩ : ∃ j, k j ≠ 0 := by
      by_contra h
      push_neg at h
      exact hk (funext h)
    obtain ⟨p, hp⟩ : ∃ p : Fin 3, p ≠ j0 := by
      by_cases h : j0 = 0
      · exact ⟨1, by rw [h]; decide⟩
      · exact ⟨0, Ne.symm h⟩
    have htrans := modePol_transverse k hp
    have heigc : maxwellOp N (cosMode (Fin.cons (0 : ZMod N) k)
          (modePol k j0 p))
        = (maxwellTransverseEig N k)
          • cosMode (Fin.cons (0 : ZMod N) k)
            (modePol k j0 p) := by
      rw [← transverse_eig_eq]
      exact cosMode_eigen h2 (Fin.cons (0 : ZMod N) k)
        (modePol k j0 p) (by rfl) htrans
    have heigs : maxwellOp N (sinMode (Fin.cons (0 : ZMod N) k)
          (modePol k j0 p))
        = (maxwellTransverseEig N k)
          • sinMode (Fin.cons (0 : ZMod N) k)
            (modePol k j0 p) := by
      rw [← transverse_eig_eq]
      exact sinMode_eigen h2 (Fin.cons (0 : ZMod N) k)
        (modePol k j0 p) (by rfl) htrans
    by_cases hc : cosMode (Fin.cons (0 : ZMod N) k)
        (modePol k j0 p) = 0
    · have hs : sinMode (Fin.cons (0 : ZMod N) k)
          (modePol k j0 p) ≠ 0 := by
        intro hs0
        have v0c : cosMode (Fin.cons (0 : ZMod N) k)
              (modePol k j0 p)
              (layerLinkOf (zeroLayerSite (N := N))
                (Fin.succ p) (Fin.succ_ne_zero p))
            = modeSin3 k j0
              * Real.cos (Real.pi * ((k p).val : ℝ)
                / (N : ℝ)) := by
          rw [cosMode_linkOf, modePol_at_p,
            sitePhase_zeroLayerSite, modePhase_succ, zero_add]
        have v0s : sinMode (Fin.cons (0 : ZMod N) k)
              (modePol k j0 p)
              (layerLinkOf (zeroLayerSite (N := N))
                (Fin.succ p) (Fin.succ_ne_zero p))
            = modeSin3 k j0
              * Real.sin (Real.pi * ((k p).val : ℝ)
                / (N : ℝ)) := by
          rw [sinMode_linkOf, modePol_at_p,
            sitePhase_zeroLayerSite, modePhase_succ, zero_add]
        have e1 : modeSin3 k j0
            * Real.cos (Real.pi * ((k p).val : ℝ) / (N : ℝ))
            = 0 := by
          have h := congrFun hc (layerLinkOf
            (zeroLayerSite (N := N)) (Fin.succ p)
            (Fin.succ_ne_zero p))
          simp only [Pi.zero_apply] at h
          rwa [v0c] at h
        have e2 : modeSin3 k j0
            * Real.sin (Real.pi * ((k p).val : ℝ) / (N : ℝ))
            = 0 := by
          have h := congrFun hs0 (layerLinkOf
            (zeroLayerSite (N := N)) (Fin.succ p)
            (Fin.succ_ne_zero p))
          simp only [Pi.zero_apply] at h
          rwa [v0s] at h
        have hsj0 : modeSin3 k j0 ≠ 0 :=
          ne_of_gt (modeSin3_pos h2 k j0 hj0)
        have hc0 : Real.cos (Real.pi * ((k p).val : ℝ)
            / (N : ℝ)) = 0 :=
          (mul_eq_zero.mp e1).resolve_left hsj0
        have hs0' : Real.sin (Real.pi * ((k p).val : ℝ)
            / (N : ℝ)) = 0 :=
          (mul_eq_zero.mp e2).resolve_left hsj0
        have hcs := Real.cos_sq_add_sin_sq
          (Real.pi * ((k p).val : ℝ) / (N : ℝ))
        rw [hc0, hs0'] at hcs
        norm_num at hcs
      exact Module.End.hasEigenvalue_of_hasEigenvector
        ⟨Module.End.mem_eigenspace_iff.mpr heigs, hs⟩
    · exact Module.End.hasEigenvalue_of_hasEigenvector
        ⟨Module.End.mem_eigenspace_iff.mpr heigc, hc⟩

set_option maxHeartbeats 1600000 in
/-- **Clause (M5).2**: at every nonzero spatial momentum,
the transverse eigenvalue carries two linearly
independent eigenmodes (the registered multiplicity).
At general Even `N`; FINITE. -/
theorem clause2 (hN : Even N) :
    ∀ k : Fin 3 → ZMod N, k ≠ 0 →
      ∃ θ₁ θ₂ : linkAngle N,
        (∀ a b : ℝ, a • θ₁ + b • θ₂ = 0 → a = 0 ∧ b = 0) ∧
        maxwellOp N θ₁ = (maxwellTransverseEig N k) • θ₁ ∧
        maxwellOp N θ₂ = (maxwellTransverseEig N k) • θ₂ := by
  obtain ⟨r, hr⟩ := hN
  have h2 : 2 ≤ N := by
    have hN0 : N ≠ 0 := NeZero.ne N
    omega
  intro k hk
  by_cases hcase : ∃ j : Fin 3,
      Real.sin (2 * (Real.pi * ((k j).val : ℝ) / (N : ℝ)))
        ≠ 0
  · obtain ⟨j, hj⟩ := hcase
    exact clause2_caseI h2 k hk j hj
  · have hall : ∀ j : Fin 3,
        Real.sin (2 * (Real.pi * ((k j).val : ℝ) / (N : ℝ)))
          = 0 := by
      intro j
      by_contra h
      exact hcase ⟨j, h⟩
    have hsin1 : ∀ j : Fin 3, k j ≠ 0 → modeSin3 k j = 1 :=
      fun j hj => modeSin3_eq_one h2 k j hj (hall j)
    by_cases hS : ∃ p : Fin 3, k p = 0
    · obtain ⟨p, hp0⟩ := hS
      by_cases hS2 : ∃ q q' : Fin 3,
          q ≠ q' ∧ k q ≠ 0 ∧ k q' ≠ 0
      · obtain ⟨q, q', hqq', hq, hq'⟩ := hS2
        exact clause2_caseIIa h2 k hsin1 hp0 hq hq' hqq'
      · push_neg at hS2
        obtain ⟨j0, hj0⟩ : ∃ j, k j ≠ 0 := by
          by_contra h
          push_neg at h
          exact hk (funext h)
        have hpj0 : p ≠ j0 := fun h => hj0 (h ▸ hp0)
        obtain ⟨q, hqp, hqj0⟩ : ∃ q : Fin 3,
            q ≠ p ∧ q ≠ j0 := by
          fin_cases j0 <;> fin_cases p <;>
            first
              | (exfalso; exact hpj0 rfl)
              | exact ⟨0, by decide, by decide⟩
              | exact ⟨1, by decide, by decide⟩
              | exact ⟨2, by decide, by decide⟩
        have hq0 : k q = 0 := by
          by_contra hq
          exact hj0 (hS2 q j0 hqj0 hq)
        exact clause2_caseIIb h2 k (Ne.symm hqp) hp0 hq0
    · push_neg at hS
      refine ⟨sinMode (Fin.cons (0 : ZMod N) k)
          (Fin.cons 0 ((Pi.single 0 (1 : ℝ))
            - (Pi.single 1 (1 : ℝ)))),
        sinMode (Fin.cons (0 : ZMod N) k)
          (Fin.cons 0 ((Pi.single 0 (1 : ℝ))
            - (Pi.single 2 (1 : ℝ)))), ?_, ?_, ?_⟩
      · intro u v huv
        have e0 := congrFun huv (layerLinkOf
          (zeroLayerSite (N := N)) (Fin.succ 0)
          (Fin.succ_ne_zero 0))
        have e1 := congrFun huv (layerLinkOf
          (zeroLayerSite (N := N)) (Fin.succ 1)
          (Fin.succ_ne_zero 1))
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul,
          Pi.zero_apply] at e0 e1
        have w00 : sinMode (Fin.cons (0 : ZMod N) k)
              (Fin.cons 0 ((Pi.single 0 (1 : ℝ))
                - (Pi.single 1 (1 : ℝ))))
              (layerLinkOf (zeroLayerSite (N := N))
                (Fin.succ 0) (Fin.succ_ne_zero 0)) = 1 := by
          rw [sinMode_linkOf, Fin.cons_succ, Pi.sub_apply,
            Pi.single_eq_same, Pi.single_apply,
            if_neg (by decide : (0 : Fin 3) ≠ 1),
            sitePhase_zeroLayerSite, modePhase_succ, zero_add,
            show Real.sin (Real.pi * ((k 0).val : ℝ)
                / (N : ℝ)) = 1 from hsin1 0 (hS 0),
            sub_zero, one_mul]
        have w02 : sinMode (Fin.cons (0 : ZMod N) k)
              (Fin.cons 0 ((Pi.single 0 (1 : ℝ))
                - (Pi.single 2 (1 : ℝ))))
              (layerLinkOf (zeroLayerSite (N := N))
                (Fin.succ 0) (Fin.succ_ne_zero 0)) = 1 := by
          rw [sinMode_linkOf, Fin.cons_succ, Pi.sub_apply,
            Pi.single_eq_same, Pi.single_apply,
            if_neg (by decide : (0 : Fin 3) ≠ 2),
            sitePhase_zeroLayerSite, modePhase_succ, zero_add,
            show Real.sin (Real.pi * ((k 0).val : ℝ)
                / (N : ℝ)) = 1 from hsin1 0 (hS 0),
            sub_zero, one_mul]
        have w10 : sinMode (Fin.cons (0 : ZMod N) k)
              (Fin.cons 0 ((Pi.single 0 (1 : ℝ))
                - (Pi.single 1 (1 : ℝ))))
              (layerLinkOf (zeroLayerSite (N := N))
                (Fin.succ 1) (Fin.succ_ne_zero 1)) = -1 := by
          rw [sinMode_linkOf, Fin.cons_succ, Pi.sub_apply,
            Pi.single_apply,
            if_neg (by decide : (1 : Fin 3) ≠ 0),
            Pi.single_eq_same, sitePhase_zeroLayerSite,
            modePhase_succ, zero_add,
            show Real.sin (Real.pi * ((k 1).val : ℝ)
                / (N : ℝ)) = 1 from hsin1 1 (hS 1)]
          norm_num
        have w12 : sinMode (Fin.cons (0 : ZMod N) k)
              (Fin.cons 0 ((Pi.single 0 (1 : ℝ))
                - (Pi.single 2 (1 : ℝ))))
              (layerLinkOf (zeroLayerSite (N := N))
                (Fin.succ 1) (Fin.succ_ne_zero 1)) = 0 := by
          rw [sinMode_linkOf, Fin.cons_succ, Pi.sub_apply,
            Pi.single_apply,
            if_neg (by decide : (1 : Fin 3) ≠ 0),
            Pi.single_apply,
            if_neg (by decide : (1 : Fin 3) ≠ 2),
            sub_self, zero_mul]
        rw [w00, w02] at e0
        rw [w10, w12] at e1
        constructor <;> linarith [e0, e1]
      · have h := sinMode_eigen h2 (Fin.cons (0 : ZMod N) k)
          (Fin.cons 0 ((Pi.single 0 (1 : ℝ))
            - (Pi.single 1 (1 : ℝ)))) (by rfl)
          (diff_transverse h2 k (hS 0) (hS 1) hsin1)
        rwa [transverse_eig_eq] at h
      · have h := sinMode_eigen h2 (Fin.cons (0 : ZMod N) k)
          (Fin.cons 0 ((Pi.single 0 (1 : ℝ))
            - (Pi.single 2 (1 : ℝ)))) (by rfl)
          (diff_transverse h2 k (hS 0) (hS 2) hsin1)
        rwa [transverse_eig_eq] at h

/-- **Clause (M5).3**: the registered gap value
`4 * sin^2 (π / N)` is an eigenvalue of the pin's
`maxwellOp N`. At general Even `N`; FINITE. -/
theorem clause3 (hN : Even N) :
    Module.End.HasEigenvalue (maxwellOp N)
      (4 * Real.sin (Real.pi / (N : ℝ)) ^ 2) := by
  have h2 : 2 ≤ N := by
    obtain ⟨r, hr⟩ := hN
    have hN0 : N ≠ 0 := NeZero.ne N
    omega
  obtain ⟨k, _, _, _, hk5⟩ := clause5 h2
  rw [← hk5]
  exact (clause1 hN k).1

/-- **MAX-3 partial discharge of the (M5) registration**:
clauses 1, 2, 3 and 5 of the pin's `maxwellM5`, in the
pin's exact clause forms, at general Even `N` — the
Fourier link modes diagonalize the pin's `maxwellOp N`
(the operator assembled by MAX-2), with transverse
eigenvalue `maxwellTransverseEig N k`, longitudinal
eigenvalue `0`, registered multiplicity two at `k ≠ 0`,
and the gap value `4 * sin^2 (π / N)` attained at
`k = (1, 0, 0)`.

Clause 4 of the registration — every eigenvalue is `0`
or at least the gap value — is **not** asserted here: it
is the pre-registered K-MAX-S seam (a global
Poincaré-type inequality for the curl-curl operator, a
separate brick, est. L). No claim on `maxwellM5` as a
whole is made. FINITE statement throughout. -/
theorem maxwellM5_spectrum_part (hN : Even N) :
    (∀ k : Fin 3 → ZMod N,
        Module.End.HasEigenvalue (maxwellOp N)
            (maxwellTransverseEig N k) ∧
        Module.End.HasEigenvalue (maxwellOp N) 0) ∧
    (∀ k : Fin 3 → ZMod N, k ≠ 0 →
        ∃ θ₁ θ₂ : linkAngle N,
          (∀ a b : ℝ, a • θ₁ + b • θ₂ = 0 → a = 0 ∧ b = 0) ∧
          maxwellOp N θ₁
              = (maxwellTransverseEig N k) • θ₁ ∧
          maxwellOp N θ₂
              = (maxwellTransverseEig N k) • θ₂) ∧
    Module.End.HasEigenvalue (maxwellOp N)
        (4 * Real.sin (Real.pi / (N : ℝ)) ^ 2) ∧
    (∃ k : Fin 3 → ZMod N,
        k 0 = 1 ∧ k 1 = 0 ∧ k 2 = 0 ∧
        maxwellTransverseEig N k
          = 4 * Real.sin (Real.pi / (N : ℝ)) ^ 2) := by
  have h2 : 2 ≤ N := by
    obtain ⟨r, hr⟩ := hN
    have hN0 : N ≠ 0 := NeZero.ne N
    omega
  exact ⟨clause1 hN, clause2 hN, clause3 hN, clause5 h2⟩

end Assembly

end ThetLogos
