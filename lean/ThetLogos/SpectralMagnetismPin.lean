import Mathlib.Tactic
import ThetLogos.TolmanExhibitPin

namespace ThetLogos

/-!
# ThetLogos.SpectralMagnetismPin — PIN (interface; frozen names; 0 strict)

**Commission:** Zero's pushback on the spectral-drag NO-GO, verbatim
(2026-11-08 00:19 EST): *"I don't think the right tests have been
designed yet, Spectral Magnetism."* — scoped on his tap ("Scope
Spectral Magnetism", 2026-11-08 00:20 EST) in
`~/workspace/your_files/spectral-magnetism-scope-2026-11-08.md`, and
fired by his tap **"Build the SM-1 exhibit"** (2026-11-08 00:31 EST)
on that scoping's priced menu (§3.3). The name "Spectral Magnetism"
is Zero's; every Lean-side name in this package is a working label
only.
**Price:** SM-0 (this pin) band **S** (0 strict); the content module
`SpectralMagnetism` at band **S–M, 10–16 strict**, pre-registered
**DIAL-INELIGIBLE**.
**Status: PIN ONLY (this file). NO CLAIM. Dials 0/4. Dial 2 = 0.**

## What this seat is

Shape **(a2)** of the scoping, and only shape (a2): *prepared-state*
functionals at fixed composition and fixed total energy-momentum.
The scoping's other shapes are not in this brick: (a1) is DEAD ON
EXISTING DATA (K-SM-SQUEEZE, fired by the scoping itself); (b) is
NOT STATEABLE in the corpus and its definition-only residue was
refused pricing; (c)'s exhibit clause is SM-2 — gated, NOT enrolled,
not part of this build.

The corpus's first **body datum**: a finite level set with energies
(`SpectralDatum`), whose **states** are occupation profiles over the
levels. The **spectral-weight functional** `spectralWeight` is the
Tolman seat's own total occupation entropy (`occEntSum`) read as a
functional on those states; the datum's energies enter through the
conserved total (`spectralTotal` = the Tolman seat's
`occWeightedSum`). The exhibit's theorems are theorems *about the
functional* — where it varies at fixed totals, where it is
stationary, and what it reduces to on equilibrium states. Nothing
here is a statement about nature.

## The fences (on the face)

- **Not a response law.** As a physical response law, shape (a2) is
  NOT STATEABLE (scoping §3.4): there is no derived response and no
  dimensionful coupling, and criterion D2-4 lists internal state
  verbatim among its body parameters, so a state variable fares
  exactly as composition did. This exhibit does not state the law;
  it defines a functional and proves finite theorems about it.
- **K-SM-PROXY fence.** No statement in this package names or treats
  `spectralWeight` as a gravitational mass, a weight in the falling
  sense, or a coupling; no descent rule consumes it; the tokens
  gravity / mass / coupling occur in no statement, definition, or
  theorem name here. The corpus has no gravity object; Dial 2 = 0
  is part of this package's statement, not a footnote to it.
- **Pre-registered DIAL-INELIGIBLE** (scoping §3.3, Tolman/flow-seat
  precedent): finite theorems about a declared functional are
  Register-A mathematics and move no dial.

## Form refinements, logged on the face (not silent deviations)

- Form (2) renders the scoping's "stationary under conserved
  transfers" in the Tolman route's finite form: maximality of the
  functional at fixed conserved total — the landed seat's own
  equilibrium notion (`IsTolmanEquilibrium`). The characterization's
  two directions are the landed `tolman_characterization`'s
  (Fermat forward, summed tangent bound converse), *cited and
  transported, never postulated here* — that citation is
  K-SM-FIAT's fence.
- Form (3) carries the interior hypothesis explicitly. Reason (the
  Tolman pin's own refinement pattern): `occSlope`/`occEnt` take
  convention values at boundary occupations (`Real.log 0 = 0`),
  under which the bare slope condition holds at non-interior
  configurations (e.g. `x₀ ≡ 0` with `λ = 0`) where the closed form
  is false; equilibrium states are interior by definition, and the
  frozen form says exactly that.

## The definitions and the three frozen statement forms

This pin carries the exhibit's definitions and states the three
forms as `Prop`s. Names are FROZEN at this commit; the content
module proves theorems whose statements are these forms verbatim.

1. **Non-vacuity, both directions** — `SpectralNonvacuityForm`:
   on the `Fin 2` datum with energies `(1, 2)`, the states
   `(1/20, 1/5)` and `(1/4, 1/10)` have equal conserved totals
   (`9/20`) and provably *different* functional values (the
   second is the landed Tolman equilibrium; the first is
   strictly below it); and on the `Fin 2` datum with energies
   `(1, 1)`, the states `(1/4, 1/2)` and `(1/2, 1/4)` are
   different distributions with equal totals and *equal*
   functional values. (K-SM-VAC's tripwire: if the first pair's
   values collapse, the exhibit is vacuous and the kill fires.)
2. **Characterization (iff)** — `SpectralCharForm`: a state is
   maximal for the functional at fixed conserved total iff it is
   interior and some global `λ` gives the slope condition
   `occSlope (x₀ i) = λ · energy i` at every level — the
   slope-equalized profiles, exactly the Tolman equilibrium
   locus of the datum.
3. **The equilibrium fence** — `SpectralEquilibriumForm`: on an
   interior slope-equalized state with witness `λ`, the
   functional collapses to the closed form
   `∑ i, log (1 + exp (λ · energy i)) − λ · ((∑ i, energy i) −
   total)` — a function of the state's totals (and the datum)
   alone. The exhibit thereby *proves*, inside its finite
   model, the finite mirror of the scoping's §2.2 verdict:
   state-dependence of the functional lives entirely off
   equilibrium; on every equilibrium state the functional is
   a function of totals.

## Kill register (scoping §4; armed from this pin onward)

- **K-SM-VAC** — fires if form (1)'s first-pair witnesses
  collapse (equal totals force equal values). **ARMED.**
- **K-SM-FIAT** — fires if the characterization (form 2) or the
  equilibrium fence (form 3) is postulated rather than derived.
  **ARMED.**
- **K-SM-PROXY** — fires if the functional, or any defined
  source, is ever named or presented as gravitational weight, a
  coupling, a field equation, or Dial evidence. **ARMED.**
- **K-SM-DIAL** — standing: fires on any summary presenting
  this exhibit, the corner's openness, or the right test's
  design as evidence *for* Spectral Magnetism as physics.
  **ARMED.**
- **K-SM-SQUEEZE** — **FIRED at scoping** on shape (a1); recorded
  here so no revival of this line in ground-state dress is
  mistaken for this exhibit. Not this brick's kill to fire.
- **K-SM-CLOSED** — registered at scoping against the dismissive
  meta-claim that the existing record closes the state corner.
  Not this brick's kill to fire.
-/

variable {ι : Type*} [Fintype ι]

/-- **Body datum** (exhibit-local definition): a finite level set
`ι` with a positive energy at each level. The corpus's first
(body, state) datum: the body is its levels and energies; its
states are occupation profiles (`IsSpectralState`). Tier T1
(definition). -/
structure SpectralDatum (ι : Type*) [Fintype ι] where
  /-- The energy of each level. -/
  energy : ι → ℝ
  /-- Every level energy is positive. -/
  energy_pos : ∀ i, 0 < energy i

/-- **State of a body datum** (exhibit-local definition): an
interior occupation profile over the datum's levels — the
spectral state, as a distribution over the level set. Tier T1
(definition). -/
def IsSpectralState (D : SpectralDatum ι) (x : ι → ℝ) : Prop :=
  ∀ i, 0 < x i ∧ x i < 1

/-- **Conserved total** of a state (exhibit-local definition):
the energy-weighted occupation sum `∑ i, energy i · x i` — the
Tolman seat's conserved quantity (`occWeightedSum`) at the
datum's energies. The exhibit's fixed-total-energy condition is
equality of this quantity. Tier T1 (definition). -/
def spectralTotal (D : SpectralDatum ι) (x : ι → ℝ) : ℝ :=
  occWeightedSum D.energy x

/-- **The spectral-weight functional** `SW` (working label;
exhibit-local definition, Register A — a declaration, not a
claim): the Tolman seat's total occupation entropy (`occEntSum`)
of the state's profile. No statement in this package names or
treats it as a gravitational mass, a weight in the falling
sense, or a coupling (K-SM-PROXY's fence is part of this
definition's reading). Tier T1 (definition). -/
noncomputable def spectralWeight (x : ι → ℝ) : ℝ :=
  occEntSum x

/-- **Maximality at fixed total** (exhibit-local definition):
a state is maximal for the functional at its conserved total
iff it is the Tolman equilibrium of the datum — entropy
maximality at fixed conserved quantity, the landed seat's own
notion at the datum's energies. Tier T1 (definition). -/
def SpectralMaximal (D : SpectralDatum ι) (x₀ : ι → ℝ) : Prop :=
  IsTolmanEquilibrium D.energy x₀

/-- **The `(1, 2)` witness datum** on `Fin 2` (exhibit data):
levels with energies `1` and `2`. Tier T1 (definition). -/
def spectralDatum12 : SpectralDatum (Fin 2) where
  energy := ![1, 2]
  energy_pos := by
    rw [Fin.forall_fin_two]
    constructor <;>
      simp [Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons] <;> norm_num

/-- **The `(1, 1)` witness datum** on `Fin 2` (exhibit data):
levels with equal energies `1` and `1`. Tier T1
(definition). -/
def spectralDatum11 : SpectralDatum (Fin 2) where
  energy := ![1, 1]
  energy_pos := by
    rw [Fin.forall_fin_two]
    constructor <;>
      simp [Matrix.cons_val_zero, Matrix.cons_val_one]

/-- **Frozen form (1) — non-vacuity, both directions.** On the
`(1, 2)` datum, the states `(1/20, 1/5)` and `(1/4, 1/10)` have
equal conserved totals and strictly different functional values
(the second, the landed Tolman equilibrium, is strictly above
the first); on the `(1, 1)` datum, the states `(1/4, 1/2)` and
`(1/2, 1/4)` are different distributions with equal conserved
totals and equal functional values. The functional genuinely
varies with the distribution at fixed totals, and is
genuinely insensitive to some redistributions (K-SM-VAC's
fence). Tier T1 (statement pin). -/
def SpectralNonvacuityForm : Prop :=
  (spectralTotal spectralDatum12 (![1 / 20, 1 / 5] : Fin 2 → ℝ)
      = spectralTotal spectralDatum12 (![1 / 4, 1 / 10] : Fin 2 → ℝ) ∧
    spectralWeight (![1 / 20, 1 / 5] : Fin 2 → ℝ)
      < spectralWeight (![1 / 4, 1 / 10] : Fin 2 → ℝ)) ∧
  ((![1 / 4, 1 / 2] : Fin 2 → ℝ) ≠ ![1 / 2, 1 / 4] ∧
    spectralTotal spectralDatum11 (![1 / 4, 1 / 2] : Fin 2 → ℝ)
      = spectralTotal spectralDatum11 (![1 / 2, 1 / 4] : Fin 2 → ℝ) ∧
    spectralWeight (![1 / 4, 1 / 2] : Fin 2 → ℝ)
      = spectralWeight (![1 / 2, 1 / 4] : Fin 2 → ℝ))

/-- **Frozen form (2) — the characterization.** A state of a
body datum is maximal for the functional at fixed conserved
total iff it is interior and some global `λ` gives the slope
condition `occSlope (x₀ i) = λ · energy i` at every level —
the slope-equalized profiles. The Tolman route: Fermat
forward, summed tangent bound converse, as landed in
`tolman_characterization` and transported here, never
postulated (K-SM-FIAT's fence). Tier T1 (statement pin). -/
def SpectralCharForm : Prop :=
  ∀ (D : SpectralDatum ι) (x₀ : ι → ℝ),
    (SpectralMaximal D x₀ ↔
      (∀ i, 0 < x₀ i ∧ x₀ i < 1) ∧
        ∃ lam : ℝ, ∀ i, occSlope (x₀ i) = lam * D.energy i)

/-- **Frozen form (3) — the equilibrium fence.** On an interior
slope-equalized state with witness `λ`, the functional
collapses to a closed form in the state's totals (and the
datum) alone:
`SW = ∑ i, log (1 + exp (λ · energy i)) − λ · ((∑ i, energy i)
− total)`. State-dependence of the functional lives entirely
off equilibrium — the finite mirror of the scoping's §2.2
verdict, proved inside the model. The interior hypothesis
stands explicitly by the face note in the header (boundary
occupations are convention-valued). Tier T1 (statement
pin). -/
def SpectralEquilibriumForm : Prop :=
  ∀ (D : SpectralDatum ι) (x₀ : ι → ℝ) (lam : ℝ),
    (∀ i, 0 < x₀ i ∧ x₀ i < 1) →
    (∀ i, occSlope (x₀ i) = lam * D.energy i) →
    spectralWeight x₀
      = (∑ i, Real.log (1 + Real.exp (lam * D.energy i)))
        - lam * ((∑ i, D.energy i) - spectralTotal D x₀)

end ThetLogos
