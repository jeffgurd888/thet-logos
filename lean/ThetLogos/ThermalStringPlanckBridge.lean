/-
# ThermalStringPlanckBridge — a length scale for the finite string family

**Scope: ~/workspace/your_files/thermal-string-planck-bridge-scope-2026-11-20.md
(Zero's thermal-string thread, 2026-11-20 01:47–02:00 EST;
scoped on his word "yes scope the bridge" 2026-11-20 02:00 EST;
build commissioned "build it and run it" 2026-11-20 02:03 EST.
Working label only — naming is Zero's hand.)
NO CLAIM. Dial-ineligible, pre-registered on this face. Dials 0/4.**

WHAT THIS PIN IS: a scale card for the finite string family of
`StringSeatPin` (a chain of `n` links, bend states in `Fin (k+1)`),
plus one weld (Brick 1): the string seat's Gibbs entropy, computed
in-tree for the first time, stated per unit length. It addresses
exactly one item of the 2026-11-17 string comparison's missing
list — the scale/tension analog (the α′ seat). The density of
states and the closed winding string closed earlier (DOS lane;
T7). All dynamics stays FRONTIER, unpriced, untouched here.

THE SCALE IS AN IMPORTED MEASURED INPUT. The length parameter `ℓ`
wherever it appears, and its Planck instantiation `planckLength`
below, are IMPORTED MEASURED INPUTS: data brought in from outside
the corpus (CODATA), face-labeled as such on every face they
touch. No theorem in this pin derives `ℓ`, the Planck length, `ℏ`,
or any constant of nature from corpus quantities, and no theorem
states or uses any property of the Planck value beyond positivity.
K-TSPB-IMPORT is armed: any statement wearing an imported input
as a derivation is void on sight.

NON-INTERFERENCE CLAUSE (the scope's §2, verbatim in substance):
the scale parameter seated here is a unit on a finite
combinatorial family. It is not the CPEC pillar object
(`CpecBridgePost` registers that pillar as a NAMED ABSENCE —
`CpecPillarPlanckAbsent`: no Planck-scale object, no Planck
length, and no measured-scale theorem exists in the corpus), it
does not fill the named absence, it attaches to no wire, and no
statement of this pin may be quoted at the CPEC, gravity, or
spectral-action seats. If it ever is, K-CPEC-PLANCK-RENAME and
K-TSPB-IMPORT fire together.

DISCIPLINE INHERITED: K-PLANCK-SEAT (ThermalDensityPin's unit
card, 2026-11-13 — "no Planck scale as physics") governs here one
grade stricter: this pin seats a length PARAMETER, not a unit
card, and repeats on its face that no theorem states or uses
Planck-scale physics. KernelHeatPlanckBridge owns the Planck
FACTOR (`planckFactor = 1 / (exp (β * E) - 1)`), never the length;
its fence K-KHP-SEAT bars quoting that module at this seat, and
this pin returns the courtesy: nothing here speaks to the factor
seat (K-KHP-UNIT / K-KHP-TIME stand). K-STRING-HAGEDORN stands:
this seat's density of states is polynomial (`levelCount n m =
n.choose m * k^m`, DOS lane); no exponential growth may be quoted
from it. K-STRING-PHYS stands: the finite seat is a toy and models
no physical string's mechanics. K-DENSITY-GRAV stands: no gravity
reading of any length, density, or entropy here.

ATTOSECOND DATA (Register-A data on this face only — no theorems):
Planck time = 5.391e-44 s = 5.391e-26 attoseconds; light crosses
~1.855e25 Planck lengths in one attosecond. The time face was
REJECTED as theorem content at scoping: the QuantumClock tick
spectrum is dimensionless (`β * (E j - E k)`, QC-2), and a period
in seconds would need `ℏ` imported only to restate it. These
numbers ride this header exactly as the calendar's T̄ = 281.47 K
rides its pin: as an input on the face.

WHAT THIS PIN DOES NOT DO: no dynamics (nothing moves, falls,
grows, or evolves); no continuum (no limit of any kind — `ℓ` is a
parameter on a finite family, not a lattice spacing taken to
zero); no Thermal String Theory (that name remains refused as
established, Zero's ruling 2026-11-19 — this is a finite-seat
scale card inside ACMD); no Planck physics (no quantum gravity,
no Planck-scale object); no particle identification and no
magnetic-field coupling (both faces were priced OBSTRUCTIONS at
scoping — the low sector is already owned by the DOS lane's
`levelSet`, and V-9's separation stands against any energy→field
reading at this seat).

BRICKS: Brick 0 (this file as drafted) — the scale seat, a record
pin, 0 strict by design. Brick 1 — the entropy-per-length
ceiling, the pin's only strict content; drafted separately
(brick1-addition.lean in the prep staging) and appended at build
time, statements exactly as scoped. Kills armed for both bricks:
K-TSPB-DUP / K-TSPB-IMPORT / K-TSPB-RENAME (see the scope).

STATUS: prep staging at ~/workspace/bench-scratch/tspb/STAGING.md.
-/

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import ThetLogos.FiniteEntropy
import ThetLogos.StringSeatPin

namespace ThetLogos

namespace ThermalStringPlanckBridge

/-! ## Brick 0 — the scale seat (record pin, 0 strict by design) -/

/-- **The scale seat, frozen as a form**: a scale for the finite
string family is a positive real length. The positivity is the
whole content — a scale is a unit, and a unit is chosen, never
derived. `ℓ` in every statement of this pin is an IMPORTED
MEASURED INPUT (see the header). -/
def ScaleSeat (ℓ : ℝ) : Prop :=
  0 < ℓ

/-- **Physical length of the `n`-link chain at link scale `ℓ`**:
`L n ℓ := n * ℓ`. This is the scope's `L n ℓ`. The definition is a
unit conversion and nothing more: it changes no truth the corpus
owns, and it is on this pin's face that it does not. `ℓ` is an
IMPORTED MEASURED INPUT. -/
def chainLength (n : ℕ) (ℓ : ℝ) : ℝ :=
  (n : ℝ) * ℓ

/-- **The Planck length, as imported data.** The CODATA value
`1.616255e-35` metres, carried as a literal on this definition's
face and cited as external data. This is a data definition, not
a theorem: the corpus does not derive this number, does not
identify it with any corpus quantity, and no statement in this
pin uses any property of the value beyond positivity
(`planckLength_pos` below). It fills no absence: the CPEC
register's Planck pillar stays absent (see the header's
non-interference clause). -/
def planckLength : ℝ :=
  1.616255e-35

/-- The one property of the imported Planck value this pin
registers: positivity. Carried as a definition (a proof term in
the record pin's genre), not a theorem — Brick 0 is 0 strict by
design. -/
def planckLength_pos : 0 < planckLength := by
  norm_num [planckLength]

/-- **The `n`-link chain read at the Planck instantiation**: the
chain's length when the imported scale is the Planck data above.
A data composition — `chainLength` at `planckLength` — stating
nothing about any physical string. -/
def planckChainLength (n : ℕ) : ℝ :=
  chainLength n planckLength

/-
Brick 1 addition — FRAGMENT, not a standalone module.

Insert this section into ThermalStringPlanckBridge.lean immediately
BEFORE the line `end ThermalStringPlanckBridge`, at build time.
Statements are exactly as scoped
(~/workspace/your_files/thermal-string-planck-bridge-scope-2026-11-20.md,
Brick 1). The weld: the string seat's Gibbs entropy is computed
in-tree here for the first time (strike-check evidence in
STAGING.md). Owned content is CITED, never re-proved
(K-TSPB-DUP): the entropy bound and its saturation are
`FiniteEntropy.entropyW_le_log_card` /
`FiniteEntropy.entropyW_eq_log_card_iff` at an abstract seat; the
configuration count is `StringSeatPin.card_config`; the Gibbs
weights are `ModularVariance.gibbsProb` at `StringSeatPin.bendEnergy`,
with `ModularVariance.gibbsProb_pos` / `sum_gibbsProb` for the
probability-weight registration and `StringSeatPin.gibbsProb_zero`
for hot uniformity. The general Gibbs-seat entropy identity
(`IdensityCoincidence.entropyW_gibbsProb_eq`) is a different
statement (an identity, at an abstract seat) and is not used.
-/

/-! ## Brick 1 — the entropy-per-length ceiling (the weld) -/

variable {n k : ℕ}

/-- **The string seat's Gibbs entropy** at slope `β`: the
`FiniteEntropy.entropyW` of the seat's own Gibbs weights,
`ModularVariance.gibbsProb` at `StringSeatPin.bendEnergy`. This
application — entropy AT the string seat — is this pin's weld;
no string module has ever computed it (see STAGING.md). -/
noncomputable def stringGibbsEntropy (β : ℝ) : ℝ :=
  entropyW (ModularVariance.gibbsProb
    (StringSeatPin.bendEnergy : (Fin n → Fin (k + 1)) → ℝ) β)

/-- The seat's Gibbs weights are a probability weight, for every
`β` — the registration `FiniteEntropy`'s bound requires. From
`ModularVariance.gibbsProb_pos` and `ModularVariance.sum_gibbsProb`,
cited. -/
theorem gibbsProb_bendEnergy_isProbWeight (β : ℝ) :
    IsProbWeight (ModularVariance.gibbsProb
      (StringSeatPin.bendEnergy : (Fin n → Fin (k + 1)) → ℝ) β) :=
  ⟨fun c => (ModularVariance.gibbsProb_pos _ β c).le,
    ModularVariance.sum_gibbsProb _ β⟩

/-- **The ceiling, count form** (the proof form of the scoped
statement): the string seat's Gibbs entropy is at most
`n * log (k + 1)` — the log of the configuration count
`(k + 1) ^ n`, by `FiniteEntropy.entropyW_le_log_card` and
`StringSeatPin.card_config`. -/
theorem stringGibbsEntropy_le (β : ℝ) :
    stringGibbsEntropy (n := n) (k := k) β ≤ (n : ℝ) * Real.log ((k : ℝ) + 1) := by
  unfold stringGibbsEntropy
  have h := entropyW_le_log_card
    (gibbsProb_bendEnergy_isProbWeight (n := n) (k := k) β)
  rw [StringSeatPin.card_config] at h
  push_cast at h
  rw [Real.log_pow] at h
  exact h

/-- **The entropy-per-length ceiling, as scoped**: seat entropy
`≤ (L / ℓ) * log (k + 1)`, where `L = chainLength n ℓ` is the
chain's physical length at the imported scale `ℓ`. The
per-length FORM is the statement; the count form above is its
proof (`L / ℓ = n` is the unit conversion doing the work, and it
is on this face that it does nothing else). -/
theorem stringGibbsEntropy_perLength_le {ℓ : ℝ} (hℓ : ScaleSeat ℓ)
    (β : ℝ) :
    stringGibbsEntropy (n := n) (k := k) β
      ≤ (chainLength n ℓ / ℓ) * Real.log ((k : ℝ) + 1) := by
  have hℓ' : 0 < ℓ := hℓ
  have hL : chainLength n ℓ / ℓ = (n : ℝ) := by
    unfold chainLength
    rw [mul_div_assoc, div_self hℓ'.ne', mul_one]
  rw [hL]
  exact stringGibbsEntropy_le β

/-- **The ceiling, divided form**: entropy per unit length is at
most `log (k + 1) / ℓ` — the per-length density of the ceiling,
for a nonempty chain at a positive scale. -/
theorem stringGibbsEntropy_div_length_le {ℓ : ℝ} (hℓ : ScaleSeat ℓ)
    (hn : 0 < n) (β : ℝ) :
    stringGibbsEntropy (n := n) (k := k) β / chainLength n ℓ
      ≤ Real.log ((k : ℝ) + 1) / ℓ := by
  have hℓ' : 0 < ℓ := hℓ
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hL : 0 < chainLength n ℓ := by
    unfold chainLength
    exact mul_pos hn' hℓ'
  rw [div_le_div_iff₀ hL hℓ']
  calc stringGibbsEntropy β * ℓ
      ≤ ((n : ℝ) * Real.log ((k : ℝ) + 1)) * ℓ :=
        mul_le_mul_of_nonneg_right (stringGibbsEntropy_le β) hℓ'.le
    _ = Real.log ((k : ℝ) + 1) * chainLength n ℓ := by
        unfold chainLength
        ring

/-- **Saturation at `β = 0`**: at zero slope the seat's Gibbs
state is uniform (`StringSeatPin.gibbsProb_zero`, hot uniformity),
so its entropy attains the ceiling exactly — `n * log (k + 1)`,
by the saturation direction of
`FiniteEntropy.entropyW_eq_log_card_iff`. -/
theorem stringGibbsEntropy_zero :
    stringGibbsEntropy (n := n) (k := k) 0 = (n : ℝ) * Real.log ((k : ℝ) + 1) := by
  have hunif : ∀ c : Fin n → Fin (k + 1),
      ModularVariance.gibbsProb
          (StringSeatPin.bendEnergy : (Fin n → Fin (k + 1)) → ℝ) 0 c
        = 1 / (Fintype.card (Fin n → Fin (k + 1)) : ℝ) := by
    intro c
    rw [one_div]
    exact StringSeatPin.gibbsProb_zero c
  have h := (entropyW_eq_log_card_iff
    (gibbsProb_bendEnergy_isProbWeight 0)).mpr hunif
  unfold stringGibbsEntropy
  rw [h, StringSeatPin.card_config]
  push_cast
  rw [Real.log_pow]

/-- **Saturation, per unit length**: at `β = 0` the entropy per
unit length is exactly `log (k + 1) / ℓ`. -/
theorem stringGibbsEntropy_perLength_zero {ℓ : ℝ} (hℓ : ScaleSeat ℓ)
    (hn : 0 < n) :
    stringGibbsEntropy (n := n) (k := k) 0 / chainLength n ℓ
      = Real.log ((k : ℝ) + 1) / ℓ := by
  have hℓ' : ℓ ≠ 0 := (show (0:ℝ) < ℓ from hℓ).ne'
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [stringGibbsEntropy_zero]
  unfold chainLength
  field_simp

end ThermalStringPlanckBridge

end ThetLogos
