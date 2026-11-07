import Mathlib.Tactic
import ThetLogos.ThermoelectricSeat

namespace ThetLogos

/-!
# ThetLogos.TolmanExhibitPin — PIN (interface; frozen names; 0 strict)

**Commission:** Jeff, verbatim: **"fire that exactly as stated"**
(2026-11-07 13:01 EST), adopting the parent's flag as stated — *a finite
equilibrium exhibit pairing the thermoelectric seat's temperature with
a site-weight in a Tolman-shaped relation — with the fence written on
it in advance that a weight is not a metric, so it would be an analog
or nothing* — and **"Fire the Tolman exhibit"** (2026-11-07 13:09 EST)
on the priced menu of the scoping
(`~/workspace/your_files/tolman-exhibit-scoping-2026-11-07.md`).
**Price:** S–M — the content module `TolmanExhibit` at **14–19 strict**,
pre-registered **DIAL-INELIGIBLE**.
**Status: PIN ONLY (this file). NO CLAIM. Dials 0/4. Dial 2 = 0.**

## What this seat is

The finite Tolman derivation in its entropy-maximization form — the
form Tolman's own argument takes (scoping §3): over a finite seat `V`,
occupations `x : V → ℝ` interior (`0 < x i < 1`) carry the binary site
entropy `occEnt`; the site factor `a : V → ℝ` (bare positive site
weight) enters ONLY through the conserved quantity `occWeightedSum`
(the `a`-weighted occupation sum). Equilibrium is *defined* as entropy
maximality at fixed conserved quantity (`IsTolmanEquilibrium`), and
the exhibit's theorems derive its first-order characterization: the
slope condition `occSlope (x₀ i) = λ · a i`, whose reciprocal-slope
reading `localTemp` gives the product `localTemp x₀ i · a i = λ⁻¹` —
local temperature factor × site factor = one global constant. The
product is the *output* of the characterization, never an input.

## The literal reading is REFUTED — and the fence is part of this pin

The commissioned item's literal reading — pair the TE seat's own
thermal field `θ` with a site-weight at the TE seat's own equilibrium —
is **false**, proved false by the corpus's landed
`teDirichlet_eq_zero_iff`: TE equilibria are exactly the fields
constant on the weight support, so for any nonconstant site factor the
product `θ · a` varies at every nonzero TE equilibrium (scoping §2,
two-site witness). Form (6) below freezes that negative as a corpus
fact beside the exhibit, so no later brick attaches the Tolman shape
to the TE seat's equilibrium.

## The weight is not a metric (K-TOL-PROXY fence, on the face)

The site factor `a` is a bare positive site weight inside a conserved
sum. It is not a metric, not a metric component, not a redshift
factor, and no statement in this package names or treats it as one:
the tokens metric / g_tt / √ / redshift occur in no statement,
definition, or theorem name here. The Tolman *shape* is an analogy of
form, stated as an analogy, on the exhibit's face — the house exhibit
discipline. The corpus has no metric and no gravity object; Dial 2 = 0
is part of this package's statement, not a footnote to it.

**Form refinement, logged on the face (not a silent deviation):** the
characterization form (1) carries the interior conjunct explicitly on
its right-hand side. Reason: `occSlope` at a boundary occupation takes
convention values (`Real.log 0 = 0`), under which the bare slope
condition can hold at non-interior configurations (e.g. `x₀ ≡ 0` with
`λ = 0`), so the bare-slope iff is false as stated; the scoping's
characterization (§3) is stated for interior configurations, and the
frozen form says exactly that.

## The definitions and the six frozen statement forms

This pin carries the exhibit-local definitions and states the six
forms as `Prop`s. Names are FROZEN at this commit; the content module
proves theorems whose statements are these forms verbatim.

1. **Characterization** — `TolmanCharForm`: equilibrium ⟺ interior ∧
   ∃ λ, the slope condition at every site.
2. **Product** — `TolmanProductForm`: at an equilibrium with slope
   witness `λ ≠ 0`, `localTemp x₀ i · a i = λ⁻¹` at every site.
3. **The λ = 0 fence** — `TolmanLambdaZeroForm`: slope identically
   zero at an interior configuration forces `x₀ ≡ 1/2` (the
   infinite-temperature configuration, named, not hidden); the
   product form is fenced off there by its `λ ≠ 0` hypothesis.
4. **The λ regimes** — `TolmanRegimeForm`: `λ > 0` puts every
   equilibrium occupation below `1/2` with positive local temperature;
   `λ < 0` puts every one past `1/2` with signed (negative) local
   temperature.
5. **Non-vacuity witnesses** — `TolmanWitnessForm` on `Fin 2`,
   `a = (1, 2)`: `x = (1/4, 1/4)` is NOT an equilibrium; `x = (1/4,
   1/10)` IS, with both products equal to `(log 3)⁻¹`.
6. **The TE fence** — `TolmanTEFenceForm`: on `Fin 2` with unit
   conductance, `θ ≡ 1` is a TE equilibrium (`teCharge = 0`) whose
   `θ · a` products for `a = (1, 2)` are the distinct values `1, 2`
   — the §2 refutation, carried as a proved fence theorem.

## Kill register (armed from this pin onward; scoping §5)

- **K-TOL-PROXY** — any statement naming or treating a site weight as
  √g_tt / a metric component kills the exhibit. **ARMED, NOT FIRED:**
  no statement in the priced brick does so; the site factor is a bare
  positive weight in every component.
- **K-TOL-FIAT** — the equilibrium relation must be derived; a
  postulated relation kills it. **ARMED, NOT FIRED:** equilibrium is
  defined as entropy maximization and the product is its proved
  characterization (forms (1)–(2)).
- **K-TOL-VAC** — a relation true of every configuration is a
  tautology in costume. **ARMED, NOT FIRED:** the characterization is
  an iff with named violating configurations certified non-equilibria
  (form (5)).
- **K-TOL-DUP** — the exhibit must not merely restate landed TE-seat
  or thermal-clock theorems. **ASSESSED AT SCOPING, DOES NOT FIRE:**
  the tilted, site-weighted characterization and the product form
  have no landed counterpart; form (6) is a NEW negative statement
  about the TE seat. Technique reuse of `FiniteEntropy`'s deficit
  route is citation-grade method, named as such.
-/

variable {V : Type*} [Fintype V]

/-- **Binary site entropy** (exhibit-local definition): the entropy of
one two-level site at occupation `t`,
`s(t) = −t·log t − (1−t)·log(1−t)`. On `(0, 1)` its slope is
`occSlope`. Tier T1 (definition). -/
noncomputable def occEnt (t : ℝ) : ℝ :=
  -t * Real.log t - (1 - t) * Real.log (1 - t)

/-- **The slope of the site entropy** (exhibit-local definition):
`s′(t) = log((1−t)/t)`, written `log (1−t) − log t`. Its reciprocal at
an equilibrium occupation is the local temperature factor
(`localTemp`). Tier T1 (definition). -/
noncomputable def occSlope (t : ℝ) : ℝ :=
  Real.log (1 - t) - Real.log t

/-- **Total occupation entropy** of a configuration:
`S(x) = ∑ i, occEnt (x i)`. Tier T1 (definition). -/
noncomputable def occEntSum (x : V → ℝ) : ℝ :=
  ∑ i, occEnt (x i)

/-- **The conserved quantity** (exhibit-local definition): the
site-factor-weighted occupation sum `A(x) = ∑ i, a i · x i`. The site
factor `a` enters the exhibit ONLY through this sum — a bare positive
site weight inside a conserved quantity. Not a metric, not a metric
component, not a redshift factor (K-TOL-PROXY's fence is part of this
definition's reading). Tier T1 (definition). -/
def occWeightedSum (a x : V → ℝ) : ℝ :=
  ∑ i, a i * x i

/-- **Equilibrium** (a definition, not a postulate): `x₀` is an
equilibrium for the site factor `a` iff it is interior (`0 < x₀ i < 1`
at every site) and maximizes the total occupation entropy among
interior configurations with the same conserved quantity. The product
relation of the exhibit is nowhere in this definition — it is the
output of the characterization (K-TOL-FIAT's fence). Tier T1
(definition). -/
def IsTolmanEquilibrium (a x₀ : V → ℝ) : Prop :=
  (∀ i, 0 < x₀ i ∧ x₀ i < 1) ∧
    ∀ x : V → ℝ, (∀ i, 0 < x i ∧ x i < 1) →
      occWeightedSum a x = occWeightedSum a x₀ →
      occEntSum x ≤ occEntSum x₀

/-- **Local temperature factor** at a configuration (exhibit-local
definition): the reciprocal slope, `T i = (occSlope (x₀ i))⁻¹`.
Meaningful where the slope is nonzero; at slope zero (the
half-occupation configuration of form (3)) the reciprocal is `0` by
the `⁻¹` convention and the product form (2) is fenced off by its
`λ ≠ 0` hypothesis. Tier T1 (definition). -/
noncomputable def localTemp (x₀ : V → ℝ) (i : V) : ℝ :=
  (occSlope (x₀ i))⁻¹

/-- **Frozen form (1) — the characterization.** For a positive site
factor, `x₀` is an equilibrium iff it is interior and some global `λ`
gives the slope condition `occSlope (x₀ i) = λ · a i` at every site.
The interior conjunct stands on the right by the face note in the
header (slope at the boundary is convention-valued). Tier T1
(statement pin). -/
def TolmanCharForm : Prop :=
  ∀ (a x₀ : V → ℝ), (∀ i, 0 < a i) →
    (IsTolmanEquilibrium a x₀ ↔
      (∀ i, 0 < x₀ i ∧ x₀ i < 1) ∧
        ∃ lam : ℝ, ∀ i, occSlope (x₀ i) = lam * a i)

/-- **Frozen form (2) — the product.** At an equilibrium whose slope
condition is witnessed by `λ ≠ 0`, the local temperature factor times
the site factor is the one global constant `λ⁻¹`, at every site:
`localTemp x₀ i · a i = λ⁻¹`. This is the Tolman shape — as the
characterization's output, with the weight a bare site weight.
Tier T1 (statement pin). -/
def TolmanProductForm : Prop :=
  ∀ (a x₀ : V → ℝ) (lam : ℝ), (∀ i, 0 < a i) →
    IsTolmanEquilibrium a x₀ →
    (∀ i, occSlope (x₀ i) = lam * a i) → lam ≠ 0 →
    ∀ i, localTemp x₀ i * a i = lam⁻¹

/-- **Frozen form (3) — the λ = 0 fence.** If the slope vanishes at
every site of an interior configuration, the configuration is
`x₀ ≡ 1/2`: the infinite-temperature configuration, at which the
product form (2) is fenced off by its `λ ≠ 0` hypothesis. Tier T1
(statement pin). -/
def TolmanLambdaZeroForm : Prop :=
  ∀ (a x₀ : V → ℝ), (∀ i, 0 < x₀ i ∧ x₀ i < 1) →
    (∀ i, occSlope (x₀ i) = 0) → ∀ i, x₀ i = 1 / 2

/-- **Frozen form (4) — the λ regimes.** With a positive site factor
and an interior configuration carrying the slope condition: a witness
`λ > 0` puts every occupation below `1/2` with positive local
temperature; a witness `λ < 0` puts every occupation past `1/2` with
signed (negative) local temperature — the population-inversion side
of the slope, stated as the mathematics' own case split. Tier T1
(statement pin). -/
def TolmanRegimeForm : Prop :=
  (∀ (a x₀ : V → ℝ) (lam : ℝ), (∀ i, 0 < a i) →
    (∀ i, 0 < x₀ i ∧ x₀ i < 1) →
    (∀ i, occSlope (x₀ i) = lam * a i) → 0 < lam →
    ∀ i, x₀ i < 1 / 2 ∧ 0 < localTemp x₀ i) ∧
  (∀ (a x₀ : V → ℝ) (lam : ℝ), (∀ i, 0 < a i) →
    (∀ i, 0 < x₀ i ∧ x₀ i < 1) →
    (∀ i, occSlope (x₀ i) = lam * a i) → lam < 0 →
    ∀ i, 1 / 2 < x₀ i ∧ localTemp x₀ i < 0)

/-- **Frozen form (5) — non-vacuity witnesses.** On `Fin 2` with site
factor `a = (1, 2)`: the configuration `x = (1/4, 1/4)` is NOT an
equilibrium (its slope ratios `log 3` and `(log 3)/2` differ, so the
characterization certifies it non-maximal); the configuration
`x = (1/4, 1/10)` IS an equilibrium, and its two products agree at
the global constant `(log 3)⁻¹`. The characterization is an iff with
named configurations on both sides (K-TOL-VAC's fence). Tier T1
(statement pin). -/
def TolmanWitnessForm : Prop :=
  (¬ IsTolmanEquilibrium (![1, 2] : Fin 2 → ℝ) (![1 / 4, 1 / 4] : Fin 2 → ℝ)) ∧
  IsTolmanEquilibrium (![1, 2] : Fin 2 → ℝ) (![1 / 4, 1 / 10] : Fin 2 → ℝ) ∧
  (∀ i : Fin 2, localTemp (![1 / 4, 1 / 10] : Fin 2 → ℝ) i
      * (![1, 2] : Fin 2 → ℝ) i = (Real.log 3)⁻¹)

/-- **Frozen form (6) — the TE fence (the scoping §2 refutation as a
corpus fact).** On `Fin 2` with unit conductance
(`w i j = if i = j then 0 else 1`), the constant field `θ ≡ 1` is a
TE equilibrium — its separated charge vanishes identically — while
its products against the site factor `a = (1, 2)` are the distinct
values `1` and `2`. The Tolman shape does NOT hold at the TE seat's
own equilibrium; this fence stands beside the exhibit permanently.
Tier T1 (statement pin). -/
def TolmanTEFenceForm : Prop :=
  teCharge (fun i j : Fin 2 => if i = j then 0 else 1) (fun _ => 1) = 0 ∧
    (fun _ : Fin 2 => (1 : ℝ)) 0 * (![1, 2] : Fin 2 → ℝ) 0 ≠
      (fun _ : Fin 2 => (1 : ℝ)) 1 * (![1, 2] : Fin 2 → ℝ) 1

end ThetLogos
