/-
# RiemannThetaAdoptionPin — RH-2 brick 3: the theta adoption
fence (fence / registration)

**Scope: ~/workspace/your_files/rh2-statement-fidelity-bridges-scope-2026-11-22.md
(§3, §6). Ladder of record: Ladder 2, RH-2, in
~/workspace/your_files/millennium-ladders-ym-and-riemann-2026-11-21.md.
Obstruction map: ~/workspace/your_files/rh1-obstruction-map-2026-11-22.md.
Fired 2026-11-24 on the parent's word, L2 lane, per brick cadence
(RH2-2 banked the same morning at `31091ae`). T5. NO CLAIM.
Parts of the Riemann Hypothesis closed by this brick: 0. The
RH dial stays 0.**

WHAT THIS BRICK IS. RH-2 is the statement-fidelity rung: for
every object any later rung names, a proved lemma that the
built object IS the standard object. Theta is the seat where
the audited external failure happened: the Comparator's
quasi-Riemann formalization introduced a custom in-file theta
definition for a Hecke-side construction, with no proved lemma
that the custom object is the series everyone means — and
everything above that joint was ungradable. This brick is the
fence that failure mode runs into here. The scope's audit
found that NO bridge is needed for Mathlib's θ itself: the
pin's `jacobiTheta` is defined as exactly the standard sum,
and Mathlib's own functional equations already route through
it. So this brick does the three things the scope prices:
it ADOPTS `jacobiTheta` by name (rule R1), REGISTERS the
classical-form bridge of record (`jacobiTheta_eq_tsum_nat`),
and STATES the R2 rule for any future form-theta on this
face, where no later lane can miss it. A registration proves
that our words and the world's words name the same object;
it proves nothing about the object. Nothing in this module
states, assumes, or approaches any zero of any function.

THE FIRE-TIME AUDIT (the scope's method, checked first).
Read in the pin (Mathlib v4.35.0-rc3) on 2026-11-24, in
Mathlib/NumberTheory/ModularForms/JacobiTheta/OneVariable.lean:

- `jacobiTheta` (line 29): `∑' n : ℤ, cexp (π * I * (n:ℂ)^2 * τ)`
  — exactly the standard object of scope §3(i),
  θ(τ) = Σ_{n∈ℤ} e^(πi n² τ). The series everyone means and
  the object in-pin coincide by construction.
- `jacobiTheta_eq_jacobiTheta₂` (line 31):
  `jacobiTheta τ = jacobiTheta₂ 0 τ` — the one-variable object
  IS the two-variable object at `z = 0`.
- `jacobiTheta_S_smul` (line 43): for `τ : ℍ`,
  `jacobiTheta (S • τ) = (-I * τ)^(1/2) * jacobiTheta τ` —
  the S-transformation of §3(i) in Möbius form
  (`S • τ = -1/τ`), carried by the pin itself; beside it
  `jacobiTheta_two_add` (line 34), the T²-translation.
- `jacobiTheta_eq_tsum_nat` (line 84): for `0 < im τ`,
  `jacobiTheta τ = 1 + 2 * ∑' n : ℕ, cexp (π * I * ((n:ℂ)+1)^2 * τ)`
  — the classical one-sided form 1 + 2·Σ_{n≥1} e^(πi n² τ).
- Load-bearing upstream, as the scope recorded: the
  two-variable `jacobiTheta₂` is what Mathlib's Hurwitz-zeta
  functional equations are proved through
  (Mathlib/NumberTheory/LSeries/HurwitzZetaEven.lean, passim)
  — Mathlib's ζ-side functional-equation work already routes
  through Mathlib's θ, never through a house substitute.

Every cited statement matches the scope's standard-object
claim verbatim — hypotheses included, nothing weakened. If
any had differed, this brick would have stopped and reported
instead of drafting; none did.

THE KILL CRITERION, ANSWERED AT DRAFTING. The scope
pre-registered this brick's kill: any draft containing a
house `def` of a theta series dies on sight — that is the
Comparator failure mode itself. This module contains NO
`def` at all (rule R1, structural, as in RH2-1). The only
theta objects named anywhere in it are Mathlib's own:
`jacobiTheta` and `jacobiTheta₂`. The kill criterion did
NOT trigger, because the draft never attempted the thing
it names.

THE RULES, ON THE FACE (scope R1–R3, binding on every RH-2
brick):
- **R1 — adopt, never redefine.** Where Mathlib carries the
  standard object, the house uses Mathlib's. For theta the
  adoption is this module: the board's θ is `jacobiTheta`,
  by name, and there is no house θ.
- **R2 — agreement before use.** No later rung may consume
  an object whose agreement lemma is not already banked.
  For Mathlib's θ the agreement is definitional (the audit
  above) and is registered by the declarations below. THE
  FORM-THETA RULE, stated here as this brick's standing
  fence: if a later rung introduces a house-side theta
  series (e.g. a theta series of a quadratic form,
  Σ q^(Q(n))), its termwise identification with
  `jacobiTheta`/`jacobiTheta₂` — or with the one-sided form
  via the registered bridge `jacobiTheta_eq_tsum_nat` —
  must be BANKED BEFORE any functional equation is quoted
  through it. Until that identification is banked, the
  house object is unusable, full stop. That is the exact
  joint where the Comparator's work failed.
- **R3 — junk values are part of the object.** `jacobiTheta`
  is a `tsum`: off the upper half-plane the series diverges
  and the sum takes the `tsum` junk value. The classical-form
  bridge is therefore registered exactly under its
  hypothesis `0 < im τ`, where both sides live; no agreement
  is claimed off it, and the S-transformation is registered
  on `ℍ`, where it is stated. A bridge that ignored the
  convention would be a bridge to a different function.

THE COLLISION FENCE (scope §3, corpus side). The corpus
already carries a name that must never be confused with
this seat: `ThetLogos.SolidBodyPeriodTheta` (rigid-body
program, stage N3) is **Landau Θ notation** — the two-sided
Θ(|log τ|) growth rate of a quadrature period, whose τ is a
real energy-gap parameter. It is NOT a theta function, it
defines no theta series, and nothing in it may be cited as
theta-function content. The collision is registered here so
no future lane mistakes the growth-rate Θ for Jacobi's θ.

THE HECKE FENCE (scope §4, restated so no reader of this
module can miss it): the Hecke seat on this board is EMPTY
and stays empty. The Comparator's custom theta was built
FOR a Hecke-side construction; fencing theta and fencing
Hecke are the same discipline seen from two sides. No Hecke
L-function exists in the pin; none is defined, named, or
touched here.

THE THREE DECLARATIONS (scope §6 price: ~3 decls, ~1–2
strict; registration bricks are thin by nature and are
counted thin):
1. `jacobiTheta_eq_jacobiTheta₂` — the adoption of record:
   the board's θ is the two-variable object at `z = 0`, the
   very object the pin's Hurwitz-zeta functional equations
   route through.
2. `jacobiTheta_eq_tsum_nat` — the classical-form bridge of
   record: on `0 < im τ`, θ is its one-sided classical form.
3. `jacobiTheta_S_smul` — the functional equation of
   record: the S-transformation, registered verbatim.
   (Registration-grade: a verbatim restatement, kept so the
   board cites one name; counted as the non-strict one of
   the three, per RH2-1's precedent.)
-/

import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable

namespace ThetLogos

/-- **The theta adoption of record** (scope §3, rule R1).
The board's theta function is Mathlib's `jacobiTheta`, by
name — and it is the two-variable object `jacobiTheta₂` at
`z = 0`, the very object Mathlib's Hurwitz-zeta functional
equations are proved through. There is no house θ. Proof is
the upstream citation itself: `jacobiTheta_eq_jacobiTheta₂`
(OneVariable.lean:31), read at fire time and matching the
standard-object claim verbatim. -/
theorem jacobiTheta_eq_jacobiTheta₂ (τ : ℂ) :
    jacobiTheta τ = jacobiTheta₂ 0 τ :=
  _root_.jacobiTheta_eq_jacobiTheta₂ τ

/-- **The classical-form bridge of record** (scope §3(iv)).
On the upper half-plane (`0 < im τ`, where both sides live —
rule R3), Mathlib's `jacobiTheta` agrees with the classical
one-sided form `1 + 2 * ∑' n : ℕ, exp (π * I * (n+1)^2 * τ)`,
i.e. `1 + 2·Σ_{n≥1} e^(πi n² τ)`. Any future house form-theta
must be identified termwise with `jacobiTheta`/`jacobiTheta₂`
or with this one-sided form, banked before use (rule R2,
stated on this module's face). Proof is the upstream
citation itself: `jacobiTheta_eq_tsum_nat`
(OneVariable.lean:84). -/
theorem jacobiTheta_eq_tsum_nat {τ : ℂ} (hτ : 0 < τ.im) :
    jacobiTheta τ = 1 + 2 * ∑' n : ℕ,
      Complex.exp (Real.pi * Complex.I * ((n : ℂ) + 1) ^ 2 * τ) :=
  _root_.jacobiTheta_eq_tsum_nat hτ

/-- **The functional equation of record** (scope §3(i)).
The S-transformation of the standard object, as the pin
states it: for `τ : ℍ`, `jacobiTheta (S • τ) = (-I * τ)^(1/2)
* jacobiTheta τ` — in classical dress, θ(−1/τ) = √(τ/i)·θ(τ).
Later rungs quoting θ's functional equation cite this name.
Registration-grade: a verbatim restatement of the upstream
theorem `jacobiTheta_S_smul` (OneVariable.lean:43), banked
so the board cites one fence. -/
theorem jacobiTheta_S_smul (τ : UpperHalfPlane) :
    jacobiTheta ((ModularGroup.S • τ : UpperHalfPlane) : ℂ)
      = (-Complex.I * (τ : ℂ)) ^ (1 / 2 : ℂ) * jacobiTheta (τ : ℂ) :=
  _root_.jacobiTheta_S_smul τ

end ThetLogos
