/-
# RiemannDirichletBridgePin — RH-2 brick 1: the ζ and Dirichlet
bridges of record (citation / registration)

**Scope: ~/workspace/your_files/rh2-statement-fidelity-bridges-scope-2026-11-22.md
(§1, §2, §6). Ladder of record: Ladder 2, RH-2, in
~/workspace/your_files/millennium-ladders-ym-and-riemann-2026-11-21.md.
Obstruction map: ~/workspace/your_files/rh1-obstruction-map-2026-11-22.md.
Fired 2026-11-24 on the parent's word, L2 lane, when a build slot
freed. T5. NO CLAIM. Parts of the Riemann Hypothesis closed by
this brick: 0. The RH dial stays 0.**

WHAT THIS BRICK IS. RH-2 is the statement-fidelity rung: for every
object any later rung names, a proved lemma that the built object
IS the standard object. This first brick registers the board's
ζ-bridge and Dirichlet bridge of record. The audit behind the
scope found both bridges ALREADY IN MATHLIB, so this brick is a
citation brick — the cheapest honest outcome: four house theorems
whose proofs are the upstream citations themselves, so later
rungs cite one fence here instead of re-deriving upstream API.
A bridge proves that our words and the world's words name the
same object; it proves nothing about the object. Nothing in this
module states, assumes, or approaches any zero of any function.

THE FIRE-TIME AUDIT (the scope's kill criterion, checked first).
The scope's kill criterion for this brick: if either cited
statement, read at fire time, differs from the standard-object
claim (hypotheses, junk-value convention), the brick stops and
reports — the citation is never silently weakened. Read in the
pin (Mathlib v4.35.0-rc3) on 2026-11-24, the statements are
exactly as the scope recorded them:

- `DirichletCharacter.LFunction_eq_LSeries`
  (Mathlib/NumberTheory/LSeries/DirichletContinuation.lean:75):
  for `1 < re s`, `LFunction χ s = LSeries (χ ·) s` — the
  analytically continued object IS the naive Dirichlet series
  where both live. (The whole `LFunction` section of that file
  sits under `variable {N : ℕ} [NeZero N]`, line 51; the
  wrapper below carries the same instance context, verbatim —
  the mathematical hypothesis and the equality are untouched.)
- `DirichletCharacter.LFunction_modOne_eq` (ibid., line 67):
  `LFunction χ = riemannZeta` for `χ` mod 1 — a FUNCTION
  equality, no half-plane hypothesis.
- `DirichletCharacter.LSeries_modOne_eq`
  (Mathlib/NumberTheory/LSeries/Dirichlet.lean:170):
  the mod-1 character's L-series is the L-series of the
  constant function `1`; beside it `modOne_eq_one` (ibid.):
  the mod-1 character, as a coefficient function, IS `1`.

The kill criterion did NOT trigger. The citations below are
verbatim in strength — no hypothesis dropped, none added.

THE RULES, ON THE FACE (scope R1–R3, binding on every RH-2
brick):
- **R1 — adopt, never redefine.** Where Mathlib carries the
  standard object, the house uses Mathlib's. This module
  contains no `def` at all: no house ζ, no house L, no house θ.
- **R2 — agreement before use.** No later rung may consume an
  object whose agreement lemma is not already banked. This
  module is where the ζ and Dirichlet agreements are banked.
- **R3 — junk values are part of the object.** Mathlib's
  `LSeries` is `0` off the convergence half-plane by convention
  (the DirichletContinuation file's own note), and `riemannZeta`
  carries its value at the pole `s = 1` as part of its
  definition. The bridges respect this: the agreement lemmas
  hold exactly on `1 < re s`, where both sides live, and the
  mod-1 bridge is a function equality — it identifies the two
  functions at EVERY `s`, pole behaviour included, rather than
  papering over the convention.

THE HECKE FENCE (scope §4, restated so no reader of this module
can miss it): the Hecke seat on this board is EMPTY and stays
empty. No Hecke L-function exists in the pin; none is defined,
named, or touched here. RH-2's deliverable for Hecke is the
fence, not a brick.

RELATION TO RH-0. The statement-level bridge is already banked:
`ThetLogos.riemannBoardStatement_iff` (RiemannHypothesisPin)
proves the corpus's target IS Mathlib's `RiemannHypothesis`.
This brick is the function-level registration beneath it: the
functions named inside any such statement are the standard
functions, by the citations below.

THE FOUR DECLARATIONS (scope §6 price: ~4 decls, ~3 strict;
citation bricks are thin by nature and are counted thin):
1. `dirichletLFunction_eq_LSeries` — scope (b): the Dirichlet
   bridge of record, the continued L-function equals its naive
   series on `1 < re s`.
2. `dirichletLFunction_modOne_eq` — scope (c): the mod-1
   character's L-function is `riemannZeta`, as functions.
   (Registration-grade: a verbatim restatement, kept so the
   board cites one name; counted as the non-strict one of the
   four, per the scope's price.)
3. `dirichletLSeries_modOne_eq` — scope (a) at series level:
   the mod-1 character's L-series is the constant-`1` series.
4. `riemannZeta_eq_LSeries_one` — scope (a) at ζ level:
   on `1 < s.re`, `riemannZeta s = LSeries 1 s` — ζ IS the
   naive series `∑ n^(−s)` where both live. Proved from the
   three citations above, nothing else.
-/

import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.LSeries.Dirichlet

namespace ThetLogos

/-- **The Dirichlet bridge of record** (scope §2, item (b)).
For `1 < s.re`, the analytically continued Dirichlet
L-function agrees with the naive Dirichlet series of its
character's coefficients. Proof is the upstream citation
itself: `DirichletCharacter.LFunction_eq_LSeries`
(DirichletContinuation.lean:75), read at fire time and
matching the standard-object claim verbatim. -/
theorem dirichletLFunction_eq_LSeries {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {s : ℂ} (hs : 1 < s.re) :
    DirichletCharacter.LFunction χ s = LSeries (χ ·) s :=
  DirichletCharacter.LFunction_eq_LSeries χ hs

/-- **The mod-1 bridge of record** (scope §2, item (c)).
The L-function of the (unique) Dirichlet character mod 1 is
the Riemann zeta function — an equality of FUNCTIONS, so it
identifies the two objects at every `s`, the pole behaviour
at `s = 1` included (rule R3). Proof is the upstream
citation itself: `DirichletCharacter.LFunction_modOne_eq`
(DirichletContinuation.lean:67). Registration-grade: a
verbatim restatement, banked so later rungs cite this name. -/
theorem dirichletLFunction_modOne_eq {χ : DirichletCharacter ℂ 1} :
    DirichletCharacter.LFunction χ = riemannZeta :=
  DirichletCharacter.LFunction_modOne_eq

/-- **The ζ bridge at series level** (scope §1/§6, item (a)).
The L-series of the mod-1 character is the L-series of the
constant function `1` — the naive zeta series. Proof is the
upstream citation itself:
`DirichletCharacter.LSeries_modOne_eq` (Dirichlet.lean:170),
whose content is that the mod-1 character's coefficient
function is `1` (`DirichletCharacter.modOne_eq_one`). -/
theorem dirichletLSeries_modOne_eq :
    LSeries ((1 : DirichletCharacter ℂ 1) ·) = LSeries 1 :=
  DirichletCharacter.LSeries_modOne_eq

/-- **The ζ bridge of record** (scope §1, item (a)). On the
convergence half-plane `1 < s.re`, the Riemann zeta function
agrees with the naive series: `riemannZeta s = LSeries 1 s`,
i.e. `∑ n^(−s)` under Mathlib's `LSeries` convention (rule
R3: off this half-plane the series side is `0` by convention
and no agreement is claimed there). Proved from this brick's
three citations and nothing else: the mod-1 L-function is
`riemannZeta` (item (c)), it agrees with its coefficient
series on the half-plane (item (b)), and the mod-1
character's coefficients are the constant `1`. -/
theorem riemannZeta_eq_LSeries_one {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s = LSeries 1 s := by
  have h1 := DirichletCharacter.LFunction_eq_LSeries (1 : DirichletCharacter ℂ 1) hs
  have h2 : DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 1) = riemannZeta :=
    DirichletCharacter.LFunction_modOne_eq
  have h3 : (((1 : DirichletCharacter ℂ 1) ·) : ℕ → ℂ) = 1 :=
    DirichletCharacter.modOne_eq_one
  rw [h2] at h1
  rw [h3] at h1
  exact h1

end ThetLogos
