/-
# RiemannDedekindRegistrationPin — RH-2 brick 4: the Dedekind ζ
registration, with its labelled hole (registration)

**Scope: ~/workspace/your_files/rh2-statement-fidelity-bridges-scope-2026-11-22.md
(§5, §6). Ladder of record: Ladder 2, RH-2, in
~/workspace/your_files/millennium-ladders-ym-and-riemann-2026-11-21.md.
Obstruction map: ~/workspace/your_files/rh1-obstruction-map-2026-11-22.md.
Fired 2026-11-24 on the parent's word, L2 lane, per brick cadence
(RH2-3 banked the same morning at `db95457`). T5. NO CLAIM.
Parts of the Riemann Hypothesis closed by this brick: 0. The
RH dial stays 0. This is the LAST brick of RH-2: with it, RH-2
is complete as scoped — no RH2-5 exists.**

WHAT THIS BRICK IS. RH-2 is the statement-fidelity rung: for
every object any later rung names, a proved lemma that the
built object IS the standard object. Dedekind ζ is the
carried object of §5, and its bridge is the unusual one of
the four: it needs no hunting, because Mathlib DEFINES
`NumberField.dedekindZeta` as its L-series — the
series-agreement half of the bridge is definitional. What a
registration brick owes here is therefore threefold: state
the definitional agreement as a citable lemma (so later
rungs cite one fence, per rule R2), register the junk-value
convention the object inherits (rule R3), and — the point of
this brick — NAME WHAT THE PIN DOES NOT CARRY, on the face,
as a labelled hole. A registration proves that our words and
the world's words name the same object; it proves nothing
about the object. Nothing in this module states, assumes,
or approaches any zero of any function.

THE FIRE-TIME AUDIT (the scope's method, checked first).
Read in the pin (Mathlib v4.35.0-rc3) on 2026-11-24, in
Mathlib/NumberTheory/NumberField/DedekindZeta.lean — the
pin's ENTIRE Dedekind ζ material (a grep over the whole pin
finds no other file mentioning `dedekindZeta`; the file is
118 lines and was read in full):

- `NumberField.dedekindZeta` (lines 50–51):
  `def dedekindZeta (s : ℂ) := LSeries (fun n ↦ Nat.card
  {I : Ideal (𝓞 K) // absNorm I = n}) s` — the Dedekind zeta
  function IS, by definition, the L-series of the
  ideal-counting function (the number of integral ideals of
  norm `n`). Exactly the scope's §5(ii) claim.
- Beside the definition the file carries only the residue
  constant `dedekindZeta_residue` (with its positivity) and
  `tendsto_sub_one_mul_dedekindZeta_nhdsGT`, the Dirichlet
  class number formula: the pole behaviour at `s = 1`,
  approached from the right on the real line.
- THE FUNCTIONAL EQUATION IS ABSENT — confirmed at fire
  time, not inherited from the scope: no functional-equation
  statement and no analytic-continuation statement for ζ_K
  exists anywhere in the pin. The file's only TODO reads
  "Generalize the construction of the Dedekind zeta
  function." The hole the scope labelled is still a hole.

THE KILL CRITERION, ANSWERED AT DRAFTING. The scope
pre-registered this brick's kill: if at fire time the in-pin
definition has changed shape (e.g. become a
completed-object definition), the registration stops and
re-audits rather than citing stale lines. The definition
has NOT changed shape — it is the bare L-series definition
above, re-read verbatim. The kill criterion did NOT
trigger.

THE LABELLED HOLE, STATED PLAINLY. The standard object of
scope §5(i) is ζ_K as a CONTINUED function, with its
functional equation. The pin carries neither the
continuation nor the functional equation. The identification
registered by this brick is therefore exactly as wide as
the definition, and no wider: ζ_K is the ideal-counting
L-series — identified with the standard object where that
series lives, and carrying the L-series junk value `0` off
absolute convergence (registered as declaration 2 below).
The continuation half of the bridge is OPEN. It is labelled
here so no later rung can mistake this registration for the
whole bridge: any later rung that needs ζ_K off the
convergence half-plane, or quotes a functional equation for
ζ_K, must first build that half as its own scoped brick.
Until then, those statements do not exist for this board.

THE RULES, ON THE FACE (scope R1–R3, binding on every RH-2
brick):
- **R1 — adopt, never redefine.** This module contains NO
  `def` at all (structural, as in RH2-1 and RH2-3). The
  only Dedekind ζ named anywhere in it is Mathlib's
  `NumberField.dedekindZeta`. There is no house ζ_K.
- **R2 — agreement before use.** No later rung may consume
  ζ_K as a series whose agreement lemma is not already
  banked. The agreement of record is declaration 1 below:
  definitional, proved by `rfl`, and citable by name.
- **R3 — junk values are part of the object.** `LSeries`
  is `0` off absolute convergence
  (`LSeries.eq_zero_of_not_LSeriesSummable`,
  LSeries/Basic.lean:207), and ζ_K inherits that convention
  through its definition — registered as declaration 2, so
  the registered object is the whole object, convention
  included. Conversely, the pole behaviour the pin DOES
  carry is registered as declaration 3 rather than assumed:
  what is banked is what may be cited.

THE HECKE FENCE (scope §4, restated so no reader of this
module can miss it): the scope notes that Dedekind ζ is,
in the world's vocabulary, the Hecke L-function of the
trivial character only. That vocabulary does NOT put a
Hecke L-function on this board. The Hecke seat stays
EMPTY; no Hecke L-function exists in the pin, and nothing
Hecke-side is defined, named, or touched here.

THE THREE DECLARATIONS (scope §6 price: ~3 decls, ~1–2
strict; registration bricks are thin by nature and are
counted thin):
1. `dedekindZeta_eq_LSeries` — the definitional agreement
   of record: ζ_K IS the L-series of its ideal-counting
   function. (Strict.)
2. `dedekindZeta_eq_zero_of_not_LSeriesSummable` — the
   junk-value receipt (R3): off absolute convergence of
   its defining series, ζ_K takes the value `0`.
   (Strict.)
3. `tendsto_sub_one_mul_dedekindZeta_nhdsGT` — the pole
   behaviour of record: the class number formula, the
   residue of ζ_K at `s = 1`, registered verbatim.
   (Registration-grade: a verbatim restatement, kept so
   the board cites one name; counted as the non-strict
   one of the three, per RH2-1's precedent.)
-/

import Mathlib.NumberTheory.NumberField.DedekindZeta

open Filter

open scoped Topology NumberField

namespace ThetLogos

/-- **The Dedekind ζ agreement of record** (scope §5, rule
R2). Mathlib's `NumberField.dedekindZeta` IS the L-series of
the ideal-counting function — the number of integral ideals
of `𝓞 K` of norm `n` — because that is its definition
(DedekindZeta.lean:50–51, re-read at fire time). The
agreement is therefore definitional and is proved by `rfl`;
it is banked as a named lemma so later rungs cite this fence
instead of unfolding the definition themselves. The
identification registered here is exactly as wide as the
definition: the continuation half of the standard object is
absent in-pin and is this bridge's labelled hole, stated on
the module face. -/
theorem dedekindZeta_eq_LSeries (K : Type*) [Field K] [NumberField K] (s : ℂ) :
    NumberField.dedekindZeta K s =
      LSeries (fun n ↦ Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n}) s := rfl

/-- **The junk-value receipt** (scope §5, rule R3). The
registered object includes its convention: where the
defining L-series is not absolutely convergent, ζ_K takes
the `LSeries` junk value `0` — the pin's convention
(`LSeries.eq_zero_of_not_LSeriesSummable`,
LSeries/Basic.lean:207), inherited by ζ_K through its
definition (declaration 1). No agreement with any continued
value is claimed at such points; the pin carries no
continuation there to agree with. -/
theorem dedekindZeta_eq_zero_of_not_LSeriesSummable
    (K : Type*) [Field K] [NumberField K] (s : ℂ)
    (h : ¬ LSeriesSummable (fun n ↦ Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n}) s) :
    NumberField.dedekindZeta K s = 0 :=
  LSeries.eq_zero_of_not_LSeriesSummable _ s h

/-- **The pole behaviour of record** (scope §5(ii)). What
the pin carries at the pole of ζ_K, registered verbatim:
the Dirichlet class number formula — `(s − 1) · ζ_K(s)`
tends to `NumberField.dedekindZeta_residue K` as the real
`s` tends to `1` from above. This is the pin's own theorem
(`NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT`,
DedekindZeta.lean), banked so the board cites one name.
Registration-grade: a verbatim restatement, per RH2-1's
precedent. It is a statement about the real approach to
`s = 1` only; it is not a continuation and not a functional
equation, and the module face names both as absent. -/
theorem tendsto_sub_one_mul_dedekindZeta_nhdsGT
    (K : Type*) [Field K] [NumberField K] :
    Tendsto (fun s : ℝ ↦ (s - 1) * NumberField.dedekindZeta K s) (𝓝[>] 1)
      (𝓝 (NumberField.dedekindZeta_residue K)) :=
  NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT K

end ThetLogos
