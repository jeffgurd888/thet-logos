import ThetLogos.NavierStokesDefs

namespace ThetLogos

/-!
# ThetLogos.NavierStokesStatement — Navier–Stokes statement brick (NS-1b)

Board charter: **NO CLAIM.** Parts of the Clay Navier–Stokes problem
closed by this house: **0** — now, and after this brick lands (a
statement brick closes no part of the problem). This module is the
statement half of NS-1 (Lane 3), split per the NS-0 audit
(`routeb-general-scratch/scoping-ns-0-2026-11-02.md` §3): it states
Fefferman's four alternatives (A)–(D) and their disjunction, composing
ONLY the frozen packages of `ThetLogos.NavierStokesDefs` (NS-1a — its
names are frozen; nothing there is renamed, extended, or edited). It
proves NO alternative and no existence or breakdown content.

Source text: Charles L. Fefferman, "Existence and Smoothness of the
Navier–Stokes Equation," CMI official problem description —
alternatives (A)–(D), as audited in NS-0 §3.

September 2026 claim fence (one sentence, per NS-0 §1): the September
2026 claim of alternatives (C)/(D) — announced 2026-09-08 with a
claimant-side Lean formalisation — is unverified and contested
(Lean↔NL fidelity challenged in arXiv:2610.08144; CMI's problem page
still listed the problem as "Active" on 2026-11-02), and this pin
neither endorses nor refutes it.

## Quantifier shapes (NS-0 §3, mirrored exactly)

Fefferman's preamble takes `ν > 0` and `n = 3` for all four
alternatives; here `ν` is universally quantified inside each `Prop`
(the statement must hold for every `ν > 0` — the composition choice
is stated on this face; `NavierStokesSystem` also carries `0 < ν`
as its own first conjunct, and `n = 3` is `NSpace` in NS-1a).

- **(A)** `∀ ν > 0, ∀ u°` with `NSInitialDataR3 u°`, `∀ f` with
  `NSZeroForcing f` (`f ≡ 0` exactly), `∃ u p` satisfying
  `NavierStokesSystem ν u° f` + `NSSolutionSmooth` (6) +
  `NSBoundedEnergy` (7).
- **(B)** `∀ ν > 0, ∀ u°` with `NSInitialDataTorus u°`, `∀ f` with
  `NSForcingPeriodic f` + `NSZeroForcing f`, `∃ u p` satisfying the
  system + `NSSolutionPeriodic` (10 + errata pressure clause) +
  `NSSolutionSmooth` (11) + `NSBoundedEnergyTorus`.
- **(C)** `∀ ν > 0, ∃ u° f` with `NSInitialDataR3 u°` and
  `NSForcingDataR3 f` — the (C) forcing package, i.e.
  `NSForcingSmooth f ∧ NSForcingDecayR3 f` (smooth `f` satisfying
  (5), all `α`, all `m`, all `K`) — such that `¬ ∃ u p` satisfying
  the system + `NSSolutionSmooth` (6) + `NSBoundedEnergy` (7)
  for that data.
- **(D)** `∀ ν > 0, ∃ u° f` with `NSInitialDataTorus u°` and
  `NSForcingDataTorus f` (smooth, (8)-periodic, (9)-decaying),
  such that `¬ ∃ u p` satisfying the system + `NSSolutionPeriodic`
  + `NSSolutionSmooth` + `NSBoundedEnergyTorus` for that data.
- **Board:** `NSBoardStatement := A ∨ B ∨ C ∨ D` — the Clay problem
  is solved by proving ANY ONE alternative; the disjunction is the
  honest board form.

## The A/C logical relation — stated honestly on the face

**C is NOT `¬A`, and neither `A ⇒ ¬C` nor `C ⇒ ¬A` holds.** A fixes
`f ≡ 0` and quantifies `∀` over ℝ³-admissible `u°`; C quantifies
`∃` over pairs `(u°, f)` with `f` ranging over ALL smooth
(5)-admissible forcing. A C-witness may use `f ≢ 0`, so it need not
witness `¬A`; and A, which speaks only of `f ≡ 0`, says nothing
about the forced data C ranges over. The one implication that does
hold for the `Prop`s as composed here is `¬A ⇒ C`: a `¬A`-witness
is an admissible `u°` with no smooth bounded-energy solution at
`f ≡ 0`, and the zero forcing is itself (5)-admissible, so that
same pair `(u°, 0)` is a C-witness. NS-0 §3 also records
`¬C ⇒ A`; that direction holds under Fefferman's ambient-`ν`
reading (`ν` a fixed given parameter, both sides at the same `ν`),
but NOT for the `∀ν`-inside-each-`Prop` composition chosen here —
`¬C` as composed yields A's conclusion at a single viscosity only.
No implication between the alternatives is proved or claimed as a
theorem in this module: exhibiting `f ≡ 0` as `NSForcingDataR3`
is analysis content beyond statement grade, so the `¬A ⇒ C`
reading above is recorded as the audit's logical reading of the
Clay text, not as a house theorem. The B/D pair mirrors A/C
exactly (B fixes `f ≡ 0` on the torus; D ranges over all smooth
(8)+(9)-admissible forcing). A proof of C or D would leave A/B
undecided, and vice versa.

## K-NS-1 receipt (statement grade)

The five `Iff.rfl` unfoldings below are the receipt: each
alternative unfolds definitionally to its literal composition of
NS-1a packages, with no package weakened, substituted, or dropped
— (4)/(8) initial packages, (5)/(9) forcing packages with
`f ≡ 0` named exactly for A/B, genuine `C^∞` smoothness on the
full half-line, uniform bounded energy, periodicity including the
errata pressure clause, `ν > 0` and `n = 3` on the face. No
non-vacuity theorem is claimed at this grade; the compositions
were checked on the face for vacuity (an unsatisfiable conjunct
or a dropped side condition would be K-NS-1 FIRING): each data
class quantified over is the Clay class (the zero field / zero
forcing satisfy each package's shape mathematically — that check
is NOT proved here), and the solution conjunctions are the Clay
conjunctions, no more and no less. K-NS-1 does not fire on this
composition.

Honesty tiers in this file:
- **T1 (proved):** only the five `Iff.rfl` unfolding self-checks —
  about these statements, not about Navier–Stokes.
- **Definitions (no tier):** the four alternatives and the board
  disjunction. A definition asserts nothing.
- **NO CLAIM:** existence, smoothness, breakdown — no alternative
  is proved, refuted, or touched here.
-/

/-- **Fefferman (A) — existence and smoothness on ℝ³:** for every
`ν > 0`, every initial field `u°` satisfying the (4) package
`NSInitialDataR3`, and every forcing `f` with `NSZeroForcing f`
(`f ≡ 0` exactly), there exist velocity `u` and pressure `p`
satisfying `NavierStokesSystem ν u° f`, joint `C^∞` smoothness
`NSSolutionSmooth` (6), and uniform bounded energy
`NSBoundedEnergy` (7). -/
def NSAlternativeA : Prop :=
  ∀ (ν : ℝ), 0 < ν → ∀ (u0 : NSInitialField), NSInitialDataR3 u0 →
    ∀ (f : NSForcingField), NSZeroForcing f →
    ∃ (u : NSVelocityField) (p : NSPressureField),
      NavierStokesSystem ν u0 f u p ∧ NSSolutionSmooth u p ∧ NSBoundedEnergy u

/-- **Fefferman (B) — existence and smoothness on ℝ³/ℤ³:** for
every `ν > 0`, every initial field `u°` satisfying the (8) package
`NSInitialDataTorus`, and every forcing `f` with
`NSForcingPeriodic f` and `NSZeroForcing f` (`f ≡ 0` exactly),
there exist `u` and `p` satisfying `NavierStokesSystem ν u° f`,
solution periodicity `NSSolutionPeriodic` (10, including the
errata pressure clause), joint `C^∞` smoothness
`NSSolutionSmooth` (11), and uniform bounded energy on the torus
`NSBoundedEnergyTorus`. -/
def NSAlternativeB : Prop :=
  ∀ (ν : ℝ), 0 < ν → ∀ (u0 : NSInitialField), NSInitialDataTorus u0 →
    ∀ (f : NSForcingField), NSForcingPeriodic f → NSZeroForcing f →
    ∃ (u : NSVelocityField) (p : NSPressureField),
      NavierStokesSystem ν u0 f u p ∧ NSSolutionPeriodic u p ∧
        NSSolutionSmooth u p ∧ NSBoundedEnergyTorus u

/-- **Fefferman (C) — breakdown on ℝ³:** for every `ν > 0`, there
exist an initial field `u°` satisfying `NSInitialDataR3` (4) and a
forcing `f` satisfying `NSForcingDataR3` (smooth, with the full
(5) decay) such that NO velocity `u` and pressure `p` satisfy
`NavierStokesSystem ν u° f` + `NSSolutionSmooth` (6) +
`NSBoundedEnergy` (7) for that data. This is `¬∃`-smooth-solution
for SOME admissible data — it is NOT `¬NSAlternativeA` (A fixes
`f ≡ 0`; C's forcing ranges over all (5)-admissible `f`); see the
module header for the exact logical relation. -/
def NSAlternativeC : Prop :=
  ∀ (ν : ℝ), 0 < ν →
    ∃ (u0 : NSInitialField) (f : NSForcingField),
      NSInitialDataR3 u0 ∧ NSForcingDataR3 f ∧
      ¬ ∃ (u : NSVelocityField) (p : NSPressureField),
        NavierStokesSystem ν u0 f u p ∧ NSSolutionSmooth u p ∧ NSBoundedEnergy u

/-- **Fefferman (D) — breakdown on ℝ³/ℤ³:** for every `ν > 0`,
there exist an initial field `u°` satisfying `NSInitialDataTorus`
(8) and a forcing `f` satisfying `NSForcingDataTorus` (smooth,
(8)-periodic, with the full (9) decay) such that NO velocity `u`
and pressure `p` satisfy `NavierStokesSystem ν u° f` +
`NSSolutionPeriodic` (10 + errata clause) + `NSSolutionSmooth`
(11) + `NSBoundedEnergyTorus` for that data. Mirrors (C) with the
torus packages; it is NOT `¬NSAlternativeB`, for the same reason
C is not `¬A`. -/
def NSAlternativeD : Prop :=
  ∀ (ν : ℝ), 0 < ν →
    ∃ (u0 : NSInitialField) (f : NSForcingField),
      NSInitialDataTorus u0 ∧ NSForcingDataTorus f ∧
      ¬ ∃ (u : NSVelocityField) (p : NSPressureField),
        NavierStokesSystem ν u0 f u p ∧ NSSolutionPeriodic u p ∧
          NSSolutionSmooth u p ∧ NSBoundedEnergyTorus u

/-- **The Clay Navier–Stokes board statement:** the disjunction of
Fefferman's four alternatives. The Clay problem is solved by
proving ANY ONE of them; the disjunction is the honest board
form. NO CLAIM — this pins the statement; it proves nothing. -/
def NSBoardStatement : Prop :=
  NSAlternativeA ∨ NSAlternativeB ∨ NSAlternativeC ∨ NSAlternativeD

/-- K-NS-1 receipt (T1, statement grade): alternative (A) unfolds
definitionally to its literal composition of NS-1a packages.
Proved by `Iff.rfl`. Asserts nothing about Navier–Stokes. -/
theorem nsAlternativeA_iff :
    NSAlternativeA ↔
      ∀ (ν : ℝ), 0 < ν → ∀ (u0 : NSInitialField), NSInitialDataR3 u0 →
        ∀ (f : NSForcingField), NSZeroForcing f →
        ∃ (u : NSVelocityField) (p : NSPressureField),
          NavierStokesSystem ν u0 f u p ∧ NSSolutionSmooth u p ∧ NSBoundedEnergy u :=
  Iff.rfl

/-- K-NS-1 receipt (T1, statement grade): alternative (B) unfolds
definitionally to its literal composition of NS-1a packages.
Proved by `Iff.rfl`. -/
theorem nsAlternativeB_iff :
    NSAlternativeB ↔
      ∀ (ν : ℝ), 0 < ν → ∀ (u0 : NSInitialField), NSInitialDataTorus u0 →
        ∀ (f : NSForcingField), NSForcingPeriodic f → NSZeroForcing f →
        ∃ (u : NSVelocityField) (p : NSPressureField),
          NavierStokesSystem ν u0 f u p ∧ NSSolutionPeriodic u p ∧
            NSSolutionSmooth u p ∧ NSBoundedEnergyTorus u :=
  Iff.rfl

/-- K-NS-1 receipt (T1, statement grade): alternative (C) unfolds
definitionally to its literal composition of NS-1a packages —
`∃` admissible data with `¬∃` smooth bounded-energy solution.
Proved by `Iff.rfl`. -/
theorem nsAlternativeC_iff :
    NSAlternativeC ↔
      ∀ (ν : ℝ), 0 < ν →
        ∃ (u0 : NSInitialField) (f : NSForcingField),
          NSInitialDataR3 u0 ∧ NSForcingDataR3 f ∧
          ¬ ∃ (u : NSVelocityField) (p : NSPressureField),
            NavierStokesSystem ν u0 f u p ∧ NSSolutionSmooth u p ∧
              NSBoundedEnergy u :=
  Iff.rfl

/-- K-NS-1 receipt (T1, statement grade): alternative (D) unfolds
definitionally to its literal composition of NS-1a packages.
Proved by `Iff.rfl`. -/
theorem nsAlternativeD_iff :
    NSAlternativeD ↔
      ∀ (ν : ℝ), 0 < ν →
        ∃ (u0 : NSInitialField) (f : NSForcingField),
          NSInitialDataTorus u0 ∧ NSForcingDataTorus f ∧
          ¬ ∃ (u : NSVelocityField) (p : NSPressureField),
            NavierStokesSystem ν u0 f u p ∧ NSSolutionPeriodic u p ∧
              NSSolutionSmooth u p ∧ NSBoundedEnergyTorus u :=
  Iff.rfl

/-- K-NS-1 receipt (T1, statement grade): the board statement
unfolds definitionally to the disjunction of the four
alternatives. Proved by `Iff.rfl`. -/
theorem nsBoardStatement_iff :
    NSBoardStatement ↔
      NSAlternativeA ∨ NSAlternativeB ∨ NSAlternativeC ∨ NSAlternativeD :=
  Iff.rfl

end ThetLogos
