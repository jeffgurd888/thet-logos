import Mathlib.Tactic
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.Star.Basic

/-!
# AGS-0 — RECORD PIN: the adjointed sum total (0 strict by design)

## The discussion that brought it about

Zero's seeing (2026-11-10 12:15 EST), verbatim: **"maybe
gravity is the adjointed sum total"** — scoped the same day
(`adjointed-sum-scope-2026-11-10.md`) as a Register-B identity
(derive-or-die), with the Register-A fork left in Zero's chair.
This pin is the register the scoping priced at §6 (band S,
0 strict, pre-registered dial-ineligible, the OG-0 precedent):
the seeing, the three readings, the per-seat verdicts, the
K-OG-SUM scope ruling, the collapse census, the K-AGS-*
registry, and the Gate B interaction — on the record, in
machine-visible form, so no future lane re-derives the audit
or cites K-OG-SUM outside its scope.

## The three readings (this module's definitions)

- **R1, the total self-adjoint sum** `Σ_{A∈F} (A + A*)` —
  `agsSelfAdjointSum`. STATEABLE as a definition wherever a
  linear operator family exists; at the corpus's canonical S1
  families it collapses on landed theorems (2D, 2γ_F; the
  graded sum γ_F·D + D·γ_F = 0).
- **R2, the adjoint of the total** `(Σ_{A∈F} A)*` —
  `agsAdjointOfSum`. Bookkeeping: under *-closure it IS R3's
  total; the reduction is registered as `AgsReductionForm`
  below (T1-grade star arithmetic as a form; unproved here —
  this pin proves nothing by design).
- **R3, the *-closed total** — `agsStarClosed` +
  `agsClosedTotal`. Every referent already exists in the
  corpus under its own name: the *-algebra AF with
  `totalConj`, the fluctuated Dirac `D + A + JAJ⁻¹`, the
  Wilson action, TE-T3's zero.

## The collapse census (§4.4 of the scoping)

Owned totals land in three modes — **2A** (self-adjoint
members double), **0** (balanced/graded pairs), **scalar**
(trace/action functionals) — and the fourth mode, **c·I**,
the only unity-shaped one, is instantiated by NOTHING the
corpus owns. Its form is registered here as
`agsConstMultipleForm`: a claimed c·I total must instantiate
it, named, and **K-AGS-COLLAPSE** arms over exactly that
claim (a proved c·I total with c ≠ 0 would be the census's
first exception — none exists).

## Verdicts and kills (carried from the scoping)

- The identity "gravity is the adjointed sum total" is
  **NOT STATEABLE as gravity at every seat**: S1 (the totals
  are the finite SM's kinematics, landed under their own
  names), S2 (the seat's total is TE-T3's 0 — REFUTED;
  K-OG-SUM stands FIRED on its home seat and does NOT
  extend to operator sums, per the §4.3 scope ruling), S3
  (**K-AGS-TYPE FIRED**: (A + A*) has no referent for
  group-valued variables), S4 (no operator family exists;
  the founding seat owns a pair, and ker L is withdrawn).
- **K-AGS-COLLAPSE — FIRED at read level** (2026-11-10) over
  the canonical families; armed over any other named family.
- **K-AGS-PROXY / K-AGS-RENAME / K-AGS-DIAL — armed/
  standing**: no AGS total may be presented as a gravity
  object, a response law, an identity, or dial evidence; a
  Register-A naming of a total is a naming act over
  already-owned objects, not progress toward the identity.
- **Gate B interaction (§4.1/§5):** gravity's primitive
  stands declared as **unity** (Zero, 2026-11-08). Naming a
  total as a designed object UNDER that primitive is
  Register-A option (A-i); replacing the primitive itself
  (A-ii) would AMEND Gate B — the Architect's hand alone,
  undecided on this pin's face. The fork is Zero's.

**NO CLAIM. Dials 0/4. Dial 2 = 0.**
-/

namespace ThetLogos

section AdjointedSum

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- **R1 — the total self-adjoint sum** (Tier T2 — definition):
    `Σ_{A ∈ F} (A + A*)` over a finite family `F` of operators.
    Stateable as a definition at any linear seat; its content
    at owned seats is the collapse census on the header. -/
noncomputable def agsSelfAdjointSum (F : Finset (Matrix m m ℂ)) :
    Matrix m m ℂ :=
  ∑ A ∈ F, (A + star A)

/-- **R2 — the adjoint of the total** (Tier T2 — definition):
    `(Σ_{A ∈ F} A)*`. Differs from a total of adjoints only in
    bookkeeping; see `AgsReductionForm`. -/
noncomputable def agsAdjointOfSum (F : Finset (Matrix m m ℂ)) :
    Matrix m m ℂ :=
  star (∑ A ∈ F, A)

/-- ** *-closure of a family** (Tier T2 — definition): every
    member's adjoint is again a member. -/
def agsStarClosed (F : Finset (Matrix m m ℂ)) : Prop :=
  ∀ A ∈ F, star A ∈ F

/-- **R3 — the *-closed total** (Tier T2 — definition): the
    plain total `Σ_{A ∈ F} A`, read over a *-closed family.
    Its owned referents are landed under their own names
    (AF / `totalConj`, the fluctuated Dirac, the Wilson
    action, TE-T3's zero) — this def registers the shape. -/
noncomputable def agsClosedTotal (F : Finset (Matrix m m ℂ)) :
    Matrix m m ℂ :=
  ∑ A ∈ F, A

/-- **The c·I form** (Tier T5 — statement form): the R1 total
    of `F` equals a scalar multiple of the identity. This is
    the collapse census's fourth mode — the only
    unity-shaped one, instantiated by nothing owned.
    K-AGS-COLLAPSE arms over any claim of this form; a
    proved instance with `c ≠ 0` would be the census's
    first exception. -/
def agsConstMultipleForm (F : Finset (Matrix m m ℂ)) (c : ℂ) :
    Prop :=
  agsSelfAdjointSum F = c • (1 : Matrix m m ℂ)

/-- **The R2 reduction, as a form** (Tier T5 — statement
    form): over a *-closed family, the adjoint of the total
    IS the total — R2 has no content beyond R3. T1-grade
    star arithmetic; registered as a form, unproved by this
    pin's 0-strict design. -/
def AgsReductionForm : Prop :=
  ∀ F : Finset (Matrix m m ℂ), agsStarClosed F →
    agsAdjointOfSum F = agsClosedTotal F

end AdjointedSum

end ThetLogos
