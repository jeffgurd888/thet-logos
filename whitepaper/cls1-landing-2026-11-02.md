# CLS-1 LANDING DOSSIER — 2026-11-02

**Item:** CLS-1 (Dial-1 classification lane) — the Grade-W
extraction gap, prove-or-kill.

## VERDICT: PARTIAL at the pre-named seam — extraction is PROVED modulo one named Prop; the audit locates exactly where a counterexample could live and proves the base cannot supply the missing half by its form

**Artifact:** `lean/ThetLogos/DialOneExtraction.lean` —
strict 46, defs 4 (in the 40–80 band). Verified by the
coordinator in the main tree (build green, 3238 jobs);
every checked headline on exactly
`[propext, Classical.choice, Quot.sound]`. **K-CLS-1 does
not fire** (no witness constructed).

**The audit (proved in-tree).** The base is exactly ten
clauses. The candidate locus for a non-character lift is
identified precisely: seats **8 (ν_R) and 9 (e_R)** — same
γ-sign (−1), partners 24/25 sharing +1, NO direct D_F
coupling between the pair, separated only by the different
Yukawa inputs (Ynu at (0,8) vs Ye at (1,9)) felt through the
first-order double commutator — yet their common lifted
weights DIFFER (0 vs −6). The harmless side is also proved:
the u_L colour seats are indistinguishable in γ, partner,
and D (same Yu) AND carry equal weight — colour mixing is a
scalar block and cannot obstruct (the seat-level reason
CLS-2b's colour-blindness held). And the decisive negative
observation, documented in the module: **every base clause
is algebraic in t** — the determinant clause is one
existential constraining only the product of lifted entries;
order-zero sees commutation, not diagonals; first-order is
a double commutator. **No base clause supplies any
regularity of t ↦ π(u1ParamGen α β t)** — and regularity is
exactly where a non-character lift could hide.

**The proved conditional:** `extraction_of_extractionLemma
: ∀ π, DialOneBase π → ExtractionLemma π → ∃ v, weightAt π
v`, where the named open Prop is stated exactly:

```
ExtractionLemma π := ∃ primitive (α, β), det = 1 ∀ t ∧
  (the lifted product is diagonal in the seat basis) ∧
  (∀ s, DifferentiableAt ℝ (fun t => liftedProd π α β t s s) 0)
```

— diagonality + differentiability at 0, no weight values
assumed. Route: base clauses give the lifted product a
one-parameter group law; diagonality collapses it to
per-seat Cauchy equations; differentiability at 0 propagates
through the ODE step to `exp (c·t)`; the family's
2π-periodicity plus `Complex.exp_eq_one_iff` forces
c = n·I, n ∈ ℤ — characters with integer weights. The seam
is **inhabited, not vacuous**: `extractionLemma_pi1` holds
along (3, −1), and π₁'s weights are recovered through the
headline (`pi1_has_weights`).

**What remains, decomposed honestly:** the gap is now
exactly `ExtractionLemma`'s two halves, of different
character. *Diagonality* is algebraic — plausibly attackable
from the base's clauses (unproved). *Differentiability* is
analytic — the audit shows the base's clauses are algebraic
in t by form, so the base cannot supply it; the live
possibilities are (i) Grade W is permanently posed over
base + a regularity clause, or (ii) a Hamel-pathological
lift (a discontinuous additive reparametrisation of the
one-parameter group, if one extends to a full base
representation) fires K-CLS-1. Either resolution is future
scoping (CLS-1a/1b), not fired here.

## Fences

NO CLAIM; **Dial 1: 0.** Grade W state: well-posed over
base + `ExtractionLemma`; `WeightQuestionW` additionally
requires the strengthened set. Grade T complete; Grade R
unposed.

**Census after landing: 12,162 strict / 12,536 total / 414 counted
modules; zero `sorry` terms tree-wide.**

## Backers since last landing

None new on the record since the last landing.
