# BRST intake (Round 2) — dossier

**Date:** 2026-10-18. **Module:** `lean/ThetLogos/BRSTFinite.lean`
(414 lines; new file only — nothing existing modified).
**Price:** M (parked-fleet gauntlet §8). **Verdict: STANDS at the
priced scope.** Program total: 3,177 + 24 = **3,201 strict**.

**Numbers.** 24 strict T1 (line-initial `^(theorem|lemma) ` on
comment-stripped source), 0 `@[simp]`, 0 sorry/admit. Definitions:
1 structure (`FiniteLieData`) + 13 defs/abbrevs. Targeted build
green, **3,117 jobs**, `.olean` present. `#print axioms` on ten
headlines (`FiniteLieData.d2_d1`, `brstQ_sq`, `exactAlt2_closed`,
`su2_d1_injective`, `su2_d1_ne_zero`, `su2_H1_vanishes`,
`su2_d2_alt_zero`, `su2_exact_of_alt`, `su2_H2_vanishes`,
`abelian_d2`): each exactly `[propext, Classical.choice,
Quot.sound]`.

## 1. What was built

**§1 — a finite Lie algebra as data, and its CE complex.**
`FiniteLieData n 𝕜` pins a finite-dimensional Lie algebra by
structure constants `c k i j` (`[eᵢ, eⱼ] = ∑ k, c k i j • eₖ`) with
antisymmetry, alternation (`c k i i = 0` — carried as independent
data, since antisymmetry alone does not give it in characteristic
2), and the Jacobi identity in contracted form. On the cochain
spaces `C⁰ = 𝕜`, `C¹ = Fin n → 𝕜`, `C²`, `C³` (trivial
coefficients), the Chevalley–Eilenberg differentials `d₁`, `d₂`
are defined by their standard coordinate formulas.

**The headline: `FiniteLieData.d2_d1` — `d₂ ∘ d₁ = 0`, and the
proof is the Jacobi identity.** The expansion factors
componentwise as `∑ m, a m * (Jacobi contraction)`
(`FiniteLieData.aux`, `FiniteLieData.jacobi'`), so nilpotency in
this model is not analogous to Jacobi; it is Jacobi, contracted.

**§2 — the assembled charge and the cohomology language.**
`brstQ` assembles `Q` on the truncated complex `C⁰ × C¹ × C²`,
`Q (x, a, A) = (0, 0, d₁ a)`, and `brstQ_sq` proves `Q (Q v) = 0`.
This direction is bookkeeping (the top component maps out of the
truncated complex), and the module says so in its own docstring:
the content-bearing nilpotency is `d₂ ∘ d₁ = 0`. Cohomology is
booked elementarily (predicates, no quotient machinery):
`Closed1`, `Alt2`, `ClosedAlt2`, `ExactAlt2`, with
`exactAlt2_closed` (exact ⇒ closed — the well-definedness of `H²`)
as a corollary of the headline. The abelian contrast is computed:
for `abelianData` (zero bracket), `d₁ = d₂ = 0`, so every cochain
is closed and nothing nonzero is exact (`H¹ = C¹`, `H² = Alt C²`
in full).

**§3 — the worked example: `𝔰𝔲(2)`, cohomology computed exactly.**
`su2Data : FiniteLieData 3 ℂ` with `c k i j = ε i j k`
(`lcEps`, the Levi-Civita symbol in closed form
`((i−j)(j−k)(k−i))/2`). Its Jacobi field is the finite
ε-contraction, discharged by `fin_cases` + `norm_num`. Then, all
by explicit computation:

- `su2_d1_injective` — `d₁` is injective (components read off:
  `(d₁ a) 0 1 = −a 2`, `(d₁ a) 1 2 = −a 0`, `(d₁ a) 2 0 = −a 1`);
- `su2_H1_vanishes` — **H¹(𝔰𝔲(2); ℂ) = 0**;
- `su2_H0` — **H⁰ = ℂ**;
- `su2_d2_alt_zero` — `d₂` vanishes on every alternating
  2-cochain (each component collapses through the ε-support to
  diagonal values, which alternation kills);
- `su2_exact_of_alt` — every alternating 2-cochain is exact, via
  the Hodge-dual candidate `a k = −½ ∑ p q, ε k p q · A p q` and
  the εε contraction identity, checked finitely;
- `su2_H2_vanishes` — **H²(𝔰𝔲(2); ℂ) = 0** (Whitehead vanishing,
  this finite case);
- `su2_d1_ne_zero` — the complex is not trivial (`d₁ ≠ 0`).

## 2. Fit table

| Clause | Status |
|---|---|
| BRST as pure algebra: nilpotent differential on a graded complex from finite gauge data | **FIT — built and proved (T1)** |
| BRST charge `Q` as a single assembled operator, `Q² = 0` | **T1** (`brstQ_sq`; bookkeeping direction named as such) |
| Content-bearing nilpotency `d² = 0` | **T1**, and it *is* Jacobi (`d2_d1`) |
| Cohomology `H(Q) = ker / im` at finite level | **T1** as predicates + computed example; no quotient-type machinery (named) |
| `𝔰𝔲(2)` low-degree cohomology | **T1: H⁰ = ℂ, H¹ = 0, H² = 0** |
| Abelian factor (`u(1)`-shaped, zero bracket) | **T1: full cochain cohomology** (contrast case) |
| Ghosts | graded vector-space generators (cochain degrees) only — **no ghost fields** |
| BRST as a quantization procedure (gauge fixing, path integral, physical state space `ker Q / im Q` as Hilbert space) | **NO-FIT** — the corpus proves exact gauge invariance without gauge fixing (Stage 0 pre-kill); nothing here is a quantization |
| Continuum BRST / BRST for the lattice gauge theory as a field theory | **ABSENT / not claimed** |
| Anomalies | **ABSENT, named**: no anomaly content is computed; the vanishing of `H²(𝔰𝔲(2))` is a Lie-algebra-cohomology fact, *not* anomaly cancellation (which concerns representation traces — not computed anywhere in this brick) |

## 3. Audit (grep-backed, pinned Mathlib v4.35.0-rc3)

- `grep -ril "brst" Mathlib/` — **0 files**. No BRST anywhere in
  pinned Mathlib; likewise **0 files** in the pre-brick corpus.
- Pinned Mathlib **does** have a neighboring fragment:
  `Mathlib/Algebra/Lie/Cochain.lean` (178 lines) defines
  `LieModule.Cohomology`'s `oneCochain`, `twoCochain`, `d₁₂`,
  `d₂₃`, `twoCocycle` for Lie-algebra *extension theory*, and
  proves the abstract nilpotency `d₂₃_comp_d₁₂` (line 143) for
  general coefficients. It has no graded complex/cohomology
  groups, no BRST charge, and computes no example. This brick
  does not route through it (deviation D2) — the finite
  coordinate complex and the explicit `𝔰𝔲(2)` computation are
  the intake's object — but the abstract identity's prior
  existence in Mathlib is recorded, not erased.

## 4. Corrections and deviations (named)

- **C1 (correction to the intake's own framing).** The abstract
  CE nilpotency in low degrees already exists in pinned Mathlib
  (`d₂₃_comp_d₁₂`, §3 above). What is new here is not the
  identity but its coordinate form — where the proof is visibly
  exactly the Jacobi contraction — together with the assembled
  charge, the corpus-facing finite model, and the computed
  example. Any future prose claiming "nilpotency was absent from
  Mathlib" would be false; this dossier is the fence against it.
- **D1 (deviation, substrate).** The corpus's gauge material is
  group-level (`SMGaugeAlgebra.lean`: `SU2 = Matrix.specialUnitaryGroup
  (Fin 2) ℂ`; `LatticeGauge.lean`: finite gauge *groups*) — it owns
  no coordinate Lie bracket. The model's algebra is therefore
  `𝔰𝔲(2)` in its standard ε-presentation, supplied and named
  here, not imported from a corpus bracket that does not exist.
- **D2 (deviation, route).** Mathlib's `LieModule.Cohomology`
  fragment not used — see §3. The intake's deliverable (finite
  coordinate complex + assembled charge + computed cohomology of
  the corpus's smallest nonabelian factor) is not that API's
  purpose (extensions, general coefficients, multilinear maps).
- **D3 (scoping, truncation).** The assembled complex is
  truncated at ghost number 2: `Q`'s `d₂`-component lands
  outside `C⁰ × C¹ × C²`, and `d₂` is carried as the standalone
  map defining closedness in degree 2. `d₃ ∘ d₂ = 0` (which
  needs alternation hypotheses on 2-cochains, not bare Jacobi)
  is **not** proved and not claimed.
- **D4 (scoping, coefficients and degrees).** Trivial
  coefficients only; cohomology in degrees 0–2 only. `H³` of
  `𝔰𝔲(2)` (which is ℂ in the literature) is not computed here.

## 5. Fences

Finite-dimensional algebraic model only. No continuum gauge
theory, no gauge fixing, no physical state space, no path
integral, no anomaly claim. Clay parts closed: **0** (unchanged).

## 6. Surprises

1. Mathlib's `Lie/Cochain.lean` fragment (with `d₂₃_comp_d₁₂`)
   was newer than the intake's expectation — the audit caught
   it before the dossier could claim an absence (C1).
2. For `𝔰𝔲(2)`, `d₂` vanishes on *all* alternating 2-cochains —
   stronger than `H² = 0` needs (exactness alone would do); the
   ε-support collapses every component to diagonal values.
3. The ε-Jacobi identity and both cohomology computations all
   fell to the same finite closer (`fin_cases` + `norm_num` +
   `ring`): at `Fin 3`, the entire analytic content of this
   intake is finitely checkable, and was checked.
