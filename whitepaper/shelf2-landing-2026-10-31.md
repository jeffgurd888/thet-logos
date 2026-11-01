# SHELF-2 — LANDED PARTIAL at the pre-named Seam A: the Friedrichs representation theorem's core is FULL (operator, representation identity, semiboundedness, graph-equality self-adjointness, at RCLike generality); the square-root clause lands over ℂ with the exact domain equality named open

**Verdict: SHELF-2 PARTIAL (Seam A, pre-named in the pack). The core of Kato's first representation theorem is proved in full: from a closed semibounded form, the associated operator exists on its natural domain, satisfies the representation identity, inherits the semibound, is closed, has the shifted resolvent surjective — and is self-adjoint as GRAPH EQUALITY `T† = T` in the pin's `LinearPMap` dialect (Seam B never triggered; no fallback characterization was substituted). The square-root (Kato) clause lands over ℂ: the root is self-adjoint and the Kato identity holds on the operator domain. TWO named remainders stand on the module's face (below): the exact square-root domain equality, and the ℂ-generality boundary of the root clause. Strike-check negative: "Friedrichs" occurs zero times in the pinned Mathlib — a fill, not a strike. NO CLAIM; dials 0/4 — a general analysis fill; it closes no posted question.**

## Presentation, named plainly

The form is taken in its **closed parametrization**: a form Hilbert space `V`, an injective continuous inclusion `J : V →L[𝕜] H` with `‖Jx‖ ≤ ‖x‖` and dense range, lower bound `m`, shift `c = 1 − m`, `t(x,y) = ⟪x,y⟫_V − c·⟪Jx, Jy⟫_H`, form domain `range J`. This is the standard equivalent data of a densely defined closed semibounded form (the form space is the form domain under the form inner product) — stated here so the landed generality is read exactly: §§1–6 at full `RCLike` generality (ℝ or ℂ, abstract Hilbert spaces). The seat module `LatticeSliceFriedrichs.lean` was reference only, unedited; its own residues are untouched.

## What landed (`FriedrichsExtension.lean`)

Core headlines (all on the standard three axioms, parent-verified): `friedrichsOperator_isSelfAdjoint`, `friedrichsOperator_representation` (+ primed form), `friedrichsOperator_semibounded`, `friedrichsOperator_mem_domain_iff`, `friedrichsOperator_add_shift_surjective`, `friedrichsOperator_isClosed`, `friedrichsResolvent_nonneg`. Square root (§7, over ℂ): `friedrichsSqrt_isSelfAdjoint`, `friedrichsSqrt_kato_identity`, `friedrichsSqrt_sq_on_operatorDomain`.

**Disclosure (builder-reported, recorded at full rank):** during the build the compiler caught a genuine mathematical error in the first statement of the resolvent characterization — it read `(T + c + 1)x = f` with a stray term, which is false; the landed statement is the correct `(T + c)x = f` surjectivity. The headline was corrected in substance, not merely repaired syntactically.

## Named remainders (verbatim from the module's §7 header)

**Seam A:** "the exact domain equality `D(S) = D(t)` (i.e. `range √R = range J` as subsets of `H`) and hence the Kato identity on all of `D(t)`, not only on `D(T)`, are NOT proved here. The obstruction at this pin is the intertwining `J ∘ (BJ)^{1/2} = (JB)^{1/2} ∘ J` for the form-space resolvent product, which the pin's CFC does not supply for noncommuting products."

**Generality boundary:** "this section is stated over `ℂ`. The bounded square root is built with the pin's `CFC.sqrt`, whose real continuous functional calculus for bounded-operator algebras is available at `ℂ` but does not synthesize at an abstract `RCLike` field in this pin… The core construction (§§1-6) is proved at full `RCLike` generality; only this square-root clause is `ℂ`-bound." (Empirically verified by the builder's probes: `CFC.sqrt` elaborates at ℂ, fails at abstract RCLike and at concrete ℝ in this pin.)

## Fences

The S2-4(b)/FG-2 fence "the general Friedrichs representation theorem" retires **at the landed generality stated above** (RCLike core; ℂ square-root clause with Seam A open). Nothing stronger is claimed anywhere downstream on the strength of this landing.

## Parent verification (from disk)

- Canonical counter: **strict=62, defs=14** (inside the L–XL estimate 50–110); zero "sorry"/`native_decide` tokens; no other file edited.
- Parent module build green, independently reproduced (3,632-job closure).
- Parent axiom checks: `friedrichsOperator_isSelfAdjoint`, `friedrichsOperator_representation`, `friedrichsOperator_semibounded`, `friedrichsSqrt_kato_identity`, `friedrichsSqrt_isSelfAdjoint` — each on exactly `[propext, Classical.choice, Quot.sound]`. (Checker note: the module's `section`s do not prefix declaration names; an axiom check addressed to section-qualified names fails with unknown constants — recorded for future bricks.)

## Census

10,162 → **10,224 strict** / 10,239 → **10,301 attribute-inclusive** / 344 → **345 modules** (delta +62 strict, +1 module). README badge and body both updated at this landing and verified against the committed README.

## Backers since last landing

No change to the backer roll since the last landing.
