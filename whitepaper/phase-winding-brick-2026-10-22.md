# Phase-Winding brick — lift-first (Definition A) (2026-10-22)

**Verdict: STANDS WHOLE (T1).** Module `ThetLogos.PhaseWinding`
(27 strict theorems, 10 definitions including the `Lift` structure,
0 sorry, standard axioms only). Cabinet tier, NO CLAIM — not a
Yang–Mills rung, no credit toward Δ. Commissioned by Jeff 2026-10-22;
charter: `whitepaper/phase-winding-charter-2026-10-21.md` (drafted
2026-10-21, parked until Jeff's word). Anchor: `ThetLogos.FluxTwist`,
imported, unmodified.

## The encoding (route A, on the module's face)

A configuration **is** a lift: `Lift n` carries site phases
Θ : Fin (n+1) → ℝ, a closing (wrap) increment, the winding number
w : ℤ, and the closing equation Θ(last) − Θ(0) + wrap = 2π·w.
Route A's known cost is stated, not hidden: w is a property of the
lift; the principal-argument definition (route B) was not built.
The data is not free — `winding_unique` proves (Θ, wrap) determine w.

## What stands

- **T1 — compound = sum.** `Lift.winding_add`: the winding of the
  pointwise sum of two lifts is the sum of the windings, in ℤ.
  (Arbitrary-lift form: `winding_add_of_eq`.)
- **T2 — gauge invariance.** `Lift.winding_gaugeShift`: a single-valued
  shift leaves w unchanged. The substance is at the bonds:
  `step_gaugeShift` (every step moves by α(cyc k) − α k, wrap bond
  included) and `sum_step_gaugeShift` (the increments cancel around
  the ring by the cyc permutation). Constant-α corollary: no step
  moves at all.
- **T3 — phase slip = the only door.** `Lift.winding_slipShift`: a
  shift with wrap mismatch 2π·s moves w by exactly s. Master form
  `winding_shift_eq`: within shift-deformations, w moves only through
  the seam mismatch, by exactly the mismatch. Stated as algebra, not
  as a continuity or phase-transition claim.
- **T4 — FluxTwist bridge.** `fourierLift m`: the Fourier phase
  configuration (uniform bond step 2π·m/(n+1), `fourierLift_step`)
  has winding exactly m (`fourierLift_winding`); its phases are
  FluxTwist's `fourierVec m`, and `fourierVec = twistedFourierVec`
  at θ = 0 — the eigenvector of `twistedShift_mulVec_twistedFourierVec`.
  The mode index in the standing module IS the winding number of its
  phase configuration. General θ carried on the face:
  `fourierPhase_total` (ring total = θ + 2π·m) — the integer is clean
  only at θ = 0, exactly as the charter priced it.

An honest note on proof weight: under route A the three headline
equalities hold by construction of the defined operations (their
proofs close definitionally) — that is the charter's design, priced
in advance ("cheap to state, algebraic to prove"). The non-definitional
content sits where the charter put it: `winding_unique`, the bond-level
anatomy of T2/T3, the uniform-step computation of T4, and the weld
onto FluxTwist's eigenvectors.

## Fences (on the module's face)

Not an Abrikosov vortex (no manifold, no order-parameter field, no
core — this brick proves the winding atom a vortex carries, and is
never captioned as one); no knots (no crossing data), no strings or
tension, no thermal/acoustic content, no simultaneity-triad claim.

## Verification (parent, independent of the build agent)

- Candidate md5 `ee5cee685dfe1e311f1906a5ba81b574`; shipped file md5
  `80b103ad0417a5df7821d12f8c258d4b` (header status flip only).
- Own comment-stripped scan: 27 strict, 0 @[simp]-attribute
  declarations, 0 sorry, 0 admit; 10 defs.
- Own `#print axioms` on seven headlines (winding_add,
  winding_gaugeShift, winding_slipShift, winding_unique,
  winding_shift_eq, fourierLift_winding, fourierLift_step): each
  exactly [propext, Classical.choice, Quot.sound].
- In-tree build on the exact shipped text: `lake build
  ThetLogos.PhaseWinding`, exit 0, 3,121 jobs, .olean present
  (deprecation warnings only).

## Census step

Program total: **3,592 → 3,619 strict** (3,632 → 3,659
attribute-inclusive), **130 → 131 counted modules**.
