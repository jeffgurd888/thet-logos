# Q7CR-1a — realification of factor operators and gradings

**Date:** 2026-10-30 · **Brick:** Q7CR-1a (M), per
`scoping-q7c4r4-gauntlet-2026-10-30.md` §§2–3, 5. New module:
`ThetLogos.Q7C4R4Realify`. **Verdict: LANDED FULL** (strict 24 /
defs 7, parent-verified from disk; inside the 20–35 estimate).

**Fences: NO CLAIM. Parts of any official statement closed: 0.
Dials: 0/4. No measured number is claimed by this line.**
**K-Q7CR-1 does NOT fire.**

## What landed (linear-map seat; general over factor operators)

- **The complex structure as data.** `complexStructure n` —
  pointwise multiplication by i as a real-linear map on
  `Fin n → ℂ`, with `complexStructure_sq : J ∘ₗ J = −1`. The
  realified factor remembers it was complex through J, not
  through prose.
- **Realification and its transport kit.** `realifyOp` (scalar
  restriction of a ℂ-linear operator to ℝ) with the full law
  kit — zero/one/add/neg/sub/real-smul/comp — and
  `realifyOp_comm_complexStructure`: every realified ℂ-linear
  operator commutes with J.
- **Self-adjointness transport.** Self-adjointness is stated
  for the form — symmetry w.r.t. a stated pairing, the corpus's
  own ProductTriple precedent (no adjoint operator constructed).
  The real pairing is Q7CR-0's registered pairing in general-n
  form, proved *identical* to `q7c4r4PairQ7` / `q7c4r4PairC4` at
  the factor seats (`factorPair_seven` / `factorPair_four`,
  by `rfl`). `realifyOp_selfAdjoint`: complex
  form-self-adjointness transports to real form-self-adjointness
  (the complex identity read through `Complex.re`). Bonus on the
  record: `complexStructure_skew` — J is skew-adjoint for the
  real pairing.
- **Grading transport — the kill's seat, passed.**
  `realifyOp_involutive` and `realifyOp_anticomm`: involution
  and anticommutation transport in the exact stated shape
  `γ ∘ₗ D + D ∘ₗ γ = 0` — restriction of scalars preserves `+`
  and `∘ₗ` on the nose, so there is no sign to lose. Packaged as
  the single theorem `grading_transport` (both
  self-adjointnesses + involution + anticommutation). The
  anticommutation field was **not** weakened anywhere.
- **The package.** `CplxFactorOp` and `FactorOp` structures
  (the gauntlet §5 draft adapted to this seat) and the
  constructor `FactorOp.ofCplx`, discharging every field of the
  real package from the transport kit. Nothing in the module
  instantiates a specific factor operator: D₇ in particular is
  nowhere chosen — factor operators are choices, and the
  clock-data diagonal remains measured input behind the D1
  fence, named on the module's face.

All checked theorems carry exactly
`[propext, Classical.choice, Quot.sound]`; module and full-tree
builds green.

## Caveat, carried verbatim-tier (gauntlet §2 discipline)

In finite dimension the **bounded-commutator criterion is
vacuous**: every operator on ℝ⁴⁴⁸ is bounded and every
commutator is a finite matrix. The testable content of this
line is spectrum, grading behavior, and the D² identity —
never bounded commutators. This dossier reports no vacuous
criterion as "verified."

**Census: 7,458 → 7,482 strict / 7,536 → 7,560
attribute-inclusive / 260 → 261 modules** (recounted from disk).
Q7CR-1b (the general product assembly + the D² identity +
self-adjointness w.r.t. the registered composite pairing) can
now spend this kit as priced; its headline identity is the
K-Q7CR-1 firing seat that remains.

## Backers since last landing

The backer roll (`BACKERS.md`) is unchanged since the last
landing; no new confirmed gift is on the record. Thank you to
everyone reading the stream — the corpus is free for everyone,
forever.

*End of dossier.*
