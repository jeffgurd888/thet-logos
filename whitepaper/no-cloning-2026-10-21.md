# NoCloning — qubit gates and the finite no-cloning theorem (breakdown-ledger entry B12)

**Verdict: STANDS WHOLE (T1).** Breakdown-ledger entry **B12 lands**:
the module's theorems are machine-checked T1, and per the scoping
draft's note to the Landing Pad they are *stage theorems* — true of
any finite Hilbert space, with the stage assumption (a composite
obeying the tensor inner-product law) cited in the statements
themselves. Compiled green 2026-10-21 (`lake build
ThetLogos.NoCloning`, 3,186 jobs, 0 errors), parent-verified on the
exact shipped text: `.olean` present, strict recount 18,
incompleteness census 0 on comment-stripped source, axioms on the
six checked headline theorems standard only (`propext`,
`Classical.choice`, `Quot.sound`).

Module: `lean/ThetLogos/NoCloning.lean` — 18 strict
theorems/lemmas, 7 defs, 0 `@[simp]` declarations. Program totals
move **3,350 → 3,368 strict** (3,390 → 3,408 attribute-inclusive),
**119 → 120 counted modules**.

## What is proved

The abstract core (any complex inner product spaces `V`, `W`; the
composite is any map `t : V → V → W` satisfying the tensor
inner-product law; the cloning map `U` is assumed only to preserve
inner products — linearity is not needed and not assumed):

- `cloning_inner_eq` — any cloning datum forces
  `⟨ψ,φ⟩ = ⟨ψ,φ⟩·⟨ψ,φ⟩` for every pair. The whole content of the
  no-cloning proof, isolated as an identity (four lines of calc).
- `cloning_inner_eq_zero_or_one` — hence every pair's inner product
  is 0 or 1 under a cloning datum.
- `no_cloning` — as soon as two states have inner product different
  from both 0 and 1, no cloning datum exists. Finite case, closed.

The concrete kill:

- `no_cloning_euclidean` — in `EuclideanSpace ℂ (Fin 2)`, the pair
  `|0⟩ = (1, 0)` and `|+⟩ = (1/√2, 1/√2)` has inner product `1/√2`,
  which is neither 0 nor 1 (both facts proved in-module); therefore
  no composite map, no inner-product-preserving `U`, and no blank
  state can clone. The draft's primary `PiLp.inner_apply` route
  compiled; the documented fallback was not needed.

The gates (concrete matrices on ℂ², unitarity as equation pairs
`M * Mᴴ = 1 ∧ Mᴴ * M = 1`):

- Pauli X, Y, Z and Hadamard: `M² = 1` for each (`pauliX_sq`,
  `pauliY_sq`, `pauliZ_sq`, `hadamard_sq`), and each is unitary
  (`pauliX_unitary`, `pauliY_unitary`, `pauliZ_unitary`,
  `hadamard_unitary`).
- Gate actions: `X|0⟩ = |1⟩`, `X|1⟩ = |0⟩`, `Z|1⟩ = (0, −1)`
  (phase flip), `H|0⟩ = |+⟩` — the same `|+⟩` that kills cloning
  above.

## Verification record

- Drafted 2026-10-20 under an UNVERIFIED header (B12 first attack);
  compiled 2026-10-21 after the WindingRing and FibonacciReturn
  landings. Green at 3,186 jobs. Header flipped to VERIFIED only
  after the parent re-ran the targeted build on the exact shipped
  text (green, 3,186/3,186; linter notes only).
- Repairs, in the open, none touching a statement: the import path
  `Mathlib.LinearAlgebra.Matrix.Notation`; root-namespace
  `dotProduct`; explicit scalar-field argument `inner ℂ` throughout
  (this pin's `Inner.inner` takes the field explicitly, matching the
  corpus's own usage in `BosonicESA.lean`); `hadamard` marked
  `noncomputable` (it depends on `invSqrtTwo`); and one systematic
  restructure — in this pin, `simp` with `Matrix.mul_apply` /
  `Matrix.conjTranspose_apply` never fires on `Matrix.of`-wrapped
  literal matrices, while the same lemmas succeed by `rw`; the eight
  matrix-identity proofs were restructured accordingly. Fifteen
  linter warnings remain (unused simp arguments, unreachable
  `norm_num`s) — cosmetic, on record, deliberately left under the
  minimal-repair rule.
- Axiom audit (`#print axioms`): `cloning_inner_eq`,
  `cloning_inner_eq_zero_or_one`, `no_cloning`,
  `no_cloning_euclidean`, `pauliX_mulVec_ket0`,
  `hadamard_unitary` — each exactly
  `[propext, Classical.choice, Quot.sound]`. No `sorryAx`.

## Fences (on the module's face)

- Finite-dimensional throughout; a stage theorem — the composite is
  an assumed pairing law, not a derived tensor product (the Landing
  Pad's tensor-product entry stays PARTIAL: stage assumed, not
  derived; this module uses the stage, it does not build it).
- Nothing about physical devices, laboratories, or implementations.
- Spin–statistics is not touched; gate-set universality /
  Solovay–Kitaev is not touched (declared import in B12, priced
  separately).
- No-cloning says exactly what it says: inner-product-preserving
  maps on the stage do not clone. Nothing more is inferred.
