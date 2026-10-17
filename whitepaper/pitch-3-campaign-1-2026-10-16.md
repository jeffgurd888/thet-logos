# Pitch 3, Campaign 1 — Fermionic Interaction — Dossier (2026-10-16)

Scoping: `whitepaper/pitch-3-interaction-scoping-DRAFT-2026-10-16.md` (§§2–4, §6).

## Verdict
**GO — Campaign 1 STANDS WHOLE.** All four tasks (A0–A3) plus the not-a-dΓ
certificate at T1. This is the corpus's **first interacting Hamiltonian**.

## Deliverable
- `lean/ThetLogos/FermionicInteraction.lean` — 1,303 lines; **58 theorems/lemmas**
  (59 grep hits; the 59th is prose in the §4 header comment, disclosed by the
  builder and confirmed on parent recount) **+ 15 definitions**; zero sorrys.
- Program total: **1,847 declarations**.

## Verification (parent agent, firsthand)
- Build green: "Build completed successfully (3297 jobs)".
- Axiom checks on `hamInt_gap_persistence`, `densityInt_not_dgamma`,
  `intOp_isSymmetric` — exactly `[propext, Classical.choice, Quot.sound]`.

## Content
- **A0:** the corpus's first operator-norm bounds — ‖a†ᵢ‖, ‖aᵢ‖ ≤ 1 as continuous
  linear maps; basis-monomial package closed under composition (every Wick
  monomial `a†ᵢ a†ⱼ aₖ aₗ` in corpus conventions).
- **A1:** interacting Hamiltonians: the general `hamInt lam W g =
  freeHamiltonian + g • intOp W` (symmetric for every coupling tensor W;
  g = 0 recovers the free Hamiltonian) and the diagonal density exhibit.
- **A2:** coefficient and row-sum bounds: every matrix coefficient and row sum
  of `intOp W` is ≤ `intBound W = 2·∑‖W i j k l‖`.
- **A3 — GAP PERSISTENCE (headline):** for `2·|g|·intBound W ≤ Δ/4`, there is a
  ground eigenvalue E₀ with |E₀| ≤ |g|·intBound W, and every eigenvalue is
  either in the ground cluster (≤ |g|·intBound W) or ≥ Δ/2 — **the free gap
  persists at size ≥ Δ/2 above the ground cluster**, eigenvalue sense,
  finite modes.
- **Certificate:** `densityInt_not_dgamma` — the density interaction equals
  `dgamma d M` for NO matrix M (every dΓ lift has additive-over-occupied-modes
  diagonal coefficients; the density term does not). "Interacting" is proved,
  not asserted.

## Honesty notes (the Concrete, exercised inside the build)
- **A scoped statement was FALSE and was caught:** §4's exact-gap claim for the
  diagonal exhibit under the weak dichotomy hypothesis fails — two zero modes
  with `U a b > 0` give an eigenvalue `g·U a b ∈ (0, Δ)`. Counterexample recorded
  in the theorem's doc-comment; the exact gap is proved under the strengthened
  no-zero-mode hypothesis, and the true weaker statements are proved instead.
- A3's transport was proved by the direct coefficient (maximal-coordinate)
  argument — the Gershgorin proof specialized to the basis — the scoping's
  priced fallback, taken openly.
- Header carries §6's clause: finite modes; eigenvalue-sense gap; matter
  self-interaction (fermions) only; no gauge field, no continuum, no Poincaré;
  NOT the interacting Yang–Mills mass gap. Parts of any Clay statement closed: 0.

## Remaining
Campaign 2 (bosonic interaction: B1 monomial/domain calculus, B2 hand-built
essential self-adjointness, B3 exact-diagonal + windowed persistence — uniform
bosonic persistence is FALSE in general, per the scoping, and is not claimed).
Route C (limit-space interaction) stays FRONTIER.
