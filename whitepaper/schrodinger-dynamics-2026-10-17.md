# Schrödinger Dynamics — finite-dimensional evolution exhibit (2026-10-17)

**Verdict: STANDS.** 11/11 on the gauntlet inventory (`gauntlet-schrodinger-2026-10-16.md` §3a),
one fenced stretch shortfall (Dyson first-order term, below). Parent-verified firsthand:
build green (3,319 jobs), all 10 headline axiom checks exactly
`[propext, Classical.choice, Quot.sound]`, zero `sorry`/`admit`.

**Module:** `lean/ThetLogos/SchrodingerDynamics.lean` — 868 lines,
49 theorem/lemma declarations + 10 definitions. (Attribute-inclusive grep gives 52
`(theorem|lemma)` hits; exactly 3 are header/comment prose, disclosed.)

## Honesty clause (carried in the module header, verbatim in substance)

Finite dimensions only. The Schrödinger and Heisenberg pictures are unitarily
equivalent bookkeeping; this module takes **no interpretation position**
(interpretations are T5, per the gauntlet). Bosonic / whole-Fock-space dynamics is
FRONTIER and absent from this module. Nothing here touches the continuum
Schrödinger PDE (Pitch 4).

## What stands

- `evolOp hT t` for any symmetric operator `T` on a finite-dimensional complex
  inner product space, specialized to `FermionicFock d`: group law
  (`evolOp_add`, plus inverse identities), `evolOp_zero`.
- Unitarity: `evolOp_isometry`, `evolUnitary : H ≃ₗᵢ[ℂ] H` with inverse
  `evolOp (−t)`, and `evolOp_adjoint`.
- Eigenbasis phases and the explicit solution formula
  (`evolOp_solution_formula`): coefficients evolve by eigenphases.
- **The Schrödinger equation as a theorem:** `hasDerivAt_evolOp_apply` —
  dψ/dt = −i • Tψ — and **uniqueness** (`evolOp_unique`, coordinatewise
  integrating factor; no ODE library needed).
- Eigenspace invariance: `evolOp_map_eigenspace_le`, `evolOp_apply_mem_eigenspace`.
- **Headline application (Pitch 3 Campaign 1's interacting Hamiltonian):**
  under the exact hypotheses of `hamInt_gap_persistence`, the ground cluster and
  the high (≥ Δ/2) cluster are subspaces, each **invariant under the time
  evolution** (`groundCluster_invariant`, `highCluster_invariant`), they cover the
  space (`hamInt_clusters_cover_and_nontrivial`: ground ⊔ high = ⊤, ground ≠ ⊥).
  Campaign 1's spectral dichotomy is now a decomposition into two invariant
  subspaces: the gap persists not only under coupling but in time.
- Heisenberg side: `heisenbergEvol` with group law and the algebra-automorphism
  package; `heisenberg_equation` (dA/dt = i[H, A] in the corpus's sign
  conventions); `picture_equiv`: expectation values agree between pictures.

## Route disclosure (a deviation, stated plainly)

`evolOp` is **constructed** diagonally — spectral phases in Mathlib's
`eigenvectorBasis` — not as a literal `NormedSpace.exp` of a continuous linear
map. The gauntlet inventory's "and/or" permits this, and the operator is
*characterized* as the exponential by the Schrödinger equation plus uniqueness
(it is the unique solution operator of dψ/dt = −i•Tψ). A literal
`evolOp = NormedSpace.exp (−it•T̂)` identification was **not** proved;
priced **S** as a follow-on for anyone who wants it.

## Correction to the gauntlet's asset estimate

The gauntlet's "¾ prebuilt" verdict was right in spirit, wrong in its named
assets. The load-bearing prebuilt pieces were: (a) Mathlib's packaged spectral
theorem (`IsSymmetric.eigenvectorBasis` with real eigenvalues), (b) Mathlib's
derivative calculus, and (c) Pitch 3 Campaign 1 itself
(`hamInt_isSymmetric`, `hamInt_gap_persistence`). The two corpus assets the
gauntlet named were **not** used: `stone_finiteDim` runs the wrong direction
(it recovers a generator from a unitary group; here the group is built from the
generator), and `jointFC` was subsumed by `eigenvectorBasis`. Recorded so the
gauntlet dossier is not quoted on this point without this correction.

## Shortfall (fenced stretch, not part of the landing)

**Dyson first-order term: NOT landed.** The interaction-picture first-order term
needs interval integrals of `s ↦ heisenbergEvol (free) s (g • intOp d W)` against
the free evolution — a further **S–M** build on top of this module. Named here as
a priced follow-on; nothing in the module gestures at it.

## Program total

1,847 (through Pitch 3 Campaign 1) + 49 = **1,896 declarations**.
