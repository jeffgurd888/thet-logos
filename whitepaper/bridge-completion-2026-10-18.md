# Bridge spectral completion — dossier (2026-10-18)

**Module:** `lean/ThetLogos/BridgeCompletion.lean` (1,194 lines).
**Build:** targeted `lake build ThetLogos.BridgeCompletion` green,
3,316 jobs, `.olean` present.
**Counts:** 60 strict theorems/lemmas (line-initial
`^(theorem|lemma) ` on comment-stripped source), 0 `@[simp]`,
attribute-inclusive = strict = 60. Zero `sorry`/`admit` on
comment-stripped source. Program total: 3,041 + 60 = **3,101 strict**.
**Axioms:** `#print axioms` on the nine headlines
(`exists_fiedler_minimizer`, `laplacianOp_fiedler_minimizer`,
`fiedler_le_of_eigenvector`, `heatFlow_hasDerivAt`, `heatFlow_decay`,
`heatOp_zero`, `circulation_eq_zero`, `faraday_package`,
`lapLin_isSymmetric`) — standard three only
(`propext`, `Classical.choice`, `Quot.sound`).

Subject: the priced follow-ons to the Bridge exhibit
(`BridgeLaplacian.lean`, STANDS WHOLE 2026-10-17), as priced in
`gauntlet-parked-fleet-2026-10-17.md` §7. `BridgeLaplacian.lean` is
NOT modified; everything here is a new module about its objects.

## Verdicts per deliverable

### (1) Attainment (priced S) — STANDS WHOLE (T1)

`exists_fiedler_minimizer`: for two distinct vertices, the Fiedler
infimum of `BridgeLaplacian` is attained — some admissible
potential (mean-zero, unit-norm) has energy exactly `fiedler w`,
and it minimizes the energy over the admissible set.

Route, exactly as priced: the admissible set `fiedlerAdmissible`
(mean-zero ∩ unit sphere in `V → ℝ`) is closed (`isClosed_eq` on the
two defining conditions, both continuous) and bounded (every
coordinate in `[−1, 1]`), hence compact in finite dimensions
(`Metric.isCompact_of_isClosed_isBounded`); the energy is
continuous (a polynomial in the coordinates); attainment is
`IsCompact.exists_isMinOn`. Nonemptiness is extracted from
`BridgeLaplacian.fiedlerSet_nonempty_of_exists_ne`. That the
attained value *equals* `fiedler w` (not merely ≥ it) closes by
`le_csInf` against the admissible energies on one side and
`fiedler_le_energy` on the other.

### (1b) The minimizer is an eigenvector; λ₂-identification (part of the priced decay package) — STANDS WHOLE (T1)

`laplacianOp_fiedler_minimizer`: the attained minimizer satisfies
`laplacianOp w F i = fiedler w * F i` pointwise — `fiedler w` is an
eigenvalue of `L` with an admissible eigenvector.

Route (the gauntlet's "one real lemma" — the finite-dimensional
Lagrange condition): the first-variation lemma
`bilin_eq_zero_of_minimizer` feeds the normalized perturbation line
`F + t • G` (renormalized by `s = √(1 + t²‖G‖²)`, which uses
orthogonality `∑ G i * F i = 0` to keep the norm at
`1 + t²∑ G i²`) into the variational bound, extracts the explicit
quadratic inequality
`0 ≤ 2t·bilin + t²·(energy G − energy F · ∑ G i²)` for all `t`, and
kills the linear coefficient at `t = −bilin/(|C| + 1)`. Pairing
against arbitrary mean-zero `G` (its `F`-component subtracted
first) shows `L F − (fiedler w) • F` is a constant vector; summing
kills the constant (the total current `sum_laplacianOp_eq_zero`
vanishes, the mean of `F` vanishes, and `|V| ≥ 2`).

`fiedler_le_of_eigenvector`: every mean-zero eigenvector of
`laplacianOp` has eigenvalue `≥ fiedler w` (normalize it and apply
`fiedler_le_energy`). Together with attainment: **`fiedler w` IS
the smallest eigenvalue of `L` on the mean-zero subspace** — an
eigenvalue, attained, and a floor for the others.
`eigenvalue_nonneg_of_eigenvector` records that eigenvalues of `L`
are nonnegative in general.

**Deviation from the gauntlet, named:** none of this needs a
connectivity hypothesis, and none is made. If the graph is
disconnected in the support of `w`, then `fiedler w = 0` and every
statement remains true verbatim (the minimizer is a
component-constant potential). The gauntlet did not ask for
connectivity; the module follows the gauntlet.

### (2) Exponential decay (priced M) — STANDS WHOLE (T1)

The flow is defined eigenbasis-wise, a direct port of
`SchrodingerDynamics`' `evolOp` pattern with real decaying
exponentials in place of phases: `heatOp hsymm t` multiplies the
`k`-th eigenbasis coefficient (in Mathlib's spectral basis of the
symmetric operator `lapLin w` on `EuclideanSpace ℝ V`) by
`Real.exp (−(lapEig k) · t)`.

- `heatFlow_hasDerivAt`: the derivative theorem — the curve
  `s ↦ heatOp s x` has derivative `−(lapLin w (heatOp t x))` at
  every `t` (the bridge heat equation `Ḟ = −L F`, as a
  `HasDerivAt` in the Euclidean norm). The gauntlet named
  "transport of `laplacianOp` through its bilinear form" as the
  friction; in the event the transport is packaged once, up front,
  as `lapLin` (conjugation by `WithLp.linearEquiv`, the corpus's
  `FermionicFock` pattern) with symmetry `lapLin_isSymmetric`
  transported from `laplacianOp_symm_form`, and the derivative is
  then a finite sum of scalar exponential derivatives.
- `heatOp_zero`: the initial condition `heatOp 0 = id`.
- `heatFlow_decay`: for `t ≥ 0`,

      ‖F(t) − mean‖ ≤ exp (−(fiedler w) · t) · ‖F₀ − mean‖,

  where `mean` is the constant vector at the mean of `F₀`
  (`euclidMean`). Proof: `heatOp` fixes the mean vector
  (`heatOp_eq_of_lapLin_eq_zero` — `L` kills constants, zero modes
  carry the factor `exp 0 = 1`), so the flow of the difference is
  the difference of the flows; then Parseval
  (`OrthonormalBasis.sum_sq_norm_inner_right`) reduces the estimate
  to a termwise inequality. The one non-formal input is the mode
  alternative: a mode with nonzero eigenvalue is mean-zero as a
  potential (orthogonal to the constants, since `L` kills them), so
  `fiedler_le_of_eigenvector` bounds its eigenvalue below by
  `fiedler w` and it decays at least at the Fiedler rate; a zero
  mode is invisible to the mean-removed data **unless**
  `fiedler w = 0` (`fiedler_eq_zero_of_inner_ne_zero`: the zero
  mode's own mean-removal is a mean-zero zero-mode, forcing
  `fiedler ≤ 0`), in which case the rate factor is `1` and no
  invisibility is needed. No connectivity hypothesis anywhere; the
  estimate is sharp verbatim in the disconnected case too.

### (3) Faraday storey (priced S–M, OPTIONAL) — LANDED (T1, as scoped)

The gauntlet ruled `LatticeGauge` does not cheapen this (its
plaquettes are group-valued holonomies on a cubical torus;
Bridge circulation is additive telescoping of real drops), and the
module follows that ruling: the face structure is built
Bridge-locally. §9 provides: `GraphFace` (a face as an ordered
quadruple of vertices), `circulation` / `edgeCirculation` /
`faceFluxOf` (flux through a face defined as its boundary
circulation — the discrete Stokes definition), the identity
`faceFluxOf_dropVec` / `circulation_eq_zero` (the flux of a
potential field through any face is zero — drops telescope around
the closed loop; the graph's `d² = 0`), and `inducedEMF` with
`inducedEMF_of_hasDerivAt` / `faraday_package` (EMF = −dΦ/dt as a
definition-theorem pair, the theorem being the derivative
computation). Fenced in the module header: graph-Faraday
bookkeeping on the finite graph, NOT Maxwell theory; no coupled
induced-field dynamics is built or claimed.

## Fences (what is NOT claimed)

- Finite weighted graph only: finite vertex type, symmetric real
  weights, nonnegativity a hypothesis where needed. No continuum
  limit, no infinite graph, no Yang–Mills content.
- The decay is for the finite semigroup defined here; `fiedler w`
  is the finite graph's spectral gap in the eigenvalue sense
  identified above.
- `BridgeLaplacian`'s three readings (resistor network / graph
  heat / DeGroot consensus) remain an equation identity, not a
  claim about the world.
- Faraday (§9) is definitions plus the two identities named; it is
  not a dynamical coupling of the flux to `L`.

## Method notes (for the record)

- `lapLin` is built by `LinearEquiv.conj` over
  `WithLp.linearEquiv 2 ℝ (V → ℝ)` (`euclEquiv`), the exact pattern
  of `FermionicFock`'s `fockEquiv`; component identities through
  the wrapper are `rfl`, as in that module.
- In this pinned Mathlib, `OrthonormalBasis.orthonormal` returns
  the `(∀ i, ‖b i‖ = 1) ∧ Pairwise …` form; `orthonormal_iff_ite.mp`
  consumes it whole.
- The first-variation argument deliberately avoids Mathlib's
  `deriv` machinery for the perturbation: the quadratic inequality
  in `t` is extracted explicitly, so no differentiability
  side-conditions are needed anywhere in §3.
