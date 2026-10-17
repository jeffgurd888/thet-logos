# The Bridge Exhibit — `L = dᵀ σ d` on a finite weighted graph (2026-10-17)

**Verdict: STANDS WHOLE — every scoped item landed, Fiedler section
included.** Parent-style verification performed firsthand by the builder:
targeted build green (**3,117 jobs**), **eight** headline axiom checks
each exactly `[propext, Classical.choice, Quot.sound]`, zero
`sorry`/`admit` in code.

**Module:** `lean/ThetLogos/BridgeLaplacian.lean` — 466 lines,
**29 theorems + 7 definitions** (count method: `grep -cE "^(theorem|lemma) "`
= 29, all line-initial, none attribute-prefixed; the 7 defs are
`dropVec`, `ohm`, `flowVec`, `diverge`, `laplacianOp`, `fiedlerSet`,
`fiedler`). The word `sorry` occurs exactly once in the file — header
prose ("Zero sorrys"), disclosed in the module. Not added to the root
import list (corpus pattern for recent exhibits); verified by targeted
build of `ThetLogos.BridgeLaplacian`.

## Provenance

Jeff's chain of 2026-10-17 (~05:03–05:07 EDT): flow/voltage dual pair →
"missing **bridge** I meant" → Faraday/Ohm placement. The exhibit is
that conversation made into bone: the translator between node
potentials and edge flows is a boundary operator, Ohm's law is the
material in the middle of the bridge, and the spectral gap (here: the
Fiedler value) is the equilibration rate. Background-algebra exhibit
in the shelf sense of `FluxTwist`/`SexagesimalClock` — **not** a
ladder rung.

## Scoped package vs landed

1. **Potentials** as `F : V → ℝ` over a generic finite vertex type `V`
   (`[Fintype V] [DecidableEq V]`; the brief's first option, chosen
   over `Fin n`). Weights `w : V → V → ℝ` are bare data; symmetry and
   nonnegativity are theorem hypotheses, never baked into defs. **STANDS.**
2. **The bridge operator** `dropVec F i j = F j - F i`: linearity
   (`dropVec_add`, `dropVec_smul`), constants have zero drop
   (`dropVec_const`), antisymmetry (`dropVec_antisymm`), and the
   telescoping path law `dropVec_telescope` (drops along
   `p 0 → … → p n` sum to `F (p n) - F (p 0)`) with the closed-path
   corollary `dropVec_telescope_closed` — the discrete Kirchhoff
   voltage law. **STANDS.**
3. **Ohm's law as the middle factor**: `ohm w X i j = w i j * X i j`,
   `flowVec w F = ohm w (dropVec F)`, flow antisymmetry
   (`flowVec_antisymm`, spends symmetry of `w`). **STANDS.**
4. **The factorization** `laplacianOp_eq_diverge_ohm_drop`:
   `laplacianOp w F = diverge (ohm w (dropVec F))`, with
   `(laplacianOp w F) i = ∑ j, w i j * (F i - F j)` and
   `diverge X i = ∑ j, X j i`. A genuine theorem, **not** `rfl`: the
   divergence gathers transposed entries, so the two sides agree only
   after the symmetry of `w` is spent. Corollary
   `laplacianOp_eq_diverge_flow`. **STANDS.**
5. **Kirchhoff current law** `sum_laplacianOp_eq_zero`:
   `∑ i, (L F) i = 0` for symmetric `w`. **STANDS.**
6. **Thomson / dissipation**: `bilin_identity`
   (`2 ∑ᵢ Gᵢ(LF)ᵢ = ∑ᵢⱼ w i j (Fᵢ-Fⱼ)(Gᵢ-Gⱼ)` — the factor is 2, via
   symmetrization), its diagonal `energy_identity`
   (`2·energy = ∑ᵢⱼ w i j (Fᵢ-Fⱼ)²`), the half form `energy_eq_half`,
   and `energy_nonneg` for `0 ≤ w`. **STANDS.**
7. **Self-adjointness** `laplacianOp_symm_form`:
   `∑ᵢ Gᵢ(LF)ᵢ = ∑ᵢ Fᵢ(LG)ᵢ`. **STANDS.**
8. **Kernel**: `energy_eq_zero_iff` (zero energy ⟺
   `∀ i j, w i j * (F i - F j)^2 = 0`), `eq_of_energy_eq_zero`
   (constancy across every conducting edge), the all-positive
   corollary `eq_const_of_energy_eq_zero` (zero energy ⟹ `F`
   constant), and `laplacianOp_const` (constants are killed by `L`).
   **STANDS.**
9. **Fiedler value** `fiedler w := sInf (fiedlerSet w)` over mean-zero
   unit-norm potentials: the variational bound `fiedler_le_energy`
   and `fiedler_nonneg` both **STAND** — the pre-authorized PARTIAL
   fallback (price the bound) was **not** needed. Edge cases handled
   honestly: for `|V| ≤ 1` the admissible set is empty, `sInf ∅ = 0`,
   and both theorems stay true (the nonneg proof case-splits on
   emptiness). Bonus landed beyond scope:
   `fiedlerSet_nonempty_of_exists_ne` — for two distinct vertices the
   admissible set is inhabited, witness `(δ_a - δ_b)/√2` proved
   mean-zero and unit-norm. Attainment (eigenvector statement) is NOT
   claimed; it belongs to the priced follow-on.
10. **Equilibria / conservation**: `laplacianOp_const` (constants are
    equilibria of `Ḟ = -L F`) and `sum_laplacianOp_eq_zero` read as
    conservation of the total/mean. **STANDS.**

## Axiom audit (all exactly `[propext, Classical.choice, Quot.sound]`)

`laplacianOp_eq_diverge_ohm_drop`, `energy_identity`, `energy_nonneg`,
`sum_laplacianOp_eq_zero`, `fiedler_le_energy`, `fiedler_nonneg`,
`eq_const_of_energy_eq_zero`, `fiedlerSet_nonempty_of_exists_ne`.

## Deviations and accommodations (complete list)

- **Vertex type**: generic `V` with `[Fintype V] [DecidableEq V]`
  (brief's preferred option) rather than `Fin n`.
- **Sign convention**: one convention fixed throughout, disclosed in
  the header — `dropVec` is the coboundary orientation
  `F j - F i`; the brief's alternative orientation `F i - F j` is
  realized through the transposed (inflow-gathering) divergence, which
  is what makes the factorization produce
  `(LF) i = ∑ j, w i j (F i - F j)`. Kirchhoff's voltage law is
  convention-free (sums are `0` either way).
- **Telescoping form**: paths as functions `p : ℕ → V` with
  `Finset.range n` sums (the brief's suggested clean form), not list
  zip.
- **No `maxHeartbeats` overrides, no accommodations in proofs.** The
  build emits only linter warnings of one kind: unused section
  instance variables (`[Fintype V]`/`[DecidableEq V]`) in the pure
  drop lemmas, which do not sum. Cosmetic; left as-is.
- **Relation to Mathlib** (stated in the header): Mathlib's
  `SimpleGraph.lapMatrix` is the unweighted `0/1` simple-graph
  Laplacian (deg − adj matrices, with PSD and kernel results). This
  exhibit differs in kind: arbitrary symmetric real weights,
  function-level operators (no matrices), and the explicit
  `d / σ / dᵀ` factorization + Kirchhoff package + Fiedler
  variational bound as one exhibit. No novelty over Mathlib is
  claimed beyond that packaging and the weighted factorization.

## Priced, NOT attempted (named in the module header)

- **Faraday's law** — needs cycle/flux data (`2`-chains, a flux
  variable); the priced second storey of the bridge.
- **Exponential decay** of `Ḟ = -L F` at the Fiedler rate (matrix
  exponential / eigenbasis argument), including attainment of the
  variational infimum.
- Everything else the header lists: Maxwell theory, continuum limits,
  any Yang–Mills content.

## Tier

T1 finite weighted-graph algebra, whole. The three readings
(resistor network / graph heat / DeGroot consensus) are recorded as an
**equation identity** — the same operator equation read three ways —
claiming nothing about real circuits, real heat, or real electorates.
