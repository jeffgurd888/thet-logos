# Gram clause — the regrouped route: SCOPING CHARTER

**Date:** 2026-10-24. **Status: SCOPING ONLY.** This document
designs a proposed route and prices it. It commissions nothing,
builds nothing, and proves nothing. Every construction below is a
design hypothesis at FRONTIER tier until its rung lands.

**NO CLAIM.** Parts of any official Clay statement closed by this
document: 0. Stage 1b-B label unchanged: positivity **T1 for
U(1)** (Route C); general (G, ρ) **OPEN**. Census unchanged:
4,339 strict / 4,388 attribute-inclusive / 143 modules.

## Background in one paragraph

The integrated criterion `osForm_nonneg_of_gram_integrated`
(`LatticeGramSeries`) stands: any countable family (A, B, Ξ) with
pointwise `hgram`, the two marginals `hmargA`/`hmargB` against the
*same* Ξ at real nonnegative dampings dA, dB, and summable bounds
gives OS positivity at general (G, ρ), sign-free in β. Two
attempts to exhibit a model family have stopped on proved
obstructions: T4c (word-entry features — the stratum factor is
tensor-shaped, not word-shaped) and T4c′ (factored occurrence
features — the strict factor's two readings are the transposed
entries (k, a) and (j, i) of one matrix, and no single shared φ₀
carries both). This charter scopes the remaining named direction:
a **regrouped, non-token decomposition** of the same kernel
series.

## §1 Design constraints

Any family that models the criterion at d ≥ 2 must satisfy all of
the following. Each is forced by a proved obstruction or by the
criterion's own statement; none is a preference.

- **C1 — Occurrence-shaped stratum dependence.** A feature's
  stratum factor must be an occurrence (tensor) coefficient of a
  joint occurrence datum, never a word entry. Word entries carry
  only path monomials; the closed-half arc monomial
  `(ρC⁻¹)_{j k}·(ρA)_{a i}` with k ≠ a is not one (T4c).
- **C2 — Joint data for global products.** `exp(−S₀)` is a product
  over all crossing plaquettes; the family's stratum factor at a
  multi-plaquette configuration must be the occurrence
  coefficient of the disjoint-union (joint) datum, since a product
  of word entries is an occurrence coefficient, not a word entry
  (T4c, second failure).
- **C3 — One hinge per scalar index, proportional readings.** For
  each scalar index i, the marginals at arbitrary observables f
  pin the two marginal densities pointwise:
  `dA i • Ξ i = S^A_i`, `dB i • Ξ i = S^B_i` as functions of the
  strict configuration. Hence S^A_i and S^B_i must be
  proportional over ℝ with a **nonnegative constant ratio**. A
  design in which the two halves read one strict matrix through
  transposed entries (k, a) vs (j, i) violates this unless the
  two readings are merged *before* the pin applies (T4c′,
  face one).
- **C4 — Independence of the planes' data.** The index set must
  range over independent per-plaquette token data on both
  planes. Determining one plane's tokens from the other's (dual
  transport as an assembly rule) sums only diagonal
  configurations and drops pointwise-nonzero off-diagonal terms
  of the product series (T4c′, face two). Regrouping may
  partition and recombine the existing summands; it may not tie
  or drop configurations.
- **C5 — `hgram` is pointwise and exact.** Each scalar summand
  `conj(B i u)·A i y` is a pure tensor, and the sum must equal
  the kernel on the nose. A sum of pure tensors may serve as one
  index only if it is itself a pure tensor; the permitted
  recombinations are exact algebraic identities among the
  summands (e.g. polarization), never integral-level or
  almost-everywhere substitutes.
- **C6 — Domination must survive.** Per-index bounds CA, CB with
  `Summable (CA · CB)` are required. Domination was verified
  feasible for the factored occurrence family in the T4c′ design
  pass (feature bounds ≤ √w per side at β ≥ 0), so admissible
  regroupings are the triangle-inequality-stable ones.
- **C7 — Sign discipline.** Dampings dA i, dB i are real and
  ≥ 0, per index. All complex phases (averaging coefficients
  γ, ε-symbols) must live inside the features or Ξ, never in the
  dampings; every proportionality ratio in C3 must be a
  nonnegative real, constant in the strict configuration.
- **C8 — The d = 1 shadow.** At d = 1 the pairs (k, a) and
  (j, i) coincide, the mirror transport is the identity on
  scalars, and the construction must reduce to Route C's closed
  family. A design that does not specialize to the landed U(1)
  proof is wrong-shaped on its face.

## §2 The candidate regrouped construction (DESIGN HYPOTHESIS)

**Notation.** A *token configuration* j assigns independent
token data (tensor power, loop tuples, orientation) to every
crossing plaquette (C4). Its kernel summand is a pure tensor with
occurrence features (C1, C2); its *marginal densities* are the
strict-half functions S^A_j, S^B_j defined by the pins,
`∫ A_j·(f∘restrict) = ∫ S^A_j·f` and likewise for B — in the
factored family, S^A_j = γ^A_j·Φ^A_j and S^B_j = γ^B_j·Φ^B_j.
Reflection Θ acts on configurations (link reflection, `Fin.rev`,
conjugation) and induces the *density transport* T on strict
densities, with

  `S^A_{Θj} = T(S^B_j)`,   `S^B_{Θj} = T(S^A_j)`

— the content of the landed occMat dual transport
(`GramMirror.integral_occMat_dual`, `occGamma_arc_dual_conj`),
restated at density level. T4c′ face one is the statement
S^A_j ∦ S^B_j at d ≥ 2: the two readings of one strict matrix
are the transposed entries (k, a) and (j, i).

**The briefed form dies on paper.** Indexing by reflection
orbits, one scalar index per orbit {j, Θj}, fails twice:

1. *Factorization (C5).* The orbit's kernel contribution
   `conj(U_j)Y_j + conj(U_{Θj})Y_{Θj}` is a sum of two pure
   tensors, hence not of the form `conj(B)A` unless the two are
   proportional — face one says they are not.
2. *Splitting does not help.* Indexing by (orbit, ε) with one
   shared Ξ per orbit re-imposes C3 on each summand separately:
   the pins are per scalar index, so S^A_j, S^A_{Θj}, S^B_j,
   S^B_{Θj} would all have to be proportional to the same Ξ —
   face one verbatim. A fiber/pairing-matrix criterion fares no
   better: the swapped pairing has OS quadratic form with matrix
   `[[0, ab′], [a′b, 0]]`, indefinite unless the cross terms
   vanish. Positivity does not decompose over orbits with
   cross-pairing, and adopting a new criterion would abandon the
   landed one besides.

**The surviving variant: polarization per mirror pair.** Apply
the regrouping not to global configurations but, via the
Hadamard transform over the product of per-pair reflection
groups, to each mirror pair of crossing plaquettes
independently. For a pair with token data (t₋, t₊) (lower and
upper tokens, independent), replace the two summand features by

  `A_± = (Y ± Y^Θ)/√2`,   `B_± = (U ± U^Θ)/√2`,

Θ the pair's mirror flip. Then
`conj(B_+)A_+ + conj(B_−)A_− = conj(U)Y + conj(U^Θ)Y^Θ`
pointwise — the parallelogram identity — so C5 holds exactly;
the Hadamard transform over all pairs is orthogonal, covers
every configuration exactly once, and ties nothing (C4).
Marginal densities factorize over pairs (stratum integrals of
joint data factor over the disjoint-union slots; marginals are
linear in the feature), so C3 for the global family reduces to
C3 **per mirror pair**. The per-pair densities of the ± features
are, with P := s^A(t₋, t₊) and Q := s^B(t₋, t₊) the pair's
factored marginal densities,

  `s^A_± ∝ P ± T Q`,   `s^B_± ∝ Q ± T P`.

**THE CRUX IDENTITY (symmetrized proportionality).** For every
mirror pair, every independent token datum (t₋, t₊), and both
signs: there exist nonnegative reals λ₊, λ₋ (depending on the
pair datum, constant in the strict configuration) with

  `Q + T P = λ₊ · (P + T Q)`,   `Q − T P = λ₋ · (P − T Q)`

as functions on the strict half. Equivalently: the pairs
(P + TQ, Q + TP) and (P − TQ, Q − TP) are each proportional
over ℝ≥0. If the crux holds, set Ξ_± := (P ± TQ)/norm and
dA_±, dB_± from λ_±; C6 follows from the factored bounds by the
triangle inequality; C8 holds since at d = 1, T = id and P = Q.
If the crux fails for any single pair datum, no regrouping of
this shape models the criterion — the obstruction will have
been promoted from the factored family to the whole
reflection-regrouping class.

## §3 Rung R0 — the counterexample test (paper; price S)

**Task.** Evaluate the T4c′ killer instance against the
regrouped family of §2, on paper, before anything is built.
Instance: (G, ρ) = (SU(2), defining), one mirror pair of
crossing plaquettes active, all other pairs at power 0 (their
± densities are the constant 1 on both sides and drop out of
every proportionality). Pair datum: lower tokens = two direct
copies with loop tuples (0,0,0,1) and (1,1,1,0); upper tokens =
power 0. Factored densities (T4c′ dossier): γ_A = −1/4,
γ_B = 1, Φ^A ∝ (ρD⁻¹)₁₀(ρD⁻¹)₀₁, Φ^B ∝ (ρD⁻¹)₀₀(ρD⁻¹)₁₁, where
D is the lower plaquette's strict link. Compute the four
symmetrized densities P ± TQ and Q ± TP as functions on the
pair's strict configuration space (the lower D-link and its
mirror link range independently over SU(2); the transport T
evaluates the mirrored pattern on the mirror link), and test
the crux: proportionality over ℝ≥0 of each ± pair, as functions
— evaluation at a minimum of two strict configurations (first:
both strict links diag(i, −i), where P vanishes and Q does
not; second: a generic SU(2) point, e.g. lower link
diag(i, −i) with mirror link a non-diagonal unitary), plus the
wedge determinant on the nose for this finite instance.

**Pre-registered kill criterion.** If either ± pair of
symmetrized densities is separated at any tested configuration
— the 2×2 determinant
`[s^A_±(z₁) s^A_±(z₂); s^B_±(z₁) s^B_±(z₂)] ≠ 0` for the two
named configurations, or a sign/vanishing mismatch forcing
λ_± < 0 or λ_± z-dependent — the regrouped route **dies at
R0**, the verdict is published as a third obstruction (the
promotion of T4c′ from the factored family to the
reflection-regrouping class), and no rung below is commissioned.
The route proceeds past R0 only if both ± pairs are
proportional over ℝ≥0 at this instance with the proportionality
verified as a function identity, not at isolated points.

## §4 Rung ladder R1–R4 (prices; kill criteria)

- **R1 — The crux identity in Lean. Price: L.** Formalize the
  density transport T at the joint-datum level (the landed dual
  transport is per-plaquette) and prove symmetrized
  proportionality for arbitrary pair data and all tensor powers:
  the ± hinges Ξ_± exist with real nonnegative dampings. This is
  the route's mathematical center; everything else is assembly.
  *Kill:* the crux fails for any datum class beyond R0's
  instance, or T at joint scale is not the involution the
  per-plaquette transport suggests (sign/order defects under
  `Fin.rev`), or proportionality holds only at tensor powers
  ≤ some bound — a finite-order closure proves nothing, since
  the criterion consumes the full series.
- **R2 — Family assembly + marginals. Price: L.** Define the
  regrouped index set (signed configurations: per-pair token
  data × per-pair sign), the features A_±, B_±, hinges Ξ_±, and
  bounds CA, CB; prove `hmargA`/`hmargB` from the landed
  factored marginals plus R1, for **all** bounded measurable
  observables f. *Kill:* the pins hold only for a restricted
  class of f; the signed index set is not countable in the
  corpus's configuration language; measurability of the ±
  features fails.
- **R3 — `hgram` for the regrouped family. Price: M.** The
  per-pair parallelogram identity is elementary; the content is
  the regrouped `tsum`: the Hadamard transform over the
  reflection group of pairs, applied to an absolutely summable
  family, with the orbit partition of the product index set made
  exact in Lean. *Kill:* absolute summability of the regrouped
  family fails (C6 was verified for the factored family, not
  this one), or polarization cross-terms survive at some tensor
  power.
- **R4 — Discharge. Price: S.** Apply
  `osForm_nonneg_of_gram_integrated` verbatim; flip the Stage
  1b-B label to STANDS at general (G, ρ). *Kill:* any hypothesis
  mismatch at the application site (β is sign-free in the
  criterion and hN is corpus-standard, so a mismatch here means
  an upstream rung silently changed the target).

Total price if the route runs clean: **S + L + L + M + S**.
The expected failure point is R0/R1 — by design: the route is
priced so its cheapest rungs carry its likeliest kills.

## §5 Honest unknowns

- **U1 — The crux may simply be false (highest risk).**
  Symmetrized proportionality for *all* pair data is a strong
  identity. The transported terms TQ, TP live on the mirror
  pair's strict links, so each ± density mixes two disjoint
  strict coordinates; proportionality of such products is
  fragile and could survive R0's instance while failing the
  next datum. R0 is a necessary gate, not evidence of truth.
- **U2 — Face two in mirror form.** The orbit partition covers
  every configuration, but each ± feature couples a
  configuration to its mirror *inside one index*. The
  criterion's marginals integrate over one half at a time, which
  is compatible with this — but Ξ_± is a strict-half function
  built from both planes' token data, and its explicit form is
  unbuilt; if any assembly step secretly needs per-plane
  independence of the *features* (not just the index set), the
  tying re-enters there.
- **U3 — Ratio constancy.** The γ coefficients are constants
  per datum, but after ± mixing the candidate ratio λ_± is a
  ratio of *sums* of terms with different strict dependence.
  C7 demands it be constant and ≥ 0. Test-point agreement can
  mask z-dependence; R0 therefore requires the identity as
  functions on the instance (finite representation: matrix
  coefficients, checkable on a basis), and R1 must prove
  constancy, not sample it.
- **U4 — Tensor powers.** R0 exercises the β¹ / two-copy
  instance. Proportionality could hold at low powers and fail
  at power 3; R1's kill criterion is written to catch exactly
  this, but a route that closes only finitely many orders is
  worthless and must not be reported as partial progress toward
  the discharge.
- **U5 — Joint-level transport.** T is landed per plaquette
  (`integral_occMat_dual`, `coeff_dual`, `occGamma_arc_dual_conj`)
  and *asserted* at joint-datum level in §2. The joint stratum
  group is a product, so the extension is expected — but
  `Fin.rev` path combinatorics at joint scale has surprised
  this campaign before (the T4c sandwich was one such
  surprise).
- **U6 — Scope of a positive outcome.** Even a clean run
  closes only Stage 1b-B at general (G, ρ) through this
  criterion. It does not advance Stage 3c, Stage 4, or any
  official statement; the label change in R4 is a stage label,
  nothing more.

---

**Charter ends.** What would commission work: Jeff's word on
this charter, rung by rung, R0 first. Until then the record
stands where the T4c′ dossier left it — criterion T1, factored
family killed at the strict factor, U(1) closed, general
(G, ρ) OPEN, and the regrouped route scoped, priced, and
unclaimed. **NO CLAIM.**
