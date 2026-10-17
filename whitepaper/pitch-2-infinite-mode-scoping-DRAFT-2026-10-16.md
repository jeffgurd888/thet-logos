# Pitch 2 Scoping — The Infinite-Mode Limit (Direct-Limit Fock Construction)

**DRAFT SCOPING — NOT A DOSSIER. Nothing in this document is built, proved, or
claimed. It is a priced build order for Jeff's greenlight, written 2026-10-16
after the Γ(U) functor campaign closed Rung 10.**

Labels that govern every line below, now and after any landing: this pitch is
about the **free** theory. Standing whole, it buys **no interaction, no gauge
dynamics, no continuum Poincaré, and no part of the Yang–Mills mass gap.** It
removes exactly one word from the ladder's labels — "finite modes" — and
replaces it with "countably many modes." Everything else on the frontier
stays where it is (§5).

Effort classes used below: **S** = one small module section (days);
**M** = one focused module (week scale); **L** = a campaign (Γ-functor
campaign scale, ~1,000+ lines); **XL** = new-infrastructure scale, open-ended.

---

## 1. What exists now — the ingredients a direct limit would consume

All names are exact, from the modules as they stand at remote `6728ccde`.

### Bosonic side (Rungs 8 / 8B / 10 + Γ campaign)

- Modes `Fin d`; configurations `Config d := Fin d →₀ ℕ`
  (`Finsupp (Fin d) ℕ`), `ThetLogos/lean/ThetLogos/BosonicFock.lean`.
- `BosonicFock d := lp (fun _ : Config d => ℂ) 2` — already an ℓ² space over
  the configuration index set, with basis `boseE d c := lp.single 2 c 1`,
  `boseE_orthonormal`, and the dense finite-particle domain
  `Dom d := Submodule.span ℂ (Set.range (boseE d))`.
- Coefficient transport: `boseEquiv d : (Config d →₀ ℂ) ≃ₗ[ℂ] Dom d`,
  `boseRepr d`.
- Creation/annihilation `adag d i`, `ann d i` on `Dom d`; CCR and the full
  adjoint relation (Rung 8B, `BosonicAssembly.lean`); `numberOp`;
  `tot c := ∑ i, c i`; sectors `sectorSub d n` with `sector_orthogonal`.
- `dgammaBos d M` on `Dom d` with `dgammaBos_one` (`dΓ(1) = numberOp`),
  `dgammaBos_adjoint`, `dgammaBos_basis_diag`, sector preservation
  (`dgammaBos_mem_domSector`, `domSector d n`) — `BosonicSecondQuant.lean`.
- Free Hamiltonian `freeHamiltonianBos d lam := dgammaBos d (onePartDiagBos
  d lam)`, with the derived gap: `free_gap_dichotomy_bos`,
  `freeHamiltonianBos_eigenvalue_gap`, expectation formula
  `freeHamiltonianBos_expectation` — eigenvalues on `Dom d` are `0` or `≥ Δ`
  whenever every `lam i` is `0` or `≥ Δ`.
- Γ: `gammaBos d M : Module.End ℂ (Dom d)` built from the kernel
  `gammaKernel d M c' c = perMinor d M c' c / (normFactor d c * normFactor d
  c')` — `BosonicGamma.lean`; functoriality closed by the campaign:
  `gammaBos_mul`, `gammaBos_one`, `gammaBos_diagonal_basis`,
  `gammaBos_adjoint`, `gammaBos_comp_conjTranspose`,
  `gammaBos_conjTranspose_comp`, `gammaBos_isometry`, on the kernel
  identities `perMinor_mul` (permanent Cauchy–Binet for repeated indices)
  and `permanent_fiberIndicator_configEnum` — `BosonicGammaFunctor.lean`.
  **Note: `perMinor`/`gammaBos` are stated for square matrices only**
  (`M : Matrix (Fin d) (Fin d) ℂ`), but the campaign's counting core
  (`fiberCount`, `card_fiberPreserving`, `permanent_submatrix_equiv`) is
  already stated over general index pairs `{n m : ℕ}`.

### Fermionic side (Rungs 8 / 9)

- `FermionicFock d := EuclideanSpace ℂ (Finset (Fin d))` — finite-dimensional:
  configurations are the *finite type* `Finset (Fin d)`. Basis `fockBasis d
  S`, vacuum `fockVac d = fockBasis d ∅`, transport
  `fockEquiv d : (Π S : Finset (Fin d), ℂ) ≃ₗ[ℂ] FermionicFock d`, sectors
  `sector d n` with `sector_orth` — `FermionicFock.lean`.
- Γ: `gamma d M : Module.End ℂ (FermionicFock d)` (everywhere defined,
  finite-dimensional), via `gammaPi d M` and the minor kernel `minorDet d M
  S T`; `gamma_one`, `gamma_mul`, `gamma_adjoint`, `gamma_inner`,
  `gamma_comp_self`, `gamma_self_comp`, `gamma_diagonal_basis`, and the
  representation lift `gamma_rep` — `SecondQuantGamma.lean`. The determinant
  core underneath (`cauchy_binet_rect`, `minorDet_mul`) is already
  rectangular in its blocks; the assembled `gamma` is square-only.
- dΓ and the free Hamiltonian: `dgamma d M`, `dgamma_one`, `freeHamiltonian`,
  `free_gap_dichotomy`, `freeHamiltonian_eigenvalue_gap`,
  `freeHamiltonian_expectation` — `SecondQuantDGamma.lean`. Same derived
  free gap, same finite-mode scope.

### What does *not* exist yet (the pitch's raw material)

- No inclusion of mode sets anywhere: no `Fin.castLE`-padding of matrices,
  no embedding of `Config d` into `Config e`, no map between Fock spaces at
  different `d`. The tower does not exist; only its floors do.
- No infinite-mode object of any kind: no `ℕ →₀ ℕ` configuration space in
  the corpus, no `ℓ²(ℕ, ℂ)` one-particle space, no operator defined on
  infinitely many modes.

---

## 2. The route fork — read this before the task list

The occupation-number construction changes what "direct limit" costs. The
corpus never built Fock space from tensor powers (that route is blocked
upstream since Rung 8); it built it as **ℓ² over a configuration index
set**. A direct limit of Fock spaces is therefore, at bottom, a **union of
index sets**: configurations over `ℕ` modes, `ℕ →₀ ℕ` (bosons) or
`Finset ℕ` (fermions), are exactly the configurations that already live at
some finite level. Two routes present themselves:

- **Route A — abstract direct limit first.** Build the algebraic direct
  limit of the `Dom d` tower with Mathlib's `Module.DirectLimit`, put an
  inner product on it (well-definedness from embedding compatibility),
  complete it (`UniformSpace.Completion` carries an inner-product instance;
  §4), then identify the completion with the concrete ℓ² space. Every step
  is real work, and the identification at the end re-proves what Route B
  gets by construction.
- **Route B — concrete target first (RECOMMENDED).** Define the limit
  spaces directly as `lp` spaces over the limit configuration sets (they
  exist in Mathlib today, complete, with inner products; §4), define the
  finite-level embeddings into them, prove the union of the embedded
  finite-particle domains is the full finite-particle domain of the limit
  and is dense. The result *is* the completed direct limit, with its
  universal property available afterwards as an optional capstone (Task
  4b) rather than as a load-bearing wall.

Route B is also the corpus's own established reflex: when the tensor-power
route was blocked at Rung 8, the occupation/ℓ² route is what stood the rung
up. This scoping prices Route B as the build order; Route A's abstract
capstone is priced separately and is killable without sinking the pitch.

---

## 3. The build order — priced tasks

Tasks are ordered so each consumes only what stands before it. Statistics
are flagged per task; §3.9 collects the comparison.

### Task 0 — The tower at the index level (both statistics) · **S–M**

*Goal.* Mode inclusions and configuration inclusions, with coherence.
Bosons: `configEmb (h : d ≤ e) : Config d ↪ Config e` via
`Finsupp.embDomain (Fin.castLEEmb h)`; fermions: `S ↦ Finset.map
(Fin.castLEEmb h) S`. Limit factorization: every `c : ℕ →₀ ℕ` (resp.
`Finset ℕ`) is `configEmb∞ d c₀` for some `d` and `c₀ : Config d` — its
support is finite, so it fits under some `Fin d`. Coherence:
`configEmb (h₁.trans h₂) = (configEmb h₂) ∘ (configEmb h₁)` (as functions /
embedding composition).
*Consumes.* Mathlib only: `Finsupp.embDomain`
(`Mathlib/Data/Finsupp/Defs.lean:416`), `Fin.castLEEmb`
(`Mathlib/Data/Fin/Embedding.lean:77`), `Fin.castSuccEmb` (:113).
*Hard step.* `Finsupp.embDomain` composition has no ready-named
`embDomain_trans` lemma in this checkout (grep, §4); the coherence proof is
a short `Finsupp.ext` + support argument — small, but it is a proof, not a
lookup. The factorization lemma is a support-bound extraction.
*Partial shape.* Successive-step coherence only (`d → d+1`, via
`Fin.castSuccEmb`) with general `d ≤ e` coherence deferred: a sequential
tower is enough for every later task; the general statement is bookkeeping.

### Task 1 — The limit spaces and their bases (both statistics) · **S**

*Goal.* `Config∞ := ℕ →₀ ℕ`, `BosonicFock∞ := lp (fun _ : Config∞ => ℂ) 2`;
`FermionicFock∞ := lp (fun _ : Finset ℕ => ℂ) 2`. Basis vectors
`boseE∞ c := lp.single 2 c 1` (resp. `fockBasis∞ S`), orthonormality from
`lp.inner_single_left`; vacuum `= boseE∞ 0` (resp. `fockBasis∞ ∅`);
finite-particle domain `Dom∞ := Submodule.span ℂ (Set.range boseE∞)`
mirroring `Dom d`; sectors `sectorSub∞ n` = span of basis vectors with
`tot∞ c = n`, `tot∞ c := ∑ i, c i` (a `Finsupp.sum` — finite by support).
*Consumes.* `lp.instInnerProductSpace` and `lp.completeSpace`
(`Mathlib/Analysis/InnerProductSpace/l2Space.lean:117`,
`Mathlib/Analysis/Normed/Lp/lpSpace.lean:1359`). No corpus module needed.
*Hard step.* None structural. This task is definitions plus the
orthonormality one-liner, deliberately first: it fixes the target every
later task aims at.
*Partial shape.* Bosons only, fermions deferred (or vice versa) — the two
statistics share no code here, so a one-statistics landing is coherent.

### Task 2 — The Fock embeddings (both statistics) · **M**

*Goal.* Linear isometries `fockEmb (h : d ≤ e) : BosonicFock d →ₗᵢ[ℂ]
BosonicFock e` and `fockEmb∞ (d) : BosonicFock d →ₗᵢ[ℂ] BosonicFock∞`
(fermionic analogs), characterized by the basis action
`fockEmb h (boseE d c) = boseE e (configEmb h c)`, with:
(i) **vacuum compatibility** — `fockEmb h (boseE d 0) = boseE e 0`,
immediate from `configEmb h 0 = 0`;
(ii) **cocycle/coherence** — `fockEmb h₂ ∘ fockEmb h₁ = fockEmb (h₁.trans
h₂)` and `fockEmb∞ e ∘ fockEmb h = fockEmb∞ d`, from Task 0 coherence plus
basis determination;
(iii) **domain compatibility** — `fockEmb h` maps `Dom d` into `Dom e`
(finite-particle to finite-particle), and sector `n` into sector `n`.
*Consumes.* Tasks 0–1; `boseE_orthonormal`; for the construction itself,
the orthonormal-family machinery of §4 (`Orthonormal.isHilbertSum`,
`OrthogonalFamily.linearIsometry`, `LinearIsometry.toSpanSingleton`) or a
direct `lp.single`-based definition extended from the dense span.
*Hard step.* **There is no ready-made `lp`-reindexing-along-an-injection
in this Mathlib** (grep, §4): the isometry must be assembled — define it on
the dense span of basis vectors, check it preserves inner products there
(orthonormality makes this a basis computation), and extend. Mathlib's
extension tools for linear isometries off submodules exist
(`LinearIsometry.extend`, `Mathlib/Analysis/InnerProductSpace/PiL2.lean:
1177`), but matching their hypotheses to this construction is the task's
real content. Expect API friction of the kind the corpus has met before
(coercions around `lp.single`), not new mathematics.
*Partial shape.* Embeddings into the limit only (`fockEmb∞`), with
finite-to-finite maps recovered a posteriori — or the reverse. Either half
alone still feeds Tasks 4–6; the cocycle is the clause most likely to be
priced down to successive steps.

### Task 3 — The embeddings *are* Γ of the one-particle inclusion · **M** (identification) + **L** (full rectangular functoriality, stretch)

*Goal (3a, the identification).* Define the padded inclusion matrix
`pad (h : d ≤ e) : Matrix (Fin e) (Fin d) ℂ`, `pad h i j = if (i : ℕ) = j
then 1 else 0` (a partial isometry: `padᴴ * pad = 1`). Extend the Γ kernel
to rectangular matrices — `perMinorRect`/`gammaBosRect` for bosons
(permanent of the enumerated-entry matrix; the definition of `perMinor`
uses only entries `M (enum c' a) (enum c b)`, so it ports verbatim), the
`minorDet`-based `gammaRect` for fermions — and prove, on `Dom d`:
`gammaBosRect (pad h) = fockEmb h` (as maps into `Dom e`), resp. the
fermionic identity. Consequence: the Fock-level cocycle of Task 2 is the
*shadow* of `gammaBos_mul`/`gamma_mul` — the tower is functorial, not a
basis accident.
*Consumes.* `gammaBos_apply_basis`, `gamma_apply`, the campaign's counting
core (already dimension-general), the fermionic rectangular Cauchy–Binet
core `cauchy_binet_rect`/`minorDet_mul`.
*Hard step.* For the pad matrix the kernel collapses to fiber-indicator
form, so 3a needs the counting lemmas, **not** a rectangular Cauchy–Binet;
that is what keeps 3a at M. The fermionic side additionally moves `Finset`
minors between two different ambient mode types — a definitional port with
card-matching vanishing (`minorDet_of_card_ne` analog).
*Goal (3b, stretch).* Full rectangular multiplicativity
`gammaRect (M * N) = gammaRect M ∘ gammaRect N` for composable rectangular
`M, N` — i.e., rectangular permanent Cauchy–Binet on the bosonic side.
This is a campaign of the same class as the two already closed (fermionic
determinants, bosonic permanents, both L). It is **not** needed for the
landing: the cocycle for inclusions is already available from Task 2
basis-wise and from 3a + square functoriality.
*Partial shape (expected if 3b is not attempted).* Pitch lands with 3a
only; rectangular functoriality recorded as an exposed price (§5). This is
the single most likely deliberate cut in the pitch.

### Task 4 — The union is everything: density and the limit's identity · **M** (+ **XL** capstone, killable)

*Goal (4a).* `Dom∞` equals the union of the embedded finite-level domains:
every finite-particle vector of the limit comes from some finite level
(Task 0 factorization + Task 2 basis action), and `Dom∞` is dense in
`BosonicFock∞` / `FermionicFock∞` (topological closure `= ⊤`). Capstone
corollary, via `Orthonormal.isHilbertSum` /
`IsHilbertSum.linearIsometryEquiv`: the limit space is the Hilbert sum of
its one-dimensional config sectors — i.e., **the completion of the
algebraic direct limit, identified concretely**.
*Consumes.* Tasks 0–2; `lp.norm_compl_sum_single`
(`lpSpace.lean:1167`, the truncation estimate that powers ℓ² density
arguments) or the `IsHilbertSum.mk` density criterion
(`l2Space.lean:278`).
*Hard step.* Density in `lp` over an *arbitrary* (countably infinite)
index set: the truncation argument must be run for the config index set
rather than quoted for `ℕ`-sequences. The pieces exist; the assembly is
the work.
*Goal (4b, capstone — XL, killable).* The abstract object: the
`Module.DirectLimit` of the `Dom` tower (`Mathlib/Algebra/Colimit/
DirectLimit.lean`, `DirectLimit.of`/`DirectLimit.lift`), its inner product
(well-defined by Task 2 isometry + cocycle), and a linear isometric
equivalence from its `UniformSpace.Completion` onto `BosonicFock∞`.
*Partial shape.* 4a stands, 4b unattempted: the pitch can honestly say
"the completed direct limit, constructed concretely and identified as
ℓ² over limit configurations" but not "the `Module.DirectLimit` object
was built and mapped." If Jeff wants the word "direct limit" to be a
theorem about Mathlib's own `DirectLimit`, 4b is the price of that
sentence.

### Task 5 — dΓ and the number operator in the limit (diagonal landing) · **M**

*Goal.* On `Dom∞`: per-mode number operators `numberOp∞ (i : ℕ)` (basis
eigenvalue `(c i : ℂ)`), the total number operator `N∞` (eigenvalue
`tot∞ c`), and the diagonal second quantization: for `λ : ℕ → ℝ`,
`dgammaDiag∞ λ` defined by the basis action
`dgammaDiag∞ λ e_c = ((∑ i, λ i * (c i : ℝ) : ℝ) : ℂ) • e_c` (finite sum,
over the support of `c`), with: vacuum annihilation; the adjoint relation
on `Dom∞` in the corpus's inner-product form; **finite-level agreement** —
`fockEmb∞ d (dgammaBos d (onePartDiagBos d (λ ∘ Fin.castLE …)) x) =
dgammaDiag∞ λ (fockEmb∞ d x)` on `Dom d`, and `N∞` agrees with
`numberOp` under the embeddings (`dgammaBos_one` transported); sector
preservation.
*Consumes.* Tasks 1–2; the finite-level basis formulas
(`dgammaBos_basis_diag`, `freeHamiltonianBos_basis`, fermionic
`dgamma_basis_diag`) — the limit operator is *defined* by the formula the
finite levels prove, and agreement is a basis computation.
*Hard step.* Defining an operator on `Dom∞` by a basis formula and proving
linearity/adjointness through the span: the corpus has this pattern
(`Dom_induction₂`, the `boseEquiv` transport), so the price is
porting, not invention. The sums `∑ i, λ i * c i` are over all of `ℕ` only
in notation — `c` has finite support, and `Finsupp.sum` handles it; no
convergence question exists on this domain.
*Explicitly out.* `dΓ∞` for a general (non-diagonal) operator on
`ℓ²(ℕ, ℂ)`: its defining sum is a double series over infinitely many
modes, with real domain questions. Exposed price, §5 — not silently
skipped, not attempted here.

### Task 6 — The free Hamiltonian in the limit, and the gap, surviving · **M**

*Goal.* `freeHamiltonian∞ λ := dgammaDiag∞ λ` on `Dom∞` (both statistics;
fermionic form `∑ j ∈ S, λ j`). Theorems, porting Rungs 9–10 line by
line: basis eigenvalue formula; vacuum eigenvalue `0`;
`freeHamiltonian∞_selfadjoint` (inner-product form on `Dom∞`); the
expectation formula `⟪x, H∞ x⟫ = ((∑_c ‖x_c‖² * eigenvalue(c) : ℝ) : ℂ)`
over limit configs (a finite sum on `Dom∞`, via the `dom_expand` analog);
and the headline:
**`free_gap_dichotomy∞` + `freeHamiltonian∞_eigenvalue_gap`** — if
`∀ i, λ i = 0 ∨ Δ ≤ λ i` for one fixed `Δ > 0`, then every eigenvalue of
`H∞` on a nonzero vector of `Dom∞` is `0` or `≥ Δ`.
*What "the gap survives" means, precisely.* Three things. (1) The
statement lives where Rungs 9–10 put it: eigenvalues of the operator **on
the finite-particle domain**, extracted at a nonzero coefficient of an
eigenvector. The port is config-local — an eigenvector in `Dom∞` has
finite support, so the Rung 9/10 extraction argument runs unchanged once
Tasks 1–5 stand. (2) The hypothesis is on a **single** `λ : ℕ → ℝ` with a
**single fixed Δ**: survival is exactly the `d`-independence of the
one-particle input. A sequence of finite-level gaps `Δ_d → 0` would
survive as nothing; that failure mode is excluded by the hypothesis, and
the document of the landing must say so. (3) It is a gap of the **free**
Hamiltonian of **countably many modes** — derived, not assumed, same as
Rungs 9–10, one scope-word wider.
*Consumes.* Task 5; finite-level `freeHamiltonianBos_eigenvalue_gap`,
`free_gap_dichotomy_bos`, `freeHamiltonian_eigenvalue_gap`.
*Hard step.* The expectation formula's sum over limit configurations:
finite on `Dom∞`, but the `dom_expand` analog (every vector of `Dom∞` is
the finite sum of its basis components) must be re-established for the
new span — a port of a proved pattern.
*Partial shape.* Dichotomy for basis vectors only, with the eigenvector
extraction deferred — i.e., "every basis eigenvalue is 0 or ≥ Δ" stands,
"every eigenvalue on Dom∞" priced. This is the second most likely cut
after Task 3b.

### Task 7 — Self-adjoint extension and the spectral gap (stretch) · **XL**

*Goal.* `H∞` on `Dom∞` is essentially self-adjoint; its closure is
self-adjoint; the **spectrum** of the closure lies in `{0} ∪ [Δ, ∞)`.
*Why it is a stretch.* This is a different kind of statement from
everything the ladder has proved: spectrum of an unbounded operator.
Mathlib's spectral API is for bounded/self-adjoint continuous linear maps
(`Mathlib/Analysis/InnerProductSpace/Spectrum.lean`); unbounded operators
exist only as partial linear maps (`Mathlib/Analysis/InnerProductSpace/
LinearPMap.lean`). There is no shelf to take this from — it is
infrastructure work, and it is **not required** for the landing, because
Rungs 9–10 set the ladder's own standard at the eigenvalue-on-domain
form, and Task 6 matches that standard exactly.
*Kill condition (pre-agreed).* If Task 7 is not attempted or does not
land, Pitch 2's verdict language must carry the clause "gap in the
eigenvalue-on-finite-particle-domain sense of Rungs 9–10; the spectral
statement for the self-adjoint closure is priced, unattempted." No
silent upgrade.

### 3.9 Fermions vs bosons — same road, tolls in different places

The road is shared (Tasks 0–6 as written cover both), but the prices sit
differently:

- **Bosons are structurally closer to the limit.** `BosonicFock d` is
  already an infinite-dimensional `lp` space; the limit changes only the
  index set. Basis-level arguments port almost verbatim. The bosonic
  tolls: `Dom`-discipline everywhere (operators live on spans), and the
  rectangular permanent kernel in Task 3.
- **Fermions cross a dimension barrier.** `FermionicFock d` is
  finite-dimensional; the limit is the first infinite-dimensional
  fermionic space in the corpus, so Task 1 creates a genuinely new kind
  of object and Task 2's maps land in a space of a different character
  than their domains. Compensation: fermionic operators are everywhere
  defined (no domain bookkeeping), `minorDet` needs no normalization
  factors, and the fermionic embedding can be built on the whole space
  directly. One fermionic-specific lemma hides in Task 3a: minors taken
  between finsets of two different ambient types — the Koszul `sgn` does
  **not** enter the coordinate formula (`gamma_apply` route), so no sign
  transport is needed; if a future proof routes through `adag` products,
  signs under `Fin.castLEEmb` (order-preserving) become a small lemma of
  their own.
- **Sequencing recommendation.** Fermions first through Tasks 0–2 (the
  finite-dimensional hygiene proves the pattern cheaply), bosons through
  the same tasks immediately after, then Tasks 3–6 statistics-by-
  statistics in whichever order the friction dictates. A one-statistics
  landing is a coherent PARTIAL, not a failure (§6).

**Total price of the recommended landing (§6): roughly two campaigns** —
Task 3a + Tasks 2/4 are the heavy modules; Tasks 0/1/5/6 are ports. For
calibration: the Γ functor campaign (one L) was 1,161 lines and closed in
a day; Rung 9's Γ + dΓ + gap was three modules. Pitch 2 is larger than
either but contains no step of a new *kind* except Task 7, which is
excluded from the landing.

---

## 4. Infrastructure check — what this Mathlib actually has (verified by grep, 2026-10-16)

Checkout: `~/workspace/thet-logos/lean/.lake/packages/mathlib/`, toolchain
`leanprover/lean4:v4.35.0-rc3` (`lean-toolchain`).

**HAS:**

- **`lp` spaces over arbitrary index families**, with inner product and
  completeness at `p = 2`: `lp` (`Mathlib/Analysis/Normed/Lp/lpSpace.lean:
  371`), `lp.single` (:1009), `instance completeSpace : CompleteSpace
  (lp E p)` (:1359), `lp.instInnerProductSpace : InnerProductSpace 𝕜
  (lp G 2)` (`Mathlib/Analysis/InnerProductSpace/l2Space.lean:117`),
  `lp.inner_single_left/right` (:160/:170), truncation estimates
  `lp.norm_compl_sum_single` (`lpSpace.lean:1167`). This is the same `lp`
  the corpus already builds on (`BosonicFock d`).
- **`ℓ²(ι, 𝕜)` notation** for the constant-fiber case:
  `scoped[lp] notation "ℓ²(" ι ", " E ")" => lp (fun _ : ι ↦ E) 2`
  (`lpSpace.lean:387`).
- **Hilbert direct sums — as a property, not a construction.** No
  `HilbertSum` type exists. What exists is `IsHilbertSum 𝕜 G V`
  (`l2Space.lean`, §`IsHilbertSum` ~:258–355): an orthogonal family of
  linear isometries into a complete space whose induced isometry from
  `lp G 2` is surjective; `IsHilbertSum.mk` discharges it from
  orthogonality + dense span; `IsHilbertSum.linearIsometryEquiv :
  E ≃ₗᵢ[𝕜] lp G 2`; `Orthonormal.isHilbertSum` (:348) turns a total
  orthonormal family with dense span into a Hilbert sum. In other words:
  Mathlib's position is that `lp G 2` *is* the Hilbert direct sum, and
  other presentations are identified with it — exactly Route B's shape.
- **Completion of inner product spaces.** `UniformSpace.Completion E`
  carries `InnerProductSpace 𝕜 (Completion E)`
  (`Mathlib/Analysis/InnerProductSpace/Completion.lean:89`), with
  `Completion.inner_coe` (:66) — the inner product extends by continuity.
- **Finite products**: `WithLp`, `PiLp 2`, `EuclideanSpace`
  (`Mathlib/Analysis/Normed/Lp/WithLp.lean`, `PiLp.lean`,
  `Mathlib/Analysis/InnerProductSpace/PiL2.lean`) — the fermionic
  finite-level spaces already live here. Finite only; no use for the
  limit beyond the floors of the tower.
- **Algebraic direct limits of modules**: `Module.DirectLimit` with
  `DirectLimit.of` and `DirectLimit.lift` (compatibility hypothesis:
  `∀ i j hij x, g j (f i j hij x) = g i x`)
  (`Mathlib/Algebra/Colimit/DirectLimit.lean:665,681`), plus a
  tensor-product direct limit
  (`Mathlib/LinearAlgebra/TensorProduct/DirectLimit.lean`).
- **Index-level parts**: `Finsupp.embDomain`
  (`Mathlib/Data/Finsupp/Defs.lean:416`), `Fin.castLEEmb`,
  `Fin.castSuccEmb` (`Mathlib/Data/Fin/Embedding.lean:77,113`),
  `LinearIsometry.extend` for extending isometries off submodules
  (`Mathlib/Analysis/InnerProductSpace/PiL2.lean:1177`).

**LACKS (each verified by a grep that returned nothing relevant):**

- **No direct limit of normed / inner-product / Hilbert spaces anywhere
  in `Mathlib/Analysis`** (`DirectLimit` does not occur under
  `Mathlib/Analysis/` at all). No inductive-limit topology, no Hilbert
  inductive limit, no API connecting `Module.DirectLimit` to norms,
  inner products, or completion. Task 4b would be hand-built.
- **No `lp` reindexing along an embedding**: no functorial map
  `lp E p → lp E' p` induced by an injection of index types in
  `lpSpace.lean`. Task 2's embeddings are assembled, not quoted.
- **No `Finsupp.embDomain_trans`**-style composition lemma under that
  name; Task 0's coherence is a short proof.
- **No unbounded-operator spectral theory** adequate for Task 7:
  spectrum API is for bounded operators; unbounded operators appear as
  partial linear maps (`LinearPMap.lean`) without a spectral calculus.

---

## 5. What Pitch 2 does NOT buy — and the prices it exposes

Even standing whole (§6), Pitch 2 leaves the following exactly where they
are. Nothing below is softened by the landing:

- **Still free theory.** Every operator in the limit is a Γ/dΓ lift or a
  diagonal Hamiltonian. There is no interaction term in the limit because
  there is none at any finite level either. **Pitch 3 (interaction) is
  not advanced one step** — it remains the rung with no starting module.
- **Still no continuum.** Countably many modes indexed by `ℕ` is not a
  continuum one-particle space: no mass shell, no Lorentz-invariant
  measure, no boosts. Rung 9 Task 4's pricing stands verbatim — a boost
  mixes modes in a way no mode tower indexed by `ℕ` with this basis
  resolves. **Pitch 4 (continuum / real Poincaré) is untouched**, and
  Pitch 2 does not even fix the one-particle space Pitch 4 would need
  (that space is a mass-shell L², not `ℓ²(ℕ, ℂ)`).
- **Still not the Yang–Mills gap.** The surviving gap of Task 6 is the
  free gap with more modes. The interacting gap's distance is unchanged;
  the honest sentence after Pitch 2 is the same as after Rung 10 with one
  word changed: "finite modes" → "countably infinite modes."
- **Exposed prices (newly visible, not paid):**
  - `Γ∞` for a *general* unitary on `ℓ²(ℕ, ℂ)` — Pitch 2 lifts only the
    inclusions and (via Task 5 agreement) diagonal data. A general
    infinite-dimensional one-particle unitary's second quantization is a
    further campaign (the kernel formula is config-local, so it is
    *plausible* work, but it is unscoped here beyond this sentence).
  - `dΓ∞` for non-diagonal one-particle operators (Task 5's exclusion).
  - Rectangular Γ functoriality in full (Task 3b), if cut.
  - The spectral form of the gap (Task 7), if cut — with its mandatory
    verdict clause.
  - The Symⁿ/⋀ⁿ tensor-power presentation of the limit sectors: still
    blocked upstream, still bypassed by the occupation basis. Pitch 2
    does not un-block it and does not need it.

---

## 6. Recommended landing — what "Pitch 2 STANDS" should mean

**The minimal honest package** (both statistics unless noted):

1. Limit spaces with orthonormal config bases and finite-particle
   domains (Task 1), over the Task 0 tower with at least successive-step
   coherence and limit factorization.
2. Fock embeddings as linear isometries with basis action, vacuum
   compatibility, domain and sector compatibility, and the cocycle at
   least along the chain `d → d+1 → …` (Task 2).
3. The identification of the embeddings with Γ of the padded inclusion,
   on `Dom d` (Task 3a) — the clause that makes the tower a functor
   limit rather than an ad hoc union.
4. Density of the finite-particle domain of the limit, and its equality
   with the union of the embedded finite-level domains (Task 4a).
5. Diagonal dΓ in the limit with finite-level agreement, including the
   number operator (Task 5).
6. The free Hamiltonian of countably many modes with basis eigenvalues,
   vacuum eigenvalue `0`, expectation formula, and the derived gap
   dichotomy for eigenvalues on the finite-particle domain under a
   fixed-Δ one-particle hypothesis (Task 6), labeled exactly as in §3
   Task 6.

With 1–6 green (zero sorrys, headline axiom checks
`[propext, Classical.choice, Quot.sound]`, per house standard), the
program may say: **"Pitch 2 STANDS — second quantization extends to
countably many modes: the Fock tower's completed direct limit is
constructed (concretely, as ℓ² over limit configurations), the Γ tower is
functorial, and the free gap is derived at infinitely many modes."** The
sentence must travel with its labels: free theory; eigenvalue-form gap;
no interaction; no continuum.

**The most likely PARTIAL shape** (named in advance, so it cannot be
dressed up later): Tasks 0–2 and 4a–6 stand for **one statistics**
(bosons, if the `Dom` ports run clean, or fermions, if the
dimension-barrier crossing runs clean), with Task 3a standing for that
same statistics, Task 3b unattempted, Task 4b unattempted, Task 7
unattempted with its verdict clause attached. Fallback PARTIAL, if the
Task 2 extension friction bites hard: embeddings and density stand, the
Γ-identification (3a) is priced rather than proved — in which case the
verdict is "the limit space and its tower stand; that the tower is Γ's
tower is priced," and Pitch 2 does **not** get the word "functorial."

**The single hardest priced step in the pitch** is Task 2's construction
of the `lp` embeddings: not because the mathematics is deep — it is a
basis computation — but because it is the one place where the needed
object (an isometry between ℓ² spaces induced by an injection of index
sets) has *no Mathlib counterpart to lean on*, and every later task
consumes it. Runner-up: Task 4a's density assembly over a general index
set. The hardest *excluded* step is Task 7, deliberately outside the
landing.

---

*Scoping ends. No Lean was written, nothing was built, nothing is
claimed. Awaiting Jeff's greenlight on the landing definition (§6) and on
the two pre-agreed cuts (Tasks 3b, 7) before any build order issues.*
