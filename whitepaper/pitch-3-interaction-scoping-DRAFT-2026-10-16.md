# Pitch 3 Scoping — Interaction (The First Non-Free Hamiltonian)

**DRAFT SCOPING — NOT A DOSSIER. Nothing in this document is built, proved, or
claimed. It is a priced build order for Jeff's greenlight, written 2026-10-16
after Pitch 2 stood (Campaigns A + B: the free theory at countably many modes).
Format and honesty template: `pitch-2-infinite-mode-scoping-DRAFT-2026-10-16.md`.**

Labels that govern every line below, now and after any landing: this pitch is
about **finite modes** and **matter self-interaction only**. Standing whole, it
buys **no continuum, no Poincaré, no gauge dynamics, and no part of the
Yang–Mills mass gap** — parts of the official Clay statement closed: **0**,
before and after. It removes exactly one word from the ladder's labels —
"free" — and replaces it with "interacting at finite modes." Everything else
on the frontier stays where it is (§7).

Effort classes used below: **S** = one small module section (days);
**M** = one focused module (week scale); **L** = a campaign (Γ-functor
campaign scale, ~1,000+ lines); **XL** = new-infrastructure scale, open-ended.
All line counts are estimates, labeled as such, calibrated against the
Γ campaign (1,161 lines) and Pitch 2 Campaign B (1,692 lines).

---

## 0. Verdict preview

**Recommendation: Route A first** — fermionic finite-mode interaction — because
the fermionic Fock space at finite modes is *finite-dimensional*, so an
interacting Hamiltonian there is a finite Hermitian matrix: self-adjointness is
linear algebra, the interaction is a genuine quartic Wick polynomial in the
corpus's own `adag`/`ann`, and **gap persistence under small coupling** becomes
the cheapest *true interacting gap theorem* available anywhere on this ladder.
Route B (bosonic, unbounded) follows as the second campaign; Route C
(interaction on the Pitch-2 limit spaces) is deferred to FRONTIER with reasons
(§2.3). Total price of the recommended landing (§6): **roughly two campaigns**.

**The honesty line.** Interaction buys **a term, not a theory.** Even landed
whole, Pitch 3 is: H = H₀ + gV on a finite-mode Fock space, V a Wick polynomial
in the corpus's creation/annihilation operators, with the first spectral
theorems about such an H. It is not an interacting quantum field theory: no
continuum, no scattering, no gauge field, no dynamics beyond what finite
matrices carry. The word "interacting" in the landing sentence must travel
with its labels exactly as "free" did (§6).

---

## 1. Starting point — the audit, the inventory, the definition

### 1.1 The no-interaction audit (grep evidence, 2026-10-16)

The corpus contains **no interaction operator anywhere**. Corpus-wide grep
over `lean/ThetLogos/*.lean` for `interact|quartic|wick|potential|coupling`
returns only:

- **Header disclaimers** — e.g. `BosonicAssembly.lean:27` "not an interacting
  theory, not Yang–Mills, and not a Millennium claim"; the same disclaimer
  pattern in `BosonicGamma.lean`, `BosonicGammaFunctor.lean`,
  `BosonicSecondQuant.lean`, `BosonicLimit.lean`, `FermionicLimit.lean`,
  `FockLimit.lean` ("no interaction").
- **Problem statements, not models** — `HaagKastler.lean:72`:
  `def InteractingHaagKastlerNet : Prop` — the open existence problem pinned
  as a proposition (T5), untouched by any construction; `FreeField.lean:11`
  prose: "no interacting 4D Wightman QFT has…".
- **Classical (non-quantized) interaction-shaped terms** —
  `SMLagrangian.lean` defines classical algebra functionals
  (`higgsPotential` :239, `yukawaTerm` :298, `fermionTerm` :134,
  `smLagrangian` :356) on finite matrices and vectors, and
  `ClassicalYangMills.lean` a classical `ymAction` (:237). These are
  *classical* Lagrangian sectors (SM-match, T1 as classical algebra). None of
  them is an operator on a Fock space; none acts on a quantum state.
- **Free-field Wick combinatorics** — `OperatorWick.lean` / `WickSigns.lean`
  are free-theory sign/combinatorics modules; `OperatorWick.lean` is a
  2-mode matrix toy (`creatorMat2m1` etc., :176–187).

Every Hamiltonian in the corpus is free. A grep for Hamiltonian definitions
returns exactly four, all of them dΓ of a diagonal one-particle matrix:

- `freeHamiltonian` (`SecondQuantDGamma.lean:201`):
  `dgamma d (onePartDiag d lam)`.
- `freeHamiltonianBos` (`BosonicSecondQuant.lean:341`):
  `dgammaBos d (onePartDiagBos d lam)`.
- `freeHamiltonianLimFerm` (`FermionicLimitOps.lean:572`) and
  `freeHamiltonianLimBos` (`BosonicLimitOps.lean:821`) — the Pitch-2 limit
  forms, diagonal by construction (`dGammaLim` of diagonal data).

**Blunt form: the single biggest absence in the program is not a missing
theorem; it is a missing term. Every Hamiltonian ever written in this corpus
is quadratic in the field operators. Pitch 3 exists to write the first one
that is not.**

### 1.2 The operator inventory interaction must be built from

All names exact, from the modules as they stand at remote `be093181`.

**Fermionic side (finite-dimensional; operators everywhere defined).**
`FermionicFock d := EuclideanSpace ℂ (Finset (Fin d))` — a *finite type* of
configurations, dimension 2^d. From `FermionicFock.lean`:

- `adag (i : Fin d) : Module.End ℂ (FermionicFock d)` (:361),
  `ann (i : Fin d)` (:365), with basis actions `adag_basis` (:399),
  `ann_basis` (:434) carrying the corpus's Koszul sign convention `sgn d i S`
  (:48).
- CAR: `car_mixed` (:547), `car_ann_ann` (:601), `car_adag_adag` (:644);
  adjoint relations in inner-product form: `ann_adjoint` (:488),
  `adag_adjoint` (:537).
- `numberOp` (:684, total), `parityFock` (:369), sectors `sector d n` (:867)
  with `sector_orth` (:907).
- Second quantization: `dgamma (M : Matrix (Fin d) (Fin d) ℂ)`
  (`SecondQuantDGamma.lean:49`), `gamma d M` (`SecondQuantGamma.lean`).
- **Missing, and needed by §4:** operator-norm bounds. A grep for
  `opNorm|‖adag|‖ann` in `FermionicFock.lean` returns **nothing** — the
  corpus has never needed ‖a‖. (From the basis action, `adag i` is a partial
  isometry, so ‖adag i‖ ≤ 1 is a short proof — but it is a proof, priced in
  Task A2.)

**Bosonic side (operators on the finite-particle domain `Dom d`).**
From `BosonicFock.lean` / `BosonicAssembly.lean` / `BosonicSecondQuant.lean`:

- `adag (d) (i) : Dom d →ₗ[ℂ] Dom d` (`BosonicFock.lean:186`), `ann` (:190),
  built from coefficient-level maps `adagC`/`annC` (:123/:127) on
  `Config d →₀ ℂ` — the √n factors live in the coefficient formulas.
- Assembly package: `adjoint_relation` (`BosonicAssembly.lean:41`),
  `ccr_mixed` (:247), `ccr_ann_ann` (:260), `ccr_adag_adag` (:269), plus
  coefficient-level CCR `ccr_coeff_*` (:127–204) and repr forms
  `repr_ann_adag` etc. (:221–239) — basis/coefficient computation routes
  already exist for exactly the monomial manipulations Route B needs.
- `numberOp (d) : Dom d →ₗ[ℂ] Dom d` (`BosonicAssembly.lean:297`);
  `dgammaBos (d) (M)` (`BosonicSecondQuant.lean:81`); `gammaBos`
  (`BosonicGamma.lean` + functor campaign).

**Not the build base:** the Rung-4 smeared-field API
(`FieldOperators.lean`: `createFermSmeared`, `createSmeared` on separate
`fermionicFock V`/`bosonicFock V` types) — a parallel, older Fock API. This
pitch builds on the Rung 8/9/10 API only; reconciling the two APIs is not
priced here and not needed.

**Environment constraint (standing fact, grep-confirmed):**
`FermionicFock.lean:361` and `BosonicFock.lean:186` both define
`ThetLogos.adag`; the two modules cannot be imported into one Lean
environment (duplicate `_proof_1`). Consequence: **mixed fermion–boson
interaction terms (Yukawa-type, a†a·(a_b + a_b†)) cannot even be stated**
until a namespace repair lands. That repair is an exposed price (§5), NOT
part of this pitch: Pitch 3 is single-statistics interaction, both kinds,
in separate modules — the same discipline Pitch 2's campaigns already used.

### 1.3 What "interaction" means at this rung — precisely

The corpus already contains every *quadratic* expression: `dgamma d M` for a
general (non-diagonal) matrix M is the quadratic form Σᵢⱼ Mᵢⱼ a†ᵢ aⱼ.
**Interaction at this rung means: a term of degree ≥ 3 in the creation/
annihilation operators** — a Wick-type polynomial

  V = Σ over monomials c_(α,β) · (a†)^(α) (a)^(β),  |α| + |β| ≥ 3,

built from the inventory of §1.2, normal-ordered per the corpus's existing
basis-action conventions. For a single statistics, the canonical first
exhibits are **quartic** (degree 4): density–density terms
nᵢnⱼ = a†ᵢaᵢa†ⱼaⱼ and hopping-type terms a†ᵢa†ⱼaₖaₗ. The interacting
Hamiltonian is

  H(g) = H₀ + g·V,   H₀ = the corpus's free Hamiltonian,

and the pitch's questions are the ladder's standard ones, asked of H(g) for
the first time about a non-free operator: Is it self-adjoint (on what
domain)? What are its eigenvalues? Does a gap survive — exactly, or for
small |g|? A "genuinely interacting" certificate is also in scope: a proof
that V (hence H(g) for g ≠ 0) is **not** of the form `dgamma d M` for any M —
dΓ eigenvalues are additive over occupied modes, and a quartic V's are not
(§4, Task A1) — so the pitch cannot be accused of relabeling a free operator.

---

## 2. The routes, honestly compared

### 2.1 Route A — Fermionic finite-mode interaction (RECOMMENDED FIRST)

**The decisive structural fact.** `FermionicFock d` is finite-dimensional
(dim 2^d, configurations the finite type `Finset (Fin d)`). An interacting
Hamiltonian there is a *finite Hermitian matrix*. Everything that makes
interaction hard in general — unboundedness, domains, essential
self-adjointness, inequivalent representations — is **absent by type**.
What remains is real but elementary: monomial bookkeeping under the Koszul
signs, operator-norm bounds, and one perturbation lemma.

**Exhibit A1 — the density–density first brick.** Per-mode number operators
nᵢ := `adag i ∘ ann i` (basis eigenvalue: the indicator of i ∈ S), and
V = Σ_{i<j} Uᵢⱼ nᵢ nⱼ. V is *diagonal in the occupation basis*, so H(g) is
diagonal: eigenvalues are the explicit finite sums
eig(S) = Σ_{i∈S} λᵢ + g·Σ_{i<j∈S} Uᵢⱼ. Yet V is a genuine quartic Wick
polynomial — a two-body interaction, not a one-particle lift — and the
not-a-dΓ certificate (Task A1) proves the point formally. With Uᵢⱼ ≥ 0 the
**exact gap persists**: every nonzero configuration has eig ≥ Δ (the free
gap), since the interaction only adds non-negative energy. This is the
flux-ring of the pitch: small, finite, theory-shaped, and it puts the words
"interacting Hamiltonian, eigenvalues, gap" into the corpus as theorems for
the first time.

**Exhibit A2 — the general quartic and gap persistence.** General normal-
ordered quartic V (hopping terms included), symmetrized to a self-adjoint
operator (adjoint relations of §1.2 make V† computable monomial by
monomial). Then the headline theorem of the pitch:

  **Gap persistence.** If ‖V‖ ≤ 1 (normalization) and |g| < Δ/2, every
  eigenvalue of H(g) lies within |g|·‖V‖ of a free eigenvalue; in
  particular H(g) has no eigenvalue in (|g|·‖V‖, Δ − |g|·‖V‖), its ground
  eigenvalue lies in [−|g|·‖V‖, |g|·‖V‖], and **the gap above the ground
  cluster is ≥ Δ − 2|g|·‖V‖ > 0**.

**The proof core is a named gap in Mathlib, not a lookup.** Verified by
grep (2026-10-16, Mathlib checkout of toolchain v4.35.0-rc3): there are
**no Weyl eigenvalue-perturbation inequalities** in this Mathlib (the only
"Weyl" hits are Lie-theory Weyl groups, `Mathlib/LinearAlgebra/Matrix/
Cartan/Realisation.lean`), and **no Courant–Fischer min-max**. What exists,
and what the proof must be assembled from:

- `Matrix.IsHermitian.spectral_theorem`
  (`Mathlib/Analysis/Matrix/Spectrum.lean:143`) and the sorted eigenvalue
  API `eigenvalues₀` (:60, antitone :63).
- **Gershgorin**: `Matrix.eigenvalue_mem_ball`
  (`Mathlib/LinearAlgebra/Matrix/Gershgorin.lean:30`) — every eigenvalue of
  a matrix lies in one of its Gershgorin balls. In the occupation basis
  H₀ is diagonal with entries eig₀(S); H(g)'s diagonal entries shift by
  g·⟨e_S, V e_S⟩ (|·| ≤ |g|·‖V‖) and its row off-diagonal sums are bounded
  by monomial counting (each quartic monomial sends a basis vector to **at
  most one** basis vector — the basis actions of §1.2 — so row sums are
  finite coefficient sums, bounded by a ‖V‖-type constant). Gershgorin then
  localizes every eigenvalue near a free diagonal entry. This route is
  elementary and self-contained; it is the recommended one.
- Fallback parts: the bounded-operator Rayleigh/resolvent API
  (`Mathlib/Analysis/InnerProductSpace/Rayleigh.lean`:
  `norm_eq_iSup_rayleighQuotient`, `rayleighQuotient_le_of_norm_mem_
  resolventSet`; spectrum/resolvent for Banach-algebra elements in
  `Mathlib/Analysis/Normed/Algebra/Spectrum.lean`) — a Neumann-series
  resolvent perturbation is available in principle if Gershgorin row-sum
  bookkeeping turns thorny.

Either way, the "Weyl substitute" is a lemma this campaign *proves* (Task
A2.3), sized inside the campaign — the single largest proof obligation of
Route A, and the reason A2 is M–L rather than M.

**Picture choice.** Schrödinger picture throughout: H(g) as an operator,
spectral statements as theorems. Dynamics (e^{−itH(g)}, interaction picture)
is **cut** (§5): at finite dimension the exponential exists
(`NormedSpace.exp` on a finite-dimensional Banach algebra), but a
Stone-theorem/unitary-group package is Pitch-2-Task-7-shaped infrastructure
and is not needed for any gap statement in §6.

**Price.** A1: **S–M** (est. 250–450 lines). A2: **M–L** (est. 600–1,000
lines) — monomial calculus + norm bounds + Weyl substitute + persistence.
Route A total: **one campaign**.

### 2.2 Route B — Bosonic Wick-polynomial interaction at finite modes

The honest bosonic version is a different weight class, for one reason:
**the operators are unbounded** (`adag`/`ann` on `Dom d`, with √n growth),
so the whole unbounded-operator stack that Route A dodges by type must be
faced — with the following Mathlib reality, verified by grep (2026-10-16):

**What Mathlib HAS.** A genuine language for unbounded self-adjointness:
`Mathlib/Analysis/InnerProductSpace/LinearPMap.lean` defines the adjoint of
a partial linear map (`LinearPMap.adjoint`, :151) and `IsSelfAdjoint` for
pmaps (`isSelfAdjoint_def : IsSelfAdjoint A ↔ A† = A`, :234), with dense
domain and closedness consequences (:241, and the file header :32).

**What Mathlib LACKS (each verified by a grep returning nothing).**

- **No Kato–Rellich theorem, no Kato anything** under `Mathlib/Analysis/`
  (grep `Kato`: no hits; grep `rellich`: no hits anywhere).
- **No essential self-adjointness** anywhere (grep `essentially self`: no
  hits) — no closure API for symmetric operators, no deficiency-index
  criterion, no analytic-vector theorem.
- **No spectral theorem for unbounded operators** (the spectrum API is for
  bounded operators — the same wall Pitch 2 priced as its Task 7).

So Route B's self-adjointness must be **hand-built** on the `LinearPMap`
adjoint API. The saving structural fact is the sector decomposition: a
*number-preserving* quartic V (a†a†aa-type monomials) preserves each
particle sector, and at finite modes each fixed-particle sector is
**finite-dimensional** (configurations `c : Fin d →₀ ℕ` with `tot c = n`
form a finite type). On each sector, H is a finite Hermitian matrix (Route
A's world); the bosonic difficulty concentrates in (i) the monomial
calculus with √n factors on `Dom d` (the coefficient-level CCR of
`BosonicAssembly` is the right tool), (ii) assembling sectorwise finite
matrices into one pmap on `Dom d` and proving `IsSelfAdjoint` for its
closure by hand, and (iii) **the gap claim's shape** — see below.

**N-relative bounds.** The standard control is ‖Vψ‖ ≤ C·‖(N + k)²ψ‖-type
estimates on basis vectors (quartic monomials grow like n² on n-particle
vectors). Basis computations via `repr_*`/`ccr_coeff_*` make these
provable; they are the bosonic analog of Route A's norm bounds, one weight
class up: necessary for domains, and for stating *which* V are allowed.

**The gap claim — where honesty bites hardest.** Uniform-in-particle-number
gap persistence for general bosonic quartic V is **false**, and the scoping
must say so before anyone builds toward it: sector-n perturbation norms
grow like g·n² (the √n factors), while free eigenvalues in sector n grow
like nΔ; worse, *attractive* density terms (−U·nᵢ(nᵢ−1)/2 with U > 0)
genuinely overwhelm nΔ at large n — eigenvalues dive, no global gap
survives, for mathematical reasons, not Lean reasons. The claim shapes that
ARE true, and that §6 adopts:

- **Exact gap for diagonal (density-type) bosonic V**, all sectors,
  uniform: eigenvalues are explicit (Σᵢ λᵢcᵢ + g·Σ Uᵢⱼcᵢcⱼ-type formulas);
  with U ≥ 0 the free gap persists exactly, as in A1 but on `Dom d`.
- **Windowed persistence** for general number-preserving V: for any fixed
  particle cutoff N₀, the gap persists in sectors n ≤ N₀ for
  |g| < g₀(N₀) — a finite-sector statement, honestly labeled as windowed.
- Uniform persistence for general V: **not claimed, not attempted** (§5),
  with the attractive-collapse counterexample recorded as the reason.

**Stretch exhibit — van Hove / displaced oscillator.** H_vH = H₀ +
Σᵢ (gᵢ·adag i + ḡᵢ·ann i) (linear terms) is the classic exactly-solvable
interaction: a displacement (Bogoliubov translation) conjugates it to
H₀ − Σᵢ|gᵢ|²/λᵢ, so its gap is *exactly* Δ, unchanged, with the coupling
arbitrary. It fits the corpus's bosonic assembly as a named exhibit
(**M**, est. 400–700 lines) IF the displacement operator is built via its
series on the full `BosonicFock d` lp space and the intertwining proved on
basis vectors. Two honesty flags, stated now: the displaced ground state
(a coherent vector) is **not in `Dom d`** — it has infinitely many particle
components, norm-convergent in the lp space only — so the exhibit's
eigenvalue statements must be posed on the full space, not in the ladder's
`Dom`-eigenvalue dialect; and the displacement is *not* one of the corpus's
Γ operators (Γ is multiplicative/second-quantized; displacement is an
affine translation) — it is new machinery, small but new. Killable without
sinking Route B (§5).

**Price.** B1 (Wick calculus + N-relative bounds): **M** (est. 500–800
lines). B2 (sector assembly + hand-built essential self-adjointness +
diagonal-exact and windowed gap forms): **L–XL** (est. 1,000–1,600+ lines;
the XL risk is the `LinearPMap` assembly, the one place in the pitch with
no corpus pattern to port). Route B total: **one campaign, the heavier of
the two**.

### 2.3 Route C — Interaction directly on the Pitch-2 limit spaces: FRONTIER

Not recommended; priced here only to record *why* it waits.

- **Missing inputs.** A limit-space interaction needs limit creation/
  annihilation operators and non-diagonal dΓ∞/Γ∞ — themselves exposed,
  unpriced-beyond-a-sentence prices in Pitch 2 (§5 of its scoping). Route C
  stacks an unscoped interaction on top of two unscoped lifts.
- **Haag-flavored obstruction.** At infinitely many modes, interactions
  generically leave the free representation: even the benign van Hove
  model has displaced vacua whose infinite-mode limit exits the free Fock
  space (orthogonal-sector phenomenon). "H₀ + gV on the Pitch-2 space" is
  therefore not even the default shape of the answer; which space the
  interacting theory lives on is model-dependent. At countably many modes
  this is milder than the continuum Haag theorem — but it is the same
  family of phenomenon, arriving one pitch early.
- **Renormalization shadow.** The Route B uniformity failure (§2.2) has no
  finite d to cap it here: monomial bounds acquire mode-sum factors over ℕ,
  and bare couplings need exactly the control the ladder has not built.
- **Least-blocked sub-variant (named for the record):** *fermionic* limit
  interaction. Fermionic monomials are bounded (‖a‖ ≤ 1 per mode) even in
  the limit, so a bounded self-adjoint V on `FermionicFock∞` with
  eigenvalue-sense gap persistence is conceivable — after limit `ann`/
  `adag` operators exist. Still: strictly more than Route A + a limit-
  operator campaign. FRONTIER; re-scope only after Routes A and B stand.

### 2.4 Comparison in one table

| | Route A (fermion, finite d) | Route B (boson, finite d) | Route C (limit) |
|---|---|---|---|
| Space | finite-dim (2^d) | `Dom d`, infinite-dim | Pitch-2 limit spaces |
| Self-adjointness | linear algebra | hand-built on `LinearPMap` | unscoped |
| Gap theorem | persistence, uniform, proved via Gershgorin (no Weyl in Mathlib) | exact (diagonal) + windowed; uniform FALSE in general | not stateable yet |
| New Mathlib needed | none (Weyl substitute proved in-campaign) | none, but `LinearPMap` assembly is new-pattern | several campaigns of inputs |
| Price | 1 campaign (S–M + M–L) | 1 campaign (M + L–XL) | FRONTIER |

---

## 3. Recommendation

**Route A first, as Campaign 1; Route B as Campaign 2; Route C deferred.**
Reasons, in order of weight:

1. **Cheapest true theorem.** A1 puts a genuinely interacting Hamiltonian
   with an exact gap into the corpus at S–M cost. No other pitch on the
   board buys a *first* at that price.
2. **Every tool Route A needs already exists in the corpus** (CAR, adjoint
   relations, basis actions) except operator norms and the Weyl substitute —
   both provable in-campaign from Gershgorin/spectral parts that grep
   confirms present (§2.1).
3. **Route A's monomial calculus is Route B's prerequisite anyway.** The
   ordered-product bookkeeping (signs for fermions, coefficient factors for
   bosons) is written once, in the finite-dimensional sandbox where
   mistakes are cheapest, then ported.
4. **Route B's risk is isolated, not contagious.** Its XL risk (hand-built
   self-adjointness) sits in Campaign 2; if it slips, the named PARTIAL
   (§6) still stands on Campaign 1.
5. The environment constraint (§1.2) is respected by construction: two
   statistics, two module families, no shared environment — the Pitch 2
   discipline.

---

## 4. Task list — the recommended campaigns

Sizes and line counts are estimates (calibration: §0). Tasks are ordered so
each consumes only what stands before it.

### Campaign 1 — Route A (fermionic interaction)

**Task A0 — Per-mode number operators and the diagonal toolkit · S**
(est. 100–200 lines). `numMode (i : Fin d) := (adag i).comp (ann i)` as
`Module.End ℂ (FermionicFock d)`; basis action `numMode_basis` (eigenvalue
= `if i ∈ S then 1 else 0`); commutation `numMode_comm` (from CAR);
`adag`/`ann` norm bounds `norm_adag_le`, `norm_ann_le` (‖·‖ ≤ 1, from the
basis actions — the corpus's first operator-norm lemmas, deliberately
placed here). *Hard step:* none structural; the norm bound is a
finite orthonormal-basis computation — but note Mathlib's operator norm on
`Module.End` of a finite-dimensional space needs the CLM coercion handled
once (API friction, expected and budgeted).

**Task A1 — The density–density exhibit and the not-a-dΓ certificate · S–M**
(est. 250–450 lines). `densityInt (U : Fin d → Fin d → ℝ) : Module.End ℂ
(FermionicFock d)` := Σ_{i<j} Uᵢⱼ • (numMode i ∘ numMode j); its quartic
normal form: `densityInt = Σ Uᵢⱼ • (adag i ∘ ann i ∘ adag j ∘ ann j)`
(provable from CAR + `numMode` basis action — the certificate that V is a
Wick polynomial, not a definition trick); basis eigenvalue formula;
`hamiltonianDens (g) := freeHamiltonian lam + g • densityInt U`;
self-adjointness (Hermitian: diagonal in an orthonormal basis with real
eigenvalues); the **exact gap theorem**: for Uᵢⱼ ≥ 0 and λ as in Rungs
9–10's dichotomy hypothesis, every eigenvalue of H(g) (g ≥ 0) on a nonzero
vector is 0 (vacuum only) or ≥ Δ. **Not-a-dΓ certificate:**
`densityInt_not_dgamma`: for d ≥ 2 and U₀₁ ≠ 0, `densityInt U` is not
`dgamma d M` for any M — proof by eigenvalue additivity failure:
eig({0,1}) − eig({0}) − eig({1}) + eig(∅) = U₀₁ ≠ 0, while any dΓ's
eigenvalues satisfy that alternating sum = 0. *Hard steps:* the eigenvalue
extraction dialect of Rungs 9–10 must be reused (eigenvalue on a vector =
extraction at a nonzero coefficient) — a port, budgeted; the alternating-
sum argument is short but is the exhibit's conceptual core.

**Task A2 — The general quartic calculus · M** (est. 350–550 lines).
Normal-ordered monomials `wickMono (α β : Fin d →₀ ℕ)`-style (fermionic
support: exponents 0/1, i.e. finsets of created/annihilated modes) as
ordered products of `adag`/`ann` under the corpus's sign conventions;
basis action of a monomial (at most one output basis vector, explicit sign
— from `adag_basis`/`ann_basis`); adjoint of a monomial (from
`ann_adjoint`/`adag_adjoint`); self-adjoint symmetrization
V ↦ (V + V†)/2 with `IsSelfAdjoint` conclusion; norm bound
‖wickMono‖ ≤ 1, hence ‖V‖ ≤ Σ|couplings| for finite Wick sums.
*Hard steps:* (i) **sign bookkeeping** — the corpus's products are defined
through `sgn d i S` and `adagPi`/`annPi` transports; monomial basis actions
must be proved through those, not through a new convention (a wrong sign
convention here invalidates A1's normal-form certificate retroactively —
the tasks are ordered to catch that); (ii) the Schrödinger-picture choice
is fixed here by construction (operators, not Heisenberg evolution).

**Task A3 — The Weyl substitute and gap persistence · M** (est. 250–450
lines). Assemble the matrix of H(g) in the occupation basis (via
`fockEquiv` / the basis's `Module.Basis`), Gershgorin data: diagonal
entries = free eigenvalue + O(|g|·‖V‖), row radii ≤ |g|·R(V) with R(V) an
explicit monomial-count bound from Task A2; conclude via
`Matrix.eigenvalue_mem_ball`: every eigenvalue of H(g) lies in a ball of
radius |g|·(‖V‖ + R(V)) around some free eigenvalue. Headline corollaries:
the **gap persistence theorem** of §2.1 (with the constant folded: for
|g|·C(V) < Δ/2, gap ≥ Δ − 2|g|·C(V)); ground-energy shift bound
|E₋(g)| ≤ |g|·C(V); vacuum is no longer asserted an eigenvector (it is
one only if V annihilates it — stated per-model, not in general).
*Hard step:* the basis-to-matrix transport of `Module.End` eigenvalue
statements (the ladder's eigenvalue dialect is basis-coefficient based;
Gershgorin is matrix based; the bridge is one focused section — budgeted,
and the reason A3 is M rather than S).

### Campaign 2 — Route B (bosonic interaction)

**Task B1 — Bosonic Wick calculus on `Dom d` · M** (est. 500–800 lines).
Monomials in `adag`/`ann` (BosonicFock versions) as endomorphisms of
`Dom d`; basis actions with √n factors via the coefficient forms
(`adagC`/`annC`, `repr_*`); sector preservation for number-preserving
monomials (`Dom`-sector analog of `dgammaBos_mem_domSector`);
**N-relative bounds**: for a monomial of degree 2k, an explicit C with
‖mono ψ‖ ≤ C·(sector-wise (n + k)^{k}) on sector n — stated as basis
estimates, the campaign's domain currency. *Hard step:* coefficient-level
arithmetic through `boseEquiv`/`boseRepr` transports — the corpus has the
pattern (Rung 8B) but every monomial identity is a fresh coefficient
computation.

**Task B2 — The interacting bosonic Hamiltonian and its self-adjointness ·
L** (est. 700–1,100 lines). `hamiltonianBosInt (g) := freeHamiltonianBos
lam + g • V` on `Dom d` for number-preserving quartic V (from B1);
symmetry on `Dom d` (inner-product form, from `adjoint_relation`);
sector decomposition: H preserves each finite-dimensional sector, where it
agrees with a finite Hermitian matrix (built sectorwise); assembly into a
`LinearPMap` and the **essential self-adjointness theorem**: the closure
of H as a pmap is self-adjoint (`IsSelfAdjoint` in the sense of
`LinearPMap.lean:234`), proved by hand from the sector matrices' spectral
theorems + density of `Dom d` — *no Mathlib theorem does this step*
(§2.2). *Hard step:* the assembly — graph/domain bookkeeping across
infinitely many finite sectors against an API with no corpus precedent.
This is the pitch's XL-risk task; its partial shape is named in §6.

**Task B3 — Bosonic gap forms · M** (est. 300–500 lines). (i) **Exact**:
the diagonal density-type V (bosonic `numMode` analogs; V diagonal in
`boseE` basis): eigenvalue formula on `Dom d`, exact gap persistence for
U ≥ 0, all sectors, uniform — the bosonic A1, on the domain. (ii)
**Windowed**: for general number-preserving V and any fixed cutoff N₀,
gap persistence in sectors ≤ N₀ for |g| below an explicit sector-computed
bound (finite check per sector family, via Campaign 1's A3 lemma applied
sectorwise). (iii) The **counterexample note** (documentation theorem,
small): attractive diagonal V with U < 0 has eigenvalues → −∞ along
configurations c = n·eᵢ+eⱼ — recorded in the module header and dossier so
the absence of a uniform claim is a *proved refusal*, not an omission.
*Hard step:* (i)'s eigenvalue formula must run the Rung-10 `Dom`
extraction dialect with cᵢcⱼ terms — a port with new arithmetic.

**Task B4 (stretch, killable) — van Hove exhibit · M** (est. 400–700
lines). As §2.2: displacement operator by series on `BosonicFock d`,
intertwining on basis vectors, spectrum shift −Σ|gᵢ|²/λᵢ, gap exactly Δ.
Headers must state the ground state is a coherent vector **outside**
`Dom d` and that eigenvalue language is the full-space one. Not required
for the landing (§6).

---

## 5. Pre-agreed cuts and kill criteria

**NOT attempted in this pitch (pre-agreed):**

- **Task 3b-analog / full dynamics:** no unitary time evolution, no
  interaction picture, no scattering — Schrödinger-picture spectral
  statements only.
- **Route C** in all forms (§2.3), including the fermionic sub-variant.
- **Mixed statistics / Yukawa terms** — blocked by the `adag` environment
  clash (§1.2); the namespace repair is exposed, not priced into this
  pitch, and no module in this pitch may import both Fock parents.
- **Uniform bosonic gap persistence for general V** — false in general
  (§2.2); only the exact-diagonal and windowed forms of Task B3 are
  claimed. Any future text upgrading this is a violation of this scoping.
- **Bosonic non-number-preserving V** (a†⁴ + a⁴ terms) beyond the van Hove
  linear exhibit: domain control for sector-mixing quartics is a further
  price, exposed here, unattempted.
- **Gauge self-interaction** — see §7; not a cut so much as a different
  pitch's prerequisite chain.

**Kill / shrink criteria (agreed in advance, so a PARTIAL cannot be
dressed up later):**

- If Task A3's Gershgorin row-sum bookkeeping resists (row radii not
  controllable by a ‖V‖-type constant), fall back to the resolvent route
  (§2.1) *once*; if both resist, Campaign 1 lands as A0–A2 + A1's exact
  gap only, and the verdict language must read "the first interacting
  Hamiltonians and an exact gap for the diagonal exhibit stand; gap
  persistence for general quartic coupling is priced, unattempted."
  Pitch 3 does **not** get the word "persistence" in that shape.
- If Task B2's `LinearPMap` assembly does not close, Campaign 2 lands as
  B1 + B3(i) (bosonic Wick calculus, relative bounds, exact diagonal gap
  on `Dom d`), with self-adjointness recorded as priced — the bosonic
  Hamiltonian is then "defined and symmetric on its domain," and no text
  may call it self-adjoint.
- If the sign bookkeeping of Task A2 contradicts A1's normal-form
  certificate, A1's certificate is re-proved or A1 is downgraded — the
  certificate is load-bearing for the word "interacting," and a silent
  mismatch kills the pitch's headline, not just a lemma.
- Route B's B4 (van Hove) is killable by Jeff's word or by friction, with
  no effect on the landing.

---

## 6. Landing definition — what "Pitch 3 STANDS" shall mean

**The minimal honest package:**

1. Campaign 1 complete (Tasks A0–A3): per-mode number operators and the
   corpus's first operator-norm bounds; a named interacting fermionic
   Hamiltonian `hamiltonianDens` (diagonal exhibit) *and* the general
   quartic class of Task A2, each proved a Wick polynomial in `adag`/`ann`;
   self-adjointness proved; the not-a-dΓ certificate (`densityInt_not_
   dgamma`) — the corpus's first proof that one of its own operators is
   *not* a free (dΓ) lift; the exact gap for the diagonal exhibit; and
   **gap persistence for general quartic V under an explicit
   small-coupling bound** (Task A3), all in the eigenvalue sense of
   Rungs 9–10.
2. Campaign 2 complete (Tasks B1–B3): the bosonic Wick calculus on
   `Dom d` with N-relative bounds; the number-preserving interacting
   bosonic Hamiltonian, symmetric on `Dom d`, with essential
   self-adjointness proved via its sector decomposition; the exact
   diagonal gap (uniform, all sectors) and windowed persistence; the
   attractive-collapse counterexample recorded.
3. All of it with zero sorrys and headline axiom checks
   `[propext, Classical.choice, Quot.sound]`, per house standard, and the
   two statistics in separate modules (no shared environment).

With 1–3 green, the program may say: **"Pitch 3 STANDS — the corpus
contains its first interacting Hamiltonians: at finite modes, for matter
self-interaction of both statistics, with self-adjointness proved, an
exact gap for the diagonal exhibits, and the free gap proved to persist
under small general quartic coupling (fermions; bosonic windowed form)."**

**Mandatory header clause** (to appear verbatim, or in wording Jeff
approves as identical in content, in every module this pitch produces, in
the style of Pitch 2's clause): *"Interacting Hamiltonian at finite modes:
H = H₀ + gV with V a Wick polynomial in the corpus's creation/annihilation
operators. The gap statements are in the eigenvalue sense of Rungs 9–10
(fermions: finite-dimensional; bosons: on the finite-particle domain).
This is matter self-interaction only — no gauge field, no continuum, no
Poincaré — and is not the interacting Yang–Mills mass gap; the spectral
statement for the bosonic operator is its sectorwise form, and uniform
gap persistence for general bosonic coupling is false in general and is
not claimed."*

**The most likely PARTIAL shape** (named in advance): Campaign 1 stands
whole; Campaign 2 lands as B1 + B3(i) with B2's self-adjointness priced
(the §5 fallback). Verdict then: "Pitch 3 STANDS for fermionic interaction;
bosonic interaction is defined with relative bounds and an exact diagonal
gap, its essential self-adjointness priced" — and the pitch's headline
sentence loses the words "both statistics" until B2 closes.

**The single hardest priced step in the pitch** is Task B2's hand-built
essential self-adjointness: the one place with neither a Mathlib theorem
(no Kato–Rellich, no essential-self-adjointness API — grep-verified) nor a
corpus pattern. Runner-up: Task A3's Weyl substitute — a real proof, but
from parts grep-verified present (Gershgorin, Hermitian spectral theorem).

---

## 7. What Pitch 3 buys / does not buy — and Pitch 4

**Buys (one scope phrase):** "free" → **"interacting at finite modes."**
Concretely: the program's Hamiltonians stop being definitionally quadratic;
the corpus gains an operator calculus for Wick polynomials, its first
operator-norm bounds, its first not-free certificate, and its first
interacting gap theorems (exact + persistence). Every later pitch that
needs an interaction term — which is all of them — consumes this pitch's
calculus instead of inventing its own.

**Does not buy:**

- **No continuum, no Poincaré.** Modes are still `Fin d`. Pitch 4
  (continuum / real Poincaré) is untouched in exactly Pitch 2's sense:
  this pitch does not fix the one-particle space Pitch 4 needs, and
  interaction at finite modes is orthogonal to the mass-shell/boost
  problem. Pitch 3 and Pitch 4 are independent walls; neither's landing
  moves the other's price. (Their eventual *composition* — interacting +
  continuum — is the constructive-QFT problem itself, and is not scoped
  by either document.)
- **No gauge self-interaction — and here is why, stated plainly.** The
  Yang–Mills interaction is the gauge field's self-coupling (the cubic and
  quartic terms of tr F² with F containing [A, A]). This corpus has **no
  quantized gauge field**: its gauge sector is classical finite algebra
  (`ClassicalYangMills.lean`'s `ymAction` on matrices; SM-match's
  classical Lagrangian sectors), and Γ(U) — its one quantum gauge-flavored
  machine — acts on *matter* Fock spaces by one-particle unitaries. There
  is no bosonic gauge-field Fock space, no connection operator on a
  Hilbert space, no covariant derivative as an operator. Pitch 3 therefore
  builds **matter self-interaction** (fermion quartic, boson quartic,
  density terms) — the interaction a theory can have before it has gauge
  dynamics. A "Pitch 3.5" that quantizes a gauge sector is a separate
  scoping, and until it exists, no sentence from this pitch may use the
  words "gauge interaction" or "Yang–Mills interaction."
- **No interacting gap in the summit's sense.** The persistence theorem
  says: a *free* gap, already derived, survives a *small* perturbation at
  *finite* modes. The Yang–Mills gap is a property of a specific
  interacting continuum theory at *all* couplings, derived from its
  dynamics. The distance between those two sentences is most of the
  remaining mountain, and this pitch's landing does not shorten it by one
  meter — it teaches the corpus to *say* "interaction" truthfully, which
  is the precondition for ever measuring that distance from inside.

**Exposed prices (newly visible, not paid):** the `adag` namespace repair
and mixed-statistics (Yukawa) terms; bosonic sector-mixing quartics;
unitary dynamics / interaction picture for the Hamiltonians built here;
Route C (§2.3) as FRONTIER.

---

*Scoping ends. No Lean was written, nothing was built, nothing is claimed.
Awaiting Jeff's greenlight on the landing definition (§6) and on the
pre-agreed cuts (§5: dynamics, Route C, mixed statistics, uniform bosonic
persistence) before any build order issues.*