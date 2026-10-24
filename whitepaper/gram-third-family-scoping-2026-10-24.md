# Gram clause, third family (the crossing-weight word series) — SCOPING CHARTER

**Date:** 2026-10-24. **Status: SCOPING (paper only). No Lean
built; census unchanged (4,445 strict / 4,494 attribute-inclusive
/ 150 counted modules).** Commissioned by Jeff's ruling
2026-10-24 ("Commission the third family — scope Item 1's last
door"), taking up the one named remainder of the transfer-route
R2 obstruction dossier
(`whitepaper/gram-transfer-r2-obstruction-2026-10-24.md`, §9).

**NO CLAIM.** Parts of any official Clay statement closed by
this document: **0**. Stage 1b-B positivity: **T1 for U(1)** at
all β ≥ 0 (Route C); general (G, ρ) **OPEN** until brick F3 of
this charter lands, and not before.

**Discharge target, on the face: β ≥ 0 only.** The R2 dossier
§4 fence stands — the seam kernel is not positive-definite for
β < 0 (circulant certificate: min eigenvalue −36.17, 8 negative
modes at β = −1, none at β = +1) — and §2 below shows the
damping signs of this family independently force the same
range. Any statement this route ever lands is a β ≥ 0
statement.

---

## Background in one paragraph

Three approaches to Stage 1b-B at general (G, ρ) now stand
closed at full rank: the factored occurrence family (T4c′ — a
shared strict factor forced as entry (k, a) on one half and
(j, i) on the other; SU(2) killer instance γ_AΦ^A = 0 ≠
γ_BΦ^B), the reflection-regrouping class (died at its R0 on the
same instance; T4c′ promoted to cover both), and the
transfer-matrix route's positivity rung (R2 — via S1+R1,
all-vector positivity of T reduces to positive-definiteness of
the seam kernel `layerWeightZero = exp(−S₀)`, whose only Gram
factorization is the tensor-power/word series over
representation indices of a crossing plaquette; that expansion
was fenced off from the transfer route by its charter D5, and
the route terminated on its own pre-registered criterion). R2
§9 named the remainder precisely: **the word expansion of the
crossing weight `exp(−wilsonActionZero)` as a factored family
for the landed conditional
`osForm_nonneg_of_gram_integrated`** — a third family, not the
occurrence family (its features are half-action averages;
these are seam words), not the polarization class — and
Gram-route territory. This charter scopes that family: it
settles the criterion fit, exhibits the factorization on
paper, fixes the jurisdiction of the (k, a)/(j, i)
obstruction, prices the assembly, and pre-registers the kills
before any build.

---

## §1 Criterion fit — FITS VERBATIM (one named sub-lemma, §1.4)

The consumer is the landed theorem
`osForm_nonneg_of_gram_integrated`
(`lean/ThetLogos/LatticeGramSeries.lean`, line 431; module
header, "T1 (criterion variant, general (G, ρ), any real β)").
Its load-bearing hypotheses, quoted from the statement:

- Index and features: `{ι : Type*} [Countable ι]`,
  `A : ι → (↥(halfLinks) → G) → ℂ`,
  `B : ι → (↥(negLinks) → G) → ℂ`,
  `Ξ : ι → (↥(posLinks) → G) → ℂ`, with `A i`, `B i`
  AEStronglyMeasurable against the product Haar measures.
- Domination: `(CA CB : ι → ℝ)`, `0 ≤ CA i`,
  `‖A i y‖ ≤ CA i`, `‖B i u‖ ≤ CB i`, and
  `(hsum : Summable fun i => CA i * CB i)`.
- The Gram identity, pointwise on the **closed** halves:
  `hgram : ∀ y u, (Real.exp (− wilsonAction (torusShift N) ρ β
  ((splitEquiv halfLinks).symm (y, u))) : ℂ) = ∑' i,
  (starRingEnd ℂ) (B i u) * A i y`.
- The marginals, through **one common** strict-half feature
  with nonnegative real dampings `(dA dB : ι → ℝ)`,
  `0 ≤ dA i`, `0 ≤ dB i`:
  `hmargA : ∫ y, A i y * f (restrictPos y) = (dA i : ℂ) *
  ∫ z, Ξ i z * f z`, and `hmargB` the same with `B i u *
  f (mirrorP hN u)` and `dB i`.
- Conclusion: `0 ≤ (osForm μG ρ β F F).re ∧
  (osForm μG ρ β F F).im = 0`, exhibited in the proof as
  `Z⁻¹ • ∑' i, (dA i * dB i) • ‖∫ Ξ i · f‖²`.

### 1.1 Infinite families: the quantifiers already allow them

The finite criterion `osForm_nonneg_of_gram` died on its
hypothesis (finite pointwise sum; T0 of the Route C module:
a finite Gram sum forces finite-dimensional kernel sections,
`finite_gram_sections_span`, while the crossing kernel has
full Peter–Weyl support). The integrated criterion was built
to remove exactly that: `ι` is an **arbitrary countable type**
and `hgram` is a **`∑'` (tsum) identity**. The word family's
index set — per seam plaquette a tuple (tensor levels n, m ≥ 0,
entry paths in (Fin d)^{2n} × (Fin d)^{2m}, internal
contraction paths), finitely many plaquettes — is a finite
product of countable types, hence countable. **No quantifier
gap.** No new criterion variant is needed or permitted by
this charter: if a variant turns out to be needed, that is
kill K-F2(e) below, not a silent amendment.

### 1.2 Domination: what the criterion demands, what the family supplies

The criterion demands pointwise, configuration-independent
bounds with `Summable (CA · CB)` — and nothing stronger: no
L² condition on the features, no measurability on `Ξ` at all
(the statement's own note: everything about `Ξ` enters
through the two marginal identities). The word features are
finite products of entries of unitary matrices and of
`ρ(τ⁻¹)`, `ρ(u)`, `ρ(τ′)` factors, hence **|feature| ≤ 1
pointwise** (entries of a unitary have modulus ≤ 1; internal
contraction indices are *not* summed inside the feature —
they are part of the index `i`, §2). Coefficients
`(β/d)^{n+m}/(n! m!)`-shares (§2) supply `CA i`, `CB i` as
their square roots split across the sides; the total
`∑ᵢ CA i · CB i` is majorized by a finite product over seam
plaquettes of exponential series `∑ₙ Kⁿ/n!` with
`K = (β/d) · d⁴`-type path-count constants (finitely many
paths per level, §2.3) — finite. AEStronglyMeasurability
follows from continuity: word features are polynomial in
entries of `repMatrix ρ ·` applied to link variables, and the
criterion's own `hρcont : Continuous fun g => repMatrix ρ g`
is a hypothesis of the ambient section, already discharged
for the corpus's `ρ`. Route C proved its features continuous,
stronger than consumed; the same is expected here.

### 1.3 The marginal shape is the shape Route C already discharged

The two-selector form (`dA`/`dB`, common `Ξ`) is not an
obstacle invented for this family: it is the exact form in
which Route C landed `marginalA` / `marginalB` at d = 1
(dossier `whitepaper/gram-route-c-2026-10-23.md`: "Marginals
in two-selector (dA/dB) form; the Gram index is the stratum's
Fourier lattice"). The third family instantiates the same
hypothesis shape with Peter–Weyl word features in place of
Fourier modes. What the family must prove is its own
marginals — as every family must — and §1.4 names the one
lemma inside that obligation that carries the route's risk.

### 1.4 The one named sub-lemma: the Damping Lemma (priced in F2)

**Damping Lemma (to be proved in F2, or the route dies
there).** *For the word family of §2 there exist `dA dB : ι →
ℝ`, `0 ≤ dA i`, `0 ≤ dB i`, and a strict-half word feature
`Ξ i` such that `hmargA` and `hmargB` hold: concretely, the
integral of a word feature over the closed half against
`f ∘ restrictPos` factors as (stratum contraction value) •
∫ (strict word feature) · f, where the stratum contraction —
the joint Haar integral over the reflection-plane links of
the word monomial, the plane links being shared between
adjacent seam plaquettes (R2 §2, absorption paragraph) —
is a nonnegative real, and the surviving strict feature on
side A equals the reflection of side B's surviving strict
feature (the common `Ξ i`).*

Why this is a lemma and not a remark: at d = 1 it is circle
orthogonality, `∫ zⁿ z̄ᵐ = δₙₘ`, and the contraction values
are 0/1 — nonnegativity is free. At general (G, ρ) the
contraction is a Peter–Weyl/Schur-orthogonality computation
over the shared plane-link network; *bare* entry-level
contractions of tensor powers are Weingarten sums, whose
weights can be negative at tensor level ≥ 2. The lemma must
therefore be proved by grouping: the contraction of the
*whole* word monomial against Haar is an invariant-projection
pairing (Haar averaging of a unitary representation is the
orthogonal projection onto its invariant subspace), and the
features of §2 are built so that each side's contraction is
such a pairing of a word with its reflection-matched partner
— a Gram diagonal, of `‖·‖²` type — not a bare Weingarten
sum. Whether the grouping survives the shared-link network
at all tensor levels is the route's crux, exactly as
symmetrized proportionality was the regrouped route's crux.
It is priced inside F2 (L) and carries kills K-F2(a)–(c).

**§1 verdict: the criterion fits the word family verbatim.**
The family's obligations under it are F1 (§2's identity, in
Lean) and F2 (assembly + the Damping Lemma). The criterion
itself needs no amendment, no variant, no weakening.

---

## §2 The factorization, on paper

### 2.1 One crossing plaquette

A seam (crossing) plaquette has holonomy
`U_p = u · τ′ · y⁻¹ · τ⁻¹` — `y` a strict positive link, `u`
its strict negative partner, `τ, τ′` the two temporal
(reflection-plane) links. By cyclicity of the trace and
unitarity of `ρ` (R2 §2; SU(2) certificate: the identity held
to 1.1e-16),

  `tr ρ(U_p) = ⟨ρ(y), ρ(τ⁻¹ u τ′)⟩_HS`,

the Hilbert–Schmidt inner product of two `d × d` matrices.
The plaquette's Boltzmann factor is therefore

  `exp(−β · plaquetteDensity) = e^{−β} · exp( (β/d) ·
  Re ⟨X, Y⟩_HS )`,  with `X := ρ(y)`, `Y := ρ(τ⁻¹ u τ′)`,

(the density is `1 − Re(tr ρ(U_p))/d`; at d = 1 this is the
corpus's `plaquetteDensity_circleRep`, T1). Set `c := β/d`
(real; `c ≥ 0 ⟺ β ≥ 0`).

### 2.2 The split: matching indices by construction

`Re z = (z + z̄)/2` and `z̄ = ⟨Y, X⟩_HS` for
`z = ⟨X, Y⟩_HS`, so, the two scalar exponents commuting,

  `exp(c · Re ⟨X, Y⟩) = exp((c/2)⟨Y, X⟩) · exp((c/2)⟨X, Y⟩)`.

Each factor expands by the exponential series and the
tensor-power identity for the HS inner product,
`⟨X^{⊗n}, Y^{⊗n}⟩_HS = ⟨X, Y⟩ⁿ`:

  `exp((c/2)⟨Y, X⟩) = ∑'_{n ≥ 0} (c/2)ⁿ/n! ·
  ⟨Y^{⊗n}, X^{⊗n}⟩_HS`.

Now expand the tensor-power inner product over **entry
paths** `α = (a, b) : [n] → Fin d × Fin d`:

  `⟨Y^{⊗n}, X^{⊗n}⟩_HS = ∑_α conj(Ψ_{n,α}(Y)) · Ψ_{n,α}(X)`,
  `Ψ_{n,α}(M) := ∏_{k<n} M_{aₖ bₖ}` —

the **same** path `α` on both sides. This is the whole point,
and it is definitional: an inner product pairs a vector with
itself index-by-index; there is no entry-selection step at
which the two halves could be forced to read different
entries of anything. (Contrast §3.)

It remains to split `Ψ_{n,α}(Y)` across the halves. Each
entry of `Y = ρ(τ⁻¹ u τ′) = ρ(τ)⁻¹ ρ(u) ρ(τ′)` is a finite
sum over internal indices `κ = (k, l)`:
`Y_{ij} = ∑_{k,l} (ρ(τ⁻¹))_{ik} ρ(u)_{kl} (ρ(τ′))_{lj}`.
Take the internal paths as part of the index (§1.2: no sum
inside any feature), so each summand is a product of three
entry factors: a `ρ(τ⁻¹)` entry and a `ρ(τ′)`
entry — functions of plane links, which live in the **closed
positive half's** variable set (`halfLinks` includes the
plane links; `negLinks` is strictly negative) — and a
`ρ(u)` entry, a function of the negative half. Assign:

- **A-side feature** (function of `y`, the closed positive
  half): the `Ψ(X)` word (entries of `ρ(y)`) times the
  plane words (`ρ(τ⁻¹)`, `ρ(τ′)` entries) from both
  exponential factors.
- **B-side feature** (function of `u`, the closed negative
  half): the `ρ(u)` words from both factors — entering
  `hgram` under `conj`, as the criterion's
  `(starRingEnd ℂ) (B i u)` requires.

The second exponential factor `exp((c/2)⟨X, Y⟩)` is treated
symmetrically (it is the `⟨Y, X⟩` expansion with the two
tensor factors' roles exchanged; its `Y`-words split the
same way, its `X`-words join the A side). The full
per-plaquette index is `(n, m, α, α′, internal paths)` and
the coefficient is `(c/2)^{n+m}/(n! · m!)`, shared between
the sides by the damping split of §1.4 (`dA · dB` reproduces
coefficient shares after contraction; the uncontracted
`hgram` identity carries the coefficient split directly in
`CA`/`CB`).

### 2.3 Convergence, stated precisely

`G` is compact, `ρ` unitary: every matrix entry has modulus
≤ 1, so every word feature has modulus ≤ 1 pointwise, and
`|⟨X, Y⟩_HS| ≤ ‖X‖_HS ‖Y‖_HS = d`. The level-`n` term of
each exponential series is bounded by `(c/2)ⁿ dⁿ / n!` at
the inner-product level; expanding over paths multiplies the
number of summands by at most `d^{2n}` per inner product and
`d^{2n}` internal paths per word — finite per level, and
`∑ₙ (K)ⁿ/n! < ∞` for the resulting constant `K` (exponential
domination beats fixed-base path growth). Hence: absolute
convergence of the per-plaquette series, uniformly on the
compact configuration space; the finite product over seam
plaquettes (§4) converges absolutely; the domination data of
§1.2 exists. This is the Peter–Weyl picture of R2 §2 made
quantitative: the class function `g ↦ exp(β Re tr ρ(g))` is
analytic, non-polynomial, of **unbounded** Peter–Weyl
support — the family is genuinely infinite, which is exactly
why the consumer had to be the `∑'`-criterion of §1 and why
no finite sub-family can substitute (T0's finite-rank
obstruction, `finite_gram_sections_span`, T1).

### 2.4 The d = 1 control

At `(G, ρ) = (U(1), defining)`, `⟨X, Y⟩ = conj(y) ·
(τ⁻¹ u τ′)` is a scalar of modulus 1, word monomials are
powers, and the (n, m)-graded series of §2.2 resums over
`n − m` to Route C's Fourier–Bessel series
`exp(β Re w) = ∑'_{n : ℤ} Iₙ(β) • wⁿ` — in the corpus as
`hasSum_fourier_exp_circle` / `fourier_exp_circle` (T1),
with `besselI β n ≥ 0` at `β ≥ 0` the damping nonnegativity
of §1.4 in its d = 1 form. **F1 carries this as an internal
control**: the F1 theorem, specialized to the circle, must
reproduce Route C's series; failure is kill K-F1(b).

---

## §3 Jurisdiction — the (k, a)/(j, i) obstruction has no purchase on the factorization; its last possible seat is named, not hidden

The T4c′ mechanism (MEMORY, GramClause entry; promoted over
the factored family and the whole reflection-regrouping
class) requires two ingredients: **(i)** the family's shared
hinge is a *finite per-occurrence scalar factor* — one matrix
entry of a plaquette density, shared between the halves; and
**(ii)** the two halves are forced to read that same factor
at *different* entries — as entry `(k, a)` in one half's
coordinates and `(j, i)`, the transpose slot, in the other's —
so the common-feature equation becomes a pointwise identity
between mismatched entries and fails on the SU(2) instance
(`γ_A Φ^A = 0 ≠ γ_B Φ^B`). Neither ingredient exists here.
The hinge of the word family is not an entry but a whole
tensor-power word, and the two halves are paired by the
Hilbert–Schmidt inner product on tensor powers, which pairs
path `α` with path `α` — §2.2's expansion is the *definition*
of `⟨Y^{⊗n}, X^{⊗n}⟩_HS`, basis-covariant (a unitary change of
basis conjugates both sides' features by the same unitary
and leaves the pairing, hence the identity, unchanged),
whereas an entry is precisely what a basis change does not
preserve. There is no step in §2 at which a factor is
*selected* as a scalar from one side and *re-inserted* at a
transposed slot on the other: the A-side and B-side features
are read off one inner product, not equated after the fact.
The d = 1 shadow confirms the jurisdiction empirically: Route
C discharged positivity for U(1) through this same series
(§2.4) in a setting where an entry-mismatch mechanism would
have had the same formal opportunity. **Concession, at full
rank:** jurisdiction over the *factorization* (§2) is not
jurisdiction over the *marginals* (§1.4) — the plane-link
contraction is a new computation in which the two sides meet
again, over a shared-link network rather than inside one
inner product, and if an index mismatch reappears anywhere
it reappears there. That seat is not argued away here; it is
priced (F2) and killed in advance (K-F2(b)). Likewise R2
§8's "full purchase on positivity" is conceded as a
*location* statement — the positivity does live in the
exponential of ρ-entries of a crossing plaquette, separable
only over representation indices — and this route goes to
that location deliberately, on Gram-route territory: R2's
kill clause 1 and its charter's D5 fence the *transfer*
route (no word expansion inside a `T = V†V` half-step
square); they do not fence the Gram criterion, whose own
charter (Route C) already performed this expansion at d = 1.
The transfer route stays terminated; nothing in this charter
revives it.

---

## §4 Assembly

**The full weight.** In the criterion's own coordinates
(Stage 1b-A's `splitEquiv` on `halfLinks`/`negLinks`), the
action splits as landed: `S = S₊ + S₋ + S₀`, with `S₊`
internal to the closed positive half, `S₋` to the negative
half, and `S₀ = wilsonActionZero` the crossing part, whose
plaquettes are exactly the seam plaquettes of §2 (finitely
many: fixed finite volume). Hence

  `exp(−S) = exp(−S₊)(y) · exp(−S₋)(u) · ∏_{p crossing}
  [ e^{−β} · exp((β/d) Re ⟨X_p, Y_p⟩_HS) ]`,

with `exp(−S₊)`, `exp(−S₋)` bounded one-sided factors
(at β ≥ 0 the actions are nonnegative, so these are ≤ 1;
in any case constant majorants exist and fold into `CA`/`CB`)
distributed into the A/B features as index-independent
factors — the same architecture as Route C's "features built
from the half actions, weights `wR = ∏ exp(−β) · Iₙ(β)`".

**Product of series.** The `hgram` identity is the finite
product over seam plaquettes of §2's absolutely convergent
series, i.e. a single `∑'` over the product index set of
§1.1. Absolute convergence (§2.3) is what licenses the
product-to-tsum step; in Lean this is finite-product HasSum
plumbing (`HasSum.prod`-family / tsum over a finite product
of index types), priced inside F2 — plumbing, not a new
analytic input.

**Interchanges owed: none beyond the criterion's own.** The
criterion's proof already performs the `∑'`↔integral
interchange from the domination hypothesis (its internal
step: `hasSum_integral_of_summable_integral_norm` applied to
`hsumInt`, built from `hsum`). The family owes the criterion
its hypotheses — pointwise identity, pointwise bounds,
summable domination, measurability, marginals — and no
further interchange argument.

**Integration tools consumed: the criterion's own, not
R1's.** R1 dossier §6 ships `integral_splitEquiv_factor` and
`integral_layerFactor_iterated` for the transfer route's
R2/R3. This route does not consume them: it works in the
criterion's coordinates directly (Haar product measures on
the two closed halves, `restrictPos`/`mirrorP` marginal
transports — the machinery Route C's `marginalA`/`marginalB`
already exercised), and S1/R1 stand untouched and unneeded
here. The seam kernel of R2 and the crossing weight of this
charter are the same factor seen from two routes; this route
factors it pointwise on the closed halves instead of asking
it to be a mid-layer square.

**Reflection pairing.** Side B's features are built from
`u`-words; `mirrorP` transports `negLinks` to `posLinks`, and
the crossing holonomy `U_p = u · τ′ · y⁻¹ · τ⁻¹` pairs `u`
with the *same* plaquette's `y` by construction, so the
strict word surviving side A's contraction and the reflected
strict word from side B are the same monomial — the common
`Ξ i` of §1.4 is a construction property, with its failure
mode pre-registered (K-F2(c)) rather than assumed away.

**β range.** `hgram` (§2) holds for every real β; the
discharge does not: the coefficient shares `(β/d)^{n+m}` and
the Damping Lemma's nonnegativity need `β ≥ 0` (at d = 1:
`Iₙ(β) = (−1)ⁿ Iₙ(|β|)` alternates for β < 0 — R2 §4). F3's
statement is a β ≥ 0 statement, matching Route C's range and
R2's fence.

---

## §5 Ladder (prices; pre-registered kill criteria)

Prices in the house scale (S = one brick; M = a module with
real content; L = research-scale brick). Dependencies are on
landed statements only.

**F0 — this charter (paper). Price: S. DONE as scoped.**
Settles §§1–4; no census impact; the route's kills are
registered below before any build, per the Concrete.

**F1 — the single-plaquette word factorization, as a
standalone Lean theorem. Price: M.**
One crossing plaquette: the identity of §2.2 as a `∑'`
equality with its domination data, at general (G, ρ), any
real β — features as word monomials over the corpus's
word/tensor machinery (`GramWordTensor`, Route B T3), the
tensor-power HS identity `⟨X^{⊗n}, Y^{⊗n}⟩ = ⟨X, Y⟩ⁿ` and its
entry-path expansion as the brick's lemmas. Dependency:
`LatticeGramSeries` (criterion + §2.4's Bessel control),
`repMatrix` API (`LatticeGauge`). Internal control (§2.4):
specialization to `(U(1), defining)` resums to
`fourier_exp_circle`.
*Kills, pre-registered:*
- **K-F1(a)** — the tensor-power HS identity or its entry
  expansion closes only through a basis choice (e.g. an
  eigenbasis of `ρ(y)`) that makes the features cease to be
  word monomials in link entries — the A/B split of §2.2 then
  does not exist as stated. Kill F1; the route re-scopes or
  dies here.
- **K-F1(b)** — the d = 1 control fails: F1's series at
  `(U(1), defining)` does not resum to the landed
  `fourier_exp_circle`. The general-d identity is then not
  the generalization it claims to be. Kill F1.

**F2 — assembly into the criterion: `hgram` for the full
weight + the Damping Lemma (the marginals). Price: L.**
The finite product over seam plaquettes (§4), the one-sided
factors, the domination package of §1.2, and §1.4's Damping
Lemma — a Peter–Weyl/Schur-orthogonality computation over
the shared plane-link network, with `marginalA`/`marginalB`
(Route C) as the worked template for the marginal *form*.
Dependency: F1; Stage 1b-A split/marginal machinery as
instantiated by `LatticeGramSeries`. This is the route's
long pole: the L prices the contraction computation and the
thin Mathlib Peter–Weyl API for tensor powers (Haar integrals
of matrix coefficients), not the assembly plumbing.
*Kills, pre-registered:*
- **K-F2(a)** — the Damping Lemma is false as stated: some
  word index's stratum contraction is non-real or negative,
  and no regrouping of the index set into Gram-diagonal
  (invariant-projection) pairings removes it — the
  Weingarten-sign mechanism, named in §1.4. Kill the route at
  F2; the obstruction ships as a dossier at the same speed
  as a landing.
- **K-F2(b)** — index mismatch at the half-feature level:
  the contraction pairs side-A path α with side-B path
  α′ ≠ α for surviving indices, irreducibly under
  reindexing — the (k, a)/(j, i) mechanism reappearing at
  its last possible seat (§3). Kill, with the instance
  exhibited as T4c′'s was.
- **K-F2(c)** — common-`Ξ` failure: for some surviving index,
  side A's contracted strict feature differs from side B's
  reflected strict feature by more than the scalar dampings
  allow. Kill (the criterion's common-feature hypothesis is
  not negotiable downward, §1.1).
- **K-F2(d)** — assembly summability failure: the product
  over seam plaquettes loses the §1.2 domination in its Lean
  form (path multiplicities defeating the exponential bound
  as formalized). Kill or re-price — stated, not patched
  silently.
- **K-F2(e)** — a criterion-quantifier mismatch surfaces at
  instantiation that §1 missed. Kill; §1's verdict is then
  corrected on the record, at full rank.

**F3 — the discharge. Price: S.**
Apply `osForm_nonneg_of_gram_integrated` to F2's family:
`osForm_nonneg` at general (G, ρ), **β ≥ 0**, even N, fixed
finite volume. Application brick only (Route C's
`osForm_circle_nonneg` is the shape). Dependency: F2.
*Kills:* none of its own — any failure at F3 is an F2 gap
reclassified and reported as such. *Label discipline:*
Stage 1b-B is "T1 at general (G, ρ), β ≥ 0" only when F3's
build is green and parent-verified under the standing
landing protocol; until then the label stays "T1 for U(1);
general (G, ρ) OPEN", and this charter changes no label by
itself.

**Route total: F0 S (done) + F1 M + F2 L + F3 S.** One long
pole (F2), and it is the pole §1.4 names.

---

## §6 Honest unknowns

- **U1 — the Damping Lemma's grouping.** Whether the
  invariant-projection grouping of §1.4 can be carried
  through the *shared* plane-link network (each plane link
  in two adjacent plaquettes' stars) at all tensor levels,
  in a form Mathlib's current Peter–Weyl/Schur API can
  carry, is genuinely unknown at scoping. It is the route's
  crux and is priced, not minimized: F2 is L because of it.
- **U2 — Weingarten vs projection bookkeeping.** The paper
  argument (§1.4, §2.3) is at the level of finite tensor
  algebra + Haar averaging; the Lean form of "Haar average
  of ρ^{⊗n} ⊗ ρ*^{⊗m} is the invariant projection" for the
  corpus's `repMatrix` representation may itself be a
  sub-brick inside F2. If it prices beyond L, F2 re-prices
  in the open before building — never mid-build.
- **U3 — no fallback inside this route.** If F2 dies, the
  record then carries four closures around 1b-B general and
  no fifth named family: the clause would stand OPEN with
  its approaches exhausted as named, and the next direction
  would be a new route decision (Jeff's call), not a
  continuation of this charter.
- **Fences (unchanged from the campaign):** fixed finite
  volume, even N; this route constructs no OS Hilbert space
  (1b-C), no transfer operator content (1b-D stands as
  landed; the transfer route stays terminated at R2), no
  limits, no gap. F3 landing would close Stage 1b-B's
  positivity clause at the finite level — Road Map Item 1's
  positivity half — and nothing beyond it: Items 2–5 of the
  Δ road map are untouched by this route. **NO CLAIM; Clay
  parts closed: 0.**

— BONES, for the record. Scoping is priced, kills are
registered before builds, and negative verdicts ship at the
same speed as positive ones.
