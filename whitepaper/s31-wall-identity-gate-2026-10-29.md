# S3-1 — The Wall-Identity Gate: Are Uniformity and Stratum-Factorization One Wall?

*Paper gate dossier, 2026-10-29. Brick S3-1 of the Span-3 first pier
(`scoping-span3-first-rung-2026-10-29.md` §2, decision point DP-1).
PAPER ONLY: nothing was built, no Lean file was touched, no proof
below is a Lean theorem unless it is cited as a landed one.*

**FENCES, ON THE FACE. NO CLAIM. Parts of the official Clay
statement closed by this gate: 0. Dials: 0/4.** Statement-grade
only — the gate discharges no hypothesis, proves no positivity,
takes no limit. Lorentzian/signature vocabulary unspent.

**DEPENDENCY, ON THE FACE.** S3-1 was pulled forward ahead of
S3-0. Brick S3-0 (the general-(G, ρ) formulation lift of the U(1)
uniformity file) has **not landed**: grep of the tree today finds
`UniformVolumeGap`, `GapPackage`, and `GapBound` at general
(G, ρ) **nowhere** — only the U(1) forms `UniformVolumeGapU1`,
`GapPackageU1`, `GapBoundU1` in `LatticeUniformGap.lean`. Every
statement below involving object (ii) therefore uses the
statement shape specified in the Span-3 memo's S3-0 entry
(§2 of that memo), mirrored clause-for-clause from the landed
U(1) file, and is labeled **S3-0-SPEC**. If K-S3-0 fires, every
arrow touching (ii) must be re-read at the U(1) seat only.

**Sources read in full for this gate:** the Span-3 scoping memo
(S3-0, S3-1, K-S3-1, §4/DP-1); the LOC-3 landing dossier
(`loc3-polymer-partition-landing-2026-10-27.md`) and its module
`PolymerPartition.lean`; `LayerKernelPos.lean` (A0) and its
landing dossier; the claim-path memo
(`scoping-claim-path-ym-2026-10-29.md`), Route D in particular;
`LatticeUniformGap.lean` (the U(1) template for (ii));
`PlaneCrossingCube.lean` (`layerAction`, `layerKernel`);
`PlaneCrossingBeta2.lean` (columns, `colDensC`, `colSites`);
`PlaneCrossingColumn.lean` (the pointwise column factorization).

---

## 0. Verdict, up front

**DP-1 VERDICT: TWO DISTINCT WALLS.** The stratum-factorization
wall and the uniformity wall do **not** stand or fall together
given landed results, and the finite 𝒜 campaign and Span 3 do
**not** merge into one campaign read at two scales. What the
map actually shows is narrower and more useful:

- Factorization (i) and the LOC-3 bridge (iii) **are** one wall:
  they are equivalent as propositions (paper proof, §2, arrows
  A1–A2), and that wall is also the finite core's wall, because
  (i) implies `LayerKernelPos` (𝒜 ⪰ 0), the A0-registered
  sufficient target for clause (a) (§2, arrow A3).
- Uniformity (ii) is a **second** wall, of a different logical
  shape: (i) feeds only the *antecedent* of `UniformVolumeGap`
  (its per-instance package, through clause (a)), and is silent
  on its *consequent* — a single δ working at every N. The step
  (i) → (ii) is blocked at a named place: **no landed statement
  converts per-(β, N) conclusions into an N-uniform margin**, and
  (i) itself is a per-(β, N) identity carrying no margin at all.
  The step (ii) → (i)/(iii) has no landed connecting statement
  of any kind (§2, arrows A4–A6).

Consequence for the claim-path memo's Route D: its verdict —
"the wall is the wall in both campaigns" — is **correct for the
pair it was written about** (the LOC-3 bridge and the finite
𝒜 ⪰ 0 campaign) and **does not extend to uniformity**. Read as
a statement about `UniformVolumeGap`, it is overstated, and
this gate is the correction of record: a kill or a landing on
either side of §2's map must not be booked as rerouting the
other wall. Details and grounds: §4.

**K-S3-1: does not fire for the gate's operative statement.**
The product-form factorization (i) is written below using only
landed definitions (`layerKernel`, `colZ`, `zPolymer`); no new
definition is invoked. K-S3-1 **does** fire for the second form
LOC-3 names — an independence hypothesis on the stratum measure
with respect to a column filtration — because no column
filtration exists or can exist as a partition (columns overlap;
§6). That variant's missing definition is named in §6 and
quarantined; the gate proceeds on the product form, which is
the form every arrow in the map actually needs.

---

## 1. The three statements, exactly

**Common setup** (the section setup of `LayerKernelPos.lean`,
which is the setup of `layerKernel` itself): `G` a group with
the measurability / topological-group / Borel / second-countable
instances of that file; `μG` a Haar probability measure on `G`,
left-, right-, and inversion-invariant; `ρ : G →*
unitaryGroup (Fin d) ℂ`; `N` with `[NeZero N]`. Standing
hypotheses are named where an arrow consumes them:
`hN : Even N`, `hρcont : Continuous fun g => repMatrix ρ g`,
`hd : 0 < d`, `hN2 : 2 ≤ N`.

The stratum is `α : LayerSite N → G` under the product measure
`πμG := Measure.pi fun _ : LayerSite N => μG` (the landed
abbreviation `stratumMeasure`). A **column** is
`P : LayerColumn N = LayerSite N × {ν : Fin 4 // ν ≠ 0}`; it
reads the stratum at exactly its two sites
`colSites P = {P.1, layerShift P.2.1 P.2.2 P.1}`
(`colWord_eq_of_agree`, `PlaneCrossingBeta2.lean`). Consequently
**each stratum site `α s` enters exactly 6 columns**: the 3
columns based at `s` (one per spatial direction ν ≠ 0) and the
3 columns whose shifted site is `s`. The columns are an
overlapping cover of the stratum, not a partition of it. This
one combinatorial fact drives everything below.

Landed pointwise facts (not in dispute, not the wall):

- `layerDensSum_eq_sum_columns` (Even N):
  `layerAction ρ β α u u' = β * ∑ P, colDensC ρ u u' P α`.
- `exp_neg_layerAction_eq_prod` (`PlaneCrossingColumn.lean`):
  pointwise in α, the Boltzmann factor **does** factor over
  columns,
  `exp (-(layerAction ρ β α u u')) = ∏ P, exp (-β * colDensC ρ u u' P α)`
  (in the file's (c, ν) indexing). The integrand factorizes.
  The integral over the shared α is what does not — that is
  the whole seam.

### (i) Column-factorization of the stratum integral — FACT

Stated as a `Prop` against `LayerKernelPos`'s setup, using
only landed definitions (`layerKernel`,
`PlaneCrossingCube.lean:782`; `colZ` and `zPolymer`,
`PolymerPartition.lean`):

> **StratumColumnFactorization (G, μG, ρ, N) : Prop** :=
> ∀ (β : ℝ) (u u' : LayerLink N → G),
>   `layerKernel μG ρ β u u'`
>     = `((zPolymer ρ μG β u u' : ℝ) : ℂ)`.

Equivalent integral form (under `hN : Even N`), by the two
pointwise facts above and `colZ_eq_integral_exp`:

> ∀ β u u',
>   `∫ α, ∏ P, Real.exp (-β * colDensC ρ u u' P α) ∂πμG`
>     = `∏ P, ∫ α, Real.exp (-β * colDensC ρ u u' P α) ∂πμG`,

i.e. **∫∏ = ∏∫** for this one integrand family: the stratum
integral of the column product is the product of the column
integrals, each column integral being `colZ ρ μG β u u' P`
(`colZ_eq_integral_exp`, landed). This is LOC-3's named missing
object in its product form, verbatim: "a product form of 𝒜
over columns" (LOC-3 dossier; `PolymerPartition.lean` header,
KL3-1). Note what FACT does **not** assert: no positivity, no
spectral content, no uniformity in anything. It is one scalar
identity per (β, N, u, u′).

Two properties of the right-hand side matter and are landed:
`colZ_independent` — `colZ` is independent of the column and of
(u, u′) — hence `zPolymer`'s value is a **constant in (u, u′)**;
and `zpolymer_pos` (under `hρcont`) — that constant is `> 0`
for every real β.

The second form LOC-3 names — "an independence hypothesis on
the stratum measure with respect to the column filtration" —
is **not** this statement and is not statable today; see §6.

### (ii) UniformVolumeGap (G ρ) under its package — S3-0-SPEC

Per the Span-3 memo's S3-0 spec, mirroring the landed U(1)
definitions clause-for-clause (U(1) citations in brackets):

> **GapBound (G ρ) (β : ℝ) (hN2 : 2 ≤ N) (δ : ℝ) : Prop** :=
> ∀ lam ∈ spectrum ℂ (transferOp μG ρ hN2 hρcont β),
>   lam ≠ 1 → ‖lam‖ ≤ 1 - δ.
> [Shape: the conclusion of `transfer_gap_of_formPos`,
> `LatticeTransferCompact.lean:2209`; U(1): `GapBoundU1`,
> `LatticeUniformGap.lean:79`.]
>
> **GapPackage (G ρ) (β : ℝ) (hN2 : 2 ≤ N) : Prop** :=
> IsCompactOperator ⇑(transferOp μG ρ hN2 hρcont β) ∧
>   TransferFormPos μG ρ β hN2 hρcont hd.
> [U(1): `GapPackageU1`, `LatticeUniformGap.lean:190`.]
>
> **UniformVolumeGap (G ρ) (β : ℝ) : Prop** :=
> (∀ (N : ℕ) [NeZero N] (hN2 : 2 ≤ N) (hN : Even N),
>     GapPackage (G ρ) β hN2) →
>   ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
>     ∀ (N : ℕ) [NeZero N] (hN2 : 2 ≤ N),
>       GapBound (G ρ) β hN2 δ.
> [U(1): `UniformVolumeGapU1`, `LatticeUniformGap.lean:267`.]

Read the quantifiers, because the verdict is in them:
the antecedent is **∀ N, (per-instance package)**; per-instance,
`transfer_gap_of_formPos` then gives **∀ N, ∃ δ_N > 0**. The
consequent is **∃ δ > 0, ∀ N** — the same δ at every volume.
`UniformVolumeGap` is exactly the assertion that the
∀∃-to-∃∀ swap over N is licensed here. Nothing else in the
statement mentions 𝒜, the stratum, columns, or polymers.

### (iii) The LOC-3 bridge — BRIDGE

`layerKernel` is ℂ-valued, but its integrand is a real
exponential cast to ℂ; the bridge is a statement about its real
density. Define (paper definition, in owned vocabulary;
`layerAction` is landed):

> **layerKernelReal (β : ℝ) (u u' : LayerLink N → G) : ℝ** :=
> ∫ α, Real.exp (-(layerAction ρ β α u u')) ∂πμG.

> **BridgeLOC3 (G, μG, ρ, N) : Prop** :=
> ∀ (β : ℝ) (u u' : LayerLink N → G) (P : LayerColumn N),
>   Real.log (layerKernelReal β u u')
>     = colCount N * Real.log (colZ ρ μG β u u' P).

That is: **the per-volume log-density of 𝒜 equals the polymer
density** — the right-hand side divided by `colCount N` is
exactly the quantity `ks_implication` (landed) proves is
`Real.log (colZ ρ μG β u u' P)` for `zPolymer`, N-independent
with an absolutely convergent defining series inside the LOC-2
radius `|β| < beta0`. The bridge identity itself is stated for
all real β (both sides are logs of positive reals once §2's
bookkeeping is in place); the radius enters only the KS
corollaries that a landed bridge would let the corpus transfer
from `zPolymer` to 𝒜 — the transfer LOC-3's fence currently
forbids ("no sentence in this corpus may borrow the polymer
radius for the kernel until the factorization exists").

One disambiguation the gate exists to enforce: **the landed
LOC-3 bridge is not (iii).** `log_zpolymer_eq` and
`ks_implication` are theorems about `zPolymer`, an object that
is a product over columns **by definition**. Statement (iii)
replaces `zPolymer` by 𝒜. The two "bridges" share a right-hand
side and nothing else.

---

## 2. The implication map

Labels, per the brick's charter: **PROVED** (a landed result,
or a complete paper derivation from landed results given here —
the two are distinguished on each arrow), **STATABLE-AND-OPEN**,
**NOT STATABLE** in current vocabulary. One auxiliary node is
used, marked as such: `LayerKernelPos β` (A0,
`LayerKernelPos.lean:77`) — 𝒜 ⪰ 0 on gauge-invariant
observables — because (i) was commissioned "as a Prop against
LayerKernelPos's setup" and the finite campaign's stake in (i)
runs through it.

| Arrow | Label | Grounds (summary) |
|---|---|---|
| A1. (i) FACT ⇒ (iii) BRIDGE | **PROVED** (paper, from landed) | FACT identifies 𝒜's density with `zPolymer`; `log_zpolymer_eq` is landed. Bookkeeping in §2.1. |
| A2. (iii) BRIDGE ⇒ (i) FACT | **PROVED** (paper, from landed) | `Real.log` is injective on positive reals; both densities are positive. §2.1. |
| A3. (i) FACT ⇒ `LayerKernelPos` (aux.) ⇒ clause (a) of `TransferFormPos`, per (β ≥ 0, N) | **PROVED** (paper, from landed) for FACT ⇒ `LayerKernelPos`; the second leg is A0's assembled sufficiency chain (landed components, dossier-grade assembly) | FACT makes 𝒜 a constant positive kernel in (u, u′); its pairing is `c · ‖∫ F‖²`-shaped, `c = zPolymer > 0`. §2.2. |
| A4. (i) FACT ⇒ (ii) `UniformVolumeGap` | **STATABLE-AND-OPEN — blocked at a named step** | (i) discharges clause (a) inside (ii)'s *antecedent* at each N (via A3). No landed statement produces the consequent's single δ; (i) carries no N-margin. The missing step is named in §2.3; it is a quantifier-strength gap, not a missing definition. |
| A5. (iii) BRIDGE ⇒ (ii) `UniformVolumeGap` | **STATABLE-AND-OPEN — blocked at the same step** | By A2 this is A4 restated. |
| A6. (ii) `UniformVolumeGap` ⇒ (i) FACT (equivalently ⇒ (iii)) | **STATABLE-AND-OPEN** | No landed statement connects transfer spectrum bounds to values or log-densities of `layerKernel`. (ii)'s antecedent *assumes* clause (a); clause (a) is strictly weaker than `LayerKernelPos` (sufficiency only, necessity unknown — A0), and `LayerKernelPos` itself says nothing about (u, u′)-constancy. §2.4. |
| A7. Polymer-internal bridge: `log zPolymer = colCount N * log (colZ P)`, with KS uniformity inside `|β| < beta0` | **PROVED** (Lean, landed) | `log_zpolymer_eq`, `ks_implication`, `PolymerPartition.lean`. This is the factorized-weight direction LOC-3 landed. It is **not** an arrow into (iii): its left-hand side is `zPolymer`, not 𝒜. |
| A8. Independence-form factorization ⇒ anything | **NOT STATABLE** | The antecedent cannot be written: no column filtration exists in owned vocabulary (§6, K-S3-1 partial firing). |

### 2.1 A1–A2: FACT ⇔ BRIDGE

Bookkeeping lemmas (paper; both are one-step consequences of
landed material, neither is a named Lean theorem today — the
formalization is priced in §7):

- (B-real) `layerKernel μG ρ β u u' = ((layerKernelReal β u u') : ℂ)`:
  the integrand of `layerKernel` is by definition the cast of
  the real integrand of `layerKernelReal`; integral commutes
  with the cast.
- (B-pos) `0 < layerKernelReal β u u'`: the integrand is
  `exp (-β * layerDensSum)` with
  `0 ≤ layerDensSum ≤ 2 * colCount N` landed
  (`layerDensSum_nonneg`, `layerDensSum_le`, Even N), so the
  integrand is bounded below by a positive constant on a
  probability space — the same argument as the landed
  `colZ_pos`, one level up.

A1: assume FACT. By (B-real), FACT says
`layerKernelReal β u u' = zPolymer ρ μG β u u'`. Apply
`Real.log` and divide: `log_zpolymer_eq` (landed; Even N,
`hρcont`) gives exactly BRIDGE's right-hand side. ∎ (paper)

A2: assume BRIDGE. Both `layerKernelReal β u u'` (B-pos) and
`zPolymer ρ μG β u u'` (`zpolymer_pos`, landed) are positive
reals with equal logarithms, hence equal; by (B-real) that
equality is FACT. ∎ (paper)

So **(i) and (iii) are the same proposition in two dialects** —
the identity dialect and the log-density dialect. Any future
result about one is a result about the other, at the cost of
the §7 bookkeeping brick and nothing else.

### 2.2 A3: FACT ⇒ 𝒜 ⪰ 0 (per instance)

Assume FACT at (β, N), with `hρcont`. In the pairing of
`LayerKernelPos`, the kernel value at each (u, u′) is, by FACT
and `colZ_independent`, the **same** positive real number
`c = zPolymer ρ μG β u u' > 0` (`zpolymer_pos`). The pairing
therefore separates:
`Re ∫∫ conj(F u) * c * F u' = c * ‖∫ F‖²`-form — in the file's
exact shape, `c` times the real part of
`(∫ conj F) * (∫ F)`, which is `c * ‖∫ F dπ‖² ≥ 0` — for every
gauge-invariant `F` (indeed for every `F`; gauge invariance is
not even consumed). Hence `LayerKernelPos β`. ∎ (paper)

Then A0's chain: `LayerKernelPos` at all β ≥ 0 ⇒ clause (a) of
`TransferFormPos` (β1 factorization
`planeCrossingMarginal_layerKernel` + α-remainder twirl
reduction + Schur product theorem; assembled on A0's landing
dossier, components landed, the assembly itself dossier-grade
prose, not one Lean theorem). Clause (b) is independently
discharged at general (G, ρ) (`fixed_mem_span`). So FACT feeds
**both** conjuncts' neighborhood of `GapPackage` except
compactness, which remains a separate package hypothesis at
general β (per the U(1) file's D-1 header, conditional on
`HDen` there; nothing in FACT speaks to it).

Note the direction of travel: FACT is vastly stronger than
𝒜 ⪰ 0 in one respect (it asserts (u, u′)-**constancy** of 𝒜,
which PSD does not need) and orthogonal in another (it is a
value identity, proved or refuted per (β, N), with no spectral
content). The finite campaign should record this honestly:
FACT is *a* sufficient route to clause (a), and an expensive
one — it buys PSD by collapsing the kernel to a constant.

### 2.3 A4–A5: where FACT → Uniformity stops

`UniformVolumeGap`'s consequent is `∃ δ ∈ (0, 1], ∀ N,
GapBound δ`. Every landed theorem that produces a `GapBound`-
shaped conclusion produces it **per instance**:
`transfer_gap_of_formPos` gives `∃ δ > 0` at fixed (β, N) from
the fixed-(β, N) package, by a compactness squeeze that is
explicitly non-quantitative (Span-3 memo, P-1). FACT, via A3,
can discharge the clause-(a) part of the package at every N —
that is, FACT helps satisfy (ii)'s **antecedent**. It says
nothing toward the consequent, for a structural reason that no
cleverness removes: FACT is a family of identities indexed by
(β, N, u, u′) with **no modulus in N anywhere in its
statement**, and `LayerKernelPos`, its strongest landed
consequence, is likewise margin-free — the corpus's own fence
at the β⁴ endpoint is that the relevant functional "is not
bounded away from zero: zero margin, no cushion" (PW-5). A
per-instance positivity with no margin is exactly the shape
whose gap may close with N; the corpus already owns a
quantitative warning of the shape, the Doeblin bound
δ₀(β, N) = exp(−192|β|N⁴) — a proved per-instance gap quantity
that **dies** as N grows (a mixing bound, cited here only as
evidence that per-instance ⇒ uniform is a real step in this
corpus, not as a counterexample to (ii), which it is not).

**The named missing step for A4/A5** is therefore not a
definition and not FACT itself; it is a *quantitative* statement
of a kind no brick has landed at general (G, ρ): an N-uniform
lower margin for the 𝒜-pairing (or equivalently for the
transfer form) that the A0 sufficiency chain would transport
to a single δ. §5 states the sharpest form of it. Until such a
statement exists and is proved, A4/A5 are open with the
obstruction located, not merely unattempted.

### 2.4 A6: Uniformity says nothing about the stratum

(ii) quantifies over the spectrum of `transferOp` on
`osSpace`. Neither `layerKernel`'s values, nor `colZ`, nor any
log-density occurs in (ii), in `GapPackage`, or in the proof of
`transfer_gap_of_formPos`. The only landed bridge between the
transfer world and the 𝒜 world is the A0 sufficiency chain,
which runs `LayerKernelPos ⇒ clause (a)` — the **opposite**
direction from what A6 would need, and one-way: necessity of
`LayerKernelPos` for clause (a) is unknown (A0, on its face).
And even a proved `LayerKernelPos` at every N would not give
FACT, since PSD kernels need not be constant in (u, u′) — the
β⁴ dependent coefficient κ₄^dep is precisely a landed,
generally (u, u′)-dependent component of 𝒜 whose diagonal sign
the corpus has spent PW-1…PW-5 establishing as ≥ 0 where it is
not zero; nothing landed asserts it vanishes identically, and
FACT would require exactly that vanishing at every order.
A6 is statable (given S3-0-SPEC for its antecedent) and open,
with no mechanism proposed by any landed statement.

---

## 3. The two commissioned questions

**Q1. Does the bridge proof, read literally, consume exactly
a factorization?**

Two readings, two different answers — and keeping them apart
is the gate's first job.

- *The landed LOC-3 proof* (`log_zpolymer_eq`,
  `ks_implication`): **consumes no factorization at all.** Its
  proof steps are `colZ_eq_integral_exp` (each column's
  activity series sums, under its own stratum integral, to
  `∫ exp (-β * dens_P)` — a dominated `integral_tsum`
  interchange inside one column), `colZ_independent`,
  `Real.log_prod` over the columns with `zpolymer_pos`, and
  LOC-2's `ks_criterion_full`. The product over columns enters
  because `zPolymer` is **defined** as that product. No
  statement of the form ∫∏ = ∏∫ for the shared stratum is
  stated, used, or needed.
- *The 𝒜-bridge (iii), if it were ever proved*: **yes,
  exactly FACT, no more and no less.** By §2.1, BRIDGE ⇔ FACT
  modulo the two bookkeeping lemmas (B-real), (B-pos), whose
  proofs consume only landed bounds. A proof of (iii) is a
  proof of (i) after one logarithm; a proof of (i) is a proof
  of (iii) after one logarithm. In particular the bridge does
  **not** consume the stronger independence hypothesis of §6,
  nor any positivity, nor any uniformity. LOC-3's dossier
  sentence — "the missing object is a column-factorization of
  the stratum integral" — is, read literally against §2.1,
  exactly right for its product form.

**Q2. Would a factorization give the bridge *and* feed
uniformity?**

- *The bridge*: **yes, immediately and completely** (A1), and
  with it the KS transfer: inside `|β| < beta0`, log 𝒜's
  per-volume density would inherit the N-independence and the
  absolute-convergence majorant that `ks_implication` lands
  for `zPolymer`. That transfer is the entire LOC-line payoff
  of FACT.
- *Uniformity*: **no — it feeds uniformity's hypothesis, not
  uniformity.** Via A3, FACT at (β, N) discharges clause (a)
  at (β, N), for every N separately; clause (b) is already
  discharged at general (G, ρ); compactness is untouched.
  That assembles (ii)'s antecedent, volume by volume. The
  consequent of (ii) — one δ for all volumes — is a statement
  FACT does not touch, because neither FACT nor any of its
  landed consequences carries an N-uniform margin (§2.3).
  Anyone booking a future FACT landing as progress on
  `UniformVolumeGap` itself, rather than on its package, would
  be repeating, inside this program, the exact conflation this
  gate was commissioned to test.

## 4. DP-1 verdict, at full rank

**The uniformity wall and the stratum-factorization wall are
two distinct walls.**

Grounds, from the map and nothing else:

1. **One wall is fully accounted for.** (i) ⇔ (iii) (A1–A2),
   and (i) ⇒ 𝒜 ⪰ 0 ⇒ clause (a) (A3). The factorization wall
   is a per-(β, N) scalar identity about one stratum integral;
   its entire known sphere of influence is: the LOC-3 bridge,
   the KS transfer to log 𝒜, and the finite core's sufficient
   route. Route D's "the wall is the wall" is true *inside
   this sphere*.
2. **The other wall's essential content appears nowhere in
   that sphere.** `UniformVolumeGap`'s content beyond its
   antecedent is the ∃δ∀N swap. No statement in FACT's sphere
   — not FACT, not BRIDGE, not `LayerKernelPos` — contains an
   N-indexed margin, so no composition of landed implications
   from that sphere reaches (ii)'s consequent (A4–A5, blocked
   at the named margin step).
3. **No road back exists either.** (ii) has no landed
   implication into the 𝒜 world at all (A6); its antecedent
   assumes, rather than proves, the package that FACT would
   feed. Two propositions neither of which implies the other
   given landed results, whose known consequences are disjoint
   except for sharing one *hypothesis* (the per-instance
   package), are two walls that happen to stand in the same
   corridor — the package is the corridor, not the wall.

**Campaign consequence (DP-1, second branch, as pre-registered
in the Span-3 memo §4):** the finite 𝒜 campaign and Span 3 do
not merge. A landing of FACT would close the LOC-3 seam and
discharge clause (a) — a finite-campaign event of the first
rank — and would leave Span 3's first consumed hypothesis,
`UniformVolumeGap`, exactly as open as it is today, because
Span 3 consumes the *consequent*, not the package. A kill of
FACT (e.g. a certified (u, u′)-dependence of 𝒜 at some seat —
κ₄^dep taking two distinct values at one seat would be one,
since FACT, holding at every β, forces every Taylor
coefficient of 𝒜 to be (u, u′)-constant)
would kill the bridge and this sufficient route to clause (a),
and would say nothing against uniformity, whose proof, if one
exists, must come from a mechanism with an N-margin in it.
The pier's later bricks must not borrow hope across the two
walls in either direction.

## 5. The sharpest identifying Prop

Statable (modulo the S3-0-SPEC dependency for its right-hand
side). The two walls would be identified by exactly the
stand-or-fall-together assertion, and nothing weaker identifies
them:

> **WallIdentity (G ρ) (β : ℝ) : Prop** :=
> (∀ (N : ℕ) [NeZero N], Even N →
>     StratumColumnFactorization (G, μG, ρ, N) at β)
>   ↔ UniformVolumeGap (G ρ) β        *(S3-0-SPEC)*.

This is sharp in the literal sense: it asserts precisely the
equivalence DP-1 asked about, with no mechanism smuggled in.
The gate's finding is that `WallIdentity` is **not** supported
by any landed implication in either direction (§2, A4–A6) and
its forward direction is blocked at a step the map names; it
is recorded here as the Prop whose future proof *or refutation*
would settle DP-1 mathematically, superseding this gate's
statement-level verdict. On today's record it must not be
assumed, quoted, or used as a campaign premise.

The mechanism-shaped strengthening whose truth would *collapse*
the two walls in practice — by supplying the missing step of
§2.3 rather than asserting the equivalence — is also statable,
and is the form a future attack would actually target:

> **UniformMarginFactorization (G ρ) (β : ℝ) : Prop** :=
> ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
>   ∀ (N : ℕ) [NeZero N] (hN2 : 2 ≤ N) (hN : Even N),
>     StratumColumnFactorization (G, μG, ρ, N) at β ∧
>     (GapPackage (G ρ) β hN2 → GapBound (G ρ) β hN2 δ).
> *(S3-0-SPEC for the Gap- names.)*

Its truth implies FACT at every volume and (ii)'s consequent
under (ii)'s antecedent, by construction. It is strictly
stronger than both walls' conjunction in one respect — it
welds the *same* δ to the factorized volumes — and that weld
is precisely the content today's corpus does not own in any
form. It is a target pin, not a result and not a priced proof.

## 6. K-S3-1 check

K-S3-1 fires iff an implication statement cannot be written
without invoking the missing factorization **definition** (not
just its truth), in which case the deliverable becomes that
named missing definition, A0-shaped.

- **Product form: K-S3-1 does not fire.** §1(i) is written
  entirely from landed definitions (`layerKernel`, `colZ`,
  `zPolymer`, `colDensC`, `layerAction`). FACT is a Prop whose
  *truth* is missing, not a definition whose *statement* is
  missing. Every arrow in §2 is stated. The gate proceeds.
- **Independence form: K-S3-1 fires, and stops there.** LOC-3's
  alternative — "an independence hypothesis on the stratum
  measure with respect to the column filtration" — cannot be
  written, for a reason stronger than absence: the would-be
  filtration cannot be a filtration by columns. The stratum
  measure `πμG` is a product over **sites**; each column's
  σ-algebra is generated by its two sites (`colSites P`), and
  columns overlap (§1: every site in 6 columns), so the column
  σ-algebras are not independent sub-σ-algebras of a product
  decomposition — they share coordinates, and a random variable
  is not independent of a non-degenerate function of itself.
  There is no `ColumnFiltration` object in the tree, and the
  naive one is not merely unbuilt but ill-posed as stated.
  **The named missing definition, A0-shaped, as K-S3-1
  requires:** a *site-partition surrogate* — a partition of
  `LayerSite N` (or a measurable equivalence / grouping of
  columns with disjoint site-supports, e.g. a proper coloring
  of the column-overlap graph) together with, for each block,
  a factorized sub-integral, such that 𝒜 is reassembled from
  block factors by a stated theorem. No such definition is
  proposed as true, useful, or priced by this gate; it is
  named so the record shows exactly which object the
  independence dialect would need, and the dialect is
  quarantined until and unless someone builds it. The gate's
  map does not depend on it: every arrow LOC-3's bridge needs
  runs through the product form.

## 7. Recommended formalization follow-ons (priced, not built)

PAPER ONLY was this dispatch's fence; the following are
specified for the parent to price into the queue, not built
here.

- **S3-1-F1 (S). The FACT ⇔ BRIDGE formalization.** A small
  module stating `StratumColumnFactorization` and
  `BridgeLOC3` as Lean Props (definitions only, A0-style) and
  proving their equivalence: the two bookkeeping lemmas
  (B-real) (integral of a cast) and (B-pos) (positivity of
  `layerKernelReal` from `layerDensSum_nonneg` /
  `layerDensSum_le`, following the landed `colZ_pos` argument),
  then A1/A2 via `log_zpolymer_eq` and `Real.log` injectivity
  on positives. The paper proof is complete in §2.1; this is
  transcription-grade. *Buys:* arrows A1–A2 become T1, and both
  LOC-3's seam and any future FACT kill/landing register
  against Lean statements.
- **S3-1-F2 (S–M). FACT ⇒ `LayerKernelPos`, formalized.**
  The constant-kernel pairing computation of §2.2
  (substitute FACT + `colZ_independent`, separate the double
  integral, close with `zpolymer_pos`). S if the pairing
  manipulation follows the landed Gram/OS pairing patterns
  directly; M if the A0 sufficiency chain's assembly
  (`LayerKernelPos` ⇒ clause (a) as one Lean theorem, currently
  dossier-grade) is folded into the same brick — recommended
  to fold it in, since A3 is the finite campaign's reason to
  care about FACT. *Buys:* a FACT landing would then
  machine-discharge clause (a) modulo compactness, with no
  prose link in the chain.
- **Not priced, deliberately:** any brick aimed at A4, A5, or
  A6 (no proof exists to formalize; pricing one would price a
  discovery, not a formalization); the §6 site-partition
  surrogate (a definition in search of a use — revisit only if
  a mechanism proposes one); `UniformMarginFactorization` as a
  proof target (FRONTIER; as a *statement pin* it can ride
  inside S3-0's scope at no extra brick, and this gate
  recommends the parent attach it there).

---

*Gate ends. NO CLAIM — parts of the official Clay statement
closed by this gate: 0. Dials: 0/4. DP-1 verdict: two distinct
walls — factorization ⇔ bridge is one wall, shared with the
finite 𝒜 campaign; uniformity is a second wall, downstream of
the first wall's strongest consequence and untouched by it.
S3-0 dependency: object (ii) throughout is S3-0-SPEC, the
not-yet-landed general-(G, ρ) lift specified in the Span-3
memo. This dossier is a whitepaper document, not a landing:
no README, census, or commit change is made or implied by it.*
