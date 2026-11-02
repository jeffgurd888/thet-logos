# SCOPING MEMO — CLS-3c-A: the `piAnti` base-status cell (Lane 1's last open cell)

Date: 2026-11-02. Scoping only — no Lean builds, no commits.
Governing pack: `routeb-general-scratch/pack-cls-3c-a-scoping.md`.
Sources read in full: `lean/ThetLogos/DialOneAntiparticleChapter.lean`
(CLS-3c module), `whitepaper/cls3c-landing-2026-11-02.md`,
`lean/ThetLogos/DialOneSeatTiePin.lean` (the frozen `DialOneBase`
pin), `lean/ThetLogos/Track1Closure.lean` (the first-order
machinery), plus bounded reads of `Track1RouteB.lean` (π₁'s def,
entry tables, `pi1_det_gen`), `PreOptionARepresentation.lean`
(π₀'s def, `AF` operations), `FiniteSpectralTriple.lean`
(`DF_oneGen` / `buildDirac`), `DialOneGammaFamilyPin.lean`
(the strengthened family), `DialOneClassificationPin.lean`
(CLS-0, `weightAt` / `commonWeightVector` / `WeightQuestionW`),
and the CLS-1 / CLS-2b landing dossiers.

**NO CLAIM; Dial 1 = 0; all dials 0/4. Classification data
only: parts of any official statement closed by this memo: 0.
Every audit statement below is T2 (scoping arithmetic /
proof-shaped transport) until the priced brick lands it at T1;
every landed fact cited is T1 in its own module.**

---

## 0. Headline of the scoping

The fork does **not** land where CLS-3c's seam guessed. There
is an algebra automorphism of `AF` — entrywise conjugation of
the colour summand alone — under which `piAnti` is *literally*
π₁ precomposed with that twist. Every clause of `DialOneBase`,
every clause of the strengthened family, and the weight
relation are covariant under that twist (the twist fixes the
clause vocabulary and flips only the β-sign of the two
generator families). So the expected verdict is **branch (ii)
by the mechanism of branch (iii)**: `piAnti` **holds the base,
holds the full strengthened family, and carries exactly the
table's weights** — a strengthened point off the toggle orbit
that **answers CLS-0's Grade-W question YES**. No
Track1Closure-style fresh entry computation is needed; the
brick is a transport, priced S–M below. K-CLS-3c-A is
registered in §5 — it fires only against an error in *this*
scoping.

---

## 1. The computation's shape — clause by clause

`DialOneBase π` (frozen in `DialOneSeatTiePin`, in order) is:
(1) `afMul` law, (2) `afAdd` law, (3) `afStar` law,
(4) `π afOne = 1`, (5) `π afZero = 0`, (6) `Function.Injective π`,
(7) grading (`gammaF * π a = π a * gammaF`), (8) order-zero
against `piOp ∘ π`, (9) first-order (entrywise vanishing of
the double commutator `[[DF_oneGen, π a], piOp (π b)]`, Yukawas
universally quantified), (10) unimodularity (∃ primitive
`(α, β)`, `det π (u1ParamGen α β t) = 1 ∀ t`).

`piAnti` differs from `pi1` in exactly two branches
(`DialOneAntiparticleChapter`, the `piAnti` def): slots
18–23 and 26–31, `star (a.color k l)` ↦ `a.color k l`
(guarded by `iso_i = iso_j`). Which clauses can read that at
all:

| Clause | Reads slots 18–23 / 26–31? | Can it separate the verdicts? |
|---|---|---|
| 1 `afMul` | **Yes, directly** — the clause quantifies over all `a b` and all entries; the antiquark entries are colour products. | No — naked and conjugated colour actions are both multiplicative (`star` is a ring hom on entries; identity is too). |
| 2 `afAdd` | **Yes, directly**, same shape. | No — `star` and identity are both additive on entries. |
| 3 `afStar` | **Yes, directly — the most conjugation-sensitive clause in form.** | No — `afStar` supplies `a.color.conjTranspose` and the matrix side supplies `(·)ᴴ`; at an antiquark entry both reps collapse to the *same* value `a.color l k` (π₁: `star (star (a.color l k))`; `piAnti`: `star (a.color l k)` from the `ᴴ` alone). |
| 4 `afOne` | Yes (`afOne.color = 1`, `star 1 = 1`). | No — value-identical at the unit. |
| 5 `afZero` | Yes (`star 0 = 0`). | No — value-identical at zero. |
| 6 Injective | **Yes, essentially** — the particle blocks of *both* reps are colour-blind (`q ⊗ I₃`, `u1` diagonals); the colour summand is recoverable *only* from slots 18–23 / 26–31. | No — `star` is injective and the naked read is injective; colour is recovered either way. |
| 7 Grading | Reads the entries, but only their sector shape: both antiquark blocks lie inside single γ-sectors (16–23 and 24–31), and `gammaF` is constant on each. | No — conjugation-blind by sector shape. |
| 8 Order-zero | **Yes, twice over** — directly at antiparticle seats, and via `piOp` at every *particle* quark seat (`partner` sends 2–7 ↦ 18–23, 10–15 ↦ 26–31, so `piOp (π b)`'s particle-quark blocks *are* the antiquark blocks of `b`, transposed). | No — see §2. π₀'s failure mode is absent from `piAnti` (next row). |
| 9 First-order | **Yes, in exactly two routes** (detailed below). | No — both routes are verdict-blind to the un-conjugation. |
| 10 Unimodularity | **Yes — the diagonal.** `piAntiBVal = +1` on both antiquark blocks vs `pi1BVal = −1`: `∑ B` flips `−12 ↦ +12`. | No — but it is the one clause whose *witness changes*: det exponent `−4α − 12β` (π₁) ↦ `−4α + 12β` (`piAnti`), primitive witness `(3, −1)` ↦ **`(3, 1)`** (π₀'s direction), `gcd 3 1 = 1`, det `= 1`. |

**Clause 9 in detail** (the pack's named question — which of
Track1Closure's witness entries involve the un-conjugated
block):

- **π₀'s landed witness reads no colour at all.**
  `Track1Closure.DF_first_order_entry_09` / `first_order_killed`
  are supported at entry `(0, 9)`, via `DF (1, 9) = ye`,
  `pi0 witA (0, 1)`, and `rho0 witB` at `(0, 0)`, `(0, 1)`,
  `(9, 9)` — which read π₀ at seats 16, 17 (the antilepton
  bolt `λ̄ • q̄`) and 25 (the `e_R^c` singlet `star a.u1`).
  Slots 18–23 / 26–31 are never touched. At every one of
  those seats `piAnti` agrees with `pi1` (CLS-3c's def
  changes nothing at 16–17 or 24–25), and π₁'s first-order
  stands (`Track1RouteB.pi1_first_order`, T5 there). So the
  `(0, 9)` computation transports to `piAnti` as a
  *vanishing* entry, not a kill — this is exactly why
  CLS-3c correctly refused to transport π₀'s kill, stated
  now at entry level.
- **Route (a): the `[DF, π a]` antiquark cross-block is `0`
  for both reps.** `DF_oneGen = buildDirac A (Ā) 0 0` connects
  the antiquark sectors only Lc ↔ Rc, through the diagonal
  B-block (Yukawas `Yu`/`Yd` by flavour, diagonal in the
  `(colour, flavour)` index). For `i` in 18–23, `j` in 26–31
  both terms of the commutator collapse to
  `Y(iso) * (colour entry)` — with the *same* colour entry,
  because Lc and Rc carry the same convention within each
  rep (both `star`, or both naked). They cancel identically.
  The first commutators of `piAnti` and `pi1` are in fact
  equal as matrices.
- **Route (b): `piOp (π b)` at particle quark seats, in the
  particle-sector rectangles (0–7 ↔ 8–15).** Here the double
  commutator does read `b`'s antiquark blocks. But
  `[DF, π a]` is colour-diagonal on the quark rectangles and
  the antiquark blocks are flavour-diagonal (`iso_i = iso_j`
  guard), so each product sum collapses colour-diagonally —
  the CLS-2b colour-sum-collapse mechanism — to a *single*
  colour entry factor, `star (b.color k l)` for π₁,
  `b.color k l` for `piAnti`, **common to both products** of
  the double commutator. The cancellation is preserved.
  Antiparticle-sector entries of the double commutator read
  only particle blocks through `piOp` and the zero cross-block
  of route (a): they are entry-identical to π₁'s and vanish.

**No clause of the base separates `piAnti` from `pi1` in
verdict.** Every clause either is value-identical at the
changed entries, or reads them through a construction
(`piOp`, the `ᴴ`/`conjTranspose` pair, the diagonal
determinant) whose verdict is invariant under the change.

---

## 2. The twist — why transport is a theorem, not an analogy

Define (new, this brick's one definition; working label —
practical naming only):

```
colourTwist (τ) : AF → AF
  τ a := ⟨a.u1, a.q, a.color.map (starRingEnd ℂ)⟩
```

i.e. entrywise conjugation of the M₃ summand, ℂ and ℍ
summands untouched. Audit facts (each short, entry-level):

- **τ is an `AF`-algebra automorphism**: `ψ(M) = M.map star`
  satisfies `ψ(M * N) = ψ(M) * ψ(N)` (entrywise:
  `star (∑ Mᵢₖ Nₖⱼ) = ∑ star Mᵢₖ * star Nₖⱼ`), additivity,
  `ψ(1) = 1`, `ψ(0) = 0`; and `ψ(Mᴴ) = (ψ M)ᴴ` entrywise
  (both sides are `M l k` after the two stars cancel —
  this is clause 3's collapse, at the algebra level).
  Hence `τ (afMul a b) = afMul (τ a) (τ b)`, likewise
  `afAdd`, `afStar`, `afOne`, `afZero`; `τ` is involutive
  (`star_star`), hence bijective.
- **`piAnti = pi1 ∘ τ`, exactly**: in the two changed
  branches `pi1 (τ a)` carries
  `star ((τ a).color k l) = star (star (a.color k l))
  = a.color k l`; every other branch reads only `a.u1`,
  `a.q`, `star a.u1` — all τ-fixed. One entry proof by the
  sector split of the two defs, `star_star` closing the two
  antiquark branches.
- **τ flips only β in the generator families**:
  `τ (u1Gen α β) = u1Gen α (−β)` (colour seat
  `(β·I) • 1 ↦ star(β·I) • 1 = (−β·I) • 1`) and
  `τ (u1ParamGen α β t) = u1ParamGen α (−β) t`
  (colour seat `exp(β t i) • 1 ↦ exp(−β t i) • 1`, the landed
  `Track1RouteB.star_exp_int` pattern).

Transport is then substitution, clause by clause, in π₁'s
*landed* base tuple (`DialOneGammaTraceChecks.dialOneBase_pi1`,
assembled from `pi1_afMul / pi1_afAdd / pi1_afStar / pi1_one /
pi1_zero / pi1_injective / pi1_grading_even / pi1_order_zero /
pi1_first_order / pi1_det_gen`):

- Clauses 1–5: rewrite by `piAnti = pi1 ∘ τ` and the τ-law,
  then cite π₁'s clause at `(τ a, τ b)`.
- Clause 6: `Injective (pi1 ∘ τ) = Injective pi1 ∘ bijective τ`.
- Clause 7: `piAnti a = pi1 (τ a)`; cite π₁'s clause at `τ a`.
- Clauses 8, 9: the clause at `(a, b)` for `piAnti` is
  *literally* π₁'s clause at `(τ a, τ b)` — `piOp (piAnti b)
  = piOp (pi1 (τ b))`, `DF_oneGen` untouched. One step each.
  (This is the formal content behind §1's route-(b) collapse
  audit; the brick does not need the entry computation.)
- Clause 10: transport π₁'s existential witness
  `(α₀, β₀)` to `(α₀, −β₀)` (`gcd` unchanged), or directly
  the frozen witness `(3, 1)` via `pi1_det_gen`:
  `det (piAnti (u1ParamGen 3 1 t))
   = det (pi1 (u1ParamGen 3 (−1) t)) = exp 0 = 1`.

The family transports the same way from
`DialOneGammaFamilyChecks.gammaFamily_pi1`
(`⟨c3lep_pi1, c3col_pi1, feR_pi1⟩`): each clause at `(α, β)`
for `piAnti` is π₁'s clause at `(α, −β)`, since
`piAnti (u1Gen α β) = pi1 (u1Gen α (−β))`. (Independently,
the scoping's sub-sum audit agrees: `C3lep` and `FeR`
projections contain no B-support — `piAntiBVal = 0` at seats
{0,1,8,9,16,17,24,25} and {9,25} — so they are identical to
π₁'s; `C3col c` contains antiquark seats
18+2c, 19+2c, 26+2c, 27+2c, whose γ-weighted Banti sum is
`(−1−1) + (+1+1) = 0` per colour, the per-colour shadow of
CLS-3c's landed `gamma_weighted_beta_direction_zero`.)
`C3 piAnti` is already landed (`c3_piAnti`).

---

## 3. The fork, stated exactly

- **(i) `piAnti` FAILS base at a computable witness —
  DEAD at scoping rank.** The only landed first-order
  witness in the corpus (π₀'s `(0, 9)`) provably does not
  read the changed blocks (§1) and transports as a
  vanishing entry; order-zero's π₀ failure reads the
  antilepton bolt `piAnti` does not have. No other witness
  is visible to the audit, and if §2's transport is
  correct none can exist. Branch (i) survives only as the
  K-CLS-3c-A trigger (§5).
- **(ii) `piAnti` HOLDS base — EXPECTED, and the fork's
  second half lands with it.** By §2: `DialOneBase piAnti`
  (transport), `GammaFamily piAnti` (transport),
  `C3 piAnti` (landed) — hence
  **`DialOneStrengthenedFam piAnti`**. And its weights are
  already visible to the scoping: along its unimodular
  direction `(3, 1)` the diagonal exponent is
  `Dₛ = 3·Aₛ + Bantiₛ = Wₛ` at *every* seat (antiquark
  seats: `0 + 1 = 0 − (−1)`; elsewhere `Banti = B = 0`),
  so the lifted weight at seat `s` is
  `Dₛ + D_{partner s} = Wₛ + W_{partner s}
  = commonWeightVector s` by that vector's definition.
  Formally: `piAnti (u1ParamGen 3 1 t)
  = pi1 (u1ParamGen 3 (−1) t)` as matrices, so
  **`weightAt piAnti commonWeightVector`** transports from
  the landed `DialOneShapeBIdentification.weightAt_pi1_common`
  (the opposite direction `(−3, −1)` gives
  `−commonWeightVector`, as for π₁).
- **Consequences, at full rank.** `piAnti` is a
  strengthened point **off the toggle orbit**: it is not
  `pi1` (landed, `piAnti_ne_pi1`), and it is no
  `orbitRep b` — CLS-2b's `orbit_classification_complete`
  leaves only `b = 0` (π₁, excluded) and `allSwapBits`,
  whose point is excluded because it does *not* carry the
  common weights (landed `allSwap_not_weightAt_common`)
  while `piAnti` does. Therefore:
  - **The strengthened set is strictly larger than the
    orbit analysis showed**: it contains at least
    {π₁, the uniform triple swap, `piAnti`}. CLS-2b's
    classification is untouched — it classifies the
    *orbit*, and CLS-3c's boundary theorem already fences
    uniqueness to toggles / named directions.
  - **CLS-1 weight extraction applies to `piAnti` and its
    weights are the table's** (above — not new weights, the
    common vector itself).
  - **`WeightQuestionW` (CLS-0, Grade W) is answered YES**:
    `⟨piAnti, DialOneStrengthenedFam piAnti, piAnti ≠ pi1,
    weightAt piAnti commonWeightVector⟩`. Grade W's open
    content was exactly the non-π₁ realizability of the
    common weights; `piAnti` realizes them. This does not
    touch any forcing statement: `piAnti` is a second
    *model* of the strengthened set carrying the table's
    weights, not a compensator with wrong weights, and no
    landed kill is disturbed (D1-A / D1-A′ kills stand —
    their counterexamples are other representations).
  - Lane 1 / Grade T: with this brick, the antiparticle
    chapter closes with **no open cells** — the direction
    is C3-invisible, base-holding, family-holding,
    weight-carrying, and off-orbit.
- **(iii) The third outcome — REAL, as the mechanism of
  (ii), with one refinement of the pack's wording.** The
  pack phrases (iii) as "no base clause can read the
  un-conjugation at all". The audit refines that: clauses
  1–3, 6, 8, 9, 10 *do* read the changed entries at the
  statement level (§1 table) — what no clause can read is
  a **difference in verdict**, because `DialOneBase` as a
  whole is covariant under precomposition with the colour
  twist τ, and `piAnti = pi1 ∘ τ`. Base status transports
  from π₁ identically (same proof terms, τ-substituted);
  the only non-identical datum is clause 10's witness
  direction, `(3, −1) ↦ (3, 1)`. The transport is priced
  in §4 — it *is* the brick; there is no separate
  first-order computation to price beside it.

---

## 4. Price

**Band S–M. Point estimate ≈ 35–55 strict, defs 2, one new
module, single lane** (suggested seat:
`lean/ThetLogos/DialOneAntiparticleBase.lean`, importing
`DialOneAntiparticleChapter` and
`DialOneShapeBIdentification` — acyclic: neither imports
the other today). No interference with the 𝒜 ⪰ 0 core chain.

Breakdown:

- τ infrastructure (`colourTwist` def; ψ entry lemmas for
  `map star` over `*`, `+`, `1`, `0`, `ᴴ`; τ laws for
  `afMul/afAdd/afStar/afOne/afZero`; involutive/bijective;
  `τ_u1Gen`, `τ_u1ParamGen`): ~15–25 strict. Risk: Mathlib
  naming for `star` over a finite sum — fallback is a
  ~15-line entry proof (`Finset.star_sum`-shape); priced in.
- `piAnti_eq_pi1_colourTwist` (the one genuine entry proof:
  sector split of the two defs, `star_star` in the two
  antiquark branches): ~10–20 strict.
- `dialOneBase_piAnti`: ten transports, 1–4 lines each off
  `dialOneBase_pi1`'s components: ~10 strict.
- `gammaFamily_piAnti` (three transports off
  `gammaFamily_pi1`), `strengthenedFam_piAnti` (assembly
  with landed `c3_piAnti`): ~5 strict.
- `weightAt_piAnti_common` (matrix equality at `(3, 1)` +
  `weightAt_pi1_common`), `weightQuestionW_piAnti`
  (assembly with landed `piAnti_ne_pi1`), off-orbit
  corollary (CLS-2b classification + `allSwap_not_weightAt_common`):
  ~5 strict.
- Headline assembly + `#print axioms` (expected standard
  `[propext, Classical.choice, Quot.sound]` throughout).

**Fallback, only if the τ route snags** (e.g. the
`piAnti = pi1 ∘ τ` entry proof explodes past its estimate):
direct clause-by-clause entry transport in CLS-2b's style —
**band M, 80–120 strict** — re-running π₁'s antiquark-block
entry lemmas with `star` deleted. Not expected to be needed;
the (0, 9)-style fresh first-order computation CLS-3c
imagined is **not** the fallback — §1 shows it cannot be
the shape of any proof or kill here.

---

## 5. Frozen target Props and K-CLS-3c-A

The brick freezes exactly these targets (names are the
brick's working labels):

```
def colourTwist (a : AF) : AF :=
  ⟨a.u1, a.q, a.color.map (starRingEnd ℂ)⟩

theorem piAnti_eq_pi1_colourTwist :
    ∀ a, piAnti a = pi1 (colourTwist a)

theorem dialOneBase_piAnti :
    ThetLogos.DialOneSeatTiePin.DialOneBase piAnti
    -- clause 10 witness frozen at (3, 1)

theorem gammaFamily_piAnti :
    ThetLogos.DialOneGammaFamilyPin.GammaFamily piAnti

theorem strengthenedFam_piAnti :
    DialOneStrengthenedFam piAnti

theorem weightAt_piAnti_common :
    weightAt piAnti commonWeightVector

theorem weightQuestionW_piAnti : WeightQuestionW
    -- via ⟨piAnti, strengthenedFam_piAnti,
    --      piAnti_ne_pi1, weightAt_piAnti_common⟩

theorem piAnti_not_orbit :
    ∀ b : Fin 4 → Bool, piAnti ≠ orbitRep b
```

**K-CLS-3c-A (pre-registered, per the pack).** The brick's
headline, if the computation lands as scoped, is the
*finding* of §3(ii)/(iii) — `piAnti` in the strengthened
set, off-orbit, carrying the common weights, Grade W
answered YES — **not a kill of anything landed**: CLS-3c's
theorems, CLS-2b's orbit classification, and every landed
kill stand untouched beside it. **K-CLS-3c-A fires only
against a scoping error — against this memo**: if the
brick's computation instead produces
`¬ DialOneBase piAnti` at any named clause/witness, or
`¬ GammaFamily piAnti`, or
`¬ weightAt piAnti commonWeightVector`, then §1's clause
audit and §2's transport expectation die at full rank, the
fork re-opens on branch (i) (base failure) or on a
base-holding / family-or-weight failure, and this memo is
corrected visibly, never quietly. One correction this memo
already makes to CLS-3c's dossier, at scoping rank only:
its guess that the cell needs "a new first-order
computation" is superseded — the computation is a
transport (§2); CLS-3c's landed OPEN naming was correct
and none of its theorems is re-read.

---

## Fences

NO CLAIM; **Dial 1 = 0; all dials 0/4.** Scoping only:
nothing above is proved by this memo. The expected brick
verdict — `DialOneBase piAnti ∧ DialOneStrengthenedFam
piAnti ∧ weightAt piAnti commonWeightVector`, answering
`WeightQuestionW` YES — is T2 until the brick lands at T1
under the full ceremony (build, census, axiom check,
dossier, push). Parts of any official statement closed by
this scoping: 0.
