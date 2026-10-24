# THIRD FAMILY F1 — THE SINGLE-PLAQUETTE WORD FACTORIZATION

**Date:** 2026-10-24. **Verdict: STANDS WHOLE (T1).** Brick F1
of the third family (charter
`whitepaper/gram-third-family-scoping-2026-10-24.md`, §2 the
factorization, §5 the F1 ladder entry; Jeff's commissioned
route to Stage 1b-B at general (G, ρ), 2026-10-24): the
exponential factor of one crossing plaquette — the factor R2's
obstruction dossier identified as the seam kernel's only Gram
factorization seat — is factored as a `∑'` over word indices in
the exact `conj (B) * A` shape the landed integrated criterion
consumes. Neither pre-registered kill fired. Parent-verified
and shipped the day it was built.

**NO CLAIM.** Parts of any official Clay statement closed by
this brick: **0**. Stage 1b-B label unchanged: positivity T1
for U(1) (Route C); general (G, ρ) **OPEN until F3 lands** —
F1 is the factorization brick, not the discharge.

---

## 1. What stands

New module `lean/ThetLogos/LatticeGramWord.lean` (namespace
`ThetLogos.GramWord`; imports only
`ThetLogos.LatticeGramSeries`, `ThetLogos.GramWordTensor`; no
proved file edited). **39 strict theorems / 16 defs**, 0
same-line `@[simp]`, 910 lines.

**Headline — `exp_re_hsInner_word`.** For abstract matrices
`X P₁ P₂ U : Matrix (Fin d) (Fin d) ℂ` and any real `c`:

```
Complex.exp ((c : ℂ) * ((hsInner X (P₁ * U * P₂)).re : ℂ))
  = ∑' idx : WordIdx d, star (featB idx U) * featA c idx X P₁ P₂
```

where `hsInner X Y = ∑ i, ∑ j, star (X i j) * Y i j` is the
entry-form Hilbert–Schmidt pairing (bridged to the trace form
by `hsInner_eq_trace : hsInner X Y = (Xᴴ * Y).trace`). In the
application `X = ρ(y)`, `P₁ = ρ(τ⁻¹)`, `U = ρ(u)`,
`P₂ = ρ(τ′)`, `c = β/d`: this is the exponential factor of
R2's per-plaquette seam factor
`e^{-β} · exp ((β/d) · Re ⟨ρ(y), ρ(τ⁻¹uτ′)⟩_HS)`.

The index set is `WordIdx d = PlaqIdx d × PlaqIdx d` with
`PlaqIdx d = Σ n : ℕ, (Fin n → Fin d × Fin d) × (Fin n → Fin d × Fin d)`:
a level `n` and two entry paths. The features are monomials in
matrix entries along those paths:
`featB idx U = featB1 idx.1.2.2 U * featB2 idx.2.2.2 U` (the
`U`-words — a function of the negative half's variable alone),
`featA c idx X P₁ P₂ = featA1 … * featA2 …` with
`featA1 c α κ X P₁ P₂ = ((c/2:ℂ))ⁿ/n! * word α X * star (planeWord α κ P₁ P₂)`
and `featA2` its conjugate twin; the entries of the triple
product `P₁ * U * P₂` are split over internal paths `κ` by
`word_mul3`, and those internal paths are **part of the
index** — no sum occurs inside any feature.

The engine lemmas stand as chartered: `tensor_hsInner`
(`⟨X^{⊗n}, Y^{⊗n}⟩_HS = ⟨X, Y⟩_HS ^ n`),
`tensor_hsInner_word` (the entry-path expansion), and the
two factor HasSums `hasSum_factor_one` / `hasSum_factor_two`,
composed via `HasSum.sigma_of_hasSum` and `HasSum.mul`. The
headline carries **no norm hypotheses**: entry bounds enter
only through the summability side conditions of the
composition, never through the identities themselves.

## 2. Why no basis choice enters (the charter §2 mechanism)

K-F1(a) — the factorization closing only through a basis
choice that breaks the word form — **did not fire**, and the
reason is structural, not cosmetic. The dead factored family
(T4c′) died because a shared strict factor was forced to be
read as entry (k,a) on one half and entry (j,i) on the other:
an entry-*selection* step is where the mismatch lived. The
word factorization has no such step. An HS inner product
pairs a vector with itself index-by-index; its tensor-power
expansion therefore pairs **the same entry path on both
sides by construction** (`tensor_hsInner_word`), and the
internal paths that split the triple product are absorbed
into the countable index rather than chosen. There is no
basis anywhere in the module: `hsInner` is defined entrywise
for an arbitrary finite index type, and the features are
paths, not basis vectors. The (k,a)/(j,i) mechanism's last
possible seat is not here — it is the marginals' plane-link
contraction, which is F2's Damping Lemma (§5 below).

## 3. The control: d = 1 resums to Route C

K-F1(b) — the control failing to resum — **did not fire**.
**`word_tsum_circle`**: at `d = 1` with `circleRep`, the
word series equals

```
∑' k : ℤ, (besselI β k : ℂ) * ((y⁻¹ * (τ⁻¹ * u * τ') : Circle) : ℂ) ^ k
```

— the right-hand side of Route C's landed `fourier_exp_circle`
(`LatticeGramSeries.lean`). The identification is made
**through the common value**: both series are proved equal
to `exp (β · Re ((y⁻¹ * (τ⁻¹ * u * τ') : Circle) : ℂ))`, the
word series via §8's headline and Route C's series via
`fourier_exp_circle` itself. No termwise (n,m) → k
regrouping is claimed or needed — exactly the control the
charter pre-registered: the third family's d = 1 shadow *is*
the Bessel series that closed U(1).

## 4. The domination package F2 inherits

The criterion `osForm_nonneg_of_gram_integrated` consumes a
factoring family together with real domination functions
`CA`, `CB` and a summability discharge of `CA · CB`. F1
ships that package in criterion shape, under entry bounds
`‖M i j‖ ≤ K` (all four matrices, `K ≥ 0`; the unitary
application has `K = 1`):

- `wordLevel c K n : ℝ := (|c|/2)ⁿ / n! * (K⁴)ⁿ` — the
  per-level bound;
- `wordCA c K idx` (coefficients + `X`-words + plane words)
  and `wordCB K idx := K^idx.1.1 * K^idx.2.1` (the `U`-words),
  with `wordCA_mul_wordCB : wordCA c K idx * wordCB K idx
  = wordLevel c K idx.1.1 * wordLevel c K idx.2.1`;
- `norm_featA_le : ‖featA c idx X P₁ P₂‖ ≤ wordCA c K idx`;
  `norm_featB_le : ‖star (featB idx U)‖ ≤ wordCB K idx` — the
  criterion's B-feature is `featB · U`, consumed under its
  `star`, exactly as stated;
- `summable_wordCA_mul : Summable fun idx : WordIdx d =>
  wordCA c K idx * wordCB K idx` — the criterion's `hsum`,
  discharged, via the level-bound engine
  `summable_plaqIdx_of_level_bound` and the fiber cardinality
  `card_plaqIdx_fiber` (`d ^ (4n)`).

F2's interface, by name: `PlaqIdx`, `WordIdx`, `featB1`,
`featB2`, `featA1`, `featA2`, `featB`, `featA`, `word`,
`planeWord`, `hsInner`, `wordLevel`, `wordCA`, `wordCB`,
`norm_featA_le`, `norm_featB_le`, `wordCA_mul_wordCB`,
`summable_wordCA_mul`.

## 5. Fences — what F1 does not assert

- **Single plaquette only.** No assembly over the seam, no
  two-selector marginals, no Haar integrals, no positivity.
  F1 asserts nothing about marginals: the per-plaquette
  features are delivered with their domination package; the
  marginals through the common `Ξ` are F2's assembly.
- **The Damping Lemma is F2's named seat.** The plane-link /
  stratum contraction must yield real nonnegative dampings
  and a common `Ξ`; at general (G, ρ) it routes through
  invariant-projection pairings, because bare tensor
  contractions are Weingarten sums with possibly negative
  weights at level ≥ 2. That is where the (k,a)/(j,i)
  mechanism's last purchase lives, pre-killed in the charter
  as K-F2(a)/(b). F1 neither proves nor assumes it.
- The headline is stated for abstract matrices — no
  unitarity, no group, no Haar measure — because the
  factorization is finite tensor algebra plus the exponential
  series; unitarity enters only §7's domination bounds, as
  hypotheses.
- Discharge target remains **β ≥ 0 only** (R2's §4 fence:
  the seam kernel is not positive-definite for β < 0). F3
  applies the criterion; until F3 is green and
  parent-verified, the label stays "T1 for U(1); general
  (G, ρ) OPEN".

## 6. Verification (parent, independent)

- Fresh `lake build ThetLogos.LatticeGramWord` with the olean
  deleted first: **EXIT 0, 3,445 jobs**; olean present.
  Post-header-flip rebuild also EXIT 0.
- House recount: **39 strict / 16 defs**, 0 same-line
  `@[simp]` — matches the builder exactly.
- Code-sorry census: **0** — `sorry`/`admit` absent from the
  source entirely (not even in comments).
- Parent-run `#print axioms` on the five headlines
  (`exp_re_hsInner_word`, `word_tsum_circle`,
  `tensor_hsInner`, `hasSum_factor_one`,
  `summable_wordCA_mul`): each only
  `[propext, Classical.choice, Quot.sound]` — **no sorryAx**.
- Census impact: full-tree recount 5,179 strict / 167 files
  minus the documented 669-strict / 15-file non-chain
  remainder = **4,510 strict / 4,559 attribute-inclusive /
  152 counted modules** (from 4,471 / 4,520 / 151; delta
  exactly +39/+1; 49 same-line `@[simp]` corpus-wide, none
  added).

## 7. What remains

**F2 (priced L)** — assembly: the per-plaquette families
assembled over the finitely many seam plaquettes into the
criterion's `hgram`, plus the Damping Lemma. **F3 (priced
S)** — discharge: apply `osForm_nonneg_of_gram_integrated`,
`osForm_nonneg` at general (G, ρ), β ≥ 0. If F2 dies, the
record carries four closures around 1b-B general and no
fifth named family (charter U3) — the next direction would
then be a new route decision.
