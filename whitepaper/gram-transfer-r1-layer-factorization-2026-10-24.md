# Gram clause, transfer-matrix route, rung R1 — the layer / Markov factorization of the Gibbs measure LANDED (2026-10-24)

**Verdict: R1 STANDS WHOLE (T1).** Module
`lean/ThetLogos/LatticeLayerFactor.lean` (new; no proved file
edited). Parent-verified: fresh `lake build
ThetLogos.LatticeLayerFactor` exit 0, **3,394 jobs**; recount
**19 strict theorems / 5 defs**, **0** `sorry`/`admit`;
`#print axioms` on the four headlines — standard axioms only
(propext, Classical.choice, Quot.sound), no `sorryAx`.
Post-header-flip rebuild exit 0.

**NO CLAIM.** Parts of any official Clay statement closed by
this landing: **0**. Stage 1b-B label unchanged: reflection
positivity T1 for U(1) at all β ≥ 0 (Route C); **general
(G, ρ) OPEN**. This rung is a factorization, not the positivity
discharge — the discharge is R4, consuming R2 + R3.

Charter: `whitepaper/gram-clause-transfer-matrix-scoping-2026-10-24.md`
§4 (rung R1), constraints D1–D6. Gap-queue item Q3:
`whitepaper/gap-theorem-queue-2026-10-24.md`.

## The factorization

At fixed even `N`, every real `β`, general `(G, ρ)`: push the
Gibbs measure forward along Stage 0's split coordinatization
`splitEquiv halfLinks` — configurations split into the closed
half (base times `< N/2`) and the negative half (base times
`≥ N/2`). The pushed measure is the normalizing scalar `Z⁻¹`
times the product of the two half Gibbs-type measures,
reweighted by the layer Boltzmann factor `exp(−S₀)`:

```
(gibbsMeasure (torusShift N) μG ρ β).map (splitEquiv halfLinks)
  = (ENNReal.ofReal (gibbsPartition (torusShift N) μG ρ β))⁻¹ •
    ((halfGibbsPlus μG ρ β).prod (halfGibbsMinus μG ρ hN β)).withDensity
      (fun p => (layerWeightZero ρ β p : ℝ≥0∞))
```

(`gibbsMeasure_map_splitEquiv`.)

The two half measures are the product Haar measure on each
half's links, reweighted by `exp` of the half action — **the
same half-action function `halfActionP` on both halves**: the
closed half read by restriction (`restrictPos`), the negative
half read through the mirror (`mirrorP`), by the landed
`wilsonActionMinus_eq_halfActionP`. The layer factor is
`exp(−wilsonActionZero)`: the temporal plaquettes based at the
two fixed link layers `N/2 − 1` and `N − 1` — the only
plaquettes coupling the two halves. Density form:
`gibbsMeasure_map_splitEquiv_half` (a single `withDensity`
over `pi.prod pi` with density `wPlus * (wMinus * wZero)`);
pointwise density factorization: `gibbsDensity_split` /
`layerWeight_product`.

## Proof route (finite machinery only)

Landed action split `wilsonAction_split_half`
(S = halfActionP∘restrictPos + halfActionP∘mirrorP + S₀) →
exp-of-sum (`layerWeight_product`) → Gibbs-density
factorization (`gibbsDensity_split`) → set-integral evaluation
of both sides: the map side via `Measure.map_apply` +
`withDensity_apply` + the set-lintegral transport
`MeasurePreserving.setLIntegral_comp_preimage_emb` along the
landed `measurePreserving_splitEquiv`; the density side via
`setLIntegral_congr_fun` + `gibbsDensity_split`. Factored form
via Mathlib `prod_withDensity` + `withDensity_mul₀`.
Expectation form via `integral_map` + `withDensity_smul_measure`
+ `integral_withDensity_eq_integral_smul`.

Everything is a permutation of finitely many product factors
plus density algebra. **No disintegration appears anywhere,
and no basis expansion of the Boltzmann weight** — charter
constraint D5 held, and honest unknown U1 is resolved
*negative at this rung*: the side door (R1 forcing a basis
expansion of `exp(−S)`) does not open. The measure identity
itself needs no condition on β at all (only the positivity of
the density is consumed; D3), and d = 1 flows through the same
proof (D4).

**Q1 `posToSlice` NOT consumed** — the iteration runs through
`restrictPos`/`mirrorP`, whose transport is already landed.
The charter's conditional ("includes posToSlice if the
iteration consumes it") does not trigger; recorded so the
queue record is exact.

## Consumer forms shipped (§6, for R2 and R3)

- `integral_splitEquiv_factor` — expectation form: for
  `StronglyMeasurable Φ` on the split space,
  `∫ U, Φ (E U) ∂gibbs = ∫ p, (layerWeightZero ρ β p) • Φ p
  ∂(Z⁻¹ • (halfGibbsPlus.prod halfGibbsMinus))` (the ℝ≥0-scalar
  pairing matching `integral_withDensity_eq_integral_smul`'s
  output form).
- `integral_layerFactor_iterated` — the Fubini iteration of
  the pairing over the two halves (`integral_prod`; SFinite of
  the half measures supplied via
  `Measure.withDensity.instSFinite`).

R2 (the half-step square T = V†V) consumes this factorization
together with S1's depth-one identification
(`LatticeTransferID`): both half-step factors now provably use
the identical `halfActionP`, so the adjointness question has
its input landed. R3 iterates `integral_layerFactor_iterated`
over the positive half's layers toward the depth-`N/2`
identification.

## Census impact

Program census after this landing (re-derived by a full-tree
recount with the house counter, minus the documented
669-strict / 15-file non-chain remainder of the 2026-10-18/19
double-check sweep): **4,401 strict / 4,450 attribute-inclusive
/ 148 counted modules** (from 4,382 / 4,431 / 147 after queue
Q2; delta +19 strict / +1 module, exactly this module's
contribution; the 49 same-line `@[simp]` declarations
corpus-wide are unchanged — this module adds none).

## Fence

R2 (half-step square; operator positivity on arbitrary
vectors), R3 (depth-`N/2` identification), R4 (the verbatim
discharge) are **unbuilt**. Stage 1b-B stays T1-for-U(1),
general (G, ρ) OPEN. The pre-registered kills for this rung —
needs disintegration; forces a basis expansion; a needed
marginal is false; the half-step factors are not adjoints —
were watched mechanically: none fired at the factorization
level (adjointness proper is R2's statement, not asserted
here).
