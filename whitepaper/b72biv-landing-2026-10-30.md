# B7-2b-iv — the total decomposition at order 7

**Date:** 2026-10-30 · **Brick:** B7-2b-iv (fourth sub-brick
of the B7-2b chain). Module:
`ThetLogos.PlaneCrossingBeta7Fibers` (§ Total7).
**Verdict: LANDED** (+107 strict / +3 defs, parent-verified
from disk — file totals 158 / 12; full build green;
`kappa7dep_total_decomposition` on exactly [propext,
Classical.choice, Quot.sound]).

**Fences: NO CLAIM. Parts of any official statement closed: 0.
Dials: 0/4.** The identity is stated in B7-1's exact
variable context (general (G, ρ); Even N, 3 ≤ N, repMatrix
continuity). No sign asserted for anything; the β⁷ sign
stays FRONTIER.

## The identity, in its true form

κ₇^dep = **A₆·κ₆^dep + A₅·κ₅^dep + A₄·κ₄^dep +
d⁻⁷·(channels + residuals)**, every coefficient read off
the landed fiber accounting (and independently re-verified
against the landed conversion lemmas before the final
ring close):

- **A₆ = 4 + (M−4)·B** — the order-5/order-6 dressing
  factor again (M = colCount N, B = 1 − e₁/d). **No new
  dressing shape at order 7.**
- **A₅** = −½·[B²M² − 7B²M + 12B² + 6BM − 24B + M −
  (M−4)·μ₂/d² + 12].
- **A₄** = (1/6)·[B³M³ − 9B³M² + 26B³M − 24B³ + 6B²M² −
  42B²M + 72B² − 3BM²·μ₂/d² + 3BM² + 21BM·μ₂/d² + 6BM −
  36B·μ₂/d² − 72B − M·μ₃/d³ − 9M·μ₂/d² + 10M + 4μ₃/d³ +
  36μ₂/d² + 24].
- **Channels at d⁻⁷:** −(1/24)·E₄₁₁₁, −(1/12)·(E₃₂₁₁Adj +
  E₃₂₁₁Opp), −(1/48)·E₂₂₂₁, −(1/2)·E₂₁₁₁₁₁C6,
  −(1/2)·E₂₁₁₁₁₁Theta, −1·Ebook — with the evaluated 8/4
  ADJ/OPP baselines absorbed in excess form.

## The forced residuals (named, at full rank)

- **+ 2e₁·(κ₆^chanC6 excess + κ₆^chanTheta excess):** the
  order-6 channels REAPPEAR at order 7, dressed by one more
  power than A₆ absorbs — the hepta conversion's hexa pool
  carries them.
- **+ e₁(μ₂ − 2e₁²)·S4theta + (e₁²/2)·S4thetaD**, where
  S4thetaD = `theta4SubsetDoubledSum` is a NEW named
  residual sum landed in this brick.
- **+ e₁·RB − 2e₁³·S4book**, the book residuals
  `bookHexaEraseSum` / `book4SubsetSum` (new named defs).

All residuals are explicit named sums, not fitted terms.
One methodological line for the record: a card-7 erasure
identity was doubted mid-brick because it fails in finite
site-product toy models; those models are unfaithful
oracles for this corpus (the column density is a word
character with Haar collapse at private sites, not a
product of independent site factors) — the identity was
derived from the landed strip calculus instead and is a
green theorem (`heptaExcess_eq_of_private`). Only the
corpus's own landed identities are ground truth here.

**Census: 8,095 → 8,202 strict / 8,173 → 8,280
attribute-inclusive / 273 modules** (recounted from disk).
Remaining: B7-2b-v packages this as the single named
`kappa7dep_eq` (a thin rename/verify — the decomposition
already sits in the exact context) and closes B7-2.

## Backers since last landing

The backer roll (`BACKERS.md`) is unchanged since the last
landing; no new confirmed gift is on the record. Thank you to
everyone reading the stream — the corpus is free for everyone,
forever.

*End of dossier.*
