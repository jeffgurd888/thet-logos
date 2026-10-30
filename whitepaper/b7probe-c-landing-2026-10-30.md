# B7-PROBE-c — β⁷ certified at (S₃, std); the probe verdict: outcome (ii), theorem-grade

**Date:** 2026-10-30 · **Brick:** B7-PROBE-c (Lean
certification, Seat 2 + verdict), per
`scoping-beta7-2026-10-29.md`. Module:
`ThetLogos.PlaneCrossingBeta7Probe` (part 2 appended).
**Verdict: LANDED** (part 2: strict 33 / defs 11,
parent-verified from disk — file totals 109 / 36; module
build green; `verdict_B7Probe` and its components depend on
exactly [propext, Classical.choice, Quot.sound]).

**Fences: NO CLAIM. Parts of any official statement closed: 0.
Dials: 0/4.** Registry **BR1-008 is now CERTIFIED at both
seats** (entry updated in this batch). Seat scope only; the
β⁷ general sign stays FRONTIER; the multiples are seat data
under the interpretation cap.

## The certified probe verdict (`verdict_B7Probe`)

**Outcome (ii), theorem-grade: every order-7 channel
vanishes on K₆ at both owned seats. K-K7 does not fire. The
β⁷ decision at the seats passes to β⁸** — which is not
queued, and the regress has no internal stop; both facts are
stated on the verdict's face, not softened. Route A is
neither killed nor advanced at order 7.

At (S₃, std): seat-K₆ = ker κ₄^dep = {φ₀ = φ₂} re-derived
(`seatK6_S3`, consuming the landed B5/B6 verdicts); the
channel multiples certified — (4,1,1,1) 20 ×, (3,2,1,1)-adj
24 ×, (3,2,1,1)-opp 12 ×, (2,2,2,1) 24 ×, C6-chain 3/2 ×,
Θ-family 3 ×, book 1/4 × — in the B6-PROBE-c mirror style
(explicit per-support-type kernels calibrated against the
seat κ₄ form, proportionality as theorems; the character-sum
derivations were part 1's work at (C₃, χ), and the header
says so).

## The A3-gated factorization — stated exactly, both directions proved

The probe's nuance is now theorem-grade:

- `K7S3Theta_gated` / `K7S3Book_gated`: the orbit-pair
  kernels factor through the **A3-gated product class**
  (`gatePair`: the product's class when both loop holonomies
  are even, κ₄'s zero class otherwise) at multiples 3 and
  1/4 — entrywise over all 121 orbit pairs.
- `K7S3Theta_not_plain` / `K7S3Book_not_plain`: **no scalar
  factors either kernel through the plain product class** —
  proved from the run log's exhibiting entry (0,4): entry
  (0,0) forces the scalar, entry (0,4) contradicts it. The
  failure of the plain reading is a theorem, not a remark.
- Vanishing for both orbit channels is proved on the joint
  span of every candidate reading, so the verdict is
  convention-independent, stated in both verdict docstrings.

**Census: 8,000 → 8,033 strict / 8,078 → 8,111
attribute-inclusive / 271 modules** (module extended;
recounted from disk).

## Backers since last landing

The backer roll (`BACKERS.md`) is unchanged since the last
landing; no new confirmed gift is on the record. Thank you to
everyone reading the stream — the corpus is free for everyone,
forever.

*End of dossier.*
