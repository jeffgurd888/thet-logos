# GAP QUEUE Q2 — POINTWISE POSITIVITY OF `T_β f`

**Date:** 2026-10-24. **Verdict: LANDED — STANDS WHOLE (T1),
parent-verified.** Module:
`lean/ThetLogos/LatticeTransferPointwise.lean`. Queue source:
`whitepaper/gap-theorem-queue-2026-10-24.md` §1, item Q2
(priced **S** there); the hole is named in the Stage 1b-D
dossier (`whitepaper/pitch-4-stage-1b-d-2026-10-17.md`),
fences.

**NO CLAIM.** Parts of any official Clay statement closed by
this item: **0**.

## What was open

The 1b-D dossier, verbatim: "**Pointwise positivity of
`T_β f`** (positive functions to positive functions) is not
stated; it follows from the form positivity by the standard
indicator argument (priced **S**, not formalized here)."
Stage 1b-D landed the *form* positivity
(`transferOp_form_nonneg`: for pointwise real nonnegative
slice observables `f, g`, the form `⟪sliceState g, T_β
(sliceState f)⟫` is real and nonnegative). The pointwise
consequence — the transferred observable is itself
nonnegative — was a named, priced hole in a landed module.

## What stands

- **`setIntegral_transferOp_sliceState`** — the indicator
  step: for every measurable set `S` of slice
  configurations, the set integral of `T_β (sliceState f)`
  over `S` has nonnegative real part and vanishing
  imaginary part. Proof: the indicator observable of `S`
  (in `L²` by the corpus's `memLp_of_bounded`) is fed to
  `transferOp_form_nonneg` as the bra; the form value is
  identified with the set integral through
  `MeasureTheory.L2.inner_def` and `integral_indicator`,
  and split by `integral_re` / `integral_im`.
- **`transferOp_pointwise_nonneg`** — the headline: for `f`
  pointwise real and nonnegative (`MemLp f 2
  (sliceMeasure β)`),
  `∀ᵐ z ∂(sliceMeasure μG ρ β), 0 ≤ (T_β (sliceState f)
  z).re ∧ (T_β (sliceState f) z).im = 0`. The a.e.
  conclusion is the honest form of "pointwise" for an `L²`
  operator: the representative of the transferred vector is
  real and nonnegative almost everywhere. It closes by
  Mathlib's `ae_nonneg_of_forall_setIntegral_nonneg` (real
  part) and
  `Integrable.ae_eq_zero_of_forall_setIntegral_eq_zero`
  (imaginary part) applied to the indicator step.

At every real `β`, general `(G, ρ)`, `2 ≤ N` — the same
hypotheses as the form positivity it consumes. No Gram
clause, no OS-form input: the Gibbs measure's positivity
alone, exactly as the dossier said the argument would go.

## Verification (parent-run)

- Fresh rebuild `lake build ThetLogos.LatticeTransferPointwise`:
  **EXIT 0, 3,562 jobs**; post-header-flip rebuild also EXIT
  0. Olean present.
- House counter: **2 strict / 0 defs**; no same-line
  `@[simp]` additions.
- Code-sorry census: **0** (the one grep hit is the word
  `sorryAx` in the header docstring).
- `#print axioms` on `setIntegral_transferOp_sliceState`
  and `transferOp_pointwise_nonneg`: each only `[propext,
  Classical.choice, Quot.sound]` — **no sorryAx**.
- Census impact: program **4,382 strict / 4,431
  attribute-inclusive / 147 counted modules** (re-derived at
  landing: whole tree minus the documented 669-strict /
  15-file non-chain remainder).

## Fence

This closes gap (the pointwise corollary) only. Operator
positivity of `T_β` on *arbitrary* vectors — the half-step
square, transfer route R2 — remains open, as does the
identification of the full OS form with transfer powers at
depth above one (R3). Stage 1b-B's label is unchanged:
positivity T1 for U(1), general (G, ρ) OPEN.

— BONES, for the record. Tiers per the Concrete; **NO CLAIM.**
