# Q12 — PARTIAL: Compactness of T_β (Conditional on a Named Density Hypothesis, Whole at β = 0); the Gap as a True Conditional; the β = 0 Gap Exact

**Date:** 2026-10-24 · **Seat:** gap queue Q12 (source: Stage 1b-D fences, item (i); priced M–L). **Verdict: PARTIAL** — in the pre-registered honest form, every conditional carried by a named hypothesis. Parent-verified 2026-10-24: targeted build exit 0 on the shipped text (2,387 lines), strict recount 57, zero `sorry`/`admit`, all nine headline axiom checks standard only.

**NO CLAIM.** Parts of any official Clay statement closed: **0**. Stage 1b-B label unchanged (U(1) T1 at all β ≥ 0; general (G, ρ) OPEN). No continuum or uniform-in-volume language anywhere — a gap uniform in volume is Stage 3c (WALL), out of scope here.

## What stands (T1) — module `LatticeTransferCompact` (57 strict / 10 defs)

- **The kernel in corpus terms.** The two-slice law of the Gibbs measure as a measure (pushforward along the landed slice / `nextConfig` readings; marginals = the slice measure), with the landed transfer form identified as its pairing; abstract integral operators from an L² kernel, with the form identity, the Cauchy–Schwarz form bound, and the Hilbert–Schmidt bound ‖kernelOp‖ ≤ ‖K‖₂.
- **Compactness.** Mathlib (this checkout) has **no Hilbert–Schmidt / integral-operator compactness API** — it was built by hand: the Parseval identity Σᵢ ‖K bᵢ‖² = ‖K‖²₂ over a Hilbert basis, finite-rank approximants with √-tail bounds, a hand-rolled finite-dimensional-range ⟹ compact lemma, and `isCompactOperator_of_tendsto`. Result: `transferOp_compact_of_HDen` — T_β is compact at general β **conditional on HDen** (the two-slice law has an L² density w.r.t. the product of its marginals); `transferOp_compact_zero` — **unconditional at β = 0** (the kernel is ≡ 1 there, HDen discharged).
- **Spectral discreteness.** At even N: eigenvalues are real with ‖λ‖ ≤ 1; eigenvectors for λ ≠ 1 are ⊥ Ω; `transfer_spectrum_finite_above` — for every ε > 0 only finitely many spectral points have norm ≥ ε (Fredholm alternative + a √2ε-separation argument).
- **The gap, conditional.** `transfer_gap_of_formPos`: conditional on the named package **TransferFormPos** (the OS form positive on *all* of osSpace + vacuum simplicity), there is δ > 0 with ‖λ‖ ≤ 1 − δ for every spectral λ ≠ 1 — a genuine fixed-volume gap at general β, exactly as strong as its named hypothesis.
- **The gap at β = 0, unconditional and exact.** `transfer_spectrum_zero` / `transfer_gap_zero`: the spectrum of T₀ lies in {0, 1} with δ = 1 — at zero coupling the transfer operator is *exactly* the vacuum projection.

## Exactly where the fences stopped it (named, not smoothed)

1. **(H-PF) at general (G, ρ) is unproved** — TransferFormPos on all of osSpace *is* the open Stage 1b-B positivity content in operator form. The corpus's landed form positivity covers slice observables only; no Perron–Frobenius step is asserted anywhere.
2. **The U(1) seat is NOT discharged** — welding Route C's osForm positivity up to (H-PF) on all of osSpace is S2-2-shaped work and was not attempted. The conditional gap theorem applies immediately to any future discharge.
3. **HDen at general β remains a named hypothesis** — its discharge needs disintegration of the configuration measure with density continuity/boundedness. Compactness at general β is exactly as strong as HDen.
4. **Separability** of osSpace does not synthesize in this checkout; the compactness corollaries carry the Hilbert basis as an explicit hypothesis — a named residue.

## Census

4,684 → **4,741 strict** · 4,733 → **4,790 attribute-inclusive** · 159 → **160 counted modules**. Seven-sorry qualification unchanged.
