# SHELF-3b — LANDED PARTIAL at the named seam: Gram positivity + composition in; the Schur product named OPEN with its obstruction on the face

**Verdict: SHELF-3b PARTIAL at the pack's pre-named seam. The Gram/composition core of the integral-kernel product theory is landed: `PosKernel` is registered, factorization (Gram) kernels are positive, kernel composition is a theorem with its adjoint-positivity corollary. The Schur product clause — the pointwise product of two positive L² kernels is positive — is named OPEN, and the module header states why at full rank: as stated at L² generality the claim is not merely unproved but ill-posed, because the pointwise product of two L² kernels need not be an L² kernel at all. The F2 fence therefore retires only in part: "no landed integral-kernel product theorem composing two pairings into positivity" is retired for the Gram/composition shape; its Schur clause stands. NO CLAIM. Dials 0/4.**

## What landed

- **`PosKernel` (registration, on the face):** operator-level positivity through 3a-ii's API — for `K : α × α → ℂ` with `hK : MemLp K 2 (μ.prod μ)`, `PosKernel K hK : Prop := ∀ f : Lp ℂ 2 μ, 0 ≤ (inner ℂ f (integralKernelOp hK f)).re`; plus `posKernel_zero`.
- **Gram/factorization positivity:** `gramKernel κ F (x, y) = ∫ t, F (x, t) * conj (F (y, t))` is an L² kernel (`gramKernel_memLp`, via Hölder 2,2,1 and Cauchy–Schwarz/Tonelli energy bounds) and is positive (`posKernel_gram`: the quadratic form equals `∫ t, ‖∫ x, conj (f x) * F (x, t)‖² ∂κ ≥ 0`, by Fubini). This is the shape the F2 weld consumes — two evaluations composed into a positivity.
- **Composition:** `compKernel ν K₁ K₂` is an L² kernel (`compKernel_memLp`) and induces exactly the operator composition (`integralKernelOp_comp`, via triple Fubini in both associations bridged by a measure-preserving middle swap); the adjoint kernel `adjKernel` satisfies `integralKernelOp_adj_inner` (⟪T_K f, g⟫ = ⟪f, T_{K*} g⟫); corollary `posKernel_comp_adj`: the T*∘T kernel is positive, with quadratic form `‖T_K f‖²`.

## The named seam — the Schur clause, and its obstruction

Item (3) of the pack (pointwise product of two positive L² kernels is a positive L² kernel) did **not** land, for a proved-shape reason stated on the module's face:

1. **The product can leave the class.** `K(x, y) = g(x) g(y)` with `g ∈ L² ∖ L⁴` is a positive L² kernel (a rank-one Gram kernel) whose pointwise square is not `MemLp 2` — so "the product kernel" is not in general an object of the registered class, and the statement as priced is false at L² generality, not just unproved.
2. **The Gram route cannot close it either:** a general `PosKernel` admits no Gram factorization in this class (the square root of a positive HS operator need not be HS), so item (2)'s method does not extend to products.

A restricted Schur theorem (e.g. for kernels additionally in L⁴, or on finite-measure spaces with an L∞ factor) is a plausible future **NEW entry** at its own price; it is not claimed, scoped, or queued by this landing. The weld remains un-attempted, exactly as fenced: it additionally needs the `reflSite_eq_torusShift_zero` duplicate resolved upstream, and is separately priced when queued.

## Parent verification (from disk)

- Module `lean/ThetLogos/IntegralKernelSchur.lean` (NEW, 1,079 lines): canonical counter **strict=17, defs=5**, zero attribute-prefixed declarations, zero "sorry"/`native_decide` tokens; no landed file edited; the `reflSite` duplicate untouched.
- Parent module build green (3,563 jobs), independently reproduced.
- Parent axiom check: `posKernel_gram`, `integralKernelOp_comp`, `posKernel_comp_adj` each on exactly `[propext, Classical.choice, Quot.sound]` (the builder's log additionally certifies the remaining eight headlines on the same three).

## Census

9,921 → **9,938 strict** / 9,999 → **10,016 attribute-inclusive** / 329 → **330 modules** (delta +17 strict, +1 module). This landing also carries the README badge correction: the shields.io badge (URL-encoded count) had lagged at 9,551 since the C96-3b2 landing while the body stayed current; badge and body are both updated here and verified against the committed README.

## Backers since last landing

No change to the backer roll since the last landing.
