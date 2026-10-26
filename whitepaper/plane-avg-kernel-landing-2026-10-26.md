# The Plane-Averaged Kernel — FULL: the Third Object, Computed

*Landing dossier, 2026-10-26. Module: `lean/ThetLogos/PlaneAvgKernel.lean`
(1,411 lines, strict 50, defs 24, zero `sorry`, zero `native_decide`;
main-tree build green, 3,396 jobs, parent-verified on the shipped
text). **Parts of the Clay Yang–Mills statement closed by this
landing: 0.***

## What the object is

The seat-kernel gate kill named a revival route for (H-PF): not the
killed kernel 𝒦̃ (which holds the plane-link variables as shared
fixed parameters), and not the frozen 𝒦̃₀ — but the kernel that
remains after `osForm`'s own marginalization, integrating the plane
variables out against the Gibbs measure. The scoping recorded it as
"a third object, computed nowhere yet." It is computed now, as a
**new entry** under the relabeling rule — no Option 1 module was
edited or continued.

## What landed (at general (G, ρ), even N, real β)

- **`planeAvgKernel`** — the double product-Haar marginal of the
  Gibbs weight over both halves' plane strata.
- **`osForm_eq_planeAvgKernel`** — the reduction identity: the OS
  form's diagonal is Z⁻¹ times the strict-half product-Haar pairing
  against K̄. (The pairing carries the Gram-criterion-style side
  conditions on f — measurability and boundedness — plus the kernel
  module's own hypotheses; the kernel, its factorization, symmetry,
  and β = 0 anchor are unconditional.)
- **`planeAvgKernel_factor`** — K̄ factors as the two half-action
  weights times the crossing/S₀ marginal, in the corpus's native
  grouping of the half-split.
- **`planeAvgKernel_symm`**, **`planeAvgKernel_conj`** (reality),
  **`planeAvgKernel_conj_symm`**.
- **`planeAvgKernel_zero`** — the anchor: K̄₀ ≡ 1.

Axiom check on the seven headlines: exactly
`[propext, Classical.choice, Quot.sound]` each.

## The fence that defines the next question

**Positivity is not asserted.** Whether K̄ is positive
semidefinite — the (H-PF) question this object was named to revive —
is exactly as open as before, now in its lossless form: by the
reduction identity, (H-PF) at the seat *is* the positivity of this
explicit kernel. That question gets its own price next; nothing in
this dossier smuggles it.

Two bookkeeping deviations from the scoping memo's displayed forms
(the factor grouping follows the pin's proved split; the pairing is
in product-Haar form) are flagged in the builder's verdict memo, not
smoothed over here.

## Census effect

Strict 5,818 → **5,868**; attribute-inclusive 5,885 → **5,935**;
modules 192 → **193**; `sorry` placeholders unchanged at **6**.

## Backers since last landing

No new backers inscribed in this interval; the roll stands as
recorded in `BACKERS.md`. Every gift is published with the proof
stream, named as the giver wishes, amounts only with the giver's
permission — the standing reciprocity of this house.
