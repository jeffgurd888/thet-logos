# RUNG 8B — Bosonic Assembly (2026-10-16)

**Directive:** Jeff, 2026-10-16: push toward the Yang–Mills prize by the
ladder — close the Rung 8 bosonic PARTIAL. The Rung 8 dossier priced the
gap exactly: full `adjoint_relation` on `Dom d` stalled on Mathlib
`Submodule` inner-product API friction ("engineering, not math"), with
CCR, number operator, sector orthogonality, vacuum cyclicity "not yet
formalized."

**Verdict condition:** STANDS if the full adjoint relation, CCR, and
number operator land T1 with zero new sorrys and axioms exactly
`[propext, Classical.choice, Quot.sound]`; PARTIAL if any target resists,
with the price stated exactly.

## VERDICT: STANDS

All four required targets stand, plus sector orthogonality and the
stretch goal (vacuum cyclicity). The Rung 8 bosonic PARTIAL is closed:
bosons now match the fermionic side's completeness at finite modes.

*File:* `lean/ThetLogos/BosonicAssembly.lean` (520 lines, new module,
imports `ThetLogos.BosonicFock`; `BosonicFock.lean` **unmodified**).
*Inventory:* **31 theorems + 6 definitions**, zero sorrys, zero admits.

## What was proved (all T1)

### Target 1 — full adjoint relation on `Dom d`
- `adjoint_relation` — for all `x y : Dom d`,
  `⟪ann i x, y⟫ = ⟪x, adag i y⟫` (inner products in `BosonicFock d` via
  coercion), assembled from Rung 8's `adjoint_basis` by its own
  `Dom_induction₂`. The Rung 8 API friction yielded to an explicit
  motive plus `Submodule.coe_add`/`Submodule.coe_smul` simp lemmas.
- `adjoint_relation_adag` — the companion form
  `⟪adag i x, y⟫ = ⟪x, ann i y⟫`, by conjugate symmetry.

### Target 2 — CCR on `Dom d`
Proved first on coefficient space (`Config d →₀ ℂ`), checked on singles
via `Finsupp.lhom_ext` (scalar content: `sqrtNat_mul_self`), then
transported through `boseRepr` by `Dom_ext_transport`:
- `ccr_coeff_mixed`, `ccr_coeff_ann_ann`, `ccr_coeff_adag_adag`.
- `ccr_mixed` — `(ann i) ∘ₗ (adag j) - (adag j) ∘ₗ (ann i)
  = if i = j then 1 else 0` in `Module.End ℂ (Dom d)`.
- `ccr_ann_ann`, `ccr_adag_adag` — commutativity of annihilators and of
  creators, as linear-map equalities on `Dom d`.
- `ccr_mixed_apply` — pointwise form:
  `ann i (adag j x) = adag j (ann i x) + (if i = j then x else 0)`.

### Target 3 — number operator
- `numberOp` — `∑ i, (adag i) ∘ₗ (ann i)` on `Dom d`.
- `numberOp_basis` — `numberOp e_c = (∑ i, (c i : ℂ)) • e_c`: the basis
  eigenvalue is the total occupation count (via `repr_numberOp_mode`:
  each mode contributes exactly the scalar `c i`).
- `numberOp_vacuum` — vacuum eigenvalue `0`.

### Target 4 — vacuum and sectors
- `ann_vacuum` — `ann i (vacDom d) = 0`, where `vacDom` is the vacuum
  as an element of `Dom d`.
- `sector_orthogonal` — with `tot c = ∑ i, c i` and `sectorSub d n` the
  span in `BosonicFock d` of basis vectors of total count `n`: sectors
  of distinct totals are orthogonal (via `Submodule.span_induction₂`
  and `boseE_inner`; distinct totals force distinct configurations).

### Stretch — vacuum cyclicity: STANDS
- `cycSub_eq_top` — the submodule of `Dom d` generated from the vacuum
  by finitely many creation operators (`applyList`, `cycSub`) is `⊤`.
  Route: `adag_mem_cycSub` (closure of the orbit span under each
  `adag i`, by `Submodule.span_induction`), `basis_mem_cycSub` (every
  basis vector is in the orbit span, by strong induction on `tot c`:
  `e_c` is a nonzero scalar multiple of `adag i e_{c - δi}`), and
  `Finsupp.induction` on coefficients through `boseEquiv`.

Supporting lemmas: `single_smul_one`, `config_add_single_apply_ne`,
`config_add_single_apply_self`, `config_sub_single_apply_ne`,
`config_sub_single_apply_self`, `config_sub_sub_comm`,
`config_add_add_comm`, `repr_ann_adag`, `repr_adag_ann`,
`repr_ann_ann`, `repr_adag_adag`, `repr_numberOp_mode`,
`sqrtNat_ne_zero`, `adag_basis_dom`, `tot_add_single`.

Definitions: `numberOp`, `vacDom`, `tot`, `sectorSub`, `applyList`,
`cycSub`.

## Verification evidence
- Targeted build: `lake build ThetLogos.BosonicAssembly` — **green,
  2,452 jobs, exit 0**.
- Root build: `lake build` — **green, 3,325 jobs, exit 0** (the
  pre-existing corpus is untouched and unbroken). Wiring note, verified
  by a delete-and-rebuild test: the root target covers the root import
  graph; rung modules such as `SecondQuantGamma` — and now
  `BosonicAssembly` — are not in `ThetLogos.lean`'s import list and are
  verified by targeted builds, as at Rung 9. Adding the one-line import
  is a separate decision.
- Sorry/admit sweep: none in `BosonicAssembly.lean`; `BosonicFock.lean`
  unmodified; `satisfiesDestruction` untouched.
- `#print axioms` spot-checks — **all exactly
  `[propext, Classical.choice, Quot.sound]`** for: `adjoint_relation`,
  `adjoint_relation_adag`, `ccr_mixed`, `ccr_ann_ann`, `ccr_adag_adag`,
  `ccr_mixed_apply`, `numberOp_basis`, `ann_vacuum`, `numberOp_vacuum`,
  `sector_orthogonal`, `cycSub_eq_top`.

## Honesty labels
Finite mode set `Fin d`. Creation/annihilation are unbounded on the
full Fock space; everything operator-algebraic here lives on the dense
finite-particle domain `Dom d`, the standard honest formulation. This
is the **free bosonic theory**: no interaction, no gauge field, no
Yang–Mills dynamics. It is not a continuum theory and not a Millennium
claim.

## What remains priced (not attempted)
- **Bosonic Γ(U)** — the second-quantization lift for bosons; the next
  rung after assembly, deliberately out of scope here.
- **Infinite-mode limit** (`d → ∞`, direct-limit/completion Fock
  space) — priced since Rung 8.
- Unitary equivalence with `Symⁿ(H)` tensor-power sectors and the
  Gram/permanent formula — priced since Rung 8 (blocked upstream on
  n-fold tensor inner products).
- Continuum one-particle space, mass-shell representation, boosts —
  the Rung 9 Task 4 frontier, unchanged.

## Verdict rationale
The Rung 8 bosonic file delivered the inner product, the orthonormal
basis, and the basis-level adjoint, and priced the rest as assembly.
This module performs exactly that assembly — adjoint, CCR, number
operator, vacuum, sectors, cyclicity — with no weakened statements and
no new axioms. **RUNG 8B STANDS. The bosonic side of Rung 8 is
complete; bosonic Γ(U) is the next honest rung.**
