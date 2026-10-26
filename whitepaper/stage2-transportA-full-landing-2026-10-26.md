# Completion Transport — FULL: the Battery Correspondence Discharged

*Landing dossier, 2026-10-26. Module: `lean/ThetLogos/SliceTransportA.lean`
(581 lines, strict 11, defs 1, zero `sorry`, zero `native_decide`;
main-tree build green, 3,695 jobs, parent-verified on the shipped
text). **Parts of the Clay Yang–Mills statement closed by this
landing: 0.***

## What closed

Route A′ went around the pin's functional-calculus wall — no `cfc`
at the pre-completion operator anywhere — using the compact spectral
decomposition instead. Three headlines, each with axiom set exactly
`[propext, Classical.choice, Quot.sound]`:

1. **`transferOp_form_gap_circle`** — the one remaining step of the
   transport: at the U(1) seat, for every `z ⊥ Ω`,
   `⟪z, transferOp z⟫.re ≤ (1 − δ)·‖z‖²`.
2. **`sliceTransport_gap_pairing`** — the battery's gap conjunct for
   the completed operator `T̂_c`, assembled from A1's moments, A3's
   `b₁² ≤ b₂`, and the form-gap, divided through by `b₁`.
3. **`sliceSpectralCorrespondence_of_transport`** — the honest
   battery's one named hypothesis, `SliceSpectralCorrespondence`,
   is **discharged at the U(1) seat**: it is now a theorem there,
   modulo exactly the seat's carried data (β > 0, δ ∈ (0, 1),
   `GapBoundU1`, the carried Hilbert basis).

## The route, in one paragraph

Compress the transfer operator to the vacuum-orthogonal complement
H₀. Its eigenvalues are eigenvalues of the full operator, never 1
(vacuum simplicity), so `GapBoundU1` bounds them all by 1 − δ; the
spectral radius of a self-adjoint operator is its norm, giving
‖S‖ ≤ 1 − δ, and the Rayleigh quotient at z is the claimed pairing.
If δ > 1, every nonzero eigenspace is orthogonal to itself, the
compact spectral theorem leaves z = 0, and the bound is trivial.

## What this completes — and what it does not

**Stage 2's fixed-volume story now has no open conjuncts.** The
stepper and the river were identified (FG-2c-4: S(1) = T̂_c); the
Jensen clause fell (FG-2c-4); the gap clause — the last one — falls
here. At the U(1) seat, for every β > 0 and every even N, the
transfer operator has a spectral gap δ(β, N) > 0 with no hypotheses
left except the carried basis convention, and the completed
Hamiltonian's pairings inherit it.

Untouched, as ever: **uniformity across N** (Item 3, the wall) and
the **continuum limit** (Item 4, the frontier — no spacing, no
tuning curve, no continuum object). A per-instance gap at every
fixed volume is not a continuum mass gap, and this dossier does not
call it one. NO CLAIM; dials 0/4.

## Census effect

Strict 5,800 → **5,811**; attribute-inclusive 5,867 → **5,878**;
modules 189 → **191** (SliceTransportA; Q7DFTPost also counted since
the last full refresh); `sorry` placeholders unchanged at **6**.

## Backers since last landing

No new backers inscribed in this interval; the roll stands as
recorded in `BACKERS.md`. Every gift is published with the proof
stream, named as the giver wishes, amounts only with the giver's
permission — the standing reciprocity of this house.
