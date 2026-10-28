# B5-PROBE — the Joint (κ₄, κ₅) Seat Evaluation: PASS

*Landing dossier, 2026-10-28. Module:
`lean/ThetLogos/PlaneCrossingBeta5Probe.lean`
(strict 56, defs 17; zero placeholders, zero
`native_decide`; main-tree build green, 3,452 jobs,
parent-verified; axiom sets exactly
`[propext, Classical.choice, Quot.sound]` on both
seat verdicts, parent-checked). **Parts of the Clay
Yang–Mills statement closed by this landing: 0.**
The pre-registered kill K-K5 does not fire — and
what the probe found instead is a rigid structure:
at both seats, the κ₅ channel form is a positive
multiple of the κ₄ form, so order 5 decides nothing
that order 4 left open. The joint kernel's first
possible decision order is β⁶.*

## The verdict and the numbers

At N = 4, the κ₅ channel form (`kappa5chan2111` on
the diagonal — κ₅^dep's dependent content modulo
B5-2's assembly identity, the fence on the probe's
face) **vanishes exactly on ker κ₄^dep**, margin
exactly zero, at both seats:

- **(C₃, faithful χ):** channel class kernel
  K5C3 = (3/8)I − (1/8)J, spectrum {0, 3/8, 3/8} —
  exactly **2×** the κ₄ class kernel (spectrum
  {0, 3/16, 3/16}). Per primitive quad of either
  type (plaquette or wrap chain), the channel total
  is (1/4)·Re χ(Δ) = 2× the κ₄ face factor; every
  doubled factor (each of the four doubled columns)
  is (1/16)·Re χ(Δ), and the three-factor averages
  vanish by the private-site mechanism.
- **(S₃, std):** the channel kernel is exactly
  **4×** the κ₄ kernel (`K4S3_calibration` proves
  the convention bridge: the κ₄ probe's density
  convention and B5-1's colRe convention differ by
  exactly d⁴ = 16, entrywise).

**K-K5 does not fire** (no certified negative on
the kernel at either seat — the restriction is
identically 0). **K-K5b does not fire** (the channel
is not identically zero — it is a positive multiple
of κ₄). The joint kernel — constant profiles at
(C₃, χ); {φ₀ = φ₂} at (S₃, std) — **survives order
5 untouched**. This is the degenerate-perturbation
regress, named on the record: each order so far
reproduces the previous order's kernel, and the
first order at which the joint kernel can be
decided is β⁶ — outside this probe's scope, and
now the β-line's named frontier.

## Provenance, stated plainly

At (C₃, χ) the per-term identities are proved in
Lean from the word definitions, both quad types.
At (S₃, std) the per-quad kernels are the seat's
computed matrices — provenance: exact enumeration
over all 1,296 α ∈ S₃⁴ (scripts and outputs in the
house scratch dir), the same status the κ₄ probe's
S₂ matrices had — and every form-level fact (outer
products, the calibration, channel = 4×κ₄, the
perfect-square forms, margins, the kernel, the
joint verdict) is proved in Lean. Two corrections
ride in the memo: the wrap chain's loop must be
taken in path order u₀u₁u₂u₃ (reverse order gives
spurious within-fiber values — an external-script
error, caught by the fiber-constancy check, the
Lean chain face in path order throughout); and the
d⁴ = 16 convention calibration between the two
probes, now a proved lemma rather than a footnote.

## Fences

Seat evidence at N = 4 and two seats only. Not a
general sign for κ₅^dep (its sign stays
unpriced/FRONTIER — triple twirls unowned); not a
statement at general (G, ρ) or other N; the channel
form stands for κ₅^dep modulo B5-2's assembly
identity. A PASS here means the small-β route
survives order 5 *at these seats* — the route's
fate now sits at β⁶, and the zero-margin pattern
(one more order, one more exact multiple) is itself
the datum to explain. NO CLAIM; dials 0/4.

Census effect: 7,040 → **7,096 strict** /
7,118 → **7,174 attribute-inclusive** / 241 → **242
modules**; the seven quarantined placeholders are
unchanged.

## Backers since last landing

No new backers inscribed in this interval; the roll
stands as recorded in `BACKERS.md`. Every gift is
published with the proof stream, named as the giver
wishes, amounts only with the giver's permission —
the standing reciprocity of this house.
