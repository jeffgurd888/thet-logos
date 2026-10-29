# The cross-check registry — BRIDGE-1 (Span 1: Lean ↔ Python)

*Standing registry, opened 2026-10-29 under the three-span bridge
scoping (`scoping-the-bridge-2026-10-28.md`, Span 1). NO CLAIM;
dials 0/4. Fence on its face: this registry is a verification
instrument. Simulations audit, probe, and catch errors; they do
not move the dials, do not convert exhibit or analogue material to
theorem grade, and do not touch Span 3 (continuum/reconstruction —
FRONTIER, named, unpriced, unbuilt; its vocabulary is not
spendable here).*

## Protocol (every entry, no exceptions)

A Python probe of a corpus object is **registered** only if it
ships with:

- **(a) The exact Lean statement it checks** — module, theorem
  name, and the proposition in words, stated so both sides are
  checking *the same* proposition.
- **(b) Exact arithmetic at the verdict line** — rational/integer
  arithmetic only; no floats at the verdict line.
- **(c) The reconciliation rule** — agreement = probe PASS at its
  stated scope (a seat, a finite case: never more). Disagreement =
  a full-rank flag: the parent re-derives, the loser is corrected
  on the record, and the correction itself is registered here.
  Mismatches are never quietly edited away; the B5-PROBE
  precedent is the model (its one convention mismatch, density
  vs `colRe`, `d⁴ = 16`, was promoted to a *proved* Lean lemma,
  `K4S3_calibration`, instead of a comment).

**Kill K-BR1:** if a probe's Python and Lean sides cannot be made
to state the same proposition, the probe is exhibit-grade. It is
labeled so and is **not** registered.

## Entries

### BR1-001 — the κ₄ probe (landed 2026-10-27, retro-registered)

- **Python side:** `routeb-general-scratch/kappa4_probe.py`,
  `routeb-general-scratch/kappa4_seat.py` — exact enumeration at
  two seats; the (S₃, std) face-block matrix `PhiS3` recomputed
  with an independent second reading, agreeing; pair-block
  margins exactly zero.
- **Lean side:** `ThetLogos/PlaneCrossingKappa4Probe.lean` —
  seat (C₃, χ) proved end-to-end in Lean (`FC3_eq`: the
  α-averaged plaquette monomial is `(1/8) · reChi (h − h′)`); at
  (S₃, std) the Lean content is exact algebra about the computed
  blocks (outer-product structure, form identities, margins,
  positivity certificates).
- **Proposition checked (both sides):** the dependent β⁴
  coefficient κ₄^dep at the two seats has no negative eigenvalue;
  pre-registered kill K-K4 does not fire.
- **Verdict:** PASS at both seats, at seat scope only. Not a
  statement about general (G, ρ).

### BR1-002 — B5-PROBE, the κ₅ channel probe (landed 2026-10-28, retro-registered)

- **Python side:** `routeb-general-scratch/s3-seat-computation.py`
  (outputs `s3-run1.txt`, `s3-check2.txt`) — exact enumeration
  over the S₃⁴ stratum configurations at N = 4;
  `kappa4_seat.py` seat machinery reused. Exact rational
  arithmetic at the verdict line.
- **Lean side:** `ThetLogos/PlaneCrossingBeta5Probe.lean` —
  `K4S3_calibration : K4S3 a b = 16 * PhiS3 a b` (the convention
  calibration, proved, not commented); `K5S3_eq : K5S3 a b =
  4 * K4S3 a b`; the (C₃, χ) side proved in-Lean by character
  sums, with `K5C3_form` / `K5C3_form_nonneg` and spectrum
  `{0, 3/8, 3/8}`; joint verdict `verdict_S3`.
- **Proposition checked (both sides):** at N = 4, seats (C₃, χ)
  and (S₃, std), the κ₅ channel form vanishes exactly on
  ker κ₄^dep and is a positive multiple of the κ₄ kernel form —
  ×2 at (C₃, χ), ×4 at (S₃, std). Pre-registered kills K-K5 /
  K-K5b do not fire.
- **Verdict:** PASS at both seats, seat scope only. The β⁵ sign
  at general (G, ρ) remains FRONTIER (triple twirls unowned);
  this entry moves no dial.
- **Registered correction:** the probe script's first wrap-chain
  reading took the loop in reverse order and produced spurious
  fiber values; corrected on the record in the module — the
  reconciliation rule working as designed.

### BR1-003 — the B6-0 card-4 exception check (landed 2026-10-29, this brick)

- **Python side:** `routeb-general-scratch/bridge-registry/b6_0_exception_check.py`
  — exact integer arithmetic only; checks one explicit finite
  configuration, coordinates and multiplicities in the script.
- **Lean side:** the corrected statement of
  `ThetLogos/OrderSixSelection.lean`'s
  `six_column_channel_characterization` — its card-4 clause is
  the disjunction (primitive quad ∨ private column) that this
  check forced. The configuration itself is *not* exhibited as a
  Lean construction; correspondence is at statement level, and
  the entry is registered at exactly that scope.
- **Proposition checked:** at N = 4 there exists a
  multiplicity-6 configuration on 4 columns — (0,0,0)→(1,0,0) ×1,
  (0,0,0)→(0,1,0) ×2, (1,0,0)→(2,0,0) ×1, (2,0,0)→(2,1,0) ×2 —
  that is weighted-fully-shared (every support site has weighted
  degree ≥ 2) yet has sites of distinct degree 1, so its support
  is **not** a primitive quad. This refutes the β⁶ scoping's
  card-4 line as originally stated.
- **Verdict:** the scoping claim FAILS as stated; B6-0 was
  re-stated in disjunctive form before building, and the
  correction is on the face of the Lean module. A kill of our
  own scoping sentence, at full rank — the registry's first
  entry where the Python side corrected the *statement*, not a
  number.

### BR1-004 — B6-PROBE, the β⁶ joint-kernel channel probe (landed 2026-10-29)

- **Python side:** `routeb-general-scratch/b6probe_seat.py`
  (output `b6probe-run.txt`) — exact enumeration at N = 4 over
  the two seats' stratum configurations; integer accumulation
  with `Fraction` at every verdict line. Parent re-ran the
  script at landing: output identical.
- **Lean side:** `ThetLogos/PlaneCrossingBeta6Probe.lean` —
  channel kernels defined from channel content at both seats;
  proportionality theorems (never definitions);
  `verdict_B6Probe`, axioms exactly
  `[propext, Classical.choice, Quot.sound]`.
- **Convention check (both sides):** the Python extraction
  reproduced ker κ₄^dep from its own κ₄ form before any
  channel was evaluated — constants at (C₃, χ),
  {φ₀ = φ₂} at (S₃, std) — and the Lean side re-derived both
  kernel characterizations in-module.
- **Proposition checked (both sides):** at N = 4, seats
  (C₃, χ) and (S₃, std), every new order-6 channel's diagonal
  form vanishes identically on the joint kernel
  K = ker κ₄^dep: each channel kernel is an exact positive
  multiple of the seat's κ₄ kernel (C₃: 3111 = 3×,
  2211-adj = 2×, 2211-opp = 1×, C6 = ¼×, Θ = ¼×; S₃:
  3111 = 12×, 2211-adj = 8×, 2211-opp = 4×, C6 = ¼×, Θ
  vanishing on the convention span below). Pre-registered
  kill K-K6 does not fire; the pre-registered outcome is
  (ii) — the regress continues. Every Lean constant
  reproduced the Python table exactly; no disagreement was
  recorded on either side.
- **Convention recorded:** Θ at (S₃, std) had no landed
  restriction convention (the Python side stopped that
  channel, K-PROBE-a); the Lean module fixes the convention
  on its face — K's pullback := the joint candidate span
  {1, s₁, s₂, s₁s₂} — and proves vanishing on the whole span,
  which implies vanishing under every candidate sub-reading
  (the Python side independently verified the restriction is
  exactly zero under every candidate reading).
- **Verdict:** outcome (ii) at both seats, at seat scope only.
  Not a statement about general (G, ρ), and not a statement
  about 𝒜 ⪰ 0 in either direction.

## Standing rules going forward

- Every future probe brick files its registry entry as part of
  its landing checklist (that forward duty is BRIDGE-2, adopted
  when this registry opened; unregistered probe numbers do not
  ship in dossiers or posts).
- An entry's scope line is part of the entry: a PASS is a pass
  *at its scope*, and quoting it beyond its scope is a registry
  violation on the face of this file.
- New entries are appended, never rewritten; corrections add a
  dated amendment under the entry they correct.
