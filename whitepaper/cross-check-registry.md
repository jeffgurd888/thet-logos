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

### BR1-005 — A2-2-PROBE, the plaquette telescoping seat check (landed 2026-10-29)

- **Python side:** `routeb-general-scratch/a22probe_seat.py`
  (output `a22probe-run.txt`; verdict memo
  `a22probe-verdict.md`) — exact polynomial arithmetic in
  ℚ[t], t = e^{−1/2}, recovered by evaluation–interpolation
  with counts sanity-checked to |G|⁴; sign checks
  interval-certified; deterministic, seeded (20261029).
  Parent re-ran the script at landing: output
  byte-identical.
- **Lean side:** none — this probe checks the REGISTERED
  statement of `ThetLogos/PlaquetteTelescoping`
  (`PlaqTelescoping` / `PlaqKernelPos`, A2-2a) at finite
  seats; there is no Lean seat module, and none is implied.
  The propositions checked are the registered ones, read
  literally.
- **Proposition checked:** at β = 1, seats (S₃, std) and
  (D₄, std) (kill-bearing) with (ℤ₅, 1-dim character) as
  control: (T) `PlaqBlock(u, u′) = Ψ(PlaqHol u, PlaqHol u′)`
  exactly (residuals: 0 nonzero over 17,552 checks at Seat A,
  67,536 at Seat B, 6,550 at the control); (P) Ψ's spectrum
  interval-certified ≥ 0 at both kill-bearing seats, with
  separate class-invariance exact; the coefficient law
  c_π = (ĉ_π/dim π)⁴ exact at both kill-bearing seats (at
  non-self-dual labels the law pairs k ↔ −k, certified at
  the control: c_k = (ĉ_k·ĉ_{−k})²). Pre-registered kill
  K-A2 does not fire; outcome: probe PASS, seat evidence
  only.
- **Certified correction (same volume):** the claim-path
  memo's literal quotient form (R1) is CERTIFIED DEAD at
  both kill-bearing seats — equal-quotient pairs with
  block difference (1−t³)⁴/324 ≈ 1.12×10⁻³ (Seat A) and
  (1−t⁴)⁴/1024 ≈ 5.46×10⁻⁴ (Seat B), intervals excluding 0.
  The revised entry R2 (registered by A2-2a) is the live
  statement.
- **Verdict:** PASS at two nonabelian seats, seat scope
  only. Not a statement about general (G, ρ); Route B's
  proof bricks (A2-2b onward) are unlocked, not landed.

### BR1-006 — GD-PROBE-a, the Gram-dominance discriminator, Python side (landed 2026-10-29)

- **Python side:** `routeb-general-scratch/gdprobe_seat.py`
  (output `gdprobe-run.txt`; verdict memo
  `gdprobe-verdict.md`) — exact rational arithmetic,
  calibrated in-script against BR1-004's seats, two
  independent exact engines agreeing on full grids. Parent
  re-ran the script at landing: output identical.
- **Lean side:** none yet — GD-PROBE-b/c are HELD: the
  probe's pre-registered step-0 gate failed at every seat
  (below), so there is no discriminator verdict to certify.
  The certifiable statements, if wanted as targets, are the
  step-0 identities (κ₄ kernel = χχᵀ/d⁴ at the two primary
  seats) plus the rejected-seat multiples table in the
  dossier.
- **Proposition checked:** the step-0 certificates
  themselves — the κ₄ observable quotient dimension at
  (S₄, std) and (Q₈, ρ₂), reserves (S₄, std⊗sign) and
  (A₅, 3-dim) — against the pre-registered requirement ≥ 3.
- **Verdict: STEP-0 GATE FAILS AT EVERY SEAT.** Every
  seat's κ₄ form has rank 1 (per-quad kernel exactly
  χχᵀ/d⁴ at every real-character seat, verified entrywise);
  quotient dimension 1 < 3; all seats REJECTED as
  discriminators in the pre-registered reserve order.
  GD-i / GD-ii / GD-iii are NOT reached and no outcome is
  routed. GD-iii does not fire: every channel restriction
  to ker κ₄^dep is exactly zero at both primary seats.
  The discriminator re-scopes on the record: a working
  discriminator needs a κ₄ seat of rank ≥ 3, which no
  real-character seat supplies (the complex-character seat
  (C₃, χ) reaches rank 2); naming one is a new
  pre-registration. Dossier:
  `whitepaper/gdprobe-a-landing-2026-10-29.md`.

## BRIDGE-2 adoption — the landing-checklist amendment (2026-10-29)

BRIDGE-2 (Span 1's forward duty, per the bridge scoping of
2026-10-28) is ADOPTED as of this entry and is a mandatory
item on every future probe's landing checklist:

- **Every probe landing names its registry entry ID in its
  dossier, or registers a new entry in this file before its
  dossier ships.** Unregistered probe numbers do not ship in
  dossiers or posts.
- **A probe with no statable Lean counterpart is
  exhibit-grade per K-BR1 and says so in its dossier** — it is
  not registered as a cross-check, and its numbers carry the
  exhibit tier wherever they are quoted.
- The registry step is part of the landing ceremony itself
  (parent verification → registry entry → dossier → README →
  commit → push), not an afterthought appended to it.

Fences: simulations audit and probe; they do not move the
dials (0/4) and assert nothing physical. Span 3 of the bridge
(continuum / reconstruction) stays named, unpriced, unbuilt.

### BR1-007 — GD-PROBE-R-a, the re-registered Gram-dominance discriminator, Python side (landed 2026-10-30)

- **Python side:** `routeb-general-scratch/gdprobeR_seat.py`
  (output `gdprobeR-run.txt`) — exact rational arithmetic,
  calibrated in-script against the B6-PROBE (BR1-004) seats
  (reproduced exactly); two independent exact engines agreeing
  (tensor vs direct α-enumeration). Parent re-ran the script
  at landing: run log byte-identical.
- **Lean side:** CERTIFIED 2026-10-30 — GD-PROBE-R-b
  (`ThetLogos.GramDominanceProbeF21`,
  `gd_probe_R_b_verdict_F21`: kernel theorem, GD-iii
  non-firing, multiples, and the Θ escape proved under all
  six readings) and GD-PROBE-R-c
  (`ThetLogos.GramDominanceProbeSL23`,
  `gd_probe_R_joint_verdict` assembling both seats; standard
  three axioms on the headlines, parent-checked). The
  verdict below is theorem-grade at both seats.
- **Proposition checked:** the re-registered discriminator of
  `scoping-gd-discriminator-rescope-2026-10-30.md` §4: step-0R
  certificates (ker dim ≥ 3; e₁ = 0; escape-room target dim
  ≥ 3; Θ orbits ≥ 10) at (F21 = C₇ ⋊ C₃, ρ₃) and
  (SL(2,3), ρ₂′), then the six channel forms per seat against
  the seat κ₄ form — proportionality (GD-strong), kernel
  restriction to ker κ₄^dep (GD-kernel / K-Kn), and the Θ
  tests (Θ-1) escape / (Θ-2) kernel restriction.
- **Verdict: GD-ii — GD-strong DIES at full rank.** Both seats
  ACCEPTED at step-0R (κ₄ rank 2 both, per the rank law; ker
  dims 3 and 5; target dims 5 and 4 — the SL(2,3) demotion
  contingency does not trigger). The exhibiting channel is
  **Θ(2,2,2) at (F21, ρ₃)**: its orbit kernel (rank 14)
  **escapes under (Θ-1)** — it factors through none of the six
  single class variables and is a pullback multiple of κ₄
  under none of them. Every class-space channel at F21 is a
  positive multiple of κ₄ (λ = 10, 31, 50, 25, 7203/320) —
  proportionality survived the full 5-dimensional escape room
  there — and Θ escaped anyway. At SL(2,3), four channels are
  identically zero forms (λ = 0; they fail GD-i's
  positive-multiple requirement but are not non-multiples in
  the strict sense — the GD-ii route does not depend on their
  classification). **Every kernel restriction at both seats is
  exactly ZERO, so GD-iii does NOT fire and Route A stands.**
  GD-global and GD-kernel survive as targets, untouched.
  Scope: N = 4, the two registered seats named above; quoting
  this verdict beyond its scope is a registry violation.
- **Fences:** NO CLAIM; parts 0; dials 0/4. Simulations audit
  and probe; they do not move the dials.

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

### BR1-008 — B7-PROBE-a, the β⁷ probe at the owned seats, Python side (landed 2026-10-30)

- **Python side:** `routeb-general-scratch/b7probe_seat.py`
  (output `b7probe-run.txt`) — exact rational arithmetic; two
  independent computations (extraction engine vs direct
  enumeration of the Lean pattern sums: 102 entry checks, 0
  mismatches). Parent re-ran the script at landing: run log
  byte-identical.
- **Lean side:** queued — B7-PROBE-b (Seat (C₃, χ)) and
  B7-PROBE-c (Seat (S₃, std) + verdict), certifying the table
  below against `ThetLogos.PlaneCrossingBeta7`'s definitions.
  The verdict is probe-grade until they land.
- **Proposition checked:** on K₆ = ker κ₄^dep ∩ ker κ₅^dep ∩
  ker κ₆^dep at (C₃, χ) and (S₃, std), N = 4 (K₆ re-derived
  in-run: seat-K₆ = ker κ₄^dep at both seats), the restriction
  of every new order-7 channel excess (B7-1's list) — the
  β⁷ decision at the seats, with K-K7 armed.
- **Result: OUTCOME (ii) — every channel vanishes on K₆ at
  both seats; the decision passes to β⁸; K-K7 does NOT
  fire.** Class-space shape: the positive-multiple pattern
  (multiples at (C₃, χ): 5/2, 3, 3/2, 3, 3/4, 3/4, 1/8; at
  (S₃, std): 20, 24, 12, 24, 3/2, 3, 1/4 — seat data only,
  interpretation capped per the GD line's ruling). Nuance on
  the record: at (S₃, std) the orbit-pair channels factor
  through the A3-gated product class, not the plain product
  class (run log entry (0,4) is the exhibiting
  counterexample); the verdict is independent of the reading
  (every candidate K-pullback reading restricts to zero).
