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
- **Lean side:** CERTIFIED 2026-10-30 — B7-PROBE-b
  (`verdict_C3_B7`, Seat (C₃, χ)) and B7-PROBE-c
  (`verdict_S3_B7` and the assembled `verdict_B7Probe`,
  Seat (S₃, std); the A3-gated factorization and the plain
  reading's failure both proved as theorems). The verdict
  below is theorem-grade at both seats.
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

### BR1-009 — VL-0, the vortex-locus probe at the pin seat, Python side (landed 2026-10-30)

- **Python side:** `routeb-general-scratch/vl0_seat.py` (output
  `vl0-run.txt`) — exact rational arithmetic throughout (ℚ,
  complex entries as rational pairs; sympy exact-Rational
  cross-check agrees). Parent re-ran the script at landing:
  run log byte-identical.
- **Lean side:** queued — VL-2 (P-VL1: finrank of the kernel
  of `commMap K₀` on W22 = d₀; P-VL2: the membership list)
  and VL-3 (P-VL3, the family corollary in the probe's true
  form). The value below is probe-grade (T4) until they land.
- **Proposition checked:** at the registered seat
  K₀ = (smDirac 1 2 3 5 7)², the real commutator system
  [K₀, Σ cᵢ·dirs22ᵢ] = 0 over the W₂₂ span (rank, kernel
  dimension d₀, kernel basis in dirs22 coordinates), the
  family locus {y ∈ ℂ⁵ : [K₀, smDirac y] = 0}, and the
  forced member D_F(y₀) (thermal_flux_vanishes).
- **Result: d₀ = 10 (rank 12) — a middle value.** Kernel =
  the family locus embedded in the SM directions (the E, U, D
  directions individually; the (ν, R) pair confined to
  yR = 7·yNu) ⊕ exactly one exotic complex direction
  (exoticReEREbarR, exoticImEREbarR); the other ten exotic
  directions are excluded. Family locus: real dimension 8
  (ℂ³ over (yE, yU, yD) free × the (yNu, yR) ℂ-line
  yR = 7·yNu) — NOT the ℂ-line (dim 2) the scoping expected;
  P-VL3's statement follows the probe. Every kernel vector
  verified by direct substitution on all 1024 entries.
  K-VORTEX-1 does not fire (neither end); K-VORTEX-2 does
  not fire (the kernel strictly exceeds the forced lines —
  the exotic direction is forced by nothing landed).

### BR1-010 — PHI-C-PROBE, the icosidodecahedral incidence complex, Python side (landed 2026-10-30)

- **Python side:** `routeb-general-scratch/phicprobe.py`
  (output `phicprobe-run.txt`; explicit tables in
  `phicprobe-tables.json`) — exact arithmetic throughout
  (coordinates in ℚ(√5) with rational coefficients, incidence
  over ℚ; no floats). Parent re-ran the script at landing:
  run log and tables byte-identical.
- **Lean side:** queued — PHI-C0 transcribes the exported
  tables (orientation convention as recorded in the run
  log); PHI-C1/C2/C3 prove against them. The values below
  are probe-grade (T4) until PHI-C3 lands.
- **Proposition checked:** for the icosidodecahedron as a
  cell complex on S² (V = 30, E = 60, F = 32 = 20 triangles
  + 12 pentagons), the oriented incidence maps ∂₁ (30×60),
  ∂₂ (60×32) over ℚ: ranks, kernels, face-family
  independence, and ∂₁∂₂ = 0. Self-checks (each edge in
  exactly one triangle and one pentagon; 1-skeleton and
  dual graph connected; Euler = 2) all pass exactly.
- **Result: rank ∂₁ = 29; rank ∂₂ = 31; ker ∂₂ = the
  constants (dim 1); triangle-boundary rank 20;
  pentagon-boundary rank 12; ∂₁∂₂ = 0 entrywise; homology
  (H₀, H₁, H₂) = (1, 0, 1)** — the scoping memo's §1 paper
  values, certified exactly, no deviation on any item.
  COMBINATORICS ONLY: this entry concerns a polyhedron's
  chain complex and nothing else.

### BR1-011 — XYZ-3, the first live tripotent family search, Python side (landed 2026-10-30)

- **Python side:** `routeb-general-scratch/xyz3-search.py`
  (run record `xyz3-run.txt`, pre-registration in its Section A
  written before any search ran) — exact arithmetic throughout
  (entries in ℚ(i,√3) as 4-tuples over ℚ in the basis
  {1, i, √3, i√3}; no floats in any decision path). An
  independent second implementation (plain dict matrices,
  direct ternary products) recomputed three sample triples
  and agreed exactly on round sizes and reached sets
  (run record, Section E).
- **Lean side:** the posted question and definitions mirrored
  exactly — `xyz_tripotents_exist` and `MemGenTRO`
  (`ThetLogos/XYZTripotents.lean` §3: the two-constructor
  WORD closure, `of_mem` / `of_ternary`; no span in the
  inductive), `ternaryMat` (`ThetLogos/TRO.lean`),
  the generator definitions `UJ` (`ThetLogos/Scaffold32.lean`),
  `genH`, `genM`, `genC`, `smGen`
  (`ThetLogos/MartinettiRep.lean`), and `tripotent_tripT` /
  `tripT` (`ThetLogos/XYZBoundaryMarker.lean`). Spot-entry
  cross-checks against landed lemmas passed BEFORE searching
  (`genM_seven_18_18`: genM 7 (18,18) = 1/√3;
  `smGen_one_offdiag`: smGen 1 (0,1) = 1; `genH_supp_block`
  supports; `tripT_entry_18_18` / `tripT_entry_18_20` /
  `tripT_apply_of` entries) — run record, Section B.
- **Proposition checked:** for the pre-registered list of
  385 triples — unordered distinct pairs from
  {UJ, genH k (k ∈ Fin 3), genM a (a ≠ 7)} (11 members,
  55 pairs) × the 7-member tripT family (tripT, its
  UJ-conjugate, its two other T₀ row positions, and its
  transports to triplets T₁, T₂, T₃) — the exact MemGenTRO
  word closure to depth ≤ 2 (ternary closure rounds,
  cumulative), scored by which of the 12 `smGen g` are
  reached as exact words. Depth 3 was NOT run: the
  pre-registered rule required every triple to satisfy
  |W≤2| ≤ 300 and dim span ≤ 96; observed max |W≤2| = 358
  (max span dim 30), so depth stayed 2 for the whole list.
- **Result: EXHAUSTED at depth ≤ 2 and the stated list.**
  All 385 triples ran, no caps hit (20.4 s total). Max score
  2/12; every reached generator is one of the triple's own
  first-two pool members, reached by `of_mem` — no triple
  produced a genuine `of_ternary` reach, and no triple
  exceeds the corpus's documented partial positives
  ({genC, UJ, gammaF} → 1 of 12; {genH 0, UJ, genM 0} →
  2 of 12, both by membership). **This is K-XYZ-2 at the
  stated depth and list ONLY — a family kill at full rank;
  the question `xyz_tripotents_exist` stays OPEN.** Failure
  to find is not a kill in any other form; no Python hit
  occurred, so nothing promotes to XYZ-5. NO CLAIM; dials 0/4.

### BR1-013 — XYZ-4 symmetry-reduced families (diagonal-unitary patterns)

- **Python side:** `routeb-general-scratch/xyz4-search.py`
  + `xyz4-run.txt` (§A pre-registration written before
  solving, 2026-10-30 20:02 EDT). Reduction: diagonal-
  unitary invariance patterns (11 patterns, all closed).
  8,872 exact verified tripotent survivors on the searched
  slice; 7,260 triples fed at word depth ≤ 2; max score
  4/12; 357 genuine `of_ternary` reaches (all
  permutation-orbit mates of pool members); smGen 11
  unreached in any form.
- **Outcome: PARTIAL at full rank** — the searched slice
  (17-value frame alphabet) exhausted; the reduced family
  NOT exhausted (1/√2 frames outside the alphabet, named
  in §A3). A K-XYZ-2-grade bound on a named slice only;
  **the question `xyz_tripotents_exist` stays OPEN**;
  failure to find is not a kill; XYZ-5 does not fire.
  Dossier: `whitepaper/xyz4-landing-2026-10-30.md`.
  NO CLAIM; dials 0/4.

### BR1-012 — Q7CR-2, the instantiated Q⁷C⁴R⁴ spectrum, Python ↔ Lean (landed 2026-10-30)

- **Python side:** `routeb-general-scratch/q7cr2-spectrum.py`
  (run record `q7cr2-run.txt`) — exact arithmetic throughout
  (`fractions.Fraction`; no float eigenvalues in any certified
  value). Factor package laws verified on exact matrices
  (Q⁷/C⁴ Hermitian packages; R⁴ against the Minkowski form).
  The composite D² spectrum computed as the exact
  Kronecker-sum (sumset) of the three factor-square spectra:
  448 eigenvalues; spectral trace M1 = 2723; second moment
  M2 = 1518111/64; minimum 1/64 (multiplicity 16); maximum
  841/64 (multiplicity 32); 14 distinct values. A variation
  run with the Q⁷ diagonal's first pair changed (3 ↦ 4) gave
  M1′ = 3619 ≠ 2723.
- **Lean side:** `ThetLogos/Q7C4R4Spectrum.lean` — anchors
  `diracQ7C4R4` / `diracQ7C4R4_sq`
  (`ThetLogos/Q7C4R4Assembly.lean`), `FactorOp`
  (`ThetLogos/Q7C4R4Realify.lean`), `z4Energy`
  (`ThetLogos/ThermalZ4Ladder.lean`). Factor packages are
  labeled choices on the module's face: Q⁷ CHOSEN diagonal
  (3, -3, 2, -2, 1, -1, 0) under the swap-pairing grading;
  C⁴ the ladder-generator analog — T2 input `z4Energy`,
  centering CHOSEN — (-3/8, -1/8, 1/8, 3/8) under reversal;
  R⁴ CHOSEN diagonal (0, 2, -2, 0) under the spatial swap.
  Required names `s₇ : Fin 14 → ℝ`, `s₄ : Fin 8 → ℝ`,
  `s_R : Fin 4 → ℝ` (§4). An explicit real eigenbasis
  (`basisComp`, §5) diagonalizes the composite D²
  (`dirac_sq_basisComp_eig`); the eigenvalue multiset
  `spectrumQ7CR2` (§6) carries `spectrumQ7CR2_card` = 448,
  `spectrumQ7CR2_sum` = 2723, `spectrumQ7CR2_sq_sum`
  = 1518111/64, with endpoints 1/64 and 841/64 attained.
  Axiom check on the headlines: propext, Classical.choice,
  Quot.sound only.
- **Proposition checked:** the D² spectrum of the
  instantiated Q⁷C⁴R⁴ product Dirac is the sumset multiset
  of the factor-square spectra, with product multiplicities;
  Python and Lean agree exactly on count, both moments, and
  the endpoints.
- **Result: exact agreement.** K-Q7CR-2 evaluated in the
  landed form and does NOT fire: a second admissible Q⁷
  package (`factorQ7'`, first diagonal pair 4, -4) is
  certified with spectral trace 3619 ≠ 2723
  (`k_q7cr2_not_forced`), so the spectrum is an explicit
  function of the factor data, not forced. No measured
  number is claimed by this line; no entropy language.
  NO CLAIM; dials 0/4.

### BR1-014 — Q7CR-SA2, the instantiated spectral-action evaluation, Python ↔ Lean (landed 2026-10-31)

- **Python side:** `routeb-general-scratch/sa2-eval.py`
  (run record `sa2-run.txt`) — exact arithmetic throughout
  (`fractions.Fraction`; no floats at any verdict line). From
  Q7CR-2's factor data alone (Q⁷ diagonal (3, −3, 2, −2, 1, −1, 0);
  C⁴ centered ladder `d₄ k = k/4 − 3/8`; R⁴ diagonal
  (0, 2, −2, 0)): the factor-square eigenvalue lists (realified
  14/8/4), their moments, the 448-value sumset spectrum with
  moments by direct summation AND by SA0's printed composition
  forms (the two routes identical in-run), the endpoints, and
  the polynomial actions for `f = x⁰, x¹, x²` at Λ = 1, 2 in
  both moment and spectral-sum form. 33 checks, all AGREE.
- **Lean side:** `ThetLogos/SpectralActionQ7CR.lean` §7
  (Q7CR-SA2) — the seat's factor spectral lists discharged from
  Q7CR-2's certified forms (`spectralListQ7Seat`,
  `spectralListC4Seat`; the R⁴ list `spectralListRSeat`
  consumed AS SUPPLIED DATA from Q7CR-2's explicit site
  eigenbasis — the K-SA-3 seam inherited and stated on §7's
  face, no §6.5-style production of the R⁴ list asserted);
  factor moments `seat_mom7/4/R_zero/one/two`
  (14/56/392; 8, 5/8, 41/512; 4/8/32) read off the lists by
  `SpectralList.trace_pow_eq_sum` against Q7CR-2's factor
  anchors; composite moments assembled by SA-COMP-2's printed
  forms — `seat_M0` = 448, `seat_M1` = 2723, `seat_M2` =
  1518111/64 — and tied to Q7CR-2's multiset anchors
  (`seat_M0_eq_card`, `seat_M1_eq_sum`, `seat_M2_eq_sq_sum`);
  SA-COMP-4 instantiated (`spectral_action_poly_composition_seat`)
  with the `x⁰/x¹/x²` cutoffs evaluated in moment and
  spectral-sum form (`seat_action_x0/x1/x2`, `seat_specSum_x0/x1/x2`:
  448 at every Λ; 2723/Λ²; (1518111/64)/(Λ²)²); SA-COMP-3
  instantiated at the seat (`heat_trace_factorization_seat`).
- **Proposition checked:** the spectral action of the
  instantiated Q⁷C⁴R⁴ composite at Q7CR-2's seat, evaluated by
  the composition machinery, has moments M 0 = 448,
  M 1 = 2723, M 2 = 1518111/64 and the stated polynomial-cutoff
  values; Python and Lean agree exactly on every value.
- **Result: exact agreement (33/33 checks).** Fences on the
  face of §7 and restated here: the action is NUMERICAL
  (spectral sums/moments), never an operator `f (D²)`; the
  finite moments are coefficient-grade data of the chosen
  seat, NEVER Seeley–DeWitt coefficients or gravity terms, and
  no curvature slot exists in this object; any coincidence of
  an output with a measured value is a new-entry Dial-1 matter
  (K-SA-4), not a result of this line. The SA line is not a
  gauntlet item: no bearing on the meta-kill, the trifecta, or
  the C⁴ leg. NO CLAIM; dials 0/4.

### BR1-015 — C96-4, the Census-96 discharge (402 = 3·46 + 3·88), Python ↔ Lean (landed 2026-10-31)

- **Python side:** `attack4_corrected/attack4_3gen.py`
  (extracted from git commit `90a80e7`, where it was read
  after its purge from the working tree by `457d150`;
  re-run record `routeb-general-scratch/c964-attack4-run.txt`,
  with its one-generation dependency `attack4_corrected.py`
  and `results/dbasis.npy` extracted from the same commit) —
  a NUMERICAL rank computation throughout (normal-equation
  eigenvalues, relative tolerance 1e-8; T4 probe). Its census
  steps report: admissible dimension at C^96 = 2352
  (= 3x272 diag + 3x512 off-diag); per-diagonal-block
  order-one nullity 46 (gap 0.774); per-mixing-block
  order-one nullity 88 (gap 0.774); TOTAL order-one nullity
  at C^96: 402 (= 3x46 diag + 3x88 mixing). Honest seam, on
  the record: the historical script then errors in its
  Step 4 (classification of the mixing directions,
  `np.tensordot` shape mismatch, line 231) — a bug in the
  file as committed, after every census number was printed;
  the script was re-run unmodified and the classification
  step is not part of this check.
- **Lean side:** `ThetLogos/Census96Assembly.lean` (C96-4) —
  `finrank_census96Sol_eq` / `census96_proved`:
  `Module.finrank ℝ Census96Sol = 402`, by the landed
  decoupling equiv `census96SolEquiv` and finrank additivity
  over products and pi types, consuming exactly the two
  proved sector numbers `finrank_sol32_eq = 46` (C96-2b) and
  `finrank_pairSpace_eq = 88` (C96-3b2; `PairSpace` is
  `Census96PairSol` by its landed definition), with
  `Fintype.card (Fin 3) = 3` and `card_genPair = 3`; plus the
  separately fenced diagonal pin `census96Diag_proved`
  (`finrank ℝ Diag96Sol = 46`, the `smDirac3diagLM` image of
  `Sol32` under an injective map — the flavour-diagonal
  corollary, NOT the census). All three headlines on exactly
  [propext, Classical.choice, Quot.sound].
- **Proposition checked:** the three-generation order-one
  census numbers — per-diagonal nullity 46, per-mixing-pair
  nullity 88, total 402 via the split 3·46 + 3·88 — agree
  between the Python census and the Lean theorem, with
  **402 ≠ 414 = 9·46** on the face (the mixing pair
  contributes 88, not 92).
- **Result: exact agreement.** The T4 note in
  `ThreeGen.lean`'s header is promoted by this discharge:
  the note becomes a proved theorem — exactly that, no
  more. Fences: generations IMPOSED; CKM/PMNS input-only;
  no flavour quantity derived; posted question Q3
  (generations) OPEN regardless of outcome; the old
  46 → 10 gloss UNSOUND AS STATED, never cited. NO CLAIM;
  dials 0/4.
