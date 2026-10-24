# THE GAP-THEOREM QUEUE — every named-but-unbuilt gap theorem in the charters and dossiers

**Date:** 2026-10-24. **Commission:** Jeff, 2026-10-24 — "build out
what you can from the foundations that we have — fill in all the
little gap theorems that make everything water tight."

**Status: GAP AUDIT ONLY.** This document enumerates, prices (only
where a source prices), and orders the open gap theorems named in
the program's charters and dossiers. It builds nothing and proves
nothing.

**NO CLAIM.** Parts of any official Clay statement closed by this
document: **0**. Census unchanged: 4,348 strict / 4,397
attribute-inclusive / 144 counted modules.

## How to read this document

Every item carries: **name**, **source** (the charter/dossier that
names it), the **gap** in the source's own terms, **price** exactly
as the source prices it (UNPRICED where no source prices — no price
is invented anywhere in this document), **dependencies**, **kill
condition** where the source names one, and a **class tag**:

- **QUEUE** — buildable from landed foundations; §1 gives the run
  order the dependencies force.
- **WALL** — research-scale or frontier; listed for honesty, NOT
  queued.
- **HELD** — waits on Jeff's word or a charter condition.
- **QUARANTINED** — sorry-backed obligations not dischargeable as
  stated (§4).

**Sequencing constraint (house rule):** one heavy Lean build at a
time. §1's run order is therefore a total order, not a menu: an
item starts when the previous one lands or dies by its named kill.

**Already closed since their charters were written (swept, not
queued):** Bridge Span (a), the Gibbs span — LANDED T1 2026-10-22
(`GibbsSpan`), so Landing Pad §5(a) and floor-to-ceiling V7 are
discharged; floor-to-ceiling V6, the general-Hermitian interior
stud — discharged by `HermitianReduction` (the Landing Pad §4
projectors remainder with it); Stokes–Einstein Rungs 1–2 and TVMD
Rungs 1–2 — LANDED 2026-10-22. TVMD has **no Rung 3 in the
record**: its chain's links 2–3 carry standing NO-GOs (K-TV2), and
Rung 2's conditional flux hook landed with the rung.

---

## §1 QUEUE — in run order

### Q1. `posToSlice` marginal identity
- **Source:** `gram-clause-transfer-matrix-scoping-2026-10-24.md`
  §2 (named loose end); home file `LatticeOSSpace.lean`.
- **Gap:** the measure.map of the product Haar measure under the
  slice-coordinatization equals the product measure — unproved,
  explicitly not used by the landed theorems; the TM charter notes
  R1/R3 may consume it.
- **Price:** **S** (priced in its home file, per the charter).
- **Dependencies:** none. Consumed by Q3 (R1) / Q8 (R3) if their
  iteration needs it.
- **Kill:** none named in source.

### Q2. Pointwise positivity of `T_β f`
- **Source:** `pitch-4-stage-1b-d-2026-10-17.md`, fences.
- **Gap:** "`Pointwise positivity of `T_β f` (positive functions
  to positive functions) is not stated; it follows from the form
  positivity by the standard indicator argument (priced **S**,
  not formalized here)."
- **Price:** **S**.
- **Dependencies:** none — `transferOp_form_nonneg` (landed,
  Stage 1b-D) is its input. The TM charter notes it is "a
  corollary shape, not needed by this route"; it is queued
  because it is a named, priced hole in a landed module.
- **Kill:** none named in source.

### Q3. TM R1 — the layer factorization
- **Source:** `gram-clause-transfer-matrix-scoping-2026-10-24.md`
  §4 (R1). (TM R0 passed on paper and step S1 landed T1,
  2026-10-24 — `LatticeTransferID`; the ladder's remaining rungs
  are Q3, Q4, Q8, Q11.)
- **Gap:** "Formalize the time-direction Markov/layer
  factorization of the Gibbs measure at one-step level: the Gibbs
  expectation of a two-slice observable as the slice-marginal
  integral of the one-step kernel pairing, in the form
  `transferOp_inner` consumes and R3 iterates — the lemma the
  1b-D dossier fenced at M–L, taken here at its one-step core.
  Includes the `posToSlice` marginal identity if the iteration
  consumes it."
- **Price:** **M**.
- **Dependencies:** Q1 (if consumed). Foundations landed: Stages
  1b-A/1b-C/1b-D, TM step S1.
- **Kill (charter, pre-registered):** "the one-step conditional
  density cannot be written with the symmetric half-step split —
  the temporal plaquettes shared between layers force a kernel
  whose two half-step factors are not adjoints of one another,
  so no square exists even before Lean cost is counted."

### Q4. TM R2 — operator positivity on all vectors (the half-step square)
- **Source:** `gram-clause-transfer-matrix-scoping-2026-10-24.md`
  §4 (R2); gap (i) of the 1b-D inventory.
- **Gap:** "From R1: the half-step operator V (osSpace → L² of
  the doubled/mid-layer data) with `transferOp = V† ∘L V`, or
  directly 0 ≤ ⟪ψ, Tψ⟫.re for arbitrary ψ, upgrading
  `transferOp_form_nonneg` from positive observables to the
  whole space."
- **Price:** **M**.
- **Dependencies:** Q3 (R1).
- **Kill (charter, pre-registered):** "the positivity proof is
  found to need a factorization of the one-step kernel over
  representation indices of a crossing plaquette — the
  (k, a)/(j, i) obstruction reappearing one level up — rather
  than over the mid-layer configuration."

### Q5. STEM B2 — gauge covariance
- **Source:** `stem-bridge-scoping-2026-10-24.md` §6 (B2);
  statement S3 in its §2.
- **Gap:** the gauge action on connections, the diagonal unitary
  `U_g`, and the conjugation theorem `L_{w,θ^g} = U_g ∘L L_{w,θ}
  ∘L U_g*`, with the spectrum corollary (spectrum and heat trace
  depend only on the gauge class of θ).
- **Price:** **S–M**.
- **Dependencies:** STEM B1 (the magnetic Laplacian) — building
  at audit time.
- **Kill (charter):** "the intertwining `L_{w,θ^g} = U_g L_{w,θ}
  U_g*` fails for the B1 definition — a definition error, caught
  here, fixed in B1's terms or the brick dies."

### Q6. STEM B3 — the heat object
- **Source:** `stem-bridge-scoping-2026-10-24.md` §6 (B3);
  statement S2 in its §2.
- **Gap:** `e^{−t L_{w,θ}}` via `HermitianReduction.heatKernelGen`
  (or the eigenbasis port of `BridgeCompletion.heatOp`):
  semigroup law, the trace identity `Tr e^{−t L_{w,θ}} = ∑ k,
  exp (−t • λ_k(θ))`, contraction for `t ≥ 0`.
- **Price:** **M**.
- **Dependencies:** STEM B1 (S1 of the charter). Ladder order
  places it after Q5 (B2).
- **Kill (charter):** "a genuine Mathlib gap in the
  complex-spectral path forces a detour larger than the brick —
  then B3 is re-priced in the open; it is never shrunk
  silently."

### Q7. STEM B5 — the zero-field weld
- **Source:** `stem-bridge-scoping-2026-10-24.md` §6 (B5);
  statement S5 in its §2.
- **Gap:** at `θ ≡ 1`, `magLap` is the complex `laplacianOp` /
  `lapLin` of the landed Bridge exhibit, eigenvalues `lapEig`,
  heat content `heatOp` over ℂ, Fiedler value as the zero-field
  gap.
- **Price:** **S**.
- **Dependencies:** Q5 + Q6 (charter S5 needs S1–S3, i.e. bricks
  B1–B3). Does not depend on Q9/Q10 (B4′/B4).
- **Kill (charter):** "a normalization mismatch (a stray factor,
  a sign) that cannot be absorbed by B1's definitions — then
  the weld fails loudly and B1 is revisited; the exhibit is
  never edited to meet the bridge."

### Q8. TM R3 — preparation and powers: the full identification
- **Source:** `gram-clause-transfer-matrix-scoping-2026-10-24.md`
  §4 (R3).
- **Gap:** "Iterate R1 over the positive half's layers: for
  arbitrary strict-half F, a prepared state ψ_F in osSpace and
  an exponent m (the half's depth) with osForm β F F = ⟪ψ_F,
  T^m ψ_F⟫; positivity of powers from `transferOp_isSelfAdjoint`
  + R2 by the even/odd square argument." Contains the 1b-D
  fence's "identification (M–L)", priced at its top.
- **Price:** **L**.
- **Dependencies:** Q3 (R1, iterated); Q4 (R2, for positivity of
  powers); Q1 if consumed.
- **Kill (charter, pre-registered):** "preparation closes for
  slice observables only — temporal links *inside* the positive
  half couple the layers in a way the iteration does not absorb
  — or the exponent/state depends on F through the kernel in a
  form that breaks the quadratic-form reading."

### Q9. STEM B4′ — face-restricted flux-dependence (the pre-named fallback)
- **Source:** `stem-bridge-scoping-2026-10-24.md` §6 (B4′).
- **Gap:** statement S4 restricted to graphs equipped with the
  face data of `BridgeCompletion` §9: the gauge class of θ is
  read from the face holonomies (products of θ around
  `GraphFace` boundaries). Landing B4′ alone leaves the STEM
  bridge at PARTIAL, with B4 named as the remainder.
- **Price:** **S**.
- **Dependencies:** B1–B3 (Q5, Q6 in substance — S4 reads the
  gauge class through S3).
- **Kill:** none separately named; it is itself the fallback
  named in advance for Q10's kill.

### Q10. STEM B4 — flux-dependence in full
- **Source:** `stem-bridge-scoping-2026-10-24.md` §6 (B4);
  statement S4 in its §2.
- **Gap:** "gauge classes of θ are determined by cycle
  holonomies (spanning-tree gauge fixing; the spectrum and heat
  trace factor through the fluxes)." The charter names the
  hidden cost on its face: it "secretly needs graph cycle-space
  machinery the corpus lacks — priced L for exactly that
  reason, and it is the ladder's honest long pole."
- **Price:** **L**.
- **Dependencies:** Q5 (S3 gauge covariance — S4 is read through
  it); Q6 for the heat-trace half of the conclusion.
- **Kill (charter):** "gauge fixing on a general finite graph
  cannot be carried in the corpus's explicit finite form — then
  B4 falls to its pre-named restriction [B4′] and the
  restriction is recorded, not hidden."

### Q11. TM R4 — discharge of Stage 1b-B at general (G, ρ)
- **Source:** `gram-clause-transfer-matrix-scoping-2026-10-24.md`
  §4 (R4).
- **Gap:** "Assemble: `osForm_nonneg` at general (G, ρ) — at
  every real β if R1–R3 are in fact sign-free (D3), else at
  β ≥ 0 with the narrowing named — by R3 + R2, in the corpus's
  exact conclusion shape; flip the Stage 1b-B label."
- **Price:** **S**.
- **Dependencies:** Q8 (R3) + Q4 (R2). Discharges with it: the
  OS re-pin's E2 PARTIAL (`os-repin-2026-10-18.md`: positivity
  at general β conditional on the Gram clause) and
  floor-to-ceiling V3's unwelded remainder.
- **Kill (charter, pre-registered):** "any hypothesis mismatch
  at the application site (hρcont, Even N, 2 ≤ N are
  corpus-standard; a mismatch means an upstream rung silently
  changed the target)."

### Q12. General-β gap at fixed volume — spectral input on `T_β`
- **Source:** `pitch-4-stage-1b-d-2026-10-17.md`, fences, item
  (i).
- **Gap:** "spectral input on `T_β` at fixed β > 0 — classically
  `T_β` is shown compact (continuous-kernel) and the gap is read
  off its spectrum; neither compactness nor a spectral theorem
  for this operator is formalized in this corpus." (Item (ii)
  of the same fence — a gap uniform in volume and coupling —
  is Stage 3c and appears as W1, not here.)
- **Price:** **M–L**.
- **Dependencies:** none formal (the landed 1b-D package is its
  ground). Sequenced after the TM ladder because it lives in
  the same module territory; it is independent of Q3–Q11's
  conclusions.
- **Kill:** none named in source.

### Q13. Stage 1c-0, clause (ii) remainder — the general closed intertwiner form of κ_p
- **Source:** `pitch-4-stage-1c-0-2026-10-18.md` (the stage's
  named PARTIAL).
- **Gap:** what landed is κ_p as "a *finite link-sharing sum* of
  explicit covariance integrals … **plus** the scalar closed
  evaluation κ_p = −1/2 on the circle/fundamental instance."
  What does **not** land: "the fully general closed intertwiner
  form for arbitrary (G, ρ) via the J-tensor / ρ⊗ρ̄
  pair-intertwiner apparatus. That apparatus was cut
  mid-scoping: building it would price above M."
- **Price:** **UNPRICED** (source bounds it only from below:
  above M). Re-price before building.
- **Dependencies:** none (stands on the landed
  `LatticeAnalyticity`).
- **Kill:** none named for the remainder itself (the gauntlet's
  KILL-1c-α/β governed the landed clauses and were not
  triggered; PARK-1c-γ concerns uniformity — W3 — not this
  item).

**QUEUE total:** 13 items — S ×5 (Q1, Q2, Q7, Q9, Q11), S–M ×1
(Q5), M ×3 (Q3, Q4, Q6), M–L ×1 (Q12), L ×2 (Q8, Q10),
UNPRICED ×1 (Q13).

---

## §2 WALL — research-scale / frontier (listed for honesty, NOT queued)

### W1. Stage 3c — uniform estimates
- **Sources:** `pitch-4-continuum-scoping-DRAFT-2026-10-17.md`
  §6.4/§9; `pitch-4-stage-1b-d-2026-10-17.md` fence (ii);
  `os-repin-2026-10-18.md` (E4 row); floor-to-ceiling blueprint
  V4 ("MISSING FLIGHT").
- **Gap, in the sources' terms:** "Proving the limits exist with
  OS control" via "uniformity along the tuning curve (Stage
  3c)"; a gap "uniform in volume and coupling along a continuum
  trajectory"; general-β decay/clustering (uniform-in-volume gap
  m(β) > 0, Osterwalder–Seiler form). In the floor-to-ceiling
  blueprint's words: "A spacing-uniform gap/observable bound
  that survives a → 0 … without it no vertical member reaches
  Beam A."
- **Price:** research-scale, open (all sources agree; the
  continuum scoping notes the in-print analogue is Balaban-scale
  and the mass gap is absent from it).

### W2. Stage 4 — the continuum theory
- **Sources:** `pitch-4-continuum-scoping-DRAFT-2026-10-17.md`
  §6.5; `bridge-landing-pad-2026-10-20.md` §5 Span (c);
  floor-to-ceiling V5; `os-repin-2026-10-18.md` §4.
- **Gap:** a measure on continuum gauge fields; local algebras
  (Type III₁ in the continuum); OS reconstruction outputs in
  the continuum (schema only in the re-pin; lattice shadows all
  stand); real Poincaré for the interacting continuum theory.
- **Price:** FRONTIER (the Landing Pad's Span (c) is
  "quarantined: … No span priced; the pad records the
  quarantine, it does not lift it").

### W3. Stage 1c-proper — uniformity / clustering body
- **Sources:** `gauntlet-parked-fleet-2026-10-17.md` §2;
  `pitch-4-stage-1c-0-2026-10-18.md` (PARK-1c-γ).
- **Gap:** the strong-coupling clustering body whose
  β-analyticity slice landed as Stage 1c-0; uniformity in volume
  is the parked step — "Uniformity is Stage 1c-proper
  (PARK-1c-γ), parked XL — untouched."
- **Price:** **XL** (parked; infrastructure park).

### W4. Route A — full Peter–Weyl in Lean
- **Source:** `gram-clause-scoping-2026-10-23.md`.
- **Gap:** Peter–Weyl orthogonality for general compact groups,
  absent from pinned Mathlib — the machinery the original Gram /
  character-expansion clause (and the OS re-pin's E2 PARTIAL)
  was fenced on before Routes B/C and the TM route bypassed it.
- **Price:** **XL / blocked. "DO NOT COMMISSION"** (the
  scoping's own words; it stays a named shelf item: "if Mathlib
  ever lands Peter–Weyl, Route B's price collapses and the
  record will say so").

### W5. Rung 9 Task 4 remainder — continuum Poincaré on Fock space
- **Sources:** `rung-9-2026-10-15.md` (Task 4 PARTIAL);
  `~/workspace/your_files/rung-9-verdict-reconciliation-2026-10-22.md`.
- **Gap:** Tasks 1–3 stand; Task 4's form of the lift is
  discharged (`gamma_rep`) and lattice translations are
  implemented. The remainder, in the reconciliation's words:
  "continuum Poincaré on Fock space — a priced, research-scale
  item (it needs the continuum/mass-shell representation, which
  is T5 today)."
- **Price:** **UNPRICED** in S/M/L letters (research-scale per
  the reconciliation; "at its standing price," letter not
  stated in the sources swept).

### W6. Stokes drag (Stokes–Einstein Rung 4)
- **Source:** `stokes-einstein-scoping-DRAFT-2026-10-18.md` §5.
- **Gap:** "Deriving η, and with it 6πηr, from an underlying
  microscopic theory."
- **Price:** **FRONTIER** ("Literature territory; no build
  priced").

**WALL total:** 6 items.

---

## §3 HELD — waits on Jeff's word or a charter condition

### H1. Stokes–Einstein Rung 3 — continuum passage
- **Source:** `stokes-einstein-scoping-DRAFT-2026-10-18.md`
  §§5, 7.
- **Gap:** "A scaling limit from the discrete processes toward
  Brownian motion / the diffusion equation."
- **Price:** **L–XL** ("Research-scale analysis; parts likely
  blocked on the pinned Mathlib. Not scheduled.").
- **Hold condition:** the charter's §7 — "no rung scheduled
  beyond Rung 1's price, and Rung 1 itself launches only on
  Jeff's word." Rungs 1–2 landed under Jeff's 2026-10-22
  commission; the Rung 2 dossier records "Rung 3 (continuum
  passage) remains unscheduled, per the charter."

### H2. Winding, Definition B (principal-argument route)
- **Source:** `~/workspace/writings/phase-winding-brick-charter-draft-2026-10-21.md`.
- **Gap:** "Define w from a unit-modulus configuration u : Fin
  (n+1) → ℂ by summing principal-branch increments. Canonical,
  but needs the branch-cut analysis and an exclusion for
  antipodal edges." Definition A (lift-first) landed as the
  `WindingRing` brick; B was the charter's stretch clause.
- **Price:** **M** ("analysis-heavy. NOT in the core scope").
- **Hold condition:** the charter is a draft addressed to Jeff
  ("Commission it (core A only, B as priced stretch), amend it,
  or leave it"); no commission of B is on record.

### H3. Combinations Atlas build specs A–D (exhibits — specced, not commissioned)
- **Source:** `~/workspace/writings/artifact-law-combinations-2026-10-21.md`.
  These are exhibit builds, not gap theorems; they are listed
  because they are named, priced, unbuilt work in a charter —
  each still requires Jeff's word at ship time per the atlas's
  own gates.
- **Spec A** — "Counts Survive, Lengths Don't" (Tesseract ×
  Hero/Villain + Shadow doctrine). **Price: M.**
- **Spec B** — "The Driver at Rest and at Work" (Modular Flow
  Lab × the Teetertotter). **Price: M.**
- **Spec C** — "The Line and the Trail" (The Walker × Shadow
  doctrine + XYZ color law). **Price: S.**
- **Spec D** — "The Toll at the Stone" (Hydrodynamics river ×
  the Transformer Law). **Price: M.**
- Reserve shelf (same source, promotion on Jeff's word without
  re-audit): Vacuum portrait × To Each Its Need; Shadow-gradient
  × Kubrick Law; Bridge Landing Pad × Gurd Law — UNPRICED as
  specs.

### H4. Breakdown-ledger landing entries B1–B12 (scoped, uncommissioned)
- **Source:** `breakdown-ledger-scoping-DRAFT-2026-10-20.md` —
  Bridge Span (b)'s scoping pass (the Landing Pad priced the
  scoping at S; the pass was delivered 2026-10-20; "landings
  individually priced after"). Each entry below is a scoped
  landing on the QM↔ACMD pad, priced by the scoping, none
  commissioned. Expected verdicts are the scoping's
  *expectations*, not verdicts.
- **B1** Measurement formalism: POVMs and state update — **M**
  (probability layer alone: S).
- **B2** Angular momentum and spin algebra — **M** (explicit
  spins S; general j is the cost driver).
- **B3** Quantum harmonic oscillator — **M** (shadow; true form
  XL, not purchasable on the pad).
- **B4** Hydrogen atom / Coulomb problem — **XL** (outside the
  pad; wall-flavored, held here because its source is this
  scoping).
- **B5** Time-independent perturbation theory — **M**
  (coefficient level; convergence package L, separate entry if
  commissioned).
- **B6** Scattering theory (S-matrix) — **XL** (outside the
  pad).
- **B7** Identical particles and (anti)symmetrization — **S–M**.
- **B8** Path integrals — **M** (shadow; true object XL).
- **B9** WKB / semiclassical limit — **XL** (outside the pad).
- **B10** Open-system dynamics (Lindblad) — **M** (layers
  (a)+(b); GKSL converse + modular package: L).
- **B11** Entanglement criteria and Bell inequalities — **M**
  (CHSH + PPT necessity; 2×2 sufficiency: L).
- **B12** Quantum information primitives: gates and no-cloning —
  **S** (universality package, if ever commissioned: M–L,
  separate).

### H5. STEM Seat 2 — the Pitch-4 lattice joining statement
- **Source:** `stem-bridge-scoping-2026-10-24.md` §§1, 6.
- **Gap:** a heat kernel of a link-carrying operator in the
  Pitch-4 lattice corpus (whose dynamical operator is the 1b-D
  transfer operator, not a covariant Laplacian). "Seat 2 is a
  different bridge; it is recorded here so nobody conflates it
  with Seat 1, and it is **not** priced in this charter."
- **Price:** **UNPRICED** (charter).
- **Hold condition:** "Not in the ladder: Seat 2 … requires its
  own charter and Jeff's word."

**HELD total:** 5 groups, 19 priced lines (H1 ×1, H2 ×1,
H3 ×4, H4 ×12, H5 ×1).

---

## §4 QUARANTINED — the seven sorry-backed declarations

The corpus's entire code-sorry census is these seven (verified
2026-10-24; dependency audit 2026-10-21: the sorryAx footprint
is exactly these, zero transitive contamination). Each is a
**formalized question, not an answer** (BlockedQuestions'
ledger rule). None is queued: per item, the record either makes
the intended content research-scale/physical rather than formal,
argues the statement is obstructed as stated, or names a route
that was explicitly left out of scope. Prices: **UNPRICED** in
every case — no source prices a discharge.

### X1. `blockedQ1_physicalClock` (BlockedQuestions.lean, T5)
∃ β, lam, obs, c ≠ 0 and an assignment f with
`modularFreqDiff β lam (f m).1 (f m).2 = c * obs m` — a thermal
triple whose modular frequency differences reproduce an
observed clock spectrum. **Why quarantined:** the record's
promotion condition demands `obs` be *a measured clock
spectrum*; the formal statement quantifies over `obs` itself,
so a formal witness would not discharge the named question
(the problem of time). Discharge route in the record: none
formal.

### X2. `blockedQ2_continuumLimit` (BlockedQuestions.lean, T5)
∃ D : ContinuumLimitData, D.recoversLocality — a controlled
continuum limit of finite thermal triples. **Why quarantined:**
the intended content *is* the continuum limit (W1/W2
territory), and `recoversLocality` is an uninterpreted Prop
field of the data structure; a formal discharge would not
discharge the question (emergence of the continuum).

### X3. `blockedQ3_threeGenerations` (BlockedQuestions.lean, T5)
∃ lam, HasThreefoldHierarchy lam — a Dirac spectrum with
threefold hierarchy. **Why quarantined:** the record's promote
condition is "exhibit the spectrum (ideally from a tripled
finite-triple construction)" and its kill is "irrelevance —
the framework may not be the right address for this question";
the bare existence statement over arbitrary spectra is weaker
than the named question (three generations *of the
framework*). No construction is on record.

### X4. `blockedQ4_closedFormGap` (BlockedQuestions.lean, T5)
∃ e : ClosedForm nYuk, ∀ y, e.eval y = spectrumGap (diracSpec
y) — a closed form for the spectral gap in the Yukawa inputs.
**Why quarantined:** the module's own 2026-10-05 amendment
argues the statement is obstructed as stated — the
min-selection Δ(Y) is generically non-analytic (structural
obstruction, "does not depend on any unproved lemma"), with a
conditional Galois barrier on top. The amendment's unblock
paths (A: conditional spectral bounds; B: sectoral
factorization — pursued as new entries, cf. `CharpolyFactor`,
2026-10-22; C: T4 numerical gap maps) are *new, weaker
entries — never "the" closed form*.

### X5. `blockedQ5_physicalDevice` (BlockedQuestions.lean, T5)
∃ L : LabRealization, 0 < L.workOutput ∧ L.bathsAreThermal ∧
L.cycleCloses — a laboratory realization extracting positive
work from a finite-triple thermal cycle. **Why quarantined:**
a laboratory realization is physical data (a proposal with
Hamiltonian, baths, and readout, per the record's promote
condition), not a formal witness; the schematic structure's
Prop fields make the formal statement weaker than the
question.

### X6. `kms_identity_diagonal` (ModularTime.lean, T3)
The diagonal KMS identity: for positive weights w summing to
1, `trace (diagState w * A * (exp (−diagModularK w) * B *
exp (diagModularK w))) = trace (diagState w * B * A)`.
**Why quarantined — with the one named exception in kind:**
this is a concrete finite matrix identity, and its general
form STANDS at T1 (`KMSBridge.gibbs_kms`,
`gibbs_kms_weight`). The KMSBridge intake note names the
discharge route exactly — "`kms_identity_diagonal` … is the
diagonal specialization of `gibbs_kms_weight` (β = 1, K
diagonal); discharging it through this route would need the
exp-of-diagonal spectral lemma, so it is left untouched per
intake scope." It stays in this section because it is one of
the census's seven and no discharge is commissioned or priced
in the record — but it is the only one of the seven with a
named, finite discharge route, and it is flagged here as the
sole candidate for promotion out of quarantine on Jeff's word.

### X7. `xyz_tripotents_exist` (XYZTripotents.lean, T5)
∃ X Y Z : Matrix I32 I32 ℂ, all tripotents, whose generated
TRO contains all twelve `smGen g`. **Why quarantined:** three
waves of machine-checked no-gos in the same module refute the
diagonal class (`sector_triple_fails`), the single-sector
class (`triple_genH_cannot_reach_genM`), and the R4/R5
families (`no_UJ_diagonal_pair_reach`,
`no_gaussInt_triple_reaches_genM7`); the remaining search
space — tripotents whose ternary closure genuinely mixes
sectors, e.g. involving UJ itself — has no witness on record.
Not dischargeable on the current record.

**Corpus note (not a sorry):** `CCMAlgebraClassification.ccm_classification`
is proved conditional on the T4 axiom `AdmitsClassifyingDirac_unpack`
and on the 46→10 chain its own header flags **UNSOUND AS STATED**
(2026-09-30); it stands unmodified under the relabeling rule.
The corrected classification stands as new entries
(`CFKernel22.cf_kernel_classification_46_22`, unconditional).
The axiom's own doc names the remaining analytic work — "the
reconstruction implication (SM-type Dirac ⇒ algebra is
smFactors)" — toward a corrected CCM capstone; no price for
that capstone appears in the sources swept, so it is recorded
here as **UNPRICED** and unqueued, not itemized as a gap
theorem.

**QUARANTINED total:** 7 declarations (+1 flagged-axiom note).

---

## §5 Count summary

| Class | Count | Contents |
|---|---|---|
| QUEUE | 13 | TM ladder remainder (R1, R2, R3, R4) + 2 transfer-package smalls (posToSlice, pointwise positivity) + STEM ladder remainder (B2, B3, B5, B4′, B4) + 1b-D spectral input + 1c-0 intertwiner remainder |
| WALL | 6 | Stage 3c; Stage 4; 1c-proper (XL park); Route A Peter–Weyl (XL, do-not-commission); Rung 9 Task 4 remainder; SE Rung 4 (FRONTIER) |
| HELD | 5 groups / 19 lines | SE Rung 3; Winding B; Atlas specs A–D; breakdown entries B1–B12; STEM Seat 2 |
| QUARANTINED | 7 | blockedQ1–Q5; kms_identity_diagonal; xyz_tripotents_exist |

The watertight core — everything buildable tonight from landed
foundations, in dependency order — is §1: thirteen items, five
of them S-sized. The walls stay drawn dashed and priced (W6 of
the welding code); the held items wait on named words, not on
vagueness; the quarantined seven stay receipts, not results.

— BONES, for the record. Tiers per the Concrete; kills and
parks at full rank; **NO CLAIM.**

---

## Status note — 2026-10-24 (TM ladder, after this queue shipped)

- **Q4 (TM R2) — KILLED by its pre-registered criterion.**
  Design-phase obstruction, no Lean built: positivity of the
  transfer operator on arbitrary vectors reduces (via landed
  S1 + R1) to positive-definiteness of the seam kernel, whose
  only Gram factorization is the tensor-power/word series
  over representation indices of a crossing plaquette —
  charter kill clause 1 + constraint D5. The kernel is also
  not positive-definite for β < 0 (numerical certificate), so
  any revival is narrowed to β ≥ 0. Dossier:
  `whitepaper/gram-transfer-r2-obstruction-2026-10-24.md`.
  The transfer route as chartered terminates at R2.
- **Q8 (TM R3) — SPLIT.** The *identification* half
  (`osForm β F F = ⟪ψ_F, T^m ψ_F⟫`, positivity-free) remains
  **QUEUE**, buildable as scoped. The positivity-dependent
  half (positivity of odd transfer powers) is **BLOCKED** —
  it is R2 on the range of T^k; even powers remain free
  (`T^{2k} = (T^k)†T^k`).
- **Q11 (TM R4) — BLOCKED.** The discharge is equivalent to
  R2 at depth one via S1, so it cannot be assembled from
  R1 + S1 + even powers. Stage 1b-B stays T1 for U(1),
  general (G, ρ) OPEN.
- **Named remainder (not an item; Jeff's call):** the word
  expansion of the crossing weight as a factored family for
  the landed `osForm_nonneg_of_gram_integrated` — a third
  family, Gram-route territory; see the R2 dossier §9.
