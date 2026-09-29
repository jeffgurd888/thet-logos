# Open Hypotheses Catalog — thet-logos

*Unproven and unkilled. Separate from everything machine-checked.*

This document is the project's idea inventory. Nothing in §2 is proved. Nothing in §2 is killed. Each entry states what would prove it and what would kill it. When an entry is proved, it leaves this catalog and enters the proof record. When an entry is killed or vetoed, it leaves this catalog and enters §3 — permanently.

**The boundary this catalog maintains:** machine-checked constructive proofs on one side, unproven physical or existence hypotheses on the other. A hypothesis never migrates across that boundary by redefinition, relabeling, or ledger edits. Only by proof.

**Status words used here:**
- **OPEN** — no proof, no refutation, attackable.
- **PARTIAL** — proved in a restricted case; the general statement is open.
- **QUARANTINED** — set aside by decision; not to be relitigated without new evidence.
- **SPEC'D** — fully specified with falsifiable targets, not yet attempted.

**Tiers:** T2 = definition/imposed structure · T3 = machine-checked · T4 = numerical evidence · T5 = hypothesis/ontology.

---

## §2. Open hypotheses

### H1 — The Tet/thet → Standard Model derivation
**Status:** OPEN · **Tier:** T5
**Statement:** The primitive thet/TRO structure *forces* the finite Standard Model geometry (algebra, Hilbert space, Dirac operator, real structure) rather than merely accommodating it as a separately constructed target.
**What would prove it:** A derivation — definitions plus theorems — starting from thet/TRO primitives and arriving at the finite SM triple with no SM-specific choices smuggled in.
**What would kill it:** A proof that thet/TRO primitives admit a different, equally natural finite geometry with equal claim to physicality (non-uniqueness of the derivation target).
**Note:** This is the central gap of the program (review OP1). Everything else in this catalog is downstream of it or independent of it.

### H2 — XYZ tripotent existence (full)
**Status:** PARTIAL · **Tier:** T5 (statement) / T3 (partial results)
**Statement:** `xyz_tripotents_exist` — there exist tripotents X, Y, Z whose generated TRO contains all 12 `smGen` generators. (lean/ThetLogos/XYZTripotents.lean)
**What is proved:** ~90 theorems; kill rubric R1–R5; partial reachability — {genH 0, UJ, genM 0} reaches smGen 1–4, {genC, UJ, gammaF} reaches smGen 0. Banked in whitepaper/xyz-campaign-results-2026-09-28.md.
**What would prove it:** An explicit triple reaching all 12 generators.
**What would kill it:** A proved invariant showing no tripotent triple can reach the full set (e.g., extending R5 to a complete obstruction).
**Note:** Parked by decision 2026-09-28. Not dead — parked.

### H3 — Weakened XYZ existence (honest variant)
**Status:** OPEN · **Tier:** T5
**Statement:** A *separately labeled* existence claim with a reduced target set (e.g., the 11 tripotent generators, or the reached subset {0,…,4}).
**What would prove it:** An explicit triple reaching the stated reduced set — a real proof, not a relabeling of the partial results.
**What would kill it:** Same as H2's kill condition, restricted to the reduced set.
**Note:** This is the legitimate form of the instinct behind the vetoed protocol item V1. It is a *new* statement, not a closure of H2. H2's sorry is untouched by anything proved about H3.

### H4 — Exact pivot certificate (rational/ℚ(√3))
**Status:** OPEN · **Tier:** T4 → T3 if proved
**Statement:** Replace the T4 `exotic_decomposition` axiom in the 46→10 classification with an exact certificate: explicit matrices M_Q, N_Q with M_Q·N_Q = 1, checked in Lean.
**Constraint discovered 2026-09-28:** the data lives in ℚ(√3), not ℚ (Gell-Mann 1/√3 entries) — encodable as a 72×72 ℚ check via the a+b√3 ↦ [[a,3b],[b,a]] block embedding. The stale `attack4_corrected` pivot files on disk are NOT an exact inverse pair (verified M@N ≠ I) and must not be used.
**What would prove it:** A bounded Python probe producing an exact ℚ(√3)-basis of the exotic 36-space with exact pivot+inverse, semantics pinned to `exoticPivotTable`, then the Lean instantiation.
**What would kill it:** A proof that no exact ℚ(√3)-basis with the required pivot property exists (unlikely) — or the probe failing within its bounded budget, which demotes this to QUARANTINED, not killed.

### H5 — General algebra uniqueness
**Status:** OPEN · **Tier:** T5
**Statement:** A sufficiently well-defined candidate class of finite algebras exists, and the stated primitive constraints select ℂ⊕ℍ⊕M₃(ℂ) (the SM algebra) from the *entire* class — not just from three candidates.
**What would prove it:** The candidate class definition plus the selection proof.
**What would kill it:** Exhibition of a second algebra in the class satisfying all the same primitive constraints.
**Note:** The current N₀ result is uniqueness among three candidates only. The earlier general proposal was killed (see V4); this is its honest successor, with the candidate class made explicit.

### H6 — Gauge-field recovery from one-forms
**Status:** OPEN · **Tier:** T5 (machinery T3)
**Statement:** The inner-fluctuation one-form space decomposes, as representations, into exactly the SM gauge content (photon, W, Z, gluons) — machine-checked, not the textbook story retold.
**What would prove it:** A T4 numerical probe first computing the one-form space's dimension and irrep decomposition and matching SM gauge content, then the Lean formalization of exactly what the probe showed.
**What would kill it:** The probe's decomposition not matching SM gauge content.
**Note:** The fluctuation *mechanism* is proved (T3); its *physical identification* is the open part. The theorem statement must say exactly what's proved — no smuggling.

### H7 — Spectral action, built not assumed
**Status:** OPEN · **Tier:** T5 (scaffold exists)
**Statement:** The six quarantined axioms in SpectralAction.lean (Lichnerowicz, heat-kernel expansion, Seeley–DeWitt coefficients, spectral-action expansion) become actual theorems; the statements whose formal content is currently `True` gain content.
**What would prove it:** Each axiom replaced by a proof, one at a time. Finite heat-trace coefficients Tr(D_F^{2k}) as exact Yukawa polynomials are the concrete first step (computable, T3-able, genuinely new Link 8 content).
**What would kill it:** A proved obstruction to the heat-kernel expansion in the finite setting (would reframe, not end, the program).
**Note:** Arguably the largest mathematical gap after H1.

### H8 — Gravity from the finite structure
**Status:** OPEN · **Tier:** T5
**Statement:** Einstein–Hilbert–type gravitational content derived from the finite triple via the spectral action, rather than asserted downstream of it.
**What would prove it:** H7 proved, then the gravitational terms extracted machine-checked.
**What would kill it:** H7 killed, or the extracted terms not matching GR's form.
**Note:** Strictly downstream of H7. No independent attack before H7 moves.

### H9 — Physical clock from modular flow
**Status:** OPEN · **Tier:** T5
**Statement:** A physical clock — a concrete time observable with the right properties — constructed from modular flow, going beyond the maximal-ignorance boundary condition.
**What would prove it:** The clock construction plus its verified properties.
**What would kill it:** A proof that modular flow in this finite setting cannot yield a clock with the required properties.
**Note:** The ThermalKMS.lean `ModularData` abstraction is the staging ground; the finite Gibbs-state flow formalization is contained textbook work that feeds this.

### H10 — Controlled continuum limit
**Status:** OPEN · **Tier:** T5
**Statement:** A controlled passage from the finite spectral triple toward the continuum regime — one of the five blocked questions.
**What would prove it:** A precise limit statement with its proof (or a no-go theorem with its proof — see below).
**What would kill it:** A proved no-go: no such controlled passage exists under stated conditions. (A kill here is a result, not a failure — it would reframe the program as intrinsically finite.)

### H11 — Three generations derived, not imposed
**Status:** PARTIAL · **Tier:** T3 (inheritance) / T5 (derivation)
**Statement:** The observed three-generation structure derived from primitives, rather than imposed as D₃ = D₁ ⊗ I₃.
**What is proved:** The inheritance theorems — the triplicated triple inherits self-adjointness, grading-oddness, J-compatibility, order-zero, order-one (ThreeGen.lean, 2026-09-28). Imposed triplication is consistent; it is not derived.
**What would prove it:** A derivation of "three" from thet/TRO primitives.
**What would kill it:** A proof that the primitives are generation-blind (forcing triplication to remain forever imposed — an honest T2, not a failure).

### H12 — Closed-form spectral gap
**Status:** OPEN · **Tier:** T5 (positivity T3)
**Statement:** A closed-form physical derivation of the finite spectral gap — not just the T3 positivity result.
**What would prove it:** The closed form, machine-checked.
**What would kill it:** A proof that no closed form exists in the stated terms.

### H13 — Full Majorana block (prove or rename)
**Status:** PROVED 2026-09-28 · **Tier:** T3 logic on T4 foundation
**Statement:** For order-one D with [D,C_F]=0, the 8×8 E-block (rows 24–31, cols 8–15) is exactly ℂ·(single-entry form) — extracted from the 46→10 machinery.
**Proof record:** `ThetLogos.majorana_Eblock_rigidity` (InnerFluctuations.lean): `IsMajoranaSubspace (eBlockOf D) (majoranaBlock 1)` — i.e., ∃ c, eBlockOf D = c • majoranaBlock 1. Via `cf_kernel_classification_46_10` (D = smDirac …) + `smDirac_E_block` + `majoranaBlock_eq_smul_one`. Zero sorrys, zero new axioms; depends on the pre-existing T4 `exotic_decomposition`/`exoticBasisAux` axioms (unchanged).
**Note:** Prove path succeeded — no rename needed. OP12 closes.

### H14 — Tripotent status of genM 1–6
**Status:** OPEN (conjectured) · **Tier:** T5
**Statement:** Each of genM 1–6 is a tripotent, via the uniform `tripotent_of_hermitian_sq_proj` criterion.
**What would prove it:** Six applications of the lemma.
**What would kill it:** Any one of them failing the criterion's hypotheses — which would itself be informative (a new obstruction shape).
**Note:** The concrete next angle left by the banked XYZ campaign.

### H15 — A non-ℤ[i] tripotent leg reaching smGen 11
**Status:** OPEN · **Tier:** T5
**Statement:** There exists a tripotent outside the Gaussian-integer world whose generated TRO reaches smGen 11 (= genM 7, entry 1/√3) — the sharp boundary left by rubric rule R5.
**What would prove it:** Exhibition of such a tripotent plus the reachability proof.
**What would kill it:** A proved invariant that no tripotent's generated TRO reaches genM 7 — which would promote R5 from a family-kill to a complete obstruction and kill H2 outright.
**Note:** genM 7 itself is provably NOT a tripotent (`not_tripotent_genM7`) — the leg must come from elsewhere.

### H16 — Engine #12: KS-DFT on the finite Hubbard lattice
**Status:** SPEC'D · **Tier:** T4 (if built)
**Statement:** Kohn-Sham DFT on a finite 1D Hubbard lattice, per whitepaper/engine12-dft-spec.md, with kill criteria K1–K4 and a 2-day time box.
**What would prove it:** The prototype hitting targets T1–T4 without tripping K1–K4.
**What would kill it:** Any of K1–K4 tripping — by design; the spec wants the kill if the kill is true.
**Note:** Deferred by Jeff's 2026-09-27 decision in favor of the Lean proof sequence. Reviving it is his un-deferral. Payoff is methods/revenue-story, not physics-chain movement. Honest chain: methodological bridge from Engine #11, not data-flow.

### H17 — N₀ nullity counts 18/6, machine-checked
**Status:** OPEN · **Tier:** T5 (counts claimed, not checked)
**Statement:** The 18- and 6-nullity counts for the two non-SM candidate algebras, machine-checked like the SM's 10.
**What would prove it:** Full candidate-representation triple scaffolding for both algebras plus the counts.
**What would kill it:** Cost/benefit — the scaffolding is large and even the SM's 10 is T4 census. Currently assessed NO-GO on cost/benefit; listed here so the assessment is visible, not hidden.
**Note:** The opaque-axiom design was deliberate. Revisit only if the scaffolding gets built for other reasons.

### H18 — Physical meaning of the 36 extra directions
**Status:** OPEN · **Tier:** T4 (classified) / T5 (interpreted)
**Statement:** The 36 exotic directions eliminated by the 46→10 classification have a physical interpretation (or a proved absence of one).
**What would prove it:** A derived interpretation, or a theorem that they carry no independent physical content under stated conditions.
**What would kill it:** N/A — this is interpretive; it resolves by construction, not by refutation.

---

## §3. Vetoed and killed — permanently logged, do not relitigate

*Entries here are closed. Reopening one requires new evidence or a new argument, stated explicitly — never silent relitigation.*

### V1 — Discharging the XYZ sorry by "universal TRO quotient" — VETOED 2026-09-28
**The proposal:** Close whitepaper/xyz-campaign-results-2026-09-28.md by "quotienting out non-tripotent scalar targets in the reachability ledger, discharging the final sorry by establishing that smGen 11 lies outside the universal TRO quotient."
**Why vetoed:** (a) No "universal TRO quotient" exists in the codebase or the mathematics — the key phrase denoted nothing. (b) Editing a results document cannot discharge a Lean sorry. (c) The weakened 11-target statement was itself unproved — no triple reaches 11 generators. (d) Redefining a goal to exclude the hard case and calling it closed is tier-blurring: it would move an unproven existence hypothesis across the boundary by relabeling rather than by proof.
**The boundary it protects:** machine-checked constructive proofs vs. unproven physical/existence hypotheses. This veto is the standing precedent for that boundary.
**Legitimate successor:** H3 — a separately labeled, honestly weaker existence statement, proved by actual proof if it can be.

### V2 — Yukawa family invariance — KILLED
The claim that inner fluctuations preserve Yukawa-family structure is mathematically false. Retired; order-one preservation is the complete theorem. (Proved dead 2026-09-28.)

### V3 — K2 mass-ratio program — PERMANENTLY QUARANTINED
Quarantined by decision, not to be relitigated. Listed so its absence from §2 is visibly deliberate.

### V4 — Original general algebra-uniqueness proposal — KILLED
Killed; succeeded by the honest H5 with an explicit candidate class.

### V5 — Chromatic/RGB as new mathematics — ADJUDICATED
The RGB chromatic triad is T5 organizing language, not mathematical strengthening (rename to X/Y/Z and everything provable survives). Möbius formalization has no concrete statement. Not a hypothesis — a settled adjudication.

### V6 — Withdrawn audit claim: IsTRO assoc2 — MACHINE-VERIFIED TRUE
**What happened:** The 2026-09-28 audit claimed the `IsTRO` class's second associativity field ([[a b c] d e] = [a b [c d e]]) was false for noncommutative matrices, with a hand-computed counterexample (a=b=d=I, c=E₁₁, e=E₁₂ → E₁₂≠E₂₁). The counterexample was miscalculated: it wrongly conjugated the third argument of the ternary product. Since ⟨a,b,c⟩ = a·bᴴ·c (third argument unconjugated), both sides reduce to a·bᴴ·c·dᴴ·e by `Matrix.mul_assoc` alone.
**The correction:** proved in Lean as `ThetLogos.ternaryMat_assoc2` (TRO.lean; proof: `simp only [ternaryMat, Matrix.mul_assoc]`), zero sorrys, standard axioms only. The `IsTRO` class stands exactly as written — no repair was made or needed — and is now instantiated for matrices (`ThetLogos.Matrix.isTRO`, ternary := ternaryMat).
**Lesson logged:** audit arithmetic gets machine-checked before it becomes a "defect found" entry. This entry stays visible as the retraction record.

### V7 — Universal tripotent spectrum (general tripotents) — FALSE
The claim "every tripotent has spectrum ⊆ {-1,0,1}" is refuted by X = i·I (tripotent: XXᴴX = X; spectrum {i}). True only with the self-adjoint hypothesis (`tripotent_selfadjoint_spectrum`: Xᴴ = X ∧ tripotent ⇒ spectrum ⊆ {-1,0,1}, since then X³ = X). It also could not have "replaced the kill proofs," which concern non-tripotents.

---

## §4. Ledger conventions

- A hypothesis enters §2 with a statement, a status, a tier, a proof condition, and a kill condition. Vague entries are returned for precision.
- A hypothesis leaves §2 by **proof** (→ the proof record, with its Lean theorem names) or by **kill/veto** (→ §3, with the reason and date).
- §3 entries are permanent. Reopening requires new evidence, stated in the open.
- **Relabeling is allowed** (2026-09-28, Jeff's decision): a killed or vetoed claim may be restated in a weaker, precise form — but the restatement is a *new* entry with its own statement, status, and proof/kill conditions. The original verdict stands untouched, and the restatement crosses the boundary only by proof. Examples: the dead general spectrum claim lives on honestly as `tripotent_selfadjoint_spectrum` (self-adjoint hypothesis added, proved); the vetoed item-3 instinct lives on honestly as H3 (weakened XYZ existence, still open). What relabeling never does: close the original claim, or move an unproved statement across the boundary by renaming it.
- The boundary — proofs vs. hypotheses — is crossed only by proof. This catalog exists so that crossing is always visible.
