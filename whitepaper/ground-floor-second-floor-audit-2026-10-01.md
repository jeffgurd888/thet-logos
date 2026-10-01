# Ground Floor / Second Floor — Formal Audit

**Date:** 2026-10-01
**Status:** Corrected audit document (Tier T4 status record, not a theorem).
**Ledger rule:** machine-checked vs. literature vs. open vs. dead are labeled per
claim. Corrected from a draft that contained five errors (listed at the end).

---

## 1. The Machine-Checked Ground Floor (Tier-1 Bedrock)

Finite-dimensional core, Lean 4. Full build green: **3323 jobs, zero errors**.
`cf_kernel_classification_46_22` is unconditional (no `h_census`); `#print axioms`
gives only `[propext, Classical.choice, Quot.sound]`. Zero `sorry`s in
`CFKernelRetarget.lean`, `CFKernel22.lean`, `CFKernel22Dim.lean`.
(Qualifier: pre-existing *labeled* sorrys remain in `XYZTripotents`,
`ModularTime`, `BlockedQuestions` — outside the classification chain. The old
flagged 46→10 chain stands untouched per the relabeling rule.)

- **State space:** H_F = ℂ³², four chiral 8-state sectors
  (H_L ⊕ H_R ⊕ H_L^c ⊕ H_R^c; index map documented in `Scaffold32.lean`).
- **Coordinate algebra:** A_F = ℂ ⊕ ℍ ⊕ M₃(ℂ) via the asymmetric Option-A
  representation π (mirrors `FiniteSpectralTriple.lean`).
- **Spectral involutions:** real structure J_F (J_F² = I, KO-dimension 6),
  chiral grading γ_F (γ_F² = I, J_F γ_F = −γ_F J_F).
- **Order-zero:** [π(a), π°(b)] = 0 checked over the selected 12-generator
  family (144 pairs), machine-checked (`smGen_order_zero`).
  The Python `dirac_scan` covers 576 pairs (24 real generators) numerically
  (T4) — a separate, non-Lean check.
- **Order-one:** [[D_F, π(a)], π°(b)] = 0 over the physical Dirac ansatz
  (C = E = 0 imposed by the ansatz `DF_oneGen`; order-one forces only the
  2×2 C/E corners in the Option-A embedding — see calibration note in
  `dirac_scan.py`). The 22-direction commutant W_22 is proved: 12
  `OrderOneHolds` + independence + spanning, zero sorrys.
- **Algebra status (honest):** A_F is *not* proved unique. The Attack-1 scan
  admits **6,494** candidate finite real ∗-algebras through order-zero +
  representation existence. Uniqueness of A_F is an open problem, not a result.

## 2. Disambiguation: the two "zero boundaries"

| | Order-one nullspace (W_22) | Dirac kernel (ker D_F) |
|---|---|---|
| Condition | [[D_F, π(a)], π°(b)] = 0 | D_F ψ = 0 |
| Space | 22-dim matrix *parameter* space in End(ℂ³²) | vector subspace of ℂ³² |
| Size of system | 147,456 complex linear equations (144 pairs × 1024 entries) | 32 × 32 eigenproblem |
| Role | locks D_F into the 5 Yukawa/Majorana blocks {Y_ν, Y_e, Y_u, Y_d, Y_R} | zero-eigenvalue (massless) fermion states |

These are different mathematical objects. Conflating them was the draft's
"boundary of zero" muddle; the table above replaces it.

## 3. Electroweak breaking & gauge dynamics (literature, not Ground Floor)

The following are **Chamseddine–Connes literature results**, recorded here as
context. They are *not* thet-logos machine-checked results.

- **Inner fluctuations (established form):** D_A = D_F + A + J_F A J_F⁻¹ with
  A = Σ a_i [D_F, b_i]. (The draft's "D_F + v{D_F, b_F}" anticommutator
  notation is not used here.)
- **Unbroken U(1)_em:** in the NCG SM the photon stays massless because the
  Higgs vacuum is electrically neutral (Q_em = T_3 + Y/2 unbroken). Literature.
- **sin²θ_W = 3/8:** the NCG gauge-coupling unification value from trace
  normalization. Literature.
- **Not done:** no spectral-action computation exists in this campaign yet
  (SA-4). Any "masslessness in the spectral action" claim is parked until then.

## 4. Visual emblem classification (Tier-5 ledger)

Polyhedral constructs are demoted from theorem status. Ledger:

| Polyhedral element (I_h) | Mnemonic role | Ground-floor status |
|---|---|---|
| Faces (F = 32) | total state count | exact identity: dim H_F = 32 |
| 12 + 20 split | pentagons / triangles | mnemonic only: H_F = 8⊕8⊕8⊕8, not 6⊕6+20 |
| Vertices (V = 30) | vertices | mismatch: 30 ≠ 22 = dim W_22 |
| Edges (E = 60) | edges | mismatch: 60 ≠ 147,456 constraint equations |
| Central inversion | reflection | Tier-5 emblem: visual aid for J_F / γ_F inversion and C = E = 0 vanishing |

**Dead:** any claim that 12/20/30/60 correspond to the algebra, W_22, D_F,
or the order-one condition. (Killed 2026-09-30.)

## 5. The Second Floor frontier (open obligations)

1. **Three-generation multiplicity — external tensor extension (rev. 2026-10-01).**
   Family replication belongs in an external tensor extension, not in a
   centralizer extension inside the base triple.

   **Base finite triple (unchanged):**
   T_F = (A_F, H_F, D_F, J_F, γ_F), H_F = ℂ³².
   The order-one nullspace W_22 remains a property of the base representation
   and its order-one constraint; its dimension and interpretation are not
   redefined by family replication.

   **External family extension.** Family space ℂ^N:
   H_F^{(N)} = H_F ⊗ ℂ^N, π_N(a) = π_F(a) ⊗ I_N,
   D_N = Σ_{i,j=1}^N D_{ij} ⊗ E_{ij}.
   The order-one expression factorizes:
   [[D_N, π_N(a)], π_N°(b)] = Σ_{i,j} [[D_{ij}, π_F(a)], π_F°(b)] ⊗ E_{ij},
   so by linear independence of the matrix units E_{ij}, the extended
   order-one condition holds precisely when every D_{ij} satisfies the base
   condition. *Qualification:* identifying each D_{ij} directly with W_22
   requires W_22 to be defined as the complete linear solution space of the
   base constraint; self-adjointness, reality, grading, and finite-triple
   conventions must be imposed separately. Schematically (pre-constraints):
   W_22^{(N)} = W_22 ⊗ M_N(ℂ).

   **Flavor mixing.** For N = 3, flavor parameters reside in family-indexed
   Yukawa blocks Y_ν, Y_e, Y_u, Y_d, Y_R. CKM/PMNS mixing arises from relative
   diagonalization of the quark/lepton mass matrices — not from the gauge
   commutant, and not from merely enlarging W_22. Any proposed Yukawa blocks
   must still be shown to satisfy all finite-triple constraints; inclusion in
   a tensor-product space alone does not establish that.

   **Modular flow.** K = βD_F² + cI is a function of D_F², so it introduces no
   independent family mixing when the family structure starts diagonal and
   the flow preserves it. Pre-existing family off-diagonal terms in D_N are
   reflected by the flow, not derived from it. *Ledger cross-reference:*
   consistent with the H-φflow-1 kill (2026-09-30) — the flow reads structure
   already present in D²; it does not create sector or family structure.

   **Tier ledger for this item.**
   - Tier 1: base finite triple + verified order-one constraints (machine-checked).
   - Exact analytic, T1-pending: the factorization identity (two-line
     computation; not yet Lean-formalized). N = 3 itself is empirical input,
     not derived.
   - Tier 3–5: flavor and modular-flow models — phenomenological; require
     explicit Yukawa matrices, mixing calculations, independent validation.

   **Conclusion.** Family replication is formulated as an external tensor
   extension of the base finite spectral triple. The order-one constraint
   factorizes over family indices, preserving the base algebraic boundary
   blockwise. Flavor mixing is represented through the relative structure of
   admissible family-indexed Yukawa operators, not through the gauge
   commutant. Modular flow is a phenomenological probe; it is not claimed to
   derive three generations or generate flavor mixing from a
   family-degenerate base triple.

   **Auditor's notes (2026-10-01).**
   (a) Factorization verified by hand — correct.
   (b) "W_22 ⊗ M_N(ℂ)" is schematic partly because W_22 is a *real* linear
   space; the complexified form needs W_22 ⊗_ℝ ℂ. Flagged, not fatal.
   (c) The honest boundary is preserved: the NCG SM accommodates the Yukawa
   sector but does not predict it — this revision does not overclaim.

   **Parameter count d(N) = 9N² + N (verified 2026-10-01).**
   Y_u, Y_d, Y_e, Y_ν ∈ M_N(ℂ): N² complex = 2N² real each → 8N².
   Y_R = Y_Rᵀ: N(N+1)/2 complex = N(N+1) real. Total 9N² + N, exact, no
   adjustment factors. N = 1 → 10 (the SM Yukawa directions *inside* W_22;
   the remaining 12 of the 22 are the exotic survivor directions — the count
   covers the Yukawa/Majorana blocks, not the exotics). N = 3 → 84.
   Scope: this is the Yukawa/Majorana parameter space dimension, not the full
   extended real solution space (exotic directions extended are not counted here).

   **Revised tier ledger.**

   | Tier | Claim | Scope | Status |
   |---|---|---|---|
   | 1 | Base finite triple (A_F, H_F, D_F, J_F, γ_F); dim_ℝ W_22 = 22 | order-zero (576 pairs), order-one, involutions | Machine-checked (Lean 4, zero sorrys in classification chain) |
   | 2 | Tensor extension H_F ⊗ ℂ^N; blockwise order-one factorization | exact algebraic extension; W_N ≅ W_22 ⊗ M_N schematic (real/complex care pending) | Pencil-and-paper, **unformalized** — Lean over arbitrary N unexecuted |
   | 3 | Physical generation choice N = 3; 84 real Yukawa parameters | fitted to mass/mixing spectrum | Empirical accommodation (fitted, not predicted) |
   | 4–5 | Continuum product M_4 × F; spectral action; KMS/modular probes | heat-kernel expansion, RG, cosmology | Field-theoretic model program (SA-3/SA-4 quarantined) |

   **Precision boundaries.**
   - "Zero open gaps" / "machine-checked core" apply *exclusively* to the
     single-generation Lean 4 artifact in the repository.
   - Tier 2 is exact analytically but unformalized; the blockwise matrix
     identity holds on paper, parameterizing H_F ⊗ ℂ^N in Lean 4 for
     arbitrary N remains an unexecuted proof target.

   **Three-question reviewer schema (questions supplied 2026-10-01; the
   draft named the schema but did not state them).** Each question isolates
   one logical layer; a "no" at any layer does not touch the others.
   - **Q1 — Base (Tier 1):** Is the finite triple internally consistent
     (order-zero, order-one, real structure, grading), and is the
     22-direction classification proved with no gaps?
   - **Q2 — Extension (Tier 2):** Does the external tensor product preserve
     every base constraint blockwise, and are reality, grading, and
     self-adjointness correctly imposed on the extended operator?
   - **Q3 — Empirical (Tier 3):** Do the 84 real parameters accommodate the
     observed fermion masses, CKM/PMNS mixing, and experimental bounds — and
     which parameters are fitted versus predicted? (Honest answer: all
     fitted; none predicted. The Yukawa sector is accommodated, not derived.)
2. **Spectral action evaluation.** Seeley–DeWitt coefficients on product
   geometries M_4 × F (SA-3/SA-4). Continuum bridge quarantined; no claim made.
3. **Low-energy calibration.** RG flow Λ_GUT → 10² GeV, CKM/PMNS, cosmological
   bounds. Target only.

## 6. Tier-1 surviving exact fact (finite spectral statistics)

H_F = ℂ³², D_F = D_F*, H := D_F², Spec(H) = {λ_i}. The finite Gibbs/modular
flow is generated by H: frequencies are the eigenvalue gaps ω_ij = λ_i − λ_j,
σ_t^β(A) = e^{−iβtH}Ae^{iβtH}. First-order response:
⟨A⟩_{β+δβ} − ⟨A⟩_β = −δβ·Cov_β(H,A) + O(δβ²),
χ_A = −Tr(D_F²A)/32 + Tr(D_F²)Tr(A)/32² at β = 0.
Exact analytic content; ledger status T4-evidenced + pen-and-paper, formal T1
pending Lean formalization. Linearity-scope caution: exact-for-all-β applies
to the generator action ([K_β,X] = β[H,X]) and first-order response only —
full ⟨A⟩_β is nonlinear in β in general.

---

## Corrections applied to the draft (audit trail)

1. Pair count — **correction revoked and re-corrected (2026-10-01):** the
   draft's "144 pairs" was correct for the Lean machine-checked claim
   (`smGen : Fin 12` → `smGen_order_zero`, `smDirac_order_one`). The
   auditor's "144 → 576" correction was wrong: 576 pairs belongs to the
   Python `dirac_scan` (24 real generators, T4 numerical). The draft's
   589,824 (= 576 × 1024) was also wrong: the classification system is
   144 pairs × 1024 entries = **147,456** complex linear equations.
   Lesson: audit the .lean files before "correcting" counts.
2. "A_F uniquely constrained" → **removed**; 6,494 candidates pass order-zero;
   uniqueness is open.
3. §3 relabeled **literature** (Chamseddine–Connes); fluctuation formula
   restored to D + A + JAJ⁻¹; "in the spectral action" claims parked at SA-4.
4. §5 three-generations item now cites the **H-φflow-1 kill (2026-09-30)** and
   the new-entry question it must answer.
5. Build jobs **3323** (not 3,317); sorry-status qualified (zero in the
   classification chain; labeled sorrys persist elsewhere).
