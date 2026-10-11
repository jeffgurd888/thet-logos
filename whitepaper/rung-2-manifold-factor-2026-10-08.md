# Rung 2: The Manifold Factor — Dossier (2026-10-08)

**Status:** Rung 2 of the repivoted mission (rigorous 4D QFT — "succeed where nobody else has").
Rung 1 (finite triple + Connes–Kreimer) is built. Rung 2 = the almost-commutative product:
the manifold factor the finite triple has been waiting for.

**Verdict: RUNG 2 STANDS.** The product construction carries the twist cleanly (derived, not
assumed). Causality re-enters (the Span-5 obstruction provably does not carry over).
Gauge bosons get their honest origin story (from the product, not the finite algebra alone).

---

## 1. What Rung 2 buys

### 1a. The product triple (T1, machine-checked)

`lean/ThetLogos/ProductTriple.lean` — build green (3117 jobs), **35 new T1 theorems**, zero
sorrys, axioms `[propext, Classical.choice, Quot.sound]` only. Local commit `3493fad`.

- The manifold factor M is **axiomatized** (T2 compact spin manifold: Dirac D_M, grading Γ_M,
  real structure J_M as class data with needed axioms). No continuum construction — that is
  Rung 3.
- Product Dirac: `Dprod² = D_M²⊗1 + 1⊗D_F²` — proved as T1 `Dprod_sq` (this *upgrades* the
  old dead T5 axiom `product_sum_of_squares`; the killed axiom returns as a theorem, per the
  relabeling rule).
- Product KO-signs `⟨-1,1,-1⟩`; KO-dim adds: 4+6≡2 mod 8.
- Inner fluctuations **decompose** (T1): `prod_commutator_decomp`,
  `prod_commutator_pureManifold`, `prod_commutator_pureFinite`.

### 1b. The twist question — derived, not assumed (T1)

The key structural question: does the DLM grading-flip twist extend to the product?
**Derived answer:** the product twist is the **flip** on the doubled product algebra
`(A_M⊗A_F)²` — *not* `ρ_M ⊗ ρ_F`, which does not even typecheck on the product algebra
(a flip acts on pairs; a tensor-twist acts on factors). CM regularity holds
**unconditionally** for the flip (one-line proof, same mechanism as TwistedTriple §7):
`flipProd_involutive`, `flipProd_CM_regular`, `prodFlip_CM_regular`.
Factorization `flip = id⊗flip_F` holds only on common-manifold-factor pairs
(`prodTwist_factorform`); the general form is `prodTwist_general_pair` (rfl — the honest
non-result: no simplification claimed where none exists).

### 1c. Gauge bosons — the honest version (T2/T5 ledger)

The finite algebra alone gives 6 real dimensions (automorphism hunt: Option-A kills M₃(ℂ)
in the representation). The finite fluctuation story is therefore **scalar-type terms only**
— no gauge bosons, no SM claim, and this dossier repeats the caveat rather than laundering it.

What the product buys: the manifold factor promotes gauge *parameters* to gauge *fields*.
Inner fluctuations of C^∞(M) are 1-forms on M — that is where gauge bosons live, in the
standard almost-commutative reading. This is the honest version of the SM claim:
- Finite factor → scalars (T2, from the fluctuation decomposition).
- Manifold factor → gauge fields (T2, from C^∞(M) 1-forms).
- The full SU(3)×SU(2)×U(1) reading still needs the representation question resolved
  (the 6-dim finding is carried explicitly in the module's §5 honest ledger).

### 1d. Causality re-enters (T1 + T4)

`lean/ThetLogos/CausalProduct.lean` + `whitepaper/bridge-causality-reentry-2026-10-08.md`.
Local commit `4674099`. **Verdict: STAND.**

The Span-5 obstruction (`causalCone_obstruction`, finite triple) provably does **not**
carry over. The failing piece is the proof's **unstated ambient hypothesis: the finite-trace
engine** — `trace_comm_eq_zero` (finite cyclicity over `Matrix n n ℂ`) composed with
`posSemidef_trace_eq_zero` (PSD + trace 0 ⟹ zero) as `dyn_comm_eq_zero`. On the product,
`[D_prod, f]` is **not trace-class** (the trace over L²(M,S) diverges), so the collapse
`PSD ⟹ = 0` cannot be invoked. Exhibited as:
- T1 `trace_collapse_hypothesis_fails`: no trace-collapse functional exists on the product.
- T1 `product_not_forced_central`: the finite conclusion is falsified on the product.
- T4: `scripts/causality_product_trace_lab.py` — `Tr_N([D_N,f_N]) = 0` exactly per
  truncation, but `‖M_N‖₁/N → 2/π` (trace norm diverges linearly), `‖M_N‖_op → 1`
  (collapse conclusion false in the limit), `Tr(M_N⁺)/N → 1/π` (PSD mass persists).
  Divergence is purely manifold-side; the finite factor contributes only a constant.

Cone axioms formulated on the product (T2): `IsProdCausalConeStatic`,
`IsProdDynamicallyCompatible`, `IsProdLorentzCompatible` (the J-form is now *statable*
via the Clifford axiom — the finite transplant lacked it; Krein/twist pylons carried over
via `prod_clifford_hermitian`).

**Pinned:** genuine causal order (F8) on `GloballyHyperbolicM` (T2 axiom — the remaining
admission price); J-form joint satisfiability (statable, unproved — no Lorentzian claims
made without the carried Krein structure).

### 1e. Toy lattice scaffold (T4, labeled TOY)

`scripts/rung2_lattice_toy.py` (+ results md/json). Local commit `818f15d`.
Naive lattice Dirac (doublers NOT handled — labeled toy choice) ⊗ the 32-dim finite space.

- **Kernel bookkeeping:** product kernel = 4 × (lattice zero modes) — 16 at L=3, 256 at L=4.
  An exact algebraic consequence of the product form (verified via the machine-checked
  identity `D² = D_lat²⊗I + I⊗D_F²`), not a numerical accident. Random product-kernel
  vectors: resid 1.2e-15, Schmidt rank ≤ 4 across the lattice|finite cut.
- **Toy fluctuations:** U(1) link variables lift ALL naive lattice zeros (kernel 4→0 even
  at amp=0.1 — naive zeros have no protection); the finite toy 1-form preserves the D_F
  4-kernel at all tested strengths (a property of the toy 1-form choice, not a theorem).
- **Explicitly cannot show:** anything about the continuum, the SM, emergent spacetime, or
  physical scales. No index theorem, single tiny volume, no continuum limit, mismatched
  toy units.

---

## 2. Full tier ledger — Rung 2

| Claim | Tier | Status |
|---|---|---|
| Product triple C^∞(M)⊗A_F (M axiomatized) | T2 | STAND (35 T1 thms) |
| Dprod² = D_M²⊗1 + 1⊗D_F² | T1 | PROVED (`Dprod_sq`) |
| DLM flip twist extends to product; CM regular unconditionally | T1 | PROVED (derived, not assumed) |
| `ρ_M ⊗ ρ_F` as product twist | — | KILLED (doesn't typecheck; flip acts on pairs) |
| Inner fluctuation decomposition (finite + manifold) | T1 | PROVED |
| Finite fluctuations → scalar-type only | T2 | STAND (honest ledger) |
| Gauge bosons from C^∞(M) 1-forms | T2 | STAND (standard reading, labeled) |
| Full SM gauge group from finite algebra | — | KILLED (6-dim finding carried) |
| Span-5 obstruction carries to product | — | KILL THE CARRYOVER (T1+T4) |
| Causal cone axioms on product | T2 | STAND (formulated) |
| Genuine causal order (F8) | T5 | PINNED on global hyperbolicity |
| Product KO-signs ⟨-1,1,-1⟩, KO-dim 2 mod 8 | T1 | PROVED |
| Lattice toy: kernel 4 × (lattice zeros) | T4 | STAND (toy, labeled) |
| Twisted first-order condition on product | T5 | PINNED (needs twist preserving opposite algebra) |
| Antilinear J on product | T5 | PINNED (needs conjugate-linear structure) |
| Krein inner product on tensor Hilbert space | T5 | PINNED (Rung 3 continuum work) |

**Pinned T5 (exact obstructions):** `ProdTwistedFirstOrderCond`, `AntilinearJProd`,
`KreinProdPin` — all in ProductTriple.lean with named unblockers.

**Killed and not returning except as new entries:** `ρ_M ⊗ ρ_F` as the product twist;
the old T5 axioms `SpinorHilbert`, `product_sum_of_squares` (the latter returned as
proved T1 `Dprod_sq` — a promotion, not a resurrection).

---

## 3. Road to Rung 3 — admission price

Rung 3 = the continuum: from axiomatized manifold to actual analysis.
- Global hyperbolicity (causality's remaining price).
- The Krein inner product on the tensor Hilbert space (`KreinProdPin`).
- The twisted first-order condition on the product (`ProdTwistedFirstOrderCond`).
- Antilinear real structure on the product (`AntilinearJProd`).
- The continuum limit itself: lattice → manifold (the toy scaffold is explicitly not this).

One pre-existing `sorry` warning in `ModularTime.lean:201` replayed during builds; no new
sorrys introduced by Rung-2 work. All Rung-2 commits are local; nothing pushed public.

**Commits (local):** `3493fad` (ProductTriple.lean) · `4674099` (CausalProduct.lean +
re-entry dossier) · `818f15d` (lattice toy).
