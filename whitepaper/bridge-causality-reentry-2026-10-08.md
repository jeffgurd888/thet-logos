# Causality re-entry — Rung 2 (dossier)

**Date:** 2026-10-08 · **Lead tier: T1** (proved non-carryover) + **sharp T2**
(manifold admission-price axioms) + **T4** (trace-divergence numerics)
**Lean:** `lean/ThetLogos/CausalProduct.lean` (new module, builds green, zero sorrys)
**Numerics:** `scripts/causality_product_trace_lab.py`, `scripts/causality_product_trace_results.md`
**Predecessor:** `whitepaper/bridge-span-5-causality-2026-10-07.md` (Span 5: KILL on the finite triple)

## Question

Span 5 killed the causal cone on the finite triple three ways. The manifold
factor is causality's new entry. Does `causalCone_obstruction`
(TwistedTriple.lean §10) carry over to the almost-commutative product
`C^∞(M) ⊗ A_F`?

**Verdict: STAND — the obstruction does NOT carry over.** The failing
hypothesis is exhibited, T1.

## Which hypothesis fails (exact)

`causalCone_obstruction` has four *stated* hypotheses: `Dᴴ = D`,
`D` non-central on self-adjoints, `IsCausalConeStatic C`,
`IsDynamicallyCompatible D C`. **None of the four fails on the product** —
all four can hold there (self-adjoint `D_prod`, non-central `D_prod`,
static cone of causal functions, `i[D_prod, f]`-PSD).

What fails is the proof's *unstated ambient* hypothesis — the **finite-trace
engine**:

- `trace_comm_eq_zero : Matrix.trace (D*f - f*D) = 0` — finite cyclicity,
  typed over `Matrix n n ℂ` with `[Fintype n]`;
- `posSemidef_trace_eq_zero` — PSD + trace 0 ⟹ zero;
- `dyn_comm_eq_zero` — their composition: `i[D,f]`-PSD ⟹ `[D,f] = 0`.

On the product, `[D_prod, f]` is **not trace-class**: the trace over the
manifold factor `L²(M,S)` diverges (`D_prod` unbounded; `i[D_M, f]` is a
bounded nonzero multiplication-type operator with infinite trace-class norm).
No finite trace exists to force the collapse.

**Exhibited in Lean** (`CausalProduct.lean`):

| # | Entry | Statement | Status |
|---|---|---|---|
| T2 | `IsOpPSD`, `IsProdCausalConeStatic`, `IsProdDynamicallyCompatible`, `IsProdLorentzCompatible`, `ProdCausalLE` | cone axioms on the product | DEF |
| T2 | `HasFiniteTraceCollapse` | the two engine properties as a predicate on `τ : ProdOp → ℂ` | DEF |
| T2 | `prod_nonzero_causal_commutator` | ∃ cone `f`: `i[D_prod,f]` PSD ∧ `[D_prod,f] ≠ 0` (manifold admission price) | AXIOM |
| T2 | `prod_clifford_hermitian` | `η[D_prod,f]` Hermitian for cone `f` (the relation the finite transplant lacked; Span-5 numerics had `‖M+M†‖ ≡ 0`) | AXIOM |
| T2 | `prod_coord_in_cone` | manifold coordinate functions exist in the cone | AXIOM |
| T1 | `trace_collapse_hypothesis_fails` | `¬ ∃ τ, HasFiniteTraceCollapse τ` — no trace-collapse functional exists | PROVED |
| T1 | `product_not_forced_central` | `¬ ∀ a` self-adjoint, `[D_prod,a] = 0` — the finite conclusion falsified | PROVED |

`#print axioms` for both theorems: `[propext, Classical.choice, Quot.sound]`
plus exactly the labeled T2/T5 product axioms — no sorrys, no smuggled
analysis. `trace_collapse_hypothesis_fails` is the precise negation of what
`dyn_comm_eq_zero` needs: on the finite triple, PSD + vanishing trace forced
`[D,f] = 0` (proved); on the product, the admission-price axiom supplies the
counterexample the finite proof rules out.

## T4 support

`scripts/causality_product_trace_lab.py` (deterministic): on S¹ with N-point
spectral discretization, `Tr_N([D_N,f_N]) = 0` **exactly** for every N (the
engine fires per truncation), while the continuum commutator's N-mode
compression M_N satisfies `‖M_N‖₁/N → 2/π ≈ 0.6366` (trace-class norm
diverges linearly), `‖M_N‖_op → 1` (bounded, nonzero — collapse conclusion
false in the limit), `Tr(M_N⁺)/N → 1/π ≈ 0.3183` (PSD mass persists).
Full tables in `scripts/causality_product_trace_results.md`.

## Carried pylons (no Lorentzian claims without them)

Krein structure (Span 3 `swapR`) and reality prescription (Span 4) stand on
the finite factor; the product adds the manifold Krein factor `ηprod` and the
Clifford relation. The J-form (`IsProdLorentzCompatible`, Franco's true (F6))
is now *statable* — which it was not on the finite triple — but its joint
spanning+inequality satisfiability is **not proved here** (PIN).

## Remaining admission price (PIN)

**Global hyperbolicity** (`GloballyHyperbolicM`, T2 axiom): Franco's recovery
theorem (F8) — the algebraic order recovering spacetime causal order — needs
it (hence non-compactness; no compact causal spacetimes). Not discharged;
no recovery theorem claimed.

## Claim verdicts

1. Causal cone axioms on the product — **STAND** (T2 formulated).
2. Obstruction carries over — **KILL the carryover**: the trace-collapse
   hypothesis provably fails (T1 `trace_collapse_hypothesis_fails` + T4).
   Causality re-entry **STANDS** per the rung criterion.
3. Genuine causal order (F8 recovery) — **PIN** on global hyperbolicity.
4. J-form joint satisfiability on the product — **PIN** (statable, unproved).

Per the relabeling rule, the finite causal cone stays killed; the product
causal cone is a NEW entry with the manifold admission price paid in
axioms 1–3 above.
