# Rung 3: The Continuum — Verdicts (2026-10-10)

**Status:** Rung 3 of the repivoted mission (rigorous 4D QFT).
Rung 1 (finite triple + Connes–Kreimer) built. Rung 2 (almost-commutative product) STANDS.
Rung 3 = the continuum limit and the pinned items Rung 2 left behind.

**Verdict: RUNG 3 STANDS.** Two of three pinned T5s promoted with obstructions genuinely
removed; the third narrowed to a partial with an exactly-priced remainder. The
continuum-limit scoping stands as priced roadmap with no claimed limit. Cleanup track:
antipode closed (T5→T1), Fock advanced.

---

## 1. Per-item verdicts

### 1a. Antilinear J on the product — PROMOTED (T2 + T1)

The pin's root obstruction was that the T2 axiomatization carried spinor modules as bare
ℂ-modules with no antilinear maps — J was not even statable. Removed by honest
enrichment of `TripleData` (commit `ac1937d`):
- `sesq`: sesquilinear form (antilinear first arg), explicitly NOT assumed
  positive-definite, nondegenerate, or complete.
- `Janti : S →ₛₗ[starRingEnd ℂ] S` with KO axioms `J² = ε`, `JD = ε′DJ`,
  `JΓ = ε″ΓJ` keyed to the existing sign data.
- Product theorems proved T1: `Jprod_sq` (J² = −1, KO-dim 2 mod 8), `Jprod_D`
  (JD = DJ), `Jprod_Γ` (JΓ = −ΓJ), via Mathlib semilinear `TensorProduct.map`.
- What is NOT done: `conjJ`↔`Janti` compatibility not axiomatized (flagged, not
  claimed); no analytic control (boundedness, compact resolvent still out).
- The promotion is axiomatization + proved consequences, not derivation from
  analysis — stated explicitly in the rewritten §7.

### 1b. Krein inner product on the tensor space — PROMOTED (T2 + T1)

Same enrichment: `ηsym` with `η² = 1` and `ηᴴ = η` as the honest algebraic content
(form-self-adjointness `sesq (ηx) y = sesq x (ηy)` — no adjoint operator constructed,
no Hilbert identity claimed). Product theorems T1: `ηprod_sq`, `ηprod_selfadj`.
Signature honesty kept: `η_prod` is an abstract fundamental symmetry; the killed
Lorentzian language stays killed — no spacetime-signature claim is made.

### 1c. Twisted first-order condition — PARTIAL (honest scope)

- **Built (T2/T1):** the opposite representation, in the `conjJ`-shadow of
  `a° = Ja*J⁻¹` (derived, not assumed): `oppProd` for the undoubled product algebra
  (T1 `oppProd_tmul`, `oppProd_anti_tmul` — multiplication reverses), `oppgrandProd`
  for the doubled algebra mirroring the DLM pattern.
- **Discharged T1:** flip-compatibility in its statable form
  (`oppgrandProd (flipProd y) = GprojPlus * oppProd y.2 + GprojMinus * oppProd y.1`);
  the old pin's `opp (flipProd y) = flipProd (opp y)` is ill-typed (retired, not
  laundered). Diagonal reduction proved: `prodTwistedFOC_diag_reduce` (twisted FOC on
  the physical diagonal ⟺ ordinary product FOC).
- **Re-pinned with exact obstruction:** the twisted FOC itself. Two quoted Lean
  failures: (1) no `Star` instance on `Module.End` over the tensor module — the
  textbook `J a* J⁻¹` cannot even be written (the enrichment gives
  form-self-adjointness of η only); (2) `ProdFirstOrderCond` needs factor-level
  order-one (`[[D_M,π_M f], conjJ_M(π_M g)] = 0`), absent from `TripleData` — and
  the finite factor's proved order-one (`OrderOneHolds_smDirac`) is for the concrete
  matrix triple, not the abstract class, so it does not transfer.
- **Priced close:** add factor-level order-one to `TripleData` (class change), or
  accept the algebraic shadow stops here and the true opposite awaits the analytic
  setting.

### 1d. Continuum-limit scoping — STANDS (roadmap, not claimed)

`whitepaper/rung-3-continuum-scoping-2026-10-10.md` (commit `fbcdac7`).
No continuum conclusion anywhere; every option priced:
- Analytic package (formulation only) — most tractable; per-axiom inventory of
  T2 shadows vs genuinely analytic missing pieces.
- Lattice refinement from the Rung-2 toy — priced at the doubler tax + scaling
  limit; buys product-form validation only, never the manifold.
- AF-algebra inductive limit — least tractable (full invention cost); we have ONE
  triple, not a directed system; recommends against replacing the machine-checked
  finite factor.
- Guardrail: the finite factor has no scale parameter and cannot "become"
  continuous — any limit refines the manifold side. "Finite triple converges"
  language killed with reason.
- Cheapest next step: Hilbert-enrichment of `TripleData` starting with the inner
  product (unblocks "bounded," "compact," "Hermitian" as statable words).

---

## 2. Cleanup track

- **antipodeAxiomEval: CLOSED (T5→T1 confirmed).** `antipodeAxiomEval_proved`
  (Renormalization.lean:1446) verified: correct eval statement (no conflation with
  the refuted as-stated version, separately killed by `antipodeAxiom_false`),
  module build green (3119 jobs), zero sorrys, `#print axioms` =
  `[propext, Classical.choice, Quot.sound]`. Commit `983f00e`'s claim checks out.
- **Fock infrastructure: advanced.** Fermionic core (commit `f02e0c2`): 4 new defs
  (`fermionicFock`, `fermionVacuum`, `fermionExp`, `createFerm`), 8 new T1s
  including `createFerm_anticommute` and `pauli_exclusion` (creator squares to
  zero, machine-checked). Still open: mixed CAR, 2-point functions, number
  operators — all blocked on the `fockInnerProduct` Mathlib gap, documented.
  `satisfiesDestruction` untouched (blocked on Jeff's Yukawa call).

---

## 3. Build status

- Full `lake build`: green (3324 jobs). Only pre-existing warnings
  (`ModularTime.lean:201` sorry replay, ThreeGen linter) — no new sorrys.
- T1 counts: ProductTriple 35 → 63 (23 enrichment/Krein/J + 5 opposite-rep/FOC);
  FreeField +8 (fermionic); Renormalization antipode confirmed T1.
- All `#print axioms` on new theorems: `[propext, Classical.choice, Quot.sound]`.

## 4. Tier ledger — Rung 3

| Claim | Tier | Status |
|---|---|---|
| Antilinear J_prod (J²=−1, JD=DJ, JΓ=−ΓJ) | T2+T1 | PROMOTED (axiomatized; consequences proved) |
| Krein η_prod (η²=1, form-self-adjoint) | T2+T1 | PROMOTED (axiomatized; consequences proved) |
| Opposite rep oppProd/oppgrandProd + flip-compat | T2+T1 | PROMOTED (shadow form) |
| Diagonal twisted-FOC reduction | T1 | PROVED |
| Twisted FOC (general) | T5 | RE-PINNED (exact obstruction: no operator `*`, no factor order-one) |
| Continuum limit | — | SCOPED/PRICED (no claim) |
| antipodeAxiomEval | T1 | CLOSED (verified) |
| Fermionic Fock core (CAR creators, Pauli) | T1 | PROVED (8 thms) |
| Mixed CAR / number operators | T5 | PINNED (fockInnerProduct gap) |

**Commits (local, nothing pushed):** `ac1937d` (enrichment+J+Krein) ·
`b0ee87b` (opposite rep + FOC partial) · `fbcdac7` (continuum scoping) ·
`f02e0c2` (Fock) · antipode verified at `983f00e`.

## 5. Road to Rung 4 — admission price

Rung 4 = the analytic setting: Hilbert-enriched `TripleData` (inner product with
positivity), bounded commutators, compact resolvent, factor-level order-one as
class data — then the twisted FOC's remaining pin and the Wightman axioms (the
summit's door, still quarantined as opaque Props until the analysis exists).
