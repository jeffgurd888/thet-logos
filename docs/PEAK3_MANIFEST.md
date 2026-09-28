# Peak 3 Verification Manifest — Consolidation & Audit

**Date:** 2026-09-28
**Repository:** github.com/jeffgurd888/thet-logos
**Branch:** master

---

## 1. Zero-Sorry CI Build

Full workspace `lake build` passes cleanly:

```
Build completed successfully (3317 jobs).
```

(One pre-existing deprecation warning in `ThreeGen.lean`: `if_pos` → `ite_eq_left`.
Non-blocking; unrelated to Peak 3 modules.)

Modules verified to compile with zero `sorry`:
- `ThetLogos.CFKernelBase`
- `ThetLogos.MartinettiRep`
- `ThetLogos.InnerFluctuations`
- `ThetLogos.ProductTriple`
- `ThetLogos.SpectralAction`

---

## 2. Commit Ledger

| Commit    | Contents                                   | Status |
|-----------|--------------------------------------------|--------|
| `56e75a0e` | `InnerFluctuations.lean` — Majorana-sector stability, opposite-one-form expansion, order-one preservation for `smDirac` | **MACHINE-CHECKED finite-matrix algebra** |
| `25739ac5` | `ProductTriple.lean` + `SpectralAction.lean` — T5 continuum scaffolding | **SCAFFOLD** — axiomatized continuum placeholders, see §4 |

---

## 3. Axiom Localization Report (`#print axioms`, 2026-09-28)

Finite-matrix theorems depend **only** on the Lean/Mathlib base axioms
(`propext`, `Classical.choice`, `Quot.sound`) — zero unexpected axioms:

| Theorem | File | Axiom dependencies |
|---|---|---|
| `inner_fluctuation_preserves_order_one_smDirac` | InnerFluctuations.lean | `propext`, `Classical.choice`, `Quot.sound` only |
| `inner_fluctuation_majorana_subspace` | InnerFluctuations.lean | `propext`, `Classical.choice`, `Quot.sound` only |
| `trace_scalar_mul_one` | SpectralAction.lean | `propext`, `Classical.choice`, `Quot.sound` only |
| `seely_dewitt_a2_formula` | SpectralAction.lean | `propext`, `Classical.choice`, `Quot.sound` only |

Continuum theorem — **T5 axioms localized here only**:

| Theorem | File | Axiom dependencies |
|---|---|---|
| `product_cross_term_vanishes` | ProductTriple.lean | `SpinorHilbert`, `gamma5`, `diracM_gamma5_anticommute`, `SpinorHilbert.add/neg/neg_add_cancel/zero` |

### Declaration counts

| File | `axiom` declarations | Character |
|---|---|---|
| `InnerFluctuations.lean` | **0** | Machine-checked finite matrix proofs |
| `ProductTriple.lean` | **12** | T5 continuum placeholders (SpinorHilbert, DiracM, gamma5, anticommutation, `productDirac : Matrix I32 I32 ℂ → String`, `product_sum_of_squares : ∀ D_F, True`) |
| `SpectralAction.lean` | **6** | T5 continuum placeholders (`scalarCurv : String`, `lichnerowicz : True`, `heatKernelExpansion : True`, `seely_dewitt_a0/a4 : True`, `spectral_action_expansion : True`) |

**T5 axiom quarantine holds:** all continuum-geometry axioms are declared in
`ProductTriple.lean` and `SpectralAction.lean` only. No finite-matrix module
depends on them.

**Name note:** the checklist referenced `trace_a2_factorization`. No theorem
with that name exists in the codebase. The real trace result is
`trace_scalar_mul_one` (genuine T3 scalar-trace lemma, zero extra axioms);
`seely_dewitt_a2_formula` is a `True`-concluding placeholder and is **not**
an $a_2$ derivation.

---

## 4. Demarcation: Proven vs. Scaffolded

### Fully machine-checked (finite matrix algebra, zero sorrys, zero extra axioms)

1. **Order-one preservation under inner fluctuations.**
   `inner_fluctuation_preserves_order_one_smDirac`: for the SM Dirac ansatz
   (`smDirac_IsJCompatible` discharged), $D_A = D_F + A + JAJ^{-1}$ satisfies
   the order-one condition for every algebraic one-form over the 12 selected
   generators.
2. **Opposite-one-form expansion.** Machine-checked with honest factor-order
   reversal and minus sign:
   $JAJ^{-1} = -\sum_i[D_F,\pi^\circ(b_i)]\pi^\circ(a_i)$.
3. **Self-adjointness of the fluctuated Dirac operator** under self-adjoint
   $D_F$, $A$.
4. **Majorana-entry stability** (`inner_fluctuation_majorana_subspace`):
   $(D_A)_{24,8} = Y_R$ — the one-form and its $J$-conjugate both vanish at
   the $(24,8)$ Majorana entry for every selected-generator one-form.
   ⚠️ **Scope caveat:** the theorem as compiled proves the single $(0,0)$
   E-block entry $(eBlockOf\,D_A)\,0\,0 = y_R$. It does **not** conclude
   `IsMajoranaSubspace` for the full $E$ block (the remaining 63 entries are
   not yet proven zero or proportional). Either prove the full block or rename
   to honest entry-invariance — open item before claiming Task 1 complete.
5. **Abstract cross-term cancellation** (`product_cross_term_vanishes`):
   compiled proof from the anticommutation and cancellation axioms.

### Scaffolded T5 (compiles; mathematical content is placeholder)

- `productDirac` is typed as `Matrix I32 I32 ℂ → String` — **not** a
  constructed tensor-product Dirac operator.
- `product_sum_of_squares` concludes `True` — **not** the operator identity
  $D^2 = D_M^2\otimes 1 + 1\otimes D_F^2$ (cross term cancellation).
- `scalarCurv` is a `String`; `lichnerowicz`, `heatKernelExpansion`,
  `seely_dewitt_a0`, `seely_dewitt_a4`, `spectral_action_expansion` conclude
  `True`.
- `endomorphismEA` returns the string `"E_A"` — **not** a matrix/operator.
- **No theorem currently proves** $\operatorname{Tr}_{128}(E_A)
  = 32R + 4\operatorname{Tr}_{32}((D_F^{(A)})^2)$.
- `seely_dewitt_a2_formula` concludes `True` — **not** a Seeley–DeWitt
  $a_2$ derivation.

### Standing limitations

- `IsAlgebraicOneForm` ranges over finite sums of the **12 selected
  generators**, not arbitrary algebra elements or linear combinations.
- The 46→10 classification result (commit chain preceding `56e75a0e`) remains
  conditional on the two T4 numerical axioms (`exoticBasisAux`,
  `pivot_matrix_invertible`), per the recorded honesty boundary.
- No continuum geometry or spectral-action derivation is claimed.

---

## 5. Open items after this consolidation

1. Repair `inner_fluctuation_majorana_subspace`: clarify `Fin 7` vs. full
   `Block8` intent (§4 scope caveat) and prove the full E-block, or rename to
   honest $(24,8)$-entry invariance.
2. Replace `ProductTriple.lean` placeholders with typed formal structures:
   honest continuum operator interface, typed product operator, meaningful
   sum-of-squares proposition.
3. Replace `SpectralAction.lean` `String`/`True` placeholders: typed $E_A$,
   actual tensor-trace factorization, real algebraic $a_2$ identity.
4. Non-blocking: replace deprecated `if_pos` in `ThreeGen.lean` with
   `ite_eq_left`.

---

*This manifest is the recorded boundary between what the machine has checked
and what remains axiomatized. It must not be cited as claiming continuum
geometry or spectral-action derivation.*
