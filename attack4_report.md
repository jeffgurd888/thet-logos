# Attack 4 Report: Order-One Nullity and the Five-Block Claim

**Date:** 2026-09-26 (final revision)
**Status:** T4 numerical exploration (not a theorem, not a Lean proof)
**Verdict:** NO-GO on the five-block forcing claim. The finite SM triple,
faithfully encoded, gives order-one nullity **46**, not 10. The five-block
form is an ansatz, not a consequence of order-one.

---

## 1. Objective

Determine mechanically whether a faithful Standard Model finite
representation makes the 589,824 scalar order-one equations
(576 generator pairs × 1,024 matrix entries) force the intended
five-block Dirac/Yukawa form:

- 8 real Dirac/Yukawa dimensions (Y_ν, Y_e, Y_u, Y_d),
- 2 real Majorana dimensions (right-neutrino mass),
- total: **10 real dimensions**.

Stopping rule: do not run the 6,494-algebra catalogue until a physically
calibrated A_F control passes all valid diagnostics.

## 2. What was built

`python/thet_logos/repair_scan.py` — multiplicity enumeration,
representations via `build_reps`, order-zero check, central projectors,
intersection form, order-one nullspace via QR-compressed SVD,
generic D_F sampling, orientability, irreducibility, controls-first
scanning.

## 3. The invalid control (nullity 0)

The originally encoded control `(m,S) = ((4,3,2), ...)` returned:

- Poincaré determinant: 0
- Order-one nullity: **0**
- All 619 encoded A_F patterns: determinant zero.

This nullity-0 result is **invalid as a physical control**: the
representation is not grading-even
(`max ||[Γ,π(a)]|| = 4.0`, `max ||[Γ,π°(a)]|| = 4.0`).
A representation violating the grading axiom cannot calibrate anything.

## 4. The (m,S) candidate (nullity 16) — SUPERSEDED

A candidate datum `m = (8, 4, 0)`, `S = ((2,0,2),(1,0,1),(0,0,0))`
gave nullity 16 with grading-evenness and order-zero passing.
A 40-pattern landscape scan found nullities 0–128, none giving 10.

This entire line is **superseded**: the `(m,S)` formalism was bypassed
(see §7), not repaired. The nullity-16 number is a property of the
`(m,S)` encoding, not of the SM triple.

## 5. The literature datum

A literature agent extracted the KO-dimension-6 finite SM triple:

- **Martinetti 2301.08346v2 §2.5** (recalling Chamseddine–Connes–Marcolli):
  A_F = C⊕H⊕M_3(C) (3 summands); H_F = C^96 (3 generations);
  D_F = D_Y + D_M with D_M block-off-diagonal in particle/antiparticle;
  the Majorana D_R couples ν_R ↔ ν̄_R and **commutes with the algebra**
  ([D_M, a] = 0, eq. (34)), so order-one holds trivially for it.
- **Krajewski hep-th/9701081 §5**: explicit representation; multiplicity
  matrix μ (4×4 in basis (C,H,C̄,M_3(C))).
- **Krajewski 0809.5137**: the 4-summand C⊕C⊕H⊕M_3(C) is required **only**
  for Poincaré duality (KO-6 intersection form is antisymmetric, hence
  singular for odd summand count); the physical representation identifies
  the two C summands. **3 summands suffice physically.**
- KO-6 signs: J²=1, JD=DJ, JΓ=−ΓJ.

## 6. Correction: the "decisive obstruction" was wrong

An earlier revision of this report claimed `build_reps` was
dimensionally incapable of carrying the 12-dimensional antiparticle
colour action. **That argument was incorrect.** The `kron(I₂, ·)`
factor on the quaternionic block doubles the irrep capacity, so
`3c_0 + 6c_1 = 12` can fit. The dimensional obstruction does not exist.

The actual problem was never dimensional — it was that the `(m,S)`
formalism indexes irreps per-left-block, while the SM representation
needs the Krajewski μ-matrix (irrep-pair) structure. Rather than repair
`(m,S)`, the SM representation was built directly (§7).

## 7. The Martinetti representation (direct construction)

Bypassing `(m,S)` entirely, the SM representation was constructed
directly from the Martinetti (C,I,α) datum in the repository's 32-dim
post-swap basis:

| Index range | Sector | Action |
|-------------|--------|--------|
| 0–7 | left particles (H doublets) | H via Pauli on (I,α) |
| 8–15 | right particles (C singlets) | C via i·I₈ |
| 16–21, 24–29 | antiquarks (M₃ triplets) | M₃ via Gell-Mann on colour index |
| 16–17, 24–25, 22–23, 30–31 | antileptons (C singlets) | C via i·I |

Key structural point: H acts on the flavour index α, M₃ acts on the
colour index I — different tensor factors, so they commute. The
antiparticle colour triplets are
(18,20,22), (19,21,23), (26,28,30), (27,29,31),
each within a single Γ-eigenspace (grading-evenness).

Diagnostics (numerical, tolerance 1e-8), 12-generator version:

- `max ||[Γ,π]|| = 0.00e+00`, `max ||[Γ,π°]|| = 0.00e+00`
- **order-zero residual: 0.00e+00** (first time in this pipeline)
- full admissible D_F basis: 272 real dimensions
- **order-one nullity: 46**, normalized spectral gap 0.83

Full 23-generator real-algebra version (C: {1,i}; H: {1,iσ_k};
M₃(C): {1, iλ_a, λ_a}):

- `max ||[Γ,π]|| = 0.0e+00`, order-zero `0.0e+00`
- **order-one nullity: 46**, gap 0.87

The 12-generator version was not incomplete — 46 is the stable number.

## 8. Dissection of the 46

Per-vector analysis of the 46-dim nullspace (SVD basis):

- **Vectors 0–7 (8 dim):** quark sector only.
- **Vectors 8–45 (38 dim):** lepton sector; all 38 have
  particle↔antiparticle (Majorana-slot) support.

The expected SM content (4 complex Yukawas + 1 complex Majorana =
10 real) is a **subspace** of this 46. The remaining 36 dimensions
are operators satisfying order-one but not of SM Yukawa/Majorana type.

## 9. Poincaré-duality obstruction (RESOLVED 2026-09-26)

Under the repository's KO-dimension-6 conventions
(J²=1, JD=DJ, JΓ=−ΓJ), the finite intersection form is antisymmetric;
a 3×3 antisymmetric matrix is necessarily singular, so the
`abs(det) > 1e-8` filter was unsatisfiable for the three-summand algebra.
Per Krajewski 0809.5137, this is expected: KO-6 Poincaré duality needs
the 4-summand C⊕C⊕H⊕M_3(C).

**Fix applied** in `python/thet_logos/repair_scan.py`:
- `poincare_form` docstring documents the KO-6 obstruction.
- The control assertion and catalogue veto removed; determinant is
  diagnostics-only.

## 10. Verdict

**NO-GO** on the claim "the 589,824 order-one equations force the
five-block form":

1. The faithfully encoded SM triple gives nullity **46**, not 10.
2. The SM Yukawa + Majorana (10 real) is a subspace of the 46, but
   order-one does **not** select it — 36 extra dimensions survive.
3. The five-block form is therefore an **ansatz** (physical input),
   not a consequence of the first-order condition.

This is a **negative result for the derivation program**, not a pipeline
defect. The pipeline now contains the first fully axiom-passing finite
SM representation (grading-even, order-zero, both `0.00e+00`), and the
machine's answer is 46. The finite triple alone does not force the SM
Yukawa structure — the Yukawa matrices must be put in by hand.

Implications for Q3: if the finite part cannot select the SM Dirac
operator, the selection (if it exists) must come from thet itself
(Open Question 9) or from the full spacetime triple, not from finite
order-one alone.

## 11. What remains

- [ ] Write Lean 4 proofs for the finite triple axioms (currently T4
      numerics only; 6 sorrys remain in the Lean development).
- [ ] Prove order-one → 46-dim nullspace as a Lean theorem.
- [ ] Characterize the 36 extra dimensions (physical? gauge artifact?
      representation redundancy?).
- [ ] Run the 6,494-algebra catalogue with a faithful encoding to test
      whether order-one selects A_F = C⊕H⊕M₃(C) among competitors.
- [ ] Address Open Question 9: does thet force the finite triple?

No Attack 4 work has been committed or pushed. All local.
