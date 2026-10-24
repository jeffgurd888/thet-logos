# STEM BRIDGE B3 — THE HEAT OBJECT

**Date:** 2026-10-24. **Verdict: STANDS WHOLE (T1).** Brick B3
of the STEM bridge (Spectral–Thermal ElectroMagnetic; charter
`whitepaper/stem-bridge-scoping-2026-10-24.md`): the charter's
statement **S2** is proved — the heat object of B1's magnetic
Laplacian exists as a matrix exponential with its semigroup
law, its trace identity against the datum form, and its
contraction at the level marked in §4. B2's deferred
heat-trace corollary lands with it (§3). Parent-verified and
shipped the day it was built.

**NO CLAIM.** Parts of any official Clay statement closed by
this brick: **0**. Stage 1b-B label unchanged: positivity T1
for U(1); general (G, ρ) OPEN.

---

## 1. What stands

New module `lean/ThetLogos/BridgeMagneticHeat.lean` (imports
`Mathlib.Tactic`, `Mathlib.Analysis.Complex.Circle`,
`Mathlib.Analysis.Matrix.PosDef`, `ThetLogos.HermitianReduction`,
`ThetLogos.BridgeMagneticGauge`; no proved file edited).
**22 strict theorems / 4 defs** (`magMat`, `magHeat`,
`magHeatTrace`, `gaugeMat`), 0 same-line `@[simp]`.

- **`magMat w θ : Matrix V V ℂ`** — the matrix of B1's
  `magLin w θ` in the canonical basis: row `i` carries the
  conductance row-sum on the diagonal and the phased hopping
  `−w i j • θ i j` off it, read off `magLap_apply` term by
  term. It is tied to the operator, not merely resembling it:
  **`magMat_mulVec`** (its `*ᵥ` action IS `magLap`) and
  **`magMat_toLin'`** (`Matrix.toLin'` of it IS `magLapFun`).
  Hermitian under B1's own hypotheses, proved entrywise
  (**`magMat_isHermitian`**, hw + hθ).
- **`magHeat w θ t := heatKernelGen (magMat w θ) t =
  exp (−t • L_{w,θ})`** — the heat object. Semigroup law
  **`magHeat_add`** (hypothesis-free, as the engine states
  it) and initial condition `magHeat_zero`.

## 2. The engine's packaging, followed exactly

The corpus's general Hermitian heat engine already existed —
`HermitianReduction.heatKernelGen` — and it is a **matrix**
exponential: `exp` of `−t • K` for a Hermitian matrix `K`,
with its semigroup law, its spectral form
(`heatKernelGen_eq_conj`), and its trace identity already in
hand. The brick therefore does not build a second heat
theory, invent an operator-level exponential, or re-prove the
engine's laws: it constructs the one missing input — B1's
operator *as a matrix*, with the tie theorems of §1 — and
feeds it to the engine in the engine's own form. Every S2
clause that the engine already carries (semigroup, spectral
form) is inherited by citation; what this brick proves is the
tie, the trace identity's applicability, the gauge corollary,
the positivity package, and the zero-field half.

## 3. The trace: proved equal to the datum form (not forged)

`magHeatTrace w θ t` is **defined** as
`Matrix.trace (magHeat w θ t)` — a bare definition carries no
content, so the content is a theorem:

- **`magHeatTrace_eq`**: `magHeatTrace w θ t = ↑(∑ i,
  Real.exp (−t * λᵢ))`, where `λ =
  (magMat_isHermitian ..).eigenvalues` — proved via the
  engine's `heatKernelGen_trace` into
  `ThermalKernel.heatKernel_trace`, the corpus's
  eigenvalue-schedule datum. Since `magMat` is `magLin`'s
  matrix by §1's ties, the `λᵢ` are the eigenvalues of
  `L_{w,θ}` itself.

The trace is therefore the datum form because a proof says
so, not because a definition was written to look like it.

**B2's deferred corollary lands here, at trace level.** B2
(§3 of its dossier) proved the operator conjugation and
explicitly deferred S3's "hence … the heat trace" half to
this brick. It lands in three steps:

- **`gaugeMat g := Matrix.diagonal (fun i => (g i : ℂ))`**,
  unitary (`gaugeMat_star_mul_self`,
  `gaugeMat_mul_star_self`).
- **`magMat_gauge`**: `magMat w (gaugeConn g θ) = gaugeMat g
  * magMat w θ * star (gaugeMat g)` — entrywise conjugation
  of the matrix, hypothesis-free, mirroring `magLin_gauge`.
- **`magHeat_gauge`**: the heat kernel conjugates, via the
  engine's `exp_conj_star`.
- **`magHeatTrace_gauge`**: `magHeatTrace w (gaugeConn g θ)
  t = magHeatTrace w θ t` — the trace depends only on the
  gauge class of `θ`, proved by cycling the trace. B2's
  named gap is closed.

## 4. Positivity and contraction — at the marked level

- **`magMat_dotProduct`**: the quadratic form of `magMat` is
  S1's phased energy (B1's `magLin_energy_identity` in
  coordinates).
- **`magMat_posSemidef`** (via
  `posSemidef_iff_dotProduct_mulVec`): `magMat` is positive
  semidefinite under B1's hypotheses, so
  **`magMat_eigenvalues_nonneg`**: every `λᵢ ≥ 0` — S2's
  "λ_k(θ) ≥ 0 by S1", now spectral.
- **`heatKernelGen_quadraticForm_eq` / `_norm`**: in
  eigenbasis coordinates `y = U* x`, the heated form is
  `∑ i, exp (−t λᵢ) ‖yᵢ‖²` against the unheated
  `∑ i, ‖yᵢ‖²`.
- **`magHeat_contraction`**: for `t ≥ 0`, `0 ≤ (star x ⬝ᵥ
  (magHeat w θ t *ᵥ x)).re ≤ (star x ⬝ᵥ x).re`.

**LEVEL MARK (kept on the module's face and here):** the
contraction is asserted at the **quadratic-form level** —
the level the engine carries. The operator-norm form is not
separately asserted. (For a self-adjoint operator the two are
one Cauchy–Schwarz apart; the module says so and claims only
what it proves.)

## 5. Zero-field: the cheap half landed; the weld is B5

- **`magMat_one_mulVec`**: at `θ ≡ 1` the matrix's action is
  the Bridge exhibit's `laplacianOpC` verbatim (via B1's
  `magLap_one`).
- **`magHeat_one`**: the heat object there is the engine's
  kernel of that matrix.

The identification with `BridgeCompletion.heatOp`'s
eigenbasis form is **NOT** asserted — it is brick B5's weld,
as chartered. Nothing here pre-empts or obstructs it.

## 6. What B4′ inherits

B4′ (the face-restricted flux-dependence fallback) now
inherits two gauge-invariant observables instead of one: the
spectrum's face-holonomy reading it must prove, and the heat
trace **already in datum form** (`magHeatTrace_eq`), whose
factors are the eigenvalues, together with its gauge
invariance already proved (`magHeatTrace_gauge`). B3 spends
nothing B4′ needs and settles nothing B4′ must prove.

## 7. Verification (parent-run, independent)

- Fresh rebuild with the olean deleted first:
  `lake build ThetLogos.BridgeMagneticHeat` **EXIT 0, 3,592
  jobs**; olean present at
  `lean/.lake/build/lib/lean/ThetLogos/BridgeMagneticHeat.olean`;
  post-header-flip rebuild EXIT 0 (3,592 jobs). (One cosmetic
  deprecation warning, `if_neg` → `ite_eq_right`, at line 319;
  no errors.)
- House recount of the module: **22 strict / 4 defs**, 0
  same-line `@[simp]` — matches the builder.
- Code-sorry census: **0** (`sorry`/`admit` absent from the
  source entirely).
- Parent-run `#print axioms` on `magMat_isHermitian`,
  `magMat_mulVec`, `magMat_toLin'`, `magHeat_add`,
  `magHeatTrace_eq`, `magMat_gauge`, `magHeat_gauge`,
  `magHeatTrace_gauge`, `magMat_posSemidef`,
  `magMat_eigenvalues_nonneg`, `magHeat_contraction`: each
  only `[propext, Classical.choice, Quot.sound]` — **no
  sorryAx**.
- **Census impact:** program census moves from 4,423 strict /
  4,472 attribute-inclusive / 149 counted modules to **4,445
  strict / 4,494 attribute-inclusive / 150 counted modules**
  (full-tree recount: whole tree 5,114 strict over 165
  files, minus the documented 669-strict / 15-file non-chain
  remainder of the 2026-10-18/19 sweep; 49 same-line
  `@[simp]` corpus-wide, none added by this module). The
  delta is exactly the module's +22 / +1.

## 8. Fences

B3 lands S2 at the level stated in §1–§5 and nothing more.
**Unbuilt:** B4 (general flux-dependence — the long pole,
needs cycle-space machinery), B4′ (the face-restricted
fallback), B5 (the full zero-field weld: the `heatOp`
eigenbasis identification plus the Fiedler-gap reading).
This is finite graph bookkeeping — a heat semigroup of a
finite matrix. It is **not Maxwell theory** (continuum
Maxwell has NO SEAT in this corpus), not a force-unification
claim, not a torsion claim, and not a modular-flux claim:
the bridge's thermal object is a heat semigroup / heat
trace, never a modular flux
(`ModularFlux.magnetophaseFlux_vanishes` stays a kill at
T1). The killed EM-torsion paste and the killed "strong
nuclear = electromagnetic" identification stay killed. Stage
1b-B is unaffected.

**NO CLAIM.** Census at this landing: 4,445 / 4,494 / 150.
