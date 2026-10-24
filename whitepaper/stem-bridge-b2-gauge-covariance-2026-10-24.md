# STEM BRIDGE B2 — GAUGE COVARIANCE

**Date:** 2026-10-24. **Verdict: STANDS WHOLE (T1).** Brick B2 of
the STEM bridge (Spectral–Thermal ElectroMagnetic; charter
`whitepaper/stem-bridge-scoping-2026-10-24.md`): the charter's
statement **S3** is proved. Parent-verified and shipped the day
it was built.

**NO CLAIM.** Parts of any official Clay statement closed by
this brick: **0**. Stage 1b-B label unchanged: positivity T1
for U(1); general (G, ρ) OPEN.

---

## 1. What stands

New module `lean/ThetLogos/BridgeMagneticGauge.lean` (imports
`Mathlib.Tactic`, `Mathlib.Analysis.Complex.Circle`,
`ThetLogos.BridgeMagnetic`; no proved file edited). **22 strict
theorems / 3 defs** (`gaugeConn`, `gaugeDiag`, `gaugeOp`), 0
same-line `@[simp]`.

For a vertex gauge transformation `g : V → Circle`, B1's
magnetic graph Laplacian is gauge-covariant:

- **Headline** `magLin_gauge`:
  `magLin w (gaugeConn g θ) = gaugeOp g ∘ₗ magLin w θ ∘ₗ
  gaugeOp (fun i => (g i)⁻¹)`.
  **Hypothesis-free** — no symmetry of `w`, no antisymmetry of
  `θ` is spent; the identity is pure algebra.
- **The adjoint in both corpus senses.** `U_g*` is carried as
  `gaugeOp (fun i => (g i)⁻¹)` and proved to be the adjoint two
  ways: as a **two-sided inverse**
  (`gaugeOp_comp_gaugeOpInv`, `gaugeOpInv_comp_gaugeOp`) and by
  the **adjoint's defining identity** `⟪U_g X, Y⟫ = ⟪X, U_g*
  Y⟫` (`gaugeOp_adjoint`, via `Circle.coe_inv_eq_conj`). On a
  Hilbert space the adjoint is unique, so this is S3's `U_g*`,
  not a namesake.
- **Antisymmetry preserved** `gaugeConn_antisymm`: if
  `θ j i = (θ i j)⁻¹` for all `i j`, so does `θ^g` — the proof
  spends only the inverse-of-product law in the abelian Circle.
  B1's theorems therefore apply to `L_{w,θ^g}` verbatim
  (transported explicitly as `magLin_gaugeConn_isSymmetric`).
- **Corollaries at the level proved.** `magEnergy_gauge`: the
  phased Dirichlet energy is invariant under simultaneous
  gauging of `θ` and the potential (the twisted difference is
  `g i` times the original, and a phase has `normSq` 1).
  `magLin_gauge_hasEigenvalue`: `μ` is an eigenvalue of
  `L_{w,θ^g}` **iff** it is one of `L_{w,θ}`, eigenvectors
  transported by `U_g` / `U_g⁻¹` through the headline.

## 2. The forced convention

The charter's S3 fixes `U_g` by `(U_g F) i = g i • F i` but
prints no formula for `θ^g`. There was no freedom to choose:
the intertwining `L_{θ^g} ∘ U_g = U_g ∘ L_θ` closes termwise
**iff** `θ^g i j * g j = g i * θ i j` for every edge — the
component computation cancels the diagonal gauge phases and
identifies each edge phase exactly under this condition,
proved as `gaugeConn_mul` (and over `ℂ` as
`gaugeConn_coe_mul`). The convention the condition forces is

    gaugeConn g θ i j = g i * θ i j * (g j)⁻¹,

which is the form the brief stated and B1's conventions bear.
No charter correction arises, and no convention was swapped
silently: the one formula that makes the algebra close is the
formula on the record.

## 3. The named gap — S3's heat-trace half belongs to B3

S3's sentence continues "hence the spectrum … **and the heat
trace of S2** depend only on the gauge class of θ". The
eigenvalue half is proved above. The **heat-trace half is NOT
asserted here**: the heat object is brick B3 and does not exist
yet. Once B3 builds `e^{−tL}` from a form that consumes the
operator (e.g. `HermitianReduction.heatKernelGen`'s conjugation
law), the trace consequence of `magLin_gauge` is a corollary of
B3, not of this module. The spectrum statement is therefore
carried at exactly the level the corpus holds today: operator
conjugacy + eigenvalue invariance + energy invariance.

## 4. Verification (parent-run, independent)

- Fresh rebuild with the olean deleted first:
  `lake build ThetLogos.BridgeMagneticGauge` **EXIT 0, 3,321
  jobs**; olean present at
  `lean/.lake/build/lib/lean/ThetLogos/BridgeMagneticGauge.olean`;
  post-header-flip rebuild EXIT 0 (3,321 jobs).
- House recount of the module: **22 strict / 3 defs**, 0
  same-line `@[simp]` — matches the builder.
- Code-sorry census: **0** (`sorry`/`admit` absent from the
  source).
- Parent-run `#print axioms` on `magLin_gauge`,
  `gaugeConn_antisymm`, `gaugeOp_adjoint`,
  `gaugeOp_comp_gaugeOpInv`, `magEnergy_gauge`,
  `magLin_gauge_hasEigenvalue`: each only
  `[propext, Classical.choice, Quot.sound]` — **no sorryAx**.
- **Census impact:** program census moves from 4,401 strict /
  4,450 attribute-inclusive / 148 counted modules to **4,423
  strict / 4,472 attribute-inclusive / 149 counted modules**
  (full-tree recount: whole tree 5,092 strict over 164 files,
  minus the documented 669-strict / 15-file non-chain remainder
  of the 2026-10-18/19 sweep; 49 same-line `@[simp]`
  corpus-wide, none added by this module).

*Transparency note:* the builder's memo projected the census
delta off a stale base (4,382, the pre-R1 figure); the counted
numbers above govern.

## 5. Fences

B2 lands S3 at the level stated in §1/§3 and nothing more.
**Unbuilt:** B3 (the heat object — S3's heat-trace corollary
lives there), B4/B4′ (flux-dependence), B5 (the full
zero-field weld). This is finite graph bookkeeping — **not
Maxwell theory** (continuum Maxwell has NO SEAT in this
corpus), not a force-unification claim, not a torsion claim,
not a modular-flux claim; the killed EM-torsion paste, the
killed "strong nuclear = electromagnetic" identification, and
the killed magnetophase flux stay killed. Stage 1b-B is
unaffected.

**NO CLAIM.** Census at this landing: 4,423 / 4,472 / 149.
