# STEM BRIDGE B5 — THE ZERO-FIELD WELD

**Date:** 2026-10-24. **Verdict: STANDS WHOLE (T1).** Brick B5
of the STEM bridge (Spectral–Thermal ElectroMagnetic; charter
`whitepaper/stem-bridge-scoping-2026-10-24.md`): the charter's
statement **S5** is proved — at the trivial connection
`θ ≡ 1`, the magnetic theory of B1–B3 contains the Bridge
exhibit's own theory as its zero-field special case, end to
end, at every level the objects live: operator, matrix, heat,
trace — plus the Fiedler reading of the `θ = 1` gap (floor and
attainment). With this landing, **the bridge's near bank is
complete** (B1, B2, B3, B5). Parent-verified and shipped the
day it was built.

**NO CLAIM.** Parts of any official Clay statement closed by
this brick: **0**. Stage 1b-B label unchanged: positivity T1
for U(1); general (G, ρ) OPEN — this brick does not touch it.

---

## 1. What stands

New module `lean/ThetLogos/BridgeMagneticWeld.lean` (imports
`Mathlib.Tactic`, `Mathlib.Analysis.Complex.Circle`,
`Mathlib.Analysis.Matrix.PosDef`,
`ThetLogos.BridgeMagneticHeat`, `ThetLogos.BridgeCompletion`;
no proved file edited). **26 strict theorems / 3 defs**
(`castVec`, `castEigVec`, `weldMat`), 0 same-line `@[simp]`.

One cast carries the whole brick: **`castVec f`**, a real
potential read over `ℂ` componentwise. B1's
`laplacianOpC_ofReal` — the complex plain Laplacian of a cast
potential is the cast of the exhibit's `laplacianOp` — turns it
into an eigenvector transport:

- **`magMat_one_mulVec_castVec`**: if `f` is an eigenvector
  of `laplacianOp` with eigenvalue `μ`, then `castVec f` is
  an eigenvector of `magMat w 1` with eigenvalue `↑μ`.

## 2. Operator level — welded

B1's definitional weld `magLap_one` (`magLap w 1 =
laplacianOpC w`) is cited, not rebuilt. Its two packagings are
recorded:

- **`magLapFun_one_apply`**: the linear-map form,
  `magLapFun w 1 F = laplacianOpC w F`.
- **`euclEquivC_magLin_one`**: the Euclidean form — `magLin
  w 1` on `EuclideanSpace ℂ V` transports under `euclEquivC`
  to `laplacianOpC`.

## 3. Matrix level — welded, entrywise and spectral

- **`magMat_one_apply` / `magMat_one`**: at `θ ≡ 1` the phase
  factor is `1`, so `magMat w 1` has the closed form
  `(if j = i then ∑ k, ↑(w i k) else 0) − ↑(w i j)` — the
  conductance row-sum on the diagonal, the bare cast
  conductance off it: the exhibit's matrix in B3's
  representation.
- **`magMat_one_toLin'_apply`**: `Matrix.toLin'` of it is
  `laplacianOpC` (via B3's `magMat_one_mulVec`).

The exhibit's spectral data (`lapBasis`, `lapEig`) are
indexed by `Fin (finrank ℝ (EuclideanSpace ℝ V))`, not by
`V`. The cast eigenbasis **`castEigVec`** — the exhibit's
`k`-th eigenbasis vector read over `ℂ` — stays orthonormal
for the `dotProduct` pairing (**`castEigVec_dotProduct`**,
real orthonormality cast), stays nonzero
(`castEigVec_ne_zero`), and satisfies the eigen equation
(**`magMat_one_mulVec_castEigVec`**: `magMat w 1 *ᵥ
castEigVec k = ↑(lapEig k) • castEigVec k`, the "eigenvalues
are `lapEig`" clause of S5). Assembled as columns they form
the rectangular **weld matrix** `weldMat` with its two
unitary identities — orthonormality
(**`weldMat_conjTranspose_mul_self`**: `weldMatᴴ * weldMat =
1`) and completeness (**`weldMat_mul_conjTranspose_self`**:
`weldMat * weldMatᴴ = 1`, by the real Parseval identity from
`lapBasis.sum_repr`) — and the spectral form of the weld:

- **`magMat_one_eq_conj`**: `magMat w 1 = weldMat * diagonal
  (↑∘lapEig) * weldMatᴴ` — hypothesis-free, pure algebra off
  the eigen equation and the two unitary identities.

## 4. Heat level — welded, three ways that agree

The exhibit's `heatOp` is an operator on `EuclideanSpace ℝ V`
in eigenbasis form; there is no ℂ-object to equate with. The
weld the objects support is the eigenbasis identification
itself, proved three ways, all agreeing:

1. **Eigenvector by eigenvector**
   (**`magHeat_one_mulVec_castEigVec`**): each cast
   eigenbasis vector is heated by exactly `heatOp`'s factor:
   `magHeat w 1 t *ᵥ castEigVec k = ↑(Real.exp (−t * lapEig
   k)) • castEigVec k`.
2. **As a solution formula** (**`castEigVec_expansion`** +
   **`magHeat_one_solution`**): every complex potential
   expands in the cast eigenbasis with `dotProduct`
   coefficients (the ℂ form of `heatOp`'s `repr` expansion),
   and `magHeat w 1 t` acts as `heatOp` read over ℂ — expand,
   damp the `k`-th coefficient by `exp (−t * lapEig k)`,
   resum. This is `heatOp_solution_formula` with ℂ
   coefficients.
3. **As a matrix identity** (**`magHeat_one_eq_conj`**):
   `magHeat w 1 t = weldMat * hermitianDiagKernel (lapEig) t
   * weldMatᴴ` — the engine's `heatKernelGen_eq_conj` form
   with the exhibit's own eigenvalues in the schedule.

One genuine constraint, routed around rather than hidden:
the rectangular `weldMat` cannot feed the engine's square
`exp_conj_star`, so (1) is proved by the **support argument**
on `magMat`'s own spectral form — a vector in the
`λ`-eigenspace of a Hermitian matrix is heated by
`exp (−tλ)`, degeneracy-proof — and (3) is recovered from
(2) by `mulVec`-injectivity (`matrix_eq_of_mulVec_eq`).

## 5. Trace level — welded

- **`magHeatTrace_one`**: `magHeatTrace w 1 t = ↑(∑ k,
  Real.exp (−t * lapEig k))` — the exhibit's heat trace
  datum at the exhibit's eigenvalues. Proved from
  `magHeat_one_eq_conj` by cycling the weld matrix through
  `Matrix.trace_mul_comm` — the engine's
  `trace_conj_diagKernel` computation in rectangular form.

## 6. The Fiedler gap at θ = 1 — floor and attainment

The exhibit's gap facts restate at the welded operator, in
the corpus's own terms:

- **`magMat_one_fiedler_floor`**: every nonzero welded
  eigenvalue is `≥ fiedler w` — the exhibit's
  `fiedler_le_lapEig` transported, with the eigenvalue's
  welded eigenvector and its nonvanishing attached.
- **`magMat_one_fiedler_eigen`**: for two distinct vertices,
  `fiedler w` *is* an eigenvalue of `magMat w 1` with a
  nonzero eigenvector — the exhibit's attained minimizer
  (`laplacianOp_fiedler_minimizer`), transported through
  the cast.

Floor + attainment: the Fiedler value is the `θ = 1`
spectral gap of the magnetic theory, stated and proved
without leaving the corpus's vocabulary.

## 7. The named seam

`weldMat` is rectangular — `Matrix V (Fin (finrank ℝ
(EuclideanSpace ℝ V))) ℂ` — because the exhibit's eigenbasis
is indexed by the finrank type, not by `V`. Mathlib carries
**no `star` on rectangular matrices**, so the weld matrix's
adjoint is `conjTranspose` (`ᴴ`), here and throughout. This
is a representation fact, not a gap in the weld: both unitary
identities are proved in the `ᴴ` form, and every conjugation
in §3–§5 is stated with it. The seam is recorded on the
module's face and kept visible here so no reader mistakes
the notation for an elided step.

## 8. Verification (parent-run, independent)

- Fresh rebuild with the olean deleted first:
  `lake build ThetLogos.BridgeMagneticWeld` **EXIT 0, 3,593
  jobs**; olean present at
  `lean/.lake/build/lib/lean/ThetLogos/BridgeMagneticWeld.olean`;
  post-header-flip rebuild EXIT 0 (3,593 jobs). (One
  cosmetic deprecation warning, `if_neg` → `ite_eq_right`,
  at line 598; no errors.)
- House recount of the module: **26 strict / 3 defs**
  (`castVec`, `castEigVec`, `weldMat`), 0 same-line
  `@[simp]` — matches the builder.
- Code-sorry census: **0** (`sorry`/`admit` absent from the
  source entirely).
- Parent-run `#print axioms` on all 18 headlines
  (`magMat_one_mulVec_castVec`, `magLapFun_one_apply`,
  `euclEquivC_magLin_one`, `magMat_one_apply`, `magMat_one`,
  `magMat_one_toLin'_apply`, `castEigVec_dotProduct`,
  `magMat_one_mulVec_castEigVec`,
  `weldMat_conjTranspose_mul_self`,
  `weldMat_mul_conjTranspose_self`, `magMat_one_eq_conj`,
  `magHeat_one_mulVec_castEigVec`, `castEigVec_expansion`,
  `magHeat_one_solution`, `magHeat_one_eq_conj`,
  `magHeatTrace_one`, `magMat_one_fiedler_floor`,
  `magMat_one_fiedler_eigen`): each only `[propext,
  Classical.choice, Quot.sound]` — **no sorryAx**.
- **Census impact:** program census moves from 4,445 strict
  / 4,494 attribute-inclusive / 150 counted modules to
  **4,471 strict / 4,520 attribute-inclusive / 151 counted
  modules** (full-tree recount: whole tree 5,140 strict
  over 166 files, minus the documented 669-strict / 15-file
  non-chain remainder of the 2026-10-18/19 sweep; 49
  same-line `@[simp]` corpus-wide, none added by this
  module). The delta is exactly the module's +26 / +1.

## 9. Fences — the near bank is complete; what remains

**The bridge's near bank is now complete:** B1 (the magnetic
operator), B2 (gauge covariance), B3 (the heat object, datum
trace, trace-level gauge invariance), B5 (this weld). The
magnetic theory is a self-contained finite theory whose
zero-field specialization is the Bridge exhibit, whole.

**Remaining on the bridge:**

- **B4′** — the face-restricted flux-dependence: the gauge
  class of the spectrum/heat trace read from face holonomies
  over `BridgeCompletion` §9 face data. Its landing leaves
  the bridge at **PARTIAL**. It inherits from this brick a
  second fully-welded observable — the heat trace in exhibit
  datum form (`magHeatTrace_one`) alongside B3's gauge
  invariance (`magHeatTrace_gauge`) — so a face-holonomy
  reading of the spectrum transports to the trace for free.
- **B4** — general flux-dependence (spectrum and heat trace
  hear the connection only through cycle holonomies, on a
  general graph): the ladder's long pole. It needs
  cycle-space / spanning-tree gauge-fixing machinery the
  corpus does not yet hold — a **named remainder**, not a
  scheduled brick.

This is finite graph bookkeeping — the zero-field
specialization of a finite matrix heat semigroup. It is
**not Maxwell theory** (continuum Maxwell has NO SEAT in
this corpus), not a force-unification claim, not a torsion
claim, and not a modular-flux claim
(`ModularFlux.magnetophaseFlux_vanishes` stays a kill at
T1). The killed EM-torsion paste and the killed "strong
nuclear = electromagnetic" identification stay killed.
Clay parts closed: 0.
