# STEM BRIDGE B1 — THE MAGNETIC GRAPH LAPLACIAN

**Date:** 2026-10-24. **Verdict: LANDED — STANDS WHOLE (T1),
parent-verified.** Module: `lean/ThetLogos/BridgeMagnetic.lean`.
Charter: `whitepaper/stem-bridge-scoping-2026-10-24.md` (§2
statement S1; §6 brick B1).

**NO CLAIM.** Parts of any official Clay statement closed by
this brick: **0**.

## The object

The STEM bridge (Spectral–Thermal ElectroMagnetic — Jeff's name)
joins two banks: the spectral–thermal bank (spectra of operators,
heat semigroups) and the electromagnetic bank (a U(1) connection).
Its joining object, per the charter, is the heat kernel of a
covariant operator. Brick B1 builds that operator in the finite
seat: the **magnetic graph Laplacian** `L_{w,θ}` on the Bridge
exhibit's own graph — the exhibit's real conductances `w`
unchanged, a Circle-valued connection `θ : V → V → Circle` (with
the reverse edge carrying the inverse phase, hypothesis `θ j i =
(θ i j)⁻¹`) seated in the Ohm factor, and complex potentials:

```
magLap w θ F i = ∑ j, (w i j : ℂ) * (F i − (θ i j : ℂ) * F j)
```

The connection enters through the covariant drop `magDrop θ F i
j = F j − (θ j i : ℂ) * F i`, and the operator factors through
the exhibit's three-map anatomy:
`magLap_eq_diverge_ohm_drop : magLap w θ F = divergeC (ohmC w
(magDrop θ F))` — spending only the symmetry of `w`, exactly as
the exhibit's own factorization does; the connection's
antisymmetry is spent later, on the energy. The linear operator
`magLin w θ` lives on `EuclideanSpace ℂ V`, built by conjugation
through `WithLp.linearEquiv` — `BridgeCompletion.lapLin`'s own
construction.

## What stands (the charter's S1, both halves)

- **S1a — self-adjointness.** `magLin_isSymmetric :
  (magLin w θ).IsSymmetric`, under `w` symmetric and `θ`
  antisymmetric in the charter's sense. Both hypotheses hold at
  `θ ≡ 1`: the zero-field case is not excluded (the charter
  kill condition's second clause, checked and clear).
- **S1b — the phased energy identity, two forms.**
  `magBilin_identity` (polarized): twice the phased bilinear
  form is the sum over ordered edge pairs of `w i j` times the
  product of conjugate twisted differences — the exhibit's
  `bilin_identity` symmetrization carried through the phases,
  the cross terms identified by the sum-swap together with
  `conj (θ i j) = θ j i` and the unitarity `(θ j i) * (θ i j)
  = 1`. `magLin_energy_identity` (diagonal, operator form):
  `⟪F, magLin w θ F⟫_ℂ` is the cast of `(1/2) * magEnergy w θ
  F`, where `magEnergy` is the sum of `w i j * ‖F i − θ i j *
  F j‖²`.
- **Positivity.** `magEnergy_nonneg` (termwise, for nonnegative
  `w`) and `magLin_energy_nonneg : 0 ≤ (⟪F, magLin w θ F⟫_ℂ).re`.
- **The definitional weld (definition check, pulled forward).**
  `magLap_one : magLap w 1 F = laplacianOpC w F`, with
  `laplacianOpC_ofReal` identifying the complex form with the
  exhibit's `laplacianOp` on real potentials: at zero field the
  magnetic operator *is* the landed exhibit's operator,
  verbatim. The full S5 weld (eigenvalues `lapEig`, heat
  content) remains brick B5 and is not asserted here.

## Verification (parent-run, independent of the builder)

- Fresh rebuild `lake build ThetLogos.BridgeMagnetic`: **EXIT
  0, 3,320 jobs**; olean present at
  `lean/.lake/build/lib/lean/ThetLogos/BridgeMagnetic.olean`.
  Post-header-flip rebuild also EXIT 0 (3,320 jobs).
- House counter (`count_lean.py`): **24 strict / 11 defs**,
  matching the builder's report; no same-line `@[simp]`
  declarations added.
- Code-sorry census: **0** occurrences of `sorry` or `admit`
  in the source.
- Parent-run `#print axioms` on `magLin_isSymmetric`,
  `magBilin_identity`, `magLin_energy_identity`, `magLap_one`:
  each depends only on `[propext, Classical.choice,
  Quot.sound]` — **no sorryAx**.
- Census impact: program **4,372 strict / 4,421
  attribute-inclusive / 145 counted modules** (re-derived at
  landing: whole tree 5,041 strict over 160 files minus the
  documented 669-strict / 15-file non-chain remainder of the
  2026-10-18/19 double-check sweep).

## Fence

B1 only: definition + S1. Gauge covariance (B2), the heat
object (B3), flux-dependence (B4/B4′), and the full zero-field
weld (B5) are untouched. This is finite graph bookkeeping — a
U(1) connection on a finite graph and an operator on a
finite-dimensional space. It is **not** Maxwell theory
(continuum Maxwell has NO SEAT in this corpus), not a
force-unification claim, not a torsion claim, and not a
modular-flux claim: the killed EM-torsion paste, the killed
"strong nuclear = electromagnetic" identification, and the
killed magnetophase flux (`ModularFlux.magnetophaseFlux_vanishes`)
stay killed. Stage 1b-B is unaffected: positivity T1 for U(1),
general (G, ρ) OPEN.

— BONES, for the record. Tiers per the Concrete; **NO CLAIM.**
