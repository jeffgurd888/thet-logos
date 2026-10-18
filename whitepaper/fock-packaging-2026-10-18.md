# Fock Packaging — Dossier (2026-10-18)

**Verdict: STANDS-AS-PRICED (M).** Rung 7 remainder, packaging half,
per the gauntlet entry of 2026-10-17: **concrete ONB port only**.
Kill K4 stands permanently — the abstract SymmetricAlgebra route
is dead and was not used anywhere in this brick.

## What was owed

The corpus had (a) the one-particle Poincaré action on the
mass-shell space (boost window discharged; translation strong
continuity discharged) and (b) the second-quantization Γ functors
over abstract/countable mode spaces. What was owed was the
**packaging**: the one-particle action of *this* corpus's
mass-shell space, ported through Γ to a unitary group action on
the assembled bosonic and fermionic Fock spaces, with the group
law and translation strong continuity transported.

## What landed

Three Lean modules, one dossier, all T1 (machine-checked, zero
sorry/admit, `#print axioms` = the standard three — `propext`,
`Classical.choice`, `Quot.sound` — on every headline):

| module | content | strict count |
|---|---|---|
| `lean/ThetLogos/FockPackaging.lean` | fence-neutral base: the shell representation packaged as a linear-isometry-equiv family, concrete ONB, separability | 38 |
| `lean/ThetLogos/FockPackagingBos.lean` | bosonic packaging | 99 |
| `lean/ThetLogos/FockPackagingFerm.lean` | fermionic packaging | 78 |
| **brick total** | | **215** |

Program total: 2,774 (pre-brick, at the 1c-0 landing) + 215 =
**2,989 strict**.

Build: targeted `lake build` of the three modules completes
successfully (3,675 jobs); all three `.olean`s postdate their
sources. Only style-linter warnings.

### The one-particle base (`FockPackaging.lean`)

- `shellLp m hm := Lp ℂ 2 (massShellMeasure m hm)`, the corpus's
  mass-shell one-particle space.
- `shellU1 m hm (g : RPoincare) : shellLp m hm ≃ₗᵢ[ℂ] shellLp m hm`,
  the one-particle representation, built from the corpus's
  measure-preservation window theorem.
- `shellONB (m) (hm) : HilbertBasis ℕ ℂ (shellLp m hm)` — the
  **concrete** orthonormal basis: normalized Gaussian-polynomial
  patches on the mass shell, transported along the shell
  parametrization `shellParamEquiv : EuclideanSpace ≃ᵐ massShell`.
  Concreteness is load-bearing: the kernels below are matrices in
  *this* basis, and separability
  (`separableSpace_shellLp`) plus infinite-dimensionality
  (`not_finiteDimensional_shellLp`) come from it.
- `shellU1_translation_tendsto`: strong continuity of the
  translation subgroup at the identity, transported from the
  discharged one-particle input.

### The packaged representations (both statistics)

For every one-particle unitary `W` on `shellLp m hm`:

- Bosonic: `gammaFock m hm W : BosonicFockLim ≃ₗᵢ[ℂ] BosonicFockLim`.
- Fermionic: `gammaFockF m hm W : FermionicFockLim ≃ₗᵢ[ℂ] FermionicFockLim`.

and the packaged Poincaré actions

- `gammaFockU1 m hm (g : RPoincare)`, `gammaFockFU1 m hm (g : RPoincare)`,

satisfying, in both statistics, all T1:

- **Representation law** (`gammaFockU1_mul`, `gammaFockFU1_mul`):
  `Γ(U₁(g₁ * g₂)) = Γ(U₁ g₂) ⋙ Γ(U₁ g₁)` (order: see Fences).
- **Identity** (`gammaFockU1_one`, `gammaFockFU1_one`): `Γ(U₁ 1) = 1`.
- **Unitarity on each sector** (`gammaFock_mem_sectorClosure`,
  `gammaFockF_mem_sectorClosure`): `Γ(W)` preserves the closure
  of every `n`-particle sector.
- **Vacuum invariance** (`gammaFock_vacuum`, `gammaFockF_vacuum`):
  `Γ(W) Ω = Ω`.
- **Translation strong continuity**
  (`gammaFockU1_translation_tendsto`,
  `gammaFockFU1_translation_tendsto`): for every Fock vector `z`,
  `a ↦ Γ(U₁⟨a, 1⟩) z` is continuous at `a = 0` — transported
  from the one-particle input through finite-particle density.

## The port route

No abstract Γ functor is invoked. For each statistic the
operator is assembled from an explicit **limit kernel** in the
concrete basis `shellONB`:

- Bosonic kernel `gammaKernelLim`: normalized permanent of the
  entry matrix `Umat W j i = ⟪b j, W (b i)⟫` between limit
  configurations (Finsupp occupation profiles), with the
  bosonic norm factors.
- Fermionic kernel `gammaKernelFermLim`: determinant minor of
  the same entry matrix between finite occupation sets
  (`Finset ℕ`), no norm factors.

Route per statistic: (1) finite-level transport — at
configurations embedded from a finite level, the limit kernel
is the corpus's finite Γ kernel (rectangular permanent /
`minorDetRect`, resp. `minorDet`); (2) the three limit theorems
by exhaustion over embedded finite configurations — identity
(L1), column orthonormality (L3′), functor law (L2) — using the
finite Cauchy–Binet identities (`permanent_mul_expansion`,
`minorDet_mul`) at a common level and Parseval entry
convergence; (3) a column bound (B0) — bosonic: `(tot c)! / ∏(cᵢ!)`;
fermionic: `(S.card)!` via the Leibniz determinant bound —
giving ℓ² columns; (4) assembly on the finite-particle domain
by finite linear combinations of kernel columns, inner-product
preservation, and extension by density
(`LinearMap.extendOfIsometry`); the global adjoint identity
`Γ(W.symm) = Γ(W)*` by two closed-set density arguments; the
functor law on the whole space by a third.

One fermionic simplification worth recording: the rectangular
Cauchy–Binet is never needed. The corpus's square `minorDet_mul`
(sum over *all* intermediate configurations at one level)
suffices, because the exhaustion stages are taken at the growing
common level `max e D` with the outer configurations embedded
from their fixed factorization level `D`, and enumeration
coherence is supplied by the corpus's
`fermConfigEmb_orderEmbOfFin` plus the uniqueness of
`Finset.orderEmbOfFin` (lemma `minorDet_stage_tendsto`).

## Fences (in writing)

- **Group.** The group is the corpus's restricted Poincaré
  group `RPoincare` — the group of `shellU1`. No statement is
  made for any larger or differently-presented group.
- **Representation-law order (correction).** The window's
  phrasing `Γ(g₁ * g₂) = (Γ g₁).trans (Γ g₂)` is an
  anti-homomorphism under Mathlib's `LinearIsometryEquiv.trans`
  convention (`trans_apply`: the first factor acts first). What
  is proved is the corrected applied law
  `Γ(g₁ * g₂) = (Γ g₂).trans (Γ g₁)`, in both statistics. This
  is a correction to the window's display, not a narrowing of
  the mathematics.
- **Lorentz strong continuity is NOT part of this brick.** Only
  the translation subgroup's strong continuity is packaged,
  transported from the discharged one-particle input. The
  full-group statement is at the operator level (unitary
  representation, group law, sectors, vacuum) with no
  continuity claim for the Lorentz/rotation part; that item
  remains its own line (priced S–M).
- **Two-module shape.** The two statistics are packaged in
  separate modules (`FockPackagingBos`, `FockPackagingFerm`)
  under this one dossier, because the corpus's two
  second-quantization stacks cannot be co-imported in one
  environment (`numberOp`/`numberOp_basis` collide between
  `FermionicFock` and `BosonicAssembly`). Neither colliding
  stack is imported by the packaging modules; the rename that
  would lift the fence is priced S and is not in this brick.
  The statistic-free exhaustion helpers are therefore proved
  once per module.
- **Kill K4.** No `SymmetricAlgebra` (or any abstract
  second-quantization universal property) appears. The port is
  through the concrete basis only, as priced.

## Deviations

None beyond the fenced items above. The decomposition of the
gauntlet price — (i) `U₁` packaged as `≃ₗᵢ` (S), (ii) ONB +
separability (S), (iii) Γ-kernel at the limit (M, core),
(iv) representation law + vacuum + continuity assembly (S) —
was discharged as decomposed, for both statistics.
