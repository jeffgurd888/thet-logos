# Rung 10 — Bosonic Second Quantization (2026-10-16)

**Verdict: Task 1 STANDS · Task 2 STANDS · Task 3 PARTIAL.**

**Completion addendum (2026-10-16, later the same day): Task 3 is CLOSED.** The Γ(U) functor campaign proved both priced obstructions — the fiber-permanent counting lemma and the permanent Cauchy–Binet identity for repeated indices — with their consequences (Γ(1) = 1, the diagonal action, multiplicativity, the unitarity package): `lean/ThetLogos/BosonicGammaFunctor.lean`, 1,161 lines, 42 T1 theorems + 8 definitions, zero sorrys, targeted build green (2,455 jobs), headline axiom checks exactly `[propext, Classical.choice, Quot.sound]`. **Rung 10 now STANDS whole.** Full record: `whitepaper/gamma-functor-campaign-2026-10-16.md`. The PARTIAL verdict below stands as the historical record of the rung's first landing.

Two new modules, `BosonicFock.lean` / `BosonicAssembly.lean` unmodified,
`satisfiesDestruction` untouched:

- `lean/ThetLogos/BosonicSecondQuant.lean` — 531 lines, **25 T1 theorems + 5 definitions**, zero sorrys.
- `lean/ThetLogos/BosonicGamma.lean` — 215 lines, **6 T1 theorems + 8 definitions**, zero sorrys.

**Rung 10 total: 31 T1 theorems + 13 definitions.**

Labels that apply to everything below: **finite modes** (`Fin d`), operators on the
**dense domain** `Dom d` (finite-particle vectors), **free bosonic theory**. This is
**not** the interacting Yang–Mills theory and **not a Millennium claim**. The Task 2
gap is *derived* for the free Hamiltonian at finite modes — exactly the bosonic analog
of Rung 9's fermionic Task 3, with the same scope.

---

## Task 1 — bosonic dΓ lift · STANDS

`dgammaBos d M = ∑ i, ∑ j, (M i j) • ((adag d i) ∘ₗ (ann d j))` on `Dom d`, mirroring
the fermionic `dgamma` of Rung 9, with the Rung 8B domain adjoint relations in place of
finite-dimensional adjoints. All of the brief's required identities are proved:

| Theorem | Content |
|---|---|
| `dgammaBos_adjoint` | `⟪dΓ(M) x, y⟫ = ⟪x, dΓ(Mᴴ) y⟫` on `Dom d` (inner-product form) |
| `dgammaBos_one` | `dΓ(1) = numberOp` — connects to Rung 8B's number operator |
| `dgammaBos_vacuum` | `dΓ(M)` annihilates the vacuum |
| `dgammaBos_basis_diag` | `dΓ(diag λ) e_c = (∑ i, λ i * (c i : ℂ)) • e_c` |
| `dgammaBos_mem_domSector` | `dΓ(M)` preserves every sector `domSector d n` |
| `domSector_coe` | `domSector d n` coerces into Rung 8B's Fock sector `sectorSub d n` |

Supporting: `ann_basis_dom` (annihilation action on basis vectors in `Dom`), 
`numberOp_mode_dom`, `dgammaBos_term_dom` (a monomial `adag i ∘ₗ ann j` sends `e_c`
to a scalar multiple of `e_{c − δj + δi}`), `dgammaBos_term_mem_domSector`; definitions
`dgammaBos`, `domSector`.

## Task 2 — bosonic free Hamiltonian gap, DERIVED · STANDS

Free theory, finite modes: `freeHamiltonianBos d lam = dΓ(diag (λ : ℂ))`, `λ i : ℝ`.

| Theorem | Content |
|---|---|
| `freeHamiltonianBos_basis` | `H e_c = ((∑ i, λ i * (c i : ℝ) : ℝ) : ℂ) • e_c` |
| `freeHamiltonianBos_coord` | coefficient form: `(boseRepr (H x)) c = eigenvalue(c) * (boseRepr x) c` |
| `freeHamiltonianBos_vacuum` | vacuum eigenvalue `0` |
| `freeHamiltonianBos_selfadjoint` | `⟪H x, y⟫ = ⟪x, H y⟫` on `Dom d` |
| `free_gap_dichotomy_bos` | every basis eigenvalue is `0` or `≥ Δ` when each `λ i = 0 ∨ Δ ≤ λ i` |
| `freeHamiltonianBos_eigenvalue_gap` | every eigenvalue of `H` on a nonzero `ψ ∈ Dom d` is a basis eigenvalue, hence `0` or `≥ Δ` |
| `freeHamiltonianBos_expectation` | `⟪x, H x⟫ = ((∑_c ‖x_c‖² * eigenvalue(c) : ℝ) : ℂ)` |
| `freeHamiltonianBos_expectation_nonneg` | `0 ≤ (⟪x, H x⟫).re` for `λ ≥ 0` |

Route: a coefficient-space lift `dgammaC` with `repr_dgammaBos` (transport along
`boseRepr`), `dgammaC_number_mode`, `dgammaC_diag_single`, and the coordinate identity
`dgammaC_diag_apply` (by `Finsupp.induction`); the operator eigenvalue gap is extracted
at a nonzero coefficient, as in Rung 9. `dom_expand` (every `x ∈ Dom d` is the finite
sum of its basis components) powers the expectation formula.

## Task 3 — bosonic Γ(U) · PARTIAL

The fermionic Γ of Rung 9 used determinant minors over subsets. Bosons need
**permanent** minors over occupation configurations (repetitions allowed). This file
builds the lift and proves what the definition gives directly:

Definitions: `configsOfTot` (the finite set of configurations of total count `n`,
via coordinate functions into `Fin (n+1)`), `configEnum` (sorted enumeration of the
occupied positions, from Mathlib's `Finsupp.toMultiset`), `perMinor` (permanent of
the enumerated-entry matrix; `0` across different total counts), `normFactor`
(`√(∏ i, (c i)!)`), `gammaKernel` (permanent minor over the normalization product),
`gammaKernelFinsupp`, `gammaC` (linear extension on coefficient space), `gammaBos`
(transport to `Dom d`).

| Theorem | Content |
|---|---|
| `mem_configsOfTot` | `c ∈ configsOfTot d n ↔ tot c = n` |
| `perMinor_of_tot_ne` | permanent minors vanish across different total counts |
| `gammaBos_apply` | `Γ(M) x = boseEquiv (gammaC M (boseRepr x))` (definitional) |
| `gammaBos_apply_basis` | `Γ(M) e_c = ∑_{c' : tot c' = tot c} gammaKernel M c' c • e_{c'}` |
| `gammaBos_sector` | `Γ(M) e_c ∈ domSector d (tot c)` |
| `gammaBos_vacuum` | `Γ(M)` fixes the vacuum (the `Fin 0` permanent is `1`) |

**Priced remainder — the two obstructions, named exactly:**

1. **`Γ(1) = 1` and the diagonal action** `Γ(diag λ) e_c = (∏ i, λᵢ^{c i}) • e_c` both
   reduce, for this kernel, to the **fiber-permanent counting lemma**: the permanent
   of the fiber-indicator matrix `a b ↦ (if configEnum c a = configEnum c b then 1
   else 0)` equals `∏ i, (c i)!` — it counts the permutations of `tot c` positions
   that preserve each mode's fiber. A finite but genuine counting argument about
   `Matrix.permanent` over repeated indices; not in Mathlib at this toolchain.
2. **Multiplicativity `Γ(M)Γ(N) = Γ(MN)` and unitarity** need a **permanent
   Cauchy–Binet identity for repeated indices**: expanding `per (M N)` over
   intermediate index functions `Fin (tot c) → Fin d` and grouping them by their
   multiset image, with the `1/∏ c'!` weights matching the kernel normalization
   exactly. This is the bosonic analog of Rung 9's rectangular Cauchy–Binet campaign
   (proved from scratch for determinants); the permanent version with multiplicities
   is a separate campaign of comparable size.

Until (1) lands, even `Γ(1) = 1` is unproved for this definition — so Γ is recorded
as a *candidate lift with its kernel formula, vacuum, and sector preservation
proved*, not as a verified functor. No statement was weakened to get here.

---

## Verification evidence (2026-10-16)

- Targeted builds green: `lake build ThetLogos.BosonicSecondQuant` (2,453 jobs),
  `lake build ThetLogos.BosonicGamma` (2,454 jobs). Root `lake build` green
  (3,325 jobs). New modules are not yet in the root `ThetLogos.lean` import list,
  per the same staging as Rungs 8B/9.
- Sorry/admit sweep: `grep -c sorry` = 0 in both new files; no `admit`.
- Axiom spot-checks (`#print axioms`, scratch file, not committed) — all exactly
  `[propext, Classical.choice, Quot.sound]`, no `sorryAx`:
  Tasks 1–2: `dgammaBos_adjoint`, `dgammaBos_one`, `dgammaBos_basis_diag`,
  `dgammaBos_mem_domSector`, `domSector_coe`, `freeHamiltonianBos_basis`,
  `freeHamiltonianBos_selfadjoint`, `freeHamiltonianBos_eigenvalue_gap`,
  `freeHamiltonianBos_expectation`, `freeHamiltonianBos_expectation_nonneg`.
  Task 3: `mem_configsOfTot`, `perMinor_of_tot_ne`, `gammaBos_apply_basis`,
  `gammaBos_sector`, `gammaBos_vacuum`.
- Local commits: Tasks 1–2 `d6f4656`; Task 3 + this dossier in the following commit.
  Not pushed (per brief).

## Priced remainder beyond this rung

- Bosonic Γ multiplicativity/unitarity and `Γ(1)`/diagonal action: the two
  permanent identities above.
- Infinite-mode limit (no longer `Fin d`): untouched, needs new analysis.
- Symⁿ(H) unitary-equivalence / permanent formula in Mathlib's tensor API: still
  blocked upstream (as priced at Rung 8).
- Continuum limit, interacting theories, Yang–Mills: the standing frontier; nothing
  in this rung touches them.
