# Pitch 2, Campaign B — Dossier (2026-10-16)

Scoping: `whitepaper/pitch-2-infinite-mode-scoping-DRAFT-2026-10-16.md` (§6 landing).
Campaign A dossier: `whitepaper/pitch-2-campaign-a-2026-10-16.md`.

## Verdict
**Tasks 3a, 4a, 5, 6 — PROVED, both statistics.** With Campaign A, the scoping §6
landing definition is met in full: **PITCH 2 STANDS.**

## Deliverables (1,692 lines; new files only)
- `lean/ThetLogos/FermionicLimitOps.lean` — 710 lines; 32 theorems/lemmas + 14 defs.
- `lean/ThetLogos/BosonicLimitOps.lean` — 982 lines; 48 theorems/lemmas + 17 defs.
- Campaign total: 80 theorems/lemmas + 31 definitions. Program total: **1,789**.

## Verification (parent agent, firsthand)
- Builds green: "Build completed successfully (3207 jobs)" across the pitch modules.
- Zero `sorry`/`admit`/`native_decide` in code (the one grep hit per file is header
  prose: "no `sorry`").
- Axiom checks on 8 headlines (`gammaFermRect_pad`, `fermDomLim_eq_iSup_range`,
  `dGammaLimFerm_compat`, `freeHamiltonianLimFerm_gap_of_orth`, `gammaBosRect_pad`,
  `DomLim_eq_iSup_map`, `dGammaLimBos_compat`, `freeHamiltonianLimBos_gap_of_orth`)
  — ALL exactly `[propext, Classical.choice, Quot.sound]`.

## Content
- **Task 3a (operator level — stronger than the scoped basis-wise landing):** the
  corpus Γ API is square-only, so a rectangular widening was ported verbatim
  (`minorDetRect`/`perMinorRect`, definitionally the square kernels by `rfl`), and
  the identifications proved: `gammaFermRect_pad` (whole-space operator equality,
  fermions) and `gammaBosRect_pad` (equality of domain maps — the honest bosonic
  landing, since bosonic Γ preserves domains, not whole spaces).
- **Task 4a:** union characterizations — `fermDomLim_eq_iSup_range` (bare range;
  fermionic levels are already domains) and `DomLim_eq_iSup_map` (domain-map form;
  the bare-range form is false for bosons, per the scoping's asymmetry), with
  density corollaries for the unions.
- **Task 5:** diagonal dΓ in the limit for both statistics, with basis eigenvalue
  formulas, finite-level compatibility as operator equalities, and the number
  operator as the `a ≡ 1` case.
- **Task 6 (Δ-general — stronger than the tasked Δ = 1):** the free gap survives at
  countably many modes: vacuum eigenvalue 0, the eigenvalue dichotomy for general
  Δ > 0, the orthogonality form at Δ = 1, self-adjointness on the domain.
  **Mandatory clause (in both module headers, verbatim): "gap in the
  eigenvalue-on-finite-particle-domain sense of Rungs 9–10; the spectral
  statement is priced, unattempted."** Task 7 was NOT attempted (pre-agreed cut);
  Task 3b likewise remains cut.

## What Pitch 2 bought (and did not)
The verified free theory now lives at **countably many modes**: limit Fock spaces
with orthonormal configuration bases, the Γ tower functorial, density/union
identity, diagonal dΓ with finite-level agreement, and the derived free gap.
Per the scoping's honesty line, standing whole it removes exactly one scope word
("finite modes" → "countably many modes"). It does NOT buy interaction (Pitch 3
has no starting module), does NOT buy continuum/Poincaré (Pitch 4 untouched),
and is not the Yang–Mills gap or any part of any Millennium statement.
