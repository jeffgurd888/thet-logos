# Pitch 2, Campaign A — Dossier (2026-10-16)

Greenlit by Jeff 2026-10-16 on the scoping's §6 landing definition (cuts held:
Task 3b rectangular functoriality and Task 7 spectral gap NOT attempted).
Scoping: `whitepaper/pitch-2-infinite-mode-scoping-DRAFT-2026-10-16.md`.

## Verdict
**Tasks 0–2 PROVED IN FULL, both statistics** — exceeding the scoping's acceptable
partials on two points: coherence is the GENERAL form (all d ≤ e ≤ f), not just
successive steps; and finite-to-finite embeddings WITH the cocycle are proved,
not merely embeddings into the limit.

## Deliverables (923 lines total; new files only)
- `lean/ThetLogos/FockLimit.lean` (186 lines; 6 theorems, 4 defs) — the shared
  machine Mathlib lacks: `onbEmb`, a linear-isometry constructor from a source
  Hilbert basis + target orthonormal family; density of finite-support vectors
  in constant-ℂ `lp` spaces.
- `lean/ThetLogos/FermionicLimit.lean` (341 lines; 26 theorems/lemmas, 10 defs).
- `lean/ThetLogos/BosonicLimit.lean` (396 lines; 29 theorems/lemmas, 12 defs).
- Split forced, verified by the parent agent: `FermionicFock` and `BosonicFock`
  cannot share an environment (both define `ThetLogos.adag`).

## Verification (parent agent, firsthand)
- Builds: `Build completed successfully (2456 jobs)` for the limit modules.
- Zero `sorry`/`admit`/`native_decide` in code.
- Axiom checks on 9 headlines (`onbEmb_apply`, `lp_single_span_topologicalClosure`,
  `fermConfigEmb_trans`, `fermConfig_factor`, `fockEmbLim_basis`, `fockEmb_cocycle`,
  `configEmb_trans`, `fockEmbBosLim_basis`, `DomLim_topologicalClosure`) — ALL
  exactly `[propext, Classical.choice, Quot.sound]`.

## Content
- Task 0: configuration inclusions (bosonic `Finsupp.embDomain` over `Fin.castLEEmb`;
  fermionic `Finset.map`), general coherence (a new `embDomain_trans` helper —
  Mathlib has none), limit cocycles, and factorization (every limit configuration
  lives at a finite level).
- Task 1: limit spaces `lp` over `ℕ →₀ ℕ` / `Finset ℕ`; orthonormal bases via
  `lp.single`; vacua; finite-particle domains; sectors. BONUS, groundwork only:
  density of both limit domains proved (an ingredient of Task 4a; the union
  characterization of 4a is Campaign B's, not claimed here).
- Task 2: linear isometries into the limits AND finite-to-finite, all from `onbEmb`;
  basis action, vacuum compatibility, domain compatibility, sector preservation,
  both cocycles.

Labels: T1. Free theory, finite-particle domains. This campaign builds the tower
and the limit spaces ONLY — no Γ-identification, no dΓ in the limit, no gap
statement (Campaign B). Not interaction, not continuum, not the Yang–Mills gap.
Program total after this campaign: 1,709 declarations (1,648 + 61).
