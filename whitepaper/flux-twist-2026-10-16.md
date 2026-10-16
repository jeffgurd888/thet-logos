# Flux-Twist Toy — Dossier (2026-10-16)

Labels (pre-agreed, holding): **T1 finite toy.** "Magnetism" appears only as flux twist
(Aharonov–Bohm in miniature). Explicitly NOT a bridge to real magnetism or Maxwell's
equations; NOT a Yang–Mills rung. Same shelf as TritGrading / SexagesimalClock.
Fleet position 1 of Jeff's 2026-10-16 order (unparked after the Γ(U) campaign closed).

## Deliverable
- `lean/ThetLogos/FluxTwist.lean` — **582 lines; 38 theorem/lemma declarations; 10 definitions.** New file only; no existing file edited.
- Definitions: `phaseOf`, `cyc`, `wpMat`, `boundaryPhase`, `twistedShift`,
  `uniformShift`, `gaugeMatrix`, `fourierVec`, `twistedFourierVec`, `hopping`.

## Verification
- Targeted build: **"Build completed successfully (3120 jobs)"** (re-run by the parent agent).
- Zero `sorry`/`admit`/`native_decide` in code.
- Axiom spot-checks (parent agent, 6 headlines): `twistedShift_unitary`,
  `twistedShift_add_two_pi`, `twistedShift_mul_gaugeMatrix`,
  `twistedShift_mulVec_twistedFourierVec`, `hopping_isHermitian`,
  `hopping_mulVec_twistedFourierVec` — ALL exactly
  `[propext, Classical.choice, Quot.sound]`.

## What was proved (all four core targets)
1. **Unitarity** — `twistedShift_unitary` (both S·Sᴴ=1 and Sᴴ·S=1), `uniformShift_unitary`,
   gauge-matrix unitarity, and `twistedShift_mem_unitary`, carried by general
   weighted-permutation-matrix lemmas.
2. **Flux periodicity** — `twistedShift_add_two_pi : S (θ + 2π) = S θ`.
3. **Gauge redistribution** — `twistedShift_mul_gaugeMatrix : S θ * G θ = G θ * Sᵘ θ`
   with the diagonal gauge matrix carrying phase θ·k/(n+1) on site k: the boundary
   twist IS the uniform twist, gauged.
4. **The ring hears the flux** — `uniformShift_mulVec_fourierVec` (spec form, plain
   Fourier vectors, eigenphase `phaseOf ((θ + 2πm)/(n+1))`) and
   `twistedShift_mulVec_twistedFourierVec` (boundary twist, same eigenphase).

## Stretch target — landed except the pre-priced item
- `hopping_isHermitian` PROVED; `hopping_mulVec_twistedFourierVec` PROVED with
  eigenvalue `−cos((θ + 2πm)/(n+1))`.
- The Gibbs-state modular-flow generation statement is NOT formalized; priced in the
  file header (needs matrix exponentials + finite-dimensional Gibbs modular theory).

## Recorded statement adjustments (from the build, kept honest)
- Sites are `Fin (n+1)`, so the cyclic successor and `Fin.last n` exist without
  side hypotheses; read `n + 1` as the site count.
- The boundary twist's eigenvectors are the flux-carrying `twistedFourierVec`:
  plain Fourier vectors fail the wrap bond by exactly the flux factor (checked by
  hand before building; documented in the file). Same eigenphase formula; consistent
  with gauge redistribution (unitarily equivalent operators share eigenvalues).
- Engineering: this project's files do not bind `π` to `Real.pi`; statements use
  `Real.pi` explicitly and `phaseOf (2π) = 1` is proved from double-angle formulas.

## Ledger labels
T1 finite toy. Buys: one proved instance of a physical detection principle — a ring
"hears" flux it never touches (eigenphases read θ mod 2π) — and the proved
gauge-equivalence of twist placements. Buys NO bridge to Maxwell, NO claim about
real magnetism, NO credit toward Yang–Mills or any Millennium item.
