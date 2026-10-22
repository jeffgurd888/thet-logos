# GibbsSpan — Bridge Span (a): STANDS (T1)

**Date:** 2026-10-22 · **Module:** `lean/ThetLogos/GibbsSpan.lean`
(namespace `ThetLogos.GibbsSpan`) · **Charter:**
`whitepaper/bridge-landing-pad-2026-10-20.md` §4 (Schrödinger row)
and §5 Span (a). Entered the ratified line 2026-10-20; launched on
the FluxClassification landing (line-up rule).

## Verdict

**STANDS (T1)** — the Schrödinger PARTIAL's Gibbs special case,
promoted to a named, finite, checked exhibit, in both pictures and
in the general-Hermitian form. **The pad's verdict is not upgraded:**
the general Schrödinger equation for an independent Hamiltonian
remains **NO SEAT**; what lands is exactly the special case, with
the fence on the module's face.

21 strict theorem/lemma declarations, 5 defs, 0 `@[simp]`, 0 sorry,
0 admits, 0 axiom declarations. Parent-verified: candidate
byte-identical to the built scratch source (md5
`812282cc9e0310076a682b16a20c542e`); own comment-stripped scan
21/0/0/0; own recompile exit 0; in-tree `lake build
ThetLogos.GibbsSpan` green on the exact shipped text (3,584 jobs,
`.olean` present); `#print axioms` on all 21 theorems — exactly
`[propext, Classical.choice, Quot.sound]`. **No route through the
quarantined `kms_identity_diagonal` sorry.**

## What is proved

1. **The built K of a Gibbs state** (`diagModularK_gibbsWeightsE`):
   for general real energies E,
   `diagModularK (gibbsWeightsE β E logZ) = (β : ℂ) • diagonal E +
   (logZ : ℂ) • 1` — K = βH plus the scalar free-energy term, **on
   the face, never dropped**. (The corpus's earlier
   `gibbsDiagWeights` is the E = λ² case.)
2. **Modular flow = rescaled time evolution**, both pictures:
   - Eigenbasis: `diagFlow_gibbsWeightsE` — the built diagonal flow
     of the Gibbs state is the Hamiltonian flow at time β·s.
   - Matrix headline: `gibbs_modularFlow_eq_heisenbergFlow` — for
     Hermitian H, `modularFlow ((β : ℂ) • H + logZ • 1) s A =
     heisenbergFlow H (β * s) A`, where the evolution is explicitly
     built: `evolutionUnitary H t := exp(−itH)` (proved unitary) and
     `heisenbergFlow H t A := U(t)ᴴ A U(t)`.
   - Packaged exhibit: `gibbsClockOf β E` is a genuine `ThermalClock`
     whose K is Target 1's matrix and whose flow is the laboratory
     flow at β·s. `gibbsState_diagonal` identifies the KMSBridge
     matrix Gibbs state with the diagonal construction;
     `gibbsState_densityFlow_stationary` — the Gibbs state is
     stationary under its own Schrödinger-picture evolution.
3. **General Hermitian H in full**, via HermitianReduction's
   exp-conjugation — no hand diagonalization. Headline finding,
   stated as a theorem with the sign on its face:
   `modularFlow_eq_genFlow_neg` — the corpus's two flow conventions
   (`modularFlow` by exp(+isK); the eigenbasis flows by ρ^{is})
   differ by exactly s ↦ −s, the K = −ln ρ sign.
   `gibbs_flow_eigenbasis` and `gibbs_two_pictures` give the Gibbs
   flow in the eigenbasis in both pictures, in agreement, sign
   included.

## Fences and the one named remainder

- Gibbs states only, on the header and every headline docstring;
  ħ appears in no statement (corpus units ħ = 1).
- **R-GS1** (named remainder, not a narrowing): at matrix level the
  generator is identified as −ln(gibbsState) via the diagonal route
  (`gibbsState_diagonal` + transport), because the corpus has no
  matrix logarithm — HermitianReduction's standing remainder R2,
  inherited unchanged.

## Census effect

Program census moves 3,522 → **3,543 strict** (3,562 → **3,583**
attribute-inclusive), 126 → **127 counted modules**.
