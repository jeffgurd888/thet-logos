# The 36 extra order-one directions: numerical characterization

**Date:** 2026-09-27
**Status:** T4 numerical exploration only. Not a theorem, not a Lean proof.
**Method:** `explore_36.py`, `stage2.py`, `stage3.py`, `stage4.py` in this directory,
reusing the exact corrected Attack 4 machinery (24 real generators, 576 pairs,
same Γ/UJ/π° conventions). Results saved under `results/`.

## Setup and verification

The corrected Attack 4 scan found the order-one nullspace has real dimension
**46** inside the 272-dimensional admissible Dirac space (self-adjoint +
grading-odd + J-compatible). Ten of those dimensions are the conventional
one-generation SM directions (Re/Im of Yν, Ye, Yu, Yd, YR).

Procedure:
1. Reconstructed the 10 SM directions as 32×32 matrices from `sm_coeffs.npy`
   ⊗ `dbasis.npy`; orthonormalized (Gram off-diagonal ≤ 4.4e−16).
2. Projected each of the 46 nullspace matrices orthogonally off the SM
   10-space. SVD rank of the residuals: **36** (singular values 1.0 ×36,
   then ≤ 2.1e−14 — clean separation).
3. Built an orthonormal 36-basis `E36` (`results/E36.npy`).
4. Direct re-verification: max ‖[[D,X],Y°]‖ over all 36 × 576 generator
   pairs = **1.78e−14**. The 36 are genuinely in the order-one nullspace.

## Canonical structure of the full 46-dim nullspace

Write a grading-odd D in 8×8 blocks on H_L ⊕ H_R ⊕ H_L^c ⊕ H_R^c
(sectors [0:8], [8:16], [16:24], [24:32]):

| block | position | content on all 46 |
|-------|----------|-------------------|
| A | [0:8, 8:16] | Yukawa-like; image dim 16 real = **8 complex** params |
| B | [16:24, 24:32] | **B = conj(A)** exactly (max deviation 1.4e−15) |
| C | [0:8, 16:24] | **identically zero** (max 9.6e−15) |
| E | [24:32, 8:16] | Majorana-like; image dim 30 real = **15 complex** params |

16 + 30 = 46. ✓

Two structural facts are basis-invariant (hence canonical, not a labeling
choice):
- **Order-one forces C = 0.** The C block (left-particle ↔ left-antiparticle
  mixing) vanishes on every nullspace direction. Order-one is not vacuous —
  it genuinely excludes a whole 8×8 block.
- **The 36-dim SM-orthogonal complement decouples exactly** into
  A-pure (E = 0, 8 real dims) ⊕ E-pure (A = 0, 28 real dims).

## Family 1 — flipped Yukawas: 8 real dims (4 complex)

Basis-invariant allowed A-entries (max over orthonormal basis, threshold 1e−10):

```
              singlet:  s0=νR  s1=eR  s2=uR  s3=dR  s4=uR  s5=dR  s6=uR  s7=dR
  doublet I0 (lepton):   SMν     FLIP     .      .      .      .      .      .
                        FLIP    SMe      .      .      .      .      .      .
  doublet I1 (quark):     .       .     SMu   FLIP     .      .      .      .
                          .       .    FLIP    SMd     .      .      .      .
  doublet I2 (quark):     .       .      .      .     SMu   FLIP     .      .
                          .       .      .      .    FLIP    SMd     .      .
  doublet I3 (quark):     .       .      .      .      .      .     SMu   FLIP
                          .       .      .      .      .      .    FLIP    SMd
```

(SM = slots used by the 10 SM directions; FLIP = extra 8 entries.)

The 4 extra complex parameters, with **exact** color-universality
(cross-color ratios = 1.0000 ± 1e−14, same locking as the SM Yukawas):

| param | slot | meaning (relative to SM labeling) |
|-------|------|-----------------------------------|
| ỹν | A[0,1] | ν_L → e_R |
| ỹe | A[1,0] | e_L → ν_R |
| ỹu | A[2,3]=A[4,5]=A[6,7] | u_L → d_R (all 3 colors, one param) |
| ỹd | A[3,2]=A[5,4]=A[7,6] | d_L → u_R (all 3 colors, one param) |

Each is a full independent complex parameter (per-entry complex span is
2 real dims). This is the exact mirror image of the SM Yukawa pattern with
up↔down isospin components swapped. Algebraically these are the couplings
a **second Higgs doublet** (general 2HDM-type) would generate — same shape,
same color-locking, independent coefficients.

## Family 2 — exotic Majorana: 28 real dims (14 complex)

E is **symmetric** (max ‖E − Eᵀ‖ = 1.9e−15) on the whole E-pure space.
Basis-invariant allowed pattern (27 of 64 entries; symmetric, so 14 complex
params):

```
          s0=νR  s1=eR  s2=uR  s3=dR  s4=uR  s5=dR  s6=uR  s7=dR
  s0=νR     SM     X      X      X      X      X      X      X
  s1=eR     X      X      X      X      X      X      X      X
  s2=uR     X      X      .      .      .      .      .      .
  s3=dR     X      X      .      .      .      .      .      .
  s4=uR     X      X      .      .      .      .      .      .
  s5=dR     X      X      .      .      .      .      .      .
  s6=uR     X      X      .      .      .      .      .      .
  s7=dR     X      X      .      .      .      .      .      .
```

(SM = the YR ν_R↔ν̄_R slot, projected out; X = allowed extra.)

The 14 complex parameters:
- **E[e_R, e_R]** (1): electron Majorana mass — violates electric charge.
- **E[ν_R, x]** for x ∈ {e_R, 6 quark singlets} (7): ν_R cross-Majorana terms.
- **E[e_R, q]** for q ∈ {6 quark singlets} (6): electron–quark cross-Majorana.
- **Forbidden** (≤ 1.5e−15): all quark–quark Majorana entries, and any
  second ν_R↔ν_R entry.

Every allowed entry carries a full complex degree of freedom. The quark
singlets can Majorana-couple to lepton singlets but never among themselves —
a curious selection rule imposed by order-one with the M₃ generators.

## What order-one excludes (numerical, residuals quoted)

- C-block (particle↔antiparticle, same chirality): **forbidden**, ≤ 9.6e−15.
- Quark–quark Majorana: **forbidden**, ≤ 1.5e−15.
- Any A-entry outside the 16 straight+flipped slots: **forbidden**
  (48 of 64 A-entries vanish on all 46 directions).
- E[ν_R,ν_R] beyond the single SM slot: **forbidden**, ≤ 2.4e−16.

## Recognizable-structure checklist

- **Grading-odd + J-compatible + self-adjoint?** All 46 — including all 36 —
  satisfy these exactly (residuals ≤ 1e−14). This is by construction: the
  scan ran inside the 272-dim admissible space. So there is no
  "grading-even / J-violating" sub-family; the 36 are all Dirac-admissible
  in the algebraic sense. What distinguishes them is flavour/block
  structure, not algebraic character.
- **Right-handed-neutrino-like:** the 7 ν_R cross-Majorana terms are the
  closest analog — sterile-sector mixing, but extending to quarks.
- **Leptoquark-like:** the 6 e_R↔quark-singlet Majorana terms mix lepton
  and quark flavour (flavour-space leptoquark analogues, not gauge
  leptoquarks). The flipped Yukawas do *not* mix lepton↔quark — they stay
  inside their doublet's isospin flip.
- **W_R-like:** not applicable — W_R is an algebra/gauge-sector question
  (would need a right-handed H summand), not a D_F direction.
- **Pure-gauge artifacts:** no. These are Dirac-operator entries, not gauge
  parameters. They are also not flavour-relabelings of the SM 10: the
  flipped pattern cannot be relabeled into the straight pattern without
  moving the SM slots.

## Verdict

The 36 are **neither missing SM physics nor truncation artifacts**:

1. **Not missing physics.** Nothing in the 36 is needed for the one-generation
   SM — the 10 SM directions form a clean, decoupled subspace. The 36 are
   *additional* order-one-allowed directions.
2. **Not generator-truncation artifacts.** The 24 real generators span the
   full real Lie algebra C⊕H⊕M₃(C) (2+4+18 real dims); nothing was omitted
   (the i·I₃ correction changed nothing). The 36 survive the complete
   576-pair test.
3. **What they are:** the explicit boundary of what order-one *cannot*
   exclude. Order-one is a kinematic admissibility condition, not a
   selector. The actual selection of the SM's 10 directions uses
   independent physical input that order-one cannot see:
   - electric-charge conservation kills 27 of the 28 exotic-Majorana
     directions (e_R Majorana and all cross terms carry charge/color);
   - minimality / one-Higgs-doublet kills (or shelves as BSM) the 8
     flipped Yukawas;
   - the surviving exotic — none — is required.

The honest slogan: **order-one admits 46, physics selects 10.** The Lean
order-one proof (144/144 pairs, `smDirac_order_one`) certifies that the
imposed ansatz *satisfies* the axiom; it does not and cannot certify that
the axiom *implies* the ansatz. These 36 directions are the concrete
measure of that gap.

## GO / NO-GO: enlarge the ansatz before triplicating?

**Pros of enlarging** (carrying some/all of the 36 into the 3-gen ansatz):
- They are genuinely order-one-allowed; a "complete" finite geometry could
  claim the full 46-dim D_F.
- The 8 flipped Yukawas are legitimate BSM physics (2HDM-type), not noise.

**Cons of enlarging:**
- 27 of 28 exotic-Majorana directions violate EM charge / color — including
  them contradicts the SM gauge structure, which is non-negotiable input.
- Triplicating the full 46 gives ~138+ real parameters (plus
  generation-mixing), nearly all of it phenomenologically excluded.
- It confuses "allowed by one axiom" with "physical."

**Verdict: NO-GO on enlarging; GO on triplicating the SM ansatz as-is.**
The one-generation ansatz does not need enlargement — it needs its
selection principle stated honestly as *physical input beyond order-one*
(charge conservation, one Higgs doublet, phenomenology). Carry this
36-direction map as the documented boundary: when the 3-generation scan is
built, expect the same per-generation pattern (≈3×36 extra) plus
generation-mixing, and apply the same selection explicitly rather than
hoping order-one will do it.

## Caveats (T4)

1. Numerics, not proof: nullity via SVD (gap 0.36, residuals ≤ 2e−14);
   "forbidden" means ≤ 1e−14, "present" means ≥ 0.1 — clean separation, but
   still numerical.
2. The 10-vs-36 split depends on the conventional flavour labeling
   (which doublet is "lepton," which singlet is "ν_R"). The 46-dim space,
   the C=0 fact, the A/E decoupling, color-universality, E-symmetry, and
   the quark–quark Majorana ban are labeling-independent.
3. One generation only (ℂ³²). The ℂ⁹⁶ extension is untested; expect
   per-generation copies plus inter-generation structure.
4. "Charge-violating" judgments presuppose the SM charge assignment, which
   comes from the full (continuum × finite) geometry — independent input,
   not derived here.

## Files

- `explore_36.py`, `stage2.py`, `stage3.py`, `stage4.py` — analysis scripts
- `results/E36.npy` — (36,32,32) orthonormal extra-direction basis
- `results/SMo.npy` — (10,32,32) orthonormalized SM directions
- `results/EA_pure.npy` / `results/EE_pure.npy` — (8,32,32)/(28,32,32) pure-family bases
- `results/allowA.npy`, `results/allowE.npy`, `results/magA.npy`, `results/magE.npy` — support masks/magnitudes
- `results/E36_feats.npy` — per-direction block norms/ranks
