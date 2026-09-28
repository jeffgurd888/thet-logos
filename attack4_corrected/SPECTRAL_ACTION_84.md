# Spectral Action over the 84-Direction Selected Dirac Space

**Status:** T4 numerical. Not a Lean theorem. 2026-09-27.
**Scope:** finite-triple trace contribution only — inner fluctuations (gauge
bosons) are set to zero; the manifold factor ∫d⁴x√g is the standard
almost-commutative product, not computed here.

---

## 1. Setup

D_96 is the three-generation Dirac ansatz (`build_dirac3` in
`spectral_action_84.py`, copied from `attack4_3gen.py`), parameterized by the
84 physically selected directions:

- Y_ν, Y_e, Y_u, Y_d: arbitrary complex 3×3 (72 real),
- M_R: complex **symmetric** 3×3 (12 real).

Symmetry of M_R is required for J-compatibility (attack4_3gen sanity check:
non-symmetric M_R gives ‖UJ conj(D) − D UJ‖ = 6.70). The E-block touches only
the (ν_R, ν_R) slot. Inner fluctuations are OFF: no gauge fields, no Higgs
fluctuation — this is the unfluctuated finite background.

The spectral action is Tr(χ(D²/Λ²)) = f_0 Λ⁴ a_0 + f_2 Λ² a_2 + f_4 a_4 + …,
with cutoff moments f_k kept symbolic. For the finite triple:

- a_0^F ∝ Tr(1),
- a_2^F ∝ Tr(D²),
- a_4^F ∝ Tr(D⁴),

up to the standard heat-kernel prefactors (normalization stated, not derived).

## 2. Structural formulas (derived, then verified)

Write D on 32 slots × 3 generations. D² has 36 nonzero 3×3 slot-blocks
(audited numerically — no others exist):

| Slot(s) | D² block |
|---|---|
| (p,p), p=0..7 | Y_p Y_p† |
| (16+p,16+p), p=0..7 | conj(Y_p Y_p†) |
| (8+p,8+p), (24+p,24+p), p=1..7 | Y_p† Y_p, conj(Y_p† Y_p) |
| (8,8) | Y_ν†Y_ν + M_R†M_R |
| (24,24) | conj(Y_ν†Y_ν) + M_R M_R† |
| (0,24), (24,0) | Y_ν M_R†, h.c. |
| (8,16), (16,8) | M_R† Y_νᵀ, h.c. |

with (Y_0,…,Y_7) = (Y_ν, Y_e, Y_u, Y_d, Y_u, Y_d, Y_u, Y_d) (color triplication).
Hence, with q(Y) = ‖YY†‖²_F = Tr((Y†Y)²):

**Tr(D²)** = 4·(‖Y_ν‖²_F + ‖Y_e‖²_F + 3‖Y_u‖²_F + 3‖Y_d‖²_F) + 2‖M_R‖²_F.

**Tr(D⁴)** = 4·[q(Y_ν)+q(Y_e)+3q(Y_u)+3q(Y_d)] − 2q(Y_ν)
+ ‖Y_ν†Y_ν + M_R†M_R‖²_F + ‖conj(Y_ν†Y_ν) + M_RM_R†‖²_F
+ 4‖Y_νM_R†‖²_F.

Also Tr(D) = Tr(D³) = 0 exactly (grading-oddness).

## 3. Numerical results

| Point | Tr(1) | Tr(D²) | Tr(D⁴) | rel. err (brute vs struct) |
|---|---|---|---|---|
| hierarchical | 96 | 2.201203e+04 | 2.016400e+08 | 0 (D²), 0 (D⁴) |
| random | 96 | 6.185265e+02 | 1.588117e+04 | 1.8e-16 (D²), 0 (D⁴) |
| mixed (CKM-like) | 96 | 1.501203e+04 | 3.750001e+07 | 1.2e-16 (D²), 0 (D⁴) |

- "hierarchical": diagonal Yukawas (up-type hierarchy to y_t=1), M_R =
  diag(10,30,100) — moderate seesaw (numerics; physical seesaw would be ≫).
- "random": seeded O(1) complex matrices, random symmetric M_R.
- "mixed": Yu, Yd conjugated by random unitaries (CKM-like mixing),
  M_R = 50·I_3. Tr(D²) ≈ 15000 = 2‖M_R‖²_F and Tr(D⁴) ≈ 3.75e7 = 2·3·50⁴
  confirm Majorana dominance analytically.
- CCM-style invariants at the hierarchical point: 𝔞 = 3.008201 ≈ 3y_t²
  (top dominance, as expected), 𝔟 = 3.000019 ≈ 3y_t⁴.
- ‖D*−D‖ = 0 at all points; Tr(D) = Tr(D³) = 0 to machine precision.

## 4. Heat-kernel reading and CCM comparison

With inner fluctuations turned on (not computed here), the standard reading:

- **a_2 → Higgs mass term**: coefficient ∝ −f_2 Λ² · 𝔞 · |H|², where
  𝔞 = ‖Y_ν‖²_F + ‖Y_e‖²_F + 3‖Y_u‖²_F + 3‖Y_d‖²_F is exactly the bracket in
  our Tr(D²) (up to our uniform factor 4 from the A+A†+B+B† block
  convention). Top dominance (𝔞 ≈ 3y_t²) reproduced numerically.
- **a_4 → Higgs quartic + gauge kinetic**: quartic ∝ f_4 · 𝔟 · |H|⁴ with
  𝔟 = q(Y_ν)+q(Y_e)+3q(Y_u)+3q(Y_d) matching our pure-Yukawa Tr(D⁴) bracket
  (same factor 4); gauge kinetic terms require the fluctuated Dirac and are
  not computed.
- **Majorana sector**: our 2‖M_R‖²_F ↔ CCM 𝔠 = Tr(MM*); our
  ‖M_R†M_R‖²_F-type terms ↔ 𝔡 = Tr((MM*)²); our 4‖Y_νM_R†‖²_F (the
  off-diagonal D² slot blocks) ↔ 𝔢 = Tr(MM* Y_ν*Y_ν). The monomial
  *structure* matches Chamseddine–Connes–Marcolli qualitatively; only the
  overall normalization (our factor 4 / 2 from block conventions) differs,
  and is stated, not hidden.

What is NOT claimed: no numerical prediction of the Higgs mass or the
cosmological constant — f_k are free cutoff moments, and the fluctuated
computation is not done.

## 5. Majorana-sector subtleties

- M_R symmetric is load-bearing: J-compatibility breaks otherwise (6.70
  residual in the attack4_3gen sanity check). Self-adjointness alone does
  not need symmetry (E† is coded as the adjoint) — J does.
- The E-block touches only (ν_R, ν_R); there is no (ν_R, e_R)-type mixing
  in the selected 84 (those live in the shelved/killed directions).
- Fermion-doubling / Pfaffian subtleties of the Majorana sector are not
  addressed at T4 scope; the computation is a straight trace.

## 6. Numerical artifacts caught (not laundered)

1. **First Tr(D⁴) formula missed the off-diagonal D² slot blocks**
   ((0,24) and (8,16) pairs): 5.9e-2 relative error at the random point.
   Fixed by including 4‖Y_νM_R†‖²_F. (The hierarchical/mixed points could
   not catch this — Y_ν is ~1e-10 there.)
2. **Slot-24 Yukawa part is conj(Y_ν†Y_ν), not Y_ν†Y_ν**: a hermitian-
   transpose slip in the hand derivation; 1.7e-3 residual at the random
   point. Fixed after block-by-block numeric audit.
3. Both fixes verified by an independent block audit on a fresh seed:
   all 36 nonzero D² slot-blocks match to 7.7e-15, zero unclaimed blocks.

Lesson recorded: the random O(1) point is the load-bearing test —
hierarchical points hide cross terms behind scale separation.

## 7. Honesty

- **T4 only.** Brute-force 96×96 traces + structural formulas verified
  numerically. No Lean theorem.
- **f_k free.** No Higgs-mass or cosmological-constant prediction.
- **Unfluctuated.** a_2/a_4 physical reading (Higgs mass/quartic, gauge
  kinetic) is the standard interpretation applied to our finite traces,
  not a new computation of the fluctuated action.
- **Imposed inputs.** The 84 parameters, three generations, and the E-block
  placement are physical input, as throughout.
- **Manifold factor.** Only the finite-triple traces are computed; the
  almost-commutative product with the manifold is standard and assumed.

## Files

- Script: `attack4_corrected/spectral_action_84.py`
- Checkpoint: `attack4_corrected/results3gen/spectral_action_ckpt.json`
- This report: `attack4_corrected/SPECTRAL_ACTION_84.md`
