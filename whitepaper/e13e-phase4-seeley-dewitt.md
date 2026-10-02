# E13-E Phase 4: Product Space Seeley–DeWitt Expansion

*E13-E Phase 4, commissioned 2026-10-02 under the temporary §8 lifting
(SA freeze + K2/H22 quarantines lifted for this computation only).
Tier-2 hand computation. LOCAL — not pushed.*

## 0. What this computes, and what it does not

Computes the heat-kernel coefficients a₀, a₂, a₄ of the product operator

    D_A² := D_{M₄}² ⊗ I₂ ⊗ I₃₂  +  I₄ ⊗ D_{S¹_β}² ⊗ I₃₂  +  I₄ ⊗ I₂ ⊗ (D_F^{(A)})²

on M₄ × S¹_β × F₃₂, where D_{M₄} is the spin Dirac on a closed Riemannian
spin 4-manifold, D_{S¹_β} the circle Dirac (eigenvalues 2πn/β), and
D_F^{(A)} = D_F + A + JAJ⁻¹ the fluctuated finite Dirac (gauge + Higgs).
The three summands pairwise commute, so D_A² is a generalized Laplacian and
its heat trace factorizes. The deliverable is the exact R–|H|² cross term in
a₄ (the ξR|H|²-type coupling), derived with every step shown.

Note on the commissioned formula "D_A = D_M ⊗ I₃₂ + γ₅ ⊗ D_F^{(A)}": γ₅ is
the M₄ chirality. The S¹_β factor enters through the standard even×odd
product D_{M₄×S¹} = D_{M₄}⊗I + γ₅⊗D_{S¹} ({D_{M₄},γ₅}=0 kills the cross term),
so D_{M₄×S¹}² = D_{M₄}²⊗I + I⊗D_{S¹}², and D_A² above is the resulting total.
This is the standard finite-temperature product construction.

Does NOT: predict anything experimental, identify exotic directions with
particles, touch the frozen SA program beyond this computation, or claim any
continuum physics beyond this explicit product heat kernel. Tier-5 readings
are labeled §6.

## 1. Product structure (exact)

Since the three summands of D_A² commute,

    K_total(t) := Tr(e^{-tD_A²}) = K_{M₄}(t) · K_{S¹_β}(t) · K_F(t),

with K_{M₄}(t) = Tr(e^{-tD_{M₄}²}), K_{S¹_β}(t) = Tr(e^{-tD_{S¹}²}),
K_F(t) = Tr_{ℂ³²}(e^{-t(D_F^{(A)})²}).

Small-t expansions (all verified §3):
- K_{M₄}(t) = (4πt)^{-2}[A₀ + A₂t + A₄t² + O(t³)], A₀ = 4Vol(M₄),
  A₂ = -(1/3)∫_{M₄}R  (anchor A2, corrected — see §3),
  A₄ = standard Gilkey invariant.
- K_{S¹_β}(t) = Σ_{n∈ℤ}e^{-t(2πn/β)²} = (β/√(4πt))(1 + O(e^{-β²/4t}))
  (Poisson; anchor A3). Only the β(4πt)^{-1/2} prefactor contributes to the
  power series; spin structure (periodic/antiperiodic) is irrelevant to it.
- K_F(t) = Σ_{k≥0}C_k t^k (entire: finite dimension),
  C_k = (-1)^k/k! · Tr((D_F^{(A)})^{2k}).

Hence, with the 5D power counting K_total = β(4πt)^{-5/2}[a₀ + a₂t + a₄t² + …]:

    a₀^{tot} = β·A₀·C₀,
    a₂^{tot} = β·(A₂C₀ + A₀C₁),
    a₄^{tot} = β·(A₄C₀ + A₂C₁ + A₀C₂).                      (★)

## 2. Finite traces (numerical + analytic, both agree)

D_F from `finite_thermal_flow.build_H` / `common.DF_oneGen`, Y_PHYS =
{Ynu:0, Ye:0.010, Yu:0.93, Yd:0.024}, VEV = 246 GeV (inputs, §7).

- C₀ = Tr(I₃₂) = 32.
- T₂ := Tr(D_F²) = 628525.95 GeV² (numerical, 28 nonzero eigenvalues).
  Analytic: 4·VEV²·a, a = Σc_fY_f² = 2.5969 → 628525.95. Agree to 12 digits.
- D_F ∝ VEV exactly (verified: D(2·VEV) = 2·D(VEV) to 1e-12; C=E=0 so no
  vev-independent pieces).
- Higgs fluctuation: A(H⁰) = diag(Y_f)·√2·H⁰·(VEV/v) in the H_L→H_R block
  (buildDirac A-block; B = conj(A)). Verified numerically:
  Tr(D_Φ(H⁰)²) = (2T₂/v²)|H⁰|² with ratio 1.00000000 at H⁰ = 50,123,174,300.
  By SU(2)_L invariance of the trace, Tr(D_Φ(H)²) = (2T₂/v²)|H|² for the full
  doublet. Hence C₁ = -Tr(D_Φ²) = -(2T₂/v²)|H|².
- C₂ = (1/2)Tr(D_Φ⁴) (numerical from eigenvalues; |H|⁴ sector, no R).
- Gauge 1-forms (u(1), su(2), su(3) from sector_bases): contribute to
  Tr(D_Φ²) only H-independently (Tr(A_g²)) or as |H|²·(gauge)² cross terms —
  they do NOT enter the R|H|² cross term. Only the Higgs doublet does.

## 3. Sanity anchors (all pass; A2 corrected the analysis)

- **A1** (scalar Laplacian, S⁴ r=1): fitted A₀ = 26.3188 (Vol = 8π²/3),
  A₂ = 52.6513 ((R/6)Vol). The R/6 anchor reproduces exactly. PASS.
- **A2** (spin Dirac, S⁴ r=1, exact spectrum ±(k+2), mult 4·C(k+3,3)):
  fitted A₀ = 105.2758 (4Vol), A₂ = -105.2748 = -(1/3)∫R.
  The recalled formula +(5/3)∫R was WRONG; the Richardson slope is stable to
  5 digits at -105.26. Correct statement: in the E-convention
  (P = ∇*∇ - E), E_M = -R/4 for the spin Dirac, giving A₂ = -(1/3)∫R.
  This anchor changed the cross-term sign AND magnitude (5/3 → 1/3). PASS.
- **A3** (S¹_β): (1/β)K_{S¹}(t) → (4πt)^{-1/2} = 0.282095 for
  β = 10,20,40,80 at t=1. PASS.
- **a₀ rank**: a₀^{tot} = β·(4Vol)·32 = 128·β·Vol(M₄); rank 128 = 4(spin)×32.
  The spin factor 4 verified by A2's A₀ fit. PASS.

Scripts: `python/thet_logos/e13e_phase4_anchors.py` (deterministic).

## 4. The R–|H|² cross term (deliverable)

In (★), R appears only in A_{2j≥2} and |H|² only in C_{k≥1}. Therefore the
monomial R|H|² occurs in a₄ in EXACTLY ONE place: A₂·C₁. No other source, no
cancellation possible. This is an exact algebraic statement.

    a₄^{tot} ⊃ β·A₂^{M₄}·[C₁^F]_{|H|²}
            = β·(-(1/3)∫_{M₄}R)·(-(2T₂/v²)|H|²)
            = +β·(2T₂/3v²)·|H|²∫_{M₄}R.                (†)

Numerically: 2T₂/3v² = 2(628525.95)/3(246)² = 6.9247 (dimensionless).

    a₄^{tot} ⊃ +6.9247·β·|H|²∫_{M₄}R,    |H| in GeV, R in GeV².

At the vev (|H|² = v²/2): a₄^{tot} ⊃ +β·(T₂/3)·∫R = +209508.7·β·∫_{M₄}R.

Dimensional check: [β]=M⁻¹, [|H|²]=M², [∫R]=M⁻² → M⁻¹ = [a₄^{tot}] ✓.

For the record, the other two coefficients explicitly (same conventions):
a₀^{tot} = 128·β·Vol(M₄),
a₂^{tot} = β·[-(32/3)∫_{M₄}R  -  (8T₂Vol(M₄)/v²)|H|²].
The |H|² term in a₂^{tot} is negative-definite (tachyonic Higgs mass term,
correct EWSB direction); numerically a₂^{tot} = -β·[10.667·∫R + 83.09·Vol·|H|²]
(|H| in GeV). a₄^{tot} = β·[A₄^{M₄}·32  +  (†)  +  4Vol(M₄)·½Tr(D_Φ⁴)].

Cross-validation (Tier-5 remark, not a gate): in standard Yukawa conventions
(a_ours = a_std/2), (2T₂/3v²) = (4/3)a_std. The Chamseddine–Connes spectral
action gives the R|H|² term with |ξ₀| = 1/12, i.e. a₄-coefficient (4/3)a in
the same conventions — magnitude match is exact; the sign is GR-convention
dependent. This agreement (after the A2 correction) strongly corroborates the
derivation. It is NOT claimed as a prediction.

## 5. Kill-condition verdicts

- **K1** (no well-defined R–⟨Φ⟩ cross term / cancellation): NOT TRIGGERED.
  Proved above: the monomial occurs in exactly one convolution term; the
  coefficient is nonzero (T₂ > 0 because Yu = 0.93 ≠ 0) and finite. PASS.
- **K2** (KO-dimension mismatch / S¹_β incompatible with finite real
  structure): NOT TRIGGERED for this deliverable. The heat coefficients
  depend only on D_A² as a generalized Laplacian (sum of three commuting
  pieces) — unambiguously defined; KO-dimension plays no role in them.
  Noted honestly: factors carry KO-dims 4 (M₄), 1 (S¹), 6 (F); the formal
  product real triple is KO-dim 3 mod 8, whose NCG product-Dirac needs the
  odd-dimensional product construction — not required for Seeley–DeWitt.
  The S¹_β real structure acts on a separate tensor factor; no
  incompatibility with J_F arises at the heat-kernel level. PASS with caveat.
- **K3** (inputs beyond proved triple + standard formulas): NOT TRIGGERED.
  Inputs used: D_F (Tier-1 triple), Y_PHYS + VEV (listed inputs, §7),
  Gilkey product/convolution formulas (Tier-2 standard), Higgs
  parametrization via inner fluctuations (Tier-2 standard NCG, verified
  numerically §2). No invented couplings, no fitted parameters. PASS.

**Phase 4 verdict: PASS.** The cross term exists, is well-defined, and is
derived: (†).

## 6. Tiering

- a₀/a₂/a₄ derivations, anchors, trace identities: Tier-2 (hand computation,
  every step checkable; scripts deterministic).
- The |ξ₀| = 1/12 magnitude agreement: Tier-5 remark (uses external
  literature normalization; not a validation gate, not a prediction).
- Any reading "the theory predicts ξ = …" for experiment: Tier-5
  interpretation, explicitly not made here.
- Nothing in this document is Tier-1 or an experimental prediction.

## 7. Assumptions (explicit, complete)

1. D_A² defined as the sum of three commuting generalized Laplacians (§0);
   not as the square of a strict NCG product Dirac (odd-dimensional subtlety
   noted in K2).
2. Y_PHYS = {Ynu:0.0, Ye:0.010, Yu:0.93, Yd:0.024}, VEV = v = 246 GeV —
   inputs (physical-ish), not derived. If they change, T₂ and the cross-term
   number change accordingly; the FORMULA (†) does not.
3. Higgs enters the finite Dirac by VEV → √2|H| scaling in the mass blocks
   (verified exact §2; SU(2) extends neutral direction to full doublet).
4. S¹_β periodic spin structure (antiperiodic gives identical coefficients).
5. M₄ closed Riemannian spin 4-manifold (S⁴ used for numerics).
6. Only the Higgs doublet enters the R|H|² cross term; gauge fluctuations
   documented as non-contributing (§2).
7. Scope: this computation only. The §8 lifting expires with this verdict;
   the SA freeze and K2/H22 quarantines are otherwise intact.

## 8. Forbidden-claims audit

No E₁–E₁₂ physical identifications. No `Nullspace22.lean`/`MatrixDecomp.lean`
vocabulary (canonical files only, and none were needed). No claim beyond
Phase 4's scope. No experimental prediction. No continuum claim beyond this
explicit product heat-kernel computation. The §8 re-freeze condition is met
by this verdict.
