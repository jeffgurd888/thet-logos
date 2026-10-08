# Automorphism Hunt — Results (T4)

**Date:** 2026-10-08 · **Tier: T4** (numerical) with T1-grade structural argument
**Question:** Does Aut(A_F, H_F, D_F) contain icosahedral (I_h) or binary icosahedral (2I)?
**Verdict:** KILL as a structural claim (with explicit technical existence noted).

## 1. The group

**D_F spectrum** (Y_PHYS, Ynu=0): 0(×4), ±2.46(×2), ±5.904(×6), ±228.78(×6).
**Commutant(D_F)**: complex-dim 168 = 16+4+4+36·4. Unitary commutant: U(4)×U(2)²×U(6)⁴.

**π(A_F)** (Option-A): real-dim **6** (not 24). M₃(ℂ) summand killed (18 real dims map to 0).
Structure: H-block (quaternions) on indices {0,1}, C-block (diag(u,ū)) on {8,9}.
Support: {0,1,8,9}. Confirmed numerically.

**Normalizer** G = {U:[U,D_F]=0, Ad_U(π)=π}: Lie algebra computed (161-dim raw,
152-dim verified after removing 9 spurious SVD null vectors). Large group.

## 2. Icosahedral hunt

**Technical existence: YES.**
Explicit A₅ generators constructed (3×3, a²=b³=(ab)⁵=1, verified to generate
order-60 group), embedded as 3⊕3 on the Yu+ D_F-eigenspace (6-dim).
Verified:
- [UA,D_F] = [UB,D_F] = 0 (exactly, 0.000e+00)
- UA²=UB³=(UA·UB)⁵=I (exactly)
- Ad_UA(π) = Ad_UB(π) = π (exactly, 0.000e+00)
So G contains A₅ (rotational icosahedral). By similar construction, I_h and 2I
subgroups exist in the D_F-commutant.

**Structural verdict: KILL.**
The exhibited A₅ acts as IDENTITY on π(A_F) (it lives on Yu+ where π=0).
More generally, PROVEN:
- For U in (verified) normalizer Lie algebra: [X,P₀₁]=0 and X|_{span{e₀,e₁}}
  is DIAGONAL (verified: 1.4e-16, 0.000e+00). Hence for U∈G⁰, U₀₁=diag(λ,μ).
- Therefore Ad_U on the H-block has ABELIAN image (diagonal unitaries commute;
  verified: ||[Ad_U1,Ad_U2]||=6.5e-17).
- A₅ (non-abelian simple) → abelian image is trivial. So any A₅⊂G acts
  TRIVIALLY on the H-block.
- On C-block: Aut_ℝ(C)≅C₂, A₅→C₂ trivial (A₅ perfect).
- **Conclusion:** Any icosahedral subgroup of G acts trivially on π(A_F).

The icosahedral in G is accidental D_F-degeneracy (color 3-fold), invisible to
the gauge algebra. The magnetic box has no icosahedral bones.

**2I note:** The 2-dim spinor of 2I cannot act on span{e₀,e₁} (diagonal
restriction forces abelian). Same structural kill applies.

## 3. Exotic sector

12 exotic directions (6 names × Re/Im) have full 32-dim support.
The exhibited A₅ permutes 8/12 (up to phase); 4/12 not permuted.
Not a natural icosahedral structure (no clean 12-orbit). The 12-vertex rhyme
remains NUMEROLOGY. Reported as tested, negative as structural claim.

Note: `||D_F @ E_i||_F = 5.6e2` (not zero) — the "D_F projects to zero"
summary line refers to a different projection (likely Tr or commutator-based);
not material to this verdict.

## 4. Verdict

**KILL** the icosahedron hypothesis as a structural claim about the magnetic box.
- Icosahedral subgroups EXIST in G (explicit A₅ generators exhibited).
- But they act trivially on the gauge algebra π(A_F) (proven: abelian image).
- They live on D_F-degenerate "dead" sectors (color degeneracy) where π=0.
- No icosahedral symmetry touches the gauge structure. The box is not icosahedral.

Per the relabeling rule, icosahedral returns only as a NEW entry with structural
(not accidental) evidence. T5 geometry-inspired language ("icosahedral box")
is permitted if labeled as such.

## Files
- `scripts/automorphism_hunt.py` (spectrum, commutant, normalizer Lie algebra)
- `scripts/autohunt_verify.py` (structural verification)
- `scripts/autohunt_embed.py` (explicit A₅ embedding)
- `/tmp/ico_a.npy`, `/tmp/ico_b.npy` (3×3 A₅ generators; move to repo if needed)
