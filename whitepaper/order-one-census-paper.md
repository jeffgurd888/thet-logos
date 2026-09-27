---
title: "The Order-One Nullspace of the Standard Model Finite Spectral Triple: A 46/402 Census"
author: "Jeffrey Gurd"
affiliation: "Nexus Research (independent research)"
date: "2026-09-27"
version: "v1.0-draft"
status: "Draft for publication. Not peer-reviewed."
---

# The Order-One Nullspace of the Standard Model Finite Spectral Triple

## A 46/402 Census

## Abstract

We compute the full space of Dirac operators satisfying the order-one
condition for the fixed Standard Model finite spectral triple
(A_F = C (+) H (+) M_3(C), H_F = C^32): it is 46 real-dimensional per
generation, decomposing into the 10 conventional Yukawa/Majorana parameters,
8 flipped-Yukawa directions, and 28 exotic-Majorana directions. The
textbook uniqueness result (Chamseddine–Connes–Marcolli, Theorem 2.21)
recovers the 10-parameter form only after imposing the additional
[D, C_F] = 0 "massless photon" condition — which is baked into that
paper's *definition* of a Dirac operator and removes exactly the 36 extra
directions (verified: all 36 fail [D, C_F] = 0; all 10 SM directions satisfy
it). We extend the census to three generations (402 = 3x46 + 3x88 real
dimensions, residuals ~1e-15), classify the 264 generation-mixing
directions, and show charge conservation plus one-Higgs minimality selects
84 directions — exactly the Standard Model flavor parameter count. The
one-generation order-one theorem is machine-verified in Lean 4 (144/144
generator pairs, zero sorrys). Order-one admits; it does not select.

## 1. Introduction

The noncommutative-geometric formulation of the Standard Model encodes its
internal degrees of freedom in a finite real spectral triple
(A_F, H_F, D_F, J_F, gamma_F) with A_F = C (+) H (+) M_3(C) and
H_F = C^32 per generation [1,2]. The Dirac operator D_F carries the Yukawa
and Majorana parameters; consistency conditions — the order-zero and
order-one conditions — constrain its form. It is widely stated that these
conditions select the Standard Model Dirac operator essentially uniquely.
We show, by explicit computation, that this is not so: order-one alone
admits a 46-real-dimensional space per generation, of which the Standard
Model occupies 10 dimensions. The remaining 36 are genuine order-one
directions, removed in the literature only by an additional condition that
is usually left implicit in the statement of uniqueness.

## 2. Background and prior art

Chamseddine–Connes–Marcolli [1] classify Dirac operators for the SM finite
triple. Their Definition 2.20 states: *"A Dirac operator is a selfadjoint
operator D in H_F commuting with J_F, C_F, anticommuting with gamma_F and
fulfilling the order one condition [[D,a],b^0] = 0"* — where
C_F = {(lambda, lambda, 0)} is a central subalgebra whose physical meaning
(Remark 2.19) is "to ensure that the photon will remain massless." Their
Theorem 2.21 ("all Dirac operators are D(Y)") is proved under this
definition. The [D, C_F] = 0 requirement is therefore *definitional*, not
derived — and every downstream uniqueness claim inherits it.

Related work: Krajewski [3] classifies abstract finite triples via diagrams;
Cacic [4] constructs moduli spaces for fixed multiplicity matrices (the SM
diagram yields the 10-dimensional SM space). Boyle–Farnsworth [5] introduce
a *new* second-order constraint precisely to force D_F into SM form —
independent evidence that order-one alone does not. Devastato–Lizzi–
Martinetti [6] classify the most general Majorana Dirac for an *enlarged*
grand algebra, a different input. Jimenez–Restrepo–Rivera [7] construct a
two-Higgs-doublet NCG model by modifying the finite geometry; we exhibit
the second doublet's 8 Yukawa slots already sitting in the *unmodified*
triple's order-one nullspace. A 2025 review [8] restates the classification
with [D, C_F] = 0 still in force.

**What is new here.** No published work computes the order-one-only
nullspace — the intermediate object between "order-one" and "order-one plus
[D, C_F] = 0." We compute it (46 per generation, 402 for three), decompose
it, locate exactly where the literature's extra condition acts, and extend
the census to generation mixing. Separately, we give a zero-sorry Lean 4
verification of order-one for the imposed one-generation SM ansatz; no
spectral-triple content exists in Physlib, the community Lean physics
library, as of September 2026 (verified by source-tree inspection).

## 3. One-generation census: 46

Scanning the full 24-real-dimensional generator algebra of
A_F = C (+) H (+) M_3(C) in its 32-dimensional representation, the space
of selfadjoint gamma-odd D with [[D, pi(a)], pi^0(b)] = 0 for all 576
generator pairs is 46 real-dimensional (T4 numerical; max residual
1.78e-14). Decomposition by support and species:

| Sector | Real dims | Description |
|---|---|---|
| SM Yukawa + Majorana | 10 | the conventional D(Y) parameters |
| Flipped Yukawas | 8 | gamma-odd, J-compatible; "wrong-Higgs" slots |
| Exotic Majorana | 28 | 14 complex; (nu_R, nu_R)-type and charged slots |

Structural invariants: the C-block vanishes identically; B = conj(A);
all 36 extras are grading-odd, J-compatible, self-adjoint — genuine
order-one directions, not numerical artifacts. Two measurement artifacts
were caught and corrected by independent verification scripts during the
census (recorded in the repository, not laundered).

## 4. Where the literature's extra condition acts

For each of the 46 directions D_k we computed ||[D_k, P_{H(+)C}]||, where
P_{H(+)C} represents the central subalgebra C_F = {(lambda,lambda,0)}:

- All 10 SM directions: ||[D, C_F]|| = 0 exactly.
- All 36 extra directions: ||[D, C_F]|| >= 0.48 — none survive.

Hence the 36 = ker([., C_F])^complement intersected with the order-one
nullspace, exactly. This refines our earlier "27/28 killed by charge
conservation" phrasing: electric charge was a proxy that mislabeled the
mechanism. The precise killer — including for the EM-neutral (nu_R,nu_R)
direction — is [D, C_F] = 0. The CCM proof invokes C_F at exactly the two
places our decomposition predicts: cutting the 16-dimensional S-sector to
the 8 SM Yukawas (our 8 flipped), and forcing the Majorana T-block to the
single (nu_R, nu_R) slot (our 28 exotic).

## 5. Three generations: 402

Imposing H_F = C^32 (x) C^3 with arbitrary 3x3 complex Yukawa matrices and
symmetric 3x3 Majorana matrix (triplication imposed, not derived): the
admissible Dirac space is 2352 real-dimensional; the order-one nullity is
**402 = 3x46 (diagonal) + 3x88 (mixing)**, verified over random trials
(residuals ~1e-15, non-vacuous probes). Per generation pair, the 88 mixing
dimensions decompose into slot-disjoint subspaces:

| Family | Real dims | Fate |
|---|---|---|
| SM-like mixing | 18 | survives: off-diagonal flavor entries (CKM/PMNS-type) |
| Flipped Yukawa mixing | 16 | shelved (one-Higgs minimality) |
| Exotic Majorana mixing | 54 | killed by [D, C_F] = 0 |

No genuinely new structures appear beyond the one-generation verdict
crossed with 3x3 flavor (one structural change: E-symmetry drops in the
mixing sector).

## 6. Selection: 84

Charge conservation ([D, C_F] = 0) plus one-Higgs minimality selects
3x10 (diagonal) + 3x18 (mixing) = **84** directions =
4x18 (four 3x3 complex Yukawa matrices) + 12 (symmetric 3x3 M_R) —
exactly the Standard Model flavor parameter count. Order-one admits 402;
the selection is physical input; the count matches.

## 7. Spectral-action cross-check

Over the selected 84-direction space: Tr(D^2) = 4(||Y_nu||^2 + ||Y_e||^2
+ 3||Y_u||^2 + 3||Y_d||^2) + 2||M_R||^2 and Tr(D^4) as computed in [9];
the brackets reproduce the Chamseddine–Connes–Marcolli coefficients
a, b, c, d, e structurally (inner fluctuations off; cutoff moments kept
symbolic — no Higgs-mass or cosmological-constant prediction claimed).

## 8. Lean 4 verification

`MartinettiRep.lean`: order-zero for 144/144 selected generator pairs;
J^2 = 1; J gamma = -gamma J; full unitality; and the full order-one
theorem for the imposed one-generation Dirac ansatz over arbitrary complex
Yukawa/Majorana parameters — all 144 pairs, zero sorrys, full `lake build`
(3,316 jobs) green. Scope, honestly: the Lean theorem covers the imposed
SM ansatz over the selected 12-generator family, not the full 46-dim
space; the ansatz is input, not derived. The three-generation Lean
scaffolding (`ThreeGen.lean`) defines the tripled operators; the diagonal
three-generation order-one reduction is deferred.

## 9. What this does and does not show

**Does show:** the order-one condition, stated alone, admits a precisely
enumerated 46/402-dimensional space; the published uniqueness theorem is
uniqueness *modulo* [D, C_F] = 0, and we exhibit the 36 directions that
condition removes; the selected 84 match the SM flavor count; the
one-generation order-one theorem is machine-checked.

**Does not show:** a derivation of the Standard Model (the ansatz and the
selection are inputs); a derivation of three generations (imposed); a
derivation of flavor structure (CKM/PMNS not derived); any mass-ratio
prediction (permanently quarantined: no legitimate pre-registerable series
exists in the current axioms).

## 10. Conclusion

The order-one condition is weaker than the literature's working definition
of "Dirac operator," and the gap is now measured: 36 directions per
generation, 318 for three, each named, each residual-audited. Nothing in
the published mathematics is contradicted; something the published
mathematics never computed is now on the record — with a machine-checked
core and a permanent, labeled boundary around what is input.

*Data and code: github.com/jeffgurd888/thet-logos (attack4_corrected/:
DIRECTIONS_36.md, THREE_GEN.md, MIXING_264.md, SPECTRAL_ACTION_84.md;
lean/ThetLogos/: MartinettiRep.lean, ThreeGen.lean).*

## References

[1] A. H. Chamseddine, A. Connes, M. Marcolli, "Gravity and the Standard
Model with neutrino mixing," Adv. Theor. Math. Phys. 11 (2007) 991–1089,
hep-th/0610241. (Definition 2.20, Remark 2.19, Theorem 2.21.)
[2] A. Connes, "Noncommutative geometry and the standard model with
neutrino mixing," JHEP 0611 (2006) 081, hep-th/0608226.
[3] T. Krajewski, "Classification of finite spectral triples,"
J. Geom. Phys. 28 (1998) 1–30, hep-th/9701081.
[4] B. Cacic, "A reconstruction theorem for almost-commutative spectral
triples," Lett. Math. Phys. 100 (2012), arXiv:0902.2068.
[5] L. Boyle, S. Farnsworth, "Non-commutative geometry, non-associative
geometry and the standard model of particle physics," New J. Phys. 16
(2014) 123027, arXiv:1604.00847.
[6] F. D'Andrea, F. Lizzi, P. Martinetti, "Spectral geometry with
torsion and the superconformal field theory," arXiv:1304.0415.
[7] N. Jimenez, R. Restrepo, A. Rivera, "Type-II 2HDM in noncommutative
geometry," arXiv:2202.04222.
[8] 2025 NCG review restating the [D, C_F] = 0 classification,
arXiv:2511.05909.
[9] J. Gurd, "The Three-Generation Map," Nexus Research research report
v1.0, 2026 (github.com/jeffgurd888/thet-logos).
