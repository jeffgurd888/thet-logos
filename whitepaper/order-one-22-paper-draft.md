% DRAFT — plain text for typesetting. Not for distribution.
% Title, author, abstract, sections follow. Mathematics in LaTeX notation.

TITLE
A 22-direction classification of the order-one commutant W_{22},
a real linear subspace of the Standard Model finite spectral triple,
formalized in Lean 4

AUTHOR
Jeffrey Michael Gurd
Nexus Research (independent researcher)
jeffrey@nexus-research.org

ABSTRACT
We study the real linear subspace W_{22} of M_{32}(C) consisting of finite
Dirac operators D on the
32-dimensional Hilbert space of the Standard Model finite spectral triple
(A_F = C (+) H (+) M_3(C), KO-dimension 6) satisfying five admissibility
conditions: the first-order condition in 144-pair generator form,
commutation with a fixed color-flavor matrix, self-adjointness,
compatibility with the real structure, and grading-oddness. We exhibit 22
explicit directions in W_{22}: the 10 real tangent directions of the Standard
Model Dirac operator (real and imaginary parts of the five Yukawa
parameters) and 12 exotic directions (real and imaginary parts of six
complex color-universal exotic cross-sector couplings). Each direction is
verified in the Lean 4 proof assistant to satisfy all five conditions,
including the first-order condition; the 22 are proved linearly
independent. Our main result is a classification theorem, unconditionally
machine-checked
in Lean 4: the real dimension of W_{22} is proved to be 22 in Lean
(via an injective pivot map giving an upper bound, matched by 22
explicit independent directions), so every admissible D is a real linear
combination of the 22 explicit directions — zero sorrys, no numerical
hypotheses. We state precisely what is
machine-checked, what is numerical, and what remains open. In particular we
make no claim that the exotic directions correspond to physical fields, and
no claim of a machine-verified grand unified theory.

1. INTRODUCTION

The reconstruction of the Standard Model of particle physics from
noncommutative geometry [1,2,4,7] is among the most striking applications
of Connes' spectral paradigm: the full bosonic sector, coupled to
Einstein gravity, emerges from the spectral action of an almost-commutative
geometry M x F, where the finite noncommutative space F encodes the
internal degrees of freedom. The finite geometry is tightly constrained.
Its algebra is A_F = C (+) H (+) M_3(C) [5], its Hilbert space is
32-dimensional for one generation, and its Dirac operator D_F carries the
Yukawa parameters. A central axiom governing D_F is the first-order
condition [[D_F, a], b^o] = 0, which expresses that D_F is a first-order
differential operator relative to the algebra [2,11].

This paper classifies the solution space of a natural linearization of
these constraints. We consider the real linear subspace W_{22} of M_{32}(C)
consisting of 32x32 complex
matrices D satisfying five conditions: the first-order condition in a
144-pair generator form, commutation with a fixed color-flavor matrix,
self-adjointness, compatibility with the real structure J, and
grading-oddness. Our main result is that W_{22} is spanned by 22 explicit
directions -- 10 from the Standard Model itself and 12 exotic
color-universal couplings -- unconditionally, and that this
classification is machine-checked in the Lean 4 proof assistant [23]
with zero sorrys and no numerical hypotheses.

The contribution is threefold. First, we give 12 explicit exotic matrices
and prove, in Lean 4, that each satisfies all five admissibility
conditions, including the first-order condition (144 pairs each). Second,
we prove the 22 directions (10 Standard Model tangents plus 12 exotics)
linearly independent by an explicit pivot argument, also machine-checked.
Third, we prove the classification theorem unconditionally: every
admissible D lies in the real span of the 22 directions. The upper bound
dim_R W_{22} ≤ 22 is itself machine-checked, via an injective pivot map
from W_{22} into ℂ¹¹ (eleven pivot pairs); the 22 independent directions
give the matching lower bound. The Python numerical census that
originally suggested the count is retained as independent corroborating
evidence (Section 7).

We emphasize what this paper does not do. It does not derive the Yukawa
couplings, which remain inputs. It does not assign physical meaning to the
exotic directions; they are distinguished directions in the solution space
of the linearized constraints, and whether any correspond to physical
fields is an open question. It does not claim a machine-verified grand
unified theory. The honesty of the formalization boundary -- what is
proved, what is numerical, what is open -- is part of the result.

2. LITERATURE REVIEW

Noncommutative geometry and the Standard Model. Connes' monograph [1]
founded noncommutative geometry as a spectral branch of mathematics; the
paper [2] introduced the real structure J and the reconstruction program
of particle physics from spectral data. The Connes-Lott models [3] gave
the first noncommutative description of the electroweak sector. The
spectral action principle of Chamseddine and Connes [4] provided the
universal bosonic functional Tr f(D/Lambda), whose asymptotic expansion
yields the Standard Model Lagrangian coupled to gravity.

The modern finite geometry. Connes [5] showed that the algebra
C (+) H (+) M_3(C) is selected, up to the KO-dimension-6 condition, for
the Standard Model with neutrino mixing; Barrett [6] gave an independent
derivation of the KO-dimension-6 requirement in Lorentzian signature. The
definitive treatment is Chamseddine-Connes-Marcolli [7], which constructs
the full model with neutrino mixing, classifies the Dirac operators, and
computes the moduli space of Yukawa parameters. Subsequent developments
include the geometric explanation of the algebra [8], the heat-kernel
refinement of the spectral action [9], and the stabilization of the Higgs
mass prediction [10].

The first-order condition. The condition [[D, a], b^o] = 0 is the
noncommutative analogue of D being a first-order differential operator.
Its role as a restrictive axiom is central: Chamseddine-Connes-van
Suijlekom [11] extended inner fluctuations to triples violating the
first-order condition, finding a semigroup of fluctuations with a
quadratic term; dropping the condition altogether leads to Pati-Salam
unification [12]. The formulation of the first-order condition for finite
real spectral triples used here follows the form emphasized by Martinetti
and collaborators in the context of the Standard Model and its twisted
extensions [20,21], where the condition is evaluated on explicit algebra
generators.

Classification of finite triples. Krajewski [13] classified finite
spectral triples diagrammatically. Iochum, Schucker and Stephan [14], with
Jureit and Stephan [15,16,17], classified irreducible almost-commutative
geometries, showing that the Standard Model fits the axioms minimally in
KO-dimension 6. Reviews and expositions include van den Dungen and van
Suijlekom [18], the monograph of van Suijlekom [19], and Connes-Marcolli
[22].

Machine formalization. The proofs in this paper are checked by the Lean 4
proof assistant [23] against the Mathlib mathematical library [24]. To our
knowledge this is the first machine-checked classification of an
order-one commutant in the noncommutative Standard Model program. The
complete Lean development is publicly available [25].

3. THE FINITE TRIPLE AND THE FIRST-ORDER CONDITION

3.1. The finite spectral triple.

We work with one generation. The finite
algebra is

    A_F = C (+) H (+) M_3(C),

acting on the 32-dimensional Hilbert space H_F = C^32 with index
decomposition

    H_L:  indices 0-7,    H_R:  indices 8-15,
    H_L^c: indices 16-23,  H_R^c: indices 24-31,

the left-handed particles, right-handed particles, and their
antiparticles. The grading is

    gamma_F = diag(+1 x8, -1 x8, -1 x8, +1 x8),

and J is the antiunitary real structure exchanging particles and
antiparticles (KO-dimension 6 mod 8) [5,7].

3.2. The first-order condition in generator form.

The algebra A_F is
represented by 12 explicit generators smGen a (a = 0,...,11) spanning its
scalar (C), quaternionic (H), and color (M) sectors, with opposites
smGenOp b obtained via the real structure. The first-order condition is
imposed as

    OrderOneHolds D :<->  for all a, b,  [[D, smGen a], smGenOp b] = 0,

144 pairs in total. Lemma (real-span generators). The map
(a, b) |-> [[D, a], b^o] is real-bilinear in (a, b), and the real span of
the 12 generators smGen a is the represented algebra while the opposites
smGenOp b span its image under the real structure; hence vanishing of the
144 generator pairs implies [[D, a], b^o] = 0 for every a, b in the
algebra. The 144-pair generator form is therefore equivalent to the usual
first-order condition on the finite-dimensional representation. The
Standard Model finite Dirac operator
smDirac(yNu, yE, yU, yD, yR), depending on five complex Yukawa parameters,
satisfies this condition; this is the machine-checked theorem
smDirac_order_one, and inner fluctuations preserve it
(inner_fluctuation_preserves_order_one_smDirac).

3.3. The admissible space.

We study the real linear subspace

    W22 = { D in M_32(C) : IsW22 D },

where IsW22 D is the conjunction of five conditions:

    (i)   OrderOneHolds D            (144-pair first-order condition);
    (ii)  [D, cfMat] = 0             (commutant of a fixed color-flavor matrix);
    (iii) D* = D                     (self-adjointness);
    (iv)  D is J-compatible          (compatibility with the real structure);
    (v)   gamma_F D + D gamma_F = 0  (grading-oddness).

Each condition is real-linear, so W22 is a real linear subspace of
M_32(C). Condition (ii) encodes invariance under the color-flavor
symmetry used to isolate the admissible deformations; conditions
(iii)-(v) are the standard axioms of a finite Dirac operator [7].

4. THE TWENTY-TWO DIRECTIONS

4.1. The ten Standard Model directions.

Differentiating smDirac with
respect to the real and imaginary parts of the five Yukawa parameters
yields ten real tangent directions

    d/d Re(yX),  d/d Im(yX),   X in {Nu, E, U, D, R},

denoted smDirReNu, smDirImNu, ..., smDirReR, smDirImR. By linearity from
the theorems governing smDirac, each satisfies all five admissibility
conditions; these are the machine-checked membership lemmas
smDirReNu_mem through smDirImR_mem.

4.2. The twelve exotic directions.

There are six complex color-universal
couplings, each contributing a real and an imaginary direction:

    (1) nu_L <-> e_R      (lepton exotic cross-sector coupling);
    (2) e_L <-> nu_R      (lepton exotic cross-sector coupling);
    (3) u_L <-> d_R       (color-universal quark exotic cross-sector coupling);
    (4) d_L <-> u_R       (color-universal quark exotic cross-sector coupling);
    (5) nu_R <-> ebar_R   (Majorana-type, particle-antiparticle);
    (6) e_R <-> ebar_R    (particle-antiparticle).

The corresponding explicit 32x32 matrices are denoted exoticReNuLeR,
exoticImNuLeR, exoticReELNuR, exoticImELNuR, exoticReULDR, exoticImULDR,
exoticReDLUR, exoticImDLUR, exoticReNuREbarR, exoticImNuREbarR,
exoticReEREbarR, exoticImEREbarR. Each is proved in Lean 4 to be
self-adjoint, grading-odd, J-compatible, commuting with cfMat, and
satisfying OrderOneHolds (144 pairs each). The quark couplings are
color-universal: they act identically on the three color copies. The
Standard Model and exotic supports are disjoint as sets of matrix entries.

We stress that these directions are distinguished solutions of the
linearized constraint system. No physical interpretation is claimed; in
particular we do not claim they correspond to particles or fields.

5. THE CLASSIFICATION THEOREM

Let dirs22 : Fin 22 -> M_32(C) enumerate the ten Standard Model directions
followed by the twelve exotic directions.

Dimension bound (machine-checked). The real vector space W22 satisfies

    Module.finrank R W22 = 22,

proved in Lean with zero sorrys: an injective pivot map
(pivotMapC_injective, eleven pivot pairs) gives finrank ≤ 22, and the
22 linearly independent directions give finrank ≥ 22. No numerical
hypothesis is assumed; the Python census of Section 7 is independent
corroborating evidence.

Theorem (cf_kernel_classification_46_22, unconditional).
For every D in M_32(C) satisfying IsW22 D,

    D in Submodule.span R (Set.range dirs22);

i.e., every admissible finite Dirac operator is a real linear combination
of the 22 explicit directions.

Proof. Each of the 22 directions satisfies IsW22 (the membership lemmas of
Section 6), so span_R(dirs22) is a submodule of W22. The 22 directions are
linearly independent (Section 6, pivot argument), so the span has real
dimension 22. The machine-checked upper bound gives W22 itself real
dimension 22; a submodule of full rank is the whole space. Every step is
machine-checked in Lean 4. ∎

Corollary. The admissible deformation space of the
finite Dirac operator is exactly 22-dimensional: 10 Standard Model
directions and 12 exotic directions.

6. MACHINE FORMALIZATION IN LEAN 4

The formalization is in the public repository [25], modules
ThetLogos.CFKernelRetarget (6932 lines) and ThetLogos.CFKernel22 (999
lines). Both build cleanly with `lake build` (over 3100 jobs), contain
zero `sorry`, and declare no axioms.

6.1. What is machine-checked.

The following is an exact inventory.

(a) The Standard Model Dirac operator satisfies the 144-pair first-order
    condition:
      smDirac_order_one  (ThetLogos/MartinettiRep.lean)
    Inner fluctuations preserve the condition:
      inner_fluctuation_preserves_order_one_smDirac
        (ThetLogos/InnerFluctuations.lean)

(b) The 12 exotic matrices are explicitly defined, and for each, four
    structural lemmas are proved: self-adjointness, grading-oddness,
    J-compatibility, and commutation with cfMat (48 lemmas total,
    ThetLogos/CFKernelRetarget.lean).

(c) Each exotic matrix satisfies the 144-pair first-order condition
    (ThetLogos/CFKernelRetarget.lean):
      exoticReNuLeR_orderOne, exoticImNuLeR_orderOne,
      exoticReELNuR_orderOne, exoticImELNuR_orderOne,
      exoticReULDR_orderOne,  exoticImULDR_orderOne,
      exoticReDLUR_orderOne,  exoticImDLUR_orderOne,
      exoticReNuREbarR_orderOne, exoticImNuREbarR_orderOne,
      exoticReEREbarR_orderOne, exoticImEREbarR_orderOne.

(d) The 10 Standard Model tangent directions and the 12 exotic directions
    each satisfy all five admissibility conditions, i.e. each is a member
    of W22 (ThetLogos/CFKernel22.lean):
      smDirReNu_mem, smDirImNu_mem, smDirReE_mem, smDirImE_mem,
      smDirReU_mem, smDirImU_mem, smDirReD_mem, smDirImD_mem,
      smDirReR_mem, smDirImR_mem,
      exoticReNuLeR_mem, exoticImNuLeR_mem, exoticReELNuR_mem,
      exoticImELNuR_mem, exoticReULDR_mem, exoticImULDR_mem,
      exoticReDLUR_mem, exoticImDLUR_mem, exoticReNuREbarR_mem,
      exoticImNuREbarR_mem, exoticReEREbarR_mem, exoticImEREbarR_mem.

(e) The 22 directions are linearly independent (dirs22_independent,
    ThetLogos/CFKernel22.lean), via a general pivot-extraction lemma
    (pivot_extract): 11 disjoint entry pivots, each seeing exactly one
    real/imaginary pair with values 1 and i while all other 20 directions
    vanish there; disjointness of the Standard Model and exotic supports
    separates the two families.

(f) The unconditional classification theorem cf_kernel_classification_46_22
    (ThetLogos/CFKernel22.lean): zero sorrys, no numerical hypotheses,
    axioms limited to Lean's standard propext, Classical.choice,
    Quot.sound.

6.2. Proof techniques.

The 144-pair verifications use support arguments:
matrix-product sparsity, disjointness of supports, and entrywise
reasoning, avoiding brute-force case analysis over the 32x32 indices.
The independence proof reduces 22-dimensional linear algebra to 11
independent 2-dimensional pivot extractions.

7. THE NUMERICAL DIMENSION CENSUS (INDEPENDENT CORROBORATION)

The dimension count dim_R W22 = 22 was first suggested by a Python
numerical census and is now proved unconditionally in Lean (Section 5).
This section documents the census as independent corroborating evidence;
it is no longer a hypothesis of the classification theorem. The pipeline,
with scripts accompanying the Lean development [25], is:

(i)   The four linear conditions (grading-oddness, [D, cfMat] = 0,
      self-adjointness, J-compatibility) are assembled as a real
      constraint matrix on the 2048 real degrees of freedom of M_32(C);
      its nullspace has real dimension 92.
(ii)  The 144 order-one pairs [[D, smGen a], smGenOp b] = 0 are imposed
      as further real-linear constraints; they have rank 70, leaving a
      nullspace of real dimension 92 - 70 = 22.
(iii) The 22-dimensional nullspace is verified to be exactly spanned by
      the 22 explicit directions of Section 4, and its support is exactly
      the 72-entry union of the Standard Model and exotic supports.

A structural observation emerging from the census, currently being
formalized in Lean, is diagonal-pair killing: for diagonal generators
A = diag(lambda), B = diag(mu),

    [[D, A], B](i,j) = D(i,j) (lambda_j - lambda_i)(mu_j - mu_i),

so the first-order condition forces D(i,j) = 0 whenever both eigenvalue
differences are nonzero. Sixteen diagonal-diagonal generator pairs
suffice to annihilate all 104 entries outside the 72-entry support; the
remaining color-copy identifications are forced by off-diagonal pairs.
This mechanism is the numerical counterpart of the now machine-checked Lean pivot-map argument.

8. DISCUSSION AND OPEN PROBLEMS

We state the open problems and the explicit non-claims.

(1) Physical identification. The 12 exotic directions are distinguished
    solution-space directions, not claimed physical fields; their physical
    interpretation, if any, is open.

(2) Physical status of the exotic directions. The twelve exotic directions
    are distinguished directions in the solution space of the linearized
    constraints. Whether any of them corresponds to a physical field, and
    what their phenomenological consequences would be, is entirely open.
    This paper makes no such claim.

(3) Generations and the spectral action. The analysis is for one
    generation; three-generation mixing, the spectral action, and the
    continuum limit are out of scope.

(4) The Yukawa parameters remain inputs. The ten Standard Model directions
    parametrize first-order deformations of the finite Dirac operator;
    the axioms do not determine the numerical values of the Yukawa
    couplings.

Explicit non-claims. This paper does not claim a machine-verified grand
unified theory and does not claim physical reality for the exotic
couplings. Theorem, numerical
evidence, and interpretation are separated throughout.

ACKNOWLEDGMENTS
The author thanks the Lean 4 and Mathlib communities for the proof
assistant and libraries that made the machine-checked component possible.

BIBLIOGRAPHY

[1] A. Connes, Noncommutative Geometry, Academic Press, London and San
    Diego, 1994.
[2] A. Connes, "Noncommutative geometry and reality," J. Math. Phys. 36
    (1995) 6194-6231.
[3] A. Connes and J. Lott, "Particle models and noncommutative geometry,"
    Nucl. Phys. B (Proc. Suppl.) 18 (1991) 29-47.
[4] A. H. Chamseddine and A. Connes, "The spectral action principle,"
    Commun. Math. Phys. 186 (1997) 731-750, arXiv:hep-th/9606001.
[5] A. Connes, "Noncommutative geometry and the standard model with
    neutrino mixing," JHEP 0611 (2006) 081, arXiv:hep-th/0608226.
[6] J. W. Barrett, "A Lorentzian version of the non-commutative geometry
    of the standard model of particle physics," J. Math. Phys. 48 (2007)
    012303, arXiv:hep-th/0608221.
[7] A. H. Chamseddine, A. Connes and M. Marcolli, "Gravity and the
    standard model with neutrino mixing," Adv. Theor. Math. Phys. 11
    (2007) 991-1089, arXiv:hep-th/0610241.
[8] A. H. Chamseddine and A. Connes, "Why the Standard Model,"
    J. Geom. Phys. 58 (2008) 38-47.
[9] A. H. Chamseddine and A. Connes, "The uncanny precision of the
    spectral action," Commun. Math. Phys. 293 (2010) 867-897.
[10] A. H. Chamseddine and A. Connes, "Resilience of the spectral
    Standard Model," JHEP 1209 (2012) 104, arXiv:1208.1030.
[11] A. H. Chamseddine, A. Connes and W. D. van Suijlekom, "Inner
    fluctuations in noncommutative geometry without the first order
    condition," J. Geom. Phys. 73 (2013) 222-234, arXiv:1304.7583.
[12] A. H. Chamseddine, A. Connes and W. D. van Suijlekom, "Beyond the
    spectral Standard Model: emergence of Pati-Salam unification,"
    JHEP 1311 (2013) 132, arXiv:1304.8050.
[13] T. Krajewski, "Classification of finite spectral triples,"
    J. Geom. Phys. 28 (1998) 1-30, arXiv:hep-th/9701081.
[14] B. Iochum, T. Schucker and C. Stephan, "On a classification of
    irreducible almost commutative geometries," J. Math. Phys. 45 (2004)
    5003-5041, arXiv:hep-th/0312276.
[15] J.-H. Jureit and C. Stephan, "On a classification of irreducible
    almost commutative geometries, a second helping," J. Math. Phys. 46
    (2005) 043512, arXiv:hep-th/0501134.
[16] J.-H. Jureit, T. Schucker and C. Stephan, "On a classification of
    irreducible almost commutative geometries III," J. Math. Phys. 46
    (2005) 072303, arXiv:hep-th/0503190.
[17] J.-H. Jureit and C. Stephan, "On a classification of irreducible
    almost commutative geometries IV," J. Math. Phys. 49 (2008) 033318,
    arXiv:hep-th/0610040.
[18] K. van den Dungen and W. D. van Suijlekom, "Particle physics from
    almost-commutative spacetimes," Rev. Math. Phys. 24 (2012) 1230004.
[19] W. D. van Suijlekom, Noncommutative Geometry and Particle Physics,
    Mathematical Physics Studies, Springer, 2015.
[20] A. Devastato, F. Lizzi and P. Martinetti, "Grand symmetry, spectral
    action and the Higgs mass," JHEP 1401 (2014) 042, arXiv:1304.0415.
[21] A. Devastato and P. Martinetti, "Twisted spectral triple for the
    Standard Model and spontaneous breaking of the grand symmetry,"
    Math. Phys. Anal. Geom. 20 (2017), arXiv:1411.1320.
[22] A. Connes and M. Marcolli, Noncommutative Geometry, Quantum Fields
    and Motives, Colloquium Publications Vol. 55, American Mathematical
    Society, 2008.
[23] L. de Moura and S. Ullrich, "The Lean 4 Theorem Prover and
    Programming Language," in Automated Deduction -- CADE 28, Springer,
    2021, pp. 625-635.
[24] The mathlib Community, "The Lean mathematical library," in Proc.
    CPP 2020, ACM, 2020, pp. 367-381.
[25] J. M. Gurd, "thet-logos: Lean 4 formalization of the order-one
    commutant classification," GitHub repository,
    https://github.com/jeffgurd888/thet-logos, 2026.

APPENDIX A. THE 22 DIRECTIONS

The 22 directions are enumerated by dirs22 : Fin 22 -> M_32(C): indices
0-9 are the Standard Model tangents, indices 10-21 the exotics.

SM directions (tangent to smDirac at the Yukawa point):
  dirs22 0:  smDirReNu  = d/d Re(yNu)      dirs22 1:  smDirImNu  = d/d Im(yNu)
  dirs22 2:  smDirReE   = d/d Re(yE)       dirs22 3:  smDirImE   = d/d Im(yE)
  dirs22 4:  smDirReU   = d/d Re(yU)       dirs22 5:  smDirImU   = d/d Im(yU)
  dirs22 6:  smDirReD   = d/d Re(yD)       dirs22 7:  smDirImD   = d/d Im(yD)
  dirs22 8:  smDirReR   = d/d Re(yR)       dirs22 9:  smDirImR   = d/d Im(yR)

Exotic directions (six complex color-universal couplings):
  dirs22 10: exoticReNuLeR     Re(nu_L <-> e_R)
  dirs22 11: exoticImNuLeR     Im(nu_L <-> e_R)
  dirs22 12: exoticReELNuR     Re(e_L <-> nu_R)
  dirs22 13: exoticImELNuR     Im(e_L <-> nu_R)
  dirs22 14: exoticReULDR      Re(u_L <-> d_R, color-universal)
  dirs22 15: exoticImULDR      Im(u_L <-> d_R, color-universal)
  dirs22 16: exoticReDLUR      Re(d_L <-> u_R, color-universal)
  dirs22 17: exoticImDLUR      Im(d_L <-> u_R, color-universal)
  dirs22 18: exoticReNuREbarR  Re(nu_R <-> ebar_R, Majorana-type)
  dirs22 19: exoticImNuREbarR  Im(nu_R <-> ebar_R, Majorana-type)
  dirs22 20: exoticReEREbarR   Re(e_R <-> ebar_R)
  dirs22 21: exoticImEREbarR   Im(e_R <-> ebar_R)

Each exotic matrix is supported on explicit index pairs recorded in the
Lean source (ThetLogos/CFKernelRetarget.lean); the Standard Model and
exotic supports are disjoint. The 11 pivot pairs used in the independence
proof are documented alongside pivot_extract in ThetLogos/CFKernel22.lean.

% END OF DRAFT
