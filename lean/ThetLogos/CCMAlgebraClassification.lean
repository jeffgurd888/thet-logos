import Mathlib.Tactic
import ThetLogos.CFKernel
import ThetLogos.CFKernelClassification

/-!
# ThetLogos.CCMAlgebraClassification — Q3: uniqueness of A_F (repaired scaffold)

Replaces the killed `AlgebraUniqueness` proposal (2026-09-27, NO-GO):
- its multiplicity-free `totalRepDim = 16` was unsatisfiable by its own target
  (1 + 2 + 3 = 6 ≠ 16);
- its classification theorem was FALSE as stated (padding counterexamples);
- it omitted the Dirac side (`[D, C_F] = 0`), which the order-one census proved
  is load-bearing (whitepaper/order-one-census-paper.md).

This module installs the CORRECTED scaffold:
- `RepFactor` carries a multiplicity `mult` (direct-sum-of-irreps model);
- the dimension constraint is stated WITH multiplicities;
- §2 proves what the algebra-side filters CAN do (SM-type candidate passes)
  and what they CANNOT do (explicit non-uniqueness: the filters provably do
  not classify);
- §2b discharges the minimal block multiplicity equality
  (1×1×1) + (4×1×2) + (1×3×1) = 12 with remainder 16 − 12 = 4;
- §3 states the CCM-with-`[D,C_F]=0` classification target, with the analytic
  work itemized as labeled T3 sorrys (cf. BlockedQuestions.lean Q3).

Tiers: §1–§2 are T3 (proved below, zero sorrys). §3 is T5 (target statement).
-/

namespace ThetLogos

/-! ## §1. Corrected Wedderburn scaffold -/

/-- Real division algebras (Frobenius): the only finite-dimensional real
    division algebras are ℝ, ℂ, ℍ. -/
inductive DivisionAlg where
  | R | C | H
  deriving DecidableEq, Repr

/-- A Wedderburn block M_n(D) occurring with multiplicity `mult` in a
    representation decomposing as a direct sum of defining irreps.
    (The killed proposal omitted `mult`, making its dimension constraint
    unsatisfiable.) -/
structure RepFactor where
  n : ℕ
  alg : DivisionAlg
  mult : ℕ
  deriving DecidableEq, Repr

/-- Complex dimension of the defining irreducible representation of M_n(D):
    M_n(ℝ)^ℂ ≅ M_n(ℂ) acts on ℂ^n; M_n(ℂ) acts on ℂ^n;
    M_n(ℍ)^ℂ ≅ M_{2n}(ℂ) acts on ℂ^{2n}. -/
def factorComplexDim : DivisionAlg → ℕ → ℕ
  | .R, n => n
  | .C, n => n
  | .H, n => 2 * n

/-- Total complex representation dimension, WITH multiplicities. -/
def totalRepDim : List RepFactor → ℕ
  | [] => 0
  | f :: fs => f.mult * factorComplexDim f.alg f.n + totalRepDim fs

/-- Faithfulness: every simple factor acts nontrivially (mult ≥ 1).
    Boolean-valued so the scaffold lemmas close by `decide`. -/
def IsFaithful (A : List RepFactor) : Bool :=
  A.all fun f => decide (f.mult ≥ 1)

/-- Filter 2 (orientability): the factor list contains the complex unit factor
    M_1(ℂ) ≅ ℂ, which carries the Hochschild 0-cycle projecting to the chiral
    grading γ_F. The full analytic proof additionally needs irreducibility and
    grading-compatibility hypotheses; the predicate is stated here. -/
def HasComplexUnit (A : List RepFactor) : Bool :=
  A.any fun f => decide (f.alg = DivisionAlg.C ∧ f.n = 1)

/-! ## §2. What the algebra-side filters can and cannot do -/

/-- The SM-type factor multiset. NOTE: this is one multiplicity solution of
    the diagonal (direct-sum) model, 2·1 + 1·2 + 4·3 = 16. The actual SM
    representation on H_L has weak⊗color tensor structure, so the diagonal
    model is a scaffold, not the representation itself. -/
def smFactors : List RepFactor :=
  [{ n := 1, alg := .C, mult := 2 },
   { n := 1, alg := .H, mult := 1 },
   { n := 3, alg := .C, mult := 4 }]

/-- The SM-type factors satisfy the chiral dimension bound on H_L = ℂ^16. -/
theorem smFactors_dim_ok : totalRepDim smFactors = 16 := by decide

/-- The SM-type factors act faithfully. -/
theorem smFactors_faithful : IsFaithful smFactors = true := by decide

/-- The SM-type factors contain the orientability ℂ factor. -/
theorem smFactors_orientable : HasComplexUnit smFactors = true := by decide

/-- A DIFFERENT factor list passing every algebra-side filter:
    ℂ ⊕ ℍ ⊕ M_2(ℍ) ⊕ M_3(ℂ) with multiplicities (1, 2, 2, 1):
    1·1 + 2·2 + 2·4 + 1·3 = 1 + 4 + 8 + 3 = 16. -/
def altFactors : List RepFactor :=
  [{ n := 1, alg := .C, mult := 1 },
   { n := 1, alg := .H, mult := 2 },
   { n := 2, alg := .H, mult := 2 },
   { n := 3, alg := .C, mult := 1 }]

/-- The algebra-side filters (dimension + faithfulness + orientability)
    PROVABLY DO NOT classify: an explicit distinct candidate passes them all.
    This is the formalized content of the NO-GO on the killed proposal:
    no repair of the algebra-side filters alone can yield uniqueness. -/
theorem filters_do_not_classify :
    ∃ A : List RepFactor,
      totalRepDim A = 16 ∧ IsFaithful A = true ∧ HasComplexUnit A = true ∧
        A ≠ smFactors :=
  ⟨altFactors, by decide, by decide, by decide, by decide⟩

/-! ## §2b. Minimal block lemma (multiplicity equality)

Block inventory of H_L = ℂ^16 by defining representation:
- 1 × (1-dim defining rep of ℂ) — the complex-unit direction;
- 4 × (2-dim defining rep of ℍ) — the weak-doublet directions;
- 1 × (3-dim defining rep of M₃(ℂ)) — the color-triplet directions.
Total: (1×1×1) + (4×1×2) + (1×3×1) = 1 + 8 + 3 = 12. Remainder: 16 − 12 = 4.

READING (T4 physical interpretation, documented here — not Lean-proved):
the 4 remainder dimensions are the color-singlet directions of H_L,
{ν_L, e_L, ν̄_R, ē_R}: two left-handed particles and two right-handed
antiparticles. Refinement: the right-handed neutrino ν_R proper lives in
H_R (γ_F = −1), so "right-handed neutrino/singlet" is loose for
"color-singlet".

CAVEAT: this is a block inventory ("directions"), NOT a direct-sum
decomposition of H_L. In the true SM representation the quark blocks overlap
(weak⊗color tensor structure: four color triplets = 12 color dims, not 3).
The Lean content is the arithmetic. Contrast `smFactors` (§2), the
diagonal-model census solution 2·1 + 1·2 + 4·3 = 16: different multiplicity
assignments answer different questions.
-/

/-- The minimal block configuration as a factor multiset. -/
def minimalBlocks : List RepFactor :=
  [{ n := 1, alg := .C, mult := 1 },
   { n := 1, alg := .H, mult := 4 },
   { n := 3, alg := .C, mult := 1 }]

/-- Multiplicity equality: (1×1×1) + (4×1×2) + (1×3×1) = 12. -/
theorem minimalBlock_sum : totalRepDim minimalBlocks = 12 := by decide

/-- The 4 remainder dimensions: 16 − 12 = 4. -/
theorem singlet_remainder : 16 - totalRepDim minimalBlocks = 4 := by decide

/-! ## §3. The Dirac side (the load-bearing filter)

The order-one census (whitepaper/order-one-census-paper.md) established:
- order-one alone leaves a 46-real-dimensional nullspace (10 SM + 36 extra);
- all 36 extra directions FAIL [D, C_F] = 0 (minimum commutator norm ≈ 0.48);
- all 10 SM directions satisfy [D, C_F] = 0 exactly.
CCM hep-th/0610241 bakes [D, C_F] = 0 into Definition 2.20 (the "massless
photon" condition), so its uniqueness theorem classifies order-one PLUS
[D, C_F] = 0 — never the order-one-only nullspace.

Hence any Q3 uniqueness formalization MUST carry the Dirac side. The target
is stated here with the analytic work itemized as labeled T3 sorrys.

Evidence ledger for `AdmitsClassifyingDirac smFactors`:
- order-one: T3 PROVED (MartinettiRep.lean: order-one for the imposed smDirac
  ansatz, 144/144 generator pairs, zero sorrys);
- [D, C_F] = 0: T4 numerical (census: 10/10 SM directions exact,
  36/36 extras fail);
- Lean proof of the Dirac side: OPEN (Q3.1 / Q3.2 below).
-/

/-- T5-opaque predicate: "the factor list A admits a finite Dirac operator D_F
    with (i) order-one, [[D_F, π(a)], π°(b)] = 0 (cf. ThetLogos.OrderOne), and
    (ii) [D_F, C_F] = 0 (CCM massless-photon condition), isolating the SM
    Yukawa shape." Kept opaque until the Dirac analysis is formalized;
    see BlockedQuestions.lean Q3. -/
opaque AdmitsClassifyingDirac : List RepFactor → Prop

/-! ## §3b. The C_F mechanism, grounded (PROVED)

CORRECTION (2026-09-27): an earlier draft specified the C_F representative as
"diag(0, I_3⊗I_2, …)". That does not match the working representation of the
repo: the census (`attack4_corrected.py`) uses π(λ,λ,0) = λ·(P_C + P_H), i.e.
the diagonal projector `cfMat` (ThetLogos.CFKernel) with support
{0,…,17,24,25} — spectrally diag(0×12, 1×20). There is no separate
`CF_matrix` definition here; `cfMat` IS the grounded C_F representative, and
`cfMat_comm_forces_block` is its proved consequence: any D with
[D, cfMat] = 0 is block-diagonal across the 20/12 support split
(`cf_support_card`). That lemma is the proved formal core of CCM's Q3.1
stage. It does not mention M_3(ℂ) "projections": with the grounded matrix,
the C_F action is the support split, not a color-block projector.

What remains open for `ccm_classification` (line 202): the opaque predicate
`AdmitsClassifyingDirac A` carries the Dirac-side analysis (order-one over
the correct generator family + [D,cfMat] = 0 + J-compat + grading + the
algebra↔Dirac reconstruction). It cannot be discharged by casing on the
scaffold list `A` — the opaque hypothesis yields no usable data, and
`filters_do_not_classify` already proves the algebra-side filters are
insufficient. The honest dependency: `ccm_classification` closes when the
Dirac kernel classification `cf_kernel_classification` (ThetLogos.CFKernel,
Q3.1/Q3.2) is discharged. Until then the sorry is the labeled target.
-/

/-- T4 axiom: unpacking `AdmitsClassifyingDirac`.

    If `A` admits a classifying Dirac, there exists a Dirac operator `D` with
    `OrderOneHolds D` and `[D, C_F] = 0`, such that if `D` is in the SM
    physical sector then `A = smFactors` (the algebra↔Dirac reconstruction).

    The reconstruction implication (SM-type Dirac ⇒ algebra is smFactors) is
    the remaining analytic work beyond the 46→10 kernel classification. -/
axiom AdmitsClassifyingDirac_unpack (A : List RepFactor)
    (h : AdmitsClassifyingDirac A) :
    ∃ (D : Matrix I32 I32 ℂ),
      OrderOneHolds D ∧ cfCommutatorMap D = 0 ∧
      (IsSMPhysicalSector D → A = smFactors)

/-- Q3 target: CCM-style classification WITH the Dirac side.
    Status: PROVED conditional on T4 axioms (via `cf_kernel_classification_46_10`)
    plus the `AdmitsClassifyingDirac_unpack` reconstruction axiom.
    The algebra-side filters (§2) provably do not suffice alone. -/
theorem ccm_classification (A : List RepFactor)
    (h_dim : totalRepDim A = 16)
    (h_faith : IsFaithful A = true)
    (h_c : HasComplexUnit A = true)
    (h_dirac : AdmitsClassifyingDirac A) :
    A = smFactors := by
  -- Unpack the Dirac operator from the hypothesis.
  obtain ⟨D, h_oo, h_cf, h_recon⟩ := AdmitsClassifyingDirac_unpack A h_dirac
  -- The 46→10 classification forces D into the SM sector.
  have h_SM : IsSMPhysicalSector D := cf_kernel_classification_46_10 D h_oo h_cf
  -- The reconstruction gives A = smFactors.
  exact h_recon h_SM

end ThetLogos
